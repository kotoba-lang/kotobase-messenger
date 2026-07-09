(ns yoro-ui.interop.signal-test
  "Full crypto round trip for yoro-ui.interop.signal, with no real network —
  ak/seed, at/at-procedure, at/at-appview-query are stubbed the same way
  post_thread_test.cljc stubs at/at-appview-or-public: cljs allows set! on
  any qualified var, restore once the whole async chain settles (not with
  with-redefs, which unwinds before the .then chain resolves)."
  (:require [cljs.test :refer-macros [deftest is async]]
            [clojure.string :as str]
            [yoro-ui.interop.signal :as signal]
            [yoro-ui.interop.actor-key :as ak]
            [yoro-ui.interop.atproto :as at]
            [kotobase.cid :as cid]
            ["@noble/curves/ed25519.js" :refer [ed25519]]))

;; Node's built-in Web Storage global only activates with a --localstorage-file
;; flag this project's `pnpm test` doesn't pass (silently a no-op otherwise —
;; every yoro-ui.interop.signal storage read/write becomes a nil/no-op, which
;; surfaces here as "no local identity" rather than a loud error). Install a
;; hermetic in-memory stand-in so the round trip doesn't depend on Node flags.
(when-not (and (exists? js/localStorage) (fn? (.-setItem js/localStorage)))
  (let [store (js/Map.)]
    (set! js/localStorage
          #js {:getItem (fn [k] (if (.has store k) (.get store k) nil))
               :setItem (fn [k v] (.set store k v) nil)
               :removeItem (fn [k] (.delete store k) nil)})))

(defn- rand-seed [] (doto (js/Uint8Array. 32) (js/crypto.getRandomValues)))

(defn- make-party []
  (let [seed (rand-seed)]
    {:seed seed :did (cid/did-key-from-ed25519-pub (.getPublicKey ed25519 seed))}))

;; A fake single-record PDS/AppView: registerPrekeys writes into `bundles`,
;; getPrekeyBundle reads from it. `current-seed` stands in for "whichever
;; party's browser is currently calling" — ensure-identity!/encrypt-message
;; read ak/seed synchronously at call time, so swapping it between calls
;; (not mid-promise-chain) correctly simulates two separate devices sharing
;; one node process.
(defn- install-fakes!
  "at-procedure/at-appview-query are multi-arity (nsid) / (nsid body|params) in
  atproto.cljc — cljs compiles call sites against that arity shape, so the
  stub must also be a multi-arity `fn` (the `([args] body)` clause form) or
  the compiled arity-2 dispatch on the replaced var throws
  \"...cljs$core$IFn$_invoke$arity$2 is not a function\". `mailbox` (default
  a fresh atom) holds app.aozora.convo.sendSealed writes, keyed by :toDid,
  each entry a vector of {:convoId :toDid :ciphertext :createdAt :rkey} —
  same shape aozora.appview.convo/list-sealed-messages would project."
  ([current-seed bundles] (install-fakes! current-seed bundles (atom {})))
  ([current-seed bundles mailbox]
   (set! ak/seed (fn [] @current-seed))
   (set! at/at-procedure
         (fn
           ([nsid] (at/at-procedure nsid {}))
           ([nsid body]
            (cond
              (= nsid "app.aozora.convo.registerPrekeys")
              (let [did (cid/did-key-from-ed25519-pub (.getPublicKey ed25519 @current-seed))]
                (swap! bundles assoc did body)
                (js/Promise.resolve {:did did :uri "at://x/y/self" :cid "bafyx" :rkey "self"}))

              (= nsid "app.aozora.convo.sendSealed")
              (let [rkey (str "sealed-" (:toDid body) "-" (random-uuid))]
                (swap! mailbox update (:toDid body) (fnil conj [])
                       (assoc body :rkey rkey :createdAt (or (:createdAt body) "2026-07-08T00:00:00Z")))
                (js/Promise.resolve {:rkey rkey :uri (str "at://mailbox/app.aozora.convo.sealedMessage/" rkey) :cid "bafyx"}))

              :else
              (js/Promise.reject (js/Error. (str "unexpected procedure " nsid)))))))
   (set! at/at-appview-query
         (fn
           ([nsid] (at/at-appview-query nsid {}))
           ([nsid params]
            (cond
              (= nsid "app.aozora.convo.getPrekeyBundle")
              (js/Promise.resolve (if-let [b (get @bundles (:did params))]
                                    (assoc b :found true)
                                    {:found false}))

              (= nsid "app.aozora.convo.listSealedMessages")
              (js/Promise.resolve {:messages (vec (get @mailbox (:toDid params) []))})

              :else
              (js/Promise.reject (js/Error. (str "unexpected query " nsid)))))))))

(defn- restore-fakes! [orig]
  (set! ak/seed (:seed orig))
  (set! at/at-procedure (:proc orig))
  (set! at/at-appview-query (:query orig)))

(deftest round-trip-encrypt-decrypt
  (async done
    (let [alice (make-party)
          bob (make-party)
          bundles (atom {})
          current-seed (atom (:seed alice))
          orig {:seed ak/seed :proc at/at-procedure :query at/at-appview-query}
          finish! (fn [] (restore-fakes! orig) (done))]
      (install-fakes! current-seed bundles)
      (-> (signal/ensure-identity! (:did alice))
          (.then (fn [_] (reset! current-seed (:seed bob)) (signal/ensure-identity! (:did bob))))
          (.then (fn [_] (reset! current-seed (:seed alice))
                   (signal/encrypt-message (:did alice) (:did bob) "hello bob")))
          (.then (fn [env1] (-> (signal/decrypt-message (:did bob) (:did alice) env1)
                                (.then (fn [pt1] [env1 pt1])))))
          (.then (fn [[env1 pt1]]
                   (is (= "hello bob" pt1) "first message round-trips through full X3DH session establishment")
                   (is (some? (:opkId env1))
                       "bob published a one-time-prekey pool (ensure-identity!'s default), so the
                        first session-establishing envelope should carry the opk-id alice consumed —
                        confirms the OPK path (x3dh-initiate's DH4) actually ran, not just X3DH-lite's 3 DHs")
                   (signal/encrypt-message (:did alice) (:did bob) "msg two")))
          (.then (fn [env2] (-> (signal/decrypt-message (:did bob) (:did alice) env2)
                                (.then (fn [pt2] [env2 pt2])))))
          (.then (fn [[env2 pt2]]
                   (is (= "msg two" pt2) "second message round-trips on the ratcheted chain")
                   (is (= 1 (get-in env2 [:header :n])) "chain counter advanced to n=1 for the second message")
                   (signal/encrypt-message (:did bob) (:did alice) "hi alice")))
          (.then (fn [env3] (-> (signal/decrypt-message (:did alice) (:did bob) env3)
                                (.then (fn [pt3] [env3 pt3])))))
          (.then (fn [[_env3 pt3]]
                   (is (= "hi alice" pt3) "reply round-trips on the independent B->A chain")
                   ;; A FRESH message, never seen by Alice: the ratchet is
                   ;; one-shot, so tampering with an ALREADY-decrypted
                   ;; envelope and redecrypting would fail for the wrong
                   ;; reason (stale chain position, not the tamper) — this
                   ;; needs a message Alice hasn't consumed yet.
                   (signal/encrypt-message (:did bob) (:did alice) "never seen untampered")))
          (.then (fn [env4]
                   ;; tampered ciphertext (correct header, wrong bytes) must
                   ;; fail closed via the AES-GCM tag, not resolve with
                   ;; garbage or throw uncaught
                   (-> (signal/decrypt-message (:did alice) (:did bob) (assoc env4 :ct "AAAAAAAAAAAAAAAA"))
                       (.then (fn [_] (is false "tampered ciphertext must reject")))
                       (.catch (fn [_] (is true "tampered ciphertext correctly rejected (GCM tag mismatch)"))))))
          (.then finish!)
          (.catch (fn [e]
                    (is false (str "unexpected rejection in round trip: " e))
                    (finish!)))))))

(deftest round-trip-degrades-gracefully-without-a-published-opk-pool
  (async done
    (let [alice (make-party)
          bob (make-party)
          bundles (atom {})
          current-seed (atom (:seed alice))
          orig {:seed ak/seed :proc at/at-procedure :query at/at-appview-query}
          finish! (fn [] (restore-fakes! orig) (done))]
      (install-fakes! current-seed bundles)
      (-> (signal/ensure-identity! (:did alice))
          (.then (fn [_] (reset! current-seed (:seed bob)) (signal/ensure-identity! (:did bob))))
          (.then (fn [_]
                   ;; simulate a legacy/emptied bundle: strip bob's published
                   ;; OPK pool AFTER ensure-identity! registered it, so
                   ;; establish-as-initiator sees none to pick from.
                   (swap! bundles update (:did bob) dissoc :oneTimePreKeys)
                   (reset! current-seed (:seed alice))
                   (signal/encrypt-message (:did alice) (:did bob) "no opk needed")))
          (.then (fn [env1]
                   (is (nil? (:opkId env1)) "no OPK available -> x3dh-initiate's opk-id is nil (DH4 skipped)")
                   (signal/decrypt-message (:did bob) (:did alice) env1)))
          (.then (fn [pt1]
                   (is (= "no opk needed" pt1)
                       "X3DH without DH4 still establishes a working session (graceful degradation, not a hard failure)")))
          (.then finish!)
          (.catch (fn [e]
                    (is false (str "unexpected rejection: " e))
                    (finish!)))))))

(deftest decrypt-rejects-wrong-peer
  (async done
    (let [alice (make-party)
          bob (make-party)
          mallory (make-party)
          bundles (atom {})
          current-seed (atom (:seed alice))
          orig {:seed ak/seed :proc at/at-procedure :query at/at-appview-query}
          finish! (fn [] (restore-fakes! orig) (done))]
      (install-fakes! current-seed bundles)
      (-> (signal/ensure-identity! (:did alice))
          (.then (fn [_] (reset! current-seed (:seed bob)) (signal/ensure-identity! (:did bob))))
          (.then (fn [_] (reset! current-seed (:seed mallory)) (signal/ensure-identity! (:did mallory))))
          (.then (fn [_] (reset! current-seed (:seed alice))
                   (signal/encrypt-message (:did alice) (:did bob) "for bob only")))
          (.then (fn [env]
                   ;; Mallory has no session with Alice and isn't the intended
                   ;; recipient — decrypting as her must not silently succeed.
                   (-> (signal/decrypt-message (:did mallory) (:did alice) env)
                       (.then (fn [_] (is false "wrong-peer decrypt must reject")))
                       (.catch (fn [_] (is true "wrong-peer decrypt correctly rejected"))))))
          (.then finish!)
          (.catch (fn [e]
                    (is false (str "unexpected rejection: " e))
                    (finish!)))))))

(deftest ensure-identity!-rejects-on-server-conflict-without-persisting-locally
  (async done
    (let [alice (make-party)
          current-seed (atom (:seed alice))
          orig {:seed ak/seed :proc at/at-procedure :query at/at-appview-query}
          finish! (fn [] (restore-fakes! orig) (done))]
      (set! ak/seed (fn [] @current-seed))
      (set! at/at-procedure
            (fn ([nsid] (at/at-procedure nsid {}))
                ([nsid _body]
                 (if (= nsid "app.aozora.convo.registerPrekeys")
                   (js/Promise.resolve {:error "IdentityConflict" :message "a different identityKey is already registered"})
                   (js/Promise.reject (js/Error. (str "unexpected procedure " nsid)))))))
      (-> (signal/ensure-identity! (:did alice))
          (.then (fn [_] (is false "must reject, not resolve, when the PDS rejects registration")))
          (.catch (fn [e]
                    (is (some? e) "rejects with the server's conflict as the reason")
                    ;; a SECOND call must retry (not think it's already registered) —
                    ;; only possible if the failed attempt never persisted locally.
                    (is (nil? (#'signal/load-identity (:did alice)))
                        "a rejected registration must not be persisted as this device's active identity")))
          (.then finish!)
          (.catch (fn [e] (is false (str "unexpected rejection: " e)) (finish!)))))))

(deftest sealed-send-receive-round-trips-and-never-stores-sender-did
  (async done
    (let [alice (make-party)
          bob (make-party)
          bundles (atom {})
          mailbox (atom {})
          current-seed (atom (:seed alice))
          orig {:seed ak/seed :proc at/at-procedure :query at/at-appview-query}
          finish! (fn [] (restore-fakes! orig) (done))]
      (install-fakes! current-seed bundles mailbox)
      (-> (signal/ensure-identity! (:did alice))
          (.then (fn [_] (reset! current-seed (:seed bob)) (signal/ensure-identity! (:did bob))))
          (.then (fn [_] (reset! current-seed (:seed alice))
                   (signal/send-sealed! (:did alice) (:did bob) "convo-1" "sealed hello")))
          (.then (fn [_] (reset! current-seed (:seed bob))
                   (signal/fetch-sealed-messages! (:did bob) (:did alice) "convo-1")))
          (.then (fn [received]
                   (is (= 1 (count received)))
                   (is (= "sealed hello" (:text (first received))) "message content round-trips")
                   (is (= (:did alice) (:senderDid (first received)))
                       "senderDid is recovered from the DECRYPTED payload, not from a plaintext record field")
                   (is (every? #(not (str/includes? (js/JSON.stringify (clj->js %)) "\"senderDid\""))
                               (get @mailbox (:did bob)))
                       "the mailbox record itself (what an AppView scan would see) never has a top-level senderDid")))
          (.then finish!)
          (.catch (fn [e] (is false (str "unexpected rejection: " e)) (finish!)))))))
