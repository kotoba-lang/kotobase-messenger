(ns yoro-ui.interop.signal
  "Signal v3 — real E2E encryption for aozora DMs, with post-compromise
  security (90-docs/yoro/260630-app-aozora-yoro-messenger-design.md
  \"Encryption policy\").

  v2 upgraded v1's per-direction-only HMAC chain (forward secrecy but no
  healing after a key compromise) to a real Double Ratchet — kotoba.signal.
  ratchet (kotoba-lang/org-signal, cljs sibling of its JVM package) — mixing
  a fresh DH exchange in every time either side switches from receiving to
  sending.

  v3 upgrades session establishment from \"X3DH-lite\" (identity key + signed
  prekey only, 3 DHs, this file's own hand-rolled sha256 root) to full X3DH
  with one-time prekeys (kotoba.signal.x3dh, RFC-5869-HKDF root, up to 4
  DHs) — a real, distinct root-derivation formula from v2's, so an old v2
  session must never be misread as v3 or vice versa (same reasoning v1→v2
  bumped scheme/content-type; a stale client fails closed on a scheme
  mismatch instead of silently misinterpreting bytes).

  There's still NO out-of-order delivery — decrypt-message advances the
  chain by exactly one step and must be called once, in delivery order, per
  incoming message (callers are responsible for caching the plaintext
  result; re-decrypting the same message is not supported, the same way a
  real ratchet can't re-derive a key it has already erased).

  Session establishment (full X3DH via kotoba.signal.x3dh/x3dh-initiate,
  x3dh-respond — this ns supplies the DH-input keys and bootstraps
  kotoba.signal.ratchet from the resulting root, not its own DH/KDF math):
    root = HKDF(F ‖ DH1 ‖ DH2 ‖ DH3 ‖ [DH4], info, 32)
      DH1 = ECDH(myIK,  peerSPK)   DH2 = ECDH(myEK/peerEK, otherIK)
      DH3 = ECDH(mySPK/myEK, peerSPK/peerEK)   DH4 = ECDH(myEK/peerEK, otherOPK) [if an OPK was available]

  **oneTimePreKeys is a POOL, not single-use-consumed the way a real Signal
  prekey SERVER tracks OPKs.** aozora has no stateful prekey service — a
  peer's read (getPrekeyBundle) can't also mark one consumed on the
  publisher's OWN self-sovereign repo, since only the owner's session can
  write there. So `establish-as-initiator` picks ONE OPK pseudo-randomly
  from the published pool per session instead of the pool being drawn down
  one-at-a-time; the WHOLE pool rotates on the same 7-day cadence as the
  signed prekey, bounding (not eliminating) cross-session OPK reuse. This is
  a deliberate, documented deviation from single-use OPKs given the
  self-sovereign-repo architecture, not an oversight. A bundle published
  with an empty/missing OPK pool degrades gracefully to X3DH without DH4 —
  the prior X3DH-lite security level for that specific actor, since
  kotoba.signal.x3dh only computes DH4 when an OPK is present on either side.

  Identity binding: the signed prekey's signature covers `identityKey ‖
  signedPreKey` (not just the SPK alone) — so a party who can't forge the
  registrant's Ed25519 did:key signature can't substitute a different
  identityKey either. Signing key = the account's *existing* Ed25519 actor
  identity (yoro-ui.interop.actor-key/seed) — no separate signing keypair,
  and NOT kotoba.signal.x3dh/generate-identity's own :sign-seed (that would
  bind the prekey bundle to a fresh throwaway key instead of the account's
  real, externally-verifiable did:key identity peers already trust); this ns
  calls kotoba.signal.x3dh's lower-level x3dh-initiate/x3dh-respond directly
  with a hand-built identity map instead of its generate-identity/
  publish-bundle/verify-bundle, which is why.

  Fail-closed: every public fn here rejects (never silently degrades to
  plaintext or a fabricated result) on missing/unverifiable prekey bundles,
  signature failures, or AES-GCM tag mismatches."
  (:require [kotobase.cacao :as cacao]
            [kotobase.cid :as cid]
            [yoro-ui.interop.key-crypto :as kc]
            [yoro-ui.interop.actor-key :as ak]
            [yoro-ui.interop.atproto :as at]
            [kotoba.signal.x25519 :as x25519]
            [kotoba.signal.x3dh :as x3dh]
            [kotoba.signal.ratchet :as ratchet]
            ["@noble/curves/ed25519.js" :refer [ed25519]]))

(def scheme "signal-v3")
(def content-type "application/x-aozora-signal-v3+json")

(def ^:private spk-rotation-ms (* 7 24 60 60 1000))
(def ^:private opk-pool-size
  "How many one-time prekeys ensure-identity! generates per rotation. Not
  single-use-tracked (see ns docstring) — just needs to be large enough that
  an initiator picking one at random keeps cross-session OPK reuse rare
  within one 7-day rotation window, not a hard security boundary."
  20)

;; ── localStorage (per my-did / per (my-did,peer-did) pair) ──────────────────

(def ^:private ns-prefix "aozora-signal:")

(defn- ls-get [k] (when (exists? js/localStorage) (try (.getItem js/localStorage k) (catch :default _ nil))))
(defn- ls-set! [k v] (when (exists? js/localStorage) (try (.setItem js/localStorage k v) (catch :default _ nil))))

(defn- json-get [k]
  (when-let [s (ls-get k)]
    (try (js->clj (js/JSON.parse s) :keywordize-keys true) (catch :default _ nil))))

(defn- json-set! [k v] (ls-set! k (js/JSON.stringify (clj->js v))))

(defn- identity-key [did] (str ns-prefix "identity:" did))
(defn- load-identity [did] (json-get (identity-key did)))
(defn- store-identity! [did m] (json-set! (identity-key did) m))

(defn- session-key [my-did peer-did] (str ns-prefix "session-v2:" my-did ":" peer-did))

;; ── ratchet state ⇄ localStorage (bytes ⇄ base64url) ─────────────────────────

(defn- b64u [v] (when v (cacao/bytes->base64url v)))
(defn- unb64u [v] (when v (cacao/base64url->bytes v)))

(defn- ratchet-state->stored [state]
  {:dhPriv (b64u (:dh-priv state)) :dhPub (b64u (:dh-pub state)) :dhRemote (b64u (:dh-remote state))
   :rootKey (b64u (:root-key state))
   :sendChainKey (b64u (:send-chain-key state)) :sendChainRemote (b64u (:send-chain-remote state))
   :recvChainKey (b64u (:recv-chain-key state)) :recvChainRemote (b64u (:recv-chain-remote state))
   :sendN (:send-n state) :recvN (:recv-n state)})

(defn- stored->ratchet-state [stored]
  {:dh-priv (unb64u (:dhPriv stored)) :dh-pub (unb64u (:dhPub stored)) :dh-remote (unb64u (:dhRemote stored))
   :root-key (unb64u (:rootKey stored))
   :send-chain-key (unb64u (:sendChainKey stored)) :send-chain-remote (unb64u (:sendChainRemote stored))
   :recv-chain-key (unb64u (:recvChainKey stored)) :recv-chain-remote (unb64u (:recvChainRemote stored))
   :send-n (or (:sendN stored) 0) :recv-n (or (:recvN stored) 0)})

(defn- load-session-state [my-did peer-did]
  (when-let [stored (json-get (session-key my-did peer-did))]
    (stored->ratchet-state stored)))

(defn- store-session-state! [my-did peer-did state]
  (json-set! (session-key my-did peer-did) (ratchet-state->stored state)))

;; ── identity registration (full X3DH prekey bundle) ──────────────────────────

(defn- sign-bundle
  "Sign identityKey‖signedPreKey with the account's Ed25519 actor identity
  key. nil when this device holds no actor key (caller must fail closed)."
  [ik-pub spk-pub]
  (when-let [actor-seed (ak/seed)]
    (.sign ed25519 (kc/concat-bytes ik-pub spk-pub) actor-seed)))

(defn- gen-opks []
  (mapv (fn [i] (assoc (x25519/generate-keypair) :id i)) (range opk-pool-size)))

(defn- opks->stored [opks]
  (mapv (fn [k] {:priv (cacao/bytes->base64url (:priv k)) :pub (cacao/bytes->base64url (:pub k)) :id (:id k)}) opks))

(defn- stored->opks [stored]
  (mapv (fn [k] {:priv (cacao/base64url->bytes (:priv k)) :pub (cacao/base64url->bytes (:pub k)) :id (:id k)})
        (or stored [])))

(defn ensure-identity!
  "Create (first run) or rotate (every 7 days) this device's X25519 identity
  key + signed prekey + one-time-prekey pool for `did`, then (re-)register
  the public bundle with the PDS. Idempotent — safe to call on every
  sign-in/sign-up. → Promise<nil>, rejects if there's no local actor
  identity key to sign with OR the PDS rejects registration (e.g.
  IdentityConflict — see aozora.pds.prekeys — a DIFFERENT identityKey is
  already registered for this account, most likely because this is a new,
  not-yet-linked device).

  Registers with the PDS BEFORE persisting locally, not after: persisting
  first and registering second would leave this device believing its NEW
  identity is active even when the server rejected it and kept the OLD one,
  silently desyncing this device's outgoing encryption from what peers
  fetch — every message to/from this device would then fail to decrypt
  until the mismatch was somehow noticed. Rejecting here instead just means
  the SAME stale local identity gets retried next call, same as any other
  ensure-identity! failure.

  The identity X25519 key (:ik) survives rotation (same account, same
  device); the signed prekey AND the whole one-time-prekey pool are FRESH
  every rotation — see ns docstring for why the OPK pool rotates wholesale
  rather than being drawn down one-at-a-time."
  [did]
  (let [existing (load-identity did)
        stale? (or (nil? existing)
                   (> (- (js/Date.now) (or (:updatedAt existing) 0)) spk-rotation-ms))]
    (if-not stale?
      (js/Promise.resolve nil)
      (let [ik (if existing
                 {:priv (cacao/base64url->bytes (:ikPriv existing))
                  :pub (cacao/base64url->bytes (:ikPub existing))}
                 (x25519/generate-keypair))
            spk (x25519/generate-keypair)
            spk-id (inc (or (:spkId existing) 0))
            opks (gen-opks)
            sig (sign-bundle (:pub ik) (:pub spk))]
        (if-not sig
          (js/Promise.reject (js/Error. "signal: no local actor identity key — sign in first"))
          (-> (at/at-procedure "app.aozora.convo.registerPrekeys"
                               {:identityKey (cacao/bytes->base64url (:pub ik))
                                :signedPreKey (cacao/bytes->base64url (:pub spk))
                                :signedPreKeySig (cacao/bytes->base64url sig)
                                :signedPreKeyId spk-id
                                :oneTimePreKeys (mapv #(cacao/bytes->base64url (:pub %)) opks)})
              (.then (fn [resp]
                       (if (:error resp)
                         (throw (ex-info (str "signal: registerPrekeys rejected: " (:error resp))
                                         {:error (:error resp) :message (:message resp)}))
                         (store-identity! did {:ikPriv (cacao/bytes->base64url (:priv ik))
                                               :ikPub (cacao/bytes->base64url (:pub ik))
                                               :spkPriv (cacao/bytes->base64url (:priv spk))
                                               :spkPub (cacao/bytes->base64url (:pub spk))
                                               :spkId spk-id
                                               :opks (opks->stored opks)
                                               :updatedAt (js/Date.now)}))))
              (.then (fn [_] nil))))))))

;; ── prekey bundle fetch + verify ─────────────────────────────────────────────

(defn- fetch-verified-bundle
  "→ Promise<bundle-map>; rejects when the peer has no bundle registered or
  the signature over identityKey‖signedPreKey doesn't verify against the
  peer's did:key — never resolves with an unverified bundle."
  [peer-did]
  (-> (at/at-appview-query "app.aozora.convo.getPrekeyBundle" {:did peer-did})
      (.then (fn [resp]
               (if-not (:found resp)
                 (js/Promise.reject (js/Error. (str "signal: no prekey bundle registered for " peer-did)))
                 (let [sign-pub (cid/did-key->ed25519-pub peer-did)
                       ik-pub (cacao/base64url->bytes (:identityKey resp))
                       spk-pub (cacao/base64url->bytes (:signedPreKey resp))
                       sig (cacao/base64url->bytes (:signedPreKeySig resp))]
                   (if (and sign-pub (.verify ed25519 sig (kc/concat-bytes ik-pub spk-pub) sign-pub))
                     resp
                     (js/Promise.reject (js/Error. (str "signal: prekey bundle signature verification failed for " peer-did))))))))))

;; ── full X3DH root secret (kotoba.signal.x3dh) → kotoba.signal.ratchet bootstrap ──

(defn- pick-opk
  "One {:pub :id} chosen pseudo-randomly from a fetched bundle's base64url
  oneTimePreKeys pool, or nil if the pool is empty/absent (graceful
  degradation to X3DH without DH4 — see ns docstring)."
  [bundle]
  (when-let [pool (seq (:oneTimePreKeys bundle))]
    (let [i (js/Math.floor (* (js/Math.random) (count pool)))]
      {:pub (cacao/base64url->bytes (nth pool i)) :id i})))

(defn- finish-initiator!
  "Bootstrap init-sender from x3dh-initiate's result, persist, return the
  live state (with :pending-first attached — see establish-as-initiator)."
  [my-did peer-did bundle {:keys [shared-secret ek-pub opk-id]}]
  (let [peer-spk-pub (cacao/base64url->bytes (:signedPreKey bundle))]
    (-> (ratchet/init-sender shared-secret peer-spk-pub)
        (.then (fn [state]
                 (let [state' (assoc state :pending-first
                                      {:ek (cacao/bytes->base64url ek-pub)
                                       :spkId (:signedPreKeyId bundle)
                                       :opkId opk-id})]
                   (store-session-state! my-did peer-did state')
                   state'))))))

(defn- initiate-x3dh
  "Promise<{:shared-secret :ek-pub :opk-id}> — x3dh-initiate against a
  verified fetched `bundle`, with one of its one-time prekeys attached if
  the pool is non-empty (see pick-opk)."
  [my-id bundle]
  (let [ik-priv (cacao/base64url->bytes (:ikPriv my-id))
        peer-spk-pub (cacao/base64url->bytes (:signedPreKey bundle))
        opk (pick-opk bundle)
        their-bundle (cond-> {:ik (cacao/base64url->bytes (:identityKey bundle))
                              :spk peer-spk-pub}
                       opk (assoc :opk (:pub opk) :opk-id (:id opk)))]
    (x3dh/x3dh-initiate {:ik {:priv ik-priv}} their-bundle)))

(defn- establish-as-initiator
  "Alice's side: fetch + verify Bob's bundle, delegate the DH+KDF math to
  kotoba.signal.x3dh/x3dh-initiate (initiate-x3dh — also generates the
  ephemeral key and picks one of Bob's one-time prekeys if any), bootstrap
  the Double Ratchet from the resulting root secret (kotoba.signal.ratchet/
  init-sender, via finish-initiator!). → Promise<live-state-with-
  :pending-first>, already persisted; :pending-first is the one-shot X3DH
  header the very first outgoing message must also carry so Bob can replay
  the same DHs (separate from the ratchet's OWN per-message {:dh-pub :n}
  header, which init-sender already builds into the state)."
  [my-did peer-did]
  (let [my-id (load-identity my-did)]
    (if-not my-id
      (js/Promise.reject (js/Error. "signal: call ensure-identity! before starting a session"))
      (-> (fetch-verified-bundle peer-did)
          (.then (fn [bundle]
                   (-> (initiate-x3dh my-id bundle)
                       (.then #(finish-initiator! my-did peer-did bundle %)))))))))

(defn- finish-responder!
  "Bootstrap init-receiver from x3dh-respond's root secret, persist, return
  the live state."
  [my-did peer-did spk-priv spk-pub root-secret]
  (-> (ratchet/init-receiver root-secret {:priv spk-priv :pub spk-pub})
      (.then (fn [state]
               (store-session-state! my-did peer-did state)
               state))))

(defn- respond-x3dh
  "Promise<Uint8Array(32)> root secret — x3dh-respond against a verified
  fetched `bundle` (Alice's), replaying the DHs with Bob's own IK/SPK/OPK
  privkeys, Alice's ephemeral pubkey, and the opk-id she used (if any)."
  [my-id bundle ek-pub opk-id]
  (let [ik-priv (cacao/base64url->bytes (:ikPriv my-id))
        spk-priv (cacao/base64url->bytes (:spkPriv my-id))
        peer-ik-pub (cacao/base64url->bytes (:identityKey bundle))
        my-identity {:ik {:priv ik-priv} :spk {:priv spk-priv}
                     :opks (stored->opks (:opks my-id))}]
    (x3dh/x3dh-respond my-identity peer-ik-pub ek-pub opk-id)))

(defn- establish-as-responder
  "Bob's side: replays the same DHs kotoba.signal.x3dh/x3dh-respond
  computes (respond-x3dh) using his own IK/SPK/OPK privkeys against Alice's
  identityKey (from her verified bundle) and ephemeral key + chosen opk-id
  (from the incoming envelope's :pending-first header), bootstraps the
  Double Ratchet as the receiver (finish-responder! → init-receiver, using
  Bob's own SPK keypair as the initial ratchet key — the same convention
  init-sender's peer-spk-pub argument assumes). A stale/rotated-away opk-id
  (Bob rotated his pool between Alice fetching the bundle and her first
  message arriving) means x3dh-respond either can't find that index or
  finds a DIFFERENT keypair than Alice used — the derived secrets won't
  match and the ratchet's own AES-GCM tag check on the first message fails
  closed, same as any other bad session (rare race, not a security hole;
  see ns docstring on OPK pool rotation). → Promise<live-state>."
  [my-did peer-did ek-b64u opk-id]
  (let [my-id (load-identity my-did)]
    (if-not my-id
      (js/Promise.reject (js/Error. "signal: call ensure-identity! before receiving a session"))
      (-> (fetch-verified-bundle peer-did)
          (.then (fn [bundle]
                   (let [spk-priv (cacao/base64url->bytes (:spkPriv my-id))
                         spk-pub (cacao/base64url->bytes (:spkPub my-id))
                         ek-pub (cacao/base64url->bytes ek-b64u)]
                     (-> (respond-x3dh my-id bundle ek-pub opk-id)
                         (.then #(finish-responder! my-did peer-did spk-priv spk-pub %))))))))))

;; ── public encrypt / decrypt ─────────────────────────────────────────────────

(defn encrypt-message
  "Encrypt `plaintext` for `peer-did`, establishing a session first if none
  exists. → Promise<envelope-map> — JSON-serialize this into the message's
  `text` field, with `contentType`/`encryption` set to the constants above."
  [my-did peer-did plaintext]
  (-> (or (some-> (load-session-state my-did peer-did) js/Promise.resolve)
          (establish-as-initiator my-did peer-did))
      (.then (fn [state]
               (-> (ratchet/encrypt-message (dissoc state :pending-first) (kc/utf8->bytes plaintext))
                   (.then (fn [[state' {:keys [header iv ciphertext]}]]
                            (store-session-state! my-did peer-did state')
                            (cond-> {:v 3 :alg scheme
                                     :header {:dhPub (b64u (:dh-pub header)) :n (:n header)}
                                     :iv (b64u iv) :ct (b64u ciphertext)}
                              (:pending-first state) (merge (:pending-first state))))))))))

(defn decrypt-message
  "Decrypt one incoming `envelope` (parsed from a message's `text` field) from
  `peer-did`. Must be called exactly once per message, in delivery order —
  each call advances the receive ratchet by one step (DH-ratcheting first if
  the sender's header dh-pub is new) and the consumed key is gone afterward
  (that's forward secrecy/post-compromise security working as intended, not
  a bug). Callers own caching the returned plaintext. → Promise<string>;
  rejects (never returns garbage) on a bad session, wrong scheme, or a
  failed AES-GCM tag."
  [my-did peer-did envelope]
  (if (not= (:alg envelope) scheme)
    (js/Promise.reject (js/Error. (str "signal: unsupported/mismatched scheme " (:alg envelope))))
    (-> (let [state (load-session-state my-did peer-did)]
          (cond
            (and (:ek envelope) (nil? state)) (establish-as-responder my-did peer-did (:ek envelope) (:opkId envelope))
            state (js/Promise.resolve state)
            :else (js/Promise.reject (js/Error. (str "signal: no session and no session-establishing header for " peer-did)))))
        (.then (fn [state]
                 (let [live-envelope {:header {:dh-pub (unb64u (get-in envelope [:header :dhPub]))
                                               :n (get-in envelope [:header :n])}
                                      :iv (unb64u (:iv envelope))
                                      :ciphertext (unb64u (:ct envelope))}]
                   (-> (ratchet/decrypt-message state live-envelope)
                       (.then (fn [[state' pt]]
                                (store-session-state! my-did peer-did state')
                                (kc/bytes->utf8 pt))))))))))

;; ── sealed sending payload convention (Sealed Sender-equivalent) ────────────
;;
;; app.aozora.convo.sendSealed stores the record with NO plaintext senderDid
;; field, under a neutral non-attributing repo — see that lexicon's
;; description and aozora.pds.convo/send-sealed-message's docstring for the
;; full design (a genuine Sealed-Sender-equivalent, not full conversation-
;; graph anonymity: toDid, like a real push service the transport still has
;; to route through, stays visible — same scope real Signal Sealed Sender
;; has). This layer is a PAYLOAD-SHAPE convention on top of the SAME
;; signal-v3 encrypt-message/decrypt-message above, not a new crypto scheme:
;; the sender's own DID rides INSIDE the already-E2E-encrypted JSON payload
;; instead of as a plaintext record field, so only the one party who can
;; decrypt it (the intended recipient, via their established ratchet
;; session) ever learns who sent it.

(defn encrypt-sealed-message
  "→ Promise<envelope-map> — same shape as encrypt-message's, but the
  encrypted plaintext is {:senderDid my-did :text plaintext} JSON instead of
  the bare text, so decrypt-sealed-message's caller learns the sender only
  after decrypting."
  [my-did peer-did plaintext]
  (encrypt-message my-did peer-did (js/JSON.stringify #js {:senderDid my-did :text plaintext})))

(defn decrypt-sealed-message
  "→ Promise<{:senderDid :text}> — decrypts exactly like decrypt-message,
  then unwraps encrypt-sealed-message's JSON payload shape."
  [my-did peer-did envelope]
  (-> (decrypt-message my-did peer-did envelope)
      (.then (fn [json-str] (js->clj (js/JSON.parse json-str) :keywordize-keys true)))))

;; ── sealed mailbox XRPC (app.aozora.convo.sendSealed / listSealedMessages) ──
;;
;; fetch-sealed-messages! takes `peer-did` explicitly — receiving a sealed
;; message REQUIRES already knowing who it's from, not the other way around.
;; This is a real, deliberate scope boundary, not an oversight: sessions here
;; are looked up by (my-did, peer-did) pair (load-session-state), the same
;; way the regular (non-sealed) path always has been, and there is no
;; cryptographic session-identification mechanism in this envelope format
;; (unlike real Signal, whose Double Ratchet header ITSELF carries enough
;; key material to identify a session without prior knowledge of the
;; sender — adding that here would mean embedding raw identity-key bytes
;; in first-message envelopes instead of relying on fetch-verified-bundle's
;; DID-keyed lookup, a real protocol change, not a UI wiring change).
;; So: sealed sending/receiving works WITHIN a conversation whose other
;; party you already know (open a thread, then check for sealed messages
;; from that specific peer) — it hides the sender from the STORAGE/AppView
;; layer (anyone scanning app.aozora.convo.sealedMessage records), not from
;; a recipient who's opened a chat with someone they already know. That is
;; still the real, useful privacy property Sealed Sender is FOR (per-message
;; transport/storage metadata, not "receive anonymous mail from strangers").

(defn send-sealed!
  "Encrypt `plaintext` for `peer-did` (as the recipient) with the sender's
  DID sealed inside the payload, then POST app.aozora.convo.sendSealed.
  Establishes a session first if none exists, same as encrypt-message/
  send-message. → Promise<xrpc-response>."
  [my-did peer-did convo-id plaintext]
  (-> (encrypt-sealed-message my-did peer-did plaintext)
      (.then (fn [envelope]
               (at/at-procedure "app.aozora.convo.sendSealed"
                                {:convoId convo-id
                                 :toDid peer-did
                                 :ciphertext (js/JSON.stringify (clj->js envelope))})))))

(defn- decrypt-sealed-record
  "One listSealedMessages row → Promise<{:convoId :rkey :createdAt :senderDid
  :text} | nil>; nil (not a rejection) on a record this device can't
  decrypt (e.g. genuinely corrupt, or addressed to a DIFFERENT session than
  the one `peer-did` names). A mailbox listing should show what it CAN
  decrypt, not fail the whole page over one bad row."
  [my-did peer-did record]
  (let [envelope (js->clj (js/JSON.parse (:ciphertext record)) :keywordize-keys true)]
    (-> (decrypt-sealed-message my-did peer-did envelope)
        (.then (fn [{:keys [senderDid text]}]
                 {:convoId (:convoId record) :rkey (:rkey record) :createdAt (:createdAt record)
                  :senderDid senderDid :text text}))
        (.catch (fn [_] nil)))))

(defn fetch-sealed-messages!
  "GET app.aozora.convo.listSealedMessages for `my-did`, scoped to
  `convo-id`, decrypt every row assuming it's from `peer-did` (best-effort —
  see decrypt-sealed-record), drop the ones that failed. → Promise<[{:convoId
  :rkey :createdAt :senderDid :text} …]>, oldest first (matches
  listMessages' ordering). See the ns section comment above for why
  `peer-did` must already be known — this is not a blind inbox scan."
  [my-did peer-did convo-id]
  (-> (at/at-appview-query "app.aozora.convo.listSealedMessages" {:toDid my-did :convoId convo-id})
      (.then (fn [{:keys [messages]}]
               (js/Promise.all (into-array (map #(decrypt-sealed-record my-did peer-did %) messages)))))
      (.then (fn [^js results] (vec (remove nil? (array-seq results)))))))
