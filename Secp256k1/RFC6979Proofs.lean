import Secp256k1.SHA256Proofs

/-!
# RFC 6979: specification and proofs

`RFC6979.Spec` transcribes the HMAC-DRBG of RFC 6979 §3.2 for
`qlen = hlen = 256` on lists of bytes, on top of the specified HMAC
(`SHA256.Spec.hmac`):

* `Spec.init`: steps (b)–(g);
* `Spec.candidate st i`: the `i`-th candidate `T` of step (h), after `i`
  rejections (each followed by `K := HMAC_K(V ‖ 0x00)`, `V := HMAC_K(V)`).

`RFC6979.findNonce_eq` proves that the implementation's candidate loop returns
the result for the first candidate (in this order) that the caller accepts,
and `PrivateKey.signHashRecoverable_eq` spells this out for signing.
-/

namespace Secp256k1.RFC6979

namespace Spec

open SHA256.Spec (hmac)

/-- The HMAC-DRBG state `(K, V)`. -/
structure St where
  K : List UInt8
  V : List UInt8

/-- Steps (b)–(g), with `seed = int2octets(x) ‖ bits2octets(h₁) ‖ additional data`. -/
def init (seed : List UInt8) : St :=
  let V := List.replicate 32 0x01
  let K := List.replicate 32 0x00
  let K := hmac K (V ++ [0x00] ++ seed)
  let V := hmac K V
  let K := hmac K (V ++ [0x01] ++ seed)
  let V := hmac K V
  ⟨K, V⟩

/-- Step (h): the candidate `T = V := HMAC_K(V)` after `i` rejections, each of
which sets `K := HMAC_K(V ‖ 0x00)` and `V := HMAC_K(V)`. -/
def candidate : St → Nat → List UInt8
  | st, 0 => hmac st.K st.V
  | st, i + 1 =>
    let V := hmac st.K st.V
    let K := hmac st.K (V ++ [0x00])
    candidate ⟨K, hmac K V⟩ i

end Spec

/-- The implementation's state holds the specification's. -/
def Rel (st : State) (s : Spec.St) : Prop := st.K.data.toList = s.K ∧ st.V.data.toList = s.V

theorem toByteArray_eq {bs : ByteArray} {l : List UInt8} (h : bs.data.toList = l) :
    bs = l.toByteArray :=
  ba_ext (by rw [h, List.toList_data_toByteArray])

/-- **The candidate loop picks the first accepted candidate** of the
specification, in order. -/
theorem findNonce_eq {α : Type} (accept : ByteArray → Option α) :
    ∀ (fuel : Nat) (st : State) (s : Spec.St), Rel st s →
      findNonce accept fuel st =
        (List.range fuel).findSome? fun i => accept (Spec.candidate s i).toByteArray
  | 0, _, _, _ => rfl
  | fuel + 1, st, s, ⟨hK, hV⟩ => by
    have hT : (SHA256.hmac st.K st.V).data.toList = Spec.candidate s 0 := by
      rw [SHA256.hmac_eq_spec, hK, hV]; rfl
    -- the state after a rejected candidate
    let sNext : Spec.St :=
      ⟨SHA256.Spec.hmac s.K (SHA256.Spec.hmac s.K s.V ++ [0x00]),
        SHA256.Spec.hmac (SHA256.Spec.hmac s.K (SHA256.Spec.hmac s.K s.V ++ [0x00]))
          (SHA256.Spec.hmac s.K s.V)⟩
    have hrel : Rel (State.reseed { st with V := SHA256.hmac st.K st.V }) sNext := by
      constructor <;>
        simp only [sNext, State.reseed, SHA256.hmac_eq_spec, ByteArray.data_push, Array.toList_push,
          hK, hV]
    have hc : ∀ i, Spec.candidate s (i + 1) = Spec.candidate sNext i := fun i => by
      rw [Spec.candidate]
    have e : findNonce accept (fuel + 1) st =
        (match accept (SHA256.hmac st.K st.V) with
          | some a => some a
          | none => findNonce accept fuel (State.reseed { st with V := SHA256.hmac st.K st.V })) :=
      rfl
    have hacc : accept (SHA256.hmac st.K st.V) = accept (Spec.candidate s 0).toByteArray := by
      rw [toByteArray_eq hT]
    rw [e, hacc, List.range_succ_eq_map, List.findSome?_cons]
    cases accept (Spec.candidate s 0).toByteArray with
    | some a => rfl
    | none =>
      simp only [List.findSome?_map, Function.comp_def, hc]
      exact findNonce_eq accept fuel _ _ hrel

/-- `init` computes steps (b)–(g). -/
theorem init_rel (x h₁ extra : ByteArray) :
    Rel (init x h₁ extra)
      (Spec.init (x.data.toList ++ (bits2octets h₁).data.toList ++ extra.data.toList)) := by
  constructor <;>
    simp only [init, Spec.init, SHA256.hmac_eq_spec, ba_append, ByteArray.data_push,
      Array.toList_push, SHA256.replicate_toList, List.append_assoc]

end Secp256k1.RFC6979

namespace Secp256k1.ECDSA

/-- **Deterministic signing uses the first acceptable RFC 6979 nonce**: without
`verifyAfterSign`, `signHashRecoverable` returns `signWithNonce` for the first
of the first 64 RFC 6979 candidates that is a scalar in range and gives
non-zero `r` and `s`. The RFC 6979 seed is the private key, `bits2octets(h)`
and the additional data `extraEntropy`. -/
theorem PrivateKey.signHashRecoverable_eq (sk : PrivateKey) (h : ByteArray) (lowS : Bool)
    (extra : ByteArray) :
    sk.signHashRecoverable h lowS extra false =
      (List.range 64).findSome? fun i =>
        (CT.Scalar.ofBytes? (RFC6979.Spec.candidate (RFC6979.Spec.init
          (sk.toBytes.data.toList ++ (RFC6979.bits2octets h).data.toList ++ extra.data.toList)) i
            ).toByteArray).bind (signWithNonce sk (hashToScalar h) · lowS extra) := by
  unfold PrivateKey.signHashRecoverable
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact RFC6979.findNonce_eq _ 64 _ _ (RFC6979.init_rel _ _ _)

end Secp256k1.ECDSA
