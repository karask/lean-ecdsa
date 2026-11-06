import Secp256k1.DERProofs
import Secp256k1.CT.SignProofs

/-!
# Bitcoin Core compatibility: low-R signing and 65-byte compact signatures

* `PrivateKey.signHashLowR_spec`: every signature of `signHashLowR` (Bitcoin
  Core's `CKey::Sign`) is a `signHash` signature (for some RFC 6979 additional
  data), has `r < 2²⁵⁵` and low `s`, and so a DER encoding of at most 70 bytes
  (`PrivateKey.signHashLowR_toDER_size`).
* `RecoverableSignature.ofBitcoinCompact?_toBitcoinCompact` and
  `toBitcoinCompact_ofBitcoinCompact?`: the 65-byte encoding of
  `CKey::SignCompact` round-trips, and the parser accepts only that encoding.
-/

namespace Secp256k1.ECDSA

/-! ## Low R -/

/-- **The grinding loop returns a low-R signature of `signHash`.** -/
theorem PrivateKey.grindLowR_spec {sk : PrivateKey} {h : ByteArray} :
    ∀ {counter fuel : Nat} {sig : Signature}, sk.grindLowR h counter fuel = some sig →
      sig.r < 2 ^ 255 ∧ ∃ extra, sk.signHash h true extra = some sig
  | _, 0, _, hs => by simp [grindLowR] at hs
  | counter, fuel + 1, sig, hs => by
    unfold grindLowR at hs
    split at hs
    · simp at hs
    · rename_i sig' hsig
      split at hs
      · rename_i hr
        cases hs
        exact ⟨hr, _, hsig⟩
      · exact grindLowR_spec hs

/-- **`signHashLowR` returns a low-R signature of `signHash`.** -/
theorem PrivateKey.signHashLowR_spec {sk : PrivateKey} {h : ByteArray} {verifyAfterSign : Bool}
    {sig : Signature} (hs : sk.signHashLowR h verifyAfterSign = some sig) :
    sig.r < 2 ^ 255 ∧ ∃ extra, sk.signHash h true extra = some sig := by
  unfold signHashLowR at hs
  -- Keep `grindLowR … 256` opaque: unfolding it would run the signing loop.
  generalize hg : sk.grindLowR h 0 256 = o at hs
  have ho : o = some sig := by
    cases verifyAfterSign with
    | false => simpa using hs
    | true =>
      cases o with
      | none => simp at hs
      | some a =>
        simp only [↓reduceIte, Option.filter] at hs
        split at hs
        · exact hs
        · exact absurd hs (by simp)
  exact grindLowR_spec (hg.trans ho)

/-- Signatures of `signHash` with `lowS := true` have `s ≤ n / 2`. -/
theorem PrivateKey.signHash_lowS {sk : PrivateKey} {h extra : ByteArray} {v : Bool}
    {sig : Signature} (hs : sk.signHash h true extra v = some sig) : sig.s ≤ n / 2 := by
  obtain ⟨k, rsig, hk, hw, rfl⟩ := PrivateKey.signHash_spec hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hlow⟩ := signWithNonce_spec hk hw
  exact hlow rfl

/-! ## DER length -/

/-- A DER integer body of a value below `2²⁵⁵` has at most 32 bytes. -/
theorem Signature.derBody_size_le_32 {x : Nat} (hx : x < 2 ^ 255) : (Signature.derBody x).size ≤ 32 := by
  by_cases h0 : x = 0
  · subst h0; rw [ba_size, derBody_zero]; decide
  · obtain ⟨b, t, hE, -, hD⟩ := derBody_cases h0
    have hlen : (natToMinimalBytes x).size ≤ 32 := by
      rw [natToMinimalBytes_size]
      unfold byteLength
      simp only [h0, ↓reduceIte]
      have : x.log2 < 255 := (Nat.log2_lt h0).2 hx
      omega
    rw [ba_size, hE] at hlen
    rw [ba_size, hD]
    split
    · rename_i hc
      have hv := natToMinimalBytes_val x
      rw [bytesToNat_eq_listVal, hE, listVal_cons] at hv
      simp only [List.length_cons] at hlen ⊢
      refine (Nat.lt_or_ge t.length 31).elim (fun _ => by omega) fun hge => absurd hx ?_
      have ht : t.length = 31 := by omega
      rw [ht] at hv
      have h1 : 128 * 256 ^ 31 ≤ x := by
        rw [← hv]
        exact Nat.le_trans (Nat.mul_le_mul_right _ hc) (Nat.le_add_right _ _)
      have h2 : (2 : Nat) ^ 255 = 128 * 256 ^ 31 := by decide
      omega
    · exact hlen

theorem Signature.toDER_size (sig : Signature) :
    sig.toDER.size = 6 + (derBody sig.r).size + (derBody sig.s).size := by
  have h2 : ∀ a b : UInt8, (ByteArray.mk #[a, b]).size = 2 := fun _ _ => rfl
  simp only [toDER, derInteger, ByteArray.size_append, h2]
  omega

/-- **Low-R, low-S signatures have DER encodings of at most 70 bytes.** -/
theorem Signature.toDER_size_le_70 {sig : Signature} (hr : sig.r < 2 ^ 255)
    (hs : sig.s < 2 ^ 255) : sig.toDER.size ≤ 70 := by
  rw [toDER_size]
  have := derBody_size_le_32 hr
  have := derBody_size_le_32 hs
  omega

/-- **Signatures of `signHashLowR` have DER encodings of at most 70 bytes.** -/
theorem PrivateKey.signHashLowR_toDER_size {sk : PrivateKey} {h : ByteArray} {v : Bool}
    {sig : Signature} (hs : sk.signHashLowR h v = some sig) : sig.toDER.size ≤ 70 := by
  obtain ⟨hr, extra, he⟩ := signHashLowR_spec hs
  have hlow := signHash_lowS he
  have : n / 2 < 2 ^ 255 := by decide
  exact Signature.toDER_size_le_70 hr (by omega)

/-! ## 65-byte compact signatures -/

namespace RecoverableSignature

private theorem header_toNat (rsig : RecoverableSignature) (c : Bool) :
    (27 + rsig.recId.val + if c then 4 else 0).toUInt8.toNat =
      27 + rsig.recId.val + if c then 4 else 0 := by
  have := rsig.recId.isLt
  rw [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by split <;> omega)]

/-- **Decoding the 65-byte encoding returns the signature and the compression
flag** (for `r, s < 2²⁵⁶`). -/
theorem ofBitcoinCompact?_toBitcoinCompact (rsig : RecoverableSignature) (c : Bool)
    (hr : rsig.sig.r < 2 ^ 256) (hs : rsig.sig.s < 2 ^ 256) :
    ofBitcoinCompact? (rsig.toBitcoinCompact c) = some (rsig, c) := by
  have hsize : (rsig.toBitcoinCompact c).size = 65 := by
    rw [toBitcoinCompact, ByteArray.size_append, Signature.toCompact_size]; rfl
  have h0 : (rsig.toBitcoinCompact c)[0]!.toNat = 27 + rsig.recId.val + if c then 4 else 0 := by
    rw [ba_getElem!, toBitcoinCompact, ba_append]
    exact header_toNat rsig c
  have hext : (rsig.toBitcoinCompact c).extract 1 65 = rsig.sig.toCompact := by
    rw [toBitcoinCompact]
    exact ByteArray.extract_append_eq_right rfl (by rw [Signature.toCompact_size]; rfl)
  have := rsig.recId.isLt
  unfold ofBitcoinCompact?
  rw [ite_eq_left hsize]
  dsimp only
  rw [h0, ite_eq_left (by split <;> omega), hext, Signature.ofCompact?_toCompact _ hr hs]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · congr 1
    apply Fin.ext
    simp only [Fin.val_ofNat]
    split <;> omega
  · cases c <;> simp <;> omega

/-- **The parser accepts only the encoding of its result**: every accepted
65-byte array is `toBitcoinCompact` of the decoded signature and flag. -/
theorem toBitcoinCompact_ofBitcoinCompact? {bs : ByteArray} {rsig : RecoverableSignature}
    {c : Bool} (h : ofBitcoinCompact? bs = some (rsig, c)) : rsig.toBitcoinCompact c = bs := by
  unfold ofBitcoinCompact? at h
  split at h
  · rename_i hsize
    dsimp only at h
    split at h
    · rename_i hhdr
      cases hsig : Signature.ofCompact? (bs.extract 1 65) with
      | none => simp [hsig] at h
      | some sig =>
        simp only [hsig, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hc := Signature.toCompact_ofCompact? hsig
        apply ba_ext
        rw [toBitcoinCompact, ba_append, hc, ba_extract]
        have hb : bs.data.toList = bs[0]! :: bs.data.toList.drop 1 := by
          rw [ba_getElem!]
          have : bs.data.toList.length = 65 := by rw [← ba_size, hsize]
          cases hl : bs.data.toList with
          | nil => rw [hl] at this; simp at this
          | cons a t => rfl
        have hhead : (27 + (Fin.ofNat 4 (bs[0]!.toNat - 27)).val +
            if decide (31 ≤ bs[0]!.toNat) then 4 else 0).toUInt8 = bs[0]! := by
          apply UInt8.toNat_inj.mp
          rw [Nat.toUInt8_eq, UInt8.toNat_ofNat', Fin.val_ofNat]
          have := bs[0]!.toNat_lt
          split <;> rename_i hd <;> simp only [decide_eq_true_eq] at hd <;>
            rw [Nat.mod_eq_of_lt (by omega)] <;> omega
        conv => rhs; rw [hb]
        simp only [List.singleton_append, hhead, List.cons.injEq, true_and]
        rw [List.extract_eq_take_drop]
        have : bs.data.toList.length = 65 := by rw [← ba_size, hsize]
        rw [List.take_of_length_le (by simp; omega)]
    · simp at h
  · simp at h

end RecoverableSignature

end Secp256k1.ECDSA
