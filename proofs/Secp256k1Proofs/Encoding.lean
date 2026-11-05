import Secp256k1Proofs.Recover

/-!
# SEC 1 point encoding

`Point.ofBytes?_toBytes`, `PublicKey.ofBytes?_toBytes`: parsing the SEC 1
encoding of a public key, compressed (`02/03 ‖ x`) or uncompressed
(`04 ‖ x ‖ y`), returns the same key. The compressed case recomputes `y` with
`Point.lift?` (`lift?_eq`).
-/

open Secp256k1

namespace Secp256k1Proofs

theorem size_singleton (c : UInt8) : (ByteArray.mk #[c]).size = 1 := rfl

theorem getElem!_zero_append (c : UInt8) (b : ByteArray) : (ByteArray.mk #[c] ++ b)[0]! = c := by
  have h : 0 < (ByteArray.mk #[c] ++ b).size := by rw [ByteArray.size_append, size_singleton]; omega
  rw [getElem!_pos (ByteArray.mk #[c] ++ b) 0 h,
    ByteArray.getElem_append_left (by rw [size_singleton]; omega)]
  rfl

theorem bytesToNat_natToBytes_fp (x : Fp) : bytesToNat (natToBytes x.val 32) = x.val := by
  rw [bytesToNat_natToBytes, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

/-- **SEC 1 decoding inverts encoding** for every affine point on the curve, in
both the compressed and the uncompressed form. -/
theorem Point.ofBytes?_toBytes {x y : Fp} (h : (Point.affine x y).OnCurve) (compressed : Bool) :
    Point.ofBytes? ((Point.affine x y).toBytes compressed) = some (.affine x y) := by
  have hon : y * y = x * x * x + 7 := h
  cases compressed with
  | true =>
    simp only [Point.toBytes, ↓reduceIte]
    have key : ∀ c : UInt8, (c == 0x02 || c == 0x03) = true → (c == 0x03) = y.isOdd →
        Point.ofBytes? (ByteArray.mk #[c] ++ natToBytes x.val 32) = some (.affine x y) := by
      intro c hc23 hc3
      have hsize : (ByteArray.mk #[c] ++ natToBytes x.val 32).size = 33 := by
        rw [ByteArray.size_append, size_singleton, natToBytes_size]
      have hx : bytesToNat ((ByteArray.mk #[c] ++ natToBytes x.val 32).extract 1 33) = x.val := by
        rw [ByteArray.extract_append_eq_right (size_singleton c).symm
          (by rw [size_singleton, natToBytes_size]), bytesToNat_natToBytes_fp]
      unfold Point.ofBytes?
      rw [hsize, getElem!_zero_append, hc23, hc3]
      simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte, hx, x.isLt, ↓reduceDIte]
      rw [show (⟨x.val, x.isLt⟩ : Fp) = x from rfl, lift?_eq hon]
      simp
    apply key <;> cases y.isOdd <;> decide
  | false =>
    simp only [Point.toBytes, Bool.false_eq_true, ↓reduceIte]
    have hA : (ByteArray.mk #[0x04] ++ natToBytes x.val 32).size = 33 := by
      rw [ByteArray.size_append, size_singleton, natToBytes_size]
    have hsize : (ByteArray.mk #[0x04] ++ natToBytes x.val 32 ++ natToBytes y.val 32).size = 65 := by
      rw [ByteArray.size_append, hA, natToBytes_size]
    have h0 : (ByteArray.mk #[0x04] ++ natToBytes x.val 32 ++ natToBytes y.val 32)[0]! = 0x04 := by
      rw [ByteArray.append_assoc, getElem!_zero_append]
    have hx : bytesToNat
        ((ByteArray.mk #[0x04] ++ natToBytes x.val 32 ++ natToBytes y.val 32).extract 1 33) =
        x.val := by
      rw [← hA, ByteArray.extract_append_size_left, hA,
        ByteArray.extract_append_eq_right (size_singleton _).symm
          (by rw [size_singleton, natToBytes_size]), bytesToNat_natToBytes_fp]
    have hy : bytesToNat
        ((ByteArray.mk #[0x04] ++ natToBytes x.val 32 ++ natToBytes y.val 32).extract 33 65) =
        y.val := by
      rw [ByteArray.extract_append_eq_right hA.symm (by rw [hA, natToBytes_size]),
        bytesToNat_natToBytes_fp]
    have hcurve : (Point.affine x y).isOnCurve = true := by
      simp only [Point.isOnCurve, b, beq_iff_eq]; exact hon
    unfold Point.ofBytes?
    simp only [hsize, h0, hx, hy, x.isLt, y.isLt, and_self, ↓reduceDIte]
    simp only [show ((65 : Nat) == 33) = false by decide, Bool.false_and, Bool.false_eq_true,
      ↓reduceIte, beq_self_eq_true, Bool.and_self]
    rw [show (⟨x.val, x.isLt⟩ : Fp) = x from rfl, show (⟨y.val, y.isLt⟩ : Fp) = y from rfl,
      hcurve]
    rfl

/-- **Parsing a serialised public key returns the same key**, compressed or not. -/
theorem PublicKey.ofBytes?_toBytes (pk : ECDSA.PublicKey) (compressed : Bool) :
    ECDSA.PublicKey.ofBytes? (pk.toBytes compressed) = some pk := by
  obtain ⟨P, hv⟩ := pk
  cases P with
  | infinity => simp [Point.isValid] at hv
  | affine x y =>
    unfold ECDSA.PublicKey.ofBytes? ECDSA.PublicKey.toBytes
    dsimp only
    rw [Point.ofBytes?_toBytes (Point.onCurve_of_isValid hv)]
    exact ECDSA.PublicKey.ofPoint?_point ⟨_, hv⟩

end Secp256k1Proofs
