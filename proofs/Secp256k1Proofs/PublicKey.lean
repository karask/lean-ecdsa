import Mathlib.GroupTheory.OrderOfElement
import Secp256k1Proofs.GroupLaw

/-!
# The order of `G` and the public key

* `addOrderOf_G`: `G` has order exactly `n` in Mathlib's group of points
  (from the kernel computation `Secp256k1.windowSpec_n` and primality of `n`).
* `publicKey_correct`: for every private key `d`, the public key computed by
  the constant-time code is `d • G` (and in particular is never `𝒪`, so the
  fallback branch of `PublicKey.ofPointD` is unreachable).
-/

open Secp256k1

namespace Secp256k1Proofs

theorem nat_prime_n : Nat.Prime n := by
  rw [Nat.prime_def]; exact ⟨n_isPrime.1, n_isPrime.2⟩

theorem toW_G_ne_zero : toW G G_onCurve ≠ 0 := by
  intro h; cases h

/-- If the windowed algorithm returns `𝒪`, the integer it encodes kills `A`. -/
theorem smul_eq_zero_of_windowSpec {A : Point} (hA : A.OnCurve) (digit : Nat → Nat) (w : Nat)
    (h : A.windowSpec digit w .infinity = .infinity) :
    (∑ j ∈ Finset.range w, digit j * 16 ^ j) • toW A hA = 0 := by
  have hw := toW_windowSpec hA digit w .infinity trivial
  rw [toW_congr h _ trivial, show toW Point.infinity trivial = 0 from rfl, nsmul_zero,
    zero_add] at hw
  exact hw.symm

/-- **`n • G = 0`** in Mathlib's group of points. -/
theorem n_smul_G : n • toW G G_onCurve = 0 := by
  have h := smul_eq_zero_of_windowSpec G_onCurve nDigit 64 windowSpec_n
  have hs : (∑ j ∈ Finset.range 64, nDigit j * 16 ^ j) = n := by
    show (∑ j ∈ Finset.range 64, (n / 16 ^ j % 16) * 16 ^ j) = n
    rw [sum_digits]
    exact Nat.mod_eq_of_lt (by decide)
  rwa [hs] at h

/-- **`G` has order `n`.** -/
theorem addOrderOf_G : addOrderOf (toW G G_onCurve) = n := by
  rcases (Nat.dvd_prime nat_prime_n).1 (addOrderOf_dvd_of_nsmul_eq_zero n_smul_G) with h | h
  · exact absurd (AddMonoid.addOrderOf_eq_one_iff.1 h) toW_G_ne_zero
  · exact h

/-- `d • G ≠ 0` for `d ∈ [1, n-1]`. -/
theorem smul_G_ne_zero {k : Nat} (hk0 : k ≠ 0) (hkn : k < n) : k • toW G G_onCurve ≠ 0 := by
  intro h
  have hd := addOrderOf_dvd_of_nsmul_eq_zero h
  rw [addOrderOf_G] at hd
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hd) (by omega)

/-! ## Scalar blinding -/

set_option maxRecDepth 10000 in
theorem blindSpec_onCurve (k : CT.Scalar) (m : UInt64) : (CT.blindSpec k m).OnCurve :=
  windowSpec_onCurve G_onCurve _ 72 .infinity trivial

-- Elaborating the 72-window specification unfolds a 72-step recursion.
set_option maxRecDepth 10000 in
/-- **The blinded windowed algorithm computes `k • G`**: the digits of `k + m·n`
give `(k + m·n) • G = k • G`, as `n • G = 0`. -/
theorem toW_blindSpec (k : CT.Scalar) (hk : k.Valid) {m : UInt64} (hm : m.toNat < 2 ^ 32) :
    toW (CT.blindSpec k m) (blindSpec_onCurve k m) = k.toNat • toW G G_onCurve := by
  have ⟨hv, he⟩ := CT.Scalar.blindedWide_spec k hk.1 hm
  show toW (G.windowSpec (fun w => ((k.blindedWide m).nibble w).toNat) 72 .infinity) _ = _
  rw [toW_windowSpec G_onCurve _ 72 .infinity trivial,
    show toW Point.infinity trivial = 0 from rfl, nsmul_zero, zero_add]
  have hlt : (k.blindedWide m).toNat < 16 ^ 72 := by
    rw [he]
    have h1 : k.toNat < n := hk.2
    have h2 : n < 2 ^ 256 := by decide
    have h3 : m.toNat * n ≤ (2 ^ 32 - 1) * n := Nat.mul_le_mul_right _ (by omega)
    have h4 : (2 ^ 32 - 1) * n + n ≤ 16 ^ 72 := by decide
    omega
  have hsum : (∑ j ∈ Finset.range 72, ((k.blindedWide m).nibble j).toNat * 16 ^ j) =
      k.toNat + m.toNat * n := by
    rw [Finset.sum_congr rfl (fun j hj => by
      rw [CT.U288.nibble_toNat _ hv j (Finset.mem_range.mp hj)]), sum_digits,
      Nat.mod_eq_of_lt hlt, he]
  rw [hsum, add_nsmul, Nat.mul_comm, mul_nsmul, n_smul_G, nsmul_zero, add_zero]

theorem blindingWord_lt (s : CT.Scalar) (tag : ByteArray) :
    (CT.blindingWord s tag).toNat < 2 ^ 32 := by
  show (CT.U256.ofBytes (SHA256.hmac s.toBytes tag)).l0.toNat < 2 ^ 32
  exact (CT.U256.ofBytes_valid _).1

set_option maxRecDepth 10000 in
theorem nonceSpec_onCurve (k : CT.Scalar) : (CT.nonceSpec k).OnCurve := blindSpec_onCurve _ _

set_option maxRecDepth 10000 in
/-- The nonce point of `signCore` is `k • G`. -/
theorem toW_nonceSpec (k : CT.Scalar) (hk : k.Valid) :
    toW (CT.nonceSpec k) (nonceSpec_onCurve k) = k.toNat • toW G G_onCurve :=
  toW_blindSpec k hk (blindingWord_lt _ _)

set_option maxRecDepth 10000 in
/-- **The blinded constant-time `k • G` computes `k • G`**, for any coordinate
blinding factor and any 32-bit scalar blinding word. -/
theorem smulGBlind_correct (k : CT.Scalar) (hk : k.Valid) {z : CT.Fe} (hz : z.Valid)
    {m : UInt64} (hm : m.toNat < 2 ^ 32) :
    ∃ (A : Point) (hA : A.OnCurve), (CT.PPoint.smulGBlind k z m).Represents A ∧
      toW A hA = k.toNat • toW G G_onCurve :=
  ⟨_, blindSpec_onCurve k m, CT.PPoint.smulGBlind_correct k hz m, toW_blindSpec k hk hm⟩

/-- **The public key is `d • G`**: for every private key, the point returned by
`PrivateKey.publicKey` (computed by the constant-time scalar multiplication
and converted to affine coordinates) corresponds to `d • G` in Mathlib's
elliptic curve group. No hypotheses: `PrivateKey` carries `d ∈ [1, n-1]`. -/
theorem publicKey_correct (sk : ECDSA.PrivateKey) :
    ∃ h, toW sk.publicKey.point h = sk.scalar.toNat • toW G G_onCurve := by
  obtain ⟨A, hA, hrep, hW⟩ := smulGBlind_correct sk.scalar sk.valid
    (z := CT.blindingFactor sk.scalar CT.keyBlindTag) (CT.Fe.ofBytes_valid _)
    (m := CT.blindingWord sk.scalar CT.keyWordTag) (blindingWord_lt _ _)
  have hpt := CT.PPoint.toPoint_eq hrep
  have hk0 := CT.Scalar.toNat_ne_zero sk.isNonzero
  have hv : A.isValid = true := by
    cases A with
    | infinity => exact absurd hW.symm (smul_G_ne_zero hk0 sk.valid.2)
    | affine x y =>
      simp only [Point.isValid, Point.isOnCurve, b, beq_iff_eq]
      exact hA
  rw [ECDSA.PrivateKey.publicKey_point sk (by rw [hpt]; exact hv), hpt]
  exact ⟨hA, hW⟩

end Secp256k1Proofs
