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

/-- **The public key is `d • G`**: for every private key, the point returned by
`PrivateKey.publicKey` (computed by the constant-time scalar multiplication
and converted to affine coordinates) corresponds to `d • G` in Mathlib's
elliptic curve group. No hypotheses: `PrivateKey` carries `d ∈ [1, n-1]`. -/
theorem publicKey_correct (sk : ECDSA.PrivateKey) :
    ∃ h, toW sk.publicKey.point h = sk.scalar.toNat • toW G G_onCurve := by
  obtain ⟨A, hA, hrep, hW⟩ := smulG_correct sk.scalar sk.valid
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
