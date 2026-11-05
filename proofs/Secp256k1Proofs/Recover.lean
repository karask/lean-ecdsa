import Secp256k1Proofs.Verify

/-!
# Public key recovery

* `sqrt?_mul_self`, `lift?_eq`: the square root modulo `p` (`a^((p+1)/4)`)
  finds a root of every square, and `Point.lift?` returns the curve point with
  the requested `x`-coordinate and parity of `y`.
* `recoverHash_signHashRecoverable`, `recover_signRecoverable`: **public key
  recovery returns the signer's public key** for every recoverable signature
  produced by `PrivateKey.signRecoverable`.
-/

open Secp256k1

namespace Secp256k1Proofs

/-! ## Square roots and lifting -/

theorem e_natCast (x : Fp) : e x = (x.val : ZMod p) := e_eq_natCast x.isLt rfl

theorem e_pow (a : Fp) (k : Nat) : e (Fp.pow a k) = e a ^ k := by
  have h1 : (Fp.pow a k).val = a.val ^ k % p := by
    show (Fin.ofNat p (powMod a.val k p)).val = _
    rw [Fin.val_ofNat, powMod_eq _ _ _ p_pos, Nat.mod_mod]
  rw [e_natCast, h1, ZMod.natCast_mod, Nat.cast_pow, ← e_natCast]

/-- `a^((p+1)/4)` is a square root of every non-zero square `a` (as `p ≡ 3 mod 4`). -/
theorem sqrt?_mul_self {y : Fp} (hy : y ≠ 0) :
    ∃ r, Fp.sqrt? (y * y) = some r ∧ (r = y ∨ r = -y) := by
  have hY : e y ≠ 0 := e_ne_zero hy
  have h4 : (p + 1) / 4 * 4 = p - 1 + 2 := by decide
  have hr : e (Fp.pow (y * y) ((p + 1) / 4)) * e (Fp.pow (y * y) ((p + 1) / 4)) = e y * e y := by
    rw [e_pow, map_mul]
    generalize (p + 1) / 4 = q at h4
    calc (e y * e y) ^ q * (e y * e y) ^ q = e y ^ (q * 4) := by ring
      _ = e y * e y := by rw [h4, pow_add, ZMod.pow_card_sub_one_eq_one hY, one_mul, sq]
  have hrr : Fp.pow (y * y) ((p + 1) / 4) * Fp.pow (y * y) ((p + 1) / 4) = y * y :=
    e.injective (by rw [map_mul, map_mul, hr])
  refine ⟨Fp.pow (y * y) ((p + 1) / 4), ?_, ?_⟩
  · simp only [Fp.sqrt?, hrr, ↓reduceIte]
  · have : (Fp.pow (y * y) ((p + 1) / 4) - y) * (Fp.pow (y * y) ((p + 1) / 4) + y) = 0 := by
      grind
    rcases Fp.mul_eq_zero this with h | h
    · left; grind
    · right; grind

/-- Negation flips the parity of a non-zero element (`p` is odd). -/
theorem isOdd_neg {y : Fp} (hy : y ≠ 0) : (-y).isOdd = !y.isOdd := by
  have hv : y.val ≠ 0 := fun h => hy (Fin.ext h)
  have hlt := y.isLt
  have hp : p % 2 = 1 := by decide
  simp only [Fp.isOdd, Fin.val_neg', Nat.mod_eq_of_lt (show p - y.val < p by omega)]
  by_cases h : y.val % 2 = 1
  · have : (p - y.val) % 2 = 0 := by omega
    simp [h, this]
  · have : (p - y.val) % 2 = 1 := by omega
    simp [h, this]

/-- **`lift?` returns the curve point with the given `x` and parity.** -/
theorem lift?_eq {x y : Fp} (h : y * y = x * x * x + 7) (odd : Bool) :
    Point.lift? x odd = some (.affine x (if y.isOdd = odd then y else -y)) := by
  have hy := Point.y_ne_zero h
  obtain ⟨r, hsq, hr⟩ := sqrt?_mul_self hy
  have hn := isOdd_neg hy
  have hsq' : Fp.sqrt? (x * x * x + b) = some r := by rw [show b = 7 from rfl, ← h]; exact hsq
  simp only [Point.lift?, hsq', Option.bind_eq_bind, Option.bind_some]
  rcases hr with rfl | rfl
  · by_cases ho : r.isOdd = odd
    · simp [ho]
    · have : (-r).isOdd = odd := by rw [hn]; cases odd <;> cases h' : r.isOdd <;> simp_all
      simp [ho, this]
  · by_cases ho : y.isOdd = odd
    · have h1 : (-y).isOdd ≠ odd := by rw [hn]; cases odd <;> cases h' : y.isOdd <;> simp_all
      simp [h1, ho, neg_neg]
    · have h1 : (-y).isOdd = odd := by rw [hn]; cases odd <;> cases h' : y.isOdd <;> simp_all
      simp [ho, h1]

/-! ## The recovery id -/

theorem recId_bits (v : Nat) (hv : v < 2) (c : Prop) [Decidable c] (flip : Bool) :
    ((v + (if c then 2 else 0)) ^^^ (if flip then 1 else 0) ≥ 2 ↔ c) ∧
    ((v + (if c then 2 else 0)) ^^^ (if flip then 1 else 0)) % 2 =
      (if flip then 1 - v else v) := by
  by_cases hc : c <;> simp only [hc, ↓reduceIte] <;>
    rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl <;> cases flip <;> decide

/-! ## Recovery -/

-- `smulGSpec` unfolds to a 64-step recursion.
set_option maxRecDepth 10000 in
/-- **Public key recovery returns the signer's key** for every recoverable
signature produced by `PrivateKey.signHashRecoverable`. -/
theorem recoverHash_signHashRecoverable {sk : ECDSA.PrivateKey} {h : ByteArray} {lowS : Bool}
    {extra : ByteArray} {verifyAfterSign : Bool} {rsig : ECDSA.RecoverableSignature}
    (hs : sk.signHashRecoverable h lowS extra verifyAfterSign = some rsig) :
    ECDSA.PublicKey.recoverHash? h rsig = some sk.publicKey := by
  obtain ⟨k, hk, hw⟩ := ECDSA.PrivateKey.signHashRecoverable_spec hs
  obtain ⟨x, y, hR, hr, hr0, hrn, hk0, s₀, hs₀, hs0, hsn, flip, hsv, hrec, -⟩ :=
    ECDSA.signWithNonce_spec hk hw
  -- `R = k • G`
  have hRon : (Point.affine x y).OnCurve := hR ▸ smulGSpec_onCurve k
  have hon : y * y = x * x * x + 7 := hRon
  have hRW : toW (.affine x y) hRon = k.toNat • toW G G_onCurve :=
    (toW_congr hR.symm hRon (smulGSpec_onCurve k)).trans (toW_smulGSpec k hk)
  have hkn : k.toNat ≤ n := hk.2.le
  -- the recovered `x`-coordinate and parity
  have hxp := x.isLt
  have hpn : p < 2 * n := by decide
  have ⟨hhi, hodd⟩ := recId_bits (y.val % 2) (Nat.mod_lt _ (by decide)) (n ≤ x.val) flip
  rw [← hrec] at hhi hodd
  have hx' : (if rsig.recId.val ≥ 2 then rsig.sig.r + n else rsig.sig.r) = x.val := by
    rw [hr]
    by_cases hc : n ≤ x.val
    · rw [ite_eq_left (hhi.2 hc), Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [ite_eq_right (fun h => hc (hhi.1 h)), Nat.mod_eq_of_lt (by omega)]
  -- the lifted point is `±R`
  set y' : Fp := if y.isOdd = (rsig.recId.val % 2 == 1) then y else -y with hy'
  have hlift := lift?_eq hon (rsig.recId.val % 2 == 1)
  have hy'on : (Point.affine x y').OnCurve := by
    show y' * y' = x * x * x + 7
    rw [hy']; split <;> grind
  have hy'W : toW (.affine x y') hy'on =
      (if flip then n - k.toNat else k.toNat) • toW G G_onCurve := by
    have hpar : y.isOdd = (rsig.recId.val % 2 == 1) ↔ flip = false := by
      rw [hodd]
      rcases Nat.mod_two_eq_zero_or_one y.val with h2 | h2 <;> cases flip <;>
        simp [Fp.isOdd, h2]
    cases flip with
    | false =>
      have : y' = y := by rw [hy']; exact ite_eq_left (hpar.2 rfl)
      rw [toW_congr (by rw [this]) hy'on hRon, hRW]
      simp only [Bool.false_eq_true, ↓reduceIte]
    | true =>
      have : y' = -y := by rw [hy']; exact ite_eq_right (fun h => absurd (hpar.1 h) (by simp))
      rw [toW_congr (by rw [this]) hy'on (neg_onCurve hRon), toW_neg hRon, hRW]
      simp only [↓reduceIte]
      rw [sub_nsmul_G hkn]
  -- `u₁ • G + u₂ • R' = d • G`
  set K : ZMod n := (k.toNat : ZMod n)
  set E : ZMod n := (ECDSA.hashToScalar h : ZMod n)
  set X : ZMod n := E + (rsig.sig.r : ZMod n) * (sk.scalar.toNat : ZMod n)
  have hhn : ECDSA.hashToScalar h < n := Nat.mod_lt _ (by decide)
  have hK : K ≠ 0 := natCast_ne_zero hk0 hk.2
  have hRz : (rsig.sig.r : ZMod n) ≠ 0 := natCast_ne_zero hr0 hrn
  have hS₀ : (s₀ : ZMod n) = K⁻¹ * X := by
    rw [hs₀]
    simp only [CT.sSpec, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, ZMod.natCast_mod, pow_n_sub_two,
      K, X, E]
  have hSK : (rsig.sig.s : ZMod n) * ((if flip then n - k.toNat else k.toNat : ℕ) : ZMod n) = X := by
    cases flip with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hsv ⊢
      rw [hsv, hS₀, mul_comm, ← mul_assoc, mul_inv_cancel₀ hK, one_mul]
    | true =>
      simp only [↓reduceIte] at hsv ⊢
      rw [hsv, natCast_sub_self hsn.le, natCast_sub_self hkn, hS₀, neg_mul_neg, mul_comm,
        ← mul_assoc, mul_inv_cancel₀ hK, one_mul]
  have hQ' : ∀ hQ : (Point.smulAdd (Fn.ofNat (n - ECDSA.hashToScalar h) *
        Fn.inv (Fn.ofNat rsig.sig.r)).val G (Fn.ofNat rsig.sig.s *
        Fn.inv (Fn.ofNat rsig.sig.r)).val (.affine x y')).OnCurve,
      toW _ hQ = toW sk.publicKey.point sk.publicKey.onCurve := by
    intro hQ
    obtain ⟨hpk, hpkW⟩ := publicKey_correct sk
    rw [toW_smulAdd G_onCurve hy'on, hy'W, smul_smul, ← add_nsmul, toW_congr rfl _ hpk, hpkW]
    apply nsmul_G_congr
    rw [Nat.cast_add, Nat.cast_mul, cast_mul_inv, cast_mul_inv, natCast_sub_self hhn.le]
    have e1 : (rsig.sig.s : ZMod n) * (rsig.sig.r : ZMod n)⁻¹ *
        ((if flip then n - k.toNat else k.toNat : ℕ) : ZMod n) =
        (rsig.sig.s : ZMod n) * ((if flip then n - k.toNat else k.toNat : ℕ) : ZMod n) *
          (rsig.sig.r : ZMod n)⁻¹ := by ring
    rw [e1, hSK, show X = E + (rsig.sig.r : ZMod n) * (sk.scalar.toNat : ZMod n) from rfl]
    field_simp
    ring
  -- unfold `recoverHash?`
  obtain ⟨⟨r, s⟩, recId⟩ := rsig
  simp only at hr0 hrn hsv hx' hlift hy' hQ' hsn
  have hs0' : 0 < s ∧ s < n := by
    rw [hsv]; cases flip <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  unfold ECDSA.PublicKey.recoverHash?
  simp only [hr0, hrn, hs0'.1, hs0'.2, and_self, not_true_eq_false, ↓reduceIte, hx', x.isLt,
    ↓reduceDIte]
  rw [show (⟨x.val, x.isLt⟩ : Fp) = x from rfl, hlift]
  simp only
  have hon' := smulAdd_onCurve G_onCurve hy'on
    (Fn.ofNat (n - ECDSA.hashToScalar h) * Fn.inv (Fn.ofNat r)).val
    (Fn.ofNat s * Fn.inv (Fn.ofNat r)).val
  have heq := toW_injective (hQ' hon')
  rw [← hy', heq]
  exact ECDSA.PublicKey.ofPoint?_point _

/-- **Public key recovery returns the signer's key** for every recoverable
signature produced by `PrivateKey.signRecoverable`. -/
theorem recover_signRecoverable {sk : ECDSA.PrivateKey} {msg : ByteArray} {lowS : Bool}
    {extra : ByteArray} {verifyAfterSign : Bool} {rsig : ECDSA.RecoverableSignature}
    (hs : sk.signRecoverable msg lowS extra verifyAfterSign = some rsig) :
    ECDSA.PublicKey.recover? msg rsig = some sk.publicKey :=
  recoverHash_signHashRecoverable hs

end Secp256k1Proofs
