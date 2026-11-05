import Secp256k1.CT.SmulProofs

/-!
# The constant-time signing core

* `CT.signCore_spec`: `signCore d k e` returns `r = R.x mod n` and
  `s = k⁻¹ · (e + r·d) mod n` (with `k⁻¹ = k^(n-2)`), where `R` is the point
  computed by the constant-time `k • G`; the recovery id holds the parity of
  `R.y` and whether `R.x ≥ n`; and the success flag is set exactly when `k`,
  `r` and `s` are all non-zero.
* `ECDSA.signWithNonce_spec`: what `signWithNonce` returns, including the
  low-S normalisation and the matching flip of the recovery id.

That such signatures satisfy the ECDSA verification equation is proved with
Mathlib in `proofs/`.
-/

namespace Secp256k1

namespace Point

/-- The affine `x`-coordinate, with `0` for `𝒪` (matching `PPoint.toAffine`). -/
def affX : Point → Fp
  | .infinity => 0
  | .affine x _ => x

/-- The affine `y`-coordinate, with `0` for `𝒪` (matching `PPoint.toAffine`). -/
def affY : Point → Fp
  | .infinity => 0
  | .affine _ y => y

theorem onCurve_of_isValid {P : Point} (h : P.isValid = true) : P.OnCurve := by
  cases P with
  | infinity => trivial
  | affine x y =>
    simp only [Point.isValid, Point.isOnCurve, b, beq_iff_eq] at h
    exact h

end Point

theorem ECDSA.PublicKey.onCurve (pk : PublicKey) : pk.point.OnCurve :=
  Point.onCurve_of_isValid pk.isValid

theorem ECDSA.PublicKey.ofPoint?_point (pk : PublicKey) : PublicKey.ofPoint? pk.point = some pk := by
  simp only [PublicKey.ofPoint?, pk.isValid, ↓reduceDIte]

theorem Fp.inv_zero : Fp.inv 0 = 0 := by
  apply Fin.ext
  rw [Fp.val_inv, show (0 : Fp).val = 0 from rfl, Nat.zero_pow (show 0 < p - 2 by decide),
    Nat.zero_mod]

namespace CT

/-! ## Arithmetic and bit facts -/

theorem Fe.R.congr {a : Fe} {x y : Fp} (h : a.R x) (e : x = y) : a.R y := e ▸ h

/-- The canonical limbs of a field element hold its value. -/
theorem Fe.R.toU256 {a : Fe} {x : Fp} (h : a.R x) :
    a.toU256.Valid ∧ a.toU256.toNat = x.val := by
  refine ⟨(pMod.fromMont_spec pMod_valid a.mont h.1.1).1, ?_⟩
  rw [← h.2, Fe.toFp_val _ h.1]
  rfl

theorem Scalar.reduce_spec (a : U256) (ha : a.Valid) :
    (Scalar.reduce a).Valid ∧ (Scalar.reduce a).toNat = a.toNat % n := by
  have hM := nMod_valid
  have ⟨v1, e1⟩ := nMod.toMont_spec hM a ha
  have ⟨v2, lt2, e2⟩ := nMod.fromMont_spec hM _ v1
  have hval : nMod.value = n := rfl
  rw [hval] at e1 lt2 e2
  have hres : (nMod.fromMont (nMod.toMont a)).toNat = a.toNat % n := by
    apply mod_cancel (k := 2 ^ 256) (m := n) hM.coprime lt2 (Nat.mod_lt _ (by decide))
    rw [Nat.mul_comm, e2, e1, Nat.mod_mod, Nat.mul_mod_mod, Nat.mul_comm]
  exact ⟨⟨v2, lt2⟩, hres⟩

theorem Scalar.ofNat_spec (x : Nat) : (Scalar.ofNat x).Valid ∧ (Scalar.ofNat x).toNat = x % n := by
  have ⟨v, e⟩ := U256.ofNat_spec (x % n)
  have hlt : x % n < n := Nat.mod_lt _ (by decide)
  have : x % n % 2 ^ 256 = x % n := Nat.mod_eq_of_lt (Nat.lt_trans hlt (by decide))
  rw [this] at e
  exact ⟨⟨v, by show (U256.ofNat (x % n)).toNat < n; rw [e]; exact hlt⟩, e⟩

theorem Scalar.isZero_eq {s : Scalar} (hs : s.Valid) :
    s.isZero = if s.toNat = 0 then 1 else 0 := by
  split
  · exact U256.isZero_eq_one hs.1 ‹_›
  · exact U256.isZero_eq_zero ‹_›

/-- The constant-time comparison returns `1` or `0`. -/
theorem U256.lt_eq {a b : U256} (ha : a.Valid) (hb : b.Valid) :
    U256.lt a b = if a.toNat < b.toNat then 1 else 0 := by
  have hc := (U256.sub_toNat a b ha hb).2
  split
  · exact (U256.lt_eq_one_iff ha hb).2 ‹_›
  · rcases UInt64.eq_zero_or_one hc with h | h
    · exact h
    · exact absurd ((U256.lt_eq_one_iff ha hb).1 h) ‹_›

theorem U256.l0_and_one (u : U256) : (u.l0 &&& 1).toNat = u.toNat % 2 := by
  rw [UInt64.toNat_and, UInt64.toNat_one, Nat.and_one_is_mod]
  simp only [U256.toNat]
  omega

theorem bit_of_toNat {u : UInt64} (h : u.toNat < 2) : u = if u.toNat = 1 then 1 else 0 := by
  rcases UInt64.eq_zero_or_one (Nat.le_of_lt_succ h) with h' | h' <;> subst h' <;> decide

theorem or_shl_toNat {u v : UInt64} (hu : u.toNat < 2) (hv : v.toNat < 2) :
    (u ||| (v <<< 1)).toNat = u.toNat + 2 * v.toNat := by
  rw [bit_of_toNat hu, bit_of_toNat hv]
  split <;> split <;> decide

theorem ok_ne_zero {a b c : UInt64} (ha : a.toNat < 2) (hb : b.toNat < 2) (hc : c.toNat < 2) :
    (a ||| b ||| c) ^^^ 1 ≠ 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  rw [bit_of_toNat ha, bit_of_toNat hb, bit_of_toNat hc]
  split <;> split <;> split <;> decide

/-! ## Affine conversion -/

/-- `toAffine` returns the affine coordinates of the represented point
(`0, 0` for `𝒪`, since `0⁻¹ = 0`). -/
theorem PPoint.toAffine_spec {P : PPoint} {A : Point} (hP : P.Represents A) :
    P.toAffine.1.R A.affX ∧ P.toAffine.2.1.R A.affY := by
  obtain ⟨hx, hy, hz, hrep⟩ := hP
  have rX : P.X.R P.X.toFp := ⟨hx, rfl⟩
  have rY : P.Y.R P.Y.toFp := ⟨hy, rfl⟩
  have rZ : P.Z.R P.Z.toFp := ⟨hz, rfl⟩
  have hxi := Fe.R.mul rX (Fe.R.inv rZ)
  have hyi := Fe.R.mul rY (Fe.R.inv rZ)
  refine ⟨hxi.congr ?_, hyi.congr ?_⟩ <;> cases A with
  | infinity =>
    obtain ⟨_, hZ, _⟩ := hrep
    rw [hZ, Fp.inv_zero, mul_zero']; rfl
  | affine x y =>
    obtain ⟨hZ, hX, hY⟩ := hrep
    have hzi := Fp.mul_inv_cancel hZ
    simp only [Point.affX, Point.affY]
    first | rw [hX] | rw [hY]
    grind

/-! ## The signing core -/

/-- The point `R = k • G` computed by the constant-time scalar multiplication
(`PPoint.smulG_correct`). -/
def smulGSpec (k : Scalar) : Point := G.windowSpec (fun w => (k.nibble w).toNat) 64 .infinity

/-- `k⁻¹ · (e + r·d) mod n` with `k⁻¹ = k^(n-2)`, in the form `signCore` computes it. -/
def sSpec (d k e r : Nat) : Nat := k ^ (n - 2) % n * ((e + r * d % n) % n) % n

/-- **The signing core computes ECDSA.** With `R = k • G`:
`r = R.x mod n`, `s = k⁻¹ · (e + r·d) mod n`, the recovery id is
`R.y mod 2 + 2·[R.x ≥ n]`, and `ok ≠ 0` exactly when `k`, `r` and `s` are
non-zero. -/
theorem signCore_spec (d k e : Scalar) (hd : d.Valid) (hk : k.Valid) (he : e.Valid) :
    (signCore d k e).r.Valid ∧
    (signCore d k e).r.toNat = (smulGSpec k).affX.val % n ∧
    (signCore d k e).s.Valid ∧
    (signCore d k e).s.toNat = sSpec d.toNat k.toNat e.toNat (signCore d k e).r.toNat ∧
    (signCore d k e).recId.toNat =
      (smulGSpec k).affY.val % 2 + (if n ≤ (smulGSpec k).affX.val then 2 else 0) ∧
    ((signCore d k e).ok ≠ 0 ↔
      k.toNat ≠ 0 ∧ (signCore d k e).r.toNat ≠ 0 ∧ (signCore d k e).s.toNat ≠ 0) := by
  have hrep : (PPoint.smulG k).Represents (smulGSpec k) := PPoint.smulG_correct k
  unfold signCore
  generalize PPoint.smulG k = P at hrep ⊢
  generalize smulGSpec k = R at hrep ⊢
  have ⟨hxR, hyR⟩ := PPoint.toAffine_spec hrep
  generalize P.toAffine = t at hxR hyR ⊢
  obtain ⟨x, y, f⟩ := t
  simp only at hxR hyR ⊢
  have ⟨xv, xe⟩ := hxR.toU256
  have ⟨_, ye⟩ := hyR.toU256
  have ⟨rv, re⟩ := Scalar.reduce_spec _ xv
  rw [xe] at re
  have ⟨rdv, rde⟩ := Scalar.mul_spec _ _ rv hd
  have ⟨av, ae⟩ := Scalar.add_spec _ _ he rdv
  have ⟨iv, ie⟩ := Scalar.inv_spec _ hk
  have ⟨sv, se⟩ := Scalar.mul_spec _ _ iv av
  refine ⟨rv, re, sv, ?_, ?_, ?_⟩
  · rw [se, ie, ae, rde]; rfl
  · have hlt := U256.lt_eq xv nMod_valid.m_valid
    rw [nMod_valid.m_eq, xe] at hlt
    have hy2 : (y.toU256.l0 &&& 1).toNat < 2 := by
      rw [U256.l0_and_one]; exact Nat.mod_lt _ (by decide)
    have hx2 : (U256.lt x.toU256 nMod.m ^^^ 1).toNat < 2 := by
      rw [hlt]; split <;> decide
    rw [or_shl_toNat hy2 hx2, U256.l0_and_one, ye, hlt]
    have hval : nMod.value = n := rfl
    rw [hval]
    split <;> split <;> first | rfl | omega
  · have hb : ∀ s : Scalar, s.Valid → s.isZero.toNat < 2 := fun s hs => by
      rw [Scalar.isZero_eq hs]; split <;> decide
    rw [ok_ne_zero (hb _ hk) (hb _ rv) (hb _ sv), Scalar.isZero_eq hk, Scalar.isZero_eq rv,
      Scalar.isZero_eq sv]
    simp only [ite_eq_right_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun h => absurd (h1 h) (by decide), fun h => absurd (h2 h) (by decide),
        fun h => absurd (h3 h) (by decide)⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun h => absurd h h1, fun h => absurd h h2, fun h => absurd h h3⟩

end CT

namespace ECDSA

/-- **What `signWithNonce` returns.** With `R = k • G = (x, y)` and
`s₀ = k⁻¹ · (e + r·d) mod n`: `r = x mod n`, `r`, `s₀` and `k` are non-zero,
and the signature is `(r, s₀)` or, after low-S normalisation, `(r, n - s₀)`,
with bit 0 of the recovery id flipped accordingly. -/
theorem signWithNonce_spec {sk : PrivateKey} {e : Nat} {k : CT.Scalar} {lowS : Bool}
    {rsig : RecoverableSignature} (hk : k.Valid) (h : signWithNonce sk e k lowS = some rsig) :
    ∃ x y, CT.smulGSpec k = .affine x y ∧
      rsig.sig.r = x.val % n ∧ 0 < rsig.sig.r ∧ rsig.sig.r < n ∧ 0 < k.toNat ∧
      ∃ s₀, s₀ = CT.sSpec sk.scalar.toNat k.toNat (e % n) rsig.sig.r ∧ 0 < s₀ ∧ s₀ < n ∧
      ∃ flip : Bool,
        rsig.sig.s = (if flip then n - s₀ else s₀) ∧
        rsig.recId.val = (y.val % 2 + (if n ≤ x.val then 2 else 0)) ^^^ (if flip then 1 else 0) ∧
        (lowS = true → rsig.sig.s ≤ n / 2) := by
  have ⟨ev, ee⟩ := CT.Scalar.ofNat_spec e
  have hc := CT.signCore_spec sk.scalar k (CT.Scalar.ofNat e) sk.valid hk ev
  unfold signWithNonce at h
  simp only [CT.declassify] at h
  generalize CT.signCore sk.scalar k (CT.Scalar.ofNat e) = c at hc h
  obtain ⟨rv, re, sv, se, ride, hok⟩ := hc
  rw [ee] at se
  by_cases hok0 : c.ok = 0
  · simp [hok0] at h
  obtain ⟨hk0, hr0, hs0⟩ := hok.1 hok0
  simp only [hok0, beq_iff_eq, ↓reduceIte] at h
  cases hR : CT.smulGSpec k with
  | infinity =>
    rw [hR] at re
    exact absurd (re.trans rfl) hr0
  | affine x y =>
    rw [hR] at re ride
    simp only [Point.affX, Point.affY] at re ride
    have hrec : c.recId.toNat < 4 := by
      rw [ride]; by_cases hx : n ≤ x.val <;> simp only [hx, ↓reduceIte] <;> omega
    refine ⟨x, y, rfl, ?_⟩
    split at h
    · rename_i hflip
      simp only [Option.some.injEq] at h
      subst h
      dsimp only
      have hx1 : c.recId.toNat ^^^ 1 < 4 := Nat.xor_lt_two_pow (n := 2) hrec (by decide)
      rw [Bool.and_eq_true] at hflip
      have hgt : c.s.toNat > n / 2 := of_decide_eq_true hflip.2
      refine ⟨re, by omega, rv.2, by omega, _, se, by omega, sv.2, true,
        (ite_eq_left_of_eq_true _ _ (eq_self true)).symm, ?_, ?_⟩
      · rw [Fin.val_ofNat, Nat.mod_eq_of_lt hx1, ride]; rfl
      · intro _; omega
    · rename_i hflip
      simp only [Option.some.injEq] at h
      subst h
      dsimp only
      have hle : lowS = true → c.s.toNat ≤ n / 2 := fun hl => by
        rw [Bool.and_eq_true] at hflip
        exact Nat.le_of_not_lt fun hgt => hflip ⟨hl, decide_eq_true hgt⟩
      refine ⟨re, by omega, rv.2, by omega, _, se, by omega, sv.2, false,
        (ite_eq_right_of_eq_false _ _ (eq_false Bool.false_ne_true)).symm, ?_, hle⟩
      rw [Fin.val_ofNat, Nat.mod_eq_of_lt hrec, ride]; exact (Nat.xor_zero _).symm

theorem _root_.Secp256k1.RFC6979.findNonce_some {α : Type} {accept : ByteArray → Option α} :
    ∀ {fuel : Nat} {st : RFC6979.State} {a : α},
      RFC6979.findNonce accept fuel st = some a → ∃ T, accept T = some a
  | 0, _, _, h => by simp [RFC6979.findNonce] at h
  | fuel + 1, st, a, h => by
    unfold RFC6979.findNonce at h
    revert h
    cases st.generate with
    | mk T st' =>
      intro h
      dsimp only at h
      split at h
      · rename_i a' heq; exact ⟨T, heq.trans h⟩
      · exact RFC6979.findNonce_some h

/-- Every signature returned by `signHashRecoverable` is `signWithNonce` with
`e = hashToScalar h` and some valid nonce (the accepted RFC 6979 candidate). -/
theorem PrivateKey.signHashRecoverable_spec {sk : PrivateKey} {h : ByteArray} {lowS : Bool}
    {extra : ByteArray} {verifyAfterSign : Bool} {rsig : RecoverableSignature}
    (hs : sk.signHashRecoverable h lowS extra verifyAfterSign = some rsig) :
    ∃ k : CT.Scalar, k.Valid ∧ signWithNonce sk (hashToScalar h) k lowS = some rsig := by
  have hfilter : ∀ {o : Option RecoverableSignature} {b : Bool} {f : RecoverableSignature → Bool},
      (if b = true then o.filter f else o) = some rsig → o = some rsig := by
    intro o b f hb
    cases b with
    | false => exact hb
    | true =>
      cases o with
      | none => simp at hb
      | some a =>
        simp only [↓reduceIte, Option.filter] at hb
        split at hb
        · exact hb
        · exact absurd hb (by simp)
  unfold PrivateKey.signHashRecoverable at hs
  have hf := hfilter hs
  obtain ⟨T, hT⟩ := RFC6979.findNonce_some hf
  cases hk : CT.Scalar.ofBytes? T with
  | none => simp [hk] at hT
  | some k =>
    simp only [hk, Option.bind_some] at hT
    exact ⟨k, CT.Scalar.ofBytes?_valid hk, hT⟩

/-- Every signature returned by `signHash` comes from `signWithNonce`. -/
theorem PrivateKey.signHash_spec {sk : PrivateKey} {h : ByteArray} {lowS : Bool}
    {extra : ByteArray} {verifyAfterSign : Bool} {sig : Signature}
    (hs : sk.signHash h lowS extra verifyAfterSign = some sig) :
    ∃ (k : CT.Scalar) (rsig : RecoverableSignature), k.Valid ∧
      signWithNonce sk (hashToScalar h) k lowS = some rsig ∧ rsig.sig = sig := by
  unfold PrivateKey.signHash at hs
  cases hr : sk.signHashRecoverable h lowS extra verifyAfterSign with
  | none => simp [hr] at hs
  | some rsig =>
    simp only [hr, Option.map_some, Option.some.injEq] at hs
    obtain ⟨k, hk, hw⟩ := PrivateKey.signHashRecoverable_spec hr
    exact ⟨k, rsig, hk, hw, hs⟩

end ECDSA

end Secp256k1
