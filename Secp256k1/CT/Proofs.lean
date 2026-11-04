import Secp256k1.CT.Lemmas
import Secp256k1.CT.Field

/-!
# Correctness of the constant-time arithmetic

Machine-checked proofs that the limb arithmetic of `Secp256k1.CT` computes
the intended values:

* `U256.add_toNat`, `U256.sub_toNat`, `U256.mulAddRow_toNat`: the carry and
  borrow chains are exact.
* `Modulus.montStep_spec`, `Modulus.mul_spec`: CIOS Montgomery multiplication
  returns the canonical `c < m` with `c · 2²⁵⁶ ≡ a · b (mod m)`, for any odd
  modulus satisfying `Modulus.Valid`.
* `Modulus.add_spec`, `Modulus.sub_spec`, `Modulus.toMont_spec`,
  `Modulus.fromMont_spec`: modular addition, subtraction and conversions.
* `pMod_valid`, `nMod_valid`: the constants for `p` and `n` satisfy those
  assumptions (checked by `decide`).
* `Modulus.pow_repr`: square-and-multiply exponentiation in Montgomery form.
* `Scalar.add_spec`, `Scalar.sub_spec`, `Scalar.mul_spec`, `Scalar.inv_spec`:
  arithmetic modulo `n`; `inv` computes `a^(n-2) mod n`.
* `Fe.add_spec`, `Fe.sub_spec`, `Fe.neg_spec`, `Fe.mul_spec`, `Fe.inv_spec`:
  field arithmetic modulo `p` on canonical values; `inv` computes `a^(p-2) mod p`.

These theorems depend only on the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). Not covered: that `a^(m-2)` is the inverse
(Fermat's little theorem, which needs `p` and `n` to be prime), and the point
formulas.
-/

namespace Secp256k1.CT

theorem low32 (t : UInt64) : (t &&& M32).toNat = t.toNat % 2 ^ 32 := by
  rw [UInt64.toNat_and]
  have : (M32 : UInt64).toNat = 2 ^ 32 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem shr_toNat (t : UInt64) (k : Nat) (hk : k < 64) :
    (t >>> k.toUInt64).toNat = t.toNat / 2 ^ k := by
  rw [UInt64.toNat_shiftRight]; simp [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hk]

theorem hi32 (t : UInt64) : (t >>> 32).toNat = t.toNat / 2 ^ 32 := shr_toNat t 32 (by decide)
theorem hi63 (t : UInt64) : (t >>> 63).toNat = t.toNat / 2 ^ 63 := shr_toNat t 63 (by decide)

/-- Carry step of `U256.add`. -/
theorem add_step (a b c : UInt64) (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32)
    (hc : c.toNat ≤ 1) :
    ((a + b + c) &&& M32).toNat + ((a + b + c) >>> 32).toNat * 2 ^ 32
      = a.toNat + b.toNat + c.toNat ∧ ((a + b + c) >>> 32).toNat ≤ 1 := by
  simp only [low32, hi32, UInt64.toNat_add]; omega

theorem add_step0 (a b : UInt64) (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    ((a + b) &&& M32).toNat + ((a + b) >>> 32).toNat * 2 ^ 32 = a.toNat + b.toNat ∧
    ((a + b) >>> 32).toNat ≤ 1 := by
  simp only [low32, hi32, UInt64.toNat_add]; omega

def U256.Valid (a : U256) : Prop :=
  a.l0.toNat < 2^32 ∧ a.l1.toNat < 2^32 ∧ a.l2.toNat < 2^32 ∧ a.l3.toNat < 2^32 ∧
  a.l4.toNat < 2^32 ∧ a.l5.toNat < 2^32 ∧ a.l6.toNat < 2^32 ∧ a.l7.toNat < 2^32

def U288.toNat (t : U288) : Nat := t.low.toNat + t.l8.toNat * 2 ^ 256

theorem U256.add_toNat (a b : U256) (ha : a.Valid) (hb : b.Valid) :
    (U256.add a b).toNat = a.toNat + b.toNat ∧ (U256.add a b).l8.toNat ≤ 1 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := b
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ := ha
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hb
  simp only [U256.add, U288.toNat, U288.low, U256.toNat]
  have ⟨e0, c0⟩ := add_step0 a0 b0 ha0 hb0
  generalize a0 + b0 = t0 at *
  have ⟨e1, c1⟩ := add_step a1 b1 (t0 >>> 32) ha1 hb1 c0
  generalize a1 + b1 + (t0 >>> 32) = t1 at *
  have ⟨e2, c2⟩ := add_step a2 b2 (t1 >>> 32) ha2 hb2 c1
  generalize a2 + b2 + (t1 >>> 32) = t2 at *
  have ⟨e3, c3⟩ := add_step a3 b3 (t2 >>> 32) ha3 hb3 c2
  generalize a3 + b3 + (t2 >>> 32) = t3 at *
  have ⟨e4, c4⟩ := add_step a4 b4 (t3 >>> 32) ha4 hb4 c3
  generalize a4 + b4 + (t3 >>> 32) = t4 at *
  have ⟨e5, c5⟩ := add_step a5 b5 (t4 >>> 32) ha5 hb5 c4
  generalize a5 + b5 + (t4 >>> 32) = t5 at *
  have ⟨e6, c6⟩ := add_step a6 b6 (t5 >>> 32) ha6 hb6 c5
  generalize a6 + b6 + (t5 >>> 32) = t6 at *
  have ⟨e7, c7⟩ := add_step a7 b7 (t6 >>> 32) ha7 hb7 c6
  generalize a7 + b7 + (t6 >>> 32) = t7 at *
  constructor
  · omega
  · exact c7

/-- Borrow step of `U256.sub`. -/
theorem sub_step (a b c : UInt64) (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32)
    (hc : c.toNat ≤ 1) :
    ((a - b - c) &&& M32).toNat + b.toNat + c.toNat
      = a.toNat + ((a - b - c) >>> 63).toNat * 2 ^ 32 ∧ ((a - b - c) >>> 63).toNat ≤ 1 := by
  simp only [low32, hi63, UInt64.toNat_sub]; omega

theorem sub_step0 (a b : UInt64) (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    ((a - b) &&& M32).toNat + b.toNat = a.toNat + ((a - b) >>> 63).toNat * 2 ^ 32 ∧
    ((a - b) >>> 63).toNat ≤ 1 := by
  simp only [low32, hi63, UInt64.toNat_sub]; omega

theorem U256.sub_toNat (a b : U256) (ha : a.Valid) (hb : b.Valid) :
    (U256.sub a b).low.toNat + b.toNat = a.toNat + (U256.sub a b).l8.toNat * 2 ^ 256 ∧
    (U256.sub a b).l8.toNat ≤ 1 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := b
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ := ha
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := hb
  simp only [U256.sub, U288.low, U256.toNat]
  have ⟨e0, c0⟩ := sub_step0 a0 b0 ha0 hb0
  generalize a0 - b0 = t0 at *
  have ⟨e1, c1⟩ := sub_step a1 b1 (t0 >>> 63) ha1 hb1 c0
  generalize a1 - b1 - (t0 >>> 63) = t1 at *
  have ⟨e2, c2⟩ := sub_step a2 b2 (t1 >>> 63) ha2 hb2 c1
  generalize a2 - b2 - (t1 >>> 63) = t2 at *
  have ⟨e3, c3⟩ := sub_step a3 b3 (t2 >>> 63) ha3 hb3 c2
  generalize a3 - b3 - (t2 >>> 63) = t3 at *
  have ⟨e4, c4⟩ := sub_step a4 b4 (t3 >>> 63) ha4 hb4 c3
  generalize a4 - b4 - (t3 >>> 63) = t4 at *
  have ⟨e5, c5⟩ := sub_step a5 b5 (t4 >>> 63) ha5 hb5 c4
  generalize a5 - b5 - (t4 >>> 63) = t5 at *
  have ⟨e6, c6⟩ := sub_step a6 b6 (t5 >>> 63) ha6 hb6 c5
  generalize a6 - b6 - (t5 >>> 63) = t6 at *
  have ⟨e7, c7⟩ := sub_step a7 b7 (t6 >>> 63) ha7 hb7 c6
  generalize a7 - b7 - (t6 >>> 63) = t7 at *
  exact ⟨by omega, c7⟩

/-- Multiply-accumulate step of `U256.mulAddRow`. -/
theorem mac_step (c x y d : UInt64) (hc : c.toNat < 2 ^ 32) (hx : x.toNat < 2 ^ 32)
    (hy : y.toNat < 2 ^ 32) (hd : d.toNat < 2 ^ 32) :
    ((c + x * y + d) &&& M32).toNat + ((c + x * y + d) >>> 32).toNat * 2 ^ 32
      = c.toNat + x.toNat * y.toNat + d.toNat ∧ ((c + x * y + d) >>> 32).toNat < 2 ^ 32 := by
  have hxy : x.toNat * y.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  simp only [low32, hi32, mac_toNat x y c d hx hy hc hd]
  generalize x.toNat * y.toNat = P at *
  omega

theorem mac_step0 (c x y : UInt64) (hc : c.toNat < 2 ^ 32) (hx : x.toNat < 2 ^ 32)
    (hy : y.toNat < 2 ^ 32) :
    ((c + x * y) &&& M32).toNat + ((c + x * y) >>> 32).toNat * 2 ^ 32
      = c.toNat + x.toNat * y.toNat ∧ ((c + x * y) >>> 32).toNat < 2 ^ 32 := by
  have hxy : x.toNat * y.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have : (c + x * y).toNat = c.toNat + x.toNat * y.toNat := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul]
    generalize x.toNat * y.toNat = P at *
    omega
  simp only [low32, hi32, this]
  generalize x.toNat * y.toNat = P at *
  omega

theorem U256.mulAddRow_toNat (acc : U256) (x : UInt64) (y : U256) (hacc : acc.Valid)
    (hx : x.toNat < 2 ^ 32) (hy : y.Valid) :
    (U256.mulAddRow acc x y).toNat = acc.toNat + x.toNat * y.toNat ∧
    (U256.mulAddRow acc x y).l8.toNat < 2 ^ 32 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := acc
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩ := y
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ := hacc
  obtain ⟨hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7⟩ := hy
  simp only [U256.mulAddRow, U288.toNat, U288.low, U256.toNat]
  have ⟨e0, c0⟩ := mac_step0 a0 x y0 ha0 hx hy0
  generalize a0 + x * y0 = t0 at *
  have ⟨e1, c1⟩ := mac_step a1 x y1 (t0 >>> 32) ha1 hx hy1 c0
  generalize a1 + x * y1 + (t0 >>> 32) = t1 at *
  have ⟨e2, c2⟩ := mac_step a2 x y2 (t1 >>> 32) ha2 hx hy2 c1
  generalize a2 + x * y2 + (t1 >>> 32) = t2 at *
  have ⟨e3, c3⟩ := mac_step a3 x y3 (t2 >>> 32) ha3 hx hy3 c2
  generalize a3 + x * y3 + (t2 >>> 32) = t3 at *
  have ⟨e4, c4⟩ := mac_step a4 x y4 (t3 >>> 32) ha4 hx hy4 c3
  generalize a4 + x * y4 + (t3 >>> 32) = t4 at *
  have ⟨e5, c5⟩ := mac_step a5 x y5 (t4 >>> 32) ha5 hx hy5 c4
  generalize a5 + x * y5 + (t4 >>> 32) = t5 at *
  have ⟨e6, c6⟩ := mac_step a6 x y6 (t5 >>> 32) ha6 hx hy6 c5
  generalize a6 + x * y6 + (t5 >>> 32) = t6 at *
  have ⟨e7, c7⟩ := mac_step a7 x y7 (t6 >>> 32) ha7 hx hy7 c6
  generalize a7 + x * y7 + (t6 >>> 32) = t7 at *
  refine ⟨?_, c7⟩
  simp only [Nat.mul_add, ← Nat.mul_assoc]
  generalize x.toNat * y0.toNat = P0 at *
  generalize x.toNat * y1.toNat = P1 at *
  generalize x.toNat * y2.toNat = P2 at *
  generalize x.toNat * y3.toNat = P3 at *
  generalize x.toNat * y4.toNat = P4 at *
  generalize x.toNat * y5.toNat = P5 at *
  generalize x.toNat * y6.toNat = P6 at *
  generalize x.toNat * y7.toNat = P7 at *
  omega

/-- The key congruence behind Montgomery reduction: with `m₀·I ≡ -1 (mod W)`
and `u = A·I mod W`, the sum `A + u·m₀` is divisible by `W`. -/
theorem mont_div (A I m0 W : Nat) (hW : 0 < W) (hI : m0 * I % W = W - 1) :
    (A + (A * I % W) * m0) % W = 0 := by
  have h1 : (A * I % W) * m0 % W = (A * (m0 * I)) % W := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc, Nat.mul_comm I m0]
  have h2 : (A * (m0 * I)) % W = (A * (W - 1)) % W := by
    rw [Nat.mul_mod, hI, Nat.mod_mul_mod]
  rw [Nat.add_mod, h1, h2, ← Nat.add_mod]
  have : A + A * (W - 1) = A * W := by
    cases W with
    | zero => omega
    | succ w => simp [Nat.mul_succ, Nat.add_comm]
  rw [this, Nat.mul_mod_left]


theorem and_M32_lt (t : UInt64) : (t &&& M32).toNat < 2 ^ 32 := by
  rw [low32]; exact Nat.mod_lt _ (by decide)

theorem U256.toNat_lt (a : U256) (ha : a.Valid) : a.toNat < 2 ^ 256 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ha
  unfold U256.toNat; omega

theorem mulAddRow_low_valid (acc : U256) (x : UInt64) (y : U256) :
    (U256.mulAddRow acc x y).low.Valid := by
  simp only [U256.mulAddRow, U288.low, U256.Valid, and_M32_lt, and_self]

/-- What the correctness proofs assume about a `Modulus`. -/
structure Modulus.Valid (M : Modulus) : Prop where
  m_valid : M.m.Valid
  m_eq : M.m.toNat = M.value
  mInv_lt : M.mInv.toNat < 2 ^ 32
  mInv_spec : M.m.l0.toNat * M.mInv.toNat % 2 ^ 32 = 2 ^ 32 - 1
  value_pos : 0 < M.value
  one_lt : 1 < M.value
  coprime : Nat.Coprime M.value (2 ^ 256)
  r2_valid : M.r2.Valid
  r2_eq : M.r2.toNat = 2 ^ 256 * 2 ^ 256 % M.value
  one_valid : M.one.Valid
  one_eq : M.one.toNat = 2 ^ 256 % M.value

theorem Modulus.montStep_spec (M : Modulus) (hM : M.Valid) (b : U256) (hb : b.Valid)
    (hbm : b.toNat < M.value) (t : U288) (ht : t.low.Valid) (ht8 : t.l8.toNat ≤ 1)
    (htm : t.toNat < 2 * M.value) (ai : UInt64) (hai : ai.toNat < 2 ^ 32) :
    (M.montStep b t ai).low.Valid ∧ (M.montStep b t ai).l8.toNat ≤ 1 ∧
    (M.montStep b t ai).toNat < 2 * M.value ∧
    ∃ u, u < 2 ^ 32 ∧
      (M.montStep b t ai).toNat * 2 ^ 32 = t.toNat + ai.toNat * b.toNat + u * M.value := by
  obtain ⟨hmv, hmeq, hIlt, hI, _, _, _, _, _, _, _⟩ := hM
  have hm0 := hmv.1
  simp only [Modulus.montStep]
  -- s = t.low + aᵢ·b
  have ⟨hs, hs8⟩ := U256.mulAddRow_toNat t.low ai b ht hai hb
  have hsv := mulAddRow_low_valid t.low ai b
  generalize U256.mulAddRow t.low ai b = s at *
  have hs0 : s.l0.toNat < 2 ^ 32 := hsv.1
  -- u = s₀·I mod 2³²
  have hu : ((s.l0 * M.mInv) &&& M32).toNat = s.l0.toNat * M.mInv.toNat % 2 ^ 32 := by
    rw [low32, UInt64.toNat_mul]
    generalize s.l0.toNat * M.mInv.toNat = X
    omega
  have hult := and_M32_lt (s.l0 * M.mInv)
  generalize (s.l0 * M.mInv) &&& M32 = u at *
  -- r = s.low + u·m, with r₀ = 0
  have ⟨hr, hr8⟩ := U256.mulAddRow_toNat s.low u M.m hsv hult hmv
  have hrv := mulAddRow_low_valid s.low u M.m
  have hr0 : (U256.mulAddRow s.low u M.m).l0.toNat = 0 := by
    show ((s.l0 + u * M.m.l0) &&& M32).toNat = 0
    have h0 := hmv.1
    rw [low32]
    have : (s.l0 + u * M.m.l0).toNat = s.l0.toNat + u.toNat * M.m.l0.toNat := by
      have hP : u.toNat * M.m.l0.toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      simp only [UInt64.toNat_add, UInt64.toNat_mul]
      generalize u.toNat * M.m.l0.toNat = P at *
      omega
    rw [this, hu]
    exact mont_div _ _ _ _ (by decide) hI
  generalize U256.mulAddRow s.low u M.m = r at *
  have hr0' := hrv.1
  -- bounds on the products
  have hab : ai.toNat * b.toNat ≤ (2 ^ 32 - 1) * M.value :=
    Nat.mul_le_mul (by omega) (by omega)
  have hum : u.toNat * M.value ≤ (2 ^ 32 - 1) * M.value :=
    Nat.mul_le_mul (by omega) (Nat.le_refl _)
  rw [hmeq] at hr
  have hmlt : M.value < 2 ^ 256 := hmeq ▸ U256.toNat_lt _ hmv
  obtain ⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7⟩ := hrv.2
  have htop : (r.l8 + (s.l8 + t.l8)).toNat = r.l8.toNat + s.l8.toNat + t.l8.toNat := by
    simp only [UInt64.toNat_add]; omega
  refine ⟨⟨hr1, hr2, hr3, hr4, hr5, hr6, hr7, and_M32_lt _⟩, ?_, ?_, u.toNat, hult, ?_⟩
  all_goals
    generalize ai.toNat * b.toNat = P at *
    generalize u.toNat * M.value = Q at *
    simp only [U288.toNat, U288.low, U256.toNat] at hs hr htm ⊢
    simp only [low32, hi32, htop]
    omega

theorem sub_low_valid (a b : U256) : (U256.sub a b).low.Valid := by
  simp only [U256.sub, U288.low, U256.Valid, and_M32_lt, and_self]

theorem U256.select_one (a b : U256) : U256.select (maskOf 1) a b = a := by
  cases a; simp [U256.select, selectWord_maskOf_one]

theorem U256.select_zero (a b : U256) : U256.select (maskOf 0) a b = b := by
  cases b; simp [U256.select, selectWord_maskOf_zero]

theorem UInt64.eq_zero_or_one {x : UInt64} (h : x.toNat ≤ 1) : x = 0 ∨ x = 1 := by
  rcases (by omega : x.toNat = 0 ∨ x.toNat = 1) with h0 | h1
  · exact Or.inl (UInt64.toNat_inj.mp (by rw [h0]; rfl))
  · exact Or.inr (UInt64.toNat_inj.mp (by rw [h1]; rfl))

/-- The selection bit of `condSub`, for bits `x` and `y`. -/
theorem condSub_bit (x y : UInt64) (hx : x.toNat ≤ 1) (hy : y.toNat ≤ 1) :
    (x ||| (y ^^^ 1) = 1 ∧ (x = 1 ∨ y = 0)) ∨ (x ||| (y ^^^ 1) = 0 ∧ x = 0 ∧ y = 1) := by
  rcases UInt64.eq_zero_or_one hx with rfl | rfl <;>
    rcases UInt64.eq_zero_or_one hy with rfl | rfl <;> decide

theorem Modulus.condSub_spec (M : Modulus) (hM : M.Valid) (t : U288) (ht : t.low.Valid)
    (ht8 : t.l8.toNat ≤ 1) (htm : t.toNat < 2 * M.value) :
    (M.condSub t).Valid ∧
    (M.condSub t).toNat = if t.toNat < M.value then t.toNat else t.toNat - M.value := by
  have hmlt : M.value < 2 ^ 256 := hM.m_eq ▸ U256.toNat_lt _ hM.m_valid
  have ⟨hd, hd8⟩ := U256.sub_toNat t.low M.m ht hM.m_valid
  have hdv := sub_low_valid t.low M.m
  have htl := U256.toNat_lt _ ht
  have hdl := U256.toNat_lt _ hdv
  rw [hM.m_eq] at hd
  unfold Modulus.condSub
  generalize U256.sub t.low M.m = d at *
  simp only [U288.toNat] at htm ⊢
  rcases condSub_bit t.l8 d.l8 ht8 hd8 with
    ⟨h1, hc⟩ | ⟨h0, hx0, hy1⟩
  · rw [h1, U256.select_one]
    refine ⟨hdv, ?_⟩
    rcases hc with hc | hc
    · have : t.l8.toNat = 1 := by rw [hc]; rfl
      by_cases hlt : t.low.toNat + t.l8.toNat * 2 ^ 256 < M.value <;>
        simp only [hlt, ↓reduceIte] <;> omega
    · have : d.l8.toNat = 0 := by rw [hc]; rfl
      by_cases hlt : t.low.toNat + t.l8.toNat * 2 ^ 256 < M.value <;>
        simp only [hlt, ↓reduceIte] <;> omega
  · rw [h0, U256.select_zero]
    refine ⟨ht, ?_⟩
    have : t.l8.toNat = 0 := by rw [hx0]; rfl
    have : d.l8.toNat = 1 := by rw [hy1]; rfl
    by_cases hlt : t.low.toNat + t.l8.toNat * 2 ^ 256 < M.value <;>
      simp only [hlt, ↓reduceIte] <;> omega

theorem zero288_low_valid : (⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ : U288).low.Valid := by
  simp [U288.low, U256.Valid]

/-- Unrolling the eight CIOS steps `Tᵢ₊₁ · 2³² = Tᵢ + Pᵢ + Qᵢ` (with `T₀ = 0`). -/
theorem cios_chain (T1 T2 T3 T4 T5 T6 T7 T8 P0 P1 P2 P3 P4 P5 P6 P7
    Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 : Nat)
    (e1 : T1 * 2 ^ 32 = P0 + Q1) (e2 : T2 * 2 ^ 32 = T1 + P1 + Q2)
    (e3 : T3 * 2 ^ 32 = T2 + P2 + Q3) (e4 : T4 * 2 ^ 32 = T3 + P3 + Q4)
    (e5 : T5 * 2 ^ 32 = T4 + P4 + Q5) (e6 : T6 * 2 ^ 32 = T5 + P5 + Q6)
    (e7 : T7 * 2 ^ 32 = T6 + P6 + Q7) (e8 : T8 * 2 ^ 32 = T7 + P7 + Q8) :
    T8 * 2 ^ 256 = (P0 + Q1) + (P1 + Q2) * 2 ^ 32 + (P2 + Q3) * 2 ^ 64 + (P3 + Q4) * 2 ^ 96 +
      (P4 + Q5) * 2 ^ 128 + (P5 + Q6) * 2 ^ 160 + (P6 + Q7) * 2 ^ 192 + (P7 + Q8) * 2 ^ 224 := by
  grind

/-- The final reduction step: if `c` is `t` or `t - m`, then `c · R` and `t · R`
agree modulo `m`. -/
theorem condSub_mod (t c m R x : Nat) (hc : c = if t < m then t else t - m)
    (hx : t * R = x) : c * R % m = x % m := by
  by_cases h : t < m
  · simp only [h, ↓reduceIte] at hc; rw [hc, hx]
  · simp only [h, ↓reduceIte] at hc
    have hle : m * R ≤ t * R := Nat.mul_le_mul_right R (by omega)
    have : c * R + R * m = x := by
      rw [hc, Nat.sub_mul, Nat.mul_comm R m, Nat.sub_add_cancel hle, hx]
    rw [← this, Nat.add_mul_mod_self_right]

/-- **Montgomery multiplication is correct**: for a valid modulus `m`, any
`a < 2²⁵⁶` and `b < m`, `Modulus.mul` returns the canonical `c < m` with
`c · 2²⁵⁶ ≡ a · b (mod m)`. -/
theorem Modulus.mul_spec (M : Modulus) (hM : M.Valid) (a b : U256) (ha : a.Valid) (hb : b.Valid)
    (hbm : b.toNat < M.value) :
    (M.mul a b).Valid ∧ (M.mul a b).toNat < M.value ∧
    (M.mul a b).toNat * 2 ^ 256 % M.value = a.toNat * b.toNat % M.value := by
  have hpos := hM.value_pos
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ := ha
  simp only [Modulus.mul]
  have ⟨v1, l1, b1, u1, _, e1⟩ := montStep_spec M hM b hb hbm _ zero288_low_valid (by decide)
    (by simp [U288.toNat, U288.low, U256.toNat]; omega) a.l0 ha0
  generalize M.montStep b ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩ a.l0 = t1 at *
  have ⟨v2, l2, b2, u2, _, e2⟩ := montStep_spec M hM b hb hbm t1 v1 l1 b1 a.l1 ha1
  generalize M.montStep b t1 a.l1 = t2 at *
  have ⟨v3, l3, b3, u3, _, e3⟩ := montStep_spec M hM b hb hbm t2 v2 l2 b2 a.l2 ha2
  generalize M.montStep b t2 a.l2 = t3 at *
  have ⟨v4, l4, b4, u4, _, e4⟩ := montStep_spec M hM b hb hbm t3 v3 l3 b3 a.l3 ha3
  generalize M.montStep b t3 a.l3 = t4 at *
  have ⟨v5, l5, b5, u5, _, e5⟩ := montStep_spec M hM b hb hbm t4 v4 l4 b4 a.l4 ha4
  generalize M.montStep b t4 a.l4 = t5 at *
  have ⟨v6, l6, b6, u6, _, e6⟩ := montStep_spec M hM b hb hbm t5 v5 l5 b5 a.l5 ha5
  generalize M.montStep b t5 a.l5 = t6 at *
  have ⟨v7, l7, b7, u7, _, e7⟩ := montStep_spec M hM b hb hbm t6 v6 l6 b6 a.l6 ha6
  generalize M.montStep b t6 a.l6 = t7 at *
  have ⟨v8, l8, b8, u8, _, e8⟩ := montStep_spec M hM b hb hbm t7 v7 l7 b7 a.l7 ha7
  generalize M.montStep b t7 a.l7 = t8 at *
  have ⟨cv, ceq⟩ := condSub_spec M hM t8 v8 l8 b8
  generalize M.condSub t8 = c at *
  simp only [U288.toNat, U288.low, U256.toNat, Nat.zero_add, UInt64.toNat_zero,
    Nat.zero_mul, Nat.add_zero] at e1
  -- t₈ · 2²⁵⁶ = a · b + U · m
  have lin := cios_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e1 e2 e3 e4 e5 e6 e7 e8
  have key : t8.toNat * 2 ^ 256 = a.toNat * b.toNat +
      (u1 + u2 * 2 ^ 32 + u3 * 2 ^ 64 + u4 * 2 ^ 96 + u5 * 2 ^ 128 + u6 * 2 ^ 160 +
        u7 * 2 ^ 192 + u8 * 2 ^ 224) * M.value := by
    rw [lin]; unfold U256.toNat; grind
  refine ⟨cv, ?_, ?_⟩
  · rw [ceq]
    by_cases hlt : t8.toNat < M.value
    · simp only [hlt, ↓reduceIte]
    · simp only [hlt, ↓reduceIte]; omega
  · rw [condSub_mod _ _ _ _ _ ceq key, Nat.add_mul_mod_self_right]

theorem add_low_valid (a b : U256) : (U256.add a b).low.Valid := by
  simp only [U256.add, U288.low, U256.Valid, and_M32_lt, and_self]

theorem condSub_eq_mod {t m : Nat} (h : t < 2 * m) :
    (if t < m then t else t - m) = t % m := by
  by_cases ht : t < m
  · simp only [ht, ↓reduceIte, Nat.mod_eq_of_lt ht]
  · simp only [ht, ↓reduceIte]
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Modular addition is correct. -/
theorem Modulus.add_spec (M : Modulus) (hM : M.Valid) (a b : U256) (ha : a.Valid)
    (hb : b.Valid) (ham : a.toNat < M.value) (hbm : b.toNat < M.value) :
    (M.add a b).Valid ∧ (M.add a b).toNat = (a.toNat + b.toNat) % M.value := by
  have ⟨hs, hs8⟩ := U256.add_toNat a b ha hb
  have ⟨cv, ceq⟩ := condSub_spec M hM (U256.add a b) (add_low_valid a b) hs8 (by omega)
  refine ⟨cv, ?_⟩
  unfold Modulus.add; rw [ceq, hs]; exact condSub_eq_mod (by omega)

/-- Modular subtraction is correct. -/
theorem Modulus.sub_spec (M : Modulus) (hM : M.Valid) (a b : U256) (ha : a.Valid)
    (hb : b.Valid) (ham : a.toNat < M.value) (hbm : b.toNat < M.value) :
    (M.sub a b).Valid ∧ (M.sub a b).toNat = (a.toNat + M.value - b.toNat) % M.value := by
  have hmlt : M.value < 2 ^ 256 := hM.m_eq ▸ U256.toNat_lt _ hM.m_valid
  have ⟨hd, hd8⟩ := U256.sub_toNat a b ha hb
  have hdv := sub_low_valid a b
  have hdl := U256.toNat_lt _ hdv
  simp only [Modulus.sub]
  generalize U256.sub a b = d at *
  rcases (by omega : d.l8.toNat = 0 ∨ d.l8.toNat = 1) with e | e
  · have h0 : d.l8 = 0 := UInt64.toNat_inj.mp (by rw [e]; rfl)
    rw [h0, U256.select_zero]
    have ⟨hs, hs8⟩ := U256.add_toNat d.low U256.zero hdv (by simp [U256.zero, U256.Valid])
    have hz : U256.zero.toNat = 0 := rfl
    have hlow := U256.toNat_lt _ (add_low_valid d.low U256.zero)
    refine ⟨add_low_valid _ _, ?_⟩
    simp only [U288.toNat] at hs
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · have h1 : d.l8 = 1 := UInt64.toNat_inj.mp (by rw [e]; rfl)
    rw [h1, U256.select_one]
    have ⟨hs, hs8⟩ := U256.add_toNat d.low M.m hdv hM.m_valid
    have hlow := U256.toNat_lt _ (add_low_valid d.low M.m)
    refine ⟨add_low_valid _ _, ?_⟩
    simp only [U288.toNat] at hs
    rw [hM.m_eq] at hs
    rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- Cancel a factor coprime to the modulus. -/
theorem mod_cancel {k m x y : Nat} (hk : Nat.Coprime m k) (hx : x < m) (hy : y < m)
    (h : k * x % m = k * y % m) : x = y := by
  have key : ∀ x y, x < m → y < m → k * x % m = k * y % m → y ≤ x → x = y := by
    intro x y hx hy h hle
    have h1 := Nat.sub_mod_eq_zero_of_mod_eq h
    rw [← Nat.mul_sub] at h1
    have h2 := hk.dvd_of_dvd_mul_left (Nat.dvd_of_mod_eq_zero h1)
    have := Nat.eq_zero_of_dvd_of_lt h2 (by omega)
    omega
  rcases Nat.le_total y x with hle | hle
  · exact key x y hx hy h hle
  · exact (key y x hy hx h.symm hle).symm

theorem U256.one_valid : U256.one.Valid := by simp [U256.one, U256.Valid]

theorem U256.one_toNat : U256.one.toNat = 1 := rfl

/-- `fromMont` divides by `R` modulo `m`. -/
theorem Modulus.fromMont_spec (M : Modulus) (hM : M.Valid) (a : U256) (ha : a.Valid) :
    (M.fromMont a).Valid ∧ (M.fromMont a).toNat < M.value ∧
    (M.fromMont a).toNat * 2 ^ 256 % M.value = a.toNat % M.value := by
  have := mul_spec M hM a U256.one ha U256.one_valid (by rw [U256.one_toNat]; exact hM.one_lt)
  rw [U256.one_toNat, Nat.mul_one] at this
  exact this

/-- `toMont` multiplies by `R` modulo `m` (and reduces any 256-bit input). -/
theorem Modulus.toMont_spec (M : Modulus) (hM : M.Valid) (a : U256) (ha : a.Valid) :
    (M.toMont a).Valid ∧ (M.toMont a).toNat = a.toNat * 2 ^ 256 % M.value := by
  have hr := hM.r2_eq
  have ⟨cv, clt, ceq⟩ := mul_spec M hM a M.r2 ha hM.r2_valid (by rw [hr]; exact Nat.mod_lt _ hM.value_pos)
  refine ⟨cv, ?_⟩
  apply mod_cancel (k := 2 ^ 256) hM.coprime clt (Nat.mod_lt _ hM.value_pos)
  rw [Nat.mul_comm, ceq, hr, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
    Nat.mul_mod (2 ^ 256), Nat.mod_mod, ← Nat.mul_mod]
  congr 1; grind

set_option exponentiation.threshold 600 in
theorem pMod_valid : pMod.Valid where
  m_valid := by unfold U256.Valid; decide
  m_eq := by decide
  mInv_lt := by decide
  mInv_spec := by decide
  value_pos := by decide
  one_lt := by decide
  coprime := by unfold Nat.Coprime; decide
  r2_valid := by unfold U256.Valid; decide
  r2_eq := by decide
  one_valid := by unfold U256.Valid; decide
  one_eq := by decide

set_option exponentiation.threshold 600 in
theorem nMod_valid : nMod.Valid where
  m_valid := by unfold U256.Valid; decide
  m_eq := by decide
  mInv_lt := by decide
  mInv_spec := by decide
  value_pos := by decide
  one_lt := by decide
  coprime := by unfold Nat.Coprime; decide
  r2_valid := by unfold U256.Valid; decide
  r2_eq := by decide
  one_valid := by unfold U256.Valid; decide
  one_eq := by decide

/-! ### Scalars (plain form modulo `n`) -/

/-- The representation invariant of `Scalar`: valid limbs and `val < n`. -/
def Scalar.Valid (a : Scalar) : Prop := a.val.Valid ∧ a.val.toNat < n

theorem Scalar.add_spec (a b : Scalar) (ha : a.Valid) (hb : b.Valid) :
    (a + b).Valid ∧ (a + b).toNat = (a.toNat + b.toNat) % n := by
  have ⟨v, e⟩ := Modulus.add_spec nMod nMod_valid a.val b.val ha.1 hb.1 ha.2 hb.2
  have hlt : (a + b).toNat < n := by
    show (nMod.add a.val b.val).toNat < n
    rw [e]; exact Nat.mod_lt _ (by decide)
  exact ⟨⟨v, hlt⟩, e⟩

theorem Scalar.sub_spec (a b : Scalar) (ha : a.Valid) (hb : b.Valid) :
    (a - b).Valid ∧ (a - b).toNat = (a.toNat + n - b.toNat) % n := by
  have ⟨v, e⟩ := Modulus.sub_spec nMod nMod_valid a.val b.val ha.1 hb.1 ha.2 hb.2
  have hlt : (a - b).toNat < n := by
    show (nMod.sub a.val b.val).toNat < n
    rw [e]; exact Nat.mod_lt _ (by decide)
  exact ⟨⟨v, hlt⟩, e⟩

/-- **Scalar multiplication modulo `n` is correct.** -/
theorem Scalar.mul_spec (a b : Scalar) (ha : a.Valid) (hb : b.Valid) :
    (a * b).Valid ∧ (a * b).toNat = a.toNat * b.toNat % n := by
  show Scalar.Valid ⟨nMod.mul (nMod.mul a.val b.val) nMod.r2⟩ ∧
    (nMod.mul (nMod.mul a.val b.val) nMod.r2).toNat = a.val.toNat * b.val.toNat % n
  have hM := nMod_valid
  have ⟨v1, lt1, e1⟩ := Modulus.mul_spec nMod hM a.val b.val ha.1 hb.1 hb.2
  generalize nMod.mul a.val b.val = c1 at *
  have hr2 : nMod.r2.toNat < nMod.value := by rw [hM.r2_eq]; exact Nat.mod_lt _ hM.value_pos
  have ⟨v2, lt2, e2⟩ := Modulus.mul_spec nMod hM c1 nMod.r2 v1 hM.r2_valid hr2
  have hval : nMod.value = n := rfl
  generalize nMod.mul c1 nMod.r2 = c2 at *
  rw [hval] at lt1 lt2 e1 e2
  rw [hM.r2_eq, hval] at e2
  refine ⟨⟨v2, lt2⟩, ?_⟩
  apply mod_cancel (k := 2 ^ 256) (by rw [← hval]; exact hM.coprime) lt2
    (Nat.mod_lt _ (by decide))
  -- R·c₂ ≡ c₁·R² ≡ (a·b)·R
  rw [Nat.mul_comm, e2, Nat.mul_mod_mod, ← Nat.mul_assoc, Nat.mul_mod, e1, ← Nat.mul_mod,
    Nat.mul_comm (2 ^ 256), Nat.mod_mul_mod]

/-! ### Field elements (Montgomery form modulo `p`) -/

/-- The representation invariant of `Fe`: valid limbs and `mont < p`. -/
def Fe.Valid (a : Fe) : Prop := a.mont.Valid ∧ a.mont.toNat < p

/-- **Field multiplication is correct**: on canonical values (`Fe.toNat`),
`Fe.mul` is multiplication modulo `p`. -/
theorem Fe.mul_spec (a b : Fe) (ha : a.Valid) (hb : b.Valid) :
    (a * b).Valid ∧ (a * b).toNat = a.toNat * b.toNat % p := by
  show Fe.Valid ⟨pMod.mul a.mont b.mont⟩ ∧ (pMod.fromMont (pMod.mul a.mont b.mont)).toNat =
    (pMod.fromMont a.mont).toNat * (pMod.fromMont b.mont).toNat % p
  have hM := pMod_valid
  have hval : pMod.value = p := rfl
  have ⟨vC, ltC, eC⟩ := Modulus.mul_spec pMod hM a.mont b.mont ha.1 hb.1 hb.2
  generalize pMod.mul a.mont b.mont = C at *
  have ⟨_, lta, ea⟩ := Modulus.fromMont_spec pMod hM a.mont ha.1
  have ⟨_, ltb, eb⟩ := Modulus.fromMont_spec pMod hM b.mont hb.1
  have ⟨_, ltc, ec⟩ := Modulus.fromMont_spec pMod hM C vC
  generalize (pMod.fromMont a.mont).toNat = a' at *
  generalize (pMod.fromMont b.mont).toNat = b' at *
  generalize (pMod.fromMont C).toNat = c' at *
  simp only [hval] at *
  refine ⟨⟨vC, ltC⟩, ?_⟩
  have hcop : Nat.Coprime p (2 ^ 256 * 2 ^ 256) :=
    Nat.Coprime.mul_right hM.coprime hM.coprime
  apply mod_cancel hcop ltc (Nat.mod_lt _ (by decide))
  rw [Nat.mod_eq_of_lt ha.2] at ea
  rw [Nat.mod_eq_of_lt hb.2] at eb
  rw [Nat.mod_eq_of_lt ltC] at ec
  calc 2 ^ 256 * 2 ^ 256 * c' % p = 2 ^ 256 * (c' * 2 ^ 256 % p) % p := by
        rw [Nat.mul_mod_mod]; congr 1; grind
    _ = C.toNat * 2 ^ 256 % p := by rw [ec, Nat.mul_comm]
    _ = a.mont.toNat * b.mont.toNat % p := eC
    _ = (a' * 2 ^ 256 % p) * (b' * 2 ^ 256 % p) % p := by rw [ea, eb]
    _ = 2 ^ 256 * 2 ^ 256 * (a' * b' % p) % p := by
        rw [← Nat.mul_mod, Nat.mul_mod_mod, Nat.mul_mul_mul_comm, Nat.mul_comm (a' * b')]

/-- **Field addition is correct** on canonical values. -/
theorem Fe.add_spec (a b : Fe) (ha : a.Valid) (hb : b.Valid) :
    (a + b).Valid ∧ (a + b).toNat = (a.toNat + b.toNat) % p := by
  show Fe.Valid ⟨pMod.add a.mont b.mont⟩ ∧ (pMod.fromMont (pMod.add a.mont b.mont)).toNat =
    ((pMod.fromMont a.mont).toNat + (pMod.fromMont b.mont).toNat) % p
  have hM := pMod_valid
  have hval : pMod.value = p := rfl
  have ⟨vC, eC⟩ := Modulus.add_spec pMod hM a.mont b.mont ha.1 hb.1 ha.2 hb.2
  have ltC : (pMod.add a.mont b.mont).toNat < p := by rw [eC]; exact Nat.mod_lt _ (by decide)
  generalize pMod.add a.mont b.mont = C at *
  have ⟨_, lta, ea⟩ := Modulus.fromMont_spec pMod hM a.mont ha.1
  have ⟨_, ltb, eb⟩ := Modulus.fromMont_spec pMod hM b.mont hb.1
  have ⟨_, ltc, ec⟩ := Modulus.fromMont_spec pMod hM C vC
  generalize (pMod.fromMont a.mont).toNat = a' at *
  generalize (pMod.fromMont b.mont).toNat = b' at *
  generalize (pMod.fromMont C).toNat = c' at *
  simp only [hval] at *
  refine ⟨⟨vC, ltC⟩, ?_⟩
  apply mod_cancel hM.coprime ltc (Nat.mod_lt _ (by decide))
  rw [Nat.mod_eq_of_lt ha.2] at ea
  rw [Nat.mod_eq_of_lt hb.2] at eb
  rw [Nat.mod_eq_of_lt ltC] at ec
  calc 2 ^ 256 * c' % p = C.toNat := by rw [Nat.mul_comm, ec]
    _ = (a.mont.toNat + b.mont.toNat) % p := eC
    _ = (a' * 2 ^ 256 % p + b' * 2 ^ 256 % p) % p := by rw [ea, eb]
    _ = 2 ^ 256 * ((a' + b') % p) % p := by
        rw [← Nat.add_mod, Nat.mul_mod_mod]; congr 1; grind

/-! ### Values in Montgomery form, exponentiation and inversion -/

/-- `x` is the canonical Montgomery form of `v` modulo `m`: `x = v · 2²⁵⁶ mod m`. -/
def Modulus.Repr (M : Modulus) (x : U256) (v : Nat) : Prop :=
  x.Valid ∧ x.toNat = v * 2 ^ 256 % M.value

theorem Modulus.Repr.lt {M : Modulus} (hM : M.Valid) {x : U256} {v : Nat} (h : M.Repr x v) :
    x.toNat < M.value := by
  rw [h.2]; exact Nat.mod_lt _ hM.value_pos

/-- Montgomery multiplication multiplies the represented values. -/
theorem Modulus.mul_repr (M : Modulus) (hM : M.Valid) {x y : U256} {v w : Nat}
    (hx : M.Repr x v) (hy : M.Repr y w) : M.Repr (M.mul x y) (v * w) := by
  have ⟨cv, clt, ceq⟩ := mul_spec M hM x y hx.1 hy.1 (hy.lt hM)
  refine ⟨cv, ?_⟩
  apply mod_cancel (k := 2 ^ 256) hM.coprime clt (Nat.mod_lt _ hM.value_pos)
  rw [Nat.mul_comm (2 ^ 256) (M.mul x y).toNat, ceq, hx.2, hy.2, ← Nat.mul_mod,
    Nat.mul_mod_mod]
  congr 1
  rw [Nat.mul_comm v w, Nat.mul_assoc, Nat.mul_comm (2 ^ 256) (w * 2 ^ 256), Nat.mul_assoc]
  ac_rfl

theorem Modulus.one_repr (M : Modulus) (hM : M.Valid) : M.Repr M.one 1 := by
  refine ⟨hM.one_valid, ?_⟩; rw [hM.one_eq, Nat.one_mul]

theorem pow_step_one (v α e i : Nat) (hb : e / 2 ^ i % 2 = 1) :
    (v * v * α) ^ 2 ^ i * α ^ (e % 2 ^ i) = v ^ 2 ^ (i + 1) * α ^ (e % 2 ^ (i + 1)) := by
  rw [Nat.mod_pow_succ, hb, Nat.mul_one, Nat.pow_succ 2 i, Nat.pow_mul, Nat.pow_two,
    Nat.pow_add, Nat.mul_pow, Nat.mul_pow]
  ac_rfl

theorem pow_step_zero (v α e i : Nat) (hb : e / 2 ^ i % 2 = 0) :
    (v * v) ^ 2 ^ i * α ^ (e % 2 ^ i) = v ^ 2 ^ (i + 1) * α ^ (e % 2 ^ (i + 1)) := by
  rw [Nat.mod_pow_succ, hb, Nat.mul_zero, Nat.pow_succ 2 i, Nat.pow_mul,
    Nat.pow_two, Nat.mul_pow, Nat.add_zero]

/-- The square-and-multiply loop: after processing the low `i` bits of `e`
starting from a representative of `v`, the result represents
`v^(2^i) · α^(e mod 2^i)`. -/
theorem Modulus.pow_go_repr (M : Modulus) (hM : M.Valid) {a : U256} {α : Nat}
    (ha : M.Repr a α) (e : Nat) :
    ∀ (i : Nat) (acc : U256) (v : Nat), M.Repr acc v →
      M.Repr (Modulus.pow.go M a e i acc) (v ^ (2 ^ i) * α ^ (e % 2 ^ i))
  | 0, acc, v, h => by
    simp only [Modulus.pow.go, Nat.pow_zero, Nat.pow_one, Nat.mod_one, Nat.mul_one]; exact h
  | i + 1, acc, v, h => by
    simp only [Modulus.pow.go]
    have hsq := M.mul_repr hM h h
    by_cases hb : e.testBit i = true
    · simp only [hb, ↓reduceIte]
      have := Modulus.pow_go_repr M hM ha e i _ _ (M.mul_repr hM hsq ha)
      rw [pow_step_one v α e i (by simpa [Nat.testBit_eq_decide_div_mod_eq] using hb)] at this
      exact this
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      have := Modulus.pow_go_repr M hM ha e i _ _ hsq
      have hb' : e / 2 ^ i % 2 = 0 := by
        simp [Nat.testBit_eq_decide_div_mod_eq] at hb; omega
      rw [pow_step_zero v α e i hb'] at this
      exact this

/-- **Exponentiation is correct**: `Modulus.pow` maps a representative of `α`
to a representative of `α ^ e`. -/
theorem Modulus.pow_repr (M : Modulus) (hM : M.Valid) {a : U256} {α : Nat}
    (ha : M.Repr a α) (e : Nat) : M.Repr (M.pow a e) (α ^ e) := by
  have := M.pow_go_repr hM ha e (e.log2 + 1) M.one 1 (M.one_repr hM)
  rw [Nat.one_pow, Nat.one_mul, Nat.mod_eq_of_lt Nat.lt_log2_self] at this
  exact this

theorem Modulus.toMont_repr (M : Modulus) (hM : M.Valid) (a : U256) (ha : a.Valid) :
    M.Repr (M.toMont a) a.toNat :=
  M.toMont_spec hM a ha

theorem Modulus.fromMont_repr (M : Modulus) (hM : M.Valid) {x : U256} {v : Nat}
    (hx : M.Repr x v) : (M.fromMont x).Valid ∧ (M.fromMont x).toNat = v % M.value := by
  have ⟨cv, clt, ceq⟩ := M.fromMont_spec hM x hx.1
  refine ⟨cv, ?_⟩
  apply mod_cancel (k := 2 ^ 256) hM.coprime clt (Nat.mod_lt _ hM.value_pos)
  rw [Nat.mul_comm (2 ^ 256) (M.fromMont x).toNat, ceq, Nat.mod_eq_of_lt (hx.lt hM), hx.2,
    Nat.mul_mod_mod, Nat.mul_comm]

/-- **Scalar inversion computes `a^(n-2) mod n`** (which is `a⁻¹` because
`n` is prime). -/
theorem Scalar.inv_spec (a : Scalar) (ha : a.Valid) :
    (Scalar.inv a).Valid ∧ (Scalar.inv a).toNat = a.toNat ^ (n - 2) % n := by
  have hM := nMod_valid
  have h := nMod.fromMont_repr hM (nMod.pow_repr hM (nMod.toMont_repr hM a.val ha.1) (n - 2))
  exact ⟨⟨h.1, by show (nMod.fromMont _).toNat < n; rw [h.2]; exact Nat.mod_lt _ (by decide)⟩, h.2⟩

/-- A valid field element is the Montgomery form of its canonical value. -/
theorem Fe.repr (a : Fe) (ha : a.Valid) : pMod.Repr a.mont a.toNat := by
  have hM := pMod_valid
  have ⟨_, _, e⟩ := pMod.fromMont_spec hM a.mont ha.1
  rw [Nat.mod_eq_of_lt (show a.mont.toNat < pMod.value from ha.2)] at e
  exact ⟨ha.1, e.symm⟩

/-- **Field inversion computes `a^(p-2) mod p`** (which is `a⁻¹` because `p`
is prime). -/
theorem Fe.inv_spec (a : Fe) (ha : a.Valid) :
    (Fe.inv a).Valid ∧ (Fe.inv a).toNat = a.toNat ^ (p - 2) % p := by
  have hM := pMod_valid
  rw [show Fe.inv a = ⟨pMod.pow a.mont (p - 2)⟩ from rfl]
  generalize hx : pMod.pow a.mont (p - 2) = x
  have hr : pMod.Repr x (a.toNat ^ (p - 2)) := hx ▸ pMod.pow_repr hM (a.repr ha) (p - 2)
  exact ⟨⟨hr.1, hr.lt hM⟩, (pMod.fromMont_repr hM hr).2⟩

/-- Cancel an addend modulo `m` between two values below `m`. -/
theorem add_mod_cancel {c d y m : Nat} (hc : c < m) (hd : d < m)
    (h : (c + y) % m = (d + y) % m) : c = d := by
  have key : ∀ c d, c < m → d < m → (c + y) % m = (d + y) % m → d ≤ c → c = d := by
    intro c d hc hd h hle
    have h1 := Nat.sub_mod_eq_zero_of_mod_eq h
    rw [Nat.add_sub_add_right] at h1
    have := Nat.eq_zero_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero h1) (by omega)
    omega
  rcases Nat.le_total d c with hle | hle
  · exact key c d hc hd h hle
  · exact (key d c hd hc h.symm hle).symm

/-- Modular subtraction on Montgomery representatives. -/
theorem Modulus.sub_repr (M : Modulus) (hM : M.Valid) {x y : U256} {v w : Nat}
    (hx : M.Repr x v) (hy : M.Repr y w) (hw : w < M.value) :
    M.Repr (M.sub x y) (v + M.value - w) := by
  have ⟨cv, ceq⟩ := M.sub_spec hM x y hx.1 hy.1 (hx.lt hM) (hy.lt hM)
  refine ⟨cv, ?_⟩
  have hm := hM.value_pos
  apply add_mod_cancel (y := y.toNat) (by rw [ceq]; exact Nat.mod_lt _ hm) (Nat.mod_lt _ hm)
  have hyl := hy.lt hM
  rw [ceq, Nat.mod_add_mod, Nat.sub_add_cancel (by omega), Nat.add_mod_right, hy.2,
    Nat.add_mod_mod, Nat.mod_add_mod, ← Nat.add_mul, Nat.sub_add_cancel (by omega),
    Nat.add_mul, Nat.mul_comm M.value, Nat.add_mul_mod_self_right, hx.2, Nat.mod_mod]

/-- **Field subtraction is correct** on canonical values. -/
theorem Fe.sub_spec (a b : Fe) (ha : a.Valid) (hb : b.Valid) :
    (a - b).Valid ∧ (a - b).toNat = (a.toNat + p - b.toNat) % p := by
  have hM := pMod_valid
  have hblt : b.toNat < p := by
    have ⟨_, h, _⟩ := pMod.fromMont_spec hM b.mont hb.1; exact h
  have hr := pMod.sub_repr hM (a.repr ha) (b.repr hb) hblt
  exact ⟨⟨hr.1, hr.lt hM⟩, (pMod.fromMont_repr hM hr).2⟩

/-- **Field negation is correct** on canonical values. -/
theorem Fe.neg_spec (a : Fe) (ha : a.Valid) :
    (-a).Valid ∧ (-a).toNat = (p - a.toNat) % p := by
  have hM := pMod_valid
  have hzero : pMod.Repr U256.zero 0 := ⟨by simp [U256.zero, U256.Valid], by decide⟩
  have halt : a.toNat < p := by
    have ⟨_, h, _⟩ := pMod.fromMont_spec hM a.mont ha.1; exact h
  have hr := pMod.sub_repr hM hzero (a.repr ha) halt
  rw [Nat.zero_add] at hr
  exact ⟨⟨hr.1, hr.lt hM⟩, (pMod.fromMont_repr hM hr).2⟩

end Secp256k1.CT
