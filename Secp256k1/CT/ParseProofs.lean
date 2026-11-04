import Secp256k1.CT.Proofs

/-!
# Parsing scalars

`Scalar.ofBytes?` accepts exactly the 32-byte encodings of values in
`[0, n-1]` and returns a scalar satisfying the representation invariant
`Scalar.Valid`. Used to make validity a structural invariant of
`ECDSA.PrivateKey`.
-/

namespace Secp256k1.CT

theorem shl_byte_lt (b : UInt8) (k : UInt64) (hk : k.toNat ≤ 24) :
    (b.toUInt64 <<< k).toNat < 2 ^ 32 := by
  have hb : b.toUInt64.toNat < 2 ^ 8 := by rw [UInt8.toNat_toUInt64]; exact b.toNat_lt
  rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt (show k.toNat < 64 by omega), Nat.shiftLeft_eq]
  have : b.toUInt64.toNat * 2 ^ k.toNat < 2 ^ 32 :=
    calc b.toUInt64.toNat * 2 ^ k.toNat < 2 ^ 8 * 2 ^ k.toNat :=
          Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos _)
      _ = 2 ^ (8 + k.toNat) := (Nat.pow_add 2 8 k.toNat).symm
      _ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) this

theorem U256.beWord_lt (bs : ByteArray) (i : Nat) : (U256.beWord bs i).toNat < 2 ^ 32 := by
  unfold U256.beWord
  simp only [UInt64.toNat_or]
  refine Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow ?_ ?_) ?_) ?_
  · exact shl_byte_lt _ 24 (by decide)
  · exact shl_byte_lt _ 16 (by decide)
  · exact shl_byte_lt _ 8 (by decide)
  · rw [UInt8.toNat_toUInt64]; exact Nat.lt_trans (UInt8.toNat_lt _) (by decide)

theorem U256.ofBytes_valid (bs : ByteArray) : (U256.ofBytes bs).Valid :=
  ⟨U256.beWord_lt bs 0, U256.beWord_lt bs 1, U256.beWord_lt bs 2, U256.beWord_lt bs 3,
   U256.beWord_lt bs 4, U256.beWord_lt bs 5, U256.beWord_lt bs 6, U256.beWord_lt bs 7⟩

/-- The constant-time comparison: `lt a b = 1` exactly when `a < b`. -/
theorem U256.lt_eq_one_iff {a b : U256} (ha : a.Valid) (hb : b.Valid) :
    U256.lt a b = 1 ↔ a.toNat < b.toNat := by
  have ⟨e, hc⟩ := U256.sub_toNat a b ha hb
  have hl := U256.toNat_lt _ (sub_low_valid a b)
  have hb' := U256.toNat_lt _ hb
  unfold U256.lt
  rcases UInt64.eq_zero_or_one hc with h | h <;> rw [h] at e ⊢ <;>
    simp only [UInt64.toNat_zero, UInt64.toNat_one] at e
  · simp only [show (0 : UInt64) ≠ 1 by decide, false_iff]; omega
  · simp only [true_iff]; omega

/-- **Parsed scalars are valid**: `Scalar.ofBytes?` returns scalars with
`32`-bit limbs and value below `n`. -/
theorem Scalar.ofBytes?_valid {bs : ByteArray} {s : Scalar} (h : Scalar.ofBytes? bs = some s) :
    s.Valid := by
  unfold Scalar.ofBytes? Scalar.ofBytesChecked at h
  simp only [declassify] at h
  split at h
  · exact absurd h (by simp)
  · have hv := U256.ofBytes_valid bs
    by_cases hlt : U256.lt (U256.ofBytes bs) nMod.m = 1
    · simp only [hlt, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      refine ⟨hv, ?_⟩
      have := (U256.lt_eq_one_iff hv nMod_valid.m_valid).1 hlt
      rwa [nMod_valid.m_eq] at this
    · simp only [beq_iff_eq, hlt, ↓reduceIte, reduceCtorEq] at h

/-- A scalar for which `isZero` returns `0` is nonzero. -/
theorem Scalar.toNat_ne_zero {s : Scalar} (h : s.isZero = 0) : s.toNat ≠ 0 := by
  intro h0
  have hlimbs : s.val.l0.toNat = 0 ∧ s.val.l1.toNat = 0 ∧ s.val.l2.toNat = 0 ∧
      s.val.l3.toNat = 0 ∧ s.val.l4.toNat = 0 ∧ s.val.l5.toNat = 0 ∧ s.val.l6.toNat = 0 ∧
      s.val.l7.toNat = 0 := by
    simp only [Scalar.toNat, U256.toNat] at h0; omega
  have hz : ∀ x : UInt64, x.toNat = 0 → x = 0 := fun x hx => UInt64.toNat_inj.mp (by rw [hx]; rfl)
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hlimbs
  simp only [Scalar.isZero, U256.isZero, hz _ h0, hz _ h1, hz _ h2, hz _ h3, hz _ h4, hz _ h5,
    hz _ h6, hz _ h7] at h
  exact absurd h (by decide)

end Secp256k1.CT
