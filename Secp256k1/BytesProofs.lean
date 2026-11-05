import Secp256k1.ECDSA

/-!
# Byte encodings

* `bytesToNat_natToBytes`, `natToBytes_bytesToNat`: the big-endian
  conversions are inverse to each other (`bytesToNat (natToBytes x len) =
  x mod 256^len`, and `natToBytes (bytesToNat bs) bs.size = bs`).
* `Signature.ofCompact?_toCompact`, `Signature.toCompact_ofCompact?`: the
  64-byte compact encoding is a bijection between 64-byte arrays and pairs
  `(r, s)` with `r, s < 2²⁵⁶`.
* `CT.U256.ofBytes_toBytes`, `PrivateKey.ofBytes?_toBytes`: the constant-time
  32-byte encoding of limbs round-trips, so serialising and re-parsing a
  private key returns the same key.
-/

namespace Secp256k1

/-! ## `ByteArray.foldl` is a list fold -/

theorem byteArray_foldl_loop {β : Type} (f : β → UInt8 → β) (as : ByteArray)
    (h : as.size ≤ as.size) :
    ∀ (i j : Nat) (b : β), j + i = as.size →
      ByteArray.foldlM.loop (m := Id) (fun b a => pure (f b a)) as as.size h i j b =
        (as.data.toList.drop j).foldl f b
  | 0, j, b, hij => by
    unfold ByteArray.foldlM.loop
    have : as.data.toList.drop j = [] := by
      rw [List.drop_eq_nil_iff, Array.length_toList, ByteArray.size_data]; omega
    rw [this]
    split <;> rfl
  | i + 1, j, b, hij => by
    unfold ByteArray.foldlM.loop
    have hj : j < as.size := by omega
    rw [dite_eq_left hj]
    have hl : j < as.data.toList.length := by
      rw [Array.length_toList, ByteArray.size_data]; exact hj
    rw [List.drop_eq_getElem_cons hl, List.foldl_cons]
    show ByteArray.foldlM.loop (m := Id) (fun b a => pure (f b a)) as as.size h i (j + 1)
      (f b as[j]) = _
    rw [byteArray_foldl_loop f as h i (j + 1) _ (by omega), ByteArray.getElem_eq_getElem_data,
      Array.getElem_toList]

theorem byteArray_foldl_eq {β : Type} (f : β → UInt8 → β) (init : β) (as : ByteArray) :
    as.foldl f init = as.data.toList.foldl f init := by
  unfold ByteArray.foldl ByteArray.foldlM
  rw [dite_eq_left (Nat.le_refl _)]
  simp only [Nat.sub_zero, Id.run]
  exact byteArray_foldl_loop f as _ as.size 0 init (Nat.zero_add _)

/-! ## Big-endian conversions -/

/-- One step of `bytesToNat`. -/
def bytesStep (acc : Nat) (b : UInt8) : Nat := acc * 256 + b.toNat

theorem bytesToNat_eq (bs : ByteArray) : bytesToNat bs = bs.data.toList.foldl bytesStep 0 :=
  byteArray_foldl_eq _ _ _

theorem foldl_bytesStep (l : List UInt8) :
    ∀ a, l.foldl bytesStep a = a * 256 ^ l.length + l.foldl bytesStep 0 := by
  induction l with
  | nil => intro a; simp
  | cons b l ih =>
    intro a
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (bytesStep a b), ih (bytesStep 0 b)]
    simp only [bytesStep, Nat.pow_succ]
    generalize 256 ^ l.length = t
    rw [Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256 t, Nat.add_assoc]

theorem foldl_bytesStep_lt (l : List UInt8) : l.foldl bytesStep 0 < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [foldl_bytesStep l (bytesStep 0 b)]
    have hb := b.toNat_lt
    simp only [bytesStep, Nat.zero_mul, Nat.zero_add, Nat.pow_succ]
    have : b.toNat * 256 ^ l.length + l.foldl bytesStep 0 < (b.toNat + 1) * 256 ^ l.length := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    exact Nat.lt_of_lt_of_le this (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hb)

/-- `natToBytes.go` read from the low end: the bytes of `v mod 256^k`. -/
theorem natToBytes_go_foldl (k : Nat) :
    ∀ (v : Nat) (acc : List UInt8) (a : Nat),
      (natToBytes.go k v acc).foldl bytesStep a = acc.foldl bytesStep (a * 256 ^ k + v % 256 ^ k) := by
  induction k with
  | zero => intro v acc a; simp [natToBytes.go, Nat.mod_one]
  | succ k ih =>
    intro v acc a
    simp only [natToBytes.go]
    rw [ih, List.foldl_cons]
    congr 1
    have hb : (v % 256).toUInt8.toNat = v % 256 := by
      simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow, Nat.dvd_refl, Nat.mod_mod_of_dvd]
    have key : v % 256 ^ (k + 1) = v % 256 + 256 * (v / 256 % 256 ^ k) := by
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, Nat.mod_mul]
    show (a * 256 ^ k + v / 256 % 256 ^ k) * 256 + (v % 256).toUInt8.toNat =
      a * 256 ^ (k + 1) + v % 256 ^ (k + 1)
    rw [hb, key, Nat.pow_succ, ← Nat.mul_assoc]
    generalize a * 256 ^ k = t
    generalize v / 256 % 256 ^ k = q
    omega

/-- **`bytesToNat ∘ natToBytes` reduces modulo `256^len`.** -/
theorem bytesToNat_natToBytes (x len : Nat) : bytesToNat (natToBytes x len) = x % 256 ^ len := by
  rw [bytesToNat_eq, natToBytes, List.toList_data_toByteArray, natToBytes_go_foldl]
  simp

theorem natToBytes_go_mod (k : Nat) :
    ∀ (v : Nat) (acc : List UInt8), natToBytes.go k v acc = natToBytes.go k (v % 256 ^ k) acc := by
  induction k with
  | zero => intro v acc; rfl
  | succ k ih =>
    intro v acc
    simp only [natToBytes.go]
    rw [ih (v / 256), ih ((v % 256 ^ (k + 1)) / 256)]
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, Nat.mod_mul_right_div_self,
      Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right 256 _), Nat.mod_mod]

/-- `natToBytes.go` read from the high end. -/
theorem natToBytes_go_succ (k : Nat) :
    ∀ (v : Nat) (acc : List UInt8),
      natToBytes.go (k + 1) v acc = (v / 256 ^ k % 256).toUInt8 :: natToBytes.go k v acc := by
  induction k with
  | zero => intro v acc; simp [natToBytes.go]
  | succ k ih =>
    intro v acc
    rw [natToBytes.go, ih, Nat.div_div_eq_div_mul, ← Nat.pow_succ']
    rfl

theorem natToBytes_go_foldl_self (l : List UInt8) :
    ∀ acc, natToBytes.go l.length (l.foldl bytesStep 0) acc = l ++ acc := by
  induction l with
  | nil => intro acc; rfl
  | cons b l ih =>
    intro acc
    simp only [List.length_cons, List.foldl_cons, List.cons_append]
    rw [natToBytes_go_succ, foldl_bytesStep l (bytesStep 0 b)]
    have hlt := foldl_bytesStep_lt l
    have hpos : 0 < 256 ^ l.length := Nat.pow_pos_iff.2 (Or.inl (by decide))
    have hb : b.toNat < 256 := b.toNat_lt
    simp only [bytesStep, Nat.zero_mul, Nat.zero_add]
    rw [Nat.mul_comm b.toNat, Nat.mul_add_div hpos, Nat.div_eq_of_lt hlt, Nat.add_zero,
      Nat.mod_eq_of_lt hb, natToBytes_go_mod l.length (256 ^ l.length * b.toNat + _),
      Nat.mul_add_mod, Nat.mod_eq_of_lt hlt, ih]
    simp only [Nat.toUInt8_eq, UInt8.ofNat_toNat]

/-- **`natToBytes ∘ bytesToNat` is the identity** at the original length. -/
theorem natToBytes_bytesToNat (bs : ByteArray) : natToBytes (bytesToNat bs) bs.size = bs := by
  rw [bytesToNat_eq, natToBytes, ← ByteArray.size_data, ← Array.length_toList,
    natToBytes_go_foldl_self, List.append_nil]
  apply ByteArray.ext
  apply Array.ext'
  rw [List.toList_data_toByteArray]

theorem bytesToNat_lt (bs : ByteArray) : bytesToNat bs < 256 ^ bs.size := by
  rw [bytesToNat_eq, ← ByteArray.size_data, ← Array.length_toList]
  exact foldl_bytesStep_lt _

/-! ## Compact signatures -/

namespace ECDSA.Signature

/-- **Compact decoding inverts encoding** for `r, s < 2²⁵⁶`. -/
theorem ofCompact?_toCompact (sig : Signature) (hr : sig.r < 2 ^ 256) (hs : sig.s < 2 ^ 256) :
    ofCompact? sig.toCompact = some sig := by
  have h256 : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  unfold ofCompact? toCompact
  rw [ite_eq_left (by rw [ByteArray.size_append, natToBytes_size, natToBytes_size]),
    ByteArray.extract_append_eq_left (natToBytes_size _ _).symm,
    ByteArray.extract_append_eq_right (natToBytes_size _ _).symm
      (by rw [natToBytes_size, natToBytes_size]),
    bytesToNat_natToBytes, bytesToNat_natToBytes, Nat.mod_eq_of_lt (h256 ▸ hr),
    Nat.mod_eq_of_lt (h256 ▸ hs)]

/-- **Compact encoding inverts decoding**: every accepted 64-byte array is the
encoding of the decoded signature. -/
theorem toCompact_ofCompact? {bs : ByteArray} {sig : Signature} (h : ofCompact? bs = some sig) :
    sig.toCompact = bs := by
  unfold ofCompact? at h
  split at h
  · rename_i hsize
    simp only [Option.some.injEq] at h
    subst h
    have h1 : (bs.extract 0 32).size = 32 := by rw [ByteArray.size_extract]; omega
    have h2 : (bs.extract 32 64).size = 32 := by rw [ByteArray.size_extract]; omega
    have e1 := natToBytes_bytesToNat (bs.extract 0 32)
    have e2 := natToBytes_bytesToNat (bs.extract 32 64)
    rw [h1] at e1
    rw [h2] at e2
    unfold toCompact
    dsimp only
    rw [e1, e2, ByteArray.extract_append_extract, Nat.min_eq_left (by omega),
      Nat.max_eq_right (by omega)]
    have : bs.extract 0 64 = bs.extract 0 bs.size := by rw [hsize]
    rw [this, ByteArray.extract_zero_size]
  · exact absurd h (by simp)

end ECDSA.Signature

/-! ## Constant-time limbs and private keys -/

namespace CT

theorem or_eq_add_of_lt {x y : Nat} (k : Nat) (hx : x % 2 ^ k = 0) (hy : y < 2 ^ k) :
    x ||| y = x + y := by
  have : x = 2 ^ k * (x / 2 ^ k) := by
    have := Nat.div_add_mod x (2 ^ k); rw [hx, Nat.add_zero] at this; exact this.symm
  rw [this, ← Nat.two_pow_add_eq_or_of_lt hy]

theorem byte_toNat (w : UInt64) (k : Nat) (hk : k < 64) :
    ((w >>> k.toUInt64).toUInt8.toUInt64).toNat = w.toNat / 2 ^ k % 256 := by
  have hk' : k.toUInt64.toNat = k := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  rw [UInt8.toNat_toUInt64, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, hk',
    Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow]

theorem word_sum (v : Nat) (hv : v < 2 ^ 32) :
    v / 2 ^ 24 % 256 * 2 ^ 24 ||| v / 2 ^ 16 % 256 * 2 ^ 16 ||| v / 2 ^ 8 % 256 * 2 ^ 8 |||
      v % 256 = v := by
  rewrite [or_eq_add_of_lt (x := v / 2 ^ 24 % 256 * 2 ^ 24) (y := v / 2 ^ 16 % 256 * 2 ^ 16) 24
      (by omega) (by omega),
    or_eq_add_of_lt (x := v / 2 ^ 24 % 256 * 2 ^ 24 + v / 2 ^ 16 % 256 * 2 ^ 16)
      (y := v / 2 ^ 8 % 256 * 2 ^ 8) 16 (by omega) (by omega),
    or_eq_add_of_lt (x := v / 2 ^ 24 % 256 * 2 ^ 24 + v / 2 ^ 16 % 256 * 2 ^ 16 +
      v / 2 ^ 8 % 256 * 2 ^ 8) (y := v % 256) 8 (by omega) (by omega)]
  omega

/-- Reassembling the four big-endian bytes of a 32-bit limb gives the limb back. -/
theorem word_bytes (w : UInt64) (hw : w.toNat < 2 ^ 32) :
    ((w >>> 24).toUInt8.toUInt64 <<< 24) ||| ((w >>> 16).toUInt8.toUInt64 <<< 16) |||
      ((w >>> 8).toUInt8.toUInt64 <<< 8) ||| w.toUInt8.toUInt64 = w := by
  apply UInt64.toNat_inj.mp
  have b3 := byte_toNat w 24 (by decide)
  have b2 := byte_toNat w 16 (by decide)
  have b1 := byte_toNat w 8 (by decide)
  have b0 : w.toUInt8.toUInt64.toNat = w.toNat % 256 := by
    rw [UInt8.toNat_toUInt64, UInt64.toNat_toUInt8]
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft] at *
  simp only [show (24 : UInt64) = (24 : Nat).toUInt64 from rfl,
    show (16 : UInt64) = (16 : Nat).toUInt64 from rfl,
    show (8 : UInt64) = (8 : Nat).toUInt64 from rfl, b3, b2, b1, b0]
  simp only [show (Nat.toUInt64 24).toNat % 64 = 24 from rfl, show (Nat.toUInt64 16).toNat % 64 = 16 from rfl,
    show (Nat.toUInt64 8).toNat % 64 = 8 from rfl, Nat.shiftLeft_eq]
  generalize w.toNat = v at *
  have e3 : v / 2 ^ 24 % 256 * 2 ^ 24 % 2 ^ 64 = v / 2 ^ 24 % 256 * 2 ^ 24 := Nat.mod_eq_of_lt (by omega)
  have e2 : v / 2 ^ 16 % 256 * 2 ^ 16 % 2 ^ 64 = v / 2 ^ 16 % 256 * 2 ^ 16 := Nat.mod_eq_of_lt (by omega)
  have e1 : v / 2 ^ 8 % 256 * 2 ^ 8 % 2 ^ 64 = v / 2 ^ 8 % 256 * 2 ^ 8 := Nat.mod_eq_of_lt (by omega)
  rw [e3, e2, e1]
  exact word_sum v hw

/-- The four big-endian bytes of a limb, as written by `U256.pushWord`. -/
def wordBytes (w : UInt64) : List UInt8 :=
  [(w >>> 24).toUInt8, (w >>> 16).toUInt8, (w >>> 8).toUInt8, w.toUInt8]

theorem pushWord_toList (out : ByteArray) (w : UInt64) :
    (U256.pushWord out w).data.toList = out.data.toList ++ wordBytes w := by
  simp [U256.pushWord, ByteArray.data_push, wordBytes]

theorem U256.toBytes_toList (a : U256) :
    (U256.toBytes a).data.toList =
      wordBytes a.l7 ++ wordBytes a.l6 ++ wordBytes a.l5 ++ wordBytes a.l4 ++
        wordBytes a.l3 ++ wordBytes a.l2 ++ wordBytes a.l1 ++ wordBytes a.l0 := by
  simp [U256.toBytes, pushWord_toList, ByteArray.emptyWithCapacity]
  rfl

theorem U256.toBytes_size (a : U256) : (U256.toBytes a).size = 32 := by
  rw [← ByteArray.size_data, ← Array.length_toList, U256.toBytes_toList]
  simp [wordBytes]

theorem getElem!_eq_list {bs : ByteArray} {l : List UInt8} (h : bs.data.toList = l) (i : Nat) :
    bs[i]! = l[i]! := by
  have hlen : bs.size = l.length := by rw [← ByteArray.size_data, ← Array.length_toList, h]
  by_cases hi : i < bs.size
  · rw [getElem!_pos bs i hi, getElem!_pos l i (hlen ▸ hi), ByteArray.getElem_eq_getElem_data,
      ← Array.getElem_toList]
    exact List.getElem_of_eq h _
  · rw [getElem!_neg bs i hi, getElem!_neg l i (hlen ▸ hi)]

/-- **Decoding the 32-byte encoding of valid limbs returns the limbs.** -/
theorem U256.ofBytes_toBytes (a : U256) (ha : a.Valid) : U256.ofBytes (U256.toBytes a) = a := by
  have hl := U256.toBytes_toList a
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7⟩ := a
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := ha
  simp only [U256.ofBytes, U256.beWord, getElem!_eq_list hl]
  simp only [wordBytes, List.cons_append, List.nil_append, List.getElem!_cons_succ,
    List.getElem!_cons_zero, Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd]
  rw [word_bytes l0 h0, word_bytes l1 h1, word_bytes l2 h2, word_bytes l3 h3, word_bytes l4 h4,
    word_bytes l5 h5, word_bytes l6 h6, word_bytes l7 h7]

/-- **Parsing the encoding of a valid scalar returns the scalar.** -/
theorem Scalar.ofBytes?_toBytes (s : Scalar) (hs : s.Valid) : Scalar.ofBytes? s.toBytes = some s := by
  have hsize := U256.toBytes_size s.val
  have hv := U256.ofBytes_toBytes s.val hs.1
  have hlt : U256.lt s.val nMod.m = 1 :=
    (U256.lt_eq_one_iff hs.1 nMod_valid.m_valid).2 (by rw [nMod_valid.m_eq]; exact hs.2)
  unfold Scalar.ofBytes? Scalar.ofBytesChecked Scalar.toBytes
  simp only [hsize, ne_eq, not_true_eq_false, ↓reduceIte, hv, declassify, hlt, beq_self_eq_true]

end CT

/-- **Serialising and re-parsing a private key returns the same key.** -/
theorem ECDSA.PrivateKey.ofBytes?_toBytes (sk : PrivateKey) :
    PrivateKey.ofBytes? sk.toBytes = some sk := by
  have h := CT.Scalar.ofBytes?_toBytes sk.scalar sk.valid
  unfold PrivateKey.ofBytes? PrivateKey.toBytes
  split
  · rename_i h'
    exact absurd (h'.symm.trans h) (by simp)
  · rename_i s h'
    have hs : s = sk.scalar := Option.some.inj (h'.symm.trans h)
    subst hs
    simp only [CT.declassify, sk.isNonzero, ↓reduceDIte]

end Secp256k1
