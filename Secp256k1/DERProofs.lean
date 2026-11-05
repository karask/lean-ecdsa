import Secp256k1.BytesProofs

/-!
# DER signatures

* `Signature.ofDER?_toDER`: decoding the DER encoding of a signature with
  `r, s < 2²⁵⁶` returns the signature.
* `Signature.toDER_ofDER?`: **the strict parser accepts only canonical
  encodings**: every byte string accepted by `ofDER?` is exactly `toDER` of the
  result. So a signature cannot be re-encoded into a different accepted byte
  string (no DER malleability, as required by BIP 66).
-/

namespace Secp256k1

/-! ## Byte arrays as lists -/

theorem ba_ext {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b :=
  ByteArray.ext (Array.ext' h)

theorem ba_size (bs : ByteArray) : bs.size = bs.data.toList.length := by
  rw [Array.length_toList, ByteArray.size_data]

theorem ba_getElem! (bs : ByteArray) (i : Nat) : bs[i]! = bs.data.toList[i]! :=
  CT.getElem!_eq_list rfl i

theorem ba_extract (bs : ByteArray) (i j : Nat) :
    (bs.extract i j).data.toList = bs.data.toList.extract i j := by
  rw [ByteArray.data_extract, Array.toList_extract]

theorem ba_append (a b : ByteArray) : (a ++ b).data.toList = a.data.toList ++ b.data.toList := by
  rw [ByteArray.data_append, Array.toList_append]

theorem ba_mk (l : List UInt8) : (ByteArray.mk l.toArray).data.toList = l := rfl

/-! ## Minimal big-endian encodings -/

def listVal (l : List UInt8) : Nat := l.foldl bytesStep 0

theorem bytesToNat_eq_listVal (bs : ByteArray) : bytesToNat bs = listVal bs.data.toList :=
  bytesToNat_eq bs

theorem listVal_cons (b : UInt8) (t : List UInt8) :
    listVal (b :: t) = b.toNat * 256 ^ t.length + listVal t := by
  simp only [listVal, List.foldl_cons]
  rw [foldl_bytesStep t (bytesStep 0 b)]
  simp [bytesStep]

theorem byteLength_bound {x : Nat} (hx : x ≠ 0) :
    256 ^ (byteLength x - 1) ≤ x ∧ x < 256 ^ byteLength x := by
  unfold byteLength
  simp only [hx, ↓reduceIte, Nat.add_sub_cancel]
  have h1 := Nat.log2_self_le hx
  have h2 := Nat.lt_log2_self (n := x)
  have e : ∀ k, (256 : Nat) ^ k = 2 ^ (8 * k) := fun k => by rw [Nat.pow_mul]
  constructor
  · rw [e]
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (Nat.mul_div_le _ _)) h1
  · rw [e]
    exact Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) (by omega))

theorem natToMinimalBytes_val (x : Nat) : bytesToNat (natToMinimalBytes x) = x := by
  rw [natToMinimalBytes, bytesToNat_natToBytes]
  by_cases hx : x = 0
  · subst hx; simp
  · exact Nat.mod_eq_of_lt (byteLength_bound hx).2

theorem natToMinimalBytes_zero : natToMinimalBytes 0 = ByteArray.empty := rfl

theorem natToMinimalBytes_size (x : Nat) : (natToMinimalBytes x).size = byteLength x :=
  natToBytes_size _ _

/-- The minimal encoding of a non-zero number starts with a non-zero byte. -/
theorem natToMinimalBytes_head {x : Nat} (hx : x ≠ 0) :
    ∃ b t, (natToMinimalBytes x).data.toList = b :: t ∧ b ≠ 0 := by
  have ⟨lo, hi⟩ := byteLength_bound hx
  have hlen : byteLength x = byteLength x - 1 + 1 := by
    unfold byteLength; simp only [hx, ↓reduceIte]; omega
  generalize hk : byteLength x - 1 = k at lo hlen
  rw [hlen] at hi
  refine ⟨(x / 256 ^ k % 256).toUInt8, (natToBytes.go k x []), ?_, ?_⟩
  · rw [natToMinimalBytes, natToBytes, List.toList_data_toByteArray, hlen, natToBytes_go_succ]
  · intro h0
    have hpos : 0 < 256 ^ k := Nat.pow_pos_iff.2 (Or.inl (by decide))
    have hq : x / 256 ^ k < 256 := by
      rw [Nat.div_lt_iff_lt_mul hpos, ← Nat.pow_succ']; exact hi
    have hq1 : 1 ≤ x / 256 ^ k := (Nat.le_div_iff_mul_le hpos).2 (by rw [Nat.one_mul]; exact lo)
    have := congrArg UInt8.toNat h0
    simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hq, UInt8.toNat_zero] at this
    omega

/-- **A byte string with a non-zero first byte is the minimal encoding of its value.** -/
theorem natToMinimalBytes_of_head {E : ByteArray} {b : UInt8} {t : List UInt8}
    (hE : E.data.toList = b :: t) (hb : b ≠ 0) : natToMinimalBytes (bytesToNat E) = E := by
  have hv : bytesToNat E = b.toNat * 256 ^ t.length + listVal t := by
    rw [bytesToNat_eq_listVal, hE, listVal_cons]
  have hb1 : 1 ≤ b.toNat := by
    have : b.toNat ≠ 0 := fun h => hb (UInt8.toNat_inj.mp (by rw [h]; rfl))
    omega
  have hb2 := b.toNat_lt
  have ht : listVal t < 256 ^ t.length := foldl_bytesStep_lt t
  have e : ∀ k, (256 : Nat) ^ k = 2 ^ (8 * k) := fun k => by rw [Nat.pow_mul]
  have lo : 2 ^ (8 * t.length) ≤ bytesToNat E := by
    rw [hv, ← e]; exact Nat.le_trans (Nat.le_mul_of_pos_left _ hb1) (Nat.le_add_right _ _)
  have hi : bytesToNat E < 2 ^ (8 * (t.length + 1)) := by
    rw [hv, ← e, Nat.pow_succ]
    have : b.toNat * 256 ^ t.length + listVal t < (b.toNat + 1) * 256 ^ t.length := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    exact Nat.lt_of_lt_of_le this (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hb2)
  have hne : bytesToNat E ≠ 0 := by
    intro h0; rw [h0] at lo; exact absurd lo (by simp)
  have hlog1 : 8 * t.length ≤ (bytesToNat E).log2 := (Nat.le_log2 hne).2 lo
  have hlog2 : (bytesToNat E).log2 < 8 * (t.length + 1) := (Nat.log2_lt hne).2 hi
  have hlen : byteLength (bytesToNat E) = E.size := by
    unfold byteLength
    simp only [hne, ↓reduceIte]
    rw [ba_size, hE, List.length_cons]
    omega
  rw [natToMinimalBytes, hlen, natToBytes_bytesToNat]

/-! ## DER integer bodies -/

theorem and80_eq_zero_iff (b : UInt8) : b &&& 0x80 = 0 ↔ b.toNat < 128 := by
  have key : ∀ v : Fin 256, (v.val &&& 128 = 0 ↔ v.val < 128) := by decide +kernel
  have h := key ⟨b.toNat, b.toNat_lt⟩
  constructor
  · intro h0
    have := congrArg UInt8.toNat h0
    rw [UInt8.toNat_and] at this
    exact h.1 this
  · intro hlt
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_and]
    exact h.2 hlt

theorem uint8_eq_zero_iff (b : UInt8) : b = 0 ↔ b.toNat = 0 :=
  ⟨fun h => by rw [h]; rfl, fun h => UInt8.toNat_inj.mp (by rw [h]; rfl)⟩

/-- The body condition checked by `derIntegerOk`: non-empty, non-negative (top
bit clear) and without a redundant leading zero. -/
def BodyOk : List UInt8 → Prop
  | [] => False
  | [b] => b.toNat < 128
  | b :: c :: _ => b.toNat < 128 ∧ (b = 0 → 128 ≤ c.toNat)

namespace ECDSA.Signature

theorem listVal_zero_cons (l : List UInt8) : listVal (0 :: l) = listVal l := by
  rw [listVal_cons]; simp

theorem derBody_zero : (derBody 0).data.toList = [0] := by
  simp [derBody, natToMinimalBytes_zero]

theorem derBody_cases {x : Nat} (hx : x ≠ 0) :
    ∃ b t, (natToMinimalBytes x).data.toList = b :: t ∧ b ≠ 0 ∧
      (derBody x).data.toList = if 128 ≤ b.toNat then 0 :: b :: t else b :: t := by
  obtain ⟨b, t, hE, hb⟩ := natToMinimalBytes_head hx
  refine ⟨b, t, hE, hb, ?_⟩
  have hsize : (natToMinimalBytes x).size ≠ 0 := by rw [ba_size, hE]; simp
  have h0 : (natToMinimalBytes x)[0]! = b := by rw [ba_getElem!, hE]; rfl
  unfold derBody
  simp only [hsize, h0, decide_false, Bool.false_or]
  by_cases hc : 128 ≤ b.toNat
  · have : (b ≥ 0x80) := UInt8.le_iff_toNat_le.2 hc
    simp only [this, decide_true, ↓reduceIte, hc]
    rw [ba_append, hE]; rfl
  · have : ¬(b ≥ 0x80) := fun h => hc (UInt8.le_iff_toNat_le.1 h)
    simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte, hc, hE]

theorem derBody_val (x : Nat) : bytesToNat (derBody x) = x := by
  by_cases hx : x = 0
  · subst hx; rw [bytesToNat_eq_listVal, derBody_zero]; rfl
  · obtain ⟨b, t, hE, -, hD⟩ := derBody_cases hx
    have hv := natToMinimalBytes_val x
    rw [bytesToNat_eq_listVal, hE] at hv
    rw [bytesToNat_eq_listVal, hD]
    split
    · rw [listVal_zero_cons]; exact hv
    · exact hv

theorem derBody_ok (x : Nat) : BodyOk (derBody x).data.toList := by
  by_cases hx : x = 0
  · subst hx; rw [derBody_zero]; show (0 : UInt8).toNat < 128; decide
  · obtain ⟨b, t, -, hb, hD⟩ := derBody_cases hx
    rw [hD]
    split
    · rename_i hc
      exact ⟨by decide, fun _ => hc⟩
    · rename_i hc
      cases t with
      | nil => show b.toNat < 128; omega
      | cons c t => exact ⟨by omega, fun h => absurd h hb⟩

theorem derBody_size_pos (x : Nat) : 0 < (derBody x).size := by
  rw [ba_size]
  by_cases hx : x = 0
  · subst hx; rw [derBody_zero]; decide
  · obtain ⟨b, t, -, -, hD⟩ := derBody_cases hx
    rw [hD]; split <;> simp

theorem derBody_size_le {x : Nat} (hx : x < 2 ^ 256) : (derBody x).size ≤ 33 := by
  by_cases h0 : x = 0
  · subst h0; rw [ba_size, derBody_zero]; decide
  · obtain ⟨b, t, hE, -, hD⟩ := derBody_cases h0
    have hlen : (natToMinimalBytes x).size ≤ 32 := by
      rw [natToMinimalBytes_size]
      unfold byteLength
      simp only [h0, ↓reduceIte]
      have : x.log2 < 256 := (Nat.log2_lt h0).2 hx
      omega
    rw [ba_size, hE] at hlen
    rw [ba_size, hD]
    split <;> simp at hlen ⊢ <;> omega

/-- **A valid DER integer body is the encoding of its value.** -/
theorem derBody_of_ok {E : ByteArray} (h : BodyOk E.data.toList) : derBody (bytesToNat E) = E := by
  match hE : E.data.toList, h with
  | [b], hb =>
    have hb' : b.toNat < 128 := hb
    by_cases b0 : b = 0
    · subst b0
      have : bytesToNat E = 0 := by rw [bytesToNat_eq_listVal, hE]; rfl
      rw [this]; apply ba_ext; rw [derBody_zero, hE]
    · have hmin := natToMinimalBytes_of_head hE b0
      have hnz : bytesToNat E ≠ 0 := by
        intro h0; rw [h0, natToMinimalBytes_zero] at hmin
        have := congrArg ByteArray.size hmin; rw [ba_size E, hE] at this; simp at this
      obtain ⟨b', t', hE', _, hD⟩ := derBody_cases hnz
      rw [hmin, hE] at hE'
      cases hE'
      apply ba_ext; rw [hD, hE, ite_eq_right (by omega)]
  | b :: c :: t, ⟨hb, hc⟩ =>
    by_cases b0 : b = 0
    · subst b0
      have hc' := hc rfl
      have c0 : c ≠ 0 := fun h => by rw [h] at hc'; exact absurd hc' (by decide)
      let E' : ByteArray := ⟨(c :: t).toArray⟩
      have hE'l : E'.data.toList = c :: t := rfl
      have hval : bytesToNat E = bytesToNat E' := by
        rw [bytesToNat_eq_listVal, bytesToNat_eq_listVal, hE, hE'l, listVal_zero_cons]
      have hmin := natToMinimalBytes_of_head hE'l c0
      have hnz : bytesToNat E' ≠ 0 := by
        intro h0; rw [h0, natToMinimalBytes_zero] at hmin
        have := congrArg ByteArray.size hmin; rw [ba_size E', hE'l] at this; simp at this
      obtain ⟨b', t', hE', _, hD⟩ := derBody_cases hnz
      rw [hmin, hE'l] at hE'
      cases hE'
      rw [hval]; apply ba_ext; rw [hD, hE, ite_eq_left hc']
    · have hmin := natToMinimalBytes_of_head hE b0
      have hnz : bytesToNat E ≠ 0 := by
        intro h0; rw [h0, natToMinimalBytes_zero] at hmin
        have := congrArg ByteArray.size hmin; rw [ba_size E, hE] at this; simp at this
      obtain ⟨b', t', hE', _, hD⟩ := derBody_cases hnz
      rw [hmin, hE] at hE'
      cases hE'
      apply ba_ext; rw [hD, hE, ite_eq_right (by omega)]

theorem extract_getElem! (bs : ByteArray) {off len i : Nat} (hi : i < len) :
    (bs.extract off (off + len)).data.toList[i]! = bs[off + i]! := by
  rw [ba_extract, ba_getElem!, List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
    List.extract_eq_take_drop, Nat.add_sub_cancel_left, List.getElem?_take_of_lt hi,
    List.getElem?_drop]

theorem extract_length {bs : ByteArray} {off len : Nat} (h : off + len ≤ bs.size) :
    (bs.extract off (off + len)).data.toList.length = len := by
  rw [← ba_size, ByteArray.size_extract]; omega

theorem bool_and_not {p q r : Bool} {P Q R : Prop} (hp : p = true ↔ P) (hq : q = true ↔ Q)
    (hr : r = true ↔ R) : (p && !(q && r)) = true ↔ P ∧ (Q → ¬R) := by
  cases p <;> cases q <;> cases r <;> simp_all

/-- `derIntegerOk` checks `BodyOk` on the slice. -/
theorem derIntegerOk_iff {bs : ByteArray} {off len : Nat} (h : off + len ≤ bs.size) :
    derIntegerOk bs off len = true ↔ BodyOk (bs.extract off (off + len)).data.toList := by
  have hlen := extract_length h
  have hget := fun i (hi : i < len) => extract_getElem! bs (off := off) hi
  unfold derIntegerOk
  generalize (bs.extract off (off + len)).data.toList = L at hlen hget
  match L, hlen, hget with
  | [], hlen, _ =>
    subst hlen; simp [BodyOk]
  | [b], hlen, hget =>
    obtain rfl : len = 1 := by simpa using hlen.symm
    have hb : b = bs[off]! := by simpa using hget 0 Nat.one_pos
    rw [← hb]
    simp only [BodyOk, ne_eq, Nat.one_ne_zero, not_false_eq_true, decide_true, Bool.true_and,
      Nat.lt_irrefl, decide_false, Bool.false_and, Bool.not_false, Bool.and_true, beq_iff_eq,
      and80_eq_zero_iff]
  | b :: c :: t, hlen, hget =>
    have hl : len ≠ 0 ∧ len > 1 := by simp at hlen; omega
    have hb : b = bs[off]! := by simpa using hget 0 (by omega)
    have hc : c = bs[off + 1]! := by simpa using hget 1 (by omega)
    rw [← hb, ← hc]
    simp only [ne_eq, hl.1, not_false_eq_true, decide_true, Bool.true_and, hl.2]
    rw [bool_and_not (beq_iff_eq.trans (and80_eq_zero_iff b)) beq_iff_eq
      (beq_iff_eq.trans (and80_eq_zero_iff c))]
    simp only [BodyOk, Nat.not_lt]

theorem toUInt8_toNat_eq {b : UInt8} {k : Nat} (h : b.toNat = k) : k.toUInt8 = b := by
  rw [← h, Nat.toUInt8_eq, UInt8.ofNat_toNat]

/-- **The strict DER parser accepts only canonical encodings**: re-encoding the
parsed signature gives back exactly the input bytes. -/
theorem toDER_ofDER? {bs : ByteArray} {sig : Signature} (h : ofDER? bs = some sig) :
    sig.toDER = bs := by
  unfold ofDER? at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  rename_i h1
  split at h
  · exact absurd h (by simp)
  rename_i h2
  split at h
  · exact absurd h (by simp)
  rename_i h3
  split at h
  · exact absurd h (by simp)
  rename_i h4
  split at h
  · exact absurd h (by simp)
  rename_i h5
  split at h
  · exact absurd h (by simp)
  rename_i h6
  cases h
  generalize hR : bs[3]!.toNat = lenR at h3 h4 h5 h6 ⊢
  generalize hS : bs[5 + lenR]!.toNat = lenS at h4 h6 ⊢
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt, bne_iff_ne, ne_eq,
    Decidable.not_not, Bool.not_eq_true', Bool.not_eq_false] at h1 h2 h3 h4 h5 h6
  obtain ⟨hs8, hs72⟩ := h1
  obtain ⟨h0, h1⟩ := h2
  obtain ⟨h2, okR⟩ := h5
  obtain ⟨h4', okS⟩ := h6
  have hsz : bs.size = lenR + lenS + 6 := h4.symm
  have okR' := (derIntegerOk_iff (by omega)).1 okR
  have okS' := (derIntegerOk_iff (by omega)).1 okS
  rw [show 6 + lenR + lenS = bs.size by omega] at okS'
  -- the two integer bodies
  unfold toDER derInteger
  dsimp only
  rw [derBody_of_ok okR', derBody_of_ok okS']
  have hE1 : (bs.extract 4 (4 + lenR)).size = lenR := by rw [ByteArray.size_extract]; omega
  have hE2 : (bs.extract (6 + lenR) bs.size).size = lenS := by rw [ByteArray.size_extract]; omega
  have hmk : ∀ a c : UInt8, (ByteArray.mk #[a, c]).size = 2 := fun _ _ => rfl
  simp only [ByteArray.size_append, hmk, hE1, hE2]
  apply ba_ext
  simp only [ba_append, ba_extract]
  -- decompose the input
  have hlen : bs.data.toList.length = lenR + lenS + 6 := by rw [← ba_size, hsz]
  simp only [ba_getElem!] at h0 h1 h2 h4' hR hS
  have d : ∀ i, i < bs.data.toList.length →
      bs.data.toList.drop i = bs.data.toList[i]! :: bs.data.toList.drop (i + 1) := fun i hi => by
    rw [List.drop_eq_getElem_cons hi, getElem!_pos bs.data.toList i hi]
  have hl' : bs.data.toList = bs.data.toList[0]! :: bs.data.toList[1]! :: bs.data.toList[2]! ::
      bs.data.toList[3]! :: bs.data.toList.drop 4 := by
    conv => lhs; rw [← List.drop_zero (l := bs.data.toList), d 0 (by omega), d 1 (by omega),
      d 2 (by omega), d 3 (by omega)]
  have hd4 : bs.data.toList.drop 4 = (bs.data.toList.drop 4).take lenR ++
      bs.data.toList[4 + lenR]! :: bs.data.toList[5 + lenR]! :: bs.data.toList.drop (6 + lenR) := by
    conv => lhs; rw [← List.take_append_drop lenR (bs.data.toList.drop 4)]
    rw [List.drop_drop, d (4 + lenR) (by omega), d (4 + lenR + 1) (by omega),
      show 4 + lenR + 1 = 5 + lenR by omega, show 5 + lenR + 1 = 6 + lenR by omega]
  rw [List.extract_eq_take_drop, List.extract_eq_take_drop, Nat.add_sub_cancel_left,
    List.take_of_length_le (l := bs.data.toList.drop (6 + lenR))
      (by rw [List.length_drop, hlen, hsz]; omega)]
  conv => rhs; rw [hl', hd4]
  rw [h0, h2, h4', toUInt8_toNat_eq hR, toUInt8_toNat_eq hS,
    show (2 + lenR + (2 + lenS)).toUInt8 = bs.data.toList[1]! from toUInt8_toNat_eq (by omega)]
  simp

theorem getElem!_append_length (L M : List UInt8) (k : Nat) : (L ++ M)[L.length + k]! = M[k]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem toUInt8_toNat_of_lt {k : Nat} (h : k < 256) : k.toUInt8.toNat = k := by
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow]; exact Nat.mod_eq_of_lt h

/-- **DER decoding inverts encoding** for `r, s < 2²⁵⁶`. -/
theorem ofDER?_toDER (sig : Signature) (hr : sig.r < 2 ^ 256) (hs : sig.s < 2 ^ 256) :
    ofDER? sig.toDER = some sig := by
  obtain ⟨r, s⟩ := sig
  simp only at hr hs
  have p1 := derBody_size_pos r
  have q1 := derBody_size_le hr
  have p2 := derBody_size_pos s
  have q2 := derBody_size_le hs
  have okD1 := derBody_ok r
  have okD2 := derBody_ok s
  have v1 := derBody_val r
  have v2 := derBody_val s
  have hl1 := (ba_size (derBody r)).symm
  have hl2 := (ba_size (derBody s)).symm
  -- the encoding as a list
  have hmk : ∀ a c : UInt8, (ByteArray.mk #[a, c]).size = 2 := fun _ _ => rfl
  have hl : (toDER ⟨r, s⟩).data.toList =
      0x30 :: (2 + (derBody r).size + (2 + (derBody s).size)).toUInt8 :: 2 ::
        (derBody r).size.toUInt8 :: ((derBody r).data.toList ++ 2 ::
          (derBody s).size.toUInt8 :: (derBody s).data.toList) := by
    unfold toDER derInteger
    dsimp only
    simp only [ByteArray.size_append, hmk, ba_append]
    simp
  generalize (derBody r) = D1 at *
  generalize (derBody s) = D2 at *
  generalize hd1 : D1.size = d1 at *
  generalize hd2 : D2.size = d2 at *
  generalize hbs : toDER ⟨r, s⟩ = bs at *
  have hsize : bs.size = d1 + d2 + 6 := by rw [ba_size, hl]; simp; omega
  -- bytes of the header
  have b0 : bs[0]! = 0x30 := by rw [ba_getElem!, hl]; rfl
  have b1 : bs[1]!.toNat = d1 + d2 + 6 - 2 := by
    rw [ba_getElem!, hl]; show (2 + d1 + (2 + d2)).toUInt8.toNat = _
    rw [toUInt8_toNat_of_lt (by omega)]; omega
  have b2 : bs[2]! = 2 := by rw [ba_getElem!, hl]; rfl
  have b3 : bs[3]!.toNat = d1 := by
    rw [ba_getElem!, hl]; show d1.toUInt8.toNat = _; exact toUInt8_toNat_of_lt (by omega)
  have b4 : bs[4 + d1]! = 2 := by
    rw [ba_getElem!, hl, Nat.add_comm 4 d1]
    show (D1.data.toList ++ 2 :: d2.toUInt8 :: D2.data.toList)[d1]! = 2
    rw [← hl1, ← Nat.add_zero D1.data.toList.length, getElem!_append_length]; rfl
  have b5 : bs[5 + d1]!.toNat = d2 := by
    rw [ba_getElem!, hl, Nat.add_comm 5 d1]
    show (D1.data.toList ++ 2 :: d2.toUInt8 :: D2.data.toList)[d1 + 1]!.toNat = _
    rw [← hl1, getElem!_append_length]; exact toUInt8_toNat_of_lt (by omega)
  -- the two integer bodies
  have e1 : bs.extract 4 (4 + d1) = D1 := by
    apply ba_ext
    rw [ba_extract, hl, List.extract_eq_take_drop, Nat.add_sub_cancel_left]
    simp only [List.drop_succ_cons, List.drop_zero]
    rw [List.take_left' hl1]
  have e2 : bs.extract (6 + d1) (d1 + d2 + 6) = D2 := by
    apply ba_ext
    rw [ba_extract, hl, List.extract_eq_take_drop, show d1 + d2 + 6 - (6 + d1) = d2 by omega,
      show 6 + d1 = 4 + (d1 + 2) by omega, ← List.drop_drop]
    simp only [List.drop_succ_cons, List.drop_zero]
    rw [← List.drop_drop, List.drop_left' hl1]
    simp only [List.drop_succ_cons, List.drop_zero]
    rw [List.take_of_length_le (Nat.le_of_eq hl2)]
  have okR : derIntegerOk bs 4 d1 = true := by
    rw [derIntegerOk_iff (by omega), e1]; exact okD1
  have okS : derIntegerOk bs (6 + d1) d2 = true := by
    rw [derIntegerOk_iff (by omega), show 6 + d1 + d2 = d1 + d2 + 6 by omega, e2]; exact okD2
  -- run the parser
  have c1 : ¬(d1 + d2 + 6 < 8) := by omega
  have c2 : ¬(d1 + d2 + 6 > 72) := by omega
  have c3 : ¬(5 + d1 ≥ d1 + d2 + 6) := by omega
  unfold ofDER?
  simp only [hsize, b0, b1, b2, b3, b5, b4, okR, okS, c1, c2, c3, decide_false, Bool.or_false,
    bne_self_eq_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true]
  rw [e1, e2, v1, v2]

end ECDSA.Signature

end Secp256k1
