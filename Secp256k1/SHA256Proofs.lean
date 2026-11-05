import Secp256k1.SHA256Spec
import Secp256k1.DERProofs

/-!
# SHA-256 and HMAC meet their specification

* `SHA256.hash_eq_spec`: `SHA256.hash` computes FIPS 180-4 SHA-256
  (`SHA256.Spec.hash`).
* `SHA256.hmac_eq_spec`: `SHA256.hmac` computes RFC 2104 HMAC-SHA-256
  (`SHA256.Spec.hmac`).

The implementation keeps the message schedule in an array and reads the padded
message from a `ByteArray`; the specification defines `Wₜ` by its recurrence
and works on lists.
-/

namespace Secp256k1.SHA256

open Spec

/-! ## Generic fold lemmas -/

theorem getElem!_push_lt' {b : Array UInt32} {x : UInt32} {t : Nat} (h : t < b.size) :
    (b.push x)[t]! = b[t]! := by
  rw [getElem!_pos (b.push x) t (by rw [Array.size_push]; omega), getElem!_pos b t h,
    Array.getElem_push_lt h]

theorem getElem!_push_size {b : Array UInt32} {x : UInt32} : (b.push x)[b.size]! = x := by
  rw [getElem!_pos (b.push x) b.size (by rw [Array.size_push]; omega), Array.getElem_push_eq]

/-- Folding `b ↦ b.push (g b a)` over `[s, s + n)` extends a prefix of `V`. -/
theorem foldl_push {V : Nat → UInt32} (g : Array UInt32 → Nat → UInt32) (lo hi : Nat)
    (hg : ∀ (b : Array UInt32) (a : Nat), lo ≤ a → a < hi → b.size = a →
      (∀ t < a, b[t]! = V t) → g b a = V a) :
    ∀ (n s : Nat) (b : Array UInt32), lo ≤ s → s + n ≤ hi → b.size = s → (∀ t < s, b[t]! = V t) →
      ((List.range' s n).foldl (fun b a => b.push (g b a)) b).size = s + n ∧
      ∀ t < s + n, ((List.range' s n).foldl (fun b a => b.push (g b a)) b)[t]! = V t := by
  intro n
  induction n with
  | zero => intro s b _ _ hs hb; exact ⟨by simp [hs], by simpa using hb⟩
  | succ n ih =>
    intro s b hlo hhi hs hb
    rw [List.range'_succ, List.foldl_cons]
    have hs' : (b.push (g b s)).size = s + 1 := by rw [Array.size_push, hs]
    have hb' : ∀ t < s + 1, (b.push (g b s))[t]! = V t := by
      intro t ht
      by_cases h : t < s
      · rw [getElem!_push_lt' (hs ▸ h)]; exact hb t h
      · have : t = s := by omega
        subst this
        rw [← hs, getElem!_push_size, hs]
        exact hg b t hlo (by omega) hs hb
    have := ih (s + 1) _ (by omega) (by omega) hs' hb'
    rw [show s + 1 + n = s + (n + 1) by omega] at this
    exact this

/-- A fold simulates another fold through `φ` if each step does. -/
theorem foldl_sim {α β γ : Type} (f : β → α → β) (g : γ → α → γ) (φ : γ → β) (P : α → Prop)
    (h : ∀ c a, P a → f (φ c) a = φ (g c a)) :
    ∀ (l : List α), (∀ a ∈ l, P a) → ∀ c, l.foldl f (φ c) = φ (l.foldl g c)
  | [], _, _ => rfl
  | a :: l, hl, c => by
    rw [List.foldl_cons, List.foldl_cons, h c a (hl a (by simp))]
    exact foldl_sim f g φ P h l (fun x hx => hl x (by simp [hx])) _

/-! ## The compression function -/

theorem sigma0_eq (x : UInt32) : sigma0 x = smallSigma0 x := rfl
theorem sigma1_eq (x : UInt32) : sigma1 x = smallSigma1 x := rfl
theorem Sigma0_eq (x : UInt32) : Sigma0 x = bigSigma0 x := rfl
theorem Sigma1_eq (x : UInt32) : Sigma1 x = bigSigma1 x := rfl
theorem ch_eq (x y z : UInt32) : ((x &&& y) ^^^ (~~~x &&& z)) = Ch x y z := rfl
theorem maj_eq (x y z : UInt32) : ((x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)) = Maj x y z := rfl

/-- **The message schedule array holds `Wₜ`.** -/
theorem schedule_spec (data : ByteArray) (off : Nat) (M : Nat → UInt32)
    (hM : ∀ t < 16, M t = readWord data (off + 4 * t)) :
    ∀ t < 64, (schedule data off)[t]! = W M t := by
  have hWlt : ∀ t < 16, W M t = M t := fun t ht => by rw [W]; simp [ht]
  have hWge : ∀ t, 16 ≤ t → W M t =
      smallSigma1 (W M (t - 2)) + W M (t - 7) + smallSigma0 (W M (t - 15)) + W M (t - 16) :=
    fun t ht => by rw [W]; simp [Nat.not_lt.2 ht]
  have ⟨s1, e1⟩ := foldl_push (V := W M) (fun _ a => readWord data (off + 4 * a)) 0 16
    (fun _ a _ ha _ _ => by rw [hWlt a ha, hM a ha]) 16 0 (Array.mkEmpty 64) (Nat.le_refl _)
    (Nat.le_refl _) rfl (fun t ht => absurd ht (by omega))
  have ⟨_, e2⟩ := foldl_push (V := W M)
    (fun w i => w[i - 16]! + sigma0 w[i - 15]! + w[i - 7]! + sigma1 w[i - 2]!) 16 64
    (fun b a ha _ _ hb => by
      rw [hWge a ha, hb (a - 16) (by omega), hb (a - 15) (by omega), hb (a - 7) (by omega),
        hb (a - 2) (by omega)]
      rw [sigma0_eq, sigma1_eq]
      generalize smallSigma0 (W M (a - 15)) = x
      generalize smallSigma1 (W M (a - 2)) = y
      generalize W M (a - 16) = z
      generalize W M (a - 7) = u
      first | ac_rfl | grind)
    48 16 _ (Nat.le_refl _) (by omega) s1 e1
  intro t ht
  unfold schedule
  simp only [List.range_eq_range']
  exact e2 t ht

/-- The working variables of the implementation and of the specification. -/
def toVars (v : Spec.Vars) : SHA256.Vars := ⟨v.a, v.b, v.c, v.d, v.e, v.f, v.g, v.h⟩

/-- **The compression function computes the specification's**, for a block whose
words are `M`. -/
theorem compress_eq_spec (h : Array UInt32) (data : ByteArray) (off : Nat) (M : Nat → UInt32)
    (hM : ∀ t < 16, M t = readWord data (off + 4 * t)) :
    compress h data off = Spec.compress h M := by
  have hw := schedule_spec data off M hM
  have hsim := foldl_sim (round (schedule data off)) (Spec.round (W M)) toVars (· < 64)
    (fun c a ha => by
      simp only [toVars, round, Spec.round, hw a ha, Sigma0_eq, Sigma1_eq, ch_eq, maj_eq])
    (List.range 64) (fun a ha => List.mem_range.1 ha)
    ⟨h[0]!, h[1]!, h[2]!, h[3]!, h[4]!, h[5]!, h[6]!, h[7]!⟩
  unfold compress Spec.compress
  simp only [toVars] at hsim
  dsimp only
  rw [hsim]
  simp only [UInt32.add_comm]

/-! ## Padding, the hash and HMAC -/

theorem replicate_toList (n : Nat) (b : UInt8) :
    (ByteArray.replicate n b).data.toList = List.replicate n b := Array.toList_replicate

/-- **Padding is FIPS 180-4 §5.1.1 padding.** -/
theorem pad_eq_spec (msg : ByteArray) : (pad msg).data.toList = Spec.padding msg.data.toList := by
  unfold pad Spec.padding Spec.bigEndian
  have hz : (120 - (msg.data.toList.length + 1) % 64) % 64 = (119 - msg.data.toList.length % 64) % 64 := by
    omega
  rw [ba_append, ba_append, ByteArray.data_push, Array.toList_push, replicate_toList,
    ByteArray.size_push, ba_size msg, Nat.mul_comm, hz]

theorem output_toList (l : List UInt32) (out : ByteArray) :
    (l.foldl (fun out (w : UInt32) => out.push (w >>> 24).toUInt8 |>.push (w >>> 16).toUInt8
      |>.push (w >>> 8).toUInt8 |>.push w.toUInt8) out).data.toList =
      out.data.toList ++ l.flatMap wordBytes := by
  induction l generalizing out with
  | nil => simp
  | cons w l ih =>
    rw [List.foldl_cons, ih]
    simp [ByteArray.data_push, wordBytes]

/-- **`SHA256.hash` is FIPS 180-4 SHA-256.** -/
theorem hash_eq_spec (msg : ByteArray) : (hash msg).data.toList = Spec.hash msg.data.toList := by
  have hP := pad_eq_spec msg
  unfold hash Spec.hash
  dsimp only
  have hstate : (List.range ((pad msg).size / blockSize)).foldl
      (fun st i => compress st (pad msg) (blockSize * i)) H0 =
      (List.range ((Spec.padding msg.data.toList).length / 64)).foldl
        (fun H i => Spec.compress H (blockWord (Spec.padding msg.data.toList) i)) H0 := by
    rw [ba_size, hP]
    congr 1
    funext H i
    apply compress_eq_spec
    intro t _
    simp only [blockWord, word, readWord, ba_getElem!, hP, blockSize]
  rw [hstate, ← Array.foldl_toList, output_toList]
  rfl

/-- **`SHA256.hmac` is RFC 2104 HMAC-SHA-256.** -/
theorem hmac_eq_spec (key msg : ByteArray) :
    (hmac key msg).data.toList = Spec.hmac key.data.toList msg.data.toList := by
  unfold hmac Spec.hmac
  dsimp only
  have hk : (if key.size > blockSize then hash key else key).data.toList =
      if key.data.toList.length > 64 then Spec.hash key.data.toList else key.data.toList := by
    rw [← ba_size]
    split <;> rename_i h <;> simp only [blockSize] at h <;> simp [h, hash_eq_spec]
  generalize hK : (if key.size > blockSize then hash key else key) = K at hk ⊢
  generalize hK' : (if key.data.toList.length > 64 then Spec.hash key.data.toList
    else key.data.toList) = K' at hk ⊢
  have hpad : (K ++ ByteArray.replicate (blockSize - K.size) 0).data.toList =
      K' ++ List.replicate (64 - K'.length) 0 := by
    rw [ba_append, replicate_toList, hk, ba_size K, hk]; rfl
  rw [hash_eq_spec, ba_append, hash_eq_spec, ba_append]
  simp only [Array.toList_map, hpad]

end Secp256k1.SHA256
