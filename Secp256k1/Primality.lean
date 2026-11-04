import Secp256k1.Field

/-!
# Primality certificates

A self-contained proof of the **Lucas primality test** (no Mathlib), used with
Pratt certificates to prove that the field prime `p` and the group order `n`
are prime, and that Fermat's little theorem holds for them.

**Lucas test.** Let `N > 1` and let `N - 1 = ∏ qᵢ^eᵢ` with every `qᵢ` prime.
If `a^(N-1) ≡ 1 (mod N)` and `a^((N-1)/qᵢ) ≢ 1 (mod N)` for every `i`, then

* every `x` with `0 < x < N` satisfies `x^(N-1) ≡ 1 (mod N)`, and
* `N` is prime.

**Proof sketch.**
1. If `a^k ≡ 1` for some `0 < k < N - 1`, then `g = gcd(k, N - 1)` also has
   `a^g ≡ 1` (Euclid's algorithm on exponents), and `g` is a proper divisor of
   `N - 1`. So some `qᵢ` divides `(N - 1)/g`, giving `a^((N-1)/qᵢ) ≡ 1`, a
   contradiction.
2. `a` is a unit (`a · a^(N-2) ≡ 1`), so step 1 makes `a⁰, …, a^(N-2)` pairwise
   distinct and non-zero modulo `N`.
3. These are `N - 1` distinct values in `[1, N - 1]`, so they are all of
   `[1, N - 1]` (pigeonhole, `List.Nodup.length_le_of_subset`).
4. Hence every `0 < x < N` is a power of `a`, so `x^(N-1) ≡ 1`, and `x` is a
   unit, which is impossible for a proper divisor of `N`.

`powMod_eq` shows that the `powMod` used to evaluate certificates computes
`b^e mod m`, so certificates can be checked by `decide`.
-/

namespace Secp256k1

/-! ## Modular exponentiation -/

theorem pow_step_one (v α e i : Nat) (hb : e / 2 ^ i % 2 = 1) :
    (v * v * α) ^ 2 ^ i * α ^ (e % 2 ^ i) = v ^ 2 ^ (i + 1) * α ^ (e % 2 ^ (i + 1)) := by
  rw [Nat.mod_pow_succ, hb, Nat.mul_one, Nat.pow_succ 2 i, Nat.pow_mul, Nat.pow_two,
    Nat.pow_add, Nat.mul_pow, Nat.mul_pow]
  ac_rfl

theorem pow_step_zero (v α e i : Nat) (hb : e / 2 ^ i % 2 = 0) :
    (v * v) ^ 2 ^ i * α ^ (e % 2 ^ i) = v ^ 2 ^ (i + 1) * α ^ (e % 2 ^ (i + 1)) := by
  rw [Nat.mod_pow_succ, hb, Nat.mul_zero, Nat.pow_succ 2 i, Nat.pow_mul,
    Nat.pow_two, Nat.mul_pow, Nat.add_zero]

theorem pow_mul_mod_congr {x y m : Nat} (k c : Nat) (h : x % m = y % m) :
    x ^ k * c % m = y ^ k * c % m := by
  rw [Nat.mul_mod, Nat.pow_mod, h, ← Nat.pow_mod, ← Nat.mul_mod]

theorem powMod_go_eq (b e m : Nat) (hm : 0 < m) :
    ∀ (i acc : Nat), acc < m → powMod.go b e m i acc = acc ^ 2 ^ i * b ^ (e % 2 ^ i) % m
  | 0, acc, h => by
    simp only [powMod.go, Nat.pow_zero, Nat.pow_one, Nat.mod_one, Nat.mul_one,
      Nat.mod_eq_of_lt h]
  | i + 1, acc, h => by
    simp only [powMod.go]
    by_cases hb : e.testBit i = true
    · simp only [hb, ↓reduceIte]
      rw [powMod_go_eq b e m hm i _ (Nat.mod_lt _ hm),
        pow_mul_mod_congr _ _ (y := acc * acc * b) (by
          rw [Nat.mod_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_mod (acc * acc),
            Nat.mod_mod, ← Nat.mul_mod]),
        pow_step_one acc b e i (by simpa [Nat.testBit_eq_decide_div_mod_eq] using hb)]
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      have hb' : e / 2 ^ i % 2 = 0 := by
        simp [Nat.testBit_eq_decide_div_mod_eq] at hb; omega
      rw [powMod_go_eq b e m hm i _ (Nat.mod_lt _ hm),
        pow_mul_mod_congr _ _ (y := acc * acc) (Nat.mod_mod _ _), pow_step_zero acc b e i hb']

/-- `powMod` computes modular exponentiation. -/
theorem powMod_eq (b e m : Nat) (hm : 0 < m) : powMod b e m = b ^ e % m := by
  unfold powMod
  rw [powMod_go_eq b e m hm _ _ (Nat.mod_lt _ hm),
    pow_mul_mod_congr _ _ (y := 1) (Nat.mod_mod _ _), Nat.one_pow, Nat.one_mul,
    Nat.mod_eq_of_lt Nat.lt_log2_self]

/-! ## Primes and factorisations -/

/-- `q` is prime: at least 2, and its only divisors are 1 and itself. -/
def IsPrime (q : Nat) : Prop := 2 ≤ q ∧ ∀ d, d ∣ q → d = 1 ∨ d = q

/-- Every element of a list is prime. -/
inductive AllPrime : List Nat → Prop
  | nil : AllPrime []
  | cons {q : Nat} {qs : List Nat} : IsPrime q → AllPrime qs → AllPrime (q :: qs)

theorem AllPrime.mem {l : List Nat} (h : AllPrime l) : ∀ q ∈ l, IsPrime q := by
  induction h with
  | nil => intro q hq; cases hq
  | cons hq _ ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hq
    · exact ih r hr

theorem prime_two : IsPrime 2 := by
  refine ⟨Nat.le_refl 2, fun d hd => ?_⟩
  have := Nat.le_of_dvd (by decide) hd
  have : d ≠ 0 := by rintro rfl; simp at hd
  omega

/-- `∏ qᵢ^eᵢ` for a list of pairs `(qᵢ, eᵢ)`. -/
def factorProd : List (Nat × Nat) → Nat
  | [] => 1
  | (q, e) :: fs => q ^ e * factorProd fs

/-- A divisor `k > 1` of `∏ qᵢ^eᵢ` (all `qᵢ` prime) is divisible by some `qᵢ`. -/
theorem exists_prime_dvd {k : Nat} (hk : 1 < k) :
    ∀ (fs : List (Nat × Nat)), AllPrime (fs.map Prod.fst) → k ∣ factorProd fs →
      ∃ q ∈ fs.map Prod.fst, q ∣ k
  | [], _, h => by simp [factorProd] at h; omega
  | (q, e) :: fs, hp, h => by
    cases hp with
    | cons hq hrest =>
      rcases hq.2 (Nat.gcd k q) (Nat.gcd_dvd_right k q) with h1 | hq'
      · have hc : Nat.Coprime k (q ^ e) := Nat.Coprime.pow_right e h1
        obtain ⟨r, hr, hrk⟩ := exists_prime_dvd hk fs hrest
          (hc.dvd_of_dvd_mul_left (by simpa [factorProd] using h))
        exact ⟨r, List.mem_cons_of_mem _ hr, hrk⟩
      · have hg : Nat.gcd k q = q := hq'
        exact ⟨q, List.mem_cons_self .., hg ▸ Nat.gcd_dvd_left k q⟩

/-! ## The Lucas test -/

/-- Exponents `e` with `a^e ≡ 1` are closed under `gcd`. -/
theorem pow_gcd_eq_one {a N : Nat} (hN : 1 < N) (m n : Nat) :
    a ^ m % N = 1 → a ^ n % N = 1 → a ^ Nat.gcd m n % N = 1 := by
  induction m, n using Nat.gcd.induction with
  | H0 n => intro _ hn; simpa using hn
  | H1 m n _ ih =>
    intro hm hn
    rw [Nat.gcd_rec]
    apply ih _ hm
    have : a ^ n = (a ^ m) ^ (n / m) * a ^ (n % m) := by
      rw [← Nat.pow_mul, ← Nat.pow_add, Nat.div_add_mod]
    rw [this, Nat.mul_mod, Nat.pow_mod, hm, Nat.one_pow, Nat.mod_eq_of_lt hN, Nat.one_mul,
      Nat.mod_mod] at hn
    exact hn

/-- The hypotheses of the Lucas test. -/
structure LucasCert (N a : Nat) (fs : List (Nat × Nat)) : Prop where
  one_lt : 1 < N
  prod : factorProd fs = N - 1
  primes : AllPrime (fs.map Prod.fst)
  full : a ^ (N - 1) % N = 1
  part : ∀ q ∈ fs.map Prod.fst, a ^ ((N - 1) / q) % N ≠ 1

namespace LucasCert

variable {N a : Nat} {fs : List (Nat × Nat)} (c : LucasCert N a fs)
include c

/-- Step 1: no exponent `0 < k < N - 1` gives `a^k ≡ 1`. -/
theorem no_small_order : ∀ k, 0 < k → k < N - 1 → a ^ k % N ≠ 1 := by
  intro k hk0 hk hak
  have hg := pow_gcd_eq_one c.one_lt k (N - 1) hak c.full
  generalize hgdef : Nat.gcd k (N - 1) = g at hg
  have hgle : g ≤ k := hgdef ▸ Nat.gcd_le_left _ hk0
  obtain ⟨d, hd⟩ : g ∣ N - 1 := hgdef ▸ Nat.gcd_dvd_right _ _
  have hd1 : 1 < d := by
    rcases d with _ | _ | d
    · omega
    · omega
    · omega
  obtain ⟨q, hq, r, hr⟩ := exists_prime_dvd hd1 fs c.primes
    (c.prod ▸ ⟨g, by rw [hd, Nat.mul_comm]⟩)
  have hq0 : 0 < q := by have := (c.primes.mem q hq).1; omega
  have hdiv : (N - 1) / q = g * r := by
    rw [hd, hr, Nat.mul_left_comm, Nat.mul_div_cancel_left _ hq0]
  apply c.part q hq
  rw [hdiv, Nat.pow_mul, Nat.pow_mod, hg, Nat.one_pow, Nat.mod_eq_of_lt c.one_lt]

/-- `a · a^(N-2) ≡ 1`. -/
theorem unit : a * a ^ (N - 2) % N = 1 := by
  have h := c.full
  have hN := c.one_lt
  rwa [show N - 1 = (N - 2) + 1 by omega, Nat.pow_succ, Nat.mul_comm] at h

/-- `a^i · (a^(N-2))^i ≡ 1`. -/
theorem unit_pow (i : Nat) : a ^ i * (a ^ (N - 2)) ^ i % N = 1 := by
  rw [← Nat.mul_pow, Nat.pow_mod, c.unit, Nat.one_pow, Nat.mod_eq_of_lt c.one_lt]

/-- Step 2: the powers `a^0, …, a^(N-2)` are pairwise distinct modulo `N`. -/
theorem pow_inj {i j : Nat} (hij : i < j) (hj : j < N - 1) : a ^ i % N ≠ a ^ j % N := by
  intro h
  apply c.no_small_order (j - i) (by omega) (by omega)
  have hb := c.unit_pow i
  calc a ^ (j - i) % N = a ^ (j - i) * (a ^ i * (a ^ (N - 2)) ^ i % N) % N := by
        rw [hb, Nat.mul_one]
    _ = a ^ j * (a ^ (N - 2)) ^ i % N := by
        rw [Nat.mul_mod_mod, ← Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    _ = a ^ i * (a ^ (N - 2)) ^ i % N := by rw [Nat.mul_mod, ← h, ← Nat.mul_mod]
    _ = 1 := hb

theorem pow_ne_zero (i : Nat) : a ^ i % N ≠ 0 := by
  intro h
  have hb := c.unit_pow i
  rw [Nat.mul_mod, h, Nat.zero_mul, Nat.zero_mod] at hb
  exact absurd hb (by decide)

/-- Step 3 (pigeonhole): every `0 < x < N` is a power of `a` modulo `N`. -/
theorem exists_pow (x : Nat) (hx0 : 0 < x) (hxN : x < N) : ∃ i, a ^ i % N = x := by
  let l := (List.range (N - 1)).map (fun i => a ^ i % N)
  have hnd : l.Nodup := by
    refine List.pairwise_map.mpr (List.pairwise_lt_range.imp_of_mem ?_)
    intro i j _ hj hij
    exact c.pow_inj hij (List.mem_range.mp hj)
  by_cases hmem : x ∈ l
  · obtain ⟨i, _, hi⟩ := List.mem_map.mp hmem
    exact ⟨i, hi⟩
  · exfalso
    have hnd' : (x :: l).Nodup := List.nodup_cons.mpr ⟨hmem, hnd⟩
    have hsub : (x :: l) ⊆ List.range' 1 (N - 1) := by
      intro y hy
      rw [List.mem_range']
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨y - 1, by omega, by omega⟩
      · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
        have h1 := c.pow_ne_zero i
        have h2 : a ^ i % N < N := Nat.mod_lt _ (by have := c.one_lt; omega)
        exact ⟨a ^ i % N - 1, by omega, by omega⟩
    have := List.Nodup.length_le_of_subset hnd' hsub
    simp [l, List.length_range'] at this
    omega

/-- **Fermat's little theorem** for `N`. -/
theorem fermat (x : Nat) (hx0 : 0 < x) (hxN : x < N) : x ^ (N - 1) % N = 1 := by
  obtain ⟨i, rfl⟩ := c.exists_pow x hx0 hxN
  rw [← Nat.pow_mod, ← Nat.pow_mul, Nat.mul_comm, Nat.pow_mul, Nat.pow_mod, c.full,
    Nat.one_pow, Nat.mod_eq_of_lt c.one_lt]

/-- **`N` is prime.** -/
theorem isPrime : IsPrime N := by
  refine ⟨c.one_lt, fun d hd => ?_⟩
  have hN := c.one_lt
  have hdle := Nat.le_of_dvd (by omega) hd
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd; omega
  by_cases hdN : d = N
  · exact Or.inr hdN
  · left
    obtain ⟨i, hi⟩ := c.exists_pow d (by omega) (by omega)
    have hu := c.unit_pow i
    rw [Nat.mul_mod, hi, Nat.mul_mod_mod] at hu
    have : d ∣ d * (a ^ (N - 2)) ^ i % N :=
      (Nat.dvd_mod_iff hd).mpr (Nat.dvd_mul_right d _)
    rw [hu] at this
    exact Nat.eq_one_of_dvd_one this

end LucasCert

/-- A Lucas certificate as a Boolean, so that it can be checked by `decide`. -/
def lucasCheck (N a : Nat) (fs : List (Nat × Nat)) : Bool :=
  decide (1 < N) && factorProd fs == N - 1 && powMod a (N - 1) N == 1 &&
    (fs.map Prod.fst).all (fun q => powMod a ((N - 1) / q) N != 1)

theorem LucasCert.of_check {N a : Nat} {fs : List (Nat × Nat)} (h : lucasCheck N a fs = true)
    (hp : AllPrime (fs.map Prod.fst)) : LucasCert N a fs := by
  simp only [lucasCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨hN, hprod⟩, hfull⟩, hpart⟩ := h
  have hN0 : 0 < N := by omega
  refine ⟨hN, hprod, hp, ?_, ?_⟩
  · rw [← powMod_eq _ _ _ hN0]; exact hfull
  · intro q hq; rw [← powMod_eq _ _ _ hN0]; exact hpart q hq

end Secp256k1
