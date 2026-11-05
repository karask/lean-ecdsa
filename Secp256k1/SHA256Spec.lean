import Secp256k1.Bytes
import Secp256k1.SHA256

/-!
# SHA-256 and HMAC: specification

A direct transcription of FIPS 180-4 (SHA-256) and RFC 2104 (HMAC) on lists of
bytes, written for reading rather than speed. Section numbers refer to
FIPS 180-4. `Secp256k1.SHA256Proofs` proves that `SHA256.hash` and
`SHA256.hmac` compute exactly these functions.

The constants are checked against their definitions: `K_spec` and `H0_spec`
show that `SHA256.K` and `SHA256.H0` are the first 32 bits of the fractional
parts of the cube roots of the first 64 primes, and of the square roots of the
first 8 primes.
-/

namespace Secp256k1.SHA256.Spec

/-! ## §3.2, §4.1.2: operations and functions on 32-bit words -/

/-- Rotate right: `ROTRⁿ(x) = (x >> n) ∨ (x << w - n)`. -/
def ROTR (n : UInt32) (x : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- Shift right: `SHRⁿ(x) = x >> n`. -/
def SHR (n : UInt32) (x : UInt32) : UInt32 := x >>> n

def Ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (~~~x &&& z)

def Maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- `Σ₀²⁵⁶`. -/
def bigSigma0 (x : UInt32) : UInt32 := ROTR 2 x ^^^ ROTR 13 x ^^^ ROTR 22 x

/-- `Σ₁²⁵⁶`. -/
def bigSigma1 (x : UInt32) : UInt32 := ROTR 6 x ^^^ ROTR 11 x ^^^ ROTR 25 x

/-- `σ₀²⁵⁶`. -/
def smallSigma0 (x : UInt32) : UInt32 := ROTR 7 x ^^^ ROTR 18 x ^^^ SHR 3 x

/-- `σ₁²⁵⁶`. -/
def smallSigma1 (x : UInt32) : UInt32 := ROTR 17 x ^^^ ROTR 19 x ^^^ SHR 10 x

/-! ## §5.1.1: padding -/

/-- The 64-bit big-endian encoding of `x` (`I2OSP(x, 8)`, see `bytesToNat_natToBytes`). -/
def bigEndian (x len : Nat) : List UInt8 := (natToBytes x len).data.toList

/-- Append the bit `1` (the byte `0x80`), then `k` zero bits with
`ℓ + 1 + k ≡ 448 (mod 512)` (here a whole number of zero bytes), then the
message length `ℓ` in bits as a 64-bit big-endian integer. -/
def padding (M : List UInt8) : List UInt8 :=
  M ++ [0x80] ++ List.replicate ((119 - M.length % 64) % 64) 0 ++ bigEndian (8 * M.length) 8

/-! ## §5.2.1, §6.2.2: parsing, message schedule and hash computation -/

/-- A 32-bit word from four bytes, most significant first. -/
def word (b₀ b₁ b₂ b₃ : UInt8) : UInt32 :=
  (b₀.toUInt32 <<< 24) ||| (b₁.toUInt32 <<< 16) ||| (b₂.toUInt32 <<< 8) ||| b₃.toUInt32

/-- Word `t` (`0 ≤ t < 16`) of message block `i` of the padded message `P`. -/
def blockWord (P : List UInt8) (i t : Nat) : UInt32 :=
  let o := 64 * i + 4 * t
  word P[o]! P[o + 1]! P[o + 2]! P[o + 3]!

/-- The message schedule `W₀, …, W₆₃` of a block with words `M`. -/
def W (M : Nat → UInt32) (t : Nat) : UInt32 :=
  if t < 16 then M t
  else smallSigma1 (W M (t - 2)) + W M (t - 7) + smallSigma0 (W M (t - 15)) + W M (t - 16)
termination_by t
decreasing_by all_goals omega

/-- The working variables `a, …, h`. -/
structure Vars where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32

/-- Round `t` of step 3. -/
def round (Wt : Nat → UInt32) (v : Vars) (t : Nat) : Vars :=
  let T₁ := v.h + bigSigma1 v.e + Ch v.e v.f v.g + SHA256.K[t]! + Wt t
  let T₂ := bigSigma0 v.a + Maj v.a v.b v.c
  ⟨T₁ + T₂, v.a, v.b, v.c, v.d + T₁, v.e, v.f, v.g⟩

/-- Steps 1–4 for one block: the new intermediate hash value from `H` and the
block's words `M`. -/
def compress (H : Array UInt32) (M : Nat → UInt32) : Array UInt32 :=
  let v := (List.range 64).foldl (round (W M)) ⟨H[0]!, H[1]!, H[2]!, H[3]!, H[4]!, H[5]!, H[6]!, H[7]!⟩
  #[v.a + H[0]!, v.b + H[1]!, v.c + H[2]!, v.d + H[3]!,
    v.e + H[4]!, v.f + H[5]!, v.g + H[6]!, v.h + H[7]!]

/-- The four bytes of a word, most significant first. -/
def wordBytes (x : UInt32) : List UInt8 :=
  [(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

/-- **SHA-256**: pad, process the `N` blocks starting from `H⁽⁰⁾`, and output
`H⁽ᴺ⁾₀ ‖ … ‖ H⁽ᴺ⁾₇`. -/
def hash (M : List UInt8) : List UInt8 :=
  let P := padding M
  let H := (List.range (P.length / 64)).foldl (fun H i => compress H (blockWord P i)) SHA256.H0
  H.toList.flatMap wordBytes

/-! ## RFC 2104: HMAC -/

/-- **HMAC-SHA-256**: `H((K' ⊕ opad) ‖ H((K' ⊕ ipad) ‖ text))`, where `K'` is the
key, first hashed if it is longer than the block size, then padded with zeros
to 64 bytes. -/
def hmac (key text : List UInt8) : List UInt8 :=
  let key := if key.length > 64 then hash key else key
  let key := key ++ List.replicate (64 - key.length) 0
  hash (key.map (· ^^^ 0x5c) ++ hash (key.map (· ^^^ 0x36) ++ text))

/-! ## §4.2.2, §5.3.3: the constants -/

/-- The first 64 primes. -/
def primes : List Nat := (List.range 312).filter fun m => 2 ≤ m ∧ ∀ d ∈ List.range m, 2 ≤ d → m % d ≠ 0

/-- `⌊a^(1/k)⌋` by bisection (for `a < 2^(16k)`). -/
def iroot (k a : Nat) : Nat := go 64 0 (2 ^ 64)
where
  go : Nat → Nat → Nat → Nat
    | 0, lo, _ => lo
    | fuel + 1, lo, hi =>
      if hi ≤ lo + 1 then lo
      else
        let mid := (lo + hi) / 2
        if mid ^ k ≤ a then go fuel mid hi else go fuel lo mid

theorem primes_length : primes.length = 64 := by decide +kernel

/-- `K` holds the first 32 bits of the fractional parts of the cube roots of
the first 64 primes: `K[i] = ⌊∛p · 2³²⌋ mod 2³² = ⌊∛(p · 2⁹⁶)⌋ mod 2³²`, where
`⌊∛(p · 2⁹⁶)⌋` is pinned down by the two inequalities. -/
theorem K_spec : ∀ i < 64,
    let p := primes[i]!
    let c := iroot 3 (p * 2 ^ 96)
    c ^ 3 ≤ p * 2 ^ 96 ∧ p * 2 ^ 96 < (c + 1) ^ 3 ∧ (SHA256.K[i]!).toNat = c % 2 ^ 32 := by
  decide +kernel

/-- `H⁽⁰⁾` holds the first 32 bits of the fractional parts of the square roots
of the first 8 primes. -/
theorem H0_spec : ∀ i < 8,
    let p := primes[i]!
    let c := iroot 2 (p * 2 ^ 64)
    c ^ 2 ≤ p * 2 ^ 64 ∧ p * 2 ^ 64 < (c + 1) ^ 2 ∧ (SHA256.H0[i]!).toNat = c % 2 ^ 32 := by
  decide +kernel

theorem K_size : SHA256.K.size = 64 := by decide

theorem H0_size : SHA256.H0.size = 8 := by decide

end Secp256k1.SHA256.Spec
