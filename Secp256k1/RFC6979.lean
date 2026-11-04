import Secp256k1.Bytes
import Secp256k1.Field
import Secp256k1.SHA256

/-!
# Deterministic nonces (RFC 6979)

Deterministic generation of the ECDSA nonce `k` with HMAC-SHA-256
(RFC 6979 §3.2), specialised to `qlen = hlen = 256`.

Optional additional data (RFC 6979 §3.6) is appended after `bits2octets(h₁)`
in steps (d) and (f), which matches the `ndata` argument of libsecp256k1's
`secp256k1_nonce_function_rfc6979`.
-/

namespace Secp256k1.RFC6979

open SHA256 (hmac)

/-- `bits2int` (RFC 6979 §2.3.2): the leftmost 256 bits of `h` as an integer. -/
def bits2int (h : ByteArray) : Nat :=
  let x := bytesToNat h
  let blen := h.size * 8
  if blen > 256 then x >>> (blen - 256) else x

/-- `int2octets` (RFC 6979 §2.3.3) for `rlen = 256`. -/
def int2octets (x : Nat) : ByteArray := natToBytes x 32

/-- `bits2octets` (RFC 6979 §2.3.4): `int2octets(bits2int(h) mod n)`. -/
def bits2octets (h : ByteArray) : ByteArray := int2octets (bits2int h % n)

/-- The HMAC-DRBG state `(K, V)` of RFC 6979 §3.2. -/
structure State where
  K : ByteArray
  V : ByteArray

/-- Steps (b)–(g): seed the generator with the private key `x`, the message
hash `h₁` and optional additional data. -/
def init (x : Nat) (h₁ : ByteArray) (extra : ByteArray := .empty) : State :=
  let seed := int2octets x ++ bits2octets h₁ ++ extra
  let V := ByteArray.replicate 32 0x01
  let K := ByteArray.replicate 32 0x00
  let K := hmac K (V.push 0x00 ++ seed)
  let V := hmac K V
  let K := hmac K (V.push 0x01 ++ seed)
  let V := hmac K V
  ⟨K, V⟩

/-- Step (h.1)–(h.3): produce the next candidate `k = bits2int(T)` with
`T = V := HMAC_K(V)` (a single block suffices since `qlen = hlen`). -/
def State.generate (st : State) : Nat × State :=
  let V := hmac st.K st.V
  (bits2int V, { st with V })

/-- Step (h.3), rejection branch: `K := HMAC_K(V ‖ 0x00)`, `V := HMAC_K(V)`. -/
def State.reseed (st : State) : State :=
  let K := hmac st.K (st.V.push 0x00)
  ⟨K, hmac K st.V⟩

/-- Run the candidate loop of step (h): return the first `accept k` that
succeeds, reseeding after every rejected candidate. At most `fuel` candidates
are tried; each rejection happens with probability `< 2⁻¹²⁷`, so the default
fuel is never exhausted in practice. -/
def findNonce {α : Type} (accept : Nat → Option α) : (fuel : Nat) → State → Option α
  | 0, _ => none
  | fuel + 1, st =>
    let (k, st) := st.generate
    match accept k with
    | some a => some a
    | none => findNonce accept fuel st.reseed

/-- The RFC 6979 nonce for private key `x` and message hash `h₁`: the first
candidate in `[1, n-1]`. -/
def nonce? (x : Nat) (h₁ : ByteArray) (extra : ByteArray := .empty) (fuel : Nat := 64) :
    Option Nat :=
  findNonce (fun k => if 0 < k ∧ k < n then some k else none) fuel (init x h₁ extra)

end Secp256k1.RFC6979
