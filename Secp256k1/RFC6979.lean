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

The private key and the candidate nonces are handled only as byte arrays
(never as `Nat`), so that their values do not influence the running time.
Only the public message hash goes through `Nat` (in `bits2octets`).
-/

namespace Secp256k1.RFC6979

open SHA256 (hmac)

/-- `bits2int` (RFC 6979 §2.3.2): the leftmost 256 bits of `h` as an integer.
**Public values only.** -/
def bits2int (h : ByteArray) : Nat :=
  let x := bytesToNat h
  let blen := h.size * 8
  if blen > 256 then x >>> (blen - 256) else x

/-- `bits2octets` (RFC 6979 §2.3.4): `int2octets(bits2int(h) mod n)`.
**Public values only** (applied to the message hash). -/
def bits2octets (h : ByteArray) : ByteArray := natToBytes (bits2int h % n) 32

/-- The HMAC-DRBG state `(K, V)` of RFC 6979 §3.2. -/
structure State where
  K : ByteArray
  V : ByteArray

/-- Steps (b)–(g): seed the generator with `x = int2octets(d)` (the 32-byte
private key), the message hash `h₁` and optional additional data. -/
def init (x : ByteArray) (h₁ : ByteArray) (extra : ByteArray := .empty) : State :=
  let seed := x ++ bits2octets h₁ ++ extra
  let V := ByteArray.replicate 32 0x01
  let K := ByteArray.replicate 32 0x00
  let K := hmac K (V.push 0x00 ++ seed)
  let V := hmac K V
  let K := hmac K (V.push 0x01 ++ seed)
  let V := hmac K V
  ⟨K, V⟩

/-- Steps (h.1)–(h.2): produce the next candidate `T = V := HMAC_K(V)`
(32 bytes; a single block suffices since `qlen = hlen`, and then
`bits2int(T)` is just the big-endian value of `T`). -/
def State.generate (st : State) : ByteArray × State :=
  let V := hmac st.K st.V
  (V, { st with V })

/-- Step (h.3), rejection branch: `K := HMAC_K(V ‖ 0x00)`, `V := HMAC_K(V)`. -/
def State.reseed (st : State) : State :=
  let K := hmac st.K (st.V.push 0x00)
  ⟨K, hmac K st.V⟩

/-- Run the candidate loop of step (h): return the first `accept T` that
succeeds, reseeding after every rejected candidate. At most `fuel` candidates
are tried; each rejection happens with probability `< 2⁻¹²⁷`, so the default
fuel is never exhausted in practice. -/
def findNonce {α : Type} (accept : ByteArray → Option α) : (fuel : Nat) → State → Option α
  | 0, _ => none
  | fuel + 1, st =>
    let (T, st) := st.generate
    match accept T with
    | some a => some a
    | none => findNonce accept fuel st.reseed

end Secp256k1.RFC6979
