import Secp256k1

/-!
# Timing leakage check (dudect-style)

Run with `lake exe timing [samples]`.

For each operation, inputs are drawn from two classes, interleaved
pseudo-randomly: a *fixed* secret with extreme shape (`k = 1`: 255 leading
zero bits, Hamming weight 1) and *random* secrets. Each call is timed
individually and Welch's t-statistic compares the two timing distributions
(after discarding the slowest 10% of samples, which are mostly scheduler
noise). Following dudect (Reparaz, Balasch, Verbauwhede 2017), `|t| > 4.5`
is evidence that timing depends on the secret.

The variable-time reference scalar multiplication is included as a positive
control: it should fail by a wide margin, showing that the test can detect
the leak it is looking for.

A passing result is evidence, not proof: it covers one machine, one build
and the input classes tried here.
-/

open Secp256k1

namespace Timing

/-- Running mean and variance (Welford). -/
structure Stats where
  count : Nat := 0
  mean : Float := 0
  m2 : Float := 0

def Stats.push (s : Stats) (x : Float) : Stats :=
  let count := s.count + 1
  let d := x - s.mean
  let mean := s.mean + d / count.toFloat
  { count, mean, m2 := s.m2 + d * (x - mean) }

def Stats.variance (s : Stats) : Float := s.m2 / (s.count - 1).toFloat

/-- Welch's t-statistic. -/
def welch (a b : Stats) : Float :=
  (a.mean - b.mean) / Float.sqrt (a.variance / a.count.toFloat + b.variance / b.count.toFloat)

def prng (i : Nat) : Nat := bytesToNat (SHA256.hash (natToBytes i 8))

/-- Time `f` on `samples` inputs. Returns `(class, nanoseconds)` pairs.

Inputs are prepared (including any conversion from `Nat`) before the clock
starts. The input is read from a reference after the first clock read and the
result is written to a sink before the second, so the computation cannot be
moved out of the timed region. -/
def measure {α : Type} [Inhabited α] (f : α → UInt64) (samples : Nat) (fixed : α)
    (random : Nat → α) : IO (Array (Bool × Nat)) := do
  let input ← IO.mkRef (default : α)
  let sink ← IO.mkRef (0 : UInt64)
  let mut out := Array.mkEmpty samples
  for i in [0:samples] do
    let isFixed := prng (10 * i + 1) % 2 == 0
    input.set (if isFixed then fixed else random (prng (10 * i + 2) % n))
    let t0 ← IO.monoNanosNow
    let k ← input.get
    let r := f k
    sink.modify (· ^^^ r)
    let t1 ← IO.monoNanosNow
    out := out.push (isFixed, t1 - t0)
  -- Keep the sink observable.
  if (← sink.get) == 0xDEADBEEF then IO.println ""
  return out

/-- Welch's t over the samples below the given percentile of all samples. -/
def tStat (data : Array (Bool × Nat)) (percentile : Float) : Float × Float × Float :=
  let sorted := (data.map (·.2)).qsort (· < ·)
  let cutoff := sorted[(percentile * sorted.size.toFloat).toUInt64.toNat]!
  let (a, b) := data.foldl (init := (({} : Stats), ({} : Stats))) fun (a, b) (fixed, t) =>
    if t > cutoff then (a, b)
    else if fixed then (a.push t.toFloat, b) else (a, b.push t.toFloat)
  (a.mean, b.mean, welch a b)

def report {α : Type} [Inhabited α] (name : String) (f : α → UInt64) (ofNat : Nat → α)
    (samples : Nat) (expectLeak : Bool) : IO Bool := do
  -- Warm up (fills caches and the base-point table).
  let _ ← measure f 50 (ofNat 1) ofNat
  let data ← measure f samples (ofNat 1) ofNat
  let (fixedMean, randomMean, t) := tStat data 0.9
  let leak := t.abs > 4.5
  let verdict := if leak then "LEAK" else "no leak detected"
  let fmt (x : Float) : String :=
    let v := (x * 10).round.toUInt64
    s!"{v / 10}.{v % 10}"
  IO.println s!"{name}: fixed {fmt (fixedMean / 1000)} µs, random \
    {fmt (randomMean / 1000)} µs, |t| = {fmt t.abs} → {verdict}\
    {if expectLeak then " (expected: positive control)" else ""}"
  return leak == expectLeak

end Timing

open Timing in
def main (args : List String) : IO UInt32 := do
  let samples := (args.head? >>= String.toNat?).getD 2000
  IO.println s!"{samples} samples per operation, classes: fixed k = 1 vs random k"
  let some sk := ECDSA.PrivateKey.ofNat? 0xC0FFEE | return 1
  let smulRef (k : Nat) : UInt64 :=
    (Jacobian.smul k (Jacobian.ofPoint G)).X.val.toUInt64
  let smulCT (k : CT.Scalar) : UInt64 :=
    let (x, _, _) := (CT.PPoint.smulG k).toAffine
    x.mont.l0
  let invCT (k : CT.Scalar) : UInt64 := k.inv.val.l0
  let sign (k : CT.Scalar) : UInt64 :=
    match ECDSA.signWithNonce sk 12345 k with
    | some rsig => rsig.sig.s.toUInt64
    | none => 0
  let ok₁ ← report "reference k•G (variable time)" smulRef id samples true
  let ok₂ ← report "CT k•G                       " smulCT CT.Scalar.ofNat samples false
  let ok₃ ← report "CT k⁻¹ mod n                 " invCT CT.Scalar.ofNat samples false
  let ok₄ ← report "ECDSA signWithNonce          " sign CT.Scalar.ofNat samples false
  return if ok₁ && ok₂ && ok₃ && ok₄ then 0 else 1
