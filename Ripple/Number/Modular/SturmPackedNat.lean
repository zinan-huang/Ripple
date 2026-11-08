import Ripple.Number.Modular.ModularPoly41Terms

/-!
# Kronecker packing: the natural-number programs the kernel runs

Definitions only (and one shift lemma), importing nothing but the term data, so that
`SturmPackedEval`, whose `decide +kernel` dominates the build, does not load Mathlib. Their
meaning is proved in `SturmPackedCore`.
-/

namespace Ripple.Number.Modular

/-- Balanced sum of `f (lo + i)` for `i < len`, recursion depth `fuel`. -/
def treeSum (f : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, lo, len => if len = 0 then 0 else f lo
  | k + 1, lo, len =>
      if len ≤ 1 then (if len = 0 then 0 else f lo)
      else treeSum f k lo (len / 2) + treeSum f k (lo + len / 2) (len - len / 2)

/-- `Σ_{k<K} 2^(w (k+1))` by binary doubling (no division); exact when `K < 2 ^ fuel`. -/
def geomF (w : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, K =>
      let g := geomF w f (K / 2)
      let g2 := g + (g <<< (w * (K / 2)))
      if K % 2 = 0 then g2 else g2 + (1 <<< (w * K))

/-- `Σ_{k<K} 2^(a (k+1))` in closed form: one power, one subtraction, one exact division and
one product. -/
def geomC (a K : Nat) : Nat := 2 ^ a * ((2 ^ (a * K) - 1) / (2 ^ a - 1))

/-- Packed `Σ_{m<n} σⱼ(m) 2^(w m)`, by the Lambert form; the geometric sums `geomC` depend only
on `w` and `d`, so packings of `σ₃` and `σ₅` at the same width share them. -/
def sigmaPack (j w n : Nat) : Nat :=
  treeSum (fun d => d ^ j * geomC (w * d) ((n - 1) / d)) 12 0 n

/-- Packed `E₄` with slot width `w` and `n` slots. -/
def e4Pack (w n : Nat) : Nat := 1 + 240 * sigmaPack 3 w n

/-- `1 <<< k = 2 ^ k`, stated once generically so that concrete instances never unfold `2 ^ k`. -/
theorem one_shiftLeft_eq_two_pow (k : Nat) : 1 <<< k = 2 ^ k := by
  rw [Nat.shiftLeft_eq, Nat.one_mul]

/-- Product modulo `m + 1`. -/
def mulM (m a b : Nat) : Nat := (a * b) &&& m

/-- Sum modulo `m + 1`. -/
def addM (m a b : Nat) : Nat := (a + b) &&& m

/-- Difference modulo `m + 1`. -/
def subM (m a b : Nat) : Nat := (a + (m + 1 - (b &&& m))) &&& m

/-- `[cur, cur·a, …, cur·a^(len-1)]` modulo `m + 1`. -/
def powTab (m a : Nat) : Nat → Nat → List Nat
  | _, 0 => []
  | cur, len + 1 => cur :: powTab m a (mulM m cur a) len

/-- `Σ_{i<len} ((v >>> (w (lo + i))) % 2 ^ w) · 2 ^ (s i)`, by a balanced split: re-packs the
`w`-bit slots `lo, …, lo + len - 1` of `v` into `s`-bit slots. -/
def spread (w s v : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, len => if len = 0 then 0 else (v >>> (w * lo)) % 2 ^ w
  | k + 1, lo, len =>
      if len ≤ 1 then (if len = 0 then 0 else (v >>> (w * lo)) % 2 ^ w)
      else spread w s v k lo (len / 2) +
        (spread w s v k (lo + len / 2) (len - len / 2) <<< (s * (len / 2)))

/-- Apply `f` to entry `n` of a list of accumulator pairs (no change when `n` is out of range). -/
def addAt (f : Nat × Nat → Nat × Nat) : Nat → List (Nat × Nat) → List (Nat × Nat)
  | _, [] => []
  | 0, b :: bs => f b :: bs
  | n + 1, b :: bs => b :: addAt f n bs

/-- Add `c · v` to the positive or the negative part of an accumulator pair. -/
def addSigned (c : Int) (v : Nat) (p : Nat × Nat) : Nat × Nat :=
  if 0 ≤ c then (p.1 + c.toNat * v, p.2) else (p.1, p.2 + c.natAbs * v)

/-- One term of the bucket pass. The state is `(x, R[x], buckets)`: the table entry of the last
`x` is kept, so terms sorted by `x` read the table once per `x`. -/
def bucketStep (R : List Nat) (st : Nat × Nat × List (Nat × Nat)) (t : SparseBivarTerm) :
    Nat × Nat × List (Nat × Nat) :=
  let v := if t.xPow = st.1 then st.2.1 else R.getD t.xPow 0
  (t.xPow, v, addAt (addSigned t.coeff v) t.yPow st.2.2)

/-- In one pass over the terms, bucket `y` accumulates the positive and the negative parts of
`Σ_{yPow = y} c · R[xPow]`. -/
def bucketPN (R : List Nat) (n : Nat) (terms : List SparseBivarTerm) : List (Nat × Nat) :=
  (terms.foldl (bucketStep R) (0, R.getD 0 0, List.replicate n (0, 0))).2.2

/-- Positive and negative parts of the terms with `key t = x`, weighted by `R` at `idx t`,
accumulated without masks and combined by one masked subtraction. -/
def innerPN (m : Nat) (R : List Nat) (key idx : SparseBivarTerm → Nat) (x : Nat)
    (terms : List SparseBivarTerm) : Nat :=
  subM m
    (terms.foldl (fun acc t => if key t = x ∧ 0 ≤ t.coeff then
      acc + t.coeff.toNat * R.getD (idx t) 0 else acc) 0)
    (terms.foldl (fun acc t => if key t = x ∧ t.coeff < 0 then
      acc + t.coeff.natAbs * R.getD (idx t) 0 else acc) 0)

/-- `-b` modulo `m + 1`, without the final mask. -/
def negM (m b : Nat) : Nat := m + 1 - (b &&& m)

/-- `Σ_{j<n} S j · D j · c^(n-1-j)` modulo `m + 1`, by Horner's rule in `c`. -/
def hornerM (m c : Nat) (S D : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => addM m (mulM m (S n) (D n)) (mulM m c (hornerM m c S D n))

/-- Spreading by one product and one mask. -/
def combSpread (a c n U : Nat) : Nat :=
  (U * (1 + geomF a 7 (n - 1))) &&& ((2 ^ c - 1) * (1 + geomF (a + c) 7 (n - 1)))

end Ripple.Number.Modular
