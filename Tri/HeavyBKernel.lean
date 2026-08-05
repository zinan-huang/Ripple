/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.BiStep
import Tri.BiMolecular
import Tri.Phase3Productive

/-!
# The Heavy-B kernel

Heavy-B is the bimolecular CRN whose blank is a HEAVY molecule, counting as two
units of population:

```text
HeavyInv n s :=  s.x + s.y + 2 * s.b = n
```

Its reactions are

```text
X + Y → B          (a creation: two light molecules fuse into one heavy blank)
X + B → X + X + X  (an X-resolution: the blank splits, adopting X)
Y + B → Y + Y + Y  (a Y-resolution)
```

with `X+X`, `Y+Y` and `B+B` inert. Each reaction preserves the population `n`
because the blank is worth two: the creation removes two light molecules and
adds one heavy, and a resolution removes one heavy and adds two light.

## Nothing new is needed for the pair distribution

Interactions draw an unordered pair of *entities*, and there are `x + y + b`
entities, so the composition of the drawn pair is distributed exactly as
`dbPairPMF` (`Tri/BiStep.lean`) already says. `PairComp` and `dbPairPMF` are
protocol-independent: only the `next` map differs between Double-B and Heavy-B.
So this file adds a `next` and its arithmetic, and nothing else.

## The Double-B property holds here on the PHYSICAL counts

On `heavyLevel s = s.x + s.b`:

```text
X + Y → B          (x−1) + (b+1) = x + b     UNCHANGED
X + B → 3X         (x+2) + (b−1) = x + b + 1  UP
Y + B → 3Y          x    + (b−1) = x + b − 1  DOWN
```

so the level moves ONLY at resolution events — the single property the entire
Double-B direction/clock engine rests on. Unlike Single-B, where the two
creations are distinct events of equal weight and force a history-carrying
ledger (`Tri/SingleBLevel.lean`), Heavy-B has ONE creation and it is
level-neutral, so the property holds for a function of `(x, y, b)` alone.

That is the structural reason Heavy-B is a genuine port and Single-B is not.

## The blank cancels from the resolution odds

The two resolutions carry weights `x*b` and `y*b`, so their ratio is `x : y`,
independent of `b`. This is the same cancellation as Double-B's, and it is what
makes the direction analysis blank-free.
-/

namespace Tri

open scoped ENNReal

/-- The Heavy-B post-reaction configuration.  The blank is worth two units, so
the creation `X+Y → B` removes two light molecules and the resolutions each
remove one heavy and add two light. -/
def PairComp.heavyNext (s : BiCfg) : PairComp → BiCfg
  | .xx | .yy | .bb => s
  | .xy => ⟨s.x - 1, s.y - 1, s.b + 1⟩
  | .xb => ⟨s.x + 2, s.y, s.b - 1⟩
  | .yb => ⟨s.x, s.y + 2, s.b - 1⟩

/-- Every positive-weight Heavy-B reaction preserves the population.

The `ℕ`-subtractions in `heavyNext` are exact precisely on the positive-weight
events, and the weight hypothesis is what supplies that. -/
theorem PairComp.heavyNext_heavyInv (n : ℕ) (s : BiCfg) (k : PairComp)
    (hs : BiCfg.HeavyInv n s)
    (hk : PairComp.weight s.x s.y s.b k ≠ 0) :
    BiCfg.HeavyInv n (PairComp.heavyNext s k) := by
  obtain ⟨x, y, b⟩ := s
  simp only [BiCfg.HeavyInv] at hs ⊢
  cases k <;>
    simp only [PairComp.heavyNext, PairComp.weight] at hk ⊢ <;>
    first
    | omega
    | (rw [Nat.mul_ne_zero_iff] at hk; omega)

/-! ### The level classification: motion only at resolutions -/

/-- The creation is level-neutral.  This is the fact that fails for Single-B and
holds here, and it is why Heavy-B needs no orientation ledger. -/
theorem heavyLevel_heavyNext_xy (s : BiCfg)
    (hk : PairComp.weight s.x s.y s.b PairComp.xy ≠ 0) :
    BiCfg.heavyLevel (PairComp.heavyNext s PairComp.xy) = BiCfg.heavyLevel s := by
  obtain ⟨x, y, b⟩ := s
  simp only [PairComp.weight] at hk
  rw [Nat.mul_ne_zero_iff] at hk
  simp only [PairComp.heavyNext, BiCfg.heavyLevel]
  omega

/-- The inert events are level-neutral, trivially. -/
theorem heavyLevel_heavyNext_inert (s : BiCfg) (k : PairComp)
    (hk : k = PairComp.xx ∨ k = PairComp.yy ∨ k = PairComp.bb) :
    BiCfg.heavyLevel (PairComp.heavyNext s k) = BiCfg.heavyLevel s := by
  rcases hk with h | h | h <;> rw [h] <;> rfl

/-- An `X`-resolution raises the level by exactly one. -/
theorem heavyLevel_heavyNext_xb (s : BiCfg)
    (hk : PairComp.weight s.x s.y s.b PairComp.xb ≠ 0) :
    BiCfg.heavyLevel (PairComp.heavyNext s PairComp.xb) = BiCfg.heavyLevel s + 1 := by
  obtain ⟨x, y, b⟩ := s
  simp only [PairComp.weight] at hk
  rw [Nat.mul_ne_zero_iff] at hk
  simp only [PairComp.heavyNext, BiCfg.heavyLevel]
  omega

/-- A `Y`-resolution lowers the level by exactly one, stated subtraction-free. -/
theorem heavyLevel_heavyNext_yb (s : BiCfg)
    (hk : PairComp.weight s.x s.y s.b PairComp.yb ≠ 0) :
    BiCfg.heavyLevel (PairComp.heavyNext s PairComp.yb) + 1 = BiCfg.heavyLevel s := by
  obtain ⟨x, y, b⟩ := s
  simp only [PairComp.weight] at hk
  rw [Nat.mul_ne_zero_iff] at hk
  simp only [PairComp.heavyNext, BiCfg.heavyLevel]
  omega

/-! ### The blank cancels from the resolution odds -/

/-- **The cancellation, cross-multiplied.**  The two resolution weights are in
the ratio `x : y`, with `b` playing no part.

Stated as a `ℕ` identity so it can be used without any division. -/
theorem heavy_resolution_odds (x y b : ℕ) :
    PairComp.weight x y b PairComp.xb * y
      = PairComp.weight x y b PairComp.yb * x := by
  simp only [PairComp.weight]
  ring

/-- **The direction guard.**  If `X` leads by a factor `k` then the
`X`-resolution takes at least a `k/(k+1)` share of the resolution mass — and the
bound does not mention `b`.

This is the exact Heavy-B analogue of `productive_down_mass_ge`, and it is what
the ported Double-B direction argument consumes. -/
theorem heavy_up_share_ge {k x y b : ℕ}
    (hres : 0 < x * b + y * b) (hguard : k * y ≤ x) :
    (k : ℝ≥0∞) / ((k : ℝ≥0∞) + 1)
      ≤ ((x * b : ℕ) : ℝ≥0∞)
        / (((x * b : ℕ) : ℝ≥0∞) + ((y * b : ℕ) : ℝ≥0∞)) :=
  productive_down_mass_ge hres (by
    calc k * (y * b) = (k * y) * b := by ring
      _ ≤ x * b := Nat.mul_le_mul_right b hguard)

/-- The resolution masses under the pair distribution, for the record: they are
the weights over the common denominator, so the cancellation above transfers
verbatim. -/
theorem heavy_resolution_mass (x y b : ℕ) (h : 2 ≤ x + y + b) :
    dbPairPMF x y b h .xb
        = ((x * b : ℕ) : ℝ≥0∞) / (Nat.choose (x + y + b) 2 : ℝ≥0∞)
      ∧ dbPairPMF x y b h .yb
        = ((y * b : ℕ) : ℝ≥0∞) / (Nat.choose (x + y + b) 2 : ℝ≥0∞) := by
  constructor <;> rw [dbPairPMF_apply] <;> rfl

/-! ### The kernel -/

/-- Heavy-B configurations of population `n`. -/
def HeavyState (n : ℕ) := {s : BiCfg // BiCfg.HeavyInv n s}

/-- Guarded Heavy-B update on invariant-carrying states. -/
noncomputable def PairComp.nextHeavyState {n : ℕ} (q : HeavyState n)
    (k : PairComp) : HeavyState n :=
  if hk : PairComp.weight q.1.x q.1.y q.1.b k = 0 then q
  else ⟨PairComp.heavyNext q.1 k,
    PairComp.heavyNext_heavyInv n q.1 k q.2 hk⟩

/-- **Heavy-B has too few entities to interact only when `n ≤ 2`.**

This needs saying because `2 ≤ n` does NOT give `2 ≤ x + y + b` here: the blank
is worth two units, so a lone heavy blank is a single entity with `n = 2`.  For
`n ≥ 3` the entity count is always at least two and the guard below never
fires. -/
theorem heavy_two_entities {n : ℕ} (hn : 3 ≤ n) (q : HeavyState n) :
    2 ≤ q.1.x + q.1.y + q.1.b := by
  have h := q.2
  simp only [BiCfg.HeavyInv] at h
  omega

/-- One Heavy-B interaction, totalized: a configuration with fewer than two
entities holds still.

The self-loop is not cosmetic.  At `n = 2` the configuration `(0, 0, 1)` — one
heavy blank and nothing else — is genuinely absorbing and is NOT consensus, and
it is REACHABLE: `(1, 1, 0)` fuses to it in one step.  See
`heavy_stuck_not_consensus`.  For `n ≥ 3` the guard never fires
(`heavy_two_entities`), which is why the paper's analysis never meets it. -/
noncomputable def heavyStateStep (n : ℕ)
    (q : HeavyState n) : PMF (HeavyState n) :=
  if h : 2 ≤ q.1.x + q.1.y + q.1.b then
    (dbPairPMF q.1.x q.1.y q.1.b h).map (PairComp.nextHeavyState q)
  else PMF.pure q

/-- **The `n = 2` degeneracy, recorded.**  The lone-heavy-blank configuration is
absorbing and is not `X`-consensus, so any Heavy-B theorem asserting consensus
must exclude `n = 2` — `3 ≤ n` suffices, by `heavy_two_entities`. -/
theorem heavy_stuck_not_consensus :
    ∃ q : HeavyState 2,
      heavyStateStep 2 q = PMF.pure q ∧ BiCfg.heavyLevel q.1 ≠ 2 := by
  refine ⟨⟨⟨0, 0, 1⟩, by simp [BiCfg.HeavyInv]⟩, ?_, ?_⟩
  · unfold heavyStateStep
    rw [dif_neg (by norm_num)]
  · simp [BiCfg.heavyLevel]

end Tri

#print axioms Tri.PairComp.heavyNext_heavyInv
#print axioms Tri.heavyLevel_heavyNext_xy
#print axioms Tri.heavyLevel_heavyNext_xb
#print axioms Tri.heavyLevel_heavyNext_yb
#print axioms Tri.heavy_resolution_odds
#print axioms Tri.heavy_up_share_ge
#print axioms Tri.heavy_resolution_mass
#print axioms Tri.heavy_two_entities
#print axioms Tri.heavy_stuck_not_consensus
