/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantineKernel
import Tri.RelaxedCounting

/-!
# Exact paper-worst bridge to an effective-rate relaxed Tri step

For the paper's adverse response, collapsing honest `Y` and Byzantine `Z`
produces exactly one unequal-rate binary Tri step on `X` versus `Y + Z`.
The effective rate is specified without division and may vary with the current
physical state.
-/

namespace Tri.Byzantine

open scoped ENNReal

variable {n B : ℕ}

abbrev paperWorstControl : Control := Control.worst

/-- Collapse a physical `X/Y/Z` composition to an unequal-rate binary
interaction outcome. -/
def aggregateRelaxedKind : TripleComp → RelaxedTripleKind
  | .xxx => .xxx
  | .xxy => .xxyFire
  | .xxz => .xxyIdle
  | .xyy => .xyyFire
  | .xyz => .xyyFire
  | .xzz => .xyyFire
  | .yyy => .yyy
  | .yyz => .yyy
  | .yzz => .yyy
  | .zzz => .yyy

/-- Unnormalized mass of each collapsed outcome. -/
noncomputable def aggregateRelaxedWeight
    (s : State n B) : RelaxedTripleKind → ℝ≥0∞
  | .xxx => TripleComp.weightAt s .xxx
  | .xxyFire => TripleComp.weightAt s .xxy
  | .xxyIdle => TripleComp.weightAt s .xxz
  | .xyyFire =>
      (TripleComp.weightAt s .xyy : ℝ≥0∞) +
        TripleComp.weightAt s .xyz +
        TripleComp.weightAt s .xzz
  | .yyy =>
      (TripleComp.weightAt s .yyy : ℝ≥0∞) +
        TripleComp.weightAt s .yyz +
        TripleComp.weightAt s .yzz +
        TripleComp.weightAt s .zzz

theorem triplePMF_map_aggregateRelaxedKind_apply
    (s : State n B) (h3 : 3 ≤ n) (k : RelaxedTripleKind) :
    ((triplePMF s h3).map aggregateRelaxedKind) k =
      aggregateRelaxedWeight s k /
        (Nat.choose n 3 : ℝ≥0∞) := by
  cases k <;>
    rw [PMF.map_apply, tsum_fintype] <;>
    rw [show (Finset.univ : Finset TripleComp) =
      {TripleComp.xxx, TripleComp.xxy, TripleComp.xxz,
        TripleComp.xyy, TripleComp.xyz, TripleComp.xzz,
        TripleComp.yyy, TripleComp.yyz, TripleComp.yzz,
        TripleComp.zzz} from rfl] <;>
    simp [aggregateRelaxedKind, aggregateRelaxedWeight,
      triplePMF_apply] <;>
    simp only [ENNReal.add_div, add_assoc]

/-- Division-free specification of the physical effective rate
`fire = y / (y + z)` and its complementary idle rate. -/
structure IsPaperEffectiveRate
    (r : RelaxedRate) (s : State n B) : Prop where
  fire_cross :
    (r.fire : ℝ≥0∞) *
        ((State.y s : ℝ≥0∞) + (State.z s : ℝ≥0∞)) =
      (State.y s : ℝ≥0∞)
  idle_cross :
    (r.idle : ℝ≥0∞) *
        ((State.y s : ℝ≥0∞) + (State.z s : ℝ≥0∞)) =
      (State.z s : ℝ≥0∞)

theorem isPaperEffectiveRate_of_yz_eq_zero
    (r : RelaxedRate) (s : State n B)
    (hzero : State.y s + State.z s = 0) :
    IsPaperEffectiveRate r s := by
  have hy : State.y s = 0 := by omega
  have hz : State.z s = 0 := by omega
  constructor <;> simp [hy, hz]

/-- Every aggregate physical outcome has exactly the corresponding relaxed
binary weight. -/
theorem aggregateRelaxedWeight_eq_relaxedWeight
    (r : RelaxedRate) (s : State n B)
    (hrate : IsPaperEffectiveRate r s)
    (k : RelaxedTripleKind) :
    aggregateRelaxedWeight s k =
      RelaxedTripleKind.weight r (State.x s)
        (State.y s + State.z s) k := by
  cases k
  · simp [aggregateRelaxedWeight, RelaxedTripleKind.weight,
      TripleComp.weightAt, TripleComp.weight]
  · simp only [aggregateRelaxedWeight, RelaxedTripleKind.weight,
      TripleComp.weightAt, TripleComp.weight]
    push_cast
    calc
      (Nat.choose (State.x s) 2 : ℝ≥0∞) * (State.y s : ℝ≥0∞) =
          (Nat.choose (State.x s) 2 : ℝ≥0∞) *
            ((r.fire : ℝ≥0∞) *
              ((State.y s : ℝ≥0∞) + (State.z s : ℝ≥0∞))) := by
                rw [hrate.fire_cross]
      _ = (r.fire : ℝ≥0∞) *
            ((Nat.choose (State.x s) 2 : ℝ≥0∞) *
              ((State.y s : ℝ≥0∞) + (State.z s : ℝ≥0∞))) := by ring
  · simp only [aggregateRelaxedWeight, RelaxedTripleKind.weight,
      TripleComp.weightAt, TripleComp.weight]
    push_cast
    calc
      (Nat.choose (State.x s) 2 : ℝ≥0∞) * (State.z s : ℝ≥0∞) =
          (Nat.choose (State.x s) 2 : ℝ≥0∞) *
            ((r.idle : ℝ≥0∞) *
              ((State.y s : ℝ≥0∞) + (State.z s : ℝ≥0∞))) := by
                rw [hrate.idle_cross]
      _ = (r.idle : ℝ≥0∞) *
            ((Nat.choose (State.x s) 2 : ℝ≥0∞) *
              ((State.y s : ℝ≥0∞) + (State.z s : ℝ≥0∞))) := by ring
  · simp only [aggregateRelaxedWeight, RelaxedTripleKind.weight,
      TripleComp.weightAt, TripleComp.weight]
    rw [Tri.pair_two_split]
    push_cast
    ring
  · simp only [aggregateRelaxedWeight, RelaxedTripleKind.weight,
      TripleComp.weightAt, TripleComp.weight]
    rw [Tri.choose_three_split]
    push_cast
    ring

/-- Exact scheduler quotient. -/
theorem triplePMF_map_aggregateRelaxedKind
    (r : RelaxedRate) (s : State n B) (h3 : 3 ≤ n)
    (hrate : IsPaperEffectiveRate r s) :
    (triplePMF s h3).map aggregateRelaxedKind =
      relaxedInteractionPMF r (State.x s)
        (State.y s + State.z s) (by
          have htotal := State.total s
          omega) := by
  have htotal :
      State.x s + (State.y s + State.z s) = n := by
    have h := State.total s
    omega
  ext k
  rw [triplePMF_map_aggregateRelaxedKind_apply]
  rw [relaxedInteractionPMF_apply]
  rw [aggregateRelaxedWeight_eq_relaxedWeight r s hrate k]
  rw [htotal]

@[simp] theorem paperWorst_nextX_eq_aggregateRelaxed
    (s : State n B) (k : TripleComp) :
    Action.nextX (State.x s) (paperWorstControl.action k) =
      RelaxedTripleKind.nextX (State.x s)
        (aggregateRelaxedKind k) := by
  cases k <;> rfl

/-- Exact honest-`X` transition law under the paper-worst response. -/
theorem paperWorst_step_map_x_eq_relaxedTriStep
    (r : RelaxedRate) (s : State n B) (h3 : 3 ≤ n)
    (hrate : IsPaperEffectiveRate r s) :
    (step paperWorstControl s h3).map State.x =
      relaxedTriStep r (State.x s) (State.y s + State.z s) (by
        have htotal := State.total s
        omega) := by
  let hAgg : 3 ≤ State.x s + (State.y s + State.z s) := by
    have htotal := State.total s
    omega
  change
    (step paperWorstControl s h3).map State.x =
      relaxedTriStep r (State.x s) (State.y s + State.z s) hAgg
  calc
    (step paperWorstControl s h3).map State.x =
        (movePMF paperWorstControl s h3).map
          (Action.nextX (State.x s)) :=
      step_map_x paperWorstControl s h3
    _ = ((triplePMF s h3).map aggregateRelaxedKind).map
          (RelaxedTripleKind.nextX (State.x s)) := by
      unfold movePMF
      rw [PMF.map_comp, PMF.map_comp]
      apply congrArg (fun f : TripleComp → ℕ =>
        (triplePMF s h3).map f)
      funext k
      simp only [Function.comp_apply]
      exact paperWorst_nextX_eq_aggregateRelaxed s k
    _ = (relaxedInteractionPMF r (State.x s)
          (State.y s + State.z s) hAgg).map
          (RelaxedTripleKind.nextX (State.x s)) := by
      rw [triplePMF_map_aggregateRelaxedKind r s h3 hrate]
    _ = relaxedTriStep r (State.x s)
          (State.y s + State.z s) hAgg := rfl

/-- Paper-worst `X` together with the productive-event indicator. -/
noncomputable def paperWorstCountStep
    (s : State n B) (h3 : 3 ≤ n) (c : ℕ) : PMF (ℕ × ℕ) :=
  ((step paperWorstControl s h3).map State.x).map
    (fun x' =>
      (x', if x' = State.x s then c else c + 1))

/-- Exact counted bridge. The effective rate is allowed to depend on the
current physical state; this is not a homogeneous-chain assertion. -/
theorem paperWorstCountStep_eq_relaxedCount
    (r : RelaxedRate) (s : State n B) (h3 : 3 ≤ n)
    (hrate : IsPaperEffectiveRate r s) (c : ℕ) :
    paperWorstCountStep s h3 c =
      relaxedCount r n (State.x s, c) := by
  let hAgg : 3 ≤ State.x s + (State.y s + State.z s) := by
    have htotal := State.total s
    omega
  have hchain :
      relaxedTriChain r n (State.x s) =
        relaxedTriStep r (State.x s)
          (State.y s + State.z s) hAgg := by
    unfold relaxedTriChain
    rw [dif_pos ⟨h3, State.x_le s⟩]
    congr 1
    have htotal := State.total s
    omega
  unfold paperWorstCountStep relaxedCount
  rw [paperWorst_step_map_x_eq_relaxedTriStep r s h3 hrate]
  rw [hchain]

end Tri.Byzantine

#print axioms Tri.Byzantine.triplePMF_map_aggregateRelaxedKind
#print axioms Tri.Byzantine.paperWorst_step_map_x_eq_relaxedTriStep
#print axioms Tri.Byzantine.paperWorstCountStep_eq_relaxedCount
