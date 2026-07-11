import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WinNFailDecomp
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.CounterSurvivalConc
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockDepletionCoupling

/-!
# ClockCounterDepthCover

Identity-free counter-depth cover for the `WinN` clock-counter survival problem.

This file supplies the adopted aggregate count formulation:

* `counterDepthWeight`;
* `counterDepthMass`;
* `counterDepthThreshold`;
* `CounterDepthDepleted`;
* singleton `DepthClocks` and `DepthDepleted`;
* a full deterministic cover
  `{c | ¬ WinN N n c} ⊆ ⋃ j ∈ DepthClocks, {c | DepthDepleted j c}`;
* the MGF tail wrapper from one isolated aggregate-drift hypothesis.

The isolated hypothesis is `CounterDepthMassDriftHypothesis`.  It is the aggregate
sibling of the landed fixed-state drift `ClockDepletionCoupling.expPot_drift`,
whose proof should reuse the same support/MGF structure and the landed
`ClockDepletionCoupling.decrement_step_prob_le` / bounded-drop facts.  Everything
after that drift input is proved here with `ExactMajority.geometric_drift_tail`.

No `sorry` / `admit` / `axiom` / `native_decide`.
-/

namespace ExactMajority
namespace ClockCounterDepthCover

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/--
Counter-depth weight for the phase-`N` survival problem with synchronized reset `R`.

* phase-`N` clocks at counter `r` get weight `exp(s * (R - r))`;
* phase-`N` non-clocks get weight `0`;
* any off-phase agent gets the absorbing failure weight `exp(s * R)`.

The off-phase case makes the deterministic cover global.  On reachable trajectories
from a `card = n` start, the `card ≠ n` mode is probability-zero by card conservation,
but the cover itself is stated in the global shape required by
`ClockCounterSurvival.survival_union_bound`.
-/
noncomputable def counterDepthWeight
    (N R : ℕ) (s : ℝ) (a : AgentState L K) : ℝ≥0∞ :=
  if a.phase.val = N then
    if a.role = Role.clock then
      ENNReal.ofReal (Real.exp (s * (((R - a.counter.val) : ℕ) : ℝ)))
    else
      0
  else
    ENNReal.ofReal (Real.exp (s * (R : ℝ)))

/--
Identity-free exponential counter-depth mass.

This is a pure count-of-state observable over `Config = Multiset (AgentState L K)`:
the chain-observable data are only the state counts `c.count a`.
-/
noncomputable def counterDepthMass
    (N R : ℕ) (s : ℝ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  ∑ a : AgentState L K,
    (c.count a : ℝ≥0∞) * counterDepthWeight (L := L) (K := K) N R s a

/-- Absorbing threshold corresponding to one clock having accumulated depth `R`. -/
noncomputable def counterDepthThreshold (R : ℕ) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (s * (R : ℝ)))

/--
The aggregate depletion event.

The `c.card ≠ n` disjunct is included so this predicate can be used directly as
the target in the global `survival_union_bound` cover.  From a `card = n` start,
that disjunct has zero mass along actual protocol trajectories.
-/
noncomputable def CounterDepthDepleted
    (n N R : ℕ) (s : ℝ) (c : Config (AgentState L K)) : Prop :=
  c.card ≠ n ∨
    counterDepthThreshold R s ≤
      counterDepthMass (L := L) (K := K) N R s c

/-- Singleton index set for the identity-free aggregate cover. -/
def DepthClocks : Finset Unit :=
  {()}

/-- The depletion predicate in the exact indexed shape expected by union-bound wrappers. -/
noncomputable def DepthDepleted
    (n N R : ℕ) (s : ℝ) :
    Unit → Config (AgentState L K) → Prop :=
  fun _ c => CounterDepthDepleted (L := L) (K := K) n N R s c

/-- Multiplicative one-step MGF rate for the aggregate depth drift. -/
noncomputable def counterDepthRate (n : ℕ) (s : ℝ) : ℝ≥0∞ :=
  1 + (2 : ℝ≥0∞) * ENNReal.ofReal (Real.exp s - 1) / (n : ℝ≥0∞)

/-- Tail scale produced by the aggregate MGF drift. -/
noncomputable def counterDepthTail (n H R : ℕ) (s : ℝ) : ℝ≥0∞ :=
  (counterDepthRate n s) ^ H * (n : ℝ≥0∞) / counterDepthThreshold R s

/-- `counterDepthMass` is measurable on the discrete configuration space. -/
theorem counterDepthMass_measurable
    (N R : ℕ) (s : ℝ) :
    Measurable (counterDepthMass (L := L) (K := K) N R s) :=
  Measurable.of_discrete

/-- The threshold is nonzero. -/
theorem counterDepthThreshold_ne_zero (R : ℕ) (s : ℝ) :
    counterDepthThreshold R s ≠ 0 := by
  unfold counterDepthThreshold
  simp [ENNReal.ofReal_eq_zero, not_le, Real.exp_pos]

/-- The threshold is finite. -/
theorem counterDepthThreshold_ne_top (R : ℕ) (s : ℝ) :
    counterDepthThreshold R s ≠ ∞ := by
  unfold counterDepthThreshold
  exact ENNReal.ofReal_ne_top

/-- Off-phase states have the absorbing threshold weight. -/
theorem counterDepthWeight_offPhase
    (N R : ℕ) (s : ℝ) (a : AgentState L K)
    (hphase : a.phase.val ≠ N) :
    counterDepthWeight (L := L) (K := K) N R s a =
      counterDepthThreshold R s := by
  simp [counterDepthWeight, counterDepthThreshold, hphase]

/-- A phase-`N` clock at counter zero has the absorbing threshold weight. -/
theorem counterDepthWeight_clock_zero
    (N R : ℕ) (s : ℝ) (a : AgentState L K)
    (hphase : a.phase.val = N)
    (hclock : a.role = Role.clock)
    (hzero : a.counter.val = 0) :
    counterDepthWeight (L := L) (K := K) N R s a =
      counterDepthThreshold R s := by
  simp [counterDepthWeight, counterDepthThreshold, hphase, hclock, hzero]

/-- A synchronized-reset phase-`N` clock has weight one. -/
theorem counterDepthWeight_clock_reset
    (N R : ℕ) (s : ℝ) (a : AgentState L K)
    (hphase : a.phase.val = N)
    (hclock : a.role = Role.clock)
    (hreset : a.counter.val = R) :
    counterDepthWeight (L := L) (K := K) N R s a = 1 := by
  simp [counterDepthWeight, hphase, hclock, hreset]

/--
A single present state whose weight is at least the threshold forces the whole
aggregate mass above the threshold.

This is the promised `Finset.single_le_sum` step: the full sum over `Finset.univ`
dominates the single heavy term, and `a ∈ c` gives `1 ≤ c.count a`.
-/
theorem counterDepthMass_ge_of_mem_weight_ge_threshold
    (N R : ℕ) (s : ℝ) (c : Config (AgentState L K)) (a : AgentState L K)
    (ha : a ∈ c)
    (hweight :
      counterDepthThreshold R s ≤
        counterDepthWeight (L := L) (K := K) N R s a) :
    counterDepthThreshold R s ≤
      counterDepthMass (L := L) (K := K) N R s c := by
  classical
  have hcountNat : 1 ≤ c.count a :=
    Multiset.one_le_count_iff_mem.mpr ha
  have hcount : (1 : ℝ≥0∞) ≤ (c.count a : ℝ≥0∞) := by
    exact_mod_cast hcountNat
  have hterm :
      counterDepthThreshold R s ≤
        (c.count a : ℝ≥0∞) *
          counterDepthWeight (L := L) (K := K) N R s a := by
    calc
      counterDepthThreshold R s
          ≤ counterDepthWeight (L := L) (K := K) N R s a := hweight
      _ = (1 : ℝ≥0∞) *
            counterDepthWeight (L := L) (K := K) N R s a := by simp
      _ ≤ (c.count a : ℝ≥0∞) *
            counterDepthWeight (L := L) (K := K) N R s a := by
              gcongr
  have hsingle :
      (c.count a : ℝ≥0∞) *
          counterDepthWeight (L := L) (K := K) N R s a
        ≤ counterDepthMass (L := L) (K := K) N R s c := by
    unfold counterDepthMass
    exact
      Finset.single_le_sum
        (fun b _hb => (bot_le :
          (0 : ℝ≥0∞) ≤
            (c.count b : ℝ≥0∞) *
              counterDepthWeight (L := L) (K := K) N R s b))
        (Finset.mem_univ a)
  exact hterm.trans hsingle

/--
Deterministic global cover for `¬ WinN`.

The three modes are exactly those of `WinNFailDecomp.not_winN_iff`:

* `card ≠ n`: direct first disjunct of `CounterDepthDepleted`;
* off-phase state: that state has absorbing threshold weight;
* clock at counter zero: if phase `N`, it has threshold weight; otherwise it is already
  covered by the off-phase branch.
-/
theorem counterDepth_hcover
    (n N R : ℕ) (s : ℝ) :
    {c : Config (AgentState L K) |
        ¬ CounterSurvivalConc.WinN (L := L) (K := K) N n c}
      ⊆
    ⋃ j ∈ (DepthClocks : Finset Unit),
      {c : Config (AgentState L K) |
        DepthDepleted (L := L) (K := K) n N R s j c} := by
  classical
  intro c hc
  have hdep : DepthDepleted (L := L) (K := K) n N R s () c := by
    dsimp [DepthDepleted, CounterDepthDepleted]
    rcases (WinNFailDecomp.not_winN_iff (L := L) (K := K) N n c).mp hc with
      hcard | hphase | hclock
    · exact Or.inl hcard
    · rcases hphase with ⟨a, ha, hne⟩
      exact Or.inr
        (counterDepthMass_ge_of_mem_weight_ge_threshold
          (L := L) (K := K) N R s c a ha
          (by
            rw [counterDepthWeight_offPhase
              (L := L) (K := K) N R s a hne]))
    · rcases hclock with ⟨a, ha, hcl, hzero⟩
      by_cases hp : a.phase.val = N
      · exact Or.inr
          (counterDepthMass_ge_of_mem_weight_ge_threshold
            (L := L) (K := K) N R s c a ha
            (by
              rw [counterDepthWeight_clock_zero
                (L := L) (K := K) N R s a hp hcl hzero]))
      · exact Or.inr
          (counterDepthMass_ge_of_mem_weight_ge_threshold
            (L := L) (K := K) N R s c a ha
            (by
              rw [counterDepthWeight_offPhase
                (L := L) (K := K) N R s a hp]))
  simpa [DepthClocks, DepthDepleted] using hdep

/--
At a synchronized-reset `WinN` start, the aggregate mass is at most the population
cardinality: each present clock has weight `1`, each present non-clock has weight `0`,
and absent states contribute `0`.
-/
theorem counterDepthMass_start_le_card
    (N R : ℕ) (s : ℝ) (c₀ : Config (AgentState L K))
    (hphase : ∀ a ∈ c₀, a.phase.val = N)
    (hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R) :
    counterDepthMass (L := L) (K := K) N R s c₀ ≤ (c₀.card : ℝ≥0∞) := by
  classical
  unfold counterDepthMass
  calc
    (∑ a : AgentState L K,
        (c₀.count a : ℝ≥0∞) *
          counterDepthWeight (L := L) (K := K) N R s a)
        ≤ ∑ a : AgentState L K, (c₀.count a : ℝ≥0∞) := by
          refine Finset.sum_le_sum ?_
          intro a _ha
          by_cases hcnt : c₀.count a = 0
          · simp [hcnt]
          · have hpos : 1 ≤ c₀.count a :=
              Nat.succ_le_of_lt (Nat.pos_of_ne_zero hcnt)
            have hamem : a ∈ c₀ :=
              Multiset.one_le_count_iff_mem.mp hpos
            have hp : a.phase.val = N := hphase a hamem
            by_cases hcl : a.role = Role.clock
            · have hR : a.counter.val = R := hreset a hamem hcl
              have hw :
                  counterDepthWeight (L := L) (K := K) N R s a = 1 :=
                counterDepthWeight_clock_reset
                  (L := L) (K := K) N R s a hp hcl hR
              simp [hw]
            · have hw :
                  counterDepthWeight (L := L) (K := K) N R s a = 0 := by
                simp [counterDepthWeight, hp, hcl]
              simp [hw]
    _ = (c₀.card : ℝ≥0∞) := by
          have hnat :
              (∑ a : AgentState L K, c₀.count a) = c₀.card := by
            exact
              Multiset.sum_count_eq_card
                (s := (Finset.univ : Finset (AgentState L K)))
                (m := c₀)
                (by
                  intro a _ha
                  exact Finset.mem_univ a)
          exact_mod_cast hnat

/-- Synchronized-reset `WinN` start mass bound in population-size form. -/
theorem counterDepthMass_start_le_n
    (n N R : ℕ) (s : ℝ) (c₀ : Config (AgentState L K))
    (hwin₀ : CounterSurvivalConc.WinN (L := L) (K := K) N n c₀)
    (hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R) :
    counterDepthMass (L := L) (K := K) N R s c₀ ≤ (n : ℝ≥0∞) := by
  calc
    counterDepthMass (L := L) (K := K) N R s c₀
        ≤ (c₀.card : ℝ≥0∞) :=
          counterDepthMass_start_le_card
            (L := L) (K := K) N R s c₀ hwin₀.2.1 hreset
    _ = (n : ℝ≥0∞) := by rw [hwin₀.1]

/--
The one isolated aggregate drift input.

This is the single research sublemma not currently landed in the fixed-state MGF
library.  It is the aggregate-depth sibling of
`ClockDepletionCoupling.expPot_drift`: prove it by adapting that proof with
`ClockDepletionCoupling.decrement_step_prob_le` and the bounded two-endpoint
support argument.  The rate here uses `e^s - 1` rather than `e^(2s) - 1` because
the aggregate depth mass accounts additively for the two selected endpoints; each
selected clock endpoint's depth weight is multiplied by at most `e^s`.
-/
def CounterDepthMassDriftHypothesis
    (n N R : ℕ) (s : ℝ) : Prop :=
  ∀ c : Config (AgentState L K),
    ∫⁻ c',
        counterDepthMass (L := L) (K := K) N R s c'
      ∂((NonuniformMajority L K).transitionKernel c)
      ≤ counterDepthRate n s *
          counterDepthMass (L := L) (K := K) N R s c

/--
MGF tail for the aggregate counter-depth mass, from the single aggregate drift input.

This is the direct `ExactMajority.geometric_drift_tail` wrapper.  The event is exactly

`{c | counterDepthThreshold R s ≤ counterDepthMass N R s c}`.
-/
theorem counterDepthMass_tail_of_drift
    (n N H R : ℕ) (s : ℝ)
    (c₀ : Config (AgentState L K))
    (hstart :
      counterDepthMass (L := L) (K := K) N R s c₀ ≤ (n : ℝ≥0∞))
    (hdepth_drift :
      CounterDepthMassDriftHypothesis (L := L) (K := K) n N R s) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
      {c : Config (AgentState L K) |
        counterDepthThreshold R s ≤
          counterDepthMass (L := L) (K := K) N R s c}
      ≤ counterDepthTail n H R s := by
  classical
  have hθ0 : counterDepthThreshold R s ≠ 0 :=
    counterDepthThreshold_ne_zero R s
  have hθtop : counterDepthThreshold R s ≠ ∞ :=
    counterDepthThreshold_ne_top R s
  have htail :
      ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          counterDepthThreshold R s ≤
            counterDepthMass (L := L) (K := K) N R s c}
        ≤
      (counterDepthRate n s) ^ H *
          counterDepthMass (L := L) (K := K) N R s c₀ /
        counterDepthThreshold R s := by
    exact
      ExactMajority.geometric_drift_tail
        (K := (NonuniformMajority L K).transitionKernel)
        (Φ := counterDepthMass (L := L) (K := K) N R s)
        (hΦ := counterDepthMass_measurable (L := L) (K := K) N R s)
        (r := counterDepthRate n s)
        hdepth_drift H c₀ (counterDepthThreshold R s) hθ0 hθtop
  calc
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
        {c : Config (AgentState L K) |
          counterDepthThreshold R s ≤
            counterDepthMass (L := L) (K := K) N R s c}
        ≤
      (counterDepthRate n s) ^ H *
          counterDepthMass (L := L) (K := K) N R s c₀ /
        counterDepthThreshold R s := htail
    _ ≤ (counterDepthRate n s) ^ H * (n : ℝ≥0∞) /
          counterDepthThreshold R s := by
          gcongr
    _ = counterDepthTail n H R s := rfl

/--
Final synchronized-reset MGF tail for the aggregate counter-depth mass.

The only carried input is `CounterDepthMassDriftHypothesis`; the start-mass bound is
proved above from `WinN` plus synchronized reset.
-/
theorem counterDepthMass_tail
    (n N H R : ℕ) (s : ℝ)
    (c₀ : Config (AgentState L K))
    (hwin₀ : CounterSurvivalConc.WinN (L := L) (K := K) N n c₀)
    (hreset : ∀ a ∈ c₀, a.role = Role.clock → a.counter.val = R)
    (hdepth_drift :
      CounterDepthMassDriftHypothesis (L := L) (K := K) n N R s) :
    ((NonuniformMajority L K).transitionKernel ^ H) c₀
      {c : Config (AgentState L K) |
        counterDepthThreshold R s ≤
          counterDepthMass (L := L) (K := K) N R s c}
      ≤ counterDepthTail n H R s :=
  counterDepthMass_tail_of_drift
    (L := L) (K := K) n N H R s c₀
    (counterDepthMass_start_le_n
      (L := L) (K := K) n N R s c₀ hwin₀ hreset)
    hdepth_drift

end ClockCounterDepthCover
end ExactMajority
