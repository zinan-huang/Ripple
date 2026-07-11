/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-2 / Phase-9 epidemic phase at O(log n) PARALLEL time

This file is the **Avenue A0** de-risk of the Doty et al. Theorem 3.1 time-half
campaign (see `DOTY_TIME_SCOPING.md`).  The campaign's central technical fact is
that the existing `PhaseConvergence` instances are at the WRONG time scale
(Θ(n² log n) parallel time — liveness witnesses), whereas the time theorem needs
O(log n) parallel time.

We build ONE untimed epidemic phase — the opinion-set epidemic of Phases 2/9 —
as a `MilestonePhase`, run it through the existing 0-sorry Janson engine
(`milestone_hitting_time_bound` / `MilestonePhase.toPhaseConvergence`), and prove
that the resulting `PhaseConvergence` has

  * interaction count `t ≤ C · n · (Real.log n + 1)`     (= O(log n) PARALLEL time)
  * failure probability `ε ≤ 1 / n`.

The carrier is the **canonical rumor epidemic** `epidemicProto : Protocol Bool`
with the single reaction `(a, b) ↦ (a ‖ b, a ‖ b)`.  This is exactly the
opinion-union dynamics of `Phase2Transition` (`opinionsUnion`) restricted to a
single sign bit — i.e. the minimal faithful model of the Phase-2/9 epidemic
spread.  Working with `Bool` lets the per-step probability bound be derived
*honestly and completely* from the real uniform random-pair scheduler
(`Scheduler.lean`), which is the substantive piece A0 is meant to exercise.

### What this proves (the A0 question)

The whole pipeline — random-pair scheduler ⇒ per-step advance probability
Ω(1/n) ⇒ `MilestonePhase` ⇒ Janson tail ⇒ `PhaseConvergence` — delivers
O(log n) parallel time at the CORRECT scale, with ε ≤ 1/n, end to end and
0-sorry.  The milestone calibration (k = n−1 unit-coverage milestones,
`meanTime = Θ(n log n)` interactions, `pMin = 1/n`) is the reusable template
every epidemic phase (2, 4, 9, and the catch-up part of 3, 5, 6, 8) consumes.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.JansonHitting
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace Phase2Time

/-! ## The canonical rumor-epidemic protocol -/

/-- The canonical rumor / opinion epidemic on a single sign bit.
`true` = "holds the spreading opinion" (informed), `false` = uninformed.
The reaction is `(a, b) ↦ (a ‖ b, a ‖ b)`: meeting an informed agent informs
you.  This is `opinionsUnion` of `Phase2Transition` restricted to one bit. -/
def epidemicProto : Protocol Bool where
  δ a b := (a || b, a || b)

/-- The number of informed (`true`) agents in a configuration. -/
def informed (c : Config Bool) : ℕ := c.count true

@[simp] theorem epidemicProto_delta (a b : Bool) :
    epidemicProto.δ a b = (a || b, a || b) := rfl

/-! ## Monotonicity of the infected count -/

/-- Exact value of `count true` of the chosen-pair update when applicable. -/
theorem informed_stepOrSelf_applicable (c : Config Bool) (r₁ r₂ : Bool)
    (happ : Protocol.Applicable c r₁ r₂) :
    informed (Protocol.stepOrSelf epidemicProto c r₁ r₂)
      = (Multiset.count true c
          - Multiset.count true ({r₁, r₂} : Multiset Bool))
        + Multiset.count true ({r₁ || r₂, r₁ || r₂} : Multiset Bool) := by
  have hc' : Protocol.stepOrSelf epidemicProto c r₁ r₂
      = c - {r₁, r₂} + {r₁ || r₂, r₁ || r₂} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  rw [hc']
  show Multiset.count true (c - {r₁, r₂} + {r₁ || r₂, r₁ || r₂}) = _
  rw [Multiset.count_add, Multiset.count_sub]

/-- The informed count is non-decreasing under any chosen-pair update. -/
theorem informed_stepOrSelf_ge (c : Config Bool) (r₁ r₂ : Bool) :
    informed c ≤ informed (Protocol.stepOrSelf epidemicProto c r₁ r₂) := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have happ' : ({r₁, r₂} : Multiset Bool) ≤ c := happ
    have hsub : Multiset.count true ({r₁, r₂} : Multiset Bool) ≤ Multiset.count true c :=
      Multiset.le_iff_count.mp happ' true
    rw [informed_stepOrSelf_applicable c r₁ r₂ happ]
    show Multiset.count true c ≤ _
    -- count true {x,y} ≤ count true {x‖y, x‖y} + (already removed): case on bits
    rcases r₁ with _ | _ <;> rcases r₂ with _ | _ <;>
      revert hsub <;>
      simp only [Bool.or_false, Bool.or_true, Bool.false_or, Bool.true_or,
        show ({false, false} : Multiset Bool) = false ::ₘ {false} from rfl,
        show ({false, true} : Multiset Bool) = false ::ₘ {true} from rfl,
        show ({true, false} : Multiset Bool) = true ::ₘ {false} from rfl,
        show ({true, true} : Multiset Bool) = true ::ₘ {true} from rfl,
        Multiset.count_cons, Multiset.count_singleton, if_true, if_false,
        Bool.true_eq_false, Bool.false_eq_true, reduceCtorEq] <;>
      intro hsub <;> omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- The `milestone_monotone` field instance: any predicate of the form
`m ≤ informed c` is preserved on the support of one step. -/
theorem informed_ge_monotone (m : ℕ) (c c' : Config Bool)
    (h : m ≤ informed c)
    (hc' : c' ∈ (epidemicProto.stepDistOrSelf c).support) :
    m ≤ informed c' := by
  classical
  -- support point comes from some scheduled pair
  by_cases hc : 2 ≤ c.card
  · rw [show epidemicProto.stepDistOrSelf c = epidemicProto.stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support epidemicProto c hc c' hc'
    rw [← hr]
    exact le_trans h (informed_stepOrSelf_ge c r₁ r₂)
  · rw [show epidemicProto.stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'
    exact h

/-! ## The per-step epidemic-advance probability (the substantive piece)

The scheduler picks an ordered state pair `(true, false)` — an informed/uninformed
meeting — with probability `interactionProb c true false =
(count true · count false) / (card · (card − 1))`.  That meeting fires the rumor
reaction and raises the informed count by one.  Hence the one-step probability of
advancing the informed count is at least that. -/

/-- Over `Bool`, the informed and uninformed counts sum to the population. -/
theorem informed_add_uninformed (c : Config Bool) :
    c.count true + c.count false = c.card := by
  classical
  have h := Multiset.card_eq_countP_add_countP (p := fun b : Bool => b = true) c
  rw [h]
  show Multiset.count true c + Multiset.count false c = _
  rw [Multiset.count, Multiset.count]
  congr 1
  · refine Multiset.countP_congr rfl ?_
    intro x _; cases x <;> simp
  · refine Multiset.countP_congr rfl ?_
    intro x _; cases x <;> simp

/-- For `PMF.map`, the image point gets at least the source mass. -/
theorem map_apply_ge {α β : Type*} (f : α → β) (p : PMF α) (a : α) :
    p a ≤ (PMF.map f p) (f a) := by
  classical
  rw [PMF.map_apply]
  calc p a = (if f a = f a then p a else 0) := by rw [if_pos rfl]
    _ ≤ ∑' a' : α, (if f a = f a' then p a' else 0) :=
        ENNReal.le_tsum a

/-- **Per-step epidemic advance.**  If `n = c.card ≥ 2` and the informed count is
exactly `j` with `1 ≤ j ≤ n−1`, then a single scheduler step raises the informed
count to `≥ j+1` with probability at least `j·(n−j) / (n·(n−1))`. -/
theorem step_advance_prob (c : Config Bool) (j : ℕ)
    (hc : 2 ≤ c.card) (hj : informed c = j) (hj1 : 1 ≤ j) (hjn : j < c.card) :
    (epidemicProto.stepDistOrSelf c).toMeasure {c' | j + 1 ≤ informed c'} ≥
      ENNReal.ofReal
        ((j * (c.card - j) : ℝ) / (c.card * (c.card - 1) : ℝ)) := by
  classical
  set n := c.card with hn
  -- count false = n - j
  have hct : c.count true = j := hj
  have hcf : c.count false = n - j := by
    have := informed_add_uninformed c
    unfold informed at hj
    omega
  -- applicability of the (true,false) state pair
  have htf_pos : 1 ≤ c.count true := by rw [hct]; exact hj1
  have hff_pos : 1 ≤ c.count false := by rw [hcf]; omega
  have htf_pos' : 1 ≤ Multiset.count true c := htf_pos
  have hff_pos' : 1 ≤ Multiset.count false c := hff_pos
  have happ : Protocol.Applicable c true false := by
    refine Multiset.le_iff_count.mpr ?_
    intro a
    rw [show ({true, false} : Multiset Bool) = true ::ₘ {false} from rfl]
    cases a <;>
      simp only [Multiset.count_cons, Multiset.count_singleton, if_true, if_false,
        Bool.true_eq_false, Bool.false_eq_true] <;> omega
  -- the resulting config has informed count j+1
  have hpost : j + 1 ≤ informed (Protocol.stepOrSelf epidemicProto c true false) := by
    rw [informed_stepOrSelf_applicable c true false happ]
    rw [show ({true, false} : Multiset Bool) = true ::ₘ {false} from rfl,
      show ({true || false, true || false} : Multiset Bool) = true ::ₘ {true} from rfl]
    simp only [Multiset.count_cons, Multiset.count_singleton, if_true, if_false,
      reduceCtorEq, Bool.true_eq_false, Bool.false_eq_true]
    have hct' : Multiset.count true c = j := hct
    omega
  -- the one-step PMF
  have hstepDist : epidemicProto.stepDistOrSelf c = epidemicProto.stepDist c hc := by
    unfold Protocol.stepDistOrSelf; rw [dif_pos hc]
  -- the singleton {scheduledStep c (true,false)} is inside the milestone set
  set q : Config Bool := Protocol.scheduledStep epidemicProto c (true, false) with hq
  have hq_eq : q = Protocol.stepOrSelf epidemicProto c true false := rfl
  have hq_mem : q ∈ {c' : Config Bool | j + 1 ≤ informed c'} := by
    show j + 1 ≤ informed q
    rw [hq_eq]; exact hpost
  -- bound: toMeasure M ≥ toMeasure {q} = (stepDist c hc) q ≥ interactionPMF (true,false)
  have hsubset : ({q} : Set (Config Bool)) ⊆ {c' | j + 1 ≤ informed c'} := by
    intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact hq_mem
  have h_meas_single : MeasurableSet ({q} : Set (Config Bool)) :=
    DiscreteMeasurableSpace.forall_measurableSet _
  calc (epidemicProto.stepDistOrSelf c).toMeasure {c' | j + 1 ≤ informed c'}
      ≥ (epidemicProto.stepDistOrSelf c).toMeasure ({q} : Set (Config Bool)) :=
        measure_mono hsubset
    _ = (epidemicProto.stepDistOrSelf c) q := by
        rw [PMF.toMeasure_apply_singleton _ _ h_meas_single]
    _ ≥ ENNReal.ofReal
          ((j * (n - j) : ℝ) / (n * (n - 1) : ℝ)) := ?_
  -- now bound the PMF value at q
  rw [hstepDist]
  show ENNReal.ofReal _ ≤ (epidemicProto.stepDist c hc) q
  unfold Protocol.stepDist
  refine le_trans ?_ (map_apply_ge (Protocol.scheduledStep epidemicProto c)
    (c.interactionPMF hc) (true, false))
  -- interactionPMF (true,false) = interactionProb c true false
  show ENNReal.ofReal _ ≤ (c.interactionPMF hc) (true, false)
  have hpmf : (c.interactionPMF hc) (true, false) = c.interactionProb true false := rfl
  rw [hpmf]
  unfold Config.interactionProb Config.interactionCount
  simp only [show (true : Bool) ≠ false by decide, if_false, reduceCtorEq]
  rw [hct, hcf]
  -- both sides equal ofReal of the same nat ratio
  have hjn' : j ≤ n := le_of_lt hjn
  have hn1 : 1 ≤ n := by omega
  have htp : c.totalPairs = n * (n - 1) := rfl
  rw [htp]
  have hden_pos : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by
    have : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hRHS : ((j * (n - j) : ℕ) : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal (((j * (n - j) : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ)) := by
    rw [ENNReal.ofReal_div_of_pos hden_pos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [hRHS]
  apply ENNReal.ofReal_le_ofReal
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hjn', Nat.cast_sub hn1, Nat.cast_one]

/-- An all-uninformed configuration stays all-uninformed under one step. -/
theorem informed_zero_monotone (c c' : Config Bool)
    (h0 : informed c = 0) (hc' : c' ∈ (epidemicProto.stepDistOrSelf c).support) :
    informed c' = 0 := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show epidemicProto.stepDistOrSelf c = epidemicProto.stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support epidemicProto c hc c' hc'
    rw [← hr]
    -- count true c = 0, so r₁ = r₂ = false on the support; result has no true
    by_cases happ : Protocol.Applicable c r₁ r₂
    · rw [Protocol.scheduledStep, informed_stepOrSelf_applicable c r₁ r₂ happ]
      -- count true c = 0
      have hct0 : Multiset.count true c = 0 := h0
      -- both selected states must be false (else count true c > 0)
      have hr1f : r₁ = false := by
        by_contra hne; have : r₁ = true := by cases r₁ <;> simp_all
        subst this
        have : 1 ≤ Multiset.count true c := by
          have := Multiset.le_iff_count.mp happ true
          rw [show ({true, r₂} : Multiset Bool) = true ::ₘ {r₂} from rfl] at this
          simp only [Multiset.count_cons, Multiset.count_singleton, if_true] at this
          omega
        omega
      have hr2f : r₂ = false := by
        by_contra hne; have : r₂ = true := by cases r₂ <;> simp_all
        subst this
        have := Multiset.le_iff_count.mp happ true
        rw [show ({r₁, true} : Multiset Bool) = r₁ ::ₘ {true} from rfl] at this
        simp only [Multiset.count_cons, Multiset.count_singleton, if_true] at this
        rcases r₁ with _ | _ <;> simp_all <;> omega
      subst hr1f; subst hr2f
      simp only [Bool.or_false, informed]
      rw [show ({false, false} : Multiset Bool) = false ::ₘ {false} from rfl]
      simp only [Multiset.count_cons, Multiset.count_singleton, if_false,
        reduceCtorEq, Bool.false_eq_true]
      omega
    · rw [Protocol.scheduledStep, Protocol.stepOrSelf_eq_self_of_not_applicable happ]
      exact h0
  · rw [show epidemicProto.stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'; exact h0

/-! ## The epidemic milestone phase -/

/-- The milestone for level `i` over a population of `n` agents.  The two guard
disjuncts (`card ≠ n`, `informed = 0`) are absorbing dead states excluded by
`Pre`; they make `progress` hold *unconditionally* — the hypothesis of `progress`
can only fire on a live, exactly-`n`-agent, partially-informed configuration,
which is precisely where the scheduler bound `step_advance_prob` applies. -/
def epMilestone (n i : ℕ) (c : Config Bool) : Prop :=
  c.card ≠ n ∨ informed c = 0 ∨ i + 2 ≤ informed c

/-- The calibrated per-step probability for level `i` over `n` agents:
`(i+1)·(n−(i+1)) / (n·(n−1))`, the chance the scheduler picks an
informed/uninformed pair when exactly `i+1` agents are informed. -/
noncomputable def epP (n i : ℕ) : ℝ :=
  ((i + 1) * (n - (i + 1)) : ℝ) / (n * (n - 1) : ℝ)

/-- Real-arithmetic facts available whenever `2 ≤ n` and `i + 1 < n`. -/
theorem epP_facts {n i : ℕ} (hn : 2 ≤ n) (hi : i + 1 < n) :
    (1 : ℝ) ≤ (i : ℝ) + 1 ∧ (i : ℝ) + 1 < n ∧ (0 : ℝ) < (n : ℝ) - 1 ∧
      (0 : ℝ) < ((i : ℝ) + 1) * ((n : ℝ) - ((i : ℝ) + 1)) ∧
      (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
  have hiR : (i : ℝ) + 1 < n := by exact_mod_cast hi
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  refine ⟨by linarith, hiR, by linarith, ?_, by nlinarith⟩
  have h1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (n : ℝ) - ((i : ℝ) + 1) := by linarith
  positivity

theorem epP_pos {n i : ℕ} (hn : 2 ≤ n) (hi : i + 1 < n) : 0 < epP n i := by
  obtain ⟨_, _, _, hnum, hden⟩ := epP_facts hn hi
  unfold epP
  exact div_pos hnum hden

theorem epP_le_one {n i : ℕ} (hn : 2 ≤ n) (hi : i + 1 < n) : epP n i ≤ 1 := by
  obtain ⟨h1, hi1, hd, _, hden⟩ := epP_facts hn hi
  unfold epP
  rw [div_le_one hden]
  nlinarith [h1, hi1, hd]

/-- `card` is preserved on the one-step support, so the `card ≠ n` guard is
monotone. -/
theorem card_eq_monotone (n : ℕ) (c c' : Config Bool)
    (h : c.card = n) (hc' : c' ∈ (epidemicProto.stepDistOrSelf c).support) :
    c'.card = n := by
  rw [Protocol.stepDistOrSelf_support_card_eq epidemicProto c c' hc', h]

/-- **The epidemic milestone phase** over a population of `n` agents.
`k = n − 1` unit-coverage milestones; per-step probability `epP n i`. -/
noncomputable def epidemicMilestonePhase (n : ℕ) (hn : 2 ≤ n) :
    MilestonePhase epidemicProto where
  k := n - 1
  milestone i c := epMilestone n i.val c
  p i := epP n i.val
  hp_pos i := epP_pos hn (by have := i.isLt; omega)
  hp_le_one i := epP_le_one hn (by have := i.isLt; omega)
  milestone_monotone := by
    rintro i c c' (hcard | hinf0 | hcov) hsupp
    · -- card ≠ n is preserved
      left
      have hcc : c'.card = c.card :=
        Protocol.stepDistOrSelf_support_card_eq epidemicProto c c' hsupp
      rw [hcc]; exact hcard
    · -- informed = 0 preserved
      right; left
      exact informed_zero_monotone c c' hinf0 hsupp
    · -- i+2 ≤ informed preserved (informed non-decreasing)
      right; right
      exact informed_ge_monotone (i.val + 2) c c' hcov hsupp
  progress := by
    intro i c hprev hcur
    -- ¬milestone i means: card = n ∧ informed ≠ 0 ∧ informed < i+2
    rw [epMilestone, not_or, not_or] at hcur
    obtain ⟨hcard, hinf0, hcovlt⟩ := hcur
    have hcard' : c.card = n := not_not.mp hcard
    have hinflt : informed c < i.val + 2 := by omega
    -- previous milestones pin informed to i+1
    have hge : i.val + 1 ≤ informed c := by
      rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
      · -- i = 0: informed ≠ 0 ⇒ informed ≥ 1 = i+1
        omega
      · -- i ≥ 1: milestone (i-1) holds and forces (i-1)+2 = i+1 ≤ informed
        have hprev' := hprev ⟨i.val - 1, by omega⟩ (by
          refine Fin.mk_lt_mk.mpr ?_; omega)
        rw [epMilestone] at hprev'
        rcases hprev' with h | h | h
        · exact absurd hcard' h
        · exact absurd h hinf0
        · simp only at h; omega
    have hjeq : informed c = i.val + 1 := by omega
    -- apply the scheduler per-step bound at j = i+1
    have hc2 : 2 ≤ c.card := by rw [hcard']; exact hn
    have hjn : i.val + 1 < c.card := by rw [hcard']; have := i.isLt; omega
    have hbound := step_advance_prob c (i.val + 1) hc2 hjeq (by omega) hjn
    -- the milestone set contains the advance set {i+2 ≤ informed}
    have hsubset : {c' : Config Bool | (i.val + 1) + 1 ≤ informed c'}
        ⊆ {c' : Config Bool | epMilestone n i.val c'} := by
      intro x hx
      right; right
      have : (i.val + 1) + 1 ≤ informed x := hx
      omega
    -- transport the bound through the milestone set and rewrite to epP
    show (epidemicProto.stepDistOrSelf c).toMeasure {c' | epMilestone n i.val c'}
      ≥ ENNReal.ofReal (epP n i.val)
    -- normalise hbound's ofReal argument to epP n i
    have heq : (((i.val + 1 : ℕ)) * (c.card - (i.val + 1 : ℕ)) : ℝ)
        / (c.card * (c.card - 1) : ℝ) = epP n i.val := by
      rw [hcard']
      unfold epP
      push_cast
      ring
    rw [heq] at hbound
    calc (epidemicProto.stepDistOrSelf c).toMeasure {c' | epMilestone n i.val c'}
        ≥ (epidemicProto.stepDistOrSelf c).toMeasure
            {c' : Config Bool | (i.val + 1) + 1 ≤ informed c'} := measure_mono hsubset
      _ ≥ ENNReal.ofReal (epP n i.val) := hbound

/-! ## Harmonic-sum calibration of `meanTime`

`1/epP(n,i) = n(n-1)/((i+1)(n-1-i))`.  Summed over `i = 0..n-2`, with
`m = i+1 ∈ 1..n-1`, this is `n(n-1)·Σ 1/(m(n-m)) = 2(n-1)·H_{n-1}`.  We never need
the exact value — only `meanTime ≤ 2(n-1)(1+log n)` (for `t = O(n log n)`) and
`pMin·meanTime ≥ log n` (for `ε ≤ 1/n`).  Both follow from the telescoping
harmonic bounds `log(M+1) ≤ Σ_{m=1}^M 1/m ≤ 1 + log M`. -/

open Finset in
/-- Telescoping upper bound: `Σ_{m=1}^{M} 1/(m+1) ≤ log (M+1)`. -/
theorem sum_inv_succ_le_log (M : ℕ) :
    ∑ m ∈ range M, (1 : ℝ) / (m + 2) ≤ Real.log (M + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ]
      have hstep : (1 : ℝ) / (M + 2) ≤ Real.log (M + 2) - Real.log (M + 1) := by
        have hx : (0 : ℝ) < (M + 2) / (M + 1) := by positivity
        have h := Real.one_sub_inv_le_log_of_pos hx
        rw [Real.log_div (by positivity) (by positivity)] at h
        have hinv : ((M + 2) / (M + 1) : ℝ)⁻¹ = (M + 1) / (M + 2) := by
          rw [inv_div]
        rw [hinv] at h
        have heq : (1 : ℝ) - (M + 1) / (M + 2) = 1 / (M + 2) := by
          field_simp; ring
        linarith [h, heq.le, heq.symm.le]
      calc (∑ m ∈ range M, (1 : ℝ) / (m + 2)) + 1 / (M + 2)
          ≤ Real.log (M + 1) + (Real.log (M + 2) - Real.log (M + 1)) :=
            add_le_add ih hstep
        _ = Real.log (M + 2) := by ring
        _ = Real.log (↑(M + 1) + 1) := by norm_num; ring_nf

open Finset in
/-- Telescoping lower bound: `log (M+1) ≤ Σ_{m=1}^{M} 1/m`. -/
theorem log_le_sum_inv (M : ℕ) :
    Real.log (M + 1) ≤ ∑ m ∈ range M, (1 : ℝ) / (m + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ]
      have hstep : Real.log (M + 2) - Real.log (M + 1) ≤ (1 : ℝ) / (M + 1) := by
        have hx : (0 : ℝ) < (M + 2) / (M + 1) := by positivity
        have h := Real.log_le_sub_one_of_pos hx
        rw [Real.log_div (by positivity) (by positivity)] at h
        have heq : ((M + 2) / (M + 1) : ℝ) - 1 = 1 / (M + 1) := by field_simp; ring
        linarith
      calc Real.log (↑(M + 1) + 1)
          = Real.log (M + 2) := by norm_num; ring_nf
        _ = Real.log (M + 1) + (Real.log (M + 2) - Real.log (M + 1)) := by ring
        _ ≤ (∑ m ∈ range M, (1 : ℝ) / (m + 1)) + 1 / (M + 1) := add_le_add ih hstep

/-- Exact partial fraction: `(epP n i)⁻¹ = (n−1)·(1/(i+1) + 1/(n−1−i))`. -/
theorem inv_epP_eq (n i : ℕ) (hn : 2 ≤ n) (hi : i + 1 < n) :
    (epP n i)⁻¹
      = ((n : ℝ) - 1) * ((1 : ℝ) / (i + 1) + (1 : ℝ) / ((n : ℝ) - 1 - i)) := by
  obtain ⟨h1, hi1, hd, hnum, hden⟩ := epP_facts hn hi
  unfold epP
  have hi1' : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hni : (0 : ℝ) < (n : ℝ) - 1 - i := by
    have : (i : ℝ) + 1 < n := hi1
    linarith
  have hni' : ((n : ℝ) - 1 - i) ≠ 0 := ne_of_gt hni
  have hi1ne : ((i : ℝ) + 1) ≠ 0 := ne_of_gt hi1'
  have hnm : ((n : ℝ) - ((i : ℝ) + 1)) ≠ 0 := by
    have : (i : ℝ) + 1 < n := hi1; intro hc; linarith [hc]
  rw [inv_div]
  rw [div_add_div _ _ hi1ne hni', div_eq_iff (by positivity)]
  field_simp
  ring

open Finset in
/-- `Σ_{i=0}^{M-1} 1/(M-i) = Σ_{j=1}^{M} 1/j` by the reflection `i ↦ M-1-i`. -/
theorem sum_inv_reflect (M : ℕ) :
    ∑ i ∈ range M, (1 : ℝ) / ((M : ℝ) - i) = ∑ m ∈ range M, (1 : ℝ) / (m + 1) := by
  rw [← Finset.sum_range_reflect (fun m => (1 : ℝ) / (m + 1)) M]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  congr 1
  have : ((M - 1 - i : ℕ) : ℝ) = (M : ℝ) - 1 - i := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  rw [this]; ring

/-! ### `meanTime` value and two-sided bounds -/

open Finset in
/-- `meanTime = (n−1) · Σ_{i<n−1} (1/(i+1) + 1/(n−1−i))`. -/
theorem meanTime_eq (n : ℕ) (hn : 2 ≤ n) :
    (epidemicMilestonePhase n hn).meanTime
      = ((n : ℝ) - 1) *
          ∑ i ∈ range (n - 1),
            ((1 : ℝ) / (i + 1) + (1 : ℝ) / ((n : ℝ) - 1 - i)) := by
  unfold MilestonePhase.meanTime
  show ∑ i : Fin (n - 1), (epP n i.val)⁻¹ = _
  rw [Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => (epP n i)⁻¹)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  exact inv_epP_eq n i hn (by omega)

open Finset in
/-- `Σ_{i<n−1} (1/(i+1) + 1/(n−1−i)) = 2 · Σ_{m<n−1} 1/(m+1)`. -/
theorem meanTime_sum_eq (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ range (n - 1), ((1 : ℝ) / (i + 1) + (1 : ℝ) / ((n : ℝ) - 1 - i))
      = 2 * ∑ m ∈ range (n - 1), (1 : ℝ) / (m + 1) := by
  rw [Finset.sum_add_distrib]
  have hrefl : ∑ i ∈ range (n - 1), (1 : ℝ) / ((n : ℝ) - 1 - i)
      = ∑ m ∈ range (n - 1), (1 : ℝ) / (m + 1) := by
    have hkey := sum_inv_reflect (n - 1)
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcast] at hkey
    rw [← hkey]
  rw [hrefl]
  ring

/-- Upper bound: `meanTime ≤ 2(n−1)(1 + log n)`. -/
theorem meanTime_le (n : ℕ) (hn : 2 ≤ n) :
    (epidemicMilestonePhase n hn).meanTime ≤ 2 * ((n : ℝ) - 1) * (1 + Real.log n) := by
  rw [meanTime_eq n hn, meanTime_sum_eq n hn]
  have hH : ∑ m ∈ Finset.range (n - 1), (1 : ℝ) / (m + 1) ≤ 1 + Real.log n := by
    -- split off the first term, telescope the rest
    have hn1 : n - 1 = (n - 2) + 1 := by omega
    have hsplit : ∑ m ∈ Finset.range (n - 1), (1 : ℝ) / (m + 1)
        = 1 + ∑ m ∈ Finset.range (n - 2), (1 : ℝ) / (m + 2) := by
      rw [hn1, Finset.sum_range_succ']
      simp only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add]
      rw [add_comm]
      congr 1
      · norm_num
      · apply Finset.sum_congr rfl
        intro x _; congr 1; push_cast; ring
    rw [hsplit]
    have htel := sum_inv_succ_le_log (n - 2)
    have hcast : Real.log (↑(n - 2) + 1) ≤ Real.log n := by
      apply Real.log_le_log (by positivity)
      rw [Nat.cast_sub (by omega)]; push_cast
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hlog0 : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    linarith [htel, hcast]
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  nlinarith [hH, hn1]

/-- Each level probability is at least `1/n`. -/
theorem epP_ge_inv_n (n i : ℕ) (hn : 2 ≤ n) (hi : i + 1 < n) :
    (1 : ℝ) / n ≤ epP n i := by
  obtain ⟨h1, hi1, hd, _, hden⟩ := epP_facts hn hi
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold epP
  rw [div_le_div_iff₀ (by positivity) hden]
  -- 1 * (n*(n-1)) ≤ (i+1)(n-(i+1)) * n.  Suffices (i+1)(n-(i+1)) ≥ n-1.
  have hkey : ((n : ℝ) - 1) ≤ ((i : ℝ) + 1) * ((n : ℝ) - ((i : ℝ) + 1)) := by
    -- (i+1)(n-i-1) - (n-1) = i(n-2-i) ≥ 0  for 0 ≤ i ≤ n-2
    have hile : (i : ℝ) + 1 ≤ n - 1 := by
      have : (i : ℝ) + 1 + 1 ≤ n := by
        have : (i : ℝ) + 2 ≤ n := by exact_mod_cast (by omega : i + 2 ≤ n)
        linarith
      linarith
    nlinarith [hi0, hile, hd]
  nlinarith [hkey, hnR, hd]

/-- `pMin ≥ 1/n`. -/
theorem pMin_ge (n : ℕ) (hn : 2 ≤ n) :
    (1 : ℝ) / n ≤ (epidemicMilestonePhase n hn).pMin := by
  have hk : (epidemicMilestonePhase n hn).k = n - 1 := rfl
  haveI : Nonempty (Fin (epidemicMilestonePhase n hn).k) := by
    rw [hk]; exact ⟨⟨0, by omega⟩⟩
  unfold MilestonePhase.pMin
  apply le_ciInf
  intro i
  show (1 : ℝ) / n ≤ epP n i.val
  have hilt : i.val < n - 1 := lt_of_lt_of_eq i.isLt hk
  exact epP_ge_inv_n n i.val hn (by omega)

open Finset in
/-- Lower bound: `meanTime ≥ n · log n`. -/
theorem meanTime_ge (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * Real.log n ≤ (epidemicMilestonePhase n hn).meanTime := by
  rw [meanTime_eq n hn, meanTime_sum_eq n hn]
  -- Σ 1/(m+1) ≥ log n  (since Σ_{m<n-1} 1/(m+1) ≥ log((n-1)+1) = log n)
  have hH : Real.log n ≤ ∑ m ∈ range (n - 1), (1 : ℝ) / (m + 1) := by
    have htel := log_le_sum_inv (n - 1)
    have hcast : Real.log (↑(n - 1) + 1) = Real.log n := by
      congr 1; rw [Nat.cast_sub (by omega)]; push_cast; ring
    rwa [hcast] at htel
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlog0 : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  -- (n-1)·2·H ≥ (n-1)·2·log n ≥ n·log n   (since 2(n-1) ≥ n for n ≥ 2)
  have h2n : (n : ℝ) ≤ 2 * ((n : ℝ) - 1) := by linarith
  nlinarith [hH, hn1, hlog0, h2n]

/-- `pMin · meanTime ≥ log n`. -/
theorem pMin_mul_meanTime_ge (n : ℕ) (hn : 2 ≤ n) :
    Real.log n ≤ (epidemicMilestonePhase n hn).pMin * (epidemicMilestonePhase n hn).meanTime := by
  have hpm := pMin_ge n hn
  have hmt := meanTime_ge n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmtpos : (0 : ℝ) ≤ (epidemicMilestonePhase n hn).meanTime := by
    have : (0 : ℝ) ≤ (n : ℝ) * Real.log n :=
      mul_nonneg (le_of_lt hnpos) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
    linarith
  -- pMin·meanTime ≥ (1/n)·(n log n) = log n
  have hlb : (1 / (n : ℝ)) * ((n : ℝ) * Real.log n) ≤
      (epidemicMilestonePhase n hn).pMin * (epidemicMilestonePhase n hn).meanTime := by
    refine mul_le_mul hpm hmt ?_ ?_
    · have : (0 : ℝ) ≤ (n : ℝ) * Real.log n :=
        mul_nonneg (le_of_lt hnpos) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
      linarith
    · have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
      linarith [le_trans this hpm]
  have : (1 / (n : ℝ)) * ((n : ℝ) * Real.log n) = Real.log n := by
    field_simp
  linarith [hlb, this.symm.le, this.le]

theorem log_five_le_two : Real.log 5 ≤ 2 := by
  rw [show (2 : ℝ) = Real.log (Real.exp 2) from (Real.log_exp 2).symm]
  apply Real.log_le_log (by norm_num)
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  rw [this]; nlinarith [he]

/-! ## The O(log n) PhaseConvergence instance (the A0 deliverable) -/

/-- The interaction-count window for the epidemic phase: `⌈5 · meanTime⌉`. -/
noncomputable def epidemicWindow (n : ℕ) (hn : 2 ≤ n) : ℕ :=
  ⌈(5 : ℝ) * (epidemicMilestonePhase n hn).meanTime⌉₊

/-- **The Phase-2/9 epidemic `PhaseConvergence` at O(log n) parallel time.**

Built directly from the 0-sorry Janson engine `milestone_hitting_time_bound`
with `λ = 5`.  `Pre` = "exactly one informed agent in a size-`n` population";
`Post` = the milestone postcondition (all-informed, modulo the dead/size guards);
`t = ⌈5·meanTime⌉` interactions; `ε = 1/n`. -/
noncomputable def epidemicPhaseConvergence (n : ℕ) (hn : 2 ≤ n) :
    PhaseConvergence epidemicProto.transitionKernel where
  Pre c := c.card = n ∧ informed c = 1
  Post := (epidemicMilestonePhase n hn).Post
  t := epidemicWindow n hn
  ε := (1 / n : ℝ≥0)
  post_absorbing := fun c hc => (epidemicMilestonePhase n hn).post_absorbing c hc
  convergence := by
    intro c₀ ⟨hcard, hinf⟩
    -- Pre ⇒ no milestone initially
    have hPre : ∀ i : Fin (epidemicMilestonePhase n hn).k,
        ¬(epidemicMilestonePhase n hn).milestone i c₀ := by
      intro i hmile
      rcases hmile with h | h | h
      · exact h hcard
      · rw [hinf] at h; exact absurd h (by norm_num)
      · rw [hinf] at h; omega
    -- meanTime ≥ 0
    have hmtpos : (0 : ℝ) ≤ (epidemicMilestonePhase n hn).meanTime := by
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have := meanTime_ge n hn
      have h2 : (0 : ℝ) ≤ (n : ℝ) * Real.log n :=
        mul_nonneg (le_of_lt hnpos) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
      linarith
    -- the window dominates 5·meanTime
    have ht : (5 : ℝ) * (epidemicMilestonePhase n hn).meanTime ≤ (epidemicWindow n hn : ℝ) := by
      unfold epidemicWindow
      exact Nat.le_ceil _
    -- Janson tail at λ = 5
    have hbound := milestone_hitting_time_bound (epidemicMilestonePhase n hn) c₀ hPre 5
      (by norm_num) (epidemicWindow n hn) ht
    -- bound the exp by 1/n
    have hexp : Real.exp (-(epidemicMilestonePhase n hn).pMin *
        (epidemicMilestonePhase n hn).meanTime * (5 - 1 - Real.log 5)) ≤ (1 / n : ℝ) := by
      have hlog5 := log_five_le_two
      have hfac : (1 : ℝ) ≤ 5 - 1 - Real.log 5 := by linarith
      have hpmmt := pMin_mul_meanTime_ge n hn
      have hpmmt0 : (0 : ℝ) ≤ (epidemicMilestonePhase n hn).pMin *
          (epidemicMilestonePhase n hn).meanTime :=
        le_trans (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))) hpmmt
      -- exponent ≥ log n
      have hXge : Real.log n ≤ (epidemicMilestonePhase n hn).pMin *
          (epidemicMilestonePhase n hn).meanTime * (5 - 1 - Real.log 5) := by
        calc Real.log n ≤ (epidemicMilestonePhase n hn).pMin *
              (epidemicMilestonePhase n hn).meanTime * 1 := by rw [mul_one]; exact hpmmt
          _ ≤ (epidemicMilestonePhase n hn).pMin *
              (epidemicMilestonePhase n hn).meanTime * (5 - 1 - Real.log 5) := by
                apply mul_le_mul_of_nonneg_left hfac hpmmt0
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      calc Real.exp (-(epidemicMilestonePhase n hn).pMin *
            (epidemicMilestonePhase n hn).meanTime * (5 - 1 - Real.log 5))
          = Real.exp (-((epidemicMilestonePhase n hn).pMin *
              (epidemicMilestonePhase n hn).meanTime * (5 - 1 - Real.log 5))) := by ring_nf
        _ ≤ Real.exp (-(Real.log n)) := by
              apply Real.exp_le_exp.mpr; linarith
        _ = (Real.exp (Real.log n))⁻¹ := by rw [Real.exp_neg]
        _ = (1 / n : ℝ) := by rw [Real.exp_log hnpos]; rw [one_div]
    -- assemble: (K^t) c₀ {¬Post} ≤ ofReal(exp ...) ≤ ofReal(1/n) = (1/n : ℝ≥0)
    calc (epidemicProto.transitionKernel ^ (epidemicWindow n hn)) c₀
            {c | ¬(epidemicMilestonePhase n hn).Post c}
        ≤ ENNReal.ofReal (Real.exp (-(epidemicMilestonePhase n hn).pMin *
            (epidemicMilestonePhase n hn).meanTime * (5 - 1 - Real.log 5))) := hbound
      _ ≤ ENNReal.ofReal (1 / n : ℝ) := ENNReal.ofReal_le_ofReal hexp
      _ = ((1 / n : ℝ≥0) : ℝ≥0∞) := by
            rw [← ENNReal.ofReal_coe_nnreal]
            norm_num

/-! ## The clean scale statement (A0 verdict)

The epidemic phase converges in `t ≤ 11·n·(log n + 1)` interactions — i.e.
`t/n ≤ 11·(log n + 1) = O(log n)` PARALLEL time — with failure probability
`ε = 1/n`.  This is the CORRECT O(log n) scale (unlike the existing Θ(n²log n)
liveness instances). -/
theorem epidemic_phase_logn_scale (n : ℕ) (hn : 2 ≤ n) :
    -- O(log n) parallel time: the interaction count is ≤ C·n·(log n + 1)
    ((epidemicPhaseConvergence n hn).t : ℝ) ≤ 11 * (n : ℝ) * (Real.log n + 1) ∧
    -- failure probability is exactly 1/n
    (epidemicPhaseConvergence n hn).ε = (1 / n : ℝ≥0) := by
  refine ⟨?_, rfl⟩
  show (epidemicWindow n hn : ℝ) ≤ 11 * (n : ℝ) * (Real.log n + 1)
  unfold epidemicWindow
  -- ⌈5·meanTime⌉ ≤ 5·meanTime + 1 ≤ 5·2(n-1)(1+log n) + 1 ≤ 11 n (log n + 1)
  have hmt := meanTime_le n hn
  have hmtpos : (0 : ℝ) ≤ (epidemicMilestonePhase n hn).meanTime := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have := meanTime_ge n hn
    have h2 : (0 : ℝ) ≤ (n : ℝ) * Real.log n :=
      mul_nonneg (le_of_lt hnpos) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
    linarith
  have hceil : (⌈(5 : ℝ) * (epidemicMilestonePhase n hn).meanTime⌉₊ : ℝ)
      ≤ (5 : ℝ) * (epidemicMilestonePhase n hn).meanTime + 1 := by
    have := Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ 5 * (epidemicMilestonePhase n hn).meanTime)
    linarith
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog0 : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hnR
  -- 5·2(n-1)(1+log n) + 1 ≤ 11 n (log n + 1)
  calc (⌈(5 : ℝ) * (epidemicMilestonePhase n hn).meanTime⌉₊ : ℝ)
      ≤ (5 : ℝ) * (epidemicMilestonePhase n hn).meanTime + 1 := hceil
    _ ≤ (5 : ℝ) * (2 * ((n : ℝ) - 1) * (1 + Real.log n)) + 1 := by
          have h5 : (0 : ℝ) ≤ 5 := by norm_num
          nlinarith [hmt, hmtpos]
    _ ≤ 11 * (n : ℝ) * (Real.log n + 1) := by nlinarith [hnR, hlog0]

end Phase2Time

end ExactMajority
