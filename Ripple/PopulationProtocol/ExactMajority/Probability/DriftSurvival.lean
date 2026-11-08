/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multiplicative-drift survival under a non-closed work window

This file combines the immediate-kill window-survival construction with the
generic geometric-drift theorem.  A natural-valued potential contracts while
the real chain remains in `Inv`; the immediate-kill kernel sends escapes to
the cemetery at once, where the lifted potential is zero.  Geometric decay on
the killed chain and a separate union bound for cemetery mass then give the
real-chain failure bound.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.WindowSurvival
import Ripple.PopulationProtocol.ExactMajority.Probability.Supermartingale

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Ripple.PopulationProtocol.ExactMajority
namespace DriftSurvival

variable {α : Type*}

/-- Lift a natural-valued potential to the cemetery extension, assigning zero
to the cemetery. -/
def potentialLift (Φ : α → ℕ) : Option α → ℝ≥0∞ :=
  fun o => o.elim 0 (fun x => (Φ x : ℝ≥0∞))

@[simp] theorem potentialLift_some (Φ : α → ℕ) (x : α) :
    potentialLift Φ (some x) = (Φ x : ℝ≥0∞) := rfl

@[simp] theorem potentialLift_none (Φ : α → ℕ) :
    potentialLift Φ (none : Option α) = 0 := rfl

variable [MeasurableSpace α] [DiscreteMeasurableSpace α] [Inhabited α]

open GatedDrift

/- The immediate-kill construction fixes the measurable space on `Option α`
to the discrete one.  Repeat those local instances here so all imported kernel
identities elaborate against exactly the same measurable-space instance. -/
local instance instOptionMS : MeasurableSpace (Option α) := ⊤
local instance instOptionDMS : DiscreteMeasurableSpace (Option α) :=
  ⟨fun _ => trivial⟩

omit [MeasurableSpace α] [DiscreteMeasurableSpace α] [Inhabited α] in
theorem measurable_potentialLift (Φ : α → ℕ) : Measurable (potentialLift Φ) :=
  Measurable.of_discrete

/-- Multiplicative drift survives passage to the immediate-kill kernel.

There are three semantic branches.  From a gated alive state, the gate map can
only erase potential, so the real-chain drift hypothesis applies.  From an
ungated alive state and from the cemetery, the killed kernel is the Dirac mass
at the zero-potential cemetery. -/
theorem killNow_lintegral_drift (K : Kernel α α) [IsMarkovKernel K]
    (Inv : α → Prop) (Φ : α → ℕ) (r : ℝ≥0∞)
    (hdrift : ∀ x, Inv x →
      ∫⁻ y, (Φ y : ℝ≥0∞) ∂(K x) ≤ r * (Φ x : ℝ≥0∞)) :
    ∀ o : Option α,
      ∫⁻ o', potentialLift Φ o' ∂(killK_now K {x | Inv x} o)
        ≤ r * potentialLift Φ o := by
  classical
  intro o
  rcases o with _ | x
  · rw [killK_now_none, MeasureTheory.lintegral_dirac' _ (Measurable.of_discrete)]
    simp
  · by_cases hx : Inv x
    · rw [killK_now_some_gated (K := K) (G := {x | Inv x}) x hx,
        MeasureTheory.lintegral_map (Measurable.of_discrete)
          (gateMap_measurable {x | Inv x})]
      calc
        (∫⁻ y, potentialLift Φ (gateMap {x | Inv x} y) ∂(K x))
            ≤ ∫⁻ y, (Φ y : ℝ≥0∞) ∂(K x) := by
              refine lintegral_mono (fun y => ?_)
              unfold gateMap
              by_cases hy : Inv y
              · simp [hy]
              · simp [hy]
        _ ≤ r * (Φ x : ℝ≥0∞) := hdrift x hx
        _ = r * potentialLift Φ (some x) := by rw [potentialLift_some]
    · rw [killK_now_ungated (K := K) (G := {x | Inv x}) x hx,
        MeasureTheory.lintegral_dirac' _ (Measurable.of_discrete)]
      simp

/-- Real-chain failure is bounded by killed-chain geometric drift plus the
window-escape union bound.

The first summand is the threshold-one Markov bound for the killed potential;
the second is the cemetery mass accumulated over `T` steps. -/
theorem real_tail_le_drift_plus_escape (K : Kernel α α) [IsMarkovKernel K]
    (Inv : α → Prop) (Φ : α → ℕ) (r : ℝ≥0∞)
    (hdrift : ∀ x, Inv x →
      ∫⁻ y, (Φ y : ℝ≥0∞) ∂(K x) ≤ r * (Φ x : ℝ≥0∞))
    (η : ℝ≥0∞) (hesc : ∀ x, Inv x → K x {y | ¬ Inv y} ≤ η)
    (T : ℕ) (x₀ : α) (hInv₀ : Inv x₀) :
    (K ^ T) x₀ {y | ¬ (Inv y ∧ Φ y = 0)}
      ≤ r ^ T * (Φ x₀ : ℝ≥0∞) + (T : ℝ≥0∞) * η := by
  classical
  set G : Set α := {x | Inv x} with hG
  set Tgt : Set (Option α) :=
    {o | o = none ∨ (∃ y, o = some y ∧ ¬ (Inv y ∧ Φ y = 0))} with hTgt

  have hescG : ∀ x ∈ G, K x Gᶜ ≤ η := by
    intro x hx
    have hGc : (Gᶜ : Set α) = {y | ¬ Inv y} := by
      ext y
      simp [hG]
    rw [hGc]
    exact hesc x hx

  have hcouple := GatedDrift.real_le_killed_now (K := K) (G := G)
    (bad := fun y => ¬ (Inv y ∧ Φ y = 0)) T x₀

  have hsplit : Tgt ⊆ {(none : Option α)} ∪ {o | ¬ WindowSurvival.safeIn Inv o}
      ∪ {o | 1 ≤ potentialLift Φ o} := by
    intro o ho
    rw [hTgt, Set.mem_setOf_eq] at ho
    rcases ho with hnone | ⟨y, hy, hbad⟩
    · exact Or.inl (Or.inl (by rw [hnone]; rfl))
    · subst hy
      by_cases hInvy : Inv y
      · refine Or.inr ?_
        rw [Set.mem_setOf_eq, potentialLift_some]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hΦ => hbad ⟨hInvy, hΦ⟩)
      · refine Or.inl (Or.inr ?_)
        rw [Set.mem_setOf_eq, WindowSurvival.not_safeIn_iff]
        exact ⟨y, rfl, hInvy⟩

  have hbadkill : (killK_now K G ^ T) (some x₀) Tgt
      ≤ (killK_now K G ^ T) (some x₀) {(none : Option α)}
        + (killK_now K G ^ T) (some x₀) {o | ¬ WindowSurvival.safeIn Inv o}
        + (killK_now K G ^ T) (some x₀) {o | 1 ≤ potentialLift Φ o} := by
    refine le_trans (measure_mono hsplit) ?_
    refine le_trans (measure_union_le (μ := (killK_now K G ^ T) (some x₀))
      ({(none : Option α)} ∪ {o | ¬ WindowSurvival.safeIn Inv o})
      {o | 1 ≤ potentialLift Φ o}) ?_
    exact add_le_add
      (measure_union_le (μ := (killK_now K G ^ T) (some x₀))
        {(none : Option α)} {o | ¬ WindowSurvival.safeIn Inv o}) le_rfl

  have hpiece1 : (killK_now K G ^ T) (some x₀) {(none : Option α)}
      ≤ (T : ℝ≥0∞) * η :=
    WindowSurvival.killed_now_none_mass_le K G η hescG T x₀ hInv₀

  have hpiece2 : (killK_now K G ^ T) (some x₀)
      {o | ¬ WindowSurvival.safeIn Inv o} = 0 := by
    have hsafe₀ : WindowSurvival.safeIn Inv (some x₀) :=
      Or.inl ⟨x₀, rfl, hInv₀⟩
    exact OneSidedCancel.pow_not_inv_eq_zero (killK_now K G)
      (WindowSurvival.safeIn Inv) (WindowSurvival.killNow_invClosed K Inv)
      (some x₀) hsafe₀ T

  have hpiece3 : (killK_now K G ^ T) (some x₀) {o | 1 ≤ potentialLift Φ o}
      ≤ r ^ T * potentialLift Φ (some x₀) := by
    exact measure_potential_ge_one (killK_now K G) (potentialLift Φ)
      (measurable_potentialLift Φ) r
      (killNow_lintegral_drift K Inv Φ r hdrift) T (some x₀)

  calc
    (K ^ T) x₀ {y | ¬ (Inv y ∧ Φ y = 0)}
        ≤ (killK_now K G ^ T) (some x₀) Tgt := hcouple
    _ ≤ (killK_now K G ^ T) (some x₀) {(none : Option α)}
          + (killK_now K G ^ T) (some x₀) {o | ¬ WindowSurvival.safeIn Inv o}
          + (killK_now K G ^ T) (some x₀) {o | 1 ≤ potentialLift Φ o} := hbadkill
    _ ≤ (T : ℝ≥0∞) * η + 0 + r ^ T * potentialLift Φ (some x₀) :=
      add_le_add (add_le_add hpiece1 (le_of_eq hpiece2)) hpiece3
    _ = r ^ T * (Φ x₀ : ℝ≥0∞) + (T : ℝ≥0∞) * η := by
      rw [add_zero, potentialLift_some]
      ac_rfl

/-- Real-chain failure under multiplicative drift with a side-prefix escape
accounting.  Gate exit costs `q` only while the side predicate `S` holds; all
other exit risk is charged once to the real-chain prefix sum of `Sᶜ`.

This is the truthful interface for timed protocol phases.  Their algebraic
work gate is not uniformly closed, but it has zero (or small) one-step leak
while all clock counters remain positive, and clock depletion is controlled by
a reachable-scoped prefix tail. -/
theorem real_tail_le_drift_plus_side_prefix
    (K : Kernel α α) [IsMarkovKernel K]
    (Inv : α → Prop) (Φ : α → ℕ) (r : ℝ≥0∞)
    (hdrift : ∀ x, Inv x →
      ∫⁻ y, (Φ y : ℝ≥0∞) ∂(K x) ≤ r * (Φ x : ℝ≥0∞))
    (S : Set α) (q : ℝ≥0∞)
    (hesc : ∀ x, Inv x → x ∈ S → K x {y | ¬ Inv y} ≤ q)
    (T : ℕ) (x₀ : α) (hInv₀ : Inv x₀) :
    (K ^ T) x₀ {y | ¬ (Inv y ∧ Φ y = 0)}
      ≤ r ^ T * (Φ x₀ : ℝ≥0∞) +
          ((T : ℝ≥0∞) * q +
            ∑ τ ∈ Finset.range T, (K ^ τ) x₀ Sᶜ) := by
  classical
  set G : Set α := {x | Inv x} with hG
  set Tgt : Set (Option α) :=
    {o | o = none ∨ (∃ y, o = some y ∧ ¬ (Inv y ∧ Φ y = 0))} with hTgt

  have hescG : ∀ x ∈ G, x ∈ S → K x Gᶜ ≤ q := by
    intro x hx hS
    have hGc : (Gᶜ : Set α) = {y | ¬ Inv y} := by
      ext y
      simp [hG]
    rw [hGc]
    exact hesc x hx hS

  have hcouple := GatedDrift.real_le_killed_now (K := K) (G := G)
    (bad := fun y => ¬ (Inv y ∧ Φ y = 0)) T x₀

  have hsplit : Tgt ⊆ {(none : Option α)} ∪
      {o | ¬ WindowSurvival.safeIn Inv o} ∪
      {o | 1 ≤ potentialLift Φ o} := by
    intro o ho
    rw [hTgt, Set.mem_setOf_eq] at ho
    rcases ho with hnone | ⟨y, hy, hbad⟩
    · exact Or.inl (Or.inl (by rw [hnone]; rfl))
    · subst hy
      by_cases hInvy : Inv y
      · refine Or.inr ?_
        rw [Set.mem_setOf_eq, potentialLift_some]
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (fun hΦ => hbad ⟨hInvy, hΦ⟩)
      · refine Or.inl (Or.inr ?_)
        rw [Set.mem_setOf_eq, WindowSurvival.not_safeIn_iff]
        exact ⟨y, rfl, hInvy⟩

  have hbadkill : (killK_now K G ^ T) (some x₀) Tgt
      ≤ (killK_now K G ^ T) (some x₀) {(none : Option α)}
        + (killK_now K G ^ T) (some x₀)
            {o | ¬ WindowSurvival.safeIn Inv o}
        + (killK_now K G ^ T) (some x₀)
            {o | 1 ≤ potentialLift Φ o} := by
    refine le_trans (measure_mono hsplit) ?_
    refine le_trans (measure_union_le
      (μ := (killK_now K G ^ T) (some x₀))
      ({(none : Option α)} ∪ {o | ¬ WindowSurvival.safeIn Inv o})
      {o | 1 ≤ potentialLift Φ o}) ?_
    exact add_le_add
      (measure_union_le (μ := (killK_now K G ^ T) (some x₀))
        {(none : Option α)} {o | ¬ WindowSurvival.safeIn Inv o}) le_rfl

  have hpiece1 : (killK_now K G ^ T) (some x₀)
      {(none : Option α)} ≤
        (T : ℝ≥0∞) * q +
          ∑ τ ∈ Finset.range T, (K ^ τ) x₀ Sᶜ :=
    GatedDrift.kill_now_escape_le_prefix_union
      (K := K) (G := G) S q hescG T x₀ hInv₀

  have hpiece2 : (killK_now K G ^ T) (some x₀)
      {o | ¬ WindowSurvival.safeIn Inv o} = 0 := by
    have hsafe₀ : WindowSurvival.safeIn Inv (some x₀) :=
      Or.inl ⟨x₀, rfl, hInv₀⟩
    exact OneSidedCancel.pow_not_inv_eq_zero (killK_now K G)
      (WindowSurvival.safeIn Inv) (WindowSurvival.killNow_invClosed K Inv)
      (some x₀) hsafe₀ T

  have hpiece3 : (killK_now K G ^ T) (some x₀)
      {o | 1 ≤ potentialLift Φ o}
      ≤ r ^ T * potentialLift Φ (some x₀) := by
    exact measure_potential_ge_one (killK_now K G) (potentialLift Φ)
      (measurable_potentialLift Φ) r
      (killNow_lintegral_drift K Inv Φ r hdrift) T (some x₀)

  calc
    (K ^ T) x₀ {y | ¬ (Inv y ∧ Φ y = 0)}
        ≤ (killK_now K G ^ T) (some x₀) Tgt := hcouple
    _ ≤ (killK_now K G ^ T) (some x₀) {(none : Option α)}
          + (killK_now K G ^ T) (some x₀)
              {o | ¬ WindowSurvival.safeIn Inv o}
          + (killK_now K G ^ T) (some x₀)
              {o | 1 ≤ potentialLift Φ o} := hbadkill
    _ ≤ ((T : ℝ≥0∞) * q +
            ∑ τ ∈ Finset.range T, (K ^ τ) x₀ Sᶜ) + 0
          + r ^ T * potentialLift Φ (some x₀) :=
      add_le_add (add_le_add hpiece1 (le_of_eq hpiece2)) hpiece3
    _ = r ^ T * (Φ x₀ : ℝ≥0∞) +
          ((T : ℝ≥0∞) * q +
            ∑ τ ∈ Finset.range T, (K ^ τ) x₀ Sᶜ) := by
      rw [add_zero, potentialLift_some]
      ac_rfl

set_option linter.unusedVariables false in
/-- Package multiplicative drift with a finite-horizon window-survival budget.

`hr` records that `r` is a contraction factor.  The quantitative discharge is
kept explicit in `hdrainε`, which is the exact bound consumed by this engine;
this avoids hiding any horizon calibration in the generic constructor. -/
noncomputable def driftSurvivalPhase (K : Kernel α α) [IsMarkovKernel K]
    (Inv : α → Prop) (Φ : α → ℕ)
    (r : ℝ≥0∞) (hr : r ≤ 1)
    (hdrift : ∀ x, Inv x →
      ∫⁻ y, (Φ y : ℝ≥0∞) ∂(K x) ≤ r * (Φ x : ℝ≥0∞))
    (η : ℝ≥0∞) (hesc : ∀ x, Inv x → K x {y | ¬ Inv y} ≤ η)
    (T Φmax : ℕ) (drainε escapeε : ℝ≥0)
    (hdrainε : r ^ T * (Φmax : ℝ≥0∞) ≤ (drainε : ℝ≥0∞))
    (hescε : (T : ℝ≥0∞) * η ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW K where
  Pre x := Inv x ∧ Φ x ≤ Φmax
  Post x := Inv x ∧ Φ x = 0
  t := T
  ε := drainε + escapeε
  convergence := by
    intro x₀ hPre₀
    obtain ⟨hInv₀, hΦ₀⟩ := hPre₀
    calc
      (K ^ T) x₀ {y | ¬ (Inv y ∧ Φ y = 0)}
          ≤ r ^ T * (Φ x₀ : ℝ≥0∞) + (T : ℝ≥0∞) * η :=
        real_tail_le_drift_plus_escape K Inv Φ r hdrift η hesc T x₀ hInv₀
      _ ≤ r ^ T * (Φmax : ℝ≥0∞) + (T : ℝ≥0∞) * η := by
        gcongr
      _ ≤ (drainε : ℝ≥0∞) + (escapeε : ℝ≥0∞) :=
        add_le_add hdrainε hescε
      _ = ((drainε + escapeε : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.coe_add]

set_option linter.unusedVariables false in
/-- Package multiplicative drift with side-prefix escape accounting.

Unlike `driftSurvivalPhase`, this constructor does not demand a uniformly small
one-step escape probability on the whole invariant.  The prefix hypothesis is
quantified over every `Pre` state because a `PhaseConvergenceW` is itself a
uniform work component; a bound for only one distinguished start would not
justify that interface. -/
noncomputable def driftSurvivalPhaseSidePrefix
    (K : Kernel α α) [IsMarkovKernel K]
    (Inv : α → Prop) (Φ : α → ℕ)
    (r : ℝ≥0∞) (hr : r ≤ 1)
    (hdrift : ∀ x, Inv x →
      ∫⁻ y, (Φ y : ℝ≥0∞) ∂(K x) ≤ r * (Φ x : ℝ≥0∞))
    (S : Set α) (q : ℝ≥0∞)
    (hesc : ∀ x, Inv x → x ∈ S → K x {y | ¬ Inv y} ≤ q)
    (T Φmax : ℕ) (drainε escapeε : ℝ≥0)
    (hdrainε : r ^ T * (Φmax : ℝ≥0∞) ≤ (drainε : ℝ≥0∞))
    (ηPrefix : ℝ≥0∞)
    (hprefix : ∀ x₀, Inv x₀ ∧ Φ x₀ ≤ Φmax →
      (∑ τ ∈ Finset.range T, (K ^ τ) x₀ Sᶜ) ≤ ηPrefix)
    (hescε : (T : ℝ≥0∞) * q + ηPrefix ≤ (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW K where
  Pre x := Inv x ∧ Φ x ≤ Φmax
  Post x := Inv x ∧ Φ x = 0
  t := T
  ε := drainε + escapeε
  convergence := by
    intro x₀ hPre₀
    obtain ⟨hInv₀, hΦ₀⟩ := hPre₀
    calc
      (K ^ T) x₀ {y | ¬ (Inv y ∧ Φ y = 0)}
          ≤ r ^ T * (Φ x₀ : ℝ≥0∞) +
              ((T : ℝ≥0∞) * q +
                ∑ τ ∈ Finset.range T, (K ^ τ) x₀ Sᶜ) :=
        real_tail_le_drift_plus_side_prefix K Inv Φ r hdrift
          S q hesc T x₀ hInv₀
      _ ≤ r ^ T * (Φmax : ℝ≥0∞) +
              ((T : ℝ≥0∞) * q + ηPrefix) := by
        gcongr
        exact hprefix x₀ ⟨hInv₀, hΦ₀⟩
      _ ≤ (drainε : ℝ≥0∞) + (escapeε : ℝ≥0∞) :=
        add_le_add hdrainε hescε
      _ = ((drainε + escapeε : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.coe_add]

#print axioms killNow_lintegral_drift
#print axioms real_tail_le_drift_plus_escape
#print axioms real_tail_le_drift_plus_side_prefix
#print axioms driftSurvivalPhase
#print axioms driftSurvivalPhaseSidePrefix

end DriftSurvival
end Ripple.PopulationProtocol.ExactMajority
