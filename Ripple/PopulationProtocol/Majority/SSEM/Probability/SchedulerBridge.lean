import Ripple.PopulationProtocol.Majority.SSEM.Probability.SelectionCount
import Ripple.PopulationProtocol.Majority.SSEM.Probability.ExpectedTime
import Mathlib.Algebra.BigOperators.Fin

namespace SSEM
namespace Probability

open scoped BigOperators ENNReal
open PMF

variable {Q X Y : Type*} {n : ℕ}

/-!
# Scheduler-prefix bridge

This file couples the finite-prefix hitting distribution used by
`ProbHitWithin` with the explicit scheduler-prefix product PMF from
`SelectionCount`.
-/

/-- Recursive product PMF obtained by appending one fresh uniform scheduler
pair at a time. -/
noncomputable def schedulerPrefixSnocPMF
    (n : ℕ) (hn : 2 ≤ n) : ∀ K : ℕ, PMF (SchedulerPrefix n K)
  | 0 => PMF.pure (fun t : Fin 0 => Fin.elim0 t)
  | K + 1 =>
      (schedulerPrefixSnocPMF n hn K).bind fun σ =>
        (uniformPair n hn).map fun p => Fin.snoc σ p

private theorem uniformPair_map_snoc_apply
    (n : ℕ) (hn : 2 ≤ n) {K : ℕ}
    (σ : SchedulerPrefix n K) (τ : SchedulerPrefix n (K + 1)) :
    ((uniformPair n hn).map fun p => Fin.snoc σ p) τ =
      if Fin.init τ = σ then uniformPair n hn (τ (Fin.last K)) else 0 := by
  classical
  rw [PMF.map_apply]
  by_cases hinit : Fin.init τ = σ
  · have hτ : τ = Fin.snoc σ (τ (Fin.last K)) := by
      rw [← hinit]
      exact (Fin.snoc_init_self τ).symm
    rw [tsum_eq_single (τ (Fin.last K))]
    · rw [if_pos hτ, if_pos hinit]
    · intro p hp
      have hp' : τ ≠ Fin.snoc σ p := by
        intro h
        apply hp
        have hp_eq : τ (Fin.last K) = p := by
          simpa using congrFun h (Fin.last K)
        exact hp_eq.symm
      simp [hp']
  · rw [if_neg hinit]
    apply ENNReal.tsum_eq_zero.2
    intro p
    by_cases hp : τ = Fin.snoc σ p
    · have hbad : Fin.init τ = σ := by
        rw [hp]
        simp
      exact False.elim (hinit hbad)
    · rw [if_neg hp]

private theorem schedulerPrefixWeight_snoc
    (n : ℕ) (hn : 2 ≤ n) {K : ℕ}
    (τ : SchedulerPrefix n (K + 1)) :
    schedulerPrefixWeight n hn (K + 1) τ =
      schedulerPrefixWeight n hn K (Fin.init τ) *
        uniformPair n hn (τ (Fin.last K)) := by
  unfold schedulerPrefixWeight
  rw [Fin.prod_univ_castSucc]
  rfl

theorem schedulerPrefixSnocPMF_apply
    (n : ℕ) (hn : 2 ≤ n) (K : ℕ) (σ : SchedulerPrefix n K) :
    schedulerPrefixSnocPMF n hn K σ =
      schedulerPrefixWeight n hn K σ := by
  classical
  induction K with
  | zero =>
      have hσ : σ = (fun t : Fin 0 => Fin.elim0 t) :=
        funext fun t => Fin.elim0 t
      subst σ
      simp [schedulerPrefixSnocPMF, schedulerPrefixWeight]
  | succ K ih =>
      rw [schedulerPrefixSnocPMF, PMF.bind_apply]
      calc
        (∑' σ₀ : SchedulerPrefix n K,
            schedulerPrefixSnocPMF n hn K σ₀ *
              ((uniformPair n hn).map fun p => Fin.snoc σ₀ p) σ)
            =
          ∑' σ₀ : SchedulerPrefix n K,
            schedulerPrefixWeight n hn K σ₀ *
              (if Fin.init σ = σ₀ then
                uniformPair n hn (σ (Fin.last K)) else 0) := by
              apply tsum_congr
              intro σ₀
              rw [ih σ₀, uniformPair_map_snoc_apply]
        _ = schedulerPrefixWeight n hn K (Fin.init σ) *
              uniformPair n hn (σ (Fin.last K)) := by
              rw [tsum_eq_single (Fin.init σ)]
              · simp
              · intro σ₀ hσ₀
                rw [if_neg (fun h => hσ₀ h.symm)]
                simp
        _ = schedulerPrefixWeight n hn (K + 1) σ := by
              rw [schedulerPrefixWeight_snoc]

theorem schedulerPrefixSnocPMF_eq_schedulerPrefixPMF
    (n : ℕ) (hn : 2 ≤ n) (K : ℕ) :
    schedulerPrefixSnocPMF n hn K = schedulerPrefixPMF n hn K := by
  apply PMF.ext
  intro σ
  rw [schedulerPrefixSnocPMF_apply, schedulerPrefixPMF_apply]

/-- State of the coupled finite-prefix process: hit-state plus the scheduler
prefix that generated it. -/
abbrev SchedulerTraceState
    (Q X : Type*) (n K : ℕ) :=
  (Config Q X n × Bool) × SchedulerPrefix n K

/-- One coupled scheduler step: append the sampled pair to the tracked prefix
and update the hit flag exactly as `hitFlagStepDist` does. -/
noncomputable def schedulerTraceStepDist
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop) {K : ℕ}
    (S : SchedulerTraceState Q X n K) :
    PMF (SchedulerTraceState Q X n (K + 1)) := by
  classical
  exact
    (uniformPair n hn).map fun p =>
      let C' : Config Q X n := S.1.1.step P p.1 p.2
      ((C', S.1.2 || decide (Goal C')), Fin.snoc S.2 p)

/-- Coupled finite-prefix distribution at length `K`. -/
noncomputable def schedulerTraceDist
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) :
    ∀ K : ℕ, PMF (SchedulerTraceState Q X n K)
  | 0 => by
      classical
      exact PMF.pure ((C₀, decide (Goal C₀)),
        (fun t : Fin 0 => Fin.elim0 t))
  | K + 1 =>
      (schedulerTraceDist P hn C₀ Goal K).bind
        (schedulerTraceStepDist P hn Goal)

theorem schedulerTraceStepDist_map_hitFlag
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop) {K : ℕ}
    (S : SchedulerTraceState Q X n K) :
    (schedulerTraceStepDist P hn Goal S).map Prod.fst =
      hitFlagStepDist P hn Goal S.1 := by
  classical
  unfold schedulerTraceStepDist hitFlagStepDist stepDist
  rw [PMF.map_comp, PMF.map_comp]
  rfl

theorem schedulerTraceDist_map_hitFlag
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) :
    ∀ K : ℕ,
      (schedulerTraceDist P hn C₀ Goal K).map Prod.fst =
        hitFlagDist P hn C₀ Goal K
  | 0 => by
      classical
      rw [schedulerTraceDist, hitFlagDist]
      by_cases h : Goal C₀
      · simpa [h] using
          (PMF.pure_map
            (f := Prod.fst)
            (a := ((C₀, true), (fun t : Fin 0 => Fin.elim0 t))))
      · simpa [h] using
          (PMF.pure_map
            (f := Prod.fst)
            (a := ((C₀, false), (fun t : Fin 0 => Fin.elim0 t))))
  | K + 1 => by
      rw [schedulerTraceDist, hitFlagDist, PMF.map_bind]
      simp only [schedulerTraceStepDist_map_hitFlag]
      change
        (schedulerTraceDist P hn C₀ Goal K).bind
            ((hitFlagStepDist P hn Goal) ∘ Prod.fst) =
          (hitFlagDist P hn C₀ Goal K).bind (hitFlagStepDist P hn Goal)
      rw [← PMF.bind_map, schedulerTraceDist_map_hitFlag P hn C₀ Goal K]

theorem schedulerTraceStepDist_map_prefix
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (Goal : Config Q X n → Prop) {K : ℕ}
    (S : SchedulerTraceState Q X n K) :
    (schedulerTraceStepDist P hn Goal S).map Prod.snd =
      (uniformPair n hn).map fun p => Fin.snoc S.2 p := by
  classical
  unfold schedulerTraceStepDist
  rw [PMF.map_comp]
  rfl

theorem schedulerTraceDist_map_prefix_snoc
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) :
    ∀ K : ℕ,
      (schedulerTraceDist P hn C₀ Goal K).map Prod.snd =
        schedulerPrefixSnocPMF n hn K
  | 0 => by
      classical
      rw [schedulerTraceDist, schedulerPrefixSnocPMF]
      simpa using
        (PMF.pure_map
          (f := Prod.snd)
          (a := ((C₀, decide (Goal C₀)),
            (fun t : Fin 0 => Fin.elim0 t))))
  | K + 1 => by
      rw [schedulerTraceDist, schedulerPrefixSnocPMF, PMF.map_bind]
      simp only [schedulerTraceStepDist_map_prefix]
      let F : SchedulerPrefix n K → PMF (SchedulerPrefix n (K + 1)) :=
        fun σ => (uniformPair n hn).map (fun p => Fin.snoc σ p)
      change
        (schedulerTraceDist P hn C₀ Goal K).bind (F ∘ Prod.snd) =
          (schedulerPrefixSnocPMF n hn K).bind F
      rw [← PMF.bind_map, schedulerTraceDist_map_prefix_snoc P hn C₀ Goal K]

theorem schedulerTraceDist_map_prefix
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop) (K : ℕ) :
    (schedulerTraceDist P hn C₀ Goal K).map Prod.snd =
      schedulerPrefixPMF n hn K := by
  rw [schedulerTraceDist_map_prefix_snoc,
    schedulerPrefixSnocPMF_eq_schedulerPrefixPMF]

private theorem trace_toOuterMeasure_le_prefix_of_support_imp
    {K : ℕ} (μ : PMF (SchedulerTraceState Q X n K))
    (B : Set (SchedulerPrefix n K))
    (A : Set (SchedulerTraceState Q X n K))
    (hA : A ⊆ {S | S.2 ∈ B}) :
    μ.toOuterMeasure A ≤ (μ.map Prod.snd).toOuterMeasure B := by
  calc
    μ.toOuterMeasure A ≤ μ.toOuterMeasure {S | S.2 ∈ B} :=
      MeasureTheory.measure_mono hA
    _ = (μ.map Prod.snd).toOuterMeasure B := by
      rw [PMF.toOuterMeasure_map_apply]
      rfl

/-- One-sided sigma-marginal bridge: if every traced path that hits `Goal`
has a high-load scheduler prefix, then the execution hit probability is at
most the scheduler-prefix high-load mass. -/
theorem ProbHitWithin_le_schedulerPrefix_high_load
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (K r : ℕ)
    (hcert :
      ∀ S : SchedulerTraceState Q X n K,
        S.1.2 = true → PrefixHighLoad S.2 r) :
    ProbHitWithin P hn C₀ Goal K ≤
      (schedulerPrefixPMF n hn K).toOuterMeasure
        {σ : SchedulerPrefix n K | PrefixHighLoad σ r} := by
  classical
  let μ := schedulerTraceDist P hn C₀ Goal K
  calc
    ProbHitWithin P hn C₀ Goal K
        = (hitFlagDist P hn C₀ Goal K).toOuterMeasure
            {S : Config Q X n × Bool | S.2 = true} := by
          simpa [ProbHitWithin] using
            (probHitBy_eq_hitFlagDist_toOuterMeasure
              (P := P) (hn := hn) (C₀ := C₀) (Goal := Goal) (t := K))
    _ = μ.toOuterMeasure {S : SchedulerTraceState Q X n K | S.1.2 = true} := by
          rw [← schedulerTraceDist_map_hitFlag
            (P := P) (hn := hn) (C₀ := C₀) (Goal := Goal) K]
          rw [PMF.toOuterMeasure_map_apply]
          rfl
    _ ≤ (μ.map Prod.snd).toOuterMeasure
          {σ : SchedulerPrefix n K | PrefixHighLoad σ r} := by
          apply trace_toOuterMeasure_le_prefix_of_support_imp
          intro S hS
          exact hcert S hS
    _ = (schedulerPrefixPMF n hn K).toOuterMeasure
          {σ : SchedulerPrefix n K | PrefixHighLoad σ r} := by
          rw [schedulerTraceDist_map_prefix]

/-- Choose-union tail bound transported from the execution hit measure to the
scheduler-prefix product measure. -/
theorem ProbHitWithin_le_schedulerPrefix_high_load_choose
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (K r : ℕ)
    (hcert :
      ∀ S : SchedulerTraceState Q X n K,
        S.1.2 = true → PrefixHighLoad S.2 r) :
    ProbHitWithin P hn C₀ Goal K ≤
      (n : ENNReal) * (Nat.choose K r : ENNReal) *
        (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ r) := by
  classical
  have hbridge :=
    ProbHitWithin_le_schedulerPrefix_high_load
      (P := P) (hn := hn) (C₀ := C₀) (Goal := Goal) (K := K) (r := r)
      hcert
  refine hbridge.trans ?_
  exact
    prefix_high_load_mass_le_union_choose
      (n := n) (K := K) (r := r)
      (mass := fun E : Set (SchedulerPrefix n K) =>
        (schedulerPrefixPMF n hn K).toOuterMeasure E)
      (A := fun σ => σ)
      (fun X Y hXY =>
        MeasureTheory.measure_mono
          (μ := (schedulerPrefixPMF n hn K).toOuterMeasure) hXY)
      (fun B =>
        schedulerPrefix_outerMeasure_iUnion_fintype_le
          (n := n) hn K B)
      (fun _a B =>
        schedulerPrefix_outerMeasure_iUnion_fintype_le
          (n := n) hn K B)
      (fun a T hT =>
        schedulerPrefix_cylinder_selectedOn_le
          (n := n) hn a T hT)

/-- Named wrapper for the disruption-tail use case.  The certificate is the
pathwise implication from a hit in the coupled execution trace to high
scheduler load of its tracked prefix. -/
theorem disruption_ProbHitWithin_le_choose
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (DisruptionPredicate : Config Q X n → Prop)
    (K r : ℕ)
    (hcert :
      ∀ S : SchedulerTraceState Q X n K,
        S.1.2 = true → PrefixHighLoad S.2 r) :
    ProbHitWithin P hn C₀ DisruptionPredicate K ≤
      (n : ENNReal) * (Nat.choose K r : ENNReal) *
        (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ r) :=
  ProbHitWithin_le_schedulerPrefix_high_load_choose
    (P := P) (hn := hn) (C₀ := C₀) (Goal := DisruptionPredicate)
    (K := K) (r := r) hcert

end Probability
end SSEM
