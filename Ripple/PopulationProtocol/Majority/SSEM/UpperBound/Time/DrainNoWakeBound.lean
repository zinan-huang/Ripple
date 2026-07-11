import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.DrainNoWakeProtocol
import Ripple.PopulationProtocol.Majority.SSEM.Probability.SchedulerBridge

namespace SSEM

open scoped BigOperators ENNReal

namespace Probability

variable {Q X Y : Type*} {n : ℕ}

/-- Support-restricted version of the private bridge used inside
`ProbHitWithin_le_schedulerPrefix_high_load`.

This is the real condition needed by the measure proof: a trace state only has
to imply high scheduler load when it is in the support of the coupled
trace distribution. -/
private theorem trace_toOuterMeasure_le_prefix_of_support_imp'
    {α β : Type*} (μ : PMF α) (f : α → β)
    (B : Set β) (A : Set α)
    (hA : ∀ a : α, a ∈ μ.support → a ∈ A → f a ∈ B) :
    μ.toOuterMeasure A ≤ (μ.map f).toOuterMeasure B := by
  classical
  calc
    μ.toOuterMeasure A
        = μ.toOuterMeasure (A ∩ μ.support) := by
          refine PMF.toOuterMeasure_apply_eq_of_inter_support_eq μ ?_
          ext a
          constructor
          · intro ha
            exact ⟨ha, ha.2⟩
          · intro ha
            exact ha.1
    _ ≤ μ.toOuterMeasure {a : α | f a ∈ B} := by
          apply MeasureTheory.measure_mono
          intro a ha
          exact hA a ha.2 ha.1
    _ = (μ.map f).toOuterMeasure B := by
          rw [PMF.toOuterMeasure_map_apply]
          rfl

/-- Support-restricted choose-union tail bound transported from the execution
hit measure to the scheduler-prefix product measure.

This is the same conclusion as
`ProbHitWithin_le_schedulerPrefix_high_load_choose`, but the certificate is
only required on the support of the coupled trace distribution. -/
theorem ProbHitWithin_le_schedulerPrefix_high_load_choose_of_support
    (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Goal : Config Q X n → Prop)
    (K r : ℕ)
    (hcert :
      ∀ S : SchedulerTraceState Q X n K,
        S ∈ (schedulerTraceDist P hn C₀ Goal K).support →
          S.1.2 = true → PrefixHighLoad S.2 r) :
    ProbHitWithin P hn C₀ Goal K ≤
      (n : ENNReal) * (Nat.choose K r : ENNReal) *
        (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ r) := by
  classical
  let μ := schedulerTraceDist P hn C₀ Goal K
  have hbridge :
      ProbHitWithin P hn C₀ Goal K ≤
        (schedulerPrefixPMF n hn K).toOuterMeasure
          {σ : SchedulerPrefix n K | PrefixHighLoad σ r} := by
    calc
      ProbHitWithin P hn C₀ Goal K
          = (hitFlagDist P hn C₀ Goal K).toOuterMeasure
              {S : Config Q X n × Bool | S.2 = true} := by
            simpa [ProbHitWithin] using
              (probHitBy_eq_hitFlagDist_toOuterMeasure
                (P := P) (hn := hn) (C₀ := C₀) (Goal := Goal) (t := K))
      _ = μ.toOuterMeasure
            {S : SchedulerTraceState Q X n K | S.1.2 = true} := by
            rw [← schedulerTraceDist_map_hitFlag
              (P := P) (hn := hn) (C₀ := C₀) (Goal := Goal) K]
            rw [PMF.toOuterMeasure_map_apply]
            rfl
      _ ≤ (μ.map Prod.snd).toOuterMeasure
            {σ : SchedulerPrefix n K | PrefixHighLoad σ r} := by
            apply trace_toOuterMeasure_le_prefix_of_support_imp'
            intro S hSupp hHit
            exact hcert S hSupp hHit
      _ = (schedulerPrefixPMF n hn K).toOuterMeasure
            {σ : SchedulerPrefix n K | PrefixHighLoad σ r} := by
            rw [schedulerTraceDist_map_prefix]
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

end Probability

/-- Drain/no-wake binomial tail for the concrete PEM drain goal, conditional on
the support-restricted pathwise certificate.

The missing remaining work is exactly the proof of `hcert` from
`schedulerTraceDist` support plus the deterministic drain certificate. -/
theorem drain_probHitWithin_le_choose_of_support_cert
    {n Rmax Emax Dmax K d : ℕ}
    (hn : 0 < n) (hn2 : 2 ≤ n)
    (C₀ : Config (AgentState n) Opinion n)
    (hcert :
      ∀ S : Probability.SchedulerTraceState (AgentState n) Opinion n K,
        S ∈
          (Probability.schedulerTraceDist
            (PEMProtocol n 1 Rmax Emax Dmax hn) hn2 C₀ SomeAgentAwake K).support →
          S.1.2 = true →
            PrefixHighLoad S.2 d) :
    Probability.ProbHitWithin
        (PEMProtocol n 1 Rmax Emax Dmax hn) hn2 C₀ SomeAgentAwake K
      ≤
        (n : ENNReal) * (Nat.choose K d : ENNReal) *
          (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ d) := by
  exact
    Probability.ProbHitWithin_le_schedulerPrefix_high_load_choose_of_support
      (P := PEMProtocol n 1 Rmax Emax Dmax hn)
      (hn := hn2)
      (C₀ := C₀)
      (Goal := SomeAgentAwake)
      (K := K)
      (r := d)
      hcert

end SSEM
