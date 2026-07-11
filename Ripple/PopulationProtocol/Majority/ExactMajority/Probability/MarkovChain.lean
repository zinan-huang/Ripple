/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Markov Chain Kernel for ExactMajority Protocols

The scheduler in `Probability.Scheduler` needs at least two agents.  The kernel
defined here uses that scheduler on configurations of size at least two and
falls back to a point mass at the current configuration on smaller populations.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Scheduler
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Defs
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace ExactMajority

open MeasureTheory ProbabilityTheory

namespace Protocol

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- One-step distribution with a degenerate fallback for populations of size
less than two. -/
noncomputable def stepDistOrSelf (P : Protocol Λ) (c : Config Λ) :
    PMF (Config Λ) :=
  if hc : 2 ≤ c.card then
    P.stepDist c hc
  else
    PMF.pure c

/-- The fallback one-step distribution only reaches protocol-reachable
configurations. -/
theorem stepDistOrSelf_support_reachable (P : Protocol Λ) (c c' : Config Λ) :
    c' ∈ (P.stepDistOrSelf c).support → P.Reachable c c' := by
  intro h
  unfold stepDistOrSelf at h
  by_cases hc : 2 ≤ c.card
  · rw [dif_pos hc] at h
    exact stepDist_support_reachable P c hc c' h
  · rw [dif_neg hc] at h
    rw [PMF.mem_support_pure_iff] at h
    subst c'
    exact Relation.ReflTransGen.refl

/-- The fallback one-step distribution preserves population size on every
support point. -/
theorem stepDistOrSelf_support_card_eq (P : Protocol Λ) (c c' : Config Λ) :
    c' ∈ (P.stepDistOrSelf c).support → c'.card = c.card := by
  intro h
  exact reachable_card_eq (stepDistOrSelf_support_reachable P c c' h)

namespace Config

/-- The measurable space on generic configurations is discrete. -/
noncomputable instance instMeasurableSpaceConfig : MeasurableSpace (Config Λ) := ⊤

/-- With the discrete σ-algebra, every set is measurable. -/
instance instDiscreteMeasurableSpaceConfig : DiscreteMeasurableSpace (Config Λ) where
  forall_measurableSet _ := trivial

end Config

/-- Markov transition kernel induced by the ExactMajority random scheduler. -/
noncomputable def transitionKernel (P : Protocol Λ) :
    ProbabilityTheory.Kernel (Config Λ) (Config Λ) where
  toFun c := (P.stepDistOrSelf c).toMeasure
  measurable' := Measurable.of_discrete

instance transitionKernel_isMarkovKernel (P : Protocol Λ) :
    IsMarkovKernel P.transitionKernel where
  isProbabilityMeasure c := by
    show IsProbabilityMeasure (P.stepDistOrSelf c).toMeasure
    infer_instance

/-- A predicate closed under one-step stochastic support points holds almost
surely after any finite number of steps of the protocol Markov kernel. -/
theorem ae_of_stepDistOrSelf_support_preserved
    (P : Protocol Λ) (Q : Config Λ → Prop)
    (hstep : ∀ c c' : Config Λ, Q c → c' ∈ (P.stepDistOrSelf c).support → Q c')
    (c : Config Λ) (hc : Q c) (t : ℕ) :
    ∀ᵐ c' ∂((P.transitionKernel ^ t) c), Q c' := by
  induction t with
  | zero =>
      simp only [pow_zero]
      change ∀ᵐ c' ∂(Kernel.id c), Q c'
      rw [Kernel.id_apply, MeasureTheory.ae_dirac_iff
        (Config.instDiscreteMeasurableSpaceConfig.forall_measurableSet _)]
      exact hc
  | succ t ih =>
      rw [MeasureTheory.ae_iff]
      have hbad_meas : MeasurableSet {c' : Config Λ | ¬Q c'} :=
        Config.instDiscreteMeasurableSpaceConfig.forall_measurableSet _
      rw [Kernel.pow_succ_apply_eq_lintegral _ _ _ hbad_meas,
        MeasureTheory.lintegral_eq_zero_iff (Kernel.measurable_coe _ hbad_meas)]
      filter_upwards [ih] with c' hc'
      change (P.stepDistOrSelf c').toMeasure {c'' : Config Λ | ¬Q c''} = 0
      rw [PMF.toMeasure_apply_eq_zero_iff
        (p := P.stepDistOrSelf c')
        (s := {c'' : Config Λ | ¬Q c''})
        (Config.instDiscreteMeasurableSpaceConfig.forall_measurableSet _)]
      rw [Set.disjoint_left]
      intro c'' hsupp hbad
      exact hbad (hstep c' c'' hc' hsupp)

/-- Probability-zero form of `ae_of_stepDistOrSelf_support_preserved`. -/
theorem transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved
    (P : Protocol Λ) (Q : Config Λ → Prop)
    (hstep : ∀ c c' : Config Λ, Q c → c' ∈ (P.stepDistOrSelf c).support → Q c')
    (c : Config Λ) (hc : Q c) (t : ℕ) :
    (P.transitionKernel ^ t) c {c' : Config Λ | ¬Q c'} = 0 := by
  have h := ae_of_stepDistOrSelf_support_preserved P Q hstep c hc t
  rwa [MeasureTheory.ae_iff] at h

/-- Every finite Markov-chain execution remains almost surely inside the
deterministic reachability closure of its starting configuration. -/
theorem ae_reachable_transitionKernel_pow
    (P : Protocol Λ) (c : Config Λ) (t : ℕ) :
    ∀ᵐ c' ∂((P.transitionKernel ^ t) c), P.Reachable c c' := by
  exact ae_of_stepDistOrSelf_support_preserved
    P (fun c' => P.Reachable c c')
    (fun c₀ c₁ hreach hsupp =>
      Relation.ReflTransGen.trans hreach
        (stepDistOrSelf_support_reachable P c₀ c₁ hsupp))
    c Relation.ReflTransGen.refl t

/-- Probability-zero form of `ae_reachable_transitionKernel_pow`. -/
theorem transitionKernel_pow_not_reachable_eq_zero
    (P : Protocol Λ) (c : Config Λ) (t : ℕ) :
    (P.transitionKernel ^ t) c {c' : Config Λ | ¬P.Reachable c c'} = 0 := by
  have h := ae_reachable_transitionKernel_pow P c t
  rwa [MeasureTheory.ae_iff] at h

/-- Any event disjoint from the deterministic reachability closure of the
starting configuration has probability zero at every finite Markov time. -/
theorem transitionKernel_pow_eq_zero_of_forall_not_reachable
    (P : Protocol Λ) (c : Config Λ) (t : ℕ) (S : Set (Config Λ))
    (hS : ∀ c' : Config Λ, c' ∈ S → ¬P.Reachable c c') :
    (P.transitionKernel ^ t) c S = 0 := by
  refine measure_mono_null ?_ (transitionKernel_pow_not_reachable_eq_zero P c t)
  intro c' hc'
  exact hS c' hc'

end Protocol

end ExactMajority
