/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Transfer of time bounds through a state simulation; Definition 1 for the finite P_EM

* `StateSimulation.probNotHitBy_encC`: the chain of the simulating protocol started at `encC C`
  (`C` good) is the image of the simulated chain, so non-hit probabilities (and hence expected
  hitting times, `expectedHittingTime_encC`) agree with those of the pulled-back goal.
* `probNotHitBy_compose_le`: window composition in additive failure form (Markov property at a
  fixed time; P2 Lemma 1.3).
* `P_EM_paper_fin_kanayaDefinition1`, `P_EM_fin_kanayaDefinition1`: the finite P_EM instances
  satisfy Kanaya et al.'s Definition 1 literally (probability one), and are silent almost surely.
-/

import Ripple.PopulationProtocol.SSEM.Probability.FiniteAlmostSure
import Ripple.PopulationProtocol.SSEM.UpperBound.PaperInstance

namespace Ripple.PopulationProtocol.SSEM

open Probability
open scoped ENNReal

variable {n : ℕ}

theorem PMF.bind_congr_support {α β : Type*} (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext x
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [PMF.mem_support_iff, not_not] at ha
    simp [ha]

namespace StateSimulation

variable {Q Q' : Type*} {P : Protocol Q Opinion Output} {P' : Protocol Q' Opinion Output}
  (S : StateSimulation P P')

include S

theorem stepDist_encC (hn : 2 ≤ n) {C : Config Q Opinion n} (hC : S.GoodC C) :
    stepDist P' hn (S.encC C) = (stepDist P hn C).map S.encC := by
  unfold stepDist
  rw [PMF.map_comp]
  congr 1
  funext p
  exact (S.encC_step hC p.1 p.2).symm

theorem hitFlagDist_encC (hn : 2 ≤ n) (G' : Config Q' Opinion n → Prop)
    {C : Config Q Opinion n} (hC : S.GoodC C) : ∀ t,
    hitFlagDist P' hn (S.encC C) G' t =
        (hitFlagDist P hn C (fun D => G' (S.encC D)) t).map (fun T => (S.encC T.1, T.2)) ∧
      ∀ T ∈ (hitFlagDist P hn C (fun D => G' (S.encC D)) t).support, S.GoodC T.1
  | 0 => by
      classical
      refine ⟨?_, ?_⟩
      · simp only [hitFlagDist, PMF.pure_map]
      · intro T hT
        simp only [hitFlagDist, PMF.support_pure, Set.mem_singleton_iff] at hT
        rw [hT]
        exact hC
  | t + 1 => by
      classical
      obtain ⟨ih, hgood⟩ := hitFlagDist_encC hn G' hC t
      refine ⟨?_, ?_⟩
      · rw [hitFlagDist, hitFlagDist, ih, PMF.bind_map, PMF.map_bind]
        apply PMF.bind_congr_support
        intro T hT
        simp only [Function.comp, hitFlagStepDist]
        rw [S.stepDist_encC hn (hgood T hT), PMF.map_comp, PMF.map_comp]
        rfl
      · intro T hT
        rw [hitFlagDist, PMF.mem_support_bind_iff] at hT
        obtain ⟨T₀, hT₀, hT⟩ := hT
        simp only [hitFlagStepDist, stepDist, PMF.map_comp, PMF.support_map,
          Set.mem_image] at hT
        obtain ⟨p, -, rfl⟩ := hT
        exact S.goodC_step (hgood T₀ hT₀) _ _

theorem probNotHitBy_encC (hn : 2 ≤ n) (G' : Config Q' Opinion n → Prop)
    {C : Config Q Opinion n} (hC : S.GoodC C) (t : ℕ) :
    probNotHitBy P' hn (S.encC C) G' t = probNotHitBy P hn C (fun D => G' (S.encC D)) t := by
  rw [probNotHitBy_eq_hitFlagDist_toOuterMeasure, probNotHitBy_eq_hitFlagDist_toOuterMeasure,
    (S.hitFlagDist_encC hn G' hC t).1, PMF.toOuterMeasure_map_apply]
  rfl

theorem expectedHittingTime_encC (hn : 2 ≤ n) (G' : Config Q' Opinion n → Prop)
    {C : Config Q Opinion n} (hC : S.GoodC C) :
    expectedHittingTime P' hn (S.encC C) G' =
      expectedHittingTime P hn C (fun D => G' (S.encC D)) := by
  unfold expectedHittingTime
  exact tsum_congr fun t => S.probNotHitBy_encC hn G' hC t

end StateSimulation

/-- **Window composition** (additive failure form): if from `C₀` the configuration misses
`Mid` within `t₁` steps with probability at most `a`, and from every `Mid` configuration `Goal` is
missed within `t₂` steps with probability at most `b`, then `Goal` is missed within `t₁ + t₂`
steps with probability at most `a + b`. -/
theorem probNotHitBy_compose_le {Q X Y : Type*} (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C₀ : Config Q X n) (Mid Goal : Config Q X n → Prop) (t₁ t₂ : ℕ) (a b : ℝ≥0∞)
    (ha : probNotHitBy P hn C₀ Mid t₁ ≤ a)
    (hb : ∀ C, Mid C → probNotHitBy P hn C Goal t₂ ≤ b) :
    probNotHitBy P hn C₀ Goal (t₁ + t₂) ≤ a + b := by
  classical
  have hnot_le : ∀ (C : Config Q X n) (G : Config Q X n → Prop) (t : ℕ),
      probNotHitBy P hn C G t ≤ 1 := fun C G t => by
    rw [← probHitBy_add_probNotHitBy P hn C G t]; exact le_add_self
  have hsum : ∀ (C : Config Q X n) (G : Config Q X n → Prop) (t : ℕ),
      probHitBy P hn C G t = 1 - probNotHitBy P hn C G t := fun C G t =>
    ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top (hnot_le C G t))
      (probHitBy_add_probNotHitBy P hn C G t)
  have hne : probNotHitBy P hn C₀ Goal (t₁ + t₂) = 1 - probHitBy P hn C₀ Goal (t₁ + t₂) :=
    ENNReal.eq_sub_of_add_eq
      (ne_top_of_le_ne_top ENNReal.one_ne_top (probHitBy_le_one' P hn C₀ Goal _))
      (by rw [add_comm]; exact probHitBy_add_probNotHitBy P hn C₀ Goal _)
  have hmul := probHitBy_add_ge_mul P hn C₀ Mid Goal t₁ t₂ (1 - a) (1 - b)
    (by rw [ProbHitWithin, hsum]; exact tsub_le_tsub_left ha 1)
    (fun C hC => by rw [ProbHitWithin, hsum]; exact tsub_le_tsub_left (hb C hC) 1)
  rw [hne]
  calc 1 - probHitBy P hn C₀ Goal (t₁ + t₂) ≤ 1 - (1 - a) * (1 - b) := tsub_le_tsub_left hmul 1
    _ ≤ a + b := by
        by_cases ha1 : a ≤ 1
        · by_cases hb1 : b ≤ 1
          · rw [tsub_le_iff_right]
            calc (1 : ℝ≥0∞) = (1 - a + a) * (1 - b) + b := by
                  rw [tsub_add_cancel_of_le ha1, one_mul, tsub_add_cancel_of_le hb1]
              _ = (1 - a) * (1 - b) + a * (1 - b) + b := by ring
              _ ≤ (1 - a) * (1 - b) + a + b := by
                  gcongr
                  exact mul_le_of_le_one_right zero_le tsub_le_self
              _ = a + b + (1 - a) * (1 - b) := by ring
          · exact tsub_le_self.trans ((le_of_lt (not_le.mp hb1)).trans le_add_self)
        · exact tsub_le_self.trans ((le_of_lt (not_le.mp ha1)).trans le_self_add)

/-! ### Definition 1 for the finite P_EM instances -/

instance finite_config_PEMFinState (n T E R D : ℕ) :
    Finite (Config (PEMFinState n T E R D) Opinion n) := by
  unfold Config
  infer_instance

/-- **Kanaya Definition 1 (probability one) for the finite paper instance.** -/
theorem P_EM_paper_fin_kanayaDefinition1 [Inhabited (Fin n × Fin n)] {trank e d : ℕ}
    {hn : 0 < n} (hn4 : 4 ≤ n) (hd : 1 ≤ d) (hn2 : 2 ≤ n) :
    KanayaDefinition1 (protocolPEMPaperFin n trank e d hn) n hn2 :=
  kanayaDefinition1_of_solvesSSEM_of_fintype hn2 (P_EM_paper_fin_solves_silent_SSEM hn4 hd).1

/-- The finite paper instance is silent with probability one. -/
theorem P_EM_paper_fin_silent_almostSurely [Inhabited (Fin n × Fin n)] {trank e d : ℕ}
    {hn : 0 < n} (hn4 : 4 ≤ n) (hd : 1 ≤ d) (hn2 : 2 ≤ n)
    (C₀ : Config (PEMFinState n (7 * (trank + 4)) (e * n) (rmaxPaper n) (d * n)) Opinion n) :
    reachesGoalAlmostSurely (protocolPEMPaperFin n trank e d hn) hn2 C₀
      (fun C => C.isSilent (protocolPEMPaperFin n trank e d hn)) :=
  silent_almostSurely_of_silentProtocol_of_fintype hn2
    (P_EM_paper_fin_solves_silent_SSEM hn4 hd).2 C₀

/-- **Kanaya Definition 1 (probability one) for the finite Lean instance** (`trank = n`). -/
theorem P_EM_fin_kanayaDefinition1 [Inhabited (Fin n × Fin n)] {hn : 0 < n} (hn4 : 4 ≤ n)
    (hn2 : 2 ≤ n) : KanayaDefinition1 (protocolPEMFin n n n n n hn) n hn2 :=
  kanayaDefinition1_of_solvesSSEM_of_fintype hn2 (P_EM_fin_silent_SSEM_states hn4).1.1

/-- Non-vacuity at `n = 4` with the constants of the time analysis (`trank = 40`, `e = 208`,
`d = 32`). -/
example : KanayaDefinition1 (protocolPEMPaperFin 4 40 208 32 (by norm_num)) 4 (by norm_num) :=
  P_EM_paper_fin_kanayaDefinition1 le_rfl (by norm_num) (by norm_num)

end Ripple.PopulationProtocol.SSEM
