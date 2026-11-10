/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reachability implies probability one on a finite configuration space

If from every configuration some deterministic schedule reaches `Goal`, and the configuration
space is finite, then the uniform random scheduler reaches `Goal` almost surely from every
configuration (`reachesGoalAlmostSurely_of_fintype`). Every reachable path of length `t` has
probability at least `(n (n - 1))⁻¹ ^ t` (`probHitBy_ge_of_execution`), and finitely many
configurations give a uniform window.

Consequence: a protocol on a finite state set that solves SSEM in the reachability sense
satisfies Kanaya et al.'s Definition 1 literally (`kanayaDefinition1_of_solvesSSEM_of_fintype`).
-/

import Ripple.PopulationProtocol.SSEM.Probability.ExpectedTime
import Ripple.PopulationProtocol.SSEM.Defs.Silent

namespace Ripple.PopulationProtocol.SSEM
namespace Probability

open scoped ENNReal
open Filter Topology

variable {Q X Y : Type*} {n : ℕ}

theorem probHitBy_mono_time_of_le (P : Protocol Q X Y) (hn : 2 ≤ n) (C₀ : Config Q X n)
    (Goal : Config Q X n → Prop) {s t : ℕ} (h : s ≤ t) :
    probHitBy P hn C₀ Goal s ≤ probHitBy P hn C₀ Goal t :=
  monotone_nat_of_le_succ (fun k => probHitBy_le_succ P hn C₀ Goal k) h

theorem probHitBy_le_one' (P : Protocol Q X Y) (hn : 2 ≤ n) (C₀ : Config Q X n)
    (Goal : Config Q X n → Prop) (t : ℕ) : probHitBy P hn C₀ Goal t ≤ 1 := by
  rw [← probHitBy_add_probNotHitBy P hn C₀ Goal t]
  exact le_self_add

/-- The one-pair probability. -/
noncomputable def pairProb (n : ℕ) : ℝ≥0∞ := ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹

theorem pairProb_le_one (hn : 2 ≤ n) : pairProb n ≤ 1 := by
  unfold pairProb
  apply ENNReal.inv_le_one.mpr
  have : 1 ≤ n * (n - 1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  exact_mod_cast this

theorem pairProb_ne_zero : pairProb n ≠ 0 := by
  unfold pairProb
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

/-- **A deterministic path of length `t` has probability at least `pairProb n ^ t`.** -/
theorem probHitBy_ge_of_execution (P : Protocol Q X Y) (hn : 2 ≤ n) :
    ∀ (t : ℕ) (Goal : Config Q X n → Prop) (C : Config Q X n) (γ : DetScheduler n),
      Goal (execution P C γ t) → pairProb n ^ t ≤ probHitBy P hn C Goal t
  | 0, Goal, C, γ, h => by
      rw [pow_zero, probHitBy_zero_of_goal P hn C Goal h]
  | t + 1, Goal, C, γ, h => by
      classical
      have ih := probHitBy_ge_of_execution P hn t (fun D => D = execution P C γ t) C γ rfl
      have hstep : ∀ D : Config Q X n, D = execution P C γ t →
          pairProb n ≤ ProbHitWithin P hn D Goal 1 := by
        intro D hD
        by_cases hG : Goal D
        · calc pairProb n ≤ 1 := pairProb_le_one hn
            _ = ProbHitWithin P hn D Goal 0 := (probHitBy_zero_of_goal P hn D Goal hG).symm
            _ ≤ ProbHitWithin P hn D Goal 1 := probHitBy_le_succ P hn D Goal 0
        · have hG' : Goal (D.step P (γ t).1 (γ t).2) := by rw [hD]; exact h
          by_cases huv : (γ t).1 = (γ t).2
          · exfalso
            apply hG
            have : D.step P (γ t).1 (γ t).2 = D := by simp [Config.step, huv]
            rw [this] at hG'
            exact hG'
          · exact probHitBy_one_lower_bound_of_step P hn D Goal hG huv hG'
      have := probHitBy_add_ge_mul P hn C (fun D => D = execution P C γ t) Goal t 1
        (pairProb n ^ t) (pairProb n) ih hstep
      rw [pow_succ]
      exact this

/-- **Finite configuration space: reachability gives probability one.** -/
theorem reachesGoalAlmostSurely_of_fintype [Finite (Config Q X n)] (P : Protocol Q X Y)
    (hn : 2 ≤ n) (Goal : Config Q X n → Prop)
    (hreach : ∀ C : Config Q X n, ∃ (γ : DetScheduler n) (t : ℕ), Goal (execution P C γ t))
    (C₀ : Config Q X n) : reachesGoalAlmostSurely P hn C₀ Goal := by
  classical
  letI := Fintype.ofFinite (Config Q X n)
  choose γ τ hτ using hreach
  set K : ℕ := Finset.univ.sup τ
  set p : ℝ≥0∞ := pairProb n ^ K
  have hwin : ∀ C : Config Q X n, ¬ Goal C → p ≤ ProbHitWithin P hn C Goal K := by
    intro C _
    have hle : τ C ≤ K := Finset.le_sup (Finset.mem_univ C)
    calc p ≤ pairProb n ^ τ C := pow_le_pow_of_le_one zero_le (pairProb_le_one hn) hle
      _ ≤ probHitBy P hn C Goal (τ C) := probHitBy_ge_of_execution P hn _ Goal C (γ C) (hτ C)
      _ ≤ probHitBy P hn C Goal K := probHitBy_mono_time_of_le P hn C Goal hle
  unfold reachesGoalAlmostSurely
  apply le_antisymm (iSup_le fun t => probHitBy_le_one' P hn C₀ Goal t)
  by_cases hG : Goal C₀
  · calc (1 : ℝ≥0∞) = probHitBy P hn C₀ Goal 0 := (probHitBy_zero_of_goal P hn C₀ Goal hG).symm
      _ ≤ ⨆ t, probHitBy P hn C₀ Goal t := le_iSup (fun t => probHitBy P hn C₀ Goal t) 0
  · have hr := probHitBy_mul_window_ge_one_sub_pow_of_not_goal P hn C₀ Goal K p hG hwin
    have hp0 : p ≠ 0 := pow_ne_zero _ pairProb_ne_zero
    have hp1 : p ≤ 1 := pow_le_one₀ zero_le (pairProb_le_one hn)
    have hlt : 1 - p < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hp0
    have h0 : Tendsto (fun r : ℕ => (1 - p) ^ r) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_iff.mpr hlt
    have hlim : Tendsto (fun r : ℕ => 1 - (1 - p) ^ r) atTop (𝓝 (1 - 0)) :=
      ENNReal.Tendsto.sub tendsto_const_nhds h0 (Or.inl ENNReal.one_ne_top)
    rw [tsub_zero] at hlim
    exact le_of_tendsto' hlim fun r =>
      (hr r).trans (le_iSup (fun t => probHitBy P hn C₀ Goal t) (r * K))

/-- **Kanaya et al. Definition 1 from reachability on a finite state set.** -/
theorem kanayaDefinition1_of_solvesSSEM_of_fintype [DecidableEq Q]
    {P : Protocol Q Opinion Output} [Finite (Config Q Opinion n)] (hn : 2 ≤ n)
    (h : SolvesSSEM P n) : KanayaDefinition1 P n hn := by
  intro C₀
  refine ⟨fun γ t hst => exactMajoritySafe_of_outputStable_of_solves h hst, ?_⟩
  apply reachesGoalAlmostSurely_of_fintype P hn
  intro C
  obtain ⟨γ, t, hst, -⟩ := h C
  exact ⟨γ, t, hst⟩

/-- Almost-sure silence from reachability of a silent configuration on a finite state set. -/
theorem silent_almostSurely_of_silentProtocol_of_fintype [DecidableEq Q]
    {P : Protocol Q Opinion Output} [Finite (Config Q Opinion n)] (hn : 2 ≤ n)
    (h : SilentProtocol P n) (C₀ : Config Q Opinion n) :
    reachesGoalAlmostSurely P hn C₀ (fun C => C.isSilent P) :=
  reachesGoalAlmostSurely_of_fintype P hn _ h C₀

end Probability
end Ripple.PopulationProtocol.SSEM
