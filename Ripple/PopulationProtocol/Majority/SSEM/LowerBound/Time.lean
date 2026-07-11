/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Time Lower Bound (Theorem 3) — scaffold

Theorem 3 of Kanaya et al. (2025): any silent self-stabilizing exact
majority protocol requires Ω(n) expected parallel time and Ω(n log n)
parallel time with high probability to reach a safe configuration.

Proof outline from the paper:
1. In a silent configuration for an odd population with more B than A,
   A-input agents have pairwise distinct states.
2. Replace one B-input agent by an A-input agent carrying one of those
   silent A states. The resulting configuration is not safe.
3. Because the original configuration is silent, the bad configuration
   can only be repaired after a particular pair of agents interacts.
4. This pair fires with probability `2 / (n * (n - 1))` per sequential
   interaction. Hence the expected wait is Ω(n²), i.e. Ω(n) parallel
   time.  The advertised whp lower bound needs a separate amplification
   or clarification; the one-pair geometric tail alone is not enough for
   the standard `1 - O(1/n)` meaning of whp.

This file is a **scaffold**.  The quantitative lower-bound claim is kept
as a target proposition until the stochastic waiting-time proof is closed;
the file lives outside the root import graph (`SSExactMajority.lean` does
not import it).  See `docs/TIME_BOUND_PLAN.md` for the full plan.
-/

import Ripple.PopulationProtocol.Majority.SSEM.Defs.Execution
import Ripple.PopulationProtocol.Majority.SSEM.LowerBound.Space
import Ripple.PopulationProtocol.Majority.SSEM.Probability.ExpectedTime

namespace SSEM

open scoped ENNReal

/-- A silent configuration is output-stable.

Kanaya §2 distinguishes the two predicates: safe/output-stable means
outputs never change, while silent means states never change. -/
theorem Config.isSilent.isOutputStable
    {Q X Y : Type*} [DecidableEq Q] [DecidableEq X]
    {n : ℕ} {P : Protocol Q X Y} {C : Config Q X n}
    (hSilent : C.isSilent P) :
    C.isOutputStable P := by
  intro γ t w
  have hExec : execution P C γ t = C := by
    induction t with
    | zero => rfl
    | succ t ih =>
        simp only [execution, ih]
        exact hSilent _ _
  rw [hExec]

/-- A protocol is *silent on `n` agents* if every deterministic execution
eventually reaches a silent configuration.

This is the deterministic-scheduler analogue of Kanaya §2's probabilistic
definition: under the uniform random scheduler, an execution reaches a
silent configuration with probability 1.  It deliberately uses
`Config.isSilent`, not `Config.isOutputStable`; the latter is only the
safe/stabilized predicate. -/
def SilentProtocol {Q : Type*} [DecidableEq Q]
    (P : Protocol Q Opinion Output) (n : ℕ) : Prop :=
  ∀ C₀ : Config Q Opinion n,
    ∀ (γ : DetScheduler n), ∃ t : ℕ,
      (execution P C₀ γ t).isSilent P

/-- Random-scheduler stabilization to a safe and correct configuration,
expressed through the finite-prefix PMF API.  This is the probabilistic
part of Kanaya §2's self-stabilizing exact-majority definition. -/
def RandomStabilizesSSEM {Q : Type*} [DecidableEq Q]
    (P : Protocol Q Opinion Output) (n : ℕ) (hn : 2 ≤ n) : Prop :=
  ∀ C₀ : Config Q Opinion n,
    Probability.reachesGoalAlmostSurely P hn C₀
      (fun C =>
        C.isOutputStable P ∧
        ExactMajoritySafe' P C Opinion.A Opinion.B Output.A Output.B Output.T)

/-- If a configuration is already output-stable, then `SolvesSSEM` forces it
to already have the correct exact-majority outputs. -/
theorem exactMajoritySafe_of_outputStable_of_solves
    {Q : Type*} [DecidableEq Q]
    {P : Protocol Q Opinion Output} {n : ℕ}
    {C : Config Q Opinion n}
    (hSolves : SolvesSSEM P n)
    (hStable : C.isOutputStable P) :
    ExactMajoritySafe' P C Opinion.A Opinion.B Output.A Output.B Output.T := by
  obtain ⟨γ, t, _hStable', hSafe'⟩ := hSolves C
  unfold ExactMajoritySafe' at hSafe' ⊢
  rw [Config.agentsWithInput_execution P C γ t Opinion.A] at hSafe'
  rw [Config.agentsWithInput_execution P C γ t Opinion.B] at hSafe'
  by_cases hgt : (C.agentsWithInput Opinion.A).card >
      (C.agentsWithInput Opinion.B).card
  · simp [hgt] at hSafe' ⊢
    intro w
    rw [hStable γ t w]
    exact hSafe' w
  · by_cases hlt : (C.agentsWithInput Opinion.A).card <
        (C.agentsWithInput Opinion.B).card
    · simp [hgt, hlt] at hSafe' ⊢
      intro w
      rw [hStable γ t w]
      exact hSafe' w
    · simp [hgt, hlt] at hSafe' ⊢
      intro w
      rw [hStable γ t w]
      exact hSafe' w

/-- A self-stabilizing exact-majority protocol on at least two agents has some
configuration that is not output-stable.  Otherwise all-A and one-A/rest-B
initial configurations would force incompatible outputs for the same local
state/input pair. -/
theorem exists_not_outputStable_of_solves
    {Q : Type*} [DecidableEq Q] [Nonempty Q]
    {P : Protocol Q Opinion Output} {n : ℕ} (hn : 2 ≤ n)
    (hSolves : SolvesSSEM P n) :
    ∃ C₀ : Config Q Opinion n, ¬ C₀.isOutputStable P := by
  classical
  by_contra hnone
  have hAllStable : ∀ C₀ : Config Q Opinion n, C₀.isOutputStable P := by
    intro C₀
    by_contra hC
    exact hnone ⟨C₀, hC⟩
  let q : Q := Classical.choice inferInstance
  let i0 : Fin n := ⟨0, by omega⟩
  let allA : Config Q Opinion n := fun _ => (q, Opinion.A)
  let mixed : Config Q Opinion n :=
    fun i => if i = i0 then (q, Opinion.A) else (q, Opinion.B)
  have hSafeAllA :
      ExactMajoritySafe' P allA Opinion.A Opinion.B Output.A Output.B Output.T :=
    exactMajoritySafe_of_outputStable_of_solves hSolves (hAllStable allA)
  have hAllA_A : allA.agentsWithInput Opinion.A = Finset.univ := by
    ext w
    simp [allA, Config.agentsWithInput, Config.inputOf]
  have hAllA_B : allA.agentsWithInput Opinion.B = ∅ := by
    ext w
    simp [allA, Config.agentsWithInput, Config.inputOf]
  have hqA : P.π_out (q, Opinion.A) = Output.A := by
    unfold ExactMajoritySafe' at hSafeAllA
    rw [hAllA_A, hAllA_B] at hSafeAllA
    simp only [Finset.card_univ, Fintype.card_fin, Finset.card_empty] at hSafeAllA
    have hnpos : 0 < n := by omega
    simp only [hnpos, gt_iff_lt, ↓reduceIte] at hSafeAllA
    have := hSafeAllA i0
    simpa [Config.allOutput, Config.outputOf, allA] using this
  have hSafeMixed :
      ExactMajoritySafe' P mixed Opinion.A Opinion.B Output.A Output.B Output.T :=
    exactMajoritySafe_of_outputStable_of_solves hSolves (hAllStable mixed)
  have hMixedA : mixed.agentsWithInput Opinion.A = {i0} := by
    ext w
    by_cases hw : w = i0
    · subst w
      simp [mixed, Config.agentsWithInput, Config.inputOf]
    · simp [mixed, Config.agentsWithInput, Config.inputOf, hw]
  have hMixedB : mixed.agentsWithInput Opinion.B = Finset.univ.erase i0 := by
    ext w
    by_cases hw : w = i0
    · subst w
      simp [mixed, Config.agentsWithInput, Config.inputOf]
    · simp [mixed, Config.agentsWithInput, Config.inputOf, hw]
  have hMixedOutNotA : mixed.outputOf P i0 ≠ Output.A := by
    unfold ExactMajoritySafe' at hSafeMixed
    rw [hMixedA, hMixedB] at hSafeMixed
    have hcardB : (Finset.univ.erase i0 : Finset (Fin n)).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ,
        Fintype.card_fin]
    simp only [Finset.card_singleton, hcardB] at hSafeMixed
    by_cases hn_eq_two : n = 2
    · have hnotGt : ¬ 1 > n - 1 := by omega
      have hnotLt : ¬ 1 < n - 1 := by omega
      simp only [hnotGt, hnotLt, ↓reduceIte] at hSafeMixed
      have := hSafeMixed i0
      rw [this]
      decide
    · have hnotGt : ¬ 1 > n - 1 := by omega
      have hlt : 1 < n - 1 := by omega
      simp only [hnotGt, hlt, ↓reduceIte] at hSafeMixed
      have := hSafeMixed i0
      rw [this]
      decide
  have hMixedOutA : mixed.outputOf P i0 = Output.A := by
    simp [Config.outputOf, mixed, i0, hqA]
  exact hMixedOutNotA hMixedOutA

/-- **Theorem 3, expected part (Ω(n) parallel time lower bound).**

Generic in the state type `Q`.  Goal is the protocol-level
output-stability `Config.isOutputStable P` — what `SolvesSSEM` actually
requires. -/
theorem time_lower_bound_omega_n_expected
    {Q : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    {P : Protocol Q Opinion Output} {n : ℕ} (hn : 2 ≤ n)
    (hSolves : SolvesSSEM P n)
    (hRandom : RandomStabilizesSSEM P n hn)
    (hSilent : SilentProtocol P n) :
    ∃ (C₀ : Config Q Opinion n) (c : ℝ), 0 < c ∧
      ENNReal.ofReal (c * n) ≤
        Probability.expectedParallelTime P hn C₀
          (fun C => C.isOutputStable P) := by
  classical
  obtain ⟨C₀, hC₀⟩ := exists_not_outputStable_of_solves hn hSolves
  let c : ℝ := ((n : ℝ) * (n : ℝ))⁻¹
  refine ⟨C₀, c, ?_, ?_⟩
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    positivity
  · have hpar :=
      Probability.inv_nat_le_expectedParallelTime_of_not_goal
        P hn C₀ (fun C => C.isOutputStable P) hC₀
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hc : c * n = (n : ℝ)⁻¹ := by
      dsimp [c]
      field_simp [hnpos.ne']
    calc
      ENNReal.ofReal (c * n) = ((n : ENNReal))⁻¹ := by
        rw [hc, ENNReal.ofReal_inv_of_pos hnpos, ENNReal.ofReal_natCast]
      _ ≤ Probability.expectedParallelTime P hn C₀
          (fun C => C.isOutputStable P) := hpar

end SSEM
