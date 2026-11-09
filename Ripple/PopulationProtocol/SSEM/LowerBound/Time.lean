/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Time lower bound (Kanaya et al. 2025, Theorem 3)

Source: arXiv:2503.17652v1, §5.1 (`ref/Kanaya-2025-SSEM-2503.17652v1.pdf`). Theorem 3: any
silent self-stabilizing exact-majority protocol needs Ω(n) parallel time in expectation and
Ω(n log n) parallel time with high probability to reach a safe configuration.

Proof (the paper's, with the input split `|V_a| = ⌊n/2⌋`, which works for every `n ≥ 2`): take a
silent configuration `C` with `⌊n/2⌋` agents of input `A`; it outputs the majority (`B` or `T`).
Give one `B` agent `u` the state and input `(s_A, A)` of an `A` agent `w`. The new configuration
`C'` has majority `A` but every agent still outputs `B` or `T`, so it is not safe; and since `C` is
silent, every interaction other than the pair `{u, w}` leaves `C'` unchanged
(`exists_stuck_config`). Under the uniform random scheduler the pair `{u, w}` is drawn with
probability `2 / (n (n - 1))` per interaction, so the first hitting time of a safe configuration
dominates a geometric variable with that parameter:

* `time_lower_bound_tail`: `P[T > t] ≥ (1 - 2/(n(n-1)))^t`;
* `time_lower_bound_expected`: `E[T] / n ≥ (n - 1) / 2` (parallel time);
* `time_lower_bound_omega_n_expected`: Ω(n) with the uniform constant `1/4`;
* `time_lower_bound_whp`: if `P[T > t] ≤ ε` then `t ≥ (n(n-1)/2 - 1) ln(1/ε)` interactions;
  with `ε = O(1/n)` this is Ω(n log n) parallel time.

Silence and self-stabilization are the reachability forms `SilentProtocol` and `SolvesSSEM`,
implied by the paper's probability-one definitions (`Defs/Silent.lean`).
-/

import Ripple.PopulationProtocol.SSEM.Defs.Execution
import Ripple.PopulationProtocol.SSEM.LowerBound.Space
import Ripple.PopulationProtocol.SSEM.Probability.ExpectedTime

namespace Ripple.PopulationProtocol.SSEM

open scoped ENNReal

universe u

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
      ExactMajoritySafe P allA Opinion.A Opinion.B Output.A Output.B Output.T :=
    exactMajoritySafe_of_outputStable_of_solves hSolves (hAllStable allA)
  have hAllA_A : allA.agentsWithInput Opinion.A = Finset.univ := by
    ext w
    simp [allA, Config.agentsWithInput, Config.inputOf]
  have hAllA_B : allA.agentsWithInput Opinion.B = ∅ := by
    ext w
    simp [allA, Config.agentsWithInput, Config.inputOf]
  have hqA : P.π_out (q, Opinion.A) = Output.A := by
    unfold ExactMajoritySafe at hSafeAllA
    rw [hAllA_A, hAllA_B] at hSafeAllA
    simp only [Finset.card_univ, Fintype.card_fin, Finset.card_empty] at hSafeAllA
    have hnpos : 0 < n := by omega
    simp only [hnpos, gt_iff_lt, ↓reduceIte] at hSafeAllA
    have := hSafeAllA i0
    simpa [Config.allOutput, Config.outputOf, allA] using this
  have hSafeMixed :
      ExactMajoritySafe P mixed Opinion.A Opinion.B Output.A Output.B Output.T :=
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
    unfold ExactMajoritySafe at hSafeMixed
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

/-! ### A configuration that only the pair `{u, w}` can change -/

/-- For distinct agents, an interaction fixes a configuration exactly when the transition
returns both states unchanged. -/
theorem Config.step_eq_self_iff {Q X Y : Type*} {n : ℕ} {P : Protocol Q X Y}
    {C : Config Q X n} {i j : Fin n} (hij : i ≠ j) :
    C.step P i j = C ↔ P.δ (C i, C j) = ((C i).1, (C j).1) := by
  unfold Config.step
  rw [if_neg hij]
  constructor
  · intro h
    have h1 := congr_fun h i
    have h2 := congr_fun h j
    simp only [if_neg (Ne.symm hij), ↓reduceIte] at h1 h2
    have e1 := congr_arg Prod.fst h1
    have e2 := congr_arg Prod.fst h2
    simp only at e1 e2
    exact Prod.ext e1 e2
  · intro h
    funext x
    by_cases hx : x = i
    · subst hx
      simp [h]
    · by_cases hxj : x = j
      · subst hxj
        simp [hx, h]
      · simp [hx, hxj]

/-- **The stuck configuration of Theorem 3.** For a silent SSEM protocol on `n ≥ 2` agents there
is a configuration that is not safe and that every interaction other than the two orientations of
one pair `{u, w}` leaves unchanged. -/
theorem exists_stuck_config {Q : Type*} [DecidableEq Q] [Nonempty Q]
    {P : Protocol Q Opinion Output} {n : ℕ} (hn : 2 ≤ n)
    (hSolves : SolvesSSEM P n) (hSilent : SilentProtocol P n) :
    ∃ (C₀ : Config Q Opinion n) (u w : Fin n), u ≠ w ∧ ¬ C₀.isOutputStable P ∧
      ∀ i j : Fin n, ¬ (i = u ∧ j = w) → ¬ (i = w ∧ j = u) → C₀.step P i j = C₀ := by
  classical
  obtain ⟨C, hS, hSafe, hA, hB⟩ :=
    exists_silent_config_with_inputA_card hSolves hSilent (n / 2) (by omega)
  obtain ⟨w, hw⟩ : (C.agentsWithInput Opinion.A).Nonempty :=
    Finset.card_pos.mp (by rw [hA]; omega)
  obtain ⟨u, hu⟩ : (C.agentsWithInput Opinion.B).Nonempty :=
    Finset.card_pos.mp (by rw [hB]; omega)
  have hwA : C.inputOf w = Opinion.A := by simpa [Config.agentsWithInput] using hw
  have huB : C.inputOf u = Opinion.B := by simpa [Config.agentsWithInput] using hu
  have hwA' : (C w).2 = Opinion.A := hwA
  have huw : u ≠ w := by
    intro h
    rw [h, hwA] at huB
    cases huB
  -- the output of `w` in `C` is the majority of `C`, which is not `A`
  have hwOut : P.π_out (C w) ≠ Output.A := by
    have h := hSafe
    simp only [ExactMajoritySafe, hA, hB] at h
    have hngt : ¬ (n / 2 > n - n / 2) := by omega
    rw [if_neg hngt] at h
    split_ifs at h
    · have := h w
      simp only [Config.outputOf] at this
      rw [this]; decide
    · have := h w
      simp only [Config.outputOf] at this
      rw [this]; decide
  let C₀ : Config Q Opinion n := Function.update C u (C w)
  have hC₀u : C₀ u = C w := Function.update_self u (C w) C
  have hC₀ : ∀ x, x ≠ u → C₀ x = C x := fun x hx => Function.update_of_ne hx (C w) C
  refine ⟨C₀, u, w, huw, ?_, ?_⟩
  · -- `C₀` has majority `A` but `u` outputs the majority of `C`
    intro hStable
    have hSafe₀ := exactMajoritySafe_of_outputStable_of_solves hSolves hStable
    have hA₀ : C₀.agentsWithInput Opinion.A = insert u (C.agentsWithInput Opinion.A) := by
      ext x
      by_cases hx : x = u
      · subst hx
        simp [Config.agentsWithInput, Config.inputOf, hC₀u, hwA']
      · simp [Config.agentsWithInput, Config.inputOf, hC₀ x hx, hx]
    have hu_notin : u ∉ C.agentsWithInput Opinion.A := by
      simp [Config.agentsWithInput, huB]
    have hcardA : (C₀.agentsWithInput Opinion.A).card = n / 2 + 1 := by
      rw [hA₀, Finset.card_insert_of_notMem hu_notin, hA]
    have hsum := Config.card_inputA_add_card_inputB C₀
    have hgt : (C₀.agentsWithInput Opinion.A).card > (C₀.agentsWithInput Opinion.B).card := by
      omega
    simp only [ExactMajoritySafe] at hSafe₀
    rw [if_pos hgt] at hSafe₀
    have := hSafe₀ u
    simp only [Config.outputOf, hC₀u] at this
    exact hwOut this
  · -- only the pair `{u, w}` can move `C₀`
    intro i j hiuw hiwu
    by_cases hij : i = j
    · subst hij
      simp [Config.step]
    rw [Config.step_eq_self_iff hij]
    have hfix : ∀ a b : Fin n, a ≠ b → P.δ (C a, C b) = ((C a).1, (C b).1) :=
      fun a b hab => (Config.step_eq_self_iff hab).mp (hS a b)
    by_cases hiu : i = u
    · subst hiu
      have hjw : j ≠ w := fun h => hiuw ⟨rfl, h⟩
      have hju := Ne.symm hij
      rw [hC₀u, hC₀ j hju]
      exact hfix w j (Ne.symm hjw)
    · by_cases hju : j = u
      · subst hju
        have hiw := fun h => hiwu ⟨h, rfl⟩
        rw [hC₀u, hC₀ i hiu]
        exact hfix i w hiw
      · rw [hC₀ i hiu, hC₀ j hju]
        exact hfix i j hij

/-! ### Geometric domination of the hitting time -/

namespace Probability

variable {Q X Y : Type*} {n : ℕ}

/-- If `C` is not a goal configuration and one random step from `C` stays at `C` with
probability at least `q`, then the goal is not hit within `t` steps with probability at least
`q ^ t`. -/
theorem pow_le_probNotHitBy_of_stay (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C : Config Q X n) (Goal : Config Q X n → Prop) (hC : ¬ Goal C)
    (q : ℝ≥0∞) (hq : q ≤ stepDist P hn C C) (t : ℕ) :
    q ^ t ≤ probNotHitBy P hn C Goal t := by
  classical
  have hstep : stepDist P hn C C ≤ hitFlagStepDist P hn Goal (C, false) (C, false) := by
    unfold hitFlagStepDist
    rw [PMF.map_apply]
    refine le_trans (le_of_eq ?_) (ENNReal.le_tsum C)
    simp [hC]
  have key : ∀ t : ℕ, q ^ t ≤ hitFlagDist P hn C Goal t (C, false) := by
    intro t
    induction t with
    | zero => simp [hitFlagDist, hC]
    | succ t ih =>
        calc q ^ (t + 1) = q ^ t * q := pow_succ q t
          _ ≤ hitFlagDist P hn C Goal t (C, false) *
                hitFlagStepDist P hn Goal (C, false) (C, false) :=
              mul_le_mul' ih (hq.trans hstep)
          _ ≤ ∑' S, hitFlagDist P hn C Goal t S * hitFlagStepDist P hn Goal S (C, false) :=
              ENNReal.le_tsum (f := fun S =>
                hitFlagDist P hn C Goal t S * hitFlagStepDist P hn Goal S (C, false)) (C, false)
          _ = hitFlagDist P hn C Goal (t + 1) (C, false) := by
              show _ = ((hitFlagDist P hn C Goal t).bind (hitFlagStepDist P hn Goal)) (C, false)
              rw [PMF.bind_apply]
  calc q ^ t ≤ hitFlagDist P hn C Goal t (C, false) := key t
    _ ≤ probNotHitBy P hn C Goal t := by
        unfold probNotHitBy
        refine le_trans (le_of_eq ?_) (ENNReal.le_tsum (C, false))
        simp

/-- Scheduler mass of the ordered pairs other than `(u, w)` and `(w, u)`. -/
noncomputable def offPairMass (n : ℕ) (hn : 2 ≤ n) (u w : Fin n) : ℝ≥0∞ :=
  pairSetMass n hn
    ((OffDiagonalPairs n).filter fun p => ¬ (p.1 = u ∧ p.2 = w) ∧ ¬ (p.1 = w ∧ p.2 = u))

/-- The pairs other than `{u, w}` carry mass `1 - 2 / (n (n - 1))`. -/
theorem offPairMass_add (n : ℕ) (hn : 2 ≤ n) {u w : Fin n} (huw : u ≠ w) :
    offPairMass n hn u w + 2 * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹ = 1 := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (OffDiagonalPairs n)
    (fun p : Fin n × Fin n => ¬ (p.1 = u ∧ p.2 = w) ∧ ¬ (p.1 = w ∧ p.2 = u))
    (fun p => uniformPair n hn p)
  have hbad : ((OffDiagonalPairs n).filter fun p : Fin n × Fin n =>
      ¬ (¬ (p.1 = u ∧ p.2 = w) ∧ ¬ (p.1 = w ∧ p.2 = u))) = {(u, w), (w, u)} := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, mem_offDiagonalPairs, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨-, h⟩
      tauto
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨huw, by tauto⟩
      · exact ⟨Ne.symm huw, by tauto⟩
  have hne : (u, w) ≠ (w, u) := by
    intro h
    exact huw (congr_arg Prod.fst h)
  rw [hbad, Finset.sum_pair hne, uniformPair_apply_pair_add_swap_of_ne n hn huw] at hsplit
  rw [offPairMass, pairSetMass, hsplit]
  exact pairSetMass_offDiagonalPairs n hn

/-- From a configuration that every pair other than `{u, w}` fixes, one random step stays put
with probability at least `offPairMass`. -/
theorem offPairMass_le_stepDist_self (P : Protocol Q X Y) (hn : 2 ≤ n)
    (C : Config Q X n) (u w : Fin n)
    (hfix : ∀ i j : Fin n, ¬ (i = u ∧ j = w) → ¬ (i = w ∧ j = u) → C.step P i j = C) :
    offPairMass n hn u w ≤ stepDist P hn C C := by
  classical
  unfold offPairMass pairSetMass stepDist
  rw [PMF.map_apply]
  calc ∑ p ∈ (OffDiagonalPairs n).filter
          (fun p => ¬ (p.1 = u ∧ p.2 = w) ∧ ¬ (p.1 = w ∧ p.2 = u)), uniformPair n hn p
      = ∑ p ∈ (OffDiagonalPairs n).filter
          (fun p => ¬ (p.1 = u ∧ p.2 = w) ∧ ¬ (p.1 = w ∧ p.2 = u)),
          (if C = C.step P p.1 p.2 then uniformPair n hn p else 0) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp' := (Finset.mem_filter.mp hp).2
        rw [if_pos (hfix p.1 p.2 hp'.1 hp'.2).symm]
    _ ≤ ∑' p, (if C = C.step P p.1 p.2 then uniformPair n hn p else 0) :=
        ENNReal.sum_le_tsum _

end Probability

/-! ### Theorem 3 -/

/-- **Theorem 3, tail form.** For a silent SSEM protocol on `n ≥ 2` agents there is a
configuration from which, under the uniform random scheduler, no safe configuration is reached
within `t` interactions with probability at least `(1 - 2/(n(n-1)))^t`. -/
theorem time_lower_bound_tail {Q : Type*} [DecidableEq Q] [Nonempty Q]
    {P : Protocol Q Opinion Output} {n : ℕ} (hn : 2 ≤ n)
    (hSolves : SolvesSSEM P n) (hSilent : SilentProtocol P n) :
    ∃ C₀ : Config Q Opinion n, ∀ t : ℕ,
      (1 - 2 * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹) ^ t ≤
        Probability.probNotHitBy P hn C₀ (fun C => C.isOutputStable P) t := by
  obtain ⟨C₀, u, w, huw, hNot, hfix⟩ := exists_stuck_config hn hSolves hSilent
  refine ⟨C₀, fun t => ?_⟩
  have hq : 1 - 2 * ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹ = Probability.offPairMass n hn u w := by
    rw [← Probability.offPairMass_add n hn huw]
    exact ENNReal.add_sub_cancel_right
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.inv_ne_top.mpr (by
        have : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
        exact_mod_cast this.ne')))
  rw [hq]
  exact Probability.pow_le_probNotHitBy_of_stay P hn C₀ _ hNot _
    (Probability.offPairMass_le_stepDist_self P hn C₀ u w hfix) t

/-- **Theorem 3, expected form (explicit constant).** For a silent SSEM protocol on `n ≥ 2`
agents there is a configuration whose expected parallel time to reach a safe configuration under
the uniform random scheduler is at least `(n - 1) / 2`. -/
theorem time_lower_bound_expected {Q : Type*} [DecidableEq Q] [Nonempty Q]
    {P : Protocol Q Opinion Output} {n : ℕ} (hn : 2 ≤ n)
    (hSolves : SolvesSSEM P n) (hSilent : SilentProtocol P n) :
    ∃ C₀ : Config Q Opinion n,
      ((n - 1 : ℕ) : ℝ≥0∞) / 2 ≤
        Probability.expectedParallelTime P hn C₀ (fun C => C.isOutputStable P) := by
  obtain ⟨C₀, u, w, huw, hNot, hfix⟩ := exists_stuck_config hn hSolves hSilent
  refine ⟨C₀, ?_⟩
  set N : ℝ≥0∞ := ((n * (n - 1) : ℕ) : ℝ≥0∞) with hN
  set q := Probability.offPairMass n hn u w
  have hNpos : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  have hN0 : N ≠ 0 := by rw [hN]; exact_mod_cast hNpos.ne'
  have hNtop : N ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsum : q + 2 * N⁻¹ = 1 := Probability.offPairMass_add n hn huw
  -- `E[T] ≥ ∑ q^t = (1 - q)⁻¹ ≥ N / 2`
  have hE : 2⁻¹ * N ≤ Probability.expectedHittingTime P hn C₀ (fun C => C.isOutputStable P) := by
    have h1 : (1 - q)⁻¹ ≤ Probability.expectedHittingTime P hn C₀
        (fun C => C.isOutputStable P) := by
      rw [← ENNReal.tsum_geometric, Probability.expectedHittingTime]
      exact ENNReal.tsum_le_tsum fun t =>
        Probability.pow_le_probNotHitBy_of_stay P hn C₀ _ hNot q
          (Probability.offPairMass_le_stepDist_self P hn C₀ u w hfix) t
    have h2 : 1 - q ≤ 2 * N⁻¹ := by
      rw [tsub_le_iff_left]
      exact le_of_eq hsum.symm
    have h3 : (2 * N⁻¹)⁻¹ = 2⁻¹ * N := by
      rw [ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl (by norm_num)), inv_inv]
    calc 2⁻¹ * N = (2 * N⁻¹)⁻¹ := h3.symm
      _ ≤ (1 - q)⁻¹ := ENNReal.inv_le_inv.mpr h2
      _ ≤ _ := h1
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hntop : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hval : 2⁻¹ * N / n = ((n - 1 : ℕ) : ℝ≥0∞) / 2 := by
    rw [hN, Nat.cast_mul, div_eq_mul_inv, div_eq_mul_inv]
    calc 2⁻¹ * ((n : ℝ≥0∞) * ((n - 1 : ℕ) : ℝ≥0∞)) * (n : ℝ≥0∞)⁻¹
        = ((n - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ * ((n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹) := by ring
      _ = ((n - 1 : ℕ) : ℝ≥0∞) * 2⁻¹ := by rw [ENNReal.mul_inv_cancel hn0 hntop, mul_one]
  rw [← hval, Probability.expectedParallelTime, Probability.parallelTime]
  exact ENNReal.div_le_div_right hE _

/-- **Theorem 3, expected part (Ω(n) parallel time).** There is a constant `c > 0` such that
every silent self-stabilizing exact-majority protocol, on every population size `n ≥ 2`, has an
initial configuration from which the expected parallel time to reach a safe configuration under
the uniform random scheduler is at least `c · n`. The constant is `c = 1/4`. -/
theorem time_lower_bound_omega_n_expected :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Q : Type u} [DecidableEq Q] [Nonempty Q] (P : Protocol Q Opinion Output)
        (n : ℕ) (hn : 2 ≤ n),
        SolvesSSEM P n → SilentProtocol P n →
        ∃ C₀ : Config Q Opinion n,
          ENNReal.ofReal (c * n) ≤
            Probability.expectedParallelTime P hn C₀ (fun C => C.isOutputStable P) := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro Q _ _ P n hn hSolves hSilent
  obtain ⟨C₀, hC₀⟩ := time_lower_bound_expected hn hSolves hSilent
  refine ⟨C₀, le_trans ?_ hC₀⟩
  have hcast : (((n - 1 : ℕ) : ℝ≥0∞) / 2) = ENNReal.ofReal (((n - 1 : ℕ) : ℝ) / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  rw [hcast]
  apply ENNReal.ofReal_le_ofReal
  have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  rw [this]
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- **Theorem 3, high-probability part (Ω(n log n) parallel time).** For a silent SSEM protocol
on `n ≥ 2` agents there is a configuration such that, whenever the probability of not having
reached a safe configuration within `t` interactions is at most `ε > 0`, the number of
interactions satisfies `t ≥ (n(n-1)/2 - 1) · ln(1/ε)`. With failure probability `ε = O(1/n)`
this is `t / n = Ω(n log n)` parallel time. -/
theorem time_lower_bound_whp {Q : Type*} [DecidableEq Q] [Nonempty Q]
    {P : Protocol Q Opinion Output} {n : ℕ} (hn : 2 ≤ n)
    (hSolves : SolvesSSEM P n) (hSilent : SilentProtocol P n) :
    ∃ C₀ : Config Q Opinion n, ∀ (t : ℕ) (ε : ℝ), 0 < ε →
      Probability.probNotHitBy P hn C₀ (fun C => C.isOutputStable P) t ≤ ENNReal.ofReal ε →
      ((n * (n - 1) : ℝ) / 2 - 1) * Real.log (1 / ε) ≤ t := by
  obtain ⟨C₀, hC₀⟩ := time_lower_bound_tail hn hSolves hSilent
  refine ⟨C₀, fun t ε hε hfail => ?_⟩
  set Nn : ℕ := n * (n - 1) with hNn
  have hNpos : 0 < Nn := Nat.mul_pos (by omega) (by omega)
  have hNreal : (Nn : ℝ) = (n * (n - 1) : ℝ) := by
    rw [hNn, Nat.cast_mul, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  rw [← hNreal]
  have hN2 : (2 : ℝ) ≤ Nn := by
    have : 2 ≤ Nn := by
      rw [hNn]
      calc 2 = 2 * 1 := rfl
        _ ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
    exact_mod_cast this
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  -- the real number `r = 1 - 2/N`
  set r : ℝ := 1 - 2 / (Nn : ℝ) with hr
  have hNposR : (0 : ℝ) < Nn := by exact_mod_cast hNpos
  have hr0 : 0 ≤ r := by
    rw [hr, sub_nonneg, div_le_one hNposR]
    exact hN2
  have hq : (1 - 2 * ((Nn : ℕ) : ℝ≥0∞)⁻¹) = ENNReal.ofReal r := by
    rw [hr, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_div_of_pos hNposR, ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast,
      div_eq_mul_inv]
  have hpow : r ^ t ≤ ε := by
    have h := (hC₀ t).trans hfail
    rw [hq, ← ENNReal.ofReal_pow hr0] at h
    exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp h
  rcases eq_or_lt_of_le hN2 with hNeq | hNgt
  · -- `N = 2`: the coefficient is `0`
    rw [← hNeq]
    norm_num
  · have hrpos : 0 < r := by
      rw [hr, sub_pos, div_lt_one hNposR]
      exact hNgt
    -- `t · log r ≤ log ε`
    have hlog : (t : ℝ) * Real.log r ≤ Real.log ε := by
      rw [← Real.log_pow]
      exact Real.log_le_log (pow_pos hrpos t) hpow
    have hNm2 : (0 : ℝ) < (Nn : ℝ) - 2 := by linarith
    -- `log r ≥ -2/(N-2)`
    have hlogr : -(2 / ((Nn : ℝ) - 2)) ≤ Real.log r := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hrpos)
      rw [Real.log_inv] at h
      have hr' : r = ((Nn : ℝ) - 2) / Nn := by
        rw [hr]
        first | (field_simp; ring) | field_simp
      have hrinv : r⁻¹ - 1 = 2 / ((Nn : ℝ) - 2) := by
        rw [hr', inv_div, div_sub_one hNm2.ne']
        ring
      linarith
    have hkey : Real.log (1 / ε) ≤ (t : ℝ) * (2 / ((Nn : ℝ) - 2)) := by
      rw [one_div, Real.log_inv]
      nlinarith [mul_nonneg ht0 (sub_nonneg.mpr hlogr), hlog]
    have hcoef : (Nn : ℝ) / 2 - 1 = ((Nn : ℝ) - 2) / 2 := by ring
    rw [hcoef]
    calc ((Nn : ℝ) - 2) / 2 * Real.log (1 / ε)
        ≤ ((Nn : ℝ) - 2) / 2 * ((t : ℝ) * (2 / ((Nn : ℝ) - 2))) :=
          mul_le_mul_of_nonneg_left hkey (by linarith)
      _ = t := by
          have := hNm2.ne'
          first | (field_simp; ring) | field_simp

/-! ### Non-vacuity: a silent SSEM protocol on two agents -/

/-- The majority output of two inputs. -/
def pairMajority : Opinion → Opinion → Output
  | .A, .A => .A
  | .B, .B => .B
  | _, _ => .T

/-- A three-state protocol for two agents: both agents copy the majority of their two inputs
into their state, and output their state. -/
def twoAgentProtocol : Protocol Output Opinion Output where
  δ := fun p => (pairMajority p.1.2 p.2.2, pairMajority p.1.2 p.2.2)
  π_out := fun s => s.1

theorem pairMajority_comm (x y : Opinion) : pairMajority x y = pairMajority y x := by
  cases x <;> cases y <;> rfl

/-- After one interaction of the two agents, the configuration is silent and outputs the exact
majority. -/
theorem twoAgentProtocol_step_silent_correct (C : Config Output Opinion 2) :
    (C.step twoAgentProtocol 0 1).isSilent twoAgentProtocol ∧
      ExactMajoritySafe twoAgentProtocol (C.step twoAgentProtocol 0 1)
        Opinion.A Opinion.B Output.A Output.B Output.T := by
  set m := pairMajority (C 0).2 (C 1).2 with hm
  have hD : C.step twoAgentProtocol 0 1 = fun w => (m, (C w).2) := by
    funext w
    fin_cases w <;> simp [Config.step, twoAgentProtocol, hm]
  rw [hD]
  constructor
  · intro i j
    by_cases hij : i = j
    · subst hij
      simp [Config.step]
    rw [Config.step_eq_self_iff hij]
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | (simp [twoAgentProtocol, hm]; done)
        | (simp [twoAgentProtocol, hm]; exact pairMajority_comm _ _)
  · have hcard : ∀ x : Opinion,
        (Config.agentsWithInput (fun w => (m, (C w).2) : Config Output Opinion 2) x).card =
          (if (C 0).2 = x then 1 else 0) + (if (C 1).2 = x then 1 else 0) := by
      intro x
      unfold Config.agentsWithInput
      rw [Finset.card_filter, Fin.sum_univ_two]
      rfl
    simp only [ExactMajoritySafe, hcard, Config.allOutput, Config.outputOf, Fin.forall_fin_two,
      twoAgentProtocol]
    rcases hx0 : (C 0).2 with _ | _ <;> rcases hx1 : (C 1).2 with _ | _ <;>
      simp [hm, hx0, hx1, pairMajority]

/-- **Non-vacuity of the premises of Theorems 2 and 3.** The three-state protocol
`twoAgentProtocol` is a silent self-stabilizing exact-majority protocol on two agents. -/
theorem twoAgentProtocol_solvesSilentSSEM : SolvesSilentSSEM twoAgentProtocol 2 := by
  refine ⟨fun C₀ => ⟨fun _ => (0, 1), 1, ?_⟩, fun C₀ => ⟨fun _ => (0, 1), 1, ?_⟩⟩
  · obtain ⟨hS, hSafe⟩ := twoAgentProtocol_step_silent_correct C₀
    exact ⟨hS.isOutputStable, hSafe⟩
  · exact (twoAgentProtocol_step_silent_correct C₀).1

end Ripple.PopulationProtocol.SSEM
