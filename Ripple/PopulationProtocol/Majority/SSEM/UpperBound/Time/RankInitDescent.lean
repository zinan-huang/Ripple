import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time

namespace SSEM

open scoped ENNReal

variable {n : ℕ}

/-- Rank-initialization potential: each `Resetting` agent contributes its
remaining delay plus one; non-resetting agents contribute zero. -/
noncomputable def rankInitPotential
    (C : Config (AgentState n) Opinion n) : ℕ :=
  ∑ w : Fin n,
    if (C w).1.role = .Resetting then 1 + (C w).1.delaytimer else 0

theorem rankInitPotential_zero_noResetting
    (C : Config (AgentState n) Opinion n)
    (hφ : rankInitPotential C = 0) :
    ∀ w : Fin n, (C w).1.role ≠ .Resetting := by
  classical
  intro w hw
  have hterms :
      ∀ x ∈ (Finset.univ : Finset (Fin n)),
        (if (C x).1.role = .Resetting then 1 + (C x).1.delaytimer else 0) = 0 := by
    simpa [rankInitPotential] using
      (Finset.sum_eq_zero_iff.mp hφ)
  have hwzero := hterms w (Finset.mem_univ w)
  simp [hw] at hwzero

theorem exists_resetting_of_rankInitPotential_pos
    (C : Config (AgentState n) Opinion n)
    (hpos : 0 < rankInitPotential C) :
    ∃ w : Fin n, (C w).1.role = .Resetting := by
  classical
  by_contra hnone
  push Not at hnone
  have hzero : rankInitPotential C = 0 := by
    unfold rankInitPotential
    rw [Finset.sum_eq_zero_iff]
    intro w _hw
    simp [hnone w]
  omega

theorem rankInitPotential_le_of_bounded
    {M : ℕ} (C : Config (AgentState n) Opinion n)
    (hBounded : IsBoundedConfig M C) :
    rankInitPotential C ≤ n * (1 + M) := by
  classical
  unfold rankInitPotential
  calc
    (∑ w : Fin n,
        if (C w).1.role = .Resetting then 1 + (C w).1.delaytimer else 0)
        ≤ ∑ _w : Fin n, (1 + M) := by
          apply Finset.sum_le_sum
          intro w _hw
          by_cases hw : (C w).1.role = .Resetting
          · have hdt : (C w).1.delaytimer ≤ M := (hBounded w).2.2.2.1
            simp [hw]
            omega
          · simp [hw]
    _ = n * (1 + M) := by
          simp [Finset.sum_const]

/-- A concrete one-step target witness gives the ordered-pair scheduler mass.
This is the probability wrapper used by the per-level descent hypothesis. -/
theorem rankInit_one_step_lower_bound_of_witness
    {Q X Y : Type*} {P : Protocol Q X Y} {C : Config Q X n}
    {Target : Config Q X n → Prop} [DecidablePred Target]
    (hn2 : 2 ≤ n) {i j : Fin n} (hij : i ≠ j)
    (hstep : Target (C.step P i j)) :
    (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn2 C Target 1 := by
  classical
  by_cases hTarget : Target C
  · have hzero :
        Probability.ProbHitWithin P hn2 C Target 0 = 1 :=
      Probability.probHitBy_zero_of_goal P hn2 C Target hTarget
    calc
      (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤ 1 := by
        exact ENNReal.inv_le_one.mpr (by
          have hn_one : 1 ≤ n := by omega
          have hpred_one : 1 ≤ n - 1 := by omega
          exact_mod_cast (Nat.mul_le_mul hn_one hpred_one))
      _ = Probability.ProbHitWithin P hn2 C Target 0 := hzero.symm
      _ ≤ Probability.ProbHitWithin P hn2 C Target 1 :=
        Probability.ProbHitWithin_mono_time P hn2 C Target (by omega)
  · exact Probability.ProbHitWithin_one_lower_bound_of_step
      P hn2 C Target hTarget hij hstep

/-- Conditional rank-initialization descent bound.

The stochastic and ENNReal plumbing is closed here.  The remaining obligations
are the deterministic invariant/nonincrease/progress hypotheses for the concrete
`rankInitPotential`. -/
theorem allR_to_noResetting_expected_le_of_rankInit_descent
    {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
    [DecidableEq (Config (AgentState n) Opinion n)]
    (hn4 : 4 ≤ n) (hn0 : 0 < n) (_hRmax : n ≤ Rmax) (_hDmaxN : n ≤ Dmax)
    (C : Config (AgentState n) Opinion n)
    (_hAllR : ∀ w : Fin n, (C w).1.role = .Resetting)
    (_hRc0 : ∀ w : Fin n, (C w).1.resetcount = 0)
    (hBounded : IsBoundedConfig (7 * (Rmax + 4) + Emax + Dmax) C)
    (Inv : Config (AgentState n) Opinion n → Prop) [DecidablePred Inv]
    (hInv₀ : Inv C)
    (hZeroGoal : ∀ D : Config (AgentState n) Opinion n,
      Inv D → rankInitPotential D = 0 →
        ∀ w : Fin n, (D w).1.role ≠ .Resetting)
    (hInvStep : ∀ D : Config (AgentState n) Opinion n,
      Inv D → ¬ (∀ w : Fin n, (D w).1.role ≠ .Resetting) →
        ∀ i j : Fin n,
          Inv (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) ∨
            (∀ w : Fin n,
              (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j w).1.role ≠
                .Resetting))
    (hNonincrease : ∀ D : Config (AgentState n) Opinion n,
      Inv D → ¬ (∀ w : Fin n, (D w).1.role ≠ .Resetting) →
        ∀ i j : Fin n,
          rankInitPotential
              (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j) ≤
            rankInitPotential D)
    (hp : ∀ k : ℕ, 0 < k →
      ∀ D : Config (AgentState n) Opinion n, Inv D →
        rankInitPotential D = k →
          (((n * (n - 1) : ℕ) : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax hn0)
              (by omega : 2 ≤ n) D
              (fun E =>
                (∀ w : Fin n, (E w).1.role ≠ .Resetting) ∨
                  (Inv E ∧ rankInitPotential E < k)) 1) :
    Probability.expectedHittingTime (PEMProtocolCoupled n Rmax Emax Dmax hn0)
      (by omega : 2 ≤ n) C (fun D => ∀ w, (D w).1.role ≠ .Resetting)
      ≤ ((n * (1 + (7 * (Rmax + 4) + Emax + Dmax)) *
            (n * (n - 1)) : ℕ) : ENNReal) := by
  classical
  let P := PEMProtocolCoupled n Rmax Emax Dmax hn0
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => ∀ w : Fin n, (D w).1.role ≠ .Resetting
  let pRate : ℕ → ENNReal :=
    fun _ => (((n * (n - 1) : ℕ) : ENNReal)⁻¹)
  let M := 7 * (Rmax + 4) + Emax + Dmax
  have hn2 : 2 ≤ n := by omega
  have hBound :=
    Probability.expectedHittingTime_le_of_variable_descent_until_goal
      P hn2 C Goal Inv rankInitPotential pRate hInv₀
      (by
        intro D hInvD hφ
        exact hZeroGoal D hInvD hφ)
      (by
        intro D hInvD hGoalD i j
        simpa [P, Goal] using hInvStep D hInvD hGoalD i j)
      (by
        intro D hInvD hGoalD i j
        simpa [P, Goal] using hNonincrease D hInvD hGoalD i j)
      (by
        intro k hk D hInvD hφ
        simpa [P, Goal, pRate] using hp k hk D hInvD hφ)
  have hφBound : rankInitPotential C ≤ n * (1 + M) := by
    simpa [M] using
      rankInitPotential_le_of_bounded (n := n) (M := M) C hBounded
  calc
    Probability.expectedHittingTime P hn2 C Goal
        ≤ ∑ _k ∈ Finset.range (rankInitPotential C),
            (pRate (_k + 1))⁻¹ := hBound
    _ = ∑ _k ∈ Finset.range (rankInitPotential C),
            ((n * (n - 1) : ℕ) : ENNReal) := by
          apply Finset.sum_congr rfl
          intro k _hk
          simp [pRate, inv_inv]
    _ = ((rankInitPotential C : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal) := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ((n * (1 + M) : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal) := by
          exact mul_le_mul_left (by exact_mod_cast hφBound) _
    _ = ((n * (1 + M) * (n * (n - 1)) : ℕ) : ENNReal) := by
          rw [← Nat.cast_mul]
    _ = ((n * (1 + (7 * (Rmax + 4) + Emax + Dmax)) *
            (n * (n - 1)) : ℕ) : ENNReal) := by
          simp [M]

end SSEM
