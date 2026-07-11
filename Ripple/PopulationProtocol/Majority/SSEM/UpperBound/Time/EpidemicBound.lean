import Ripple.PopulationProtocol.Majority.SSEM.Convergence.BurmanConvergenceFinal
import Ripple.PopulationProtocol.Majority.SSEM.Probability.ExpectedTime

namespace SSEM

open scoped BigOperators ENNReal

/-!
Explicit one-way epidemic bound for the reset propagation layer.

This file isolates the stochastic part from the protocol-region bookkeeping:
once a reset/epidemic region is closed and every `(phi, non-phi)` interaction
strictly decreases `phiCount`, the uniform scheduler drains `phiCount` with
the coupon/epidemic rate `2*k*(n-k)/(n*(n-1))`.
-/

def EpidemicAnswerInv {n : ℕ} (m : Answer)
    (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ v : Fin n, (C v).1.answer = m ∨ (C v).1.answer = .phi

def EpidemicPhiGoal {n : ℕ} (m : Answer)
    (C : Config (AgentState n) Opinion n) : Prop :=
  phiCount C = 0 ∧ ∀ v : Fin n, (C v).1.answer = m

def phiAgents {n : ℕ} (C : Config (AgentState n) Opinion n) :
    Finset (Fin n) :=
  Finset.univ.filter fun v : Fin n => (C v).1.answer = .phi

def nonPhiAgents {n : ℕ} (C : Config (AgentState n) Opinion n) :
    Finset (Fin n) :=
  Finset.univ.filter fun v : Fin n => (C v).1.answer ≠ .phi

def phiNonPhiPairs {n : ℕ} (C : Config (AgentState n) Opinion n) :
    Finset (Fin n × Fin n) :=
  (phiAgents C).product (nonPhiAgents C) ∪
    (nonPhiAgents C).product (phiAgents C)

theorem phiAgents_card {n : ℕ}
    (C : Config (AgentState n) Opinion n) :
    (phiAgents C).card = phiCount C := by
  rfl

theorem nonPhiAgents_card {n : ℕ}
    (C : Config (AgentState n) Opinion n) :
    (nonPhiAgents C).card = n - phiCount C := by
  classical
  have h :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n)))
      (p := fun v : Fin n => (C v).1.answer = .phi)
  simpa [nonPhiAgents, phiCount, Finset.card_univ, Fintype.card_fin,
    Nat.add_comm] using (Nat.eq_sub_of_add_eq' h)

theorem phiNonPhiPairs_subset_offDiagonal {n : ℕ}
    (C : Config (AgentState n) Opinion n) :
    phiNonPhiPairs C ⊆ Probability.OffDiagonalPairs n := by
  classical
  intro p hp
  rw [phiNonPhiPairs, Finset.mem_union] at hp
  rw [Probability.mem_offDiagonalPairs]
  rcases hp with hp | hp
  · have hp' :
        p.1 ∈ phiAgents C ∧ p.2 ∈ nonPhiAgents C := by
      simpa using hp
    intro h
    have hphi : (C p.2).1.answer = .phi := by
      rw [← h]
      exact (Finset.mem_filter.mp hp'.1).2
    exact (Finset.mem_filter.mp hp'.2).2 hphi
  · have hp' :
        p.1 ∈ nonPhiAgents C ∧ p.2 ∈ phiAgents C := by
      simpa using hp
    intro h
    have hphi : (C p.1).1.answer = .phi := by
      rw [h]
      exact (Finset.mem_filter.mp hp'.2).2
    exact (Finset.mem_filter.mp hp'.1).2 hphi

theorem phiNonPhiPairs_card {n : ℕ}
    (C : Config (AgentState n) Opinion n) :
    (phiNonPhiPairs C).card =
      2 * phiCount C * (n - phiCount C) := by
  classical
  let A := (phiAgents C).product (nonPhiAgents C)
  let B := (nonPhiAgents C).product (phiAgents C)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hpA hpB
    have hpA' :
        p.1 ∈ phiAgents C ∧ p.2 ∈ nonPhiAgents C := by
      simpa [A] using hpA
    have hpB' :
        p.1 ∈ nonPhiAgents C ∧ p.2 ∈ phiAgents C := by
      simpa [B] using hpB
    have hphi : (C p.1).1.answer = .phi :=
      (Finset.mem_filter.mp hpA'.1).2
    exact (Finset.mem_filter.mp hpB'.1).2 hphi
  calc
    (phiNonPhiPairs C).card
        = (A ∪ B).card := by rfl
    _ = A.card + B.card := Finset.card_union_of_disjoint hdisj
    _ = (phiAgents C).card * (nonPhiAgents C).card +
          (nonPhiAgents C).card * (phiAgents C).card := by
          simp [A, B, Finset.card_product]
    _ = phiCount C * (n - phiCount C) +
          (n - phiCount C) * phiCount C := by
          rw [phiAgents_card, nonPhiAgents_card]
    _ = 2 * phiCount C * (n - phiCount C) := by ring

theorem epidemic_phi_pair_mass {n : ℕ} (hn : 2 ≤ n)
    (C : Config (AgentState n) Opinion n) :
    Probability.pairSetMass n hn (phiNonPhiPairs C) =
      ((2 * phiCount C * (n - phiCount C) : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
  rw [Probability.pairSetMass_eq_card_mul_inv_of_subset]
  rw [phiNonPhiPairs_card]
  exact phiNonPhiPairs_subset_offDiagonal C

theorem EpidemicPhiGoal_of_inv_phiCount_zero {n : ℕ}
    {m : Answer} {C : Config (AgentState n) Opinion n}
    (hInv : EpidemicAnswerInv m C) (hphi : phiCount C = 0) :
    EpidemicPhiGoal m C := by
  refine ⟨hphi, ?_⟩
  have hNoPhi := (phiCount_eq_zero_iff C).mp hphi
  intro v
  rcases hInv v with hm | hp
  · exact hm
  · exact False.elim (hNoPhi v hp)

/-- One-step success probability for the reset one-way epidemic.

At level `k = phiCount C`, all ordered `(phi, non-phi)` pairs are good.  Their
number is `2*k*(n-k)`, so their scheduler mass is exactly
`2*k*(n-k)/(n*(n-1))`. -/
theorem epidemic_phiCount_one_step_prob_ge
    [DecidableEq (Config (AgentState n) Opinion n)]
    (P : Protocol (AgentState n) Opinion Output) (hn : 2 ≤ n)
    {m : Answer} (C : Config (AgentState n) Opinion n)
    (Inv : Config (AgentState n) Opinion n → Prop)
    [DecidablePred Inv]
    (k : ℕ) (hk : 0 < k) (hphi : phiCount C = k)
    (hGood : ∀ p : Fin n × Fin n, p ∈ phiNonPhiPairs C →
      EpidemicPhiGoal m (C.step P p.1 p.2) ∨
        (Inv (C.step P p.1 p.2) ∧ phiCount (C.step P p.1 p.2) < k)) :
    ((2 * k * (n - k) : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹
      ≤
        Probability.ProbHitWithin P hn C
          (fun D => EpidemicPhiGoal m D ∨ (Inv D ∧ phiCount D < k)) 1 := by
  classical
  let Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => EpidemicPhiGoal m D ∨ (Inv D ∧ phiCount D < k)
  have hNotGoal : ¬ Goal C := by
    intro h
    rcases h with hG | hLower
    · have hk0 : k = 0 := by
        rw [← hphi]
        exact hG.1
      omega
    · rw [hphi] at hLower
      exact Nat.lt_irrefl k hLower.2
  have hmass :
      Probability.pairSetMass n hn (phiNonPhiPairs C) =
        ((2 * k * (n - k) : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹ := by
    rw [epidemic_phi_pair_mass hn C, hphi]
  rw [← hmass]
  exact Probability.ProbHitWithin_one_lower_bound_of_pairSet
    P hn C Goal hNotGoal (phiNonPhiPairs C)
    (phiNonPhiPairs_subset_offDiagonal C)
    (by
      intro p hp
      exact hGood p hp)

/-- Explicit variable-rate expected-time bound for the one-way reset epidemic.

The theorem is intentionally stated with the reset-region closure facts as
hypotheses.  In the concrete PEM protocol these facts are exactly the local
obligations saying that, until the reset epidemic target is reached, every
step stays in the one-way epidemic region, `phiCount` never increases, and
every `(phi, non-phi)` ordered pair strictly decreases `phiCount`.
-/
theorem epidemic_phiCount_to_zero_expected_le
    [DecidableEq (Config (AgentState n) Opinion n)]
    (P : Protocol (AgentState n) Opinion Output) (hn : 2 ≤ n)
    {m : Answer} (C : Config (AgentState n) Opinion n)
    (Inv : Config (AgentState n) Opinion n → Prop)
    [DecidablePred Inv]
    (hInv₀ : Inv C)
    (hAnsInv : ∀ D : Config (AgentState n) Opinion n,
      Inv D → EpidemicAnswerInv m D)
    (hInvStep : ∀ D : Config (AgentState n) Opinion n, Inv D →
      ¬ EpidemicPhiGoal m D →
        ∀ i j : Fin n, Inv (D.step P i j) ∨ EpidemicPhiGoal m (D.step P i j))
    (hNonincrease : ∀ D : Config (AgentState n) Opinion n, Inv D →
      ¬ EpidemicPhiGoal m D →
        ∀ i j : Fin n, phiCount (D.step P i j) ≤ phiCount D)
    (hGood : ∀ D : Config (AgentState n) Opinion n, Inv D →
      ¬ EpidemicPhiGoal m D → 0 < phiCount D →
        ∀ p : Fin n × Fin n, p ∈ phiNonPhiPairs D →
          EpidemicPhiGoal m (D.step P p.1 p.2) ∨
            (Inv (D.step P p.1 p.2) ∧
              phiCount (D.step P p.1 p.2) < phiCount D)) :
    Probability.expectedHittingTime P hn C (EpidemicPhiGoal m) ≤
      ∑ r ∈ Finset.range (phiCount C),
        ((((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal) *
            ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹) := by
  classical
  let pRate : ℕ → ENNReal :=
    fun k =>
      ((2 * k * (n - k) : ℕ) : ENNReal) *
        ((n * (n - 1) : ℕ) : ENNReal)⁻¹
  have hBound :=
    Probability.expectedHittingTime_le_of_variable_descent_until_goal
      P hn C (EpidemicPhiGoal m) Inv phiCount pRate hInv₀
      (by
        intro D hInvD hphi
        exact EpidemicPhiGoal_of_inv_phiCount_zero (hAnsInv D hInvD) hphi)
      hInvStep
      hNonincrease
      (by
        intro k hk D hInvD hphi
        exact epidemic_phiCount_one_step_prob_ge
          P hn D Inv k hk hphi
          (by
            intro p hp
            simpa [hphi] using hGood D hInvD
              (by
                intro hG
                exact Nat.ne_of_gt hk (by simpa [hphi] using hG.1))
              (by simpa [hphi] using hk) p hp))
  simpa [pRate] using hBound

end SSEM
