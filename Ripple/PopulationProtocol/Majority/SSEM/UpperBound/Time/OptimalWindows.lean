import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.DecisionTiming
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.DrainProductive
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.EpidemicBound
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.EpidemicMechanics
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.PolynomialBound

/-!
# Optimal parallel-time bound — reduced to two expected-time keystones

The team's assembly `PEM_expected_parallel_time_from_global_expected_phase_bounds`
(Time.lean) already chains the ranking window, the proven swap window
(`PEM_swap_ProbHitWithin_InSswap_timer_live_const35_bounded`), and the consensus
window via `ProbHitWithin_add_ge_mul` + window-amplification. It is conditional on
exactly two universal expected-hitting-time bounds. Discharging them here yields the
**unconditional** optimal parallel-time theorem.

Remaining work = these two keystones:
* `OW_rankBound` — from any timer-bounded config, expected time to reach the ranking
  endpoint (`InSrank ∧ median timer ≥ 35 ∧ timer-bounded`) is `≤ C_rank·n²`.
  (Universal ranking time; needs reset-normalization from arbitrary configs +
  `PEM_FreshRankingStart_expected_until_srank_timer2_or_consensus_or_heap_exit_le`.)
* `OW_consensusBound` — from `InSswap` with a fresh (`≥ 35`), bounded median
  timer, expected time to consensus is bounded by one renewal window times the
  inverse of the cited reset-success probability, using only the cited [12]
  reset-completion, rank, and re-rank windows.
-/

namespace SSEM

open scoped BigOperators ENNReal

attribute [local instance] Classical.propDecidable

section
variable {n Rmax Emax Dmax : ℕ} [Inhabited (Fin n × Fin n)]
  [DecidableEq (Config (AgentState n) Opinion n)]

/-- The silence endpoint used by the renewal: a ranked swap configuration
with no remaining `phi` answers in the reservoir. -/
def OW_silenceEndpoint {n : ℕ} (C : Config (AgentState n) Opinion n) : Prop :=
  InSswap C ∧ ResAns (majorityAnswer C) C ∧ phiCount C = 0

/-- The branch on which the cited [12] return/ranking hypothesis is invoked. -/
def OW_restartBranch {n : ℕ} (C : Config (AgentState n) Opinion n) : Prop :=
  CorrectResetSeed C ∨ ¬ (InSswap C ∧ MedianTimerAtLeast 1 C)

/-- Proven swap-window length used in the consensus renewal. -/
def OW_swapWindow (n T_timer : ℕ) : ℕ :=
  2 * (n * (n - 1)) + 2 * (T_timer * n * (n - 1))

/-- Markov window for the productive MAC-live drain. -/
def OW_macLiveWindow (n T_timer : ℕ) : ℕ :=
  2 * (T_timer * n * (n - 1) + n * (n - 1))

/-- Markov window for the answer epidemic after the reset-completion target.
The underlying expected-time bound is `n^2` sequential interactions. -/
def OW_answerEpidemicWindow (n : ℕ) : ℕ :=
  2 * n * n

/-- Productive live-swap window: isolate a median decision, then drain/reset
from the MAC-live branch. -/
def OW_liveConsensusWindow (n T_timer T_reset T_rank : ℕ) : ℕ :=
  decisionWindow n + OW_macLiveWindow n T_timer +
    (T_reset + OW_answerEpidemicWindow n + T_rank)

/-- One renewal-cycle window for the consensus proof. -/
def OW_consensusCycleWindow (n T_timer T_reset T_rank T_rerank : ℕ) : ℕ :=
  T_rerank + OW_liveConsensusWindow n T_timer T_reset T_rank

/-- End-to-end finite window for the direct rank -> live -> consensus
`ProbHitWithin` chain used by the parallel-time keystone. -/
def OW_globalWindow (n C_rank T_timer T_reset T_rank T_rerank : ℕ) : ℕ :=
  (2 * C_rank * n * n + T_rerank) +
    OW_liveConsensusWindow n T_timer T_reset T_rank

/-- The endpoint supplied by the [12] ranking window after the reset epidemic has
already made the answer uniform: ranking has reached `InSswap`, the uniform
answer is still `m`, and the global majority answer agrees with `m`. -/
def OW_rankedEpidemicEndpoint {n : ℕ} (m : Answer)
    (C : Config (AgentState n) Opinion n) : Prop :=
  InSswap C ∧ EpidemicPhiGoal m C ∧ majorityAnswer C = m

omit [Inhabited (Fin n × Fin n)] [DecidableEq (Config (AgentState n) Opinion n)] in
/-- The proven silence link for a ranked uniform endpoint.  This is the Kanaya
part: no [12] timing statement is used here. -/
theorem OW_silenceEndpoint_of_rankedEpidemicEndpoint
    {m : Answer} {C : Config (AgentState n) Opinion n}
    (hC : OW_rankedEpidemicEndpoint m C) :
    OW_silenceEndpoint C := by
  rcases hC with ⟨hSswap, hEpi, hMaj⟩
  refine ⟨hSswap, ?_, hEpi.1⟩
  intro w
  exact Or.inl (by
    rw [hMaj]
    exact hEpi.2 w)

omit [Inhabited (Fin n × Fin n)] in
/-- Markov-window form of the proven abstract epidemic descent theorem. -/
theorem epidemic_phiCount_to_zero_window_ge_half
    (P : Protocol (AgentState n) Opinion Output) (hn : 2 ≤ n)
    {m : Answer} (C : Config (AgentState n) Opinion n)
    (Inv : Config (AgentState n) Opinion n → Prop)
    [DecidablePred Inv]
    (M T : ℕ)
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
              phiCount (D.step P p.1 p.2) < phiCount D))
    (hSumLe :
      (∑ r ∈ Finset.range (phiCount C),
        ((((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal) *
            ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹)) ≤
        ((M : ℕ) : ENNReal))
    (hWindow : 2 * M ≤ T + 1) :
    ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin P hn C (EpidemicPhiGoal m) T := by
  have hExp :=
    epidemic_phiCount_to_zero_expected_le
      P hn (m := m) C Inv hInv₀ hAnsInv hInvStep hNonincrease hGood
  exact Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
    P hn C (EpidemicPhiGoal m) (hExp.trans hSumLe) hWindow

omit [Inhabited (Fin n × Fin n)] [DecidableEq (Config (AgentState n) Opinion n)] in
/-- In an epidemic region at least one agent carries the non-`phi` answer, so
the number of `phi` agents is strictly below `n`. -/
theorem epidemicRegion_phiCount_lt {m : Answer}
    {C : Config (AgentState n) Opinion n}
    (hReg : EpidemicRegion m C) :
    phiCount C < n := by
  classical
  rcases hReg.2.2.2 with ⟨w, hw⟩
  have hsub : phiAgents C ⊆ (Finset.univ : Finset (Fin n)) := by
    intro v hv
    simp
  have hproper : phiAgents C ⊂ (Finset.univ : Finset (Fin n)) := by
    rw [Finset.ssubset_iff_of_subset hsub]
    refine ⟨w, by simp, ?_⟩
    intro hwmem
    have hphi : (C w).1.answer = .phi := (Finset.mem_filter.mp hwmem).2
    exact hReg.2.2.1 (hw.symm.trans hphi)
  have hcard := Finset.card_lt_card hproper
  simpa [phiAgents_card, Fintype.card_fin] using hcard

omit [Inhabited (Fin n × Fin n)] [DecidableEq (Config (AgentState n) Opinion n)] in
/-- Coarse coupon bound for the one-way reset epidemic.  Each non-terminal
level has rate at least `1 / (n*(n-1))`, and there are at most `n` levels. -/
theorem epidemic_coupon_sum_le_quadratic {m : Answer}
    {C : Config (AgentState n) Opinion n}
    (hReg : EpidemicRegion m C) :
    (∑ r ∈ Finset.range (phiCount C),
      ((((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹)) ≤
      ((n * n * (n - 1) : ℕ) : ENNReal) := by
  classical
  have hPhi_lt : phiCount C < n := epidemicRegion_phiCount_lt hReg
  have hTerm :
      ∀ r ∈ Finset.range (phiCount C),
        ((((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal) *
            ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹) ≤
          ((n * (n - 1) : ℕ) : ENNReal) := by
    intro r hr
    have hr_lt : r < phiCount C := Finset.mem_range.mp hr
    have hrn : r + 1 < n := by omega
    have hleft : 0 < 2 * (r + 1) := by positivity
    have hright : 0 < n - (r + 1) := Nat.sub_pos_of_lt hrn
    have hApos : 0 < 2 * (r + 1) * (n - (r + 1)) :=
      Nat.mul_pos hleft hright
    have hAge1 : 1 ≤ 2 * (r + 1) * (n - (r + 1)) :=
      Nat.succ_le_of_lt hApos
    have hA_ne_zero :
        (((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal)) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hApos
    have hA_ne_top :
        (((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal)) ≠ ⊤ :=
      ENNReal.natCast_ne_top _
    rw [ENNReal.mul_inv (Or.inl hA_ne_zero) (Or.inl hA_ne_top), inv_inv]
    have hInv_le : (((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal))⁻¹ ≤ 1 := by
      apply ENNReal.inv_le_one.mpr
      exact_mod_cast hAge1
    calc
      (((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal))⁻¹ *
          ((n * (n - 1) : ℕ) : ENNReal)
          ≤ 1 * ((n * (n - 1) : ℕ) : ENNReal) :=
            by
              simpa [mul_comm] using
                (mul_le_mul_right hInv_le
                  (((n * (n - 1) : ℕ) : ENNReal)))
      _ = ((n * (n - 1) : ℕ) : ENNReal) := one_mul _
  calc
    (∑ r ∈ Finset.range (phiCount C),
      ((((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹))
        ≤ ∑ _r ∈ Finset.range (phiCount C),
            ((n * (n - 1) : ℕ) : ENNReal) :=
          Finset.sum_le_sum hTerm
    _ = (phiCount C : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (n : ENNReal) * ((n * (n - 1) : ℕ) : ENNReal) := by
          have hPhi_le : (phiCount C : ENNReal) ≤ (n : ENNReal) := by
            exact_mod_cast le_of_lt hPhi_lt
          simpa [mul_comm] using
            (mul_le_mul_right hPhi_le (((n * (n - 1) : ℕ) : ENNReal)))
    _ = ((n * n * (n - 1) : ℕ) : ENNReal) := by
          push_cast
          ring

omit [Inhabited (Fin n × Fin n)] [DecidableEq (Config (AgentState n) Opinion n)] in
/-- Faithful quadratic coupon bound for the answer epidemic after reset
completion.  At level `k` with `0 < k < n`, the ordered `(phi, non-phi)`
mass has denominator at most `n`, so each level costs at most `n` sequential
interactions and there are fewer than `n` levels. -/
theorem epidemic_coupon_sum_le_nsq {m : Answer}
    {C : Config (AgentState n) Opinion n}
    (hReg : EpidemicRegion m C) :
    (∑ r ∈ Finset.range (phiCount C),
      ((((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹)) ≤
      ((n * n : ℕ) : ENNReal) := by
  classical
  have hPhi_lt : phiCount C < n := epidemicRegion_phiCount_lt hReg
  have hTerm :
      ∀ r ∈ Finset.range (phiCount C),
        ((((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal) *
            ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹) ≤
          (n : ENNReal) := by
    intro r hr
    have hr_lt : r < phiCount C := Finset.mem_range.mp hr
    have hrn : r + 1 < n := by omega
    have hleft : 0 < 2 * (r + 1) := by positivity
    have hright : 0 < n - (r + 1) := Nat.sub_pos_of_lt hrn
    have hApos : 0 < 2 * (r + 1) * (n - (r + 1)) :=
      Nat.mul_pos hleft hright
    have hA_ne_zero :
        (((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal)) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hApos
    have hA_ne_top :
        (((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal)) ≠ ⊤ :=
      ENNReal.natCast_ne_top _
    rw [ENNReal.mul_inv (Or.inl hA_ne_zero) (Or.inl hA_ne_top), inv_inv]
    have hden_ge_nat : n - 1 ≤ 2 * (r + 1) * (n - (r + 1)) := by
      have hsub_cast :
          ((n - (r + 1) : ℕ) : ℤ) = (n : ℤ) - ((r + 1 : ℕ) : ℤ) := by
        omega
      have hn1_cast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
        omega
      have hnonneg_left : 0 ≤ ((r + 1 : ℕ) : ℤ) - 1 := by
        omega
      have hnonneg_right : 0 ≤ (n : ℤ) - ((r + 1 : ℕ) : ℤ) - 1 := by
        omega
      have hprod_nonneg :
          0 ≤ (((r + 1 : ℕ) : ℤ) - 1) *
            ((n : ℤ) - ((r + 1 : ℕ) : ℤ) - 1) :=
        mul_nonneg hnonneg_left hnonneg_right
      have hidentity :
          ((r + 1 : ℕ) : ℤ) * ((n : ℤ) - ((r + 1 : ℕ) : ℤ)) -
              ((n : ℤ) - 1) =
            (((r + 1 : ℕ) : ℤ) - 1) *
              ((n : ℤ) - ((r + 1 : ℕ) : ℤ) - 1) := by
        ring
      have hprod_ge :
          (n : ℤ) - 1 ≤
            ((r + 1 : ℕ) : ℤ) * ((n : ℤ) - ((r + 1 : ℕ) : ℤ)) := by
        nlinarith
      have hprod_nat :
          ((n - 1 : ℕ) : ℤ) ≤
            (((r + 1) * (n - (r + 1)) : ℕ) : ℤ) := by
        rw [Nat.cast_mul, hsub_cast, hn1_cast]
        exact hprod_ge
      have hprod_nat' : n - 1 ≤ (r + 1) * (n - (r + 1)) := by
        exact_mod_cast hprod_nat
      have hdouble :
          (r + 1) * (n - (r + 1)) ≤
            2 * ((r + 1) * (n - (r + 1))) :=
        Nat.le_mul_of_pos_left _ (by norm_num : 0 < 2)
      have hdouble_eq :
          2 * ((r + 1) * (n - (r + 1))) =
            2 * (r + 1) * (n - (r + 1)) := by ring
      exact hprod_nat'.trans (by simpa [hdouble_eq] using hdouble)
    have hden_ge :
        (((n - 1 : ℕ) : ENNReal)) ≤
          ((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal) := by
      exact_mod_cast hden_ge_nat
    have hInv_le :
        (((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal))⁻¹ ≤
          (((n - 1 : ℕ) : ENNReal))⁻¹ :=
      ENNReal.inv_le_inv.mpr hden_ge
    have hn1_ne_zero : (((n - 1 : ℕ) : ENNReal)) ≠ 0 := by
      exact_mod_cast (by omega : n - 1 ≠ 0)
    have hn1_ne_top : (((n - 1 : ℕ) : ENNReal)) ≠ ⊤ :=
      ENNReal.natCast_ne_top _
    calc
      (((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal))⁻¹ *
          ((n * (n - 1) : ℕ) : ENNReal)
          ≤ (((n - 1 : ℕ) : ENNReal))⁻¹ *
              ((n * (n - 1) : ℕ) : ENNReal) := by
            simpa [mul_comm] using
              (mul_le_mul_right hInv_le (((n * (n - 1) : ℕ) : ENNReal)))
      _ = (n : ENNReal) := by
            have hprod_cast :
                ((n * (n - 1) : ℕ) : ENNReal) =
                  (n : ENNReal) * (((n - 1 : ℕ) : ENNReal)) := by
              norm_num [Nat.cast_mul]
            rw [hprod_cast]
            rw [mul_comm ((n : ENNReal)) (((n - 1 : ℕ) : ENNReal))]
            rw [ENNReal.inv_mul_cancel_left hn1_ne_zero hn1_ne_top]
  calc
    (∑ r ∈ Finset.range (phiCount C),
      ((((2 * (r + 1) * (n - (r + 1)) : ℕ) : ENNReal) *
          ((n * (n - 1) : ℕ) : ENNReal)⁻¹)⁻¹))
        ≤ ∑ _r ∈ Finset.range (phiCount C), (n : ENNReal) :=
          Finset.sum_le_sum hTerm
    _ = (phiCount C : ENNReal) * (n : ENNReal) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (n : ENNReal) * (n : ENNReal) := by
          have hPhi_le : (phiCount C : ENNReal) ≤ (n : ENNReal) := by
            exact_mod_cast le_of_lt hPhi_lt
          simpa [mul_comm] using (mul_le_mul_right hPhi_le (n : ENNReal))
    _ = ((n * n : ℕ) : ENNReal) := by
          push_cast
          ring

omit [Inhabited (Fin n × Fin n)] [DecidableEq (Config (AgentState n) Opinion n)] in
/-- Bare all-`Resetting` epidemic-region helper retained for local mechanics.
The reset-completion contracts cite the completed epidemic target directly. -/
def ResetCompletionTarget12 {n : ℕ} (m : Answer)
    (C : Config (AgentState n) Opinion n) : Prop :=
  EpidemicRegion m C

omit [Inhabited (Fin n × Fin n)] [DecidableEq (Config (AgentState n) Opinion n)] in
/-- The attack-2 "not about to wake" predicate
`¬ (resetcount = 0 ∧ delaytimer = 0)` is not a one-step no-wake condition.
With `resetcount = 0`, `delaytimer = 1`, `oldRc = 0`, and a Resetting
partner, `processAgent` first decrements the delay timer to `0` and then
fires `resetOSSR`. -/
theorem processAgent_not_about_to_wake_counterexample
    {Emax Dmax : ℕ} {hn : 0 < n} :
    ∃ s : AgentState n,
      s.role = .Resetting ∧
      s.resetcount = 0 ∧
      s.delaytimer = 1 ∧
      ¬ (s.resetcount = 0 ∧ s.delaytimer = 0) ∧
      (processAgent Emax Dmax hn s 0 true).role ≠ .Resetting := by
  let s : AgentState n :=
    { role := .Resetting
      rank := ⟨0, hn⟩
      leader := .L
      resetcount := 0
      answer := .phi
      timer := 0
      children := 0
      errorcount := 0
      delaytimer := 1 }
  refine ⟨s, rfl, rfl, rfl, ?_, ?_⟩
  · rintro ⟨_, hdt⟩
    norm_num [s] at hdt
  · simp [s, processAgent, resetOSSR]

omit [Inhabited (Fin n × Fin n)] [DecidableEq (Config (AgentState n) Opinion n)] in
/-- Exact one-step no-wake condition for a `Resetting` endpoint with a
Resetting partner: either the endpoint has positive resetcount and therefore
does not enter `processAgent`'s dormant branch, or it has enough delay budget
to survive the decrement-then-test path. -/
def NoWakeAgent {n : ℕ} (s : AgentState n) : Prop :=
  0 < s.resetcount ∨ 1 < s.delaytimer

omit [Inhabited (Fin n × Fin n)] [DecidableEq (Config (AgentState n) Opinion n)] in
/-- The exact one-step `processAgent` no-wake fact for a Resetting partner. -/
theorem processAgent_noWake_role {Emax Dmax : ℕ} {hn : 0 < n}
    {s : AgentState n} {oldRc : ℕ}
    (hs : s.role = .Resetting)
    (hNoWake : NoWakeAgent s)
    (hDmax : 0 < Dmax) :
    (processAgent Emax Dmax hn s oldRc true).role = .Resetting := by
  rcases hNoWake with hrc_pos | hdt
  · have hpa :=
      processAgent_rc_ne_zero (Emax := Emax) (Dmax := Dmax) (hn := hn)
        (s := s) (Nat.ne_of_gt hrc_pos) oldRc true
    rw [hpa, hs]
  · by_cases hrc : s.resetcount = 0
    · unfold processAgent
      simp only [hs, hrc, and_self, ite_true, Bool.not_true,
        Bool.false_eq_true, or_false]
      by_cases hold : 0 < oldRc
      · simp [hold, hDmax.ne']
      · have hdt_ne : s.delaytimer - 1 ≠ 0 := by omega
        simp [hold, hdt_ne]
    · have hpa :=
        processAgent_rc_ne_zero (Emax := Emax) (Dmax := Dmax) (hn := hn)
          (s := s) hrc oldRc true
      rw [hpa, hs]

omit [Inhabited (Fin n × Fin n)] [DecidableEq (Config (AgentState n) Opinion n)] in
/-- `NoWakeAgent` is not an invariant, even though it is the correct one-step
no-wake condition.  A dormant endpoint with `resetcount = 0` and
`delaytimer = 2` stays `Resetting` for this interaction, but the timer drops to
`1`, so the post-state no longer satisfies `NoWakeAgent`. -/
theorem processAgent_noWake_not_preserved_counterexample
    {Emax Dmax : ℕ} {hn : 0 < n} :
    ∃ s : AgentState n,
      s.role = .Resetting ∧
      NoWakeAgent s ∧
      (processAgent Emax Dmax hn s 0 true).role = .Resetting ∧
      ¬ NoWakeAgent (processAgent Emax Dmax hn s 0 true) := by
  let s : AgentState n :=
    { role := .Resetting
      rank := ⟨0, hn⟩
      leader := .L
      resetcount := 0
      answer := .phi
      timer := 0
      children := 0
      errorcount := 0
      delaytimer := 2 }
  refine ⟨s, rfl, Or.inr (by norm_num [s]), ?_, ?_⟩
  · simp [s, processAgent]
  · simp [NoWakeAgent, s, processAgent]

omit [Inhabited (Fin n × Fin n)] [DecidableEq (Config (AgentState n) Opinion n)] in
/-- A bare `EpidemicRegion` target is not a sufficient starting condition for
the local answer-epidemic bridge.  It permits all-`Resetting` states whose
reset counters and delay timers are already drained; such a state can wake on
the very next interaction, so the joint target
`EpidemicPhiGoal ∧ still all Resetting` is not even one-step closed from the
cited target alone. -/
theorem bare_epidemicRegion_can_wake_counterexample :
    ∃ C : Config (AgentState 2) Opinion 2,
      EpidemicRegion .outA C ∧
      ¬ (∀ w : Fin 2,
        ((C.step (PEMProtocolCoupled 2 2 2 2 (by norm_num : 0 < 2))
          (0 : Fin 2) (1 : Fin 2)) w).1.role = .Resetting) := by
  let sA : AgentState 2 :=
    { role := .Resetting
      rank := (0 : Fin 2)
      leader := .L
      resetcount := 0
      answer := .outA
      timer := 0
      children := 0
      errorcount := 0
      delaytimer := 0 }
  let sPhi : AgentState 2 :=
    { role := .Resetting
      rank := (1 : Fin 2)
      leader := .F
      resetcount := 0
      answer := .phi
      timer := 0
      children := 0
      errorcount := 0
      delaytimer := 0 }
  let C : Config (AgentState 2) Opinion 2 :=
    fun v => if v = (0 : Fin 2) then (sA, .A) else (sPhi, .B)
  refine ⟨C, ?_, ?_⟩
  · refine ⟨?_, ?_, by decide, ?_⟩
    · intro w
      fin_cases w <;> simp [C, sA, sPhi]
    · intro w
      fin_cases w <;> simp [C, sA, sPhi]
    · exact ⟨(0 : Fin 2), by simp [C, sA]⟩
  · intro hAll
    have h0 := hAll (0 : Fin 2)
    have hStep0 :
        ((C.step (PEMProtocolCoupled 2 2 2 2 (by norm_num : 0 < 2))
          (0 : Fin 2) (1 : Fin 2)) (0 : Fin 2)).1.role = .Settled := by
      simp [Config.step, C, sA, sPhi, PEMProtocolCoupled, PEMProtocol,
        protocolPEM, transitionPEM, transitionPEM_prePhase4,
        transitionPEM_phase4, rankDeltaOSSR, propagateReset, processAgent,
        resetOSSR, ceilHalf]
    rw [hStep0] at h0
    exact Role.noConfusion h0

omit [Inhabited (Fin n × Fin n)] [DecidableEq (Config (AgentState n) Opinion n)] in
/-- Faithful [12]-cited reset-completion contract.

The reset fact is probabilistic: from a `CorrectResetSeed` configuration, the
random scheduler reaches the completed answer epidemic within
`K_reset = O(n^2)` sequential interactions with constant probability
`p_reset`.  This is the shape to cite from [12] Lemma 3.2 / Corollary 3.5.
The reset-counter dormancy race is internal to this cited window rather than
an exposed deterministic invariant over all `EpidemicRegion` configurations. -/
structure CRSResetCompletion12 {n Rmax Emax Dmax : ℕ} (hn : 0 < n)
    (p_reset : ENNReal) (C_reset K_reset : ℕ) : Prop where
  resetProb_pos : 0 < p_reset
  resetProb_le_one : p_reset ≤ 1
  resetConstant_pos : 0 < C_reset
  resetWindow_quadratic : K_reset ≤ C_reset * n * n
  resetReach :
    ∀ (hn2 : 2 ≤ n) (C : Config (AgentState n) Opinion n),
      IsTimerBoundedConfig (7 * (Rmax + 4)) C →
      CorrectResetSeed C →
        p_reset ≤
          Probability.ProbHitWithin
            (PEMProtocolCoupled n Rmax Emax Dmax hn) hn2 C
            (EpidemicPhiGoal (majorityAnswer C)) K_reset

omit [Inhabited (Fin n × Fin n)] in
/-- Faithful CRS-to-silence wrapper retaining the actual product probability.
With a `1/2` rank window this gives a `p_reset/4`
CRS-to-silence window. -/
theorem CRS_to_silence_faithful_product (hn4 : 4 ≤ n)
    (K_reset T_rank : ℕ)
    (p_reset rankProb : ENNReal) (C_reset : ℕ)
    (h12resetCompletion :
      CRSResetCompletion12 (n := n) (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) (by omega : 0 < n) p_reset C_reset K_reset)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
          rankProb ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank) :
    ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C →
      CorrectResetSeed C →
        p_reset * ((2 : ENNReal)⁻¹) * rankProb ≤
          Probability.ProbHitWithin
            (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C OW_silenceEndpoint
            (K_reset + OW_answerEpidemicWindow n + T_rank) := by
  classical
  intro C hTimer hSeed
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0 with hP
  have hReset :
      p_reset ≤
        Probability.ProbHitWithin P hn2 C
          (EpidemicPhiGoal (majorityAnswer C)) K_reset := by
    simpa [P] using h12resetCompletion.resetReach hn2 C hTimer hSeed
  have hRankToSilence :
      ∀ D : Config (AgentState n) Opinion n,
        EpidemicPhiGoal (majorityAnswer C) D →
          rankProb ≤
            Probability.ProbHitWithin P hn2 D OW_silenceEndpoint T_rank := by
    intro D hD
    have hRankRaw :
        rankProb ≤
          Probability.ProbHitWithin P hn2 D
            (OW_rankedEpidemicEndpoint (majorityAnswer C)) T_rank := by
      simpa [P] using h12rank (majorityAnswer C) D hD
    exact hRankRaw.trans
      (Probability.ProbHitWithin_mono_goal P hn2 D
        (OW_rankedEpidemicEndpoint (majorityAnswer C)) OW_silenceEndpoint
        (fun E hE => OW_silenceEndpoint_of_rankedEpidemicEndpoint hE)
        T_rank)
  have hStrong :
      p_reset * rankProb ≤
        Probability.ProbHitWithin P hn2 C OW_silenceEndpoint
          (K_reset + T_rank) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C
      (EpidemicPhiGoal (majorityAnswer C)) OW_silenceEndpoint
      K_reset T_rank p_reset rankProb hReset hRankToSilence
  have hWeak :
      p_reset * ((2 : ENNReal)⁻¹) * rankProb ≤ p_reset * rankProb := by
    have hmul :
        p_reset * ((2 : ENNReal)⁻¹) ≤ p_reset * (1 : ENNReal) := by
      exact mul_le_mul' le_rfl (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1)
    have hmulRank :
        p_reset * ((2 : ENNReal)⁻¹) * rankProb ≤
          p_reset * (1 : ENNReal) * rankProb := by
      exact mul_le_mul' hmul le_rfl
    simpa [mul_assoc] using hmulRank
  have hTime :
      Probability.ProbHitWithin P hn2 C OW_silenceEndpoint (K_reset + T_rank) ≤
        Probability.ProbHitWithin P hn2 C OW_silenceEndpoint
          (K_reset + OW_answerEpidemicWindow n + T_rank) :=
    Probability.ProbHitWithin_mono_time P hn2 C OW_silenceEndpoint (by omega)
  exact hWeak.trans (hStrong.trans hTime)

omit [Inhabited (Fin n × Fin n)] in
/-- Faithful CRS-to-silence wrapper with a caller-chosen lower-bound target. -/
theorem CRS_to_silence_faithful (hn4 : 4 ≤ n)
    (K_reset T_rank : ℕ)
    (hitProb p_reset rankProb : ENNReal) (C_reset : ℕ)
    (hProduct : hitProb ≤ p_reset * ((2 : ENNReal)⁻¹) * rankProb)
    (h12resetCompletion :
      CRSResetCompletion12 (n := n) (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) (by omega : 0 < n) p_reset C_reset K_reset)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
          rankProb ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank) :
    ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C →
      CorrectResetSeed C →
        hitProb ≤
          Probability.ProbHitWithin
            (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C OW_silenceEndpoint
            (K_reset + OW_answerEpidemicWindow n + T_rank) := by
  intro C hTimer hSeed
  exact hProduct.trans
    (CRS_to_silence_faithful_product
      (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 K_reset T_rank p_reset rankProb C_reset
      h12resetCompletion h12rank C hTimer hSeed)

omit [Inhabited (Fin n × Fin n)] in
/-- CRS branch converted to consensus, retaining the actual product
probability from reset-epidemic and ranking. -/
theorem CRS_to_consensus_faithful_product (hn4 : 4 ≤ n)
    (K_reset T_rank : ℕ)
    (p_reset rankProb : ENNReal) (C_reset : ℕ)
    (h12resetCompletion :
      CRSResetCompletion12 (n := n) (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) (by omega : 0 < n) p_reset C_reset K_reset)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
          rankProb ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank) :
    ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C →
      CorrectResetSeed C →
        p_reset * ((2 : ENNReal)⁻¹) * rankProb ≤
          Probability.ProbHitWithin
            (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C IsConsensusConfig
            (K_reset + OW_answerEpidemicWindow n + T_rank) := by
  classical
  intro C hTimer hSeed
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0 with hP
  have hSilence :
      p_reset * ((2 : ENNReal)⁻¹) * rankProb ≤
        Probability.ProbHitWithin P hn2 C OW_silenceEndpoint
          (K_reset + OW_answerEpidemicWindow n + T_rank) := by
    simpa [P] using
      (CRS_to_silence_faithful_product
        (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 K_reset T_rank p_reset rankProb C_reset h12resetCompletion h12rank
        C hTimer hSeed)
  exact hSilence.trans
    (Probability.ProbHitWithin_mono_goal P hn2 C
      OW_silenceEndpoint IsConsensusConfig
      (fun D hD => isConsensusConfig_of_InSswap_phiCount_zero hD.1 hD.2.1 hD.2.2)
      (K_reset + OW_answerEpidemicWindow n + T_rank))

omit [Inhabited (Fin n × Fin n)] in
/-- CRS branch converted all the way to consensus.  This is the productive
half of the old `hRank12` restart branch, discharged via the faithful
reset+rank wrapper and the proved silence-to-consensus link. -/
theorem CRS_to_consensus_faithful (hn4 : 4 ≤ n)
    (K_reset T_rank : ℕ)
    (hitProb p_reset rankProb : ENNReal) (C_reset : ℕ)
    (hProduct : hitProb ≤ p_reset * ((2 : ENNReal)⁻¹) * rankProb)
    (h12resetCompletion :
      CRSResetCompletion12 (n := n) (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) (by omega : 0 < n) p_reset C_reset K_reset)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
          rankProb ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank) :
    ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C →
      CorrectResetSeed C →
        hitProb ≤
          Probability.ProbHitWithin
            (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C IsConsensusConfig
            (K_reset + OW_answerEpidemicWindow n + T_rank) := by
  classical
  intro C hTimer hSeed
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0 with hP
  have hSilence :
      hitProb ≤
        Probability.ProbHitWithin P hn2 C OW_silenceEndpoint
          (K_reset + OW_answerEpidemicWindow n + T_rank) := by
    simpa [P] using
      (CRS_to_silence_faithful
        (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 K_reset T_rank hitProb p_reset rankProb C_reset hProduct
        h12resetCompletion h12rank
        C hTimer hSeed)
  exact hSilence.trans
    (Probability.ProbHitWithin_mono_goal P hn2 C
      OW_silenceEndpoint IsConsensusConfig
      (fun D hD => isConsensusConfig_of_InSswap_phiCount_zero hD.1 hD.2.1 hD.2.2)
      (K_reset + OW_answerEpidemicWindow n + T_rank))

omit [Inhabited (Fin n × Fin n)] [DecidableEq (Config (AgentState n) Opinion n)] in
/-- **Keystone 1 (universal ranking time).** From any timer-bounded configuration,
the expected time to reach a ranked configuration with a fresh (`≥ 35`) bounded
median timer is at most `C_rank·n²`, matching the cited [12] ranking theorem
rather than the reset parameter. -/
theorem OW_rankBound (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C_rank T_timer : ℕ)
    (h12ranking :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
          IsTimerBoundedConfig T_timer C →
          Probability.expectedHittingTime
            (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C
            (fun D => InSrank D ∧ MedianTimerAtLeast 35 D ∧
              IsTimerBoundedConfig (7 * (Rmax + 4)) D ∧
              IsTimerBoundedConfig T_timer D) ≤
            ((C_rank * n * n : ℕ) : ENNReal)) :
    ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C →
      IsTimerBoundedConfig T_timer C →
        Probability.expectedHittingTime
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C
          (fun D => InSrank D ∧ MedianTimerAtLeast 35 D ∧
            IsTimerBoundedConfig (7 * (Rmax + 4)) D ∧
            IsTimerBoundedConfig T_timer D) ≤
          ((C_rank * n * n : ℕ) : ENNReal) := by
  have _hRmax : n ≤ Rmax := hRmax
  have _hEmax : n ≤ Emax := hEmax
  have _hDmax : n ≤ Dmax := hDmax
  exact h12ranking

/-- Decision-phase window (Markov form of `PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le`):
from `InSswap` with a live median timer and a wrong median answer, within `2·n(n-1)` steps
the median answer becomes correct (or the swap/timer region is left) with probability ≥ 1/2. -/
theorem decision_window (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (C : Config (AgentState n) Opinion n) (hC : InSswap C)
    (hT : MedianTimerAtLeast 1 C) (hND : ¬ MedianAnswerCorrect C) :
    ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => (InSswap D ∧ MedianAnswerCorrect D) ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (2 * (n * (n - 1))) := by
  have hM := PEM_expected_Tswap_to_MedianAnswerCorrect_or_exit_le
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (by omega : 2 ≤ n) hn0 hn4 hC hT hND
  rw [inv_inv] at hM
  exact Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C _ hM (by omega)


/-- Timer-drain/propagate window (Markov form of `PEM_expected_timer_drain_poly`):
from `InSswap`+`MAC`+bounded live timer, within `2·T_timer·n(n-1)` steps reach
consensus, or form a correct reset seed, or leave the live-swap region, with prob ≥ 1/2. -/
theorem timer_drain_window (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (T_timer : ℕ)
    (C : Config (AgentState n) Opinion n) (hC : InSswap C)
    (hMAC : MedianAnswerCorrect C) (hTLo : MedianTimerAtLeast 1 C)
    (hTHi : IsTimerBoundedConfig T_timer C) :
    ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (2 * (T_timer * n * (n - 1))) :=
  Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C _
    (PEM_expected_timer_drain_poly (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax T_timer C hC hMAC hTLo hTHi)
    (by omega)

/-- Markov-window form of the productive MAC-live drain: from `InSswap` with
correct median answer and a live bounded timer, reach consensus or a correct
reset seed with probability at least `1/2`. -/
theorem MAClive_to_consensus_or_crs_window (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (T_timer : ℕ)
    (C : Config (AgentState n) Opinion n)
    (hC : InSswap C) (hMAC : MedianAnswerCorrect C)
    (hTLo : MedianTimerAtLeast 1 C)
    (hTHi : IsTimerBoundedConfig T_timer C) :
    ((2 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => IsConsensusConfig D ∨ CorrectResetSeed D)
        (OW_macLiveWindow n T_timer) := by
  have hM :=
    MAClive_to_consensus_or_crs
      (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
      hn4 hn0 hRmax hEmax hDmax T_timer C hC hMAC hTLo hTHi
  exact Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
    (PEMProtocolCoupled n Rmax Emax Dmax hn0) (by omega : 2 ≤ n) C _
    hM
    (by
      dsimp [OW_macLiveWindow]
      omega)


/-- Chain decision -> timer-drain (bounded invariant threaded). From InSswap with a
live, bounded median timer, within `2n(n-1) + 2*T_timer*n(n-1)` steps reach consensus /
a correct reset seed / leave the live-swap region, with probability >= 1/4. -/
theorem swap_live_to_cons_or_crs_or_break (hn4 : 4 ≤ n) (hn0 : 0 < n) (hRmax : n ≤ Rmax)
    (T_timer : ℕ)
    (hTimerStep : ∀ D : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig T_timer D → ∀ i j : Fin n,
        IsTimerBoundedConfig T_timer (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j))
    (C : Config (AgentState n) Opinion n) (hC : InSswap C)
    (hT : MedianTimerAtLeast 1 C) (hB : IsTimerBoundedConfig T_timer C) :
    ((4 : ENNReal)⁻¹) ≤
      Probability.ProbHitWithin (PEMProtocolCoupled n Rmax Emax Dmax hn0)
        (by omega : 2 ≤ n) C
        (fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨
          ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
        (2 * (n * (n - 1)) + 2 * (T_timer * n * (n - 1))) := by
  have hn2 : (2 : ℕ) ≤ n := by omega
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0 with hP
  set Inv : Config (AgentState n) Opinion n → Prop :=
    fun D => IsTimerBoundedConfig T_timer D with hInvDef
  set Goal : Config (AgentState n) Opinion n → Prop :=
    fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨ ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
    with hGoalDef
  have hInvStep : ∀ D, Inv D → ∀ i j, Inv (D.step P i j) :=
    fun D hD i j => by
      simpa [P, Inv] using hTimerStep D hD i j
  by_cases hMAC : MedianAnswerCorrect C
  · refine le_trans ?_ (Probability.ProbHitWithin_mono_time P hn2 C Goal
      (m := 2 * (T_timer * n * (n - 1))) (by omega))
    refine le_trans ?_ (timer_drain_window hn4 hn0 hRmax T_timer C hC hMAC hT hB)
    rw [ENNReal.inv_le_inv]; norm_num
  · set dG : Config (AgentState n) Opinion n → Prop :=
      fun D => (InSswap D ∧ MedianAnswerCorrect D) ∨ ¬ (InSswap D ∧ MedianTimerAtLeast 1 D)
      with hdGDef
    set Mid : Config (AgentState n) Opinion n → Prop := fun D => dG D ∧ Inv D with hMidDef
    have hMid : ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C Mid (2 * (n * (n - 1))) := by
      rw [hMidDef,
        Probability.ProbHitWithin_eq_and_inv_of_invariant P hn2 C dG Inv hB hInvStep]
      exact decision_window hn4 hn0 C hC hT hMAC
    have hGoal : ∀ C' : Config (AgentState n) Opinion n, Mid C' →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C' Goal (2 * (T_timer * n * (n - 1))) := by
      intro C' hC'
      obtain ⟨hdg, hinv⟩ := hC'
      by_cases hlive : InSswap C' ∧ MedianTimerAtLeast 1 C'
      · have hmac : MedianAnswerCorrect C' := by
          rcases hdg with ⟨_, hm⟩ | hexit
          · exact hm
          · exact absurd hlive hexit
        exact timer_drain_window hn4 hn0 hRmax T_timer C' hlive.1 hmac hlive.2 hinv
      · have hgC' : Goal C' := Or.inr (Or.inr hlive)
        have h1 : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 C' Goal (2 * (T_timer * n * (n - 1))) := by
          calc (1 : ENNReal) = Probability.probReached P hn2 C' Goal 0 :=
                (Probability.probReached_zero_of_goal P hn2 C' Goal hgC').symm
            _ ≤ Probability.ProbHitWithin P hn2 C' Goal 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 C' Goal 0
            _ ≤ Probability.ProbHitWithin P hn2 C' Goal (2 * (T_timer * n * (n - 1))) :=
                Probability.ProbHitWithin_mono_time P hn2 C' Goal (Nat.zero_le _)
        exact le_trans (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1) h1
    have hchain := Probability.ProbHitWithin_add_ge_mul P hn2 C Mid Goal
      (2 * (n * (n - 1))) (2 * (T_timer * n * (n - 1)))
      ((2 : ENNReal)⁻¹) ((2 : ENNReal)⁻¹) hMid hGoal
    have harith : ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) = ((4 : ENNReal)⁻¹) := by
      rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]; norm_num
    rwa [harith] at hchain

/-- Exit branch re-enters the live swap cycle using the cited [12] re-rank
window, then the proven swap window.  The endpoint is the swap-cycle event,
not silence or consensus. -/
theorem OW_exit_rerank_to_swap_event (hn4 : 4 ≤ n) (hn0 : 0 < n)
    (hRmax : n ≤ Rmax) (T_timer T_rerank : ℕ)
    (hTimerStep : ∀ D : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig T_timer D → ∀ i j : Fin n,
        IsTimerBoundedConfig T_timer (D.step (PEMProtocolCoupled n Rmax Emax Dmax hn0) i j))
    (h12reRank :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig T_timer C →
        ¬ (InSswap C ∧ MedianTimerAtLeast 1 C) →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax hn0)
              (by omega : 2 ≤ n) C
              (fun D => InSswap D ∧ MedianTimerAtLeast 1 D) T_rerank) :
    ∀ C : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig T_timer C →
      ¬ (InSswap C ∧ MedianTimerAtLeast 1 C) →
        ((8 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin
            (PEMProtocolCoupled n Rmax Emax Dmax hn0)
            (by omega : 2 ≤ n) C
            (fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨
              ¬ (InSswap D ∧ MedianTimerAtLeast 1 D))
            (T_rerank + OW_swapWindow n T_timer) := by
  classical
  intro C hTimer hExit
  have hn2 : 2 ≤ n := by omega
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0 with hP
  let Inv : Config (AgentState n) Opinion n → Prop :=
    IsTimerBoundedConfig T_timer
  let Live : Config (AgentState n) Opinion n → Prop :=
    fun D => InSswap D ∧ MedianTimerAtLeast 1 D
  let SwapEvent : Config (AgentState n) Opinion n → Prop :=
    fun D => IsConsensusConfig D ∨ CorrectResetSeed D ∨ ¬ Live D
  have hInvStep : ∀ D : Config (AgentState n) Opinion n, Inv D →
      ∀ i j : Fin n, Inv (D.step P i j) := by
    intro D hD i j
    simpa [P, Inv] using hTimerStep D hD i j
  have hLive :
      ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C
          (fun D => Live D ∧ Inv D) T_rerank := by
    rw [Probability.ProbHitWithin_eq_and_inv_of_invariant
      P hn2 C Live Inv hTimer hInvStep T_rerank]
    simpa [P, Live] using h12reRank C hTimer hExit
  have hSwap :
      ∀ D : Config (AgentState n) Opinion n, Live D ∧ Inv D →
        ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 D SwapEvent (OW_swapWindow n T_timer) := by
    intro D hD
    simpa [P, Live, Inv, SwapEvent, OW_swapWindow] using
      swap_live_to_cons_or_crs_or_break
        (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
        hn4 hn0 hRmax T_timer hTimerStep D hD.1.1 hD.1.2 hD.2
  have hChain :
      ((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C SwapEvent
          (T_rerank + OW_swapWindow n T_timer) :=
    Probability.ProbHitWithin_add_ge_mul P hn2 C
      (fun D => Live D ∧ Inv D) SwapEvent
      T_rerank (OW_swapWindow n T_timer)
      ((2 : ENNReal)⁻¹) ((4 : ENNReal)⁻¹)
      hLive hSwap
  have hprod : ((2 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹) = ((8 : ENNReal)⁻¹) := by
    rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    norm_num
  simpa [P, Live, SwapEvent, hprod] using hChain

/-- **Keystone 2 (consensus from a fresh live swap).** From `InSswap` with a
fresh (`≥ 35`), bounded median timer, the expected time to consensus is bounded
by one renewal window times the inverse of the cited reset-success probability.

The renewal uses only the cited [12] reset-completion, rank, and re-rank windows.
The old aggregate `hRank12` hypothesis is not used. -/
theorem OW_consensusBound (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (T_timer K_reset T_rank T_rerank : ℕ)
    (p_reset : ENNReal) (C_reset : ℕ)
    (hTimerStep : ∀ D : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig T_timer D → ∀ i j : Fin n,
        IsTimerBoundedConfig T_timer
          (D.step (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n)) i j))
    (h12resetCompletion :
      CRSResetCompletion12 (n := n) (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) (by omega : 0 < n) p_reset C_reset K_reset)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank)
    (h12reRank :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        IsTimerBoundedConfig T_timer C →
        ¬ (InSswap C ∧ MedianTimerAtLeast 35 C) →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (fun D => InSswap D ∧ MedianTimerAtLeast 35 D) T_rerank) :
    ∀ C : Config (AgentState n) Opinion n,
      InSswap C → MedianTimerAtLeast 35 C →
      IsTimerBoundedConfig (7 * (Rmax + 4)) C →
      IsTimerBoundedConfig T_timer C →
        Probability.expectedHittingTime
          (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
          (by omega : 2 ≤ n) C IsConsensusConfig ≤
          ((OW_consensusCycleWindow n T_timer K_reset T_rank T_rerank : ℕ) : ENNReal) *
            (p_reset * ((64 : ENNReal)⁻¹))⁻¹ := by
  classical
  intro C₀ hS₀ hT₀ hB₀ hBT₀
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0 with hP
  let Inv : Config (AgentState n) Opinion n → Prop :=
    fun C => IsTimerBoundedConfig (7 * (Rmax + 4)) C ∧
      IsTimerBoundedConfig T_timer C
  let Live35 : Config (AgentState n) Opinion n → Prop :=
    fun C => InSswap C ∧ MedianTimerAtLeast 35 C
  let Live35Mid : Config (AgentState n) Opinion n → Prop :=
    fun C => Live35 C ∧ Inv C
  let DecisionTarget : Config (AgentState n) Opinion n → Prop :=
    (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop)
  let DecisionMid : Config (AgentState n) Opinion n → Prop :=
    fun C => DecisionTarget C ∧ Inv C
  let ConsOrCRS : Config (AgentState n) Opinion n → Prop :=
    fun C => IsConsensusConfig C ∨ CorrectResetSeed C
  let ConsOrCRSMid : Config (AgentState n) Opinion n → Prop :=
    fun C => ConsOrCRS C ∧ Inv C
  let KLive : ℕ := OW_liveConsensusWindow n T_timer K_reset T_rank
  let K : ℕ := OW_consensusCycleWindow n T_timer K_reset T_rank T_rerank
  have hDecisionPos : 0 < decisionWindow n := by
    dsimp [decisionWindow]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
  have hLivePos : 0 < OW_liveConsensusWindow n T_timer K_reset T_rank := by
    dsimp [OW_liveConsensusWindow]
    omega
  have hKpos : 0 < K := by
    dsimp [K, OW_consensusCycleWindow]
    omega
  haveI : NeZero K := ⟨Nat.pos_iff_ne_zero.mp hKpos⟩
  have hp_le_one : p_reset * ((64 : ENNReal)⁻¹) ≤ 1 := by
    exact (mul_le_mul' h12resetCompletion.resetProb_le_one
      (by norm_num : ((64 : ENNReal)⁻¹) ≤ 1)).trans (by simp)
  have hInvStep : ∀ C : Config (AgentState n) Opinion n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j) := by
    intro C hC i j
    constructor
    · simpa [P, Inv] using
        PEMProtocolCoupled_preserves_timer_bounded hn0 C hC.1 i j
    · simpa [P, Inv] using hTimerStep C hC.2 i j
  have hConsOrCRSToConsensus :
      ∀ C : Config (AgentState n) Opinion n, ConsOrCRSMid C →
        p_reset * ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig
            (K_reset + OW_answerEpidemicWindow n + T_rank) := by
    intro C hC
    rcases hC with ⟨hEvent, hInvC⟩
    rcases hEvent with hCons | hSeed
    · have hOne : (1 : ENNReal) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig
            (K_reset + OW_answerEpidemicWindow n + T_rank) := by
        calc
          (1 : ENNReal) = Probability.probReached P hn2 C IsConsensusConfig 0 := by
              exact (Probability.probReached_zero_of_goal P hn2 C IsConsensusConfig hCons).symm
          _ ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig 0 :=
              Probability.probReached_le_ProbHitWithin P hn2 C IsConsensusConfig 0
          _ ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig
                (K_reset + OW_answerEpidemicWindow n + T_rank) :=
              Probability.ProbHitWithin_mono_time P hn2 C IsConsensusConfig (Nat.zero_le _)
      have hp4_le_one : p_reset * ((4 : ENNReal)⁻¹) ≤ 1 := by
        exact (mul_le_mul' h12resetCompletion.resetProb_le_one
          (by norm_num : ((4 : ENNReal)⁻¹) ≤ 1)).trans (by simp)
      exact le_trans hp4_le_one hOne
    · have hCRS :
          p_reset * ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin P hn2 C IsConsensusConfig
              (K_reset + OW_answerEpidemicWindow n + T_rank) := by
        simpa [P] using
          (CRS_to_consensus_faithful_product
            (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn4 K_reset T_rank p_reset ((2 : ENNReal)⁻¹) C_reset
            h12resetCompletion h12rank C hInvC.1 hSeed)
      have hprod :
          p_reset * ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) =
            p_reset * ((4 : ENNReal)⁻¹) := by
        have hhalf :
            ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) = ((4 : ENNReal)⁻¹) := by
          rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          norm_num
        rw [mul_assoc, hhalf]
      simpa [hprod] using hCRS
  have hDecisionToConsOrCRS :
      ∀ C : Config (AgentState n) Opinion n, DecisionMid C →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C ConsOrCRSMid
            (OW_macLiveWindow n T_timer) := by
    intro C hC
    rcases hC with ⟨hDecision, hInvC⟩
    rcases hDecision with hMAC | hRest
    · have hBase :
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin P hn2 C ConsOrCRS
              (OW_macLiveWindow n T_timer) := by
        simpa [P, ConsOrCRS] using
          (MAClive_to_consensus_or_crs_window
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn4 hn0 hRmax hEmax hDmax T_timer C
            hMAC.1 hMAC.2.1 hMAC.2.2 hInvC.2)
      rw [Probability.ProbHitWithin_eq_and_inv_of_invariant
        P hn2 C ConsOrCRS Inv hInvC hInvStep (OW_macLiveWindow n T_timer)]
      exact hBase
    · rcases hRest with hCons | hSeed
      · have hGoalC : ConsOrCRSMid C := ⟨Or.inl hCons, hInvC⟩
        have hOne : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 C ConsOrCRSMid
              (OW_macLiveWindow n T_timer) := by
          calc
            (1 : ENNReal) =
                Probability.probReached P hn2 C ConsOrCRSMid 0 := by
                  exact (Probability.probReached_zero_of_goal P hn2 C
                    ConsOrCRSMid hGoalC).symm
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 C ConsOrCRSMid 0
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid
                  (OW_macLiveWindow n T_timer) :=
                Probability.ProbHitWithin_mono_time P hn2 C ConsOrCRSMid
                  (Nat.zero_le _)
        exact le_trans (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1) hOne
      · have hGoalC : ConsOrCRSMid C := ⟨Or.inr hSeed, hInvC⟩
        have hOne : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 C ConsOrCRSMid
              (OW_macLiveWindow n T_timer) := by
          calc
            (1 : ENNReal) =
                Probability.probReached P hn2 C ConsOrCRSMid 0 := by
                  exact (Probability.probReached_zero_of_goal P hn2 C
                    ConsOrCRSMid hGoalC).symm
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 C ConsOrCRSMid 0
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid
                  (OW_macLiveWindow n T_timer) :=
                Probability.ProbHitWithin_mono_time P hn2 C ConsOrCRSMid
                  (Nat.zero_le _)
        exact le_trans (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1) hOne
  have hLiveToConsensus :
      ∀ C : Config (AgentState n) Opinion n, Inv C → Live35 C →
        p_reset * ((32 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig KLive := by
    intro C hInvC hLive
    have hDecisionBase :
        ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C DecisionTarget (decisionWindow n) := by
      simpa [P, DecisionTarget] using
        (decision_before_timer_zero
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn4 hn0 hRmax hEmax hDmax C hLive.1 hLive.2)
    have hDecision :
        ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C DecisionMid (decisionWindow n) := by
      rw [Probability.ProbHitWithin_eq_and_inv_of_invariant
        P hn2 C DecisionTarget Inv hInvC hInvStep (decisionWindow n)]
      exact hDecisionBase
    have hAB :
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C ConsOrCRSMid
            (decisionWindow n + OW_macLiveWindow n T_timer) :=
      Probability.ProbHitWithin_add_ge_mul P hn2 C DecisionMid ConsOrCRSMid
        (decisionWindow n) (OW_macLiveWindow n T_timer)
        ((4 : ENNReal)⁻¹) ((2 : ENNReal)⁻¹)
        hDecision hDecisionToConsOrCRS
    have hChain :
        (((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹)) *
            (p_reset * ((4 : ENNReal)⁻¹)) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig
            ((decisionWindow n + OW_macLiveWindow n T_timer) +
              (K_reset + OW_answerEpidemicWindow n + T_rank)) :=
      Probability.ProbHitWithin_add_ge_mul P hn2 C ConsOrCRSMid IsConsensusConfig
        (decisionWindow n + OW_macLiveWindow n T_timer)
        (K_reset + OW_answerEpidemicWindow n + T_rank)
        (((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹))
        (p_reset * ((4 : ENNReal)⁻¹))
        hAB hConsOrCRSToConsensus
    have h42 :
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) = ((8 : ENNReal)⁻¹) := by
      rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num
    have hprod :
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) *
            (p_reset * ((4 : ENNReal)⁻¹)) =
          p_reset * ((32 : ENNReal)⁻¹) := by
      have h84 :
          ((8 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹) = ((32 : ENNReal)⁻¹) := by
        rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        norm_num
      calc
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) *
            (p_reset * ((4 : ENNReal)⁻¹))
            = p_reset * (((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) *
                ((4 : ENNReal)⁻¹)) := by ac_rfl
        _ = p_reset * (((8 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹)) := by rw [h42]
        _ = p_reset * ((32 : ENNReal)⁻¹) := by rw [h84]
    simpa [KLive, OW_liveConsensusWindow, hprod] using hChain
  have hWindow : ∀ C : Config (AgentState n) Opinion n, Inv C →
      ¬ IsConsensusConfig C →
      p_reset * ((64 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C IsConsensusConfig K := by
    intro C hInvC _hNotCons
    by_cases hLive : Live35 C
    · have hLiveHit := hLiveToConsensus C hInvC hLive
      have hLiveK : p_reset * ((32 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig K :=
        hLiveHit.trans
          (Probability.ProbHitWithin_mono_time P hn2 C IsConsensusConfig
            (by
              dsimp [K, KLive, OW_consensusCycleWindow]
              omega))
      have hprob_le :
          p_reset * ((64 : ENNReal)⁻¹) ≤ p_reset * ((32 : ENNReal)⁻¹) := by
        simpa [mul_comm] using
          (mul_le_mul_right
            (by norm_num : ((64 : ENNReal)⁻¹) ≤ ((32 : ENNReal)⁻¹))
            p_reset)
      exact hprob_le.trans hLiveK
    · have hReRankBase :
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin P hn2 C Live35 T_rerank := by
        simpa [P, Live35] using h12reRank C hInvC.1 hInvC.2 hLive
      have hReRank :
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin P hn2 C Live35Mid T_rerank := by
        rw [Probability.ProbHitWithin_eq_and_inv_of_invariant
          P hn2 C Live35 Inv hInvC hInvStep T_rerank]
        exact hReRankBase
      have hAfter :
          ∀ D : Config (AgentState n) Opinion n, Live35Mid D →
            p_reset * ((32 : ENNReal)⁻¹) ≤
              Probability.ProbHitWithin P hn2 D IsConsensusConfig KLive := by
        intro D hD
        exact hLiveToConsensus D hD.2 hD.1
      have hChain :
          ((2 : ENNReal)⁻¹) * (p_reset * ((32 : ENNReal)⁻¹)) ≤
            Probability.ProbHitWithin P hn2 C IsConsensusConfig
              (T_rerank + KLive) :=
        Probability.ProbHitWithin_add_ge_mul P hn2 C Live35Mid IsConsensusConfig
          T_rerank KLive ((2 : ENNReal)⁻¹) (p_reset * ((32 : ENNReal)⁻¹))
          hReRank hAfter
      have hprod :
          ((2 : ENNReal)⁻¹) * (p_reset * ((32 : ENNReal)⁻¹)) =
            p_reset * ((64 : ENNReal)⁻¹) := by
        have h232 :
            ((2 : ENNReal)⁻¹) * ((32 : ENNReal)⁻¹) = ((64 : ENNReal)⁻¹) := by
          rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          norm_num
        calc
          ((2 : ENNReal)⁻¹) * (p_reset * ((32 : ENNReal)⁻¹))
              = p_reset * (((2 : ENNReal)⁻¹) * ((32 : ENNReal)⁻¹)) := by ac_rfl
          _ = p_reset * ((64 : ENNReal)⁻¹) := by rw [h232]
      simpa [K, KLive, OW_consensusCycleWindow, hprod] using hChain
  have hExpected :=
    Probability.expectedHittingTime_le_window_mul_inv_of_invariant
      P hn2 C₀ IsConsensusConfig Inv K (p_reset * ((64 : ENNReal)⁻¹))
      hp_le_one ⟨hB₀, hBT₀⟩ hInvStep hWindow
  simpa [K] using hExpected

/-- **Unconditional parallel-time bound modulo the cited [12] ranking windows.**
From any timer-bounded initial configuration, the expected parallel time to
consensus is controlled by the ranking window, the [12] re-rank entry window,
and the consensus renewal above. -/
theorem PEM_expectedParallelTime_optimal (hn4 : 4 ≤ n)
    (hRmax : n ≤ Rmax) (hEmax : n ≤ Emax) (hDmax : n ≤ Dmax)
    (C_rank T_timer K_reset T_rank T_rerank : ℕ)
    (p_reset : ENNReal) (C_reset : ℕ)
    (hTimerStep : ∀ D : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig T_timer D → ∀ i j : Fin n,
        IsTimerBoundedConfig T_timer
          (D.step (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n)) i j))
    (h12ranking :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
          IsTimerBoundedConfig T_timer C →
          Probability.expectedHittingTime
            (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
            (by omega : 2 ≤ n) C
            (fun D => InSrank D ∧ MedianTimerAtLeast 35 D ∧
              IsTimerBoundedConfig (7 * (Rmax + 4)) D ∧
              IsTimerBoundedConfig T_timer D) ≤
            ((C_rank * n * n : ℕ) : ENNReal))
    (h12resetCompletion :
      CRSResetCompletion12 (n := n) (Rmax := Rmax) (Emax := Emax)
        (Dmax := Dmax) (by omega : 0 < n) p_reset C_reset K_reset)
    (h12rank :
      ∀ (m : Answer) (D : Config (AgentState n) Opinion n),
        EpidemicPhiGoal m D →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) D
              (OW_rankedEpidemicEndpoint m) T_rank)
    (h12reRank :
      ∀ C : Config (AgentState n) Opinion n,
        IsTimerBoundedConfig (7 * (Rmax + 4)) C →
        IsTimerBoundedConfig T_timer C →
        ¬ (InSswap C ∧ MedianTimerAtLeast 35 C) →
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin
              (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
              (by omega : 2 ≤ n) C
              (fun D => InSswap D ∧ MedianTimerAtLeast 35 D) T_rerank) :
    ∀ C₀ : Config (AgentState n) Opinion n,
      IsTimerBoundedConfig (7 * (Rmax + 4)) C₀ →
      IsTimerBoundedConfig T_timer C₀ →
      Probability.expectedParallelTimeToConsensus
        (PEMProtocolCoupled n Rmax Emax Dmax (by omega : 0 < n))
        (by omega : 2 ≤ n) C₀ ≤
        (((OW_globalWindow n C_rank T_timer K_reset T_rank T_rerank : ℕ) : ENNReal) *
          (p_reset * ((128 : ENNReal)⁻¹))⁻¹ / n) := by
  classical
  intro C₀ hTimer₀ hTimerT₀
  have hn0 : 0 < n := by omega
  have hn2 : 2 ≤ n := by omega
  set P := PEMProtocolCoupled n Rmax Emax Dmax hn0 with hP
  let Inv : Config (AgentState n) Opinion n → Prop :=
    fun C => IsTimerBoundedConfig (7 * (Rmax + 4)) C ∧
      IsTimerBoundedConfig T_timer C
  let RankTarget : Config (AgentState n) Opinion n → Prop :=
    fun C =>
      InSrank C ∧ MedianTimerAtLeast 35 C ∧
        IsTimerBoundedConfig (7 * (Rmax + 4)) C ∧
        IsTimerBoundedConfig T_timer C
  let Live35 : Config (AgentState n) Opinion n → Prop :=
    fun C => InSswap C ∧ MedianTimerAtLeast 35 C
  let Live35Target : Config (AgentState n) Opinion n → Prop :=
    fun C => Live35 C ∧ Inv C
  let DecisionTarget : Config (AgentState n) Opinion n → Prop :=
    (DecisionProductiveTarget : Config (AgentState n) Opinion n → Prop)
  let DecisionMid : Config (AgentState n) Opinion n → Prop :=
    fun C => DecisionTarget C ∧ Inv C
  let ConsOrCRS : Config (AgentState n) Opinion n → Prop :=
    fun C => IsConsensusConfig C ∨ CorrectResetSeed C
  let ConsOrCRSMid : Config (AgentState n) Opinion n → Prop :=
    fun C => ConsOrCRS C ∧ Inv C
  let KLive : ℕ := OW_liveConsensusWindow n T_timer K_reset T_rank
  let K : ℕ := OW_globalWindow n C_rank T_timer K_reset T_rank T_rerank
  have hKpos : 0 < K := by
    have hDecisionPos : 0 < decisionWindow n := by
      dsimp [decisionWindow]
      exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
    have hLivePos : 0 < OW_liveConsensusWindow n T_timer K_reset T_rank := by
      dsimp [OW_liveConsensusWindow]
      omega
    dsimp [K, OW_globalWindow]
    omega
  haveI : NeZero K := ⟨Nat.pos_iff_ne_zero.mp hKpos⟩
  have hp_le_one : p_reset * ((128 : ENNReal)⁻¹) ≤ 1 := by
    exact (mul_le_mul' h12resetCompletion.resetProb_le_one
      (by norm_num : ((128 : ENNReal)⁻¹) ≤ 1)).trans (by simp)
  have hInvStep : ∀ C : Config (AgentState n) Opinion n, Inv C →
      ∀ i j : Fin n, Inv (C.step P i j) := by
    intro C hC i j
    constructor
    · simpa [P, Inv] using
        PEMProtocolCoupled_preserves_timer_bounded hn0 C hC.1 i j
    · simpa [P, Inv] using hTimerStep C hC.2 i j
  have hRankBound := OW_rankBound
    (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
    hn4 hRmax hEmax hDmax C_rank T_timer h12ranking
  have hConsOrCRSToConsensus :
      ∀ C : Config (AgentState n) Opinion n, ConsOrCRSMid C →
        p_reset * ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig
            (K_reset + OW_answerEpidemicWindow n + T_rank) := by
    intro C hC
    rcases hC with ⟨hEvent, hInvC⟩
    rcases hEvent with hCons | hSeed
    · have hOne : (1 : ENNReal) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig
            (K_reset + OW_answerEpidemicWindow n + T_rank) := by
        calc
          (1 : ENNReal) = Probability.probReached P hn2 C IsConsensusConfig 0 := by
              exact (Probability.probReached_zero_of_goal P hn2 C IsConsensusConfig hCons).symm
          _ ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig 0 :=
              Probability.probReached_le_ProbHitWithin P hn2 C IsConsensusConfig 0
          _ ≤ Probability.ProbHitWithin P hn2 C IsConsensusConfig
                (K_reset + OW_answerEpidemicWindow n + T_rank) :=
              Probability.ProbHitWithin_mono_time P hn2 C IsConsensusConfig (Nat.zero_le _)
      have hp4_le_one : p_reset * ((4 : ENNReal)⁻¹) ≤ 1 := by
        exact (mul_le_mul' h12resetCompletion.resetProb_le_one
          (by norm_num : ((4 : ENNReal)⁻¹) ≤ 1)).trans (by simp)
      exact hp4_le_one.trans hOne
    · have hCRS :
          p_reset * ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin P hn2 C IsConsensusConfig
              (K_reset + OW_answerEpidemicWindow n + T_rank) := by
        simpa [P] using
          (CRS_to_consensus_faithful_product
            (n := n) (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn4 K_reset T_rank p_reset ((2 : ENNReal)⁻¹) C_reset
            h12resetCompletion h12rank C hInvC.1 hSeed)
      have hprod :
          p_reset * ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) =
            p_reset * ((4 : ENNReal)⁻¹) := by
        have hhalf :
            ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) = ((4 : ENNReal)⁻¹) := by
          rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          norm_num
        rw [mul_assoc, hhalf]
      simpa [hprod] using hCRS
  have hDecisionToConsOrCRS :
      ∀ C : Config (AgentState n) Opinion n, DecisionMid C →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C ConsOrCRSMid
            (OW_macLiveWindow n T_timer) := by
    intro C hC
    rcases hC with ⟨hDecision, hInvC⟩
    rcases hDecision with hMAC | hRest
    · have hBase :
          ((2 : ENNReal)⁻¹) ≤
            Probability.ProbHitWithin P hn2 C ConsOrCRS
              (OW_macLiveWindow n T_timer) := by
        simpa [P, ConsOrCRS] using
          (MAClive_to_consensus_or_crs_window
            (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
            hn4 hn0 hRmax hEmax hDmax T_timer C
            hMAC.1 hMAC.2.1 hMAC.2.2 hInvC.2)
      rw [Probability.ProbHitWithin_eq_and_inv_of_invariant
        P hn2 C ConsOrCRS Inv hInvC hInvStep (OW_macLiveWindow n T_timer)]
      exact hBase
    · rcases hRest with hCons | hSeed
      · have hGoalC : ConsOrCRSMid C := ⟨Or.inl hCons, hInvC⟩
        have hOne : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 C ConsOrCRSMid
              (OW_macLiveWindow n T_timer) := by
          calc
            (1 : ENNReal) =
                Probability.probReached P hn2 C ConsOrCRSMid 0 := by
                  exact (Probability.probReached_zero_of_goal P hn2 C
                    ConsOrCRSMid hGoalC).symm
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 C ConsOrCRSMid 0
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid
                  (OW_macLiveWindow n T_timer) :=
                Probability.ProbHitWithin_mono_time P hn2 C ConsOrCRSMid
                  (Nat.zero_le _)
        exact le_trans (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1) hOne
      · have hGoalC : ConsOrCRSMid C := ⟨Or.inr hSeed, hInvC⟩
        have hOne : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 C ConsOrCRSMid
              (OW_macLiveWindow n T_timer) := by
          calc
            (1 : ENNReal) =
                Probability.probReached P hn2 C ConsOrCRSMid 0 := by
                  exact (Probability.probReached_zero_of_goal P hn2 C
                    ConsOrCRSMid hGoalC).symm
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 C ConsOrCRSMid 0
            _ ≤ Probability.ProbHitWithin P hn2 C ConsOrCRSMid
                  (OW_macLiveWindow n T_timer) :=
                Probability.ProbHitWithin_mono_time P hn2 C ConsOrCRSMid
                  (Nat.zero_le _)
        exact le_trans (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1) hOne
  have hLiveToConsensus :
      ∀ C : Config (AgentState n) Opinion n, Live35Target C →
        p_reset * ((32 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig KLive := by
    intro C hLiveTarget
    rcases hLiveTarget with ⟨hLive, hInvC⟩
    have hDecisionBase :
        ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C DecisionTarget (decisionWindow n) := by
      simpa [P, DecisionTarget] using
        (decision_before_timer_zero
          (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax)
          hn4 hn0 hRmax hEmax hDmax C hLive.1 hLive.2)
    have hDecision :
        ((4 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C DecisionMid (decisionWindow n) := by
      rw [Probability.ProbHitWithin_eq_and_inv_of_invariant
        P hn2 C DecisionTarget Inv hInvC hInvStep (decisionWindow n)]
      exact hDecisionBase
    have hAB :
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C ConsOrCRSMid
            (decisionWindow n + OW_macLiveWindow n T_timer) :=
      Probability.ProbHitWithin_add_ge_mul P hn2 C DecisionMid ConsOrCRSMid
        (decisionWindow n) (OW_macLiveWindow n T_timer)
        ((4 : ENNReal)⁻¹) ((2 : ENNReal)⁻¹)
        hDecision hDecisionToConsOrCRS
    have hChain :
        (((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹)) *
            (p_reset * ((4 : ENNReal)⁻¹)) ≤
          Probability.ProbHitWithin P hn2 C IsConsensusConfig
            ((decisionWindow n + OW_macLiveWindow n T_timer) +
              (K_reset + OW_answerEpidemicWindow n + T_rank)) :=
      Probability.ProbHitWithin_add_ge_mul P hn2 C ConsOrCRSMid IsConsensusConfig
        (decisionWindow n + OW_macLiveWindow n T_timer)
        (K_reset + OW_answerEpidemicWindow n + T_rank)
        (((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹))
        (p_reset * ((4 : ENNReal)⁻¹))
        hAB hConsOrCRSToConsensus
    have h42 :
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) = ((8 : ENNReal)⁻¹) := by
      rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num
    have h84 :
        ((8 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹) = ((32 : ENNReal)⁻¹) := by
      rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      norm_num
    have hprod :
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) *
            (p_reset * ((4 : ENNReal)⁻¹)) =
          p_reset * ((32 : ENNReal)⁻¹) := by
      calc
        ((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) *
            (p_reset * ((4 : ENNReal)⁻¹))
            = p_reset * (((4 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) *
                ((4 : ENNReal)⁻¹)) := by ac_rfl
        _ = p_reset * (((8 : ENNReal)⁻¹) * ((4 : ENNReal)⁻¹)) := by rw [h42]
        _ = p_reset * ((32 : ENNReal)⁻¹) := by rw [h84]
    simpa [KLive, OW_liveConsensusWindow, hprod] using hChain
  have hwin : ∀ C : Config (AgentState n) Opinion n, Inv C →
      ¬ IsConsensusConfig C →
      p_reset * ((128 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C IsConsensusConfig K := by
    intro C hInvC _hNot
    have hRankE : Probability.expectedHittingTime P hn2 C RankTarget ≤
        ((C_rank * n * n : ℕ) : ENNReal) := by
      simpa [P, RankTarget, Inv] using hRankBound C hInvC.1 hInvC.2
    have hRankW : 2 * (C_rank * n * n) ≤ (2 * C_rank * n * n) + 1 := by nlinarith
    have hRankPH : ((2 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C RankTarget (2 * C_rank * n * n) :=
      Probability.ProbHitWithin_ge_half_of_expectedHittingTime_le
        P hn2 C RankTarget hRankE hRankW
    have hLivePH : ∀ D : Config (AgentState n) Opinion n, RankTarget D →
        ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 D Live35Target T_rerank := by
      intro D hD
      by_cases hLive : Live35 D
      · have hGoalD : Live35Target D := ⟨hLive, hD.2.2⟩
        have hOne : (1 : ENNReal) ≤
            Probability.ProbHitWithin P hn2 D Live35Target T_rerank := by
          calc
            (1 : ENNReal) =
                Probability.probReached P hn2 D Live35Target 0 := by
                  exact (Probability.probReached_zero_of_goal P hn2 D
                    Live35Target hGoalD).symm
            _ ≤ Probability.ProbHitWithin P hn2 D Live35Target 0 :=
                Probability.probReached_le_ProbHitWithin P hn2 D Live35Target 0
            _ ≤ Probability.ProbHitWithin P hn2 D Live35Target T_rerank :=
                Probability.ProbHitWithin_mono_time P hn2 D Live35Target
                  (Nat.zero_le _)
        exact le_trans (by norm_num : ((2 : ENNReal)⁻¹) ≤ 1) hOne
      · have hBase :
            ((2 : ENNReal)⁻¹) ≤
              Probability.ProbHitWithin P hn2 D Live35 T_rerank := by
          simpa [P, Live35] using h12reRank D hD.2.2.1 hD.2.2.2 hLive
        rw [Probability.ProbHitWithin_eq_and_inv_of_invariant
          P hn2 D Live35 Inv hD.2.2 hInvStep T_rerank]
        exact hBase
    have hAB : ((4 : ENNReal)⁻¹) ≤
        Probability.ProbHitWithin P hn2 C Live35Target
          (2 * C_rank * n * n + T_rerank) := by
      have hAB' : ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) ≤
          Probability.ProbHitWithin P hn2 C Live35Target
            (2 * C_rank * n * n + T_rerank) :=
        Probability.ProbHitWithin_add_ge_mul P hn2 C RankTarget Live35Target
          (2 * C_rank * n * n) T_rerank
          ((2 : ENNReal)⁻¹) ((2 : ENNReal)⁻¹)
          hRankPH hLivePH
      have hprod :
          ((2 : ENNReal)⁻¹) * ((2 : ENNReal)⁻¹) = ((4 : ENNReal)⁻¹) := by
        rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        norm_num
      simpa [hprod] using hAB'
    have hChain : ((4 : ENNReal)⁻¹) * (p_reset * ((32 : ENNReal)⁻¹)) ≤
        Probability.ProbHitWithin P hn2 C IsConsensusConfig
          ((2 * C_rank * n * n + T_rerank) + KLive) :=
      Probability.ProbHitWithin_add_ge_mul P hn2 C Live35Target IsConsensusConfig
        (2 * C_rank * n * n + T_rerank) KLive
        ((4 : ENNReal)⁻¹) (p_reset * ((32 : ENNReal)⁻¹))
        hAB hLiveToConsensus
    have hprod :
        ((4 : ENNReal)⁻¹) * (p_reset * ((32 : ENNReal)⁻¹)) =
          p_reset * ((128 : ENNReal)⁻¹) := by
      have h432 :
          ((4 : ENNReal)⁻¹) * ((32 : ENNReal)⁻¹) = ((128 : ENNReal)⁻¹) := by
        rw [← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        norm_num
      calc
        ((4 : ENNReal)⁻¹) * (p_reset * ((32 : ENNReal)⁻¹))
            = p_reset * (((4 : ENNReal)⁻¹) * ((32 : ENNReal)⁻¹)) := by ac_rfl
        _ = p_reset * ((128 : ENNReal)⁻¹) := by rw [h432]
    simpa [K, OW_globalWindow, hprod] using hChain
  simpa [Probability.expectedParallelTimeToConsensus, P, Inv, K] using
    (Probability.expectedParallelTime_le_window_mul_inv_of_invariant
      P hn2 C₀ IsConsensusConfig Inv K (p_reset * ((128 : ENNReal)⁻¹))
      hp_le_one ⟨hTimer₀, hTimerT₀⟩ hInvStep hwin)

end

end SSEM
