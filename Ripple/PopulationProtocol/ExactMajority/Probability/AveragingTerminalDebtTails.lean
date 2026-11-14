-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingTerminalDebtTails.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingChangingZeroTail
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingMajorityPartners

/-!
# Actual stopped drains for X and Y

X is serviced by current Clock/eligible-Main interactions. Y is serviced by
current exact-hour-zero/near-majority interactions. Both orientations are
retained. The killed ceiling processes and their conditional death bounds
are constructed on the original physical-label scheduler.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.AveragingTerminalDebtTails

open TimeTheorem PairLog PhaseOneDrain AveragingMixedAlgebra AveragingMixedLedgers
open AveragingDebtAlgebra AveragingDebtTransitions AveragingDebtService
open AveragingPotentialService AveragingTerminalDebt AveragingMajorityPartners
open AveragingChangingZeroTail AveragingServiceProbability AveragingStoppedDebtLaw

variable {L : ℕ}

open Classical in
structure XGate (σ : Sign) (k : ℕ) (Dstar : ℚ) (n C : ℕ)
    (c : Cfg L 256) : Prop where
  population : c.card = n
  domain : PotentialDomain c
  minority : minorityDebt σ k c ≤ Dstar
  clocks : C ≤ c.countP (ClockServiceSource k)

open Classical in
structure YGate (σ : Sign) (ell : ℕ) (xstar : ℚ) (n R : ℕ)
    (c : Cfg L 256) : Prop where
  population : c.card = n
  domain : PotentialDomain c
  first_debt : debtX σ (ell + 2) c ≤ xstar
  partners : R ≤ c.countP (NearMajority σ ell)

open Classical in
theorem exactZeroCount_eq_count (k : ℕ) (c : Cfg L 256)
    (hcap : ∀ a ∈ c, a.phase.val ≤ 3) :
    exactZeroCount k c = c.countP (TerminalZero k) := by
  classical
  revert hcap
  induction c using Multiset.induction_on with
  | empty => intro _; simp [exactZeroCount]
  | cons a c ih =>
      intro hcap
      have ha := hcap a (Multiset.mem_cons_self _ _)
      have ht := ih (fun b hb => hcap b (Multiset.mem_cons_of_mem hb))
      calc
        exactZeroCount k (a ::ₘ c) = exactZeroWeight k a + exactZeroCount k c := by
          simp [exactZeroCount]
        _ = (if TerminalZero k a then 1 else 0) + c.countP (TerminalZero k) := by
          rw [exactZeroWeight_eq_indicator k a ha, ht]
        _ = (a ::ₘ c).countP (TerminalZero k) := by
          rw [Multiset.countP_cons]
          omega

open Classical in
theorem nearMajorityCount_eq_count (σ : Sign) (ell : ℕ) (c : Cfg L 256)
    (hcap : ∀ a ∈ c, a.phase.val ≤ 3) :
    nearMajorityCount σ ell c = c.countP (NearMajority σ ell) := by
  classical
  revert hcap
  induction c using Multiset.induction_on with
  | empty => intro _; simp [nearMajorityCount]
  | cons a c ih =>
      intro hcap
      have ha := hcap a (Multiset.mem_cons_self _ _)
      have ht := ih (fun b hb => hcap b (Multiset.mem_cons_of_mem hb))
      calc
        nearMajorityCount σ ell (a ::ₘ c) =
            nearMajorityWeight σ ell a + nearMajorityCount σ ell c := by
          simp [nearMajorityCount]
        _ = (if NearMajority σ ell a then 1 else 0) +
            c.countP (NearMajority σ ell) := by
          rw [nearMajorityWeight_eq_indicator σ ell a ha, ht]
        _ = (a ::ₘ c).countP (NearMajority σ ell) := by
          rw [Multiset.countP_cons]
          omega

theorem debtX_draw_le (σ : Sign) (k : ℕ) (c : Cfg L 256)
    (hc : PotentialDomain c) (d : Draw L 256) (hd : PotentialDomain (applyDraw c d)) :
    debtX σ k (applyDraw c d) ≤ debtX σ k c := by
  have hcoeff := coefficients_nonneg σ k
  change totalDebt (positiveCoefficient σ k) (negativeCoefficient σ k) k
      (applyDraw c d) ≤ _
  apply totalDebt_draw _ _ k hcoeff.1 hcoeff.2 _ c d
    (fun a ha => (hc a ha).range) (fun a ha => (hc a ha).safe)
    (fun a ha => (hc a ha).small_carrier)
    (fun a ha => (hd a ha).range.2)
  rw [coefficients_sum]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (Nat.le_succ k)

theorem debtY_draw_le (σ : Sign) (k : ℕ) (c : Cfg L 256)
    (hc : PotentialDomain c) (d : Draw L 256) (hd : PotentialDomain (applyDraw c d)) :
    debtY σ k (applyDraw c d) ≤ debtY σ k c := by
  have hcoeff := coefficients_nonneg σ k
  change totalDebt (positiveCoefficient σ k) (negativeCoefficient σ k) (k + 1)
      (applyDraw c d) ≤ _
  exact totalDebt_draw _ _ (k + 1) hcoeff.1 hcoeff.2
    (le_of_eq (coefficients_sum σ k).symm) c d
    (fun a ha => (hc a ha).range) (fun a ha => (hc a ha).safe)
    (fun a ha => (hc a ha).small_carrier)
    (fun a ha => (hd a ha).range.2)

open Classical in
theorem debtX_ceil_le_targets (σ : Sign) (k : ℕ) (Dstar : ℚ)
    (n C : ℕ) (c : Cfg L 256) (hc : XGate σ k Dstar n C c) :
    Nat.ceil (debtX σ k c - 2 * Dstar) ≤ c.countP (ClockServiceTarget k) := by
  apply Nat.ceil_le.mpr
  rw [clockTarget_count]
  exact (le_max_left _ _).trans (debtX_service_floor σ k c Dstar hc.minority)

open Classical in
theorem debtY_ceil_le_targets (σ : Sign) (ell : ℕ) (xstar : ℚ)
    (n R : ℕ) (c : Cfg L 256) (hc : YGate σ ell xstar n R c) :
    Nat.ceil (debtY σ (ell + 2) c - xstar) ≤ c.countP (TerminalZero (ell + 2)) := by
  apply Nat.ceil_le.mpr
  rw [← exactZeroCount_eq_count (ell + 2) c (fun a ha => (hc.domain a ha).range.2)]
  exact (le_max_left _ _).trans
    (debtY_service_floor σ (ell + 2) c xstar hc.first_debt)

open Classical in
/-- The gap/potential theorem supplies the actual Y partner-count gate. -/
theorem yGate_of_gap_and_phi (σ : Sign) (ell : ℕ) (xstar gap : ℚ)
    (n R M : ℕ) (c : Cfg L 256)
    (hpop : c.card = n) (hc : PotentialDomain c)
    (hX : debtX σ (ell + 2) c ≤ xstar)
    (hell : 1 ≤ ell) (hM : RoleSplitConcentration.mainCount c = M)
    (hsigned : prePhase4MassSum c = if σ = .pos then gap else -gap)
    (hscale : (2 / 5 : ℚ) * M ≤ (2 : ℚ) ^ ell * gap)
    (hphi : augmentedPhi ell c ≤ (1 / 1000 : ℚ) * M)
    (hR : 100 * R ≤ 19 * M) :
    YGate σ ell xstar n R c := by
  have hcarrier : ∀ a ∈ c, ¬ a.phase.val < 3 → a.role ≠ .main → a.bias = .zero := by
    intro a ha hp hm
    have hphase : a.phase.val = 3 := by
      have hr := (hc a ha).range
      omega
    exact (hc a ha).active_carrier hphase hm
  have hfloor := majority_partner_floor_of_gap_and_phi σ ell M c gap hell hM
    hcarrier hsigned hscale hphi
  rw [nearMajorityCount_eq_count σ ell c (fun a ha => (hc a ha).range.2)] at hfloor
  exact ⟨hpop, hc, hX, by omega⟩

open Classical in
theorem rate_from_rectangle (n R J : ℕ) (c : Cfg L 256)
    (hn : 2 ≤ n) (hpop : c.card = n)
    (P Q : AgentState L 256 → Prop) (E : Cfg L 256 → Prop)
    (hJ : J ≤ c.countP P) (hR : R ≤ c.countP Q)
    (hdisjoint : ∀ a, P a → ¬ Q a)
    (hservice : ∀ s t, Protocol.Applicable c s t →
      (P s ∧ Q t) ∨ (Q s ∧ P t) →
      E (Protocol.stepOrSelf (NonuniformMajority L 256) c s t)) :
    clockDeathRate n R * J ≤
      ∫ d, (if E (applyDraw c d) then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure := by
  have htotal : c.totalPairs = n * (n - 1) := by
    simp only [Config.totalPairs, hpop]
  calc
    clockDeathRate n R * J =
        (2 * (J : ℝ) * (R : ℝ)) / (c.totalPairs : ℝ) := by
      rw [htotal]
      unfold clockDeathRate
      ring
    _ ≤ (2 * (c.countP P : ℝ) * (c.countP Q : ℝ)) / (c.totalPairs : ℝ) := by
      gcongr <;> first | exact_mod_cast hJ | exact_mod_cast hR
    _ ≤ _ := service_rectangle_real c (by rw [hpop]; exact hn)
      P Q E hdisjoint hservice

open Classical in
/-- The first stopped drain uses both orientations of the Clock rectangle. -/
theorem debtX_service_probability (σ : Sign) (k : ℕ) (hk : k ≤ L)
    (Dstar : ℚ) (n C : ℕ) (hn : 2 ≤ n)
    (c : Cfg L 256) (hc : XGate σ k Dstar n C c) :
    clockDeathRate n C * (Nat.ceil (debtX σ k c - 2 * Dstar) : ℝ) ≤
      ∫ d, (if ¬ XGate σ k Dstar n C (applyDraw c d) ∨
          debtX σ k (applyDraw c d) + 1 ≤ debtX σ k c
        then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure := by
  have hserv : ∀ s t, Protocol.Applicable c s t →
      (ClockServiceTarget k s ∧ ClockServiceSource k t) ∨
        (ClockServiceSource k s ∧ ClockServiceTarget k t) →
      (fun c' : Cfg L 256 => ¬ XGate σ k Dstar n C c' ∨
          debtX σ k c' + 1 ≤ debtX σ k c)
        (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) := by
    intro s t happ hrect
    apply Or.inr
    have hs : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : t ∈ c := Multiset.mem_of_le happ (by simp)
    apply le_of_eq
    apply totalDebt_step_service _ _ k c s t happ
    rcases hrect with hforward | hreverse
    · exact transition_clock_service_left _ _ k hk s t
        (hc.domain s hs).range (hc.domain s hs).safe hforward.1 hforward.2
    · exact transition_clock_service_right _ _ k hk s t
        (hc.domain t ht).range (hc.domain t ht).safe hreverse.1 hreverse.2
  have key := rate_from_rectangle n C ⌈debtX σ k c - 2 * Dstar⌉₊ c hn hc.population
    (ClockServiceTarget k) (ClockServiceSource k)
    (fun c' : Cfg L 256 => ¬ XGate σ k Dstar n C c' ∨
      debtX σ k c' + 1 ≤ debtX σ k c)
    (debtX_ceil_le_targets σ k Dstar n C c hc) hc.clocks (clockTarget_disjoint k) hserv
  convert key

open Classical in
/-- The second drain uses the true exact-hour-zero count, with the actual
two-index majority partner set. No hour-selection independence is needed. -/
theorem debtY_service_probability (σ : Sign) (ell : ℕ) (xstar : ℚ)
    (n R : ℕ) (hn : 2 ≤ n) (c : Cfg L 256) (hc : YGate σ ell xstar n R c) :
    clockDeathRate n R * (Nat.ceil (debtY σ (ell + 2) c - xstar) : ℝ) ≤
      ∫ d, (if ¬ YGate σ ell xstar n R (applyDraw c d) ∨
          debtY σ (ell + 2) (applyDraw c d) + 1 ≤ debtY σ (ell + 2) c
        then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure := by
  have hdis : ∀ a : AgentState L 256, TerminalZero (ell + 2) a → ¬ NearMajority σ ell a := by
    intro a ha hb
    exact terminalZero_ne_nearMajority σ ell a a ha hb rfl
  have hserv : ∀ s t, Protocol.Applicable c s t →
      (TerminalZero (ell + 2) s ∧ NearMajority σ ell t) ∨
        (NearMajority σ ell s ∧ TerminalZero (ell + 2) t) →
      (fun c' : Cfg L 256 => ¬ YGate σ ell xstar n R c' ∨
          debtY σ (ell + 2) c' + 1 ≤ debtY σ (ell + 2) c)
        (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) := by
    intro s t happ hrect
    apply Or.inr
    rcases hrect with hforward | hreverse
    · exact (debtY_step_service_left σ ell c s t happ hforward.1 hforward.2).le
    · exact (debtY_step_service_right σ ell c s t happ hreverse.1 hreverse.2).le
  have key := rate_from_rectangle n R ⌈debtY σ (ell + 2) c - xstar⌉₊ c hn hc.population
    (TerminalZero (ell + 2)) (NearMajority σ ell)
    (fun c' : Cfg L 256 => ¬ YGate σ ell xstar n R c' ∨
      debtY σ (ell + 2) c' + 1 ≤ debtY σ (ell + 2) c)
    (debtY_ceil_le_targets σ ell xstar n R c hc) hc.partners hdis hserv
  convert key

theorem debtX_tail_from (init : Cfg L 256) (s : ℕ)
    (B : Set ((i : Finset.Iic s) → Draw L 256))
    (σ : Sign) (k : ℕ) (hk : k ≤ L) (Dstar : ℚ)
    (n C M : ℕ) (hn : 2 ≤ n) (hsize : 2 * C * M ≤ n * (n - 1))
    (a : ℝ) (T : ℕ) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ debtFailure init s (debtX σ k) (2 * Dstar) (XGate σ k Dstar n C) M a T} ≤
      ENNReal.ofReal
        (Real.exp ((7 * Real.exp (-clockDeathRate n C * T) - a * Real.log 8) * M)) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B} :=
  stoppedDebt_tail_from init s B (debtX σ k) (2 * Dstar) (XGate σ k Dstar n C)
    M (clockDeathRate n C) a (clockDeathRate_nonneg n C)
    (clockDeathRate_size_bound n C M hn hsize)
    (fun c hc d hd => debtX_draw_le σ k c hc.domain d hd.domain)
    (debtX_service_probability σ k hk Dstar n C hn) T

theorem debtY_tail_from (init : Cfg L 256) (s : ℕ)
    (B : Set ((i : Finset.Iic s) → Draw L 256))
    (σ : Sign) (ell : ℕ) (xstar : ℚ)
    (n R M : ℕ) (hn : 2 ≤ n) (hsize : 2 * R * M ≤ n * (n - 1))
    (a : ℝ) (T : ℕ) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ debtFailure init s (debtY σ (ell + 2)) xstar (YGate σ ell xstar n R) M a T} ≤
      ENNReal.ofReal
        (Real.exp ((7 * Real.exp (-clockDeathRate n R * T) - a * Real.log 8) * M)) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B} :=
  stoppedDebt_tail_from init s B (debtY σ (ell + 2)) xstar (YGate σ ell xstar n R)
    M (clockDeathRate n R) a (clockDeathRate_nonneg n R)
    (clockDeathRate_size_bound n R M hn hsize)
    (fun c hc d hd => debtY_draw_le σ (ell + 2) c hc.domain d hd.domain)
    (debtY_service_probability σ ell xstar n R hn) T

theorem debtX_tail_at_pastTime (init : Cfg L 256)
    (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ)
    (σ : Sign) (k : ℕ) (hk : k ≤ L) (Dstar : ℚ)
    (n C M : ℕ) (hn : 2 ≤ n) (hsize : 2 * C * M ≤ n * (n - 1))
    (a : ℝ) (T : ℕ) :
    law init {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
        ω ∈ debtFailure init s (debtX σ k) (2 * Dstar) (XGate σ k Dstar n C) M a T} ≤
      ENNReal.ofReal
        (Real.exp ((7 * Real.exp (-clockDeathRate n C * T) - a * Real.log 8) * M)) :=
  stoppedDebt_tail_at_pastTime init τ hτ (debtX σ k) (2 * Dstar) (XGate σ k Dstar n C)
    M (clockDeathRate n C) a (clockDeathRate_nonneg n C)
    (clockDeathRate_size_bound n C M hn hsize)
    (fun c hc d hd => debtX_draw_le σ k c hc.domain d hd.domain)
    (debtX_service_probability σ k hk Dstar n C hn) T

theorem debtY_tail_at_pastTime (init : Cfg L 256)
    (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ)
    (σ : Sign) (ell : ℕ) (xstar : ℚ)
    (n R M : ℕ) (hn : 2 ≤ n) (hsize : 2 * R * M ≤ n * (n - 1))
    (a : ℝ) (T : ℕ) :
    law init {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
        ω ∈ debtFailure init s (debtY σ (ell + 2)) xstar (YGate σ ell xstar n R) M a T} ≤
      ENNReal.ofReal
        (Real.exp ((7 * Real.exp (-clockDeathRate n R * T) - a * Real.log 8) * M)) :=
  stoppedDebt_tail_at_pastTime init τ hτ (debtY σ (ell + 2)) xstar (YGate σ ell xstar n R)
    M (clockDeathRate n R) a (clockDeathRate_nonneg n R)
    (clockDeathRate_size_bound n R M hn hsize)
    (fun c hc d hd => debtY_draw_le σ (ell + 2) c hc.domain d hd.domain)
    (debtY_service_probability σ ell xstar n R hn) T

end Ripple.PopulationProtocol.ExactMajority.AveragingTerminalDebtTails

end
