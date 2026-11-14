-- Ripple/PopulationProtocol/ExactMajority/Probability/LateTwoLevelService.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedMixedPositive
import Ripple.PopulationProtocol.ExactMajority.Probability.LateTwoLevelWarmup
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedTwoLevelArithmetic
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedNonlinearService

/-!
# Actual two-level nonlinear service

The integer positive-part minimum uses the pending-aware majority process
and the compiled changing-zero/minority debt. The useful ordered rectangle
is precisely an active majority at index ell and an active zero at hour
ell+1. Both orientations remove one from each process.

The final tails use first-gate killing, the original scheduler law, and
arbitrary recorded prefixes or genuine pair-log stopping times. The role
density upper bound is retained in the geometric-parameter envelope.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.LateStrengthening

open TimeTheorem PairLog PhaseOneDrain
open AveragingMixedLedgers AveragingTerminalDebt AveragingDebtService
open AveragingPotentialService AveragingLiveProduct AveragingMajorityPartners
open AveragingTerminalDebtTails AveragingStoppedDebt

variable {L : ℕ}

def twoLevelIndex (σ : Sign) (ell M : ℕ) (c : Cfg L 256) : ℕ :=
  twoLevelBarrier M (mixedShallowPositiveNat σ ell c) (twoLevelDebt σ ell c)

structure TwoLevelServiceGate (σ : Sign) (j : Fin (L + 1)) (n M : ℕ)
    (c : Cfg L 256) : Prop where
  population : c.card = n
  domain : PotentialDomain c
  main_count : RoleSplitConcentration.mainCount c = M
  potential : augmentedPhi j.val c ≤ (1 / 1000 : ℚ) * M
  lower_debt : lowerHourDebt σ j.val c ≤ (9 / 500 : ℚ) * M

theorem twoLevelBarrier_mono (M X X' : ℕ) (Y Y' : ℚ)
    (hX : X' ≤ X) (hY : Y' ≤ Y) :
    twoLevelBarrier M X' Y' ≤ twoLevelBarrier M X Y := by
  have hf := Nat.floor_mono hY
  unfold twoLevelBarrier
  omega

theorem twoLevelBarrier_drop (M X X' : ℕ) (Y Y' : ℚ)
    (hY' : 0 ≤ Y') (hX : X' + 1 = X) (hY : Y' + 1 = Y)
    (hpos : 0 < twoLevelBarrier M X Y) :
    twoLevelBarrier M X' Y' + 1 ≤ twoLevelBarrier M X Y := by
  have hf : (Nat.floor Y' : ℚ) ≤ Y' := Nat.floor_le hY'
  have hq : ((Nat.floor Y' + 1 : ℕ) : ℚ) ≤ Y := by
    push_cast
    linarith only [hf, hY]
  have hfloor : Nat.floor Y' + 1 ≤ Nat.floor Y := by
    simpa only [Nat.floor_natCast] using Nat.floor_mono hq
  unfold twoLevelBarrier at hpos ⊢
  omega

theorem twoLevelIndex_draw_le (σ : Sign) (ell M : ℕ)
    (c : Cfg L 256) (hc : PotentialDomain c) (d : Draw L 256)
    (hd : PotentialDomain (applyDraw c d)) :
    twoLevelIndex σ ell M (applyDraw c d) ≤ twoLevelIndex σ ell M c := by
  have hx := mixedShallowPositive_draw σ ell c d
    (fun a ha => (hc a ha).range)
    (fun a ha => (hc a ha).safe)
    (fun a ha => (hc a ha).small_carrier)
    (fun a ha => (hd a ha).range.2)
  rw [mixedShallowPositive_eq_nat σ ell _ (fun a ha => (hd a ha).safe),
    mixedShallowPositive_eq_nat σ ell _ (fun a ha => (hc a ha).safe)] at hx
  have hxn : mixedShallowPositiveNat σ ell (applyDraw c d) ≤
      mixedShallowPositiveNat σ ell c := by exact_mod_cast hx
  exact twoLevelBarrier_mono M _ _ _ _ hxn
    (debtY_draw_le σ (ell + 1) c hc d hd)

theorem twoLevelIndex_le_majority_count
    (σ : Sign) (j : Fin (L + 1)) (hj : 1 ≤ j.val) (n M : ℕ)
    (c : Cfg L 256) (hc : TwoLevelServiceGate σ j n M c) :
    twoLevelIndex σ j.val M c ≤ levelCount σ j c := by
  have hx := mixedShallowPositive_service_floor σ j hj M c
    (fun a ha => (hc.domain a ha).range.2) hc.potential
  rw [mixedShallowPositive_eq_nat σ j.val c
    (fun a ha => (hc.domain a ha).safe)] at hx
  have hb : (1 / 500 : ℚ) * M ≤ (Nat.ceil ((1 / 500 : ℚ) * M) : ℚ) :=
    Nat.le_ceil _
  have hq : (mixedShallowPositiveNat σ j.val c : ℚ) ≤
      (Nat.ceil ((1 / 500 : ℚ) * M) : ℚ) + levelCount σ j c := by
    linarith only [hx, hb]
  have hn : mixedShallowPositiveNat σ j.val c ≤
      Nat.ceil ((1 / 500 : ℚ) * M) + levelCount σ j c := by exact_mod_cast hq
  unfold twoLevelIndex twoLevelBarrier
  omega

theorem twoLevelIndex_le_zero_count
    (σ : Sign) (ell M : ℕ) (c : Cfg L 256)
    (hlower : lowerHourDebt σ ell c ≤ (9 / 500 : ℚ) * M) :
    twoLevelIndex σ ell M c ≤ exactZeroCount (ell + 1) c :=
  (min_le_right _ _).trans
    (twoLevelDebt_floor_excess_le_zero σ ell M c hlower)

theorem twoLevelIndex_le_main_count
    (σ : Sign) (ell M : ℕ) (c : Cfg L 256)
    (hlower : lowerHourDebt σ ell c ≤ (9 / 500 : ℚ) * M) :
    twoLevelIndex σ ell M c ≤ RoleSplitConcentration.mainCount c := by
  have hj := twoLevelIndex_le_zero_count σ ell M c hlower
  have hs := lowHourZeroCount_succ (ell + 1) c
  have hm := clock_targets_le_mainCount (ell + 1 + 1) c
  omega

theorem twoLevelIndex_le_main
    (σ : Sign) (j : Fin (L + 1)) (n M : ℕ)
    (c : Cfg L 256) (hc : TwoLevelServiceGate σ j n M c) :
    twoLevelIndex σ j.val M c ≤ M := by
  simpa only [hc.main_count] using
    twoLevelIndex_le_main_count σ j.val M c hc.lower_debt

theorem twoLevelDebt_step_split_left
    (σ : Sign) (j : Fin (L + 1)) (c : Cfg L 256) (s t : AgentState L 256)
    (happ : Protocol.Applicable c s t)
    (hs : TerminalZero (j.val + 1) s) (ht : AtLevel σ j t) :
    twoLevelDebt σ j.val (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) + 1 =
      twoLevelDebt σ j.val c := by
  exact totalDebt_step_service _ _ (j.val + 1 + 1) c s t happ
    (transition_split_service_left _ _ (j.val + 1 + 1) s t σ j
      hs.1 ht.1 hs.2.1 ht.2.1 hs.2.2.1 ht.2.2
      (by rw [hs.2.2.2]; omega) (by rw [hs.2.2.2]; omega))

theorem twoLevelDebt_step_split_right
    (σ : Sign) (j : Fin (L + 1)) (c : Cfg L 256) (s t : AgentState L 256)
    (happ : Protocol.Applicable c s t)
    (hs : AtLevel σ j s) (ht : TerminalZero (j.val + 1) t) :
    twoLevelDebt σ j.val (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) + 1 =
      twoLevelDebt σ j.val c := by
  exact totalDebt_step_service _ _ (j.val + 1 + 1) c s t happ
    (transition_split_service_right _ _ (j.val + 1 + 1) s t σ j
      hs.1 ht.1 hs.2.1 ht.2.1 hs.2.2 ht.2.2.1
      (by rw [ht.2.2.2]; omega) (by rw [ht.2.2.2]; omega))

theorem twoLevelIndex_step_split_left
    (σ : Sign) (j : Fin (L + 1)) (M : ℕ) (c : Cfg L 256)
    (s t : AgentState L 256) (happ : Protocol.Applicable c s t)
    (hc : PotentialDomain c)
    (hd : PotentialDomain (Protocol.stepOrSelf (NonuniformMajority L 256) c s t))
    (hs : TerminalZero (j.val + 1) s) (ht : AtLevel σ j t)
    (hpos : 0 < twoLevelIndex σ j.val M c) :
    twoLevelIndex σ j.val M (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) + 1 ≤
      twoLevelIndex σ j.val M c := by
  have hx := mixedShallowPositiveNat_step_split_drop_left σ j.val c s t j happ
    hs.1 ht.1 hs.2.1 ht.2.1 hs.2.2.1 ht.2.2 rfl
    (by rw [hs.2.2.2]; omega)
    (fun a ha => (hc a ha).safe) (fun a ha => (hd a ha).safe)
  have hy := twoLevelDebt_step_split_left σ j c s t happ hs ht
  exact twoLevelBarrier_drop M _ _ _ _ (twoLevelDebt_nonneg σ j.val _) hx hy hpos

theorem twoLevelIndex_step_split_right
    (σ : Sign) (j : Fin (L + 1)) (M : ℕ) (c : Cfg L 256)
    (s t : AgentState L 256) (happ : Protocol.Applicable c s t)
    (hc : PotentialDomain c)
    (hd : PotentialDomain (Protocol.stepOrSelf (NonuniformMajority L 256) c s t))
    (hs : AtLevel σ j s) (ht : TerminalZero (j.val + 1) t)
    (hpos : 0 < twoLevelIndex σ j.val M c) :
    twoLevelIndex σ j.val M (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) + 1 ≤
      twoLevelIndex σ j.val M c := by
  have hx := mixedShallowPositiveNat_step_split_drop σ j.val c s t j happ
    hs.1 ht.1 hs.2.1 ht.2.1 hs.2.2 ht.2.2.1 rfl
    (by rw [ht.2.2.2]; omega)
    (fun a ha => (hc a ha).safe) (fun a ha => (hd a ha).safe)
  have hy := twoLevelDebt_step_split_right σ j c s t happ hs ht
  exact twoLevelBarrier_drop M _ _ _ _ (twoLevelDebt_nonneg σ j.val _) hx hy hpos

open Classical in
/-- The current physical-label scheduler supplies 2 J^2 / (n(n-1)).
A gate failure is charged on its first sampled transition. -/
theorem twoLevelIndex_service_probability
    (σ : Sign) (j : Fin (L + 1)) (hj : 1 ≤ j.val)
    (n M : ℕ) (hn : 2 ≤ n) (c : Cfg L 256)
    (hc : TwoLevelServiceGate σ j n M c) :
    nonlinearServiceRate ((n : ℝ) * ((n : ℝ) - 1)) (twoLevelIndex σ j.val M c) ≤
      ∫ d, (if ¬ TwoLevelServiceGate σ j n M (applyDraw c d) ∨
          (twoLevelIndex σ j.val M (applyDraw c d) : ℚ) + 1 ≤ twoLevelIndex σ j.val M c
        then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure := by
  classical
  by_cases hpos : 0 < twoLevelIndex σ j.val M c
  · have hP : twoLevelIndex σ j.val M c ≤ c.countP (TerminalZero (j.val + 1)) := by
      rw [← exactZeroCount_eq_count (j.val + 1) c
        (fun a ha => (hc.domain a ha).range.2)]
      exact twoLevelIndex_le_zero_count σ j.val M c hc.lower_debt
    have hQ : twoLevelIndex σ j.val M c ≤ c.countP (AtLevel σ j) :=
      twoLevelIndex_le_majority_count σ j hj n M c hc
    have hdis : ∀ a : AgentState L 256, TerminalZero (j.val + 1) a → ¬ AtLevel σ j a := by
      intro a ha hb
      have he := hb.2.2
      rw [ha.2.2.1] at he
      cases he
    have hservice : ∀ s t, Protocol.Applicable c s t →
        (TerminalZero (j.val + 1) s ∧ AtLevel σ j t) ∨
          (AtLevel σ j s ∧ TerminalZero (j.val + 1) t) →
        (fun c' : Cfg L 256 => ¬ TwoLevelServiceGate σ j n M c' ∨
          (twoLevelIndex σ j.val M c' : ℚ) + 1 ≤ twoLevelIndex σ j.val M c)
          (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) := by
      intro s t happ hrect
      by_cases hd : TwoLevelServiceGate σ j n M
          (Protocol.stepOrSelf (NonuniformMajority L 256) c s t)
      · apply Or.inr
        have hdrop : twoLevelIndex σ j.val M
            (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) + 1 ≤
            twoLevelIndex σ j.val M c := by
          rcases hrect with hforward | hreverse
          · exact twoLevelIndex_step_split_left σ j M c s t happ hc.domain hd.domain
              hforward.1 hforward.2 hpos
          · exact twoLevelIndex_step_split_right σ j M c s t happ hc.domain hd.domain
              hreverse.1 hreverse.2 hpos
        exact_mod_cast hdrop
      · exact Or.inl hd
    convert nonlinear_service_rectangle n (twoLevelIndex σ j.val M c) c hn hc.population
      (TerminalZero (j.val + 1)) (AtLevel σ j)
      (fun c' : Cfg L 256 => ¬ TwoLevelServiceGate σ j n M c' ∨
        (twoLevelIndex σ j.val M c' : ℚ) + 1 ≤ twoLevelIndex σ j.val M c)
      hP hQ hdis hservice
  · have hz : twoLevelIndex σ j.val M c = 0 := by omega
    rw [hz]
    simp only [nonlinearServiceRate, Nat.cast_zero,
      zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div]
    exact integral_nonneg fun d => by split_ifs <;> norm_num

def twoLevelServiceFailure (init : Cfg L 256) (s : ℕ)
    (σ : Sign) (j : Fin (L + 1)) (n M : ℕ) : Set (Ω L 256) :=
  {ω | (∀ u, u ≤ twoLevelTrials n M →
      TwoLevelServiceGate σ j n M (trace init ω (s + u))) ∧
    twoLevelTarget M <
      twoLevelIndex σ j.val M (trace init ω (s + twoLevelTrials n M))}

theorem twoLevelService_failure_subset (init : Cfg L 256) (s : ℕ)
    (σ : Sign) (j : Fin (L + 1)) (n M : ℕ) :
    twoLevelServiceFailure init s σ j n M ⊆
      nonlinearDebtFailure init s (fun c => (twoLevelIndex σ j.val M c : ℚ)) 0
        (TwoLevelServiceGate σ j n M) M (twoLevelTarget M) (twoLevelTrials n M) := by
  rintro ω ⟨hwindow, hbad⟩
  have hstart := hwindow 0 (Nat.zero_le _)
  simp only [Nat.add_zero] at hstart
  refine ⟨⟨?_, hwindow⟩, ?_⟩
  · simpa only [sub_zero, Nat.ceil_natCast] using
      twoLevelIndex_le_main σ j n M (trace init ω s) hstart
  · simpa only [sub_zero, Nat.ceil_natCast] using hbad

open Classical in
theorem twoLevelService_tail_from (init : Cfg L 256) (s : ℕ)
    (B : Set ((i : Finset.Iic s) → Draw L 256))
    (σ : Sign) (j : Fin (L + 1)) (hj : 1 ≤ j.val)
    (n M : ℕ) (hn : 3 ≤ n) (hM : 0 < M) (hrole : 25 * M ≤ 13 * n) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ twoLevelServiceFailure init s σ j n M} ≤
      ENNReal.ofReal (Real.exp (-(twoLevelTarget M : ℝ) / 6)) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B} := by
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : 0 < (n : ℝ) * ((n : ℝ) - 1) :=
    mul_pos (by linarith only [hnreal]) (by linarith only [hnreal])
  have hmono : ∀ c, TwoLevelServiceGate σ j n M c → ∀ d,
      TwoLevelServiceGate σ j n M (applyDraw c d) →
        (twoLevelIndex σ j.val M (applyDraw c d) : ℚ) ≤ twoLevelIndex σ j.val M c := by
    intro c hc d hd
    exact_mod_cast twoLevelIndex_draw_le σ j.val M c hc.domain d hd.domain
  have hservice : ∀ c, TwoLevelServiceGate σ j n M c →
      nonlinearServiceRate ((n : ℝ) * ((n : ℝ) - 1))
          (Nat.ceil ((twoLevelIndex σ j.val M c : ℚ) - 0)) ≤
        ∫ d, (if ¬ TwoLevelServiceGate σ j n M (applyDraw c d) ∨
            (twoLevelIndex σ j.val M (applyDraw c d) : ℚ) + 1 ≤ twoLevelIndex σ j.val M c
          then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure := by
    intro c hc
    simpa only [sub_zero, Nat.ceil_natCast] using
      twoLevelIndex_service_probability σ j hj n M (by omega) c hc
  have htail := nonlinear_service_tail_from init s B
    (fun c => (twoLevelIndex σ j.val M c : ℚ)) 0 (TwoLevelServiceGate σ j n M)
    M (twoLevelTarget M) ((n : ℝ) * ((n : ℝ) - 1)) hN
    (twoLevelTarget_pos hM) (twoLevelTarget_le M)
    (nonlinear_role_density_cap n M hn hrole) hmono hservice
    (twoLevelTrials n M) (twoLevelTrials_deadline n M)
  refine (measure_mono ?_).trans htail
  rintro ω ⟨hp, hf⟩
  exact ⟨hp, twoLevelService_failure_subset init s σ j n M hf⟩

open Classical in
theorem twoLevelService_tail_at_pastTime (init : Cfg L 256)
    (τ : Ω L 256 → WithTop ℕ) (hτ : PairLogPastTime τ)
    (σ : Sign) (j : Fin (L + 1)) (hj : 1 ≤ j.val)
    (n M : ℕ) (hn : 3 ≤ n) (hM : 0 < M) (hrole : 25 * M ≤ 13 * n) :
    law init {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
        ω ∈ twoLevelServiceFailure init s σ j n M} ≤
      ENNReal.ofReal (Real.exp (-(twoLevelTarget M : ℝ) / 6)) := by
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : 0 < (n : ℝ) * ((n : ℝ) - 1) :=
    mul_pos (by linarith only [hnreal]) (by linarith only [hnreal])
  have hmono : ∀ c, TwoLevelServiceGate σ j n M c → ∀ d,
      TwoLevelServiceGate σ j n M (applyDraw c d) →
        (twoLevelIndex σ j.val M (applyDraw c d) : ℚ) ≤ twoLevelIndex σ j.val M c := by
    intro c hc d hd
    exact_mod_cast twoLevelIndex_draw_le σ j.val M c hc.domain d hd.domain
  have hservice : ∀ c, TwoLevelServiceGate σ j n M c →
      nonlinearServiceRate ((n : ℝ) * ((n : ℝ) - 1))
          (Nat.ceil ((twoLevelIndex σ j.val M c : ℚ) - 0)) ≤
        ∫ d, (if ¬ TwoLevelServiceGate σ j n M (applyDraw c d) ∨
            (twoLevelIndex σ j.val M (applyDraw c d) : ℚ) + 1 ≤ twoLevelIndex σ j.val M c
          then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure := by
    intro c hc
    simpa only [sub_zero, Nat.ceil_natCast] using
      twoLevelIndex_service_probability σ j hj n M (by omega) c hc
  have htail := nonlinear_service_tail_at_pastTime init τ hτ
    (fun c => (twoLevelIndex σ j.val M c : ℚ)) 0 (TwoLevelServiceGate σ j n M)
    M (twoLevelTarget M) ((n : ℝ) * ((n : ℝ) - 1)) hN
    (twoLevelTarget_pos hM) (twoLevelTarget_le M)
    (nonlinear_role_density_cap n M hn hrole) hmono hservice
    (twoLevelTrials n M) (twoLevelTrials_deadline n M)
  refine (measure_mono ?_).trans htail
  rintro ω ⟨s, hs, hf⟩
  exact ⟨s, hs, twoLevelService_failure_subset init s σ j n M hf⟩


/-- The actual first-barrier-stopped integer J. The generic initial cap is
redundant here because every live service gate already implies J ≤ M. -/
def stoppedTwoLevelIndex (init : Cfg L 256) (s : ℕ)
    (σ : Sign) (j : Fin (L + 1)) (n M t : ℕ) (ω : Ω L 256) : ℕ :=
  stoppedDebt init s (fun c => (twoLevelIndex σ j.val M c : ℚ)) 0
    (TwoLevelServiceGate σ j n M) M t ω

open Classical in
theorem stoppedTwoLevelIndex_eq (init : Cfg L 256) (s : ℕ)
    (σ : Sign) (j : Fin (L + 1)) (n M t : ℕ) (ω : Ω L 256) :
    stoppedTwoLevelIndex init s σ j n M t ω =
      if ∀ u, u ≤ t → TwoLevelServiceGate σ j n M (trace init ω (s + u))
      then twoLevelIndex σ j.val M (trace init ω (s + t)) else 0 := by
  classical
  by_cases hw : ∀ u, u ≤ t → TwoLevelServiceGate σ j n M (trace init ω (s + u))
  · have hstart := hw 0 (Nat.zero_le _)
    simp only [Nat.add_zero] at hstart
    have hlive : DebtLive init s (fun c => (twoLevelIndex σ j.val M c : ℚ)) 0
        (TwoLevelServiceGate σ j n M) M t ω := by
      refine ⟨?_, hw⟩
      simpa only [sub_zero, Nat.ceil_natCast] using
        twoLevelIndex_le_main σ j n M (trace init ω s) hstart
    simp only [stoppedTwoLevelIndex, stoppedDebt, if_pos hlive, if_pos hw,
      sub_zero, Nat.ceil_natCast]
  · have hlive : ¬ DebtLive init s (fun c => (twoLevelIndex σ j.val M c : ℚ)) 0
        (TwoLevelServiceGate σ j n M) M t ω := fun h => hw h.2
    simp only [stoppedTwoLevelIndex, stoppedDebt, if_neg hlive, if_neg hw]

theorem stoppedTwoLevelIndex_stronglyMeasurable
    (init : Cfg L 256) (s : ℕ) (σ : Sign) (j : Fin (L + 1))
    (n M t : ℕ) :
    StronglyMeasurable[AveragingRecordedExpectation.shiftedPairLog L 256 s t]
      (stoppedTwoLevelIndex init s σ j n M t) :=
  stoppedDebt_stronglyMeasurable init s
    (fun c => (twoLevelIndex σ j.val M c : ℚ)) 0 (TwoLevelServiceGate σ j n M) M t

theorem stoppedTwoLevelIndex_mono (init : Cfg L 256) (s : ℕ)
    (σ : Sign) (j : Fin (L + 1)) (n M t : ℕ) (ω : Ω L 256) :
    stoppedTwoLevelIndex init s σ j n M (t + 1) ω ≤
      stoppedTwoLevelIndex init s σ j n M t ω := by
  apply stoppedDebt_mono
  intro c hc d hd
  exact_mod_cast twoLevelIndex_draw_le σ j.val M c hc.domain d hd.domain

theorem stoppedTwoLevelIndex_le (init : Cfg L 256) (s : ℕ)
    (σ : Sign) (j : Fin (L + 1)) (n M t : ℕ) (ω : Ω L 256) :
    stoppedTwoLevelIndex init s σ j n M t ω ≤ M := by
  apply stoppedDebt_le
  intro c hc d hd
  exact_mod_cast twoLevelIndex_draw_le σ j.val M c hc.domain d hd.domain

end Ripple.PopulationProtocol.ExactMajority.LateStrengthening

end
