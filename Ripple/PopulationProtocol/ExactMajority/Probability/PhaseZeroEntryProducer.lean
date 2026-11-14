-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseZeroEntryProducer.lean
/-
Compiler repairs for the Phase-0 entry producer.

The fixed role deadline is 80001*n + logWindow n 20.
The final horizon and error are 350*n*clockHours n and ofReal (8/n^3).
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseZeroRoles
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneDrainProducer
import Ripple.PopulationProtocol.ExactMajority.Probability.RectangleDriftIdentity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal NNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseZeroEntryProducer

open TimeTheorem PairLog PairLogAuxiliary PhaseZeroEntry RoleSplitConcentration
open PhaseThreeModel.OccurrenceScheduler

variable {L K : ℕ}

/-! ## Profile-to-drain bridge -/

theorem centredBiasSum_eq_mainSmallBiasSum {L K : ℕ} (c : Cfg L K) :
    AveragingRate.centredBiasSum c = mainSmallBiasSum c := by
  unfold AveragingRate.centredBiasSum mainSmallBiasSum
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro a _
  by_cases hm : a.role = .main <;>
    simp [AveragingRate.biasZ, AgentState.smallBiasInt, hm]

theorem phaseOneDrainEntry_of_profile {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (ω : InputLog n) (s : ℕ)
    (hprofile : PhaseOneEntryProfile init ω s)
    (hsmall :
      40 * (initialGap init).natAbs ≤ mainCount (trace init ω s)) :
    PhaseOneDrain.PhaseOneDrainEntry n (initialGap init) (trace init ω s) := by
  have hcard : (trace init ω s).card = n :=
    (Protocol.reachable_card_eq
      (phase_zero_trace_reachable init ω s)).trans hinput.2.2
  refine ⟨⟨hcard, hprofile.all_one⟩, hprofile.final_roles,
    ?_, ?_, ?_, ?_, ?_, hprofile.nonmain_zero, ?_, hsmall⟩
  · have hreal :
        (99 : ℝ) * (n : ℝ) ≤
          200 * (mainCount (trace init ω s) : ℝ) := by
      linarith only [hprofile.main_lower]
    exact_mod_cast hreal
  · have hreal :
        (200 : ℝ) * (mainCount (trace init ω s) : ℝ) ≤
          101 * (n : ℝ) := by
      linarith only [hprofile.main_upper]
    exact_mod_cast hreal
  · have hreal :
        (97 : ℝ) * (n : ℝ) ≤
          400 * (clockCount (trace init ω s) : ℝ) := by
      linarith only [hprofile.clock_lower]
    exact_mod_cast hreal
  · have hreal :
        (97 : ℝ) * (n : ℝ) ≤
          400 * (reserveCount (trace init ω s) : ℝ) := by
      linarith only [hprofile.reserve_lower]
    exact_mod_cast hreal
  · intro a ha hclock
    simpa only [PhaseThreeModel.Numeric.clockHours] using
      hprofile.clock_counter a ha hclock
  · exact (centredBiasSum_eq_mainSmallBiasSum _).trans hprofile.main_mass

/-! ## CR clearance from a genuine prefix event -/

theorem cr_rate_floor {n q : ℕ} (hn : 200 ≤ n) (hq : n / 100 < q) :
    (1 / 20000 : ℝ) ≤
      (((q * (q - 1) : ℕ) : ℝ) /
        ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hnq : n ≤ 100 * q := by omega
  have hnprev : n ≤ 200 * (q - 1) := by omega
  have hprod := Nat.mul_le_mul hnq hnprev
  have hsmall := Nat.mul_le_mul_left n (Nat.sub_le n 1)
  have hnat : n * (n - 1) ≤ 20000 * (q * (q - 1)) := by
    nlinarith only [hprod, hsmall]
  have hnR : (200 : ℝ) ≤ n := by exact_mod_cast hn
  have hnOne : 1 ≤ n := by omega
  have hden : 0 < (n : ℝ) * ((n : ℝ) - 1) :=
    mul_pos (by linarith only [hnR]) (by linarith only [hnR])
  have hcast :
      (((n * (n - 1) : ℕ) : ℝ)) ≤
        (((20000 * (q * (q - 1)) : ℕ) : ℝ)) := by
    exact_mod_cast hnat
  have hreal :
      (n : ℝ) * ((n : ℝ) - 1) ≤
        20000 * (((q * (q - 1) : ℕ) : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_sub hnOne,
      Nat.cast_one, Nat.cast_ofNat] using hcast
  apply (le_div_iff₀ hden).2
  linarith only [hreal]

/-- The uniform floor also holds in the original conditional-expectation
interface. The explicit bridge keeps the imported classical indicator and the
ordinary decidable indicator from being identified by instance reduction. -/
theorem cr_conditional_rate_floor {n : ℕ}
    (init : Cfg L K) (hn : 200 ≤ n) (hcard : init.card = n) (t : ℕ) :
    ∀ᵐ ω ∂law init,
      Phase0Window.allPhase0 (trace init ω t) →
      n / 100 < crCount (trace init ω t) →
      (1 / 20000 : ℝ) ≤
        (law init)[fun ω =>
          if crCount (trace init ω (t + 1)) < crCount (trace init ω t)
          then (1 : ℝ) else 0 | pairLogFiltration L K t] ω := by
  have hc : 2 ≤ init.card := by omega
  have hcond := phase_zero_cr_conditional_decrease init hc t
  have hcond' := Filter.EventuallyLE.trans_eq hcond
    (show _ =ᵐ[law init]
      (law init)[fun ω =>
        if crCount (trace init ω (t + 1)) < crCount (trace init ω t)
        then (1 : ℝ) else 0 | pairLogFiltration L K t] from by
      apply condExp_congr_ae (μ := law init) (m := pairLogFiltration L K t)
      apply Filter.Eventually.of_forall
      intro ω'
      beta_reduce
      split_ifs <;> rfl)
  filter_upwards [hcond'] with ω hω
  intro hp hq
  exact (cr_rate_floor hn hq).trans
    (by simpa only [if_pos hp, hcard] using hω)

theorem cr_count_applyDraw_le (c : Cfg L K) (d : Draw L K)
    (hmcr : roleMCRCount c = 0)
    (hcr : ∀ a ∈ c, a.role = .cr → a.phase.val = 0) :
    crCount (applyDraw c d) ≤ crCount c :=
  crCount_le_of_reachable_noMCRCRPhase0
    (applyDraw_reachable c d) hmcr hcr

theorem cr_shell_reachable {n : ℕ} {c c' : Cfg L K}
    (hreach : (NonuniformMajority L K).Reachable c c')
    (hc : c ∈ noMCRCRPhase0Shell (L := L) (K := K) n) :
    c' ∈ noMCRCRPhase0Shell (L := L) (K := K) n := by
  refine ⟨?_, ?_, ?_⟩
  · exact (Protocol.reachable_card_eq hreach).trans hc.1
  · exact roleMCRCount_zero_of_reachable hreach hc.2.1
  · exact crPhase0_of_reachable hreach hc.2.1 hc.2.2

theorem cr_uniform_drop {n : ℕ} (hn : 200 ≤ n) (c : Cfg L K)
    (hc : c ∈ noMCRCRPhase0Shell (L := L) (K := K) n)
    (hlarge : ¬ crCount c ≤ n / 100) :
    ENNReal.ofReal (1 / 20000 : ℝ) ≤
      (NonuniformMajority L K).transitionKernel c
        {c' | crCount c' + 1 ≤ crCount c} := by
  have hrate := phase0_crCount_decrease_prob c n hc.1
    (by omega : 2 ≤ n) hc.2.2
  have hfloor := cr_rate_floor hn
    (show n / 100 < crCount c by omega)
  have hset :
      {c' : Cfg L K | crCount c' + 1 ≤ crCount c} =
        {c' : Cfg L K | crCount c' < crCount c} := by
    ext c'
    simp only [Set.mem_setOf_eq]
    omega
  rw [hset]
  exact (ENNReal.ofReal_le_ofReal hfloor).trans hrate

theorem cr_clearance_scalar (n : ℕ) :
    (1 - ENNReal.ofReal (1 / 20000 : ℝ) / 2) ^ (80000 * n) *
        ((2 ^ n : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 1000)) := by
  refine (PhaseOneDrainProducer.drain_scalar
    (1 / 20000 : ℝ) (by norm_num) (by norm_num)
    (80000 * n) n).trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  have hlog := Real.log_two_lt_d9
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast
  nlinarith

theorem cr_clearance_tail_from {n : ℕ} (init : Cfg L K) (hn : 200 ≤ n)
    (s : ℕ) (A : Set ((k : Finset.Iic s) → Draw L K))
    (hA : ∀ p ∈ A,
      prefixCfg init s p ∈ noMCRCRPhase0Shell (L := L) (K := K) n) :
    law init
        {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
          n / 100 < crCount (trace init ω (s + 80000 * n))} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 1000)) *
        law init {ω |
          frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  have h := PhaseOneDrainProducer.drain_tail_from init crCount
    (fun c => c ∈ noMCRCRPhase0Shell (L := L) (K := K) n)
    (fun c => crCount c ≤ n / 100)
    (fun c hc d => cr_count_applyDraw_le c d hc.2.1 hc.2.2)
    (ENNReal.ofReal (1 / 20000 : ℝ))
    (fun c hc hbad => cr_uniform_drop hn c hc hbad)
    s (80000 * n) A n
    (by
      intro p hp
      calc
        crCount (prefixCfg init s p) ≤ (prefixCfg init s p).card :=
          crCount_le_card _
        _ = n := (hA p hp).1)
  refine (measure_mono ?_).trans (h.trans ?_)
  · intro ω hω
    have hshell :
        trace init ω s ∈ noMCRCRPhase0Shell (L := L) (K := K) n :=
      hA (frestrictLe (π := fun _ : ℕ => Draw L K) s ω) hω.1
    refine ⟨hω.1, ?_⟩
    intro u hsu hu
    have hushell :
        trace init ω u ∈ noMCRCRPhase0Shell (L := L) (K := K) n :=
      cr_shell_reachable
        (TimeTheorem.trace_reachable init ω (s := s) (t := u) hsu)
        hshell
    refine ⟨hushell, ?_⟩
    have hmono :
        crCount (trace init ω (s + 80000 * n)) ≤
          crCount (trace init ω u) :=
      crCount_le_of_reachable_noMCRCRPhase0
        (TimeTheorem.trace_reachable init ω
          (s := u) (t := s + 80000 * n) (by omega))
        hushell.2.1 hushell.2.2
    exact not_le_of_gt (lt_of_lt_of_le hω.2 hmono)
  · exact mul_le_mul_right' (cr_clearance_scalar n) _

/-! ## Count floors from the conserved role ledger -/

theorem main_bounds_of_top_split {n : ℕ} (c : Cfg L K)
    (hcard : c.card = n) (hmcr : roleMCRCount c = 0)
    (hsplit : TopSplitWindow (1 / 100 : ℝ) n c) :
    (99 / 200 : ℝ) * (n : ℝ) ≤ (mainCount c : ℝ) ∧
      (mainCount c : ℝ) ≤ (101 / 200 : ℝ) * (n : ℝ) := by
  have hsum :
      (mainCount c : ℝ) + (topCRMass c : ℝ) = (n : ℝ) := by
    exact_mod_cast mainCount_add_topCRMass c hcard hmcr
  change |(mainCount c : ℝ) - (topCRMass c : ℝ)| ≤
    (1 / 100 : ℝ) * (n : ℝ) at hsplit
  obtain ⟨hlo, hhi⟩ := abs_le.mp hsplit
  constructor <;> linarith only [hsum, hlo, hhi]

theorem clock_reserve_lower_nat {n : ℕ} (c : Cfg L K)
    (hcard : c.card = n) (hmcr : roleMCRCount c = 0)
    (hbalance : ClockReserveBalanced c)
    (hmain : 200 * mainCount c ≤ 101 * n)
    (hcr : 100 * crCount c ≤ n) :
    97 * n ≤ 400 * clockCount c ∧
      97 * n ≤ 400 * reserveCount c := by
  have hcons := balanced_conservation c hcard hbalance
  rw [hmcr, Nat.add_zero] at hcons
  have hclock : 97 * n ≤ 400 * clockCount c := by omega
  have hbal : clockCount c = reserveCount c := hbalance
  refine ⟨hclock, ?_⟩
  simpa only [← hbal] using hclock

theorem clock_reserve_lower_of_cutoff {n : ℕ} (c : Cfg L K)
    (hcard : c.card = n) (hmcr : roleMCRCount c = 0)
    (hbalance : ClockReserveBalanced c)
    (hmain :
      (mainCount c : ℝ) ≤ (101 / 200 : ℝ) * (n : ℝ))
    (hcr : crCount c ≤ n / 100) :
    (97 / 400 : ℝ) * (n : ℝ) ≤ (clockCount c : ℝ) ∧
      (97 / 400 : ℝ) * (n : ℝ) ≤ (reserveCount c : ℝ) := by
  have hmainNat : 200 * mainCount c ≤ 101 * n := by
    have hmainReal :
        (200 : ℝ) * (mainCount c : ℝ) ≤ 101 * (n : ℝ) := by
      linarith only [hmain]
    exact_mod_cast hmainReal
  have hcrNat : 100 * crCount c ≤ n := by omega
  obtain ⟨hclock, hreserve⟩ :=
    clock_reserve_lower_nat c hcard hmcr hbalance hmainNat hcrNat
  have hclockReal :
      (97 : ℝ) * (n : ℝ) ≤ 400 * (clockCount c : ℝ) := by
    exact_mod_cast hclock
  have hreserveReal :
      (97 : ℝ) * (n : ℝ) ≤ 400 * (reserveCount c : ℝ) := by
    exact_mod_cast hreserve
  constructor <;> linarith only [hclockReal, hreserveReal]

/-! ## Stopped Main/side concentration on the actual trace -/

open Classical in
/-- A growing potential killed when the trace leaves its window.
The window need not be absorbing. -/
theorem stoppedGrowth_endpoint_tail
    (init : Cfg L K) (φ : Cfg L K → ℝ≥0∞)
    (W : Cfg L K → Prop) (κ : ℝ≥0∞)
    (hdrift : ∀ c, W c →
      ∫⁻ c', φ c' ∂(NonuniformMajority L K).transitionKernel c ≤ κ * φ c)
    (N : ℕ) (thr : ℝ≥0∞) :
    thr * law init {ω |
      (N : WithTop ℕ) < TraceDrain.exitTime init (fun c => ¬ W c) ω ∧
        thr ≤ φ (trace init ω N)} ≤ κ ^ N * φ init := by
  let B : Cfg L K → Prop := fun c => ¬ W c
  let G : (t : ℕ) → ((k : Finset.Iic t) → Draw L K) → ℝ≥0∞ :=
    fun t q =>
      if TraceDrain.AliveThrough init B t q
      then φ (prefixCfg init t q) else 0
  let Y : ℕ → Ω L K → ℝ≥0∞ := fun t ω =>
    G t (frestrictLe (π := fun _ : ℕ => Draw L K) t ω)
  have hY (t : ℕ) : Measurable (Y t) :=
    (measurable_of_countable (G t)).comp
      (measurable_frestrictLe (X := fun _ : ℕ => Draw L K) t)
  have hYval (t : ℕ) (ω : Ω L K) :
      Y t ω =
        if (t : WithTop ℕ) < TraceDrain.exitTime init B ω
        then φ (trace init ω t) else 0 := by
    change
      (if TraceDrain.AliveThrough init B t
        (frestrictLe (π := fun _ : ℕ => Draw L K) t ω)
        then _ else _) = _
    rw [if_congr (TraceDrain.aliveThrough_iff init B t ω) rfl rfl]
    rfl
  have hstep (t : ℕ) :
      ∫⁻ ω, Y (t + 1) ω ∂law init ≤ κ * ∫⁻ ω, Y t ω ∂law init := by
    let F : ((k : Finset.Iic t) → Draw L K) → Draw L K → ℝ≥0∞ :=
      fun q d =>
        if TraceDrain.AliveThrough init B t q
        then φ (applyDraw (prefixCfg init t q) d) else 0
    have hle : ∀ ω, Y (t + 1) ω ≤
        F (frestrictLe (π := fun _ : ℕ => Draw L K) t ω) (ω (t + 1)) := by
      intro ω
      rw [hYval]
      split_ifs with hnext
      · have hnow : (t : WithTop ℕ) < TraceDrain.exitTime init B ω :=
          lt_of_le_of_lt (by exact_mod_cast Nat.le_succ t) hnext
        have halive := (TraceDrain.aliveThrough_iff init B t ω).2 hnow
        change _ ≤
          (if TraceDrain.AliveThrough init B t
            (frestrictLe (π := fun _ : ℕ => Draw L K) t ω)
            then _ else _)
        rw [if_pos halive]
        exact le_rfl
      · exact zero_le
    have hinner :
        ∀ ω,
          ∫⁻ d, F (frestrictLe (π := fun _ : ℕ => Draw L K) t ω) d
              ∂pairKernel init t (frestrictLe (π := fun _ : ℕ => Draw L K) t ω) ≤
            κ * Y t ω := by
      intro ω
      change _ ≤ κ *
        (if TraceDrain.AliveThrough init B t
          (frestrictLe (π := fun _ : ℕ => Draw L K) t ω)
          then _ else _)
      by_cases halive : TraceDrain.AliveThrough init B t
          (frestrictLe (π := fun _ : ℕ => Draw L K) t ω)
      · simp only [F, if_pos halive]
        rw [TraceDrain.lintegral_pairKernel_applyDraw init t _ φ]
        have hW : W (prefixCfg init t
            (frestrictLe (π := fun _ : ℕ => Draw L K) t ω)) := by
          have h := halive t le_rfl
          simpa [B] using h
        exact hdrift _ hW
      · simp only [F, if_neg halive, lintegral_zero, mul_zero, le_refl]
    calc
      ∫⁻ ω, Y (t + 1) ω ∂law init
          ≤ ∫⁻ ω, F (frestrictLe (π := fun _ : ℕ => Draw L K) t ω)
              (ω (t + 1)) ∂law init := lintegral_mono hle
      _ = ∫⁻ ω,
          (∫⁻ d, F (frestrictLe (π := fun _ : ℕ => Draw L K) t ω) d
            ∂pairKernel init t
              (frestrictLe (π := fun _ : ℕ => Draw L K) t ω)) ∂law init :=
        TraceDrain.lintegral_prefix_next init t F
      _ ≤ ∫⁻ ω, κ * Y t ω ∂law init := lintegral_mono hinner
      _ = κ * ∫⁻ ω, Y t ω ∂law init :=
        lintegral_const_mul _ (hY t)
  have hexp : ∀ t, ∫⁻ ω, Y t ω ∂law init ≤ κ ^ t * φ init := by
    intro t
    induction t with
    | zero =>
        have hzero : ∀ ω, Y 0 ω ≤ φ init := by
          intro ω
          rw [hYval]
          split_ifs
          · exact le_rfl
          · exact zero_le
        calc
          ∫⁻ ω, Y 0 ω ∂law init ≤ ∫⁻ _ω, φ init ∂law init :=
            lintegral_mono hzero
          _ = κ ^ 0 * φ init := by
            rw [lintegral_const, measure_univ, mul_one, pow_zero, one_mul]
    | succ t ih =>
        calc
          ∫⁻ ω, Y (t + 1) ω ∂law init ≤ κ * ∫⁻ ω, Y t ω ∂law init :=
            hstep t
          _ ≤ κ * (κ ^ t * φ init) := by gcongr
          _ = κ ^ (t + 1) * φ init := by ring
  have hsub :
      {ω | (N : WithTop ℕ) < TraceDrain.exitTime init B ω ∧
          thr ≤ φ (trace init ω N)} ⊆
        {ω | thr ≤ Y N ω} := by
    rintro ω ⟨halive, hlarge⟩
    change thr ≤ Y N ω
    rw [hYval, if_pos halive]
    exact hlarge
  calc
    thr * law init {ω |
        (N : WithTop ℕ) < TraceDrain.exitTime init B ω ∧
          thr ≤ φ (trace init ω N)}
        ≤ thr * law init {ω | thr ≤ Y N ω} :=
      mul_le_mul_left' (measure_mono hsub) thr
    _ ≤ ∫⁻ ω, Y N ω ∂law init :=
      mul_meas_ge_le_lintegral₀ (hY N).aemeasurable thr
    _ ≤ κ ^ N * φ init := hexp N

/-- Cosh concentration jointly with a genuine Phase-0 prefix. -/
theorem phaseZero_cosh_prefix_tail
    {n : ℕ} (init : Cfg L K)
    (hinit : Phase0InitialFresh (L := L) (K := K) n init)
    (hn : 2 ≤ n) (σ : ℝ) (hσ : 0 ≤ σ)
    (δ : ℝ) (hδn : 0 ≤ δ * (n : ℝ)) (T : ℕ) :
    law init {ω |
      (∀ t ≤ T, Phase0Window.allPhase0 (trace init ω t)) ∧
        ¬ TopSplitWindow δ n (trace init ω T)} ≤
      ENNReal.ofReal
        ((Real.cosh σ) ^ T / Real.cosh (σ * (δ * (n : ℝ)))) := by
  let W : Cfg L K → Prop := fun c =>
    c.card = n ∧ Phase0Window.allPhase0 c ∧ LedgerInv c
  have hdrift : ∀ c, W c →
      ∫⁻ c', coshPot σ c' ∂(NonuniformMajority L K).transitionKernel c ≤
        ENNReal.ofReal (Real.cosh σ) * coshPot σ c := by
    intro c hc
    have hcsmall : 2 ≤ c.card := by
      rw [hc.1]
      exact hn
    exact coshPot_drift σ hσ c hcsmall hc.2.1
      (inwardDrift_of_ledger σ hσ c hcsmall hc.2.1 hc.2.2
        (rectangleDriftIdentity_of_allPhase0 c hcsmall hc.2.1))
  have hbound := stoppedGrowth_endpoint_tail init (coshPot σ) W
    (ENNReal.ofReal (Real.cosh σ)) hdrift T
    (ENNReal.ofReal (Real.cosh (σ * (δ * (n : ℝ)))))
  rw [coshPot_init_one σ hinit.1, mul_one] at hbound
  have hsub :
      {ω |
        (∀ t ≤ T, Phase0Window.allPhase0 (trace init ω t)) ∧
          ¬ TopSplitWindow δ n (trace init ω T)} ⊆
        {ω |
          (T : WithTop ℕ) < TraceDrain.exitTime init (fun c => ¬ W c) ω ∧
            ENNReal.ofReal (Real.cosh (σ * (δ * (n : ℝ)))) ≤
              coshPot σ (trace init ω T)} := by
    rintro ω ⟨hall, hbad⟩
    have hledger := phaseZero_ledger_trace_prefix init ω T hinit
      (fun t ht => hall t ht.le)
    have hcard (t : ℕ) : (trace init ω t).card = n := by
      calc
        (trace init ω t).card = (trace init ω 0).card :=
          Protocol.reachable_card_eq
            (TimeTheorem.trace_reachable init ω
              (s := 0) (t := t) (Nat.zero_le t))
        _ = n := by simpa only [TimeTheorem.trace_zero] using hinit.1.1
    refine ⟨?_, coshPot_ge_thresh_of_not_window σ hσ hδn _ hbad⟩
    rw [← not_le, TraceDrain.exitTime_le_iff]
    rintro ⟨t, ht, hnot⟩
    exact hnot ⟨hcard t, hall t ht, hledger t ht⟩
  have hproduct :
      ENNReal.ofReal (Real.cosh (σ * (δ * (n : ℝ)))) *
        law init {ω |
          (∀ t ≤ T, Phase0Window.allPhase0 (trace init ω t)) ∧
            ¬ TopSplitWindow δ n (trace init ω T)} ≤
      ENNReal.ofReal (Real.cosh σ) ^ T :=
    (mul_le_mul_left' (measure_mono hsub) _).trans hbound
  have hθzero :
      ENNReal.ofReal (Real.cosh (σ * (δ * (n : ℝ)))) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.cosh_pos _)).ne'
  calc
    law init {ω |
        (∀ t ≤ T, Phase0Window.allPhase0 (trace init ω t)) ∧
          ¬ TopSplitWindow δ n (trace init ω T)}
        ≤ ENNReal.ofReal (Real.cosh σ) ^ T /
          ENNReal.ofReal (Real.cosh (σ * (δ * (n : ℝ)))) := by
      rw [ENNReal.le_div_iff_mul_le
        (Or.inl hθzero) (Or.inl ENNReal.ofReal_ne_top)]
      simpa only [mul_comm] using hproduct
    _ = ENNReal.ofReal
        ((Real.cosh σ) ^ T / Real.cosh (σ * (δ * (n : ℝ)))) := by
      rw [ENNReal.ofReal_div_of_pos (Real.cosh_pos _),
        ENNReal.ofReal_pow (Real.cosh_pos σ).le]

theorem phaseZero_cosh_ratio_exp (σ a : ℝ) (T : ℕ) :
    (Real.cosh σ) ^ T / Real.cosh (σ * a) ≤
      2 * Real.exp ((T : ℝ) * σ ^ 2 / 2 - σ * a) := by
  have hnum :
      (Real.cosh σ) ^ T ≤ Real.exp ((T : ℝ) * σ ^ 2 / 2) := by
    calc
      (Real.cosh σ) ^ T ≤ (Real.exp (σ ^ 2 / 2)) ^ T :=
        pow_le_pow_left₀ (Real.cosh_pos σ).le
          (Real.cosh_le_exp_half_sq σ) T
      _ = Real.exp ((T : ℝ) * σ ^ 2 / 2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hden : Real.exp (σ * a) / 2 ≤ Real.cosh (σ * a) := by
    rw [Real.cosh_eq]
    linarith only [Real.exp_pos (-(σ * a))]
  calc
    (Real.cosh σ) ^ T / Real.cosh (σ * a)
        ≤ Real.exp ((T : ℝ) * σ ^ 2 / 2) / Real.cosh (σ * a) :=
      div_le_div_of_nonneg_right hnum (Real.cosh_pos _).le
    _ ≤ Real.exp ((T : ℝ) * σ ^ 2 / 2) / (Real.exp (σ * a) / 2) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity) hden
    _ = 2 * Real.exp ((T : ℝ) * σ ^ 2 / 2 - σ * a) := by
      rw [Real.exp_sub]
      field_simp
      <;> ring

theorem phaseZero_balance_scalar {n T : ℕ}
    (hpop : timePopulationThreshold ≤ n)
    (hT : (T : ℝ) ≤ 21 * (n : ℝ) * Real.log (n : ℝ)) :
    (Real.cosh (1 / (2100 * Real.log (n : ℝ)))) ^ T /
      Real.cosh
        ((1 / (2100 * Real.log (n : ℝ))) * ((1 / 100 : ℝ) * (n : ℝ))) ≤
      1 / (n : ℝ) ^ 3 := by
  obtain ⟨hnpos, hlog⟩ := PhaseOneDrain.population_calibration hpop
  have hnreal : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast
      ((by norm_num : (2 : ℕ) ≤ 40).trans
        (time_population_bounds hpop).2)
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith only [hlog]
  let σ : ℝ := 1 / (2100 * Real.log (n : ℝ))
  have hexponent :
      (T : ℝ) * σ ^ 2 / 2 - σ * ((1 / 100 : ℝ) * (n : ℝ)) ≤
        -((n : ℝ) / (420000 * Real.log (n : ℝ))) := by
    have hscaled := mul_le_mul_of_nonneg_right hT
      (show (0 : ℝ) ≤ σ ^ 2 / 2 by positivity)
    have hid :
        (21 * (n : ℝ) * Real.log (n : ℝ)) * (σ ^ 2 / 2) -
            σ * ((1 / 100 : ℝ) * (n : ℝ)) =
          -((n : ℝ) / (420000 * Real.log (n : ℝ))) := by
      dsimp only [σ]
      field_simp [hlogpos.ne']
      <;> ring
    calc
      (T : ℝ) * σ ^ 2 / 2 - σ * ((1 / 100 : ℝ) * (n : ℝ)) ≤
          (21 * (n : ℝ) * Real.log (n : ℝ)) * (σ ^ 2 / 2) -
            σ * ((1 / 100 : ℝ) * (n : ℝ)) := by
        nlinarith only [hscaled]
      _ = -((n : ℝ) / (420000 * Real.log (n : ℝ))) := hid
  have hquartic : (Real.log (n : ℝ)) ^ 4 / 24 ≤ (n : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (Real.log (n : ℝ)) hlogpos.le 4
    norm_num at h ⊢
    simpa only [Real.exp_log hnpos] using h
  have hsquare : (40320000 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
    nlinarith only [hlog, sq_nonneg (Real.log (n : ℝ) - 2000000)]
  have hproduct :
      0 ≤ (Real.log (n : ℝ)) ^ 2 *
        ((Real.log (n : ℝ)) ^ 2 - 40320000) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hsquare)
  have hpopulation :
      (1680000 : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) := by
    nlinarith only [hquartic, hproduct]
  have hdominates :
      4 * Real.log (n : ℝ) ≤
        (n : ℝ) / (420000 * Real.log (n : ℝ)) := by
    apply (le_div_iff₀ (by positivity :
      (0 : ℝ) < 420000 * Real.log (n : ℝ))).2
    nlinarith only [hpopulation]
  have hpower :
      Real.exp (-(4 * Real.log (n : ℝ))) = 1 / (n : ℝ) ^ 4 := by
    have hmul :
        Real.exp (4 * Real.log (n : ℝ)) =
          (Real.exp (Real.log (n : ℝ))) ^ (4 : ℕ) := by
      simpa only [Nat.cast_ofNat] using
        (Real.exp_nat_mul (Real.log (n : ℝ)) 4)
    rw [Real.exp_neg, hmul, Real.exp_log hnpos, one_div]
  change (Real.cosh σ) ^ T /
    Real.cosh (σ * ((1 / 100 : ℝ) * (n : ℝ))) ≤ _
  calc
    (Real.cosh σ) ^ T /
        Real.cosh (σ * ((1 / 100 : ℝ) * (n : ℝ))) ≤
        2 * Real.exp
          ((T : ℝ) * σ ^ 2 / 2 - σ * ((1 / 100 : ℝ) * (n : ℝ))) :=
      phaseZero_cosh_ratio_exp σ ((1 / 100 : ℝ) * (n : ℝ)) T
    _ ≤ 2 * Real.exp (-((n : ℝ) / (420000 * Real.log (n : ℝ)))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num)
    _ ≤ 2 * Real.exp (-(4 * Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (neg_le_neg hdominates)) (by norm_num)
    _ = 2 * (1 / (n : ℝ) ^ 4) := by rw [hpower]
    _ = 2 / (n : ℝ) ^ 4 := by ring
    _ ≤ 1 / (n : ℝ) ^ 3 := by
      apply (div_le_div_iff₀ (pow_pos hnpos 4) (pow_pos hnpos 3)).2
      have h := mul_nonneg (pow_nonneg hnpos.le 3)
        (sub_nonneg.mpr hnreal)
      nlinarith only [h]

/-- A deliberately longer CR stage avoids a variable-rate waiting-time lemma. -/
theorem phaseZero_role_horizon_extended_le {n : ℕ}
    (hpop : timePopulationThreshold ≤ n) :
    ((80001 * n + logWindow n 20 : ℕ) : ℝ) ≤
      21 * (n : ℝ) * Real.log (n : ℝ) := by
  obtain ⟨hnpos, hlog⟩ := PhaseOneDrain.population_calibration hpop
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast
      ((by norm_num : (1 : ℕ) ≤ 40).trans
        (time_population_bounds hpop).2)
  have hlognonneg : 0 ≤ Real.log (n : ℝ) := by linarith only [hlog]
  have hmul :
      (2000000 : ℝ) * (n : ℝ) ≤ (n : ℝ) * Real.log (n : ℝ) := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hlog hnpos.le
  have hceil : (logWindow n 20 : ℝ) <
      20 * (n : ℝ) * Real.log (n : ℝ) + 1 := by
    change (Nat.ceil ((20 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) : ℝ) < _
    exact Nat.ceil_lt_add_one (by positivity)
  push_cast
  nlinarith only [hnreal, hmul, hceil]

theorem phaseZero_entry_horizon_extended_le {n : ℕ}
    (hpop : timePopulationThreshold ≤ n) :
    80001 * n + logWindow n 20 +
      300 * n * PhaseThreeModel.Numeric.clockHours n +
      logWindow n 7 ≤
      350 * n * PhaseThreeModel.Numeric.clockHours n := by
  have hold := phase_zero_horizon_le hpop
  obtain ⟨_, hlog⟩ := PhaseOneDrain.population_calibration hpop
  obtain ⟨_, _, _, hlogH, _, _⟩ := time_hour_calibration hpop
  have hhours : 39880 ≤ PhaseThreeModel.Numeric.clockHours n := by
    have hreal :
        (39880 : ℝ) ≤ (PhaseThreeModel.Numeric.clockHours n : ℝ) := by
      linarith only [hlog, hlogH]
    exact_mod_cast hreal
  have hextra :
      79760 * n ≤ 2 * n * PhaseThreeModel.Numeric.clockHours n := by
    calc
      79760 * n = (2 * 39880) * n := by ring
      _ ≤ (2 * PhaseThreeModel.Numeric.clockHours n) * n :=
        Nat.mul_le_mul_right n (Nat.mul_le_mul_left 2 hhours)
      _ = 2 * n * PhaseThreeModel.Numeric.clockHours n := by ring
  nlinarith only [hold, hextra]

theorem phaseZero_balance_prefix_tail {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (T : ℕ)
    (hT : (T : ℝ) ≤ 21 * (n : ℝ) * Real.log (n : ℝ)) :
    law init {ω |
      (∀ t ≤ T, Phase0Window.allPhase0 (trace init ω t)) ∧
        ¬ TopSplitWindow (1 / 100 : ℝ) n (trace init ω T)} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 3) := by
  have hinit := phase0InitialFresh_of_validInitial
    n init hinput.2.1 hinput.2.2
  have hn : 2 ≤ n :=
    (by norm_num : (2 : ℕ) ≤ 40).trans
      (time_population_bounds hinput.1).2
  have hlog := (PhaseOneDrain.population_calibration hinput.1).2
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith only [hlog]
  have h := phaseZero_cosh_prefix_tail init hinit hn
    (1 / (2100 * Real.log (n : ℝ))) (by positivity)
    (1 / 100 : ℝ) (by positivity) T
  exact h.trans
    (ENNReal.ofReal_le_ofReal (phaseZero_balance_scalar hinput.1 hT))

theorem phaseZero_balance_role_horizon_tail {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    law init {ω |
      (∀ t ≤ 80001 * n + logWindow n 20,
        Phase0Window.allPhase0 (trace init ω t)) ∧
        ¬ TopSplitWindow (1 / 100 : ℝ) n
          (trace init ω (80001 * n + logWindow n 20))} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 3) :=
  phaseZero_balance_prefix_tail init hinput
    (80001 * n + logWindow n 20)
    (phaseZero_role_horizon_extended_le hinput.1)

/-! ## No early Phase-0 exit: the affine clock potential -/

def phaseZeroEarlyWindow (n : ℕ) (c : Cfg L K) : Prop :=
  c.card = n ∧ Phase0Window.allPhase0 c ∧ Phase0Window.noClockAtZero c

noncomputable def phaseZeroEarlyImmigration (L : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (-(Real.log (3 / 2 : ℝ) * ((50 * (L + 1) : ℕ) : ℝ))))

open Classical in
noncomputable def phaseZeroEarlyMass (n : ℕ) (c : Cfg L K) : ℝ≥0∞ :=
  if phaseZeroEarlyWindow n c then
    Phase0Window.clockCounterPotential (Real.log (3 / 2 : ℝ)) c +
      (n : ℝ≥0∞) * phaseZeroEarlyImmigration L
  else 1

theorem phaseZeroEarlyMass_step_le_raw (n : ℕ) (c : Cfg L K)
    (hc : phaseZeroEarlyWindow n c) (a b : AgentState L K) :
    phaseZeroEarlyMass n
        (Protocol.stepOrSelf (NonuniformMajority L K) c a b) ≤
      Phase0Window.clockCounterPotential (Real.log (3 / 2 : ℝ))
          (Protocol.stepOrSelf (NonuniformMajority L K) c a b) +
        (n : ℝ≥0∞) * phaseZeroEarlyImmigration L := by
  classical
  have hcard :
      (Protocol.stepOrSelf (NonuniformMajority L K) c a b).card = n :=
    (Protocol.stepOrSelf_card_eq
      (P := NonuniformMajority L K) c a b).trans hc.1
  have hall : Phase0Window.allPhase0
      (Protocol.stepOrSelf (NonuniformMajority L K) c a b) := by
    by_contra h
    exact (Phase0Window.det_phase0_exit c a b hc.2.1 h) hc.2.2
  unfold phaseZeroEarlyMass
  split_ifs with hgood
  · exact le_rfl
  · have hbad : ¬ Phase0Window.noClockAtZero
        (Protocol.stepOrSelf (NonuniformMajority L K) c a b) :=
      fun hno => hgood ⟨hcard, hall, hno⟩
    exact (Phase0Window.clockCounterPotential_ge_one_of_not_noClockAtZero
      (Real.log (3 / 2 : ℝ))
      (Protocol.stepOrSelf (NonuniformMajority L K) c a b) hbad).trans
        (le_add_right le_rfl)

theorem phaseZeroEarlyMass_drift {n : ℕ} (hn : 2 ≤ n)
    (c : Cfg L K) (hc : phaseZeroEarlyWindow n c) :
    (∫⁻ c', phaseZeroEarlyMass n c'
      ∂(NonuniformMajority L K).transitionKernel c) ≤
      (1 + 1 / (n : ℝ≥0∞)) * phaseZeroEarlyMass n c := by
  classical
  have hcTwo : 2 ≤ c.card := by simpa only [hc.1] using hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnzero : (n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hntop : (n : ℝ≥0∞) ≠ ∞ := by simp
  have hθ : 0 ≤ Real.log (3 / 2 : ℝ) := Real.log_nonneg (by norm_num)
  have hrate :
      ENNReal.ofReal (1 + 2 * (Real.exp (Real.log (3 / 2 : ℝ)) - 1) / (n : ℝ)) =
        1 + 1 / (n : ℝ≥0∞) := by
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)]
    norm_num only [show (2 : ℝ) * (3 / 2 - 1) = 1 by norm_num]
    rw [ENNReal.ofReal_add (by norm_num) (by positivity),
      ENNReal.ofReal_one, ENNReal.ofReal_div_of_pos hnpos,
      ENNReal.ofReal_one, ENNReal.ofReal_natCast]
  have haff := Phase0Window.clockCounterPotential_drift_affine
    (Real.log (3 / 2 : ℝ)) hθ n c hc.1 hcTwo hc.2.1
  rw [hrate] at haff
  have halg (x : ℝ≥0∞) :
      ((1 + 1 / (n : ℝ≥0∞)) * x + phaseZeroEarlyImmigration L) +
          (n : ℝ≥0∞) * phaseZeroEarlyImmigration L =
        (1 + 1 / (n : ℝ≥0∞)) *
          (x + (n : ℝ≥0∞) * phaseZeroEarlyImmigration L) := by
    simp only [mul_add, add_mul, one_div, one_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel hnzero hntop] <;> ring
  calc
    (∫⁻ c', phaseZeroEarlyMass n c'
        ∂(NonuniformMajority L K).transitionKernel c) ≤
        ∫⁻ c', Phase0Window.clockCounterPotential (Real.log (3 / 2 : ℝ)) c' +
          (n : ℝ≥0∞) * phaseZeroEarlyImmigration L
          ∂(NonuniformMajority L K).transitionKernel c := by
      simp only [Phase0Window.lintegral_transitionKernel_eq_sum
        (NonuniformMajority L K) c hcTwo]
      apply Finset.sum_le_sum
      intro pair _
      exact mul_le_mul_right'
        (phaseZeroEarlyMass_step_le_raw n c hc pair.1 pair.2) _
    _ = (∫⁻ c', Phase0Window.clockCounterPotential (Real.log (3 / 2 : ℝ)) c'
          ∂(NonuniformMajority L K).transitionKernel c) +
        (n : ℝ≥0∞) * phaseZeroEarlyImmigration L := by
      rw [lintegral_add_right _ measurable_const,
        lintegral_const, measure_univ, mul_one]
    _ ≤ ((1 + 1 / (n : ℝ≥0∞)) *
        Phase0Window.clockCounterPotential (Real.log (3 / 2 : ℝ)) c +
        phaseZeroEarlyImmigration L) +
        (n : ℝ≥0∞) * phaseZeroEarlyImmigration L :=
      add_le_add haff le_rfl
    _ = (1 + 1 / (n : ℝ≥0∞)) * phaseZeroEarlyMass n c := by
      rw [phaseZeroEarlyMass, if_pos hc]
      exact halg _

theorem phaseZeroEarlyMass_threshold (n : ℕ) (c : Cfg L K)
    (hc : ¬ phaseZeroEarlyWindow n c) :
    1 ≤ phaseZeroEarlyMass n c := by
  simp only [phaseZeroEarlyMass, if_neg hc, le_refl]

theorem phaseZeroEarlyMass_initial {n : ℕ} (init : Cfg L K)
    (hinit : Phase0Initial n init) :
    phaseZeroEarlyMass n init ≤
      (2 : ℝ≥0∞) * n * phaseZeroEarlyImmigration L := by
  classical
  have hnoClock : ∀ a ∈ init, a.role ≠ Role.clock := by
    intro a ha hclock
    have hmcr := (hinit.2 a ha).2
    rw [hmcr] at hclock
    cases hclock
  have hall : Phase0Window.allPhase0 init := fun a ha => (hinit.2 a ha).1
  have hno : Phase0Window.noClockAtZero init := by
    intro a ha hclock
    exact (hnoClock a ha hclock).elim
  have hgood : phaseZeroEarlyWindow n init := ⟨hinit.1, hall, hno⟩
  rw [phaseZeroEarlyMass, if_pos hgood]
  have hfull : ∀ a ∈ init, a.role = Role.clock → a.counter.val = 50 * (L + 1) := by
    intro a ha hclock
    exact (hnoClock a ha hclock).elim
  have hbound := Phase0Window.clockCounterPotential_init_le
    (Real.log (3 / 2 : ℝ)) n init hinit.1 hfull
  calc
    _ ≤ (n : ℝ≥0∞) * phaseZeroEarlyImmigration L +
        (n : ℝ≥0∞) * phaseZeroEarlyImmigration L :=
      add_le_add hbound le_rfl
    _ = _ := by ring

theorem phase_zero_early_window_raw_tail {n : ℕ} (init : Cfg L K)
    (hinit : Phase0Initial n init) (hn : 2 ≤ n) (T : ℕ) :
    law init {ω | ∃ S ≤ T, ¬ phaseZeroEarlyWindow n (trace init ω S)} ≤
      (1 + 1 / (n : ℝ≥0∞)) ^ T *
        ((2 : ℝ≥0∞) * n * phaseZeroEarlyImmigration L) := by
  have h := TraceDrain.growth_exit_tail_from init
    (phaseZeroEarlyMass n) (phaseZeroEarlyWindow n)
    (1 + 1 / (n : ℝ≥0∞)) (le_add_right le_rfl)
    (fun c hc => phaseZeroEarlyMass_drift hn c hc)
    1 (phaseZeroEarlyMass_threshold n) 0 T Set.univ
    ((2 : ℝ≥0∞) * n * phaseZeroEarlyImmigration L)
    (fun _ _ => phaseZeroEarlyMass_initial init hinit)
  simpa only [Set.mem_univ, true_and, Nat.zero_add, Nat.zero_le,
    Set.setOf_true, one_mul, mul_one, measure_univ] using h

theorem phase_zero_early_seed_raw_tail {n : ℕ} (init : Cfg L K)
    (hinit : Phase0Initial n init) (hn : 2 ≤ n) (T : ℕ) :
    law init {ω | ∃ S ≤ T, firstPhaseSeed init 1 S ω} ≤
      (1 + 1 / (n : ℝ≥0∞)) ^ T *
        ((2 : ℝ≥0∞) * n * phaseZeroEarlyImmigration L) := by
  refine (measure_mono ?_).trans
    (phase_zero_early_window_raw_tail init hinit hn T)
  rintro ω ⟨S, hST, hseed⟩
  refine ⟨S, hST, ?_⟩
  intro hgood
  obtain ⟨a, ha, hphase⟩ := hseed.1
  have hz : a.phase.val = 0 :=
    congrArg Fin.val (hgood.2.1 a ha)
  omega

theorem phase_zero_early_tail_real (n T : ℕ)
    (hn : 2 ≤ n)
    (hT : (T : ℝ) ≤ 21 * (n : ℝ) * Real.log (n : ℝ)) :
    (1 + 1 / (n : ℝ)) ^ T * ((2 : ℝ) * (n : ℝ)) *
        Real.exp
          (-(Real.log (3 / 2 : ℝ) *
            ((50 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ))) ≤
      1 / (n : ℝ) ^ 6 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnTwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by linarith only [hnTwo])
  have hmgf :
      (1 + 1 / (n : ℝ)) ^ T ≤ Real.exp ((T : ℝ) / (n : ℝ)) := by
    calc
      (1 + 1 / (n : ℝ)) ^ T ≤ (Real.exp (1 / (n : ℝ))) ^ T :=
        pow_le_pow_left₀ (by positivity)
          (by simpa only [add_comm] using
            Real.add_one_le_exp (1 / (n : ℝ))) T
      _ = Real.exp ((T : ℝ) / (n : ℝ)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hmean :
      (T : ℝ) / (n : ℝ) ≤ 21 * Real.log (n : ℝ) := by
    apply (div_le_iff₀ hnpos).2
    nlinarith only [hT]
  have hhour := PhaseOneDrain.clock_hour_log_lower n
  have hscaled :=
    mul_le_mul_of_nonneg_left PhaseOneDrain.clock_log_certificate.le
      (Nat.cast_nonneg (PhaseThreeModel.Numeric.clockHours n) : (0 : ℝ) ≤ _)
  have hcounter :
      29 * Real.log (n : ℝ) ≤
        Real.log (3 / 2 : ℝ) *
          ((50 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [hhour, hscaled, hlog]
  have htwo : (2 : ℝ) * n ≤ (n : ℝ) ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hnTwo hnpos.le]
  have hsquare :
      Real.exp (2 * Real.log (n : ℝ)) = (n : ℝ) ^ 2 := by
    calc
      _ = Real.exp (Real.log (n : ℝ) + Real.log (n : ℝ)) := by
        congr 1
        ring
      _ = (n : ℝ) * n := by rw [Real.exp_add, Real.exp_log hnpos]
      _ = _ := by ring
  have hsix :
      Real.exp (6 * Real.log (n : ℝ)) = (n : ℝ) ^ 6 := by
    have hlogpow : Real.log ((n : ℝ) ^ 6) = 6 * Real.log (n : ℝ) := by
      simp only [Real.log_pow, Nat.cast_ofNat]
    rw [← hlogpow, Real.exp_log (by positivity)]
  calc
    _ ≤ Real.exp ((T : ℝ) / (n : ℝ)) * (n : ℝ) ^ 2 *
        Real.exp
          (-(Real.log (3 / 2 : ℝ) *
            ((50 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      exact mul_le_mul hmgf htwo (by positivity) (Real.exp_nonneg _)
    _ = Real.exp
        ((T : ℝ) / (n : ℝ) + 2 * Real.log (n : ℝ) -
          Real.log (3 / 2 : ℝ) *
            ((50 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ)) := by
      simp only [Real.exp_sub, Real.exp_add, hsquare, Real.exp_neg, div_eq_mul_inv]
    _ ≤ Real.exp (-(6 * Real.log (n : ℝ))) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hmean, hcounter]
    _ = 1 / (n : ℝ) ^ 6 := by
      rw [Real.exp_neg, hsix, one_div]

theorem phase_zero_early_tail_calibration (n T : ℕ)
    (hn : 2 ≤ n)
    (hT : (T : ℝ) ≤ 21 * (n : ℝ) * Real.log (n : ℝ)) :
    (1 + 1 / (n : ℝ≥0∞)) ^ T *
        ((2 : ℝ≥0∞) * n *
          phaseZeroEarlyImmigration (PhaseThreeModel.Numeric.hourIndex n)) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 6) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbase : (0 : ℝ) ≤ 1 + 1 / (n : ℝ) := by positivity
  have hrate :
      ENNReal.ofReal (1 + 1 / (n : ℝ)) = 1 + 1 / (n : ℝ≥0∞) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity),
      ENNReal.ofReal_one, ENNReal.ofReal_div_of_pos hnpos,
      ENNReal.ofReal_one, ENNReal.ofReal_natCast]
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  have hreal := ENNReal.ofReal_le_ofReal
    (phase_zero_early_tail_real n T hn hT)
  simpa only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤
      (1 + 1 / (n : ℝ)) ^ T * (2 * (n : ℝ))),
    ENNReal.ofReal_mul (pow_nonneg hbase T),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_mul (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
    ENNReal.ofReal_pow hbase, hrate, htwo,
    ENNReal.ofReal_natCast, phaseZeroEarlyImmigration,
    PhaseThreeModel.Numeric.clockHours, mul_assoc] using hreal

theorem phase_zero_early_window_tail {n : ℕ} (init : InputCfg n)
    (hinit : Phase0Initial n init) (hn : 2 ≤ n) (T : ℕ)
    (hT : (T : ℝ) ≤ 21 * (n : ℝ) * Real.log (n : ℝ)) :
    law init {ω | ∃ S ≤ T, ¬ phaseZeroEarlyWindow n (trace init ω S)} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 6) :=
  (phase_zero_early_window_raw_tail init hinit hn T).trans
    (phase_zero_early_tail_calibration n T hn hT)

theorem phase_zero_early_seed_tail {n : ℕ} (init : InputCfg n)
    (hinit : Phase0Initial n init) (hn : 2 ≤ n) (T : ℕ)
    (hT : (T : ℝ) ≤ 21 * (n : ℝ) * Real.log (n : ℝ)) :
    law init {ω | ∃ S ≤ T, firstPhaseSeed init 1 S ω} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 6) :=
  (phase_zero_early_seed_raw_tail init hinit hn T).trans
    (phase_zero_early_tail_calibration n T hn hT)

/-! ## Count transport through the mixed Phase-0/Phase-1 interval -/

private def EarlyRole (r q : Role) : Prop :=
  q = r ∨ r = .cr ∧ (q = .clock ∨ q = .reserve)

private theorem earlyRole_refl (r : Role) : EarlyRole r r := Or.inl rfl

private theorem earlyRole_trans {r q z : Role}
    (hrq : EarlyRole r q) (hqz : EarlyRole q z) : EarlyRole r z := by
  rcases hrq with rfl | ⟨rfl, hq⟩
  · exact hqz
  · rcases hq with rfl | rfl
    · rcases hqz with rfl | ⟨hbad, _⟩
      · exact Or.inr ⟨rfl, Or.inl rfl⟩
      · cases hbad
    · rcases hqz with rfl | ⟨hbad, _⟩
      · exact Or.inr ⟨rfl, Or.inr rfl⟩
      · cases hbad

private theorem earlyRole_no_mcr {r q : Role}
    (h : EarlyRole r q) (hr : r ≠ .mcr) : q ≠ .mcr := by
  rcases h with rfl | ⟨rfl, hq⟩
  · exact hr
  · rcases hq with rfl | rfl <;> decide

private theorem earlyRole_main_iff {r q : Role}
    (h : EarlyRole r q) : q = .main ↔ r = .main := by
  rcases h with rfl | ⟨rfl, hq⟩
  · rfl
  · rcases hq with rfl | rfl <;> decide

private theorem earlyRole_clock {r q : Role}
    (h : EarlyRole r q) (hr : r = .clock) : q = .clock := by
  rcases h with rfl | ⟨hcr, _⟩
  · exact hr
  · rw [hr] at hcr
    cases hcr

private theorem earlyRole_reserve {r q : Role}
    (h : EarlyRole r q) (hr : r = .reserve) : q = .reserve := by
  rcases h with rfl | ⟨hcr, _⟩
  · exact hr
  · rw [hr] at hcr
    cases hcr

private theorem phaseInit_earlyRole (p : Fin 11) (a : AgentState L K) :
    EarlyRole a.role (phaseInit L K p a).role := by
  rw [phaseInit_role]
  split_ifs with h
  · exact Or.inr ⟨h.2, Or.inr rfl⟩
  · exact earlyRole_refl _

private theorem runInitsBetween_earlyRole
    (oldP newP : ℕ) (a : AgentState L K) :
    EarlyRole a.role (runInitsBetween L K oldP newP a).role := by
  unfold runInitsBetween
  have hfold : ∀ (ks : List ℕ) (b : AgentState L K),
      EarlyRole b.role
        (ks.foldl (fun acc k =>
          if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) b).role := by
    intro ks
    induction ks with
    | nil =>
        intro b
        exact earlyRole_refl _
    | cons k ks ih =>
        intro b
        simp only [List.foldl]
        split_ifs with hk
        · exact earlyRole_trans (phaseInit_earlyRole ⟨k, hk⟩ b) (ih _)
        · exact ih _
  exact hfold _ a

private theorem phaseEpidemicUpdate_earlyRole (s t : AgentState L K) :
    EarlyRole s.role (phaseEpidemicUpdate L K s t).1.role ∧
      EarlyRole t.role (phaseEpidemicUpdate L K s t).2.role := by
  unfold phaseEpidemicUpdate
  dsimp only
  split_ifs <;> simp only [phase10EpidemicEntry_role] <;>
    exact ⟨
      runInitsBetween_earlyRole s.phase.val (max s.phase t.phase).val
        {s with phase := max s.phase t.phase},
      runInitsBetween_earlyRole t.phase.val (max s.phase t.phase).val
        {t with phase := max s.phase t.phase}⟩

private theorem Phase0Transition_earlyRole (s t : AgentState L K)
    (hs : s.role ≠ .mcr) (ht : t.role ≠ .mcr) :
    EarlyRole s.role (Phase0Transition L K s t).1.role ∧
      EarlyRole t.role (Phase0Transition L K s t).2.role := by
  cases hsrole : s.role <;> cases htrole : t.role <;>
    simp_all [Phase0Transition, EarlyRole]

private theorem Transition_earlyRole (s t : AgentState L K)
    (hs : s.role ≠ .mcr) (ht : t.role ≠ .mcr)
    (hpost : (Transition L K s t).1.phase.val ≤ 1) :
    EarlyRole s.role (Transition L K s t).1.role ∧
      EarlyRole t.role (Transition L K s t).2.role := by
  have hphase :=
    (phaseEpidemicUpdate_phase_le_Transition_phase L K s t).1.trans hpost
  have hroles := phaseEpidemicUpdate_earlyRole s t
  rcases he : phaseEpidemicUpdate L K s t with ⟨a, b⟩
  simp only [he] at hphase hroles
  have ha := earlyRole_no_mcr hroles.1 hs
  have hb := earlyRole_no_mcr hroles.2 ht
  rcases (show a.phase.val = 0 ∨ a.phase.val = 1 by omega) with hz | ho
  · have hap : a.phase = ⟨0, by decide⟩ := Fin.ext hz
    have hpair := Phase0Transition_earlyRole a b ha hb
    unfold Transition
    rw [he]
    dsimp only
    simp only [hap, finishPhase10Entry_role_eq]
    exact ⟨earlyRole_trans hroles.1 hpair.1,
      earlyRole_trans hroles.2 hpair.2⟩
  · have hap : a.phase = ⟨1, by decide⟩ := Fin.ext ho
    have hpair := PhaseOnlyWindows.Phase1Transition_role (L := L) (K := K) a b
    unfold Transition
    rw [he]
    dsimp only
    simpa only [hap, finishPhase10Entry_role_eq, hpair.1, hpair.2] using hroles

private theorem role_counts_pair_early (s t : AgentState L K)
    (hs : s.role ≠ .mcr) (ht : t.role ≠ .mcr)
    (hpost : (Transition L K s t).1.phase.val ≤ 1) :
    mainCount ({(Transition L K s t).1, (Transition L K s t).2} :
        Cfg L K) = mainCount ({s, t} : Cfg L K) ∧
      clockCount ({s, t} : Cfg L K) ≤
        clockCount ({(Transition L K s t).1, (Transition L K s t).2} :
          Cfg L K) ∧
      reserveCount ({s, t} : Cfg L K) ≤
        reserveCount ({(Transition L K s t).1, (Transition L K s t).2} :
          Cfg L K) := by
  obtain ⟨hleft, hright⟩ := Transition_earlyRole s t hs ht hpost
  have hmleft := earlyRole_main_iff hleft
  have hmright := earlyRole_main_iff hright
  have hcleft := earlyRole_clock hleft
  have hcright := earlyRole_clock hright
  have hrleft := earlyRole_reserve hleft
  have hrright := earlyRole_reserve hright
  refine ⟨?_, ?_, ?_⟩
  · simp only [mainCount, Multiset.insert_eq_cons, ← Multiset.cons_zero,
      Multiset.countP_cons, Multiset.countP_zero, hmleft, hmright]
  · rw [clockCount_pair', clockCount_pair']
    apply Nat.add_le_add
    · split_ifs <;> simp_all
    · split_ifs <;> simp_all
  · rw [reserveCount_pair', reserveCount_pair']
    apply Nat.add_le_add
    · split_ifs <;> simp_all
    · split_ifs <;> simp_all

/-- A terminal phase cap propagates backwards through a genuine step. -/
theorem phase_cap_before_step {c c' : Cfg L K} (p : ℕ)
    (hstep : (NonuniformMajority L K).StepRel c c')
    (hphase : ∀ a ∈ c', a.phase.val ≤ p) :
    ∀ a ∈ c, a.phase.val ≤ p := by
  classical
  rcases hstep with ⟨r₁, r₂, happ, hc'⟩
  dsimp [Protocol.Applicable, NonuniformMajority] at happ hc'
  have hmono := Transition_phase_monotone (L := L) (K := K) r₁ r₂
  have hp₁ : (Transition L K r₁ r₂).1 ∈ c' := by
    rw [hc']
    simp
  have hp₂ : (Transition L K r₁ r₂).2 ∈ c' := by
    rw [hc']
    simp
  have hr₁ := hmono.1.trans (hphase _ hp₁)
  have hr₂ := hmono.2.trans (hphase _ hp₂)
  intro a ha
  by_cases ha₁ : a = r₁
  · simpa [ha₁] using hr₁
  by_cases ha₂ : a = r₂
  · simpa [ha₂] using hr₂
  have hres : a ∈ c - r₁ ::ₘ {r₂} := by
    have hfirst : a ∈ c.erase r₁ := (Multiset.mem_erase_of_ne ha₁).2 ha
    have hsecond : a ∈ (c.erase r₁).erase r₂ :=
      (Multiset.mem_erase_of_ne ha₂).2 hfirst
    simpa using hsecond
  exact hphase a (by rw [hc']; exact Multiset.mem_add.2 (Or.inl hres))

theorem role_counts_step_early {c c' : Cfg L K}
    (hstep : (NonuniformMajority L K).StepRel c c')
    (hmcr : roleMCRCount c = 0)
    (hphase : ∀ a ∈ c', a.phase.val ≤ 1) :
    mainCount c' = mainCount c ∧
      clockCount c ≤ clockCount c' ∧ reserveCount c ≤ reserveCount c' := by
  classical
  rcases hstep with ⟨r₁, r₂, happ, hc'⟩
  have hc'' : c' = c - {r₁, r₂} +
      {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := hc'
  have hs : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
  have ht : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
  have hpost : (Transition L K r₁ r₂).1.phase.val ≤ 1 :=
    hphase _ (by rw [hc'']; simp)
  obtain ⟨hmain, hclock, hreserve⟩ :=
    role_counts_pair_early r₁ r₂
      (not_mcr_of_mem_noMCR hmcr hs) (not_mcr_of_mem_noMCR hmcr ht) hpost
  have hrestore : c - {r₁, r₂} + {r₁, r₂} = c :=
    Multiset.sub_add_cancel happ
  have hmainRestore := congrArg (mainCount (L := L) (K := K)) hrestore
  have hclockRestore := congrArg (clockCount (L := L) (K := K)) hrestore
  have hreserveRestore := congrArg (reserveCount (L := L) (K := K)) hrestore
  rw [hc'']
  simp only [mainCount, clockCount, reserveCount, Multiset.countP_add]
    at hmain hclock hreserve hmainRestore hclockRestore hreserveRestore ⊢
  exact ⟨by omega, by omega, by omega⟩

theorem role_counts_reachable_early {c c' : Cfg L K}
    (hreach : (NonuniformMajority L K).Reachable c c')
    (hmcr : roleMCRCount c = 0)
    (hphase : ∀ a ∈ c', a.phase.val ≤ 1) :
    mainCount c' = mainCount c ∧
      clockCount c ≤ clockCount c' ∧ reserveCount c ≤ reserveCount c' := by
  induction hreach with
  | refl => exact ⟨rfl, le_rfl, le_rfl⟩
  | tail hprev hstep ih =>
      have hmidphase := phase_cap_before_step 1 hstep hphase
      have hmidmcr := roleMCRCount_zero_of_reachable hprev hmcr
      obtain ⟨hmPrev, hcPrev, hrPrev⟩ := ih hmidphase
      obtain ⟨hmStep, hcStep, hrStep⟩ :=
        role_counts_step_early hstep hmidmcr hphase
      exact ⟨hmStep.trans hmPrev, hcPrev.trans hcStep, hrPrev.trans hrStep⟩

theorem role_counts_trace_to_all_one (init : Cfg L K) (ω : Ω L K)
    (s t : ℕ) (hst : s ≤ t)
    (hmcr : roleMCRCount (trace init ω s) = 0)
    (hone : ∀ a ∈ trace init ω t, a.phase.val = 1) :
    mainCount (trace init ω t) = mainCount (trace init ω s) ∧
      clockCount (trace init ω s) ≤ clockCount (trace init ω t) ∧
      reserveCount (trace init ω s) ≤ reserveCount (trace init ω t) :=
  role_counts_reachable_early (TimeTheorem.trace_reachable init ω hst)
    hmcr (fun a ha => le_of_eq (hone a ha))

theorem phase_one_entry_profile_from_role_counts {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (ω : InputLog n) (s t : ℕ) (hst : s ≤ t)
    (hmcr : roleMCRCount (trace init ω s) = 0)
    (hmainlo : (99 / 200 : ℝ) * (n : ℝ) ≤
      (mainCount (trace init ω s) : ℝ))
    (hmainhi : (mainCount (trace init ω s) : ℝ) ≤
      (101 / 200 : ℝ) * (n : ℝ))
    (hclock : (97 / 400 : ℝ) * (n : ℝ) ≤
      (clockCount (trace init ω s) : ℝ))
    (hreserve : (97 / 400 : ℝ) * (n : ℝ) ≤
      (reserveCount (trace init ω s) : ℝ))
    (hone : ∀ a ∈ trace init ω t, a.phase.val = 1)
    (hcounter : ∀ a ∈ trace init ω t, a.role = .clock →
      30 * PhaseThreeModel.Numeric.clockHours n ≤ a.counter.val) :
    PhaseOneEntryProfile init ω t := by
  obtain ⟨hmain, hclockMono, hreserveMono⟩ :=
    role_counts_trace_to_all_one init ω s t hst hmcr hone
  have hclockReal :
      (clockCount (trace init ω s) : ℝ) ≤
        (clockCount (trace init ω t) : ℝ) := by exact_mod_cast hclockMono
  have hreserveReal :
      (reserveCount (trace init ω s) : ℝ) ≤
        (reserveCount (trace init ω t) : ℝ) := by exact_mod_cast hreserveMono
  exact phase_one_entry_profile_of_bounds init hinput ω t hone
    (by simpa only [hmain] using hmainlo)
    (by simpa only [hmain] using hmainhi)
    (hclock.trans hclockReal) (hreserve.trans hreserveReal) hcounter

/-! ## Composition of the role stages at fixed offsets -/

noncomputable def phaseZeroRoleHorizon (n : ℕ) : ℕ :=
  80001 * n + logWindow n 20

/-- The state information needed before waiting for the first seed. -/
def PhaseZeroRoleReady (n : ℕ) (c : Cfg L K) : Prop :=
  c.card = n ∧ Phase0Window.allPhase0 c ∧ roleMCRCount c = 0 ∧
    (99 / 200 : ℝ) * (n : ℝ) ≤ (mainCount c : ℝ) ∧
    (mainCount c : ℝ) ≤ (101 / 200 : ℝ) * (n : ℝ) ∧
    (97 / 400 : ℝ) * (n : ℝ) ≤ (clockCount c : ℝ) ∧
    (97 / 400 : ℝ) * (n : ℝ) ≤ (reserveCount c : ℝ)

/-- The successful role event retains its complete Phase-0 past. -/
def PhaseZeroRoleReadyAt {n : ℕ} (init : InputCfg n)
    (ω : InputLog n) (T : ℕ) : Prop :=
  (∀ t ≤ T, Phase0Window.allPhase0 (trace init ω t)) ∧
    PhaseZeroRoleReady n (trace init ω T)

theorem phaseZero_mcr_prefix_tail {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    law init {ω |
      PhaseZeroRoles.rolePhaseZeroPrefix init (n + logWindow n 20) ω ∧
        0 < roleMCRCount (trace init ω (n + logWindow n 20))} ≤
      ENNReal.ofReal (2 * Real.exp (-(n : ℝ) / 1000)) +
        ENNReal.ofReal (1 / (n : ℝ) ^ 3) := by
  let F : Set (InputLog n) := {ω |
    PhaseZeroRoles.rolePhaseZeroPrefix init n ω ∧
      (freeTargetCount (trace init ω n) : ℝ) < (n : ℝ) / 10}
  let M : Set (InputLog n) := {ω |
    PhaseZeroRoles.rolePhaseZeroPrefix init (n + logWindow n 20) ω ∧
      0 < roleMCRCount (trace init ω (n + logWindow n 20)) ∧
      (n : ℝ) / 10 ≤ (freeTargetCount (trace init ω n) : ℝ)}
  have hsub : {ω |
      PhaseZeroRoles.rolePhaseZeroPrefix init (n + logWindow n 20) ω ∧
        0 < roleMCRCount (trace init ω (n + logWindow n 20))} ⊆ F ∪ M := by
    rintro ω ⟨hp, hm⟩
    by_cases hf : (freeTargetCount (trace init ω n) : ℝ) < (n : ℝ) / 10
    · exact Or.inl ⟨fun t ht => hp t (by omega), hf⟩
    · exact Or.inr ⟨hp, hm, le_of_not_gt hf⟩
  exact (measure_mono hsub).trans
    ((measure_union_le F M).trans
      (add_le_add (PhaseZeroRoles.role_fresh_pool_actual_tail_ennreal init hinput)
        (PhaseZeroRoles.role_mcr_joint_actual_tail_ennreal init hinput)))

theorem phaseZero_exponential_budget {n : ℕ}
    (hpop : timePopulationThreshold ≤ n) :
    Real.exp (-(n : ℝ) / 1000) ≤ 1 / (n : ℝ) ^ 3 := by
  obtain ⟨hnpos, hlog⟩ := PhaseOneDrain.population_calibration hpop
  have hlogpos : 0 < Real.log (n : ℝ) := by linarith only [hlog]
  have hquad : Real.log (n : ℝ) ^ 2 / 2 ≤ (n : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (Real.log (n : ℝ)) hlogpos.le 2
    norm_num at h ⊢
    simpa only [Real.exp_log hnpos] using h
  have hfactor : 0 ≤ Real.log (n : ℝ) * (Real.log (n : ℝ) - 6000) :=
    mul_nonneg hlogpos.le (by linarith only [hlog])
  have hlinear : 3 * Real.log (n : ℝ) ≤ (n : ℝ) / 1000 := by
    nlinarith only [hquad, hfactor]
  have hpower : Real.exp (3 * Real.log (n : ℝ)) = (n : ℝ) ^ 3 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hnpos] using
      (Real.exp_nat_mul (Real.log (n : ℝ)) 3)
  calc
    Real.exp (-(n : ℝ) / 1000) ≤
        Real.exp (-(3 * Real.log (n : ℝ))) :=
      Real.exp_le_exp.mpr (by linarith only [hlinear])
    _ = 1 / (n : ℝ) ^ 3 := by rw [Real.exp_neg, hpower, one_div]

theorem phaseZero_role_budget {n : ℕ}
    (hpop : timePopulationThreshold ≤ n) :
    ((ENNReal.ofReal (1 / (n : ℝ) ^ 6) +
        (ENNReal.ofReal (2 * Real.exp (-(n : ℝ) / 1000)) +
          ENNReal.ofReal (1 / (n : ℝ) ^ 3))) +
        ENNReal.ofReal (Real.exp (-(n : ℝ) / 1000))) +
        ENNReal.ofReal (1 / (n : ℝ) ^ 3) ≤
      ENNReal.ofReal (7 / (n : ℝ) ^ 3) := by
  obtain ⟨hnpos, _⟩ := PhaseOneDrain.population_calibration hpop
  have hnOne : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast
      ((by norm_num : (1 : ℕ) ≤ 40).trans
        (time_population_bounds hpop).2)
  have hsmall : 1 / (n : ℝ) ^ 6 ≤ 1 / (n : ℝ) ^ 3 := by
    rw [div_le_div_iff₀ (pow_pos hnpos 6) (pow_pos hnpos 3)]
    simpa only [one_mul] using
      pow_le_pow_right₀ hnOne (by norm_num : 3 ≤ 6)
  have he := phaseZero_exponential_budget hpop
  have hz : 0 ≤ 1 / (n : ℝ) ^ 3 := by positivity
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (7 : ℝ) * (1 / (n : ℝ) ^ 3) := by
      linarith only [hsmall, he, hz]
    _ = 7 / (n : ℝ) ^ 3 := by ring

/-- The roles have the needed counts by a fixed deadline, while the recorded
past is still Phase 0. All probabilities remain under the original law. -/
theorem phase_zero_role_ready_estimate {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    law init {ω | ¬ PhaseZeroRoleReadyAt init ω (phaseZeroRoleHorizon n)} ≤
      ENNReal.ofReal (7 / (n : ℝ) ^ 3) := by
  classical
  let s : ℕ := n + logWindow n 20
  let T : ℕ := phaseZeroRoleHorizon n
  have hsT : s ≤ T := by dsimp [s, T, phaseZeroRoleHorizon]; omega
  have hdeadline : s + 80000 * n = T := by
    dsimp [s, T, phaseZeroRoleHorizon]
    omega
  have hinit := phase0InitialFresh_of_validInitial
    n init hinput.2.1 hinput.2.2
  have hn : 200 ≤ n :=
    (by norm_num : (200 : ℕ) ≤ 2 ^ 24).trans
      (phase_zero_population_lower hinput.1)
  have hcard (ω : InputLog n) (t : ℕ) : (trace init ω t).card = n :=
    (Protocol.reachable_card_eq
      (phase_zero_trace_reachable init ω t)).trans hinput.2.2
  let E : Set (InputLog n) := {ω |
    ∃ u ≤ T, ¬ phaseZeroEarlyWindow n (trace init ω u)}
  let M : Set (InputLog n) := {ω |
    PhaseZeroRoles.rolePhaseZeroPrefix init s ω ∧
      0 < roleMCRCount (trace init ω s)}
  let A : Set ((k : Finset.Iic s) →
      Draw (PhaseThreeModel.Numeric.hourIndex n) 256) :=
    {p | prefixCfg init s p ∈ noMCRCRPhase0Shell n}
  let C : Set (InputLog n) := {ω |
    frestrictLe (π := fun _ : ℕ =>
      Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A ∧
      n / 100 < crCount (trace init ω T)}
  let B : Set (InputLog n) := {ω |
    (∀ t ≤ T, Phase0Window.allPhase0 (trace init ω t)) ∧
      ¬ TopSplitWindow (1 / 100 : ℝ) n (trace init ω T)}
  have hE : law init E ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 6) :=
    phase_zero_early_window_tail init hinit.1 (by omega) T
      (phaseZero_role_horizon_extended_le hinput.1)
  have hM : law init M ≤
      ENNReal.ofReal (2 * Real.exp (-(n : ℝ) / 1000)) +
        ENNReal.ofReal (1 / (n : ℝ) ^ 3) :=
    phaseZero_mcr_prefix_tail init hinput
  have hC : law init C ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) / 1000)) := by
    have h := cr_clearance_tail_from init hn s A (fun _ hp => hp)
    rw [hdeadline] at h
    have hprob : law init {ω |
        frestrictLe (π := fun _ : ℕ =>
          Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A} ≤ 1 := by
      calc
        _ ≤ law init Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    exact h.trans (by simpa only [mul_one] using
      mul_le_mul_left' hprob (ENNReal.ofReal (Real.exp (-(n : ℝ) / 1000))))
  have hB : law init B ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 3) :=
    phaseZero_balance_role_horizon_tail init hinput
  have hsub : {ω | ¬ PhaseZeroRoleReadyAt init ω T} ⊆ ((E ∪ M) ∪ C) ∪ B := by
    intro ω hbad
    by_cases hEω : ω ∈ E
    · exact Or.inl (Or.inl (Or.inl hEω))
    have hwindow (u : ℕ) (hu : u ≤ T) :
        phaseZeroEarlyWindow n (trace init ω u) := by
      by_contra h
      exact hEω ⟨u, hu, h⟩
    have hall (u : ℕ) (hu : u ≤ T) :
        Phase0Window.allPhase0 (trace init ω u) := (hwindow u hu).2.1
    by_cases hm : roleMCRCount (trace init ω s) = 0
    · have hshell : trace init ω s ∈ noMCRCRPhase0Shell n :=
        ⟨hcard ω s, hm, fun a ha _ => congrArg Fin.val (hall s hsT a ha)⟩
      have hmT : roleMCRCount (trace init ω T) = 0 :=
        roleMCRCount_zero_of_reachable
          (TimeTheorem.trace_reachable init ω (s := s) (t := T) hsT) hm
      by_cases hc : crCount (trace init ω T) ≤ n / 100
      · by_cases hb : TopSplitWindow (1 / 100 : ℝ) n (trace init ω T)
        · have hbalance := phaseZero_clockReserve_trace_prefix init ω T hinit
            (fun u hu => hall u hu.le) T le_rfl
          obtain ⟨hmlo, hmhi⟩ :=
            main_bounds_of_top_split (trace init ω T) (hcard ω T) hmT hb
          obtain ⟨hclo, hrlo⟩ :=
            clock_reserve_lower_of_cutoff (trace init ω T)
              (hcard ω T) hmT hbalance hmhi hc
          exact (hbad ⟨hall,
            hcard ω T, hall T le_rfl, hmT, hmlo, hmhi, hclo, hrlo⟩).elim
        · exact Or.inr ⟨hall, hb⟩
      · exact Or.inl (Or.inr ⟨hshell, Nat.lt_of_not_ge hc⟩)
    · exact Or.inl (Or.inl (Or.inr
        ⟨fun u hu => hall u (hu.le.trans hsT), by omega⟩))
  calc
    law init {ω | ¬ PhaseZeroRoleReadyAt init ω (phaseZeroRoleHorizon n)}
        ≤ law init (((E ∪ M) ∪ C) ∪ B) := measure_mono hsub
    _ ≤ law init ((E ∪ M) ∪ C) + law init B := measure_union_le _ _
    _ ≤ (law init (E ∪ M) + law init C) + law init B :=
      add_le_add (measure_union_le (E ∪ M) C) le_rfl
    _ ≤ ((law init E + law init M) + law init C) + law init B :=
      add_le_add (add_le_add (measure_union_le E M) le_rfl) le_rfl
    _ ≤ ((ENNReal.ofReal (1 / (n : ℝ) ^ 6) +
        (ENNReal.ofReal (2 * Real.exp (-(n : ℝ) / 1000)) +
          ENNReal.ofReal (1 / (n : ℝ) ^ 3))) +
        ENNReal.ofReal (Real.exp (-(n : ℝ) / 1000))) +
        ENNReal.ofReal (1 / (n : ℝ) ^ 3) :=
      add_le_add (add_le_add (add_le_add hE hM) hC) hB
    _ ≤ ENNReal.ofReal (7 / (n : ℝ) ^ 3) := phaseZero_role_budget hinput.1

/-! ## First-seed timing from the minimum Clock counter -/

open Classical in
noncomputable def clockLevel (c : Cfg L K) : ℕ :=
  if h : ∃ k, ∃ a ∈ c, a.role = .clock ∧ a.counter.val = k
  then
    @Nat.find
      (fun k => ∃ a ∈ c, a.role = .clock ∧ a.counter.val = k)
      (fun k =>
        Classical.propDecidable
          (∃ a ∈ c, a.role = .clock ∧ a.counter.val = k))
      h + 1
  else 0

open Classical in
noncomputable def phaseZeroClockLevel (c : Cfg L K) : ℕ :=
  if Phase0Window.allPhase0 c then clockLevel c else 0

theorem clockLevel_le_of_mem (c : Cfg L K) (a : AgentState L K)
    (ha : a ∈ c) (hc : a.role = .clock) :
    clockLevel c ≤ a.counter.val + 1 := by
  classical
  let P : ℕ → Prop :=
    fun k => ∃ a ∈ c, a.role = .clock ∧ a.counter.val = k
  let decP : DecidablePred P :=
    fun k => Classical.propDecidable (P k)
  have hex : ∃ k, P k := ⟨a.counter.val, a, ha, hc, rfl⟩
  rw [clockLevel, dif_pos hex]
  change @Nat.find P decP hex + 1 ≤ a.counter.val + 1
  exact Nat.add_le_add_right
    (@Nat.find_min' P decP hex a.counter.val ⟨a, ha, hc, rfl⟩) 1

theorem clockLevel_witness (c : Cfg L K)
    (hc : 0 < clockCount c) :
    ∃ a ∈ c, a.role = .clock ∧ clockLevel c = a.counter.val + 1 := by
  classical
  let P : ℕ → Prop :=
    fun k => ∃ a ∈ c, a.role = .clock ∧ a.counter.val = k
  let decP : DecidablePred P :=
    fun k => Classical.propDecidable (P k)
  have hclock : ∃ a ∈ c, a.role = .clock :=
    Multiset.countP_pos.mp hc
  have hex : ∃ k, P k := by
    obtain ⟨a, ha, hr⟩ := hclock
    exact ⟨a.counter.val, a, ha, hr, rfl⟩
  obtain ⟨a, ha, hr, hk⟩ := @Nat.find_spec P decP hex
  refine ⟨a, ha, hr, ?_⟩
  rw [clockLevel, dif_pos hex]
  change @Nat.find P decP hex + 1 = a.counter.val + 1
  omega

theorem clockLevel_le_cap (c : Cfg L K) :
    clockLevel c ≤ 50 * (L + 1) + 1 := by
  classical
  let P : ℕ → Prop :=
    fun k => ∃ a ∈ c, a.role = .clock ∧ a.counter.val = k
  let decP : DecidablePred P :=
    fun k => Classical.propDecidable (P k)
  unfold clockLevel
  split_ifs with h
  · obtain ⟨a, _, _, ha⟩ := @Nat.find_spec P decP h
    change @Nat.find P decP h + 1 ≤ 50 * (L + 1) + 1
    have hcap := a.counter.isLt
    omega
  · omega

theorem phaseZeroClockLevel_le_cap (c : Cfg L K) :
    phaseZeroClockLevel c ≤ 50 * (L + 1) + 1 := by
  classical
  unfold phaseZeroClockLevel
  split_ifs
  · exact clockLevel_le_cap c
  · omega

theorem phaseZeroClockLevel_le_of_mem (c : Cfg L K) (a : AgentState L K)
    (ha : a ∈ c) (hc : a.role = .clock) :
    phaseZeroClockLevel c ≤ a.counter.val + 1 := by
  classical
  unfold phaseZeroClockLevel
  split_ifs
  · exact clockLevel_le_of_mem c a ha hc
  · omega

theorem phaseZeroClockLevel_label_minimizer {m : ℕ}
    (f : Fin m → AgentState L K)
    (hall : Phase0Window.allPhase0 (labelCfg f))
    (hc : 0 < clockCount (labelCfg f)) :
    ∃ i, (f i).role = .clock ∧
      phaseZeroClockLevel (labelCfg f) = (f i).counter.val + 1 := by
  obtain ⟨a, ha, hr, hlev⟩ := clockLevel_witness (labelCfg f) hc
  change a ∈ (Finset.univ : Finset (Fin m)).val.map f at ha
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp ha
  refine ⟨i, hr, ?_⟩
  rw [phaseZeroClockLevel, if_pos hall]
  exact hlev

/-- Clock counter zero is tested before the decrement. The level therefore
contains the extra one corresponding to the advancing interaction. -/
theorem phaseZero_clock_left_data (a b : AgentState L K)
    (ha : a.phase.val = 0) (hb : b.phase.val = 0)
    (hclock : a.role = .clock) (hbmcr : b.role ≠ .mcr) :
    ((NonuniformMajority L K).δ a b).1.role = .clock ∧
      (((NonuniformMajority L K).δ a b).1.phase.val = 0 →
        ((NonuniformMajority L K).δ a b).1.counter.val ≤ a.counter.val ∧
          (b.role = .clock →
            ((NonuniformMajority L K).δ a b).1.counter.val + 1 ≤ a.counter.val)) := by
  classical
  have hraw :
      (Phase0Transition L K a b).1 =
        if b.role = .clock then stdCounterSubroutine L K a else a := by
    simp [Phase0Transition, hclock, hbmcr]
  rw [← PhaseZeroRoles.phaseZeroRoleRule_eq_transition a b ha hb]
  simp only [PhaseZeroRoles.phaseZeroRoleRule, finishPhase10Entry_role,
    finishPhase10Entry_phase_val, finishPhase10Entry_counter, hraw]
  by_cases hbc : b.role = .clock
  · rw [if_pos hbc]
    refine ⟨stdCounterSubroutine_clock_role_eq L K a hclock, ?_⟩
    intro hout
    have hz : a.counter.val ≠ 0 := by
      intro hz
      have hphase : (stdCounterSubroutine L K a).phase.val = 1 := by
        simp [stdCounterSubroutine, hz, advancePhaseWithInit, advancePhase,
          phaseInit, ha, hclock]
      omega
    have hcounter : (stdCounterSubroutine L K a).counter.val = a.counter.val - 1 := by
      simp [stdCounterSubroutine, hz]
    rw [hcounter]
    exact ⟨Nat.sub_le _ _, fun _ => by omega⟩
  · rw [if_neg hbc]
    exact ⟨hclock, fun _ => ⟨le_rfl, fun h => (hbc h).elim⟩⟩

theorem phaseZero_clock_right_data (a b : AgentState L K)
    (ha : a.phase.val = 0) (hb : b.phase.val = 0)
    (hamcr : a.role ≠ .mcr) (hclock : b.role = .clock) :
    ((NonuniformMajority L K).δ a b).2.role = .clock ∧
      (((NonuniformMajority L K).δ a b).2.phase.val = 0 →
        ((NonuniformMajority L K).δ a b).2.counter.val ≤ b.counter.val ∧
          (a.role = .clock →
            ((NonuniformMajority L K).δ a b).2.counter.val + 1 ≤ b.counter.val)) := by
  classical
  have hraw :
      (Phase0Transition L K a b).2 =
        if a.role = .clock then stdCounterSubroutine L K b else b := by
    simp [Phase0Transition, hamcr, hclock]
  rw [← PhaseZeroRoles.phaseZeroRoleRule_eq_transition a b ha hb]
  simp only [PhaseZeroRoles.phaseZeroRoleRule, finishPhase10Entry_role,
    finishPhase10Entry_phase_val, finishPhase10Entry_counter, hraw]
  by_cases hac : a.role = .clock
  · rw [if_pos hac]
    refine ⟨stdCounterSubroutine_clock_role_eq L K b hclock, ?_⟩
    intro hout
    have hz : b.counter.val ≠ 0 := by
      intro hz
      have hphase : (stdCounterSubroutine L K b).phase.val = 1 := by
        simp [stdCounterSubroutine, hz, advancePhaseWithInit, advancePhase,
          phaseInit, hb, hclock]
      omega
    have hcounter : (stdCounterSubroutine L K b).counter.val = b.counter.val - 1 := by
      simp [stdCounterSubroutine, hz]
    rw [hcounter]
    exact ⟨Nat.sub_le _ _, fun _ => by omega⟩
  · rw [if_neg hac]
    exact ⟨hclock, fun _ => ⟨le_rfl, fun h => (hac h).elim⟩⟩

theorem phaseZero_clock_updateLabels_data {m : ℕ}
    (f : Fin m → AgentState L K)
    (hall : Phase0Window.allPhase0 (labelCfg f))
    (hmcr : roleMCRCount (labelCfg f) = 0)
    (i j : Fin m) (hij : i ≠ j) (k : Fin m) (hck : (f k).role = .clock) :
    (updateLabels f i j k).role = .clock ∧
      ((updateLabels f i j k).phase.val = 0 →
        (updateLabels f i j k).counter.val ≤ (f k).counter.val ∧
          (((k = i ∧ (f j).role = .clock) ∨ (k = j ∧ (f i).role = .clock)) →
            (updateLabels f i j k).counter.val + 1 ≤ (f k).counter.val)) := by
  classical
  have hp (l : Fin m) : (f l).phase.val = 0 :=
    congrArg Fin.val (hall _ (PhaseZeroRoles.role_label_mem f l))
  have hn (l : Fin m) : (f l).role ≠ .mcr :=
    not_mcr_of_mem_noMCR hmcr (PhaseZeroRoles.role_label_mem f l)
  by_cases hki : k = i
  · subst k
    simpa [updateLabels, hij, Ne.symm hij] using
      phaseZero_clock_left_data (f i) (f j) (hp i) (hp j) hck (hn j)
  · by_cases hkj : k = j
    · subst k
      simpa [updateLabels, hij, Ne.symm hij] using
        phaseZero_clock_right_data (f i) (f j) (hp i) (hp j) (hn i) hck
    · simp [updateLabels, hki, hkj, hck]

theorem phaseZero_clock_stepLabels_role {m : ℕ}
    (f : Fin m → AgentState L K)
    (hall : Phase0Window.allPhase0 (labelCfg f))
    (hmcr : roleMCRCount (labelCfg f) = 0)
    (d : Draw L K) (k : Fin m) (hck : (f k).role = .clock) :
    (stepLabels f d k).role = .clock := by
  classical
  cases hsel : selectLabels f d with
  | none => simpa only [stepLabels, hsel] using hck
  | some pair =>
      obtain ⟨i, j⟩ := pair
      have hij := selectLabels_distinct f d i j hsel
      simpa only [stepLabels, hsel] using
        (phaseZero_clock_updateLabels_data f hall hmcr i j hij k hck).1

theorem clock_labels_card {m : ℕ} (f : Fin m → AgentState L K) :
    (Finset.univ.filter (fun i => (f i).role = .clock)).card =
      clockCount (labelCfg f) := by
  unfold clockCount labelCfg
  exact (Multiset.countP_map f (Finset.univ : Finset (Fin m)).val
    (fun a : AgentState L K => a.role = .clock)).symm

theorem phaseZero_clockCount_applyDraw_le (c : Cfg L K)
    (hall : Phase0Window.allPhase0 c)
    (hmcr : roleMCRCount c = 0) (d : Draw L K) :
    clockCount c ≤ clockCount (applyDraw c d) := by
  classical
  let f := initialLabels c
  have hf : labelCfg f = c := initialLabels_config c
  have hphase : Phase0Window.allPhase0 (labelCfg f) := hf.symm ▸ hall
  have hnomcr : roleMCRCount (labelCfg f) = 0 := hf.symm ▸ hmcr
  have hsub :
      Finset.univ.filter (fun i => (f i).role = .clock) ⊆
        Finset.univ.filter (fun i => (stepLabels f d i).role = .clock) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      phaseZero_clock_stepLabels_role f hphase hnomcr d i
        (Finset.mem_filter.mp hi).2⟩
  calc
    clockCount c = (Finset.univ.filter (fun i => (f i).role = .clock)).card := by
      rw [clock_labels_card, hf]
    _ ≤ (Finset.univ.filter (fun i => (stepLabels f d i).role = .clock)).card :=
      Finset.card_le_card hsub
    _ = clockCount (applyDraw c d) := by
      rw [clock_labels_card, stepLabels_config, hf]

theorem phaseZeroClockLevel_stepLabels_le {m : ℕ}
    (f : Fin m → AgentState L K)
    (hall : Phase0Window.allPhase0 (labelCfg f))
    (hmcr : roleMCRCount (labelCfg f) = 0)
    (hc : 0 < clockCount (labelCfg f)) (d : Draw L K) :
    phaseZeroClockLevel (labelCfg (stepLabels f d)) ≤
      phaseZeroClockLevel (labelCfg f) := by
  classical
  obtain ⟨k, hck, hk⟩ := phaseZeroClockLevel_label_minimizer f hall hc
  by_cases hout : Phase0Window.allPhase0 (labelCfg (stepLabels f d))
  · cases hsel : selectLabels f d with
    | none => simp only [stepLabels, hsel, le_refl]
    | some pair =>
        obtain ⟨i, j⟩ := pair
        have hij := selectLabels_distinct f d i j hsel
        have hdata := phaseZero_clock_updateLabels_data f hall hmcr i j hij k hck
        have hp : (updateLabels f i j k).phase.val = 0 := by
          have h := congrArg Fin.val
            (hout _ (PhaseZeroRoles.role_label_mem (stepLabels f d) k))
          simpa only [stepLabels, hsel] using h
        have hcounter := (hdata.2 hp).1
        have hlev := phaseZeroClockLevel_le_of_mem
          (labelCfg (updateLabels f i j)) (updateLabels f i j k)
          (PhaseZeroRoles.role_label_mem (updateLabels f i j) k) hdata.1
        simp only [stepLabels, hsel]
        omega
  · rw [phaseZeroClockLevel, if_neg hout]
    exact Nat.zero_le _

theorem phaseZeroClockLevel_applyDraw_le (c : Cfg L K)
    (hall : Phase0Window.allPhase0 c)
    (hmcr : roleMCRCount c = 0)
    (hc : 0 < clockCount c) (d : Draw L K) :
    phaseZeroClockLevel (applyDraw c d) ≤ phaseZeroClockLevel c := by
  let f := initialLabels c
  have hf : labelCfg f = c := initialLabels_config c
  have h := phaseZeroClockLevel_stepLabels_le f
    (hf.symm ▸ hall) (hf.symm ▸ hmcr) (hf.symm ▸ hc) d
  rwa [stepLabels_config, hf] at h

theorem phaseZeroClockLevel_selected_drop {m : ℕ}
    (f : Fin m → AgentState L K)
    (hall : Phase0Window.allPhase0 (labelCfg f))
    (hmcr : roleMCRCount (labelCfg f) = 0)
    (d : Draw L K) (i j k : Fin m)
    (hsel : selectLabels f d = some (i, j))
    (hci : (f i).role = .clock) (hcj : (f j).role = .clock)
    (hk : k = i ∨ k = j)
    (hmin : phaseZeroClockLevel (labelCfg f) = (f k).counter.val + 1) :
    phaseZeroClockLevel (applyDraw (labelCfg f) d) + 1 ≤
      phaseZeroClockLevel (labelCfg f) := by
  classical
  rw [← stepLabels_config]
  by_cases hout : Phase0Window.allPhase0 (labelCfg (stepLabels f d))
  · have hij := selectLabels_distinct f d i j hsel
    have hck : (f k).role = .clock := by
      rcases hk with rfl | rfl
      · exact hci
      · exact hcj
    have hdata := phaseZero_clock_updateLabels_data f hall hmcr i j hij k hck
    have hp : (updateLabels f i j k).phase.val = 0 := by
      have h := congrArg Fin.val
        (hout _ (PhaseZeroRoles.role_label_mem (stepLabels f d) k))
      simpa only [stepLabels, hsel] using h
    have hdrop := (hdata.2 hp).2 (hk.elim
      (fun h => Or.inl ⟨h, hcj⟩) (fun h => Or.inr ⟨h, hci⟩))
    have hlev := phaseZeroClockLevel_le_of_mem
      (labelCfg (updateLabels f i j)) (updateLabels f i j k)
      (PhaseZeroRoles.role_label_mem (updateLabels f i j) k) hdata.1
    simp only [stepLabels, hsel]
    omega
  · rw [phaseZeroClockLevel, if_neg hout, hmin]
    omega

theorem phaseZero_clock_star_scalar {n C : ℕ}
    (hn : 40 ≤ n) (hC : 97 * n ≤ 400 * C) :
    ENNReal.ofReal (2 / (5 * (n : ℝ))) ≤
      ((2 * (C - 1) : ℕ) : ℝ≥0∞) *
        ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹ := by
  have hnR : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have hCpos : 1 ≤ C := by omega
  have hCnat : n - 1 ≤ 5 * (C - 1) := by omega
  have hCsub : (n : ℝ) - 1 ≤ 5 * ((C : ℝ) - 1) := by
    have hcast : ((n - 1 : ℕ) : ℝ) ≤ 5 * ((C - 1 : ℕ) : ℝ) := by
      exact_mod_cast hCnat
    simpa only [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub hCpos,
      Nat.cast_one] using hcast
  have hnpos : 0 < (n : ℝ) := by linarith
  have hden : 0 < ((n * (n - 1) : ℕ) : ℝ) := by
    have hdenNat : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast hdenNat
  have hreal :
      2 / (5 * (n : ℝ)) ≤
        ((2 * (C - 1) : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hden).mpr
    push_cast [Nat.cast_sub hCpos, Nat.cast_sub (by omega : 1 ≤ n)]
    have hmul := mul_le_mul_of_nonneg_left hCsub
      (by positivity : 0 ≤ 2 * (n : ℝ))
    nlinarith
  have heq :
      ENNReal.ofReal (((2 * (C - 1) : ℕ) : ℝ) /
        ((n * (n - 1) : ℕ) : ℝ)) =
        ((2 * (C - 1) : ℕ) : ℝ≥0∞) *
          ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos hden, ENNReal.ofReal_natCast,
      ENNReal.ofReal_natCast, div_eq_mul_inv]
  exact (ENNReal.ofReal_le_ofReal hreal).trans heq.le

/-- Fix a minimizing occurrence and count all other Clock occurrences in
both orientations. This also covers equal state values. -/
theorem phaseZeroClockLevel_drop_mass {n : ℕ}
    (c : Cfg L K) (hn : 40 ≤ n)
    (hcard : c.card = n) (hall : Phase0Window.allPhase0 c)
    (hmcr : roleMCRCount c = 0)
    (hclock : 97 * n ≤ 400 * clockCount c) :
    ENNReal.ofReal (2 / (5 * (n : ℝ))) ≤
      (NonuniformMajority L K).transitionKernel c
        {c' | phaseZeroClockLevel c' + 1 ≤ phaseZeroClockLevel c} := by
  classical
  let f := initialLabels c
  have hf : labelCfg f = c := initialLabels_config c
  have hcf : 0 < clockCount (labelCfg f) := by rw [hf]; omega
  have hphase : Phase0Window.allPhase0 (labelCfg f) := hf.symm ▸ hall
  have hnomcr : roleMCRCount (labelCfg f) = 0 := hf.symm ▸ hmcr
  obtain ⟨i, hci, hmin⟩ := phaseZeroClockLevel_label_minimizer f hphase hcf
  let F : Finset (Fin c.card) :=
    Finset.univ.filter (fun j => (f j).role = .clock)
  let J := F.erase i
  have hiF : i ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hci⟩
  have hiJ : i ∉ J := by simp [J]
  have hFcard : F.card = clockCount c := by
    dsimp only [F]
    rw [clock_labels_card, hf]
  have hJcard : J.card = clockCount c - 1 := by
    dsimp only [J]
    rw [Finset.card_erase_of_mem hiF, hFcard]
  have hmass := selected_label_partner_mass f
    (by omega : 2 ≤ c.card) i J hiJ
  let E : Set (Draw L K) :=
    {d | ∃ j ∈ J, selectLabels f d = some (i, j) ∨
      selectLabels f d = some (j, i)}
  have hmassE :
      (drawLaw c).toMeasure E =
        ((2 * (clockCount c - 1) : ℕ) : ℝ≥0∞) *
          ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹ := by
    calc
      (drawLaw c).toMeasure E =
          ((2 * J.card : ℕ) : ℝ≥0∞) *
            ((c.card * (c.card - 1) : ℕ) : ℝ≥0∞)⁻¹ := by
        simpa only [E, hf] using hmass
      _ = _ := by rw [hJcard, hcard]
  let D : Set (Draw L K) :=
    {d | phaseZeroClockLevel (applyDraw c d) + 1 ≤ phaseZeroClockLevel c}
  have hsub : E ⊆ D := by
    rintro d ⟨j, hj, hd⟩
    have hcj : (f j).role = .clock :=
      (Finset.mem_filter.mp (Finset.mem_erase.mp hj).2).2
    rcases hd with hd | hd
    · have h := phaseZeroClockLevel_selected_drop f hphase hnomcr d i j i
        hd hci hcj (Or.inl rfl) hmin
      simpa only [D, Set.mem_setOf_eq, hf] using h
    · have h := phaseZeroClockLevel_selected_drop f hphase hnomcr d j i i
        hd hcj hci (Or.inr rfl) hmin
      simpa only [D, Set.mem_setOf_eq, hf] using h
  have hmap :
      (NonuniformMajority L K).transitionKernel c
        {c' | phaseZeroClockLevel c' + 1 ≤ phaseZeroClockLevel c} =
        (drawLaw c).toMeasure D := by
    rw [← drawLaw_map_toMeasure,
      Measure.map_apply (measurable_of_countable (applyDraw c))
        (Set.to_countable _).measurableSet]
    rfl
  calc
    ENNReal.ofReal (2 / (5 * (n : ℝ))) ≤
        ((2 * (clockCount c - 1) : ℕ) : ℝ≥0∞) *
          ((n * (n - 1) : ℕ) : ℝ≥0∞)⁻¹ :=
      phaseZero_clock_star_scalar hn hclock
    _ = (drawLaw c).toMeasure E := hmassE.symm
    _ ≤ (drawLaw c).toMeasure D := measure_mono hsub
    _ = _ := hmap.symm

def PhaseZeroClockWindow (n : ℕ) (c : Cfg L K) : Prop :=
  c.card = n ∧ Phase0Window.allPhase0 c ∧ roleMCRCount c = 0 ∧
    97 * n ≤ 400 * clockCount c

theorem phaseZeroClockLevel_drift {n : ℕ} (hn : 40 ≤ n)
    (c : Cfg L K) (hc : PhaseZeroClockWindow n c) :
    ∫⁻ c', ((2 ^ phaseZeroClockLevel c' : ℕ) : ℝ≥0∞)
        ∂(NonuniformMajority L K).transitionKernel c ≤
      (1 - ENNReal.ofReal (2 / (5 * (n : ℝ))) / 2) *
        ((2 ^ phaseZeroClockLevel c : ℕ) : ℝ≥0∞) := by
  exact TraceDrain.exp_drift_of_drop phaseZeroClockLevel c
    (phaseZeroClockLevel_applyDraw_le c hc.2.1 hc.2.2.1 (by
      have := hc.2.2.2
      omega))
    (ENNReal.ofReal (2 / (5 * (n : ℝ))))
    (phaseZeroClockLevel_drop_mass c hn hc.1 hc.2.1 hc.2.2.1 hc.2.2.2)

theorem phaseZero_late_exit_tail_raw {n : ℕ}
    (init : Cfg L K) (hn : 40 ≤ n) (s N : ℕ)
    (A : Set ((k : Finset.Iic s) → Draw L K))
    (hA : ∀ p ∈ A, PhaseZeroClockWindow n (prefixCfg init s p)) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        ∀ u, s ≤ u → u < s + N → Phase0Window.allPhase0 (trace init ω u)} ≤
      (1 - ENNReal.ofReal (2 / (5 * (n : ℝ))) / 2) ^ N *
        ((2 ^ (50 * (L + 1) + 1) : ℕ) : ℝ≥0∞) *
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  have h := TraceDrain.potential_drift_tail_from init
    (fun c => 2 ^ phaseZeroClockLevel c) (PhaseZeroClockWindow n)
    (ENNReal.ofReal (2 / (5 * (n : ℝ))) / 2)
    (phaseZeroClockLevel_drift hn) s N A (2 ^ (50 * (L + 1) + 1))
    (fun p _ => Nat.pow_le_pow_right (by norm_num) (phaseZeroClockLevel_le_cap _))
  refine (measure_mono ?_).trans h
  rintro ω ⟨hωA, hphase⟩
  have hstart : PhaseZeroClockWindow n (trace init ω s) :=
    hA (frestrictLe (π := fun _ : ℕ => Draw L K) s ω) hωA
  refine ⟨hωA, ?_, Nat.one_le_two_pow⟩
  intro u hsu huN
  have hreach := TimeTheorem.trace_reachable init ω hsu
  have hmcr : roleMCRCount (trace init ω u) = 0 :=
    roleMCRCount_zero_of_reachable hreach hstart.2.2.1
  have hclock :
      clockCount (trace init ω s) ≤ clockCount (trace init ω u) := by
    apply PhaseOneDrainProducer.trace_persist_of_window init ω
      (fun c => clockCount (trace init ω s) ≤ clockCount c)
      (fun c => Phase0Window.allPhase0 c ∧ roleMCRCount c = 0)
      (fun c hc hle d =>
        hle.trans (phaseZero_clockCount_applyDraw_le c hc.1 hc.2 d))
      s u hsu
    · intro v hsv hvu
      refine ⟨hphase v hsv (hvu.trans huN), ?_⟩
      exact roleMCRCount_zero_of_reachable
        (TimeTheorem.trace_reachable init ω hsv) hstart.2.2.1
    · exact le_rfl
  exact ⟨(Protocol.reachable_card_eq hreach).trans hstart.1,
    hphase u hsu huN, hmcr,
    hstart.2.2.2.trans (Nat.mul_le_mul_left 400 hclock)⟩

theorem phaseZero_late_exit_scalar {n : ℕ}
    (hpop : timePopulationThreshold ≤ n) :
    (1 - ENNReal.ofReal (2 / (5 * (n : ℝ))) / 2) ^
        (300 * n * PhaseThreeModel.Numeric.clockHours n) *
      ((2 ^ (50 * PhaseThreeModel.Numeric.clockHours n + 1) : ℕ) : ℝ≥0∞) ≤
        ENNReal.ofReal (1 / (n : ℝ) ^ 20) := by
  obtain ⟨hn, hnp, hlog, hHlo, _, _⟩ := time_hour_calibration hpop
  have hnR : (40 : ℝ) ≤ n := by exact_mod_cast hn
  have hrzero : 0 ≤ 2 / (5 * (n : ℝ)) := by positivity
  have hrone : 2 / (5 * (n : ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  have htime :
      ((300 * n * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ) *
          (2 / (5 * (n : ℝ))) / 2 =
        60 * (PhaseThreeModel.Numeric.clockHours n : ℝ) := by
    push_cast
    field_simp [hnp.ne'] <;> ring
  have hlogtwo : Real.log 2 ≤ (7 / 10 : ℝ) := by
    linarith only [Real.log_two_lt_d9]
  have hprod := mul_le_mul_of_nonneg_left hlogtwo
    (show 0 ≤ 50 * (PhaseThreeModel.Numeric.clockHours n : ℝ) + 1 by positivity)
  have hexponent :
      ((50 * PhaseThreeModel.Numeric.clockHours n + 1 : ℕ) : ℝ) * Real.log 2 -
          ((300 * n * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ) *
            (2 / (5 * (n : ℝ))) / 2 ≤
        -(20 * Real.log (n : ℝ)) := by
    rw [htime]
    push_cast
    linarith only [hprod, hHlo, hlog]
  have hexp :
      Real.exp (20 * Real.log (n : ℝ)) = (n : ℝ) ^ 20 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hnp] using
      Real.exp_nat_mul (Real.log (n : ℝ)) 20
  calc
    _ ≤ ENNReal.ofReal (Real.exp
        (((50 * PhaseThreeModel.Numeric.clockHours n + 1 : ℕ) : ℝ) * Real.log 2 -
          ((300 * n * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ) *
            (2 / (5 * (n : ℝ))) / 2)) :=
      PhaseOneDrainProducer.drain_scalar _ hrzero hrone _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(20 * Real.log (n : ℝ)))) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent)
    _ = ENNReal.ofReal (1 / (n : ℝ) ^ 20) := by
      rw [Real.exp_neg, hexp, one_div]

theorem phaseZero_late_exit_tail_from {n : ℕ}
    (init : InputCfg n) (hpop : timePopulationThreshold ≤ n) (s : ℕ)
    (A : Set ((k : Finset.Iic s) →
      Draw (PhaseThreeModel.Numeric.hourIndex n) 256))
    (hA : ∀ p ∈ A, PhaseZeroClockWindow n (prefixCfg init s p)) :
    law init {ω |
      frestrictLe (π := fun _ : ℕ =>
        Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A ∧
      ∀ u, s ≤ u →
        u < s + 300 * n * PhaseThreeModel.Numeric.clockHours n →
          Phase0Window.allPhase0 (trace init ω u)} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 20) *
        law init {ω |
          frestrictLe (π := fun _ : ℕ =>
            Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A} := by
  have h := phaseZero_late_exit_tail_raw init (time_population_bounds hpop).2
    s (300 * n * PhaseThreeModel.Numeric.clockHours n) A hA
  have hscalar := phaseZero_late_exit_scalar hpop
  have hbound := mul_le_mul_right' hscalar
    (law init {ω |
      frestrictLe (π := fun _ : ℕ =>
        Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A})
  exact h.trans (by simpa only [PhaseThreeModel.Numeric.clockHours] using hbound)

/-! ## Residual counters during the mixed Phase-0/Phase-1 epidemic -/

noncomputable def phaseOneSpreadWeight (a : AgentState L K) : ℝ≥0∞ :=
  if a.phase.val = 1 ∧ a.role = .clock then
    ENNReal.ofReal (Real.exp (Real.log 2 *
      (((50 * (L + 1) - a.counter.val : ℕ)) : ℝ)))
  else 1

theorem phaseOneSpreadWeight_le_twice_subcounter (k : ℕ) (hk : 0 < k) :
    ENNReal.ofReal (Real.exp (Real.log 2 *
      (((50 * (L + 1) - (k - 1) : ℕ)) : ℝ))) ≤
      2 * ENNReal.ofReal (Real.exp (Real.log 2 *
        (((50 * (L + 1) - k : ℕ)) : ℝ))) := by
  have h := Phase1ClockDepthStopped.depthWeight_sub_one_le
    (50 * (L + 1)) k (Real.log 2) (Real.log_nonneg (by norm_num)) hk
  simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2),
    show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num] using h

theorem phaseOneSpreadWeight_one_le (a : AgentState L K) :
    1 ≤ phaseOneSpreadWeight a := by
  unfold phaseOneSpreadWeight
  split_ifs
  · calc
      (1 : ℝ≥0∞) = ENNReal.ofReal (Real.exp 0) := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by positivity))
  · exact le_rfl

theorem phaseOneSpreadWeight_stdCounter_phase_zero
    (a : AgentState L K) (hp : a.phase.val = 0) (hr : a.role = .clock) :
    (stdCounterSubroutine L K a).phase.val ≤ 1 ∧
      phaseOneSpreadWeight (stdCounterSubroutine L K a) = 1 := by
  unfold stdCounterSubroutine
  split_ifs with hz
  · have hadv : advancePhase L K a = {a with phase := ⟨1, by decide⟩} := by
      unfold advancePhase
      rw [dif_pos (by omega)]
      congr 1
      exact Fin.ext (by simp [hp])
    have hreset : advancePhaseWithInit L K a =
        {a with phase := ⟨1, by decide⟩, counter := ⟨50 * (L + 1), (by omega)⟩} := by
      simp only [advancePhaseWithInit, hadv]
      rcases a with ⟨input, output, phase, role, assigned, bias, smallBias,
        hour, minute, full, opinions, counter⟩
      cases role with
      | main => cases hr
      | reserve => cases hr
      | clock => rfl
      | mcr => cases hr
      | cr => cases hr
    simp [hreset, hr, phaseOneSpreadWeight]
  · simp [hp, phaseOneSpreadWeight]

theorem phaseOneSpreadWeight_clockStep_phase_one
    (a : AgentState L K) (hp : a.phase.val = 1)
    (hpos : a.role = .clock → 0 < a.counter.val) :
    (clockCounterStep L K a).phase.val = 1 ∧
      phaseOneSpreadWeight (clockCounterStep L K a) ≤
        2 * phaseOneSpreadWeight a := by
  by_cases hr : a.role = .clock
  · have hk := hpos hr
    have hne : a.counter.val ≠ 0 := Nat.ne_of_gt hk
    constructor
    · simp [clockCounterStep, hr, stdCounterSubroutine, hne, hp]
    · simpa [clockCounterStep, hr, stdCounterSubroutine,
        hne, phaseOneSpreadWeight, hp] using
        phaseOneSpreadWeight_le_twice_subcounter (L := L) a.counter.val hk
  · norm_num [clockCounterStep, hr, hp, phaseOneSpreadWeight]

theorem phaseOneSpreadWeight_phase_zero_pair
    (a b : AgentState L K)
    (ha : a.phase.val = 0) (hb : b.phase.val = 0)
    (hma : a.role ≠ .mcr) (hmb : b.role ≠ .mcr) :
    (Phase0Transition L K a b).1.phase.val ≤ 1 ∧
      (Phase0Transition L K a b).2.phase.val ≤ 1 ∧
      phaseOneSpreadWeight (Phase0Transition L K a b).1 = 1 ∧
      phaseOneSpreadWeight (Phase0Transition L K a b).2 = 1 := by
  have hstd := phaseOneSpreadWeight_stdCounter_phase_zero (L := L) (K := K)
  by_cases hcr : a.role = .cr ∧ b.role = .cr
  · simp [Phase0Transition, hma, hmb, hcr, ha, hb, phaseOneSpreadWeight]
  · by_cases hclock : a.role = .clock ∧ b.role = .clock
    · have has := hstd a ha hclock.1
      have hbs := hstd b hb hclock.2
      simpa only [Phase0Transition, hma, hmb, false_and, and_false, if_false,
        if_neg hcr, if_pos hclock] using
        (show (stdCounterSubroutine L K a).phase.val ≤ 1 ∧
          (stdCounterSubroutine L K b).phase.val ≤ 1 ∧
          phaseOneSpreadWeight (stdCounterSubroutine L K a) = 1 ∧
          phaseOneSpreadWeight (stdCounterSubroutine L K b) = 1 from
          ⟨has.1, hbs.1, has.2, hbs.2⟩)
    · simp [Phase0Transition, hma, hmb, hcr, hclock, ha, hb,
        phaseOneSpreadWeight]

theorem phaseOneSpreadWeight_phase_one_pair
    (a b : AgentState L K)
    (ha : a.phase.val = 1) (hb : b.phase.val = 1)
    (hca : a.role = .clock → 0 < a.counter.val)
    (hcb : b.role = .clock → 0 < b.counter.val) :
    (Phase1Transition L K a b).1.phase.val = 1 ∧
      (Phase1Transition L K a b).2.phase.val = 1 ∧
      phaseOneSpreadWeight (Phase1Transition L K a b).1 ≤
        2 * phaseOneSpreadWeight a ∧
      phaseOneSpreadWeight (Phase1Transition L K a b).2 ≤
        2 * phaseOneSpreadWeight b := by
  by_cases hmain : a.role = .main ∧ b.role = .main
  · have hmainClock : (Role.main : Role) ≠ Role.clock := by decide
    norm_num [Phase1Transition, hmain, clockCounterStep, hmain.1, hmain.2,
      hmainClock, ha, hb, phaseOneSpreadWeight]
  · have has := phaseOneSpreadWeight_clockStep_phase_one a ha hca
    have hbs := phaseOneSpreadWeight_clockStep_phase_one b hb hcb
    rw [PhaseOnlyWindows.Phase1Transition_eq_of_not_both_main a b hmain]
    exact ⟨has.1, hbs.1, has.2, hbs.2⟩

def phaseOneSpreadLift (a : AgentState L K) : AgentState L K :=
  phaseInit L K ⟨1, by decide⟩ {a with phase := ⟨1, by decide⟩}

theorem phaseOneSpreadLift_phase (a : AgentState L K) (hm : a.role ≠ .mcr) :
    (phaseOneSpreadLift a).phase.val = 1 := by
  rcases a with ⟨input, output, phase, role, assigned, bias, smallBias,
    hour, minute, full, opinions, counter⟩
  cases role with
  | main => rfl
  | reserve => rfl
  | clock => rfl
  | mcr => exact (hm rfl).elim
  | cr => rfl

theorem phaseOneSpreadLift_clock_counter
    (a : AgentState L K) (hm : a.role ≠ .mcr)
    (hc : (phaseOneSpreadLift a).role = .clock) :
    (phaseOneSpreadLift a).counter.val = 50 * (L + 1) := by
  rcases a with ⟨input, output, phase, role, assigned, bias, smallBias,
    hour, minute, full, opinions, counter⟩
  cases role with
  | main =>
      change Role.main = Role.clock at hc
      cases hc
  | reserve =>
      change Role.reserve = Role.clock at hc
      cases hc
  | clock => rfl
  | mcr => exact (hm rfl).elim
  | cr =>
      change Role.reserve = Role.clock at hc
      cases hc

theorem phaseOneSpreadLift_weight (a : AgentState L K) (hm : a.role ≠ .mcr) :
    phaseOneSpreadWeight (phaseOneSpreadLift a) = 1 := by
  by_cases hc : (phaseOneSpreadLift a).role = .clock
  · simp [phaseOneSpreadWeight, phaseOneSpreadLift_phase a hm, hc,
      phaseOneSpreadLift_clock_counter a hm hc]
  · simp [phaseOneSpreadWeight, hc]

theorem phaseOneSpreadLift_clock_positive
    (a : AgentState L K) (hm : a.role ≠ .mcr)
    (hc : (phaseOneSpreadLift a).role = .clock) :
    0 < (phaseOneSpreadLift a).counter.val := by
  rw [phaseOneSpreadLift_clock_counter a hm hc]
  omega

theorem phaseOneSpreadLift_run_inits (a : AgentState L K) :
    runInitsBetween L K 0 1 {a with phase := ⟨1, by decide⟩} =
      phaseOneSpreadLift a := by
  have hlist : (List.range 11).filter (fun k => 0 < k ∧ k ≤ 1) = [1] := by decide
  unfold runInitsBetween
  rw [hlist] <;> rfl

theorem phaseOneSpread_epidemic_left
    (a b : AgentState L K) (ha : a.phase.val = 0) (hb : b.phase.val = 1)
    (hma : a.role ≠ .mcr) :
    phaseEpidemicUpdate L K a b = (phaseOneSpreadLift a, b) := by
  have hap : a.phase = ⟨0, by decide⟩ := Fin.ext ha
  have hbp : b.phase = ⟨1, by decide⟩ := Fin.ext hb
  have hmax : max a.phase b.phase = (⟨1, by decide⟩ : Fin 11) := by
    simp [hap, hbp]
  have hbself : ({b with phase := ⟨1, by decide⟩} : AgentState L K) = b := by
    rw [← hbp]
  have hinita :
      runInitsBetween L K a.phase.val (max a.phase b.phase).val
        {a with phase := max a.phase b.phase} = phaseOneSpreadLift a := by
    simpa only [hmax, ha, Fin.val_mk] using phaseOneSpreadLift_run_inits a
  have hinitb :
      runInitsBetween L K b.phase.val (max a.phase b.phase).val
        {b with phase := max a.phase b.phase} = b := by
    simpa only [hmax, hb, Fin.val_mk, runInitsBetween_self] using hbself
  have hnotten :
      ¬ ((phaseOneSpreadLift a).phase.val = 10 ∨ b.phase.val = 10) := by
    rw [phaseOneSpreadLift_phase a hma, hb]
    decide
  unfold phaseEpidemicUpdate
  dsimp only
  rw [hinita, hinitb] <;> exact if_neg (fun h => hnotten h.2)

theorem phaseOneSpread_epidemic_right
    (a b : AgentState L K) (ha : a.phase.val = 1) (hb : b.phase.val = 0)
    (hmb : b.role ≠ .mcr) :
    phaseEpidemicUpdate L K a b = (a, phaseOneSpreadLift b) := by
  have hap : a.phase = ⟨1, by decide⟩ := Fin.ext ha
  have hbp : b.phase = ⟨0, by decide⟩ := Fin.ext hb
  have hmax : max a.phase b.phase = (⟨1, by decide⟩ : Fin 11) := by
    simp [hap, hbp]
  have haself : ({a with phase := ⟨1, by decide⟩} : AgentState L K) = a := by
    rw [← hap]
  have hinita :
      runInitsBetween L K a.phase.val (max a.phase b.phase).val
        {a with phase := max a.phase b.phase} = a := by
    simpa only [hmax, ha, Fin.val_mk, runInitsBetween_self] using haself
  have hinitb :
      runInitsBetween L K b.phase.val (max a.phase b.phase).val
        {b with phase := max a.phase b.phase} = phaseOneSpreadLift b := by
    simpa only [hmax, hb, Fin.val_mk] using phaseOneSpreadLift_run_inits b
  have hnotten :
      ¬ (a.phase.val = 10 ∨ (phaseOneSpreadLift b).phase.val = 10) := by
    rw [ha, phaseOneSpreadLift_phase b hmb]
    decide
  unfold phaseEpidemicUpdate
  dsimp only
  rw [hinita, hinitb] <;> exact if_neg (fun h => hnotten h.2)

theorem phaseOneSpread_dispatch_one
    (a b e f : AgentState L K)
    (hpe : phaseEpidemicUpdate L K a b = (e, f))
    (he : e.phase.val = 1) :
    (Transition L K a b).1.phase.val = (Phase1Transition L K e f).1.phase.val ∧
      (Transition L K a b).2.phase.val = (Phase1Transition L K e f).2.phase.val ∧
      phaseOneSpreadWeight (Transition L K a b).1 =
        phaseOneSpreadWeight (Phase1Transition L K e f).1 ∧
      phaseOneSpreadWeight (Transition L K a b).2 =
        phaseOneSpreadWeight (Phase1Transition L K e f).2 := by
  have hep : e.phase = ⟨1, by decide⟩ := Fin.ext he
  unfold Transition
  rw [hpe]
  dsimp only
  rw [hep]
  simp only [finishPhase10Entry_phase_val, phaseOneSpreadWeight,
    finishPhase10Entry_role, finishPhase10Entry_counter, and_self]

theorem phaseOneSpread_dispatch_zero
    (a b : AgentState L K) (ha : a.phase.val = 0) (hb : b.phase.val = 0) :
    (Transition L K a b).1.phase.val = (Phase0Transition L K a b).1.phase.val ∧
      (Transition L K a b).2.phase.val = (Phase0Transition L K a b).2.phase.val ∧
      phaseOneSpreadWeight (Transition L K a b).1 =
        phaseOneSpreadWeight (Phase0Transition L K a b).1 ∧
      phaseOneSpreadWeight (Transition L K a b).2 =
        phaseOneSpreadWeight (Phase0Transition L K a b).2 := by
  have hap : a.phase = ⟨0, by decide⟩ := Fin.ext ha
  have hpe := phaseEpidemicUpdate_eq_self_of_both_phase0
    (L := L) (K := K) a b ha hb
  unfold Transition
  rw [hpe]
  dsimp only
  rw [hap]
  simp only [finishPhase10Entry_phase_val, phaseOneSpreadWeight,
    finishPhase10Entry_role, finishPhase10Entry_counter, and_self]

theorem phaseOneSpread_dispatch_one_bound
    (a b e f : AgentState L K)
    (hpe : phaseEpidemicUpdate L K a b = (e, f))
    (he : e.phase.val = 1) (hf : f.phase.val = 1)
    (hce : e.role = .clock → 0 < e.counter.val)
    (hcf : f.role = .clock → 0 < f.counter.val)
    (hwe : phaseOneSpreadWeight e = phaseOneSpreadWeight a)
    (hwf : phaseOneSpreadWeight f = phaseOneSpreadWeight b) :
    (Transition L K a b).1.phase.val ≤ 1 ∧
      (Transition L K a b).2.phase.val ≤ 1 ∧
      phaseOneSpreadWeight (Transition L K a b).1 ≤
        2 * phaseOneSpreadWeight a ∧
      phaseOneSpreadWeight (Transition L K a b).2 ≤
        2 * phaseOneSpreadWeight b := by
  have hd := phaseOneSpread_dispatch_one a b e f hpe he
  have hp := phaseOneSpreadWeight_phase_one_pair e f he hf hce hcf
  rw [hd.1, hd.2.1, hd.2.2.1, hd.2.2.2]
  exact ⟨hp.1.le, hp.2.1.le,
    by simpa only [hwe] using hp.2.2.1,
    by simpa only [hwf] using hp.2.2.2⟩

theorem phaseOneSpread_transition_bound
    (a b : AgentState L K)
    (ha : a.phase.val ≤ 1) (hb : b.phase.val ≤ 1)
    (hma : a.role ≠ .mcr) (hmb : b.role ≠ .mcr)
    (hca : a.phase.val = 1 → a.role = .clock → 0 < a.counter.val)
    (hcb : b.phase.val = 1 → b.role = .clock → 0 < b.counter.val) :
    (Transition L K a b).1.phase.val ≤ 1 ∧
      (Transition L K a b).2.phase.val ≤ 1 ∧
      phaseOneSpreadWeight (Transition L K a b).1 ≤
        2 * phaseOneSpreadWeight a ∧
      phaseOneSpreadWeight (Transition L K a b).2 ≤
        2 * phaseOneSpreadWeight b := by
  have haph : a.phase.val = 0 ∨ a.phase.val = 1 := by omega
  have hbph : b.phase.val = 0 ∨ b.phase.val = 1 := by omega
  rcases haph with haz | hao <;> rcases hbph with hbz | hbo
  · have hd := phaseOneSpread_dispatch_zero a b haz hbz
    have hp := phaseOneSpreadWeight_phase_zero_pair a b haz hbz hma hmb
    rw [hd.1, hd.2.1, hd.2.2.1, hd.2.2.2, hp.2.2.1, hp.2.2.2]
    exact ⟨hp.1, hp.2.1,
      by norm_num [phaseOneSpreadWeight, haz],
      by norm_num [phaseOneSpreadWeight, hbz]⟩
  · apply phaseOneSpread_dispatch_one_bound a b (phaseOneSpreadLift a) b
      (phaseOneSpread_epidemic_left a b haz hbo hma)
      (phaseOneSpreadLift_phase a hma) hbo
      (phaseOneSpreadLift_clock_positive a hma) (hcb hbo)
    · rw [phaseOneSpreadLift_weight a hma]
      simp [phaseOneSpreadWeight, haz]
    · rfl
  · apply phaseOneSpread_dispatch_one_bound a b a (phaseOneSpreadLift b)
      (phaseOneSpread_epidemic_right a b hao hbz hmb)
      hao (phaseOneSpreadLift_phase b hmb)
      (hca hao) (phaseOneSpreadLift_clock_positive b hmb)
    · rfl
    · rw [phaseOneSpreadLift_weight b hmb]
      simp [phaseOneSpreadWeight, hbz]
  · exact phaseOneSpread_dispatch_one_bound a b a b
      (Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1
        (L := L) (K := K) a b hao hbo)
      hao hbo (hca hao) (hcb hbo) rfl rfl

noncomputable def phaseOneSpreadRawMass (c : Cfg L K) : ℝ≥0∞ :=
  Config.sumOf phaseOneSpreadWeight c

def phaseOneSpreadWindow (n : ℕ) (c : Cfg L K) : Prop :=
  c.card = n ∧ roleMCRCount c = 0 ∧
    (∀ a ∈ c, a.phase.val ≤ 1) ∧
    ∀ a ∈ c, a.phase.val = 1 → a.role = .clock →
      30 * (L + 1) ≤ a.counter.val

noncomputable def phaseOneSpreadThreshold (L : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (Real.log 2 * ((20 * (L + 1) : ℕ) : ℝ)))

open Classical in
noncomputable def phaseOneSpreadStoppedMass (n : ℕ) (c : Cfg L K) : ℝ≥0∞ :=
  if phaseOneSpreadWindow n c then phaseOneSpreadRawMass c
  else phaseOneSpreadThreshold L

private theorem phaseOneSpread_sum_pair (c : Cfg L K) (a b : AgentState L K)
    (happ : Protocol.Applicable c a b) :
    phaseOneSpreadRawMass c =
      phaseOneSpreadRawMass (c - {a, b}) +
        (phaseOneSpreadWeight a + phaseOneSpreadWeight b) := by
  unfold phaseOneSpreadRawMass Config.sumOf
  rw [← Multiset.sub_add_cancel happ, Multiset.map_add, Multiset.sum_add]
  simp

private theorem phaseOneSpread_sum_step (c : Cfg L K) (a b : AgentState L K)
    (happ : Protocol.Applicable c a b) :
    phaseOneSpreadRawMass
        (Protocol.stepOrSelf (NonuniformMajority L K) c a b) =
      phaseOneSpreadRawMass (c - {a, b}) +
        (phaseOneSpreadWeight (Transition L K a b).1 +
          phaseOneSpreadWeight (Transition L K a b).2) := by
  unfold Protocol.stepOrSelf
  rw [if_pos happ]
  unfold phaseOneSpreadRawMass Config.sumOf
  rw [Multiset.map_add, Multiset.sum_add]
  simp [NonuniformMajority]

theorem phaseOneSpread_step_le (n : ℕ) (c : Cfg L K)
    (hc : phaseOneSpreadWindow n c) (a b : AgentState L K) :
    phaseOneSpreadRawMass
        (Protocol.stepOrSelf (NonuniformMajority L K) c a b) ≤
      phaseOneSpreadRawMass c +
        (phaseOneSpreadWeight a + phaseOneSpreadWeight b) := by
  classical
  by_cases happ : Protocol.Applicable c a b
  · have ha : a ∈ c := Multiset.mem_of_le happ (by simp)
    have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
    have hma := not_mcr_of_mem_noMCR hc.2.1 ha
    have hmb := not_mcr_of_mem_noMCR hc.2.1 hb
    have hca : a.phase.val = 1 → a.role = .clock → 0 < a.counter.val := by
      intro hp hr
      have h := hc.2.2.2 a ha hp hr
      omega
    have hcb : b.phase.val = 1 → b.role = .clock → 0 < b.counter.val := by
      intro hp hr
      have h := hc.2.2.2 b hb hp hr
      omega
    have hpair := phaseOneSpread_transition_bound a b
      (hc.2.2.1 a ha) (hc.2.2.1 b hb) hma hmb hca hcb
    rw [phaseOneSpread_sum_step c a b happ, phaseOneSpread_sum_pair c a b happ]
    calc
      _ ≤ phaseOneSpreadRawMass (c - {a, b}) +
          (2 * phaseOneSpreadWeight a + 2 * phaseOneSpreadWeight b) :=
        add_le_add le_rfl (add_le_add hpair.2.2.1 hpair.2.2.2)
      _ = _ := by ring
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable
      (P := NonuniformMajority L K) happ]
    exact le_add_right le_rfl

theorem phaseOneSpread_raw_drift (n : ℕ) (hn : 2 ≤ n)
    (c : Cfg L K) (hc : phaseOneSpreadWindow n c) :
    (∫⁻ c', phaseOneSpreadRawMass c'
      ∂(NonuniformMajority L K).transitionKernel c) ≤
      (1 + 2 / (n : ℝ≥0∞)) * phaseOneSpreadRawMass c := by
  classical
  have hcard := hc.1
  have hcTwo : 2 ≤ c.card := by omega
  rw [Phase0Window.lintegral_transitionKernel_eq_sum
    (NonuniformMajority L K) c hcTwo]
  refine (Finset.sum_le_sum (fun pair _ =>
    mul_le_mul_right' (phaseOneSpread_step_le n c hc pair.1 pair.2) _)).trans ?_
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hsumprob :
      (∑ pair : AgentState L K × AgentState L K,
        c.interactionProb pair.1 pair.2) = 1 := by
    have h := (c.interactionPMF hcTwo).tsum_coe
    rw [tsum_eq_sum (s := Finset.univ)
      (by intro x hx; exact absurd (Finset.mem_univ x) hx)] at h
    convert h using 1
  rw [← Finset.mul_sum, hsumprob, mul_one,
    Phase0Window.sum_fst_interactionProb c hcTwo phaseOneSpreadWeight,
    Phase0Window.sum_snd_interactionProb c hcTwo phaseOneSpreadWeight, hcard]
  change phaseOneSpreadRawMass c +
      (phaseOneSpreadRawMass c / (n : ℝ≥0∞) +
        phaseOneSpreadRawMass c / (n : ℝ≥0∞)) ≤ _
  simp only [one_mul, ENNReal.div_eq_inv_mul]
  ring_nf <;> exact le_rfl

theorem phaseOneSpread_step_structure (n : ℕ) (c : Cfg L K)
    (hc : phaseOneSpreadWindow n c) (a b : AgentState L K) :
    roleMCRCount
        (Protocol.stepOrSelf (NonuniformMajority L K) c a b) = 0 ∧
      ∀ x ∈ Protocol.stepOrSelf (NonuniformMajority L K) c a b,
        x.phase.val ≤ 1 := by
  classical
  by_cases happ : Protocol.Applicable c a b
  · have ha : a ∈ c := Multiset.mem_of_le happ (by simp)
    have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
    have hma := not_mcr_of_mem_noMCR hc.2.1 ha
    have hmb := not_mcr_of_mem_noMCR hc.2.1 hb
    have hca : a.phase.val = 1 → a.role = .clock → 0 < a.counter.val := by
      intro hp hr
      have h := hc.2.2.2 a ha hp hr
      omega
    have hcb : b.phase.val = 1 → b.role = .clock → 0 < b.counter.val := by
      intro hp hr
      have h := hc.2.2.2 b hb hp hr
      omega
    have hpair := phaseOneSpread_transition_bound a b
      (hc.2.2.1 a ha) (hc.2.2.1 b hb) hma hmb hca hcb
    constructor
    · simpa only [Protocol.stepOrSelf, if_pos happ, NonuniformMajority] using
        roleMCRCount_config_zero_of_noMCR c a b happ hc.2.1
    · intro x hx
      simp only [Protocol.stepOrSelf, if_pos happ, NonuniformMajority,
        Multiset.mem_add, Multiset.insert_eq_cons, Multiset.mem_cons,
        Multiset.mem_singleton] at hx
      rcases hx with hleft | rfl | rfl
      · exact hc.2.2.1 x
          (Multiset.mem_of_le (Multiset.sub_le_self _ _) hleft)
      · exact hpair.1
      · exact hpair.2.1
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable
      (P := NonuniformMajority L K) happ]
    exact ⟨hc.2.1, hc.2.2.1⟩

theorem phaseOneSpread_threshold_of_small_counter
    (c : Cfg L K) (a : AgentState L K) (ha : a ∈ c)
    (hp : a.phase.val = 1) (hr : a.role = .clock)
    (hk : a.counter.val < 30 * (L + 1)) :
    phaseOneSpreadThreshold L ≤ phaseOneSpreadRawMass c := by
  have hdepth : 20 * (L + 1) ≤ 50 * (L + 1) - a.counter.val := by omega
  have hclock : a.phase.val = 1 ∧ a.role = .clock := ⟨hp, hr⟩
  have hweight : phaseOneSpreadThreshold L ≤ phaseOneSpreadWeight a := by
    simp only [phaseOneSpreadWeight, if_pos hclock, phaseOneSpreadThreshold]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hdepth)
      (Real.log_nonneg (by norm_num))
  exact hweight.trans
    (Multiset.single_le_sum (fun x _ => zero_le') _
      (Multiset.mem_map_of_mem _ ha))

theorem phaseOneSpread_stopped_step_le (n : ℕ) (c : Cfg L K)
    (hc : phaseOneSpreadWindow n c) (a b : AgentState L K) :
    phaseOneSpreadStoppedMass n
        (Protocol.stepOrSelf (NonuniformMajority L K) c a b) ≤
      phaseOneSpreadRawMass
        (Protocol.stepOrSelf (NonuniformMajority L K) c a b) := by
  classical
  let c' := Protocol.stepOrSelf (NonuniformMajority L K) c a b
  have hcard : c'.card = n :=
    (Protocol.stepOrSelf_card_eq (P := NonuniformMajority L K) c a b).trans hc.1
  have hstruct := phaseOneSpread_step_structure n c hc a b
  change phaseOneSpreadStoppedMass n c' ≤ phaseOneSpreadRawMass c'
  unfold phaseOneSpreadStoppedMass
  split_ifs with hgood
  · exact le_rfl
  · have hbad : ¬ ∀ a ∈ c', a.phase.val = 1 → a.role = .clock →
        30 * (L + 1) ≤ a.counter.val :=
      fun hh => hgood ⟨hcard, hstruct.1, hstruct.2, hh⟩
    push_neg at hbad
    obtain ⟨x, hx, hp, hr, hk⟩ := hbad
    exact phaseOneSpread_threshold_of_small_counter c' x hx hp hr hk

theorem phaseOneSpread_stopped_drift (n : ℕ) (hn : 2 ≤ n)
    (c : Cfg L K) (hc : phaseOneSpreadWindow n c) :
    (∫⁻ c', phaseOneSpreadStoppedMass n c'
      ∂(NonuniformMajority L K).transitionKernel c) ≤
      (1 + 2 / (n : ℝ≥0∞)) * phaseOneSpreadStoppedMass n c := by
  classical
  have hcTwo : 2 ≤ c.card := by simpa only [hc.1] using hn
  calc
    _ ≤ ∫⁻ c', phaseOneSpreadRawMass c'
        ∂(NonuniformMajority L K).transitionKernel c := by
      simp only [Phase0Window.lintegral_transitionKernel_eq_sum
        (NonuniformMajority L K) c hcTwo]
      exact Finset.sum_le_sum (fun pair _ =>
        mul_le_mul_right' (phaseOneSpread_stopped_step_le n c hc pair.1 pair.2) _)
    _ ≤ (1 + 2 / (n : ℝ≥0∞)) * phaseOneSpreadRawMass c :=
      phaseOneSpread_raw_drift n hn c hc
    _ = _ := by rw [phaseOneSpreadStoppedMass, if_pos hc]

theorem phaseOneSpread_stopped_threshold (n : ℕ) (c : Cfg L K)
    (hc : ¬ phaseOneSpreadWindow n c) :
    phaseOneSpreadThreshold L ≤ phaseOneSpreadStoppedMass n c := by
  simp only [phaseOneSpreadStoppedMass, if_neg hc, le_refl]

theorem phaseOneSpread_mass_eq_card (c : Cfg L K)
    (hw : ∀ a ∈ c, phaseOneSpreadWeight a = 1) :
    phaseOneSpreadRawMass c = c.card := by
  revert hw
  induction c using Multiset.induction with
  | empty => intro hw; simp [phaseOneSpreadRawMass, Config.sumOf]
  | cons a c ih =>
    intro hw
    have ha := hw a (by simp)
    have hc := ih (fun x hx => hw x (by simp [hx]))
    simp only [phaseOneSpreadRawMass, Config.sumOf,
      Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
      Nat.cast_add, Nat.cast_one] at hc ⊢
    rw [ha, hc, add_comm]

theorem phaseOneSpread_mass_eq_card_of_full
    (c : Cfg L K)
    (hfull : ∀ a ∈ c, a.phase.val = 1 → a.role = .clock →
      a.counter.val = 50 * (L + 1)) :
    phaseOneSpreadRawMass c = c.card := by
  apply phaseOneSpread_mass_eq_card
  intro a ha
  unfold phaseOneSpreadWeight
  split_ifs with h
  · simp [hfull a ha h.1 h.2]
  · rfl

theorem phaseOneSpread_exit_from (n : ℕ) (hn : 2 ≤ n)
    (init : Cfg L K) (s T : ℕ)
    (A : Set ((k : Finset.Iic s) → Draw L K))
    (hA : ∀ p ∈ A,
      phaseOneSpreadWindow n (prefixCfg init s p) ∧
        ∀ a ∈ prefixCfg init s p, a.phase.val = 1 → a.role = .clock →
          a.counter.val = 50 * (L + 1)) :
    phaseOneSpreadThreshold L *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
          ∃ u, s ≤ u ∧ u ≤ s + T ∧
            ¬ phaseOneSpreadWindow n (trace init ω u)} ≤
      (1 + 2 / (n : ℝ≥0∞)) ^ T * n *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  apply TraceDrain.growth_exit_tail_from init
    (phaseOneSpreadStoppedMass n) (phaseOneSpreadWindow n)
    (1 + 2 / (n : ℝ≥0∞)) (le_add_right le_rfl)
    (fun c hc => phaseOneSpread_stopped_drift n hn c hc)
    (phaseOneSpreadThreshold L) (phaseOneSpread_stopped_threshold n)
    s T A n
  intro p hp
  rw [phaseOneSpreadStoppedMass, if_pos (hA p hp).1,
    phaseOneSpread_mass_eq_card_of_full _ (hA p hp).2,
    (hA p hp).1.1]

theorem phaseOneSpread_tail_real (n T : ℕ)
    (hn : 2 ≤ n) (hlog : 1 ≤ Real.log (n : ℝ))
    (hT : (T : ℝ) ≤ 7 * (n : ℝ) * Real.log (n : ℝ) + 1) :
    (1 + 2 / (n : ℝ)) ^ T * (n : ℝ) /
        Real.exp (Real.log 2 *
          ((20 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ)) ≤
      1 / (n : ℝ) ^ 4 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnTwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmgf :
      (1 + 2 / (n : ℝ)) ^ T ≤ Real.exp (2 * (T : ℝ) / (n : ℝ)) := by
    calc
      _ ≤ (Real.exp (2 / (n : ℝ))) ^ T :=
        pow_le_pow_left₀ (by positivity)
          (by simpa only [add_comm] using Real.add_one_le_exp (2 / (n : ℝ))) T
      _ = _ := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hmean : 2 * (T : ℝ) / (n : ℝ) ≤ 14 * Real.log (n : ℝ) + 1 := by
    apply (div_le_iff₀ hnpos).2
    nlinarith only [hT, hnTwo]
  have hcounter : 20 * Real.log (n : ℝ) ≤
      Real.log 2 * ((20 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ) := by
    have hhour := PhaseOneDrain.clock_hour_log_lower n
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith only [hhour]
  have hfour : Real.exp (4 * Real.log (n : ℝ)) = (n : ℝ) ^ 4 := by
    have hlogpow : Real.log ((n : ℝ) ^ 4) = 4 * Real.log (n : ℝ) := by
      simp only [Real.log_pow, Nat.cast_ofNat]
    rw [← hlogpow, Real.exp_log (by positivity)]
  calc
    _ ≤ Real.exp (2 * (T : ℝ) / (n : ℝ)) * (n : ℝ) /
        Real.exp (Real.log 2 *
          ((20 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hmgf hnpos.le) (Real.exp_nonneg _)
    _ = Real.exp (2 * (T : ℝ) / (n : ℝ) + Real.log (n : ℝ) -
        Real.log 2 *
          ((20 * PhaseThreeModel.Numeric.clockHours n : ℕ) : ℝ)) := by
      rw [Real.exp_sub, Real.exp_add, Real.exp_log hnpos]
    _ ≤ Real.exp (-(4 * Real.log (n : ℝ))) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hmean, hcounter, hlog]
    _ = 1 / (n : ℝ) ^ 4 := by rw [Real.exp_neg, hfour, one_div]

theorem phaseOneSpread_tail_calibration (n : ℕ)
    (hn : 2 ≤ n) (hlog : 1 ≤ Real.log (n : ℝ)) :
    (1 + 2 / (n : ℝ≥0∞)) ^ logWindow n 7 * n /
        phaseOneSpreadThreshold (PhaseThreeModel.Numeric.hourIndex n) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 4) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbase : (0 : ℝ) ≤ 1 + 2 / (n : ℝ) := by positivity
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  have hrate : ENNReal.ofReal (1 + 2 / (n : ℝ)) =
      1 + 2 / (n : ℝ≥0∞) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity),
      ENNReal.ofReal_one, ENNReal.ofReal_div_of_pos hnpos,
      htwo, ENNReal.ofReal_natCast]
  have hlognonneg : 0 ≤ Real.log (n : ℝ) := by linarith only [hlog]
  have hceil : (logWindow n 7 : ℝ) ≤
      7 * (n : ℝ) * Real.log (n : ℝ) + 1 := by
    unfold logWindow
    norm_num only [Nat.cast_ofNat]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have h := ENNReal.ofReal_le_ofReal
    (phaseOneSpread_tail_real n (logWindow n 7) hn hlog hceil)
  simpa only [ENNReal.ofReal_div_of_pos (Real.exp_pos _),
    ENNReal.ofReal_mul (pow_nonneg hbase (logWindow n 7)),
    ENNReal.ofReal_pow hbase, ENNReal.ofReal_natCast, hrate,
    phaseOneSpreadThreshold, PhaseThreeModel.Numeric.clockHours] using h

theorem phaseOneSpread_exit_tail_from {n : ℕ}
    (hn : 2 ≤ n) (hlog : 1 ≤ Real.log (n : ℝ))
    (init : InputCfg n) (s : ℕ)
    (A : Set ((k : Finset.Iic s) →
      Draw (PhaseThreeModel.Numeric.hourIndex n) 256))
    (hA : ∀ p ∈ A,
      phaseOneSpreadWindow n (prefixCfg init s p) ∧
        ∀ a ∈ prefixCfg init s p, a.phase.val = 1 → a.role = .clock →
          a.counter.val = 50 * (PhaseThreeModel.Numeric.hourIndex n + 1)) :
    law init {ω | frestrictLe
        (π := fun _ : ℕ => Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A ∧
      ∃ u, s ≤ u ∧ u ≤ s + logWindow n 7 ∧
        ¬ phaseOneSpreadWindow n (trace init ω u)} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 4) *
        law init {ω | frestrictLe
          (π := fun _ : ℕ => Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A} := by
  let thr := phaseOneSpreadThreshold (PhaseThreeModel.Numeric.hourIndex n)
  have h := phaseOneSpread_exit_from n hn init s (logWindow n 7) A hA
  have hzero : thr ≠ 0 :=
    ClockCounterDepthCover.counterDepthThreshold_ne_zero
      (20 * (PhaseThreeModel.Numeric.hourIndex n + 1)) (Real.log 2)
  have htop : thr ≠ ∞ :=
    ClockCounterDepthCover.counterDepthThreshold_ne_top
      (20 * (PhaseThreeModel.Numeric.hourIndex n + 1)) (Real.log 2)
  calc
    _ = thr⁻¹ * (thr *
        law init {ω | frestrictLe
          (π := fun _ : ℕ => Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A ∧
          ∃ u, s ≤ u ∧ u ≤ s + logWindow n 7 ∧
            ¬ phaseOneSpreadWindow n (trace init ω u)}) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hzero htop, one_mul]
    _ ≤ thr⁻¹ *
        ((1 + 2 / (n : ℝ≥0∞)) ^ logWindow n 7 * n *
          law init {ω | frestrictLe
            (π := fun _ : ℕ => Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A}) :=
      mul_le_mul_left' h _
    _ = ((1 + 2 / (n : ℝ≥0∞)) ^ logWindow n 7 * n / thr) *
        law init {ω | frestrictLe
          (π := fun _ : ℕ => Draw (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A} := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ _ := mul_le_mul_right' (phaseOneSpread_tail_calibration n hn hlog) _

/-! ## Translating the first raw exit into the genuine first seed -/

theorem phase_zero_transition_phase_le_one_of_no_mcr
    (a b : AgentState L K) (ha : a.phase.val = 0) (hb : b.phase.val = 0)
    (hma : a.role ≠ .mcr) (hmb : b.role ≠ .mcr) :
    (Transition L K a b).1.phase.val ≤ 1 ∧
      (Transition L K a b).2.phase.val ≤ 1 := by
  have hd := phaseOneSpread_dispatch_zero a b ha hb
  have hp := phaseOneSpreadWeight_phase_zero_pair a b ha hb hma hmb
  exact ⟨hd.1.trans_le hp.1, hd.2.1.trans_le hp.2.1⟩

theorem phase_zero_stepOrSelf_phase_le_one
    (c : Cfg L K) (hall : Phase0Window.allPhase0 c)
    (hmcr : roleMCRCount c = 0) (r₁ r₂ : AgentState L K) :
    ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂,
      a.phase.val ≤ 1 := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hs : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
    have hpair := phase_zero_transition_phase_le_one_of_no_mcr r₁ r₂
      (show r₁.phase.val = 0 from congrArg Fin.val (hall r₁ hs))
      (show r₂.phase.val = 0 from congrArg Fin.val (hall r₂ ht))
      (not_mcr_of_mem_noMCR hmcr hs) (not_mcr_of_mem_noMCR hmcr ht)
    have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ =
        c - {r₁, r₂} +
          {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ] <;> rfl
    intro a ha
    rw [hstep] at ha
    rcases Multiset.mem_add.mp ha with hres | hnew
    · have hz := hall a
        (Multiset.mem_of_le (Multiset.sub_le_self _ _) hres)
      simp [hz]
    · have hnew' : a = (Transition L K r₁ r₂).1 ∨
          a = (Transition L K r₁ r₂).2 := by simpa using hnew
      rcases hnew' with rfl | rfl
      · exact hpair.1
      · exact hpair.2
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    intro a ha
    simp [hall a ha]

theorem phase_zero_applyDraw_phase_le_one
    (c : Cfg L K) (hall : Phase0Window.allPhase0 c)
    (hmcr : roleMCRCount c = 0) (d : Draw L K) :
    ∀ a ∈ applyDraw c d, a.phase.val ≤ 1 := by
  cases d with
  | none =>
      intro a ha
      simp [hall a ha]
  | some p =>
      exact phase_zero_stepOrSelf_phase_le_one c hall hmcr p.1.1 p.2.1

theorem first_seed_of_phase_zero_exit
    (init : Cfg L K) (ω : Ω L K) (t : ℕ)
    (hpast : ∀ u < t, Phase0Window.allPhase0 (trace init ω u))
    (hcap : ∀ a ∈ trace init ω t, a.phase.val ≤ 1)
    (hexit : ¬ Phase0Window.allPhase0 (trace init ω t)) :
    firstPhaseSeed init 1 t ω := by
  classical
  change ¬ ∀ a ∈ trace init ω t, a.phase = 0 at hexit
  push_neg at hexit
  obtain ⟨a, ha, hne⟩ := hexit
  have hval : a.phase.val ≠ 0 := fun hz => hne (Fin.ext hz)
  have hle := hcap a ha
  refine ⟨⟨a, ha, by omega⟩, ?_⟩
  intro u hu b hb
  simp [hpast u hu b hb]

theorem all_phase_zero_of_no_first_seed
    (init : Cfg L K) (ω : Ω L K) (s T : ℕ)
    (hpast : ∀ t ≤ s, Phase0Window.allPhase0 (trace init ω t))
    (hmcr : roleMCRCount (trace init ω s) = 0)
    (hno : ¬ ∃ S ≤ T, firstPhaseSeed init 1 S ω) :
    ∀ t ≤ T, Phase0Window.allPhase0 (trace init ω t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro ht
      by_cases hts : t ≤ s
      · exact hpast t hts
      · cases t with
        | zero => omega
        | succ u =>
            have hsu : s ≤ u := by omega
            have hbefore : ∀ v < u + 1,
                Phase0Window.allPhase0 (trace init ω v) := by
              intro v hv
              exact ih v hv (by omega)
            have hmidmcr : roleMCRCount (trace init ω u) = 0 :=
              roleMCRCount_zero_of_reachable
                (TimeTheorem.trace_reachable init ω hsu) hmcr
            have hcap : ∀ a ∈ trace init ω (u + 1), a.phase.val ≤ 1 := by
              rw [TimeTheorem.trace_succ]
              exact phase_zero_applyDraw_phase_le_one (trace init ω u)
                (hbefore u (Nat.lt_succ_self u)) hmidmcr (ω (u + 1))
            by_contra hexit
            exact hno ⟨u + 1, ht,
              first_seed_of_phase_zero_exit init ω (u + 1) hbefore hcap hexit⟩

/-! ## The mixed-counter gate holds at the genuine first seed -/

theorem phase_zero_stepOrSelf_spread_weight
    (c : Cfg L K) (hall : Phase0Window.allPhase0 c)
    (hmcr : roleMCRCount c = 0) (r₁ r₂ : AgentState L K) :
    ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂,
      phaseOneSpreadWeight a = 1 := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hs : r₁ ∈ c := Multiset.mem_of_le happ (by simp)
    have ht : r₂ ∈ c := Multiset.mem_of_le happ (by simp)
    have hsphase : r₁.phase.val = 0 := congrArg Fin.val (hall r₁ hs)
    have htphase : r₂.phase.val = 0 := congrArg Fin.val (hall r₂ ht)
    obtain ⟨_, _, hwleft, hwright⟩ :=
      phaseOneSpreadWeight_phase_zero_pair r₁ r₂ hsphase htphase
        (not_mcr_of_mem_noMCR hmcr hs) (not_mcr_of_mem_noMCR hmcr ht)
    obtain ⟨_, _, hdleft, hdright⟩ :=
      phaseOneSpread_dispatch_zero r₁ r₂ hsphase htphase
    have hleft : phaseOneSpreadWeight (Transition L K r₁ r₂).1 = 1 :=
      hdleft.trans hwleft
    have hright : phaseOneSpreadWeight (Transition L K r₁ r₂).2 = 1 :=
      hdright.trans hwright
    have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂ =
        c - {r₁, r₂} +
          {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ] <;> rfl
    intro a ha
    rw [hstep] at ha
    rcases Multiset.mem_add.mp ha with hres | hnew
    · have hz : a.phase.val = 0 := congrArg Fin.val
        (hall a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hres))
      simp [phaseOneSpreadWeight, hz]
    · have hnew' : a = (Transition L K r₁ r₂).1 ∨
          a = (Transition L K r₁ r₂).2 := by simpa using hnew
      rcases hnew' with rfl | rfl
      · exact hleft
      · exact hright
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    intro a ha
    have hz : a.phase.val = 0 := congrArg Fin.val (hall a ha)
    simp [phaseOneSpreadWeight, hz]

theorem phase_zero_applyDraw_spread_weight
    (c : Cfg L K) (hall : Phase0Window.allPhase0 c)
    (hmcr : roleMCRCount c = 0) (d : Draw L K) :
    ∀ a ∈ applyDraw c d, phaseOneSpreadWeight a = 1 := by
  cases d with
  | none =>
      intro a ha
      have hz : a.phase.val = 0 := congrArg Fin.val (hall a ha)
      simp [phaseOneSpreadWeight, hz]
  | some p =>
      exact phase_zero_stepOrSelf_spread_weight c hall hmcr p.1.1 p.2.1

theorem phaseOneSpreadWeight_counter_full
    (a : AgentState L K) (hp : a.phase.val = 1) (hr : a.role = .clock)
    (hw : phaseOneSpreadWeight a = 1) :
    a.counter.val = 50 * (L + 1) := by
  have hclock : a.phase.val = 1 ∧ a.role = .clock := ⟨hp, hr⟩
  have he : Real.exp (Real.log 2 *
      (((50 * (L + 1) - a.counter.val : ℕ)) : ℝ)) = 1 := by
    apply ENNReal.ofReal_eq_one.mp
    simpa only [phaseOneSpreadWeight, if_pos hclock] using hw
  have hz : Real.log 2 *
      (((50 * (L + 1) - a.counter.val : ℕ)) : ℝ) = 0 :=
    Real.exp_injective (by simpa only [Real.exp_zero] using he)
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hcast : (((50 * (L + 1) - a.counter.val : ℕ)) : ℝ) = 0 :=
    (mul_eq_zero.mp hz).resolve_left hlog
  have hnat : 50 * (L + 1) - a.counter.val = 0 := by exact_mod_cast hcast
  have hupper := a.counter.isLt
  omega

theorem phase_one_spread_seed_initial {n : ℕ}
    (init : Cfg L K) (hcard : init.card = n) (ω : Ω L K) (S : ℕ)
    (hpos : 0 < S) (hseed : firstPhaseSeed init 1 S ω)
    (hmcr : roleMCRCount (trace init ω (S - 1)) = 0) :
    phaseOneSpreadWindow n (trace init ω S) ∧
      (∀ a ∈ trace init ω S, a.phase.val = 1 → a.role = .clock →
        a.counter.val = 50 * (L + 1)) := by
  have hsucc : S - 1 + 1 = S := by omega
  have hstep : trace init ω S =
      applyDraw (trace init ω (S - 1)) (ω S) := by
    simpa only [hsucc] using TimeTheorem.trace_succ init ω (S - 1)
  have hsource : Phase0Window.allPhase0 (trace init ω (S - 1)) :=
    phaseZero_allPhaseZero_before_seed init ω S hseed (S - 1) (by omega)
  have hcap : ∀ a ∈ trace init ω S, a.phase.val ≤ 1 := by
    rw [hstep]
    exact phase_zero_applyDraw_phase_le_one
      (trace init ω (S - 1)) hsource hmcr (ω S)
  have hweights : ∀ a ∈ trace init ω S, phaseOneSpreadWeight a = 1 := by
    rw [hstep]
    exact phase_zero_applyDraw_spread_weight
      (trace init ω (S - 1)) hsource hmcr (ω S)
  have hfull : ∀ a ∈ trace init ω S,
      a.phase.val = 1 → a.role = .clock →
        a.counter.val = 50 * (L + 1) := by
    intro a ha hp hr
    exact phaseOneSpreadWeight_counter_full a hp hr (hweights a ha)
  have hcardS : (trace init ω S).card = n :=
    (Protocol.reachable_card_eq
      (TimeTheorem.trace_reachable init ω (s := 0) (t := S)
        (Nat.zero_le S))).trans hcard
  have hmcrS : roleMCRCount (trace init ω S) = 0 :=
    roleMCRCount_zero_of_reachable
      (TimeTheorem.trace_reachable init ω (s := S - 1) (t := S) (by omega)) hmcr
  refine ⟨⟨hcardS, hmcrS, hcap, ?_⟩, hfull⟩
  intro a ha hp hr
  rw [hfull a ha hp hr]
  omega

theorem phase_one_spread_seed_initial_of_goodInput {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init)
    (ω : InputLog n) (S : ℕ)
    (hpos : 0 < S) (hseed : firstPhaseSeed init 1 S ω)
    (hmcr : roleMCRCount (trace init ω (S - 1)) = 0) :
    phaseOneSpreadWindow n (trace init ω S) ∧
      (∀ a ∈ trace init ω S, a.phase.val = 1 → a.role = .clock →
        a.counter.val = 50 * PhaseThreeModel.Numeric.clockHours n) := by
  simpa only [PhaseThreeModel.Numeric.clockHours] using
    phase_one_spread_seed_initial init hinput.2.2 ω S hpos hseed hmcr

theorem phase_one_spread_seed_mass {n : ℕ}
    (init : Cfg L K) (hcard : init.card = n) (ω : Ω L K) (S : ℕ)
    (hpos : 0 < S) (hseed : firstPhaseSeed init 1 S ω)
    (hmcr : roleMCRCount (trace init ω (S - 1)) = 0) :
    phaseOneSpreadRawMass (trace init ω S) = (n : ℝ≥0∞) := by
  have h := phase_one_spread_seed_initial init hcard ω S hpos hseed hmcr
  rw [phaseOneSpread_mass_eq_card_of_full _ h.2, h.1.1]

/-! ## The residual-counter bound at the genuine first seed -/

theorem phaseZero_first_seed_unique (init : Cfg L K) (p : ℕ)
    (ω : Ω L K) {s t : ℕ}
    (hs : firstPhaseSeed init p s ω) (ht : firstPhaseSeed init p t ω) :
    s = t := by
  rcases lt_trichotomy s t with hst | heq | hts
  · obtain ⟨a, ha, hp⟩ := hs.1
    have hlt := ht.2 s hst a ha
    omega
  · exact heq
  · obtain ⟨a, ha, hp⟩ := ht.1
    have hlt := hs.2 t hts a ha
    omega

/-- A prefix bound at each genuine seed is summed without a factor for the
number of possible seed times. -/
theorem phaseZero_first_seed_splice (init : Cfg L K) (p : ℕ)
    (E : ℕ → Set (Ω L K)) (ε : ℝ≥0∞)
    (hE : ∀ s, MeasurableSet (E s))
    (hlocal : ∀ s,
      law init ({ω | firstPhaseSeed init p s ω} ∩ E s) ≤
        ε * law init {ω | firstPhaseSeed init p s ω}) :
    law init {ω | ∃ s, firstPhaseSeed init p s ω ∧ ω ∈ E s} ≤ ε := by
  classical
  let S (ω : Ω L K) : WithTop ℕ :=
    if h : ∃ s, firstPhaseSeed init p s ω then (Nat.find h : WithTop ℕ) else ⊤
  have hSiff (ω : Ω L K) (s : ℕ) :
      S ω = (s : WithTop ℕ) ↔ firstPhaseSeed init p s ω := by
    dsimp only [S]
    split_ifs with hex
    · constructor
      · intro h
        have hfind : Nat.find hex = s := WithTop.coe_injective h
        simpa only [hfind] using Nat.find_spec hex
      · intro hs
        exact congrArg (fun r : ℕ => (r : WithTop ℕ))
          (phaseZero_first_seed_unique init p ω (Nat.find_spec hex) hs)
    · constructor
      · intro h
        exact absurd h (by simp)
      · intro hs
        exact absurd ⟨s, hs⟩ hex
  have hseedMeas (s : ℕ) :
      MeasurableSet {ω | firstPhaseSeed init p s ω} :=
    (pairLogFiltration L K).le s _
      (firstPhaseSeed_measurableSet init p s)
  let D : Set (Ω L K) :=
    {ω | ∃ s, firstPhaseSeed init p s ω ∧ ω ∈ E s}
  have hD : MeasurableSet D := by
    have heq : D = ⋃ s : ℕ, {ω | firstPhaseSeed init p s ω} ∩ E s := by
      ext ω
      simp only [D, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    rw [heq]
    exact MeasurableSet.iUnion (fun s => (hseedMeas s).inter (hE s))
  have hSeq (s : ℕ) :
      {ω | S ω = (s : WithTop ℕ)} = {ω | firstPhaseSeed init p s ω} :=
    Set.ext fun ω => hSiff ω s
  apply genuine_seed_splice (law init) S D ε hD
  · intro s
    rw [hSeq s]
    exact hseedMeas s
  · intro ω hω
    obtain ⟨s, hs, _⟩ := hω
    rw [(hSiff ω s).mpr hs]
    exact WithTop.coe_ne_top
  · intro s
    have heq :
        D ∩ {ω | S ω = (s : WithTop ℕ)} =
          {ω | firstPhaseSeed init p s ω} ∩ E s := by
      ext ω
      rw [hSeq s]
      constructor
      · rintro ⟨⟨r, hr, hbad⟩, hs⟩
        have hrs := phaseZero_first_seed_unique init p ω hr hs
        subst r
        exact ⟨hs, hbad⟩
      · rintro ⟨hs, hbad⟩
        exact ⟨⟨s, hs, hbad⟩, hs⟩
    rw [heq, hSeq s]
    exact hlocal s

def phaseZeroSpreadBad {n : ℕ} (init : InputCfg n) : Set (InputLog n) :=
  {ω | ∃ S, firstPhaseSeed init 1 S ω ∧ 0 < S ∧
    roleMCRCount (trace init ω (S - 1)) = 0 ∧
    ∃ u, S ≤ u ∧ u ≤ S + logWindow n 7 ∧
      ¬ phaseOneSpreadWindow n (trace init ω u)}

theorem phase_zero_residual_counter_tail {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (phaseZeroSpreadBad init) ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 4) := by
  classical
  let E : ℕ → Set (InputLog n) := fun S => {ω |
    0 < S ∧ roleMCRCount (trace init ω (S - 1)) = 0 ∧
    ∃ u, S ≤ u ∧ u ≤ S + logWindow n 7 ∧
      ¬ phaseOneSpreadWindow n (trace init ω u)}
  have hmeasCounter (S : ℕ) :
      MeasurableSet {ω : InputLog n |
        roleMCRCount (trace init ω (S - 1)) = 0} :=
    (show MeasurableSet {c : InputCfg n | roleMCRCount c = 0} from
      (Set.to_countable _).measurableSet).preimage
        ((measurable_pi_apply (S - 1)).comp (measurable_trace init))
  have hmeasBad (S : ℕ) :
      MeasurableSet {ω : InputLog n |
        ∃ u, S ≤ u ∧ u ≤ S + logWindow n 7 ∧
          ¬ phaseOneSpreadWindow n (trace init ω u)} := by
    have heq :
        {ω : InputLog n | ∃ u, S ≤ u ∧ u ≤ S + logWindow n 7 ∧
          ¬ phaseOneSpreadWindow n (trace init ω u)} =
        ⋃ u : ℕ, {ω : InputLog n | S ≤ u ∧ u ≤ S + logWindow n 7 ∧
          ¬ phaseOneSpreadWindow n (trace init ω u)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rw [heq]
    refine MeasurableSet.iUnion fun u => ?_
    by_cases hsu : S ≤ u
    · by_cases hu : u ≤ S + logWindow n 7
      · simpa only [hsu, hu, true_and] using
          (show MeasurableSet {c : InputCfg n | ¬ phaseOneSpreadWindow n c} from
            (Set.to_countable _).measurableSet).preimage
              ((measurable_pi_apply u).comp (measurable_trace init))
      · simp only [hu, false_and, and_false, Set.setOf_false, MeasurableSet.empty]
    · simp only [hsu, false_and, Set.setOf_false, MeasurableSet.empty]
  have hE (S : ℕ) : MeasurableSet (E S) := by
    by_cases hs : 0 < S
    · change MeasurableSet {ω : InputLog n |
        0 < S ∧ roleMCRCount (trace init ω (S - 1)) = 0 ∧
          ∃ u, S ≤ u ∧ u ≤ S + logWindow n 7 ∧
            ¬ phaseOneSpreadWindow n (trace init ω u)}
      simp only [hs, true_and]
      exact (hmeasCounter S).inter (hmeasBad S)
    · simp only [E, hs, false_and, Set.setOf_false, MeasurableSet.empty]
  have hn : 2 ≤ n :=
    (by norm_num : (2 : ℕ) ≤ 40).trans (time_population_bounds hinput.1).2
  have hlog : 1 ≤ Real.log (n : ℝ) := by
    have h := (PhaseOneDrain.population_calibration hinput.1).2
    linarith only [h]
  apply phaseZero_first_seed_splice init 1 E
    (ENNReal.ofReal (1 / (n : ℝ) ^ 4)) hE
  intro S
  have hseedPast := firstPhaseSeed_measurableSet init 1 S
  rw [pairLogFiltration_eq_comap] at hseedPast
  obtain ⟨Aseed, _, hAseed⟩ := hseedPast
  let A : Set ((k : Finset.Iic S) →
      Draw (PhaseThreeModel.Numeric.hourIndex n) 256) :=
    {p | p ∈ Aseed ∧ phaseOneSpreadWindow n (prefixCfg init S p) ∧
      ∀ a ∈ prefixCfg init S p, a.phase.val = 1 → a.role = .clock →
        a.counter.val = 50 * (PhaseThreeModel.Numeric.hourIndex n + 1)}
  have hmem (ω : InputLog n) :
      frestrictLe (π := fun _ : ℕ =>
        Draw (PhaseThreeModel.Numeric.hourIndex n) 256) S ω ∈ Aseed ↔
        firstPhaseSeed init 1 S ω := by
    change ω ∈ frestrictLe (π := fun _ : ℕ =>
      Draw (PhaseThreeModel.Numeric.hourIndex n) 256) S ⁻¹' Aseed ↔
        ω ∈ {ω | firstPhaseSeed init 1 S ω}
    rw [hAseed]
  have htail := phaseOneSpread_exit_tail_from hn hlog init S A
    (fun _ hp => hp.2)
  calc
    law init ({ω | firstPhaseSeed init 1 S ω} ∩ E S) ≤
        law init {ω | frestrictLe
          (π := fun _ : ℕ => Draw (PhaseThreeModel.Numeric.hourIndex n) 256)
            S ω ∈ A ∧
          ∃ u, S ≤ u ∧ u ≤ S + logWindow n 7 ∧
            ¬ phaseOneSpreadWindow n (trace init ω u)} := by
      apply measure_mono
      rintro ω ⟨hseed, hpos, hmcr, hbad⟩
      have hinit := phase_one_spread_seed_initial
        init hinput.2.2 ω S hpos hseed hmcr
      exact ⟨⟨(hmem ω).mpr hseed, hinit.1, hinit.2⟩, hbad⟩
    _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 4) *
        law init {ω | frestrictLe
          (π := fun _ : ℕ => Draw (PhaseThreeModel.Numeric.hourIndex n) 256)
            S ω ∈ A} := htail
    _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 4) *
        law init {ω | firstPhaseSeed init 1 S ω} :=
      mul_le_mul_left' (measure_mono fun ω hω => (hmem ω).mp hω.1) _

/-! ## Final composition on the original pair-log law -/

theorem phase_zero_late_seed_estimate {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    law init {ω |
      PhaseZeroRoleReadyAt init ω (phaseZeroRoleHorizon n) ∧
      ¬ ∃ S ≤ phaseZeroRoleHorizon n +
          300 * n * PhaseThreeModel.Numeric.clockHours n,
        firstPhaseSeed init 1 S ω} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 20) := by
  let s := phaseZeroRoleHorizon n
  let A : Set ((k : Finset.Iic s) →
      Draw (PhaseThreeModel.Numeric.hourIndex n) 256) :=
    {p | PhaseZeroRoleReady n (prefixCfg init s p)}
  have hA : ∀ p ∈ A, PhaseZeroClockWindow n (prefixCfg init s p) := by
    intro p hp
    obtain ⟨hc, hpz, hmcr, _, _, hclock, _⟩ := hp
    have hclockReal : (97 : ℝ) * (n : ℝ) ≤
        400 * (clockCount (prefixCfg init s p) : ℝ) := by
      linarith only [hclock]
    refine ⟨hc, hpz, hmcr, ?_⟩
    exact_mod_cast hclockReal
  have htail := phaseZero_late_exit_tail_from init hinput.1 s A hA
  have hprob : law init {ω | frestrictLe
      (π := fun _ : ℕ => Draw (PhaseThreeModel.Numeric.hourIndex n) 256)
        s ω ∈ A} ≤ 1 := by
    calc
      _ ≤ law init Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  refine (measure_mono ?_).trans (htail.trans ?_)
  · rintro ω ⟨hready, hno⟩
    have hall := all_phase_zero_of_no_first_seed init ω s
      (s + 300 * n * PhaseThreeModel.Numeric.clockHours n)
      hready.1 hready.2.2.2.1 hno
    exact ⟨hready.2, fun u _ hu => hall u hu.le⟩
  · simpa only [mul_one] using
      mul_le_mul_left' hprob (ENNReal.ofReal (1 / (n : ℝ) ^ 20))

/-- The Phase-0 entry estimate, with the calibrated horizon and error budget.
The role stages use fixed offsets; only the genuine first seed is spliced. -/
theorem phase_zero_entry_estimate {n : ℕ}
    (init : InputCfg n) (hinput : ThresholdEpidemic.GoodInput n init) :
    law init {ω | ¬ ∃ s ≤ 350 * n * PhaseThreeModel.Numeric.clockHours n,
      IsFirstAllPhaseOne init ω s ∧ PhaseOneEntryProfile init ω s} ≤
      ENNReal.ofReal (8 / (n : ℝ) ^ 3) := by
  classical
  let R := phaseZeroRoleHorizon n
  let Q := R + 300 * n * PhaseThreeModel.Numeric.clockHours n
  let Erole : Set (InputLog n) := {ω | ¬ PhaseZeroRoleReadyAt init ω R}
  let Elate : Set (InputLog n) := {ω |
    PhaseZeroRoleReadyAt init ω R ∧
      ¬ ∃ S ≤ Q, firstPhaseSeed init 1 S ω}
  let Espread : Set (InputLog n) := {ω |
    ∃ S, firstPhaseSeed init 1 S ω ∧
      ¬ ∃ s ≤ S + logWindow n 7, IsFirstAllPhaseOne init ω s}
  let Ecounter := phaseZeroSpreadBad init
  have hrole : law init Erole ≤ ENNReal.ofReal (7 / (n : ℝ) ^ 3) :=
    phase_zero_role_ready_estimate init hinput
  have hlate : law init Elate ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 20) :=
    phase_zero_late_seed_estimate init hinput
  have hspread : law init Espread ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 4) :=
    phase_one_spread_first_entry_tail init hinput
  have hcounter : law init Ecounter ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 4) :=
    phase_zero_residual_counter_tail init hinput
  have hn : 0 < n := by
    have h := (time_population_bounds hinput.1).2
    omega
  have hcard (ω : InputLog n) (t : ℕ) : (trace init ω t).card = n :=
    (Protocol.reachable_card_eq
      (phase_zero_trace_reachable init ω t)).trans hinput.2.2
  have hsub :
      {ω | ¬ ∃ s ≤ 350 * n * PhaseThreeModel.Numeric.clockHours n,
        IsFirstAllPhaseOne init ω s ∧ PhaseOneEntryProfile init ω s} ⊆
      (Erole ∪ Elate) ∪ (Espread ∪ Ecounter) := by
    intro ω hbad
    by_cases hready : PhaseZeroRoleReadyAt init ω R
    · by_cases hseedExists : ∃ S ≤ Q, firstPhaseSeed init 1 S ω
      · obtain ⟨S, hSQ, hseed⟩ := hseedExists
        have hRS : R < S := by
          by_contra h
          have hz := hready.1 S (Nat.le_of_not_gt h)
          obtain ⟨a, ha, hp⟩ := hseed.1
          have hzero : a.phase.val = 0 := congrArg Fin.val (hz a ha)
          omega
        have hSpos : 0 < S := by omega
        have hmcrPre : roleMCRCount (trace init ω (S - 1)) = 0 :=
          roleMCRCount_zero_of_reachable
            (TimeTheorem.trace_reachable init ω
              (s := R) (t := S - 1) (by omega)) hready.2.2.2.1
        by_cases hentryExists :
            ∃ s ≤ S + logWindow n 7, IsFirstAllPhaseOne init ω s
        · obtain ⟨s, hsWindow, hfirst⟩ := hentryExists
          have hSs : S ≤ s := by
            by_contra h
            have hsS : s < S := Nat.lt_of_not_ge h
            have hcardpos : 0 < (trace init ω s).card := by
              rw [hcard ω s]
              exact hn
            obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp hcardpos
            have hlo : 1 ≤ a.phase.val := hfirst.1 a ha
            have hhi : a.phase.val < 1 := hseed.2 s hsS a ha
            omega
          by_cases hwin : phaseOneSpreadWindow n (trace init ω s)
          · have hone : ∀ a ∈ trace init ω s, a.phase.val = 1 := by
              intro a ha
              exact Nat.le_antisymm (hwin.2.2.1 a ha) (hfirst.1 a ha)
            have hclocks : ∀ a ∈ trace init ω s, a.role = .clock →
                30 * PhaseThreeModel.Numeric.clockHours n ≤ a.counter.val := by
              intro a ha hc
              simpa only [PhaseThreeModel.Numeric.clockHours] using
                hwin.2.2.2 a ha (hone a ha) hc
            obtain ⟨_, _, hmcr, hmlo, hmhi, hclo, hrlo⟩ := hready.2
            have hprofile := phase_one_entry_profile_from_role_counts init hinput ω
              R s (hRS.le.trans hSs) hmcr hmlo hmhi hclo hrlo hone hclocks
            have hdeadline : s ≤
                350 * n * PhaseThreeModel.Numeric.clockHours n := by
              calc
                s ≤ Q + logWindow n 7 :=
                  hsWindow.trans (Nat.add_le_add_right hSQ _)
                _ ≤ 350 * n * PhaseThreeModel.Numeric.clockHours n :=
                  phaseZero_entry_horizon_extended_le hinput.1
            exact (hbad ⟨s, hdeadline, hfirst, hprofile⟩).elim
          · exact Or.inr (Or.inr
              ⟨S, hseed, hSpos, hmcrPre, s, hSs, hsWindow, hwin⟩)
        · exact Or.inr (Or.inl ⟨S, hseed, hentryExists⟩)
      · exact Or.inl (Or.inr ⟨hready, hseedExists⟩)
    · exact Or.inl (Or.inl hready)
  have h40 : (40 : ℝ) ≤ n := by
    exact_mod_cast (time_population_bounds hinput.1).2
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    law init {ω | ¬ ∃ s ≤ 350 * n * PhaseThreeModel.Numeric.clockHours n,
        IsFirstAllPhaseOne init ω s ∧ PhaseOneEntryProfile init ω s}
        ≤ law init ((Erole ∪ Elate) ∪ (Espread ∪ Ecounter)) :=
      measure_mono hsub
    _ ≤ law init (Erole ∪ Elate) + law init (Espread ∪ Ecounter) :=
      measure_union_le _ _
    _ ≤ (law init Erole + law init Elate) +
        (law init Espread + law init Ecounter) :=
      add_le_add (measure_union_le _ _) (measure_union_le _ _)
    _ ≤ (ENNReal.ofReal (7 / (n : ℝ) ^ 3) +
          ENNReal.ofReal (1 / (n : ℝ) ^ 20)) +
        (ENNReal.ofReal (1 / (n : ℝ) ^ 4) +
          ENNReal.ofReal (1 / (n : ℝ) ^ 4)) :=
      add_le_add (add_le_add hrole hlate) (add_le_add hspread hcounter)
    _ = ENNReal.ofReal (7 / (n : ℝ) ^ 3) +
          ENNReal.ofReal (1 / (n : ℝ) ^ 20) +
          ENNReal.ofReal (2 / (n : ℝ) ^ 4) := by
      congr 1
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (8 / (n : ℝ) ^ 3) := phase_zero_error_budget_ennreal h40

/-! ## Why the bridge retains the population-cardinality hypothesis -/

/-- These witnesses are intentionally not valid Phase-0 inputs. -/
def profileReserveWitness (o : Opinion) :
    AgentState (PhaseThreeModel.Numeric.hourIndex 0) 256 where
  input := o
  output := .T
  phase := ⟨1, by decide⟩
  role := .reserve
  assigned := false
  bias := .zero
  smallBias := ⟨3, by decide⟩
  hour := ⟨0, by omega⟩
  minute := ⟨0, by omega⟩
  full := false
  opinions := 0
  counter := ⟨0, by omega⟩

def profileCardinalityInit : InputCfg 0 :=
  {profileReserveWitness .A, profileReserveWitness .B}

def profileCardinalityLog : InputLog 0 := fun _ => none

theorem profileCardinalityInit_card : profileCardinalityInit.card = 2 := by
  decide

theorem profileCardinalityInit_gap : initialGap profileCardinalityInit = 0 := by
  decide

theorem profileCardinalityInit_counts :
    mainCount profileCardinalityInit = 0 ∧
      clockCount profileCardinalityInit = 0 ∧
      reserveCount profileCardinalityInit = 2 := by
  decide

theorem profileCardinalityInit_mass :
    mainSmallBiasSum profileCardinalityInit = 0 := by
  decide

theorem profileCardinalityInit_fields :
    ∀ a ∈ profileCardinalityInit,
      a.phase.val = 1 ∧ a.role = .reserve ∧ a.smallBias.val = 3 := by
  intro a ha
  have hmem : a = profileReserveWitness .A ∨
      a = profileReserveWitness .B := by
    simpa only [profileCardinalityInit, Multiset.insert_eq_cons,
      Multiset.mem_cons, Multiset.mem_singleton] using ha
  rcases hmem with rfl | rfl <;> decide

theorem profileCardinalityInit_profile :
    PhaseOneEntryProfile profileCardinalityInit profileCardinalityLog 0 := by
  obtain ⟨hm, hc, hr⟩ := profileCardinalityInit_counts
  have hfields : ∀ a ∈ trace profileCardinalityInit profileCardinalityLog 0,
      a.phase.val = 1 ∧ a.role = .reserve ∧ a.smallBias.val = 3 := by
    simpa only [TimeTheorem.trace_zero] using profileCardinalityInit_fields
  refine
    { all_one := fun a ha => (hfields a ha).1
      final_roles := fun a ha => Or.inr (Or.inr (hfields a ha).2.1)
      main_lower := ?_
      main_upper := ?_
      clock_lower := ?_
      reserve_lower := ?_
      clock_counter := ?_
      nonmain_zero := fun a ha _ => (hfields a ha).2.2
      main_mass := ?_ }
  · norm_num [TimeTheorem.trace_zero, hm]
  · norm_num [TimeTheorem.trace_zero, hm]
  · norm_num [TimeTheorem.trace_zero, hc]
  · norm_num [TimeTheorem.trace_zero, hr]
  · intro a ha hclock
    have hreserve := (hfields a ha).2.1
    rw [hreserve] at hclock
    cases hclock
  · rw [TimeTheorem.trace_zero, profileCardinalityInit_mass,
      profileCardinalityInit_gap]

theorem profileCardinalityInit_small_gap :
    40 * (initialGap profileCardinalityInit).natAbs ≤
      mainCount (trace profileCardinalityInit profileCardinalityLog 0) := by
  norm_num [TimeTheorem.trace_zero, profileCardinalityInit_gap,
    profileCardinalityInit_counts.1]

theorem profileCardinalityInit_not_drain :
    ¬ PhaseOneDrain.PhaseOneDrainEntry 0 (initialGap profileCardinalityInit)
      (trace profileCardinalityInit profileCardinalityLog 0) := by
  intro h
  have hcard : profileCardinalityInit.card = 0 := h.1.1
  rw [profileCardinalityInit_card] at hcard
  omega

theorem profile_only_bridge_counterexample :
    ∃ (init : InputCfg 0) (ω : InputLog 0) (s : ℕ),
      PhaseOneEntryProfile init ω s ∧
        40 * (initialGap init).natAbs ≤ mainCount (trace init ω s) ∧
        ¬ PhaseOneDrain.PhaseOneDrainEntry 0 (initialGap init) (trace init ω s) :=
  ⟨profileCardinalityInit, profileCardinalityLog, 0,
    profileCardinalityInit_profile, profileCardinalityInit_small_gap,
    profileCardinalityInit_not_drain⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseZeroEntryProducer

end
