-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockJointFields.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockJointFront
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRareChainFibres
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRawLocalRow
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockThinningCalibrated

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockJointFields

open TimeTheorem PairLog PhaseThreeClockVirtual PhaseThreeClockGatedLaw
  PhaseThreeClockGatedLevelOne PhaseThreeClockSeedTails PhaseThreeClockActivationSeed
  PhaseThreeClockThinning PhaseThreeClockShapeFreeze
  PhaseThreeClockRareDrips PhaseThreeClockRareDripCharging
  PhaseThreeClockMarkedShape PhaseThreeClockSharpActivationSeed
  PhaseThreeClockMacroscopicActivation PhaseThreeClockMarkCoverage
  PhaseThreeClockJointFront PhaseThreeClockRareChainCalibration
  PhaseThreeClockRareChainFibres PhaseThreeClockCore PhaseThreeClockCoreCounts
  PhaseThreeClockRawLocalRow PhaseThreeClockStoppedPassage PairLogAuxiliary
open PhaseThreeModel.Numeric

variable {n : ℕ}

theorem joint_front_induction_of_rare_good (init : InputCfg n)
    (hn : populationThreshold ≤ n) (C : Finset (Fin init.card))
    (s alpha : ℕ) (f tau : ℕ → ℕ) (ω : InputLog n)
    (hseed : ω ∈ seedPrefix init s)
    (hmask : C = clockSet (labelsAt init ω s))
    (hsafe : ∀ v, s ≤ v → shapeSafeAt init C s v ω)
    (ha : macroscopicTime init s ω = (alpha : WithTop ℕ))
    (hfirst : ∀ ell, 1 ≤ ell → ell ≤ clockCap n →
      StageEventSpec.firstAfter
        (fun t => 1 ≤ frontCount (virtualLabels init ω t) ell) s (f ell))
    (hbulk : ∀ ell, 1 ≤ ell → ell ≤ clockCap n →
      StageEventSpec.firstAfter
        (fun t => StageEventSpec.bulkThreshold C.card ≤
          frontCount (virtualLabels init ω t) ell) s (tau ell))
    (hsharp : ω ∉ sharpActivationFailure init s C.card)
    (hmarked : ∀ ell, 1 ≤ ell → ell < clockCap n →
      ω ∉ markedShapeFailure init C ell s)
    (hraw : ∀ ell, 1 ≤ ell → ell ≤ clockCap n →
      tau ell ≤ f ell + firstHitHorizon n)
    (hbase : maskContacts init C alpha (tau 1) ω ≤ 100 * C.card)
    (hcoarse : ∀ ell, 1 ≤ ell → ell < clockCap n →
      maskContacts init C (tau ell) (tau (ell + 1)) ω ≤ 100 * C.card)
    (hrare : ω ∉ rareChainFamilyFailure init C.card s (clockCap n)) :
    ∀ i, 1 ≤ i → i ≤ clockCap n →
      maskContacts init C (max (f i) alpha) (tau i) ω ≤ fineTicks C.card ∧
      (i < clockCap n → ThroughBulkShape init C s tau i ω) ∧
      (2 * frontWidth C.card < i → tau (i - 2 * frontWidth C.card) ≤ f i) := by
  apply joint_front_induction init hn C s alpha f tau ω
    hseed hmask hsafe ha hfirst hbulk hsharp hmarked hraw hbase hcoarse
  intro k hk hkQ
  apply lt_of_not_ge
  intro hcount
  apply hrare
  apply Set.mem_iUnion.mpr
  refine ⟨k, Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hk, by omega⟩, ?_⟩⟩
  apply Set.mem_iUnion.mpr
  refine ⟨f k, firstAfter_mem_positive_fibre init s k (f k) ω
    (hfirst k hk (by omega)), ?_⟩
  simpa only [sparseUpper, seedPrefix_card_eq init ω s hseed] using hcount

theorem effectiveMinuteL_le_top (init : InputCfg n)
    (fv : Lab init) (i : Fin init.card) :
    effectiveMinuteL init fv i ≤ StageEventSpec.clockTop n := by
  rw [effectiveMinuteL_eq_effMinute]
  unfold effMinute
  split_ifs
  · exact Nat.le_of_lt_succ (fv i).minute.isLt
  · exact Nat.zero_le _

/-- The first-hit width assertion gives the exact all-times Core bulk_width.
This does not use any rate estimate between consecutive maximum hits. -/
theorem bulk_width_of_first_hit_width (init : InputCfg n)
    (C : Finset (Fin init.card)) (s W : ℕ) (f tau : ℕ → ℕ) (ω : InputLog n)
    (hseed : ω ∈ seedPrefix init s)
    (hsafe : ∀ v, s ≤ v → shapeSafeAt init C s v ω)
    (hfirst : ∀ ell, 1 ≤ ell → ell ≤ clockCap n →
      StageEventSpec.firstAfter
        (fun t => 1 ≤ frontCount (virtualLabels init ω t) ell) s (f ell))
    (hbulk : ∀ ell, 1 ≤ ell → ell ≤ clockCap n →
      StageEventSpec.firstAfter
        (fun t => StageEventSpec.bulkThreshold C.card ≤
          frontCount (virtualLabels init ω t) ell) s (tau ell))
    (hwidth : ∀ ell, 1 ≤ ell → ell ≤ clockCap n → W < ell →
      tau (ell - W) ≤ f ell) :
    ∀ v, s ≤ v →
      frontHeightL init (virtualLabels init ω s) (virtualLabels init ω v) -
        frontQuantileL init (virtualLabels init ω s) (virtualLabels init ω v)
          (StageEventSpec.bulkThreshold C.card) ≤ W := by
  classical
  intro v hsv
  let beta := frontQuantileL init (virtualLabels init ω s) (virtualLabels init ω v)
    (StageEventSpec.bulkThreshold C.card)
  have hheight : frontHeightL init (virtualLabels init ω s) (virtualLabels init ω v) ≤
      beta + W := by
    unfold frontHeightL
    apply Finset.sup_le
    intro a ha
    have hclock := (Finset.mem_filter.mp ha).2
    let ell := effectiveMinuteL init (virtualLabels init ω v) a
    change ell ≤ beta + W
    by_cases hsmall : ell ≤ W
    · omega
    · have hellpos : 1 ≤ ell := by omega
      have hellQ : ell ≤ clockCap n :=
        effectiveMinuteL_le_top init (virtualLabels init ω v) a
      have hpositive : 1 ≤ frontCountL init
          (virtualLabels init ω s) (virtualLabels init ω v) ell := by
        unfold frontCountL StageEventSpec.labelCount
        apply Nat.succ_le_iff.mpr
        exact Finset.card_pos.mpr ⟨a, by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hclock, le_rfl⟩⟩
      rw [frontCountL_virtual_seed init ω s v ell hseed hsv (hsafe v hsv).2] at hpositive
      have hfv : f ell ≤ v :=
        firstAfter_le_of_hit (hfirst ell hellpos hellQ) hsv hpositive
      have htv : tau (ell - W) ≤ v :=
        (hwidth ell hellpos hellQ (by omega)).trans hfv
      have hlow : 1 ≤ ell - W := by omega
      have hlowQ : ell - W ≤ clockCap n := by omega
      have hm := frontCount_mono_safe init C s (tau (ell - W)) v (ell - W)
        (hbulk (ell - W) hlow hlowQ).1 htv hlow hlowQ
        ω (hsafe v hsv)
      have hb : StageEventSpec.bulkThreshold C.card ≤
          frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) (ell - W) := by
        rw [frontCountL_virtual_seed init ω s v (ell - W) hseed hsv (hsafe v hsv).2]
        exact (hbulk (ell - W) hlow hlowQ).2.1.trans hm
      have hmem : ell - W ∈
          (Finset.range (StageEventSpec.clockTop n + 1)).filter
            (fun q => StageEventSpec.bulkThreshold C.card ≤
              frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) q) := by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by change ell - W < clockCap n + 1; omega), hb⟩
      have hq : ell - W ≤ beta := Finset.le_sup (f := id) hmem
      omega
  change _ - beta ≤ W
  omega

theorem clockMask_card_eq_virtual_seed (init : InputCfg n)
    (C : Finset (Fin init.card)) (s : ℕ) (ω : InputLog n)
    (hseed : ω ∈ seedPrefix init s)
    (hmask : C = clockSet (labelsAt init ω s)) :
    C.card = RoleSplitConcentration.clockCount (virtualCfg init ω s) := by
  rw [virtualCfg_eq_trace_at_seedPrefix init ω s hseed]
  rw [← clockCount_labelsAt_eq_trace init ω s]
  change C.card = (clockSet (labelsAt init ω s)).card
  rw [hmask]

theorem core_tick_local_of_mask_budget (init : InputCfg n)
    (C : Finset (Fin init.card)) (s alpha : ℕ) (f tau : ℕ → ℕ) (ω : InputLog n)
    (hseed : ω ∈ seedPrefix init s)
    (hmask : C = clockSet (labelsAt init ω s))
    (hbudget : ∀ ell, 1 ≤ ell → ell ≤ clockCap n →
      maskContacts init C (max (f ell) alpha) (tau ell) ω ≤ fineTicks C.card) :
    ∀ ell, 1 ≤ ell → ell ≤ StageEventSpec.clockTop n →
      clockContactsL init (virtualLabels init ω s) (drawLabels init ω)
        (max (f ell) alpha) (tau ell) ≤
      StageEventSpec.localTickBudget (RoleSplitConcentration.clockCount (virtualCfg init ω s)) := by
  intro ell hell htop
  rw [← clockMask_card_eq_virtual_seed init C s ω hseed hmask,
    clockContactsL_virtual_seed init ω s _ _ hseed]
  have he := maskContacts_seed_eq_stageEvent init ω s (max (f ell) alpha) (tau ell)
  rw [← hmask] at he
  rw [← he]
  exact hbudget ell hell htop

theorem core_front_shape_of_through_bulk (init : InputCfg n)
    (C : Finset (Fin init.card)) (s : ℕ) (tau : ℕ → ℕ) (ω : InputLog n)
    (hseed : ω ∈ seedPrefix init s)
    (hmask : C = clockSet (labelsAt init ω s))
    (hsafe : ∀ v, s ≤ v → shapeSafeAt init C s v ω)
    (hshape : ∀ ell, 1 ≤ ell → ell < clockCap n →
      ThroughBulkShape init C s tau ell ω) :
    ∀ ell v, 1 ≤ ell → ell < StageEventSpec.clockTop n →
      s ≤ v → v ≤ tau ell →
      StageEventSpec.frontCutoff (RoleSplitConcentration.clockCount (virtualCfg init ω s)) ≤
        frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) ell →
      frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) ell ≤
        StageEventSpec.bulkThreshold (RoleSplitConcentration.clockCount (virtualCfg init ω s)) →
      RoleSplitConcentration.clockCount (virtualCfg init ω s) *
          frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) (ell + 1) ≤
        frontCountL init (virtualLabels init ω s) (virtualLabels init ω v) ell ^ 2 := by
  intro ell v hell htop hsv hvtau hlow hupp
  have hC := clockMask_card_eq_virtual_seed init C s ω hseed hmask
  have hfront (q : ℕ) := frontCountL_virtual_seed init ω s v q hseed hsv (hsafe v hsv).2
  rw [← hC, hfront ell] at hlow hupp
  rw [← hC, hfront ell, hfront (ell + 1)]
  exact hshape ell hell htop v hsv hvtau hlow hupp

/-- Every genuine positive bulk hit occurs on a recorded Clock pair. -/
theorem bulk_hit_is_mask_contact (init : InputCfg n)
    (C : Finset (Fin init.card)) (s ell b tau : ℕ)
    (hell : 1 ≤ ell) (hb : 1 ≤ b) (hcap : ell ≤ clockCap n)
    (ω : InputLog n) (hsafe : shapeSafeAt init C s tau ω)
    (hfirst : StageEventSpec.firstAfter
      (fun t => b ≤ frontCount (virtualLabels init ω t) ell) s tau) :
    maskContact init C tau ω := by
  classical
  have hst : s < tau := by
    have hz := frontCount_zero_at_seed init ω s ell hsafe.1.1 hell
    have hsle : s ≤ tau := hfirst.1
    by_contra hnot
    have he : tau = s := by omega
    have hp : b ≤ frontCount (virtualLabels init ω tau) ell := hfirst.2.1
    rw [he, hz] at hp
    omega
  have hsucc : tau - 1 + 1 = tau := by omega
  have hbelow : frontCount (virtualLabels init ω (tau - 1)) ell < b := by
    have hnot := hfirst.2.2 (tau - 1) (by omega) (by omega)
    omega
  have hstep := front_step_safe init C ell 0 s (tau - 1) (by omega) hell hcap ω
    (by simpa only [hsucc] using hsafe)
  have hpositive : 0 < gatedIndicator init ell (tau - 1) ω := by
    have hlo : (b : ℝ) ≤ frontCount (virtualLabels init ω tau) ell := by
      exact_mod_cast hfirst.2.1
    have hhi : (frontCount (virtualLabels init ω (tau - 1)) ell : ℝ) < b := by
      exact_mod_cast hbelow
    rw [hsucc] at hstep
    linarith
  have hex : ∃ i j, drawLabels init ω (tau - 1 + 1) = some (i, j) ∧
      GatedTick ell (virtualLabels init ω (tau - 1)) i j := by
    by_contra hnot
    have hz : gatedIndicator init ell (tau - 1) ω = 0 := by
      simp only [gatedIndicator, show ¬ ∃ i j,
        drawLabels init ω (tau - 1 + 1) = some (i, j) ∧
          GatedTick ell (auxLabels init virtualRule ω (tau - 1)) i j from hnot,
        if_false]
    rw [hz] at hpositive
    exact (lt_irrefl 0) hpositive
  obtain ⟨i, j, hd, hg⟩ := hex
  have hroles := gatedTick_clock_roles _ ell i j hg
  have hcur := shapeSafeAt_anti init C s (tau - 1) tau (by omega) ω hsafe
  have hguard := shapeSafeAt_guard init C ell 0 s (tau - 1) (by omega) hell ω hcur
  have hmi : i ∈ C := by
    rw [hguard.2.1]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hroles.1⟩
  have hmj : j ∈ C := by
    rw [hguard.2.1]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hroles.2⟩
  exact ⟨i, j, by simpa only [hsucc] using hd, hmi, hmj⟩

theorem maskContacts_strict_before_contact (init : InputCfg n)
    (C : Finset (Fin init.card)) (u v tau : ℕ) (ω : InputLog n)
    (huv : u ≤ v) (hvt : v < tau) (htick : maskContact init C tau ω) :
    maskContacts init C u v ω < maskContacts init C u tau ω := by
  classical
  let A := (Finset.Ioc u v).filter (fun t => maskContact init C t ω)
  have hnot : tau ∉ A := by
    intro h
    have hh := Finset.mem_Ioc.mp (Finset.mem_filter.mp h).1
    omega
  have hsub : insert tau A ⊆
      (Finset.Ioc u tau).filter (fun t => maskContact init C t ω) := by
    intro t ht
    rcases Finset.mem_insert.mp ht with he | ha
    · subst t
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, le_rfl⟩, htick⟩
    · rcases Finset.mem_filter.mp ha with ⟨hi, hc⟩
      rcases Finset.mem_Ioc.mp hi with ⟨hut, htv⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hut, by omega⟩, hc⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at hh
  exact Nat.lt_of_succ_le hh

/-- Equality at the D-contact threshold is sufficient: if tau were later,
its own hitting interaction would be an additional Clock contact. -/
theorem fine_raw_of_tick_budget_and_contacts (init : InputCfg n)
    (C : Finset (Fin init.card)) (s ell alpha f tau N : ℕ)
    (hell : 1 ≤ ell) (hb : 1 ≤ StageEventSpec.bulkThreshold C.card)
    (hcap : ell ≤ clockCap n) (ω : InputLog n)
    (hsafe : shapeSafeAt init C s tau ω)
    (hbulk : StageEventSpec.firstAfter
      (fun t => StageEventSpec.bulkThreshold C.card ≤
        frontCount (virtualLabels init ω t) ell) s tau)
    (hbudget : maskContacts init C (max f alpha) tau ω ≤ fineTicks C.card)
    (hcontacts : fineTicks C.card ≤
      maskContacts init C (max f alpha) (max f alpha + N) ω) :
    tau ≤ max f alpha + N := by
  by_contra hnot
  have hstrict := maskContacts_strict_before_contact init C (max f alpha)
    (max f alpha + N) tau ω (Nat.le_add_right _ _) (by omega)
    (bulk_hit_is_mask_contact init C s ell (StageEventSpec.bulkThreshold C.card)
      tau hell hb hcap ω hsafe hbulk)
  omega

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockJointFields

end
