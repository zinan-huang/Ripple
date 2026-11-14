-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockMarkCoverage.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMarkedShape
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockSharpActivationSeed
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRareDripCharging

/-!
P5 coverage in the P6 induction. The sharp activation event is used only
pathwise. In particular it is not intersected into a conditioning event.
The right endpoint includes the hitting Clock tick.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMarkCoverage

open TimeTheorem PairLog PhaseThreeClockVirtual PhaseThreeClockGatedLaw
  PhaseThreeClockSeedTails PhaseThreeClockThinning
  PhaseThreeClockSmallActivation PhaseThreeClockMacroscopicActivation
  PhaseThreeClockMarkedWindow PhaseThreeClockMarkedShape
  PhaseThreeClockSharpActivationSeed PhaseThreeClockActivationCalibration

variable {L K n : ℕ}

theorem maskContacts_mono_right (init : Cfg L K)
    (C : Finset (Fin init.card)) (a b c : ℕ) (hbc : b ≤ c) (ω : Ω L K) :
    maskContacts init C a b ω ≤ maskContacts init C a c ω := by
  classical
  apply Finset.card_le_card
  intro t ht
  rcases Finset.mem_filter.mp ht with ⟨ht, hc⟩
  rcases Finset.mem_Ioc.mp ht with ⟨hat, htb⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hat, htb.trans hbc⟩, hc⟩

theorem maskContacts_antitone_left (init : Cfg L K)
    (C : Finset (Fin init.card)) (a b c : ℕ) (hab : a ≤ b) (ω : Ω L K) :
    maskContacts init C b c ω ≤ maskContacts init C a c ω := by
  classical
  apply Finset.card_le_card
  intro t ht
  rcases Finset.mem_filter.mp ht with ⟨ht, hc⟩
  rcases Finset.mem_Ioc.mp ht with ⟨hbt, htc⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hab.trans_lt hbt, htc⟩, hc⟩

theorem maskContacts_triangle (init : Cfg L K)
    (C : Finset (Fin init.card)) (a b c : ℕ) (ω : Ω L K) :
    maskContacts init C a c ω ≤
      maskContacts init C a b ω + maskContacts init C b c ω := by
  classical
  let A := (Finset.Ioc a b).filter (fun t => maskContact init C t ω)
  let B := (Finset.Ioc b c).filter (fun t => maskContact init C t ω)
  have hsub : (Finset.Ioc a c).filter (fun t => maskContact init C t ω) ⊆ A ∪ B := by
    intro t ht
    rcases Finset.mem_filter.mp ht with ⟨ht, hc⟩
    rcases Finset.mem_Ioc.mp ht with ⟨hat, htc⟩
    by_cases htb : t ≤ b
    · exact Finset.mem_union.mpr (Or.inl
        (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hat, htb⟩, hc⟩))
    · exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, htc⟩, hc⟩))
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le A B)

theorem levelPositiveTime_eq_firstAfter (init : Cfg L K)
    (s ell f : ℕ) (ω : Ω L K)
    (hf : StageEventSpec.firstAfter
      (fun t => 1 ≤ frontCount (virtualLabels init ω t) ell) s f) :
    levelPositiveTime init s ell ω = (f : WithTop ℕ) := by
  classical
  have hf1 : 1 ≤ frontCount (virtualLabels init ω f) ell := hf.2.1
  have hex : ∃ t, s ≤ t ∧ 0 < frontCount (virtualLabels init ω t) ell :=
    ⟨f, hf.1, by omega⟩
  have he : Nat.find hex = f := by
    apply Nat.le_antisymm
    · exact Nat.find_min' hex ⟨hf.1, by omega⟩
    · by_contra hnot
      have hstate := Nat.find_spec hex
      have hs1 : s ≤ Nat.find hex := hstate.1
      have hs2 : 0 < frontCount (virtualLabels init ω (Nat.find hex)) ell := hstate.2
      exact hf.2.2 (Nat.find hex) hs1 (by omega) (by omega)
  simp only [levelPositiveTime, dif_pos hex, he]

theorem secondStart_eq_max (init : Cfg L K)
    (s ell u N alpha f : ℕ) (ω : Ω L K)
    (ha : macroscopicTime init s ω = (alpha : WithTop ℕ))
    (hf : levelPositiveTime init s ell ω = (f : WithTop ℕ))
    (hdeadline : alpha ≤ u + N) :
    secondStart init s ell u N ω = ((max alpha f : ℕ) : WithTop ℕ) := by
  have hd : (alpha : WithTop ℕ) ≤ ((u + N : ℕ) : WithTop ℕ) := by
    exact_mod_cast hdeadline
  simp only [secondStart, earlyEnd, ha, hf, min_eq_left hd]
  by_cases h : alpha ≤ f
  · have h' : (alpha : WithTop ℕ) ≤ (f : WithTop ℕ) := by exact_mod_cast h
    rw [max_eq_right h, max_eq_right h']
  · have h' : (f : WithTop ℕ) ≤ (alpha : WithTop ℕ) := by
      exact_mod_cast (show f ≤ alpha by omega)
    rw [max_eq_left (show f ≤ alpha by omega), max_eq_left h']

theorem markWindow_of_tick_budget (init : InputCfg n)
    (C : Finset (Fin init.card)) (s ell u alpha f tau v : ℕ) (ω : InputLog n)
    (hu : smallActivationTime init s C.card ω = (u : WithTop ℕ))
    (ha : macroscopicTime init s ω = (alpha : WithTop ℕ))
    (hf : StageEventSpec.firstAfter
      (fun t => 1 ≤ frontCount (virtualLabels init ω t) ell) s f)
    (hua : u ≤ alpha)
    (hdeadline : alpha ≤ u + PhaseThreeModel.Numeric.activationHalfHorizon init.card)
    (hbudget : maskContacts init C (max f alpha) tau ω ≤
      PhaseThreeModel.Numeric.fineTicks C.card)
    (hvtau : v ≤ tau) :
    markWindow init C ell s v ω := by
  by_cases hvu : v ≤ u
  · left
    rw [hu]
    exact_mod_cast hvu
  · right
    have huv : u ≤ v := by omega
    refine ⟨u, hu, huv, ?_⟩
    have hB := secondStart_eq_max init s ell u
      (PhaseThreeModel.Numeric.activationHalfHorizon init.card) alpha f ω ha
      (levelPositiveTime_eq_firstAfter init s ell f ω hf) hdeadline
    have hcount := laterClockCount_eq_maskContacts init C s ell u
      (PhaseThreeModel.Numeric.activationHalfHorizon init.card) (max alpha f) ω
      hB (hua.trans (le_max_left _ _)) (v - u)
    have he : u + (v - u) = v := Nat.add_sub_of_le huv
    rw [he, max_comm alpha f] at hcount
    rw [hcount]
    exact_mod_cast ((maskContacts_mono_right init C (max f alpha) v tau hvtau ω).trans hbudget)

/-- A2 supplies the actual small-activation fibre and identifies H with alpha.
Every required v through tau is covered, including v before the second start. -/
theorem markWindow_of_sharp_activation (init : InputCfg n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (C : Finset (Fin init.card)) (s ell alpha f tau : ℕ) (ω : InputLog n)
    (hseed : ω ∈ seedPrefix init s)
    (hmask : C = clockSet (labelsAt init ω s))
    (ha : macroscopicTime init s ω = (alpha : WithTop ℕ))
    (hf : StageEventSpec.firstAfter
      (fun t => 1 ≤ frontCount (virtualLabels init ω t) ell) s f)
    (hsharp : ω ∉ sharpActivationFailure init s C.card)
    (hbudget : maskContacts init C (max f alpha) tau ω ≤
      PhaseThreeModel.Numeric.fineTicks C.card) :
    ∀ v, v ≤ tau → markWindow init C ell s v ω := by
  have hcount : clockCount (labelsAt init ω s) = C.card := by
    change (clockSet (labelsAt init ω s)).card = C.card
    rw [← hmask]
  obtain ⟨hm, hlo, hCn⟩ := seed_clock_calibration_inputs init hn ω s C.card hseed hcount
  have hcal := activation_calibration_data hm hlo hCn
  have hnotTop : smallActivationTime init s C.card ω ≠ ⊤ := by
    intro h
    exact hsharp (Or.inl h)
  obtain ⟨u, hu'⟩ := WithTop.ne_top_iff_exists.mp hnotTop
  have hu : smallActivationTime init s C.card ω = (u : WithTop ℕ) := hu'.symm
  have hua : u ≤ alpha := by
    have h := smallActivationTime_le_macroscopic init s C.card ω hcal.small_le_macro
    rw [hu, ha] at h
    exact_mod_cast h
  have hd : alpha ≤ u + PhaseThreeModel.Numeric.activationHalfHorizon init.card := by
    by_contra hnot
    apply hsharp
    right
    refine ⟨u, hu, ?_⟩
    rw [ha]
    exact_mod_cast (show u + PhaseThreeModel.Numeric.activationHalfHorizon init.card < alpha by omega)
  intro v hv
  exact markWindow_of_tick_budget init C s ell u alpha f tau v ω
    hu ha hf hua hd hbudget hv

/-- The A_i -> F_i step of P6, with the P5 coverage obligation discharged. -/
theorem shape_through_bulk_of_tick_budget (init : InputCfg n)
    (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (C : Finset (Fin init.card)) (s ell alpha f tau : ℕ) (ω : InputLog n)
    (hseed : ω ∈ seedPrefix init s)
    (hmask : C = clockSet (labelsAt init ω s))
    (ha : macroscopicTime init s ω = (alpha : WithTop ℕ))
    (hf : StageEventSpec.firstAfter
      (fun t => 1 ≤ frontCount (virtualLabels init ω t) ell) s f)
    (hsharp : ω ∉ sharpActivationFailure init s C.card)
    (hshape : ω ∉ markedShapeFailure init C ell s)
    (hbudget : maskContacts init C (max f alpha) tau ω ≤
      PhaseThreeModel.Numeric.fineTicks C.card) :
    ∀ v, s ≤ v → v ≤ tau →
      (∀ i, (virtualLabels init ω v i).phase.val ≤ 3) →
      PhaseThreeModel.Numeric.shapeCutoff C.card ≤ frontCount (virtualLabels init ω v) ell →
      frontCount (virtualLabels init ω v) ell ≤ StageEventSpec.bulkThreshold C.card →
      C.card * frontCount (virtualLabels init ω v) (ell + 1) ≤
        frontCount (virtualLabels init ω v) ell ^ 2 := by
  intro v hsv hvtau hcap hw hb
  by_contra hbad
  exact hshape ⟨v, hsv, hcap, hw, hb,
    markWindow_of_sharp_activation init hn C s ell alpha f tau ω
      hseed hmask ha hf hsharp hbudget v hvtau, hbad⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMarkCoverage

end
