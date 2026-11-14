-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockRareChainFibres.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRareChainCalibration
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockRareDripCharging
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockShapeSeedFibre
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockBulkFamily
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockAssembly

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRareChainFibres

open TimeTheorem PairLog StageEventSpec PhaseThreeModel.Numeric
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockSeedTails
  PhaseThreeClockProducer PhaseThreeClockAssembly
  PhaseThreeClockEarlyMarkInitialization PhaseThreeClockNormalRiseStoppedLaw
  PhaseThreeClockNormalBarrierStarts PhaseThreeClockRareDrips
  PhaseThreeClockRareDripCharging PhaseThreeClockRareChainCalibration
  PhaseThreeClockShapeFreeze PhaseThreeClockShapeSeedFibre
  PhaseThreeClockSharpActivationSeed PhaseThreeClockEarlyMarkSeedTail
  PhaseThreeClockBulkFamily PhaseThreeClockActivationSeed

variable {n : ℕ}

def rareChainFailure (init : InputCfg n) (C s k : ℕ) : Set (InputLog n) :=
  ⋃ u : ℕ, earlyCutoffFibre init s k 1 u ∩
    {ω | ((PhaseThreeModel.Numeric.frontWidth C - 1 : ℕ) : ℝ) ≤
      rareDripCount init k (shapeCutoff C) (sparseUpper C) u
        (firstHitHorizon init.card) ω}

def rareChainFamilyFailure (init : InputCfg n) (C s Q : ℕ) :
    Set (InputLog n) :=
  ⋃ k ∈ Finset.Icc 1 Q, rareChainFailure init C s k

theorem rareChainFailure_measurable (init : InputCfg n) (C s k : ℕ) :
    MeasurableSet (rareChainFailure init C s k) := by
  refine MeasurableSet.iUnion fun u => ?_
  exact (((pairLogFiltration _ _).le u) _
    (earlyCutoffFibre_measurable init s k 1 u)).inter
      (((pairLogFiltration _ _).le (u + firstHitHorizon init.card)) _
        (rareDripCount_tail_measurable init k (shapeCutoff C) (sparseUpper C)
          u (firstHitHorizon init.card) _))

theorem rareChainFamilyFailure_measurable (init : InputCfg n) (C s Q : ℕ) :
    MeasurableSet (rareChainFamilyFailure init C s Q) :=
  MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
    rareChainFailure_measurable init C s k

theorem rare_chain_observed_prefix_tail (init : InputCfg n) (C s k : ℕ)
    (hn : populationThreshold ≤ init.card)
    (hlo : (6 / 25 : ℝ) * (init.card : ℝ) ≤ C) (hCm : C ≤ init.card)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E) :
    law init (E ∩ rareChainFailure init C s k) ≤
      ENNReal.ofReal ((C : ℝ) ^ rareExponent C) * law init E := by
  let A : ℕ → Set (InputLog n) := fun u => E ∩ earlyCutoffFibre init s k 1 u
  let B : ℕ → Set (InputLog n) := fun u =>
    {ω | ((PhaseThreeModel.Numeric.frontWidth C - 1 : ℕ) : ℝ) ≤
      rareDripCount init k (shapeCutoff C) (sparseUpper C) u
        (firstHitHorizon init.card) ω}
  have hA (u : ℕ) : MeasurableSet[pairLogFiltration _ _ u] (A u) :=
    earlyCutoff_prefix_measurable init s k 1 u E hE
  have hdisj : Pairwise (fun u v => Disjoint (A u) (A v)) := by
    intro u v huv
    apply Set.disjoint_left.mpr
    intro ω hu hv
    exact huv (earlyCutoffFibre_unique init s k 1 u v ω hu.2 hv.2)
  have hmass : (∑' u, law init (A u)) ≤ law init E := by
    rw [← measure_iUnion hdisj
      (fun u => ((pairLogFiltration _ _).le u) _ (hA u))]
    apply measure_mono
    intro ω hω
    obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hω
    exact hu.1
  have hlocal (u : ℕ) : law init (A u ∩ B u) ≤
      ENNReal.ofReal ((C : ℝ) ^ rareExponent C) * law init (A u) :=
    rareDrip_calibrated_prefix_tail init C hn hlo hCm k u (A u) (hA u)
  have hcover : E ∩ rareChainFailure init C s k ⊆ ⋃ u : ℕ, A u ∩ B u := by
    rintro ω ⟨he, hb⟩
    obtain ⟨u, hu, hr⟩ := Set.mem_iUnion.mp hb
    exact Set.mem_iUnion.mpr ⟨u, ⟨he, hu⟩, hr⟩
  calc
    law init (E ∩ rareChainFailure init C s k) ≤ law init (⋃ u : ℕ, A u ∩ B u) :=
      measure_mono hcover
    _ ≤ ∑' u : ℕ, law init (A u ∩ B u) := measure_iUnion_le _
    _ ≤ ∑' u : ℕ, ENNReal.ofReal ((C : ℝ) ^ rareExponent C) * law init (A u) :=
      ENNReal.tsum_le_tsum hlocal
    _ = ENNReal.ofReal ((C : ℝ) ^ rareExponent C) * ∑' u : ℕ, law init (A u) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ _ := mul_le_mul_left' hmass _

theorem rare_chain_family_prefix_tail (init : InputCfg n) (C s Q : ℕ)
    (hn : populationThreshold ≤ init.card)
    (hlo : (6 / 25 : ℝ) * (init.card : ℝ) ≤ C) (hCm : C ≤ init.card)
    (hQ : (Q : ℝ) ≤ 1024 * Real.log (C : ℝ))
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E) :
    law init (E ∩ rareChainFamilyFailure init C s Q) ≤
      ENNReal.ofReal ((C : ℝ) ^ (-(81 / 8 : ℝ))) * law init E := by
  have hfamily := finite_union_prefix_bound (law init) E
    (rareChainFailure init C s) (Finset.Icc 1 Q)
    (ENNReal.ofReal ((C : ℝ) ^ rareExponent C) * law init E)
    (fun k _ => rare_chain_observed_prefix_tail init C s k hn hlo hCm E hE)
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hfamily
  obtain ⟨hC, hx, -⟩ := logarithmic_inputs hn hlo hCm
  have hcoef : (Q : ℝ≥0∞) * ENNReal.ofReal ((C : ℝ) ^ rareExponent C) ≤
      ENNReal.ofReal ((C : ℝ) ^ (-(81 / 8 : ℝ))) := by
    calc
      _ = ENNReal.ofReal ((Q : ℝ) * (C : ℝ) ^ rareExponent C) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg Q), ENNReal.ofReal_natCast]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (rare_level_union_calibration hC hx hQ)
  exact hfamily.trans (by
    simpa only [mul_assoc] using mul_le_mul_right' hcoef (law init E))

theorem seed_rare_chain_fixed_mask_prefix_tail
    (init : InputCfg n) (hn : populationThreshold ≤ n)
    (C : Finset (Fin init.card)) (s : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : ∀ ω ∈ E, ω ∈ seedPrefix init s ∧ C = clockSet (labelsAt init ω s)) :
    law init (E ∩ rareChainFamilyFailure init C.card s (clockCap n)) ≤
      ENNReal.ofReal ((C.card : ℝ) ^ (-(81 / 8 : ℝ))) * law init E := by
  by_cases he : E = ∅
  · simp only [he, Set.empty_inter, measure_empty, mul_zero, le_refl]
  · obtain ⟨ω, hω⟩ := Set.nonempty_iff_ne_empty.mpr he
    have hs := hseed ω hω
    have hcount : clockCount (labelsAt init ω s) = C.card := by
      change (clockSet (labelsAt init ω s)).card = C.card
      rw [← hs.2]
    obtain ⟨hm, hlo, hCm⟩ :=
      seed_clock_calibration_inputs init hn ω s C.card hs.1 hcount
    have hcard := seedPrefix_card_eq init ω s hs.1
    have hloN : (6 / 25 : ℝ) * (n : ℝ) ≤ C.card := by
      simpa only [hcard] using hlo
    have hCn : C.card ≤ n := by simpa only [hcard] using hCm
    obtain ⟨_, _, _, _, _, _, _, _, _, hQ, _, _, _, _⟩ :=
      numeric_calibration_core hn hloN hCn
    exact rare_chain_family_prefix_tail init C.card s (clockCap n)
      hm hlo hCm hQ E hE

def seedRareChainFailure (init : InputCfg n) (s : ℕ) : Set (InputLog n) :=
  {ω | ω ∈ rareChainFamilyFailure init (clockSet (labelsAt init ω s)).card
    s (clockCap n)}

theorem seed_rare_chain_population_prefix_tail
    (init : InputCfg n) (hn : populationThreshold ≤ n) (s : ℕ)
    (E : Set (InputLog n)) (hE : MeasurableSet[pairLogFiltration _ _ s] E)
    (hseed : E ⊆ seedPrefix init s) :
    law init (E ∩ seedRareChainFailure init s) ≤
      ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 10)) * law init E := by
  apply seed_mask_prefix_union init s E hE
    (fun C => rareChainFamilyFailure init C.card s (clockCap n))
    (ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 10)))
  intro C
  let A : Set (InputLog n) := E ∩ {ω | C = clockSet (labelsAt init ω s)}
  have hA : MeasurableSet[pairLogFiltration _ _ s] A :=
    hE.inter (seed_clockMask_measurable init s C)
  have hbound := seed_rare_chain_fixed_mask_prefix_tail init hn C s A hA
    (fun ω hω => ⟨hseed hω.1, hω.2⟩)
  by_cases he : A = ∅
  · change law init (A ∩ _) ≤ _ * law init A
    simp only [he, Set.empty_inter, measure_empty, mul_zero, le_refl]
  · obtain ⟨ω, hω⟩ := Set.nonempty_iff_ne_empty.mpr he
    have hs := hseed hω.1
    have hcount : clockCount (labelsAt init ω s) = C.card := by
      change (clockSet (labelsAt init ω s)).card = C.card
      rw [← hω.2]
    obtain ⟨hm, hlo, hCm⟩ :=
      seed_clock_calibration_inputs init hn ω s C.card hs hcount
    have hcard := seedPrefix_card_eq init ω s hs
    have hloN : (6 / 25 : ℝ) * (n : ℝ) ≤ C.card := by
      simpa only [hcard] using hlo
    have hCn : C.card ≤ n := by simpa only [hcard] using hCm
    exact hbound.trans (mul_le_mul_right'
      (ENNReal.ofReal_le_ofReal (rare_population_calibration hn hloN hCn)) _)

theorem firstAfter_mem_positive_fibre (init : InputCfg n)
    (s k u : ℕ) (ω : InputLog n)
    (hfirst : StageEventSpec.firstAfter
      (fun t => 1 ≤ frontCount (virtualLabels init ω t) k) s u) :
    ω ∈ earlyCutoffFibre init s k 1 u := by
  refine ⟨hfirst.1, hfirst.2.1, ?_⟩
  intro t hst htu
  exact lt_of_not_ge (hfirst.2.2 t hst htu)

theorem sparse_chain_mem_rare_failure (init : InputCfg n)
    (C : Finset (Fin init.card)) (s k b : ℕ)
    (hC : 0 < C.card) (hk : 1 ≤ k)
    (hd : 2 ≤ PhaseThreeModel.Numeric.frontWidth C.card)
    (hw : 1 ≤ shapeCutoff C.card) (hwb : shapeCutoff C.card ≤ b)
    (hcap : k + PhaseThreeModel.Numeric.frontWidth C.card ≤ clockCap n)
    (f : ℕ → ℕ) (tau : ℕ) (ω : InputLog n)
    (hfirst : ∀ ell, k ≤ ell → ell ≤ k + PhaseThreeModel.Numeric.frontWidth C.card →
      StageEventSpec.firstAfter
        (fun t => 1 ≤ frontCount (virtualLabels init ω t) ell) s (f ell))
    (hsafe : shapeSafeAt init C s
      (max (f (k + PhaseThreeModel.Numeric.frontWidth C.card)) tau) ω)
    (hbulk : StageEventSpec.firstAfter
      (fun t => b ≤ frontCount (virtualLabels init ω t) k) s tau)
    (hshape : ∀ t, s ≤ t → t ≤ tau →
      shapeCutoff C.card ≤ frontCount (virtualLabels init ω t) k →
      frontCount (virtualLabels init ω t) k ≤ b →
      C.card * frontCount (virtualLabels init ω t) (k + 1) ≤
        frontCount (virtualLabels init ω t) k ^ 2)
    (horizon : tau ≤ f k + firstHitHorizon init.card)
    (hsmall : frontCount
      (virtualLabels init ω (f (k + PhaseThreeModel.Numeric.frontWidth C.card))) k <
        shapeCutoff C.card) :
    ω ∈ rareChainFailure init C.card s k := by
  apply Set.mem_iUnion.mpr
  refine ⟨f k, firstAfter_mem_positive_fibre init s k (f k) ω
    (hfirst k le_rfl (by omega)), ?_⟩
  exact sparse_chain_implies_rare_count init C s k
    (PhaseThreeModel.Numeric.frontWidth C.card) (shapeCutoff C.card) b
    (firstHitHorizon init.card) hC hk hd hw hwb
    (by simpa only [clockCap, clockHours] using hcap)
    f tau ω hfirst hsafe hbulk hshape horizon hsmall

theorem sparse_chain_excluded (init : InputCfg n)
    (C : Finset (Fin init.card)) (s k b : ℕ)
    (hC : 0 < C.card) (hk : 1 ≤ k)
    (hd : 2 ≤ PhaseThreeModel.Numeric.frontWidth C.card)
    (hw : 1 ≤ shapeCutoff C.card) (hwb : shapeCutoff C.card ≤ b)
    (hcap : k + PhaseThreeModel.Numeric.frontWidth C.card ≤ clockCap n)
    (f : ℕ → ℕ) (tau : ℕ) (ω : InputLog n)
    (hfirst : ∀ ell, k ≤ ell → ell ≤ k + PhaseThreeModel.Numeric.frontWidth C.card →
      StageEventSpec.firstAfter
        (fun t => 1 ≤ frontCount (virtualLabels init ω t) ell) s (f ell))
    (hsafe : shapeSafeAt init C s
      (max (f (k + PhaseThreeModel.Numeric.frontWidth C.card)) tau) ω)
    (hbulk : StageEventSpec.firstAfter
      (fun t => b ≤ frontCount (virtualLabels init ω t) k) s tau)
    (hshape : ∀ t, s ≤ t → t ≤ tau →
      shapeCutoff C.card ≤ frontCount (virtualLabels init ω t) k →
      frontCount (virtualLabels init ω t) k ≤ b →
      C.card * frontCount (virtualLabels init ω t) (k + 1) ≤
        frontCount (virtualLabels init ω t) k ^ 2)
    (horizon : tau ≤ f k + firstHitHorizon init.card)
    (hgood : ω ∉ rareChainFamilyFailure init C.card s (clockCap n)) :
    shapeCutoff C.card ≤ frontCount
      (virtualLabels init ω (f (k + PhaseThreeModel.Numeric.frontWidth C.card))) k := by
  by_contra hnot
  apply hgood
  apply Set.mem_iUnion.mpr
  refine ⟨k, Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hk, by omega⟩, ?_⟩⟩
  exact sparse_chain_mem_rare_failure init C s k b hC hk hd hw hwb hcap
    f tau ω hfirst hsafe hbulk hshape horizon (lt_of_not_ge hnot)

theorem seed_rare_chain_entry_fibre_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) (s : ℕ) :
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
      SeedProfile n init (trace init ω s) ∧
      ∃ T, T ≤ earlyHorizon n ∧ AsyncEntry init ω s T ∧
        ω ∈ seedRareChainFailure init s} ≤
      ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 10)) *
        law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  apply (measure_mono ?_).trans
    ((seed_rare_chain_population_prefix_tail init hn s (seedPrefix init s)
      (seedPrefix_measurable init s) (fun _ h => h)).trans
        (mul_le_mul_left' (measure_mono
          (show seedPrefix init s ⊆ {ω | seedTime init 3 ω = (s : WithTop ℕ)}
            from fun _ h => h.1)) _))
  rintro ω ⟨hs, hp, T, hT, he, hb⟩
  exact ⟨⟨hs, hp⟩, hb⟩

def rareChainEntryFailure (init : InputCfg n) : Set (InputLog n) :=
  {ω | ∃ s T : ℕ, seedTime init 3 ω = (s : WithTop ℕ) ∧
    T ≤ earlyHorizon n ∧ AsyncEntry init ω s T ∧ ω ∈ seedRareChainFailure init s}

theorem rare_chain_global_entry_tail (init : InputCfg n)
    (hn : populationThreshold ≤ n) :
    law init (rareChainEntryFailure init) ≤
      ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 10)) := by
  apply splice_of_local (law init) (seedTime init 3) (rareChainEntryFailure init) _
    (fun s => (pairLogFiltration _ _).le s _ (seedTime_pastTime init 3 s))
  · rintro ω ⟨s, T, hs, hT, he, hb⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    apply (measure_mono ?_).trans (seed_rare_chain_entry_fibre_tail init hn s)
    rintro ω ⟨⟨u, T, hu, hT, he, hb⟩, hs⟩
    have hus : u = s := WithTop.coe_injective (hu.symm.trans hs)
    subst u
    exact ⟨hs, he.seed_profile, T, hT, he, hb⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockRareChainFibres

end
