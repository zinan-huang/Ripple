-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockFiniteAllCap.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockFinitePassageLevels
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockEarlyMarkEmbedding
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockActivationRows

/-!
# A genuine finite all-cap passage on the virtual continuation

Every fixed physical pair is selected again almost surely after every
deterministic time, under the original pair-log law. A positive front
therefore spreads to every Clock on the homogeneous virtual continuation.
Combining this with finite bulk passage at the cap proves a finite all-cap
hit, and hence a genuine first-after witness on an AsyncEntry seed fibre.

This file proves finiteness only. It does not give the 16000*n*log(n)
all-cap deadline or the 20000*n*log(n) Core deadline.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockFiniteAllCap

open TimeTheorem PairLog PairLogAuxiliary
  PhaseThreeClockVirtual PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne
  PhaseThreeClockThinning PhaseThreeClockFirstPositive
  PhaseThreeClockNextFrontBirth PhaseThreeClockFinitePassageLevels
  PhaseThreeClockEmbeddingBridge PhaseThreeClockEarlyMarkEmbedding
  PhaseThreeClockCore PhaseThreeClockSeedTails PhaseThreeClockActivationSeed
  PhaseThreeClockRawLocalRow PhaseThreeClockActivationRows PhaseThreeClockProducer

variable {L : ℕ}

theorem mask_no_future_contact_null (init : Cfg L 256) (hc : 2 ≤ init.card)
    (A : Finset (Fin init.card)) (hA : 2 ≤ A.card) (u : ℕ) :
    law init {ω | ∀ t, ¬ maskContact init A (u + t + 1) ω} = 0 := by
  classical
  let D : Set (Ω L 256) := {ω | ∀ t, ¬ maskContact init A (u + t + 1) ω}
  let a : ℝ := (law init).real D
  have hmR : (2 : ℝ) ≤ init.card := by exact_mod_cast hc
  have hAR : (2 : ℝ) ≤ A.card := by exact_mod_cast hA
  have hq : 0 < clockMaskRate init.card A.card := by
    rw [clockMaskRate_eq_real init.card A.card (by omega)]
    exact div_pos (mul_pos (by linarith) (by linarith))
      (mul_pos (by linarith) (by linarith))
  have hzero (ω : Ω L 256) (hω : ω ∈ D) (N : ℕ) :
      maskTickCount init A u N ω = 0 := by
    unfold maskTickCount PhaseThreeScalar.bernoulliCount
    apply Finset.sum_eq_zero
    intro t ht
    exact if_neg (hω t)
  have hbound (N : ℕ) :
      a ≤ Real.exp (-clockMaskRate init.card A.card * (N : ℝ) / 2) := by
    have hsub : D ⊆ Set.univ ∩ {ω | (-Real.log (2 : ℝ)) * 0 ≤
        (-Real.log (2 : ℝ)) * maskTickCount init A u N ω} := by
      intro ω hω
      exact ⟨Set.mem_univ _, by simp only [Set.mem_setOf_eq]; rw [hzero ω hω N]⟩
    have ht := prefix_maskTick_exponential_tail init hc A u N Set.univ
      MeasurableSet.univ (-Real.log (2 : ℝ)) 0
    have hexp : Real.exp (-Real.log (2 : ℝ)) = (1 : ℝ) / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    have harg :
        (Real.exp (-Real.log (2 : ℝ)) - 1) * clockMaskRate init.card A.card * (N : ℝ) -
            (-Real.log (2 : ℝ)) * 0 =
          -clockMaskRate init.card A.card * (N : ℝ) / 2 := by
      rw [hexp]
      ring
    rw [harg] at ht
    exact (measureReal_mono hsub).trans (by simpa using ht)
  have ha : a = 0 := by
    apply le_antisymm ?_ (by dsimp only [a]; positivity)
    by_contra hnot
    have hpos : 0 < a := lt_of_not_ge hnot
    obtain ⟨N, hN⟩ := exists_nat_gt (-2 * Real.log a / clockMaskRate init.card A.card)
    have hprod : -2 * Real.log a < (N : ℝ) * clockMaskRate init.card A.card :=
      (div_lt_iff₀ hq).1 hN
    have harg : -clockMaskRate init.card A.card * (N : ℝ) / 2 < Real.log a := by
      nlinarith
    have hexp : Real.exp (-clockMaskRate init.card A.card * (N : ℝ) / 2) < a := by
      simpa only [Real.exp_log hpos] using Real.exp_lt_exp.mpr harg
    exact (not_lt_of_ge (hbound N)) hexp
  calc
    law init {ω | ∀ t, ¬ maskContact init A (u + t + 1) ω} = ENNReal.ofReal a :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = 0 := by rw [ha, ENNReal.ofReal_zero]

/-- One full-measure scheduler event handles all later observed starts. -/
theorem fixed_pair_contacts_everywhere_ae (init : Cfg L 256) (hc : 2 ≤ init.card) :
    ∀ᵐ ω ∂law init, ∀ u (i j : Fin init.card), i ≠ j →
      ∃ t, maskContact init {i, j} (u + t + 1) ω := by
  classical
  apply ae_all_iff.mpr
  intro u
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i ≠ j
  · have hA : 2 ≤ ({i, j} : Finset (Fin init.card)).card := by simp [hij]
    have hgood : ∀ᵐ ω ∂law init, ∃ t, maskContact init {i, j} (u + t + 1) ω := by
      apply ae_iff.mpr
      simpa only [not_exists] using mask_no_future_contact_null init hc {i, j} hA u
    filter_upwards [hgood] with ω hω
    exact fun _ => hω
  · exact ae_of_all _ (fun _ h => False.elim (hij h))

theorem selected_clock_pair_above (init : Cfg L 256) (ω : Ω L 256)
    (v ell : ℕ) (hv : HomogeneousStart init ω v) (hell : 1 ≤ ell)
    (i j : Fin init.card) (hd : drawLabels init ω (v + 1) = some (i, j))
    (hi : (virtualLabels init ω v i).role = .clock)
    (hj : (virtualLabels init ω v j).role = .clock)
    (hsource : ell ≤ effMinute (virtualLabels init ω v i) ∨
      ell ≤ effMinute (virtualLabels init ω v j)) :
    i ∈ aboveSet (virtualLabels init ω (v + 1)) ell ∧
      j ∈ aboveSet (virtualLabels init ω (v + 1)) ell := by
  have henv := homogeneous_clockEnvironment init ω v hv v le_rfl
  have hout := clock_pair_outputs_above (virtualLabels init ω v i)
    (virtualLabels init ω v j) (by decide : 0 < (256 : ℕ))
    (henv.clock_regime i hi) (henv.clock_regime j hj) ell hell hsource
  have hij := (labelsAt_selected_transition init ω v i j hd).1
  simpa only [virtualLabels_succ, hd, auxStep, aboveSet, Finset.mem_filter,
    Finset.mem_univ, true_and, ruleUpdate, Function.update_of_ne hij,
    Function.update_self] using hout

/-- A recurring physical pair copies an observed positive level to each
Clock label. This is a pathwise statement on the scheduler event above. -/
theorem full_front_of_recurring_pairs (init : Cfg L 256) (ω : Ω L 256)
    (hrecur : ∀ u (i j : Fin init.card), i ≠ j →
      ∃ t, maskContact init {i, j} (u + t + 1) ω)
    (u ell : ℕ) (hu : HomogeneousStart init ω u) (hell : 1 ≤ ell)
    (hpositive : 0 < frontCount (virtualLabels init ω u) ell) :
    ∃ N, frontCount (virtualLabels init ω (u + N)) ell =
      clockCount (virtualLabels init ω u) := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpositive
  have haData : (virtualLabels init ω u a).role = .clock ∧
      ell ≤ effMinute (virtualLabels init ω u a) := by
    simpa only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and] using ha
  have hreach (i : Fin init.card)
      (hi : (virtualLabels init ω u i).role = .clock) :
      ∃ N, i ∈ aboveSet (virtualLabels init ω (u + N)) ell := by
    by_cases hia : i = a
    · subst i
      exact ⟨0, by simpa only [Nat.add_zero] using ha⟩
    · obtain ⟨r, hr⟩ := hrecur u a i (Ne.symm hia)
      obtain ⟨j, k, hd, hj, hk⟩ := hr
      have hjk := (labelsAt_selected_transition init ω (u + r) j k hd).1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj hk
      have hrole (z : Fin init.card) (hz : z = a ∨ z = i) :
          (virtualLabels init ω (u + r) z).role = .clock := by
        rw [roles_fixed_from_homogeneous init ω u hu (u + r) (by omega)]
        rcases hz with rfl | rfl
        · exact haData.1
        · exact hi
      have haNow := aboveSet_mono_from_homogeneous init ω u hu u (u + r)
        le_rfl (by omega) ell ha
      have haMinute : ell ≤ effMinute (virtualLabels init ω (u + r) a) := by
        have h : (virtualLabels init ω (u + r) a).role = .clock ∧
            ell ≤ effMinute (virtualLabels init ω (u + r) a) := by
          simpa only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and] using haNow
        exact h.2
      have hsource : ell ≤ effMinute (virtualLabels init ω (u + r) j) ∨
          ell ≤ effMinute (virtualLabels init ω (u + r) k) := by
        rcases hj with hja | hji
        · exact Or.inl (by simpa only [hja] using haMinute)
        · rcases hk with hka | hki
          · exact Or.inr (by simpa only [hka] using haMinute)
          · exact False.elim (hjk (hji.trans hki.symm))
      have hiPair : j = i ∨ k = i := by
        rcases hk with hka | hki
        · rcases hj with hja | hji
          · exact False.elim (hjk (hja.trans hka.symm))
          · exact Or.inl hji
        · exact Or.inr hki
      have hout := selected_clock_pair_above init ω (u + r) ell
        (homogeneousStart_of_time init ω u hu (u + r) (by omega))
        hell j k hd (hrole j hj) (hrole k hk) hsource
      refine ⟨r + 1, ?_⟩
      have hiNow : i ∈ aboveSet (virtualLabels init ω (u + r + 1)) ell := by
        rcases hiPair with hji | hki
        · simpa only [hji] using hout.1
        · simpa only [hki] using hout.2
      simpa only [Nat.add_assoc] using hiNow
  have hchoose : ∀ i : Fin init.card, ∃ N,
      (virtualLabels init ω u i).role = .clock →
        i ∈ aboveSet (virtualLabels init ω (u + N)) ell := by
    intro i
    by_cases hi : (virtualLabels init ω u i).role = .clock
    · obtain ⟨N, hN⟩ := hreach i hi
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => False.elim (hi h)⟩
  choose D hD using hchoose
  let N := Finset.univ.sup D
  have hDN (i : Fin init.card) : D i ≤ N := Finset.le_sup (Finset.mem_univ i)
  have hall (i : Fin init.card) (hi : (virtualLabels init ω u i).role = .clock) :
      i ∈ aboveSet (virtualLabels init ω (u + N)) ell :=
    aboveSet_mono_from_homogeneous init ω u hu (u + D i) (u + N)
      (by omega) (by have h := hDN i; omega) ell (hD i hi)
  have hsets : aboveSet (virtualLabels init ω (u + N)) ell =
      clockSet (virtualLabels init ω u) := by
    ext i
    constructor
    · intro hi
      have hData : (virtualLabels init ω (u + N) i).role = .clock ∧
          ell ≤ effMinute (virtualLabels init ω (u + N) i) := by
        simpa only [aboveSet, Finset.mem_filter, Finset.mem_univ, true_and] using hi
      have hr := hData.1
      simp only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [roles_fixed_from_homogeneous init ω u hu (u + N) (by omega)] at hr
      exact hr
    · intro hi
      apply hall i
      simpa only [clockSet, Finset.mem_filter, Finset.mem_univ, true_and] using hi
  exact ⟨N, congrArg Finset.card hsets⟩

theorem full_front_everywhere_ae (init : Cfg L 256) (hc : 2 ≤ init.card) :
    ∀ᵐ ω ∂law init, ∀ u ell,
      HomogeneousStart init ω u → 1 ≤ ell →
      0 < frontCount (virtualLabels init ω u) ell →
      ∃ N, frontCount (virtualLabels init ω (u + N)) ell =
        clockCount (virtualLabels init ω u) := by
  filter_upwards [fixed_pair_contacts_everywhere_ae init hc] with ω hω
  exact fun u ell hu hell hp => full_front_of_recurring_pairs init ω hω u ell hu hell hp

theorem all_cap_everywhere_ae (init : Cfg L 256) (hc : 2 ≤ init.card) :
    ∀ᵐ ω ∂law init, ∀ u C,
      HomogeneousStart init ω u →
      clockCount (virtualLabels init ω u) = C →
      11 ≤ C → 6 * init.card ≤ 25 * C →
      ∃ N, frontCount (virtualLabels init ω (u + N)) (256 * (L + 1)) = C := by
  filter_upwards [finite_bulk_levels_ae init hc, full_front_everywhere_ae init hc]
    with ω hbulk hfull
  intro u C hu hcount hC hdensity
  obtain ⟨N, hN⟩ := hbulk u C hu hcount hC hdensity (256 * (L + 1)) le_rfl
  have hpos : 0 < frontCount (virtualLabels init ω (u + N)) (256 * (L + 1)) := by
    have hb := two_le_bulkThreshold C hC
    omega
  obtain ⟨R, hR⟩ := hfull (u + N) (256 * (L + 1))
    (homogeneousStart_of_time init ω u hu (u + N) (by omega)) (by omega) hpos
  have hcount' : clockCount (virtualLabels init ω (u + N)) = C := by
    calc
      clockCount (virtualLabels init ω (u + N)) =
          clockCount (virtualLabels init ω u) :=
        congrArg Finset.card (clockSet_fixed_from_homogeneous init ω u hu (u + N) (by omega))
      _ = C := hcount
  refine ⟨N + R, ?_⟩
  simpa only [Nat.add_assoc, hcount'] using hR

variable {n : ℕ}

/-- Existence of the exact cap_first witness on every successful seed
history, outside a single original-law null set. No deadline is asserted. -/
theorem seed_all_cap_first_null (init : InputCfg n) (hc : 2 ≤ init.card)
    (hn : 42 ≤ n) (s : ℕ) :
    law init {ω | ω ∈ seedPrefix init s ∧
      ∃ T, StageEventSpec.AsyncEntry init ω s T ∧
        ¬ ∃ cap, StageEventSpec.firstAfter (fun v =>
          frontCountL init (virtualLabels init ω s) (virtualLabels init ω v)
            (StageEventSpec.clockTop n) = StageEventSpec.clockCount (virtualCfg init ω s))
          s cap} = 0 := by
  have havoid : ∀ᵐ ω ∂law init, ω ∉ {ω | ω ∈ seedPrefix init s ∧
      ∃ T, StageEventSpec.AsyncEntry init ω s T ∧
        ¬ ∃ cap, StageEventSpec.firstAfter (fun v =>
          frontCountL init (virtualLabels init ω s) (virtualLabels init ω v)
            (StageEventSpec.clockTop n) = StageEventSpec.clockCount (virtualCfg init ω s))
          s cap} := by
    filter_upwards [all_cap_everywhere_ae init hc] with ω hfull
    rintro ⟨hseed, T, hentry, hbad⟩
    have henv := virtualLabels_clockEnvironment_of_asyncEntry init ω s T hentry T hentry.order
    have hhom : HomogeneousStart init ω T := by
      refine ⟨?_, henv.carrier⟩
      intro i
      rw [virtualLabels_eq_labelsAt_through_asyncEntry init ω s T hentry T le_rfl]
      exact hentry.advanced_profile.all_three _ (labelsAt_mem_trace init ω T i)
    have hcount :
        clockCount (virtualLabels init ω T) =
          StageEventSpec.clockCount (virtualCfg init ω s) := by
      rw [virtual_clockCount_eq_seed_of_current_phase_cap init ω s T hseed hentry.order
        (fun i => (henv.phase_range i).2), clockCount_labelsAt_eq_trace,
        virtualCfg_eq_trace_at_seedPrefix init ω s hseed]
      rfl
    have hdensity := (seed_role_density init ω s hseed).2
    have hC : 11 ≤ StageEventSpec.clockCount (virtualCfg init ω s) := by omega
    have hdensity' : 6 * init.card ≤ 25 * StageEventSpec.clockCount (virtualCfg init ω s) := by
      rw [seedPrefix_card_eq init ω s hseed]
      exact hdensity
    obtain ⟨N, hN⟩ := hfull T _ hhom hcount hC hdensity'
    have hsT : s ≤ T := hentry.order
    have hex : ∃ v, s ≤ v ∧
        frontCountL init (virtualLabels init ω s) (virtualLabels init ω v)
          (StageEventSpec.clockTop n) = StageEventSpec.clockCount (virtualCfg init ω s) := by
      refine ⟨T + N, by omega, ?_⟩
      rw [core_front_eq_current_of_asyncEntry init ω s T (T + N)
        (StageEventSpec.clockTop n) hseed hentry (by omega)]
      exact hN
    apply hbad
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
    intro v hsv hv hhit
    have hle : Nat.find hex ≤ v := Nat.find_min' hex ⟨hsv, hhit⟩
    omega
  simpa only [not_not] using ae_iff.mp havoid


/-- The genuine cap_first existence row has zero extra seed-fibre error. -/
theorem seed_cap_first_row_tail (init : InputCfg n) (hc : 2 ≤ init.card)
    (hn : 42 ≤ n) (s : ℕ) :
    law init {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧
      StageEventSpec.SeedProfile n init (trace init ω s) ∧
      ∃ T, StageEventSpec.AsyncEntry init ω s T ∧
        ¬ ∃ cap, StageEventSpec.firstAfter (fun v =>
          frontCountL init (virtualLabels init ω s) (virtualLabels init ω v)
            (StageEventSpec.clockTop n) = StageEventSpec.clockCount (virtualCfg init ω s))
          s cap} ≤
      (0 : ℝ≥0∞) * law init {ω | seedTime init 3 ω = (s : WithTop ℕ)} := by
  rw [zero_mul]
  apply le_trans (measure_mono ?_) (le_of_eq (seed_all_cap_first_null init hc hn s))
  rintro ω ⟨hs, hp, hbad⟩
  exact ⟨⟨hs, hp⟩, hbad⟩

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockFiniteAllCap

end
