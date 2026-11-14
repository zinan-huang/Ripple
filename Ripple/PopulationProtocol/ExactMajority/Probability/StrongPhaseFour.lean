-- Ripple/PopulationProtocol/ExactMajority/Probability/StrongPhaseFour.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.UniformRecovery
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoThresholds
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneDrainStopping

/-!
The Phase-4 work rung. A reachable fixed configuration is already a correct
stable endpoint. Otherwise a big-bias physical label is a witness, and either
orientation of its next contact creates a Phase-5 seed. The two tagged rows
contain exactly 2(n-1) distinct ordered pairs. The prefix bound retains the
original recorded-prefix mass and requires no future event in that prefix.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators

namespace Ripple.PopulationProtocol.ExactMajority.StrongPhaseFour

open TimeTheorem PairLog PairLogAuxiliary UniformRecovery
  PhaseOneDrainStopping PhaseTwoThresholds

variable {L K : ℕ}

theorem phase_four_pair_fixed_of_no_big (a b : AgentState L K)
    (ha : a.phase.val = 4) (hb : b.phase.val = 4)
    (hna : ¬ phase4HasBigBias a) (hnb : ¬ phase4HasBigBias b) :
    Transition L K a b = (a, b) := by
  have hga : phaseFourGuard a = false := (phaseFourGuard_eq_false a).2 hna
  have hgb : phaseFourGuard b = false := (phaseFourGuard_eq_false b).2 hnb
  have hlocal : Phase4Transition L K a b = (a, b) := by
    change (if phaseFourGuard a || phaseFourGuard b then
      (advancePhaseWithInit L K a, advancePhaseWithInit L K b) else (a, b)) = (a, b)
    rw [hga, hgb]
    rfl
  have hpa : a.phase = ⟨4, by decide⟩ := Fin.ext ha
  have hpb : b.phase = ⟨4, by decide⟩ := Fin.ext hb
  have hepi := ConditionalPhaseProgress.epidemic_inert_same_phase
    (L := L) (K := K) ⟨4, by decide⟩ (by decide) a b hpa hpb
  unfold Transition
  rw [hepi]
  simp only [hpa]
  rw [hlocal]
  simp [ha, hb]

theorem exists_big_bias_of_unfinished (init c : Cfg L K)
    (hinit : validInitial init) (hlow : 11 ≤ init.card)
    (hsize : init.card ≤ 2 ^ L)
    (hreach : ReachableFrom L K init c)
    (hpure : PurePhase 4 c) (hnot : c ∉ StableDone L K init) :
    ∃ a ∈ c, phase4HasBigBias a := by
  classical
  by_contra hno
  have hnobig : ∀ a ∈ c, ¬ phase4HasBigBias a := by
    intro a ha hb
    exact hno ⟨a, ha, hb⟩
  apply hnot
  apply reachable_pairwiseFixed_mem_stableDone init c hinit hlow hsize hreach
  intro a b
  by_cases happ : Protocol.Applicable c a b
  · have ha : a ∈ c := Multiset.mem_of_le happ (by simp)
    have hb : b ∈ c := Multiset.mem_of_le happ (by simp)
    have heq := phase_four_pair_fixed_of_no_big a b
      (hpure a ha) (hpure b hb) (hnobig a ha) (hnobig b hb)
    have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c a b =
        c - {a, b} + {(Transition L K a b).1, (Transition L K a b).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    rw [hstep, heq]
    exact Multiset.sub_add_cancel happ
  · exact Protocol.stepOrSelf_eq_self_of_not_applicable happ

def taggedPairs (m : ℕ) (i : Fin m) : Finset (Fin m × Fin m) :=
  ({i} ×ˢ (Finset.univ.erase i)) ∪ ((Finset.univ.erase i) ×ˢ {i})

theorem taggedPairs_card (m : ℕ) (i : Fin m) :
    (taggedPairs m i).card = 2 * (m - 1) := by
  classical
  have hdisj : Disjoint ({i} ×ˢ (Finset.univ.erase i))
      ((Finset.univ.erase i) ×ˢ {i}) := by
    apply Finset.disjoint_left.mpr
    rintro ⟨a, b⟩ hab hba
    have hai : a = i := Finset.mem_singleton.mp (Finset.mem_product.mp hab).1
    have hane : a ≠ i := (Finset.mem_erase.mp (Finset.mem_product.mp hba).1).1
    exact hane hai
  rw [taggedPairs, Finset.card_union_of_disjoint hdisj,
    Finset.card_product, Finset.card_product, Finset.card_singleton,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  omega

theorem mem_taggedPairs {m : ℕ} {i a b : Fin m} :
    (a, b) ∈ taggedPairs m i ↔ a ≠ b ∧ (a = i ∨ b = i) := by
  classical
  simp only [taggedPairs, Finset.mem_union, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro (⟨hai, hbi⟩ | ⟨hai, hbi⟩)
    · subst a
      exact ⟨hbi.symm, Or.inl rfl⟩
    · subst b
      exact ⟨hai, Or.inr rfl⟩
  · rintro ⟨hab, hai | hbi⟩
    · subst a
      exact Or.inl ⟨rfl, hab.symm⟩
    · subst b
      exact Or.inr ⟨hab, rfl⟩

theorem taggedPairs_force_seed (m : ℕ) (f : Fin m → AgentState L K)
    (hf : ∀ i, (f i).phase.val = 4) (i : Fin m)
    (hi : phase4HasBigBias (f i)) (init : Cfg L K) :
    taggedPairs m i ⊆ goodPairs
      (fun g a b => labelCfg (updateLabels g a b) ∈ phaseWorkTarget 4 init) f := by
  classical
  rintro ⟨a, b⟩ hab
  obtain ⟨hne, htag⟩ := mem_taggedPairs.mp hab
  have hbig : phase4HasBigBias (f a) ∨ phase4HasBigBias (f b) := by
    rcases htag with rfl | rfl
    · exact Or.inl hi
    · exact Or.inr hi
  have hadv := Transition_phase4_advances_of_big_bias (f a) (f b) (hf a) (hf b) hbig
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, Or.inr ?_⟩
  refine ⟨(Transition L K (f a) (f b)).1, ?_, by omega⟩
  rw [updateLabels_config f a b hne]
  simp only [Multiset.mem_add, Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton]
  exact Or.inr (Or.inl rfl)

theorem tagged_rate_eq (n : ℕ) (hn : 2 ≤ n) :
    (((2 * (n - 1) : ℕ) : ℝ≥0∞) *
      (((n * (n - 1) : ℕ) : ℝ≥0∞))⁻¹) = 2 / (n : ℝ≥0∞) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hmpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hden : 0 < ((n * (n - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    exact mul_pos hnpos hmpos
  rw [← div_eq_mul_inv]
  calc
    (((2 * (n - 1) : ℕ) : ℝ≥0∞) /
        (((n * (n - 1) : ℕ) : ℝ≥0∞))) =
        ENNReal.ofReal (((2 * (n - 1) : ℕ) : ℝ) /
          (((n * (n - 1) : ℕ) : ℝ))) := by
      rw [ENNReal.ofReal_div_of_pos hden, ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (2 / (n : ℝ)) := by
      congr 1
      simp only [Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      field_simp [hnpos.ne', hmpos.ne']
      <;> ring
    _ = 2 / (n : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos hnpos, ENNReal.ofReal_natCast]
      norm_num

theorem phase_four_seed_probability (n : ℕ) (hn : 2 ≤ n)
    (init c : Cfg L K) (hinit : validInitial init)
    (hlow : 11 ≤ init.card) (hsize : init.card ≤ 2 ^ L)
    (hreach : ReachableFrom L K init c) (hcard : c.card = n)
    (hpure : PurePhase 4 c) (hnot : c ∉ StableDone L K init) :
    2 / (n : ℝ≥0∞) ≤
      (NonuniformMajority L K).transitionKernel c (phaseWorkTarget 4 init) := by
  classical
  obtain ⟨a, ha, hbig⟩ :=
    exists_big_bias_of_unfinished init c hinit hlow hsize hreach hpure hnot
  let f := initialLabels c
  have hcfg : labelCfg f = c := initialLabels_config c
  have ha' : a ∈ (Finset.univ : Finset (Fin c.card)).val.map f := by
    change a ∈ labelCfg f
    rw [hcfg]
    exact ha
  obtain ⟨i, -, hfi⟩ := Multiset.mem_map.mp ha'
  have hi : phase4HasBigBias (f i) := by simpa only [hfi] using hbig
  have hf : ∀ j, (f j).phase.val = 4 := by
    intro j
    apply hpure (f j)
    rw [← hcfg]
    exact Multiset.mem_map.mpr ⟨j, Finset.mem_univ_val j, rfl⟩
  have hcount := Finset.card_le_card (taggedPairs_force_seed c.card f hf i hi init)
  rw [taggedPairs_card] at hcount
  have hsizec : 2 ≤ c.card := by omega
  calc
    2 / (n : ℝ≥0∞) =
        (((2 * (c.card - 1) : ℕ) : ℝ≥0∞) *
          (((c.card * (c.card - 1) : ℕ) : ℝ≥0∞))⁻¹) := by
      rw [hcard, tagged_rate_eq n hn]
    _ ≤ ((goodPairs
          (fun g a b => labelCfg (updateLabels g a b) ∈ phaseWorkTarget 4 init) f).card :
          ℝ≥0∞) * (((c.card * (c.card - 1) : ℕ) : ℝ≥0∞))⁻¹ :=
      mul_le_mul_right' (by exact_mod_cast hcount) _
    _ = (NonuniformMajority L K).transitionKernel (labelCfg f)
          (phaseWorkTarget 4 init) :=
      (transitionKernel_labelCfg_eq_goodPairs f hsizec _).symm
    _ = _ := by rw [hcfg]

open Classical in
def unfinishedIndicator (init c : Cfg L K) : ℕ :=
  if c ∈ phaseWorkTarget 4 init then 0 else 1

theorem unfinishedIndicator_le_one (init c : Cfg L K) :
    unfinishedIndicator init c ≤ 1 := by
  classical
  unfold unfinishedIndicator
  split_ifs <;> omega

theorem unfinishedIndicator_drift (n : ℕ) (hn : 2 ≤ n)
    (init : Cfg L K) (hinit : validInitial init)
    (hlow : 11 ≤ init.card) (hsize : init.card ≤ 2 ^ L)
    (c : Cfg L K) (hc : phaseWorkInv 4 n init c) :
    (∫⁻ c', (unfinishedIndicator init c' : ℝ≥0∞)
      ∂(NonuniformMajority L K).transitionKernel c) ≤
      (1 - 2 / (n : ℝ≥0∞)) * unfinishedIndicator init c := by
  classical
  have hfun : (fun c' : Cfg L K => (unfinishedIndicator init c' : ℝ≥0∞)) =
      (phaseWorkTarget 4 init)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext c'
    by_cases h : c' ∈ phaseWorkTarget 4 init
    · rw [unfinishedIndicator, if_pos h,
        Set.indicator_of_notMem (by simpa only [Set.mem_compl_iff, not_not] using h)]
      simp
    · rw [unfinishedIndicator, if_neg h, Set.indicator_of_mem h]
      simp
  rw [hfun, lintegral_indicator_const (Set.to_countable _).measurableSet, one_mul]
  by_cases hdone : c ∈ phaseWorkTarget 4 init
  · rw [phaseWorkTarget_kernel_absorbing 4 init c hdone]
    exact zero_le
  · have hpure := purePhase_of_ge_not_phaseWorkTarget 4 n init c hc.2 hdone
    have hnot : c ∉ StableDone L K init := fun h => hdone (Or.inl h)
    have hp := phase_four_seed_probability n hn init c hinit hlow hsize
      hc.1 hc.2.1 hpure hnot
    rw [unfinishedIndicator, if_neg hdone, Nat.cast_one, mul_one,
      prob_compl_eq_one_sub (Set.to_countable _).measurableSet]
    exact tsub_le_tsub_left hp 1

theorem phase_work_inv_reachable (p n : ℕ) (init c d : Cfg L K)
    (hc : phaseWorkInv p n init c)
    (hcd : (NonuniformMajority L K).Reachable c d) :
    phaseWorkInv p n init d := by
  refine ⟨Relation.ReflTransGen.trans hc.1 hcd, ?_, ?_⟩
  · exact (Protocol.reachable_card_eq hcd).trans hc.2.1
  · exact phase_lower_reachable p c d hcd hc.2.2

theorem phase_four_prefix_tail (init : Cfg L K)
    (hinit : validInitial init) (hlow : 11 ≤ init.card)
    (hsize : init.card ≤ 2 ^ L)
    (n : ℕ) (hn : 2 ≤ n) (s N : ℕ)
    (A : Set ((k : Finset.Iic s) → Draw L K))
    (hA : ∀ p ∈ A, phaseWorkInv 4 n init (prefixCfg init s p)) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        trace init ω (s + N) ∉ phaseWorkTarget 4 init} ≤
      (1 - 2 / (n : ℝ≥0∞)) ^ N *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  classical
  have ht := TraceDrain.potential_drift_tail_from init (unfinishedIndicator init)
    (phaseWorkInv 4 n init) (2 / (n : ℝ≥0∞))
    (fun c hc => unfinishedIndicator_drift n hn init hinit hlow hsize c hc)
    s N A 1 (fun p _ => unfinishedIndicator_le_one init _)
  simp only [Nat.cast_one, mul_one] at ht
  apply (measure_mono ?_).trans ht
  rintro ω ⟨ha, hb⟩
  refine ⟨ha, ?_, ?_⟩
  · intro u hsu _
    exact phase_work_inv_reachable 4 n init (trace init ω s) (trace init ω u)
      (hA _ ha) (trace_reachable init ω hsu)
  · simp only [unfinishedIndicator, if_neg hb, le_refl]

theorem phase_four_scalar (n : ℕ) (hn : 2 ≤ n) :
    (1 - 2 / (n : ℝ≥0∞)) ^ logWindow n 3 ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 6) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hr : 0 ≤ 2 / (n : ℝ) := by positivity
  have hrone : 2 / (n : ℝ) ≤ 1 := (div_le_one hnpos).2 hnR
  have hbase : 0 ≤ 1 - 2 / (n : ℝ) := by linarith
  have hcast :
      1 - 2 / (n : ℝ≥0∞) = ENNReal.ofReal (1 - 2 / (n : ℝ)) := by
    rw [ENNReal.ofReal_sub _ hr, ENNReal.ofReal_one,
      ENNReal.ofReal_div_of_pos hnpos, ENNReal.ofReal_natCast]
    norm_num
  rw [hcast, ← ENNReal.ofReal_pow hbase]
  apply ENNReal.ofReal_le_ofReal
  have hceil : (3 : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤
      (logWindow n 3 : ℝ) := Nat.le_ceil _
  have hprod := mul_le_mul_of_nonneg_left hceil hr
  have hexp : 6 * Real.log (n : ℝ) ≤
      (2 / (n : ℝ)) * (logWindow n 3 : ℝ) := by
    have heq : (2 / (n : ℝ)) *
        ((3 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) =
        6 * Real.log (n : ℝ) := by
      field_simp [hnpos.ne']
      <;> ring
    rwa [heq] at hprod
  calc
    (1 - 2 / (n : ℝ)) ^ logWindow n 3 ≤
        Real.exp (-(2 / (n : ℝ))) ^ logWindow n 3 :=
      pow_le_pow_left₀ hbase (by linarith [Real.add_one_le_exp (-(2 / (n : ℝ)))]) _
    _ = Real.exp (-(2 / (n : ℝ)) * (logWindow n 3 : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (-(6 : ℝ) * Real.log (n : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith only [hexp])
    _ = 1 / (n : ℝ) ^ 6 := by
      rw [show -(6 : ℝ) * Real.log (n : ℝ) =
        -((6 : ℝ) * Real.log (n : ℝ)) by ring, Real.exp_neg]
      have heq : Real.exp ((6 : ℝ) * Real.log (n : ℝ)) = (n : ℝ) ^ 6 := by
        simpa only [Real.exp_log hnpos] using (Real.exp_nat_mul (Real.log (n : ℝ)) 6)
      rw [heq, one_div]

theorem phase_four_prefix_calibrated (init : Cfg L K)
    (hinit : validInitial init) (hlow : 11 ≤ init.card)
    (hsize : init.card ≤ 2 ^ L)
    (n : ℕ) (hn : 2 ≤ n) (s : ℕ)
    (A : Set ((k : Finset.Iic s) → Draw L K))
    (hA : ∀ p ∈ A, phaseWorkInv 4 n init (prefixCfg init s p)) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        trace init ω (s + logWindow n 3) ∉ phaseWorkTarget 4 init} ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 6) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} :=
  (phase_four_prefix_tail init hinit hlow hsize n hn s (logWindow n 3) A hA).trans
    (mul_le_mul_right' (phase_four_scalar n hn) _)

end Ripple.PopulationProtocol.ExactMajority.StrongPhaseFour

end
