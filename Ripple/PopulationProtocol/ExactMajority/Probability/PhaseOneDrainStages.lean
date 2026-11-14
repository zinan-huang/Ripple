import Ripple.PopulationProtocol.ExactMajority.Probability.TraceDrain
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseOneDrain

/-!
# Stage tails of the Phase-1 drain for the actual trace

Stage estimates of the small-gap Phase-1 drain (Doty et al., exact majority), proved for the actual trace up to a pair-log stopping
time: the trace reaches the stage target or leaves the stage window. Leaving the
window is charged separately (clock survival, (27)).

* `preliminary_stage_tail`, `preliminary_stage_tail_calibrated`: (21), the far
  potential falls to at most `n / 100` within `16000 n` steps except with
  probability `e^{-n/2}`.
* `far_stage_tail`, `far_stage_tail_calibrated`: (23), in the far window the far
  potential is gone by `⌈27/2 n ln n⌉` except with probability `n^{-4183/2000}/100`.
* `cancellation_kernel_floor`, `mass_drop_probability`: (24) in kernel form.
* `mass_stage_tail`, `mass_stage_tail_calibrated`: (25), the unit mass falls to
  `3 M / 100` within `800000 n` steps except with probability `e^{-n/4}`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseOneDrainStages

open TimeTheorem TraceDrain

variable {L K : ℕ}

/-- The window of the preliminary stage (21): population `n` all in Phase 1, Main
count at least `12 n / 25`, and centred bias sum at most `d` with `40 d ≤ M`. -/
def PreliminaryWindow (n d : ℕ) (c : Cfg L K) : Prop :=
  PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c ∧
    12 * n ≤ 25 * RoleSplitConcentration.mainCount c ∧
    40 * d ≤ RoleSplitConcentration.mainCount c ∧
    |AveragingRate.centredBiasSum c| ≤ (d : ℤ)

/-- The target of the preliminary stage: far potential at most `n / 100`. -/
def PreliminaryTarget (n : ℕ) (c : Cfg L K) : Prop :=
  100 * Phase1FarPhi.farPhiN c ≤ n

theorem farPhiN_applyDraw_le {n : ℕ} (c : Cfg L K)
    (hwin : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c) (d : Draw L K) :
    Phase1FarPhi.farPhiN (applyDraw c d) ≤ Phase1FarPhi.farPhiN c := by
  cases d with
  | none => exact le_rfl
  | some p => exact Phase1FarPhi.farPhiN_stepOrSelf_le_of_phase1Win n c hwin _ _

/-- (21), general horizon: the trace leaves the preliminary window or reaches the
target within `N` steps except with probability
`exp ((farPhiN init + 1) log 2 - N / 8000)`. -/
theorem preliminary_stage_tail (init : Cfg L K) {n d : ℕ} (hn : 2 ≤ n) (N : ℕ) :
    (law init).real
        {ω | (N : WithTop ℕ) < exitTime init
          (fun c => ¬ PreliminaryWindow n d c ∨ PreliminaryTarget n c) ω} ≤
      Real.exp (((Phase1FarPhi.farPhiN init : ℝ) + 1) * Real.log 2 -
        (N : ℝ) * (1 / 4000 : ℝ) / 2) := by
  have hr : ENNReal.ofReal (1 / 4000 : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hrt : (ENNReal.ofReal (1 / 4000 : ℝ)).toReal = 1 / 4000 :=
    ENNReal.toReal_ofReal (by norm_num)
  have h := potential_drain_tail init Phase1FarPhi.farPhiN
    (PreliminaryWindow n d) (PreliminaryTarget n)
    (fun c hc dr => farPhiN_applyDraw_le c hc.1 dr)
    (ENNReal.ofReal (1 / 4000 : ℝ)) hr (by rw [hrt]; norm_num)
    (fun c hc htarget => by
      obtain ⟨hwin, hmain, hsmall, hgap⟩ := hc
      have hphi : n < 100 * Phase1FarPhi.farPhiN c := by
        unfold PreliminaryTarget at htarget
        omega
      exact PhaseOneDrain.preliminary_drop_probability hn c hwin hmain hsmall hgap hphi)
    N
  rwa [hrt] at h

/-- (21), calibrated: from a start with far potential at most `2 n`, within `16000 n`
steps the trace reaches `100 Φ ≤ n` or leaves the window, except with probability
`e^{-n/2}`, for `n ≥ 7`. -/
theorem preliminary_stage_tail_calibrated (init : Cfg L K) {n d : ℕ} (hn : 7 ≤ n)
    (hphi : Phase1FarPhi.farPhiN init ≤ 2 * n) :
    (law init).real
        {ω | ((16000 * n : ℕ) : WithTop ℕ) < exitTime init
          (fun c => ¬ PreliminaryWindow n d c ∨ PreliminaryTarget n c) ω} ≤
      Real.exp (-(n : ℝ) / 2) := by
  refine (preliminary_stage_tail init (d := d) (by omega) (16000 * n)).trans
    (Real.exp_le_exp.mpr ?_)
  have hphiR : (Phase1FarPhi.farPhiN init : ℝ) ≤ 2 * n := by exact_mod_cast hphi
  have hnR : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_two_lt_d9
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  push_cast
  nlinarith

/-- The window of the far-extinction stage (23): the preliminary window with the far
potential already at most `n / 100`. -/
def FarWindow (n d : ℕ) (c : Cfg L K) : Prop :=
  PreliminaryWindow n d c ∧ PreliminaryTarget n c

/-- (23), general horizon: while the trace stays in the far window, the far potential
contracts by the refined partner rate; it is still positive at time `N` (with the
trace in the window throughout) with probability at most
`(1 - partnerRate) ^ N farPhiN init`. -/
theorem far_stage_tail (init : Cfg L K) {n d : ℕ} (hn : 2 ≤ n) (N : ℕ) :
    law init {ω | (N : WithTop ℕ) < exitTime init (fun c => ¬ FarWindow n d c) ω ∧
        1 ≤ Phase1FarPhi.farPhiN (trace init ω N)} ≤
      (1 - PhaseOneDrain.partnerRate n ((229 * n + 999) / 1000)) ^ N *
        Phase1FarPhi.farPhiN init :=
  potential_drift_tail init Phase1FarPhi.farPhiN (FarWindow n d) _
    (fun c hc => PhaseOneDrain.refined_farPhi_drift hn d c hc.1.1 hc.1.2.1 hc.1.2.2.1
      hc.1.2.2.2 hc.2) N

/-- (23), calibrated: from `100 farPhiN init ≤ n`, at `T_far = ⌈27/2 n ln n⌉` the far
potential is positive with the trace in the far window throughout with probability
at most `n ^ (-4183/2000) / 100`. -/
theorem far_stage_tail_calibrated (init : Cfg L K) {n d : ℕ} (hn : 2 ≤ n)
    (hphi : 100 * Phase1FarPhi.farPhiN init ≤ n) :
    law init {ω | ((Nat.ceil ((27 / 2 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) : ℕ) :
          WithTop ℕ) < exitTime init (fun c => ¬ FarWindow n d c) ω ∧
        1 ≤ Phase1FarPhi.farPhiN (trace init ω
          (Nat.ceil ((27 / 2 : ℝ) * (n : ℝ) * Real.log (n : ℝ))))} ≤
      ENNReal.ofReal ((1 / 100 : ℝ) * Real.rpow (n : ℝ) (-(4183 / 2000 : ℝ))) := by
  set T : ℕ := Nat.ceil ((27 / 2 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) with hT
  refine (far_stage_tail init (d := d) hn T).trans ?_
  set x : ℝ := (229 : ℝ) / (1000 * (n : ℝ)) with hx
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one (by positivity)]
    linarith
  have hρ : ENNReal.ofReal x ≤ PhaseOneDrain.partnerRate n ((229 * n + 999) / 1000) :=
    PhaseOneDrain.refined_partnerRate_lower hn
  have h1 : 1 - PhaseOneDrain.partnerRate n ((229 * n + 999) / 1000) ≤
      ENNReal.ofReal (1 - x) := by
    calc 1 - PhaseOneDrain.partnerRate n ((229 * n + 999) / 1000)
        ≤ 1 - ENNReal.ofReal x := tsub_le_tsub_left hρ 1
      _ = ENNReal.ofReal (1 - x) := by rw [ENNReal.ofReal_sub _ hx0, ENNReal.ofReal_one]
  have h2 : (1 - PhaseOneDrain.partnerRate n ((229 * n + 999) / 1000)) ^ T ≤
      ENNReal.ofReal ((1 - x) ^ T) := by
    rw [ENNReal.ofReal_pow (by linarith)]
    gcongr
  have hψ : (Phase1FarPhi.farPhiN init : ℝ) ≤ (n : ℝ) / 100 := by
    have : ((100 * Phase1FarPhi.farPhiN init : ℕ) : ℝ) ≤ n := by exact_mod_cast hphi
    push_cast at this
    linarith
  have hreal : (1 - x) ^ T * (Phase1FarPhi.farPhiN init : ℝ) ≤
      (1 / 100 : ℝ) * Real.rpow (n : ℝ) (-(4183 / 2000 : ℝ)) := by
    have he : (1 - x) ^ T ≤ Real.exp (-x * (T : ℝ)) := by
      calc (1 - x) ^ T ≤ (Real.exp (-x)) ^ T :=
            pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-x)]) T
        _ = Real.exp (-x * (T : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
    have hcal := PhaseOneDrain.far_decay_calibration hnpos
    calc (1 - x) ^ T * (Phase1FarPhi.farPhiN init : ℝ)
        ≤ Real.exp (-x * (T : ℝ)) * ((n : ℝ) / 100) :=
          mul_le_mul he hψ (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = ((n : ℝ) / 100) * Real.exp (-((229 : ℝ) / (1000 * (n : ℝ))) *
            (Nat.ceil ((27 / 2 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) : ℝ)) := by
          rw [hx, hT]; ring
      _ ≤ _ := hcal
  calc (1 - PhaseOneDrain.partnerRate n ((229 * n + 999) / 1000)) ^ T *
        (Phase1FarPhi.farPhiN init : ℝ≥0∞)
      ≤ ENNReal.ofReal ((1 - x) ^ T) * ENNReal.ofReal (Phase1FarPhi.farPhiN init : ℝ) := by
        rw [ENNReal.ofReal_natCast]
        gcongr
    _ = ENNReal.ofReal ((1 - x) ^ T * (Phase1FarPhi.farPhiN init : ℝ)) :=
        (ENNReal.ofReal_mul (pow_nonneg (by linarith) T)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-! ## (24)-(25): cancellation of the unit Main biases -/

/-- Main agents with integer bias `+1` (small bias `4`). -/
def plusUnitSet (L K : ℕ) : Finset (AgentState L K) :=
  Finset.univ.filter fun a => a.role = Role.main ∧ a.smallBias.val = 4

/-- Main agents with integer bias `-1` (small bias `2`). -/
def minusUnitSet (L K : ℕ) : Finset (AgentState L K) :=
  Finset.univ.filter fun a => a.role = Role.main ∧ a.smallBias.val = 2

theorem plus_minus_ne (a : AgentState L K) (ha : a ∈ plusUnitSet L K)
    (b : AgentState L K) (hb : b ∈ minusUnitSet L K) : a ≠ b := by
  simp only [plusUnitSet, minusUnitSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  intro h
  rw [h] at ha
  omega

theorem minus_plus_ne (a : AgentState L K) (ha : a ∈ minusUnitSet L K)
    (b : AgentState L K) (hb : b ∈ plusUnitSet L K) : a ≠ b :=
  fun h => plus_minus_ne b hb a ha h.symm

/-- Ordered opposite-unit pairs. -/
def cancelRect (L K : ℕ) : Finset (AgentState L K × AgentState L K) :=
  (plusUnitSet L K ×ˢ minusUnitSet L K) ∪ (minusUnitSet L K ×ˢ plusUnitSet L K)

theorem avgFin7_mass_pair_le (x y : Fin 7) :
    (((avgFin7 x y).1.val : ℤ) - 3).natAbs + (((avgFin7 x y).2.val : ℤ) - 3).natAbs ≤
      ((x.val : ℤ) - 3).natAbs + ((y.val : ℤ) - 3).natAbs := by
  revert x y
  decide +kernel

theorem mass_pair (x y : AgentState L K) :
    ((({x, y} : Multiset (AgentState L K)).map
        (fun a => (AveragingRate.biasZ a).natAbs)).sum) =
      (AveragingRate.biasZ x).natAbs + (AveragingRate.biasZ y).natAbs := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  simp [Multiset.map_cons, Multiset.sum_cons]

/-- Phase-1 interactions never increase the integer-bias mass of a pair. -/
theorem Transition_mass_pair_le (s t : AgentState L K)
    (hs1 : s.phase.val = 1) (ht1 : t.phase.val = 1) :
    (AveragingRate.biasZ (Transition L K s t).1).natAbs +
        (AveragingRate.biasZ (Transition L K s t).2).natAbs ≤
      (AveragingRate.biasZ s).natAbs + (AveragingRate.biasZ t).natAbs := by
  by_cases hboth : s.role = Role.main ∧ t.role = Role.main
  · rw [Phase1Convergence.Transition_eq_avg_of_phase1_main s t hs1 ht1 hboth.1 hboth.2]
    simp only [AveragingRate.biasZ, hboth.1, hboth.2, if_true]
    exact avgFin7_mass_pair_le s.smallBias t.smallBias
  · obtain ⟨hr1, hr2⟩ := PhaseOnlyWindows.Transition_role_phase1 (L := L) (K := K) s t hs1 ht1
    obtain ⟨hfix1, hfix2⟩ :=
      Phase1GapFloorEntryClosure.main_endpoints_fixed_of_not_both_main s t hs1 ht1 hboth
    have h1 : AveragingRate.biasZ (Transition L K s t).1 = AveragingRate.biasZ s := by
      by_cases hsM : s.role = Role.main
      · rw [hfix1 hsM]
      · simp only [AveragingRate.biasZ, hr1, hsM, if_false]
    have h2 : AveragingRate.biasZ (Transition L K s t).2 = AveragingRate.biasZ t := by
      by_cases htM : t.role = Role.main
      · rw [hfix2 htM]
      · simp only [AveragingRate.biasZ, hr2, htM, if_false]
    rw [h1, h2]

/-- Config-level conservation identity for one applicable interaction. -/
theorem mass_stepOrSelf_add (c : Cfg L K) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t) :
    PhaseOneDrain.PhaseOneMass (Protocol.stepOrSelf (NonuniformMajority L K) c s t) +
        ((AveragingRate.biasZ s).natAbs + (AveragingRate.biasZ t).natAbs) =
      PhaseOneDrain.PhaseOneMass c +
        ((AveragingRate.biasZ (Transition L K s t).1).natAbs +
          (AveragingRate.biasZ (Transition L K s t).2).natAbs) := by
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  have hsplit : c = (c - {s, t}) + ({s, t} : Multiset (AgentState L K)) := by
    rw [Multiset.sub_add_cancel hsub]
  unfold PhaseOneDrain.PhaseOneMass
  rw [hc', Multiset.map_add, Multiset.sum_add, mass_pair]
  conv_rhs => rw [hsplit]
  rw [Multiset.map_add, Multiset.sum_add, mass_pair]
  ring

theorem mass_stepOrSelf_le {n : ℕ} (c : Cfg L K)
    (hwin : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c) (s t : AgentState L K) :
    PhaseOneDrain.PhaseOneMass (Protocol.stepOrSelf (NonuniformMajority L K) c s t) ≤
      PhaseOneDrain.PhaseOneMass c := by
  by_cases happ : Protocol.Applicable c s t
  · have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
    have hs : s ∈ c := Multiset.mem_of_le hsub (by simp)
    have ht : t ∈ c := Multiset.mem_of_le hsub (by simp)
    have hid := mass_stepOrSelf_add c s t happ
    have hle := Transition_mass_pair_le s t (hwin.2 s hs) (hwin.2 t ht)
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

theorem mass_applyDraw_le {n : ℕ} (c : Cfg L K)
    (hwin : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c) (d : Draw L K) :
    PhaseOneDrain.PhaseOneMass (applyDraw c d) ≤ PhaseOneDrain.PhaseOneMass c := by
  cases d with
  | none => exact le_rfl
  | some p => exact mass_stepOrSelf_le c hwin _ _

/-- An opposite-unit Main pair cancels: the mass drops by two. -/
theorem cancelRect_step_drop {n : ℕ} (c : Cfg L K)
    (hwin : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (p : AgentState L K × AgentState L K) (hp : p ∈ cancelRect L K)
    (hp1 : 1 ≤ c.count p.1) (hp2 : 1 ≤ c.count p.2) :
    PhaseOneDrain.PhaseOneMass (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) + 1 ≤
      PhaseOneDrain.PhaseOneMass c := by
  have hm1 : p.1 ∈ c := Multiset.one_le_count_iff_mem.mp hp1
  have hm2 : p.2 ∈ c := Multiset.one_le_count_iff_mem.mp hp2
  have key : ∀ s t : AgentState L K, s ∈ c → t ∈ c → s.role = Role.main →
      t.role = Role.main → s.smallBias.val + t.smallBias.val = 6 → s ≠ t →
      PhaseOneDrain.PhaseOneMass (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1 ≤
        PhaseOneDrain.PhaseOneMass c ∨ s.smallBias.val = 3 := by
    intro s t hs ht hsM htM hsum hne
    by_cases h3 : s.smallBias.val = 3
    · exact Or.inr h3
    left
    have happ := Phase5Convergence.applicable_of_mem_distinct5 hs ht hne
    have hid := mass_stepOrSelf_add c s t happ
    rw [Phase1Convergence.Transition_eq_avg_of_phase1_main s t (hwin.2 s hs) (hwin.2 t ht)
      hsM htM] at hid
    simp only [AveragingRate.biasZ, hsM, htM, if_true, avgFin7] at hid
    have hs7 := s.smallBias.isLt
    have ht7 := t.smallBias.isLt
    have e1 : (s.smallBias.val + t.smallBias.val) / 2 = 3 := by omega
    have e2 : (s.smallBias.val + t.smallBias.val + 1) / 2 = 3 := by omega
    rw [e1, e2] at hid
    omega
  unfold cancelRect at hp
  rw [Finset.mem_union, Finset.mem_product, Finset.mem_product] at hp
  rcases hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hne := plus_minus_ne p.1 ha p.2 hb
    simp only [plusUnitSet, minusUnitSet, Finset.mem_filter, Finset.mem_univ, true_and]
      at ha hb
    rcases key p.1 p.2 hm1 hm2 ha.1 hb.1 (by omega) hne with h | h
    · exact h
    · omega
  · have hne := minus_plus_ne p.1 ha p.2 hb
    simp only [plusUnitSet, minusUnitSet, Finset.mem_filter, Finset.mem_univ, true_and]
      at ha hb
    rcases key p.1 p.2 hm1 hm2 ha.1 hb.1 (by omega) hne with h | h
    · exact h
    · omega

theorem sum_interactionCount_cancelRect (c : Cfg L K) :
    (∑ p ∈ cancelRect L K, c.interactionCount p.1 p.2) =
      (plusUnitSet L K).sum c.count * (minusUnitSet L K).sum c.count +
        (minusUnitSet L K).sum c.count * (plusUnitSet L K).sum c.count := by
  classical
  unfold cancelRect
  have hdisj : Disjoint (plusUnitSet L K ×ˢ minusUnitSet L K)
      (minusUnitSet L K ×ˢ plusUnitSet L K) := by
    refine Finset.disjoint_product.mpr (Or.inl ?_)
    exact Finset.disjoint_left.mpr fun a ha hb => plus_minus_ne a ha a hb rfl
  rw [Finset.sum_union hdisj,
    Phase7Convergence.sum_interactionCount_cross_disjoint7 c _ _ plus_minus_ne,
    Phase7Convergence.sum_interactionCount_cross_disjoint7 c _ _ minus_plus_ne]

/-- Kernel form of the cancellation rate: the mass drops with probability at least
`2 A B / (n (n - 1))`, where `A`, `B` count the `+1` and `-1` Mains. -/
theorem cancellation_kernel_floor {n : ℕ} (hn : 2 ≤ n) (c : Cfg L K)
    (hwin : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c) :
    ENNReal.ofReal (((2 * (plusUnitSet L K).sum c.count * (minusUnitSet L K).sum c.count :
        ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      (NonuniformMajority L K).transitionKernel c
        {c' | PhaseOneDrain.PhaseOneMass c' + 1 ≤ PhaseOneDrain.PhaseOneMass c} := by
  have h := Phase7Convergence.drop_prob_of_rect
    (fun b : Cfg L K => PhaseOneDrain.PhaseOneMass b) n hn c hwin.1 (cancelRect L K)
    (2 * (plusUnitSet L K).sum c.count * (minusUnitSet L K).sum c.count)
    (fun p hp hp1 hp2 _ => cancelRect_step_drop c hwin p hp hp1 hp2)
    (by rw [sum_interactionCount_cancelRect]; ring_nf; exact le_rfl)
  exact h

theorem sum_map_eq_sum_count {M : Type*} [AddCommMonoid M] (c : Cfg L K)
    (f : AgentState L K → M) :
    (c.map f).sum = ∑ a, c.count a • f a := by
  classical
  rw [Finset.sum_multiset_map_count]
  refine Finset.sum_subset (Finset.subset_univ _) ?_
  intro a _ ha
  rw [Multiset.count_eq_zero.mpr (fun h => ha (Multiset.mem_toFinset.mpr h)), zero_smul]

theorem finset_sum_count_eq (c : Cfg L K) (P : Finset (AgentState L K)) :
    P.sum c.count = ∑ a, c.count a * (if a ∈ P then 1 else 0) := by
  classical
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]

/-- On a configuration whose Main biases are all integer units or zero, the mass is
`A + B` and the centred bias sum is `A - B`. -/
theorem mass_and_bias_of_unit (c : Cfg L K)
    (hunit : ∀ a ∈ c, a.role = Role.main → a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) :
    PhaseOneDrain.PhaseOneMass c =
        (plusUnitSet L K).sum c.count + (minusUnitSet L K).sum c.count ∧
      AveragingRate.centredBiasSum c =
        (((plusUnitSet L K).sum c.count : ℕ) : ℤ) - (((minusUnitSet L K).sum c.count : ℕ) : ℤ) := by
  classical
  have hpt : ∀ a, c.count a * (AveragingRate.biasZ a).natAbs =
      c.count a * (if a ∈ plusUnitSet L K then 1 else 0) +
        c.count a * (if a ∈ minusUnitSet L K then 1 else 0) ∧
      (c.count a : ℤ) * AveragingRate.biasZ a =
        (c.count a : ℤ) * (if a ∈ plusUnitSet L K then 1 else 0) -
          (c.count a : ℤ) * (if a ∈ minusUnitSet L K then 1 else 0) := by
    intro a
    by_cases hz : c.count a = 0
    · simp [hz]
    have ha : a ∈ c := Multiset.count_ne_zero.mp hz
    simp only [plusUnitSet, minusUnitSet, Finset.mem_filter, Finset.mem_univ, true_and,
      AveragingRate.biasZ]
    by_cases hM : a.role = Role.main
    · have hv := hunit a ha hM
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with hv | hv | hv <;> simp [hM, hv]
    · simp [hM]
  constructor
  · unfold PhaseOneDrain.PhaseOneMass
    rw [sum_map_eq_sum_count, finset_sum_count_eq, finset_sum_count_eq,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_eq_mul]; exact (hpt a).1
  · unfold AveragingRate.centredBiasSum
    rw [sum_map_eq_sum_count, finset_sum_count_eq, finset_sum_count_eq]
    push_cast
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by
      first
      | (rw [nsmul_eq_mul]; exact (hpt a).2)
      | exact (hpt a).2

/-- The window of the mass stage (25). -/
def MassWindow (n d : ℕ) (c : Cfg L K) : Prop :=
  PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c ∧
    (∀ a ∈ c, a.role = Role.main → a.smallBias.val ∈ ({2, 3, 4} : Finset ℕ)) ∧
    12 * n ≤ 25 * RoleSplitConcentration.mainCount c ∧
    40 * d ≤ RoleSplitConcentration.mainCount c ∧
    |AveragingRate.centredBiasSum c| ≤ (d : ℤ)

/-- The target of the mass stage: `W ≤ 3 M / 100`. -/
def MassTarget (c : Cfg L K) : Prop :=
  100 * PhaseOneDrain.PhaseOneMass c ≤ 3 * RoleSplitConcentration.mainCount c

/-- (24) in kernel form on the mass window off the target. -/
theorem mass_drop_probability {n d : ℕ} (hn : 2 ≤ n) (c : Cfg L K)
    (hc : MassWindow n d c) (htarget : ¬ MassTarget c) :
    ENNReal.ofReal (1 / 400000 : ℝ) ≤
      (NonuniformMajority L K).transitionKernel c
        {c' | PhaseOneDrain.PhaseOneMass c' + 1 ≤ PhaseOneDrain.PhaseOneMass c} := by
  obtain ⟨hwin, hunit, hmain, hsmall, hgap⟩ := hc
  obtain ⟨hmass, hbias⟩ := mass_and_bias_of_unit c hunit
  set A := (plusUnitSet L K).sum c.count
  set B := (minusUnitSet L K).sum c.count
  set M := RoleSplitConcentration.mainCount c
  have hwork : 3 * M < 100 * (A + B) := by
    unfold MassTarget at htarget
    rw [hmass] at htarget
    omega
  rw [hbias] at hgap
  have hg := abs_le.mp hgap
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hrate : (1 / 400000 : ℝ) <
      ((2 * A * B : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    rcases le_total B A with hBA | hAB
    · have hfl := PhaseOneDrain.minority_count_floor n M A B hmain hBA (by omega) hwork
      have h := PhaseOneDrain.cancellation_probability_floor n A B hn hBA hfl
      push_cast
      exact h
    · have hfl := PhaseOneDrain.minority_count_floor n M B A hmain hAB (by omega)
        (by omega)
      have h := PhaseOneDrain.cancellation_probability_floor n B A hn hAB hfl
      push_cast
      calc (1 / 400000 : ℝ) < 2 * (B : ℝ) * A / ((n : ℝ) * ((n : ℝ) - 1)) := h
        _ = 2 * (A : ℝ) * B / ((n : ℝ) * ((n : ℝ) - 1)) := by ring
  exact (ENNReal.ofReal_le_ofReal hrate.le).trans (cancellation_kernel_floor hn c hwin)

/-- (25), general horizon. -/
theorem mass_stage_tail (init : Cfg L K) {n d : ℕ} (hn : 2 ≤ n) (N : ℕ) :
    (law init).real
        {ω | (N : WithTop ℕ) < exitTime init
          (fun c => ¬ MassWindow n d c ∨ MassTarget c) ω} ≤
      Real.exp (((PhaseOneDrain.PhaseOneMass init : ℝ) + 1) * Real.log 2 -
        (N : ℝ) * (1 / 400000 : ℝ) / 2) := by
  have hr : ENNReal.ofReal (1 / 400000 : ℝ) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hrt : (ENNReal.ofReal (1 / 400000 : ℝ)).toReal = 1 / 400000 :=
    ENNReal.toReal_ofReal (by norm_num)
  have h := potential_drain_tail init PhaseOneDrain.PhaseOneMass
    (MassWindow n d) MassTarget
    (fun c hc dr => mass_applyDraw_le c hc.1 dr)
    (ENNReal.ofReal (1 / 400000 : ℝ)) hr (by rw [hrt]; norm_num)
    (fun c hc htarget => mass_drop_probability hn c hc htarget) N
  rwa [hrt] at h

/-- (25), calibrated: from mass at most `n`, within `800000 n` steps the trace reaches
`W ≤ 3 M / 100` or leaves the window, except with probability `e^{-n/4}`, for
`n ≥ 13`. -/
theorem mass_stage_tail_calibrated (init : Cfg L K) {n d : ℕ} (hn : 13 ≤ n)
    (hmass : PhaseOneDrain.PhaseOneMass init ≤ n) :
    (law init).real
        {ω | ((800000 * n : ℕ) : WithTop ℕ) < exitTime init
          (fun c => ¬ MassWindow n d c ∨ MassTarget c) ω} ≤
      Real.exp (-(n : ℝ) / 4) := by
  refine (mass_stage_tail init (d := d) (by omega) (800000 * n)).trans
    (Real.exp_le_exp.mpr ?_)
  have hmR : (PhaseOneDrain.PhaseOneMass init : ℝ) ≤ n := by exact_mod_cast hmass
  have hnR : (13 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.log_two_lt_d9
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  push_cast
  nlinarith

end Ripple.PopulationProtocol.ExactMajority.PhaseOneDrainStages

end
