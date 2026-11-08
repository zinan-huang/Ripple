/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Symmetric Phase-1 saturated-extreme drain

The old slot-1 gate carried a positive `+3` extreme as an invariant, while its
postcondition required the two-sided saturated-extreme count to be zero.  That
made the literal postcondition empty.  The drop argument only needs an extreme
witness while the potential is positive.  This file records that fact in a
sign-symmetric gate: a live `+3` extreme requires a positive-side partner floor,
and a live `-3` extreme requires its reflected partner floor.  At potential zero
both implications are vacuous, so the postcondition remains inhabitable.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase1ReadySurvival

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase1SymmetricDrain

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Reflected negative-side drop cell -/

/-- A saturated `-3` Main. -/
def extremeNeg (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ a.smallBias.val = 0

instance (a : AgentState L K) : Decidable (extremeNeg a) := by
  unfold extremeNeg
  infer_instance

/-- Partners that pull a `-3` Main into the interior under averaging. -/
def pullNeg (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ 2 ≤ a.smallBias.val

instance (a : AgentState L K) : Decidable (pullNeg a) := by
  unfold pullNeg
  infer_instance

def extremeNegSet (L K : ℕ) : Finset (AgentState L K) :=
  Finset.univ.filter extremeNeg

def pullNegSet (L K : ℕ) : Finset (AgentState L K) :=
  Finset.univ.filter pullNeg

theorem extremeNeg_pullNeg_disjoint
    (a : AgentState L K) (ha : a ∈ extremeNegSet L K)
    (b : AgentState L K) (hb : b ∈ pullNegSet L K) : a ≠ b := by
  simp only [extremeNegSet, pullNegSet, Finset.mem_filter,
    extremeNeg, pullNeg] at ha hb
  obtain ⟨_, _, hav⟩ := ha
  obtain ⟨_, _, hbv⟩ := hb
  intro heq
  rw [heq] at hav
  omega

/-- Reflection of the existing positive-side `avgFin7` calculation. -/
theorem avgFin7_extremeVal_pair_drop_neg
    (x y : Fin 7) (hx : x.val = 0) (hy : 2 ≤ y.val) :
    (if Phase1Convergence.extremeVal (avgFin7 x y).1 then 1 else 0) +
          (if Phase1Convergence.extremeVal (avgFin7 x y).2 then 1 else 0) + 1
      ≤ (if Phase1Convergence.extremeVal x then 1 else 0) +
          (if Phase1Convergence.extremeVal y then 1 else 0) := by
  have hxv : x = (0 : Fin 7) := Fin.ext (by simpa using hx)
  subst x
  fin_cases y <;> first | (exfalso; revert hy; decide) | decide

/-- A `-3` extreme paired with a reflected partner strictly lowers the
two-sided saturated-extreme count. -/
theorem Transition_extremeU_pair_drop_neg
    (s t : AgentState L K)
    (hs1 : s.phase.val = 1) (ht1 : t.phase.val = 1)
    (hsE : extremeNeg s) (htP : pullNeg t) :
    Multiset.countP (fun a => Phase1Convergence.extremeSt a)
          ({(Transition L K s t).1, (Transition L K s t).2} :
            Multiset (AgentState L K)) + 1
      ≤ Multiset.countP (fun a => Phase1Convergence.extremeSt a)
          ({s, t} : Multiset (AgentState L K)) := by
  obtain ⟨hsM, hsv⟩ := hsE
  obtain ⟨htM, htv⟩ := htP
  rw [Phase1Convergence.Transition_eq_avg_of_phase1_main
    s t hs1 ht1 hsM htM]
  rw [Phase1Convergence.countP_extremeSt_pair,
    Phase1Convergence.countP_extremeSt_pair]
  set o1 := ({s with smallBias := (avgFin7 s.smallBias t.smallBias).1} :
    AgentState L K) with ho1
  set o2 := ({t with smallBias := (avgFin7 s.smallBias t.smallBias).2} :
    AgentState L K) with ho2
  have hkey : ∀ a : AgentState L K, a.role = Role.main →
      (Phase1Convergence.extremeSt a ↔
        Phase1Convergence.extremeVal a.smallBias = true) :=
    fun a ha => by
      unfold Phase1Convergence.extremeSt
      exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
  have ho1M : o1.role = Role.main := by rw [ho1]; exact hsM
  have ho2M : o2.role = Role.main := by rw [ho2]; exact htM
  have ho1sb : o1.smallBias = (avgFin7 s.smallBias t.smallBias).1 := by
    rw [ho1]
  have ho2sb : o2.smallBias = (avgFin7 s.smallBias t.smallBias).2 := by
    rw [ho2]
  rw [if_congr (hkey o1 ho1M) rfl rfl,
    if_congr (hkey o2 ho2M) rfl rfl,
    if_congr (hkey s hsM) rfl rfl,
    if_congr (hkey t htM) rfl rfl, ho1sb, ho2sb]
  simpa using avgFin7_extremeVal_pair_drop_neg
    s.smallBias t.smallBias hsv htv

private theorem countP_stepOrSelf_drop_of_pair
    (P : AgentState L K → Prop) [DecidablePred P]
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hpair : Multiset.countP P
        ({(Transition L K s t).1, (Transition L K s t).2} :
          Multiset (AgentState L K)) + 1 ≤
      Multiset.countP P ({s, t} : Multiset (AgentState L K))) :
    Multiset.countP P
          (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1
      ≤ Multiset.countP P c := by
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
      c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  have hpair_le : Multiset.countP P ({s, t} : Multiset (AgentState L K)) ≤
      Multiset.countP P c := Multiset.countP_le_of_le P hsub
  omega

/-- Negative-side scheduler rectangle on the phase-only honest window. -/
theorem extremeU_drop_prob_rect_neg_of_phase1Win
    (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c) :
    ENNReal.ofReal
        (((extremeNegSet L K).sum c.count *
            (pullNegSet L K).sum c.count : ℕ) /
          ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase1Convergence.extremeU c' + 1 ≤
          Phase1Convergence.extremeU c} := by
  obtain ⟨hcardn, hph⟩ := hInv
  refine Phase7Convergence.drop_prob_of_rect
    (fun c => Phase1Convergence.extremeU c) n hn c hcardn
    ((extremeNegSet L K) ×ˢ (pullNegSet L K)) _ ?_ (le_of_eq ?_)
  · rintro ⟨s, t⟩ hp hcs hct _
    rw [Finset.mem_product] at hp
    obtain ⟨hsmem, htmem⟩ := hp
    have hsm : s ∈ c := Multiset.one_le_count_iff_mem.mp hcs
    have htm : t ∈ c := Multiset.one_le_count_iff_mem.mp hct
    have hs1 : s.phase.val = 1 := hph s hsm
    have ht1 : t.phase.val = 1 := hph t htm
    simp only [extremeNegSet, Finset.mem_filter] at hsmem
    simp only [pullNegSet, Finset.mem_filter] at htmem
    obtain ⟨_, hsE⟩ := hsmem
    obtain ⟨_, htP⟩ := htmem
    have hne : s ≠ t := extremeNeg_pullNeg_disjoint s
      (by
        simp only [extremeNegSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hsE⟩) t
      (by
        simp only [pullNegSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, htP⟩)
    have happ : Protocol.Applicable c s t :=
      Phase5Convergence.applicable_of_mem_distinct5 hsm htm hne
    exact countP_stepOrSelf_drop_of_pair
      (fun a => Phase1Convergence.extremeSt a) c s t happ
      (Transition_extremeU_pair_drop_neg s t hs1 ht1 hsE htP)
  · rw [Phase7Convergence.sum_interactionCount_cross_disjoint7 c _ _
      extremeNeg_pullNeg_disjoint]

/-- Negative-side structural floor. -/
theorem phase1_drop_floor_neg_of_phase1Win
    (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hInv : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (P : ℕ)
    (hext : 1 ≤ (extremeNegSet L K).sum c.count)
    (hpull : P ≤ (pullNegSet L K).sum c.count) :
    ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase1Convergence.extremeU c' + 1 ≤
          Phase1Convergence.extremeU c} := by
  refine le_trans ?_ (extremeU_drop_prob_rect_neg_of_phase1Win n hn c hInv)
  have hprod : P ≤ (extremeNegSet L K).sum c.count *
      (pullNegSet L K).sum c.count := by
    calc
      P ≤ 1 * P := by omega
      _ ≤ (extremeNegSet L K).sum c.count * P :=
        Nat.mul_le_mul_right _ hext
      _ ≤ (extremeNegSet L K).sum c.count *
          (pullNegSet L K).sum c.count := Nat.mul_le_mul_left _ hpull
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply DrainThreading.ofReal_div_le_of_num_le _ (by positivity) (by nlinarith)
  exact_mod_cast hprod

/-! ## Adaptive, post-compatible ready gate -/

/-- The two saturated ends partition every positive `extremeU` witness. -/
theorem extremePos_or_neg_count_pos_of_extremeU_pos
    (c : Config (AgentState L K))
    (hU : 1 ≤ Phase1Convergence.extremeU c) :
    1 ≤ (DrainThreading.extremePosSet L K).sum c.count ∨
      1 ≤ (extremeNegSet L K).sum c.count := by
  classical
  have hcount : 0 < Multiset.countP
      (fun a : AgentState L K => Phase1Convergence.extremeSt a) c := by
    simpa [Phase1Convergence.extremeU] using hU
  rw [Multiset.countP_pos] at hcount
  obtain ⟨a, ha, hst⟩ := hcount
  have hv : a.smallBias.val = 0 ∨ a.smallBias.val = 6 := by
    have hv' := hst.2
    unfold Phase1Convergence.extremeVal at hv'
    simpa using hv'
  rcases hv with hv | hv
  · right
    have hamem : a ∈ extremeNegSet L K := by
      simp only [extremeNegSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hst.1, hv⟩
    have hca : 1 ≤ c.count a := Multiset.one_le_count_iff_mem.mpr ha
    exact le_trans hca
      (Finset.single_le_sum (f := c.count) (fun _ _ => Nat.zero_le _) hamem)
  · left
    have hamem : a ∈ DrainThreading.extremePosSet L K := by
      simp only [DrainThreading.extremePosSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hst.1, hv⟩
    have hca : 1 ≤ c.count a := Multiset.one_le_count_iff_mem.mpr ha
    exact le_trans hca
      (Finset.single_le_sum (f := c.count) (fun _ _ => Nat.zero_le _) hamem)

/-- Partner floors are required only when the corresponding saturated end is
actually populated. -/
structure Phase1AdaptiveReady
    (n P : ℕ) (c : Config (AgentState L K)) : Prop where
  honest : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c
  pullPos : 1 ≤ (DrainThreading.extremePosSet L K).sum c.count →
    P ≤ (DrainThreading.pullPosSet L K).sum c.count
  pullNeg : 1 ≤ (extremeNegSet L K).sum c.count →
    P ≤ (pullNegSet L K).sum c.count

/-- At potential zero, the adaptive structural fields are vacuous.  This is the
formal post-compatibility property missing from the old ready gate. -/
theorem adaptiveReady_of_phase1Win_noExtreme
    (n P : ℕ) (c : Config (AgentState L K))
    (hhonest : PhaseOnlyWindows.Phase1Win (L := L) (K := K) n c)
    (hzero : Phase1Convergence.extremeU c = 0) :
    Phase1AdaptiveReady (L := L) (K := K) n P c := by
  refine ⟨hhonest, ?_, ?_⟩
  · intro hpos
    classical
    have hne : (DrainThreading.extremePosSet L K).sum c.count ≠ 0 := by
      omega
    obtain ⟨a, ha, hca⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    simp only [DrainThreading.extremePosSet, Finset.mem_filter] at ha
    have hamem : a ∈ c :=
      Multiset.one_le_count_iff_mem.mp (Nat.one_le_iff_ne_zero.mpr hca)
    have hU : 1 ≤ Phase1Convergence.extremeU c := by
      unfold Phase1Convergence.extremeU
      exact Multiset.countP_pos_of_mem hamem ⟨ha.2.1, by
        unfold Phase1Convergence.extremeVal
        simp [ha.2.2]⟩
    omega
  · intro hneg
    have hU : 1 ≤ Phase1Convergence.extremeU c := by
      classical
      have hne : (extremeNegSet L K).sum c.count ≠ 0 := by omega
      obtain ⟨a, ha, hca⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      simp only [extremeNegSet, Finset.mem_filter] at ha
      have hamem : a ∈ c :=
        Multiset.one_le_count_iff_mem.mp (Nat.one_le_iff_ne_zero.mpr hca)
      unfold Phase1Convergence.extremeU
      exact Multiset.countP_pos_of_mem hamem ⟨ha.2.1, by
        unfold Phase1Convergence.extremeVal
        simp [ha.2.2]⟩
    omega

theorem potNonincrOn_extremeU_adaptive (n P : ℕ) :
    OneSidedCancel.PotNonincrOn
      (fun c => Phase1AdaptiveReady (L := L) (K := K) n P c)
      (NonuniformMajority L K).transitionKernel
      (fun c => Phase1Convergence.extremeU c) := by
  intro c hc
  exact PhaseOnlyWindows.potNonincrOn_extremeU_phase1Win
    (L := L) (K := K) n c hc.honest

/-- Per-level drop bound with the live saturated end selected at runtime. -/
theorem hdrop1_adaptive
    (n P : ℕ) (hn : 2 ≤ n) :
    ∀ m, ∀ b : Config (AgentState L K),
      Phase1AdaptiveReady (L := L) (K := K) n P b →
      Phase1Convergence.extremeU b = m →
      (NonuniformMajority L K).transitionKernel b
          (OneSidedCancel.potBelow Phase1Convergence.extremeU m)ᶜ ≤
        DrainEngine.qHat P n m := by
  intro m b hb hbm
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact DrainEngine.qHat_zero_bound P n
      (Phase1Convergence.extremeU (L := L) (K := K)) b
  · rw [DrainEngine.qHat_eq_on_pos P n m hm]
    unfold DrainRates.levelRate
    apply DrainThreading.extremeU_hdrop_of_floor m
      (ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) b hbm
    have hU : 1 ≤ Phase1Convergence.extremeU b := by omega
    rcases extremePos_or_neg_count_pos_of_extremeU_pos b hU with hpos | hneg
    · exact PhaseWinDrain.phase1_drop_floor_of_phase1Win
        n hn b hb.honest P hpos (hb.pullPos hpos)
    · exact phase1_drop_floor_neg_of_phase1Win
        n hn b hb.honest P hneg (hb.pullNeg hneg)

/-- Honest one-step escape budget for the adaptive gate. -/
structure AdaptiveEscapeAtom
    (n P : ℕ) (η : ℝ≥0∞) : Prop where
  hesc : ∀ x, Phase1AdaptiveReady (L := L) (K := K) n P x →
    (NonuniformMajority L K).transitionKernel x
      {y | ¬ Phase1AdaptiveReady (L := L) (K := K) n P y} ≤ η

/-- Slot-1 survival with an independent drain and adaptive-gate escape budget. -/
noncomputable def phase1AdaptiveSurvivalBudgeted
    {n : ℕ} (P M₀ : ℕ) (hn : 2 ≤ n)
    (η : ℝ≥0∞) (hesc : AdaptiveEscapeAtom (L := L) (K := K) n P η)
    (tWin : ℕ → ℕ) (drainε escapeε : ℝ≥0)
    (hDrain : (∑ m ∈ Finset.Icc 1 M₀,
      (DrainEngine.qHat P n m) ^ (tWin m) : ℝ≥0∞) ≤ (drainε : ℝ≥0∞))
    (hescε : (((∑ m ∈ Finset.Icc 1 M₀, tWin m) : ℕ) : ℝ≥0∞) * η ≤
      (escapeε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  WindowSurvival.slotSurvival
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase1AdaptiveReady (L := L) (K := K) n P c)
    (fun c => Phase1Convergence.extremeU c)
    (potNonincrOn_extremeU_adaptive (L := L) (K := K) n P)
    (DrainEngine.qHat P n) (by rw [DrainEngine.qHat_zero])
    (hdrop1_adaptive (L := L) (K := K) n P hn)
    η hesc.hesc tWin M₀ drainε escapeε hDrain hescε

#print axioms avgFin7_extremeVal_pair_drop_neg
#print axioms Transition_extremeU_pair_drop_neg
#print axioms extremeU_drop_prob_rect_neg_of_phase1Win
#print axioms phase1_drop_floor_neg_of_phase1Win
#print axioms extremePos_or_neg_count_pos_of_extremeU_pos
#print axioms adaptiveReady_of_phase1Win_noExtreme
#print axioms potNonincrOn_extremeU_adaptive
#print axioms hdrop1_adaptive
#print axioms phase1AdaptiveSurvivalBudgeted

end Phase1SymmetricDrain
end Ripple.PopulationProtocol.ExactMajority
