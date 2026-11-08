/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Quantitative Phase-10 recovery from an initializer-error seed

`Recovery10EntryReachable` proves that an active initializer-error seed can be
scheduled to `Phase10Ready`.  This file supplies the corresponding scheduler
bound.  Unlike the ordinary timed seam, this epidemic starts while other agents
may still be far below Phase 9, so its invariant is only fixed population size
plus one Phase-10 seed; no `AllClockGEpCard 9` premise is used.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Recovery10EntryReachable
import Ripple.PopulationProtocol.ExactMajority.Probability.TimedChainRungs
import Ripple.PopulationProtocol.ExactMajority.Probability.PartnerMargin

namespace Ripple.PopulationProtocol.ExactMajority
namespace Recovery10EntryTime

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal Classical
open ConditionalPhaseProgress AdvanceEpidemics Phase10Drop

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Global Phase-10 epidemic rectangle -/

/-- A mixed pair with one agent at phase at least `q` produces two agents at
phase at least `q`.  The lower-phase member needs no phase-floor hypothesis. -/
theorem geP_pair_advances_global (q : ℕ) (s t : AgentState L K)
    (hmixed : (geP (L := L) (K := K) q s ∧ ¬ geP (L := L) (K := K) q t) ∨
      (¬ geP (L := L) (K := K) q s ∧ geP (L := L) (K := K) q t)) :
    Multiset.countP (fun a => geP q a)
          ({s, t} : Multiset (AgentState L K)) + 1 ≤
      Multiset.countP (fun a => geP q a)
        ({(Transition L K s t).1, (Transition L K s t).2}
          : Multiset (AgentState L K)) := by
  have hmaxq : q ≤ max s.phase.val t.phase.val := by
    rcases hmixed with ⟨hs, _⟩ | ⟨_, ht⟩
    · exact le_trans hs (le_max_left _ _)
    · exact le_trans ht (le_max_right _ _)
  have hout1 : geP (L := L) (K := K) q (Transition L K s t).1 :=
    le_trans hmaxq
      (Transition_left_phase_ge_pair_max (L := L) (K := K) s t)
  have hout2 : geP (L := L) (K := K) q (Transition L K s t).2 :=
    le_trans hmaxq
      (Transition_right_phase_ge_pair_max (L := L) (K := K) s t)
  rw [countP_geP_pair, countP_geP_pair, if_pos hout1, if_pos hout2]
  rcases hmixed with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [if_pos hs, if_neg ht]
  · rw [if_neg hs, if_pos ht]

/-- Scheduling a mixed pair raises the global phase-`q` count by one. -/
theorem geCount_stepOrSelf_advance_global (q : ℕ)
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hmixed : (geP (L := L) (K := K) q s ∧ ¬ geP (L := L) (K := K) q t) ∨
      (¬ geP (L := L) (K := K) q s ∧ geP (L := L) (K := K) q t)) :
    geCount (L := L) (K := K) q c + 1 ≤
      geCount (L := L) (K := K) q
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t =
      c - {s, t} +
        {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  unfold geCount
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  have hpair_le :
      Multiset.countP (fun a => geP q a)
          ({s, t} : Multiset (AgentState L K)) ≤
        Multiset.countP (fun a => geP q a) c :=
    Multiset.countP_le_of_le _ hsub
  have hadv := geP_pair_advances_global
    (L := L) (K := K) q s t hmixed
  omega

private theorem applicable_of_mem_distinct
    {c : Config (AgentState L K)} {x y : AgentState L K}
    (hx : x ∈ c) (hy : y ∈ c) (hxy : x ≠ y) :
    Protocol.Applicable c x y := by
  refine Multiset.le_iff_count.mpr ?_
  intro a
  rw [show ({x, y} : Multiset (AgentState L K)) =
      x ::ₘ y ::ₘ 0 from rfl,
    Multiset.count_cons, Multiset.count_cons, Multiset.count_zero]
  have hxc : 1 ≤ Multiset.count x c := Multiset.one_le_count_iff_mem.mpr hx
  have hyc : 1 ≤ Multiset.count y c := Multiset.one_le_count_iff_mem.mpr hy
  by_cases hax : a = x
  · subst hax
    have hay : ¬ a = y := fun h => hxy (h ▸ rfl)
    rw [if_pos rfl, if_neg hay]
    omega
  · by_cases hay : a = y
    · subst hay
      rw [if_neg hax, if_pos rfl]
      omega
    · rw [if_neg hax, if_neg hay]
      exact Nat.zero_le _

/-- The complement of the phase-`q` count has the expected cardinality. -/
theorem countP_not_geP_eq_card_sub (q : ℕ)
    (c : Config (AgentState L K)) :
    Multiset.countP (fun a => ¬ geP q a) c =
      c.card - geCount (L := L) (K := K) q c := by
  unfold geCount
  induction c using Multiset.induction_on with
  | empty => simp
  | @cons a c ih =>
      have hle : Multiset.countP (fun a => geP q a) c ≤ c.card :=
        Multiset.countP_le_card _ _
      rw [Multiset.countP_cons, Multiset.countP_cons,
        Multiset.card_cons, ih]
      by_cases ha : geP (L := L) (K := K) q a
      · simp [ha]
      · simp [ha]
        omega

/-- The global informed×uninformed rectangle has mass `m(n-m)`. -/
theorem sum_interactionCount_global_rect (q n : ℕ)
    (c : Config (AgentState L K)) (hcard : c.card = n) :
    (∑ pr ∈
        (Finset.univ.filter (fun a : AgentState L K => geP q a)) ×ˢ
          (Finset.univ.filter (fun a : AgentState L K => ¬ geP q a)),
      c.interactionCount pr.1 pr.2) =
        geCount (L := L) (K := K) q c *
          (n - geCount (L := L) (K := K) q c) := by
  rw [sum_interactionCount_cross_disjoint c _ _ ?_,
    sum_count_geP,
    PartnerMargin.sum_count_filter_eq_countP,
    countP_not_geP_eq_card_sub, hcard]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  intro hab
  exact hb.2 (hab ▸ ha.2)

/-- From any card-`n` state, the scheduler raises `geCount 10` with the usual
epidemic probability.  No lower phase floor is assumed. -/
theorem ge10_advance_prob (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hcard : c.card = n) :
    ENNReal.ofReal
        (((geCount (L := L) (K := K) 10 c *
            (n - geCount (L := L) (K := K) 10 c) : ℕ) : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | geCount (L := L) (K := K) 10 c + 1 ≤
          geCount (L := L) (K := K) 10 c'} := by
  set R :=
    (Finset.univ.filter (fun a : AgentState L K => geP 10 a)) ×ˢ
      (Finset.univ.filter (fun a : AgentState L K => ¬ geP 10 a)) with hR
  set m := geCount (L := L) (K := K) 10 c with hm
  have hcount : m * (n - m) ≤
      ∑ pr ∈ R, c.interactionCount pr.1 pr.2 := by
    rw [hR, sum_interactionCount_global_rect 10 n c hcard]
  have h := advance_prob_of_rect (L := L) (K := K) 9 n hn c hcard R
    (m * (n - m)) ?_ hcount
  · simpa using h
  · rintro ⟨a, b⟩ hp h1 h2 _hsame
    rw [hR, Finset.mem_product, Finset.mem_filter,
      Finset.mem_filter] at hp
    obtain ⟨⟨_, ha⟩, ⟨_, hb⟩⟩ := hp
    have hamem : a ∈ c := Multiset.one_le_count_iff_mem.mp h1
    have hbmem : b ∈ c := Multiset.one_le_count_iff_mem.mp h2
    have hab : a ≠ b := by
      intro hab
      exact hb (hab ▸ ha)
    have happ : Protocol.Applicable c a b :=
      applicable_of_mem_distinct hamem hbmem hab
    simpa using geCount_stepOrSelf_advance_global
      (L := L) (K := K) 10 c a b happ (Or.inl ⟨ha, hb⟩)

/-! ## Coupon engine on the seed invariant -/

/-- Fixed cardinality plus a surviving Phase-10 epidemic seed. -/
def SpreadInv (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ 1 ≤ geCount (L := L) (K := K) 10 c

/-- Number of agents not yet at Phase 10. -/
def spreadPot (n : ℕ) (c : Config (AgentState L K)) : ℕ :=
  n - geCount (L := L) (K := K) 10 c

theorem SpreadInv_closed (n : ℕ) :
    Engine.InvClosed (NonuniformMajority L K).transitionKernel
      (SpreadInv (L := L) (K := K) n) := by
  intro b hb
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
      {x | ¬ SpreadInv (L := L) (K := K) n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hx hbad
  apply hbad
  refine ⟨?_, ?_⟩
  · exact (Protocol.stepDistOrSelf_support_card_eq
      (NonuniformMajority L K) b x hx).trans hb.1
  · exact geCount_ge_monotone (L := L) (K := K) 10 1 b x hb.2 hx

theorem spreadPot_nonincr (n : ℕ) :
    Engine.PotNonincrOn (SpreadInv (L := L) (K := K) n)
      (NonuniformMajority L K).transitionKernel
      (spreadPot (L := L) (K := K) n) := by
  intro b _hb
  change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
      {x | spreadPot (L := L) (K := K) n b <
        spreadPot (L := L) (K := K) n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _
    (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hx hbad
  simp only [Set.mem_setOf_eq, spreadPot] at hbad
  have hmono : geCount (L := L) (K := K) 10 b ≤
      geCount (L := L) (K := K) 10 x :=
    geCount_ge_monotone (L := L) (K := K) 10
      (geCount (L := L) (K := K) 10 b) b x (le_refl _) hx
  omega

/-- Raw one-level failure bound supplied by the global epidemic rectangle. -/
theorem spread_hdrop_raw (n : ℕ) (hn : 2 ≤ n) :
    ∀ m : ℕ, ∀ b : Config (AgentState L K),
      SpreadInv (L := L) (K := K) n b →
      spreadPot (L := L) (K := K) n b = m →
      (NonuniformMajority L K).transitionKernel b
          (Engine.potBelow (spreadPot (L := L) (K := K) n) m)ᶜ ≤
        1 - ENNReal.ofReal
          ((((n - geCount (L := L) (K := K) 10 b) *
            geCount (L := L) (K := K) 10 b : ℕ)) /
              ((n : ℝ) * ((n : ℝ) - 1))) := by
  intro m b hb hbm
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hzero : n - geCount (L := L) (K := K) 10 b = 0 := by
      simpa [spreadPot] using hbm
    rw [hzero]
    simp only [Nat.zero_mul, Nat.cast_zero, zero_div,
      ENNReal.ofReal_zero, tsub_zero]
    exact MeasureTheory.prob_le_one
  · have hadv := ge10_advance_prob (L := L) (K := K) n hn b hb.1
    have hsub :
        {c' | geCount (L := L) (K := K) 10 b + 1 ≤
          geCount (L := L) (K := K) 10 c'} ⊆
        Engine.potBelow (spreadPot (L := L) (K := K) n) m := by
      intro c' hc'
      simp only [Set.mem_setOf_eq] at hc'
      change spreadPot (L := L) (K := K) n c' < m
      have hle : geCount (L := L) (K := K) 10 b ≤ n := by
        unfold geCount
        rw [← hb.1]
        exact Multiset.countP_le_card _ _
      simp only [spreadPot] at hbm ⊢
      by_cases hc'le : geCount (L := L) (K := K) 10 c' ≤ n
      · have hbsub :
            n - geCount (L := L) (K := K) 10 b +
                geCount (L := L) (K := K) 10 b = n :=
          Nat.sub_add_cancel hle
        have hcsub :
            n - geCount (L := L) (K := K) 10 c' +
                geCount (L := L) (K := K) 10 c' = n :=
          Nat.sub_add_cancel hc'le
        omega
      · have hzero : n - geCount (L := L) (K := K) 10 c' = 0 := by
          omega
        omega
    have hmono :
        ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
            {c' | geCount (L := L) (K := K) 10 b + 1 ≤
              geCount (L := L) (K := K) 10 c'} ≤
          ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
            (Engine.potBelow (spreadPot (L := L) (K := K) n) m) :=
      measure_mono hsub
    have hadv' : ENNReal.ofReal
          ((((n - geCount (L := L) (K := K) 10 b) *
            geCount (L := L) (K := K) 10 b : ℕ)) /
              ((n : ℝ) * ((n : ℝ) - 1))) ≤
        ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
          {c' | geCount (L := L) (K := K) 10 b + 1 ≤
            geCount (L := L) (K := K) 10 c'} := by
      simpa [Nat.mul_comm] using hadv
    have hrate : ENNReal.ofReal
          ((((n - geCount (L := L) (K := K) 10 b) *
            geCount (L := L) (K := K) 10 b : ℕ)) /
              ((n : ℝ) * ((n : ℝ) - 1))) ≤
        (NonuniformMajority L K).transitionKernel b
          (Engine.potBelow (spreadPot (L := L) (K := K) n) m) :=
      le_trans hadv' hmono
    have hmeas : MeasurableSet
        (Engine.potBelow (spreadPot (L := L) (K := K) n) m) :=
      Engine.potBelow_measurable _ _
    rw [MeasureTheory.prob_compl_eq_one_sub hmeas]
    exact tsub_le_tsub_left hrate 1

/-- The global seed epidemic reaches the all-Phase-10 count surface in expected
at most `n²` interactions. -/
theorem spread_expectedHitting_le_nsq (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hc : SpreadInv (L := L) (K := K) n c) :
    expectedHitting (NonuniformMajority L K).transitionKernel c
        (Engine.potBelow (spreadPot (L := L) (K := K) n) 1) ≤
      ((n * n : ℕ) : ℝ≥0∞) := by
  have hstart : spreadPot (L := L) (K := K) n c ≤ n - 1 := by
    unfold spreadPot
    have hseed := hc.2
    omega
  have hkey :
      expectedHitting (NonuniformMajority L K).transitionKernel c
          (Engine.potBelow (spreadPot (L := L) (K := K) n) 1) ≤
        ((n - 1 : ℕ) : ℝ≥0∞) * (n : ℝ≥0∞) :=
    Engine.coupon_expectedHitting_le_uniform_on
      (NonuniformMajority L K).transitionKernel
      (SpreadInv (L := L) (K := K) n)
      (SpreadInv_closed (L := L) (K := K) n)
      (spreadPot (L := L) (K := K) n)
      (spreadPot_nonincr (L := L) (K := K) n)
      (TimedChainRungs.advanceQ n)
      (by
        intro m b hb hbm
        have h := spread_hdrop_raw (L := L) (K := K) n hn m b hb hbm
        have hle : geCount (L := L) (K := K) 10 b ≤ n := by
          unfold geCount
          rw [← hb.1]
          exact Multiset.countP_le_card _ _
        have hm1 : n - geCount (L := L) (K := K) 10 b = m := by
          simpa [spreadPot] using hbm
        have hm2 : geCount (L := L) (K := K) 10 b = n - m := by omega
        unfold TimedChainRungs.advanceQ
        rw [hm1, hm2] at h
        simpa [Nat.mul_comm] using h)
      (n - 1) c hstart hc (n : ℝ≥0∞)
      (fun m hm1 hmn =>
        TimedChainRungs.advanceQ_inv_le n hn m hm1 hmn)
  refine le_trans hkey ?_
  calc
    ((n - 1 : ℕ) : ℝ≥0∞) * (n : ℝ≥0∞)
        ≤ (n : ℝ≥0∞) * (n : ℝ≥0∞) := by
          gcongr
          exact_mod_cast Nat.sub_le n 1
    _ = ((n * n : ℕ) : ℝ≥0∞) := by push_cast; ring

/-! ## Reachability-scoped bridge to the exact ready surface -/

/-- On a reachable card-`n` slice from a recovery entry, the drained spread
target is a genuine `Phase10Ready` state, including activity in the tie case. -/
theorem reachable_spread_target_is_ready (n : ℕ)
    (root y : Config (AgentState L K))
    (hentry : Phase2EntryDispatcher.Recovery10Entry
      (L := L) (K := K) n root)
    (hreach : (NonuniformMajority L K).Reachable root y)
    (hy : y ∈ Engine.potBelow (spreadPot (L := L) (K := K) n) 1) :
    Phase10Drop.Phase10Ready (L := L) (K := K) n y := by
  rcases hentry with ⟨hcard, a, ha, haPhase, haFull, haBad⟩
  have hycard : y.card = n := by
    rw [Protocol.reachable_card_eq (P := NonuniformMajority L K) hreach]
    exact hcard
  have hyAll : Phase10Drop.AllPhase10 y := by
    have hfin : TimedChainRungs.advancePot
        (L := L) (K := K) 9 n y < 1 := by
      have hy' : spreadPot (L := L) (K := K) n y < 1 := hy
      simpa [TimedChainRungs.advancePot, spreadPot] using hy'
    exact BackupEntry.advancePot_nine_drained_imp_allPhase10
      (L := L) (K := K) n y hycard hfin
  have hactiveRoot : hasActiveAgent root := ⟨a, ha, haFull⟩
  have hyActive : hasActiveAgent y := by
    by_cases hrootAll : Phase10Drop.AllPhase10 root
    · exact (SeedStepAndSignThreading.hasActiveAgent_of_reachable
        (L := L) (K := K) hreach hrootAll hactiveRoot).1
    · exact Phase2EntryDispatcher.hasActiveAgent_of_reachable_allPhase10_of_not_allPhase10
        (L := L) (K := K) hreach hrootAll hyAll
  exact Phase2EntryDispatcher.phase10Ready_of_allPhase10_card_active
    (L := L) (K := K) n y hyAll hycard hyActive

/-- **Quantitative initializer-error recovery.**  One active Phase-10 seed
reaches the exact existing `Phase10Ready` work surface in expected at most
`n²` interactions. -/
theorem recovery10Entry_expectedHitting_ready_le_nsq
    (n : ℕ) (hn : 2 ≤ n) (root : Config (AgentState L K))
    (hentry : Phase2EntryDispatcher.Recovery10Entry
      (L := L) (K := K) n root) :
    expectedHitting (NonuniformMajority L K).transitionKernel root
        {y | Phase10Drop.Phase10Ready (L := L) (K := K) n y} ≤
      ((n * n : ℕ) : ℝ≥0∞) := by
  classical
  set ker := (NonuniformMajority L K).transitionKernel
  set J : Config (AgentState L K) → Prop :=
    fun y => (NonuniformMajority L K).Reachable root y
  set Bare : Set (Config (AgentState L K)) :=
    Engine.potBelow (spreadPot (L := L) (K := K) n) 1
  set Ready : Set (Config (AgentState L K)) :=
    {y | Phase10Drop.Phase10Ready (L := L) (K := K) n y}
  have hInvRoot : SpreadInv (L := L) (K := K) n root := by
    refine ⟨hentry.1, ?_⟩
    rcases hentry.2 with ⟨a, ha, haPhase, _haFull, _haBad⟩
    unfold geCount
    exact Multiset.countP_pos.mpr ⟨a, ha, by
      simp only [geP]
      omega⟩
  have hbare : expectedHitting ker root Bare ≤
      ((n * n : ℕ) : ℝ≥0∞) := by
    simpa [ker, Bare] using
      spread_expectedHitting_le_nsq
        (L := L) (K := K) n hn root hInvRoot
  have hJclosed : ∀ b, J b → ker b {x | ¬ J x} = 0 := by
    intro b hb
    change ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
        {x | ¬ J x} = 0
    rw [PMF.toMeasure_apply_eq_zero_iff _
      (DiscreteMeasurableSpace.forall_measurableSet _)]
    rw [Set.disjoint_left]
    intro x hx hnot
    apply hnot
    exact Relation.ReflTransGen.trans hb
      (Protocol.stepDistOrSelf_support_reachable
        (NonuniformMajority L K) b x hx)
  have hJroot : J root := Relation.ReflTransGen.refl
  have hpowJ : ∀ t : ℕ, (ker ^ t) root {x | ¬ J x} = 0 :=
    fun t => Engine.pow_not_inv_eq_zero ker J hJclosed root hJroot t
  have hslice : ∀ t : ℕ,
      (ker ^ t) root (Readyᶜ) ≤ (ker ^ t) root (Bareᶜ) := by
    intro t
    have hsub : (Readyᶜ : Set (Config (AgentState L K))) ⊆
        Bareᶜ ∪ {x | ¬ J x} := by
      intro y hy
      by_cases hyJ : J y
      · left
        intro hyBare
        exact hy (reachable_spread_target_is_ready
          (L := L) (K := K) n root y hentry hyJ hyBare)
      · right
        exact hyJ
    calc
      (ker ^ t) root (Readyᶜ) ≤
          (ker ^ t) root (Bareᶜ ∪ {x | ¬ J x}) := measure_mono hsub
      _ ≤ (ker ^ t) root (Bareᶜ) +
          (ker ^ t) root {x | ¬ J x} := measure_union_le _ _
      _ = (ker ^ t) root (Bareᶜ) := by rw [hpowJ t, add_zero]
  calc
    expectedHitting ker root Ready =
        ∑' t : ℕ, (ker ^ t) root (Readyᶜ) :=
      expectedHitting_eq_tsum ker root Ready
    _ ≤ ∑' t : ℕ, (ker ^ t) root (Bareᶜ) :=
      ENNReal.tsum_le_tsum hslice
    _ = expectedHitting ker root Bare :=
      (expectedHitting_eq_tsum ker root Bare).symm
    _ ≤ ((n * n : ℕ) : ℝ≥0∞) := hbare

#print axioms ge10_advance_prob
#print axioms spread_expectedHitting_le_nsq
#print axioms recovery10Entry_expectedHitting_ready_le_nsq

end Recovery10EntryTime
end Ripple.PopulationProtocol.ExactMajority
