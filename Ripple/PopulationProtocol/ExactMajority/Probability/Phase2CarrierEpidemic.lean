/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase-2 branch-carrier epidemic

The strict Phase-2 branches enter with every opinion compatible with one fixed
verdict and at least one opinion carrying its surviving sign.  Opinion union
then runs an ordinary push epidemic: a carrier/non-carrier interaction leaves
both selected agents as carriers.  This file packages that epidemic at the
canonical `O(n log n)` Janson horizon.

The tie branch needs no epidemic: its public precondition already fixes every
opinion to the exact tie code.  It is nevertheless exposed through the same
horizon and budget, so downstream outcome assembly has one branch-generic
interface.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase2OutputCleanup
import Ripple.PopulationProtocol.ExactMajority.Probability.TightEpidemicWork
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase5Convergence

namespace Ripple.PopulationProtocol.ExactMajority
namespace Phase2CarrierEpidemic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Real

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-- Opinion-bitset compatibility with a fixed Phase-2 verdict branch. -/
def opinionCompatible (out : Output) (o : Fin 8) : Prop :=
  match out with
  | .A => hasMinusOne o = false
  | .B => hasPlusOne o = false
  | .T => o = phase2OpinionT

/-- The selected strict verdict sign is present in an opinion bitset. -/
def opinionCarrier (out : Output) (o : Fin 8) : Prop :=
  match out with
  | .A => hasPlusOne o = true
  | .B => hasMinusOne o = true
  | .T => False

/-- Two opinions compatible with one verdict cannot trigger Phase 2's
conflicting-sign advance branch after union. -/
theorem opinionCompatible_union_not_conflicting
    (out : Output) (u v : Fin 8)
    (hu : opinionCompatible out u) (hv : opinionCompatible out v) :
    (hasMinusOne (opinionsUnion u v) &&
        hasPlusOne (opinionsUnion u v)) = false := by
  cases out <;> fin_cases u <;> fin_cases v <;>
    simp [opinionCompatible, phase2OpinionT, opinionsUnion,
      hasMinusOne, hasPlusOne] at hu hv ⊢

/-- Public branch-generic Phase-2 carrier-epidemic input surface. -/
def Phase2BranchPre (out : Output) (n : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧
    (∀ a ∈ c, a.phase.val = 2 ∧ opinionCompatible out a.opinions) ∧
      match out with
      | .A | .B => ∃ a ∈ c, opinionCarrier out a.opinions
      | .T => True

/-- Same-phase Phase-2 interactions do not run any phase initializer. -/
private theorem phaseEpidemicUpdate_eq_self_of_phase2
    (s t : AgentState L K) (hs : s.phase.val = 2) (ht : t.phase.val = 2) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hs_eq : s.phase = ⟨2, by decide⟩ := Fin.ext hs
  have ht_eq : t.phase = ⟨2, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hs_eq, ht_eq, max_self]
  simp only [runInitsBetween_self]
  cases s
  cases t
  simp_all

/-- Number of agents whose Phase-2 opinion contains the selected strict sign. -/
noncomputable def carrierCount (out : Output)
    (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP
    (fun a => opinionCarrier out a.opinions) c

/-- The exact pointwise surface retained during strict-branch propagation. -/
def StrictInv (out : Output) (n : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧
    (∀ a ∈ c, a.phase.val = 2 ∧
      opinionCompatible out a.opinions) ∧
    1 ≤ carrierCount out c

/-- Compatibility excludes the Phase-2 advance branch, and opinion union
copies any selected carrier to both endpoints. -/
theorem Transition_phase2_carrier_pair
    (out : Output) (s t : AgentState L K)
    (hs2 : s.phase.val = 2) (ht2 : t.phase.val = 2)
    (hs : opinionCompatible out s.opinions)
    (ht : opinionCompatible out t.opinions) :
    ((Transition L K s t).1.phase.val = 2 ∧
        opinionCompatible out (Transition L K s t).1.opinions) ∧
      ((Transition L K s t).2.phase.val = 2 ∧
        opinionCompatible out (Transition L K s t).2.opinions) ∧
      (opinionCarrier out s.opinions ∨
          opinionCarrier out t.opinions →
        opinionCarrier out (Transition L K s t).1.opinions ∧
          opinionCarrier out (Transition L K s t).2.opinions) := by
  have hepi := phaseEpidemicUpdate_eq_self_of_phase2
    (L := L) (K := K) s t hs2 ht2
  have hsp : s.phase = ⟨2, by decide⟩ := Fin.ext hs2
  have htp : t.phase = ⟨2, by decide⟩ := Fin.ext ht2
  cases out with
  | A =>
      generalize hsop : s.opinions = u at hs ⊢
      generalize htop : t.opinions = v at ht ⊢
      fin_cases u <;> fin_cases v <;>
        simp [Transition, hepi, hsp, htp, Phase2Transition,
          opinionCompatible, opinionCarrier,
          opinionsUnion, hasMinusOne, hasPlusOne, hsop, htop,
          finishPhase10Entry, canonicalPhase10Entry] at hs ht ⊢
  | B =>
      generalize hsop : s.opinions = u at hs ⊢
      generalize htop : t.opinions = v at ht ⊢
      fin_cases u <;> fin_cases v <;>
        simp [Transition, hepi, hsp, htp, Phase2Transition,
          opinionCompatible, opinionCarrier,
          opinionsUnion, hasMinusOne, hasPlusOne, hsop, htop,
          finishPhase10Entry, canonicalPhase10Entry] at hs ht ⊢
  | T =>
      have hsSign : Phase2OutputCleanup.Phase2SignState .T s := by
        exact ⟨hs2, by simpa [opinionCompatible] using hs⟩
      have htSign : Phase2OutputCleanup.Phase2SignState .T t := by
        exact ⟨ht2, by simpa [opinionCompatible] using ht⟩
      have hpair := Phase2OutputCleanup.Transition_phase2_sign_pair
        (L := L) (K := K) .T s t hsSign htSign
      exact ⟨
        ⟨hpair.1.1.1, by simpa [opinionCompatible] using hpair.1.1.2⟩,
        ⟨hpair.2.1.1, by simpa [opinionCompatible] using hpair.2.1.2⟩,
        by simp [opinionCarrier]⟩

/-- Replacing an applicable pair preserves the pointwise Phase-2 compatibility
surface. -/
theorem StrictInv_pointwise_stepOrSelf
    (out : Output) (n : ℕ) (c : Config (AgentState L K))
    (hInv : StrictInv out n c) (s t : AgentState L K) :
    ∀ a ∈ Protocol.stepOrSelf (NonuniformMajority L K) c s t,
      a.phase.val = 2 ∧ opinionCompatible out a.opinions := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs_mem : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht_mem : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hpair := Transition_phase2_carrier_pair out s t
      (hInv.2.1 s hs_mem).1 (hInv.2.1 t ht_mem).1
      (hInv.2.1 s hs_mem).2 (hInv.2.1 t ht_mem).2
    have hc' :
        Protocol.stepOrSelf (NonuniformMajority L K) c s t =
          c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    rw [hc']
    intro a ha
    have ha' :
        a = (Transition L K s t).1 ∨ a ∈ c - {s, t} ∨
          a = (Transition L K s t).2 := by
      simpa using ha
    rcases ha' with rfl | haold | rfl
    · exact hpair.1
    · exact hInv.2.1 a
        (Multiset.mem_of_le (Multiset.sub_le_self c {s, t}) haold)
    · exact hpair.2.1
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]
    exact hInv.2.1

/-- The carrier count never decreases on the strict compatibility surface. -/
theorem carrierCount_stepOrSelf_le
    (out : Output) (n : ℕ) (c : Config (AgentState L K))
    (hInv : StrictInv out n c) (s t : AgentState L K) :
    carrierCount out c ≤
      carrierCount out
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  by_cases happ : Protocol.Applicable c s t
  · have hs_mem : s ∈ c := Multiset.mem_of_le happ (by simp)
    have ht_mem : t ∈ c := Multiset.mem_of_le happ (by simp)
    have hpair := Transition_phase2_carrier_pair out s t
      (hInv.2.1 s hs_mem).1 (hInv.2.1 t ht_mem).1
      (hInv.2.1 s hs_mem).2 (hInv.2.1 t ht_mem).2
    have hc' :
        Protocol.stepOrSelf (NonuniformMajority L K) c s t =
          c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
      unfold Protocol.stepOrSelf
      rw [if_pos happ]
      rfl
    have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
    have hsplit : carrierCount out c =
        carrierCount out (c - {s, t}) +
          Multiset.countP
            (fun a => opinionCarrier out a.opinions)
            ({s, t} : Multiset (AgentState L K)) := by
      unfold carrierCount
      rw [← Multiset.countP_add, Multiset.sub_add_cancel hsub]
    unfold carrierCount at hsplit
    unfold carrierCount
    rw [hc', Multiset.countP_add]
    rw [hsplit]
    rw [show ({s, t} : Multiset (AgentState L K)) = s ::ₘ t ::ₘ 0 from rfl,
      show ({(Transition L K s t).1, (Transition L K s t).2} :
        Multiset (AgentState L K)) =
          (Transition L K s t).1 ::ₘ (Transition L K s t).2 ::ₘ 0 from rfl]
    rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero,
      Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
    by_cases hsCarrier : opinionCarrier out s.opinions <;>
      by_cases htCarrier : opinionCarrier out t.opinions
    · have hout := hpair.2.2 (Or.inl hsCarrier)
      simp [hsCarrier, htCarrier, hout.1, hout.2]
    · have hout := hpair.2.2 (Or.inl hsCarrier)
      simp [hsCarrier, htCarrier, hout.1, hout.2]
    · have hout := hpair.2.2 (Or.inr htCarrier)
      simp [hsCarrier, htCarrier, hout.1, hout.2]
    · simp [hsCarrier, htCarrier]
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- A selected carrier/non-carrier pair raises the global carrier count by one. -/
theorem carrierCount_stepOrSelf_advance
    (out : Output) (n : ℕ) (c : Config (AgentState L K))
    (hInv : StrictInv out n c) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hsCarrier : opinionCarrier out s.opinions)
    (htCarrier : ¬ opinionCarrier out t.opinions) :
    carrierCount out c + 1 ≤
      carrierCount out
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  have hs_mem : s ∈ c := Multiset.mem_of_le happ (by simp)
  have ht_mem : t ∈ c := Multiset.mem_of_le happ (by simp)
  have hpair := Transition_phase2_carrier_pair out s t
    (hInv.2.1 s hs_mem).1 (hInv.2.1 t ht_mem).1
    (hInv.2.1 s hs_mem).2 (hInv.2.1 t ht_mem).2
  have hout := hpair.2.2 (Or.inl hsCarrier)
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hc' :
      Protocol.stepOrSelf (NonuniformMajority L K) c s t =
        c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  unfold carrierCount
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  have hpair_le :
      Multiset.countP
          (fun a : AgentState L K =>
            opinionCarrier out a.opinions) {s, t} ≤
        Multiset.countP
          (fun a : AgentState L K =>
            opinionCarrier out a.opinions) c :=
    Multiset.countP_le_of_le
    (fun a : AgentState L K =>
      opinionCarrier out a.opinions) hsub
  have hold :
      Multiset.countP
          (fun a : AgentState L K =>
            opinionCarrier out a.opinions) {s, t} = 1 := by
    rw [show ({s, t} : Multiset (AgentState L K)) = s ::ₘ t ::ₘ 0 from rfl,
      Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
    simp [hsCarrier, htCarrier]
  have hnew :
      Multiset.countP
          (fun a : AgentState L K =>
            opinionCarrier out a.opinions)
          {(Transition L K s t).1, (Transition L K s t).2} = 2 := by
    rw [show ({(Transition L K s t).1, (Transition L K s t).2} :
        Multiset (AgentState L K)) =
          (Transition L K s t).1 ::ₘ (Transition L K s t).2 ::ₘ 0 from rfl,
      Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
    simp [hout.1, hout.2]
  rw [hold] at hpair_le
  rw [hnew]
  omega

/-- The strict invariant is preserved by every scheduled pair. -/
theorem StrictInv_stepOrSelf
    (out : Output) (n : ℕ) (c : Config (AgentState L K))
    (hInv : StrictInv out n c) (s t : AgentState L K) :
    StrictInv out n
      (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  refine ⟨?_, StrictInv_pointwise_stepOrSelf out n c hInv s t, ?_⟩
  · rw [Protocol.stepOrSelf_card_eq]
    exact hInv.1
  · exact le_trans hInv.2.2 (carrierCount_stepOrSelf_le out n c hInv s t)

/-- Strict-invariant closure along one deterministic protocol step. -/
theorem StrictInv_stepRel
    (out : Output) (n : ℕ) {c c' : Config (AgentState L K)}
    (hInv : StrictInv out n c)
    (hstep : (NonuniformMajority L K).StepRel c c') :
    StrictInv out n c' := by
  rcases hstep with ⟨s, t, happ, hc'⟩
  dsimp at hc'
  have heq :
      Protocol.stepOrSelf (NonuniformMajority L K) c s t = c' := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    exact hc'.symm
  rw [← heq]
  exact StrictInv_stepOrSelf out n c hInv s t

/-- The strict surface is closed along every finite execution. -/
theorem StrictInv_reachable
    (out : Output) (n : ℕ) {c c' : Config (AgentState L K)}
    (hInv : StrictInv out n c)
    (hreach : (NonuniformMajority L K).Reachable c c') :
    StrictInv out n c' := by
  induction hreach with
  | refl => exact hInv
  | tail _ hstep ih => exact StrictInv_stepRel out n ih hstep

/-- Carrier-count monotonicity along one deterministic protocol step. -/
theorem carrierCount_stepRel_le
    (out : Output) (n : ℕ) {c c' : Config (AgentState L K)}
    (hInv : StrictInv out n c)
    (hstep : (NonuniformMajority L K).StepRel c c') :
    carrierCount out c ≤ carrierCount out c' := by
  rcases hstep with ⟨s, t, happ, hc'⟩
  dsimp at hc'
  have heq :
      Protocol.stepOrSelf (NonuniformMajority L K) c s t = c' := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    exact hc'.symm
  rw [← heq]
  exact carrierCount_stepOrSelf_le out n c hInv s t

/-- Carrier-count monotonicity along every finite execution. -/
theorem carrierCount_reachable_le
    (out : Output) (n : ℕ) {c c' : Config (AgentState L K)}
    (hInv : StrictInv out n c)
    (hreach : (NonuniformMajority L K).Reachable c c') :
    carrierCount out c ≤ carrierCount out c' := by
  induction hreach with
  | refl => exact le_rfl
  | @tail b d hprefix hstep ih =>
      exact le_trans ih
        (carrierCount_stepRel_le out n
          (StrictInv_reachable out n hInv hprefix) hstep)

/-- Scheduler-support form of strict-invariant closure. -/
theorem StrictInv_of_stepDistOrSelf_support
    (out : Output) (n : ℕ) (c c' : Config (AgentState L K))
    (hInv : StrictInv out n c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    StrictInv out n c' :=
  StrictInv_reachable out n hInv
    (Protocol.stepDistOrSelf_support_reachable
      (NonuniformMajority L K) c c' hsupp)

/-- Scheduler-support form of carrier-count monotonicity. -/
theorem carrierCount_of_stepDistOrSelf_support_le
    (out : Output) (n : ℕ) (c c' : Config (AgentState L K))
    (hInv : StrictInv out n c)
    (hsupp : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    carrierCount out c ≤ carrierCount out c' :=
  carrierCount_reachable_le out n hInv
    (Protocol.stepDistOrSelf_support_reachable
      (NonuniformMajority L K) c c' hsupp)

/-! ## Carrier/non-carrier rectangle -/

/-- Sum of occurrence counts over a decidable state predicate. -/
private theorem sum_count_filter_eq_countP
    (p : AgentState L K → Prop) [DecidablePred p]
    (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter p, c.count a) = Multiset.countP p c := by
  classical
  calc
    (∑ a ∈ Finset.univ.filter p, c.count a)
        = ∑ a : AgentState L K, if p a then c.count a else 0 :=
          Finset.sum_filter _ _
    _ = ∑ a : AgentState L K, (c.filter p).count a := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      show _ = Multiset.count a (c.filter p)
      rw [Multiset.count_filter]
      rfl
    _ = (c.filter p).card :=
      Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)
    _ = Multiset.countP p c := (Multiset.countP_eq_card_filter _ _).symm

/-- Every occurrence is either a carrier or a non-carrier. -/
private theorem carrierCount_add_noncarrierCount
    (out : Output) (c : Config (AgentState L K)) :
    carrierCount out c +
        Multiset.countP
          (fun a : AgentState L K =>
            ¬ opinionCarrier out a.opinions) c =
      c.card := by
  classical
  induction c using Multiset.induction_on with
  | empty => simp [carrierCount]
  | @cons a c ih =>
      unfold carrierCount at ih ⊢
      rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.card_cons]
      by_cases h : opinionCarrier out a.opinions <;>
        simp [h] at ih ⊢ <;> omega

/-- States carrying the selected branch sign. -/
noncomputable def carrierStates (out : Output) : Finset (AgentState L K) :=
  Finset.univ.filter
    (fun a => opinionCarrier out a.opinions)

/-- States not yet carrying the selected branch sign. -/
noncomputable def noncarrierStates (out : Output) : Finset (AgentState L K) :=
  Finset.univ.filter
    (fun a => ¬ opinionCarrier out a.opinions)

theorem carrierStates_noncarrierStates_disjoint
    (out : Output) (a : AgentState L K) (ha : a ∈ carrierStates out)
    (b : AgentState L K) (hb : b ∈ noncarrierStates out) : a ≠ b := by
  simp only [carrierStates, noncarrierStates, Finset.mem_filter] at ha hb
  intro hab
  subst b
  exact hb.2 ha.2

/-- Exact scheduler mass of the one-way carrier/non-carrier rectangle. -/
theorem sum_interactionCount_carrierRect
    (out : Output) (c : Config (AgentState L K)) :
    (∑ p ∈ carrierStates (L := L) (K := K) out ×ˢ
        noncarrierStates (L := L) (K := K) out,
        c.interactionCount p.1 p.2) =
      carrierCount out c * (c.card - carrierCount out c) := by
  classical
  rw [Phase5Convergence.sum_interactionCount_cross_disjoint5 c _ _
      (carrierStates_noncarrierStates_disjoint out),
    carrierStates, noncarrierStates,
    sum_count_filter_eq_countP, sum_count_filter_eq_countP]
  have hsplit := carrierCount_add_noncarrierCount out c
  have hle : carrierCount out c ≤ c.card := by
    unfold carrierCount
    exact Multiset.countP_le_card _ _
  have hnon :
      Multiset.countP
          (fun a : AgentState L K =>
            ¬ opinionCarrier out a.opinions) c =
        c.card - carrierCount out c := by
    omega
  rw [hnon]
  rfl

/-- Genuine one-step rumor rate on the strict Phase-2 surface. -/
theorem carrier_advance_prob
    (out : Output) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : StrictInv out n c) :
    ENNReal.ofReal
        (((carrierCount out c * (n - carrierCount out c) : ℕ) : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | carrierCount out c + 1 ≤ carrierCount out c'} := by
  classical
  set R := carrierStates (L := L) (K := K) out ×ˢ
    noncarrierStates (L := L) (K := K) out with hR
  refine Phase5Convergence.rise_prob_of_rect5
    (carrierCount (L := L) (K := K) out) n hn c hInv.1 R
      (carrierCount out c * (n - carrierCount out c)) ?_ ?_
  · rintro ⟨s, t⟩ hp hsCount htCount _hsame
    rw [hR, Finset.mem_product, carrierStates, noncarrierStates,
      Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨_, hsCarrier⟩, ⟨_, htCarrier⟩⟩ := hp
    have hs_mem : s ∈ c := Multiset.one_le_count_iff_mem.mp hsCount
    have ht_mem : t ∈ c := Multiset.one_le_count_iff_mem.mp htCount
    have hne : s ≠ t := by
      intro hst
      subst t
      exact htCarrier hsCarrier
    have happ : Protocol.Applicable c s t :=
      Phase5Convergence.applicable_of_mem_distinct5 hs_mem ht_mem hne
    exact carrierCount_stepOrSelf_advance out n c hInv s t happ hsCarrier htCarrier
  · rw [hR, sum_interactionCount_carrierRect, hInv.1]

/-! ## Canonical milestone phase -/

/-- A strict public branch precondition supplies the pointwise invariant and
the initial carrier floor. -/
theorem strictInv_of_pre
    (out : Output) (n : ℕ) (hout : out ≠ .T)
    (c : Config (AgentState L K))
    (hPre : Phase2BranchPre out n c) :
    StrictInv out n c := by
  refine ⟨hPre.1, hPre.2.1, ?_⟩
  cases out with
  | A =>
      rcases hPre.2.2 with ⟨a, ha, hcarrier⟩
      unfold carrierCount
      exact Multiset.countP_pos_of_mem ha hcarrier
  | B =>
      rcases hPre.2.2 with ⟨a, ha, hcarrier⟩
      unfold carrierCount
      exact Multiset.countP_pos_of_mem ha hcarrier
  | T => exact (hout rfl).elim

/-- Carrier-count milestone `i`: at least `i+2` carriers, guarded by the
closed strict Phase-2 surface. -/
def milestone (out : Output) (n i : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  StrictInv out n c ∧ i + 2 ≤ carrierCount out c

/-- Canonical push-epidemic milestones for a fixed strict Phase-2 branch. -/
noncomputable def milestonePhase
    (out : Output) (n : ℕ) (hn : 2 ≤ n) :
    RoleSplitConcentration.MilestonePhaseOn
      (L := L) (K := K) (NonuniformMajority L K) where
  k := n - 1
  milestone i c := milestone (L := L) (K := K) out n i.val c
  p i := Phase2Time.epP n i.val
  hp_pos i := Phase2Time.epP_pos hn (by have := i.isLt; omega)
  hp_le_one i := Phase2Time.epP_le_one hn (by have := i.isLt; omega)
  milestone_monotone := by
    intro i c c' h hsupp
    exact ⟨
      StrictInv_of_stepDistOrSelf_support out n c c' h.1 hsupp,
      le_trans h.2
        (carrierCount_of_stepDistOrSelf_support_le out n c c' h.1 hsupp)⟩
  Inv := StrictInv out n
  inv_closed := by
    intro c hInv
    change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {c' | ¬ StrictInv out n c'} = 0
    rw [PMF.toMeasure_apply_eq_zero_iff
      (p := (NonuniformMajority L K).stepDistOrSelf c)
      (DiscreteMeasurableSpace.forall_measurableSet _)]
    rw [Set.disjoint_left]
    intro c' hsupp hbad
    exact hbad (StrictInv_of_stepDistOrSelf_support out n c c' hInv hsupp)
  progress_on := by
    intro i c hInv hprev hcur
    have hcount_eq : carrierCount out c = i.val + 1 := by
      have hlt : carrierCount out c < i.val + 2 :=
        Nat.lt_of_not_ge (fun hge => hcur ⟨hInv, hge⟩)
      have hge : i.val + 1 ≤ carrierCount out c := by
        by_cases hi0 : i.val = 0
        · rw [hi0]
          exact hInv.2.2
        · have hprev' := hprev ⟨i.val - 1, by omega⟩ (by
            exact Fin.mk_lt_mk.mpr (by omega))
          have hprev_cov :
              (i.val - 1) + 2 ≤ carrierCount out c := hprev'.2
          omega
      omega
    have hbound := carrier_advance_prob out n hn c hInv
    have heq :
        ((((carrierCount out c * (n - carrierCount out c) : ℕ) : ℝ) /
          ((n : ℝ) * ((n : ℝ) - 1)))) = Phase2Time.epP n i.val := by
      rw [hcount_eq]
      unfold Phase2Time.epP
      have hi1_le : i.val + 1 ≤ n := by
        have := i.isLt
        omega
      rw [Nat.cast_mul, Nat.cast_sub hi1_le, Nat.cast_add, Nat.cast_one]
    rw [heq] at hbound
    set A := {c' : Config (AgentState L K) |
      i.val + 2 ≤ carrierCount out c'}
    set M := {c' : Config (AgentState L K) |
      milestone (L := L) (K := K) out n i.val c'}
    have hA_le_M :
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A ≤
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure M := by
      have hsub :
          A ⊆ M ∪ {c' : Config (AgentState L K) | ¬ StrictInv out n c'} := by
        intro x hx
        by_cases hxInv : StrictInv out n x
        · left
          exact ⟨hxInv, hx⟩
        · right
          exact hxInv
      have hclosed :
          ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
            {c' : Config (AgentState L K) | ¬ StrictInv out n c'} = 0 := by
        rw [PMF.toMeasure_apply_eq_zero_iff
          (p := (NonuniformMajority L K).stepDistOrSelf c)
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]
        intro c' hsupp hbad
        exact hbad
          (StrictInv_of_stepDistOrSelf_support out n c c' hInv hsupp)
      calc
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A
            ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
                (M ∪ {c' : Config (AgentState L K) | ¬ StrictInv out n c'}) :=
              measure_mono hsub
        _ ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure M +
              ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
                {c' : Config (AgentState L K) | ¬ StrictInv out n c'} :=
              measure_union_le M _
        _ = ((NonuniformMajority L K).stepDistOrSelf c).toMeasure M := by
              rw [hclosed, add_zero]
    have hboundA : ENNReal.ofReal (Phase2Time.epP n i.val) ≤
        ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A := by
      simpa [A, hcount_eq, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hbound
    exact le_trans hboundA hA_le_M

theorem pMin_eq_epidemic (out : Output) (n : ℕ) (hn : 2 ≤ n) :
    (milestonePhase (L := L) (K := K) out n hn).pMin =
      (Phase2Time.epidemicMilestonePhase n hn).pMin := rfl

theorem meanTime_eq_epidemic (out : Output) (n : ℕ) (hn : 2 ≤ n) :
    (milestonePhase (L := L) (K := K) out n hn).meanTime =
      (Phase2Time.epidemicMilestonePhase n hn).meanTime := rfl

/-- Compatibility plus the selected sign is exactly the cleanup module's
pointwise sign-support predicate. -/
theorem Phase2SignState_of_compatible_carrier
    (out : Output) (a : AgentState L K)
    (hphase : a.phase.val = 2)
    (hcompat : opinionCompatible out a.opinions)
    (hcarrier : opinionCarrier out a.opinions) :
    Phase2OutputCleanup.Phase2SignState out a := by
  cases out with
  | A => exact ⟨hphase, hcarrier, hcompat⟩
  | B => exact ⟨hphase, hcarrier, hcompat⟩
  | T => simp [opinionCarrier] at hcarrier

/-- Reaching all carrier milestones yields the exact cleanup entry surface. -/
theorem post_imp_signsDone
    (out : Output) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K))
    (hPost : (milestonePhase (L := L) (K := K) out n hn).Post c) :
    Phase2OutputCleanup.Phase2SignsDone out n c := by
  let i : Fin ((milestonePhase (L := L) (K := K) out n hn).k) :=
    ⟨n - 2, by
      change n - 2 < n - 1
      omega⟩
  have hi := hPost i
  change milestone (L := L) (K := K) out n i.val c at hi
  have hival : i.val = n - 2 := rfl
  rw [hival] at hi
  have hcov : n ≤ carrierCount out c := by
    have := hi.2
    omega
  have hle : carrierCount out c ≤ c.card := by
    unfold carrierCount
    exact Multiset.countP_le_card _ _
  have hcount_eq :
      Multiset.countP
          (fun a : AgentState L K =>
            opinionCarrier out a.opinions) c = c.card := by
    unfold carrierCount at hcov hle
    rw [hi.1.1] at hle ⊢
    omega
  have hallCarrier :
      ∀ a ∈ c, opinionCarrier out a.opinions :=
    Multiset.countP_eq_card.mp hcount_eq
  refine ⟨hi.1.1, ?_⟩
  intro a ha
  exact Phase2SignState_of_compatible_carrier out a
    (hi.1.2.1 a ha).1 (hi.1.2.1 a ha).2 (hallCarrier a ha)

/-! ## Weak convergence packages -/

/-- Strict A/B branch carrier epidemic at the canonical tight horizon. -/
noncomputable def strictCarrierConvergence
    (out : Output) (n : ℕ) (hn : 2 ≤ n) (hout : out ≠ .T) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := Phase2BranchPre out n
  Post := Phase2OutputCleanup.Phase2SignsDone out n
  t := TightEpidemicWork.epiHorizonTight n hn
  ε := TightEpidemicWork.tightBudget n
  convergence := by
    intro c hPre
    set mp := milestonePhase (L := L) (K := K) out n hn with hmp
    have hInv : mp.Inv c := by
      rw [hmp]
      exact strictInv_of_pre out n hout c hPre
    have ht :
        (6 : ℝ) * mp.meanTime ≤
          (TightEpidemicWork.epiHorizonTight n hn : ℝ) := by
      rw [hmp]
      unfold TightEpidemicWork.epiHorizonTight
      exact Nat.le_ceil _
    have hj := mp.milestone_hitting_time_bound_on_partial c hInv 6
      (by norm_num) (TightEpidemicWork.epiHorizonTight n hn) ht
    have hexp :=
      TightEpidemicWork.epidemic_janson_exp_le_half_inv_sq
        (L := L) (K := K) mp n hn
        (by rw [hmp]; exact pMin_eq_epidemic out n hn)
        (by rw [hmp]; exact meanTime_eq_epidemic out n hn)
    have htail :
        ((NonuniformMajority L K).transitionKernel ^
            TightEpidemicWork.epiHorizonTight n hn) c
            {c' | ¬ mp.Post c'} ≤
          ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2)) :=
      le_trans hj (ENNReal.ofReal_le_ofReal hexp)
    have hsub :
        {c' : Config (AgentState L K) |
          ¬ Phase2OutputCleanup.Phase2SignsDone out n c'} ⊆
            {c' | ¬ mp.Post c'} := by
      intro c' hbad hpost
      exact hbad (by
        rw [hmp] at hpost
        exact post_imp_signsDone out n hn c' hpost)
    calc
      ((NonuniformMajority L K).transitionKernel ^
          TightEpidemicWork.epiHorizonTight n hn) c
          {c' | ¬ Phase2OutputCleanup.Phase2SignsDone out n c'}
          ≤ ((NonuniformMajority L K).transitionKernel ^
              TightEpidemicWork.epiHorizonTight n hn) c
              {c' | ¬ mp.Post c'} := measure_mono hsub
      _ ≤ ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2)) := htail
      _ = ((TightEpidemicWork.tightBudget n : ℝ≥0) : ℝ≥0∞) := by
        rw [TightEpidemicWork.tightBudget,
          ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal]
        positivity

/-- The tie precondition already is the exact cleanup support surface. -/
theorem tie_pre_imp_signsDone
    (n : ℕ) (c : Config (AgentState L K))
    (hPre : Phase2BranchPre .T n c) :
    Phase2OutputCleanup.Phase2SignsDone .T n c := by
  refine ⟨hPre.1, ?_⟩
  intro a ha
  have h := hPre.2.1 a ha
  simpa [Phase2OutputCleanup.Phase2SignState,
    opinionCompatible, phase2OpinionT] using h

/-- Tie branch embedded into the same public epidemic horizon and budget. -/
noncomputable def tieConvergence
    (n : ℕ) (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := Phase2BranchPre .T n
  Post := Phase2OutputCleanup.Phase2SignsDone .T n
  t := TightEpidemicWork.epiHorizonTight n hn
  ε := TightEpidemicWork.tightBudget n
  convergence := by
    intro c hPre
    have hInv := tie_pre_imp_signsDone n c hPre
    have hzero :
        ((NonuniformMajority L K).transitionKernel ^
            TightEpidemicWork.epiHorizonTight n hn) c
            {c' | ¬ Phase2OutputCleanup.Phase2SignsDone .T n c'} = 0 :=
      Protocol.transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved
        (NonuniformMajority L K)
        (Phase2OutputCleanup.Phase2SignsDone (L := L) (K := K) .T n)
        (fun c₀ c₁ hc hsupp =>
          Phase2OutputCleanup.Phase2SignsDone_of_stepDistOrSelf_support
            .T n hn c₀ c₁ hc hsupp)
        c hInv (TightEpidemicWork.epiHorizonTight n hn)
    rw [hzero]
    exact bot_le

/-- Branch-generic carrier epidemic from a Phase-2 verdict branch to the
Phase-2 output-cleanup entry surface. -/
noncomputable def phase2CarrierEpidemic
    (out : Output) (n : ℕ) (hn : 2 ≤ n) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := Phase2BranchPre out n
  Post := Phase2OutputCleanup.Phase2SignsDone out n
  t := TightEpidemicWork.epiHorizonTight n hn
  ε := TightEpidemicWork.tightBudget n
  convergence := by
    intro c hPre
    cases out with
    | A =>
        exact (strictCarrierConvergence (L := L) (K := K) .A n hn (by decide)).convergence
          c hPre
    | B =>
        exact (strictCarrierConvergence (L := L) (K := K) .B n hn (by decide)).convergence
          c hPre
    | T => exact (tieConvergence (L := L) (K := K) n hn).convergence c hPre

/-- The carrier epidemic fits the public `17 n (L+1)` phase allowance. -/
theorem phase2CarrierEpidemic_t_le_ht_of_logp1
    (out : Output) (n L' : ℕ) (hn : 2 ≤ n)
    (hlogp1 : Real.log (n : ℝ) + 1 ≤ (L' + 1 : ℝ)) :
    (phase2CarrierEpidemic (L := L) (K := K) out n hn).t ≤
      17 * n * (L' + 1) :=
  TightEpidemicWork.epiHorizonTight_le_ht_of_logp1 n L' hn hlogp1

/-- The public carrier-epidemic budget is half of `1/n²`. -/
theorem phase2CarrierEpidemic_epsilon_le_inv_sq
    (out : Output) (n : ℕ) (hn : 2 ≤ n) :
    (((phase2CarrierEpidemic (L := L) (K := K) out n hn).ε : ℝ≥0) : ℝ≥0∞) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 2) := by
  change ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2)) ≤
    ENNReal.ofReal (1 / (n : ℝ) ^ 2)
  apply ENNReal.ofReal_le_ofReal
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  apply one_div_le_one_div_of_le
  · positivity
  · have hsquare : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnpos
    nlinarith

/-- Exact public carrier-epidemic error budget. -/
theorem phase2CarrierEpidemic_epsilon_eq_half_inv_sq
    (out : Output) (n : ℕ) (hn : 2 ≤ n) :
    (((phase2CarrierEpidemic (L := L) (K := K) out n hn).ε : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2)) := by
  change ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2)) =
    ENNReal.ofReal (1 / (2 * (n : ℝ) ^ 2))
  rfl

#print axioms opinionCompatible_union_not_conflicting
#print axioms Transition_phase2_carrier_pair
#print axioms carrier_advance_prob
#print axioms milestonePhase
#print axioms strictCarrierConvergence
#print axioms tieConvergence
#print axioms phase2CarrierEpidemic
#print axioms phase2CarrierEpidemic_epsilon_eq_half_inv_sq

end Phase2CarrierEpidemic
end Ripple.PopulationProtocol.ExactMajority
