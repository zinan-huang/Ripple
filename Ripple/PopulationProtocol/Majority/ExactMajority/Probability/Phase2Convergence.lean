/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Avenue (f-untimed) — the FAITHFUL real-kernel Phase-2 opinion-union epidemic

This file builds a genuine `PhaseConvergence` for the **untimed Phase-2 opinion
epidemic** on the REAL `NonuniformMajority L K` kernel.  It is one of A1's 11
phase instances and is **clock-INDEPENDENT** — no `minute`/`hour`/`habs`
hypothesis appears anywhere.

## The mechanism (Phase 2 = opinion-set epidemic)

`Phase2Transition` sets both interacting agents' `opinions` to the bitwise union
`opinionsUnion` (Transition.lean:533).  This is a MONOTONE epidemic: the opinion
set only grows.  We work in the genuinely faithful **consensus (single-sign)
regime**, exactly the binary `Bool` epidemic of `Phase2TimeConvergence`
(`epidemicProto`) lifted to the real kernel:

* a fixed target opinion `U : Fin 8` with `singleSign U` (`U` carries at most one
  of the two signs), and a susceptible opinion `v` with `opinionsUnion v U = U`,
  `opinionsUnion v v = v` and `singleSign v`.  Single-sign-ness guarantees the
  union never contains BOTH signs, so the Phase-2 rule never fires its Phase-3
  advancement branch: agents stay in Phase 2 and just union opinions.  This is
  precisely the opinion-propagation regime (Doty et al. §6 Phases 2/9).

`U`-informed count `informedU U c = countP (opinions = U)` is the epidemic's
infected count; a susceptible (`opinions = v`) agent that meets a `U`-informed
agent becomes `U`-informed.

## What is derived (NOT assumed)

* `opinionAdvance_prob` — the per-step advance probability
  `≥ m·(n−m)/(n(n−1))` (`m = informedU`), DERIVED by `interactionCount`/
  `totalPairs` pair-counting over the informed×susceptible rectangle — the SAME
  derivation pattern as `ClockRealMixed.advance_prob_of_rect`/A0's
  `step_advance_prob`, but on the REAL kernel.
* `informedU_ge_monotone` — the informed count is non-decreasing on the step
  support inside the window.
* `phase2OpinionDrift` — the per-step contraction
  `∫⁻ Φ dK(c) ≤ r·Φ(c)` on the absorbing window, DERIVED from the above.
* `phase2Convergence` — the `PhaseConvergence` on `(NonuniformMajority L K)
  .transitionKernel`, built through `WindowConcentration.windowDrift_PhaseConvergence`.

## What is carried

Nothing beyond the window membership.  The window `Q2` (all agents in Phase 2,
all opinions in `{U, v}`, fixed size `n`) is PROVEN one-step closed
(`Q2_absorbing`) directly from `Phase2Transition`'s structure — there is no
deferred structural invariant, and no clock hypothesis.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WindowConcentration
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase2TimeConvergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.PhaseProgress

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace Phase2Convergence

variable {L K : ℕ}

/-- Discrete measurable structure on agent states (top σ-algebra), needed for the
`PMF`-to-measure pushforward in the rectangle advance-probability derivation.
Mirrors `ClockRealKernel.instMeasurableSpaceAgentState`. -/
noncomputable instance instMeasurableSpaceAgentState' :
    MeasurableSpace (AgentState L K) := ⊤

instance instDiscreteMeasurableSpaceAgentState' :
    DiscreteMeasurableSpace (AgentState L K) where
  forall_measurableSet _ := trivial

noncomputable instance instMeasurableSpaceAgentStateProd' :
    MeasurableSpace (AgentState L K × AgentState L K) := ⊤

instance instDiscreteMeasurableSpaceAgentStateProd' :
    DiscreteMeasurableSpace (AgentState L K × AgentState L K) :=
  ⟨fun _ => trivial⟩

/-! ## Part A — single-sign opinions and the consensus union algebra. -/

/-- An opinion set is *single-sign* if it does not carry BOTH the `+1` and the
`−1` sign.  In this regime the Phase-2 union never triggers the Phase-3
advancement branch (`hasMinusOne univ && hasPlusOne univ`), so the epidemic stays
in Phase 2 — exactly the opinion-propagation / consensus regime. -/
def singleSign (o : Fin 8) : Prop := ¬ (hasMinusOne o = true ∧ hasPlusOne o = true)

instance (o : Fin 8) : Decidable (singleSign o) := by unfold singleSign; infer_instance

/-- The union of two single-sign opinions whose union equals `U` (single-sign) is
single-sign — used to keep the advancement branch silent. -/
theorem singleSign_of_union_eq {u v U : Fin 8}
    (hU : singleSign U) (huv : opinionsUnion u v = U) : singleSign (opinionsUnion u v) := by
  rw [huv]; exact hU

/-- For a single-sign union the Phase-2 advancement branch is inert. -/
theorem not_both_signs_of_singleSign {o : Fin 8} (h : singleSign o) :
    (hasMinusOne o && hasPlusOne o) = false := by
  unfold singleSign at h
  by_cases hm : hasMinusOne o = true
  · by_cases hp : hasPlusOne o = true
    · exact absurd ⟨hm, hp⟩ h
    · simp [Bool.not_eq_true] at hp; simp [hp]
  · simp [Bool.not_eq_true] at hm; simp [hm]

/-! ## Part B — the informed count and the consensus window. -/

/-- An agent is `U`-informed if it is a Phase-2 agent holding exactly opinion `U`. -/
def informedP (U : Fin 8) (a : AgentState L K) : Prop := a.phase.val = 2 ∧ a.opinions = U

instance (U : Fin 8) (a : AgentState L K) : Decidable (informedP U a) := by
  unfold informedP; infer_instance

/-- The `U`-informed agent count. -/
def informedU (U : Fin 8) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => informedP U a) c

/-- An agent is `v`-susceptible if it is a Phase-2 agent holding exactly opinion `v`. -/
def susceptibleP (v : Fin 8) (a : AgentState L K) : Prop := a.phase.val = 2 ∧ a.opinions = v

instance (v : Fin 8) (a : AgentState L K) : Decidable (susceptibleP v a) := by
  unfold susceptibleP; infer_instance

/-- The consensus window for the binary epidemic with informed value `U` and
susceptible value `v`: every agent is a Phase-2 agent holding either `U` or `v`,
and the population has fixed size `n`.  This is genuinely one-step closed. -/
def Q2 (U v : Fin 8) (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∀ a ∈ c, a.phase.val = 2 ∧ (a.opinions = U ∨ a.opinions = v)

instance (U v : Fin 8) (n : ℕ) (c : Config (AgentState L K)) : Decidable (Q2 U v n c) := by
  unfold Q2; infer_instance

/-! ## Part C — the one-step behaviour of `Transition` on the window. -/

/-- On the window, every interacting pair is two Phase-2 agents whose opinions are
each `U` or `v`.  With `opinionsUnion v U = U` (single-sign) the union of any such
pair is again in `{U, v}` and is single-sign, so `Transition` keeps both outputs
in Phase 2 with opinions = the union.  This is the deterministic per-pair update
of the consensus epidemic. -/
theorem Transition_consensus_pair (U v : Fin 8)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (s t : AgentState L K)
    (hs2 : s.phase.val = 2) (ht2 : t.phase.val = 2)
    (hsop : s.opinions = U ∨ s.opinions = v)
    (htop : t.opinions = U ∨ t.opinions = v) :
    let s' := (Transition L K s t).1
    let t' := (Transition L K s t).2
    s'.phase.val = 2 ∧ t'.phase.val = 2 ∧
      (s'.opinions = U ∨ s'.opinions = v) ∧ (t'.opinions = U ∨ t'.opinions = v) ∧
      -- the union value of the pair:
      (s'.opinions = opinionsUnion s.opinions t.opinions) ∧
      (t'.opinions = opinionsUnion s.opinions t.opinions) := by
  intro s' t'
  -- phaseEpidemicUpdate is inert for two Phase-2 agents.
  have hs_phase_eq : s.phase = ⟨2, by decide⟩ := Fin.ext hs2
  have ht_phase_eq : t.phase = ⟨2, by decide⟩ := Fin.ext ht2
  have hepidemic : phaseEpidemicUpdate L K s t = (s, t) := by
    unfold phaseEpidemicUpdate
    rw [hs_phase_eq, ht_phase_eq, max_self]
    simp only [runInitsBetween_self_api]
    have hs_self : ({s with phase := (⟨2, by decide⟩ : Fin 11)} : AgentState L K) = s := by
      rw [← hs_phase_eq]
    have ht_self : ({t with phase := (⟨2, by decide⟩ : Fin 11)} : AgentState L K) = t := by
      rw [← ht_phase_eq]
    rw [hs_self, ht_self]
    rw [if_neg (by push Not; intro _; simp)]
  -- the union value
  set univ := opinionsUnion s.opinions t.opinions with huniv
  -- compute the union: it is U if either is U, else v (both v).
  have hunion_val : univ = U ∨ univ = v := by
    rcases hsop with hsU | hsv <;> rcases htop with htU | htv
    · left; rw [huniv, hsU, htU, hUU]
    · left; rw [huniv, hsU, htv, hUv]
    · left; rw [huniv, hsv, htU, hvU]
    · right; rw [huniv, hsv, htv, hvv]
  have hunion_single : singleSign univ := by
    rcases hunion_val with h | h <;> rw [h]
    · exact hUsign
    · exact hvsign
  have hnotboth : (hasMinusOne univ && hasPlusOne univ) = false :=
    not_both_signs_of_singleSign hunion_single
  -- Transition = finishPhase10Entry∘Phase2Transition (dispatch at phase 2).
  have hTrans : Transition L K s t =
      (finishPhase10Entry L K s (Phase2Transition L K s t).1,
       finishPhase10Entry L K t (Phase2Transition L K s t).2) := by
    unfold Transition
    rw [hepidemic]
    simp only [hs_phase_eq]
  -- The non-advancing branch keeps opinions = univ and phase = 2 for BOTH outputs;
  -- only the `output` field may change.  Compute phase + opinions of Phase2Transition.
  have hP2_phase_op :
      (Phase2Transition L K s t).1.phase = s.phase ∧
      (Phase2Transition L K s t).1.opinions = univ ∧
      (Phase2Transition L K s t).2.phase = t.phase ∧
      (Phase2Transition L K s t).2.opinions = univ := by
    unfold Phase2Transition
    rw [← huniv]
    rw [if_neg (by simp [hnotboth])]
    split_ifs <;> simp_all
  -- assemble: finishPhase10Entry is inert since the after-phase is 2 ≠ 10.
  have hsafter : ((Phase2Transition L K s t).1).phase.val ≠ 10 := by
    rw [hP2_phase_op.1, hs2]; omega
  have htafter : ((Phase2Transition L K s t).2).phase.val ≠ 10 := by
    rw [hP2_phase_op.2.2.1, ht2]; omega
  have hsfin : finishPhase10Entry L K s (Phase2Transition L K s t).1 = (Phase2Transition L K s t).1 :=
    finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _ hsafter
  have htfin : finishPhase10Entry L K t (Phase2Transition L K s t).2 = (Phase2Transition L K s t).2 :=
    finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _ htafter
  have hs'_phase : s'.phase.val = 2 := by
    show (Transition L K s t).1.phase.val = 2
    rw [hTrans]; show (finishPhase10Entry L K s (Phase2Transition L K s t).1).phase.val = 2
    rw [hsfin, hP2_phase_op.1, hs2]
  have ht'_phase : t'.phase.val = 2 := by
    show (Transition L K s t).2.phase.val = 2
    rw [hTrans]; show (finishPhase10Entry L K t (Phase2Transition L K s t).2).phase.val = 2
    rw [htfin, hP2_phase_op.2.2.1, ht2]
  have hs'_op : s'.opinions = univ := by
    show (Transition L K s t).1.opinions = univ
    rw [hTrans]; show (finishPhase10Entry L K s (Phase2Transition L K s t).1).opinions = univ
    rw [hsfin]; exact hP2_phase_op.2.1
  have ht'_op : t'.opinions = univ := by
    show (Transition L K s t).2.opinions = univ
    rw [hTrans]; show (finishPhase10Entry L K t (Phase2Transition L K s t).2).opinions = univ
    rw [htfin]; exact hP2_phase_op.2.2.2
  refine ⟨hs'_phase, ht'_phase, ?_, ?_, hs'_op, ht'_op⟩
  · rw [hs'_op]; exact hunion_val
  · rw [ht'_op]; exact hunion_val

/-! ## Part D — `countP informedP` of a pair and its monotonicity. -/

private theorem mem_of_applicable_left' {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c := by
  have hle : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
  exact Multiset.mem_of_le hle (by simp)

private theorem mem_of_applicable_right' {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c := by
  have hle : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
  exact Multiset.mem_of_le hle (by simp)

/-- `countP informedP` over a two-element pair. -/
theorem countP_informedP_pair (U : Fin 8) (x y : AgentState L K) :
    Multiset.countP (fun a => informedP U a) ({x, y} : Multiset (AgentState L K))
      = (if informedP U x then 1 else 0) + (if informedP U y then 1 else 0) := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
  ring

/-- **Per-pair informed-count monotonicity** on the consensus window: the
`U`-informed count of the produced pair is at least that of the consumed pair.
If either input is `U`-informed, the union is `U`, so BOTH outputs are
`U`-informed (count 2 ≥ input); if neither is, the union is `v`, count 0 = 0. -/
theorem informedP_pair_mono (U v : Fin 8)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (s t : AgentState L K)
    (hs2 : s.phase.val = 2) (ht2 : t.phase.val = 2)
    (hsop : s.opinions = U ∨ s.opinions = v)
    (htop : t.opinions = U ∨ t.opinions = v) :
    Multiset.countP (fun a => informedP U a) ({s, t} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => informedP U a)
          ({(Transition L K s t).1, (Transition L K s t).2}
            : Multiset (AgentState L K)) := by
  obtain ⟨hs'2, ht'2, _, _, hs'opU, ht'opU⟩ :=
    Transition_consensus_pair U v hUsign hvsign hvU hUv hvv hUU s t hs2 ht2 hsop htop
  set s' := (Transition L K s t).1
  set t' := (Transition L K s t).2
  rw [countP_informedP_pair, countP_informedP_pair]
  -- the union value of the pair, common to both outputs.
  set univ := opinionsUnion s.opinions t.opinions with huniv
  have hs'op : s'.opinions = univ := hs'opU
  have ht'op : t'.opinions = univ := ht'opU
  -- informedP outputs ↔ univ = U.
  have hs'inf : informedP U s' ↔ univ = U := by
    unfold informedP; rw [hs'op]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨hs'2, h⟩
  have ht'inf : informedP U t' ↔ univ = U := by
    unfold informedP; rw [ht'op]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨ht'2, h⟩
  -- input informedP ↔ opinions = U (phase is 2).
  have hsinf : informedP U s ↔ s.opinions = U := by
    unfold informedP
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨hs2, h⟩
  have htinf : informedP U t ↔ t.opinions = U := by
    unfold informedP
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨ht2, h⟩
  -- case on whether either input holds U.
  by_cases hsU : s.opinions = U
  · -- s informed ⇒ univ = U ⇒ both outputs informed (count 2).
    have huU : univ = U := by rw [huniv, hsU]; rcases htop with h | h <;> rw [h]; exacts [hUU, hUv]
    rw [if_pos (hs'inf.mpr huU), if_pos (ht'inf.mpr huU)]
    -- LHS ≤ 2.
    have : (if informedP U s then 1 else 0) + (if informedP U t then 1 else 0) ≤ 2 := by
      split_ifs <;> omega
    omega
  · by_cases htU : t.opinions = U
    · have huU : univ = U := by
        rw [huniv]; rcases hsop with h | h
        · exact absurd h hsU
        · rw [h, htU, hvU]
      rw [if_pos (hs'inf.mpr huU), if_pos (ht'inf.mpr huU)]
      have : (if informedP U s then 1 else 0) + (if informedP U t then 1 else 0) ≤ 2 := by
        split_ifs <;> omega
      omega
    · -- neither informed: both inputs hold v, univ = v ≠ U (if v ≠ U).
      rw [if_neg (by rw [hsinf]; exact hsU), if_neg (by rw [htinf]; exact htU)]
      omega

/-- `informedU U` is non-decreasing under any chosen-pair update on the window
`Q2 U v n`. -/
theorem informedU_stepOrSelf_ge (U v : Fin 8) (n : ℕ)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (c : Config (AgentState L K)) (hw : Q2 U v n c) (r₁ r₂ : AgentState L K) :
    informedU U c ≤ informedU U (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hmem1 := mem_of_applicable_left' happ
    have hmem2 := mem_of_applicable_right' happ
    obtain ⟨h1p, h1op⟩ := hw.2 r₁ hmem1
    obtain ⟨h2p, h2op⟩ := hw.2 r₂ hmem2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    unfold informedU
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair_le : Multiset.countP (fun a => informedP U a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => informedP U a) c := Multiset.countP_le_of_le _ hsub
    have hmono := informedP_pair_mono U v hUsign hvsign hvU hUv hvv hUU r₁ r₂ h1p h2p h1op h2op
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- `informedU U` is preserved-or-raised on the one-step kernel support over the
window `Q2 U v n` (the real-kernel `milestone_monotone` for opinions). -/
theorem informedU_ge_monotone (U v : Fin 8) (n m : ℕ)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (c c' : Config (AgentState L K)) (hw : Q2 U v n c) (h : m ≤ informedU U c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    m ≤ informedU U c' := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact le_trans h (informedU_stepOrSelf_ge U v n hUsign hvsign hvU hUv hvv hUU c hw r₁ r₂)
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'; exact h

/-! ## Part E — the per-pair advance and the rectangle advance probability. -/

/-- **Per-pair advance.**  An (informed, susceptible) ordered pair `(s, t)` with
`s` holding `U` and `t` holding `v` (both Phase-2), when applied, raises the
`U`-informed count of the pair from 1 to 2 — the susceptible becomes informed.
Combined with the floor `informedU` of the rest, this advances the global count. -/
theorem informedP_pair_advances (U v : Fin 8)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v)
    (s t : AgentState L K)
    (hs2 : s.phase.val = 2) (ht2 : t.phase.val = 2)
    (hsU : s.opinions = U) (htv : t.opinions = v) :
    Multiset.countP (fun a => informedP U a) ({s, t} : Multiset (AgentState L K)) + 1
      ≤ Multiset.countP (fun a => informedP U a)
          ({(Transition L K s t).1, (Transition L K s t).2}
            : Multiset (AgentState L K)) := by
  obtain ⟨hs'2, ht'2, _, _, hs'opU, ht'opU⟩ :=
    Transition_consensus_pair U v hUsign hvsign hvU hUv hvv hUU s t hs2 ht2
      (Or.inl hsU) (Or.inr htv)
  set s' := (Transition L K s t).1
  set t' := (Transition L K s t).2
  rw [countP_informedP_pair, countP_informedP_pair]
  have huU : opinionsUnion s.opinions t.opinions = U := by rw [hsU, htv, hUv]
  have hs'op : s'.opinions = U := by rw [hs'opU, huU]
  have ht'op : t'.opinions = U := by rw [ht'opU, huU]
  have hs'inf : informedP U s' := ⟨hs'2, hs'op⟩
  have ht'inf : informedP U t' := ⟨ht'2, ht'op⟩
  -- input: s informed (opinions=U), t NOT informed (opinions=v≠U).
  have hsinf : informedP U s := ⟨hs2, hsU⟩
  have htninf : ¬ informedP U t := by
    rintro ⟨_, h⟩; rw [htv] at h; exact hUv_ne h.symm
  rw [if_pos hs'inf, if_pos ht'inf, if_pos hsinf, if_neg htninf]

/-! ### State-set count sums. -/

/-- `∑ count` over the informed STATES equals `informedU U c`. -/
theorem sum_count_informed (U : Fin 8) (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => informedP U a), c.count a)
      = informedU U c := by
  classical
  have hcard : (Multiset.filter (fun a : AgentState L K => informedP U a) c).card
      = informedU U c := by
    unfold informedU; rw [Multiset.countP_eq_card_filter]
  rw [← hcard]
  have hcount_eq : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => informedP U a),
      c.count a
        = Multiset.count a (Multiset.filter (fun a : AgentState L K => informedP U a) c) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Config.count, Multiset.count_filter, if_pos ha.2]
  rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
  intro a ha
  rw [Multiset.mem_filter] at ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩

/-- `∑ count` over the susceptible STATES equals `susceptibleU v c`. -/
theorem sum_count_susceptible (v : Fin 8) (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => susceptibleP v a), c.count a)
      = Multiset.countP (fun a => susceptibleP v a) c := by
  classical
  have hcard : (Multiset.filter (fun a : AgentState L K => susceptibleP v a) c).card
      = Multiset.countP (fun a => susceptibleP v a) c := by
    rw [Multiset.countP_eq_card_filter]
  rw [← hcard]
  have hcount_eq : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => susceptibleP v a),
      c.count a
        = Multiset.count a (Multiset.filter (fun a : AgentState L K => susceptibleP v a) c) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Config.count, Multiset.count_filter, if_pos ha.2]
  rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
  intro a ha
  rw [Multiset.mem_filter] at ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩

/-- On the window `Q2 U v n` with `U ≠ v`, every agent is informed or susceptible,
so `informedU + susceptibleU = n`.  Hence the susceptible count is `n − m`. -/
theorem susceptible_count_eq (U v : Fin 8) (n : ℕ) (hUv : U ≠ v)
    (c : Config (AgentState L K)) (hw : Q2 U v n c) :
    Multiset.countP (fun a => susceptibleP v a) c = n - informedU U c := by
  classical
  unfold informedU
  -- every agent is informed XOR susceptible; their counts add to card = n.
  have hsplit : Multiset.countP (fun a => informedP U a) c
      + Multiset.countP (fun a => susceptibleP v a) c = c.card := by
    rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter, ← Multiset.card_add]
    congr 1
    -- the two filters partition c (every agent in c is informed or susceptible, not both).
    refine Multiset.ext.mpr ?_
    intro a
    rw [Multiset.count_add, Multiset.count_filter, Multiset.count_filter]
    by_cases hmem : a ∈ c
    · obtain ⟨hp, hop⟩ := hw.2 a hmem
      by_cases hinf : informedP U a
      · have hnsus : ¬ susceptibleP v a := by
          rintro ⟨_, hv⟩; rw [hinf.2] at hv; exact hUv hv
        rw [if_pos hinf, if_neg hnsus]; omega
      · have hsus : susceptibleP v a := by
          refine ⟨hp, ?_⟩
          rcases hop with hU | hv
          · exact absurd ⟨hp, hU⟩ hinf
          · exact hv
        rw [if_neg hinf, if_pos hsus]; omega
    · have h0 : Multiset.count a c = 0 := Multiset.count_eq_zero.mpr hmem
      rw [h0]; simp
  rw [hw.1] at hsplit
  omega

/-! ## Part F — the rectangle advance probability (DERIVED by pair-counting). -/

private theorem applicable_of_mem_distinct' {c : Config (AgentState L K)}
    {x y : AgentState L K} (hx : x ∈ c) (hy : y ∈ c) (hxy : x ≠ y) :
    Protocol.Applicable c x y := by
  classical
  refine Multiset.le_iff_count.mpr ?_
  intro a
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl,
      Multiset.count_cons, Multiset.count_cons, Multiset.count_zero]
  have hxc : 1 ≤ Multiset.count x c := Multiset.one_le_count_iff_mem.mpr hx
  have hyc : 1 ≤ Multiset.count y c := Multiset.one_le_count_iff_mem.mpr hy
  by_cases hax : a = x
  · subst hax
    have hay : ¬ a = y := fun h => hxy (h ▸ rfl)
    rw [if_pos rfl, if_neg hay]; omega
  · by_cases hay : a = y
    · subst hay; rw [if_neg hax, if_pos rfl]; omega
    · rw [if_neg hax, if_neg hay]; omega

/-- A scheduled (informed, susceptible) pair advances the GLOBAL informed count
`informedU` by one: `informedU c + 1 ≤ informedU (stepOrSelf c s t)`. -/
theorem informedU_stepOrSelf_advance (U v : Fin 8)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v)
    (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hs2 : s.phase.val = 2) (ht2 : t.phase.val = 2)
    (hsU : s.opinions = U) (htv : t.opinions = v) :
    informedU U c + 1 ≤ informedU U (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  classical
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  unfold informedU
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  have hpair_le : Multiset.countP (fun a => informedP U a) ({s, t} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => informedP U a) c := Multiset.countP_le_of_le _ hsub
  have hadv := informedP_pair_advances U v hUsign hvsign hvU hUv hvv hUU hUv_ne s t hs2 ht2 hsU htv
  omega

/-- **The generic rectangle → informed-advance-probability bound.**  Mirrors
`ClockRealMixed.advance_prob_of_rect`, with `informedU` as the advancing quantity.
DERIVED by `interactionCount`/`totalPairs` pair-counting. -/
theorem informed_advance_prob_of_rect (U : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hcardn : c.card = n)
    (R : Finset (AgentState L K × AgentState L K)) (N : ℕ)
    (hadv : ∀ p ∈ R, 1 ≤ c.count p.1 → 1 ≤ c.count p.2 → (p.1 = p.2 → 2 ≤ c.count p.1) →
      informedU U c + 1 ≤ informedU U (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2))
    (hcount : (N : ℕ) ≤ ∑ p ∈ R, c.interactionCount p.1 p.2) :
    ENNReal.ofReal ((N : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | informedU U c + 1 ≤ informedU U c'} := by
  classical
  set j := informedU U c with hjdef
  have hcard2 : 2 ≤ c.card := by rw [hcardn]; omega
  have hmeas : MeasurableSet {c' : Config (AgentState L K) | j + 1 ≤ informedU U c'} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  set S : Finset (AgentState L K × AgentState L K) :=
    R.filter (fun p => 1 ≤ c.count p.1 ∧ 1 ≤ c.count p.2 ∧ (p.1 = p.2 → 2 ≤ c.count p.1)) with hS
  have hsub : (↑S : Set (AgentState L K × AgentState L K)) ⊆
      (Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
        {c' | j + 1 ≤ informedU U c'} := by
    intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hS] at hp
    obtain ⟨hpc, hp1, hp2, hp3⟩ := hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Protocol.scheduledStep]
    exact hadv p hpc hp1 hp2 hp3
  have hstepDist : (NonuniformMajority L K).stepDistOrSelf c
      = (NonuniformMajority L K).stepDist c hcard2 := by
    unfold Protocol.stepDistOrSelf; rw [dif_pos hcard2]
  have hbase : ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | j + 1 ≤ informedU U c'}
      = (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | j + 1 ≤ informedU U c'}) := by
    rw [hstepDist]; unfold Protocol.stepDist
    rw [PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete) hmeas]
  rw [hbase]
  have hmono : (c.interactionPMF hcard2).toMeasure (↑S : Set _)
      ≤ (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | j + 1 ≤ informedU U c'}) :=
    measure_mono hsub
  refine le_trans ?_ hmono
  have hSmeasure : (c.interactionPMF hcard2).toMeasure (↑S : Set _)
      = ∑ p ∈ S, c.interactionProb p.1 p.2 := by
    rw [PMF.toMeasure_apply_finset]; rfl
  have hSsum : ∑ p ∈ S, c.interactionProb p.1 p.2
      = ∑ p ∈ R, c.interactionProb p.1 p.2 := by
    rw [hS]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hpc hpnot
    rw [Finset.mem_filter] at hpnot
    push Not at hpnot
    have hexcl := hpnot hpc
    have hzero : c.interactionCount p.1 p.2 = 0 := by
      unfold Config.interactionCount
      by_cases h1 : 1 ≤ c.count p.1
      · by_cases h2 : 1 ≤ c.count p.2
        · obtain ⟨hpe, hlt⟩ := hexcl h1 h2
          rw [if_pos hpe]
          have hc1 : c.count p.1 = 1 := by omega
          rw [hc1]
        · have hz2 : c.count p.2 = 0 := by omega
          by_cases hpe : p.1 = p.2
          · rw [if_pos hpe]; rw [hpe, hz2, Nat.zero_mul]
          · rw [if_neg hpe, hz2, Nat.mul_zero]
      · have hz1 : c.count p.1 = 0 := by omega
        by_cases hpe : p.1 = p.2
        · rw [if_pos hpe, hz1, Nat.zero_mul]
        · rw [if_neg hpe, hz1, Nat.zero_mul]
    unfold Config.interactionProb; rw [hzero]; simp
  rw [hSmeasure, hSsum]
  have heqterm : ∀ p : AgentState L K × AgentState L K,
      c.interactionProb p.1 p.2
        = (↑(c.interactionCount p.1 p.2) : ℝ≥0∞) * (↑c.totalPairs)⁻¹ := by
    intro p; unfold Config.interactionProb; rw [div_eq_mul_inv]
  rw [Finset.sum_congr rfl (fun p _ => heqterm p), ← Finset.sum_mul, ← Nat.cast_sum]
  set M := ∑ p ∈ R, c.interactionCount p.1 p.2 with hM
  have htp : c.totalPairs = n * (n - 1) := by rw [Config.totalPairs, hcardn]
  rw [htp, ← div_eq_mul_inv]
  have hden_pos : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by
    have : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hdenR : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]; push_cast; ring
  have hstep1 : ENNReal.ofReal ((N : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))
      ≤ ENNReal.ofReal (((M : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    rw [hdenR]
    have hNM : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hcount
    have hposden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by rw [← hdenR]; exact hden_pos
    gcongr
  refine le_trans hstep1 ?_
  rw [← ENNReal.ofReal_natCast M, ← ENNReal.ofReal_natCast (n * (n - 1)),
      ← ENNReal.ofReal_div_of_pos hden_pos]

/-! ## Part G — the informed×susceptible rectangle and the SYNC advance probability. -/

/-- For two state-finsets `A`, `B` of pairwise-distinct states, the
`interactionCount` mass of `A ×ˢ B` is `(∑_A count)·(∑_B count)`.  (Inlined
mirror of `ClockRealMixed.sum_interactionCount_cross_disjoint`.) -/
theorem sum_interactionCount_cross_disjoint'
    (c : Config (AgentState L K)) (A B : Finset (AgentState L K))
    (hdisj : ∀ a ∈ A, ∀ b ∈ B, a ≠ b) :
    (∑ p ∈ A ×ˢ B, c.interactionCount p.1 p.2)
      = (∑ a ∈ A, c.count a) * (∑ b ∈ B, c.count b) := by
  classical
  rw [Finset.sum_product, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  unfold Config.interactionCount
  rw [if_neg (hdisj a ha b hb)]

/-- The informed×susceptible rectangle `interactionCount` mass is `m·(n−m)`,
`m = informedU U c` (cross pairs are distinct: informed hold `U`, susceptible hold
`v ≠ U`). -/
theorem sum_interactionCount_syncRect (U v : Fin 8) (n : ℕ) (hUv : U ≠ v)
    (c : Config (AgentState L K)) (hw : Q2 U v n c) :
    (∑ p ∈ (Finset.univ.filter (fun a : AgentState L K => informedP U a)) ×ˢ
        (Finset.univ.filter (fun a : AgentState L K => susceptibleP v a)),
        c.interactionCount p.1 p.2)
      = informedU U c * (n - informedU U c) := by
  classical
  rw [sum_interactionCount_cross_disjoint' c _ _ ?_, sum_count_informed,
      sum_count_susceptible, susceptible_count_eq U v n hUv c hw]
  -- distinctness: informed opinions = U, susceptible opinions = v ≠ U.
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  intro hab
  have : a.opinions = U := ha.2.2
  have hbv : b.opinions = v := hb.2.2
  rw [hab, hbv] at this
  exact hUv this.symm

/-- **The SYNC informed-advance probability (DERIVED).**  One step raises
`informedU U` by `≥ 1` with probability `≥ m·(n−m)/(n(n−1))`, `m = informedU U c`.
DERIVED from the informed×susceptible rectangle by pair-counting — never assumed. -/
theorem opinion_advance_prob (U v : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v)
    (c : Config (AgentState L K)) (hw : Q2 U v n c) :
    ENNReal.ofReal
        (((informedU U c * (n - informedU U c) : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | informedU U c + 1 ≤ informedU U c'} := by
  classical
  set R := (Finset.univ.filter (fun a : AgentState L K => informedP U a)) ×ˢ
    (Finset.univ.filter (fun a : AgentState L K => susceptibleP v a)) with hR
  set m := informedU U c with hmdef
  have hcount : m * (n - m) ≤ ∑ p ∈ R, c.interactionCount p.1 p.2 := by
    rw [hR, sum_interactionCount_syncRect U v n hUv_ne c hw]
  refine informed_advance_prob_of_rect U n hn c hw.1 R (m * (n - m)) ?_ hcount
  · -- every informed×susceptible pair advances when present-applicable.
    rintro ⟨a, b⟩ hp h1 h2 _hsame
    rw [hR, Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨_, hainf⟩, ⟨_, hbsus⟩⟩ := hp
    have ha2 : a.phase.val = 2 := hainf.1
    have haU : a.opinions = U := hainf.2
    have hb2 : b.phase.val = 2 := hbsus.1
    have hbv : b.opinions = v := hbsus.2
    have hamem : a ∈ c := Multiset.one_le_count_iff_mem.mp h1
    have hbmem : b ∈ c := Multiset.one_le_count_iff_mem.mp h2
    have hab : a ≠ b := by intro h; rw [h, hbv] at haU; exact hUv_ne haU.symm
    have happ : Protocol.Applicable c a b := applicable_of_mem_distinct' hamem hbmem hab
    exact informedU_stepOrSelf_advance U v hUsign hvsign hvU hUv hvv hUU hUv_ne c a b happ
      ha2 hb2 haU hbv

/-! ## Part H — the opinion-deficit potential and its one-step drift. -/

/-- The clamped informed count `min (informedU U c) n`. -/
def oClamp (U : Fin 8) (n : ℕ) (c : Config (AgentState L K)) : ℕ := min (informedU U c) n

/-- "Finished": all `n` agents are `U`-informed. -/
def oFinished (U : Fin 8) (n : ℕ) (c : Config (AgentState L K)) : Prop := n ≤ informedU U c

instance (U : Fin 8) (n : ℕ) (c : Config (AgentState L K)) : Decidable (oFinished U n c) := by
  unfold oFinished; infer_instance

/-- The exponential-window deficit potential: `0` when finished (all informed),
else `ofReal(exp(s·(n − oClamp)))`.  Mirrors `ClockRealKernel.rSeedPot` (the
finished value is `0`, so the finished-case drift `∫ ≤ r·0 = 0` is automatic). -/
noncomputable def oDeficitPot (U : Fin 8) (n : ℕ) (s : ℝ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  if oFinished U n c then 0
  else ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (oClamp U n c : ℝ))))

theorem oDeficitPot_measurable (U : Fin 8) (n : ℕ) (s : ℝ) :
    Measurable (oDeficitPot U n s (L := L) (K := K)) :=
  Measurable.of_discrete

/-- On the unfinished window the potential is `ofReal(exp(s·(n − m)))`,
`m = informedU`. -/
theorem oDeficitPot_eq_of_lt (U : Fin 8) (n : ℕ) (s : ℝ) (c : Config (AgentState L K))
    (hlt : informedU U c < n) :
    oDeficitPot U n s c = ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (informedU U c : ℝ)))) := by
  unfold oDeficitPot oFinished oClamp
  rw [if_neg (by omega)]
  congr 2
  rw [min_eq_left (le_of_lt hlt)]

/-- `¬oFinished → 1 ≤ Φ` (the threshold link at `θ = 1`). -/
theorem not_finished_imp_oDeficitPot_ge_one (U : Fin 8) (n : ℕ) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hc : ¬ oFinished U n c) :
    (1 : ℝ≥0∞) ≤ oDeficitPot U n s c := by
  have hlt : informedU U c < n := by unfold oFinished at hc; omega
  rw [oDeficitPot_eq_of_lt U n s c hlt]
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
  apply ENNReal.ofReal_le_ofReal
  rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
  apply Real.exp_le_exp.mpr
  have hdef : (1 : ℝ) ≤ (n : ℝ) - (informedU U c : ℝ) := by
    have : (informedU U c : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hlt
    linarith
  nlinarith [hs, hdef]

/-- `oFinished` is one-step closed (informed count non-decreasing on the window). -/
theorem oFinished_absorbing (U v : Fin 8) (n : ℕ)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (c c' : Config (AgentState L K)) (hw : Q2 U v n c)
    (hfin : oFinished U n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    oFinished U n c' := by
  unfold oFinished at hfin ⊢
  exact informedU_ge_monotone U v n n hUsign hvsign hvU hUv hvv hUU c c' hw hfin hc'

/-- Pointwise one-step bound on the deficit potential, using the PROVEN
monotonicity `informedU_ge_monotone`.  Mirrors
`ClockRealMixed.rSeedPot_pointwise_bound_mixed`. -/
theorem oDeficitPot_pointwise_bound (U : Fin 8) (n : ℕ) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (m : ℕ)
    (_hm : informedU U c = m) (_hm_hi : m < n)
    (c' : Config (AgentState L K)) (hmono : m ≤ informedU U c') :
    oDeficitPot U n s c' ≤
      (if m + 1 ≤ informedU U c' then
        ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (m : ℝ) - 1)))
      else
        ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (m : ℝ))))) := by
  unfold oDeficitPot oFinished oClamp
  by_cases hfin : n ≤ informedU U c'
  · rw [if_pos hfin]; split_ifs <;> exact bot_le
  · rw [if_neg hfin]
    rw [not_le] at hfin
    by_cases hadv : m + 1 ≤ informedU U c'
    · rw [if_pos hadv]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      rw [min_eq_left (le_of_lt hfin)]
      have : (m : ℝ) + 1 ≤ (informedU U c' : ℝ) := by exact_mod_cast hadv
      nlinarith [hs, this]
    · rw [if_neg hadv]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      rw [min_eq_left (le_of_lt hfin)]
      have hle : (m : ℝ) ≤ (informedU U c' : ℝ) := by exact_mod_cast hmono
      nlinarith [hs, hle]

/-- The PROVEN advance-fraction floor: for `1 ≤ m ≤ n−1`, `n − 1 ≤ m·(n−m)`.
(`m·(n−m) − (n−1) = (m−1)(n−1−m) + (n−1−m) ... ≥ 0`; both endpoints give `n−1`.) -/
theorem advance_floor (n m : ℕ) (h1 : 1 ≤ m) (hlt : m < n) : n - 1 ≤ m * (n - m) := by
  -- introduce k = n − m ≥ 1; then n − 1 = m + k − 1 and m·k ≥ m + k − 1 ⟺ (m−1)(k−1) ≥ 0.
  obtain ⟨k, hk⟩ : ∃ k, n = m + k ∧ 1 ≤ k := ⟨n - m, by omega, by omega⟩
  obtain ⟨hnk, hk1⟩ := hk
  subst hnk
  rw [Nat.add_sub_cancel_left]
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, k = b + 1 := ⟨k - 1, by omega⟩
  have : (a + 1) * (b + 1) = a * b + a + b + 1 := by ring
  omega

/-! ## Part I — the genuine one-step opinion drift. -/

/-- **The genuine Phase-2 opinion drift.**  On the consensus window `Q2 U v n`
with `n ≥ 2`, in the unfinished regime (`informedU U c < n`), the deficit
potential contracts at the GENUINE rate `r = 1 − ((n−1)/(n(n−1)))·(1 − e^{−s})`.

The contraction PROBABILITY is DERIVED (`opinion_advance_prob`, full `n(n−1)`
denominator); the monotonicity is PROVEN (`informedU_ge_monotone`); the
advance-fraction floor `n−1 ≤ m·(n−m)` is PROVEN (`advance_floor`).  NOTHING is
assumed beyond the structural window membership `Q2` and `1 ≤ informedU`. -/
theorem phase2OpinionDrift (U v : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hQ : Q2 U v n c)
    (hlo : 1 ≤ informedU U c) (hnc : informedU U c < n) :
    ∫⁻ c', oDeficitPot U n s c' ∂((NonuniformMajority L K).transitionKernel c) ≤
      ENNReal.ofReal (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s)))
        * oDeficitPot U n s c := by
  classical
  set m := informedU U c with hm
  -- Φ(c) = ofReal(exp(s·(n − m))).
  have hΦc : oDeficitPot U n s c
      = ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (m : ℝ)))) :=
    oDeficitPot_eq_of_lt U n s c hnc
  set A := {c' : Config (AgentState L K) | m + 1 ≤ informedU U c'} with hA_def
  have hA_meas : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
  set pR : ℝ := (((n - 1 : ℕ)) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) with hpR
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  -- the advance numerator floor.
  have hfloorN : n - 1 ≤ m * (n - m) := advance_floor n m hlo hnc
  -- m·(n−m) ≤ n(n−1).
  have hmRle : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hnc
  have hnmR : ((n - m : ℕ) : ℝ) = (n : ℝ) - (m : ℝ) := by rw [Nat.cast_sub (le_of_lt hnc)]
  have hrec_le : ((m * (n - m) : ℕ) : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    rw [Nat.cast_mul, hnmR]
    nlinarith [sq_nonneg ((n : ℝ) - 2 * (m : ℝ)), hmRle, hnR,
      mul_nonneg (by linarith : (0:ℝ) ≤ (m:ℝ)) (by linarith : (0:ℝ) ≤ (n:ℝ) - (m:ℝ))]
  have hfloorR : (((n - 1 : ℕ)) : ℝ) ≤ ((m * (n - m) : ℕ) : ℝ) := by exact_mod_cast hfloorN
  have hnum_le : (((n - 1 : ℕ)) : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := le_trans hfloorR hrec_le
  have hpR_nonneg : 0 ≤ pR := by rw [hpR]; exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hden_pos)
  have hpR_le_one : pR ≤ 1 := by rw [hpR, div_le_one hden_pos]; exact hnum_le
  set E0 : ℝ := Real.exp (s * ((n : ℝ) - (m : ℝ))) with hE0
  set E1 : ℝ := Real.exp (s * ((n : ℝ) - (m : ℝ) - 1)) with hE1
  have hE0_pos : 0 < E0 := Real.exp_pos _
  have hE1_pos : 0 < E1 := Real.exp_pos _
  have hE1_eq : E1 = E0 * Real.exp (-s) := by rw [hE0, hE1, ← Real.exp_add]; congr 1; ring
  -- the GENUINE derived advance probability lower bound: pR ≤ measure(A).
  have hstep : ENNReal.ofReal pR ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A := by
    have hadv := opinion_advance_prob U v n hn hUsign hvsign hvU hUv hvv hUU hUv_ne c hQ
    rw [← hm] at hadv
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hadv
    rw [hpR]
    apply (div_le_div_iff_of_pos_right hden_pos).mpr
    exact hfloorR
  change ∫⁻ c', oDeficitPot U n s c'
    ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure ≤ _
  calc ∫⁻ c', oDeficitPot U n s c'
        ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      ≤ ∫⁻ c', (if m + 1 ≤ informedU U c' then ENNReal.ofReal E1
          else ENNReal.ofReal E0) ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure := by
        apply lintegral_mono_ae
        rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]
        intro x hsupp hbad
        apply hbad
        have hmono_x : m ≤ informedU U x :=
          informedU_ge_monotone U v n m hUsign hvsign hvU hUv hvv hUU c x hQ (le_of_eq hm.symm) hsupp
        exact oDeficitPot_pointwise_bound U n s hs c m hm.symm hnc x hmono_x
    _ = (∫⁻ c' in A, ENNReal.ofReal E1 ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure) +
        (∫⁻ c' in Aᶜ, ENNReal.ofReal E0 ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure) := by
        rw [← lintegral_add_compl _ hA_meas]
        congr 1
        · apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem hA_meas] with c' hc'
          simp only [Set.mem_setOf_eq, hA_def] at hc'
          simp [hc']
        · apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem hA_meas.compl] with c' hc'
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq, hA_def] at hc'
          simp [hc']
    _ = ENNReal.ofReal E1 * ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A +
        ENNReal.ofReal E0 * ((NonuniformMajority L K).stepDistOrSelf c).toMeasure Aᶜ := by
        rw [lintegral_const, Measure.restrict_apply_univ,
            lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal (1 - pR * (1 - Real.exp (-s))) * oDeficitPot U n s c := by
        rw [hΦc]
        set q := ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A with hq_def
        set qc := ((NonuniformMajority L K).stepDistOrSelf c).toMeasure Aᶜ with hqc_def
        haveI : IsProbabilityMeasure ((NonuniformMajority L K).stepDistOrSelf c).toMeasure :=
          PMF.toMeasure.isProbabilityMeasure _
        have hq_ge : ENNReal.ofReal pR ≤ q := hstep
        have hq_le_one : q ≤ 1 := by
          calc q ≤ ((NonuniformMajority L K).stepDistOrSelf c).toMeasure Set.univ :=
                measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        have hq_ne_top : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq_le_one
        have hqc_eq : qc = 1 - q := by
          have h_compl := measure_compl hA_meas hq_ne_top
          rw [show ((NonuniformMajority L K).stepDistOrSelf c).toMeasure Set.univ = 1
            from measure_univ] at h_compl
          exact h_compl
        set qr := q.toReal with hqr_def
        have hqr_nonneg : 0 ≤ qr := ENNReal.toReal_nonneg
        have hqr_le_one : qr ≤ 1 := by
          have := ENNReal.toReal_mono ENNReal.one_ne_top hq_le_one
          rwa [ENNReal.toReal_one] at this
        have hq_ofReal : q = ENNReal.ofReal qr := (ENNReal.ofReal_toReal hq_ne_top).symm
        have hp_le_qr : pR ≤ qr := by
          have h1 : ENNReal.ofReal pR ≤ ENNReal.ofReal qr := by rw [← hq_ofReal]; exact hq_ge
          exact (ENNReal.ofReal_le_ofReal_iff hqr_nonneg).mp h1
        have h1mqr_nonneg : 0 ≤ 1 - qr := by linarith
        have hqc_ofReal : qc = ENNReal.ofReal (1 - qr) := by
          rw [hqc_eq, hq_ofReal,
              show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
              ← ENNReal.ofReal_sub 1 hqr_nonneg]
        have lhs_eq : ENNReal.ofReal E1 * q + ENNReal.ofReal E0 * qc =
            ENNReal.ofReal (E1 * qr + E0 * (1 - qr)) := by
          rw [hq_ofReal, hqc_ofReal,
              ← ENNReal.ofReal_mul hE1_pos.le, ← ENNReal.ofReal_mul hE0_pos.le,
              ← ENNReal.ofReal_add (mul_nonneg hE1_pos.le hqr_nonneg)
                (mul_nonneg hE0_pos.le h1mqr_nonneg)]
        have hexp_le_one : Real.exp (-s) ≤ 1 := by
          rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
          exact Real.exp_le_exp.mpr (by linarith)
        have rhs_eq : ENNReal.ofReal (1 - pR * (1 - Real.exp (-s))) * ENNReal.ofReal E0 =
            ENNReal.ofReal ((1 - pR * (1 - Real.exp (-s))) * E0) := by
          rw [← ENNReal.ofReal_mul]
          have : (1 : ℝ) - pR * (1 - Real.exp (-s)) ≥ 0 := by
            have h0 : (0 : ℝ) ≤ 1 - Real.exp (-s) := by linarith
            nlinarith [hpR_nonneg, hpR_le_one, h0]
          linarith
        rw [lhs_eq, rhs_eq]
        apply ENNReal.ofReal_le_ofReal
        have hfactor : E1 * qr + E0 * (1 - qr) = E0 * (1 - qr * (1 - Real.exp (-s))) := by
          rw [hE1_eq]; ring
        rw [hfactor]
        have hrhs : (1 - pR * (1 - Real.exp (-s))) * E0
            = E0 * (1 - pR * (1 - Real.exp (-s))) := by ring
        rw [hrhs]
        apply mul_le_mul_of_nonneg_left _ hE0_pos.le
        have h1me : (0 : ℝ) ≤ 1 - Real.exp (-s) := by linarith
        nlinarith [mul_le_mul_of_nonneg_right hp_le_qr h1me]

/-! ## Part J — the window is one-step closed (no carried invariant). -/

/-- The window property is preserved by a single chosen-pair update: produced
agents are Phase-2 with opinions in `{U, v}` (`Transition_consensus_pair`),
unchanged agents keep the property, and `card` is preserved. -/
theorem Q2_stepOrSelf (U v : Fin 8) (n : ℕ)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (c : Config (AgentState L K)) (hw : Q2 U v n c) (r₁ r₂ : AgentState L K) :
    Q2 U v n (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hmem1 := mem_of_applicable_left' happ
    have hmem2 := mem_of_applicable_right' happ
    obtain ⟨h1p, h1op⟩ := hw.2 r₁ hmem1
    obtain ⟨h2p, h2op⟩ := hw.2 r₂ hmem2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    obtain ⟨hp1', hp2', hop1', hop2', _, _⟩ :=
      Transition_consensus_pair U v hUsign hvsign hvU hUv hvv hUU r₁ r₂ h1p h2p h1op h2op
    refine ⟨?_, ?_⟩
    · -- card preserved.
      have hcard := Protocol.reachable_card_eq
        (Protocol.reachable_stepOrSelf (P := NonuniformMajority L K) c r₁ r₂)
      rw [hcard]; exact hw.1
    · intro a ha
      rw [hc'] at ha
      rcases Multiset.mem_add.mp ha with hold | hnew
      · -- a is an unchanged agent from c.
        exact hw.2 a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hold)
      · -- a is one of the two produced agents.
        rw [show ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
              : Multiset (AgentState L K))
            = (Transition L K r₁ r₂).1 ::ₘ (Transition L K r₁ r₂).2 ::ₘ 0 from rfl] at hnew
        simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hnew
        rcases hnew with h | h
        · subst h; exact ⟨hp1', hop1'⟩
        · subst h; exact ⟨hp2', hop2'⟩
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; exact hw

/-- `Q2` is one-step-support closed (the `windowDrift_PhaseConvergence` `hQ_abs`). -/
theorem Q2_absorbing (U v : Fin 8) (n : ℕ)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (c c' : Config (AgentState L K)) (hw : Q2 U v n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    Q2 U v n c' := by
  classical
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact Q2_stepOrSelf U v n hUsign hvsign hvU hUv hvv hUU c hw r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'; exact hw

/-! ## Part K — the off-window guarded potential and the final `PhaseConvergence`.

The guarded potential is `⊤` off the window `Q2 U v n`, else the deficit potential.
This makes `Φ` uniformly bounded on `Pre` and lets the framework absorb the window
into the drift exactly as in `ClockRealBulk`. -/

/-- The window-guarded deficit potential: `⊤` off `Q2`, else `oDeficitPot`. -/
noncomputable def oPotG (U v : Fin 8) (n : ℕ) (s : ℝ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  if Q2 U v n c then oDeficitPot U n s c else ⊤

theorem oPotG_measurable (U v : Fin 8) (n : ℕ) (s : ℝ) :
    Measurable (oPotG U v n s (L := L) (K := K)) :=
  Measurable.of_discrete

theorem oPotG_eq_on_window (U v : Fin 8) (n : ℕ) (s : ℝ) (c : Config (AgentState L K))
    (hw : Q2 U v n c) : oPotG U v n s c = oDeficitPot U n s c := by
  unfold oPotG; rw [if_pos hw]

/-- On `Pre` (at least one informed), the deficit potential is at most
`ofReal(exp(s·(n−1)))`. -/
theorem oDeficitPot_le_pre (U : Fin 8) (n : ℕ) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hlo : 1 ≤ informedU U c) :
    oDeficitPot U n s c ≤ ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) := by
  unfold oDeficitPot oClamp
  by_cases hfin : oFinished U n c
  · rw [if_pos hfin]; exact bot_le
  · rw [if_neg hfin]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hmin : (min (informedU U c) n : ℕ) = informedU U c := by
      unfold oFinished at hfin; omega
    rw [hmin]
    have h1 : (1 : ℝ) ≤ (informedU U c : ℝ) := by exact_mod_cast hlo
    nlinarith [hs, h1]

/-- The full drift window: the consensus window plus at least one informed agent
(`1 ≤ informedU`, the seed floor).  Both conjuncts are one-step closed. -/
def Qwin (U v : Fin 8) (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  Q2 U v n c ∧ 1 ≤ informedU U c

instance (U v : Fin 8) (n : ℕ) (c : Config (AgentState L K)) : Decidable (Qwin U v n c) := by
  unfold Qwin; infer_instance

/-- `Qwin` is one-step-support closed: `Q2` is closed (`Q2_absorbing`) and the
informed-count floor `1 ≤ informedU` is preserved (`informedU_ge_monotone`). -/
theorem Qwin_absorbing (U v : Fin 8) (n : ℕ)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (c c' : Config (AgentState L K)) (hw : Qwin U v n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    Qwin U v n c' :=
  ⟨Q2_absorbing U v n hUsign hvsign hvU hUv hvv hUU c c' hw.1 hc',
   informedU_ge_monotone U v n 1 hUsign hvsign hvU hUv hvv hUU c c' hw.1 hw.2 hc'⟩

/-- The guarded potential restricted to `Qwin`: `⊤` off `Qwin`, else `oDeficitPot`. -/
noncomputable def oPotW (U v : Fin 8) (n : ℕ) (s : ℝ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  if Qwin U v n c then oDeficitPot U n s c else ⊤

theorem oPotW_measurable (U v : Fin 8) (n : ℕ) (s : ℝ) :
    Measurable (oPotW U v n s (L := L) (K := K)) :=
  Measurable.of_discrete

theorem oPotW_eq_on_window (U v : Fin 8) (n : ℕ) (s : ℝ) (c : Config (AgentState L K))
    (hw : Qwin U v n c) : oPotW U v n s c = oDeficitPot U n s c := by
  unfold oPotW; rw [if_pos hw]

/-! ## Part L — the deliverable `PhaseConvergence` on the REAL kernel. -/

/-- **The Phase-2 (and Phase-9) opinion-union epidemic `PhaseConvergence` on the
REAL `NonuniformMajority L K` kernel.**

* `Pre c` = consensus window `Q2 U v n` (every agent Phase-2 with opinion in
  `{U, v}`, size `n`) with at least one `U`-informed agent;
* `Post c` = `oFinished U n c` (all `n` agents are `U`-informed — opinion consensus
  reached);
* `t` = the interaction budget, `ε` = the target failure probability, with the
  single arithmetic check `hε` that the geometric tail fits under `ε`.

The convergence is GENUINELY DERIVED: the drift `phase2OpinionDrift` is proven from
the opinion-union epidemic mechanism + the DERIVED pair-counting advance
probability `opinion_advance_prob`; the window is PROVEN one-step closed
(`Q2_absorbing`).  This is CLOCK-INDEPENDENT — no `minute`/`hour`/`habs`
hypothesis appears. -/
noncomputable def phase2Convergence (U v : Fin 8) (n : ℕ) (hn : 2 ≤ n)
    (hUsign : singleSign U) (hvsign : singleSign v)
    (hvU : opinionsUnion v U = U) (hUv : opinionsUnion U v = U)
    (hvv : opinionsUnion v v = v) (hUU : opinionsUnion U U = U)
    (hUv_ne : U ≠ v) (s : ℝ) (hs : 0 < s)
    (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal
            (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
            ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1
          ≤ (ε : ℝ≥0∞)) :
    PhaseConvergence (NonuniformMajority L K).transitionKernel := by
  refine WindowConcentration.windowDrift_PhaseConvergence (NonuniformMajority L K)
    (oPotW U v n s) (oPotW_measurable U v n s)
    (fun c => Qwin U v n c)                                                -- Q
    (Qwin_absorbing U v n hUsign hvsign hvU hUv hvv hUU)                   -- hQ_abs
    (ENNReal.ofReal
      (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))))  -- r
    ?_                                                                     -- hdrift
    (fun c => Qwin U v n c)                                               -- Pre
    (fun c => Qwin U v n c ∧ oFinished U n c)                             -- Post
    ?_                                                                     -- hPost_abs
    1 one_ne_zero ENNReal.one_ne_top                                       -- θ = 1
    ?_                                                                     -- hlink
    (fun c h => h)                                                         -- hPre_Q
    (ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))))                       -- Φ₀
    ?_                                                                     -- hPre_bound
    t ε hε                                                                -- hε
  · -- hdrift : on the window, the GENUINE opinion drift (unfinished) or `Φ = 0` (finished).
    intro c hQw
    obtain ⟨hQ, hlo⟩ := hQw
    rw [oPotW_eq_on_window U v n s c ⟨hQ, hlo⟩]
    -- replace oPotW by oDeficitPot a.e. inside the integral (Qwin is absorbing).
    have hint_eq : ∫⁻ c', oPotW U v n s c'
          ∂((NonuniformMajority L K).transitionKernel c)
        = ∫⁻ c', oDeficitPot U n s c'
          ∂((NonuniformMajority L K).transitionKernel c) := by
      apply lintegral_congr_ae
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure,
        oPotW U v n s c' = oDeficitPot U n s c'
      rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      rw [Set.disjoint_left]
      intro x hsupp hbad
      apply hbad
      exact oPotW_eq_on_window U v n s x
        (Qwin_absorbing U v n hUsign hvsign hvU hUv hvv hUU c x ⟨hQ, hlo⟩ hsupp)
    rw [hint_eq]
    by_cases hfin : oFinished U n c
    · -- finished: Φ(c) = 0, and all support points stay finished ⇒ integral 0.
      have hΦc0 : oDeficitPot U n s c = 0 := by unfold oDeficitPot; rw [if_pos hfin]
      rw [hΦc0, mul_zero, nonpos_iff_eq_zero]
      change ∫⁻ c', oDeficitPot U n s c'
          ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure = 0
      rw [lintegral_eq_zero_iff (oDeficitPot_measurable U n s)]
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨((NonuniformMajority L K).stepDistOrSelf c).support, ?_, ?_⟩
      · rw [mem_ae_iff, PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]; intro x hsupp hx
        exact hx (PMF.mem_support_iff _ _ |>.mp hsupp)
      · intro c' hc'
        have hfin' : oFinished U n c' :=
          oFinished_absorbing U v n hUsign hvsign hvU hUv hvv hUU c c' hQ hfin hc'
        change oDeficitPot U n s c' = 0
        unfold oDeficitPot; rw [if_pos hfin']
    · -- unfinished: the GENUINE opinion contraction (the seed floor `1 ≤ m` is in Qwin).
      have hnc : informedU U c < n := by unfold oFinished at hfin; omega
      exact phase2OpinionDrift U v n hn hUsign hvsign hvU hUv hvv hUU hUv_ne s hs c hQ hlo hnc
  · -- hPost_abs : (Qwin ∧ oFinished) one-step closed.
    rintro c c' ⟨hQw, hfin⟩ hc'
    exact ⟨Qwin_absorbing U v n hUsign hvsign hvU hUv hvv hUU c c' hQw hc',
      oFinished_absorbing U v n hUsign hvsign hvU hUv hvv hUU c c' hQw.1 hfin hc'⟩
  · -- hlink : ¬Post → 1 ≤ Φ.  Off-window Φ = ⊤; on-window-unfinished Φ ≥ 1.
    intro c hnp
    unfold oPotW
    by_cases hQw : Qwin U v n c
    · rw [if_pos hQw]
      have hnf : ¬ oFinished U n c := fun hfin => hnp ⟨hQw, hfin⟩
      exact not_finished_imp_oDeficitPot_ge_one U n s hs c hnf
    · rw [if_neg hQw]; exact le_top
  · -- hPre_bound : Φ ≤ exp(s·(n−1)) on Pre = Qwin.
    intro c hPre
    rw [oPotW_eq_on_window U v n s c hPre]
    exact oDeficitPot_le_pre U n s hs c hPre.2

end Phase2Convergence

end ExactMajority
