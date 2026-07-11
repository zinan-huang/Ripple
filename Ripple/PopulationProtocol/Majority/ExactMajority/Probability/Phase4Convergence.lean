/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase 4 — tie detection / non-tie continuation (Doty et al. §6, Phase 4)

`Phase4Transition` (Protocol/Transition.lean:1042) is the post-clock **tie
detector**:

```
def Phase4Transition (s t) :=
  let hasBigBias a := match a.bias with
    | .zero      => false
    | .dyadic _ i => decide (i.val < L)
  if hasBigBias s || hasBigBias t then (advancePhase s, advancePhase t)  -- → Phase 5
  else (s, t)                                                            -- stay (tie)
```

So a phase-4 agent with a **big bias** (a nonzero dyadic bias whose exponent
index `i < L`, i.e. `|bias| > 2^{-L}`) is a **witness**: meeting *any* partner
advances both to Phase 5.  This file formalizes both branches of Phase 4:

* **Tie branch** (Theorem 6.1 input): if no agent has a big bias (all biased
  agents are at the minimum exponent `L`, so `|g| < 1 ⟹ g = 0`), then
  `Phase4Transition` is the identity forever, every agent keeps output `T`, and
  the population is *deterministically* stable — `StableTie4` is one-step closed.
  This gives a `PhaseConvergenceW` with `t = 0`, `ε = 0`.

* **Non-tie branch** (Theorem 6.2 input): some agent has already advanced to
  Phase `≥ 5` (the epidemic source — provided by the upstream phase, exactly as
  `Phase3Convergence` carries its source `∃ a, 4 ≤ a.phase`).  The phase-`max`
  epidemic baked into `phaseEpidemicUpdate` then spreads `phase ≥ 5` to everyone:
  whenever a phase-`< 5` agent meets a phase-`≥ 5` agent, BOTH outputs land at
  phase `≥ 5` (`Transition_*_phase_ge_pair_max`).  The descending potential is
  `phaseBelowCount 5` (count of not-yet-advanced agents), the SAME mechanism as
  `Phase3Convergence`'s `phaseBelowCount 4` descent, ported to threshold 5.

## Honest predicate choices (vs. the HANDOFF sketch placeholders)

The sketch named `TieAllMinExp`, `Phase3StructuredNonTiePost`, `StableTieOutput`,
`Phase5Pre`, which do not exist in the repo.  We use honest in-file predicates
read off the actual `Phase4Transition` rule:

* `noBigBias a`     — `a.bias` is `.zero` or `.dyadic _ i` with `¬ i.val < L`
  (mirrors `StableEndpoints.phase4NoBigBias`, which is `private`);
* `StableTie4 c`    — every agent is phase-4, output `T`, `noBigBias` (mirrors the
  `private` `StableEndpoints.phase4TieWith`); this is the tie `Post`;
* `Advanced5 c`     — every agent is at phase `≥ 5` (`phaseBelowCount 5 c = 0`);
  the non-tie `Post`.

This file is self-contained and uses only proved dependencies.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WindowConcentration
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Phase3Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.Invariants

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Phase4Convergence

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part A — the no-big-bias predicate and the tie window. -/

/-- An agent has *no big bias* if its bias is zero or a dyadic with exponent index
`= L` (i.e. `¬ i.val < L`).  This is exactly the negation of `Phase4Transition`'s
`hasBigBias` guard, so a population of no-big-bias phase-4 agents never advances. -/
def noBigBias (a : AgentState L K) : Prop :=
  match a.bias with
  | .zero => True
  | .dyadic _ i => ¬ i.val < L

instance (a : AgentState L K) : Decidable (noBigBias a) := by
  unfold noBigBias; cases a.bias <;> infer_instance

/-- The Phase-4 **tie window / stable-tie postcondition**: every agent is a phase-4
agent reporting output `T` with no big bias.  Mirrors the `private`
`StableEndpoints.phase4TieWith`. -/
def StableTie4 (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.phase.val = 4 ∧ a.output = Output.T ∧ noBigBias a

instance (c : Config (AgentState L K)) : Decidable (StableTie4 c) := by
  unfold StableTie4; infer_instance

/-- The stable tie branch together with the ambient population size.  The bare
`StableTie4` predicate is intentionally card-free, so slot-4 work surfaces use
this carded form when they need to feed the next seam. -/
def StableTie4Card (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ StableTie4 (L := L) (K := K) c

instance (n : ℕ) (c : Config (AgentState L K)) : Decidable (StableTie4Card n c) := by
  unfold StableTie4Card; infer_instance

/-! ## Part B — the tie branch is deterministically one-step closed. -/

/-- With no big bias on either side, the `Phase4Transition` guard is `false`, so it
is the identity. -/
theorem Phase4Transition_eq_self_of_noBigBias (s t : AgentState L K)
    (hs : noBigBias (L := L) (K := K) s) (ht : noBigBias (L := L) (K := K) t) :
    Phase4Transition L K s t = (s, t) := by
  rcases s with
    ⟨sinput, soutput, sphase, srole, sassigned, sbias, ssmallBias,
      shour, sminute, sfull, sopinions, scounter⟩
  rcases t with
    ⟨tinput, toutput, tphase, trole, tassigned, tbias, tsmallBias,
      thour, tminute, tfull, topinions, tcounter⟩
  unfold noBigBias at hs ht
  unfold Phase4Transition
  dsimp at hs ht ⊢
  cases sbias with
  | zero =>
    cases tbias with
    | zero => simp
    | dyadic tg j => simp [ht]
  | dyadic sg i =>
    cases tbias with
    | zero => simp [hs]
    | dyadic tg j => simp [hs, ht]

/-- For two phase-4 agents, `phaseEpidemicUpdate` is the identity (max of equal
phases, no init to run, no phase-10 entry). -/
theorem phaseEpidemicUpdate_eq_self_of_phase4 (s t : AgentState L K)
    (hs : s.phase.val = 4) (ht : t.phase.val = 4) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hsp : s.phase = ⟨4, by decide⟩ := Fin.ext hs
  have htp : t.phase = ⟨4, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hsp, htp, max_self]
  simp only [runInitsBetween_self_api]
  have hs_self : ({s with phase := (⟨4, by decide⟩ : Fin 11)} : AgentState L K) = s := by
    rw [← hsp]
  have ht_self : ({t with phase := (⟨4, by decide⟩ : Fin 11)} : AgentState L K) = t := by
    rw [← htp]
  rw [hs_self, ht_self]
  rw [if_neg (by push Not; intro _; simp)]

/-- **Per-pair tie preservation.**  Two tie-agents (phase 4, output `T`, no big
bias) produce two tie-agents under the full `Transition`. -/
theorem Transition_preserves_tie_pair (s t : AgentState L K)
    (hs4 : s.phase.val = 4) (ht4 : t.phase.val = 4)
    (hsT : s.output = Output.T) (htT : t.output = Output.T)
    (hsB : noBigBias (L := L) (K := K) s) (htB : noBigBias (L := L) (K := K) t) :
    let s' := (Transition L K s t).1
    let t' := (Transition L K s t).2
    (s'.phase.val = 4 ∧ s'.output = Output.T ∧ noBigBias (L := L) (K := K) s') ∧
      (t'.phase.val = 4 ∧ t'.output = Output.T ∧ noBigBias (L := L) (K := K) t') := by
  intro s' t'
  have hepi := phaseEpidemicUpdate_eq_self_of_phase4 (L := L) (K := K) s t hs4 ht4
  have hp4 := Phase4Transition_eq_self_of_noBigBias (L := L) (K := K) s t hsB htB
  have hsp : s.phase = ⟨4, by decide⟩ := Fin.ext hs4
  -- Transition unfolds: phaseEpidemicUpdate = (s,t); dispatch at phase 4 = Phase4Transition = (s,t).
  have hTrans : Transition L K s t = (s, t) := by
    unfold Transition
    rw [hepi]
    simp only [hsp]
    rw [show (Phase4Transition L K s t) = (s, t) from hp4]
    -- finishPhase10Entry s s = s, finishPhase10Entry t t = t (phase 4 ≠ 10).
    rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s s (by rw [hs4]; omega),
        finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t t (by rw [ht4]; omega)]
  have hs'eq : s' = s := by show (Transition L K s t).1 = s; rw [hTrans]
  have ht'eq : t' = t := by show (Transition L K s t).2 = t; rw [hTrans]
  rw [hs'eq, ht'eq]
  exact ⟨⟨hs4, hsT, hsB⟩, ⟨ht4, htT, htB⟩⟩

private theorem mem_of_applicable_left {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c := by
  have hle : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
  exact Multiset.mem_of_le hle (by simp)

private theorem mem_of_applicable_right {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c := by
  have hle : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
  exact Multiset.mem_of_le hle (by simp)

/-- `StableTie4` is preserved by a single chosen-pair update: the two produced
agents are tie-agents (`Transition_preserves_tie_pair`), the unchanged ones keep
the property. -/
theorem StableTie4_stepOrSelf (c : Config (AgentState L K))
    (hw : StableTie4 (L := L) (K := K) c) (r₁ r₂ : AgentState L K) :
    StableTie4 (L := L) (K := K)
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hmem1 := mem_of_applicable_left happ
    have hmem2 := mem_of_applicable_right happ
    obtain ⟨h14, h1T, h1B⟩ := hw r₁ hmem1
    obtain ⟨h24, h2T, h2B⟩ := hw r₂ hmem2
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    obtain ⟨hp1', hp2'⟩ :=
      Transition_preserves_tie_pair (L := L) (K := K) r₁ r₂ h14 h24 h1T h2T h1B h2B
    intro a ha
    rw [hc'] at ha
    rcases Multiset.mem_add.mp ha with hold | hnew
    · exact hw a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hold)
    · rw [show ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
            : Multiset (AgentState L K))
          = (Transition L K r₁ r₂).1 ::ₘ (Transition L K r₁ r₂).2 ::ₘ 0 from rfl] at hnew
      simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hnew
      rcases hnew with h | h
      · subst h; exact hp1'
      · subst h; exact hp2'
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; exact hw

/-- `StableTie4` is one-step-support closed (kernel-absorbing). -/
theorem StableTie4_absorbing (c c' : Config (AgentState L K))
    (hw : StableTie4 (L := L) (K := K) c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    StableTie4 (L := L) (K := K) c' := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact StableTie4_stepOrSelf c hw r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'; exact hw

/-- The carded stable tie branch is one-step-support closed. -/
theorem StableTie4Card_absorbing (n : ℕ) (c c' : Config (AgentState L K))
    (hw : StableTie4Card (L := L) (K := K) n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    StableTie4Card (L := L) (K := K) n c' := by
  refine ⟨?_, ?_⟩
  · rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c' hc']
    exact hw.1
  · exact StableTie4_absorbing (L := L) (K := K) c c' hw.2 hc'

/-! ## Part C — the non-tie advanced-count epidemic (phase ≥ 5 spread).

The mechanism is the phase-`max` epidemic baked into `phaseEpidemicUpdate`:
whenever an advanced agent (`phase ≥ 5`) meets a not-yet-advanced agent, both
`Transition` outputs land at phase `≥ 5` (`Transition_*_phase_ge_pair_max`).  The
informed count `advancedU` is monotone and advances on each (advanced,
non-advanced) interaction.  This is the SAME engine as `Phase2Convergence`'s
opinion epidemic, with "informed" = "phase ≥ 5".  The window `Q4 n` only requires
every agent to be at phase `≥ 4` (so the partner of an advanced agent is also at
phase `≥ 4`, guaranteeing the `max ≥ 5` advance for BOTH outputs). -/

/-- An agent is *advanced* if it has reached Phase 5 or beyond. -/
def advancedP (a : AgentState L K) : Prop := 5 ≤ a.phase.val

instance (a : AgentState L K) : Decidable (advancedP a) := by
  unfold advancedP; infer_instance

/-- The advanced-agent count. -/
def advancedU (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => advancedP a) c

/-- The Phase-4 non-tie window: every agent has phase `≥ 4`, fixed size `n`.
One-step closed by phase monotonicity. -/
def Q4 (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∀ a ∈ c, 4 ≤ a.phase.val

instance (n : ℕ) (c : Config (AgentState L K)) : Decidable (Q4 n c) := by
  unfold Q4; infer_instance

/-- `countP advancedP` over a two-element pair. -/
theorem countP_advancedP_pair (x y : AgentState L K) :
    Multiset.countP (fun a => advancedP a) ({x, y} : Multiset (AgentState L K))
      = (if advancedP x then 1 else 0) + (if advancedP y then 1 else 0) := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
  ring

/-- **Per-pair advanced-count monotonicity.**  Phase only rises under `Transition`
(`Transition_phase_monotone`), and `advancedP` is upward-closed in phase, so the
advanced count of the produced pair is at least that of the consumed pair. -/
theorem advancedP_pair_mono (s t : AgentState L K) :
    Multiset.countP (fun a => advancedP a) ({s, t} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => advancedP a)
          ({(Transition L K s t).1, (Transition L K s t).2}
            : Multiset (AgentState L K)) := by
  have hmono := Transition_phase_monotone (L := L) (K := K) s t
  simp only [] at hmono
  obtain ⟨hsm, htm⟩ := hmono
  rw [countP_advancedP_pair, countP_advancedP_pair]
  have hs' : advancedP s → advancedP (Transition L K s t).1 := fun h => le_trans h hsm
  have ht' : advancedP t → advancedP (Transition L K s t).2 := fun h => le_trans h htm
  by_cases hsa : advancedP s
  · by_cases hta : advancedP t
    · rw [if_pos hsa, if_pos hta, if_pos (hs' hsa), if_pos (ht' hta)]
    · rw [if_pos hsa, if_neg hta, if_pos (hs' hsa)]; split_ifs <;> omega
  · by_cases hta : advancedP t
    · rw [if_neg hsa, if_pos hta, if_pos (ht' hta)]; split_ifs <;> omega
    · rw [if_neg hsa, if_neg hta]; omega

/-- **Per-pair advance.**  A mixed pair — one advanced (`phase ≥ 5`), one
in-window (`phase ≥ 4`) but not advanced — produces two advanced agents, since
both `Transition` outputs have phase `≥ max(s,t) ≥ 5`.  Hence the pair's advanced
count rises from 1 to 2. -/
theorem advancedP_pair_advances (s t : AgentState L K)
    (_hs4 : 4 ≤ s.phase.val) (_ht4 : 4 ≤ t.phase.val)
    (hmixed : (advancedP (L := L) (K := K) s ∧ ¬ advancedP (L := L) (K := K) t) ∨
              (¬ advancedP (L := L) (K := K) s ∧ advancedP (L := L) (K := K) t)) :
    Multiset.countP (fun a => advancedP a) ({s, t} : Multiset (AgentState L K)) + 1
      ≤ Multiset.countP (fun a => advancedP a)
          ({(Transition L K s t).1, (Transition L K s t).2}
            : Multiset (AgentState L K)) := by
  -- both outputs have phase ≥ max(s,t).phase ≥ 5.
  have hmax5 : 5 ≤ max s.phase.val t.phase.val := by
    rcases hmixed with ⟨hsa, _⟩ | ⟨_, hta⟩
    · exact le_trans hsa (le_max_left _ _)
    · exact le_trans hta (le_max_right _ _)
  have hout1 : advancedP (L := L) (K := K) (Transition L K s t).1 :=
    le_trans hmax5 (Transition_left_phase_ge_pair_max (L := L) (K := K) s t)
  have hout2 : advancedP (L := L) (K := K) (Transition L K s t).2 :=
    le_trans hmax5 (Transition_right_phase_ge_pair_max (L := L) (K := K) s t)
  rw [countP_advancedP_pair, countP_advancedP_pair, if_pos hout1, if_pos hout2]
  rcases hmixed with ⟨hsa, hta⟩ | ⟨hsa, hta⟩
  · rw [if_pos hsa, if_neg hta]
  · rw [if_neg hsa, if_pos hta]

/-- `advancedU` is non-decreasing under any chosen-pair update. -/
theorem advancedU_stepOrSelf_ge (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K) :
    advancedU (L := L) (K := K) c
      ≤ advancedU (L := L) (K := K) (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    unfold advancedU
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair_le : Multiset.countP (fun a => advancedP a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => advancedP a) c := Multiset.countP_le_of_le _ hsub
    have hmono := advancedP_pair_mono (L := L) (K := K) r₁ r₂
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- `advancedU` is preserved-or-raised on the one-step kernel support. -/
theorem advancedU_ge_monotone (m : ℕ) (c c' : Config (AgentState L K))
    (h : m ≤ advancedU (L := L) (K := K) c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    m ≤ advancedU (L := L) (K := K) c' := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact le_trans h (advancedU_stepOrSelf_ge c r₁ r₂)
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'; exact h

/-! ## Part D — the rectangle advance probability (DERIVED by pair-counting). -/

instance instMeasurableSpaceAgentState4 : MeasurableSpace (AgentState L K) := ⊤
instance instDiscreteMeasurableSpaceAgentState4 :
    DiscreteMeasurableSpace (AgentState L K) where
  forall_measurableSet _ := trivial

/-- A `phase = 4` (susceptible / not-yet-advanced) agent. -/
def susceptibleP (a : AgentState L K) : Prop := a.phase.val = 4

instance (a : AgentState L K) : Decidable (susceptibleP a) := by
  unfold susceptibleP; infer_instance

private theorem applicable_of_mem_distinct {c : Config (AgentState L K)}
    {x y : AgentState L K} (hx : x ∈ c) (hy : y ∈ c) (hxy : x ≠ y) :
    Protocol.Applicable c x y := by
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

/-- A scheduled (advanced, susceptible) pair advances the GLOBAL advanced count
`advancedU` by one. -/
theorem advancedU_stepOrSelf_advance (c : Config (AgentState L K)) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (hs4 : 4 ≤ s.phase.val) (ht4 : 4 ≤ t.phase.val)
    (hmixed : (advancedP (L := L) (K := K) s ∧ ¬ advancedP (L := L) (K := K) t) ∨
              (¬ advancedP (L := L) (K := K) s ∧ advancedP (L := L) (K := K) t)) :
    advancedU (L := L) (K := K) c + 1
      ≤ advancedU (L := L) (K := K) (Protocol.stepOrSelf (NonuniformMajority L K) c s t) := by
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  unfold advancedU
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  have hpair_le : Multiset.countP (fun a => advancedP a) ({s, t} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => advancedP a) c := Multiset.countP_le_of_le _ hsub
  have hadv := advancedP_pair_advances (L := L) (K := K) s t hs4 ht4 hmixed
  omega

/-- **The generic rectangle → advanced-advance-probability bound.**  Mirrors
`Phase2Convergence.informed_advance_prob_of_rect`, with `advancedU` as the
advancing quantity. -/
theorem advanced_advance_prob_of_rect (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hcardn : c.card = n)
    (R : Finset (AgentState L K × AgentState L K)) (N : ℕ)
    (hadv : ∀ p ∈ R, 1 ≤ c.count p.1 → 1 ≤ c.count p.2 → (p.1 = p.2 → 2 ≤ c.count p.1) →
      advancedU (L := L) (K := K) c + 1
        ≤ advancedU (L := L) (K := K) (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2))
    (hcount : (N : ℕ) ≤ ∑ p ∈ R, c.interactionCount p.1 p.2) :
    ENNReal.ofReal ((N : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | advancedU (L := L) (K := K) c + 1 ≤ advancedU (L := L) (K := K) c'} := by
  set j := advancedU (L := L) (K := K) c with hjdef
  have hcard2 : 2 ≤ c.card := by rw [hcardn]; omega
  have hmeas : MeasurableSet {c' : Config (AgentState L K) | j + 1 ≤ advancedU c'} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  set S : Finset (AgentState L K × AgentState L K) :=
    R.filter (fun p => 1 ≤ c.count p.1 ∧ 1 ≤ c.count p.2 ∧ (p.1 = p.2 → 2 ≤ c.count p.1)) with hS
  have hsub : (↑S : Set (AgentState L K × AgentState L K)) ⊆
      (Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
        {c' | j + 1 ≤ advancedU c'} := by
    intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hS] at hp
    obtain ⟨hpc, hp1, hp2, hp3⟩ := hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Protocol.scheduledStep]
    exact hadv p hpc hp1 hp2 hp3
  have hstepDist : (NonuniformMajority L K).stepDistOrSelf c
      = (NonuniformMajority L K).stepDist c hcard2 := by
    unfold Protocol.stepDistOrSelf; rw [dif_pos hcard2]
  have hbase : ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | j + 1 ≤ advancedU c'}
      = (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | j + 1 ≤ advancedU c'}) := by
    rw [hstepDist]; unfold Protocol.stepDist
    rw [PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete) hmeas]
  rw [hbase]
  have hmono : (c.interactionPMF hcard2).toMeasure (↑S : Set _)
      ≤ (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | j + 1 ≤ advancedU c'}) :=
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

/-! ## Part E — the advanced×susceptible rectangle and the SYNC advance prob. -/

/-- For two state-finsets `A`, `B` of pairwise-distinct states, the
`interactionCount` mass of `A ×ˢ B` is `(∑_A count)·(∑_B count)`.  (Local copy of
`Phase2Convergence.sum_interactionCount_cross_disjoint'`.) -/
theorem sum_interactionCount_cross_disjoint
    (c : Config (AgentState L K)) (A B : Finset (AgentState L K))
    (hdisj : ∀ a ∈ A, ∀ b ∈ B, a ≠ b) :
    (∑ p ∈ A ×ˢ B, c.interactionCount p.1 p.2)
      = (∑ a ∈ A, c.count a) * (∑ b ∈ B, c.count b) := by
  rw [Finset.sum_product, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  unfold Config.interactionCount
  rw [if_neg (hdisj a ha b hb)]

/-- `∑ count` over the advanced STATES equals `advancedU c`. -/
theorem sum_count_advanced (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => advancedP a), c.count a)
      = advancedU (L := L) (K := K) c := by
  have hcard : (Multiset.filter (fun a : AgentState L K => advancedP a) c).card
      = advancedU (L := L) (K := K) c := by
    unfold advancedU; rw [Multiset.countP_eq_card_filter]
  rw [← hcard]
  have hcount_eq : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => advancedP a),
      c.count a
        = Multiset.count a (Multiset.filter (fun a : AgentState L K => advancedP a) c) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Config.count, Multiset.count_filter, if_pos ha.2]
  rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
  intro a ha
  rw [Multiset.mem_filter] at ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩

/-- `∑ count` over the susceptible STATES equals `countP susceptibleP c`. -/
theorem sum_count_susceptible (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter (fun a : AgentState L K => susceptibleP a), c.count a)
      = Multiset.countP (fun a => susceptibleP a) c := by
  have hcard : (Multiset.filter (fun a : AgentState L K => susceptibleP a) c).card
      = Multiset.countP (fun a => susceptibleP a) c := by
    rw [Multiset.countP_eq_card_filter]
  rw [← hcard]
  have hcount_eq : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => susceptibleP a),
      c.count a
        = Multiset.count a (Multiset.filter (fun a : AgentState L K => susceptibleP a) c) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Config.count, Multiset.count_filter, if_pos ha.2]
  rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
  intro a ha
  rw [Multiset.mem_filter] at ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩

/-- On the window `Q4 n`, every agent is advanced (`phase ≥ 5`) XOR susceptible
(`phase = 4`), so `advancedU + susceptibleU = n`.  Hence the susceptible count is
`n − advancedU`. -/
theorem susceptible_count_eq (n : ℕ) (c : Config (AgentState L K)) (hw : Q4 n c) :
    Multiset.countP (fun a => susceptibleP a) c = n - advancedU (L := L) (K := K) c := by
  unfold advancedU
  have hsplit : Multiset.countP (fun a => advancedP a) c
      + Multiset.countP (fun a => susceptibleP a) c = c.card := by
    rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter, ← Multiset.card_add]
    congr 1
    refine Multiset.ext.mpr ?_
    intro a
    rw [Multiset.count_add, Multiset.count_filter, Multiset.count_filter]
    by_cases hmem : a ∈ c
    · have hp4 := hw.2 a hmem
      by_cases hadv : advancedP (L := L) (K := K) a
      · have hnsus : ¬ susceptibleP (L := L) (K := K) a := by
          simp only [advancedP, susceptibleP] at hadv ⊢; omega
        rw [if_pos hadv, if_neg hnsus]; omega
      · have hsus : susceptibleP (L := L) (K := K) a := by
          simp only [advancedP, susceptibleP] at hadv ⊢; omega
        rw [if_neg hadv, if_pos hsus]; omega
    · have h0 : Multiset.count a c = 0 := Multiset.count_eq_zero.mpr hmem
      rw [h0]; simp
  rw [hw.1] at hsplit
  omega

/-- The advanced×susceptible rectangle `interactionCount` mass is `m·(n−m)`,
`m = advancedU c` (cross pairs distinct: advanced `phase ≥ 5`, susceptible
`phase = 4`). -/
theorem sum_interactionCount_syncRect (n : ℕ) (c : Config (AgentState L K)) (hw : Q4 n c) :
    (∑ p ∈ (Finset.univ.filter (fun a : AgentState L K => advancedP a)) ×ˢ
        (Finset.univ.filter (fun a : AgentState L K => susceptibleP a)),
        c.interactionCount p.1 p.2)
      = advancedU (L := L) (K := K) c * (n - advancedU (L := L) (K := K) c) := by
  rw [sum_interactionCount_cross_disjoint c _ _ ?_, sum_count_advanced,
      sum_count_susceptible, susceptible_count_eq n c hw]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  intro hab
  have haA : advancedP (L := L) (K := K) a := ha.2
  have hbS : susceptibleP (L := L) (K := K) b := hb.2
  rw [hab] at haA
  simp only [advancedP, susceptibleP] at haA hbS; omega

/-- **The SYNC advanced-advance probability (DERIVED).**  One step raises
`advancedU` by `≥ 1` with probability `≥ m·(n−m)/(n(n−1))`, `m = advancedU c`. -/
theorem advanced_advance_prob (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hw : Q4 n c) :
    ENNReal.ofReal
        (((advancedU (L := L) (K := K) c * (n - advancedU (L := L) (K := K) c) : ℕ) : ℝ)
          / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | advancedU (L := L) (K := K) c + 1 ≤ advancedU (L := L) (K := K) c'} := by
  set R := (Finset.univ.filter (fun a : AgentState L K => advancedP a)) ×ˢ
    (Finset.univ.filter (fun a : AgentState L K => susceptibleP a)) with hR
  set m := advancedU (L := L) (K := K) c with hmdef
  have hcount : m * (n - m) ≤ ∑ p ∈ R, c.interactionCount p.1 p.2 := by
    rw [hR, sum_interactionCount_syncRect n c hw]
  refine advanced_advance_prob_of_rect n hn c hw.1 R (m * (n - m)) ?_ hcount
  · rintro ⟨a, b⟩ hp h1 h2 _hsame
    rw [hR, Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨_, haA⟩, ⟨_, hbS⟩⟩ := hp
    have haadv : advancedP (L := L) (K := K) a := haA
    have hbsus : susceptibleP (L := L) (K := K) b := hbS
    have ha4 : 4 ≤ a.phase.val := by simp only [advancedP] at haadv; omega
    have hb4 : 4 ≤ b.phase.val := by simp only [susceptibleP] at hbsus; omega
    have hbnadv : ¬ advancedP (L := L) (K := K) b := by
      simp only [advancedP, susceptibleP] at hbsus ⊢; omega
    have hamem : a ∈ c := Multiset.one_le_count_iff_mem.mp h1
    have hbmem : b ∈ c := Multiset.one_le_count_iff_mem.mp h2
    have hab : a ≠ b := by
      intro h; rw [h] at haadv; exact hbnadv haadv
    have happ : Protocol.Applicable c a b := applicable_of_mem_distinct hamem hbmem hab
    exact advancedU_stepOrSelf_advance c a b happ ha4 hb4 (Or.inl ⟨haadv, hbnadv⟩)

/-! ## Part F — the window `Q4` is one-step closed, and the deficit potential. -/

/-- `Q4 n` is preserved by a single chosen-pair update (phase only rises, card
preserved). -/
theorem Q4_stepOrSelf (n : ℕ) (c : Config (AgentState L K)) (hw : Q4 n c)
    (r₁ r₂ : AgentState L K) :
    Q4 n (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hmem1 := mem_of_applicable_left happ
    have hmem2 := mem_of_applicable_right happ
    have h1p := hw.2 r₁ hmem1
    have h2p := hw.2 r₂ hmem2
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    have hmono := Transition_phase_monotone (L := L) (K := K) r₁ r₂
    simp only [] at hmono
    obtain ⟨hsm, htm⟩ := hmono
    refine ⟨?_, ?_⟩
    · have hcard := Protocol.reachable_card_eq
        (Protocol.reachable_stepOrSelf (P := NonuniformMajority L K) c r₁ r₂)
      rw [hcard]; exact hw.1
    · intro a ha
      rw [hc'] at ha
      rcases Multiset.mem_add.mp ha with hold | hnew
      · exact hw.2 a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hold)
      · rw [show ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
              : Multiset (AgentState L K))
            = (Transition L K r₁ r₂).1 ::ₘ (Transition L K r₁ r₂).2 ::ₘ 0 from rfl] at hnew
        simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hnew
        rcases hnew with h | h
        · subst h; exact le_trans h1p hsm
        · subst h; exact le_trans h2p htm
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; exact hw

/-- `Q4 n` is one-step-support closed. -/
theorem Q4_absorbing (n : ℕ) (c c' : Config (AgentState L K)) (hw : Q4 n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    Q4 n c' := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact Q4_stepOrSelf n c hw r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'
    subst hc'; exact hw

/-- The clamped advanced count `min (advancedU c) n`. -/
def aClamp (n : ℕ) (c : Config (AgentState L K)) : ℕ := min (advancedU (L := L) (K := K) c) n

/-- "Finished": all `n` agents are advanced (`phase ≥ 5`). -/
def advFinished (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  n ≤ advancedU (L := L) (K := K) c

instance (n : ℕ) (c : Config (AgentState L K)) : Decidable (advFinished n c) := by
  unfold advFinished; infer_instance

/-- The exponential-window deficit potential: `0` when finished, else
`ofReal(exp(s·(n − aClamp)))`.  Mirrors `Phase2Convergence.oDeficitPot`. -/
noncomputable def aDeficitPot (n : ℕ) (s : ℝ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  if advFinished (L := L) (K := K) n c then 0
  else ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (aClamp (L := L) (K := K) n c : ℝ))))

theorem aDeficitPot_measurable (n : ℕ) (s : ℝ) :
    Measurable (aDeficitPot n s (L := L) (K := K)) :=
  Measurable.of_discrete

theorem aDeficitPot_eq_of_lt (n : ℕ) (s : ℝ) (c : Config (AgentState L K))
    (hlt : advancedU (L := L) (K := K) c < n) :
    aDeficitPot n s c
      = ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (advancedU (L := L) (K := K) c : ℝ)))) := by
  unfold aDeficitPot advFinished aClamp
  rw [if_neg (by omega)]
  congr 2
  rw [min_eq_left (le_of_lt hlt)]

theorem not_finished_imp_aDeficitPot_ge_one (n : ℕ) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hc : ¬ advFinished (L := L) (K := K) n c) :
    (1 : ℝ≥0∞) ≤ aDeficitPot n s c := by
  have hlt : advancedU (L := L) (K := K) c < n := by unfold advFinished at hc; omega
  rw [aDeficitPot_eq_of_lt n s c hlt]
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm]
  apply ENNReal.ofReal_le_ofReal
  rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
  apply Real.exp_le_exp.mpr
  have hdef : (1 : ℝ) ≤ (n : ℝ) - (advancedU (L := L) (K := K) c : ℝ) := by
    have : (advancedU (L := L) (K := K) c : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hlt
    linarith
  nlinarith [hs, hdef]

theorem advFinished_absorbing (n : ℕ) (c c' : Config (AgentState L K))
    (hfin : advFinished (L := L) (K := K) n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    advFinished (L := L) (K := K) n c' := by
  unfold advFinished at hfin ⊢
  exact advancedU_ge_monotone n c c' hfin hc'

/-- Pointwise one-step bound on the deficit potential, using the PROVEN
monotonicity `advancedU_ge_monotone`. -/
theorem aDeficitPot_pointwise_bound (n : ℕ) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (m : ℕ)
    (_hm : advancedU (L := L) (K := K) c = m) (_hm_hi : m < n)
    (c' : Config (AgentState L K)) (hmono : m ≤ advancedU (L := L) (K := K) c') :
    aDeficitPot n s c' ≤
      (if m + 1 ≤ advancedU (L := L) (K := K) c' then
        ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (m : ℝ) - 1)))
      else
        ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (m : ℝ))))) := by
  unfold aDeficitPot advFinished aClamp
  by_cases hfin : n ≤ advancedU (L := L) (K := K) c'
  · rw [if_pos hfin]; split_ifs <;> exact bot_le
  · rw [if_neg hfin]
    rw [not_le] at hfin
    by_cases hadv : m + 1 ≤ advancedU (L := L) (K := K) c'
    · rw [if_pos hadv]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      rw [min_eq_left (le_of_lt hfin)]
      have : (m : ℝ) + 1 ≤ (advancedU (L := L) (K := K) c' : ℝ) := by exact_mod_cast hadv
      nlinarith [hs, this]
    · rw [if_neg hadv]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      rw [min_eq_left (le_of_lt hfin)]
      have hle : (m : ℝ) ≤ (advancedU (L := L) (K := K) c' : ℝ) := by exact_mod_cast hmono
      nlinarith [hs, hle]

/-! ## Part G — the genuine one-step advanced-count drift. -/

/-- The PROVEN advance-fraction floor: for `1 ≤ m ≤ n−1`, `n − 1 ≤ m·(n−m)`.
(Local copy of `Phase2Convergence.advance_floor`.) -/
theorem advance_floor (n m : ℕ) (h1 : 1 ≤ m) (hlt : m < n) : n - 1 ≤ m * (n - m) := by
  obtain ⟨k, hk⟩ : ∃ k, n = m + k ∧ 1 ≤ k := ⟨n - m, by omega, by omega⟩
  obtain ⟨hnk, hk1⟩ := hk
  subst hnk
  rw [Nat.add_sub_cancel_left]
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, k = b + 1 := ⟨k - 1, by omega⟩
  have : (a + 1) * (b + 1) = a * b + a + b + 1 := by ring
  omega

/-- **The genuine Phase-4 non-tie advanced-count drift.**  On the window `Q4 n`
with `n ≥ 2`, in the unfinished regime (`advancedU c < n`), the deficit potential
contracts at the GENUINE rate `r = 1 − ((n−1)/(n(n−1)))·(1 − e^{−s})`. -/
theorem phase4AdvancedDrift (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hQ : Q4 n c)
    (hlo : 1 ≤ advancedU (L := L) (K := K) c) (hnc : advancedU (L := L) (K := K) c < n) :
    ∫⁻ c', aDeficitPot n s c' ∂((NonuniformMajority L K).transitionKernel c) ≤
      ENNReal.ofReal (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s)))
        * aDeficitPot n s c := by
  set m := advancedU (L := L) (K := K) c with hm
  have hΦc : aDeficitPot n s c
      = ENNReal.ofReal (Real.exp (s * ((n : ℝ) - (m : ℝ)))) :=
    aDeficitPot_eq_of_lt n s c hnc
  set A := {c' : Config (AgentState L K) | m + 1 ≤ advancedU (L := L) (K := K) c'} with hA_def
  have hA_meas : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
  set pR : ℝ := (((n - 1 : ℕ)) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) with hpR
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden_pos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hfloorN : n - 1 ≤ m * (n - m) := advance_floor n m hlo hnc
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
  have hstep : ENNReal.ofReal pR ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure A := by
    have hadv := advanced_advance_prob n hn c hQ
    rw [← hm] at hadv
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hadv
    rw [hpR]
    apply (div_le_div_iff_of_pos_right hden_pos).mpr
    exact hfloorR
  change ∫⁻ c', aDeficitPot n s c'
    ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure ≤ _
  calc ∫⁻ c', aDeficitPot n s c'
        ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      ≤ ∫⁻ c', (if m + 1 ≤ advancedU (L := L) (K := K) c' then ENNReal.ofReal E1
          else ENNReal.ofReal E0) ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure := by
        apply lintegral_mono_ae
        rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]
        intro x hsupp hbad
        apply hbad
        have hmono_x : m ≤ advancedU (L := L) (K := K) x :=
          advancedU_ge_monotone m c x (le_of_eq hm.symm) hsupp
        exact aDeficitPot_pointwise_bound n s hs c m hm.symm hnc x hmono_x
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
    _ ≤ ENNReal.ofReal (1 - pR * (1 - Real.exp (-s))) * aDeficitPot n s c := by
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

/-! ## Part H — the non-tie `PhaseConvergence` on the REAL kernel. -/

/-- On `Pre` (at least one advanced agent), the deficit potential is at most
`ofReal(exp(s·(n−1)))`. -/
theorem aDeficitPot_le_pre (n : ℕ) (s : ℝ) (hs : 0 < s)
    (c : Config (AgentState L K)) (hlo : 1 ≤ advancedU (L := L) (K := K) c) :
    aDeficitPot n s c ≤ ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) := by
  unfold aDeficitPot aClamp
  by_cases hfin : advFinished (L := L) (K := K) n c
  · rw [if_pos hfin]; exact bot_le
  · rw [if_neg hfin]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hmin : (min (advancedU (L := L) (K := K) c) n : ℕ) = advancedU (L := L) (K := K) c := by
      unfold advFinished at hfin; omega
    rw [hmin]
    have h1 : (1 : ℝ) ≤ (advancedU (L := L) (K := K) c : ℝ) := by exact_mod_cast hlo
    nlinarith [hs, h1]

/-- The full drift window: the non-tie window plus at least one advanced agent
(`1 ≤ advancedU`, the epidemic seed).  Both conjuncts are one-step closed. -/
def Qwin4 (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  Q4 n c ∧ 1 ≤ advancedU (L := L) (K := K) c

instance (n : ℕ) (c : Config (AgentState L K)) : Decidable (Qwin4 n c) := by
  unfold Qwin4; infer_instance

theorem Qwin4_absorbing (n : ℕ) (c c' : Config (AgentState L K)) (hw : Qwin4 n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    Qwin4 n c' :=
  ⟨Q4_absorbing n c c' hw.1 hc', advancedU_ge_monotone 1 c c' hw.2 hc'⟩

/-- The window-guarded deficit potential: `⊤` off `Qwin4`, else `aDeficitPot`. -/
noncomputable def aPotW (n : ℕ) (s : ℝ) (c : Config (AgentState L K)) : ℝ≥0∞ :=
  if Qwin4 n c then aDeficitPot n s c else ⊤

theorem aPotW_measurable (n : ℕ) (s : ℝ) :
    Measurable (aPotW n s (L := L) (K := K)) :=
  Measurable.of_discrete

theorem aPotW_eq_on_window (n : ℕ) (s : ℝ) (c : Config (AgentState L K))
    (hw : Qwin4 n c) : aPotW n s c = aDeficitPot n s c := by
  unfold aPotW; rw [if_pos hw]

/-- **The Phase-4 NON-TIE advanced-count epidemic `PhaseConvergence` on the REAL
`NonuniformMajority L K` kernel.**

* `Pre c` = non-tie window `Q4 n` (every agent at phase `≥ 4`, size `n`) with at
  least one already-advanced (`phase ≥ 5`) seed agent — the epidemic source,
  provided by the upstream non-tie structure exactly as `Phase3Convergence`
  carries its `∃ a, 4 ≤ a.phase` source;
* `Post c` = `advFinished n c` (all `n` agents are at phase `≥ 5` — the population
  has advanced to Phase 5).

The drift `phase4AdvancedDrift` is GENUINELY DERIVED from the phase-`max` epidemic
mechanism + the DERIVED pair-counting advance probability `advanced_advance_prob`;
the window is PROVEN one-step closed (`Q4_absorbing`). -/
noncomputable def phase4NonTieConvergence (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s)
    (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal
            (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
            ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1
          ≤ (ε : ℝ≥0∞)) :
    PhaseConvergence (NonuniformMajority L K).transitionKernel := by
  refine WindowConcentration.windowDrift_PhaseConvergence (NonuniformMajority L K)
    (aPotW n s) (aPotW_measurable n s)
    (fun c => Qwin4 n c)
    (Qwin4_absorbing n)
    (ENNReal.ofReal
      (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))))
    ?_
    (fun c => Qwin4 n c)
    (fun c => Qwin4 n c ∧ advFinished (L := L) (K := K) n c)
    ?_
    1 one_ne_zero ENNReal.one_ne_top
    ?_
    (fun c h => h)
    (ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))))
    ?_
    t ε hε
  · -- hdrift
    intro c hQw
    obtain ⟨hQ, hlo⟩ := hQw
    rw [aPotW_eq_on_window n s c ⟨hQ, hlo⟩]
    have hint_eq : ∫⁻ c', aPotW n s c'
          ∂((NonuniformMajority L K).transitionKernel c)
        = ∫⁻ c', aDeficitPot n s c'
          ∂((NonuniformMajority L K).transitionKernel c) := by
      apply lintegral_congr_ae
      change ∀ᵐ c' ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure,
        aPotW n s c' = aDeficitPot n s c'
      rw [ae_iff, PMF.toMeasure_apply_eq_zero_iff _
        (DiscreteMeasurableSpace.forall_measurableSet _)]
      rw [Set.disjoint_left]
      intro x hsupp hbad
      apply hbad
      exact aPotW_eq_on_window n s x (Qwin4_absorbing n c x ⟨hQ, hlo⟩ hsupp)
    rw [hint_eq]
    by_cases hfin : advFinished (L := L) (K := K) n c
    · have hΦc0 : aDeficitPot n s c = 0 := by unfold aDeficitPot; rw [if_pos hfin]
      rw [hΦc0, mul_zero, nonpos_iff_eq_zero]
      change ∫⁻ c', aDeficitPot n s c'
          ∂((NonuniformMajority L K).stepDistOrSelf c).toMeasure = 0
      rw [lintegral_eq_zero_iff (aDeficitPot_measurable n s)]
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨((NonuniformMajority L K).stepDistOrSelf c).support, ?_, ?_⟩
      · rw [mem_ae_iff, PMF.toMeasure_apply_eq_zero_iff _
          (DiscreteMeasurableSpace.forall_measurableSet _)]
        rw [Set.disjoint_left]; intro x hsupp hx
        exact hx (PMF.mem_support_iff _ _ |>.mp hsupp)
      · intro c' hc'
        have hfin' : advFinished (L := L) (K := K) n c' :=
          advFinished_absorbing n c c' hfin hc'
        change aDeficitPot n s c' = 0
        unfold aDeficitPot; rw [if_pos hfin']
    · have hnc : advancedU (L := L) (K := K) c < n := by unfold advFinished at hfin; omega
      exact phase4AdvancedDrift n hn s hs c hQ hlo hnc
  · -- hPost_abs
    rintro c c' ⟨hQw, hfin⟩ hc'
    exact ⟨Qwin4_absorbing n c c' hQw hc',
      advFinished_absorbing n c c' hfin hc'⟩
  · -- hlink
    intro c hnp
    unfold aPotW
    by_cases hQw : Qwin4 n c
    · rw [if_pos hQw]
      have hnf : ¬ advFinished (L := L) (K := K) n c := fun hfin => hnp ⟨hQw, hfin⟩
      exact not_finished_imp_aDeficitPot_ge_one n s hs c hnf
    · rw [if_neg hQw]; exact le_top
  · -- hPre_bound
    intro c hPre
    rw [aPotW_eq_on_window n s c hPre]
    exact aDeficitPot_le_pre n s hs c hPre.2

/-! ## Part I — the tie branch is deterministic with `ε = 0`, and the unified
Phase-4 instance. -/

/-- `StableTie4` is kernel-absorbing in the `K x {¬Post} = 0` form. -/
theorem StableTie4_kernel_absorbing (c : Config (AgentState L K))
    (hc : StableTie4 (L := L) (K := K) c) :
    (NonuniformMajority L K).transitionKernel c
      {c' | ¬ StableTie4 (L := L) (K := K) c'} = 0 := by
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {c' | ¬ StableTie4 (L := L) (K := K) c'} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hbad
  exact hbad (StableTie4_absorbing c x hc hsupp)

/-- The multi-step tie tail is exactly `0`: from a tie configuration, after any
number of interactions the population is still a stable tie. -/
theorem StableTie4_pow_tail (t : ℕ) (c : Config (AgentState L K))
    (hc : StableTie4 (L := L) (K := K) c) :
    ((NonuniformMajority L K).transitionKernel ^ t) c
      {c' | ¬ StableTie4 (L := L) (K := K) c'} = 0 := by
  induction t generalizing c with
  | zero =>
    simp only [pow_zero]
    change (Kernel.id c) {c' | ¬ StableTie4 (L := L) (K := K) c'} = 0
    rw [Kernel.id_apply]
    rw [show {c' : Config (AgentState L K) | ¬ StableTie4 (L := L) (K := K) c'}
        = {c | StableTie4 (L := L) (K := K) c}ᶜ from by ext y; simp]
    rw [Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
    simp [hc]
  | succ t ih =>
    have hmeas : MeasurableSet {c' : Config (AgentState L K) | ¬ StableTie4 (L := L) (K := K) c'} :=
      DiscreteMeasurableSpace.forall_measurableSet _
    rw [Kernel.pow_succ_apply_eq_lintegral _ t c hmeas]
    rw [lintegral_eq_zero_iff (Kernel.measurable_coe _ hmeas)]
    -- a.e. (under (K^t) c) the inner one-step tail is 0, because (K^t) c lives on tie configs.
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨{c' | StableTie4 (L := L) (K := K) c'}, ?_, ?_⟩
    · rw [mem_ae_iff]
      rw [show {c' : Config (AgentState L K) | StableTie4 (L := L) (K := K) c'}ᶜ
          = {c' | ¬ StableTie4 (L := L) (K := K) c'} from by ext y; simp]
      exact ih c hc
    · intro y hy
      simp only [Set.mem_setOf_eq] at hy
      change (NonuniformMajority L K).transitionKernel y
        {c' | ¬ StableTie4 (L := L) (K := K) c'} = 0
      exact StableTie4_kernel_absorbing y hy

/-- The multi-step carded-tie tail is exactly zero. -/
theorem StableTie4Card_pow_tail (n t : ℕ) (c : Config (AgentState L K))
    (hc : StableTie4Card (L := L) (K := K) n c) :
    ((NonuniformMajority L K).transitionKernel ^ t) c
      {c' | ¬ StableTie4Card (L := L) (K := K) n c'} = 0 :=
  Protocol.transitionKernel_pow_not_pred_eq_zero_of_stepDistOrSelf_support_preserved
    (NonuniformMajority L K)
    (fun c' : Config (AgentState L K) =>
      StableTie4Card (L := L) (K := K) n c')
    (StableTie4Card_absorbing (L := L) (K := K) n)
    c hc t

/-- Slot-4's public postcondition keeps the card-`n` fact on both branches. -/
def Phase4Post (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧
    (StableTie4 (L := L) (K := K) c ∨
      advFinished (L := L) (K := K) n c)

instance (n : ℕ) (c : Config (AgentState L K)) : Decidable (Phase4Post n c) := by
  unfold Phase4Post; infer_instance

/-- The carded slot-4 post is one-step-support closed. -/
theorem Phase4Post_absorbing (n : ℕ) (c c' : Config (AgentState L K))
    (hw : Phase4Post (L := L) (K := K) n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    Phase4Post (L := L) (K := K) n c' := by
  refine ⟨?_, ?_⟩
  · rw [Protocol.stepDistOrSelf_support_card_eq (NonuniformMajority L K) c c' hc']
    exact hw.1
  · rcases hw.2 with hTie | hAdv
    · exact Or.inl (StableTie4_absorbing (L := L) (K := K) c c' hTie hc')
    · exact Or.inr (advFinished_absorbing (L := L) (K := K) n c c' hAdv hc')

/-- **The unified Phase-4 instance** (`PhaseConvergenceW` on the REAL kernel).

* `Pre c`  = `StableTie4Card n c ∨ Qwin4 n c` — either the tie window
  with the ambient population size, or the non-tie window (all phase `≥ 4`,
  size `n`) with an advanced seed.
* `Post c` = `Phase4Post n c` — the card-`n` stable tie output `T`, or
  the card-`n` population has advanced to Phase `≥ 5` (ready for Phase 5).

The tie branch converges *deterministically* with failure `0` (`StableTie4_pow_tail`);
the non-tie branch converges via the genuine advanced-count epidemic
(`phase4NonTieConvergence`).  The single horizon `t` and failure `ε` are those of
the non-tie epidemic (the tie branch contributes `0`). -/
noncomputable def phase4Convergence (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s)
    (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal
            (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
            ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1
          ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre := fun c => StableTie4Card (L := L) (K := K) n c ∨ Qwin4 (L := L) (K := K) n c
  Post := fun c => Phase4Post (L := L) (K := K) n c
  t := t
  ε := ε
  convergence := by
    intro c₀ hPre
    set NT := phase4NonTieConvergence (L := L) (K := K) n hn s hs t ε hε with hNT
    have hsubsetTie : {c' : Config (AgentState L K) |
        ¬ Phase4Post (L := L) (K := K) n c'}
          ⊆ {c' | ¬ StableTie4Card (L := L) (K := K) n c'} := by
      intro c' hc'
      intro hTie
      exact hc' ⟨hTie.1, Or.inl hTie.2⟩
    rcases hPre with hTie | hNTpre
    · calc ((NonuniformMajority L K).transitionKernel ^ t) c₀
              {c' | ¬ Phase4Post (L := L) (K := K) n c'}
          ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
              {c' | ¬ StableTie4Card (L := L) (K := K) n c'} := measure_mono hsubsetTie
        _ = 0 := StableTie4Card_pow_tail n t c₀ hTie
        _ ≤ (ε : ℝ≥0∞) := zero_le'
    · have hNTconv := NT.convergence c₀ hNTpre
      have hPostsub : {c' : Config (AgentState L K) |
          ¬ Phase4Post (L := L) (K := K) n c'}
            ⊆ {c' | ¬ (Qwin4 (L := L) (K := K) n c'
                ∧ advFinished (L := L) (K := K) n c')} := by
        intro c' hc'
        intro hQ
        exact hc' ⟨hQ.1.1.1, Or.inr hQ.2⟩
      calc ((NonuniformMajority L K).transitionKernel ^ t) c₀
              {c' | ¬ Phase4Post (L := L) (K := K) n c'}
          ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
              {c' | ¬ (Qwin4 (L := L) (K := K) n c'
                ∧ advFinished (L := L) (K := K) n c')} := measure_mono hPostsub
        _ ≤ (ε : ℝ≥0∞) := hNTconv

end Phase4Convergence

end ExactMajority
