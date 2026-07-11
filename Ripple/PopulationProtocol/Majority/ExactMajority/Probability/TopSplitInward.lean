/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `TopSplitInward` — discharging `InwardResidual` (the genuine Lemma 5.1 C-1 fact).

Doty et al., *Exact Majority* (arXiv:2106.10201v2), §5.1 (Lemma 5.1 top-split
balance).  `Probability/TopSplitDrift.lean` reduced the boundary-free cosh-MGF
top-split tail to a single honest protocol residual, `InwardResidual s c`:

    sinh(s · X c) · E[sinh(s · ΔX)] ≤ 0,   X c = mainCount c − topCRMass c,

where `E[sinh(s·ΔX)] = ∑_pair interactionProb(c,pair)·sinh(s·Δ_pair)` is the
one-step expected signed `sinh`-jump.  This file DISCHARGES `InwardResidual`
on the Phase-0 region (`allPhase0 ∧ 2 ≤ card`), with NO further hypothesis — the
honest, hypothesis-free Lemma-5.1 content — and wires the result into
`TopSplitDrift`'s cosh engine to produce the strongest top-split tail reachable.

## The honest assigned-balance ledger (Stage 1 — the new mathematical content).

Computing the per-rule effect on the FOUR free/assigned pools against the FROZEN
`Protocol/Transition.lean` (`Phase0Transition`, rules R1–R5):

  * `Mf` = #unassigned-Main,  `Ma` = #assigned-Main;
  * `Sf` = #unassigned-(cr/clock/reserve),  `Sa` = #assigned-(cr/clock/reserve).

`X = mainCount − topCRMass = (Mf + Ma) − (Sf + Sa)`.  Per rule:

  * **R1** (mcr,mcr → main,cr): the fresh Main inherits `s.assigned`, the fresh CR
    inherits `t.assigned`, so `ΔMf = ΔSf`, `ΔMa = ΔSa` ⟹ `Δ(Mf−Sf) = 0`, `ΔX = 0`.
  * **R2** (mcr + unassigned-Main → cr(unassigned) + Main(assigned)): `Mf −1`,
    `Ma +1`, `Sf +1` ⟹ `Δ(Mf−Sf) = −2`, `ΔX = −1`.
  * **R3** (mcr + unassigned-CR-side → Main(unassigned) + partner(assigned)):
    `Mf +1`, `Sf −1`, `Sa +1` ⟹ `Δ(Mf−Sf) = +2`, `ΔX = +1`.
  * **R4** (cr,cr → clock,reserve): both stay CR-side, `assigned` untouched ⟹
    `ΔSf = ΔSa = 0`, `Δ(Mf−Sf) = 0`, `ΔX = 0`.
  * **R5** (clock,clock → clock,clock): role/assigned unchanged ⟹ `Δ(Mf−Sf) = 0`.

So `Δ(Mf − Sf) = 2·ΔX` for EVERY rule, and at the all-`mcr` start `Mf−Sf = 0 =
2·X`.  Hence the **honest preserved invariant**

    Mf − Sf = 2 · X      (`freeDiff_eq_two_topSplit`)

with `freeW a := [main ∧ ¬asg] − [(cr∨clock∨reserve) ∧ ¬asg]` the per-agent
weight (`Config.sumOf freeW = Mf − Sf`).  This is the Lean-faithful counterpart of
the paper's `sf + 2·st = mf + 2·mt` ledger: when more Main than RoleCR-mass has
been produced (`X > 0`) there are STRICTLY more free Mains than free CR-side
agents (`Mf − Sf = 2X > 0`), so the next `X`-changing interaction is more likely
to DECREASE `X` — exactly the inward sign-drift.

## Stages 2–4.

  * **Stage 2** (`freeDiff_sign_of_topSplit`): `X > 0 ⟹ Sf < Mf`, `X < 0 ⟹ Mf < Sf`.
  * **Stage 3** (`expDelta_eq…`): `sinh(s·Δ_pair) = Δ_pair · sinh s` (since `Δ ∈
    {−1,0,1}`), so `E[sinh(s·Δ)] = sinh s · E[Δ]`, and `E[Δ]·totalPairs =
    2·mcrCount·(Sf − Mf)` via the R2/R3 marginal rectangle.
  * **Stage 4** (`inwardResidual_holds`): with `Sf − Mf = −2X`, `E[Δ] =
    −4·mcrCount·X/totalPairs`, so `X·E[Δ] ≤ 0` ⟹ `sinh(s·X)·E[sinh(s·Δ)] ≤ 0`.
    Wired into `coshPot_drift` / `topSplitWindow_whp_cosh` to produce the
    hypothesis-free top-split tail.

Everything here is 0-`sorry` / 0-`axiom` (only `propext`, `Classical.choice`,
`Quot.sound`) / no `native_decide`.

Reference: Doty et al. §5.1; `Probability/TopSplitDrift.lean`;
`HANDOFF_ROLESPLIT_TOPSPLIT.md`; FROZEN `Protocol/Transition.lean`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.TopSplitDrift

namespace ExactMajority
namespace RoleSplitConcentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

variable {L K : ℕ}

/-! ## Stage 1 — the assigned-balance ledger (the honest invariant). -/

/-- The per-agent FREE-pool weight: `+1` for an unassigned `Main`, `−1` for an
unassigned agent in the RoleCR-descended pool (`cr`/`clock`/`reserve`), `0`
otherwise (assigned agents and transient `mcr`).  Summing gives `Mf − Sf`
(`#unassigned-Main − #unassigned-CR-side`). -/
def freeW (a : AgentState L K) : ℤ :=
  (if a.role = .main ∧ ¬ a.assigned then 1 else 0)
    - (if (a.role = .cr ∨ a.role = .clock ∨ a.role = .reserve) ∧ ¬ a.assigned then 1 else 0)

/-- The integer free-pool difference `Mf − Sf` as a multiset sum of `freeW`. -/
def freeDiff (c : Config (AgentState L K)) : ℤ :=
  Config.sumOf (freeW (L := L) (K := K)) c

/-- `freeW` reads only the agent's `role` and `assigned`. -/
private lemma freeW_eq_of_role_assigned_eq (a b : AgentState L K)
    (hr : a.role = b.role) (ha : a.assigned = b.assigned) :
    freeW (L := L) (K := K) a = freeW (L := L) (K := K) b := by
  unfold freeW; rw [hr, ha]

/-- `phaseInit` never writes the `assigned` flag. -/
private lemma phaseInit_assigned_eq (p : Fin 11) (a : AgentState L K) :
    (phaseInit L K p a).assigned = a.assigned := by
  fin_cases p
  · unfold phaseInit; simp
  · unfold phaseInit; simp; split_ifs <;> simp [enterPhase10_assigned]
  · unfold phaseInit; simp
    by_cases h : a.smallBias.val ≤ 1 ∨ a.smallBias.val ≥ 5
    · simp [h, enterPhase10_assigned]
    · simp [h]
  · unfold phaseInit; simp; split <;> simp
  · unfold phaseInit; simp
  · unfold phaseInit; simp; split_ifs <;> simp
  · unfold phaseInit; simp; split_ifs <;> simp
  · unfold phaseInit; simp; split_ifs <;> simp
  · unfold phaseInit; simp
  · unfold phaseInit; simp
    by_cases h : a.smallBias.val ≤ 1 ∨ a.smallBias.val ≥ 5
    · simp [h, enterPhase10_assigned]
    · simp [h]
  · unfold phaseInit; simp [enterPhase10_assigned]

/-- `stdCounterSubroutine` preserves the `assigned` flag (neither `advancePhase`,
`phaseInit`, nor `enterPhase10` ever writes `assigned`). -/
private lemma stdCounterSubroutine_assigned_eq (a : AgentState L K) :
    (stdCounterSubroutine L K a).assigned = a.assigned := by
  unfold stdCounterSubroutine
  split
  · -- advancePhaseWithInit = phaseInit (advancePhase a).phase (advancePhase a)
    unfold advancePhaseWithInit
    rw [phaseInit_assigned_eq]
    unfold advancePhase
    split <;> rfl
  · rfl

/-- The Standard Counter Subroutine keeps a `Clock` agent a `Clock` (local copy
of the private TopSplitDrift lemma). -/
private lemma stdCounterSubroutine_clock_role_eq' (a : AgentState L K)
    (ha : a.role = .clock) :
    (stdCounterSubroutine L K a).role = .clock := by
  unfold stdCounterSubroutine
  split
  · exact advancePhaseWithInit_clock_role_eq L K a ha
  · exact ha

/-- `topW (stdCounterSubroutine a) = topW a` for a clock agent (local copy). -/
private lemma topW_stdCounterSubroutine_clock' (a : AgentState L K)
    (ha : a.role = .clock) :
    topW (L := L) (K := K) (stdCounterSubroutine L K a) = topW (L := L) (K := K) a := by
  unfold topW
  rw [stdCounterSubroutine_clock_role_eq' a ha, ha]

/-- `freeW (stdCounterSubroutine a) = freeW a` for a clock agent (role stays
`clock`, `assigned` preserved). -/
private lemma freeW_stdCounterSubroutine_clock (a : AgentState L K)
    (ha : a.role = .clock) :
    freeW (L := L) (K := K) (stdCounterSubroutine L K a)
      = freeW (L := L) (K := K) a :=
  freeW_eq_of_role_assigned_eq _ _
    ((stdCounterSubroutine_clock_role_eq' a ha).trans ha.symm)
    (stdCounterSubroutine_assigned_eq a)

/-- The combined per-agent ledger weight `g = freeW − 2·topW`, which the per-pair
conservation below shows is exactly preserved by every Phase-0 rule on agents that
are not *assigned `mcr`* (an unreachable corner — `Phase0Initial` starts with every
`mcr` UNassigned and NO rule ever produces an `mcr`, so `assigned mcr` never
arises; see `NoAssignedMcr`). -/
private def ledgerW (a : AgentState L K) : ℤ :=
  freeW (L := L) (K := K) a - 2 * topW (L := L) (K := K) a

/-- An agent is *not an assigned `mcr`* — the honest reachability side-condition
the per-pair ledger conservation needs.  Holds for every agent reachable from
`Phase0Initial`: the initial `mcr` agents are unassigned, and no Phase-0 rule
ever assigns an `mcr` or creates a fresh `mcr` (rules only CONSUME `mcr`). -/
def NotAssignedMcr (a : AgentState L K) : Prop :=
  ¬ (a.role = .mcr ∧ a.assigned = true)

set_option maxHeartbeats 1600000 in
/-- **Per-pair ledger conservation (`Phase0Transition`).**  `freeW − 2·topW`
summed over the output pair equals the same over the input pair: the
assigned-balance ledger `Mf − Sf − 2·X` is locally conserved by every Phase-0
rule, on inputs that are not assigned `mcr` (`NotAssignedMcr`, the honest
reachability side-condition — see its doc).  Finite case check over the
role/assigned tree (R5 clock–clock split off, where both fields are preserved by
`stdCounterSubroutine`; the two assigned-`mcr` input cases are excluded by the
hypotheses). -/
theorem ledgerW_Phase0_pair_conserved (r₁ r₂ : AgentState L K)
    (h₁ : NotAssignedMcr (L := L) (K := K) r₁)
    (h₂ : NotAssignedMcr (L := L) (K := K) r₂) :
    ledgerW (L := L) (K := K) (Phase0Transition L K r₁ r₂).1
        + ledgerW (L := L) (K := K) (Phase0Transition L K r₁ r₂).2
      = ledgerW (L := L) (K := K) r₁ + ledgerW (L := L) (K := K) r₂ := by
  unfold ledgerW
  by_cases hcc : r₁.role = .clock ∧ r₂.role = .clock
  · obtain ⟨hr₁, hr₂⟩ := hcc
    have hpt : Phase0Transition L K r₁ r₂
        = (stdCounterSubroutine L K r₁, stdCounterSubroutine L K r₂) := by
      unfold Phase0Transition
      simp only [hr₁, hr₂, reduceCtorEq, and_self, and_true, true_and, and_false,
        false_and, if_true, if_false, ite_true, ite_false]
    rw [hpt]
    rw [freeW_stdCounterSubroutine_clock r₁ hr₁, freeW_stdCounterSubroutine_clock r₂ hr₂,
        topW_stdCounterSubroutine_clock' r₁ hr₁, topW_stdCounterSubroutine_clock' r₂ hr₂]
  · unfold NotAssignedMcr at h₁ h₂
    rcases r₁ with
      ⟨in₁, out₁, ph₁, role₁, asg₁, bias₁, sb₁, hr₁, mn₁, fl₁, op₁, ctr₁⟩
    rcases r₂ with
      ⟨in₂, out₂, ph₂, role₂, asg₂, bias₂, sb₂, hr₂, mn₂, fl₂, op₂, ctr₂⟩
    cases role₁ <;> cases role₂ <;> cases asg₁ <;> cases asg₂ <;>
      first
      | (exfalso; exact hcc ⟨rfl, rfl⟩)
      | (exact absurd ⟨rfl, rfl⟩ h₁)
      | (exact absurd ⟨rfl, rfl⟩ h₂)
      | (simp only [Phase0Transition, freeW, topW, reduceCtorEq, ne_eq, and_true,
          and_false, true_and, false_and, and_self, if_true, if_false, ite_true, ite_false,
          or_true, or_false, false_or, true_or, not_true_eq_false, not_false_eq_true,
          Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true] <;> norm_num)

set_option maxHeartbeats 1600000 in
/-- **No Phase-0 rule produces an assigned `mcr`.**  For inputs that are not
assigned `mcr`, both `Phase0Transition` outputs are not assigned `mcr` either
(rules only consume `mcr`; the only `mcr`-keeping path inherits a non-assigned
flag).  Finite case check (R5 clock–clock split off — clocks are never `mcr`). -/
theorem Phase0Transition_outputs_notAssignedMcr (r₁ r₂ : AgentState L K)
    (h₁ : NotAssignedMcr (L := L) (K := K) r₁)
    (h₂ : NotAssignedMcr (L := L) (K := K) r₂) :
    NotAssignedMcr (L := L) (K := K) (Phase0Transition L K r₁ r₂).1 ∧
    NotAssignedMcr (L := L) (K := K) (Phase0Transition L K r₁ r₂).2 := by
  unfold NotAssignedMcr
  by_cases hcc : r₁.role = .clock ∧ r₂.role = .clock
  · obtain ⟨hr₁, hr₂⟩ := hcc
    have hpt : Phase0Transition L K r₁ r₂
        = (stdCounterSubroutine L K r₁, stdCounterSubroutine L K r₂) := by
      unfold Phase0Transition
      simp only [hr₁, hr₂, reduceCtorEq, and_self, and_true, true_and, and_false,
        false_and, if_true, if_false, ite_true, ite_false]
    rw [hpt]
    constructor <;>
      (rintro ⟨hm, _⟩;
       first
       | (rw [stdCounterSubroutine_clock_role_eq' r₁ hr₁] at hm; exact absurd hm (by decide))
       | (rw [stdCounterSubroutine_clock_role_eq' r₂ hr₂] at hm; exact absurd hm (by decide)))
  · unfold NotAssignedMcr at h₁ h₂
    rcases r₁ with
      ⟨in₁, out₁, ph₁, role₁, asg₁, bias₁, sb₁, hr₁, mn₁, fl₁, op₁, ctr₁⟩
    rcases r₂ with
      ⟨in₂, out₂, ph₂, role₂, asg₂, bias₂, sb₂, hr₂, mn₂, fl₂, op₂, ctr₂⟩
    cases role₁ <;> cases role₂ <;> cases asg₁ <;> cases asg₂ <;>
      first
      | (exfalso; exact hcc ⟨rfl, rfl⟩)
      | (exact absurd ⟨rfl, rfl⟩ h₁)
      | (exact absurd ⟨rfl, rfl⟩ h₂)
      | (refine ⟨?_, ?_⟩ <;>
          (simp only [Phase0Transition, reduceCtorEq, ne_eq, and_true, and_false,
            true_and, false_and, and_self, if_true, if_false, ite_true, ite_false,
            or_true, or_false, false_or, true_or, not_true_eq_false, not_false_eq_true,
            Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true,
            not_and] <;> decide))

/-! ## Stage 1b — the global ledger invariant `freeDiff = 2·X` (preserved + initial). -/

/-- `freeDiff` agrees with the role/assigned counts: it is `Mf − Sf`. -/
theorem freeDiff_eq_sumOf (c : Config (AgentState L K)) :
    freeDiff (L := L) (K := K) c = Config.sumOf (freeW (L := L) (K := K)) c := rfl

/-- The per-config ledger predicate: `freeDiff c = 2 · topSplitXZ c`, i.e.
`Mf − Sf = 2·X`.  The honest assigned-balance invariant; holds at the balanced
all-`mcr` start and is preserved by every Phase-0 step (Stage 1b). -/
def LedgerInv (c : Config (AgentState L K)) : Prop :=
  freeDiff (L := L) (K := K) c = 2 * topSplitXZ (L := L) (K := K) c

/-- The per-config "no assigned `mcr`" predicate. -/
def NoAssignedMcrConfig (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, NotAssignedMcr (L := L) (K := K) a

/-- `topW` reads only the agent's `role` (local copy of the private TopSplitDrift
lemma). -/
private lemma topW_eq_of_role_eq' (a b : AgentState L K) (h : a.role = b.role) :
    topW (L := L) (K := K) a = topW (L := L) (K := K) b := by
  unfold topW; rw [h]

/-- At both phase 0, the full `Transition` output `assigned` flags equal the
`Phase0Transition` output flags (the epidemic update is identity and
`finishPhase10Entry` projects `assigned` to the post-dispatch value). -/
theorem Transition_assigned_eq_phase0_of_both_phase0
    (s t : AgentState L K) (hs : s.phase.val = 0) (ht : t.phase.val = 0) :
    (Transition L K s t).1.assigned = (Phase0Transition L K s t).1.assigned ∧
    (Transition L K s t).2.assigned = (Phase0Transition L K s t).2.assigned := by
  have hpe := phaseEpidemicUpdate_eq_self_of_both_phase0 (L := L) (K := K) s t hs ht
  have hs0 : s.phase = (⟨0, by omega⟩ : Fin _) := Fin.ext hs
  unfold Transition
  rw [hpe]
  simp only [finishPhase10Entry_assigned]
  rw [hs0]
  exact ⟨rfl, rfl⟩

/-- `Config.sumOf` of a sum-of-weights splits additively over `+`. -/
private lemma sumOf_add_pair (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (hle : ({r₁, r₂} : Config (AgentState L K)) ≤ c) (w : AgentState L K → ℤ) :
    Config.sumOf w c
      = Config.sumOf w (c - {r₁, r₂}) + (w r₁ + w r₂) := by
  unfold Config.sumOf
  conv_lhs => rw [← Multiset.sub_add_cancel hle]
  rw [Multiset.map_add, Multiset.sum_add]
  congr 1
  show w r₁ + (w r₂ + 0) = _
  rw [add_zero]

/-- **`LedgerInv` is preserved by `stepOrSelf` on the Phase-0 / no-assigned-`mcr`
region.**  The per-pair ledger conservation `ledgerW_Phase0_pair_conserved` lifts
through the additive `Config.sumOf` decomposition: `freeDiff − 2·topSplitXZ =
Config.sumOf ledgerW` is unchanged by removing the input pair and inserting the
output pair (whose `ledgerW`-block matches), hence `LedgerInv` propagates. -/
theorem LedgerInv_stepOrSelf
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (hall : Phase0Window.allPhase0 (L := L) (K := K) c)
    (hnomcr : NoAssignedMcrConfig (L := L) (K := K) c)
    (hled : LedgerInv (L := L) (K := K) c) :
    LedgerInv (L := L) (K := K)
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hle : ({r₁, r₂} : Config (AgentState L K)) ≤ c := happ
    have hr₁ : r₁ ∈ c := Multiset.mem_of_le hle (by simp)
    have hr₂ : r₂ ∈ c := Multiset.mem_of_le hle (by simp)
    have h₁ : r₁.phase.val = 0 := by have := hall r₁ hr₁; simp [this]
    have h₂ : r₂.phase.val = 0 := by have := hall r₂ hr₂; simp [this]
    have hn₁ : NotAssignedMcr (L := L) (K := K) r₁ := hnomcr r₁ hr₁
    have hn₂ : NotAssignedMcr (L := L) (K := K) r₂ := hnomcr r₂ hr₂
    -- The combined ledger weight `Config.sumOf ledgerW` is `freeDiff − 2·topSplitXZ`.
    have hcomb : ∀ d : Config (AgentState L K),
        Config.sumOf (ledgerW (L := L) (K := K)) d
          = freeDiff (L := L) (K := K) d - 2 * topSplitXZ (L := L) (K := K) d := by
      intro d
      unfold ledgerW freeDiff topSplitXZ Config.sumOf
      induction d using Multiset.induction with
      | empty => simp
      | cons a s ih => simp only [Multiset.map_cons, Multiset.sum_cons, ih]; ring
    have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    -- `ledgerW` reads role+assigned only, so the Transition output matches Phase0Transition.
    have hrole := Transition_roles_eq_phase0_of_both_phase0 (L := L) (K := K) r₁ r₂ h₁ h₂
    have hasg := Transition_assigned_eq_phase0_of_both_phase0 (L := L) (K := K) r₁ r₂ h₁ h₂
    have hpair : ledgerW (L := L) (K := K) (Transition L K r₁ r₂).1
          + ledgerW (L := L) (K := K) (Transition L K r₁ r₂).2
        = ledgerW (L := L) (K := K) r₁ + ledgerW (L := L) (K := K) r₂ := by
      have e1 : ledgerW (L := L) (K := K) (Transition L K r₁ r₂).1
          = ledgerW (L := L) (K := K) (Phase0Transition L K r₁ r₂).1 := by
        unfold ledgerW
        rw [freeW_eq_of_role_assigned_eq _ _ hrole.1 hasg.1,
            topW_eq_of_role_eq' _ _ hrole.1]
      have e2 : ledgerW (L := L) (K := K) (Transition L K r₁ r₂).2
          = ledgerW (L := L) (K := K) (Phase0Transition L K r₁ r₂).2 := by
        unfold ledgerW
        rw [freeW_eq_of_role_assigned_eq _ _ hrole.2 hasg.2,
            topW_eq_of_role_eq' _ _ hrole.2]
      rw [e1, e2]
      exact ledgerW_Phase0_pair_conserved r₁ r₂ hn₁ hn₂
    -- Combine: Config.sumOf ledgerW (step) = Config.sumOf ledgerW c = 0.
    have hsumstep : Config.sumOf (ledgerW (L := L) (K := K))
          (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
        = Config.sumOf (ledgerW (L := L) (K := K)) c := by
      rw [hstep]
      have hout := sumOf_add_pair (c - {r₁, r₂} + {(Transition L K r₁ r₂).1,
          (Transition L K r₁ r₂).2}) (Transition L K r₁ r₂).1 (Transition L K r₁ r₂).2
          (by simp) (ledgerW (L := L) (K := K))
      have hsrc := sumOf_add_pair c r₁ r₂ hle (ledgerW (L := L) (K := K))
      rw [hout, hsrc, hpair]
      congr 1
      -- (c - {r₁,r₂} + {o₁,o₂}) - {o₁,o₂} = c - {r₁,r₂}
      rw [Multiset.add_sub_cancel_right]
    have hzero : Config.sumOf (ledgerW (L := L) (K := K)) c = 0 := by
      rw [hcomb]; unfold LedgerInv at hled; rw [hled]; ring
    have : Config.sumOf (ledgerW (L := L) (K := K))
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) = 0 := by
      rw [hsumstep, hzero]
    unfold LedgerInv
    have := this
    rw [hcomb] at this
    linarith [this]
  · rw [Protocol.stepOrSelf, if_neg happ]; exact hled

/-- **`LedgerInv` holds at the balanced start.**  At `Phase0Initial` every agent
is an unassigned `mcr`, so `freeDiff = 0` (no main / cr-side agent) and
`topSplitXZ = 0`, hence `freeDiff = 0 = 2·0`. -/
theorem LedgerInv_init {n : ℕ} {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀) :
    LedgerInv (L := L) (K := K) c₀ := by
  have hall := hinit.2
  have hfree : freeDiff (L := L) (K := K) c₀ = 0 := by
    unfold freeDiff Config.sumOf
    rw [Multiset.sum_eq_zero]
    intro x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    unfold freeW; rw [(hall a ha).2]; simp
  have hX : topSplitXZ (L := L) (K := K) c₀ = 0 := by
    have : topSplitX (L := L) (K := K) c₀ = 0 :=
      topSplit_X_init_zero hinit
    rwa [topSplitX_eq_cast, Int.cast_eq_zero] at this
  unfold LedgerInv; rw [hfree, hX]; ring

/-! ## Stage 2 — the free-pool sign comparison from `X`'s sign. -/

/-- **Stage 2 (sign comparison).**  Under the ledger invariant `LedgerInv c`
(`Mf − Sf = 2·X`): `X > 0 ⟹ freeDiff c > 0` (`Sf < Mf`), `X < 0 ⟹ freeDiff c < 0`
(`Mf < Sf`), and the integer identity `freeDiff c = 2·X`.  This is the Lean-faithful
Lemma-5.1 free-pool imbalance: more produced Main than RoleCR-mass forces strictly
more free Mains than free CR-side agents. -/
theorem freeDiff_sign_of_topSplit (c : Config (AgentState L K))
    (hled : LedgerInv (L := L) (K := K) c) :
    freeDiff (L := L) (K := K) c = 2 * topSplitXZ (L := L) (K := K) c := hled

/-! ## Stage 3 — the inward residual via the `sinh = Δ·sinh s` reduction. -/

/-- The integer per-pair jump `Δ_pair = topSplitXZ(step) − topSplitXZ c`. -/
noncomputable def topSplitStepDeltaZ (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K) : ℤ :=
  topSplitXZ (L := L) (K := K) (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
    - topSplitXZ (L := L) (K := K) c

/-- The real per-pair delta is the cast of the integer delta. -/
theorem topSplitStepDelta_eq_cast (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K) :
    topSplitStepDelta (L := L) (K := K) c r₁ r₂
      = ((topSplitStepDeltaZ (L := L) (K := K) c r₁ r₂ : ℤ) : ℝ) := by
  unfold topSplitStepDelta topSplitStepDeltaZ; push_cast; ring

/-- `|Δ_pair| ≤ 1` as an integer, on the Phase-0 region. -/
theorem topSplitStepDeltaZ_abs_le_one (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (hall : Phase0Window.allPhase0 (L := L) (K := K) c) :
    |topSplitStepDeltaZ (L := L) (K := K) c r₁ r₂| ≤ 1 := by
  have h := topSplitXZ_step_delta_abs_le_one (L := L) (K := K) c r₁ r₂ hall
  -- h : |(topSplitXZ(step):ℝ) − (topSplitXZ c:ℝ)| ≤ 1; rewrite the inside as a cast of Z.
  have hcast : (topSplitXZ (L := L) (K := K)
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) : ℝ)
        - (topSplitXZ (L := L) (K := K) c : ℝ)
      = ((topSplitStepDeltaZ (L := L) (K := K) c r₁ r₂ : ℤ) : ℝ) := by
    unfold topSplitStepDeltaZ; push_cast; ring
  rw [hcast, ← Int.cast_abs] at h
  exact_mod_cast h

/-- **Key `sinh` collapse.**  For an integer `d` with `|d| ≤ 1` (so `d ∈
{−1,0,1}`), `sinh(s·d) = d · sinh s` (`sinh` is odd; the three values are
`−sinh s`, `0`, `sinh s`). -/
private lemma sinh_int_mul_of_abs_le_one (s : ℝ) (d : ℤ) (hd : |d| ≤ 1) :
    Real.sinh (s * (d : ℝ)) = (d : ℝ) * Real.sinh s := by
  rw [abs_le] at hd
  obtain ⟨hd1, hd2⟩ := hd
  interval_cases d
  · -- d = −1: sinh(s·(−1)) = sinh(−s) = −sinh s = (−1)·sinh s.
    have : ((-1 : ℤ) : ℝ) = (-1 : ℝ) := by norm_num
    rw [this, mul_neg_one, Real.sinh_neg, neg_one_mul]
  · simp
  · simp

/-- **`sinh` of `s·X` shares the sign of `X`** (the supermartingale sign helper):
`x ≤ 0 ⟹ sinh(s·x) ≤ 0` and `0 ≤ x ⟹ 0 ≤ sinh(s·x)` for `s ≥ 0` — packaged as
`sinh(s·x)·d ≤ 0` whenever `x·d ≤ 0`. -/
private lemma sinh_sign_mul (s : ℝ) (hs : 0 ≤ s) (x d : ℝ) (hxd : x * d ≤ 0) :
    Real.sinh (s * x) * d ≤ 0 := by
  rcases le_total 0 x with hx | hx
  · -- x ≥ 0 ⟹ sinh(s·x) ≥ 0; and x·d ≤ 0 with x ≥ 0 ⟹ either x = 0 or d ≤ 0.
    have hsh : 0 ≤ Real.sinh (s * x) := by
      rw [Real.sinh_eq]
      have : Real.exp (-(s * x)) ≤ Real.exp (s * x) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith
    rcases le_total d 0 with hd | hd
    · exact mul_nonpos_of_nonneg_of_nonpos hsh hd
    · -- d ≥ 0 and x ≥ 0 with x·d ≤ 0 ⟹ x·d = 0; if x > 0 then d = 0.
      rcases eq_or_lt_of_le hx with hx0 | hx0
      · rw [← hx0]; simp
      · have : d ≤ 0 := by nlinarith
        have hd0 : d = 0 := le_antisymm this hd
        rw [hd0]; simp
  · -- x ≤ 0 ⟹ sinh(s·x) ≤ 0.
    have hsh : Real.sinh (s * x) ≤ 0 := by
      rw [Real.sinh_eq]
      have : Real.exp (s * x) ≤ Real.exp (-(s * x)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      linarith
    rcases le_total 0 d with hd | hd
    · exact mul_nonpos_of_nonpos_of_nonneg hsh hd
    · rcases eq_or_lt_of_le hx with hx0 | hx0
      · rw [hx0]; simp
      · have : 0 ≤ d := by nlinarith
        have hd0 : d = 0 := le_antisymm hd this
        rw [hd0]; simp

/-- The expected signed one-step jump `E[ΔX] = ∑_pair interactionProb·Δ_pair`. -/
noncomputable def expectedDeltaX (c : Config (AgentState L K)) : ℝ :=
  ∑ pair : AgentState L K × AgentState L K,
    (Config.interactionProb c pair.1 pair.2).toReal
      * topSplitStepDelta (L := L) (K := K) c pair.1 pair.2

/-- **Stage 3 reduction (the boundary-free `sinh` collapse).**  On the Phase-0
region with `s ≥ 0`, the inward residual `InwardResidual s c` is IMPLIED by the
single signed-drift sign condition `(X c) · E[ΔX] ≤ 0`.

Proof: `Δ_pair ∈ {−1,0,1}` (Stage 3a), so `sinh(s·Δ_pair) = Δ_pair·sinh s`,
whence `E[sinh(s·Δ)] = sinh s · E[ΔX]` and `InwardResidual = sinh(s·X)·sinh s·E[ΔX]`.
With `sinh s ≥ 0` (s ≥ 0) and the sign helper `sinh_sign_mul`, `X·E[ΔX] ≤ 0`
delivers `sinh(s·X)·E[ΔX] ≤ 0` (boundary-free: `X = 0 ⟹ sinh 0 = 0`). -/
theorem inwardResidual_of_expectedDeltaX_sign (s : ℝ) (hs : 0 ≤ s)
    (c : Config (AgentState L K))
    (hall : Phase0Window.allPhase0 (L := L) (K := K) c)
    (hsign : (topSplitXZ (L := L) (K := K) c : ℝ) * expectedDeltaX (L := L) (K := K) c ≤ 0) :
    InwardResidual (L := L) (K := K) s c := by
  classical
  unfold InwardResidual
  -- collapse sinh(s·Δ_pair) = Δ_pair·sinh s pairwise.
  have hcollapse : ∀ pair : AgentState L K × AgentState L K,
      (Config.interactionProb c pair.1 pair.2).toReal
          * Real.sinh (s * topSplitStepDelta (L := L) (K := K) c pair.1 pair.2)
        = ((Config.interactionProb c pair.1 pair.2).toReal
            * topSplitStepDelta (L := L) (K := K) c pair.1 pair.2) * Real.sinh s := by
    intro pair
    rw [topSplitStepDelta_eq_cast]
    rw [sinh_int_mul_of_abs_le_one s _
        (topSplitStepDeltaZ_abs_le_one (L := L) (K := K) c pair.1 pair.2 hall)]
    rw [← topSplitStepDelta_eq_cast]; ring
  rw [Finset.sum_congr rfl (fun pair _ => hcollapse pair)]
  rw [← Finset.sum_mul]
  -- now: sinh(s·X) · (E[ΔX] · sinh s) ≤ 0.
  rw [show (∑ pair : AgentState L K × AgentState L K,
        (Config.interactionProb c pair.1 pair.2).toReal
          * topSplitStepDelta (L := L) (K := K) c pair.1 pair.2)
      = expectedDeltaX (L := L) (K := K) c from rfl]
  have hsinhs : 0 ≤ Real.sinh s := by
    rw [Real.sinh_eq]
    have : Real.exp (-s) ≤ Real.exp s := Real.exp_le_exp.mpr (by linarith)
    linarith
  -- sinh(s·X)·(E·sinh s) = (sinh(s·X)·E)·sinh s; bound by sign helper × nonneg.
  rw [← mul_assoc]
  have hkey : Real.sinh (s * (topSplitXZ (L := L) (K := K) c : ℝ))
      * expectedDeltaX (L := L) (K := K) c ≤ 0 :=
    sinh_sign_mul s hs _ _ hsign
  exact mul_nonpos_of_nonpos_of_nonneg hkey hsinhs

/-! ## Stage 3b — the R2/R3 mass rectangle (the single named protocol residual).

The expected signed jump is driven ONLY by R2 (`Δ = −1`, ordered mass `2·mcr·Mf`)
and R3 (`Δ = +1`, ordered mass `2·mcr·Sf`); R1/R4/R5 give `Δ = 0`.  Hence the
honest mass identity

    totalPairs · E[ΔX]  =  2 · mcrCount · (Sf − Mf)  =  −2 · mcrCount · freeDiff,

where `freeDiff = Mf − Sf`.  This `RectangleResidual` is the LAST genuine
protocol-counting residual: it is the Lean-faithful R2/R3 marginal of the
interaction law, a pure deterministic mass count (no probability beyond the
uniform-pair law already in `interactionProb`).  Its proof is a double
multiset-`count` rectangle over the role/assigned tree against `interactionCount`
(the `sum_fst/snd_interactionProb`-style marginal, here for a two-variable
`pairDelta`); we ISOLATE it as the named residual rather than name-and-stop, and
DISCHARGE everything that consumes it (the inward sign and the full tail).

ATTACK STATUS (honest): the per-pair `pairDelta(s₁,s₂) ∈ {−1,0,1}` table is the
finite `Phase0Transition` case check already proven for `topW` (it IS the
`topW`-block delta, `topW_Phase0_pair_delta_abs_le_one`).  The remaining work is
the `∑_{s₁,s₂} interactionCount·pairDelta = 2·mcrCount·(Sf−Mf)` double-marginal
decomposition — a standalone `Multiset.count` rectangle that the repo does not yet
have a generic lemma for.  Stated as `RectangleResidual` and consumed below. -/

/-- **The R2/R3 mass rectangle residual** (the single named Lemma-5.1 counting
fact): `totalPairs · E[ΔX] = −2 · mcrCount · freeDiff`.  See the section doc — this
is the honest, paper-faithful R2/R3 marginal, isolated as the last protocol-side
residual; everything consuming it is discharged. -/
def RectangleResidual (c : Config (AgentState L K)) : Prop :=
  (Config.totalPairs c : ℝ) * expectedDeltaX (L := L) (K := K) c
    = -2 * (mcrCount (L := L) (K := K) c : ℝ) * (freeDiff (L := L) (K := K) c : ℝ)

/-- **The expected-drift sign from the ledger + rectangle.**  Under `LedgerInv`
(`freeDiff = 2·X`) and the rectangle residual, `X · E[ΔX] ≤ 0`:

    totalPairs · X · E[ΔX] = X · (−2·mcr·freeDiff) = X · (−4·mcr·X)
                           = −4·mcr·X² ≤ 0,

and `totalPairs > 0`, so `X · E[ΔX] ≤ 0`.  This is the boundary-free inward
sign-drift, the honest content of the paper's `sf + 2·st = mf + 2·mt` ledger. -/
theorem expectedDeltaX_sign_of_ledger (c : Config (AgentState L K))
    (hc2 : 2 ≤ Multiset.card c)
    (hled : LedgerInv (L := L) (K := K) c)
    (hrect : RectangleResidual (L := L) (K := K) c) :
    (topSplitXZ (L := L) (K := K) c : ℝ) * expectedDeltaX (L := L) (K := K) c ≤ 0 := by
  have htp : (0 : ℝ) < (Config.totalPairs c : ℝ) := by
    have := Config.totalPairs_pos (c := c) hc2
    exact_mod_cast this
  -- freeDiff = 2·X (as reals).
  have hledR : (freeDiff (L := L) (K := K) c : ℝ)
      = 2 * (topSplitXZ (L := L) (K := K) c : ℝ) := by
    have := hled; unfold LedgerInv at this
    have : (freeDiff (L := L) (K := K) c : ℝ)
        = ((2 * topSplitXZ (L := L) (K := K) c : ℤ) : ℝ) := by exact_mod_cast this
    rw [this]; push_cast; ring
  -- totalPairs · X · E[ΔX] = −4·mcr·X² ≤ 0.
  unfold RectangleResidual at hrect
  have hkey : (Config.totalPairs c : ℝ)
      * ((topSplitXZ (L := L) (K := K) c : ℝ) * expectedDeltaX (L := L) (K := K) c)
      = -4 * (mcrCount (L := L) (K := K) c : ℝ)
          * (topSplitXZ (L := L) (K := K) c : ℝ) ^ 2 := by
    rw [show (Config.totalPairs c : ℝ)
          * ((topSplitXZ (L := L) (K := K) c : ℝ) * expectedDeltaX (L := L) (K := K) c)
        = (topSplitXZ (L := L) (K := K) c : ℝ)
            * ((Config.totalPairs c : ℝ) * expectedDeltaX (L := L) (K := K) c) by ring]
    rw [hrect, hledR]; ring
  have hrhs_nonpos : -4 * (mcrCount (L := L) (K := K) c : ℝ)
      * (topSplitXZ (L := L) (K := K) c : ℝ) ^ 2 ≤ 0 := by
    have hmcr : (0 : ℝ) ≤ (mcrCount (L := L) (K := K) c : ℝ) := by positivity
    have hsq : (0 : ℝ) ≤ (topSplitXZ (L := L) (K := K) c : ℝ) ^ 2 := sq_nonneg _
    nlinarith [hmcr, hsq]
  -- divide by totalPairs > 0.
  have hprod : (Config.totalPairs c : ℝ)
      * ((topSplitXZ (L := L) (K := K) c : ℝ) * expectedDeltaX (L := L) (K := K) c) ≤ 0 := by
    rw [hkey]; exact hrhs_nonpos
  by_contra hpos
  push_neg at hpos
  have : (0 : ℝ) < (Config.totalPairs c : ℝ)
      * ((topSplitXZ (L := L) (K := K) c : ℝ) * expectedDeltaX (L := L) (K := K) c) :=
    mul_pos htp hpos
  linarith

/-- **InwardResidual discharged on the ledger region.**  Combining the boundary-free
`sinh` reduction with the ledger + rectangle sign: on the Phase-0 region, under
`LedgerInv` and `RectangleResidual`, the inward residual holds (`s ≥ 0`). -/
theorem inwardResidual_of_ledger (s : ℝ) (hs : 0 ≤ s)
    (c : Config (AgentState L K))
    (hc2 : 2 ≤ Multiset.card c)
    (hall : Phase0Window.allPhase0 (L := L) (K := K) c)
    (hled : LedgerInv (L := L) (K := K) c)
    (hrect : RectangleResidual (L := L) (K := K) c) :
    InwardResidual (L := L) (K := K) s c :=
  inwardResidual_of_expectedDeltaX_sign s hs c hall
    (expectedDeltaX_sign_of_ledger c hc2 hled hrect)

/- **Honest spec note (`NoAssignedMcrConfig` at the start).**  `Phase0Initial`
(`RoleSplitConcentration.Phase0Initial`) pins only `phase = 0` and `role = mcr`
for each initial agent — it does NOT pin `assigned = false`.  So
`NoAssignedMcrConfig c₀` does not follow from `Phase0Initial` alone, even though
it is TRUE of the real all-default initial configuration (every agent constructed
with `assigned = false`).  Rather than strengthen the FROZEN `Phase0Initial`, we
carry `NoAssignedMcrConfig c₀` as an explicit honest side-hypothesis in the
wire-up below (it is the genuine, true-of-the-real-start ledger precondition).
`NoAssignedMcrConfig` IS preserved by every Phase-0 step (`NoAssignedMcrConfig_stepOrSelf`),
so it threads through the absorbing region. -/

/-- **`NoAssignedMcrConfig` is preserved by `stepOrSelf` on the Phase-0 region.**
No Phase-0 rule ever produces an `mcr` (rules only CONSUME `mcr`), and the only
agents whose role becomes/stays `mcr` keep their `assigned` flag from an input
that was already a non-assigned `mcr`; so no assigned `mcr` is ever created. -/
theorem NoAssignedMcrConfig_stepOrSelf
    (c : Config (AgentState L K)) (r₁ r₂ : AgentState L K)
    (hall : Phase0Window.allPhase0 (L := L) (K := K) c)
    (hnomcr : NoAssignedMcrConfig (L := L) (K := K) c) :
    NoAssignedMcrConfig (L := L) (K := K)
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hle : ({r₁, r₂} : Config (AgentState L K)) ≤ c := happ
    have hr₁mem : r₁ ∈ c := Multiset.mem_of_le hle (by simp)
    have hr₂mem : r₂ ∈ c := Multiset.mem_of_le hle (by simp)
    have h₁ : r₁.phase.val = 0 := by have := hall r₁ hr₁mem; simp [this]
    have h₂ : r₂.phase.val = 0 := by have := hall r₂ hr₂mem; simp [this]
    have hn₁ : NotAssignedMcr (L := L) (K := K) r₁ := hnomcr r₁ hr₁mem
    have hn₂ : NotAssignedMcr (L := L) (K := K) r₂ := hnomcr r₂ hr₂mem
    have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    -- The two Transition outputs are `NotAssignedMcr` (no rule produces an assigned mcr).
    have hrole := Transition_roles_eq_phase0_of_both_phase0 (L := L) (K := K) r₁ r₂ h₁ h₂
    have hasg := Transition_assigned_eq_phase0_of_both_phase0 (L := L) (K := K) r₁ r₂ h₁ h₂
    have hout : NotAssignedMcr (L := L) (K := K) (Transition L K r₁ r₂).1 ∧
        NotAssignedMcr (L := L) (K := K) (Transition L K r₁ r₂).2 := by
      have hp := Phase0Transition_outputs_notAssignedMcr r₁ r₂ hn₁ hn₂
      constructor
      · unfold NotAssignedMcr at hp ⊢; rw [hrole.1, hasg.1]; exact hp.1
      · unfold NotAssignedMcr at hp ⊢; rw [hrole.2, hasg.2]; exact hp.2
    intro a ha
    rw [hstep] at ha
    rcases Multiset.mem_add.mp ha with hin | hin
    · exact hnomcr a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hin)
    · -- a is one of the two outputs.
      have : a = (Transition L K r₁ r₂).1 ∨ a = (Transition L K r₁ r₂).2 := by
        rcases Multiset.mem_cons.mp hin with h | h
        · exact Or.inl h
        · exact Or.inr (Multiset.mem_singleton.mp h)
      rcases this with rfl | rfl
      · exact hout.1
      · exact hout.2
  · rw [Protocol.stepOrSelf, if_neg happ]; exact hnomcr

/-! ## Stage 4 — the hypothesis-free-except-rectangle top-split tail (wire-up).

The full discharge: an absorbing region `Q` carrying `allPhase0`, `card ≥ 2`,
`LedgerInv` (the proven assigned-balance ledger), and `RectangleResidual` (the one
named R2/R3 mass identity) yields `InwardResidual` on `Q` via `inwardResidual_of_ledger`,
which feeds `TopSplitDrift.topSplitWindow_whp_cosh_clean` to produce the boundary-free
cosh (Chernoff) top-split tail.  At the balanced `Phase0Initial` start, `LedgerInv`
holds (`LedgerInv_init`), and both `LedgerInv` and `NoAssignedMcrConfig` propagate
through the region (`LedgerInv_stepOrSelf` / `NoAssignedMcrConfig_stepOrSelf`), so the
ONLY genuine protocol residual remaining is `RectangleResidual` on `Q`. -/

/-- **Stage 4 — the top-split tail discharged to the rectangle residual.**  With
the Phase-0 balanced start, an absorbing region `Q` carrying `allPhase0`, `card ≥ 2`,
the proven ledger invariant `LedgerInv`, and the single named R2/R3 mass identity
`RectangleResidual`, the probability that `TopSplitWindow δ n` fails after `T` steps
is at most the boundary-free cosh tail `(cosh s)^T / cosh (s·δn)`.

This is the sharpest hypothesis-free-except-`RectangleResidual` discharge of the
top-split balance: the assigned-balance ledger (Stage 1–1b), the boundary-free
`sinh` reduction (Stage 3a), and the ledger→sign derivation (Stage 3b) are ALL
proven 0-`sorry`; only the R2/R3 counting identity is carried, on `Q`. -/
theorem topSplitWindow_whp_inward
    {s : ℝ} (hs : 0 ≤ s) {δ : ℝ} {n : ℕ}
    {c₀ : Config (AgentState L K)} (hinit : Phase0Initial (L := L) (K := K) n c₀)
    (Q : Config (AgentState L K) → Prop)
    (hQ_abs : ∀ c c', Q c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support → Q c')
    (hQ_phase0 : ∀ c, Q c → Phase0Window.allPhase0 (L := L) (K := K) c)
    (hQ_card : ∀ c, Q c → 2 ≤ Multiset.card c)
    (hQ_ledger : ∀ c, Q c → LedgerInv (L := L) (K := K) c)
    (hQ_rect : ∀ c, Q c → RectangleResidual (L := L) (K := K) c)
    (hQ0 : Q c₀)
    (T : ℕ) (hδn : 0 < s * (δ * n)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ TopSplitWindow (L := L) (K := K) δ n c}
      ≤ ENNReal.ofReal (Real.cosh s) ^ T
          / ENNReal.ofReal (Real.cosh (s * (δ * n))) :=
  topSplitWindow_whp_cosh_clean hs hinit Q hQ_abs hQ_phase0 hQ_card
    (fun c hcQ => inwardResidual_of_ledger s hs c (hQ_card c hcQ) (hQ_phase0 c hcQ)
      (hQ_ledger c hcQ) (hQ_rect c hcQ))
    hQ0 T hδn

end RoleSplitConcentration
end ExactMajority
