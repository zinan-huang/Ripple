/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `RectangleResidualProof` — discharging the last R2/R3 mass rectangle.

`Probability/TopSplitInward.lean` reduced the boundary-free top-split inward
drift to a single named counting identity, `RectangleResidual c`:

    totalPairs · E[ΔX]  =  −2 · mcrCount · freeDiff,

equivalently the joint double-marginal

    ∑_{s₁,s₂} interactionCount(s₁,s₂) · pairDelta(s₁,s₂)  =  2 · mcrCount · (Sf − Mf),

where `pairDelta(s₁,s₂) ∈ {−1,0,1}` is the role-determined per-pair `topW`-block
delta (the integer `X`-jump of the `Phase0Transition` output two-agent block),
`Mf = #unassigned-Main`, `Sf = #unassigned-(cr/clock/reserve)`, and
`freeDiff = Mf − Sf`.

## The orientation / diagonal accounting (verified against FROZEN `Transition`).

`Phase0Transition` (Protocol/Transition.lean) dispatches the one-sided MCR
conversions with an EXPLICIT two-branch table — a `(s = mcr, t = target)` branch
and the mirror `(t = mcr, s = target)` branch.  Both branches produce the SAME
per-block `topW`-delta, so `pairDelta` is SYMMETRIC: `pairDelta s t = pairDelta t s`.
Concretely, on the role/assigned tree:

  * **R2** (mcr ↔ unassigned-Main): the `mcr` becomes `cr` (`topW: 0 → −1`), the
    Main stays Main (`topW` unchanged), block delta `−1`.  Fires on the ordered
    pair `(mcr, uMain)` AND its mirror `(uMain, mcr)`.
  * **R3** (mcr ↔ unassigned-CR-side): the `mcr` becomes `main` (`topW: 0 → +1`),
    the partner stays CR-side (`topW` unchanged), block delta `+1`.  Both
    orientations.
  * **R1/R4/R5** and every other block: delta `0`.

Because R2/R3 pairs are `mcr × non-mcr` (DIFFERENT roles), `interactionCount`
never hits its self-pair diagonal correction there: `s₁ ≠ s₂` forces
`interactionCount s₁ s₂ = count s₁ · count s₂` with no `−1`.  We prove this
disjointness explicitly (`mcr ∉ uMain-class`, `mcr ∉ uCR-class`).  Summing the
`(mcr, uMain)` orientation gives `mcrCount · Mf`, the mirror gives `Mf · mcrCount`;
so R2 contributes `−2·mcrCount·Mf` and R3 contributes `+2·mcrCount·Sf` — the
**factor 2 is exactly the two orientations**.  Total:

    −2·mcrCount·Mf + 2·mcrCount·Sf = 2·mcrCount·(Sf − Mf) = −2·mcrCount·freeDiff.

## What this discharges.

Once `RectangleResidual` is proven hypothesis-free, `inwardResidual_of_ledger`
and `topSplitWindow_whp_inward` (TopSplitInward.lean) shed their `hQ_rect`
hypothesis: the strongest hypothesis-free top-split tail
`topSplitWindow_whp_rectFree` below carries only `Phase0Initial`,
`NoAssignedMcrConfig` (the honest true-of-the-real-start side condition), and the
absorbing/ledger structure of the region `Q` — all provable from the protocol.

Everything here is 0-`sorry` / 0-`axiom` / no `native_decide`.

Reference: Doty et al. §5.1; `Probability/TopSplitInward.lean`
(`RectangleResidual`, `expectedDeltaX`); `Probability/Phase0Window.lean`
(`sum_fst_interactionProb` marginal collapse); `Probability/Scheduler.lean`
(`interactionCount`, `totalPairs`); FROZEN `Protocol/Transition.lean`.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.TopSplitInward

namespace ExactMajority
namespace RoleSplitConcentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

variable {L K : ℕ}

/-- The Standard Counter Subroutine keeps a `Clock` agent a `Clock` (local copy
of the private TopSplit lemma, via the public `advancePhaseWithInit` fact). -/
private lemma stdCounterSubroutine_clock_role_eq'' (a : AgentState L K)
    (ha : a.role = .clock) :
    (stdCounterSubroutine L K a).role = .clock := by
  unfold stdCounterSubroutine
  split
  · exact advancePhaseWithInit_clock_role_eq L K a ha
  · exact ha

/-! ## The role-determined per-pair `X`-jump (`pairDeltaZ`). -/

/-- The role-determined integer per-pair `X`-jump: the `topW`-block delta of the
`Phase0Transition` output.  On an APPLICABLE phase-0 pair this equals the actual
config step delta `topSplitStepDeltaZ` (the `topSplitXZ` jump localizes to the two
interacting agents). -/
def pairDeltaZ (s₁ s₂ : AgentState L K) : ℤ :=
  (topW (L := L) (K := K) (Phase0Transition L K s₁ s₂).1
      + topW (L := L) (K := K) (Phase0Transition L K s₁ s₂).2)
    - (topW (L := L) (K := K) s₁ + topW (L := L) (K := K) s₂)

/-! ## The three interaction classes (mcr / unassigned-Main / unassigned-CR-side). -/

/-- The `mcr` initiator/responder class. -/
def isMcrB (a : AgentState L K) : Bool := decide (a.role = .mcr)

/-- The R2 target class: unassigned `Main` (`Mf`). -/
def isUMainB (a : AgentState L K) : Bool := decide (a.role = .main) && (!a.assigned)

/-- The R3 target class: unassigned CR-side (`cr`/`clock`/`reserve`) — `Sf`. -/
def isUCRB (a : AgentState L K) : Bool :=
  (decide (a.role = .cr) || decide (a.role = .clock) || decide (a.role = .reserve))
    && (!a.assigned)

/-- `Mf c = #unassigned-Main`, as a `countP`. -/
def MfCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => isUMainB (L := L) (K := K) a) c

/-- `Sf c = #unassigned-CR-side`, as a `countP`. -/
def SfCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => isUCRB (L := L) (K := K) a) c

/-! ## The `pairDelta` table — the finite role/assigned case check.

`pairDeltaZ` is fully role/assigned-determined and equals, on every pair, the
signed indicator `[R3 pair] − [R2 pair]`, where an R2 pair is an ordered
`mcr ↔ uMain` pair (either orientation) and an R3 pair an ordered `mcr ↔ uCR`
pair.  This is the same 5×5×2×2 finite check that bounds `|pairDelta| ≤ 1` in
`topW_Phase0_pair_delta_abs_le_one`, refined to the exact value. -/

/-- The signed R2 indicator: `1` on `mcr ↔ uMain` ordered pairs (either
orientation), else `0`. -/
def indR2 (s₁ s₂ : AgentState L K) : ℤ :=
  if (isMcrB (L := L) (K := K) s₁ ∧ isUMainB (L := L) (K := K) s₂)
      ∨ (isUMainB (L := L) (K := K) s₁ ∧ isMcrB (L := L) (K := K) s₂) then 1 else 0

/-- The signed R3 indicator: `1` on `mcr ↔ uCR` ordered pairs (either
orientation), else `0`. -/
def indR3 (s₁ s₂ : AgentState L K) : ℤ :=
  if (isMcrB (L := L) (K := K) s₁ ∧ isUCRB (L := L) (K := K) s₂)
      ∨ (isUCRB (L := L) (K := K) s₁ ∧ isMcrB (L := L) (K := K) s₂) then 1 else 0

set_option maxHeartbeats 2000000 in
/-- **The per-pair `pairDelta` table.**  `pairDeltaZ s₁ s₂ = indR3 s₁ s₂ −
indR2 s₁ s₂`: the role-determined block delta is `−1` exactly on R2 pairs
(mcr ↔ unassigned-Main, either orientation), `+1` exactly on R3 pairs
(mcr ↔ unassigned-CR-side), `0` everywhere else.  Finite case check over the
5×5×2×2 role/assigned tree (the opaque counter/bias machinery never touches the
`role`, the only field `topW` inspects). -/
theorem pairDeltaZ_eq_table (s₁ s₂ : AgentState L K) :
    pairDeltaZ (L := L) (K := K) s₁ s₂
      = indR3 (L := L) (K := K) s₁ s₂ - indR2 (L := L) (K := K) s₁ s₂ := by
  -- R5 (clock–clock) split off: both outputs stay clocks, delta 0, and it is
  -- neither R2 nor R3 (clock ∉ mcr/uMain/uCR-as-initiator since uCR needs the
  -- other to be mcr).  Handle via the same `stdCounterSubroutine` role-preservation.
  unfold pairDeltaZ indR2 indR3 isMcrB isUMainB isUCRB
  by_cases hcc : s₁.role = .clock ∧ s₂.role = .clock
  · obtain ⟨hr₁, hr₂⟩ := hcc
    have hpt : Phase0Transition L K s₁ s₂
        = (stdCounterSubroutine L K s₁, stdCounterSubroutine L K s₂) := by
      unfold Phase0Transition
      simp only [hr₁, hr₂, reduceCtorEq, and_self, and_true, true_and, and_false,
        false_and, if_true, if_false, ite_true, ite_false]
    rw [hpt]
    have e1 : (stdCounterSubroutine L K s₁).role = .clock :=
      stdCounterSubroutine_clock_role_eq'' s₁ hr₁
    have e2 : (stdCounterSubroutine L K s₂).role = .clock :=
      stdCounterSubroutine_clock_role_eq'' s₂ hr₂
    simp only [topW, e1, e2, hr₁, hr₂, reduceCtorEq, or_true, or_false, false_or,
      true_or, if_true, if_false, ite_true, ite_false, decide_true, decide_false,
      Bool.false_eq_true, Bool.true_and, Bool.and_false, Bool.and_true,
      false_and, and_false, or_self]
    norm_num
  · rcases s₁ with
      ⟨in₁, out₁, ph₁, role₁, asg₁, bias₁, sb₁, hr₁, mn₁, fl₁, op₁, ctr₁⟩
    rcases s₂ with
      ⟨in₂, out₂, ph₂, role₂, asg₂, bias₂, sb₂, hr₂, mn₂, fl₂, op₂, ctr₂⟩
    cases role₁ <;> cases role₂ <;> cases asg₁ <;> cases asg₂ <;>
      first
      | (exfalso; exact hcc ⟨rfl, rfl⟩)
      | (simp only [Phase0Transition, topW, stdCounterSubroutine, reduceCtorEq, ne_eq,
          and_true, and_false, true_and, false_and, and_self, if_true, if_false,
          ite_true, ite_false, or_true, or_false, false_or, true_or,
          not_true_eq_false, not_false_eq_true, Bool.not_true, Bool.not_false,
          Bool.true_eq_false, Bool.false_eq_true, decide_true, decide_false,
          Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
          Bool.or_true, Bool.or_false, Bool.true_or, Bool.false_or] <;> decide)

/-! ## Localization: the config step delta equals `pairDeltaZ` on positive-count pairs. -/

/-- `topW` reads only the agent's `role` (local copy of the private TopSplit
lemma). -/
private lemma topW_eq_of_role_eq''' (a b : AgentState L K) (h : a.role = b.role) :
    topW (L := L) (K := K) a = topW (L := L) (K := K) b := by
  unfold topW; rw [h]

/-- Positive `interactionCount` implies `Applicable` (local copy; the upstream is
`private`). -/
private lemma applicable_of_pos_iCount'' (c : Config (AgentState L K))
    (s₁ s₂ : AgentState L K) (h : 0 < c.interactionCount s₁ s₂) :
    Protocol.Applicable c s₁ s₂ := by
  show {s₁, s₂} ≤ c; rw [Multiset.le_iff_count]; intro a
  simp only [Config.interactionCount, Config.count] at h
  simp only [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  by_cases heq : s₁ = s₂
  · subst heq; simp only [ite_true] at h
    have : 2 ≤ Multiset.count s₁ c := by
      by_contra h_lt
      have hle : Multiset.count s₁ c ≤ 1 := by omega
      have : Multiset.count s₁ c * (Multiset.count s₁ c - 1) = 0 := by
        rcases Nat.eq_zero_or_pos (Multiset.count s₁ c) with h0 | h0
        · simp [h0]
        · have : Multiset.count s₁ c = 1 := by omega
          simp [this]
      omega
    by_cases ha : a = s₁ <;> simp_all
  · simp only [heq, ite_false] at h
    have hc1 : 0 < Multiset.count s₁ c := pos_of_mul_pos_left h (Nat.zero_le _)
    have hc2 : 0 < Multiset.count s₂ c := pos_of_mul_pos_right h (Nat.zero_le _)
    by_cases ha1 : a = s₁ <;> by_cases ha2 : a = s₂ <;> simp_all <;> omega

/-- **Localization of the config step delta.**  On an applicable phase-0 pair, the
integer process delta `topSplitStepDeltaZ c s₁ s₂` equals the role-determined
block delta `pairDeltaZ s₁ s₂` (the `topSplitXZ` jump is the additive `Config.sumOf
topW` change, localized to the two interacting agents, and `topW` reads only the
`role`, which the full `Transition` matches `Phase0Transition` on at phase 0). -/
theorem topSplitStepDeltaZ_eq_pairDeltaZ_of_applicable
    (c : Config (AgentState L K)) (s₁ s₂ : AgentState L K)
    (happ : Protocol.Applicable c s₁ s₂)
    (h₁ : s₁.phase.val = 0) (h₂ : s₂.phase.val = 0) :
    topSplitStepDeltaZ (L := L) (K := K) c s₁ s₂ = pairDeltaZ (L := L) (K := K) s₁ s₂ := by
  have hle : ({s₁, s₂} : Config (AgentState L K)) ≤ c := happ
  have hstep : Protocol.stepOrSelf (NonuniformMajority L K) c s₁ s₂
      = c - {s₁, s₂} + {(Transition L K s₁ s₂).1, (Transition L K s₁ s₂).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  have hbase_src : topSplitXZ (L := L) (K := K) c
      = Config.sumOf (topW (L := L) (K := K)) (c - {s₁, s₂})
        + (topW (L := L) (K := K) s₁ + topW (L := L) (K := K) s₂) := by
    unfold topSplitXZ Config.sumOf
    conv_lhs => rw [← Multiset.sub_add_cancel hle]
    rw [Multiset.map_add, Multiset.sum_add]
    congr 1
    show topW (L := L) (K := K) s₁ + (topW (L := L) (K := K) s₂ + 0) = _
    rw [add_zero]
  have hbase_out : topSplitXZ (L := L) (K := K)
        (Protocol.stepOrSelf (NonuniformMajority L K) c s₁ s₂)
      = Config.sumOf (topW (L := L) (K := K)) (c - {s₁, s₂})
        + (topW (L := L) (K := K) (Transition L K s₁ s₂).1
           + topW (L := L) (K := K) (Transition L K s₁ s₂).2) := by
    rw [hstep]
    unfold topSplitXZ Config.sumOf
    rw [Multiset.map_add, Multiset.sum_add]
    congr 1
    show topW (L := L) (K := K) (Transition L K s₁ s₂).1
          + (topW (L := L) (K := K) (Transition L K s₁ s₂).2 + 0) = _
    rw [add_zero]
  -- The Transition output `topW` matches the Phase0Transition output (role only).
  have hrole := Transition_roles_eq_phase0_of_both_phase0 (L := L) (K := K) s₁ s₂ h₁ h₂
  unfold topSplitStepDeltaZ pairDeltaZ
  rw [hbase_out, hbase_src,
      topW_eq_of_role_eq''' _ _ hrole.1, topW_eq_of_role_eq''' _ _ hrole.2]
  ring

/-! ## The disjoint-class rectangle marginal (joint double-marginal collapse).

The signed weight `interactionCount(s₁,s₂)·[P s₁]·[Q s₂]` summed over ordered
pairs collapses to `(∑_{P} count)·(∑_{Q} count)` when the classes `P`, `Q` are
DISJOINT (so every `(s₁,s₂)` in the rectangle has `s₁ ≠ s₂`, killing the self-pair
diagonal of `interactionCount`).  This is the joint generalization of
`sum_interactionCount_mcr_assign`; here for `ℤ`-valued signed sums. -/

/-- For a fixed initiator `s₁` in class `P`, summing `interactionCount s₁ s₂` over
responders in a class `Q` DISJOINT from `P` gives `count s₁ · (∑_{Q} count)` — no
diagonal `−1`, since `s₁ ∈ P` and `s₂ ∈ Q` forces `s₁ ≠ s₂`. -/
private lemma sum_iCount_right_disjoint
    (c : Config (AgentState L K)) (P Q : AgentState L K → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hdisj : ∀ a, P a → ¬ Q a) (s₁ : AgentState L K) (hs₁ : P s₁) :
    ∑ s₂ : AgentState L K, (if Q s₂ then c.interactionCount s₁ s₂ else 0)
      = c.count s₁ * ∑ s₂ : AgentState L K, (if Q s₂ then c.count s₂ else 0) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s₂ _ => ?_)
  by_cases hq : Q s₂
  · simp only [if_pos hq]
    have hne : s₁ ≠ s₂ := fun heq => hdisj s₁ hs₁ (heq ▸ hq)
    unfold Config.interactionCount; rw [if_neg hne]
  · simp only [if_neg hq, mul_zero]

/-- **Disjoint-class rectangle.**  For disjoint classes `P`, `Q`, the double sum
of `interactionCount(s₁,s₂)` over the `P × Q` rectangle is the product of the two
class counts:

  `∑_{s₁,s₂} [P s₁]·[Q s₂]·interactionCount(s₁,s₂)
     = (∑_{P} count)·(∑_{Q} count)`. -/
theorem sum_iCount_rectangle_disjoint
    (c : Config (AgentState L K)) (P Q : AgentState L K → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hdisj : ∀ a, P a → ¬ Q a) :
    ∑ s₁ : AgentState L K, ∑ s₂ : AgentState L K,
        (if P s₁ then (if Q s₂ then c.interactionCount s₁ s₂ else 0) else 0)
      = (∑ s₁ : AgentState L K, (if P s₁ then c.count s₁ else 0))
        * (∑ s₂ : AgentState L K, (if Q s₂ then c.count s₂ else 0)) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun s₁ _ => ?_)
  by_cases hp : P s₁
  · simp only [if_pos hp]
    rw [sum_iCount_right_disjoint c P Q hdisj s₁ hp]
  · simp only [if_neg hp, zero_mul]
    exact Finset.sum_const_zero

/-! ## Class-count collapse: `∑ [Q s]·count s = countP Q c`. -/

/-- The univ-sum of `count` restricted to a Bool class equals the `countP` of that
class.  (`∑_{s} [q s]·count s = #{a ∈ c | q a}`.) -/
private lemma sum_ite_count_eq_countP (c : Config (AgentState L K))
    (q : AgentState L K → Bool) :
    ∑ s : AgentState L K, (if q s = true then c.count s else 0)
      = Multiset.countP (fun a => q a) c := by
  classical
  set F : Finset (AgentState L K) := Finset.univ.filter (fun s => q s = true) with hF
  set cq := Multiset.filter (fun a : AgentState L K => q a = true) c with hcq
  have hrw : ∑ s : AgentState L K, (if q s = true then c.count s else 0)
      = ∑ s ∈ F, c.count s := by
    rw [hF, Finset.sum_filter]
  rw [hrw]
  have hcount : ∀ s ∈ F, c.count s = Multiset.count s cq := fun s hs => by
    show Multiset.count s c = Multiset.count s cq
    have hs_q : q s = true := (Finset.mem_filter.mp hs).2
    simp only [cq, Multiset.count_filter, hs_q, ite_true]
  calc ∑ s ∈ F, c.count s
      = ∑ s ∈ F, Multiset.count s cq := Finset.sum_congr rfl hcount
    _ = Multiset.card cq :=
        Multiset.sum_count_eq_card (s := F) (m := cq)
          (fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ a,
            (Multiset.mem_filter.mp ha).2⟩)
    _ = Multiset.countP (fun a => q a) c := by
        rw [hcq, Multiset.countP_eq_card_filter]

/-- `∑ [isMcr s]·count s = mcrCount c`. -/
private lemma sum_count_mcr (c : Config (AgentState L K)) :
    ∑ s : AgentState L K, (if isMcrB (L := L) (K := K) s = true then c.count s else 0)
      = ExactMajority.mcrCount (L := L) (K := K) c := by
  rw [sum_ite_count_eq_countP]
  unfold ExactMajority.mcrCount isMcrB
  rw [Multiset.countP_eq_card_filter]
  congr 1
  apply Multiset.filter_congr
  intro a _; simp

/-- `∑ [isUMain s]·count s = MfCount c`. -/
private lemma sum_count_uMain (c : Config (AgentState L K)) :
    ∑ s : AgentState L K, (if isUMainB (L := L) (K := K) s = true then c.count s else 0)
      = MfCount (L := L) (K := K) c :=
  sum_ite_count_eq_countP c (isUMainB (L := L) (K := K))

/-- `∑ [isUCR s]·count s = SfCount c`. -/
private lemma sum_count_uCR (c : Config (AgentState L K)) :
    ∑ s : AgentState L K, (if isUCRB (L := L) (K := K) s = true then c.count s else 0)
      = SfCount (L := L) (K := K) c :=
  sum_ite_count_eq_countP c (isUCRB (L := L) (K := K))

/-! ## Disjointness of the three classes (no diagonal correction on R2/R3 blocks). -/

/-- `mcr` and `uMain` classes are disjoint (`mcr ≠ main`). -/
private lemma mcr_uMain_disjoint (a : AgentState L K) :
    isMcrB (L := L) (K := K) a = true → isUMainB (L := L) (K := K) a ≠ true := by
  unfold isMcrB isUMainB
  intro h
  simp only [decide_eq_true_eq] at h
  simp [h]

/-- `mcr` and `uCR` classes are disjoint (`mcr ∉ {cr,clock,reserve}`). -/
private lemma mcr_uCR_disjoint (a : AgentState L K) :
    isMcrB (L := L) (K := K) a = true → isUCRB (L := L) (K := K) a ≠ true := by
  unfold isMcrB isUCRB
  intro h
  simp only [decide_eq_true_eq] at h
  simp [h]

/-! ## The integer rectangle identity.

`∑_{s₁,s₂} interactionCount·pairDeltaZ = 2·mcrCount·(Sf − Mf)`.  Splitting
`pairDeltaZ = indR3 − indR2` and each oriented indicator into its two disjoint
orientations, the four rectangle sums collapse (disjoint-class marginal) to
`mcrCount·Mf`, `Mf·mcrCount`, `mcrCount·Sf`, `Sf·mcrCount`. -/

/-- `indR2` splits into the two disjoint orientations as a sum of single-rectangle
indicators (the two disjuncts are mutually exclusive — `mcr`/`uMain` disjoint). -/
private lemma indR2_split (s₁ s₂ : AgentState L K) :
    (indR2 (L := L) (K := K) s₁ s₂ : ℤ)
      = (if isMcrB (L := L) (K := K) s₁ = true then
            (if isUMainB (L := L) (K := K) s₂ = true then (1:ℤ) else 0) else 0)
        + (if isUMainB (L := L) (K := K) s₁ = true then
            (if isMcrB (L := L) (K := K) s₂ = true then (1:ℤ) else 0) else 0) := by
  unfold indR2
  by_cases hA : isMcrB (L := L) (K := K) s₁ = true ∧ isUMainB (L := L) (K := K) s₂ = true
  · have hnB : ¬ (isUMainB (L := L) (K := K) s₁ = true) := by
      intro h; exact mcr_uMain_disjoint (L := L) (K := K) s₁ hA.1 h
    simp [hA.1, hA.2, hnB]
  · by_cases hB : isUMainB (L := L) (K := K) s₁ = true ∧ isMcrB (L := L) (K := K) s₂ = true
    · have hnA : ¬ (isMcrB (L := L) (K := K) s₁ = true) := by
        intro h; exact mcr_uMain_disjoint (L := L) (K := K) s₁ h hB.1
      simp [hB.1, hB.2, hnA]
    · simp only [hA, hB, or_self, if_false]
      by_cases h1 : isMcrB (L := L) (K := K) s₁ = true <;>
        by_cases h2 : isUMainB (L := L) (K := K) s₂ = true <;>
        by_cases h3 : isUMainB (L := L) (K := K) s₁ = true <;>
        by_cases h4 : isMcrB (L := L) (K := K) s₂ = true <;>
        simp_all

/-- `indR3` splits analogously into its two disjoint orientations. -/
private lemma indR3_split (s₁ s₂ : AgentState L K) :
    (indR3 (L := L) (K := K) s₁ s₂ : ℤ)
      = (if isMcrB (L := L) (K := K) s₁ = true then
            (if isUCRB (L := L) (K := K) s₂ = true then (1:ℤ) else 0) else 0)
        + (if isUCRB (L := L) (K := K) s₁ = true then
            (if isMcrB (L := L) (K := K) s₂ = true then (1:ℤ) else 0) else 0) := by
  unfold indR3
  by_cases hA : isMcrB (L := L) (K := K) s₁ = true ∧ isUCRB (L := L) (K := K) s₂ = true
  · have hnB : ¬ (isUCRB (L := L) (K := K) s₁ = true) := by
      intro h; exact mcr_uCR_disjoint (L := L) (K := K) s₁ hA.1 h
    simp [hA.1, hA.2, hnB]
  · by_cases hB : isUCRB (L := L) (K := K) s₁ = true ∧ isMcrB (L := L) (K := K) s₂ = true
    · have hnA : ¬ (isMcrB (L := L) (K := K) s₁ = true) := by
        intro h; exact mcr_uCR_disjoint (L := L) (K := K) s₁ h hB.1
      simp [hB.1, hB.2, hnA]
    · simp only [hA, hB, or_self, if_false]
      by_cases h1 : isMcrB (L := L) (K := K) s₁ = true <;>
        by_cases h2 : isUCRB (L := L) (K := K) s₂ = true <;>
        by_cases h3 : isUCRB (L := L) (K := K) s₁ = true <;>
        by_cases h4 : isMcrB (L := L) (K := K) s₂ = true <;>
        simp_all

/-- A single oriented `interactionCount`-weighted rectangle collapses to the
product of the two class counts (via the disjoint-class marginal, with the Bool
classes `q₁ a := q₁ a = true`). -/
private lemma iCount_rect_collapse (c : Config (AgentState L K))
    (q₁ q₂ : AgentState L K → Bool)
    (hdisj : ∀ a, q₁ a = true → q₂ a ≠ true) :
    ∑ s₁ : AgentState L K, ∑ s₂ : AgentState L K,
        ((if q₁ s₁ = true then
            (if q₂ s₂ = true then (1:ℤ) else 0) else 0) * c.interactionCount s₁ s₂)
      = (∑ s₁ : AgentState L K, (if q₁ s₁ = true then (c.count s₁ : ℤ) else 0))
        * (∑ s₂ : AgentState L K, (if q₂ s₂ = true then (c.count s₂ : ℤ) else 0)) := by
  classical
  -- Push the ℤ indicators into the nat-rectangle and cast.
  have hpt : ∀ s₁ s₂ : AgentState L K,
      ((if q₁ s₁ = true then (if q₂ s₂ = true then (1:ℤ) else 0) else 0)
          * c.interactionCount s₁ s₂)
        = ((if q₁ s₁ = true then
              (if q₂ s₂ = true then c.interactionCount s₁ s₂ else 0) else 0 : ℕ) : ℤ) := by
    intro s₁ s₂
    by_cases h1 : q₁ s₁ = true <;> by_cases h2 : q₂ s₂ = true <;> simp [h1, h2]
  simp_rw [hpt]
  rw [show (∑ s₁ : AgentState L K, ∑ s₂ : AgentState L K,
        ((if q₁ s₁ = true then (if q₂ s₂ = true then c.interactionCount s₁ s₂ else 0)
          else 0 : ℕ) : ℤ))
      = ((∑ s₁ : AgentState L K, ∑ s₂ : AgentState L K,
          (if q₁ s₁ = true then (if q₂ s₂ = true then c.interactionCount s₁ s₂ else 0)
            else 0) : ℕ) : ℤ) from by push_cast; rfl]
  rw [sum_iCount_rectangle_disjoint c (fun a => q₁ a = true) (fun a => q₂ a = true)
      (fun a ha hb => hdisj a ha hb)]
  push_cast
  congr 1 <;>
    (refine Finset.sum_congr rfl (fun s _ => ?_); by_cases h : _ = true <;> simp [h])

set_option maxHeartbeats 800000 in
/-- **The integer rectangle identity.**  The double `interactionCount`-weighted
`pairDeltaZ` sum equals `2·mcrCount·(Sf − Mf)`. -/
theorem sum_iCount_pairDeltaZ
    (c : Config (AgentState L K)) :
    ∑ s₁ : AgentState L K, ∑ s₂ : AgentState L K,
        (pairDeltaZ (L := L) (K := K) s₁ s₂ * c.interactionCount s₁ s₂)
      = 2 * (ExactMajority.mcrCount (L := L) (K := K) c : ℤ)
          * ((SfCount (L := L) (K := K) c : ℤ) - (MfCount (L := L) (K := K) c : ℤ)) := by
  classical
  -- pairDeltaZ = indR3 − indR2, split each into two oriented rectangles.
  have hexpand : ∀ s₁ s₂ : AgentState L K,
      pairDeltaZ (L := L) (K := K) s₁ s₂ * c.interactionCount s₁ s₂
        = ((if isMcrB (L := L) (K := K) s₁ = true then
              (if isUCRB (L := L) (K := K) s₂ = true then (1:ℤ) else 0) else 0)
            * c.interactionCount s₁ s₂)
          + ((if isUCRB (L := L) (K := K) s₁ = true then
              (if isMcrB (L := L) (K := K) s₂ = true then (1:ℤ) else 0) else 0)
            * c.interactionCount s₁ s₂)
          - ((if isMcrB (L := L) (K := K) s₁ = true then
              (if isUMainB (L := L) (K := K) s₂ = true then (1:ℤ) else 0) else 0)
            * c.interactionCount s₁ s₂)
          - ((if isUMainB (L := L) (K := K) s₁ = true then
              (if isMcrB (L := L) (K := K) s₂ = true then (1:ℤ) else 0) else 0)
            * c.interactionCount s₁ s₂) := by
    intro s₁ s₂
    rw [pairDeltaZ_eq_table, indR3_split, indR2_split]; ring
  simp_rw [hexpand]
  -- Distribute the four rectangle sums.
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- collapse each of the four oriented rectangles.
  rw [iCount_rect_collapse c (isMcrB (L := L) (K := K)) (isUCRB (L := L) (K := K))
        (mcr_uCR_disjoint (L := L) (K := K)),
      iCount_rect_collapse c (isUCRB (L := L) (K := K)) (isMcrB (L := L) (K := K))
        (fun a ha hb => mcr_uCR_disjoint (L := L) (K := K) a hb ha),
      iCount_rect_collapse c (isMcrB (L := L) (K := K)) (isUMainB (L := L) (K := K))
        (mcr_uMain_disjoint (L := L) (K := K)),
      iCount_rect_collapse c (isUMainB (L := L) (K := K)) (isMcrB (L := L) (K := K))
        (fun a ha hb => mcr_uMain_disjoint (L := L) (K := K) a hb ha)]
  -- rewrite each class-count sum (cast to ℤ).
  have hcastM : ∀ q : AgentState L K → Bool,
      (∑ s : AgentState L K, (if q s = true then (c.count s : ℤ) else 0))
        = ((∑ s : AgentState L K, (if q s = true then c.count s else 0) : ℕ) : ℤ) := by
    intro q; push_cast
    refine Finset.sum_congr rfl (fun s _ => ?_); by_cases h : q s = true <;> simp [h]
  rw [hcastM (isMcrB (L := L) (K := K)), hcastM (isUCRB (L := L) (K := K)),
      hcastM (isUMainB (L := L) (K := K))]
  rw [sum_count_mcr, sum_count_uCR, sum_count_uMain]
  push_cast
  ring

/-! ## `freeDiff = Mf − Sf` (the ledger free-pool difference as class counts). -/

/-- The per-agent `freeW` weight is the signed class indicator `[uMain] − [uCR]`. -/
private lemma freeW_eq_indicator (a : AgentState L K) :
    freeW (L := L) (K := K) a
      = (if isUMainB (L := L) (K := K) a = true then (1:ℤ) else 0)
        - (if isUCRB (L := L) (K := K) a = true then (1:ℤ) else 0) := by
  unfold freeW isUMainB isUCRB
  by_cases hr : a.role = .main <;> by_cases hr2 : a.role = .cr <;>
    by_cases hr3 : a.role = .clock <;> by_cases hr4 : a.role = .reserve <;>
    by_cases ha : a.assigned <;>
    simp_all [Bool.and_eq_true, decide_eq_true_eq]

/-- **`freeDiff = Mf − Sf`.**  The integer free-pool difference is exactly
`#unassigned-Main − #unassigned-CR-side`. -/
theorem freeDiff_eq_Mf_sub_Sf (c : Config (AgentState L K)) :
    freeDiff (L := L) (K := K) c
      = (MfCount (L := L) (K := K) c : ℤ) - (SfCount (L := L) (K := K) c : ℤ) := by
  classical
  unfold freeDiff MfCount SfCount Config.sumOf
  rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter]
  induction c using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, freeW_eq_indicator,
        Multiset.filter_cons, Multiset.filter_cons]
    by_cases h1 : isUMainB (L := L) (K := K) a = true <;>
      by_cases h2 : isUCRB (L := L) (K := K) a = true <;>
      simp only [h1, h2, Bool.false_eq_true, if_true, if_false, ite_true, ite_false,
        Multiset.card_add, Multiset.card_singleton, Multiset.card_zero,
        Nat.cast_add, Nat.cast_one, Nat.cast_zero] <;>
      ring

/-! ## The real connection: `totalPairs · E[ΔX] = ((∑ iCount·pairDeltaZ : ℤ) : ℝ)`. -/

/-- On the Phase-0 window, the per-pair real step delta equals the cast of the
role-determined `pairDeltaZ` whenever the pair's `interactionCount` is positive
(positive count ⟹ applicable ⟹ both agents are at phase 0). -/
private lemma topSplitStepDelta_eq_pairDeltaZ_cast_of_pos
    (c : Config (AgentState L K)) (s₁ s₂ : AgentState L K)
    (hall : Phase0Window.allPhase0 (L := L) (K := K) c)
    (hpos : 0 < c.interactionCount s₁ s₂) :
    topSplitStepDelta (L := L) (K := K) c s₁ s₂
      = (pairDeltaZ (L := L) (K := K) s₁ s₂ : ℝ) := by
  have happ : Protocol.Applicable c s₁ s₂ := applicable_of_pos_iCount'' c s₁ s₂ hpos
  have hle : ({s₁, s₂} : Config (AgentState L K)) ≤ c := happ
  have hm₁ : s₁ ∈ c := Multiset.mem_of_le hle (by simp)
  have hm₂ : s₂ ∈ c := Multiset.mem_of_le hle (by simp)
  have h₁ : s₁.phase.val = 0 := by have := hall s₁ hm₁; simp [this]
  have h₂ : s₂.phase.val = 0 := by have := hall s₂ hm₂; simp [this]
  rw [topSplitStepDelta_eq_cast]
  congr 1
  exact topSplitStepDeltaZ_eq_pairDeltaZ_of_applicable c s₁ s₂ happ h₁ h₂

/-- **`totalPairs · E[ΔX]` as the integer rectangle sum (real cast).**  On the
Phase-0 window, `totalPairs · E[ΔX] = ((∑_{s₁,s₂} iCount·pairDeltaZ : ℤ) : ℝ)`. -/
theorem totalPairs_expectedDeltaX_eq
    (c : Config (AgentState L K)) (hc2 : 2 ≤ Multiset.card c)
    (hall : Phase0Window.allPhase0 (L := L) (K := K) c) :
    (Config.totalPairs c : ℝ) * expectedDeltaX (L := L) (K := K) c
      = ((∑ s₁ : AgentState L K, ∑ s₂ : AgentState L K,
          (pairDeltaZ (L := L) (K := K) s₁ s₂ * c.interactionCount s₁ s₂) : ℤ) : ℝ) := by
  classical
  have hPpos : (0 : ℝ) < (c.totalPairs : ℝ) := by
    have := Config.totalPairs_pos hc2; exact_mod_cast this
  have hPne : (c.totalPairs : ℝ) ≠ 0 := ne_of_gt hPpos
  unfold expectedDeltaX
  rw [Finset.mul_sum]
  -- per-pair: totalPairs · (interactionProb.toReal · delta) = iCount · delta.
  have hterm : ∀ pair : AgentState L K × AgentState L K,
      (Config.totalPairs c : ℝ)
          * ((Config.interactionProb c pair.1 pair.2).toReal
              * topSplitStepDelta (L := L) (K := K) c pair.1 pair.2)
        = (c.interactionCount pair.1 pair.2 : ℝ)
            * topSplitStepDelta (L := L) (K := K) c pair.1 pair.2 := by
    intro pair
    have hprobR : (Config.interactionProb c pair.1 pair.2).toReal
        = (c.interactionCount pair.1 pair.2 : ℝ) / (c.totalPairs : ℝ) := by
      unfold Config.interactionProb
      rw [ENNReal.toReal_div]
      simp only [ENNReal.toReal_natCast]
    rw [hprobR]
    field_simp
  rw [Finset.sum_congr rfl (fun pair _ => hterm pair)]
  -- replace the real delta with the cast of pairDeltaZ on positive-count pairs.
  have hreplace : ∀ pair : AgentState L K × AgentState L K,
      (c.interactionCount pair.1 pair.2 : ℝ)
          * topSplitStepDelta (L := L) (K := K) c pair.1 pair.2
        = (((pairDeltaZ (L := L) (K := K) pair.1 pair.2
              * c.interactionCount pair.1 pair.2 : ℤ)) : ℝ) := by
    intro pair
    by_cases hpos : 0 < c.interactionCount pair.1 pair.2
    · rw [topSplitStepDelta_eq_pairDeltaZ_cast_of_pos c pair.1 pair.2 hall hpos]
      push_cast; ring
    · have hz : c.interactionCount pair.1 pair.2 = 0 := by omega
      rw [hz]; push_cast; simp
  rw [Finset.sum_congr rfl (fun pair _ => hreplace pair)]
  -- the univ-sum over pairs is the double sum; cast out.
  rw [← Int.cast_sum, Fintype.sum_prod_type]

/-! ## `RectangleResidual` — the headline. -/

/-- **`RectangleResidual` discharged on the Phase-0 window.**  Assembling the
real connection, the integer rectangle identity, and `freeDiff = Mf − Sf`:

    totalPairs · E[ΔX]
      = ((∑ iCount·pairDeltaZ : ℤ) : ℝ)        (real connection)
      = (2·mcrCount·(Sf − Mf) : ℝ)              (integer rectangle)
      = −2·mcrCount·freeDiff.                   (freeDiff = Mf − Sf)

This is the last named protocol-counting residual of TopSplitInward; everything
consuming it is now hypothesis-free (modulo the absorbing region structure). -/
theorem rectangleResidual_of_allPhase0
    (c : Config (AgentState L K)) (hc2 : 2 ≤ Multiset.card c)
    (hall : Phase0Window.allPhase0 (L := L) (K := K) c) :
    RectangleResidual (L := L) (K := K) c := by
  unfold RectangleResidual
  rw [totalPairs_expectedDeltaX_eq c hc2 hall, sum_iCount_pairDeltaZ,
      freeDiff_eq_Mf_sub_Sf]
  push_cast
  ring

/-! ## The hypothesis-free top-split tail (rectangle residual discharged).

`topSplitWindow_whp_inward` (TopSplitInward.lean) carried the open hypothesis
`hQ_rect : ∀ c, Q c → RectangleResidual c`.  With `rectangleResidual_of_allPhase0`
that hypothesis is now PROVABLE from the absorbing region's own `allPhase0` +
`card ≥ 2` data, so it is dropped.  The strongest top-split tail now carries only:

  * `Phase0Initial n c₀` — the all-`mcr` balanced start;
  * the absorbing region `Q` with `allPhase0`, `card ≥ 2`, `LedgerInv`
    (all provable: `LedgerInv` from `LedgerInv_init`/`LedgerInv_stepOrSelf`);
  * `NoAssignedMcrConfig` is no longer needed HERE (it threads only through the
    ledger-propagation construction of `Q`, not through this tail statement).

No `RectangleResidual` hypothesis remains — it is now a THEOREM. -/

/-- **The hypothesis-free top-split tail (rectangle residual discharged).**  Same
conclusion as `topSplitWindow_whp_inward`, but WITHOUT the `hQ_rect` hypothesis:
`RectangleResidual` on the region `Q` is supplied internally by
`rectangleResidual_of_allPhase0` (from `hQ_phase0` + `hQ_card`).  This is the
strongest top-split balance tail now reachable: every protocol-counting residual
(`RectangleResidual`) is discharged; only the absorbing/ledger structure of `Q`
(itself protocol-provable) and the Phase-0 balanced start remain. -/
theorem topSplitWindow_whp_rectFree
    {s : ℝ} (hs : 0 ≤ s) {δ : ℝ} {n : ℕ}
    {c₀ : Config (AgentState L K)} (hinit : Phase0Initial (L := L) (K := K) n c₀)
    (Q : Config (AgentState L K) → Prop)
    (hQ_abs : ∀ c c', Q c →
      c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support → Q c')
    (hQ_phase0 : ∀ c, Q c → Phase0Window.allPhase0 (L := L) (K := K) c)
    (hQ_card : ∀ c, Q c → 2 ≤ Multiset.card c)
    (hQ_ledger : ∀ c, Q c → LedgerInv (L := L) (K := K) c)
    (hQ0 : Q c₀)
    (T : ℕ) (hδn : 0 < s * (δ * n)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ TopSplitWindow (L := L) (K := K) δ n c}
      ≤ ENNReal.ofReal (Real.cosh s) ^ T
          / ENNReal.ofReal (Real.cosh (s * (δ * n))) :=
  topSplitWindow_whp_inward hs hinit Q hQ_abs hQ_phase0 hQ_card hQ_ledger
    (fun c hcQ => rectangleResidual_of_allPhase0 c (hQ_card c hcQ) (hQ_phase0 c hcQ))
    hQ0 T hδn

end RoleSplitConcentration
end ExactMajority
