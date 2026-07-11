/-
# HonestWindows — re-scoping the all-Main idealized drain windows to chain-honest windows

## The CRITICAL finding (source-verified, this file pins it formally)

The drain work windows `Phase1AllMain` / `Phase7AllMain` / `Phase8AllMain` are

    c.card = n ∧ ∀ a ∈ c, a.phase.val = p ∧ a.role = Role.main      (all-Main)

i.e. they require EVERY agent to be a phase-`p` Main.  But on the real chain, the
phase-0 role split (`RoleSplitConcentration.RoleSplitGood`) leaves
`clockCount ≥ n/5 > 0` clocks (and `reserveCount ≥ n/5`) coexisting with
`mainCount ≥ n/3` mains.  These role counts are **permanent** in phases 1–8 (no
frozen per-phase rule converts a Main↔Clock).  Hence on any reachable
full-population config with `n ≥ 1`, the all-Main windows are **UNSATISFIABLE**:
the 21-instance assembly's drain slots are conditionally vacuous at those work
slots.  (Doty arXiv:2106.10201v2 §6 analyzes the *Main sub-population* for the
bias dynamics; the formalization's windows over-idealized to the full population.)

`incompat_allMain_with_chain_roles` formalizes the contradiction: a config that is
both `Phase1AllMain n` (all Main) and `RoleSplitGood η n` (`n/5 ≤ #clock`, with
`n ≥ 5`) does not exist.

## The honest re-scoping

The chain-honest window drops the spurious `role = Role.main` conjunct, keeping
only the phase pin:

    c.card = n ∧ ∀ a ∈ c, a.phase.val = p             (phase-only, `PhasePHonest`)

This is exactly the shape slots 5 (`Phase5AllWin`) and 6 (`Phase6Win`) already use,
and it IS satisfiable on the chain (the phase epidemic synchronizes every agent —
Main, Clock, Reserve — to the population phase `p`; `RoleSplitGood` is silent on
the phase distribution).

## What the drain machinery actually needed (and what survives)

The landed `drop_prob_rect` lower bounds sum the drop probability over the TARGET
RECTANGLE only (a Main–Main pair that drops the potential).  Mixed pairs
(Main–Clock, Clock–Clock, Main–Reserve in phases 1/7/8) are **no-ops on the
rectangle**: they reduce neither the rectangle mass nor the bound.  So the
all-Main hypothesis was never feeding the drop lower bound directly.  What it fed:

  (a) **closure** of the working window, and
  (b) **non-increase of the potential under ALL pairs** (`PotNonincrOn`).

This file re-derives both for the weakened window, for the worst-affected slot
(slot 1) as the TEMPLATE, then slots 7 and 8 (the same `Phase{7,8}Transition`
"both-Main-or-identity" dispatch shape):

  * **Potential non-increase — SURVIVES.**  All four drain potentials
    (`extremeU` reads `smallBias`+`role=main`; `minoritySt`/`highMass` read
    `bias`+`role=main`) read ONLY Main-role fields.  In `Phase{1,7,8}Transition` a
    Main agent paired with a non-Main is returned **identically** (the
    `if both-Main` branch fails, and the trailing `clockCounterStep`/clock-guard is
    the identity on a Main); and any advanced Clock is still a non-Main, so it
    contributes `0` to every potential before and after.  Hence the per-pair
    potential bound — exactly the `PotNonincrOn` ingredient — holds on the
    phase-only window with NO role hypothesis.  The hour-drag (Phase-3 Rule 2,
    which writes a Main's `hour`) does NOT fire in phases 1/7/8 (it is in
    `Phase3Transition`), and no slot-{1,5,6,7,8} potential reads `hour`.

  * **Window closure — same status as Phase 6 (genuine, NAMED gap).**  A
    Clock–Clock interaction can ADVANCE a clock to phase `p+1`
    (`stdCounterSubroutine`), so the phase-only window is NOT one-step closed —
    identical to `Phase6Win`, which the campaign already does NOT treat as the
    engine `InvClosed` (the closure is the seam/working-window doctrine's separate
    concern).  We pin this as `clock_advance_breaks_phase_closure` so the gap is
    named, not faked.

Append-only: this file edits NO existing file.  Single-file `lake env lean` builds.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase1Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase6Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase7Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase8Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitConcentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace ExactMajority
namespace HonestWindows

variable {L K : ℕ}

/-! ## Part A — the unsatisfiability of the all-Main windows on chain-honest roles. -/

/-- On an all-Main window, EVERY agent is a Main, so `clockCount = 0`. -/
theorem clockCount_eq_zero_of_phase1AllMain {n : ℕ} {c : Config (AgentState L K)}
    (hw : Phase1Convergence.Phase1AllMain (L := L) (K := K) n c) :
    RoleSplitConcentration.clockCount (L := L) (K := K) c = 0 := by
  obtain ⟨_, hph⟩ := hw
  unfold RoleSplitConcentration.clockCount
  rw [Multiset.countP_eq_zero]
  intro a ha hclk
  have : a.role = Role.main := (hph a ha).2
  rw [this] at hclk
  exact absurd hclk (by decide)

/-- **The CRITICAL finding, formalized.**  No configuration can be simultaneously an
all-Main phase-1 window (`Phase1AllMain n`) and a chain-honest role split
(`RoleSplitGood η n` with `n ≥ 5`, `η ≤ 1/25`): the latter forces `n/5 ≤ #clock`,
the former forces `#clock = 0`, impossible for `n ≥ 5`.  Hence the all-Main drain
window is UNSATISFIABLE on every reachable post-role-split full-population config. -/
theorem incompat_allMain_with_chain_roles
    {η : ℝ} (hη : η ≤ 1 / 25) {n : ℕ} (hn : 5 ≤ n) {c : Config (AgentState L K)}
    (hAllMain : Phase1Convergence.Phase1AllMain (L := L) (K := K) n c)
    (hGood : RoleSplitConcentration.RoleSplitGood (L := L) (K := K) η n c) : False := by
  have hzero : RoleSplitConcentration.clockCount (L := L) (K := K) c = 0 :=
    clockCount_eq_zero_of_phase1AllMain hAllMain
  have hfloor : (n : ℝ) / 5 ≤ (RoleSplitConcentration.clockCount (L := L) (K := K) c : ℝ) :=
    RoleSplitConcentration.clockCount_linear_of_RoleSplitGood hη hGood
  rw [hzero] at hfloor
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have : (1 : ℝ) ≤ (n : ℝ) / 5 := by linarith
  simp only [Nat.cast_zero] at hfloor
  linarith

/-! ## Part B — the chain-honest windows (phase-only, drop the spurious role pin). -/

/-- The chain-honest phase-1 window: size `n`, every agent at phase **exactly 1**
(NO role pin).  Satisfiable on the chain (the phase epidemic synchronizes Mains,
Clocks and Reserves alike to the population phase). -/
def Phase1Honest (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∀ a ∈ c, a.phase.val = 1

/-- The chain-honest phase-7 window. -/
def Phase7Honest (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∀ a ∈ c, a.phase.val = 7

/-- The chain-honest phase-8 window. -/
def Phase8Honest (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∀ a ∈ c, a.phase.val = 8

/-- The honest window is genuinely WEAKER than the all-Main window (every all-Main
config is honest): the re-scoping only drops a conjunct, so all landed work-`Pre`
data that the all-Main window carried still holds on it. -/
theorem phase1Honest_of_allMain {n : ℕ} {c : Config (AgentState L K)}
    (hw : Phase1Convergence.Phase1AllMain (L := L) (K := K) n c) :
    Phase1Honest (L := L) (K := K) n c :=
  ⟨hw.1, fun a ha => (hw.2 a ha).1⟩

theorem phase7Honest_of_allMain {n : ℕ} {c : Config (AgentState L K)}
    (hw : Phase7Convergence.Phase7AllMain (L := L) (K := K) n c) :
    Phase7Honest (L := L) (K := K) n c :=
  ⟨hw.1, fun a ha => (hw.2 a ha).1⟩

theorem phase8Honest_of_allMain {n : ℕ} {c : Config (AgentState L K)}
    (hw : Phase8Convergence.Phase8AllMain (L := L) (K := K) n c) :
    Phase8Honest (L := L) (K := K) n c :=
  ⟨hw.1, fun a ha => (hw.2 a ha).1⟩

/-! ## Part C — SLOT 1 TEMPLATE: closure-neutrality + potential non-increase
re-derived on `Phase1Honest` (the worst-affected slot).

`Phase1Convergence` proved the engine `PotNonincrOn` only on the all-Main window
`Phase1AllMain`, where every applicable pair is both-Main and `Transition` reduces
to the averaging rule.  We re-derive the SAME `PotNonincrOn` ingredient on the
chain-honest phase-only window `Phase1Honest`, where applicable pairs may be
Main–Clock, Clock–Clock, Main–Reserve, etc.  The key structural facts:

* **Role permanence (`Transition_role_phase1`).**  The full `Transition` pipeline
  preserves every agent's role on a phase-1 pair (per-phase rule preserves role;
  `clockCounterStep` preserves role; `finishPhase10Entry` preserves role).  Hence
  an output is a Main iff its input was a Main.

* **Main untouched in mixed pairs (`Phase1Transition` not-both-Main branch).**  When
  the pair is not both-Main, `Phase1Transition` skips the averaging branch and the
  trailing `clockCounterStep` is the identity on each Main (a Main is not a clock).

Because `extremeU` counts only Mains (`extremeSt a → a.role = main`), and Mains are
either untouched (mixed pair) or averaged with the exhaustive non-increasing bound
(both-Main pair), `extremeU` does not increase under ANY applicable phase-1 pair —
no role hypothesis needed.  (A clock that ADVANCES — even into phase 10 — is still
a non-Main, hence still not `extremeSt`; `extremeU` reads no clock/hour field.)
-/

/-- `clockCounterStep` preserves an agent's role (clock stays clock; non-clock is
fixed). -/
theorem clockCounterStep_role (a : AgentState L K) :
    (clockCounterStep L K a).role = a.role := by
  unfold clockCounterStep
  split_ifs with h
  · rw [stdCounterSubroutine_clock_role_eq L K a h, h]
  · rfl

/-- `Phase1Transition` preserves both agents' roles. -/
theorem Phase1Transition_role (s t : AgentState L K) :
    (Phase1Transition L K s t).1.role = s.role ∧
      (Phase1Transition L K s t).2.role = t.role := by
  unfold Phase1Transition
  refine ⟨?_, ?_⟩ <;> · simp only []; rw [clockCounterStep_role]; split_ifs <;> rfl

/-- **Role permanence of the full `Transition` on a phase-1 pair.**  Each output's
role equals its input's role.  (Per-phase rule, counter step, and phase-10 finish
are all role-preserving.) -/
theorem Transition_role_phase1 (s t : AgentState L K)
    (hs : s.phase.val = 1) (ht : t.phase.val = 1) :
    (Transition L K s t).1.role = s.role ∧ (Transition L K s t).2.role = t.role := by
  have hepi := Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1
    (L := L) (K := K) s t hs ht
  have hsp : s.phase = ⟨1, by decide⟩ := Fin.ext hs
  unfold Transition
  rw [hepi]; simp only [hsp]
  rw [finishPhase10Entry, finishPhase10Entry, canonicalPhase10Entry_role,
    canonicalPhase10Entry_role]
  exact Phase1Transition_role s t

/-- When the pair is **not** both-Main, `Phase1Transition` skips averaging: each
output is the `clockCounterStep` of its input. -/
theorem Phase1Transition_eq_of_not_both_main (s t : AgentState L K)
    (hnb : ¬ (s.role = Role.main ∧ t.role = Role.main)) :
    Phase1Transition L K s t = (clockCounterStep L K s, clockCounterStep L K t) := by
  unfold Phase1Transition; rw [if_neg hnb]

/-- **The dispatch equality on the honest window, with the NAMED clock-no-overshoot
side condition.**  For two phase-1 agents whose `Phase1Transition` outputs do not
enter phase 10, `Transition = Phase1Transition`.  The side condition holds whenever
the advancing clock is well-formed (`smallBias ∈ {2,3,4}`, the chain invariant `W`
of `HANDOFF_SEAM_NOOVERSHOOT`): then `phaseInit`-at-2's `biasMagGT1` guard fails and
no clock enters phase 10.  This is the ONE genuinely-carried per-phase neutrality
side fact (named, not faked).  Note the potential bound below does NOT need it. -/
theorem Transition_eq_Phase1Transition_of_phase1 (s t : AgentState L K)
    (hs : s.phase.val = 1) (ht : t.phase.val = 1)
    (hno1 : (Phase1Transition L K s t).1.phase.val ≠ 10)
    (hno2 : (Phase1Transition L K s t).2.phase.val ≠ 10) :
    Transition L K s t = Phase1Transition L K s t := by
  have hepi := Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1
    (L := L) (K := K) s t hs ht
  have hsp : s.phase = ⟨1, by decide⟩ := Fin.ext hs
  unfold Transition
  rw [hepi]; simp only [hsp]
  rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _ hno1,
      finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _ hno2]

/-- **The mixed-pair `extremeU` non-increase (NO role hypothesis, NO no-overshoot).**
For a phase-1 pair that is NOT both-Main, the produced pair's `extremeSt` count is
`≤` the input pair's.  Each output is a Main iff its input is (role permanence); the
Main side (if any) is `clockCounterStep`-fixed; the non-Main side is never extreme. -/
theorem Transition_extremeU_pair_le_of_not_both_main (s t : AgentState L K)
    (hs : s.phase.val = 1) (ht : t.phase.val = 1)
    (hnb : ¬ (s.role = Role.main ∧ t.role = Role.main)) :
    Multiset.countP (fun a => Phase1Convergence.extremeSt a)
        ({(Transition L K s t).1, (Transition L K s t).2} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => Phase1Convergence.extremeSt a)
          ({s, t} : Multiset (AgentState L K)) := by
  obtain ⟨hr1, hr2⟩ := Transition_role_phase1 s t hs ht
  rw [Phase1Convergence.countP_extremeSt_pair, Phase1Convergence.countP_extremeSt_pair]
  -- helper: full Transition reduces to Phase1Transition's per-side value on the Main
  -- side; we compute each output explicitly.
  have hmain_fst : s.role = Role.main → (Transition L K s t).1 = s := by
    intro hsM
    have hepi := Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1
      (L := L) (K := K) s t hs ht
    have hsp : s.phase = ⟨1, by decide⟩ := Fin.ext hs
    have hp1 : (Phase1Transition L K s t).1 = s := by
      unfold Phase1Transition; rw [if_neg hnb]; simp only []
      exact Phase1Convergence.clockCounterStep_eq_self_of_main s hsM
    unfold Transition; rw [hepi]; simp only [hsp]
    rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _
      (by rw [hp1, hs]; decide)]
    exact hp1
  have hmain_snd : t.role = Role.main → (Transition L K s t).2 = t := by
    intro htM
    have hepi := Phase1Convergence.phaseEpidemicUpdate_eq_self_of_phase1
      (L := L) (K := K) s t hs ht
    have hsp : s.phase = ⟨1, by decide⟩ := Fin.ext hs
    have hp1 : (Phase1Transition L K s t).2 = t := by
      unfold Phase1Transition; rw [if_neg hnb]; simp only []
      exact Phase1Convergence.clockCounterStep_eq_self_of_main t htM
    unfold Transition; rw [hepi]; simp only [hsp]
    rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _
      (by rw [hp1, ht]; decide)]
    exact hp1
  -- per-side indicator bound
  have side1 : (if Phase1Convergence.extremeSt (Transition L K s t).1 then 1 else 0)
      ≤ (if Phase1Convergence.extremeSt s then 1 else 0) := by
    by_cases hsM : s.role = Role.main
    · rw [hmain_fst hsM]
    · have : ¬ Phase1Convergence.extremeSt (Transition L K s t).1 :=
        Phase1Convergence.not_extremeSt_of_not_main _ (by rw [hr1]; exact hsM)
      simp [this]
  have side2 : (if Phase1Convergence.extremeSt (Transition L K s t).2 then 1 else 0)
      ≤ (if Phase1Convergence.extremeSt t then 1 else 0) := by
    by_cases htM : t.role = Role.main
    · rw [hmain_snd htM]
    · have : ¬ Phase1Convergence.extremeSt (Transition L K s t).2 :=
        Phase1Convergence.not_extremeSt_of_not_main _ (by rw [hr2]; exact htM)
      simp [this]
  omega

/-- **Per-pair `extremeU` non-increase on the honest window (ANY roles).**  Combines
the existing both-Main bound (`Transition_extremeU_pair_le_of_both_main`) with the
mixed-pair bound above.  This is the genuinely-honest replacement for the all-Main
per-pair ingredient. -/
theorem Transition_extremeU_pair_le_honest (s t : AgentState L K)
    (hs : s.phase.val = 1) (ht : t.phase.val = 1) :
    Multiset.countP (fun a => Phase1Convergence.extremeSt a)
        ({(Transition L K s t).1, (Transition L K s t).2} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => Phase1Convergence.extremeSt a)
          ({s, t} : Multiset (AgentState L K)) := by
  by_cases hboth : s.role = Role.main ∧ t.role = Role.main
  · exact Phase1Convergence.Transition_extremeU_pair_le_of_both_main s t hs ht hboth.1 hboth.2
  · exact Transition_extremeU_pair_le_of_not_both_main s t hs ht hboth

/-! ### Lift to the engine `PotNonincrOn` on `Phase1Honest`. -/

private theorem mem_of_app_left1H {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right1H {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-- **`extremeU` is non-increasing under any chosen-pair update on `Phase1Honest`.**
The honest (phase-only) analogue of `Phase1Convergence.extremeU_stepOrSelf_le`. -/
theorem extremeU_stepOrSelf_le_honest (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase1Honest (L := L) (K := K) n c) (r₁ r₂ : AgentState L K) :
    Phase1Convergence.extremeU (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ Phase1Convergence.extremeU c := by
  obtain ⟨_, hph⟩ := hInv
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left1H happ
    have hm2 := mem_of_app_right1H happ
    have h11 : r₁.phase.val = 1 := hph r₁ hm1
    have h21 : r₂.phase.val = 1 := hph r₂ hm2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    unfold Phase1Convergence.extremeU
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair := Transition_extremeU_pair_le_honest r₁ r₂ h11 h21
    have hpair_le : Multiset.countP (fun a => Phase1Convergence.extremeSt a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => Phase1Convergence.extremeSt a) c :=
      Multiset.countP_le_of_le _ hsub
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- `extremeU` non-increase on the one-step kernel support from a `Phase1Honest` config. -/
theorem extremeU_le_on_support_honest (n : ℕ) (m : ℕ)
    (c c' : Config (AgentState L K)) (hInv : Phase1Honest (L := L) (K := K) n c)
    (hle : Phase1Convergence.extremeU c ≤ m)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    Phase1Convergence.extremeU c' ≤ m := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]; exact le_trans (extremeU_stepOrSelf_le_honest n c hInv r₁ r₂) hle
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'; exact hle

/-- **The engine's `hmono` (`PotNonincrOn`) ingredient for the HONEST slot-1 window.**
This is the genuinely-honest replacement for `Phase1Convergence.potNonincrOn_extremeU`:
same potential `extremeU`, same engine interface, but the working window is the
chain-SATISFIABLE `Phase1Honest n` (phase-only), not the unsatisfiable all-Main
`Phase1AllMain n`.  No role hypothesis enters. -/
theorem extremeU_kernel_noincr_honest (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase1Honest (L := L) (K := K) n c) :
    (NonuniformMajority L K).transitionKernel c
        {x | Phase1Convergence.extremeU c < Phase1Convergence.extremeU x} = 0 := by
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | Phase1Convergence.extremeU c < Phase1Convergence.extremeU x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  simp only [Set.mem_setOf_eq] at hx
  have hle : Phase1Convergence.extremeU x ≤ Phase1Convergence.extremeU c :=
    extremeU_le_on_support_honest n (Phase1Convergence.extremeU c) c x hInv le_rfl hsupp
  omega

/-- Packaged as the engine's `PotNonincrOn` predicate on `Phase1Honest n`. -/
theorem potNonincrOn_extremeU_honest (n : ℕ) :
    OneSidedCancel.PotNonincrOn (fun c => Phase1Honest (L := L) (K := K) n c)
      (NonuniformMajority L K).transitionKernel (fun c => Phase1Convergence.extremeU c) :=
  fun c hInv => extremeU_kernel_noincr_honest n c hInv

/-! ## Part D — the closure gap, NAMED (not faked).

The phase-only honest window is NOT one-step closed: a Clock–Clock interaction can
advance a clock from phase 1 to phase 2 (the `stdCounterSubroutine` counter step),
or even to phase 10 (the `phaseInit`-at-2 overshoot for an extreme-`smallBias`
clock), breaking `∀ a, phase = 1`.  This is the SAME status `Phase6Win` has — the
campaign does NOT treat `Phase6Win` as the engine `InvClosed`; closure is the seam /
working-window doctrine's separate concern (the §6 clock timing windows).  We name
the obstruction so it is an honest gap, not a hidden assumption.

The potential lift above (`potNonincrOn_extremeU_honest`) is the ingredient the
drop-rectangle lower bound actually consumes; it survives WITHOUT closure, because
`PotNonincrOn` is a per-step ≤ on the potential, not a window-membership claim. -/

/-- **The named closure obstruction.**  If a phase-1 clock's counter step lands it
at a different phase (the generic case once its counter reaches 0), then its
`clockCounterStep` image is no longer at phase 1 — so the phase-only window is not
preserved by that agent's update.  (This is exactly the clock advance the §6 timing
windows govern; the seam doctrine owns it, not the drain engine.) -/
theorem clock_advance_breaks_phase_closure
    (a : AgentState L K)
    (hadv : (clockCounterStep L K a).phase.val = 2) :
    (clockCounterStep L K a).phase.val ≠ 1 := by
  rw [hadv]; decide

/-! ## Part E — SLOT 8 (and SLOT 7): the template carries verbatim.

Slots 7 (`cancelSplit`) and 8 (`absorbConsume`) have the IDENTICAL
"both-Main-or-identity" `Phase{7,8}Transition` shape as slot 1's `Phase1Transition`.
The potential is `minoritySt σ` (Doty `B`-pool), which — like `extremeU` — counts
only Mains (`minoritySt σ a → a.role = main`).  We re-derive the slot-8 honest
`PotNonincrOn` (`minorityU σ` non-increase on `Phase8Honest`), then package slot 7
the same way modulo its extra eliminator-gap hypothesis.

Slot 8 is the cleanest because its both-Main per-pair bound
(`Phase8Convergence.Transition_minorityU_pair_le_of_both_main`) is UNCONDITIONAL.
-/

/-- `Phase8Transition` preserves both agents' roles (`absorbConsume` preserves role;
the clock guard keeps a clock a clock). -/
theorem Phase8Transition_role (s t : AgentState L K) :
    (Phase8Transition L K s t).1.role = s.role ∧
      (Phase8Transition L K s t).2.role = t.role := by
  refine ⟨?_, ?_⟩
  · unfold Phase8Transition; simp only []
    have hs1 : (if s.role = Role.main ∧ t.role = Role.main
        then (absorbConsume L K s t).1 else s).role = s.role := by
      split_ifs with h
      · exact absorbConsume_role_fst L K s t
      · rfl
    set s1 := (if s.role = Role.main ∧ t.role = Role.main
      then (absorbConsume L K s t).1 else s)
    split_ifs with hc
    · rw [stdCounterSubroutine_clock_role_eq L K s1 hc, ← hs1, hc]
    · exact hs1
  · unfold Phase8Transition; simp only []
    have ht1 : (if s.role = Role.main ∧ t.role = Role.main
        then (absorbConsume L K s t).2 else t).role = t.role := by
      split_ifs with h
      · exact absorbConsume_role_snd L K s t
      · rfl
    set t1 := (if s.role = Role.main ∧ t.role = Role.main
      then (absorbConsume L K s t).2 else t)
    split_ifs with hc
    · rw [stdCounterSubroutine_clock_role_eq L K t1 hc, ← ht1, hc]
    · exact ht1

/-- **Role permanence of the full `Transition` on a phase-8 pair.** -/
theorem Transition_role_phase8 (s t : AgentState L K)
    (hs : s.phase.val = 8) (ht : t.phase.val = 8) :
    (Transition L K s t).1.role = s.role ∧ (Transition L K s t).2.role = t.role := by
  have hepi := Phase8Convergence.phaseEpidemicUpdate_eq_self_of_phase8
    (L := L) (K := K) s t hs ht
  have hsp : s.phase = ⟨8, by decide⟩ := Fin.ext hs
  unfold Transition
  rw [hepi]; simp only [hsp]
  rw [finishPhase10Entry, finishPhase10Entry, canonicalPhase10Entry_role,
    canonicalPhase10Entry_role]
  exact Phase8Transition_role s t

/-- **The mixed-pair `minorityU` non-increase, phase 8 (NO role / no-overshoot hyp).** -/
theorem Transition_minorityU_pair_le_of_not_both_main8 (σ : Sign) (s t : AgentState L K)
    (hs : s.phase.val = 8) (ht : t.phase.val = 8)
    (hnb : ¬ (s.role = Role.main ∧ t.role = Role.main)) :
    Multiset.countP (fun a => Phase7Convergence.minoritySt σ a)
        ({(Transition L K s t).1, (Transition L K s t).2} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => Phase7Convergence.minoritySt σ a)
          ({s, t} : Multiset (AgentState L K)) := by
  obtain ⟨hr1, hr2⟩ := Transition_role_phase8 s t hs ht
  rw [Phase7Convergence.countP_minoritySt_pair, Phase7Convergence.countP_minoritySt_pair]
  -- Main side untouched (mixed pair); non-Main side never a minority.
  have hmain_fst : s.role = Role.main → (Transition L K s t).1 = s := by
    intro hsM
    have hepi := Phase8Convergence.phaseEpidemicUpdate_eq_self_of_phase8
      (L := L) (K := K) s t hs ht
    have hsp : s.phase = ⟨8, by decide⟩ := Fin.ext hs
    have hp8 : (Phase8Transition L K s t).1 = s := by
      unfold Phase8Transition; simp only [if_neg hnb]
      rw [if_neg (show s.role ≠ Role.clock by rw [hsM]; decide)]
    unfold Transition; rw [hepi]; simp only [hsp]
    rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _
      (by rw [hp8, hs]; decide)]
    exact hp8
  have hmain_snd : t.role = Role.main → (Transition L K s t).2 = t := by
    intro htM
    have hepi := Phase8Convergence.phaseEpidemicUpdate_eq_self_of_phase8
      (L := L) (K := K) s t hs ht
    have hsp : s.phase = ⟨8, by decide⟩ := Fin.ext hs
    have hp8 : (Phase8Transition L K s t).2 = t := by
      unfold Phase8Transition; simp only [if_neg hnb]
      rw [if_neg (show t.role ≠ Role.clock by rw [htM]; decide)]
    unfold Transition; rw [hepi]; simp only [hsp]
    rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _
      (by rw [hp8, ht]; decide)]
    exact hp8
  have side1 : (if Phase7Convergence.minoritySt σ (Transition L K s t).1 then 1 else 0)
      ≤ (if Phase7Convergence.minoritySt σ s then 1 else 0) := by
    by_cases hsM : s.role = Role.main
    · rw [hmain_fst hsM]
    · have : ¬ Phase7Convergence.minoritySt σ (Transition L K s t).1 :=
        Phase7Convergence.not_minoritySt_of_not_main σ _ (by rw [hr1]; exact hsM)
      simp [this]
  have side2 : (if Phase7Convergence.minoritySt σ (Transition L K s t).2 then 1 else 0)
      ≤ (if Phase7Convergence.minoritySt σ t then 1 else 0) := by
    by_cases htM : t.role = Role.main
    · rw [hmain_snd htM]
    · have : ¬ Phase7Convergence.minoritySt σ (Transition L K s t).2 :=
        Phase7Convergence.not_minoritySt_of_not_main σ _ (by rw [hr2]; exact htM)
      simp [this]
  omega

/-- **Per-pair `minorityU σ` non-increase on the honest phase-8 window (ANY roles).** -/
theorem Transition_minorityU_pair_le_honest8 (σ : Sign) (s t : AgentState L K)
    (hs : s.phase.val = 8) (ht : t.phase.val = 8) :
    Multiset.countP (fun a => Phase7Convergence.minoritySt σ a)
        ({(Transition L K s t).1, (Transition L K s t).2} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => Phase7Convergence.minoritySt σ a)
          ({s, t} : Multiset (AgentState L K)) := by
  by_cases hboth : s.role = Role.main ∧ t.role = Role.main
  · exact Phase8Convergence.Transition_minorityU_pair_le_of_both_main σ s t hs ht
      hboth.1 hboth.2
  · exact Transition_minorityU_pair_le_of_not_both_main8 σ s t hs ht hboth

/-- **`minorityU σ` non-increase under any chosen-pair update on `Phase8Honest`.** -/
theorem minorityU_stepOrSelf_le_honest8 (σ : Sign) (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase8Honest (L := L) (K := K) n c) (r₁ r₂ : AgentState L K) :
    Phase7Convergence.minorityU σ (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ Phase7Convergence.minorityU σ c := by
  obtain ⟨_, hph⟩ := hInv
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left1H happ
    have hm2 := mem_of_app_right1H happ
    have h18 : r₁.phase.val = 8 := hph r₁ hm1
    have h28 : r₂.phase.val = 8 := hph r₂ hm2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    unfold Phase7Convergence.minorityU
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair := Transition_minorityU_pair_le_honest8 σ r₁ r₂ h18 h28
    have hpair_le : Multiset.countP (fun a => Phase7Convergence.minoritySt σ a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => Phase7Convergence.minoritySt σ a) c :=
      Multiset.countP_le_of_le _ hsub
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- **The engine `PotNonincrOn` ingredient for the HONEST slot-8 window.**  The
genuinely-honest replacement for `Phase8Convergence`'s all-Main `PotNonincrOn`:
same potential `minorityU σ`, chain-SATISFIABLE phase-only window `Phase8Honest n`. -/
theorem potNonincrOn_minorityU_honest8 (σ : Sign) (n : ℕ) :
    OneSidedCancel.PotNonincrOn (fun c => Phase8Honest (L := L) (K := K) n c)
      (NonuniformMajority L K).transitionKernel
      (fun c => Phase7Convergence.minorityU σ c) := by
  intro c hInv
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | Phase7Convergence.minorityU σ c < Phase7Convergence.minorityU σ x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  simp only [Set.mem_setOf_eq] at hx
  have hle : Phase7Convergence.minorityU σ x ≤ Phase7Convergence.minorityU σ c := by
    by_cases hc : 2 ≤ c.card
    · rw [show (NonuniformMajority L K).stepDistOrSelf c
          = (NonuniformMajority L K).stepDist c hc by
          unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hsupp
      obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc x hsupp
      rw [← hr]; exact minorityU_stepOrSelf_le_honest8 σ n c hInv r₁ r₂
    · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
          unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hsupp
      rw [PMF.mem_support_pure_iff] at hsupp; subst hsupp; exact le_rfl
  omega

/-! ### SLOT 7 — same template, modulo the eliminator-gap carry.

`Phase7Transition` has the identical "both-Main `cancelSplit` or identity" shape.
The mixed-pair part of the bound is identical to slot 8 (Main untouched, non-Main
never a minority).  The both-Main part keeps `Phase7Convergence`'s extra
eliminator-gap hypothesis `hgap` (a genuine per-config carry — Lemma 7.4's gap
ordering), NOT a role hypothesis.  We deliver the mixed-pair bound + role
permanence so the honest slot-7 `PotNonincrOn` closes the moment `hgap` is supplied. -/

/-- `Phase7Transition` preserves both agents' roles. -/
theorem Phase7Transition_role (s t : AgentState L K) :
    (Phase7Transition L K s t).1.role = s.role ∧
      (Phase7Transition L K s t).2.role = t.role := by
  refine ⟨?_, ?_⟩
  · unfold Phase7Transition; simp only []
    have hs1 : (if s.role = Role.main ∧ t.role = Role.main
        then (cancelSplit L K s t).1 else s).role = s.role := by
      split_ifs with h
      · exact cancelSplit_role_fst L K s t
      · rfl
    set s1 := (if s.role = Role.main ∧ t.role = Role.main
      then (cancelSplit L K s t).1 else s)
    split_ifs with hc
    · rw [stdCounterSubroutine_clock_role_eq L K s1 hc, ← hs1, hc]
    · exact hs1
  · unfold Phase7Transition; simp only []
    have ht1 : (if s.role = Role.main ∧ t.role = Role.main
        then (cancelSplit L K s t).2 else t).role = t.role := by
      split_ifs with h
      · exact cancelSplit_role_snd L K s t
      · rfl
    set t1 := (if s.role = Role.main ∧ t.role = Role.main
      then (cancelSplit L K s t).2 else t)
    split_ifs with hc
    · rw [stdCounterSubroutine_clock_role_eq L K t1 hc, ← ht1, hc]
    · exact ht1

/-- **Role permanence of the full `Transition` on a phase-7 pair.** -/
theorem Transition_role_phase7 (s t : AgentState L K)
    (hs : s.phase.val = 7) (ht : t.phase.val = 7) :
    (Transition L K s t).1.role = s.role ∧ (Transition L K s t).2.role = t.role := by
  have hepi := Phase7Convergence.phaseEpidemicUpdate_eq_self_of_phase7
    (L := L) (K := K) s t hs ht
  have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs
  unfold Transition
  rw [hepi]; simp only [hsp]
  rw [finishPhase10Entry, finishPhase10Entry, canonicalPhase10Entry_role,
    canonicalPhase10Entry_role]
  exact Phase7Transition_role s t

/-- **The mixed-pair `minorityU` non-increase, phase 7 (NO role / no-overshoot hyp).**
Identical to slot 8: the Main is untouched, the non-Main is never a minority. -/
theorem Transition_minorityU_pair_le_of_not_both_main7 (σ : Sign) (s t : AgentState L K)
    (hs : s.phase.val = 7) (ht : t.phase.val = 7)
    (hnb : ¬ (s.role = Role.main ∧ t.role = Role.main)) :
    Multiset.countP (fun a => Phase7Convergence.minoritySt σ a)
        ({(Transition L K s t).1, (Transition L K s t).2} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => Phase7Convergence.minoritySt σ a)
          ({s, t} : Multiset (AgentState L K)) := by
  obtain ⟨hr1, hr2⟩ := Transition_role_phase7 s t hs ht
  rw [Phase7Convergence.countP_minoritySt_pair, Phase7Convergence.countP_minoritySt_pair]
  have hmain_fst : s.role = Role.main → (Transition L K s t).1 = s := by
    intro hsM
    have hepi := Phase7Convergence.phaseEpidemicUpdate_eq_self_of_phase7
      (L := L) (K := K) s t hs ht
    have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs
    have hp7 : (Phase7Transition L K s t).1 = s := by
      unfold Phase7Transition; simp only [if_neg hnb]
      rw [if_neg (show s.role ≠ Role.clock by rw [hsM]; decide)]
    unfold Transition; rw [hepi]; simp only [hsp]
    rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _
      (by rw [hp7, hs]; decide)]
    exact hp7
  have hmain_snd : t.role = Role.main → (Transition L K s t).2 = t := by
    intro htM
    have hepi := Phase7Convergence.phaseEpidemicUpdate_eq_self_of_phase7
      (L := L) (K := K) s t hs ht
    have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs
    have hp7 : (Phase7Transition L K s t).2 = t := by
      unfold Phase7Transition; simp only [if_neg hnb]
      rw [if_neg (show t.role ≠ Role.clock by rw [htM]; decide)]
    unfold Transition; rw [hepi]; simp only [hsp]
    rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _
      (by rw [hp7, ht]; decide)]
    exact hp7
  have side1 : (if Phase7Convergence.minoritySt σ (Transition L K s t).1 then 1 else 0)
      ≤ (if Phase7Convergence.minoritySt σ s then 1 else 0) := by
    by_cases hsM : s.role = Role.main
    · rw [hmain_fst hsM]
    · have : ¬ Phase7Convergence.minoritySt σ (Transition L K s t).1 :=
        Phase7Convergence.not_minoritySt_of_not_main σ _ (by rw [hr1]; exact hsM)
      simp [this]
  have side2 : (if Phase7Convergence.minoritySt σ (Transition L K s t).2 then 1 else 0)
      ≤ (if Phase7Convergence.minoritySt σ t then 1 else 0) := by
    by_cases htM : t.role = Role.main
    · rw [hmain_snd htM]
    · have : ¬ Phase7Convergence.minoritySt σ (Transition L K s t).2 :=
        Phase7Convergence.not_minoritySt_of_not_main σ _ (by rw [hr2]; exact htM)
      simp [this]
  omega

/-! ### SLOT 6 — already honest.

`Phase6Win n = (card = n ∧ ∀ a, phase = 6)` is ALREADY the phase-only honest shape:
no `role = main` conjunct.  Its landed `highMass` non-increase
(`Phase6Convergence.highMass_stepOrSelf_le`) and dispatch
(`Transition_eq_Phase6Transition_of_phase6`, phase-only) already admit Main–Clock,
Main–Reserve and Clock–Clock pairs.  So slot 6 needs NO re-scoping (verdict:
full-population-honest).  We record the identification for the roster. -/
theorem phase6Win_is_honest_shape (n : ℕ) (c : Config (AgentState L K)) :
    Phase6Convergence.Phase6Win (L := L) (K := K) n c ↔
      (c.card = n ∧ ∀ a ∈ c, a.phase.val = 6) :=
  Iff.rfl

end HonestWindows
end ExactMajority
