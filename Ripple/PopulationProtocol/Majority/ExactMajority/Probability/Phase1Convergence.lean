/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase 1 — discrete averaging / cancellation before opinion collection (Doty et al., §5, Lemma 5.3)

`Phase1Transition` (Protocol/Transition.lean:447) averages the small-integer
biases of two interacting **Main** agents:

```
def Phase1Transition (s t) :=
  let (s1,t1) :=
    if s.role = .main ∧ t.role = .main then
      let (b1,b2) := avgFin7 s.smallBias t.smallBias
      ({s with smallBias := b1}, {t with smallBias := b2})
    else (s,t)
  (clockCounterStep s1, clockCounterStep t1)        -- clocks run the counter
```

where `avgFin7 x y = (⌊(x+y)/2⌋, ⌈(x+y)/2⌉)` on the `Fin 7` encoding (value `v`
encodes the integer bias `v − 3 ∈ {−3,…,+3}`).  Two Mains' smallBiases are
replaced by their floor/ceil average; the sum is **preserved**
(`avgFin7_preserves_sum`), so the global gap `g = Σ bias` is conserved.

## Lemma 5.3 — the paper's actual technique (quoted)

> "Let µ = ⌊g/|M|⌉ be the average bias among all Main agents, rounded to the
> nearest integer.  By [45], we will converge to have all bias ∈ {µ−1, µ, µ+1},
> in O(log n) time with high probability 1 − O(1/n²).  We use Corollary 1 of
> [45] … If |g| > 0.5|M| … all remaining biased agents have the majority
> opinion … stabilize in Phase 2.  If |g| ≤ 0.5|M|, then µ = 0, so now all
> bias ∈ {−1,0,+1}.  We will use Lemma 4.6 [one-sided cancel] …"

So Lemma 5.3 is **NOT** a self-contained per-step monotone-potential argument:
the *quantitative collapse to the three consecutive values* `{µ−1,µ,µ+1}` is
imported wholesale from reference [45] (Mocquard–Anceaume–… discrete averaging,
Corollary 1).  The minority-elimination tail then reuses Lemma 4.6, which is the
`OneSidedCancel` engine already in this repo.  Phase 1 is **counter-timed**: the
phase ENDS at the clock timeout regardless; Lemma 5.3 is what is TRUE at the end.

## The honest, fully-closable per-step potential

The *full* {µ−1,µ,µ+1} window-collapse is genuinely external ([45]); the inner
levels are not per-step monotone (a `−3` averaged with a `−1` yields two `−2`s,
raising the "outside {−1,0,+1}" count — checked exhaustively).  What **is**
unconditionally per-step non-increasing under `avgFin7` is the count of agents
pinned at the **saturated extremes** of the small-bias range — `smallBias.val = 6`
(`+3`) and `smallBias.val = 0` (`−3`).  Averaging can only move an extreme value
inward; it never creates a new saturated extreme (exhaustively verified over all
49 pairs).  This is the honest Phase-1 analogue of Phase 8's `minorityU`:

* `extremeSt a`   — a Main whose `smallBias` is saturated (`= 0` or `= 6`);
* `extremeU c`    — the saturated-extreme count (the ℕ-potential `Φ`);
* `Phase1AllMain n c` — the structural window: size `n`, all phase-1 Mains.

`Φ = extremeU` is non-increasing on the all-Main phase-1 window (Part C/D), and
`Φ = 0` is a genuine Lemma-5.3-shape sub-event (no Main pinned at ±3 — the spread
has contracted off the saturated boundary).  The instance `phase1Convergence`
packages this through the `OneSidedCancel.crude_PhaseConvergenceW` engine, exactly
as Phase 8 does, carrying the averaging-drain rate `q`/`hstep` as a hypothesis
(its quantitative value is the [45]/Lemma-4.6 input documented at the file foot).

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.OneSidedCancel
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.CounterTimeout
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase7Convergence

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Phase1Convergence

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

instance instMeasurableSpaceAgentState1 : MeasurableSpace (AgentState L K) := ⊤
instance instDiscreteMeasurableSpaceAgentState1 :
    DiscreteMeasurableSpace (AgentState L K) where
  forall_measurableSet _ := trivial

/-! ## Part A — the per-pair averaging arithmetic on `smallBias` (`avgFin7`). -/

/-- Sum of the two averaged small-biases equals the sum of the inputs: the global
gap `g = Σ smallBias` is conserved by an averaging interaction.  (Public restatement
of the private `avgFin7_preserves_sum_transition`.) -/
theorem avgFin7_preserves_sum (x y : Fin 7) :
    ((avgFin7 x y).1.val : ℤ) + ((avgFin7 x y).2.val : ℤ)
      = (x.val : ℤ) + (y.val : ℤ) := by
  unfold avgFin7
  have h : (x.val + y.val) / 2 + (x.val + y.val + 1) / 2 = x.val + y.val := by omega
  push_cast
  omega

/-- The two averaged values are within `1` of each other: averaging contracts the
pair spread to at most one (`⌈⌉ − ⌊⌋ ≤ 1`). -/
theorem avgFin7_spread_le_one (x y : Fin 7) :
    ((avgFin7 x y).2.val : ℤ) - ((avgFin7 x y).1.val : ℤ) ≤ 1
      ∧ (0 : ℤ) ≤ ((avgFin7 x y).2.val : ℤ) - ((avgFin7 x y).1.val : ℤ) := by
  unfold avgFin7
  have hx : x.val < 7 := x.2
  have hy : y.val < 7 := y.2
  refine ⟨?_, ?_⟩ <;> push_cast <;> omega

/-! ## Part B — the saturated-extreme predicate and the per-pair non-increase. -/

/-- A `Fin 7` small-bias value is **saturated-extreme** if it is pinned at either
end of the `{−3,…,+3}` range: `val = 0` (`−3`) or `val = 6` (`+3`). -/
def extremeVal (v : Fin 7) : Bool := v.val = 0 || v.val = 6

/-- **The key per-pair arithmetic fact (exhaustive).**  Averaging never *creates*
a saturated extreme: the number of saturated-extreme values among the two outputs
of `avgFin7` is at most the number among the two inputs.  Checked over all
`7 × 7 = 49` pairs by `decide`. -/
theorem avgFin7_extremeVal_pair_le (x y : Fin 7) :
    (if extremeVal (avgFin7 x y).1 then 1 else 0)
        + (if extremeVal (avgFin7 x y).2 then 1 else 0)
      ≤ (if extremeVal x then 1 else 0) + (if extremeVal y then 1 else 0) := by
  revert x y; decide

/-- An agent is a **saturated-extreme Main** if it is a phase-1 Main whose
`smallBias` sits at a saturated end (`val = 0` or `val = 6`).  This is the Doty
Phase-1 analogue of `minoritySt`: the agents that the averaging process drains off
the boundary toward the interior `{−1,0,+1}` window. -/
def extremeSt (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ extremeVal a.smallBias = true

instance (a : AgentState L K) : Decidable (extremeSt a) := by
  unfold extremeSt; infer_instance

/-- The saturated-extreme count over a configuration (the ℕ-potential `Φ`). -/
def extremeU (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => extremeSt a) c

/-- An agent that is not a Main is never a saturated-extreme Main. -/
theorem not_extremeSt_of_not_main (a : AgentState L K)
    (h : a.role ≠ Role.main) : ¬ extremeSt a := fun ⟨hm, _⟩ => h hm

/-- `countP extremeSt` over a two-element pair as a sum of indicators. -/
theorem countP_extremeSt_pair (x y : AgentState L K) :
    Multiset.countP (fun a => extremeSt a) ({x, y} : Multiset (AgentState L K))
      = (if extremeSt x then 1 else 0) + (if extremeSt y then 1 else 0) := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
  ring

/-! ## Part C — the per-pair reduction to averaging for two phase-1 Mains. -/

/-- For two phase-1 agents, `phaseEpidemicUpdate` is the identity (max of equal
phases, no init to run, no phase-10 entry).  Mirror of Phase 7/8's
`phaseEpidemicUpdate_eq_self_of_phaseN` at threshold 1. -/
theorem phaseEpidemicUpdate_eq_self_of_phase1 (s t : AgentState L K)
    (hs : s.phase.val = 1) (ht : t.phase.val = 1) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hsp : s.phase = ⟨1, by decide⟩ := Fin.ext hs
  have htp : t.phase = ⟨1, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hsp, htp, max_self]
  simp only [runInitsBetween_self_api]
  have hs_self : ({s with phase := (⟨1, by decide⟩ : Fin 11)} : AgentState L K) = s := by
    rw [← hsp]
  have ht_self : ({t with phase := (⟨1, by decide⟩ : Fin 11)} : AgentState L K) = t := by
    rw [← htp]
  rw [hs_self, ht_self]
  rw [if_neg (by push Not; intro _; simp)]

/-- For a Main (role ≠ clock), `clockCounterStep` is the identity. -/
theorem clockCounterStep_eq_self_of_main (a : AgentState L K)
    (h : a.role = Role.main) : clockCounterStep L K a = a := by
  unfold clockCounterStep
  rw [if_neg (by rw [h]; decide)]

/-- The averaged pair both stay Main (a `with smallBias := _` update preserves
`role`). -/
private theorem avgPair_role (s t : AgentState L K) (hsM : s.role = Role.main)
    (htM : t.role = Role.main) :
    ({s with smallBias := (avgFin7 s.smallBias t.smallBias).1} : AgentState L K).role
        = Role.main
      ∧ ({t with smallBias := (avgFin7 s.smallBias t.smallBias).2} : AgentState L K).role
        = Role.main := by
  exact ⟨hsM, htM⟩

/-- **Per-pair reduction.**  Two phase-1 Main agents interact, under the full
`Transition`, by replacing their `smallBias` fields with the floor/ceil average
(`avgFin7`); all other fields are untouched.  (Epidemic = id, dispatch =
`Phase1Transition`, both Mains so `clockCounterStep` is the identity, phase stays
`1 ≠ 10` so the phase-10 finish is the identity.) -/
theorem Transition_eq_avg_of_phase1_main (s t : AgentState L K)
    (hs1 : s.phase.val = 1) (ht1 : t.phase.val = 1)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    Transition L K s t
      = ({s with smallBias := (avgFin7 s.smallBias t.smallBias).1},
         {t with smallBias := (avgFin7 s.smallBias t.smallBias).2}) := by
  have hepi := phaseEpidemicUpdate_eq_self_of_phase1 (L := L) (K := K) s t hs1 ht1
  have hsp : s.phase = ⟨1, by decide⟩ := Fin.ext hs1
  -- Phase1Transition with both Main: averaging, then clockCounterStep = id on Mains.
  have hp1 : Phase1Transition L K s t
      = ({s with smallBias := (avgFin7 s.smallBias t.smallBias).1},
         {t with smallBias := (avgFin7 s.smallBias t.smallBias).2}) := by
    unfold Phase1Transition
    simp only [if_pos (show s.role = Role.main ∧ t.role = Role.main from ⟨hsM, htM⟩)]
    rw [clockCounterStep_eq_self_of_main (L := L) (K := K)
          ({s with smallBias := (avgFin7 s.smallBias t.smallBias).1}) (by exact hsM),
        clockCounterStep_eq_self_of_main (L := L) (K := K)
          ({t with smallBias := (avgFin7 s.smallBias t.smallBias).2}) (by exact htM)]
  unfold Transition
  rw [hepi]
  -- beta-reduce the outer `(s,t)` destructuring, then select the phase-1 dispatch arm.
  simp only []
  rw [hsp]
  -- the dispatch `match ⟨1,_⟩` reduces to the phase-1 arm = `Phase1Transition`.
  show (finishPhase10Entry L K s (Phase1Transition L K s t).1,
        finishPhase10Entry L K t (Phase1Transition L K s t).2)
      = _
  rw [hp1]
  rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _ (by simp [hs1]),
      finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _ (by simp [ht1])]
  -- the produced `.1`/`.2` records match the target up to `s.phase = ⟨1,_⟩` (hsp).
  rw [hsp]

/-- **Per-pair `extremeU` non-increase, both-Main.**  Reduce to the averaging rule
and apply the exhaustive `avgFin7_extremeVal_pair_le`. -/
theorem Transition_extremeU_pair_le_of_both_main (s t : AgentState L K)
    (hs1 : s.phase.val = 1) (ht1 : t.phase.val = 1)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    Multiset.countP (fun a => extremeSt a)
        ({(Transition L K s t).1, (Transition L K s t).2} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => extremeSt a)
          ({s, t} : Multiset (AgentState L K)) := by
  rw [Transition_eq_avg_of_phase1_main s t hs1 ht1 hsM htM]
  rw [countP_extremeSt_pair, countP_extremeSt_pair]
  -- the projected output records (the `.1`/`.2` of the produced pair).
  set o1 := ({s with smallBias := (avgFin7 s.smallBias t.smallBias).1} : AgentState L K) with ho1
  set o2 := ({t with smallBias := (avgFin7 s.smallBias t.smallBias).2} : AgentState L K) with ho2
  -- both inputs/outputs are Main, so `extremeSt` collapses to `extremeVal smallBias`.
  have hkey : ∀ a : AgentState L K, a.role = Role.main →
      (extremeSt a ↔ extremeVal a.smallBias = true) := fun a ha => by
    unfold extremeSt; exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
  have ho1M : o1.role = Role.main := by rw [ho1]; exact hsM
  have ho2M : o2.role = Role.main := by rw [ho2]; exact htM
  have ho1sb : o1.smallBias = (avgFin7 s.smallBias t.smallBias).1 := by rw [ho1]
  have ho2sb : o2.smallBias = (avgFin7 s.smallBias t.smallBias).2 := by rw [ho2]
  rw [if_congr (hkey o1 ho1M) rfl rfl, if_congr (hkey o2 ho2M) rfl rfl,
      if_congr (hkey s hsM) rfl rfl, if_congr (hkey t htM) rfl rfl,
      ho1sb, ho2sb]
  -- the outputs' smallBias are the averaged values; apply the exhaustive bound.
  have h := avgFin7_extremeVal_pair_le s.smallBias t.smallBias
  -- normalize `if (extremeVal _ = true)` to `if extremeVal _` (Bool decidable).
  simpa using h

/-! ## Part D — lifting to the config kernel: `PotNonincrOn` and `InvClosed`.

The structural Phase-1 window and the kernel-level non-increase of `extremeU`,
mirroring `Phase8Convergence` Parts C/D with `extremeU` in place of `minorityU`.
`Transition_eq_avg_of_phase1_main` shows that for two phase-1 Mains the produced
records are `{s/t with smallBias := …}`, so `phase` and `role` are preserved
*definitionally* — `Phase1AllMain` is closed with no auxiliary invariant. -/

/-- The structural Phase-1 window: a configuration of `n` agents, all phase-1
Mains. -/
def Phase1AllMain (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∀ a ∈ c, a.phase.val = 1 ∧ a.role = Role.main

private theorem mem_of_app_left1 {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right1 {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-- `extremeU` is non-increasing under any chosen-pair update on an all-Main
phase-1 window. -/
theorem extremeU_stepOrSelf_le (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase1AllMain n c) (r₁ r₂ : AgentState L K) :
    extremeU (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) ≤ extremeU c := by
  obtain ⟨_, hph⟩ := hInv
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left1 happ
    have hm2 := mem_of_app_right1 happ
    obtain ⟨h11, h1M⟩ := hph r₁ hm1
    obtain ⟨h21, h2M⟩ := hph r₂ hm2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    unfold extremeU
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair := Transition_extremeU_pair_le_of_both_main r₁ r₂ h11 h21 h1M h2M
    have hpair_le : Multiset.countP (fun a => extremeSt a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => extremeSt a) c := Multiset.countP_le_of_le _ hsub
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- `extremeU` is non-increasing on the one-step kernel support. -/
theorem extremeU_le_on_support (n : ℕ) (m : ℕ)
    (c c' : Config (AgentState L K)) (hInv : Phase1AllMain n c)
    (hle : extremeU c ≤ m)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    extremeU c' ≤ m := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]; exact le_trans (extremeU_stepOrSelf_le n c hInv r₁ r₂) hle
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'; exact hle

/-- **The engine's `hmono` (PotNonincrOn) ingredient for Phase 1.** -/
theorem extremeU_kernel_noincr (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase1AllMain n c) :
    (NonuniformMajority L K).transitionKernel c {x | extremeU c < extremeU x} = 0 := by
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | extremeU c < extremeU x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  simp only [Set.mem_setOf_eq] at hx
  have hle : extremeU x ≤ extremeU c :=
    extremeU_le_on_support n (extremeU c) c x hInv le_rfl hsupp
  omega

/-- Packaged as the engine's `PotNonincrOn` predicate. -/
theorem potNonincrOn_extremeU (n : ℕ) :
    OneSidedCancel.PotNonincrOn (fun c => Phase1AllMain n c)
      (NonuniformMajority L K).transitionKernel (fun c => extremeU c) :=
  fun c hInv => extremeU_kernel_noincr n c hInv

/-- `Phase1AllMain` is preserved by a chosen-pair update.  For two phase-1 Mains the
produced records are `{r₁/r₂ with smallBias := …}`, so `phase`/`role` are unchanged. -/
theorem Phase1AllMain_stepOrSelf (n : ℕ) (c : Config (AgentState L K))
    (hw : Phase1AllMain n c) (r₁ r₂ : AgentState L K) :
    Phase1AllMain n (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  obtain ⟨hcard, hph⟩ := hw
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left1 happ
    have hm2 := mem_of_app_right1 happ
    obtain ⟨h11, h1M⟩ := hph r₁ hm1
    obtain ⟨h21, h2M⟩ := hph r₂ hm2
    have hac := Transition_eq_avg_of_phase1_main r₁ r₂ h11 h21 h1M h2M
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    refine ⟨?_, ?_⟩
    · have hcard' := Protocol.reachable_card_eq
        (Protocol.reachable_stepOrSelf (P := NonuniformMajority L K) c r₁ r₂)
      rw [hcard']; exact hcard
    · intro a ha
      rw [hc'] at ha
      rcases Multiset.mem_add.mp ha with hold | hnew
      · exact hph a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hold)
      · rw [show ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
              : Multiset (AgentState L K))
            = (Transition L K r₁ r₂).1 ::ₘ (Transition L K r₁ r₂).2 ::ₘ 0 from rfl] at hnew
        simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hnew
        rw [hac] at hnew
        rcases hnew with h | h
        · subst h; exact ⟨h11, h1M⟩
        · subst h; exact ⟨h21, h2M⟩
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; exact ⟨hcard, hph⟩

/-- `Phase1AllMain` is one-step-support closed (the FULL engine `InvClosed`). -/
theorem Phase1AllMain_support_closed (n : ℕ) (c c' : Config (AgentState L K))
    (hw : Phase1AllMain n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    Phase1AllMain n c' := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]; exact Phase1AllMain_stepOrSelf n c hw r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'; exact hw

/-- Packaged as the engine's `InvClosed` predicate (FULL, for Phase 1). -/
theorem invClosed_phase1AllMain (n : ℕ) :
    OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Phase1AllMain (L := L) (K := K) n c) := by
  intro c hInv
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | ¬ Phase1AllMain (L := L) (K := K) n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  exact hx (Phase1AllMain_support_closed n c x hInv hsupp)

/-! ## Part E — the Phase-1 `PhaseConvergenceW` from the engine.

With both `hmono` (`potNonincrOn_extremeU`) and the FULL `hClosed`
(`invClosed_phase1AllMain`) discharged, the only remaining input is the engine's
**per-step averaging-drain bound** `hstep` — from any `Phase1AllMain`-config with at
least one saturated-extreme Main, one interaction fails to pull a saturated value
inward with probability `≤ q`.  This is the quantitative content imported from
reference [45] (Mocquard et al., the discrete-averaging convergence, Corollary 1)
in the paper's proof of Lemma 5.3: the per-interaction probability that an
extreme-holding Main meets a partner with which it averages strictly inward is
`≥ extreme·other/(n(n−1))`-shape, so the failure is `≤ q`.  We expose it as a
hypothesis (its derivation is the averaging-drain rectangle — the extreme × interior
interaction count bound, the Phase-8 `minorityU_drop_prob_rect` analogue — the
remaining quantitative atom, documented at the file foot).

`potDone (extremeU) = {c | extremeU c = 0} = NoExtreme`: no Main is pinned at the
saturated boundary `±3`.  This is a genuine Lemma-5.3-shape sub-event: the bias
spread has contracted strictly off the saturated ends toward the interior window. -/

/-- `NoExtreme c`: no phase-1 Main is pinned at a saturated bias end (`±3`) — the
honest, fully-closable Phase-1 post, equal to the engine's `potDone (extremeU)`.
The *full* Lemma-5.3 collapse to `{−1,0,+1}` is the inner-level refinement imported
from [45]. -/
def NoExtreme (c : Config (AgentState L K)) : Prop := extremeU c = 0

theorem potDone_extremeU_eq :
    OneSidedCancel.potDone (fun c : Config (AgentState L K) => extremeU c)
      = {c | NoExtreme c} := rfl

/-- **The Phase-1 averaging `PhaseConvergenceW` on the REAL kernel** (engine form b).
`Pre c = Phase1AllMain n c ∧ extremeU c ≤ M₀` (the all-Main phase-1 window with a
saturated-extreme budget — the carried role floor); `Post c = Phase1AllMain n c ∧
extremeU c = 0` (still in-window, no saturated extreme left).  Horizon `t`, failure
`ε ≥ q^t` — the `⌈C₁·n·log n⌉` / `O(1/n²)` shape of Lemma 5.3.

`hmono` and full `hClosed` are the proved `potNonincrOn_extremeU` /
`invClosed_phase1AllMain`; `hstep` is the carried averaging-drain bound (the
[45]/Lemma-4.6 quantitative input, the remaining rectangle atom). -/
noncomputable def phase1Convergence (n : ℕ) (q : ℝ≥0∞)
    (hstep : ∀ b : Config (AgentState L K), Phase1AllMain n b → 1 ≤ extremeU b →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potDone (fun c => extremeU c))ᶜ ≤ q)
    (M₀ : ℕ) (t : ℕ) (ε : ℝ≥0) (hε : (q ^ t : ℝ≥0∞) ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.crude_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase1AllMain (L := L) (K := K) n c)
    (invClosed_phase1AllMain n)
    (fun c => extremeU c)
    (potNonincrOn_extremeU n)
    q hstep M₀ t ε hε

/-- The Phase-1 instance's `Post` is exactly the structural window together with
`NoExtreme` (no Main pinned at `±3`) — the honest Lemma-5.3-shape endpoint that the
spread has contracted off the saturated boundary. -/
theorem phase1Convergence_Post (n : ℕ) (q : ℝ≥0∞)
    (hstep : ∀ b : Config (AgentState L K), Phase1AllMain n b → 1 ≤ extremeU b →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potDone (fun c => extremeU c))ᶜ ≤ q)
    (M₀ : ℕ) (t : ℕ) (ε : ℝ≥0) (hε : (q ^ t : ℝ≥0∞) ≤ (ε : ℝ≥0∞))
    (c : Config (AgentState L K)) :
    (phase1Convergence n q hstep M₀ t ε hε).Post c
      ↔ (Phase1AllMain n c ∧ NoExtreme c) := Iff.rfl

/-! ## Remaining quantitative atom (the carried `hstep`) and the scope of `Post`.

What is FULLY proved here (0-sorry, axiom-clean):

* the per-pair averaging arithmetic (`avgFin7_preserves_sum`, `avgFin7_spread_le_one`)
  and the exhaustive non-creation of saturated extremes (`avgFin7_extremeVal_pair_le`);
* the per-pair reduction `Transition = avg` for two phase-1 Mains
  (`Transition_eq_avg_of_phase1_main`) and the per-pair `extremeU` non-increase;
* the config-kernel `PotNonincrOn` (`potNonincrOn_extremeU`) and the FULL `InvClosed`
  (`invClosed_phase1AllMain`) for the all-Main phase-1 window;
* the packaged instance `phase1Convergence : PhaseConvergenceW` and its `Post`
  characterization (`phase1Convergence_Post`).

The SINGLE carried input is the engine's per-step drain bound `hstep` (the
`q`-rate).  Its honest derivation is the **averaging-drain rectangle**: on a
`Phase1AllMain` config with `≥ 1` saturated-extreme Main, the per-interaction
probability that the extreme Main meets a partner with which `avgFin7` moves the
extreme value strictly inward is `≥ extreme·other/(n(n−1))`-shape, so the failure is
`≤ q = 1 − …`.  This is the Phase-8 `minorityU_drop_prob_rect`/`drop_prob_of_rect`
analogue (the same `interactionCount`/`totalPairs` rectangle pair-counting), and is
the quantitative content the paper imports from reference [45] (Mocquard et al.,
discrete averaging, Corollary 1) in the proof of Lemma 5.3.  It is exposed as a
hypothesis exactly as Phase 7/8 expose theirs.

SCOPE of `Post = NoExtreme` vs the full Lemma 5.3:  `Post` is the honest,
per-step-monotone sub-event "no Main pinned at the saturated ends `±3`".  The
*full* Lemma-5.3 small-gap conclusion — all biases in the three consecutive values
`{µ−1,µ,µ+1}` and `≤ 0.03|M|` biased — is the inner-level window collapse, which is
NOT per-step monotone (a `−3` averaged with a `−1` yields two `−2`s, raising the
"outside `{−1,0,+1}`" count — checked exhaustively in `avgFin7_extremeVal_pair_le`'s
sibling probe).  That collapse is the external [45] convergence theorem plus the
Lemma-4.6 (`OneSidedCancel`) minority-elimination tail; instantiating it inside this
file would require formalizing [45]'s variance-decay argument, which is out of scope
for the per-step potential engine and is the genuine remaining gap for the full
small-gap Post.  The large-gap branch (`|g| ≥ 0.025|M|` ⇒ stabilize in Phase 2) is
deferred to the Phase-2 instance, as in the paper. -/
