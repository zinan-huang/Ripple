/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase 8 — consume the last minority agents (Doty et al. §6, Phase 8)

`Phase8Transition` (Protocol/Transition.lean:1407) is the final consumption phase,
via `absorbConsume`:

```
def Phase8Transition (s t) :=
  if s.role = .main ∧ t.role = .main then absorbConsume L K s t
  else (s,t)   -- (clock agents run the counter subroutine)
```

and `absorbConsume` (Transition.lean:1313) on two **opposite-sign** dyadic biases:
the higher-exponent (larger index `i`, smaller |bias|) agent with `full = false`
consumes the other — marks itself `full := true` and sets the consumed agent's bias
to `.zero`.  Crucially it **never sign-flips**: each branch either zeroes one agent
or is the identity.  Hence the count of `σ`-signed Main agents is **unconditionally
non-increasing** — no index-ordering hypothesis is needed (unlike Phase 7's
`cancelSplit`, whose gap-2 branch can copy a sign).

## Honest predicate / potential choices (vs the HANDOFF sketch placeholders)

The sketch named `Phase7PostCore`, `NoMinority`, `IsMinority` — none exist in the
repo.  We read honest in-file predicates off the actual `absorbConsume` rule:

* `minoritySt σ a`  — a Main with a `σ`-signed dyadic bias (the Doty `B`-pool);
  reused from `Phase7Convergence`;
* `minorityU σ c`   — the minority count;
* `Phase8AllMain n` — the structural window: size `n`, all agents phase-8 Mains.

The **shrinking-eliminator handling** the task flags: `absorbConsume` sets the
consumer's `full := true`, and a `full` agent can no longer consume (it drops out of
the eliminator pool).  But this does **not** threaten the potential: the eliminator
floor enters only through the per-step drain probability `q` (the `hstep` hypothesis
of the engine), and the honest carried invariant is that the eliminator pool stays
`≥ minority-remaining + margin` (Doty Lemma 7.6: after Phase 7, `≥ 0.8|M|` majority
vs `≤ 0.2|M|` minority, and even as eliminators go `full` the surviving non-`full`
majority stays above the minority count).  The potential `Φ = minorityU σ` itself is
non-increasing regardless of `full` (consumption only zeroes biases), which is what
the engine's `hmono` needs — proved here unconditionally.

This file delivers the engine's `hmono` (PotNonincrOn) + structural `InvClosed`
core for Phase 8, mirroring `Phase7Convergence` but WITHOUT the index ordering
(`absorbConsume` is sign-preserving).  The drain rectangle (`hstep`) is the
remaining atom, documented at the file foot.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.OneSidedCancel
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase7Convergence

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Phase8Convergence

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

open Phase7Convergence (minoritySt minorityU biasIsSigned minoritySt_iff
  countP_minoritySt_pair not_minoritySt_of_not_main)

/-! ## Part A — the per-pair reduction to `absorbConsume` for two phase-8 Mains. -/

/-- For two phase-8 agents, `phaseEpidemicUpdate` is the identity. -/
theorem phaseEpidemicUpdate_eq_self_of_phase8 (s t : AgentState L K)
    (hs : s.phase.val = 8) (ht : t.phase.val = 8) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hsp : s.phase = ⟨8, by decide⟩ := Fin.ext hs
  have htp : t.phase = ⟨8, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hsp, htp, max_self]
  simp only [runInitsBetween_self_api]
  have hs_self : ({s with phase := (⟨8, by decide⟩ : Fin 11)} : AgentState L K) = s := by
    rw [← hsp]
  have ht_self : ({t with phase := (⟨8, by decide⟩ : Fin 11)} : AgentState L K) = t := by
    rw [← htp]
  rw [hs_self, ht_self]
  rw [if_neg (by push Not; intro _; simp)]

/-- `absorbConsume` never changes an agent's phase. -/
theorem absorbConsume_phase (s t : AgentState L K) :
    (absorbConsume L K s t).1.phase = s.phase ∧ (absorbConsume L K s t).2.phase = t.phase := by
  unfold absorbConsume
  match s.bias, t.bias with
  | .zero, _ => simp
  | .dyadic .pos _, .zero => simp
  | .dyadic .neg _, .zero => simp
  | .dyadic .pos i, .dyadic .neg j => simp; split_ifs <;> simp
  | .dyadic .neg i, .dyadic .pos j => simp; split_ifs <;> simp
  | .dyadic .pos _, .dyadic .pos _ => simp
  | .dyadic .neg _, .dyadic .neg _ => simp

/-- **Per-pair reduction.**  Two phase-8 Main agents interact via `absorbConsume`
under the full `Transition`. -/
theorem Transition_eq_absorbConsume_of_phase8_main (s t : AgentState L K)
    (hs8 : s.phase.val = 8) (ht8 : t.phase.val = 8)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    Transition L K s t = absorbConsume L K s t := by
  have hepi := phaseEpidemicUpdate_eq_self_of_phase8 (L := L) (K := K) s t hs8 ht8
  have hsp : s.phase = ⟨8, by decide⟩ := Fin.ext hs8
  have hnsclk : s.role ≠ Role.clock := by rw [hsM]; decide
  have hntclk : t.role ≠ Role.clock := by rw [htM]; decide
  have hp8 : Phase8Transition L K s t = absorbConsume L K s t := by
    unfold Phase8Transition
    simp only [if_pos (show s.role = Role.main ∧ t.role = Role.main from ⟨hsM, htM⟩),
      absorbConsume_role_fst, absorbConsume_role_snd, if_neg hnsclk, if_neg hntclk]
  obtain ⟨hac1, hac2⟩ := absorbConsume_phase (L := L) (K := K) s t
  unfold Transition
  rw [hepi]
  simp only [hsp]
  rw [show (Phase8Transition L K s t) = absorbConsume L K s t from hp8]
  rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _ (by rw [hac1, hs8]; omega),
      finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _ (by rw [hac2, ht8]; omega)]

/-! ## Part B — per-pair minority non-increase under `absorbConsume` (unconditional).

Every `absorbConsume` branch either is the identity or sets exactly one agent's
bias to `.zero` (consumption) while only flipping the other's `full` flag — it
**never changes a sign**.  So the `σ`-Main count of the produced pair is at most
that of the consumed pair, with NO index-ordering hypothesis. -/

/-- A bias-side characterization, reused. `absorbConsume` preserves roles
(`absorbConsume_role_fst/snd`), so indicators are evaluated at Mains exactly when
the inputs are. -/
theorem absorbConsume_minorityU_pair_le (σ : Sign) (s t : AgentState L K)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    Multiset.countP (fun a => minoritySt σ a)
        ({(absorbConsume L K s t).1, (absorbConsume L K s t).2} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => minoritySt σ a)
          ({s, t} : Multiset (AgentState L K)) := by
  classical
  have hr1 : (absorbConsume L K s t).1.role = s.role := absorbConsume_role_fst L K s t
  have hr2 : (absorbConsume L K s t).2.role = t.role := absorbConsume_role_snd L K s t
  rw [countP_minoritySt_pair, countP_minoritySt_pair]
  have key : ∀ x : AgentState L K, x.role = Role.main →
      (minoritySt σ x ↔ biasIsSigned σ x.bias) := fun x hx => by
    rw [minoritySt_iff]; exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  rw [if_congr (key s hsM) rfl rfl, if_congr (key t htM) rfl rfl,
      if_congr (key _ (by rw [hr1]; exact hsM)) rfl rfl,
      if_congr (key _ (by rw [hr2]; exact htM)) rfl rfl]
  -- Bias-level case analysis: each branch zeroes a bias or is identity.
  unfold absorbConsume biasIsSigned
  rcases hsb : s.bias with _ | ⟨sgs, i⟩ <;> rcases htb : t.bias with _ | ⟨sgt, j⟩ <;>
    simp only [hsb, htb]
  all_goals (
    first
    | (rcases sgs with _ | _ <;> rcases sgt with _ | _ <;>
        simp only [] <;> split_ifs <;> simp_all <;> omega)
    | (split_ifs <;> simp_all <;> omega)
    | simp_all)

/-- **Per-pair strict drain.**  The canonical eliminator-consumes-minority event:
`s` is a `σ`-minority Main at exponent index `i`, `t` is a `σ.flip` (majority /
eliminator) Main at the strictly higher index `j > i` and is not yet `full`.  Then
`absorbConsume` fires the second consume branch, zeroing the minority `s`'s bias, so
the pair's `σ`-Main count strictly drops (output `+ 1 ≤` input).  This is the
per-pair seed of the drain rectangle: each (eliminator, minority) interaction with
the eliminator at the higher index removes one minority agent. -/
theorem absorbConsume_minorityU_pair_drop (σ st : Sign) (s t : AgentState L K)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (i j : Fin (L + 1)) (hsb : s.bias = Bias.dyadic σ i)
    (htb : t.bias = Bias.dyadic st j) (hst : st ≠ σ) (hlt : i.val < j.val)
    (htf : ¬ t.full) :
    Multiset.countP (fun a => minoritySt σ a)
        ({(absorbConsume L K s t).1, (absorbConsume L K s t).2} : Multiset (AgentState L K))
        + 1
      ≤ Multiset.countP (fun a => minoritySt σ a)
          ({s, t} : Multiset (AgentState L K)) := by
  classical
  -- `s` is a `σ`-minority; `t` is a `st`-Main with `st ≠ σ` hence NOT a `σ`-minority.
  have hsmin : minoritySt σ s := ⟨hsM, i, hsb⟩
  have htnotmin : ¬ minoritySt σ t := by
    rw [minoritySt_iff]; rintro ⟨_, hb⟩
    rw [htb] at hb; simp only [biasIsSigned] at hb
    exact hst hb
  -- `σ` and `st` are the two distinct signs.  Identify the consume output: the
  -- second branch (`j > i ∧ ¬ t.full`) zeroes `s` (the minority).
  have hcs : absorbConsume L K s t = ({s with bias := .zero}, {t with full := true}) := by
    unfold absorbConsume
    rw [hsb, htb]
    rcases hσ : σ with _ | _ <;> rcases hst' : st with _ | _ <;>
      simp only [] <;>
      first
      | (exact absurd (hst'.trans hσ.symm) hst)
      | (rw [if_neg (by rintro ⟨h, _⟩; omega), if_pos ⟨hlt, htf⟩])
  rw [countP_minoritySt_pair, countP_minoritySt_pair, hcs]
  -- Outputs: `{s with bias := .zero}` is not a minority; `{t with full := true}` is
  -- not a `σ`-minority (its bias is still `st ≠ σ`).
  have ho1 : ¬ minoritySt σ ({s with bias := (.zero : Bias L)}) := by
    rw [minoritySt_iff]; rintro ⟨_, hb⟩
    simp only [biasIsSigned] at hb
  have ho2 : ¬ minoritySt σ ({t with full := true}) := by
    rw [minoritySt_iff]; rintro ⟨_, hb⟩
    simp only at hb; rw [htb] at hb; simp only [biasIsSigned] at hb
    exact hst hb
  rw [if_neg ho1, if_neg ho2, if_pos hsmin, if_neg htnotmin]
theorem Phase8Transition_minorityU_eq_of_not_both_main (σ : Sign) (s t : AgentState L K)
    (h : ¬ (s.role = Role.main ∧ t.role = Role.main)) :
    Multiset.countP (fun a => minoritySt σ a)
        ({(Phase8Transition L K s t).1, (Phase8Transition L K s t).2}
          : Multiset (AgentState L K))
      = Multiset.countP (fun a => minoritySt σ a) ({s, t} : Multiset (AgentState L K)) := by
  classical
  rw [countP_minoritySt_pair, countP_minoritySt_pair]
  have hside : ∀ (x : AgentState L K),
      (if minoritySt σ (if x.role = Role.clock then stdCounterSubroutine L K x else x)
        then (1 : ℕ) else 0) = (if minoritySt σ x then 1 else 0) := by
    intro x
    by_cases hxc : x.role = Role.clock
    · rw [if_pos hxc]
      have h1 : ¬ minoritySt σ (stdCounterSubroutine L K x) :=
        not_minoritySt_of_not_main σ _ (by
          have hcr : (stdCounterSubroutine L K x).role = Role.clock :=
            stdCounterSubroutine_clock_role_eq (L := L) (K := K) x hxc
          rw [hcr]; decide)
      have h2 : ¬ minoritySt σ x := not_minoritySt_of_not_main σ x (by rw [hxc]; decide)
      rw [if_neg h1, if_neg h2]
    · rw [if_neg hxc]
  unfold Phase8Transition
  simp only [if_neg h]
  rw [hside s, hside t]

/-! ## Part C — config-level non-increase over an all-Main phase-8 window. -/

/-- The all-Main phase-8 window: the honest carried Phase-7 output (every agent a
phase-8 Main).  No index ordering is needed — `absorbConsume` is sign-preserving. -/
def Phase8AllMain (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ ∀ a ∈ c, a.phase.val = 8 ∧ a.role = Role.main

private theorem mem_of_app_left8 {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right8 {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-- **Per-pair `Transition` minority non-increase, both-Main.**  Reduce to
`absorbConsume` and apply the unconditional pair bound. -/
theorem Transition_minorityU_pair_le_of_both_main (σ : Sign) (s t : AgentState L K)
    (hs8 : s.phase.val = 8) (ht8 : t.phase.val = 8)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    Multiset.countP (fun a => minoritySt σ a)
        ({(Transition L K s t).1, (Transition L K s t).2} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => minoritySt σ a) ({s, t} : Multiset (AgentState L K)) := by
  rw [Transition_eq_absorbConsume_of_phase8_main s t hs8 ht8 hsM htM]
  exact absorbConsume_minorityU_pair_le σ s t hsM htM

/-- **Config-level strict drain.**  On an all-Main phase-8 window, an applicable
pair `(s,t)` where `s` is a `σ`-minority at index `i`, `t` is an opposite-sign Main
at the strictly higher index `j > i` and is not `full`, drops the global minority
count by one (`minorityU (step) + 1 ≤ minorityU c`).  The eliminator-consumes-minority
rectangle's per-cell drop fact (the Phase-4 `advancedU_stepOrSelf_advance` analogue,
in the draining direction). -/
theorem minorityU_stepOrSelf_drop (σ st : Sign) (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase8AllMain n c) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t)
    (i j : Fin (L + 1)) (hsb : s.bias = Bias.dyadic σ i)
    (htb : t.bias = Bias.dyadic st j) (hst : st ≠ σ) (hlt : i.val < j.val)
    (htf : ¬ t.full) :
    minorityU σ (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1
      ≤ minorityU σ c := by
  obtain ⟨_, hph⟩ := hInv
  have hm1 := mem_of_app_left8 happ
  have hm2 := mem_of_app_right8 happ
  obtain ⟨h18, h1M⟩ := hph s hm1
  obtain ⟨h28, h2M⟩ := hph t hm2
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  unfold minorityU
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  rw [Transition_eq_absorbConsume_of_phase8_main s t h18 h28 h1M h2M]
  have hdrop := absorbConsume_minorityU_pair_drop σ st s t h1M h2M i j hsb htb hst hlt htf
  have hpair_le : Multiset.countP (fun a => minoritySt σ a)
      ({s, t} : Multiset (AgentState L K))
        ≤ Multiset.countP (fun a => minoritySt σ a) c := Multiset.countP_le_of_le _ hsub
  omega

/-- `minorityU σ` is non-increasing under any chosen-pair update on an all-Main
phase-8 window. -/
theorem minorityU_stepOrSelf_le (σ : Sign) (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase8AllMain n c) (r₁ r₂ : AgentState L K) :
    minorityU σ (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ minorityU σ c := by
  obtain ⟨_, hph⟩ := hInv
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left8 happ
    have hm2 := mem_of_app_right8 happ
    obtain ⟨h18, h1M⟩ := hph r₁ hm1
    obtain ⟨h28, h2M⟩ := hph r₂ hm2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    unfold minorityU
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    have hpair := Transition_minorityU_pair_le_of_both_main σ r₁ r₂ h18 h28 h1M h2M
    have hpair_le : Multiset.countP (fun a => minoritySt σ a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => minoritySt σ a) c := Multiset.countP_le_of_le _ hsub
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- `minorityU σ` is non-increasing on the one-step kernel support. -/
theorem minorityU_le_on_support (σ : Sign) (n : ℕ) (m : ℕ)
    (c c' : Config (AgentState L K)) (hInv : Phase8AllMain n c)
    (hle : minorityU σ c ≤ m)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    minorityU σ c' ≤ m := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]; exact le_trans (minorityU_stepOrSelf_le σ n c hInv r₁ r₂) hle
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'; exact hle

/-- **The engine's `hmono` (PotNonincrOn) ingredient for Phase 8.** -/
theorem minorityU_kernel_noincr (σ : Sign) (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase8AllMain n c) :
    (NonuniformMajority L K).transitionKernel c
      {x | minorityU σ c < minorityU σ x} = 0 := by
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | minorityU σ c < minorityU σ x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  simp only [Set.mem_setOf_eq] at hx
  have hle : minorityU σ x ≤ minorityU σ c :=
    minorityU_le_on_support σ n (minorityU σ c) c x hInv le_rfl hsupp
  omega

/-- Packaged as the engine's `PotNonincrOn` predicate. -/
theorem potNonincrOn_minorityU (σ : Sign) (n : ℕ) :
    OneSidedCancel.PotNonincrOn (fun c => Phase8AllMain n c)
      (NonuniformMajority L K).transitionKernel (fun c => minorityU σ c) :=
  fun c hInv => minorityU_kernel_noincr σ n c hInv

/-! ## Part D — the structural (card + phase-8 + role-Main) closure of `Phase8AllMain`.

`absorbConsume` preserves phase (`absorbConsume_phase`) and role
(`absorbConsume_role_fst/snd`), and every applicable pair on the window is
both-Main, so `Transition` = `absorbConsume`.  Hence `Phase8AllMain` is one-step
closed — this is the FULL engine `InvClosed` (no separate ordering invariant is
needed, unlike Phase 7). -/

/-- `Phase8AllMain` is preserved by a chosen-pair update. -/
theorem Phase8AllMain_stepOrSelf (n : ℕ) (c : Config (AgentState L K))
    (hw : Phase8AllMain n c) (r₁ r₂ : AgentState L K) :
    Phase8AllMain n (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  obtain ⟨hcard, hph⟩ := hw
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left8 happ
    have hm2 := mem_of_app_right8 happ
    obtain ⟨h18, h1M⟩ := hph r₁ hm1
    obtain ⟨h28, h2M⟩ := hph r₂ hm2
    have hac := Transition_eq_absorbConsume_of_phase8_main r₁ r₂ h18 h28 h1M h2M
    have hacphase := absorbConsume_phase (L := L) (K := K) r₁ r₂
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
        · subst h
          exact ⟨by rw [hacphase.1]; exact h18, by rw [absorbConsume_role_fst]; exact h1M⟩
        · subst h
          exact ⟨by rw [hacphase.2]; exact h28, by rw [absorbConsume_role_snd]; exact h2M⟩
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; exact ⟨hcard, hph⟩

/-- `Phase8AllMain` is one-step-support closed (the FULL engine `InvClosed`). -/
theorem Phase8AllMain_support_closed (n : ℕ) (c c' : Config (AgentState L K))
    (hw : Phase8AllMain n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    Phase8AllMain n c' := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]; exact Phase8AllMain_stepOrSelf n c hw r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'; exact hw

/-- Packaged as the engine's `InvClosed` predicate (FULL, for Phase 8). -/
theorem invClosed_phase8AllMain (n : ℕ) :
    OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Phase8AllMain (L := L) (K := K) n c) := by
  intro c hInv
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | ¬ Phase8AllMain (L := L) (K := K) n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  exact hx (Phase8AllMain_support_closed n c x hInv hsupp)

/-! ## Part D' — the generic drop-rectangle probability bound.

The dual of `Phase4Convergence.advanced_advance_prob_of_rect`: for a potential `Φ`
and a rectangle `R` of pairs each of which, when fired, drops `Φ` by `≥ 1`, the
one-step probability of the **drop** event `{c' | Φ c' + 1 ≤ Φ c}` is at least
`N/(n(n−1))` where `N ≤ ∑_R interactionCount`.  Φ-agnostic; the per-cell drop fact
is the hypothesis `hdrop`.  This is the rectangle layer for the Phase-8 drain
(`hdrop` = `minorityU_stepOrSelf_drop`-shaped). -/
theorem drop_prob_of_rect (Φ : Config (AgentState L K) → ℕ) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hcardn : c.card = n)
    (R : Finset (AgentState L K × AgentState L K)) (N : ℕ)
    (hdrop : ∀ p ∈ R, 1 ≤ c.count p.1 → 1 ≤ c.count p.2 → (p.1 = p.2 → 2 ≤ c.count p.1) →
      Φ (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2) + 1 ≤ Φ c)
    (hcount : (N : ℕ) ≤ ∑ p ∈ R, c.interactionCount p.1 p.2) :
    ENNReal.ofReal ((N : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Φ c' + 1 ≤ Φ c} := by
  set j := Φ c with hjdef
  have hcard2 : 2 ≤ c.card := by rw [hcardn]; omega
  have hmeas : MeasurableSet {c' : Config (AgentState L K) | Φ c' + 1 ≤ j} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  set S : Finset (AgentState L K × AgentState L K) :=
    R.filter (fun p => 1 ≤ c.count p.1 ∧ 1 ≤ c.count p.2 ∧ (p.1 = p.2 → 2 ≤ c.count p.1)) with hS
  have hsub : (↑S : Set (AgentState L K × AgentState L K)) ⊆
      (Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
        {c' | Φ c' + 1 ≤ j} := by
    intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hS] at hp
    obtain ⟨hpc, hp1, hp2, hp3⟩ := hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Protocol.scheduledStep]
    exact hdrop p hpc hp1 hp2 hp3
  have hstepDist : (NonuniformMajority L K).stepDistOrSelf c
      = (NonuniformMajority L K).stepDist c hcard2 := by
    unfold Protocol.stepDistOrSelf; rw [dif_pos hcard2]
  have hbase : ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Φ c' + 1 ≤ j}
      = (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | Φ c' + 1 ≤ j}) := by
    rw [hstepDist]; unfold Protocol.stepDist
    rw [PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete) hmeas]
  rw [hbase]
  have hmono : (c.interactionPMF hcard2).toMeasure (↑S : Set _)
      ≤ (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹'
            {c' | Φ c' + 1 ≤ j}) :=
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

/-! ## Part D'' — the eliminator × minority rectangle at a fixed level.

Fix a level `i`.  The minority states at exponent index `i` (`σ`-Mains with bias
`.dyadic σ i`) interacting with eliminator states at any STRICTLY higher index `>i`
that are non-`full` `σ.flip`-Mains form a rectangle each of whose cells, when fired,
drops `minorityU σ` by one (`minorityU_stepOrSelf_drop`).  The rectangle's
`interactionCount` mass is `(#minority@i)·(#elim@>i)` (cross pairs are distinct: the
biases differ, so the states differ).  Feeding it to `drop_prob_of_rect` gives the
per-step drop probability `≥ (#minority@i)·(#elim@>i)/(n(n−1))`. -/

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

/-- For two state-finsets of pairwise-distinct states, the `interactionCount` mass
of `A ×ˢ B` is `(∑_A count)·(∑_B count)`.  Local copy of
`Phase4Convergence.sum_interactionCount_cross_disjoint`. -/
private theorem sum_interactionCount_cross_disjoint
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

/-- The `σ`-minority states at a fixed exponent index `i`. -/
def minorityAt (σ : Sign) (i : Fin (L + 1)) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.main ∧ a.bias = Bias.dyadic σ i)

/-- The eliminator states above index `i`: non-`full` `σ.flip`-Mains at index `> i`. -/
def elimAbove (σ : Sign) (i : Fin (L + 1)) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.main ∧ ¬ a.full ∧
    ∃ st j, st ≠ σ ∧ i.val < j.val ∧ a.bias = Bias.dyadic st j)

/-- Cross pairs `(minority@i, elim@>i)` are distinct states (their biases differ:
index `i` vs index `> i`). -/
theorem minorityAt_elimAbove_disjoint (σ : Sign) (i : Fin (L + 1))
    (a : AgentState L K) (ha : a ∈ minorityAt (L := L) (K := K) σ i)
    (b : AgentState L K) (hb : b ∈ elimAbove (L := L) (K := K) σ i) : a ≠ b := by
  simp only [minorityAt, elimAbove, Finset.mem_filter] at ha hb
  obtain ⟨_, _, hab⟩ := ha
  obtain ⟨_, _, _, st, j, _, hij, hbb⟩ := hb
  intro heq; subst heq
  rw [hab] at hbb; injection hbb with _ hidx
  rw [hidx] at hij; omega

/-- **Per-level eliminator×minority rectangle drop probability.**  On a phase-8
all-Main window, the probability that one step drops `minorityU σ` is at least
`(#minority@i)·(#elim@>i)/(n(n−1))`, for any fixed level `i`. -/
theorem minorityU_drop_prob_rect (σ : Sign) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : Phase8AllMain n c) (i : Fin (L + 1)) :
    ENNReal.ofReal
        (((minorityAt (L := L) (K := K) σ i).sum c.count *
          (elimAbove (L := L) (K := K) σ i).sum c.count : ℕ) /
          ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | minorityU σ c' + 1 ≤ minorityU σ c} := by
  have hcardn : c.card = n := hInv.1
  refine drop_prob_of_rect (fun c => minorityU σ c) n hn c hcardn
    ((minorityAt (L := L) (K := K) σ i) ×ˢ (elimAbove (L := L) (K := K) σ i))
    _ ?_ (le_of_eq ?_)
  · -- per-cell drop: each (minority@i, elim@>i) pair drops minorityU by one.
    rintro ⟨s, t⟩ hp hcs hct _
    rw [Finset.mem_product] at hp
    obtain ⟨hsmem, htmem⟩ := hp
    simp only [minorityAt, Finset.mem_filter] at hsmem
    simp only [elimAbove, Finset.mem_filter] at htmem
    obtain ⟨_, hsM, hsb⟩ := hsmem
    obtain ⟨_, htM, htf, st, j, hst, hij, htb⟩ := htmem
    have happ : Protocol.Applicable c s t := by
      have hsm : s ∈ c := Multiset.one_le_count_iff_mem.mp hcs
      have htm : t ∈ c := Multiset.one_le_count_iff_mem.mp hct
      have hne : s ≠ t :=
        minorityAt_elimAbove_disjoint σ i s
          (by simp only [minorityAt, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hsM, hsb⟩) t
          (by simp only [elimAbove, Finset.mem_filter]
              exact ⟨Finset.mem_univ _, htM, htf, st, j, hst, hij, htb⟩)
      exact applicable_of_mem_distinct hsm htm hne
    exact minorityU_stepOrSelf_drop σ st n c hInv s t happ i j hsb htb hst hij htf
  · -- rectangle interactionCount mass = product of counts.
    rw [sum_interactionCount_cross_disjoint c _ _
      (minorityAt_elimAbove_disjoint σ i)]

/-! ## Part D''' — the engine `hdrop` from the rectangle drop probability.

The level-`m` engine `hdrop` is `K b (potBelow Φ m)ᶜ ≤ q` for `Φ b = m`.  The
complement of the drop-success event `{Φ c' + 1 ≤ Φ b} = {Φ c' < m} = potBelow Φ m`
is exactly `(potBelow Φ m)ᶜ`, and `transitionKernel` is Markov (total mass 1), so the
failure mass is `1 − (drop-success mass) ≤ 1 − p` where `p` is the rectangle floor.
We package the per-level `hdrop` with `q m = 1 − (#min@i)·(#elim@>i)/(n(n−1))` as the
honest level-`m` drain bound — the remaining input is the carried eliminator floor
(`#elim@>i ≥` margin, `#min@i ≥ 1` at level `m`), the documented Doty-Lemma-7.6
boundary, supplied as the `p`-lower-bound hypothesis. -/

/-- **The engine `hdrop` from a drop-probability floor.**  If from a phase-8 window
state `b` with `minorityU σ b = m` the one-step drop probability is `≥ p` (the
rectangle floor at some level), then the engine's level-`m` failure mass is `≤ 1 − p`. -/
theorem minorityU_hdrop_of_floor (σ : Sign) (n : ℕ) (m : ℕ)
    (p : ℝ≥0∞) (b : Config (AgentState L K)) (hb8 : Phase8AllMain n b)
    (hbm : minorityU σ b = m)
    (hfloor : p ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
        {c' | minorityU σ c' + 1 ≤ minorityU σ b}) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (minorityU σ) m)ᶜ ≤ 1 - p := by
  classical
  -- The drop-success event equals `potBelow (minorityU σ) m` (using `minorityU b = m`).
  have hKb : (NonuniformMajority L K).transitionKernel b
      = ((NonuniformMajority L K).stepDistOrSelf b).toMeasure := rfl
  have hsucc_eq : {c' : Config (AgentState L K) | minorityU σ c' + 1 ≤ minorityU σ b}
      = OneSidedCancel.potBelow (minorityU σ) m := by
    ext c'; simp only [OneSidedCancel.potBelow, Set.mem_setOf_eq, hbm]; omega
  have hmeas : MeasurableSet (OneSidedCancel.potBelow (minorityU σ) m) :=
    OneSidedCancel.potBelow_measurable (minorityU (L := L) (K := K) σ) m
  -- total mass 1 (Markov), so complement = 1 − success.
  haveI hprob : IsProbabilityMeasure
      (((NonuniformMajority L K).stepDistOrSelf b).toMeasure) := by
    rw [← hKb]
    exact (inferInstance :
      IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure b
  have htot : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure Set.univ = 1 :=
    hprob.measure_univ
  have hcompl : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
        (OneSidedCancel.potBelow (minorityU σ) m)ᶜ
      = 1 - ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
          (OneSidedCancel.potBelow (minorityU σ) m) := by
    rw [measure_compl hmeas (measure_ne_top _ _), htot]
  rw [hKb, hcompl]
  have hp_le : p ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
      (OneSidedCancel.potBelow (minorityU σ) m) := by
    rw [← hsucc_eq]; exact hfloor
  exact tsub_le_tsub_left hp_le 1

/-! ## Part E — the Phase-8 `PhaseConvergenceW` from the engine.

With both `hmono` (`potNonincrOn_minorityU`) and the FULL `hClosed`
(`invClosed_phase8AllMain`) discharged, the only remaining input is the engine's
**per-step drain bound** `hstep` — from any `Phase8AllMain`-config with at least one
minority agent, one interaction fails to consume a minority with probability `≤ q`.
This is exactly the honest carried eliminator-floor fact: by Lemma 7.6 the
non-`full` majority pool (`≥ 0.8|M| − consumed`) stays above the minority pool
(`≤ 0.2|M|`), so the per-step consume probability is `≥ minority·eFloor/(n(n−1))`,
i.e. the failure is `≤ q = 1 − eFloor/(n(n−1))`-shape.  We expose it as a hypothesis
(its derivation is the drain-rectangle atom — the eliminator × minority interaction
count bound, the Phase-4 `advanced_advance_prob_of_rect` analogue — documented as the
remaining work).

`potDone (minorityU σ) = {c | minorityU σ c = 0} = NoMinority σ`: no `σ`-minority
agent remains, the honest Phase-8 `Post` (Lemma 7.6). -/

/-- `NoMinority σ c`: no `σ`-Main remains — the honest Phase-8 post (Lemma 7.6),
equal to the engine's `potDone (minorityU σ)`. -/
def NoMinority (σ : Sign) (c : Config (AgentState L K)) : Prop := minorityU σ c = 0

theorem potDone_minorityU_eq (σ : Sign) :
    OneSidedCancel.potDone (fun c : Config (AgentState L K) => minorityU σ c)
      = {c | NoMinority σ c} := rfl

/-- **The Phase-8 consumption `PhaseConvergenceW` on the REAL kernel** (engine
form b).  `Pre c = Phase8AllMain n c ∧ minorityU σ c ≤ M₀` (the all-Main phase-8
window with a minority budget); `Post c = Phase8AllMain n c ∧ minorityU σ c = 0`
(still in-window, no minority left).  Horizon `t`, failure `ε ≥ q^t`.

The `hmono` and full `hClosed` are the proved `potNonincrOn_minorityU` /
`invClosed_phase8AllMain`; `hstep` is the carried eliminator-floor drain bound
(the remaining drain-rectangle atom). -/
noncomputable def phase8Convergence (σ : Sign) (n : ℕ) (q : ℝ≥0∞)
    (hstep : ∀ b : Config (AgentState L K), Phase8AllMain n b → 1 ≤ minorityU σ b →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potDone (fun c => minorityU σ c))ᶜ ≤ q)
    (M₀ : ℕ) (t : ℕ) (ε : ℝ≥0) (hε : (q ^ t : ℝ≥0∞) ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.crude_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase8AllMain (L := L) (K := K) n c)
    (invClosed_phase8AllMain n)
    (fun c => minorityU σ c)
    (potNonincrOn_minorityU σ n)
    q hstep M₀ t ε hε

end Phase8Convergence

end ExactMajority
