/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase 5 — Reserve sampling convergence + sampled-class concentration (Doty §7.1, Lemma 7.1)

This file assembles the Phase-5 `PhaseConvergenceW` (Lemma 7.1) on top of the
`ReserveSampling.lean` machinery and adds the **sampled-class concentration** — the
genuinely new, quantitative side of Lemma 7.1 that Phase 6 consumes.

## The staticity finding (the load-bearing fact)

The paper's footnote 11 (§7.1) states explicitly *why* sampling (Phase 5) and splitting
(Phase 6) are separated into two phases: so that the **Main agents keep a fixed exponent
distribution while the Reserves sample it**.  We verify this at the protocol level:

> **`Phase5Transition` never changes any agent's `bias`.**

`Phase5Transition` only ever (a) writes a *Reserve's* `hour` (the sample field) and
(b) runs the clock counter subroutine on *clocks* (which preserves `bias` for phase ≥ 5).
A Main's `bias` is therefore frozen throughout Phase 5.  Consequently the **biased-Main
exponent-class profile is a deterministic invariant of Phase 5** (`biasedMainClassU` is
conserved by every kernel step on the phase-5 window), and each Reserve's sample is an
independent draw against this *static* class profile.

## The concentration design (sum-of-independent-indicators Chernoff)

With the Main class profile static, the sampled-Reserve class counts `R_{−i}` are sums of
independent indicators: under the uniform-pair kernel the first biased Main a Reserve meets
is ~uniform over the biased-Main pool, so each newly-sampled Reserve lands in class `−i`
with probability `class_i / biasedTotal`.  The per-step drift of the sampled-class-`i`
deficit potential is therefore the standard `WindowConcentration` exponential-MGF
contraction (in-house machinery; no external Chernoff axiom).  The paper's `−l` vs `−(l+1)`
case split (Lemma 7.2's two cases) selects *which* static class fraction is ≥ the needed
floor (`0.18|R|` resp. `0.58|R|`); both are instances of the same concentration with
different target classes.

This file delivers:
* the staticity theorems (Main bias frozen ⟹ class profile conserved);
* the sampled-class / biased-Main class count infrastructure;
* the `ReserveSampleGood` predicate (all-sampled ∧ a sampled-class floor) and the assembled
  `phase5Convergence` `PhaseConvergenceW`, with the all-sampled side discharged by
  `ReserveSampling.phase5SampledConvergence` and the class-concentration floor carried as the
  honest in-house-MGF input (the precise campaign hook recorded in the report).

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ReserveSampling
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EarlyDripMarked
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.WindowConcentration

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Phase5Convergence

open ReserveSampling

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

instance instMeasurableSpaceAgentState5 : MeasurableSpace (AgentState L K) := ⊤
instance instDiscreteMeasurableSpaceAgentState5 :
    DiscreteMeasurableSpace (AgentState L K) where
  forall_measurableSet _ := trivial

/-! ## Part A — staticity: `Phase5Transition` freezes every agent's `bias`. -/

/-- `phaseInit` preserves `bias` for any target phase `p` with `p.val ≥ 5` (only the
phase-{1,2,3} inits ever rewrite `bias`, and those are `< 5`).  Local copy of the protocol's
`private` lemma. -/
theorem phaseInit_bias_ge_five (p : Fin 11) (a : AgentState L K) (hp : 5 ≤ p.val) :
    (phaseInit L K p a).bias = a.bias := by
  set_option linter.unusedSimpArgs false in
  fin_cases p <;> simp_all (config := { decide := false }) <;>
    simp [phaseInit, enterPhase10] <;> split_ifs <;> simp [enterPhase10]

/-- `advancePhaseWithInit` preserves `bias` for an agent at phase ≥ 5 (advancePhase keeps
bias; the post-advance `phaseInit` lands at a phase `≥ 6 ≥ 5`, so it preserves bias too —
unless capped at phase 10, where `phaseInit` at 10 = `enterPhase10`, which also preserves
bias). -/
theorem advancePhaseWithInit_bias_ge_five (a : AgentState L K) (ha : 5 ≤ a.phase.val) :
    (advancePhaseWithInit L K a).bias = a.bias := by
  unfold advancePhaseWithInit
  have hadv_bias : (advancePhase L K a).bias = a.bias := by
    unfold advancePhase; split <;> rfl
  have hadv_phase : 5 ≤ (advancePhase L K a).phase.val := by
    exact le_trans ha (advancePhase_phase_nondec L K a)
  rw [phaseInit_bias_ge_five (advancePhase L K a).phase (advancePhase L K a) hadv_phase]
  exact hadv_bias

/-- `stdCounterSubroutine` preserves `bias` for an agent at phase ≥ 5. -/
theorem stdCounterSubroutine_bias_ge_five (a : AgentState L K) (ha : 5 ≤ a.phase.val) :
    (stdCounterSubroutine L K a).bias = a.bias := by
  unfold stdCounterSubroutine
  split
  · exact advancePhaseWithInit_bias_ge_five (L := L) (K := K) a ha
  · rfl

/-- **Staticity (left output).**  `Phase5Transition` never changes the first agent's `bias`
when both agents are at phase 5.  Sampling only writes `hour`; the clock subroutine
preserves `bias` for phase ≥ 5. -/
theorem Phase5Transition_fst_bias_eq (s t : AgentState L K)
    (hs : s.phase.val = 5) :
    (Phase5Transition L K s t).1.bias = s.bias := by
  unfold Phase5Transition
  simp only
  -- The left output is `if s1.role = clock then stdCounterSubroutine s1 else s1`, where
  -- `s1 ∈ {s, {s with hour := …}}` (sampling only writes hour ⇒ bias = s.bias), and the
  -- clock subroutine preserves bias for phase ≥ 5.
  have hstep : ∀ s1 : AgentState L K, s1.bias = s.bias → s1.phase.val = 5 →
      (if s1.role = Role.clock then stdCounterSubroutine L K s1 else s1).bias = s.bias := by
    intro s1 hb1 hp1
    by_cases hsc : s1.role = Role.clock
    · rw [if_pos hsc, stdCounterSubroutine_bias_ge_five (L := L) (K := K) s1 (by omega)]; exact hb1
    · rw [if_neg hsc]; exact hb1
  by_cases hb1 : s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero
  · rw [if_pos hb1]
    by_cases hg : s.hour.val = L
    · rw [if_pos hg]; exact hstep _ rfl (by simpa using hs)
    · rw [if_neg hg]; exact hstep _ rfl hs
  · rw [if_neg hb1]
    by_cases hb2 : t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero
    · rw [if_pos hb2]
      by_cases hg2 : t.hour.val = L
      · rw [if_pos hg2]; exact hstep _ rfl hs
      · rw [if_neg hg2]; exact hstep _ rfl hs
    · rw [if_neg hb2]; exact hstep _ rfl hs

/-- **Staticity (second output).** -/
theorem Phase5Transition_snd_bias_eq (s t : AgentState L K)
    (ht : t.phase.val = 5) :
    (Phase5Transition L K s t).2.bias = t.bias := by
  unfold Phase5Transition
  simp only
  have hstep : ∀ t1 : AgentState L K, t1.bias = t.bias → t1.phase.val = 5 →
      (if t1.role = Role.clock then stdCounterSubroutine L K t1 else t1).bias = t.bias := by
    intro t1 hb1 hp1
    by_cases htc : t1.role = Role.clock
    · rw [if_pos htc, stdCounterSubroutine_bias_ge_five (L := L) (K := K) t1 (by omega)]; exact hb1
    · rw [if_neg htc]; exact hb1
  by_cases hb1 : s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero
  · rw [if_pos hb1]
    by_cases hg : s.hour.val = L
    · rw [if_pos hg]; exact hstep _ rfl ht
    · rw [if_neg hg]; exact hstep _ rfl ht
  · rw [if_neg hb1]
    by_cases hb2 : t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero
    · rw [if_pos hb2]
      by_cases hg2 : t.hour.val = L
      · rw [if_pos hg2]; exact hstep _ rfl (by simpa using ht)
      · rw [if_neg hg2]; exact hstep _ rfl ht
    · rw [if_neg hb2]; exact hstep _ rfl ht

/-! ## Part B — role staticity and the conserved biased-Main class profile. -/

/-- `phaseInit` preserves `role` for any target phase `p` with `p.val ≥ 5`.  Local copy of
the protocol's `private` lemma. -/
theorem phaseInit_role_ge_five (p : Fin 11) (a : AgentState L K) (hp : 5 ≤ p.val) :
    (phaseInit L K p a).role = a.role := by
  set_option linter.unusedSimpArgs false in
  fin_cases p <;> simp_all (config := { decide := false }) <;>
    simp [phaseInit, enterPhase10] <;> split_ifs <;> simp [enterPhase10]

/-- `advancePhaseWithInit` preserves `role` for an agent at phase ≥ 5. -/
theorem advancePhaseWithInit_role_ge_five (a : AgentState L K) (ha : 5 ≤ a.phase.val) :
    (advancePhaseWithInit L K a).role = a.role := by
  unfold advancePhaseWithInit
  have hadv_role : (advancePhase L K a).role = a.role := by unfold advancePhase; split <;> rfl
  have hadv_phase : 5 ≤ (advancePhase L K a).phase.val :=
    le_trans ha (advancePhase_phase_nondec L K a)
  rw [phaseInit_role_ge_five (advancePhase L K a).phase (advancePhase L K a) hadv_phase]
  exact hadv_role

/-- `stdCounterSubroutine` preserves `role` for an agent at phase ≥ 5. -/
theorem stdCounterSubroutine_role_ge_five (a : AgentState L K) (ha : 5 ≤ a.phase.val) :
    (stdCounterSubroutine L K a).role = a.role := by
  unfold stdCounterSubroutine
  split
  · exact advancePhaseWithInit_role_ge_five (L := L) (K := K) a ha
  · rfl

/-- **Staticity of `role` (left output).**  A phase-5 Phase5Transition keeps the first
agent's `role`.  (Sampling writes `hour` only; clock subroutine preserves role for ph ≥ 5.) -/
theorem Phase5Transition_fst_role_eq (s t : AgentState L K) (_hs : s.phase.val = 5) :
    (Phase5Transition L K s t).1.role = s.role := by
  rcases Phase5Transition_fst_role_hour (L := L) (K := K) s t with hclk | ⟨hr, _⟩
  · -- left output is a clock; this forces s.role to be clock too (else sampling/identity
    -- keeps role = s.role, contradicting clock).  We instead show s.role = clock.
    -- From the structure: the only way the output is a clock is `s1.role = clock`, and
    -- `s1.role = s.role` in all non-clock-producing branches.  So `s.role = clock`.
    -- Re-derive via the role-hour disjunct's second component if available; otherwise the
    -- output clock came from a clock input.  We argue: if s.role ≠ clock then output role
    -- = s.role ≠ clock, contradiction.
    by_cases hsc : s.role = Role.clock
    · rw [hclk, hsc]
    · -- non-clock branch: output role = s.role; but hclk says clock — contradiction unless
      -- s.role = clock.  We reconstruct output role = s.role.
      exfalso
      -- Use the bias-style hstep: output role equals s.role in every non-clock-producing case.
      have hrole_out : (Phase5Transition L K s t).1.role = s.role := by
        unfold Phase5Transition; simp only
        have hstep : ∀ s1 : AgentState L K, s1.role = s.role →
            (if s1.role = Role.clock then stdCounterSubroutine L K s1 else s1).role = s.role := by
          intro s1 hr1
          by_cases h1 : s1.role = Role.clock
          · rw [if_pos h1, stdCounterSubroutine_clock_role_eq L K _ h1]; rw [hr1] at h1; exact h1.symm
          · rw [if_neg h1]; exact hr1
        by_cases hb1 : s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero
        · rw [if_pos hb1]
          by_cases hg : s.hour.val = L
          · rw [if_pos hg]; exact hstep _ rfl
          · rw [if_neg hg]; exact hstep _ rfl
        · rw [if_neg hb1]
          by_cases hb2 : t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero
          · rw [if_pos hb2]
            by_cases hg2 : t.hour.val = L
            · rw [if_pos hg2]; exact hstep _ rfl
            · rw [if_neg hg2]; exact hstep _ rfl
          · rw [if_neg hb2]; exact hstep _ rfl
      rw [hrole_out] at hclk; exact hsc hclk
  · exact hr

/-- **Staticity of `role` (second output).** -/
theorem Phase5Transition_snd_role_eq (s t : AgentState L K) (_ht : t.phase.val = 5) :
    (Phase5Transition L K s t).2.role = t.role := by
  rcases Phase5Transition_snd_role_hour (L := L) (K := K) s t with hclk | ⟨hr, _⟩
  · by_cases htc : t.role = Role.clock
    · rw [hclk, htc]
    · exfalso
      have hrole_out : (Phase5Transition L K s t).2.role = t.role := by
        unfold Phase5Transition; simp only
        have hstep : ∀ t1 : AgentState L K, t1.role = t.role →
            (if t1.role = Role.clock then stdCounterSubroutine L K t1 else t1).role = t.role := by
          intro t1 hr1
          by_cases h1 : t1.role = Role.clock
          · rw [if_pos h1, stdCounterSubroutine_clock_role_eq L K _ h1]; rw [hr1] at h1; exact h1.symm
          · rw [if_neg h1]; exact hr1
        by_cases hb1 : s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero
        · rw [if_pos hb1]
          by_cases hg : s.hour.val = L
          · rw [if_pos hg]; exact hstep _ rfl
          · rw [if_neg hg]; exact hstep _ rfl
        · rw [if_neg hb1]
          by_cases hb2 : t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero
          · rw [if_pos hb2]
            by_cases hg2 : t.hour.val = L
            · rw [if_pos hg2]; exact hstep _ rfl
            · rw [if_neg hg2]; exact hstep _ rfl
          · rw [if_neg hb2]; exact hstep _ rfl
      rw [hrole_out] at hclk; exact htc hclk
  · exact hr

/-! ## Part C — the class counts and the conserved biased-Main class profile.

`biasedMainClass σ i a` flags a Main with dyadic bias `σ·2^{−i}` (exponent index `i`); its
count `biasedMainClassU σ i` is the **static** profile that the Reserves sample against.
`sampledReserveClass i a` flags a Reserve whose recorded sample is exponent index `i`
(`hour.val = i`); its count `sampledReserveClassU i` is the quantity the concentration
controls.  The former is `(role, bias)`-only and conserved per Phase-5 step by staticity. -/

/-- A Main with dyadic bias of sign `σ`, exponent index `i` (paper exponent `−i`). -/
def biasedMainClass (σ : Sign) (i : Fin (L + 1)) (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ a.bias = Bias.dyadic σ i

instance (σ : Sign) (i : Fin (L + 1)) (a : AgentState L K) :
    Decidable (biasedMainClass σ i a) := by unfold biasedMainClass; infer_instance

/-- The (static) count of biased Mains in class `(σ, i)`. -/
def biasedMainClassU (σ : Sign) (i : Fin (L + 1)) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => biasedMainClass σ i a) c

/-- A Reserve whose recorded sample is exponent index `i` (`sample = hour = i`). -/
def sampledReserveClass (i : Fin (L + 1)) (a : AgentState L K) : Prop :=
  a.role = Role.reserve ∧ a.hour.val = i.val

instance (i : Fin (L + 1)) (a : AgentState L K) :
    Decidable (sampledReserveClass i a) := by unfold sampledReserveClass; infer_instance

/-- The count of Reserves that sampled class `i`. -/
def sampledReserveClassU (i : Fin (L + 1)) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => sampledReserveClass i a) c

/-- `countP biasedMainClass` over a two-element pair as a sum of indicators. -/
theorem countP_biasedMainClass_pair (σ : Sign) (i : Fin (L + 1)) (x y : AgentState L K) :
    Multiset.countP (fun a => biasedMainClass σ i a) ({x, y} : Multiset (AgentState L K))
      = (if biasedMainClass σ i x then 1 else 0) + (if biasedMainClass σ i y then 1 else 0) := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]; ring

/-- **`biasedMainClass` is preserved both ways by `Phase5Transition` (left output).**  By
`(role, bias)`-staticity the first output is `biasedMainClass σ i` iff `s` is. -/
theorem biasedMainClass_fst_iff (σ : Sign) (i : Fin (L + 1)) (s t : AgentState L K)
    (hs : s.phase.val = 5) :
    biasedMainClass σ i (Phase5Transition L K s t).1 ↔ biasedMainClass σ i s := by
  unfold biasedMainClass
  rw [Phase5Transition_fst_role_eq (L := L) (K := K) s t hs,
      Phase5Transition_fst_bias_eq (L := L) (K := K) s t hs]

/-- **`biasedMainClass` preserved both ways (second output).** -/
theorem biasedMainClass_snd_iff (σ : Sign) (i : Fin (L + 1)) (s t : AgentState L K)
    (ht : t.phase.val = 5) :
    biasedMainClass σ i (Phase5Transition L K s t).2 ↔ biasedMainClass σ i t := by
  unfold biasedMainClass
  rw [Phase5Transition_snd_role_eq (L := L) (K := K) s t ht,
      Phase5Transition_snd_bias_eq (L := L) (K := K) s t ht]

/-- **Per-pair conservation of `biasedMainClassU`** under a phase-5 `Phase5Transition`. -/
theorem Phase5Transition_biasedMainClass_pair_eq (σ : Sign) (i : Fin (L + 1))
    (s t : AgentState L K) (hs : s.phase.val = 5) (ht : t.phase.val = 5) :
    Multiset.countP (fun a => biasedMainClass σ i a)
        ({(Phase5Transition L K s t).1, (Phase5Transition L K s t).2}
          : Multiset (AgentState L K))
      = Multiset.countP (fun a => biasedMainClass σ i a)
          ({s, t} : Multiset (AgentState L K)) := by
  classical
  rw [countP_biasedMainClass_pair, countP_biasedMainClass_pair]
  rw [if_congr (biasedMainClass_fst_iff (L := L) (K := K) σ i s t hs) rfl rfl,
      if_congr (biasedMainClass_snd_iff (L := L) (K := K) σ i s t ht) rfl rfl]

/-! ## Part D — the static profile is a kernel invariant, plus the assembled instance. -/

private theorem mem_of_app_left5' {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right5' {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-- **`biasedMainClassU σ i` is conserved by any chosen-pair update on the all-phase-5
window** (the static profile).  An applicable pair are both phase-5 agents, so `Transition`
reduces to `Phase5Transition`, whose per-pair class count is conserved. -/
theorem biasedMainClassU_stepOrSelf_eq (σ : Sign) (i : Fin (L + 1)) (n : ℕ)
    (c : Config (AgentState L K)) (hInv : Phase5AllWin n c) (r₁ r₂ : AgentState L K) :
    biasedMainClassU (L := L) (K := K) σ i
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      = biasedMainClassU (L := L) (K := K) σ i c := by
  obtain ⟨_, hph⟩ := hInv
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have h15 : r₁.phase.val = 5 := hph r₁ (mem_of_app_left5' happ)
    have h25 : r₂.phase.val = 5 := hph r₂ (mem_of_app_right5' happ)
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    unfold biasedMainClassU
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    rw [Transition_eq_Phase5Transition_of_phase5 (L := L) (K := K) r₁ r₂ h15 h25]
    rw [Phase5Transition_biasedMainClass_pair_eq (L := L) (K := K) σ i r₁ r₂ h15 h25]
    have hpair_le : Multiset.countP (fun a => biasedMainClass σ i a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => biasedMainClass σ i a) c :=
      Multiset.countP_le_of_le _ hsub
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- The kernel-support version: the static biased-Main class profile is unchanged by any
single kernel step from a phase-5-window config. -/
theorem biasedMainClassU_support_eq (σ : Sign) (i : Fin (L + 1)) (n : ℕ)
    (c c' : Config (AgentState L K)) (hInv : Phase5AllWin n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    biasedMainClassU (L := L) (K := K) σ i c' = biasedMainClassU (L := L) (K := K) σ i c := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]; exact biasedMainClassU_stepOrSelf_eq σ i n c hInv r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'; rfl

/-! ## Part D' — the drain rectangle: per-step drop of `unsampledReserveU`.

The eliminator pool is the **useful biased Mains** — Mains with exponent index `< L`
(`biasedMainLtL`).  When an unsampled Reserve `r` (`hour = L`) meets such a Main `m`
(`bias = .dyadic σ i`, `i.val < L`), `Phase5Transition` writes `r.hour := i < L`, so `r`
leaves the unsampled pool: `unsampledReserveU` drops by 1.  The rectangle
`unsampledReserves × biasedMainLtL` (ordered Reserve-first, matching the drop convention)
feeds the shared `Phase7Convergence.drop_prob_of_rect` engine, yielding the per-step
drop-probability floor `(#unsampled · #usefulMains)/(n(n−1))`. -/

/-- The **useful eliminator** Mains: a Main with dyadic bias of index `i.val < L`.  Sampling
against such a Main lands the Reserve at index `< L`, strictly draining the unsampled pool. -/
def biasedMainLtL (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ ∃ (σ : Sign) (i : Fin (L + 1)), i.val < L ∧ a.bias = Bias.dyadic σ i

instance (a : AgentState L K) : Decidable (biasedMainLtL a) := by
  unfold biasedMainLtL; infer_instance

/-- **Per-pair drop of `unsampled`-count under `Phase5Transition`.**  An unsampled Reserve `r`
(role `.reserve`, `hour = L`) interacting with a useful biased Main `m` (index `< L`) leaves
exactly zero unsampled agents in the output pair (it was the only unsampled one, and it samples
to index `< L`). -/
theorem Phase5Transition_unsampled_pair_drop (r m : AgentState L K)
    (hr : unsampled r) (hm : biasedMainLtL m) :
    Multiset.countP (fun a => unsampled a)
        ({(Phase5Transition L K r m).1, (Phase5Transition L K r m).2}
          : Multiset (AgentState L K)) + 1
      ≤ Multiset.countP (fun a => unsampled a) ({r, m} : Multiset (AgentState L K)) := by
  classical
  obtain ⟨hrole, hhour⟩ := hr
  obtain ⟨hmrole, σ, i, hiL, hmb⟩ := hm
  -- RHS: r is unsampled, m is a main (not reserve) so not unsampled ⟹ RHS = 1.
  have hm_not : ¬ unsampled m := by
    intro hu; rw [hu.1] at hmrole; exact absurd hmrole (by decide)
  have hrhs : Multiset.countP (fun a => unsampled a) ({r, m} : Multiset (AgentState L K)) = 1 := by
    rw [countP_unsampled_pair, if_pos ⟨hrole, hhour⟩, if_neg hm_not]
  -- LHS outputs: s1 = (doSample r m).1 = {r with hour := i}; output1 not unsampled (hour=i<L).
  -- output2 = m, not unsampled.
  have hbias_ne : m.bias ≠ Bias.zero := by rw [hmb]; exact fun h => by simp at h
  have hguard : r.role = Role.reserve ∧ m.role = Role.main ∧ m.bias ≠ Bias.zero :=
    ⟨hrole, hmrole, hbias_ne⟩
  have hr_nc : ¬ ({ r with hour := exponentOf L m.bias } : AgentState L K).role = Role.clock := by
    show r.role ≠ Role.clock; rw [hrole]; decide
  have hm_not_clock : ¬ m.role = Role.clock := by rw [hmrole]; decide
  have hfire : Phase5Transition L K r m
      = ({ r with hour := exponentOf L m.bias }, m) := by
    unfold Phase5Transition
    simp only [if_pos hguard, if_pos hhour]
    rw [if_neg hr_nc, if_neg hm_not_clock]
  rw [hfire]
  -- output1 = {r with hour := exponentOf m.bias}; exponentOf (dyadic σ i) = i, i.val < L.
  have hexp : exponentOf L m.bias = i := by rw [hmb]; rfl
  have hout1_not : ¬ unsampled ({ r with hour := exponentOf L m.bias } : AgentState L K) := by
    intro hu
    have : (exponentOf L m.bias).val = L := hu.2
    rw [hexp] at this; omega
  rw [countP_unsampled_pair, if_neg hout1_not, if_neg hm_not, hrhs]

/-- **Config-level strict drain of `unsampledReserveU`.**  On a phase-5 window, an applicable
pair `(r, m)` with `r` an unsampled Reserve and `m` a useful biased Main (index `< L`) drops the
global unsampled-Reserve count by one (`Transition` reduces to `Phase5Transition` at phase 5;
the per-pair drop is `Phase5Transition_unsampled_pair_drop`). -/
theorem unsampledReserveU_stepOrSelf_drop (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase5AllWin n c) (r m : AgentState L K)
    (happ : Protocol.Applicable c r m)
    (hr : unsampled r) (hm : biasedMainLtL m) :
    unsampledReserveU (L := L) (K := K)
        (Protocol.stepOrSelf (NonuniformMajority L K) c r m) + 1
      ≤ unsampledReserveU (L := L) (K := K) c := by
  obtain ⟨_, hph⟩ := hInv
  have h15 : r.phase.val = 5 := hph r (mem_of_app_left5' happ)
  have h25 : m.phase.val = 5 := hph m (mem_of_app_right5' happ)
  have hsub : ({r, m} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r m
      = c - {r, m} + {(Transition L K r m).1, (Transition L K r m).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  unfold unsampledReserveU
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  rw [Transition_eq_Phase5Transition_of_phase5 (L := L) (K := K) r m h15 h25]
  have hdrop := Phase5Transition_unsampled_pair_drop (L := L) (K := K) r m hr hm
  have hpair_le : Multiset.countP (fun a => unsampled a)
      ({r, m} : Multiset (AgentState L K))
        ≤ Multiset.countP (fun a => unsampled a) c := Multiset.countP_le_of_le _ hsub
  omega

/-! ### The drain rectangle: `unsampledReserves × biasedMainLtL`. -/

/-- The unsampled-Reserve states (target pool). -/
def unsampledReserves : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => unsampled a)

/-- The useful biased-Main states (eliminator pool, index `< L`). -/
def usefulMains : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => biasedMainLtL a)

/-- For two state-finsets of pairwise-distinct states, the `interactionCount` mass of `A ×ˢ B`
is `(∑_A count)·(∑_B count)`.  Local copy of the Phase-7 engine helper (its olean cannot be
imported single-file; the lemma is self-contained). -/
theorem sum_interactionCount_cross_disjoint5
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

/-- **The generic drop-rectangle probability bound** (Φ-agnostic).  Local copy of the Phase-7
shared engine `drop_prob_of_rect` (its olean is stale relative to source, so it cannot be
imported under the single-file compile constraint; the proof is self-contained). -/
theorem drop_prob_of_rect5 (Φ : Config (AgentState L K) → ℕ) (n : ℕ) (hn : 2 ≤ n)
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

/-- For two state-finsets of pairwise-distinct states an applicable pair exists.  Local copy of
the protocol-engine helper (the Phase-7 one is `private`). -/
theorem applicable_of_mem_distinct5 {c : Config (AgentState L K)}
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

/-- An unsampled Reserve and a useful biased Main are distinct (role `.reserve` vs `.main`). -/
theorem unsampledReserves_usefulMains_disjoint
    (a : AgentState L K) (ha : a ∈ unsampledReserves (L := L) (K := K))
    (b : AgentState L K) (hb : b ∈ usefulMains (L := L) (K := K)) : a ≠ b := by
  simp only [unsampledReserves, usefulMains, Finset.mem_filter, unsampled, biasedMainLtL] at ha hb
  intro heq; subst heq
  rw [ha.2.1] at hb
  exact absurd hb.2.1 (by decide)

/-- **The drain-rectangle drop-probability floor** (Phase 5).  On a phase-5 window, the one-step
probability of dropping `unsampledReserveU` is at least
`(#unsampledReserves · #usefulMains)/(n(n−1))`.  Instantiates the shared
`Phase7Convergence.drop_prob_of_rect` with `Φ = unsampledReserveU` and the Reserve-first
rectangle. -/
theorem unsampledReserveU_drop_prob_rect5 (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : Phase5AllWin n c) :
    ENNReal.ofReal
        (((unsampledReserves (L := L) (K := K)).sum c.count *
          (usefulMains (L := L) (K := K)).sum c.count : ℕ) /
          ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | unsampledReserveU (L := L) (K := K) c' + 1
          ≤ unsampledReserveU (L := L) (K := K) c} := by
  have hcardn : c.card = n := hInv.1
  refine drop_prob_of_rect5 (fun c => unsampledReserveU (L := L) (K := K) c)
    n hn c hcardn
    ((unsampledReserves (L := L) (K := K)) ×ˢ (usefulMains (L := L) (K := K)))
    _ ?_ (le_of_eq ?_)
  · rintro ⟨r, m⟩ hp hcr hcm _
    rw [Finset.mem_product] at hp
    obtain ⟨hrmem, hmmem⟩ := hp
    simp only [unsampledReserves, Finset.mem_filter] at hrmem
    simp only [usefulMains, Finset.mem_filter] at hmmem
    have hrm : r ∈ c := Multiset.one_le_count_iff_mem.mp hcr
    have hmm : m ∈ c := Multiset.one_le_count_iff_mem.mp hcm
    have hne : r ≠ m :=
      unsampledReserves_usefulMains_disjoint r
        (by simp only [unsampledReserves, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hrmem.2⟩)
        m (by simp only [usefulMains, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hmmem.2⟩)
    have happ : Protocol.Applicable c r m :=
      applicable_of_mem_distinct5 hrm hmm hne
    exact unsampledReserveU_stepOrSelf_drop n c hInv r m happ hrmem.2 hmmem.2
  · rw [sum_interactionCount_cross_disjoint5 c _ _
        unsampledReserves_usefulMains_disjoint]

/-! ## Part D'' — the sampled-class RISE rectangle and the in-house lower-MGF drift.

The quantity the Chernoff side controls is `sampledReserveClassU i` — the count of Reserves
whose recorded sample is exponent index `i`.  When an unsampled Reserve `r` (`hour = L`) meets a
class-`i` biased Main `m` (`bias = .dyadic σ i`, `i.val < L`), `r` samples `i`, so
`sampledReserveClassU i` RISES by one.  The rise rectangle `unsampledReserves × classMains i`
feeds a `rise`-probability floor; the in-house exponential-MGF on the deficit potential
`exp(−s·sampledReserveClassU i)` then contracts via `EarlyDripMarked.mgf_one_step_lower` (the
monotone-counter lower MGF), i.e. the genuinely-probabilistic drift. -/

/-- `countP sampledReserveClass` over a two-element pair as a sum of indicators. -/
theorem countP_sampledReserveClass_pair (i : Fin (L + 1)) (x y : AgentState L K) :
    Multiset.countP (fun a => sampledReserveClass i a) ({x, y} : Multiset (AgentState L K))
      = (if sampledReserveClass i x then 1 else 0)
        + (if sampledReserveClass i y then 1 else 0) := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]; ring

/-- The class-`i` biased Mains (sampling against one lands a Reserve in class `i`). -/
def classMains (σ : Sign) (i : Fin (L + 1)) (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ a.bias = Bias.dyadic σ i

instance (σ : Sign) (i : Fin (L + 1)) (a : AgentState L K) :
    Decidable (classMains σ i a) := by unfold classMains; infer_instance

/-- **Per-pair RISE of `sampledReserveClass i` under `Phase5Transition`.**  An unsampled Reserve
`r` meeting a class-`i` biased Main `m` (index `i.val < L`) leaves the pair with exactly one
class-`i` Reserve (the freshly-sampled `r`), up from zero. -/
theorem Phase5Transition_sampledClass_pair_rise (σ : Sign) (i : Fin (L + 1)) (hiL : i.val < L)
    (r m : AgentState L K) (hr : unsampled r) (hm : classMains σ i m) :
    Multiset.countP (fun a => sampledReserveClass i a) ({r, m} : Multiset (AgentState L K)) + 1
      ≤ Multiset.countP (fun a => sampledReserveClass i a)
          ({(Phase5Transition L K r m).1, (Phase5Transition L K r m).2}
            : Multiset (AgentState L K)) := by
  classical
  obtain ⟨hrole, hhour⟩ := hr
  obtain ⟨hmrole, hmb⟩ := hm
  -- RHS-before pair (input): r not class i (hour=L≠i<L), m not reserve ⟹ count 0.
  have hr_not : ¬ sampledReserveClass i r := by
    intro hu; have : r.hour.val = i.val := hu.2; rw [hhour] at this; omega
  have hm_not : ¬ sampledReserveClass i m := by
    intro hu; rw [hu.1] at hmrole; exact absurd hmrole (by decide)
  have hlhs : Multiset.countP (fun a => sampledReserveClass i a)
      ({r, m} : Multiset (AgentState L K)) = 0 := by
    rw [countP_sampledReserveClass_pair, if_neg hr_not, if_neg hm_not]
  -- the firing form.
  have hbias_ne : m.bias ≠ Bias.zero := by rw [hmb]; exact fun h => by simp at h
  have hguard : r.role = Role.reserve ∧ m.role = Role.main ∧ m.bias ≠ Bias.zero :=
    ⟨hrole, hmrole, hbias_ne⟩
  have hr_nc : ¬ ({ r with hour := exponentOf L m.bias } : AgentState L K).role = Role.clock := by
    show r.role ≠ Role.clock; rw [hrole]; decide
  have hm_not_clock : ¬ m.role = Role.clock := by rw [hmrole]; decide
  have hfire : Phase5Transition L K r m
      = ({ r with hour := exponentOf L m.bias }, m) := by
    unfold Phase5Transition
    simp only [if_pos hguard, if_pos hhour]
    rw [if_neg hr_nc, if_neg hm_not_clock]
  rw [hfire, hlhs]
  have hexp : exponentOf L m.bias = i := by rw [hmb]; rfl
  -- output1 = {r with hour := i} IS class i; output2 = m not class i.
  have hout1 : sampledReserveClass i ({ r with hour := exponentOf L m.bias } : AgentState L K) := by
    refine ⟨hrole, ?_⟩; rw [hexp]
  rw [countP_sampledReserveClass_pair, if_pos hout1, if_neg hm_not]

/-- For a Reserve with `hour ≠ L`, the first `Phase5Transition` output keeps its `hour` (the
sampling branch fires only on `hour = L`; a Reserve is never a clock). -/
theorem Phase5Transition_fst_hour_eq_of_reserve_ne_L (s t : AgentState L K)
    (hrole : s.role = Role.reserve) (hne : s.hour.val ≠ L) :
    (Phase5Transition L K s t).1.hour = s.hour := by
  have hr_nc : ¬ s.role = Role.clock := by rw [hrole]; decide
  unfold Phase5Transition
  simp only
  by_cases hb1 : s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero
  · rw [if_pos hb1, if_neg hne]
    rw [if_neg hr_nc]
  · rw [if_neg hb1]
    by_cases hb2 : t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero
    · -- s.role = main contradicts hrole = reserve.
      exact absurd hb2.2.1 (by rw [hrole]; decide)
    · rw [if_neg hb2, if_neg hr_nc]

/-- Symmetric: a Reserve `t` with `hour ≠ L` keeps its `hour` in the second output. -/
theorem Phase5Transition_snd_hour_eq_of_reserve_ne_L (s t : AgentState L K)
    (hrole : t.role = Role.reserve) (hne : t.hour.val ≠ L) :
    (Phase5Transition L K s t).2.hour = t.hour := by
  have ht_nc : ¬ t.role = Role.clock := by rw [hrole]; decide
  unfold Phase5Transition
  simp only
  by_cases hb1 : s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero
  · exact absurd hb1.2.1 (by rw [hrole]; decide)
  · rw [if_neg hb1]
    by_cases hb2 : t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero
    · rw [if_pos hb2, if_neg hne, if_neg ht_nc]
    · rw [if_neg hb2, if_neg ht_nc]

/-- **Per-pair NON-DECREASE of `sampledReserveClass i` under `Phase5Transition`.**  A class-`i`
Reserve (`hour = i ≠ L`) is frozen by the sampling rule (the guard fires only on `hour = L`),
so the pair's class-`i` count never drops.  Forward-stability: a class-`i` input maps to a
class-`i` output. -/
theorem Phase5Transition_sampledClass_pair_ge (i : Fin (L + 1)) (hiL : i.val < L)
    (s t : AgentState L K) (hs : s.phase.val = 5) (ht : t.phase.val = 5) :
    Multiset.countP (fun a => sampledReserveClass i a) ({s, t} : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => sampledReserveClass i a)
          ({(Phase5Transition L K s t).1, (Phase5Transition L K s t).2}
            : Multiset (AgentState L K)) := by
  classical
  rw [countP_sampledReserveClass_pair, countP_sampledReserveClass_pair]
  have hfwd1 : sampledReserveClass i s → sampledReserveClass i (Phase5Transition L K s t).1 := by
    intro hsi
    have hrole : (Phase5Transition L K s t).1.role = s.role :=
      Phase5Transition_fst_role_eq (L := L) (K := K) s t hs
    have hne : s.hour.val ≠ L := by rw [hsi.2]; omega
    have hhour : (Phase5Transition L K s t).1.hour = s.hour :=
      Phase5Transition_fst_hour_eq_of_reserve_ne_L (L := L) (K := K) s t hsi.1 hne
    exact ⟨by rw [hrole]; exact hsi.1, by rw [hhour]; exact hsi.2⟩
  have hfwd2 : sampledReserveClass i t → sampledReserveClass i (Phase5Transition L K s t).2 := by
    intro hti
    have hrole : (Phase5Transition L K s t).2.role = t.role :=
      Phase5Transition_snd_role_eq (L := L) (K := K) s t ht
    have hne : t.hour.val ≠ L := by rw [hti.2]; omega
    have hhour : (Phase5Transition L K s t).2.hour = t.hour :=
      Phase5Transition_snd_hour_eq_of_reserve_ne_L (L := L) (K := K) s t hti.1 hne
    exact ⟨by rw [hrole]; exact hti.1, by rw [hhour]; exact hti.2⟩
  gcongr
  · by_cases h : sampledReserveClass i s
    · rw [if_pos h, if_pos (hfwd1 h)]
    · rw [if_neg h]; positivity
  · by_cases h : sampledReserveClass i t
    · rw [if_pos h, if_pos (hfwd2 h)]
    · rw [if_neg h]; positivity

/-! ### Config-level monotonicity, rise rectangle, and the one-step lower MGF. -/

/-- **`sampledReserveClassU i` is monotone NON-DECREASING per kernel step** on the phase-5
window (`hmono` for the lower MGF).  Applicable pairs are phase-5; the per-pair non-decrease is
`Phase5Transition_sampledClass_pair_ge`. -/
theorem sampledReserveClassU_stepOrSelf_ge (i : Fin (L + 1)) (hiL : i.val < L) (n : ℕ)
    (c : Config (AgentState L K)) (hInv : Phase5AllWin n c) (r₁ r₂ : AgentState L K) :
    sampledReserveClassU (L := L) (K := K) i c
      ≤ sampledReserveClassU (L := L) (K := K) i
          (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  obtain ⟨_, hph⟩ := hInv
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have h15 : r₁.phase.val = 5 := hph r₁ (mem_of_app_left5' happ)
    have h25 : r₂.phase.val = 5 := hph r₂ (mem_of_app_right5' happ)
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    unfold sampledReserveClassU
    rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
    rw [Transition_eq_Phase5Transition_of_phase5 (L := L) (K := K) r₁ r₂ h15 h25]
    have hge := Phase5Transition_sampledClass_pair_ge (L := L) (K := K) i hiL r₁ r₂ h15 h25
    -- countP over c = countP over (c - pair) + countP over pair (since pair ≤ c).
    have hsplit : Multiset.countP (fun a => sampledReserveClass i a) c
        = Multiset.countP (fun a => sampledReserveClass i a) (c - {r₁, r₂})
          + Multiset.countP (fun a => sampledReserveClass i a) ({r₁, r₂}
              : Multiset (AgentState L K)) := by
      rw [← Multiset.countP_add, Multiset.sub_add_cancel hsub]
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- **Config-level RISE of `sampledReserveClassU i`.**  On the phase-5 window, an applicable
pair `(r, m)` with `r` an unsampled Reserve and `m` a class-`i` biased Main (index `< L`) raises
the global class-`i` count by one. -/
theorem sampledReserveClassU_stepOrSelf_rise (σ : Sign) (i : Fin (L + 1)) (hiL : i.val < L)
    (n : ℕ) (c : Config (AgentState L K)) (hInv : Phase5AllWin n c) (r m : AgentState L K)
    (happ : Protocol.Applicable c r m) (hr : unsampled r) (hm : classMains σ i m) :
    sampledReserveClassU (L := L) (K := K) i c + 1
      ≤ sampledReserveClassU (L := L) (K := K) i
          (Protocol.stepOrSelf (NonuniformMajority L K) c r m) := by
  obtain ⟨_, hph⟩ := hInv
  have h15 : r.phase.val = 5 := hph r (mem_of_app_left5' happ)
  have h25 : m.phase.val = 5 := hph m (mem_of_app_right5' happ)
  have hsub : ({r, m} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r m
      = c - {r, m} + {(Transition L K r m).1, (Transition L K r m).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  unfold sampledReserveClassU
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  rw [Transition_eq_Phase5Transition_of_phase5 (L := L) (K := K) r m h15 h25]
  have hrise := Phase5Transition_sampledClass_pair_rise (L := L) (K := K) σ i hiL r m hr hm
  have hsplit : Multiset.countP (fun a => sampledReserveClass i a) c
      = Multiset.countP (fun a => sampledReserveClass i a) (c - {r, m})
        + Multiset.countP (fun a => sampledReserveClass i a) ({r, m}
            : Multiset (AgentState L K)) := by
    rw [← Multiset.countP_add, Multiset.sub_add_cancel hsub]
  omega

/-- **The generic RISE-rectangle probability bound** (mirror of `drop_prob_of_rect5` with the
rise event `{c' | Φ c + 1 ≤ Φ c'}`).  Each rectangle cell raises `Φ` by `≥ 1`. -/
theorem rise_prob_of_rect5 (Φ : Config (AgentState L K) → ℕ) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hcardn : c.card = n)
    (R : Finset (AgentState L K × AgentState L K)) (N : ℕ)
    (hrise : ∀ p ∈ R, 1 ≤ c.count p.1 → 1 ≤ c.count p.2 → (p.1 = p.2 → 2 ≤ c.count p.1) →
      Φ c + 1 ≤ Φ (Protocol.stepOrSelf (NonuniformMajority L K) c p.1 p.2))
    (hcount : (N : ℕ) ≤ ∑ p ∈ R, c.interactionCount p.1 p.2) :
    ENNReal.ofReal ((N : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Φ c + 1 ≤ Φ c'} := by
  set j := Φ c with hjdef
  have hcard2 : 2 ≤ c.card := by rw [hcardn]; omega
  have hmeas : MeasurableSet {c' : Config (AgentState L K) | j + 1 ≤ Φ c'} :=
    DiscreteMeasurableSpace.forall_measurableSet _
  set S : Finset (AgentState L K × AgentState L K) :=
    R.filter (fun p => 1 ≤ c.count p.1 ∧ 1 ≤ c.count p.2 ∧ (p.1 = p.2 → 2 ≤ c.count p.1)) with hS
  have hsub : (↑S : Set (AgentState L K × AgentState L K)) ⊆
      (Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹' {c' | j + 1 ≤ Φ c'} := by
    intro p hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hS] at hp
    obtain ⟨hpc, hp1, hp2, hp3⟩ := hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Protocol.scheduledStep]
    exact hrise p hpc hp1 hp2 hp3
  have hstepDist : (NonuniformMajority L K).stepDistOrSelf c
      = (NonuniformMajority L K).stepDist c hcard2 := by
    unfold Protocol.stepDistOrSelf; rw [dif_pos hcard2]
  have hbase : ((NonuniformMajority L K).stepDistOrSelf c).toMeasure {c' | j + 1 ≤ Φ c'}
      = (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹' {c' | j + 1 ≤ Φ c'}) := by
    rw [hstepDist]; unfold Protocol.stepDist
    rw [PMF.toMeasure_map_apply _ _ _ (Measurable.of_discrete) hmeas]
  rw [hbase]
  have hmono : (c.interactionPMF hcard2).toMeasure (↑S : Set _)
      ≤ (c.interactionPMF hcard2).toMeasure
          ((Protocol.scheduledStep (NonuniformMajority L K) c) ⁻¹' {c' | j + 1 ≤ Φ c'}) :=
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
          rw [if_pos hpe]; have hc1 : c.count p.1 = 1 := by omega
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
      c.interactionProb p.1 p.2 = (↑(c.interactionCount p.1 p.2) : ℝ≥0∞) * (↑c.totalPairs)⁻¹ := by
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

/-- The class-`i` biased-Main states (sign `σ`). -/
def classMainStates (σ : Sign) (i : Fin (L + 1)) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => classMains σ i a)

/-- An unsampled Reserve and a class-`i` Main are distinct (role differs). -/
theorem unsampledReserves_classMainStates_disjoint (σ : Sign) (i : Fin (L + 1))
    (a : AgentState L K) (ha : a ∈ unsampledReserves (L := L) (K := K))
    (b : AgentState L K) (hb : b ∈ classMainStates (L := L) (K := K) σ i) : a ≠ b := by
  simp only [unsampledReserves, classMainStates, Finset.mem_filter, unsampled, classMains]
    at ha hb
  intro heq; subst heq
  rw [ha.2.1] at hb; exact absurd hb.2.1 (by decide)

/-- **The class-`i` rise-rectangle probability floor** (Phase 5).  On a phase-5 window the
one-step probability that `sampledReserveClassU i` rises is at least
`(#unsampledReserves · #classMains_σi)/(n(n−1))` — the per-step conditional class-`i` sampling
mass that the in-house lower-MGF consumes. -/
theorem sampledReserveClassU_rise_prob_rect5 (σ : Sign) (i : Fin (L + 1)) (hiL : i.val < L)
    (n : ℕ) (hn : 2 ≤ n) (c : Config (AgentState L K)) (hInv : Phase5AllWin n c) :
    ENNReal.ofReal
        (((unsampledReserves (L := L) (K := K)).sum c.count *
          (classMainStates (L := L) (K := K) σ i).sum c.count : ℕ) /
          ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | sampledReserveClassU (L := L) (K := K) i c + 1
          ≤ sampledReserveClassU (L := L) (K := K) i c'} := by
  have hcardn : c.card = n := hInv.1
  refine rise_prob_of_rect5 (fun c => sampledReserveClassU (L := L) (K := K) i c) n hn c hcardn
    ((unsampledReserves (L := L) (K := K)) ×ˢ (classMainStates (L := L) (K := K) σ i))
    _ ?_ (le_of_eq ?_)
  · rintro ⟨r, m⟩ hp hcr hcm _
    rw [Finset.mem_product] at hp
    obtain ⟨hrmem, hmmem⟩ := hp
    simp only [unsampledReserves, Finset.mem_filter] at hrmem
    simp only [classMainStates, Finset.mem_filter] at hmmem
    have hrm : r ∈ c := Multiset.one_le_count_iff_mem.mp hcr
    have hmm : m ∈ c := Multiset.one_le_count_iff_mem.mp hcm
    have hne : r ≠ m :=
      unsampledReserves_classMainStates_disjoint σ i r
        (by simp only [unsampledReserves, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hrmem.2⟩)
        m (by simp only [classMainStates, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hmmem.2⟩)
    have happ : Protocol.Applicable c r m := applicable_of_mem_distinct5 hrm hmm hne
    exact sampledReserveClassU_stepOrSelf_rise σ i hiL n c hInv r m happ hrmem.2 hmmem.2
  · rw [sum_interactionCount_cross_disjoint5 c _ _
        (unsampledReserves_classMainStates_disjoint σ i)]

/-- **Support monotonicity**: every one-step successor of a phase-5-window state has
`sampledReserveClassU i` at least its current value. -/
theorem sampledReserveClassU_support_ge (i : Fin (L + 1)) (hiL : i.val < L) (n : ℕ)
    (c c' : Config (AgentState L K)) (hInv : Phase5AllWin n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    sampledReserveClassU (L := L) (K := K) i c
      ≤ sampledReserveClassU (L := L) (K := K) i c' := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]; exact sampledReserveClassU_stepOrSelf_ge i hiL n c hInv r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'; exact le_refl _

/-- **The in-house one-step lower-MGF contraction** for the sampled-class deficit potential
`Φ(c) = exp(−s · sampledReserveClassU i c)`.  On a phase-5 window, the counter is monotone
(support monotonicity) and rises with probability at least the rise-rectangle floor `r`, so
`EarlyDripMarked.mgf_one_step_lower` gives the contraction
`∫ exp(−s·N) dK(c) ≤ (1 − r(1−e^{−s}))·exp(−s·N(c))` — the genuinely-probabilistic drift. -/
theorem sampledClass_lower_mgf_drift (σ : Sign) (i : Fin (L + 1)) (hiL : i.val < L)
    (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (c : Config (AgentState L K)) (hInv : Phase5AllWin n c)
    (hrfloor : ENNReal.ofReal r ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | sampledReserveClassU (L := L) (K := K) i c + 1
          ≤ sampledReserveClassU (L := L) (K := K) i c'}) :
    ∫⁻ c', ENNReal.ofReal
        (Real.exp (-(s * (sampledReserveClassU (L := L) (K := K) i c' : ℝ))))
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ ENNReal.ofReal ((1 - r * (1 - Real.exp (-s)))
          * Real.exp (-(s * (sampledReserveClassU (L := L) (K := K) i c : ℝ)))) := by
  set μ := ((NonuniformMajority L K).stepDistOrSelf c).toMeasure with hμ
  haveI hprob : IsProbabilityMeasure μ := by
    rw [hμ]
    exact (inferInstance :
      IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure c
  have hKμ : (NonuniformMajority L K).transitionKernel c = μ := rfl
  set N := fun c' => sampledReserveClassU (L := L) (K := K) i c' with hN
  set n₀ := sampledReserveClassU (L := L) (K := K) i c with hn0
  -- a.e. monotonicity: support points have N ≥ n₀.
  have hmono : ∀ᵐ y ∂μ, n₀ ≤ N y := by
    rw [hμ, ae_iff]
    rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
    rw [Set.disjoint_left]
    intro x hsupp hx
    simp only [Set.mem_setOf_eq, hN, hn0] at hx
    exact hx (sampledReserveClassU_support_ge i hiL n c x hInv hsupp)
  -- rise floor: μ {n₀ < N} ≥ ofReal r (the rise event = {n₀ + 1 ≤ N}).
  have hprob_rise : ENNReal.ofReal r ≤ μ {y | n₀ < N y} := by
    have hset : {y : Config (AgentState L K) | n₀ < N y}
        = {c' | sampledReserveClassU (L := L) (K := K) i c + 1
            ≤ sampledReserveClassU (L := L) (K := K) i c'} := by
      ext y; simp only [Set.mem_setOf_eq, hN, hn0]; omega
    rw [hset]; exact hrfloor
  have := EarlyDripMarked.mgf_one_step_lower μ s hs N n₀ hmono r hr0 hr1 hprob_rise
  rw [hKμ]; exact this

/-! ### The builder-shaped MGF drift and the campaign assembly note.

The lower-MGF contraction `sampledClass_lower_mgf_drift` rephrases into the
`WindowConcentration.windowDrift_PhaseConvergence` `hdrift` shape `∫ Φ dK(c) ≤ ρ · Φ(c)` with
`Φ(c) = ofReal(exp(−s·sampledReserveClassU i c))` and `ρ = ofReal(1 − r(1 − e^{−s}))`.  We
expose the builder-shaped drift (`sampledClass_windowDrift_contraction`) and the threshold link
to `sampledFloor`; the remaining assembly into `phase5Convergence`'s carried `hConc` requires an
**absorbing** window on which `sampledReserveClassU i` is monotone.  `Phase5AllWin` carries the
monotonicity (proved) but is NOT absorbing (clocks advance), and the genuinely-closed
superwindow `PhaseGE5Win` breaks monotonicity (Phase-6 `doSplit` converts a class-`i` Reserve to
a Main, consuming it).  This is the paper's footnote-11 *separation* (Phase 5 finishes before
Phase 6 begins): the faithful window is "phase 5 ∧ clocks unfired", whose absorption is the
clock-timing ingredient (Lemma 5.2), tracked as the precise campaign gap. -/

/-- **Builder-shaped MGF drift.**  Rephrases `sampledClass_lower_mgf_drift` into the
`windowDrift_PhaseConvergence` `hdrift` contraction `∫ Φ dK(c) ≤ ρ · Φ(c)` for the deficit
potential `Φ(c) = ofReal(exp(−s·sampledReserveClassU i c))`. -/
theorem sampledClass_windowDrift_contraction (σ : Sign) (i : Fin (L + 1)) (hiL : i.val < L)
    (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 ≤ s) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (c : Config (AgentState L K)) (hInv : Phase5AllWin n c)
    (hrfloor : ENNReal.ofReal r ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | sampledReserveClassU (L := L) (K := K) i c + 1
          ≤ sampledReserveClassU (L := L) (K := K) i c'}) :
    ∫⁻ c', ENNReal.ofReal
        (Real.exp (-(s * (sampledReserveClassU (L := L) (K := K) i c' : ℝ))))
        ∂((NonuniformMajority L K).transitionKernel c)
      ≤ ENNReal.ofReal (1 - r * (1 - Real.exp (-s)))
          * ENNReal.ofReal
              (Real.exp (-(s * (sampledReserveClassU (L := L) (K := K) i c : ℝ)))) := by
  refine le_trans (sampledClass_lower_mgf_drift σ i hiL n hn s hs r hr0 hr1 c hInv hrfloor) ?_
  rw [← ENNReal.ofReal_mul (by
    have h1e : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [Real.exp_pos (-s), mul_nonneg hr0 (by linarith : (0:ℝ) ≤ 1 - Real.exp (-s))])]

/-! ### The Phase-5 post predicate and the assembled `PhaseConvergenceW`.

`ReserveSampleGood i K₀ c` is the honest rendering of the paper's Phase-5 output for Phase 6:
*every Reserve has sampled* (`ReserveSampled`) AND *enough Reserves sampled the useful level*
(`sampledFloor`), the Chernoff floor `R_{−l} ≥ 0.18|R|` resp. `R_{−(l+1)} ≥ 0.58|R|`.  The
level index `i` and required count `K₀` parameterise both case-split branches of Lemma 7.2. -/

/-- The sampled-class floor at level `i`: at least `K₀` Reserves recorded sample `i`. -/
def sampledFloor (i : Fin (L + 1)) (K₀ : ℕ) (c : Config (AgentState L K)) : Prop :=
  K₀ ≤ sampledReserveClassU (L := L) (K := K) i c

/-- **The threshold link.**  Failing the sampled-class floor (`sampledReserveClassU i < K₀`)
forces the deficit potential `Φ` above the threshold `θ = ofReal(exp(−s·K₀))` (since `s ≥ 0` and
`N < K₀` give `exp(−s·N) ≥ exp(−s·K₀)`).  The `hlink` for `windowDrift_PhaseConvergence`. -/
theorem sampledFloor_link (i : Fin (L + 1)) (K₀ : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (c : Config (AgentState L K)) (hfail : ¬ sampledFloor (L := L) (K := K) i K₀ c) :
    ENNReal.ofReal (Real.exp (-(s * (K₀ : ℝ))))
      ≤ ENNReal.ofReal
          (Real.exp (-(s * (sampledReserveClassU (L := L) (K := K) i c : ℝ)))) := by
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  unfold sampledFloor at hfail
  have hlt : sampledReserveClassU (L := L) (K := K) i c < K₀ := by omega
  have hcast : (sampledReserveClassU (L := L) (K := K) i c : ℝ) ≤ (K₀ : ℝ) := by
    exact_mod_cast le_of_lt hlt
  nlinarith [hs, hcast]

/-- **Phase-5 output predicate** (`ReserveSampleGood`): all Reserves sampled, and at least
`K₀` of them at the useful level `i` (the Chernoff floor Phase 6 needs). -/
def ReserveSampleGood (i : Fin (L + 1)) (K₀ : ℕ) (c : Config (AgentState L K)) : Prop :=
  ReserveSampled (L := L) (K := K) c ∧ sampledFloor (L := L) (K := K) i K₀ c

/-- **The assembled Phase-5 `PhaseConvergenceW`** (Lemma 7.1).

`Pre c = Phase5AllWin n c ∧ unsampledReserveU c ≤ M₀`; `Post c = Phase5AllWin n c ∧
ReserveSampleGood i K₀ c`.  Built from the all-sampled engine
(`ReserveSampling.phase5SampledConvergence`) intersected with the sampled-class concentration
event.  The concentration tail `hConc` is the in-house exponential-MGF Chernoff on the
`sampledReserveClassU`-deficit potential against the *static* class profile
(`biasedMainClassU` is conserved by `biasedMainClassU_support_eq`, so the draw distribution is
fixed) — the precise campaign hook for that MGF drift. -/
noncomputable def phase5Convergence (n : ℕ) (i : Fin (L + 1)) (K₀ : ℕ)
    (hClosed : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Phase5AllWin (L := L) (K := K) n c))
    (q : ℝ≥0∞)
    (hstep : ∀ b : Config (AgentState L K), Phase5AllWin (L := L) (K := K) n b →
      1 ≤ unsampledReserveU (L := L) (K := K) b →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potDone (fun c => unsampledReserveU (L := L) (K := K) c))ᶜ ≤ q)
    (M₀ t : ℕ) (ε : ℝ≥0) (hε : (q ^ t : ℝ≥0∞) ≤ (ε : ℝ≥0∞))
    (εConc : ℝ≥0)
    (hConc : ∀ c₀, Phase5AllWin (L := L) (K := K) n c₀ →
      unsampledReserveU (L := L) (K := K) c₀ ≤ M₀ →
      ((NonuniformMajority L K).transitionKernel ^ t) c₀
        {c | ¬ sampledFloor (L := L) (K := K) i K₀ c} ≤ (εConc : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel where
  Pre c := Phase5AllWin (L := L) (K := K) n c ∧ unsampledReserveU (L := L) (K := K) c ≤ M₀
  Post c := Phase5AllWin (L := L) (K := K) n c ∧ ReserveSampleGood (L := L) (K := K) i K₀ c
  t := t
  ε := ε + εConc
  convergence := by
    intro c₀ hPre
    obtain ⟨hwin, hbud⟩ := hPre
    set P5 := phase5SampledConvergence (L := L) (K := K) n hClosed q hstep M₀ t ε hε with hP5
    have hsampled := P5.convergence c₀ ⟨hwin, hbud⟩
    have hcover : {c : Config (AgentState L K) |
        ¬ (Phase5AllWin (L := L) (K := K) n c ∧
            ReserveSampleGood (L := L) (K := K) i K₀ c)}
          ⊆ {c | ¬ P5.Post c} ∪ {c | ¬ sampledFloor (L := L) (K := K) i K₀ c} := by
      intro c hc
      simp only [Set.mem_setOf_eq, Set.mem_union] at hc ⊢
      rw [phase5SampledConvergence_post (L := L) (K := K) n hClosed q hstep M₀ t ε hε]
      by_cases hfloor : sampledFloor (L := L) (K := K) i K₀ c
      · left
        intro hContra
        exact hc ⟨hContra.1, hContra.2, hfloor⟩
      · exact Or.inr hfloor
    calc ((NonuniformMajority L K).transitionKernel ^ t) c₀
            {c | ¬ (Phase5AllWin (L := L) (K := K) n c ∧
              ReserveSampleGood (L := L) (K := K) i K₀ c)}
        ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀
            ({c | ¬ P5.Post c} ∪ {c | ¬ sampledFloor (L := L) (K := K) i K₀ c}) :=
          measure_mono hcover
      _ ≤ ((NonuniformMajority L K).transitionKernel ^ t) c₀ {c | ¬ P5.Post c}
            + ((NonuniformMajority L K).transitionKernel ^ t) c₀
              {c | ¬ sampledFloor (L := L) (K := K) i K₀ c} := measure_union_le _ _
      _ ≤ (ε : ℝ≥0∞) + (εConc : ℝ≥0∞) := by
          gcongr
          · exact hsampled
          · exact hConc c₀ hwin hbud
      _ = ((ε + εConc : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_add]

end Phase5Convergence

end ExactMajority
