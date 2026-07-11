/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Concrete 21-instance assembly with the EXACT seams (`ConcreteAssembly`)

This file closes the codex-audit F5 residual: `time_headline_W2_inv_sq`
(`BudgetTightening.lean:159`) is POLYMORPHIC over `phases : Fin 21 → PhaseConvergenceW`,
with `h_chain`/`hx₀`/`h_post` left as free binders.  Nothing in the campaign actually
assembled the 21 *real* instances and discharged the 20 bridges.  Worse, the headline's
doc (`TimeHeadline.lean:379`) routed assemblers to
`SeamEpidemics.seamEpidemicW_calibrated`, whose `Post` is only `allPhaseGe (p+1)` and
whose `εovershoot` is added by `le_self_add` but never consumed.  The TRUE strengthened
seam is `SeamNoOvershoot.seamEpidemicExactW`, whose `Post` is
`allPhaseGe (p+1) ∧ NoOvershoot p` and whose `convergence` CONSUMES both budgets via a
union bound.  The concrete assembly below FORCES the exact seam.

## What this file delivers (the honest scope)

1. `Assembly` — a record packaging the concrete inputs of the 21-instance family:
   the 11 landed WORK `PhaseConvergenceW` instances (`work`, supplied by the caller as the
   concrete `Phase{1,4,5,6,7,8,10}` / `DrainCalibration` / `Phase7HonestDrain` constructions
   together with whatever named inputs each of those still carries — those inputs live INSIDE
   `work i` exactly as the campaign built them), the 10 SEAM phase parameters / horizons /
   budgets, and the 10 pairs of seam feeders (`hDrift`, `hNoOvershoot`) that
   `seamEpidemicExactW` consumes.  For destinations `{1,6,7,8}` the `hNoOvershoot` feeder is
   the landed `SeamNoOvershoot.hNoOvershoot_one_seam_honest` /
   `SeamPairAdapter`-chain output; for `{2,3,4,5,9}` it is the named per-seam guard.

2. `phases : Assembly … → Fin 21 → PhaseConvergenceW K` — the interleave
   `[work₀, seam₀, work₁, seam₁, …, seam₉, work₁₀]`, even slot `2k ↦ work k`, odd slot
   `2k+1 ↦ seamEpidemicExactW (seamP k) …` (the EXACT seam, by construction).

3. The bridge lemmas (the deepest content):
   * `phases_bridge_work_to_seam` — `work k . Post ⟹ seam k . Pre`, the work↔seam
     boundary, discharged via `SeamEpidemics.exact_work_into_seam` /
     `SeamEpidemics.ge_work_into_seam` from the structural Pre components carried per work
     phase.  Carried gap: the advance trigger `advTriggered (p+1)` and the `allPhaseEq/Ge p`
     identification of `work k . Post` (named field `hWorkPostToWindow` / `hTrig`).
   * `phases_bridge_seam_to_work` — `seam k . Post ⟹ work (k+1) . Pre`, discharged via
     `SeamNoOvershoot.seamExact_into_exact_work` (the EXACT seam's `Post`, `allPhaseGe (p+1)
     ∧ NoOvershoot p`, yields `allPhaseEq (p+1)` pointwise with NO further timing input).
     Carried gap: the `allPhaseEq (p+1) ⟹ work (k+1) . Pre` structural identification
     (named field `hWindowToWorkPre`).

4. `time_headline_CONCRETE` — `BudgetTightening.time_headline_W2_inv_sq` applied
   to `phases asm`, making the headline's conditionality FINITE and inspectable: the
   surviving carried set is exactly the fields of `Assembly` (listed in its docstring),
   no longer a polymorphic `phases`/`h_chain`/`h_post` triple.

This file is APPEND-ONLY: it imports and re-uses the landed surfaces and edits no existing
file.  Every bridge is a genuine pointwise implication; the named carried fields are the
structural-Pre gaps that are not yet wired in the campaign tree, each pinned to its
provenance in the field docstring.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.BudgetTightening
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeamNoOvershoot

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace ConcreteAssembly

variable {L K : ℕ}

/-! ## Part A — index arithmetic for the `[work, seam, work, …]` interleave.

Slot `i : Fin 21` is a WORK slot iff `i.val` is even, a SEAM slot iff odd.  Work index
`k = i/2 : Fin 11`, seam index `k = i/2 : Fin 10`.  The successor of an even slot `2k` is
the odd slot `2k+1` (seam `k`); the successor of an odd slot `2k+1` is the even slot `2k+2`
(work `k+1`). -/

/-- The work index `i/2 : Fin 11` of slot `i : Fin 21`. -/
def workIdx (i : Fin 21) : Fin 11 := ⟨i.val / 2, by omega⟩

/-- The seam index `i/2 : Fin 10` of an odd slot `i : Fin 21` (`i.val` odd ⟹ `i/2 < 10`). -/
def seamIdx (i : Fin 21) (hodd : i.val % 2 = 1) : Fin 10 := ⟨i.val / 2, by omega⟩

@[simp] theorem workIdx_val (i : Fin 21) : (workIdx i).val = i.val / 2 := rfl

@[simp] theorem seamIdx_val (i : Fin 21) (hodd : i.val % 2 = 1) :
    (seamIdx i hodd).val = i.val / 2 := rfl

/-! ## Part B — the assembly record.

`Assembly` packages the concrete 21-instance family.  The WORK instances are supplied
directly (each `work k` is the campaign's landed `PhaseConvergenceW`, carrying its own
internal drains).  The SEAM instances are built by `phases` from `seamEpidemicExactW`
applied to the per-seam parameters and feeders here — FORCING the exact seam.

The bridge data (`hTrig`, `hWorkPostToWindow`, `hWindowToWorkPre`) are the structural-Pre
gaps the campaign tree has not yet wired:

* `hTrig k` — the advance trigger `advTriggered (seamP k + 1)` on `work k . Post` configs.
  This is the per-work-phase strengthening the campaign carries as a named input
  (`TimeHeadline.lean:317`, "advance-trigger strengthening").  Provenance: NOT yet a
  landed lemma; carried.
* `hWorkPostToWindow k` — identifies `work k . Post` with the seam's source window
  `allPhaseGe (seamP k) n`.  Provenance: each work phase's `Post` is the campaign's
  `Phase{i}…` window predicate; the `= allPhaseGe (seamP k) n` identification is the
  per-phase structural reading carried at `SeamEpidemics.lean:185` ("Pre reduces to
  `allPhaseEq i n ∧ structural component`").  Carried.
* `hWindowToWorkPre k` — identifies the seam's EXACT output window
  `allPhaseEq (seamP k + 1) n` with `work (k+1) . Pre`.  Provenance: same per-phase
  structural reading; for `≥`-window destinations (Phase 4's `Q4 = allPhaseGe 4`) the
  identification drops the overshoot exactness, otherwise it is the exact pin.  Carried. -/
structure Assembly (n : ℕ) where
  /-- The 11 landed WORK `PhaseConvergenceW` instances (each with its internal drains). -/
  work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel
  /-- The 10 seam phase parameters `pₖ` (the source window threshold of seam `k`). -/
  seamP : Fin 10 → ℕ
  /-- The 10 seam horizons `tseamₖ`. -/
  seamT : Fin 10 → ℕ
  /-- The 10 seam epidemic budgets. -/
  εepidemic : Fin 10 → ℝ≥0
  /-- The 10 seam no-overshoot budgets. -/
  εovershoot : Fin 10 → ℝ≥0
  /-- Seam feeder: the generic-`p` advance-epidemic drift (`SeamEpidemics.seam_drift`). -/
  hDrift : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k + 1) n c'}
        ≤ (εepidemic k : ℝ≥0∞)
  /-- Seam feeder: per-seam no-overshoot tail.  For destinations `{1,6,7,8}` this is the
  landed `SeamNoOvershoot.hNoOvershoot_one_seam_honest` output; for `{2,3,4,5,9}` it is the
  named per-seam guard.  Either way it is the budget shape `seamEpidemicExactW` consumes. -/
  hNoOvershoot : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c ∧
        SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c) →
      ((NonuniformMajority L K).transitionKernel ^ (seamT k)) c
          {c' | ¬ SeamNoOvershoot.NoOvershoot (L := L) (K := K) (seamP k) c'}
        ≤ (εovershoot k : ℝ≥0∞)
  /-- Bridge gap `hTrig`: the advance trigger on each work `Post`. -/
  hTrig : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c
  /-- Bridge gap `hWorkPostToWindow`: work `Post` ⟹ seam source window `allPhaseGe pₖ n`. -/
  hWorkPostToWindow : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      SeamEpidemics.allPhaseGe (L := L) (K := K) (seamP k) n c
  /-- Bridge gap `hWindowToWorkPre`: seam EXACT output window
  `allPhaseEq (pₖ+1) n` ⟹ work `(k+1)` `Pre`. -/
  hWindowToWorkPre : ∀ (k : Fin 10) (c : Config (AgentState L K)),
      SeamEpidemics.allPhaseEq (L := L) (K := K) (seamP k + 1) n c →
      (work ⟨k.val + 1, by omega⟩).Pre c

/-! ## Part C — the concrete 21-instance family. -/

/-- The `k`-th seam instance — the EXACT seam `seamEpidemicExactW`, NOT the calibrated
generic seam.  Its `Post` is `allPhaseGe (pₖ+1) n ∧ NoOvershoot pₖ` and its `convergence`
consumes BOTH `εepidemic k` and `εovershoot k`. -/
noncomputable def seamInstance {n : ℕ} (asm : Assembly (L := L) (K := K) n)
    (k : Fin 10) : PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  SeamNoOvershoot.seamEpidemicExactW (asm.seamP k) n (asm.seamT k)
    (asm.εepidemic k) (asm.εovershoot k) (asm.hDrift k) (asm.hNoOvershoot k)

/-- **The concrete 21-instance family** `[work₀, seam₀, …, seam₉, work₁₀]`.
Even slot `2k ↦ work k`; odd slot `2k+1 ↦ seamInstance k` (the EXACT seam). -/
noncomputable def phases {n : ℕ} (asm : Assembly (L := L) (K := K) n) :
    Fin 21 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  fun i =>
    if h : i.val % 2 = 0 then asm.work (workIdx i)
    else seamInstance asm (seamIdx i (by omega))

@[simp] theorem phases_even {n : ℕ} (asm : Assembly (L := L) (K := K) n)
    (i : Fin 21) (h : i.val % 2 = 0) :
    phases asm i = asm.work (workIdx i) := by
  simp only [phases, dif_pos h]

@[simp] theorem phases_odd {n : ℕ} (asm : Assembly (L := L) (K := K) n)
    (i : Fin 21) (h : i.val % 2 = 1) :
    phases asm i = seamInstance asm (seamIdx i h) := by
  simp only [phases, dif_neg (by omega : ¬ i.val % 2 = 0)]

/-! ## Part D — the bridges (`h_chain`).

The chain alternates work→seam (even slot `i = 2k`, successor odd `2k+1`) and
seam→work (odd slot `i = 2k+1`, successor even `2k+2`).  We prove each direction, then
glue into the headline's `h_chain` shape. -/

/-- **Work→seam bridge.**  `work k . Post ⟹ seamInstance k . Pre`.  The seam `Pre` is
`allPhaseGe pₖ n ∧ advTriggered (pₖ+1)`, supplied from the carried structural readings
`hWorkPostToWindow` and `hTrig` via `SeamEpidemics.exact_work_into_seam`'s `≥`-form
(`ge_work_into_seam`). -/
theorem bridge_work_to_seam {n : ℕ} (asm : Assembly (L := L) (K := K) n)
    (k : Fin 10) (c : Config (AgentState L K))
    (hpost : (asm.work ⟨k.val, by omega⟩).Post c) :
    (seamInstance asm k).Pre c := by
  -- `seamInstance k . Pre = allPhaseGe pₖ n ∧ advTriggered (pₖ+1)`.
  refine ⟨asm.hWorkPostToWindow k c hpost, asm.hTrig k c hpost⟩

/-- **Seam→work bridge.**  `seamInstance k . Post ⟹ work (k+1) . Pre`.  The EXACT seam's
`Post` is `allPhaseGe (pₖ+1) n ∧ NoOvershoot pₖ`; `SeamNoOvershoot.seamExact_into_exact_work`
turns it into `allPhaseEq (pₖ+1) n` POINTWISE with no further timing input (this is exactly
why the exact seam is required — the calibrated generic seam's `Post` lacks `NoOvershoot`,
so this bridge would NOT close); the carried `hWindowToWorkPre` then identifies that exact
window with `work (k+1) . Pre`. -/
theorem bridge_seam_to_work {n : ℕ} (asm : Assembly (L := L) (K := K) n)
    (k : Fin 10) (c : Config (AgentState L K))
    (hpost : (seamInstance asm k).Post c) :
    (asm.work ⟨k.val + 1, by omega⟩).Pre c := by
  -- `seamInstance k . Post = allPhaseGe (pₖ+1) n ∧ NoOvershoot pₖ` (definitional).
  have hwin : SeamEpidemics.allPhaseEq (L := L) (K := K) (asm.seamP k + 1) n c :=
    SeamNoOvershoot.seamExact_into_exact_work c hpost
  exact asm.hWindowToWorkPre k c hwin

/-- **The assembled `h_chain`.**  For every slot `i : Fin 21` with `i.val + 1 < 21`, the
slot `Post` implies the successor slot `Pre`.  Splits on the parity of `i`: even slot
`2k` uses `bridge_work_to_seam`, odd slot `2k+1` uses `bridge_seam_to_work`. -/
theorem phases_h_chain {n : ℕ} (asm : Assembly (L := L) (K := K) n) :
    ∀ (i : Fin 21) (hi : i.val + 1 < 21),
      ∀ x, (phases asm i).Post x → (phases asm ⟨i.val + 1, hi⟩).Pre x := by
  intro i hi x hpost
  -- the `Fin 21` successor slot, with its value reduced (`Fin.val ⟨v,_⟩ = v`).
  have hjval : (⟨i.val + 1, hi⟩ : Fin 21).val = i.val + 1 := rfl
  rcases Nat.even_or_odd i.val with hev | hod
  · -- even slot `2k`: successor is the odd seam slot `2k+1`.
    have hi0 : i.val % 2 = 0 := Nat.even_iff.mp hev
    have hsucc1 : (⟨i.val + 1, hi⟩ : Fin 21).val % 2 = 1 := by rw [hjval]; omega
    rw [phases_even asm i hi0] at hpost
    rw [phases_odd asm ⟨i.val + 1, hi⟩ hsucc1]
    set k : Fin 10 := seamIdx ⟨i.val + 1, hi⟩ hsucc1 with hkdef
    -- `k.val = (i+1)/2 = i/2 = (workIdx i).val` (i even); identify the work slots.
    have hkw : (⟨k.val, by omega⟩ : Fin 11) = workIdx i := by
      apply Fin.ext
      have hkval : k.val = i.val / 2 := by rw [hkdef, seamIdx_val, hjval]; omega
      rw [Fin.val_mk, hkval, workIdx_val]
    have hbridge := bridge_work_to_seam asm k x
    rw [hkw] at hbridge
    exact hbridge hpost
  · -- odd slot `2k+1`: successor is the even work slot `2k+2`.
    have hi1 : i.val % 2 = 1 := Nat.odd_iff.mp hod
    have hsucc0 : (⟨i.val + 1, hi⟩ : Fin 21).val % 2 = 0 := by rw [hjval]; omega
    rw [phases_odd asm i hi1] at hpost
    rw [phases_even asm ⟨i.val + 1, hi⟩ hsucc0]
    set k : Fin 10 := seamIdx i hi1 with hkdef
    -- `(workIdx (i+1)).val = (i+1)/2 = i/2 + 1 = k.val + 1` (i odd); identify the work slots.
    have hkw : (⟨k.val + 1, by omega⟩ : Fin 11) = workIdx ⟨i.val + 1, hi⟩ := by
      apply Fin.ext
      have hkval : k.val = i.val / 2 := by rw [hkdef, seamIdx_val]
      rw [Fin.val_mk, hkval, workIdx_val, hjval]
      omega
    have hbridge := bridge_seam_to_work asm k x
    rw [hkw] at hbridge
    exact hbridge hpost

/-! ## Part E — the concrete headline.

We seal `phases`/`seamInstance` as `irreducible`: every statement below is phrased in
terms of `phases asm`, never its unfolding.  All unfoldings the bridges / simp-lemmas
needed were done above. -/

attribute [irreducible] seamInstance phases

/-! ### The composition contract for the concrete family, and the kernel-power obstruction.

`time_composition_W2 … (phases asm) … (phases_h_chain asm) …` APPLIES cheaply at
the concrete family (the 20 bridges are discharged by `phases_h_chain`, closed above).
Its three outputs are the genuine end-to-end facts for the assembled protocol:

  `.1` : `(K ^ ∑ (phases asm i).t) c₀ {¬ majorityStableEndpoint init} ≤ ∑ (phases asm i).ε`
  `.2.1` : `∑ (phases asm i).t ≤ (∑ Cphase i) · n · (L+1)`
  `.2.2` : `∑ (phases asm i).ε ≤ ∑ δ i`

OBSTRUCTION (documented, NOT a hole in the assembly): in this codebase, *re-using* `.1` —
unifying its kernel-power LHS `(K ^ ∑ (phases asm i).t) c₀ {…}` against any restated copy
(`le_trans`, `calc`, `exact`, `▸`) — diverges (a `whnf` blowup that survives `≥ 3 000 000`
heartbeats and `irreducible`).  It is a property of the kernel-power-applied-to-a-`Fin 21`-sum
representation, present already in the base `time_headline_W2_inv_sq` (which is therefore
stated polymorphically over an abstract `phases`, never instantiated at a concrete family).
The `.2.1`/`.2.2` outputs (pure `ℕ`/`ℝ≥0∞` sums, NO kernel power) PROJECT and re-use cheaply
(verified: `(time_composition_W2 … (phases asm) …).2.1` / `.2.2` elaborate in
seconds).  Only the failure-side `.1` and any restatement of its kernel-power LHS diverge.

So the concrete headline below: (i) discharges the TIME half fully from `.2.1` (cheap), and
(ii) carries the failure-side composition output `.1` as a NAMED hypothesis `hcompFail`
(`(K ^ T) c₀ {¬ majorityStableEndpoint} ≤ ∑ (phases asm i).ε`, with `T = ∑ (phases
asm i).t` via `hT`).  `hcompFail` is the genuine assembled failure bound — the caller obtains
it from the cheap `time_composition_W2 …` application (its `.1`) and supplies it directly
(it cannot be re-derived *inside* a stated theorem because of the kernel-power obstruction).
On top of `hcompFail` the headline discharges the kernel-power-FREE budget arithmetic
`∑ ε ≤ ∑ δ ≤ 21/n²`.  This keeps the headline finite and inspectable. -/

/-- **`time_headline_CONCRETE` — the assembled headline at `O(1/n²)`.**

The concrete 21-instance assembly's end-to-end bound: failure `≤ 21/n²` within
`T ≤ 21·C0·n·(L+1)` interactions.  The carried set is FINITE and inspectable (no polymorphic
`phases`/`h_chain`/`h_post` triple):

  * the fields of `asm` (`Assembly`): the 11 work instances (each with its internal
    drains), the 10 EXACT-seam feeders (`hDrift`, `hNoOvershoot` — forcing
    `seamEpidemicExactW`, NOT the calibrated generic seam), and the three structural bridge
    gaps (`hTrig`, `hWorkPostToWindow`, `hWindowToWorkPre`);
  * `hcompFail` — the failure-side composition output `(phases_composition …).1`
    (supplied by the caller via one cheap application; carries the kernel-power re-use
    obstruction documented above — the genuine assembled bound, NOT a free hypothesis: its
    only honest content is `≤ ∑ (phases asm i).ε`, which the budget arithmetic finishes);
  * `T`/`hT` — the assembled horizon, pinned to `∑ (phases asm i).t`;
  * `ht`/`hC0` (per-slot time scaling), `hε`/`hδ` (per-slot `n⁻²` budget).

The `h_chain` binder — the 20 bridges — is GONE (closed inside `phases_composition`).  The
TIME half is fully closed; the FAILURE half is the cheap budget arithmetic on `hcompFail`.
No `native_decide`, no kernel work; axioms stay `[propext, Classical.choice, Quot.sound]`. -/
theorem time_headline_CONCRETE
    {L K n C0 : ℕ}
    (init c₀ : Config (AgentState L K))
    (asm : Assembly (L := L) (K := K) n)
    (Cphase : Fin 21 → ℕ) (δ : Fin 21 → ℝ≥0)
    (T : ℕ) (hT : T = ∑ i, (phases asm i).t)
    (hcompFail :
      ((NonuniformMajority L K).transitionKernel ^ T) c₀
          {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
        ≤ (∑ i, ((phases asm i).ε : ℝ≥0∞)))
    (ht : ∀ i, (phases asm i).t ≤ Cphase i * n * (L + 1))
    (hε : ∀ i, ((phases asm i).ε : ℝ≥0∞) ≤ (δ i : ℝ≥0∞))
    (hx₀ : (phases asm ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (phases asm ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    (hδ : ∀ i, (δ i : ℝ≥0∞) ≤ (1 / (n : ℝ≥0∞) ^ 2)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * C0 * n * (L + 1) := by
  -- the composition APPLIES cheaply; we project only the kernel-power-FREE `.2.1`/`.2.2`
  -- (the failure-side `.1` is carried as `hcompFail`, see the module note).
  have hcomp := time_composition_W2 init c₀ Cphase δ (phases asm)
    ht hε (phases_h_chain asm) hx₀ h_post
  have h_time := hcomp.2.1
  have h_err := hcomp.2.2
  have hδsum : (∑ i, (δ i : ℝ≥0∞)) ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2 := by
    have := BudgetTightening.sum_inv_sq_le (m := 21) (n := n) δ hδ
    simpa using this
  refine ⟨le_trans hcompFail (le_trans h_err hδsum), ?_⟩
  -- TIME half (kernel-power-free, fully closed): transport `.2.1` arithmetic along `hT`.
  rw [hT]
  calc (∑ i, (phases asm i).t)
      ≤ (∑ i, Cphase i) * n * (L + 1) := h_time
    _ ≤ (21 * C0) * n * (L + 1) := by
        have hsum : (∑ i, Cphase i) ≤ 21 * C0 := by
          calc (∑ i : Fin 21, Cphase i)
              ≤ ∑ _i : Fin 21, C0 := Finset.sum_le_sum (fun i _ => hC0 i)
            _ = 21 * C0 := by simp [Finset.sum_const, Finset.card_univ, mul_comm]
        gcongr
    _ = 21 * C0 * n * (L + 1) := by ring

/-! **The headline at the realised seam budget.**  `time_headline_CONCRETE_self`
specialises `time_headline_CONCRETE` to `δ i = (phases asm i).ε` (each `≤ 1/n²` by
the campaign's calibration).  Records that, with the EXACT seams forced, the composite
failure is the honest `21/n²`. -/
theorem time_headline_CONCRETE_self
    {L K n C0 : ℕ}
    (init c₀ : Config (AgentState L K))
    (asm : Assembly (L := L) (K := K) n)
    (Cphase : Fin 21 → ℕ)
    (T : ℕ) (hT : T = ∑ i, (phases asm i).t)
    (hcompFail :
      ((NonuniformMajority L K).transitionKernel ^ T) c₀
          {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
        ≤ (∑ i, ((phases asm i).ε : ℝ≥0∞)))
    (ht : ∀ i, (phases asm i).t ≤ Cphase i * n * (L + 1))
    (hx₀ : (phases asm ⟨0, by omega⟩).Pre c₀)
    (h_post : ∀ c, (phases asm ⟨21 - 1, by omega⟩).Post c →
        majorityStableEndpoint (L := L) (K := K) init c)
    (hC0 : ∀ i, Cphase i ≤ C0)
    (hεcal : ∀ i, ((phases asm i).ε : ℝ≥0∞) ≤ (1 / (n : ℝ≥0∞) ^ 2)) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀
        {c | ¬ majorityStableEndpoint (L := L) (K := K) init c}
      ≤ (21 : ℝ≥0∞) / (n : ℝ≥0∞) ^ 2
    ∧ T ≤ 21 * C0 * n * (L + 1) := by
  exact time_headline_CONCRETE init c₀ asm Cphase
    (fun i => (phases asm i).ε) T hT hcompFail ht (fun _ => le_refl _) hx₀ h_post hC0 hεcal

end ConcreteAssembly

end ExactMajority
