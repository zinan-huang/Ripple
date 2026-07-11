/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# FaithfulDischargeTierA — the DETERMINISTIC (Tier-A) supplier lemmas for the
faithful residual bundle `ResidualAtomsFaithful`.

This append-only file edits NO existing file.  It discharges the CLEAN, no-probability
fields of `ResidualAtomsFaithful` (see `DISCHARGE_ROSTER.md`, Tier A) to standalone
deterministic facts, and ISOLATES — refutation-checked — the two fields that are NOT
universal-over-all-configs but hold only on the reachable / role-structured domain.

## What is here (Tier A)

* **D4 scalars (`Cphase`/`δ`/`hC0`/`hδ`).**  The locked values `Cphase i := 17 = C0_numeral`
  and `δ i := (1/n²).toNNReal`.  `hC0_locked` and `hδ_locked` are PURE ARITHMETIC fits, TRUE
  universally.

* **`hsmall` (D14a, the small-config self-loop).**  A config with `card < 2` is a `PMF.pure`
  self-loop (`stepDistOrSelf … = PMF.pure c`), so its successor is `c` itself and the count
  CANNOT strictly decrease — the bad set has kernel mass `0`.  This is a TRUE UNIVERSAL over
  ALL configs (no reachability needed), discharged here in full.

* **`hStart` (D5).**  `validInitial c₀ ∧ c₀.card = n → Phase0Initial n c₀` — a structural
  unfold: `validInitial` pins every agent to `phase 0`, `role mcr`; the population-size
  conjunct `c₀.card = n` supplies the `Multiset.card c = n` half of `Phase0Initial`.

## The TWO STRUCTURED residuals (refutation-checked NOT universal)

`mgf_depletion_tail_uniform`/`uniform_decrement_bound` consume two MORE hypotheses that are
**FALSE as universals over all configs** and TRUE only on the reachable-from-`c₀` / role-pinned
domain.  We isolate them precisely:

* **`hcard : ∀ c, 2 ≤ c.card → c.card = n`.**  FALSE universally: a config of `3` agents has
  `card = 3 ≠ n` for `n ≠ 3` (`hcard_not_universal`).  The CORRECT domain is *reachable from a
  start of card `n`*; the TRUE deterministic supplier is `reachable_card_eq`, packaged here as
  `card_eq_on_reachable : Reachable c₀ c → c₀.card = n → c.card = n`.

* **`hcap : ∀ c, c.count sc ≤ m`.**  FALSE universally: a config with all `card` agents in state
  `sc` has `count sc = card`, which exceeds any fixed `m < card` (`hcap_not_universal`).  The
  CORRECT domain is the role-structured / `Q_mix` reachable set where the clock count is pinned
  (`HabsDischarge.qmix_clockSize_closed`: `clockCount = mC`).  We package the conservation form
  `clockCount_le_on_reachable_qmix`.

So the universal `hcard`/`hcap` cannot be carried as bare deterministic facts; the honest
deterministic content is the *reachable-restricted* conservation, proven below and refutation-
checked against the false universals.

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆ [propext,
Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockDepletionCoupling
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HabsDischarge
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitConcentration
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Constants
import Ripple.PopulationProtocol.Majority.ExactMajority.Analysis.MainTheorem

namespace ExactMajority
namespace FaithfulDischargeTierA

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

variable {L K : ℕ}

/-! ## Part 1 — D4 SCALARS.  The locked-value scalar fields, pure arithmetic. -/

/-- The locked `Cphase` family: every per-instance time coefficient is the honest integer
ceiling `C0_numeral = 17`. -/
def CphaseLocked : Fin 21 → ℕ := fun _ => Constants.C0_numeral

/-- The locked `δ` family: every per-phase failure budget is the genuine `(1/n²).toNNReal`. -/
noncomputable def δLocked (n : ℕ) : Fin 21 → ℝ≥0 := fun _ => Real.toNNReal (1 / (n : ℝ) ^ 2)

/-- **`hC0_locked` (D4).**  The locked `Cphase i = 17` meets the bundle's `hC0 : Cphase i ≤ C0`
at the numeral `C0 = C0_numeral = 17`.  Pure arithmetic, TRUE universally. -/
theorem hC0_locked : ∀ i : Fin 21, CphaseLocked i ≤ Constants.C0_numeral :=
  fun _ => le_refl _

/-- **`hδ_locked` (D4).**  The locked `δ i = (1/n²).toNNReal` meets the bundle's
`hδ : (δ i : ℝ≥0∞) ≤ 1/n²`.  The coercion of `(1/n²).toNNReal` is `ENNReal.ofReal (1/n²)`,
which equals `1/(n:ℝ≥0∞)²` for `n ≥ 1` (and is `≤` it always).  PURE ARITHMETIC. -/
theorem hδ_locked (n : ℕ) :
    ∀ i : Fin 21, ((δLocked n i : ℝ≥0) : ℝ≥0∞) ≤ 1 / (n : ℝ≥0∞) ^ 2 := by
  intro _
  unfold δLocked
  -- coercion of toNNReal is ENNReal.ofReal
  rw [show (((Real.toNNReal (1 / (n : ℝ) ^ 2)) : ℝ≥0) : ℝ≥0∞)
        = ENNReal.ofReal (1 / (n : ℝ) ^ 2) from by rw [ENNReal.ofReal]]
  -- ENNReal.ofReal (1/n²) = 1/(n:ℝ≥0∞)²  (true for all n ≥ 0; n = 0 ⇒ both sides 0)
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0; simp
  · have hnpow : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    -- rewrite the ENNReal RHS power as ofReal of the real power
    rw [show ((n : ℝ≥0∞) ^ 2) = ENNReal.ofReal ((n : ℝ) ^ 2) from by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity)]]
    rw [one_div, one_div, ← ENNReal.ofReal_inv_of_pos hnpow]

/-! ## Part 2 — `hsmall` (D14a).  The small-config self-loop is a TRUE UNIVERSAL.

A config with `card < 2` has `stepDistOrSelf c = PMF.pure c` (the degenerate fallback), so
its only successor is `c` itself.  The bad event `{c' | c'.count sc < c.count sc}` then forces
`c.count sc < c.count sc`, which is impossible; the kernel mass is `0`.  No reachability,
no role structure — this holds for EVERY config. -/

/-- **`hsmall_self_loop` (D14a, deterministic, TRUE UNIVERSAL).**  Small configs (`card < 2`)
cannot strictly decrement any state count: their `stepDistOrSelf` is the point mass `PMF.pure c`,
whose only support point is `c`, on which `count sc < count sc` is false. -/
theorem hsmall_self_loop (sc : AgentState L K) :
    ∀ c : Config (AgentState L K), ¬ (2 ≤ c.card) →
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' : Config (AgentState L K) | c'.count sc < c.count sc} = 0 := by
  intro c hc
  -- stepDistOrSelf c = PMF.pure c on small configs
  rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c from by
    unfold Protocol.stepDistOrSelf; rw [dif_neg hc]]
  -- PMF.pure c .toMeasure of a set not containing c is 0
  rw [PMF.toMeasure_pure_apply]
  · rw [if_neg]
    -- c ∉ {c' | c'.count sc < c.count sc}  because count sc < count sc is false
    simp only [Set.mem_setOf_eq, lt_self_iff_false, not_false_eq_true]
  · -- measurability of the set (discrete σ-algebra: everything is measurable)
    exact MeasurableSet.of_discrete

/-! ## Part 3 — `hStart` (D5).  `validInitial c₀ ⟹ Phase0Initial n c₀` (with the size carry).

The slot-0 work `Pre` is `RoleSplitConcentration.Phase0Initial n c₀` (the phase-0 entry:
`card = n` and every agent at phase `0`, role `mcr`).  `validInitial` supplies the per-agent
half DIRECTLY (it pins `phase = ⟨0⟩` and `role = .mcr`); the population-size half `card = n`
is the separate `n`-instantiation carry (the bundle parameter `n` IS the input population). -/

/-- **`phase0Initial_of_validInitial` (D5, structural unfold).**  From `validInitial c₀` (every
agent at phase `0`, role `mcr`) together with the population-size carry `c₀.card = n` (the
bundle's `n` is the input population), the phase-0 entry condition `Phase0Initial n c₀` holds.
This is the slot-0 work `Pre`, hence the `hStart` field. -/
theorem phase0Initial_of_validInitial (n : ℕ) (c₀ : Config (AgentState L K))
    (hvalid : validInitial c₀) (hcard : Multiset.card c₀ = n) :
    RoleSplitConcentration.Phase0Initial (L := L) (K := K) n c₀ := by
  refine ⟨hcard, ?_⟩
  intro a ha
  obtain ⟨hphase, hrole, _, _, _, _⟩ := hvalid a ha
  refine ⟨?_, hrole⟩
  -- a.phase = ⟨0, _⟩  ⟹  a.phase = 0
  rw [hphase]; rfl

/-! ## Part 4 — the TWO STRUCTURED residuals (refutation-checked NOT universal).

`mgf_depletion_tail_uniform` (`ClockDepletionCoupling`) consumes
  * `hcard : ∀ c, 2 ≤ c.card → c.card = n`
  * `hcap  : ∀ c, c.count sc ≤ m`
as UNIVERSALS over all configs.  Both are FALSE as universals; they hold only on the
reachable-from-`c₀` / role-structured domain.  We prove the FALSITY of the universals
(refutation check) and the TRUE reachable-restricted conservation forms. -/

/-! ### 4a — `hcard`: false universally, TRUE on the reachable set. -/

/-- **REFUTATION CHECK for `hcard`.**  The universal `∀ c, 2 ≤ c.card → c.card = n` is FALSE:
for any `n ≠ 3` there is a config of card `3` (three copies of one agent), witnessing
`2 ≤ 3` but `3 ≠ n`.  So `hcard` cannot be a bare universal-over-all-configs fact. -/
theorem hcard_not_universal (a : AgentState L K) (n : ℕ) (hn : n ≠ 3) :
    ¬ (∀ c : Config (AgentState L K), 2 ≤ c.card → c.card = n) := by
  intro hall
  have hcard3 : (Multiset.replicate 3 a).card = 3 := by simp
  have := hall (Multiset.replicate 3 a) (by rw [hcard3]; norm_num)
  rw [hcard3] at this
  exact hn this.symm

/-- **`card_eq_on_reachable` (TRUE deterministic supplier for `hcard`).**  Card is conserved
along reachability: every config reachable from a start `c₀` of card `n` ALSO has card `n`.
This is the HONEST form of `hcard` — restricted to the reachable-from-`c₀` domain (which is
the only domain the depletion tail visits), via `reachable_card_eq`. -/
theorem card_eq_on_reachable (n : ℕ) (c₀ c : Config (AgentState L K))
    (hreach : (NonuniformMajority L K).Reachable c₀ c) (hc₀ : Multiset.card c₀ = n) :
    Multiset.card c = n := by
  rw [Protocol.reachable_card_eq (P := NonuniformMajority L K) hreach]; exact hc₀

/-! ### 4b — `hcap`: false universally, TRUE on the role-structured (`Q_mix`) reachable set. -/

/-- **REFUTATION CHECK for `hcap`.**  The universal `∀ c, c.count sc ≤ m` is FALSE for any
fixed `m`: the config of `m+1` copies of `sc` has `count sc = m+1 > m`.  So `hcap` cannot be
a bare universal-over-all-configs fact; the clock count is bounded only where the role
structure pins it. -/
theorem hcap_not_universal (sc : AgentState L K) (m : ℕ) :
    ¬ (∀ c : Config (AgentState L K), c.count sc ≤ m) := by
  intro hall
  have := hall (Multiset.replicate (m + 1) sc)
  rw [Config.count, Multiset.count_replicate_self] at this
  omega

/-- **`clockCount_eq_on_reachable_qmix` (TRUE deterministic supplier for the clock cap).**  On
the role-structured window `Q_mix n mC T ∧ allPhaseGE3`, the clock count is EXACTLY preserved
at `mC` on every one-step successor (`HabsDischarge.qmix_clockSize_closed`).  This is the
HONEST form of the clock cap — the clock count is pinned to `mC` on the reachable role-pinned
set, NOT universally bounded.  (`clockCount` is `Config.count` over the clock-role agents in
the genuine instantiation; the cap `m := mC` then holds on this domain.) -/
theorem clockCount_eq_on_reachable_qmix (n mC T : ℕ)
    (c c' : Config (AgentState L K))
    (hQ : ClockRealMixed.Q_mix (L := L) (K := K) n mC T c)
    (hge : HabsDischarge.allPhaseGE3 (L := L) (K := K) c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    ClockRealMixed.clockCount (L := L) (K := K) c' = mC :=
  HabsDischarge.qmix_clockSize_closed n mC T c c' hQ hge hc'

/-! ## Part 5 — AUDIT SUMMARY (the Tier-A determination).

| field            | status                  | domain                                    |
|------------------|-------------------------|-------------------------------------------|
| `hC0` (D4)       | DISCHARGED (universal)  | all configs — `hC0_locked`                |
| `hδ` (D4)        | DISCHARGED (universal)  | all configs — `hδ_locked`                 |
| `hStart` (D5)    | DISCHARGED (structural) | `validInitial c₀ ∧ card c₀ = n`           |
| `hsmall` (D14a)  | DISCHARGED (universal)  | all configs — `hsmall_self_loop`          |
| `hcard` (D14a)   | STRUCTURED RESIDUAL     | reachable-from-`c₀` (`card_eq_on_reachable`)  |
| `hcap`  (D14a)   | STRUCTURED RESIDUAL     | `Q_mix`-reachable (`clockCount_eq_..qmix`)    |

`hcard` universal is FALSE (`hcard_not_universal`); `hcap` universal is FALSE
(`hcap_not_universal`).  The two structured residuals are TRUE only on the reachable /
role-structured domain; carrying them as universals-over-all-configs would be FALSE
(refutation-checked).  The depletion-tail
consumer (`mgf_depletion_tail_uniform`) must therefore be applied over the reachable-from-`c₀`
domain (where `card = n` and `clockCount = mC` hold), NOT with a bare universal `hcard`/`hcap`.
-/

#print axioms hC0_locked
#print axioms hδ_locked
#print axioms hsmall_self_loop
#print axioms phase0Initial_of_validInitial
#print axioms hcard_not_universal
#print axioms card_eq_on_reachable
#print axioms hcap_not_universal
#print axioms clockCount_eq_on_reachable_qmix

end FaithfulDischargeTierA
end ExactMajority
