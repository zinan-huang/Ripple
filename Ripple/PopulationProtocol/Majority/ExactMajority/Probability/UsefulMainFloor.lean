/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Theorem 6.2 useful-Main floor at Phase-5 entry (Doty et al. §6)

`PhaseFloors.phase5_hdrop_wired` consumes ONE structural count floor as a named hypothesis:

```text
hmain : P ≤ (Phase5Convergence.usefulMains).sum b.count
```

where `usefulMains := filter biasedMainLtL` and `biasedMainLtL a := a.role = main ∧
∃ σ i, i.val < L ∧ a.bias = dyadic σ i` (a Main whose dyadic exponent **index** is `< L`, i.e.
`|bias| > 2^{-L}` — a *useful eliminator* in the Reserve-sampling phase).

The provenance is the paper's **Theorem 6.2** (Doty–Eftekhari–Gąsieniec–Severson–Uznański–Xu,
arXiv:2106.10201v2, §6):

> **Theorem 6.2.** Assume the initial gap `|g| < 0.025|M|`.  Let `−l = ⌊log₂(0.4|M|/…)⌋` and let
> `M' = { Main agents with majority opinion and exponent ∈ {−l, −(l+1), −(l+2)} }`.  Then at the
> end of Phase 3 (= Phase-5 entry), `|M'| ≥ 0.92|M|` with high probability `1 − O(1/n²)`.

## Why this is genuinely-new probability, not a landed export (audit)

No landed `Post` in the chain exports a count lower bound on Mains confined below the exponent cap:

* `ReserveSampling.Phase5AllWin n c = c.card = n ∧ ∀ a ∈ c, a.phase.val = 5` — a PURE PHASE
  window; it carries NOTHING about the bias/exponent profile.
* The Phase-3/4 `Post`s (`Phase4Convergence`'s `advFinished` / `StableTie4`) are phase-advance
  facts (`phaseBelowCount 5 = 0`) and the tie predicate (`noBigBias` for ALL agents); neither is a
  count LOWER bound on the big-bias (`index < L`) Mains.  In fact the tie branch is the OPPOSITE
  extreme (`noBigBias` = every biased agent at index `= L`).  Theorem 6.2 is the NON-tie branch.
* `RoleSplitConcentration.mainCount_lower_of_RoleSplitGood` gives `n/3 ≤ mainCount` (Lemma 5.2),
  the role split — but says nothing about the exponent distribution WITHIN the Mains.

### Genuine attack on deriving it from the landed §6 width/hour machinery

The landed §6 machinery — `ClockFrontProfile` (Theorem 6.5 windowed doubly-exponential decay),
`WidthTransport` / `CrossHourSide` / `FrontTailDecay` (Theorem 6.9/6.12 clock-front width
`O(log log n)`) — concentrates the **Clock minute distribution**.  It bounds how far ahead any
clock agent's `minute`/`hour` field can run, which is the ENABLING mechanism for Theorem 6.2 (it
is why "hour `i` lasts long enough to bring most biased agents down to exponent `−i`").  But these
exports are about the CLOCK field, not a count over Main bias exponents.  Producing the
`|M'| ≥ 0.92|M|` count requires the full Phase-3 bias-ledger argument: the cancel/split mass
accounting over all `L` hours (Theorem 6.5's `c≥(i+1)(t) < p·c≥i(t)²` squaring applied to the
*Main* exponent profile, plus the total-mass-above / minority-mass bounds `µ(>−l) ≤ 0.002|M|2^{−l}`,
`β⁻ ≤ 0.004|M|2^{−l}`), union-bounded over the `O(log n)` hours.  That inductive bias-ledger
collapse is NOT a consequence of the landed clock-front concentration alone; it is the
genuinely-new probabilistic content of Theorem 6.2.

So Theorem 6.2 is carried as ONE precisely-stated named fact inside `Theorem62EntryHypotheses`
(field `hConfine`), with its paper provenance documented.  Everything ELSE — the partition
arithmetic that turns the `0.92·|M|` confinement plus the `n/3 ≤ |M|` role floor into the consumer
shape `P ≤ usefulMains.sum count` for `P ≤ 23n/75` — is PROVEN here, axiom-clean.

## What IS proven here (the partition arithmetic)

* `mainCount_eq_usefulMains_add_satExp` — the genuine Main decomposition
  `mainCount c = usefulMains.sum count + satExpMains.sum count`, where `satExpMains` is the
  complement of `usefulMains` within the Mains (bias zero, or dyadic at the cap index `= L`).
  This is the Phase-5 analogue of `PhaseFloors.mainCount_eq_pullPos_add_saturatedPos`.
* `theorem6_2_usefulMains_floor` — from `Theorem62EntryHypotheses` (the named Theorem-6.2
  confinement `0.92·|M| ≤ usefulMains.sum count` plus the role floor `n/3 ≤ |M|`) and the
  arithmetic side condition `P ≤ 23n/75`, conclude `P ≤ usefulMains.sum count`, by
  `23n/75 = 0.92·(n/3) ≤ 0.92·|M| ≤ usefulMains.sum count`.
* `phase5_hdrop_wired_from_theorem6_2` — the wired adapter into
  `PhaseFloors.phase5_hdrop_wired`, supplying the `hmain` floor from the entry hypotheses.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseFloors

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace UsefulMainFloor

variable {L K : ℕ}

/-! ## Part A — the complement of `usefulMains` within the Mains.

`usefulMains := filter biasedMainLtL` collects Mains whose dyadic bias has exponent index `< L`.
Its complement within the Main population is the set of Mains that are EITHER unbiased (`bias =
zero`) OR saturated at the cap exponent (`dyadic` with index `= L`, i.e. `¬ index < L`).  We call
this `satExpMain` (saturated-exponent Main); it is exactly `role = main ∧ noBigBias`.  The Main
population partitions as `usefulMains ⊔ satExpMains`, giving the count identity that converts the
Theorem-6.2 confinement bound into the consumer floor. -/

/-- The `noBigBias` predicate (inlined from `Phase4Convergence.noBigBias`, which is not in this
file's import closure): the bias is `.zero`, or `.dyadic _ i` with `¬ i.val < L` (cap exponent). -/
def noBigBias (a : AgentState L K) : Prop :=
  match a.bias with
  | .zero => True
  | .dyadic _ i => ¬ i.val < L

instance (a : AgentState L K) : Decidable (noBigBias (L := L) (K := K) a) := by
  unfold noBigBias; cases a.bias <;> infer_instance

/-- A Main with no big bias: unbiased, or dyadic at the cap exponent index `= L`
(`¬ index < L`).  This is the complement of `biasedMainLtL` within the Mains, i.e.
`role = main ∧ noBigBias`. -/
def satExpMain (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ noBigBias (L := L) (K := K) a

instance (a : AgentState L K) : Decidable (satExpMain (L := L) (K := K) a) := by
  unfold satExpMain; infer_instance

/-- The finset of saturated-exponent Mains (the complement of `usefulMains` within the Mains). -/
def satExpMains (L K : ℕ) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => satExpMain (L := L) (K := K) a)

/-- **A Main is either useful (`biasedMainLtL`) or saturated-exponent (`satExpMain`), never both.**
Both require `role = main`; they split on the bias: `biasedMainLtL` = dyadic with index `< L`,
`satExpMain` = unbiased or dyadic with index `= L`. -/
theorem main_iff_useful_or_satExp (a : AgentState L K) :
    a.role = Role.main ↔
      (Phase5Convergence.biasedMainLtL (L := L) (K := K) a ∨ satExpMain (L := L) (K := K) a) := by
  unfold Phase5Convergence.biasedMainLtL satExpMain noBigBias
  constructor
  · intro hrole
    -- case on the bias; `cases hb` rewrites `a.bias` into the goal's match, reducing it.
    cases hb : a.bias with
    | zero =>
      exact Or.inr ⟨hrole, trivial⟩
    | dyadic s i =>
      by_cases hi : i.val < L
      · exact Or.inl ⟨hrole, s, i, hi, rfl⟩
      · exact Or.inr ⟨hrole, hi⟩
  · rintro (⟨hrole, _⟩ | ⟨hrole, _⟩) <;> exact hrole

/-- `usefulMains` and `satExpMains` are disjoint (a state cannot have a dyadic bias with index
both `< L` and `= L`, and the unbiased case is excluded from `biasedMainLtL`). -/
theorem usefulMains_satExpMains_disjoint :
    Disjoint (Phase5Convergence.usefulMains (L := L) (K := K)) (satExpMains L K) := by
  classical
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Phase5Convergence.usefulMains, satExpMains, Finset.mem_filter,
    Phase5Convergence.biasedMainLtL, satExpMain, noBigBias] at ha hb
  obtain ⟨_, σ, i, hiL, hbias⟩ := ha.2
  obtain ⟨_, hnb⟩ := hb.2
  rw [hbias] at hnb
  exact hnb hiL

/-- **The Main decomposition (Phase 5).**  Over a fixed config, the Main count splits exactly into
the useful eliminator pool (`biasedMainLtL`, dyadic index `< L`) and the saturated-exponent pool
(`satExpMain`, unbiased or dyadic index `= L`):
`mainCount c = usefulMains.sum count + satExpMains.sum count`.
This is the genuine arithmetic bridge from the Main role count to the `usefulMains` floor; the
Phase-5 analogue of `PhaseFloors.mainCount_eq_pullPos_add_saturatedPos`. -/
theorem mainCount_eq_usefulMains_add_satExp (c : Config (AgentState L K)) :
    RoleSplitConcentration.mainCount (L := L) (K := K) c
      = (Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count
        + (satExpMains L K).sum c.count := by
  classical
  rw [RoleSplitConcentration.mainCount,
    Phase6Convergence.countP_eq_sum_count6 (fun a : AgentState L K => a.role = Role.main) c]
  have hsplit :
      Finset.univ.filter (fun a : AgentState L K => a.role = Role.main)
        = Phase5Convergence.usefulMains (L := L) (K := K) ∪ satExpMains L K := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Phase5Convergence.usefulMains, satExpMains]
    exact main_iff_useful_or_satExp a
  rw [hsplit, Finset.sum_union usefulMains_satExpMains_disjoint]

/-! ## Part B — the honest entry hypothesis predicate (`Theorem62EntryHypotheses`).

The blueprint's `Theorem62EntryHypotheses` placeholder, defined from what the landed chain
ACTUALLY exports plus the ONE genuinely-new Theorem-6.2 confinement fact.  The mapping:

* `hCard` / `hPhase5` (= `ReserveSampling.Phase5AllWin n c`) — the carried Phase-5 window; the
  Phase-4→5 chain Pre.  Drawn from the actual `Phase5AllWin` def.
* `hMainFloor : (n : ℝ)/3 ≤ mainCount c` — the role split (Lemma 5.2), landed as
  `RoleSplitConcentration.mainCount_lower_of_RoleSplitGood` (from `RoleSplitGood`).  Here taken as
  a hypothesis so the floor is parametric in whatever role-split post the chain carries.
* `hConfine : (0.92 : ℝ) · mainCount c ≤ usefulMains.sum count` — the genuinely-new **Theorem 6.2**
  confinement: the majority Mains confined to `{−l,−(l+1),−(l+2)}` (a SUBSET of `biasedMainLtL`,
  since `l + 2 < L`) number `≥ 0.92|M|` whp.  This is the ONE carried probabilistic core; see the
  file header audit for why it is not a landed export. -/

/-- **Theorem-6.2 entry hypotheses** at Phase-5 entry.  Bundles the landed chain facts (the
Phase-5 window + the Lemma-5.2 role floor) with the ONE genuinely-new Theorem-6.2 confinement
count (the carried probabilistic core, `0.92·|M| ≤ #usefulMains`). -/
structure Theorem62EntryHypotheses (n : ℕ) (c : Config (AgentState L K)) : Prop where
  /-- The Phase-5 structural window carried by the Phase-4→5 chain. -/
  hPhase5 : ReserveSampling.Phase5AllWin (L := L) (K := K) n c
  /-- The Lemma-5.2 role floor `n/3 ≤ |M|` (from `RoleSplitGood`). -/
  hMainFloor : (n : ℝ) / 3 ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
  /-- **The Theorem-6.2 confinement core (carried).**  At Phase-5 entry, the useful Mains (dyadic
  exponent index `< L`) number at least `0.92·|M|` — the paper's `|M'| ≥ 0.92|M|` whp, with
  `M' ⊆ usefulMains` since the confined exponents `l, l+1, l+2` are all `< L`. -/
  hConfine : (0.92 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ)
    ≤ (((Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count : ℕ) : ℝ)

/-! ## Part C — the Theorem-6.2 useful-Main floor in the blueprint shape. -/

/-- **Theorem 6.2 useful-Main floor at Phase-5 entry** (blueprint shape).  From the
`Theorem62EntryHypotheses` (the carried Theorem-6.2 confinement `0.92·|M| ≤ #usefulMains` plus the
Lemma-5.2 role floor `n/3 ≤ |M|`) and the arithmetic side condition `P ≤ 23n/75`, the consumer
floor `P ≤ usefulMains.sum count` holds.  The arithmetic is
`P ≤ 23n/75 = 0.92·(n/3) ≤ 0.92·|M| ≤ #usefulMains`. -/
theorem theorem6_2_usefulMains_floor {n : ℕ} {c : Config (AgentState L K)}
    (hT62 : Theorem62EntryHypotheses (L := L) (K := K) n c) (P : ℕ)
    (hP : (P : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75) :
    P ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count := by
  -- Work in ℝ then descend to ℕ.
  -- 23n/75 = 0.92·(n/3).
  have hsplitR : (23 : ℝ) * (n : ℝ) / 75 = (0.92 : ℝ) * ((n : ℝ) / 3) := by ring
  -- 0.92·(n/3) ≤ 0.92·|M|.
  have hstep1 : (0.92 : ℝ) * ((n : ℝ) / 3)
      ≤ (0.92 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ) := by
    apply mul_le_mul_of_nonneg_left hT62.hMainFloor (by norm_num)
  -- chain: P ≤ 23n/75 = 0.92·(n/3) ≤ 0.92·|M| ≤ #usefulMains.
  have hreal : (P : ℝ)
      ≤ (((Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count : ℕ) : ℝ) := by
    calc (P : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75 := hP
      _ = (0.92 : ℝ) * ((n : ℝ) / 3) := hsplitR
      _ ≤ (0.92 : ℝ) * (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ) := hstep1
      _ ≤ (((Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count : ℕ) : ℝ) :=
          hT62.hConfine
  exact_mod_cast hreal

/-! ## Part D — the wired adapter into `PhaseFloors.phase5_hdrop_wired`. -/

/-- **Phase 5 — the wired `hdrop` from the Theorem-6.2 entry hypotheses.**  Supplies the
`PhaseFloors.phase5_hdrop_wired` `hmain` floor directly from `Theorem62EntryHypotheses` plus the
side condition `P ≤ 23n/75`.  The Theorem-6.2 confinement is the only carried probabilistic input;
everything else (the partition arithmetic) is discharged here. -/
theorem phase5_hdrop_wired_from_theorem6_2 {n m : ℕ} (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hInv : ReserveSampling.Phase5AllWin n b)
    (hbm : ReserveSampling.unsampledReserveU (L := L) (K := K) b = m) (P : ℕ)
    (hres : 1 ≤ (Phase5Convergence.unsampledReserves (L := L) (K := K)).sum b.count)
    (hT62 : Theorem62EntryHypotheses (L := L) (K := K) n b)
    (hP : (P : ℝ) ≤ (23 : ℝ) * (n : ℝ) / 75) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow
          (ReserveSampling.unsampledReserveU (L := L) (K := K)) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  PhaseFloors.phase5_hdrop_wired n m hn b hInv hbm P hres
    (theorem6_2_usefulMains_floor hT62 P hP)

end UsefulMainFloor

end ExactMajority
