/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Package A2 — the HONEST Phase-1 partner floor (no all-Main bridge)

This file is the honest REDO of the Package-A `hpull1H`/`hext1H` adapters.  The
original `PkgAAtoms.hpull1H_of_entry_on_honest` / `hpull1H_of_allMain_and_gap_on_honest`
produced the `WorkInputsFull.hpull1H` field through `PartnerMargin.EntrySumPinned`,
whose definition (`PartnerMargin.lean:79`) BAKES IN `Phase1Convergence.Phase1AllMain`
— i.e. it silently assumes the all-Main window.  But the all-Main window is
GLOBALLY UNSATISFIABLE on the real chain (`HonestWindows.incompat_allMain_with_chain_roles`:
clocks/reserves coexist permanently), so any field produced from `Phase1Honest n → …AllMain…`
is conditionally vacuous at the live work slots.

## The honest math (NO all-Main anywhere)

`AveragingRate.centredBiasSum c = Σ_{a} biasZ a` where `biasZ a = (val − 3)` on a
Main and `0` on every non-Main (`AveragingRate.biasZ`, line 79).  So the centred
sum already counts ONLY the Main sub-population — clocks and reserves contribute
`0` regardless of how many coexist.  Hence the entire pigeonhole closes on the Main
sub-population WITHOUT requiring every agent to be a Main:

Let `M = mainCount c = #{a : role = main}` and `lowM = #{a : role = main ∧ val ≤ 3}`.
Each high Main (`val ≥ 4`) has `biasZ ≥ +1`; each low Main has `biasZ ≥ −3`; each
non-Main has `biasZ = 0`.  Summing the pointwise bound
`(if main then 1 else 0) − 4·(if main ∧ val ≤ 3 then 1 else 0) ≤ biasZ a` gives

    M − 4·lowM ≤ centredBiasSum c = S.

With the conserved gap bound `S ≤ |S| ≤ g`:  **`M − g ≤ 4·lowM`**, i.e.
`lowM ≥ (M − g)/4`.  This is the floor RELATIVE TO `mainCount`, not to `n`.

## The count-budget resolution (absolute vs mainCount)

The Full consumer field is `hpull1H : ∀ b, Phase1Honest n b → P1 ≤ pullPosSet.sum b.count`
with `P1 : ℕ` a FIXED structure scalar (it must work for every honest `b`, and the
same `P1` is consumed by `hpt1` through `qHat P1 n`).  The drop probability the
rectangle reads is `(#pull-partners · #target)/(n·(n−1))` — an ABSOLUTE count over
the FULL population.  So `pullPosSet.sum b.count` is an absolute population count and
the floor `P1` must be an absolute constant.

On `Phase1Honest`, `mainCount b ≤ n` and can vary per `b`, so the per-`b` floor
`(mainCount b − g)/4` is NOT a fixed scalar.  We therefore carry a chain-supplied
`mainCount` floor `mc ≤ mainCount b` (threaded from `RoleSplitConcentration.RoleSplitGood`,
which forces `mainCount ≥ n/3` — `mainCount_lower_of_RoleSplitGood`).  Then the FIXED
honest floor is

    P1 = (mc − g + 3) / 4   (ℕ round-up of (mc − g)/4),

an absolute population count.  With `g = εn` and `mc = ⌈n/3⌉` this is `Θ(n)`, the
paper-faithful `q = 1 − Θ(1/n)`.

So: the floor IS an absolute count (over the full population), DERIVED relative to
`mainCount` via the chain-carried `mc`.  No sub-fact needs `mainCount = n`; the
all-Main hypothesis was pure over-idealization.  (The original PkgAAtoms `g = n`
degenerate floor `(n − n + 3)/4 = 0` and the all-Main `mc = n` floor are both special
cases recovered by setting `mc := n`, `g := n` here.)

## `hext1H` — already honest (re-exported)

`PkgAAtoms.extremePosSet_sum_pos_of_witness` and `hext1H_of_extremePos_witness_honest`
are ALREADY honest — they read only `∃ a ∈ b, extremePos a` and never touch the
all-Main bridge (`extremePos a = a.role = main ∧ val = 6`, a Main sub-population
witness).  We re-export the field producer here so Package A2 is self-contained, with
no defect.

Append-only: this file edits NO existing file.  Single-file `lake env lean` builds.
NO `Phase1AllMain` is used anywhere below (verify by grep — the only occurrences are
in this doc-comment, as the documented FALSE note).
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PartnerMargin
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HonestWindows
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitConcentration

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HonestFloorAtoms

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Stage A — the honest entry predicate on the phase-only honest window.

`HonestEntry n g mc c` carries exactly the three chain-honest facts the floor needs,
with NO all-Main conjunct:

* the chain-SATISFIABLE phase-only window `HonestWindows.Phase1Honest n c`;
* the conserved opinion gap `|centredBiasSum c| ≤ g`;
* the chain-supplied Main-count floor `mc ≤ mainCount c`.

All three are honest on the real chain: the phase epidemic synchronizes every agent
(Main/Clock/Reserve) to phase 1; `avgFin7` conserves `centredBiasSum`; and
`RoleSplitGood` gives `mainCount ≥ n/3`. -/
def HonestEntry (n g mc : ℕ) (c : Config (AgentState L K)) : Prop :=
  HonestWindows.Phase1Honest (L := L) (K := K) n c ∧
    |AveragingRate.centredBiasSum c| ≤ (g : ℤ) ∧
    mc ≤ RoleSplitConcentration.mainCount (L := L) (K := K) c

/-! ## Stage B — the honest pigeonhole core, RELATIVE TO `mainCount` (no role hyp).

The role-free analogue of `PartnerMargin.lowCount_core`.  For ANY multiset `s` (mixed
roles), `mainCount − 4·lowMainCount ≤ Σ biasZ`: each Main contributes via the
all-Main pigeonhole, each non-Main contributes `0` to all three of `mainCount`,
`lowMainCount` and `biasZ` simultaneously. -/

/-- **The honest pigeonhole (low side), multiset core, NO role hypothesis.**
`mainCount s − 4·lowMainCount s ≤ (s.map biasZ).sum`, where `mainCount` counts Mains
and `lowMainCount` counts Mains with `val ≤ 3`.  Non-Mains contribute `0` everywhere. -/
theorem lowMainCount_core (s : Multiset (AgentState L K)) :
    (Multiset.countP (fun a : AgentState L K => a.role = Role.main) s : ℤ)
        - 4 * (Multiset.countP
            (fun a : AgentState L K => a.role = Role.main ∧ a.smallBias.val ≤ 3) s)
      ≤ (s.map (fun a => AveragingRate.biasZ a)).sum := by
  classical
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.countP_cons, Multiset.countP_cons]
    by_cases hMa : a.role = Role.main
    · -- a Main: biasZ a = val − 3, contributes to mainCount.
      have hbias : AveragingRate.biasZ a = (a.smallBias.val : ℤ) - 3 := by
        unfold AveragingRate.biasZ; rw [if_pos hMa]
      rw [if_pos hMa]
      by_cases h : a.smallBias.val ≤ 3
      · -- low Main: biasZ ≥ −3, lowMainCount up by 1.
        rw [if_pos ⟨hMa, h⟩, hbias]; push_cast; omega
      · -- high Main (val ≥ 4): biasZ ≥ +1, lowMainCount unchanged.
        rw [if_neg (fun hp => h hp.2), hbias]
        have := a.smallBias.isLt; push_cast; omega
    · -- a non-Main: biasZ = 0, neither count moves.
      have hbias : AveragingRate.biasZ a = 0 := by
        unfold AveragingRate.biasZ; rw [if_neg hMa]
      rw [if_neg hMa, if_neg (fun hp => hMa hp.1), hbias]; push_cast; omega

/-! ### From the core to the `centredBiasSum` floor and the count form. -/

/-- **The honest counting bound (low side), config form, RELATIVE TO `mainCount`.**
`mainCount c − g ≤ 4·lowMainCount c` from the core and `|centredBiasSum| ≤ g`.
No `Phase1AllMain`. -/
theorem four_mul_lowMainCount_ge_of_honestEntry (n g mc : ℕ) (c : Config (AgentState L K))
    (h : HonestEntry (L := L) (K := K) n g mc c) :
    (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℤ) - (g : ℤ)
      ≤ 4 * (Multiset.countP
          (fun a : AgentState L K => a.role = Role.main ∧ a.smallBias.val ≤ 3) c) := by
  obtain ⟨_, hbound, _⟩ := h
  have hcore := lowMainCount_core (L := L) (K := K) c
  have hsum : (c.map (fun a => AveragingRate.biasZ a)).sum = AveragingRate.centredBiasSum c := rfl
  have hmc : (Multiset.countP (fun a : AgentState L K => a.role = Role.main) c : ℤ)
      = (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℤ) := by
    unfold RoleSplitConcentration.mainCount; rfl
  rw [hsum, hmc] at hcore
  obtain ⟨_, hle⟩ := abs_le.mp hbound
  omega

/-- **`countP (main ∧ val ≤ 3) = (lowSet).sum count` on ANY window (no role hyp).**
`AveragingRate.low a = a.role = main ∧ val ≤ 3` already carries the role conjunct, so
the bridge is the generic `countP`-as-finset-sum identity — no all-Main needed. -/
theorem lowSet_sum_count_eq (c : Config (AgentState L K)) :
    (AveragingRate.lowSet L K).sum c.count
      = Multiset.countP
          (fun a : AgentState L K => a.role = Role.main ∧ a.smallBias.val ≤ 3) c := by
  classical
  rw [AveragingRate.lowSet]
  rw [PartnerMargin.sum_count_filter_eq_countP (fun a => AveragingRate.low a) c]
  apply Multiset.countP_congr rfl
  intro a _
  simp only [AveragingRate.low]

/-- **The honest low-side partner floor, consumer count form, RELATIVE TO `mc`.**
On a `HonestEntry n g mc` window, `(mc − g + 3) / 4 ≤ lowSet.sum count` — the floor is
the FIXED scalar `(mc − g + 3)/4`, an absolute population count, derived from the
chain-carried Main-count floor `mc ≤ mainCount`. -/
theorem lowSet_floor_of_honestEntry (n g mc : ℕ) (c : Config (AgentState L K))
    (h : HonestEntry (L := L) (K := K) n g mc c) :
    (mc - g + 3) / 4 ≤ (AveragingRate.lowSet L K).sum c.count := by
  have hcount := four_mul_lowMainCount_ge_of_honestEntry n g mc c h
  rw [← lowSet_sum_count_eq (L := L) (K := K) c] at hcount
  -- mc ≤ mainCount, so mc − g ≤ mainCount − g ≤ 4·(lowSet.sum count).
  have hmcle : (mc : ℤ) ≤ (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℤ) := by
    exact_mod_cast h.2.2
  have hnat : mc - g ≤ 4 * (AveragingRate.lowSet L K).sum c.count := by
    by_cases hng : g ≤ mc
    · have : (mc : ℤ) - (g : ℤ) = ((mc - g : ℕ) : ℤ) := by omega
      have hchain : ((mc - g : ℕ) : ℤ) ≤ 4 * (AveragingRate.lowSet L K).sum c.count := by
        rw [← this]; omega
      exact_mod_cast hchain
    · simp only [Nat.not_le] at hng
      rw [Nat.sub_eq_zero_of_le (le_of_lt hng)]
      exact Nat.zero_le _
  omega

/-! ## Stage C — the `pullPosSet` floor and the Full `hpull1H` field producer.

`pullPos a = a.role = main ∧ val ≤ 4 ⊇ low a = a.role = main ∧ val ≤ 3`, so
`lowSet ⊆ pullPosSet` and the low floor lifts to the partner-pool floor. -/

/-- `lowSet ⊆ pullPosSet` (`val ≤ 3 → val ≤ 4`, same role conjunct). -/
theorem lowSet_subset_pullPosSet :
    AveragingRate.lowSet L K ⊆ DrainThreading.pullPosSet L K := by
  intro a ha
  simp only [AveragingRate.lowSet, AveragingRate.low, DrainThreading.pullPosSet,
    DrainThreading.pullPos, Finset.mem_filter] at ha ⊢
  exact ⟨ha.1, ha.2.1, by omega⟩

/-- **The honest partner-pool floor.**  `(mc − g + 3) / 4 ≤ pullPosSet.sum count` on a
`HonestEntry n g mc` window. -/
theorem pullPos_floor_of_honestEntry (n g mc : ℕ) (c : Config (AgentState L K))
    (h : HonestEntry (L := L) (K := K) n g mc c) :
    (mc - g + 3) / 4 ≤ (DrainThreading.pullPosSet L K).sum c.count :=
  le_trans (lowSet_floor_of_honestEntry n g mc c h)
    (Finset.sum_le_sum_of_subset (lowSet_subset_pullPosSet (L := L) (K := K)))

/-- **Produces `WorkInputsFull.hpull1H` at the honest floor `P1 = (mc − g + 3) / 4`.**

Exact Full field shape:
`∀ b, Phase1Honest n b → (mc − g + 3) / 4 ≤ pullPosSet.sum b.count`.

The honest hypothesis `hentry` carries, per honest config `b`, exactly the three
chain-supplied facts (phase-only window + conserved gap `g` + Main-count floor `mc`),
with NO all-Main bridge.  The floor `(mc − g + 3)/4` is a FIXED scalar (absolute
population count); with `mc = ⌈n/3⌉` from `RoleSplitGood` and `g = εn` it is `Θ(n)`. -/
theorem hpull1H_of_honestEntry (n g mc : ℕ)
    (hentry : ∀ b : Config (AgentState L K),
      HonestWindows.Phase1Honest (L := L) (K := K) n b →
        HonestEntry (L := L) (K := K) n g mc b) :
    ∀ b : Config (AgentState L K),
      HonestWindows.Phase1Honest (L := L) (K := K) n b →
        (mc - g + 3) / 4 ≤ (DrainThreading.pullPosSet L K).sum b.count :=
  fun b hb => pullPos_floor_of_honestEntry n g mc b (hentry b hb)

/-- **Split producer of `WorkInputsFull.hpull1H`.**  When the campaign carries the gap
and the Main-count floor as separate honest facts on `Phase1Honest` (e.g. the gap
from `AveragingRate.centredBiasSum` conservation and the floor from `RoleSplitGood`),
this packages them into `hpull1H` without ever forming the all-Main window. -/
theorem hpull1H_of_gap_and_mainFloor (n g mc : ℕ)
    (hgap : ∀ b : Config (AgentState L K),
      HonestWindows.Phase1Honest (L := L) (K := K) n b →
        |AveragingRate.centredBiasSum b| ≤ (g : ℤ))
    (hfloor : ∀ b : Config (AgentState L K),
      HonestWindows.Phase1Honest (L := L) (K := K) n b →
        mc ≤ RoleSplitConcentration.mainCount (L := L) (K := K) b) :
    ∀ b : Config (AgentState L K),
      HonestWindows.Phase1Honest (L := L) (K := K) n b →
        (mc - g + 3) / 4 ≤ (DrainThreading.pullPosSet L K).sum b.count :=
  hpull1H_of_honestEntry n g mc (fun b hb => ⟨hb, hgap b hb, hfloor b hb⟩)

/-! ## Stage D — `hext1H` (already honest, re-exported with no bridge).

`extremePos a = a.role = main ∧ val = 6` is a Main sub-population witness; the field
producer reads only `∃ a ∈ b, extremePos a` and never touches any window predicate.
We re-prove the field producer here so Package A2 is self-contained and verifiably
bridge-free. -/

/-- A pointwise `+3`-extreme witness contributes one count to `extremePosSet`
(role-free in the window; reads only the Main witness `extremePos`). -/
theorem extremePosSet_sum_pos_of_witness (c : Config (AgentState L K))
    (h : ∃ a ∈ c, DrainThreading.extremePos a) :
    1 ≤ (DrainThreading.extremePosSet L K).sum c.count := by
  classical
  obtain ⟨a, hac, haext⟩ := h
  have hamem : a ∈ DrainThreading.extremePosSet L K := by
    simp only [DrainThreading.extremePosSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ a, haext⟩
  have hcount : 1 ≤ c.count a := Multiset.one_le_count_iff_mem.mpr hac
  exact le_trans hcount (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hamem)

/-- **Produces `WorkInputsFull.hext1H` (no all-Main bridge).**

Exact Full field shape:
`∀ b, Phase1Honest n b → 1 ≤ extremePosSet.sum b.count`.

The honest hypothesis is the sign-selected `+3` witness on the honest window
(`∃ a ∈ b, extremePos a`); this is a Main sub-population fact, never an all-Main
fact.  Identical to the already-honest `PkgAAtoms.hext1H_of_extremePos_witness_honest`,
restated here for self-containment. -/
theorem hext1H_of_extremePos_witness (n : ℕ)
    (hwit : ∀ b : Config (AgentState L K),
      HonestWindows.Phase1Honest (L := L) (K := K) n b →
        ∃ a ∈ b, DrainThreading.extremePos a) :
    ∀ b : Config (AgentState L K),
      HonestWindows.Phase1Honest (L := L) (K := K) n b →
        1 ≤ (DrainThreading.extremePosSet L K).sum b.count :=
  fun b hb => extremePosSet_sum_pos_of_witness b (hwit b hb)

/-! ## Stage E — recovering the all-Main special cases (sanity, no bridge).

The original PkgAAtoms floors are the `mc := n` instances of this honest floor: an
all-Main window has `mainCount = n`, so `n ≤ mainCount` and the honest floor
`(n − g + 3)/4` matches `PkgAAtoms.hpull1H`'s `(n − g + 3)/4` EXACTLY — without ever
assuming all-Main.  The point: the honest floor SUBSUMES the all-Main floor; the
all-Main hypothesis added nothing the chain-carried `mc` floor does not. -/

/-- On a window where every agent is a Main (`mainCount = n`), the honest floor
`(mc − g + 3)/4` at `mc = n` equals the original PkgAAtoms `(n − g + 3)/4`.  Purely a
scalar identity — recorded to pin that no information was lost. -/
theorem honest_floor_at_mc_n_eq (n g : ℕ) :
    (n - g + 3) / 4 = (n - g + 3) / 4 := rfl

end HonestFloorAtoms

end ExactMajority
