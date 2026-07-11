/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Θ(n) partner-margin floor — discharging the carried `P'` atom of `AveragingRate.lean`

`AveragingRate.lean` lands the per-level second-moment drain rate `q m = 1 − ofReal(P/(n(n−1)))`
(`secondMomentN_hdrop_of_struct_high/_low`) but carries exactly one quantitative input: the
**partner margin** `P`.  With `P = 1` (a single far witness) the rate is `1 − 1/(n(n−1))` and the
horizon is the crude `Θ(n²·log n)`; the paper-faithful `Θ(n·log n)` of Lemma 5.3 needs `P = Θ(n)`.
This file derives that `Θ(n)` floor HONESTLY from the conserved SUM INVARIANT of `AveragingRate`
(`SumPinned`: `|centredBiasSum| ≤ n`, `K`-closed, proven), no `[45]` import.

## The honest derivation (the pigeonhole that actually closes)

The naive contradiction "`#low < δn ⟹ sum > n`" does NOT close at the granularity `|S| ≤ n`: every
Main has centred value in `[−3,3]`, and `S ≥ (n − #low)·1 + #low·(−3) = n − 4·#low`, which is `≤ n`
with NO contradiction (a briefing error caught today).  The genuine derivation needs the HONEST
entry sum bound — sharper than `|S| ≤ n`.

The Doty Phase-1 entry encodes each Main's `±1` opinion as `smallBias.val ∈ {2,4}` (centred `±1`),
so `S = centredBiasSum = (#plus) − (#minus) = gap`, the INITIAL OPINION GAP, conserved by `avgFin7`
(`AveragingRate.centredBiasSum_stepOrSelf_eq`).  At a contested entry the gap is small: `|S| ≤ g`
with `g = εn` (a sub-linear or small-constant-fraction margin).  THEN the pigeonhole closes:

Let `H = #{Main : val ≥ 4}` (the high side, centred `≥ +1`) and `lowCount = #{Main : val ≤ 3}`
(centred `≤ 0`); on the window every agent is a Main so `H + lowCount = n`.  Each high agent has
centred value `≥ +1`, each low agent `≥ −3`, so

  `S ≥ 1·H + (−3)·lowCount = H − 3·lowCount = (n − lowCount) − 3·lowCount = n − 4·lowCount`.

With `S ≤ |S| ≤ g`: `n − 4·lowCount ≤ g`, i.e. **`n − g ≤ 4·lowCount`** (division-free), giving
`lowCount ≥ (n − g)/4 = (1 − ε)·n/4 = Θ(n)` — the partner floor.  The mirror (`g`-bounded entry,
each Main centred `≤ +3`/`≥ −1`) gives the high-side floor `n − g ≤ 4·highCount`.

## What this file delivers

* **Stage A** — the honest entry sum bound: `EntrySumPinned n g c` (`Phase1AllMain ∧ |S| ≤ g`),
  `K`-closed (`EntrySumPinned_support_closed` / `invClosed_entrySumPinned`), generalising
  `AveragingRate.SumPinned` (the `g = n` case) to the honest entry gap `g`.
* **Stage B** — the counting lemma: `four_mul_lowCount_ge_of_entry` (ℤ, division-free)
  `(n : ℤ) − g ≤ 4 · lowCount`, and the mirror `four_mul_highCount_ge_of_entry`; converted to the
  consumer's count form `lowSet_floor_of_entry` / `highSet_floor_of_entry`
  (`(n − g + 3) / 4 ≤ (lowSet).sum count`).
* **Stage C** — instantiate `AveragingRate`'s `P'` slot: `secondMomentN_hdrop_of_entry_high/_low`
  delivers `hdrop` at the derived `P = (n − g)/4`, so the rate is `q m = 1 − ofReal(P/(n(n−1)))`
  with `P = Θ(n)`, the paper-faithful `q = 1 − Θ(1/n)`.
* **Stage D** — the strongest hypothesis-free floor surface `phase1_pullPos_floor_whp_of_entry`:
  the only inputs are the protocol window `Phase1AllMain`, the honest entry gap `g`, and the rate
  family `q` discharged by the structural `hdrop`.

NEW file (append-only); no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.AveragingRate
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseFloors

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace PartnerMargin

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Stage A — the honest entry sum bound.

`AveragingRate.SumPinned` pins `|centredBiasSum| ≤ n`; the honest Doty Phase-1 entry pins the
SHARPER `|centredBiasSum| ≤ g` where `g` is the initial opinion gap (each Main encodes `±1`, so
`S = #plus − #minus = gap`).  We carry `g` as an explicit conserved quantity — the same atom
`AveragingRate.SumPinned` carries, only at the honest entry value rather than the trivial `g = n`. -/

/-- **The honest entry predicate.**  The centred Main bias sum is bounded by the initial opinion
gap `g` (true at the Doty Phase-1 entry: each Main encodes a `±1` opinion, so the centred sum is the
signed opinion difference `#plus − #minus`, bounded by `g`).  Conserved by `avgFin7`. -/
def EntrySumPinned (n g : ℕ) (c : Config (AgentState L K)) : Prop :=
  Phase1Convergence.Phase1AllMain n c ∧ |AveragingRate.centredBiasSum c| ≤ (g : ℤ)

/-- `EntrySumPinned` refines `AveragingRate.SumPinned` whenever the honest gap is sub-`n`. -/
theorem sumPinned_of_entrySumPinned (n g : ℕ) (c : Config (AgentState L K))
    (hg : g ≤ n) (h : EntrySumPinned n g c) : AveragingRate.SumPinned n c :=
  ⟨h.1, le_trans h.2 (by exact_mod_cast hg)⟩

/-- `EntrySumPinned` is one-step-support closed: the window is closed and the sum is conserved. -/
theorem EntrySumPinned_support_closed (n g : ℕ) (c c' : Config (AgentState L K))
    (hw : EntrySumPinned n g c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    EntrySumPinned n g c' := by
  obtain ⟨hwin, hbound⟩ := hw
  refine ⟨Phase1Convergence.Phase1AllMain_support_closed n c c' hwin hc', ?_⟩
  rw [AveragingRate.centredBiasSum_eq_on_support n (AveragingRate.centredBiasSum c) c c' hwin rfl hc']
  exact hbound

/-- Packaged as the engine's `InvClosed` predicate for `EntrySumPinned`. -/
theorem invClosed_entrySumPinned (n g : ℕ) :
    OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => EntrySumPinned (L := L) (K := K) n g c) := by
  intro c hInv
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | ¬ EntrySumPinned (L := L) (K := K) n g x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  exact hx (EntrySumPinned_support_closed n g c x hInv hsupp)

/-! ## Stage B — the counting lemma (the honest pigeonhole).

`S = centredBiasSum c ≥ n − 4·lowCount` where `lowCount = #{Main : val ≤ 3}`, via a pointwise
lower bound `4·[¬low] − 3 ≤ biasZ` on every Main, summed over the all-Main window.  With `S ≤ g`
this gives `n − g ≤ 4·lowCount`. -/

/-- **Pointwise bias lower bound (low side).**  On a Main, `4·[val ≥ 4] − 3 ≤ biasZ`:
a low Main (`val ≤ 3`) has `biasZ = val − 3 ≥ −3 = 4·0 − 3`; a high Main (`val ≥ 4`) has
`biasZ = val − 3 ≥ 1 = 4·1 − 3`. -/
theorem biasZ_ge_low (a : AgentState L K) (hM : a.role = Role.main) :
    4 * (if 4 ≤ a.smallBias.val then (1 : ℤ) else 0) - 3 ≤ AveragingRate.biasZ a := by
  unfold AveragingRate.biasZ
  rw [if_pos hM]
  by_cases h : 4 ≤ a.smallBias.val
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- **Pointwise bias upper bound (high side).**  On a Main, `biasZ ≤ 4·[val ≤ 2] · (−1) + 3`,
equivalently `biasZ ≤ 3 − 4·[val ≤ 2]`: a high Main (`val ≥ 3`) has `biasZ = val − 3 ≤ 3`; a low
Main (`val ≤ 2`) has `biasZ = val − 3 ≤ −1 = 3 − 4`. -/
theorem biasZ_le_high (a : AgentState L K) (hM : a.role = Role.main) :
    AveragingRate.biasZ a ≤ 3 - 4 * (if a.smallBias.val ≤ 2 then (1 : ℤ) else 0) := by
  unfold AveragingRate.biasZ
  rw [if_pos hM]
  by_cases h : a.smallBias.val ≤ 2
  · rw [if_pos h]; omega
  · rw [if_neg h]; have := a.smallBias.isLt; omega

/-- **The honest pigeonhole (low side), multiset core.**  For any all-Main multiset `s`, the
centred bias sum is `≥ card − 4·lowCount`: every Main contributes `≥ −3`, and high Mains (`val ≥ 4`,
NOT counted in `lowCount`) contribute `≥ +1`, so each of the `card − lowCount` high Mains adds `≥ 4`
above the `−3` floor.  Proven by direct multiset induction (no map-sub/scalar rewrites). -/
theorem lowCount_core (s : Multiset (AgentState L K))
    (hM : ∀ a ∈ s, a.role = Role.main) :
    (Multiset.card s : ℤ) - 4 * (Multiset.countP (fun a : AgentState L K => a.smallBias.val ≤ 3) s)
      ≤ (s.map (fun a => AveragingRate.biasZ a)).sum := by
  classical
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have hMs : ∀ b ∈ s, b.role = Role.main := fun b hb => hM b (Multiset.mem_cons_of_mem hb)
    have hMa : a.role = Role.main := hM a (Multiset.mem_cons_self a s)
    have hih := ih hMs
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Multiset.countP_cons]
    have hbias : AveragingRate.biasZ a = (a.smallBias.val : ℤ) - 3 := by
      unfold AveragingRate.biasZ; rw [if_pos hMa]
    by_cases h : a.smallBias.val ≤ 3
    · rw [if_pos h]
      -- a low Main: biasZ a = val − 3 ≥ −3, and lowCount goes up by 1.
      rw [hbias]; push_cast; omega
    · rw [if_neg h]
      -- a high Main (val ≥ 4): biasZ a = val − 3 ≥ +1, lowCount unchanged.
      rw [hbias]; have := a.smallBias.isLt; push_cast; omega

/-- **The mirror pigeonhole (high side), multiset core.**  `card − 4·highCount ≤ −S`, lower-bounding
`highCount = #{Main : val ≥ 3}`: per Main `1 − 4·[val≥3] ≤ −biasZ = 3 − val` (a high Main `val ≥ 3`
has `3 − val ≤ 0` so `−3 ≤ ·` from `val ≤ 6`; a low Main `val ≤ 2` has `3 − val ≥ 1`).  Summed, this
gives `n − 4·#{val≥3} ≤ −S`, so `−S ≥ n − 4·highCount`; with `−S ≤ g` (the entry bound applied to
`−S = |S| ≥ −g`... ) it yields the high-side floor.  Note this is NOT the negation of `lowCount_core`:
the far-LOW witness needs `val ≥ 3` partners, whose count is large precisely when `−S` is small, i.e.
`S ≥ −g` — the lower half of `|S| ≤ g`. -/
theorem highCount_core (s : Multiset (AgentState L K))
    (hM : ∀ a ∈ s, a.role = Role.main) :
    (Multiset.card s : ℤ) - 4 * (Multiset.countP (fun a : AgentState L K => 3 ≤ a.smallBias.val) s)
      ≤ -(s.map (fun a => AveragingRate.biasZ a)).sum := by
  classical
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have hMs : ∀ b ∈ s, b.role = Role.main := fun b hb => hM b (Multiset.mem_cons_of_mem hb)
    have hMa : a.role = Role.main := hM a (Multiset.mem_cons_self a s)
    have hih := ih hMs
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Multiset.countP_cons]
    have hbias : AveragingRate.biasZ a = (a.smallBias.val : ℤ) - 3 := by
      unfold AveragingRate.biasZ; rw [if_pos hMa]
    by_cases h : 3 ≤ a.smallBias.val
    · rw [if_pos h]
      -- a high Main (val ≥ 3): −biasZ = 3 − val ≤ 0, highCount up by 1; need −3 ≤ 3 − val (val ≤ 6).
      rw [hbias]; have := a.smallBias.isLt; push_cast; omega
    · rw [if_neg h]
      -- a low Main (val ≤ 2): −biasZ = 3 − val ≥ 1, highCount unchanged.
      rw [hbias]; push_cast; omega

/-! ### From the multiset cores to the `centredBiasSum` bound and the count floor.

Specialise the cores to a config (`Multiset.card c = c.card`, `(c.map biasZ).sum = centredBiasSum c`),
combine with `EntrySumPinned`'s `|S| ≤ g`, and convert the resulting `countP` floor into the
consumer's `Finset.sum count` shape. -/

/-- The `countP`-as-finset-sum bridge for `AgentState L K` (the generic argument used by
`EarlyDripMarked.sum_count_filter_eq_countP` for `MarkedAgent`, reproduced here for `AgentState`). -/
theorem sum_count_filter_eq_countP (p : AgentState L K → Prop) [DecidablePred p]
    (c : Config (AgentState L K)) :
    (∑ a ∈ Finset.univ.filter p, c.count a) = Multiset.countP (fun a => p a) c := by
  classical
  calc (∑ a ∈ Finset.univ.filter p, c.count a)
      = ∑ a : AgentState L K, if p a then c.count a else 0 := Finset.sum_filter _ _
    _ = ∑ a : AgentState L K, (c.filter p).count a := by
        refine Finset.sum_congr rfl (fun a _ => ?_)
        show _ = Multiset.count a (c.filter p)
        rw [Multiset.count_filter]; rfl
    _ = (c.filter p).card :=
        Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)
    _ = Multiset.countP (fun a => p a) c := (Multiset.countP_eq_card_filter _ _).symm

/-- **The honest counting bound (low side), config form.**  `n − g ≤ 4·#{Main : val ≤ 3}` from
the multiset core and `EntrySumPinned`'s `|centredBiasSum| ≤ g`. -/
theorem four_mul_lowCount_ge_of_entry (n g : ℕ) (c : Config (AgentState L K))
    (h : EntrySumPinned n g c) :
    (n : ℤ) - (g : ℤ)
      ≤ 4 * (Multiset.countP (fun a : AgentState L K => a.smallBias.val ≤ 3) c) := by
  obtain ⟨⟨hcard, hph⟩, hbound⟩ := h
  have hM : ∀ a ∈ c, a.role = Role.main := fun a ha => (hph a ha).2
  have hcore := lowCount_core c hM
  have hsum : (c.map (fun a => AveragingRate.biasZ a)).sum = AveragingRate.centredBiasSum c := rfl
  have hcardZ : (Multiset.card c : ℤ) = (n : ℤ) := by exact_mod_cast hcard
  rw [hsum, hcardZ] at hcore
  -- centredBiasSum ≤ |centredBiasSum| ≤ g
  obtain ⟨_, hle⟩ := abs_le.mp hbound
  omega

/-- **The honest counting bound (high side), config form.**  `n − g ≤ 4·#{Main : val ≥ 3}` from
the mirror core and `−g ≤ centredBiasSum` (`−|S| ≤ S`). -/
theorem four_mul_highCount_ge_of_entry (n g : ℕ) (c : Config (AgentState L K))
    (h : EntrySumPinned n g c) :
    (n : ℤ) - (g : ℤ)
      ≤ 4 * (Multiset.countP (fun a : AgentState L K => 3 ≤ a.smallBias.val) c) := by
  obtain ⟨⟨hcard, hph⟩, hbound⟩ := h
  have hM : ∀ a ∈ c, a.role = Role.main := fun a ha => (hph a ha).2
  have hcore := highCount_core c hM
  have hsum : (c.map (fun a => AveragingRate.biasZ a)).sum = AveragingRate.centredBiasSum c := rfl
  have hcardZ : (Multiset.card c : ℤ) = (n : ℤ) := by exact_mod_cast hcard
  rw [hsum, hcardZ] at hcore
  -- core: n − 4·highCount ≤ −S; and −g ≤ S (from |S| ≤ g).
  obtain ⟨hge, _⟩ := abs_le.mp hbound
  omega

/-- **`countP (val ≤ 3) = (lowSet).sum count` on the all-Main window.**  Every agent is a Main, so
the role conjunct in `low` is free, and `countP (low) = #filtered = (lowSet).sum count`. -/
theorem lowSet_sum_count_eq_countP (n g : ℕ) (c : Config (AgentState L K))
    (h : EntrySumPinned n g c) :
    (AveragingRate.lowSet L K).sum c.count
      = Multiset.countP (fun a : AgentState L K => a.smallBias.val ≤ 3) c := by
  obtain ⟨⟨_, hph⟩, _⟩ := h
  rw [AveragingRate.lowSet]
  rw [sum_count_filter_eq_countP (fun a => AveragingRate.low a) c]
  -- countP low c = countP (val ≤ 3) c, since every member is a Main.
  apply Multiset.countP_congr rfl
  intro a ha
  have hM : a.role = Role.main := (hph a ha).2
  simp only [AveragingRate.low, hM, true_and]

/-- **`countP (val ≥ 3) = (highSet).sum count` on the all-Main window.** -/
theorem highSet_sum_count_eq_countP (n g : ℕ) (c : Config (AgentState L K))
    (h : EntrySumPinned n g c) :
    (AveragingRate.highSet L K).sum c.count
      = Multiset.countP (fun a : AgentState L K => 3 ≤ a.smallBias.val) c := by
  obtain ⟨⟨_, hph⟩, _⟩ := h
  rw [AveragingRate.highSet]
  rw [sum_count_filter_eq_countP (fun a => AveragingRate.high a) c]
  apply Multiset.countP_congr rfl
  intro a ha
  have hM : a.role = Role.main := (hph a ha).2
  simp only [AveragingRate.high, hM, true_and]

/-- **The low-side partner floor, consumer count form.**  On an `EntrySumPinned n g` window, the
low-side partner pool has at least `(n − g + 3) / 4` Mains (ℕ-division round-up of `(n−g)/4`):
`4·(lowSet.sum count) ≥ n − g`. -/
theorem lowSet_floor_of_entry (n g : ℕ) (c : Config (AgentState L K))
    (h : EntrySumPinned n g c) :
    (n - g + 3) / 4 ≤ (AveragingRate.lowSet L K).sum c.count := by
  have hcount := four_mul_lowCount_ge_of_entry n g c h
  rw [← lowSet_sum_count_eq_countP n g c h] at hcount
  -- (n:ℤ) − g ≤ 4 · (lowSet.sum count); push to ℕ and round up the division.
  have hnat : n - g ≤ 4 * (AveragingRate.lowSet L K).sum c.count := by
    by_cases hng : g ≤ n
    · have : (n : ℤ) - (g : ℤ) = ((n - g : ℕ) : ℤ) := by omega
      rw [this] at hcount
      exact_mod_cast hcount
    · simp only [Nat.not_le] at hng
      rw [Nat.sub_eq_zero_of_le (le_of_lt hng)]
      exact Nat.zero_le _
  omega

/-- **The high-side partner floor, consumer count form.** -/
theorem highSet_floor_of_entry (n g : ℕ) (c : Config (AgentState L K))
    (h : EntrySumPinned n g c) :
    (n - g + 3) / 4 ≤ (AveragingRate.highSet L K).sum c.count := by
  have hcount := four_mul_highCount_ge_of_entry n g c h
  rw [← highSet_sum_count_eq_countP n g c h] at hcount
  have hnat : n - g ≤ 4 * (AveragingRate.highSet L K).sum c.count := by
    by_cases hng : g ≤ n
    · have : (n : ℤ) - (g : ℤ) = ((n - g : ℕ) : ℤ) := by omega
      rw [this] at hcount
      exact_mod_cast hcount
    · simp only [Nat.not_le] at hng
      rw [Nat.sub_eq_zero_of_le (le_of_lt hng)]
      exact Nat.zero_le _
  omega

/-! ## Stage C — instantiating `AveragingRate`'s `P'` slot with the derived `Θ(n)` floor.

The carried partner margin `P` of `AveragingRate.secondMomentN_hdrop_of_struct_high/_low` is now
`(n − g + 3) / 4 = Θ(n)` (a constant fraction of Mains, since `g = εn` with `ε < 1`).  We instantiate
the far-high (resp. far-low) rectangle floor with `P = (n − g + 3) / 4`, leaving only the far witness
`1 ≤ farHighSet.sum count` (resp. `farLowSet`) as the honest config-dependent hypothesis — exactly
the side-determination the structure lemma `farExists_of_secondMoment_gt_n` leaves open (it supplies
*a* far Main; *which* side it sits on is the per-config datum the rectangle pairs against the
opposite-side partner floor). -/

/-- **The far-high `hdrop` at the derived `Θ(n)` partner margin.**  On an `EntrySumPinned n g`
window with a far-high witness, the level-`m` second-moment failure mass is
`≤ 1 − ofReal((⌈(n−g)/4⌉) / (n(n−1)))` — the honest `q = 1 − Θ(1/n)` when `g = εn`. -/
theorem secondMomentN_hdrop_of_entry_high (n g : ℕ) (hn : 2 ≤ n) (m : ℕ)
    (b : Config (AgentState L K)) (h : EntrySumPinned n g b)
    (hbm : AveragingCollapse.secondMomentN b = m)
    (hfar : 1 ≤ (AveragingRate.farHighSet L K).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (fun c => AveragingCollapse.secondMomentN c) m)ᶜ
      ≤ 1 - ENNReal.ofReal
          ((((n - g + 3) / 4 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  AveragingRate.secondMomentN_hdrop_of_struct_high n m hn b h.1 hbm ((n - g + 3) / 4)
    hfar (lowSet_floor_of_entry n g b h)

/-- **The far-low `hdrop` at the derived `Θ(n)` partner margin.** -/
theorem secondMomentN_hdrop_of_entry_low (n g : ℕ) (hn : 2 ≤ n) (m : ℕ)
    (b : Config (AgentState L K)) (h : EntrySumPinned n g b)
    (hbm : AveragingCollapse.secondMomentN b = m)
    (hfar : 1 ≤ (AveragingRate.farLowSet L K).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (fun c => AveragingCollapse.secondMomentN c) m)ᶜ
      ≤ 1 - ENNReal.ofReal
          ((((n - g + 3) / 4 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  AveragingRate.secondMomentN_hdrop_of_struct_low n m hn b h.1 hbm ((n - g + 3) / 4)
    hfar (highSet_floor_of_entry n g b h)

/-! ## Stage D — the strongest hypothesis-free Phase-1 floor surface.

`phase1_pullPos_floor_whp_of_entry` instantiates `AveragingRate.phase1_pullPos_floor_whp_of_struct`
with the derived partner margin `P = (n − g + 3) / 4`.  The only remaining inputs are the protocol
window `Phase1AllMain`, the honest entry gap `g`, and the rate family `q` — the latter discharged at
every level `m > n` (the `{2,3,4}` ceiling) by `secondMomentN_hdrop_of_entry_high/_low`, with the far
witness supplied by `AveragingRate.farExists_of_secondMoment_gt_n` and the partner floor by this file.

### The Θ(n log n) horizon arithmetic (documented).

With `P = (n − g + 3)/4 = Θ(n)` (taking `g = εn`, `ε < 1`, gives `P ≥ (1−ε)n/4`), the per-level rate
is `q m = 1 − ofReal(P/(n(n−1))) = 1 − Θ(1/n)`.  The consumer `phase1_pullPos_floor_whp` reads the
floor at level `m = 4(n − P) + 1`; the level-tail gives failure mass `≤ (q m)^t`.  Then

  `(q m)^t = (1 − Θ(1/n))^t ≤ exp(−Θ(t/n))`,

so `t = Θ(n · log n)` drives the failure to `O(1/n²)` — the paper-faithful `O(n log n)` horizon of
Lemma 5.3 (reference [45], Mocquard et al. Corollary 1), now derived honestly from `avgFin7`'s frozen
second-moment contraction rather than imported.  The crude single-witness regime (`P = 1`,
`q = 1 − 1/(n(n−1))`, `t = Θ(n²·log n)`) is the `g = n` degenerate case `P = ⌈0/4⌉`. -/

/-- **The hypothesis-free Phase-1 saturated-side floor at the derived `Θ(n)` partner margin.**
Instantiates `AveragingRate.phase1_pullPos_floor_whp_of_struct` with `P = (n − g + 3) / 4`: with the
rate family `q` (discharged structurally by `secondMomentN_hdrop_of_entry_high/_low`) and the entry
budget `secondMomentN c ≤ 4(n − P) + 1`, the floor `P ≤ pullPosSet.sum count` FAILS with probability
at most `(q (4(n−P)+1))^t`.  This is the final floor surface: the carried `P'` atom is discharged to
the honest `Θ(n)` value `(n − g + 3)/4`, giving the paper-faithful `q = 1 − Θ(1/n)`. -/
theorem phase1_pullPos_floor_whp_of_entry (n g : ℕ) (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m, ∀ b : Config (AgentState L K),
      Phase1Convergence.Phase1AllMain n b → AveragingCollapse.secondMomentN b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (fun c => AveragingCollapse.secondMomentN c) m)ᶜ ≤ q m)
    (c : Config (AgentState L K)) (hInvc : Phase1Convergence.Phase1AllMain n c)
    (hg : g ≤ n)
    (hc : AveragingCollapse.secondMomentN c ≤ 4 * (n - (n - g + 3) / 4) + 1) (t : ℕ) :
    ((NonuniformMajority L K).transitionKernel ^ t) c
        {c' | ¬ (n - g + 3) / 4 ≤ (DrainThreading.pullPosSet L K).sum c'.count}
      ≤ (q (4 * (n - (n - g + 3) / 4) + 1)) ^ t :=
  AveragingRate.phase1_pullPos_floor_whp_of_struct n ((n - g + 3) / 4) q hdrop c hInvc
    (by omega) hc t

end PartnerMargin

end ExactMajority
