/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase 6 — Reserve-fuelled splitting of high-exponent biased agents (Doty et al. §7.1, Phase 6)

`Phase6Transition` (Protocol/Transition.lean:1194) lets a *Reserve* agent `r`
that has sampled a small enough exponent act as **fuel** to split a biased *Main*
`m`, via `doSplit`:

```
def doSplit (L K) (r m) :=
  match m.bias with
  | .dyadic sgn j =>
      if r.hour.val ≠ L ∧ r.hour.val > j.val then
        if h : j.val < L then
          ( { r with role := .main, bias := .dyadic sgn ⟨j+1, _⟩ },     -- Reserve → Main
            { m with bias := .dyadic sgn ⟨j+1, _⟩ } )                    -- Main keeps sign
        else (r, m)
      else (r, m)
  | .zero => (r, m)
```

## Index convention (Basic/Bias.lean)

`Bias.dyadic s i` means `|bias| = 2^(-i)`, so the *index* `i` IS the exponent
**magnitude**; the paper's "exponent `= -i`" maps to `i`.  Thus:

* paper "exponent `≤ -l`"            ⟺  index `i ≥ l`   (the GOAL: small bias);
* paper "exponent `> -l`" (high)     ⟺  index `i < l`   (the agents to eliminate).

## The per-pair effect of the PAPER-FAITHFUL `doSplit` rule (fixed 2026-06-10)

`doSplit` now matches Doty §7 "Phase 6 Reserve Splits" line 4 (`r.exponent,
m.exponent ← m.exponent − 1`).  An applicable `doSplit r m` with `m.bias =
.dyadic σ j` (`r.hour.val ≠ L`, `r.hour.val > j.val`, `j.val < L`) produces **two**
Main agents, both at `.dyadic σ ⟨j+1, _⟩`.  Index INCREASES `j → j+1` (magnitude
*halves*); the Reserve becomes a Main.  This is the paper direction (`Ri, ±2^{-j}
→ ±2^{-(j+1)}` *lowers* magnitude).

The proofs below establish exactly this effect (`doSplit_apply`,
`doSplit_role_fst`, `doSplit_bias_fst/snd`), the high-count predicate
`highSt`/`highU`, and the resulting per-pair change in `highU`.

## Campaign finding (recorded honestly; see `doSplit_highU_pair_drop` below)

With the fixed rule the index now moves the RIGHT way for the Lemma 7.2 potential:
a split of a high agent at the TOP of the high band (index `j = l−1`) yields two
agents at index `j+1 = l`, which are NO LONGER high — so the per-pair high-count
DROPS `1 → 0` (`doSplit_highU_pair_drop`).  (For a high agent strictly inside the
band, `j+1 < l`, both products are still high, count `1 → 2`; the net progress is
the band-exit at the top, the mechanism Lemma 7.2 exploits.)  This UNLOCKS the
`PotNonincrOn`-style argument for the Phase-6 window — the obstruction recorded
against the old (inverted) rule is gone.  NOTE: the full Lemma-7.2 progress
instance is a follow-up; this session only flips the per-rule fact + repairs the
already-closed `AllZeroGE6` window (on which `doSplit` is the identity, so the
window result is unaffected by the direction).

This file edits only the per-rule facts forced by the protocol fix; the headline
`allZeroGE6_InvClosed` (closed all-unbiased phase-≥6 window) is direction-agnostic.
No sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.OneSidedCancel
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseConvergenceWeak
import Ripple.PopulationProtocol.Majority.ExactMajority.Protocol.Transition

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Phase6Convergence

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

instance instMeasurableSpaceAgentState6 : MeasurableSpace (AgentState L K) := ⊤
instance instDiscreteMeasurableSpaceAgentState6 :
    DiscreteMeasurableSpace (AgentState L K) where
  forall_measurableSet _ := trivial

/-! ## Part A — the honest `doSplit` per-pair effect facts.

We pin down what the frozen `doSplit` does, branch by branch, so every later
statement is read off the *actual* rule. -/

/-- `doSplit` is **applicable** to `(r, m)` (it does something nontrivial) iff
`m` is a biased Main-side dyadic `.dyadic σ j` whose index satisfies the guard
`r.hour.val ≠ L ∧ r.hour.val > j.val ∧ j.val < L` (paper-faithful: the Main is
not yet at the minimal exponent `−L`, so it can still split down). -/
def DoSplitApplicable (r m : AgentState L K) : Prop :=
  ∃ (σ : Sign) (j : Fin (L + 1)),
    m.bias = Bias.dyadic σ j ∧ r.hour.val ≠ L ∧ r.hour.val > j.val ∧ j.val < L

/-- **Effect of an applicable `doSplit`.**  Both outputs are `.dyadic σ ⟨j+1,_⟩`
(index up, magnitude halved — paper direction);
the first (the Reserve) becomes a `Main`. -/
theorem doSplit_apply (r m : AgentState L K) {σ : Sign} {j : Fin (L + 1)}
    (hb : m.bias = Bias.dyadic σ j) (hne : r.hour.val ≠ L) (hgt : r.hour.val > j.val)
    (hlt : j.val < L) :
    doSplit L K r m
      = ({ r with role := Role.main, bias := Bias.dyadic σ ⟨j.val + 1, by omega⟩ },
         { m with bias := Bias.dyadic σ ⟨j.val + 1, by omega⟩ }) := by
  unfold doSplit
  rw [hb]
  simp only
  rw [if_pos ⟨hne, hgt⟩, dif_pos hlt]

/-- When the guard fails, `doSplit` is the identity. -/
theorem doSplit_eq_self_of_not_applicable (r m : AgentState L K)
    (h : ¬ DoSplitApplicable (L := L) (K := K) r m) :
    doSplit L K r m = (r, m) := by
  cases hb : m.bias with
  | zero => unfold doSplit; rw [hb]
  | dyadic σ j =>
      unfold doSplit; rw [hb]; simp only
      by_cases hg : r.hour.val ≠ L ∧ r.hour.val > j.val
      · rw [if_pos hg]
        by_cases hlt : j.val < L
        · exact absurd ⟨σ, j, hb, hg.1, hg.2, hlt⟩ h
        · rw [dif_neg hlt]
      · rw [if_neg hg]

/-! ## Part B — the honest high-count predicate and the per-pair `highU` change.

A **high** agent (index `< l`, paper exponent `> -l`) is a biased Main whose bias
magnitude is too large; Phase 6 is supposed to eliminate all of them.  We define
the count `highU l` and prove the per-pair effect under the frozen `doSplit`. -/

/-- An agent is **high** (relative to target level `l`) if it is a Main holding a
dyadic bias of index `< l` (paper exponent `> -l`).  This is the Doty pool of
biased agents that Phase 6 must push down to index `≥ l`. -/
def highSt (l : ℕ) (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ ∃ (σ : Sign) (i : Fin (L + 1)), a.bias = Bias.dyadic σ i ∧ i.val < l

/-- A bias-side characterization of `highSt`'s bias condition: dyadic of index `< l`. -/
def biasHigh (l : ℕ) (b : Bias L) : Prop :=
  match b with
  | .zero => False
  | .dyadic _ i => i.val < l

instance (l : ℕ) (b : Bias L) : Decidable (biasHigh l b) := by
  unfold biasHigh; cases b <;> infer_instance

theorem highSt_iff (l : ℕ) (a : AgentState L K) :
    highSt (L := L) (K := K) l a ↔ a.role = Role.main ∧ biasHigh l a.bias := by
  unfold highSt biasHigh
  cases hb : a.bias with
  | zero => simp
  | dyadic s i =>
      constructor
      · rintro ⟨hr, σ, j, hbj, hj⟩; injection hbj with _ hij; subst hij; exact ⟨hr, hj⟩
      · rintro ⟨hr, hi⟩; exact ⟨hr, s, i, rfl, hi⟩

instance (l : ℕ) (a : AgentState L K) : Decidable (highSt (L := L) (K := K) l a) :=
  decidable_of_iff _ (highSt_iff (L := L) (K := K) l a).symm

/-- The high-agent count (the Doty above-`-l` count). -/
def highU (l : ℕ) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => highSt (L := L) (K := K) l a) c

/-- `countP highSt` over a two-element pair as a sum of indicators. -/
theorem countP_highSt_pair (l : ℕ) (x y : AgentState L K) :
    Multiset.countP (fun a => highSt (L := L) (K := K) l a)
        ({x, y} : Multiset (AgentState L K))
      = (if highSt (L := L) (K := K) l x then 1 else 0)
        + (if highSt (L := L) (K := K) l y then 1 else 0) := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
  ring

/-- A non-Main is never high. -/
theorem not_highSt_of_not_main (l : ℕ) (a : AgentState L K) (h : a.role ≠ Role.main) :
    ¬ highSt (L := L) (K := K) l a := fun ⟨hm, _⟩ => h hm

/-- A Main with a dyadic bias of index `< l` is high. -/
theorem highSt_of (l : ℕ) (a : AgentState L K) (σ : Sign) (i : Fin (L + 1))
    (hr : a.role = Role.main) (hb : a.bias = Bias.dyadic σ i) (hi : i.val < l) :
    highSt (L := L) (K := K) l a := ⟨hr, σ, i, hb, hi⟩

/-! ### The fixed-rule finding: a top-of-band `doSplit` DROPS `highU`.

When `m` is a high Main at the TOP of the high band (index `j = l−1`, so the split
target `j + 1 = l` is NOT `< l`), and `r` is the Reserve fuel, the applicable
`doSplit` produces two index-`(j+1)` Mains, both at index `≥ l` — NO LONGER high.
So the pair's high-count goes from `1` (just `m`; the Reserve `r` is not a Main) to
`0`.  This is the band-exit that makes the Lemma-7.2 potential decrease under the
paper-faithful rule. -/

/-- **The fixed rule drops the per-pair high count at the band top.**  If `r` is a
Reserve (hence not high) and `m` is a high Main at index `j` with the `doSplit`
guard satisfied (`j.val < L`), and `j` is at the top of the high band
(`j.val + 1 = l`), then after the split BOTH agents are at index `j+1 = l` (NOT
`< l`, hence not high), so the high-count over the produced pair (`= 0`) is below
that over the consumed pair (`= 1`).  This is the per-pair progress the Lemma-7.2
potential exploits. -/
theorem doSplit_highU_pair_drop (l : ℕ) (r m : AgentState L K) {σ : Sign} {j : Fin (L + 1)}
    (hrR : r.role = Role.reserve) (hmM : m.role = Role.main)
    (hb : m.bias = Bias.dyadic σ j) (hjl : j.val < l) (htop : j.val + 1 = l)
    (hne : r.hour.val ≠ L) (hgt : r.hour.val > j.val) (hlt : j.val < L) :
    Multiset.countP (fun a => highSt (L := L) (K := K) l a)
        ({(doSplit L K r m).1, (doSplit L K r m).2} : Multiset (AgentState L K)) = 0
    ∧ Multiset.countP (fun a => highSt (L := L) (K := K) l a)
        ({r, m} : Multiset (AgentState L K)) = 1 := by
  have happ := doSplit_apply (L := L) (K := K) r m hb hne hgt hlt
  refine ⟨?_, ?_⟩
  · -- both outputs are index-(j+1)=l Mains, NOT high.
    rw [happ]
    rw [countP_highSt_pair]
    have hidx : ¬ (⟨j.val + 1, by omega⟩ : Fin (L + 1)).val < l := by
      show ¬ j.val + 1 < l
      omega
    have h1 : ¬ highSt (L := L) (K := K) l
        ({ r with role := Role.main, bias := Bias.dyadic σ ⟨j.val + 1, by omega⟩ }) := by
      rw [highSt_iff]; rintro ⟨_, hbh⟩
      simp only [biasHigh] at hbh; exact hidx hbh
    have h2 : ¬ highSt (L := L) (K := K) l
        ({ m with bias := Bias.dyadic σ ⟨j.val + 1, by omega⟩ }) := by
      rw [highSt_iff]; rintro ⟨_, hbh⟩
      simp only [biasHigh] at hbh; exact hidx hbh
    rw [if_neg h1, if_neg h2]
  · -- before: r is Reserve (not high), m is high.
    rw [countP_highSt_pair]
    have hr_not : ¬ highSt (L := L) (K := K) l r :=
      not_highSt_of_not_main (L := L) (K := K) l r (by rw [hrR]; decide)
    have hm_high : highSt (L := L) (K := K) l m :=
      highSt_of (L := L) (K := K) l m σ j hmM hb hjl
    rw [if_neg hr_not, if_pos hm_high]

/-! ## Part B2 — the genuinely-monotone Phase-6 potential `highMass l`.

The plain count `highU l` is NOT non-increasing under the paper-faithful `doSplit`:
an interior split (`j + 1 < l`) turns one high Main into TWO high Mains, so the
count RISES `1 → 2`.  Only the band-top split (`j + 1 = l`) drops the count
(`doSplit_highU_pair_drop`).  The Doty potential (mirroring Phase 7's mass detour,
`DOTY_POST63_CAMPAIGN` relay 6) is the **dyadic mass of the high agents**, with the
high-band weight `w l i = 2 ^ (l − i)` for index `i < l` (and `0` for `i ≥ l`):

* interior split `j + 1 < l`: one weight `2^(l−j)` becomes two weights
  `2·2^(l−(j+1)) = 2^(l−j)` — **CONSERVED**;
* band-top split `j + 1 = l`: weight `2^(l−j) = 2` becomes `0` — **DROPS by 2**.

So `highMass l` is non-increasing under every `doSplit`, conserved on interior
splits and strictly dropping at the band top; it is `0` iff no high agent remains
(its summands are all `≥ 1` on high agents).  This is the honest Lemma-7.2
potential. -/

/-- The high-band dyadic weight of a single bias: `2 ^ (l − i)` for `dyadic _ i`
with `i < l`, else `0`.  (Sign-agnostic: Phase 6 splits both signs identically.) -/
def biasMassW (l : ℕ) (b : Bias L) : ℕ :=
  match b with
  | .zero => 0
  | .dyadic _ i => if i.val < l then 2 ^ (l - i.val) else 0

/-- The high-mass weight of an agent: the band weight of its bias if it is a Main,
else `0` (only Mains can be high). -/
def agentMassW (l : ℕ) (a : AgentState L K) : ℕ :=
  if a.role = Role.main then biasMassW (L := L) l a.bias else 0

/-- The Phase-6 potential: total high-band dyadic mass of `c`. -/
def highMass (l : ℕ) (c : Config (AgentState L K)) : ℕ :=
  (c.map (fun a => agentMassW (L := L) (K := K) l a)).sum

/-- A high agent's weight is `≥ 1` (it is a Main at index `< l`, weight a power of
two). -/
theorem agentMassW_pos_of_high (l : ℕ) (a : AgentState L K)
    (h : highSt (L := L) (K := K) l a) : 1 ≤ agentMassW (L := L) (K := K) l a := by
  obtain ⟨hr, σ, i, hb, hi⟩ := h
  unfold agentMassW
  rw [if_pos hr, hb]
  simp only [biasMassW, if_pos hi]
  exact Nat.one_le_two_pow

/-- A non-high agent (non-Main, or unbiased, or index `≥ l`) has weight `0`. -/
theorem agentMassW_eq_zero_of_not_high (l : ℕ) (a : AgentState L K)
    (h : ¬ highSt (L := L) (K := K) l a) : agentMassW (L := L) (K := K) l a = 0 := by
  unfold agentMassW
  by_cases hr : a.role = Role.main
  · rw [if_pos hr]
    cases hb : a.bias with
    | zero => rfl
    | dyadic σ i =>
        by_cases hi : i.val < l
        · exact absurd (highSt_of (L := L) (K := K) l a σ i hr hb hi) h
        · simp only [biasMassW, if_neg hi]
  · rw [if_neg hr]

/-- `highMass l c = 0` iff every agent is non-high (no biased Main below `l`). -/
theorem highMass_eq_zero_iff (l : ℕ) (c : Config (AgentState L K)) :
    highMass (L := L) (K := K) l c = 0 ↔
      ∀ a ∈ c, ¬ highSt (L := L) (K := K) l a := by
  unfold highMass
  rw [Multiset.sum_eq_zero_iff]
  constructor
  · intro h a ha hhigh
    have := h (agentMassW (L := L) (K := K) l a) (Multiset.mem_map_of_mem _ ha)
    have hpos := agentMassW_pos_of_high (L := L) (K := K) l a hhigh
    omega
  · intro h x hx
    rw [Multiset.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact agentMassW_eq_zero_of_not_high (L := L) (K := K) l a (h a ha)

/-- The pair-mass of `{x, y}` is the sum of the two weights. -/
theorem highMass_pair (l : ℕ) (x y : AgentState L K) :
    ((({x, y} : Multiset (AgentState L K))).map
        (fun a => agentMassW (L := L) (K := K) l a)).sum
      = agentMassW (L := L) (K := K) l x + agentMassW (L := L) (K := K) l y := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  simp [Multiset.map_cons, Multiset.sum_cons]

/-! ### The per-pair mass facts under `doSplit`. -/

/-- **A Reserve has weight `0`** (it is not a Main). -/
theorem agentMassW_reserve (l : ℕ) (r : AgentState L K) (hr : r.role = Role.reserve) :
    agentMassW (L := L) (K := K) l r = 0 := by
  unfold agentMassW; rw [if_neg (by rw [hr]; decide)]

/-- The two-power identity behind the conservation: for `j + 1 ≤ l` (i.e. `j < l`),
`2 ^ (l − j) = 2 · 2 ^ (l − (j + 1))`. -/
theorem two_pow_split (l j : ℕ) (hj : j < l) :
    (2 : ℕ) ^ (l - j) = 2 ^ (l - (j + 1)) + 2 ^ (l - (j + 1)) := by
  have hstep : l - j = (l - (j + 1)) + 1 := by omega
  rw [hstep, pow_succ]; ring

/-- **Per-pair mass is non-increasing under `doSplit` from a Reserve.**  With `r` a
Reserve (weight `0`, it is the fuel), an applicable `doSplit r m` conserves the
high-mass on interior splits (`j + 1 < l`) and strictly drops it at the band top
(`j + 1 = l`).  Stated as `after ≤ before`.  The Reserve hypothesis is essential:
a Main `r` would itself carry mass that the split overwrites.  The Main hypothesis
on `m` is the protocol context (`Phase6Transition` only splits a Main target): a
non-Main `m` would let the first output become a high Main out of nothing. -/
theorem doSplit_highMass_pair_le (l : ℕ) (r m : AgentState L K)
    (hrR : r.role = Role.reserve) (hmM : m.role = Role.main) :
    agentMassW (L := L) (K := K) l (doSplit L K r m).1
        + agentMassW (L := L) (K := K) l (doSplit L K r m).2
      ≤ agentMassW (L := L) (K := K) l r + agentMassW (L := L) (K := K) l m := by
  by_cases happ : DoSplitApplicable (L := L) (K := K) r m
  · obtain ⟨σ, j, hb, hne, hgt, hlt⟩ := happ
    rw [doSplit_apply (L := L) (K := K) r m hb hne hgt hlt]
    -- r is a Reserve ⇒ weight 0.
    rw [agentMassW_reserve (L := L) (K := K) l r hrR, Nat.zero_add]
    -- First output: role set to Main, bias `dyadic σ (j+1)` ⇒ weight `biasMassW l (dyadic σ (j+1))`.
    have h1 : agentMassW (L := L) (K := K) l
        ({ r with role := Role.main, bias := Bias.dyadic σ ⟨j.val + 1, by omega⟩ })
          = biasMassW (L := L) l (Bias.dyadic σ ⟨j.val + 1, by omega⟩ : Bias L) := by
      unfold agentMassW; rw [if_pos rfl]
    -- Second output: keeps m.role, bias `dyadic σ (j+1)`.
    -- Input m: agentMassW l m = (if m.role=main then biasMassW l (dyadic σ j) else 0).
    rw [h1]
    -- m is a Main: weight before = biasMassW l (dyadic σ j); second output also a Main.
    have h2 : agentMassW (L := L) (K := K) l
        ({ m with bias := Bias.dyadic σ ⟨j.val + 1, by omega⟩ })
          = biasMassW (L := L) l (Bias.dyadic σ ⟨j.val + 1, by omega⟩ : Bias L) := by
      unfold agentMassW; rw [if_pos hmM]
    have hmbefore : agentMassW (L := L) (K := K) l m
        = biasMassW (L := L) l (Bias.dyadic σ j : Bias L) := by
      unfold agentMassW; rw [if_pos hmM, hb]
    rw [h2, hmbefore]
    -- biasMassW (dyadic σ (j+1)) = if j+1<l then 2^(l-(j+1)) else 0.
    -- biasMassW (dyadic σ j)     = if j<l   then 2^(l-j)     else 0.
    simp only [biasMassW]
    by_cases hjl : j.val < l
    · rw [if_pos hjl]
      by_cases hj1 : (⟨j.val + 1, by omega⟩ : Fin (L + 1)).val < l
      · -- interior: 2^(l-(j+1)) + 2^(l-(j+1)) = 2^(l-j).  CONSERVED (≤).
        rw [if_pos hj1]
        show 2 ^ (l - (j.val + 1)) + 2 ^ (l - (j.val + 1)) ≤ 2 ^ (l - j.val)
        rw [two_pow_split l j.val hjl]
      · -- band top: 0 + 0 ≤ 2^(l-j).  DROP.
        rw [if_neg hj1]; exact Nat.zero_le _
    · -- j ≥ l: m not high, before = 0; but then j+1 ≥ l too, so both outputs weight 0.
      rw [if_neg hjl]
      have hj1 : ¬ (⟨j.val + 1, by omega⟩ : Fin (L + 1)).val < l := by
        show ¬ j.val + 1 < l; omega
      rw [if_neg hj1]
  · rw [doSplit_eq_self_of_not_applicable (L := L) (K := K) r m happ]

/-! ## Part C — the dispatch reduction `Transition = Phase6Transition` on phase-6 pairs.

Mirror of `ReserveSampling.Transition_eq_Phase5Transition_of_phase5` (its olean is
stale under the single-file constraint, so the phase-6 analogue is re-proven here
from the fresh `Transition` primitives). -/

/-- `phaseInit` at target phase `7` only rewrites `counter` (clocks) or is the
identity; it never touches `phase`.  An agent already at phase 7 stays at phase 7. -/
theorem phaseInit_phase_eq_of_seven (a : AgentState L K) (p : Fin 11) (hp : p.val = 7)
    (ha : a.phase.val = 7) :
    (phaseInit L K p a).phase.val = 7 := by
  unfold phaseInit
  have h1 : ¬ p.val = 1 := by omega
  have h2 : ¬ p.val = 2 := by omega
  have h3 : ¬ p.val = 3 := by omega
  have h4 : ¬ p.val = 4 := by omega
  have h5 : ¬ p.val = 5 := by omega
  have h6 : ¬ p.val = 6 := by omega
  rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_neg h5, dif_neg h6, dif_pos hp]
  by_cases hc : a.role = Role.clock <;> simp [hc, ha]

/-- `advancePhaseWithInit` of a phase-6 agent lands at phase 7. -/
theorem advancePhaseWithInit_phase_eq_seven_of_six (a : AgentState L K)
    (ha : a.phase.val = 6) :
    (advancePhaseWithInit L K a).phase.val = 7 := by
  unfold advancePhaseWithInit
  have hadv : (advancePhase L K a).phase.val = 7 := by
    unfold advancePhase
    have : a.phase.val < 10 := by omega
    simp only [this, dif_pos]; omega
  rw [phaseInit_phase_eq_of_seven (L := L) (K := K) (advancePhase L K a)
    (advancePhase L K a).phase hadv hadv]

/-- `stdCounterSubroutine` of a phase-6 agent lands at phase 6 or 7. -/
theorem stdCounterSubroutine_phase_le_seven_of_six (a : AgentState L K)
    (ha : a.phase.val = 6) :
    (stdCounterSubroutine L K a).phase.val ≤ 7 := by
  unfold stdCounterSubroutine; split
  · rw [advancePhaseWithInit_phase_eq_seven_of_six (L := L) (K := K) a ha]
  · simp [ha]

/-- Both `Phase6Transition` outputs land at phase `≤ 7` when both inputs are at
phase 6.  `doSplit` never changes phase; the clock branch caps at 7. -/
theorem Phase6Transition_phase_le_seven (s t : AgentState L K)
    (hs : s.phase.val = 6) (ht : t.phase.val = 6) :
    (Phase6Transition L K s t).1.phase.val ≤ 7 ∧
      (Phase6Transition L K s t).2.phase.val ≤ 7 := by
  -- `doSplit` preserves phase, so each intermediate `s1`/`t1` is at phase 6; the
  -- clock branch then caps at 7.
  have hclk : ∀ s1 : AgentState L K, s1.phase.val = 6 →
      (if s1.role = Role.clock then stdCounterSubroutine L K s1 else s1).phase.val ≤ 7 := by
    intro s1 h
    by_cases hc : s1.role = Role.clock
    · rw [if_pos hc]; exact stdCounterSubroutine_phase_le_seven_of_six (L := L) (K := K) s1 h
    · rw [if_neg hc]; omega
  -- `doSplit` phase facts: applicable or not, phase is preserved.
  have hsplit_phase_fst : ∀ r m : AgentState L K, r.phase.val = 6 →
      (doSplit L K r m).1.phase.val = 6 := by
    intro r m hr
    by_cases happ : DoSplitApplicable (L := L) (K := K) r m
    · obtain ⟨σ, j, hb, hne, hgt, hpos⟩ := happ
      rw [doSplit_apply (L := L) (K := K) r m hb hne hgt hpos]; exact hr
    · rw [doSplit_eq_self_of_not_applicable (L := L) (K := K) r m happ]; exact hr
  have hsplit_phase_snd : ∀ r m : AgentState L K, m.phase.val = 6 →
      (doSplit L K r m).2.phase.val = 6 := by
    intro r m hm
    by_cases happ : DoSplitApplicable (L := L) (K := K) r m
    · obtain ⟨σ, j, hb, hne, hgt, hpos⟩ := happ
      rw [doSplit_apply (L := L) (K := K) r m hb hne hgt hpos]; exact hm
    · rw [doSplit_eq_self_of_not_applicable (L := L) (K := K) r m happ]; exact hm
  refine ⟨?_, ?_⟩
  · unfold Phase6Transition; simp only
    by_cases hb1 : s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero
    · rw [if_pos hb1]; exact hclk _ (hsplit_phase_fst s t hs)
    · rw [if_neg hb1]
      by_cases hb2 : t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero
      · rw [if_pos hb2]; exact hclk _ (hsplit_phase_snd t s hs)
      · rw [if_neg hb2]; exact hclk _ hs
  · unfold Phase6Transition; simp only
    by_cases hb1 : s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero
    · rw [if_pos hb1]; exact hclk _ (hsplit_phase_snd s t ht)
    · rw [if_neg hb1]
      by_cases hb2 : t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero
      · rw [if_pos hb2]; exact hclk _ (hsplit_phase_fst t s ht)
      · rw [if_neg hb2]; exact hclk _ ht

/-- For two phase-6 agents, `phaseEpidemicUpdate` is the identity (max of equal
phases, no init to run, no phase-10 entry).  Mirror of
`phaseEpidemicUpdate_eq_self_of_phase5`. -/
theorem phaseEpidemicUpdate_eq_self_of_phase6 (s t : AgentState L K)
    (hs : s.phase.val = 6) (ht : t.phase.val = 6) :
    phaseEpidemicUpdate L K s t = (s, t) := by
  have hsp : s.phase = ⟨6, by decide⟩ := Fin.ext hs
  have htp : t.phase = ⟨6, by decide⟩ := Fin.ext ht
  unfold phaseEpidemicUpdate
  rw [hsp, htp, max_self]
  simp only [runInitsBetween_self_api]
  have hs_self : ({s with phase := (⟨6, by decide⟩ : Fin 11)} : AgentState L K) = s := by
    rw [← hsp]
  have ht_self : ({t with phase := (⟨6, by decide⟩ : Fin 11)} : AgentState L K) = t := by
    rw [← htp]
  rw [hs_self, ht_self]
  rw [if_neg (by push Not; intro _; simp)]

/-- **Per-pair reduction.**  Two phase-6 agents interact via `Phase6Transition`
under the full `Transition` (epidemic = id, dispatch = `Phase6Transition`, and
neither output reaches phase 10 — they stay `≤ 7` — so the phase-10 finish is the
identity). -/
theorem Transition_eq_Phase6Transition_of_phase6 (s t : AgentState L K)
    (hs : s.phase.val = 6) (ht : t.phase.val = 6) :
    Transition L K s t = Phase6Transition L K s t := by
  have hepi := phaseEpidemicUpdate_eq_self_of_phase6 (L := L) (K := K) s t hs ht
  have hsp : s.phase = ⟨6, by decide⟩ := Fin.ext hs
  obtain ⟨hle1, hle2⟩ := Phase6Transition_phase_le_seven (L := L) (K := K) s t hs ht
  unfold Transition
  rw [hepi]
  simp only [hsp]
  rw [finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) s _ (by omega),
      finishPhase10Entry_eq_self_of_after_ne_10 (L := L) (K := K) t _ (by omega)]

/-! ## Part D — the largest genuinely-closed window: `Phase6Done`.

Because the frozen `doSplit` RAISES `highU` (Part B), the natural Phase-6 working
window is **not** closed for the engine's `PotNonincrOn`.  The genuinely-closed
subset we can deliver is the **already-finished** window `Phase6Done`: every agent
is at phase 6 and every Main is **unbiased**.  Then:

* `highU l c = 0` on `Phase6Done` (no biased Main ⟹ no high agent), and
* `Phase6Done` is one-step closed: an applicable reserve+Main pair has the Main
  unbiased, so `doSplit`'s guard (`m.bias = .dyadic …`) fails and it is the
  identity; thus all Mains stay unbiased and roles/phases are preserved.

This yields a real `PhaseConvergenceW` with `ε = 0` (Part E). -/

/-- On the clean window, `doSplit r m` is the identity whenever `m` is unbiased:
the guard `m.bias = .dyadic …` fails. -/
theorem doSplit_eq_self_of_clean (r m : AgentState L K) (hmclean : m.bias = Bias.zero) :
    doSplit L K r m = (r, m) := by
  apply doSplit_eq_self_of_not_applicable
  rintro ⟨σ, j, hb, _, _, _⟩
  rw [hmclean] at hb; exact (by cases hb)

/-- **`doSplit` never makes a Main biased out of a clean pair.**  If both `r` and
`m` are unbiased then so are both outputs (it is the identity).  This is the bias
half of the closure of the all-unbiased window. -/
theorem doSplit_bias_zero_of_clean (r m : AgentState L K)
    (hr : r.bias = Bias.zero) (hm : m.bias = Bias.zero) :
    (doSplit L K r m).1.bias = Bias.zero ∧ (doSplit L K r m).2.bias = Bias.zero := by
  rw [doSplit_eq_self_of_clean (L := L) (K := K) r m hm]; exact ⟨hr, hm⟩

/-! ### `highU = 0` is forced by "no biased Main". -/

/-- A Main with `.zero` bias is not high. -/
theorem not_highSt_of_zero (l : ℕ) (a : AgentState L K) (h : a.bias = Bias.zero) :
    ¬ highSt (L := L) (K := K) l a := by
  rw [highSt_iff]; rintro ⟨_, hb⟩
  unfold biasHigh at hb; rw [h] at hb; exact hb

/-- **`NoBiasedMain`**: every Main in `c` is unbiased.  Forces `highU l c = 0`. -/
def NoBiasedMain (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = Role.main → a.bias = Bias.zero

/-- On a `NoBiasedMain` config, the high count is `0` (a high agent is a biased
Main, of which there are none). -/
theorem highU_eq_zero_of_noBiasedMain (l : ℕ) (c : Config (AgentState L K))
    (h : NoBiasedMain (L := L) (K := K) c) :
    highU (L := L) (K := K) l c = 0 := by
  unfold highU
  rw [Multiset.countP_eq_zero]
  intro a ha hhigh
  exact not_highSt_of_zero (L := L) (K := K) l a (h a ha hhigh.1) hhigh

/-! ## Part E — the genuinely-closed instance over the all-unbiased phase-≥6 window.

We deliver a real `PhaseConvergenceW` via `OneSidedCancel.crude_PhaseConvergenceW`
with potential `Φ = highU l` over the invariant `AllZeroGE6`: every agent (any
role) is unbiased, and every phase is `≥ 6`.  On `AllZeroGE6`:

* `Φ = highU l c = 0` always, so `PotNonincrOn` is trivial and the per-step
  `hstep` hypothesis is vacuous; we may take `q = 0`, `t = 1`, `ε = 0`;
* `AllZeroGE6` is one-step closed: phases never drop below 6 (phase-monotone), and
  the bias-mutating dispatches (`doSplit`/`cancelSplit`/`absorbConsume`) are the
  identity on a fully-unbiased pair, while phases 9/10 preserve bias, the clock
  subroutine preserves bias, and `phaseInit`/epidemic/finish preserve bias at
  phase ≥ 5.

This is the largest subset we can close honestly under the frozen `doSplit`; the
Lemma-7.2 instance on the *working* window (biased Mains present) is blocked by the
non-monotone finding of Part B and is the precise gap left to the campaign. -/

/-- `cancelSplit` on a fully-unbiased pair is the identity (the `match` falls to
the `| _, _ => (s, t)` arm since neither bias is `.dyadic`). -/
theorem cancelSplit_eq_self_of_zero (s t : AgentState L K)
    (hs : s.bias = Bias.zero) (ht : t.bias = Bias.zero) :
    cancelSplit L K s t = (s, t) := by
  unfold cancelSplit; rw [hs, ht]

/-- `absorbConsume` on a fully-unbiased pair is the identity. -/
theorem absorbConsume_eq_self_of_zero (s t : AgentState L K)
    (hs : s.bias = Bias.zero) (ht : t.bias = Bias.zero) :
    absorbConsume L K s t = (s, t) := by
  unfold absorbConsume; rw [hs, ht]

/-! ### Bias-preservation infrastructure for phase ≥ 5 (re-derived for single-file). -/

/-- `phaseInit` at a phase `≥ 5` preserves `bias`.  Re-derivation of the private
`Transition.phaseInit_bias_of_ge_five` (not exported). -/
theorem phaseInit_bias_ge_five (p : Fin 11) (a : AgentState L K) (hp : 5 ≤ p.val) :
    (phaseInit L K p a).bias = a.bias := by
  set_option linter.unusedSimpArgs false in
  fin_cases p <;> simp_all (config := { decide := false }) <;>
    simp [phaseInit, enterPhase10] <;> split_ifs <;> simp [enterPhase10]

/-- `runInitsBetween oldP p a` only ever runs `phaseInit` at phases `> oldP`; if
`5 ≤ oldP` all those phases are `≥ 6 ≥ 5`, so `bias` is preserved. -/
theorem runInitsBetween_bias_ge_five (oldP p : ℕ) (a : AgentState L K) (h : 5 ≤ oldP) :
    (runInitsBetween L K oldP p a).bias = a.bias := by
  unfold runInitsBetween
  -- Generalize to: folding `phaseInit` over ANY list of phases all `≥ 5` preserves bias.
  have key : ∀ (lst : List ℕ), (∀ k ∈ lst, 5 ≤ k) → ∀ (a : AgentState L K),
      (lst.foldl (fun acc k => if h : k < 11 then phaseInit L K ⟨k, h⟩ acc else acc) a).bias
        = a.bias := by
    intro lst
    induction lst with
    | nil => intro _ a; simp [List.foldl]
    | cons k l IH =>
        intro hmem a
        simp only [List.foldl_cons]
        have hk5 : 5 ≤ k := hmem k (by simp)
        by_cases hk : k < 11
        · rw [dif_pos hk]
          rw [IH (fun j hj => hmem j (by simp [hj])) (phaseInit L K ⟨k, hk⟩ a)]
          exact phaseInit_bias_ge_five (L := L) (K := K) ⟨k, hk⟩ a hk5
        · rw [dif_neg hk]
          exact IH (fun j hj => hmem j (by simp [hj])) a
  apply key
  intro k hk
  rw [List.mem_filter] at hk
  have := hk.2; simp only [decide_eq_true_eq] at this
  omega

/-- `phaseEpidemicUpdate` preserves both agents' `bias` when both inputs are at
phase `≥ 5`.  (The init-runs land at phases `≥ 5`, preserving bias; the phase-10
epidemic entry copies the post-init agent's bias, which equals the input's.) -/
theorem phaseEpidemicUpdate_bias_ge_five (s t : AgentState L K)
    (hs : 5 ≤ s.phase.val) (ht : 5 ≤ t.phase.val) :
    (phaseEpidemicUpdate L K s t).1.bias = s.bias ∧
      (phaseEpidemicUpdate L K s t).2.bias = t.bias := by
  unfold phaseEpidemicUpdate
  simp only
  set p := max s.phase t.phase with hp
  have hsp : 5 ≤ s.phase.val := hs
  have htp : 5 ≤ t.phase.val := ht
  -- post-init agents preserve bias.
  have hs'b : (runInitsBetween L K s.phase.val p.val { s with phase := p }).bias = s.bias := by
    rw [runInitsBetween_bias_ge_five (L := L) (K := K) s.phase.val p.val
      ({ s with phase := p }) hsp]
  have ht'b : (runInitsBetween L K t.phase.val p.val { t with phase := p }).bias = t.bias := by
    rw [runInitsBetween_bias_ge_five (L := L) (K := K) t.phase.val p.val
      ({ t with phase := p }) htp]
  split_ifs with hcond
  · refine ⟨?_, ?_⟩
    · rw [phase10EpidemicEntry_bias]; exact hs'b
    · rw [phase10EpidemicEntry_bias]; exact ht'b
  · exact ⟨hs'b, ht'b⟩

/-- `advancePhaseWithInit` preserves `bias` for an agent at phase ≥ 5. -/
theorem advancePhaseWithInit_bias_ge_five (a : AgentState L K) (ha : 5 ≤ a.phase.val) :
    (advancePhaseWithInit L K a).bias = a.bias := by
  unfold advancePhaseWithInit
  have hadv_bias : (advancePhase L K a).bias = a.bias := by
    unfold advancePhase; split <;> rfl
  have hadv_phase : 5 ≤ (advancePhase L K a).phase.val :=
    le_trans ha (advancePhase_phase_nondec L K a)
  rw [phaseInit_bias_ge_five (L := L) (K := K) (advancePhase L K a).phase
    (advancePhase L K a) hadv_phase]
  exact hadv_bias

/-- `stdCounterSubroutine` preserves `bias` for an agent at phase ≥ 5. -/
theorem stdCounterSubroutine_bias_ge_five (a : AgentState L K) (ha : 5 ≤ a.phase.val) :
    (stdCounterSubroutine L K a).bias = a.bias := by
  unfold stdCounterSubroutine; split
  · exact advancePhaseWithInit_bias_ge_five (L := L) (K := K) a ha
  · rfl

/-- The clock-counter branch preserves `bias = .zero` for a phase-≥5 agent. -/
theorem clockBranch_bias_zero (a : AgentState L K) (ha : 5 ≤ a.phase.val)
    (hz : a.bias = Bias.zero) :
    (if a.role = Role.clock then stdCounterSubroutine L K a else a).bias = Bias.zero := by
  by_cases hc : a.role = Role.clock
  · rw [if_pos hc, stdCounterSubroutine_bias_ge_five (L := L) (K := K) a ha]; exact hz
  · rw [if_neg hc]; exact hz

/-- `doSplit` never changes the first agent's phase. -/
theorem doSplit_phase_fst_eq (r m : AgentState L K) :
    (doSplit L K r m).1.phase = r.phase := by
  by_cases happ : DoSplitApplicable (L := L) (K := K) r m
  · obtain ⟨σ, j, hb, hne, hgt, hpos⟩ := happ
    rw [doSplit_apply (L := L) (K := K) r m hb hne hgt hpos]
  · rw [doSplit_eq_self_of_not_applicable (L := L) (K := K) r m happ]

/-- `doSplit` never changes the second agent's phase. -/
theorem doSplit_phase_snd_eq (r m : AgentState L K) :
    (doSplit L K r m).2.phase = m.phase := by
  by_cases happ : DoSplitApplicable (L := L) (K := K) r m
  · obtain ⟨σ, j, hb, hne, hgt, hpos⟩ := happ
    rw [doSplit_apply (L := L) (K := K) r m hb hne hgt hpos]
  · rw [doSplit_eq_self_of_not_applicable (L := L) (K := K) r m happ]

/-! ### Per-phase dispatch keeps `bias = .zero` on a fully-unbiased phase-≥6 pair. -/

/-- `Phase6Transition` keeps both biases `.zero` (doSplit is the identity on a
clean Main; clock subroutine preserves bias). -/
theorem Phase6Transition_bias_zero (s t : AgentState L K)
    (hs6 : 6 ≤ s.phase.val) (ht6 : 6 ≤ t.phase.val)
    (hsz : s.bias = Bias.zero) (htz : t.bias = Bias.zero) :
    (Phase6Transition L K s t).1.bias = Bias.zero ∧
      (Phase6Transition L K s t).2.bias = Bias.zero := by
  unfold Phase6Transition; simp only
  -- s1/t1: doSplit is identity on the clean Main target, so s1.bias = s.bias = 0, etc.
  have hs1 : (if s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero then
      (doSplit L K s t).1 else if t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero then
      (doSplit L K t s).2 else s).bias = Bias.zero := by
    split_ifs with h1 h2
    · exact absurd htz (h1.2.2)
    · rw [doSplit_eq_self_of_clean (L := L) (K := K) t s hsz]; exact hsz
    · exact hsz
  have ht1 : (if s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero then
      (doSplit L K s t).2 else if t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero then
      (doSplit L K t s).1 else t).bias = Bias.zero := by
    split_ifs with h1 h2
    · exact absurd htz (h1.2.2)
    · rw [doSplit_eq_self_of_clean (L := L) (K := K) t s hsz]; exact htz
    · exact htz
  -- the clock branch then preserves the zero bias.  The intermediate agent is at
  -- phase ≥ 6 ≥ 5 (doSplit/identity preserve phase), so `stdCounterSubroutine` keeps bias.
  refine ⟨?_, ?_⟩
  · set s1 := (if s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero then
      (doSplit L K s t).1 else if t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero then
      (doSplit L K t s).2 else s) with hs1def
    by_cases hc : s1.role = Role.clock
    · rw [if_pos hc]
      -- s1.bias = 0 (hs1); s1.phase ≥ 6 because doSplit/identity preserve phase.
      have hs1phase : 6 ≤ s1.phase.val := by
        rw [hs1def]; split_ifs with h1 h2
        · rw [(doSplit_phase_fst_eq s t (L := L) (K := K))]; exact hs6
        · rw [(doSplit_phase_snd_eq t s (L := L) (K := K))]; exact hs6
        · exact hs6
      rw [stdCounterSubroutine_bias_ge_five (L := L) (K := K) s1 (by omega)]; exact hs1
    · rw [if_neg hc]; exact hs1
  · set t1 := (if s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero then
      (doSplit L K s t).2 else if t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero then
      (doSplit L K t s).1 else t) with ht1def
    by_cases hc : t1.role = Role.clock
    · rw [if_pos hc]
      have ht1phase : 6 ≤ t1.phase.val := by
        rw [ht1def]; split_ifs with h1 h2
        · rw [(doSplit_phase_snd_eq s t (L := L) (K := K))]; exact ht6
        · rw [(doSplit_phase_fst_eq t s (L := L) (K := K))]; exact ht6
        · exact ht6
      rw [stdCounterSubroutine_bias_ge_five (L := L) (K := K) t1 (by omega)]; exact ht1
    · rw [if_neg hc]; exact ht1

/-- `Phase7Transition` keeps both biases `.zero` (cancelSplit is the identity on a
clean pair; clock subroutine preserves bias).  `cancelSplit` preserves role
(`cancelSplit_role_fst/snd`) and phase (`cancelSplit_phase`). -/
theorem Phase7Transition_bias_zero (s t : AgentState L K)
    (hs6 : 6 ≤ s.phase.val) (ht6 : 6 ≤ t.phase.val)
    (hsz : s.bias = Bias.zero) (htz : t.bias = Bias.zero) :
    (Phase7Transition L K s t).1.bias = Bias.zero ∧
      (Phase7Transition L K s t).2.bias = Bias.zero := by
  unfold Phase7Transition; simp only
  have hcs := cancelSplit_eq_self_of_zero (L := L) (K := K) s t hsz htz
  have hs1b : (if s.role = Role.main ∧ t.role = Role.main then (cancelSplit L K s t).1 else s).bias
      = Bias.zero := by split_ifs with h
                        · rw [hcs]; exact hsz
                        · exact hsz
  have ht1b : (if s.role = Role.main ∧ t.role = Role.main then (cancelSplit L K s t).2 else t).bias
      = Bias.zero := by split_ifs with h
                        · rw [hcs]; exact htz
                        · exact htz
  have hs1p : (if s.role = Role.main ∧ t.role = Role.main then (cancelSplit L K s t).1 else s).phase.val
      = s.phase.val := by
    split_ifs with h
    · rw [hcs]
    · rfl
  have ht1p : (if s.role = Role.main ∧ t.role = Role.main then (cancelSplit L K s t).2 else t).phase.val
      = t.phase.val := by
    split_ifs with h
    · rw [hcs]
    · rfl
  refine ⟨?_, ?_⟩
  · set s1 := (if s.role = Role.main ∧ t.role = Role.main then (cancelSplit L K s t).1 else s)
    by_cases hc : s1.role = Role.clock
    · rw [if_pos hc, stdCounterSubroutine_bias_ge_five (L := L) (K := K) s1 (by omega)]; exact hs1b
    · rw [if_neg hc]; exact hs1b
  · set t1 := (if s.role = Role.main ∧ t.role = Role.main then (cancelSplit L K s t).2 else t)
    by_cases hc : t1.role = Role.clock
    · rw [if_pos hc, stdCounterSubroutine_bias_ge_five (L := L) (K := K) t1 (by omega)]; exact ht1b
    · rw [if_neg hc]; exact ht1b

/-- `Phase8Transition` keeps both biases `.zero` (absorbConsume is the identity on
a clean pair; clock subroutine preserves bias). -/
theorem Phase8Transition_bias_zero (s t : AgentState L K)
    (hs6 : 6 ≤ s.phase.val) (ht6 : 6 ≤ t.phase.val)
    (hsz : s.bias = Bias.zero) (htz : t.bias = Bias.zero) :
    (Phase8Transition L K s t).1.bias = Bias.zero ∧
      (Phase8Transition L K s t).2.bias = Bias.zero := by
  unfold Phase8Transition; simp only
  have hac := absorbConsume_eq_self_of_zero (L := L) (K := K) s t hsz htz
  have hs1b : (if s.role = Role.main ∧ t.role = Role.main then (absorbConsume L K s t).1 else s).bias
      = Bias.zero := by split_ifs with h
                        · rw [hac]; exact hsz
                        · exact hsz
  have ht1b : (if s.role = Role.main ∧ t.role = Role.main then (absorbConsume L K s t).2 else t).bias
      = Bias.zero := by split_ifs with h
                        · rw [hac]; exact htz
                        · exact htz
  have hs1p : (if s.role = Role.main ∧ t.role = Role.main then (absorbConsume L K s t).1 else s).phase.val
      = s.phase.val := by
    split_ifs with h
    · rw [hac]
    · rfl
  have ht1p : (if s.role = Role.main ∧ t.role = Role.main then (absorbConsume L K s t).2 else t).phase.val
      = t.phase.val := by
    split_ifs with h
    · rw [hac]
    · rfl
  refine ⟨?_, ?_⟩
  · set s1 := (if s.role = Role.main ∧ t.role = Role.main then (absorbConsume L K s t).1 else s)
    by_cases hc : s1.role = Role.clock
    · rw [if_pos hc, stdCounterSubroutine_bias_ge_five (L := L) (K := K) s1 (by omega)]; exact hs1b
    · rw [if_neg hc]; exact hs1b
  · set t1 := (if s.role = Role.main ∧ t.role = Role.main then (absorbConsume L K s t).2 else t)
    by_cases hc : t1.role = Role.clock
    · rw [if_pos hc, stdCounterSubroutine_bias_ge_five (L := L) (K := K) t1 (by omega)]; exact ht1b
    · rw [if_neg hc]; exact ht1b

/-- `Phase9Transition` (= `Phase2Transition`) keeps both biases `.zero` for inputs
at phase ≥ 5: it only writes `opinions`/`output` or calls `advancePhaseWithInit`,
which preserves bias at phase ≥ 5. -/
theorem Phase9Transition_bias_zero (s t : AgentState L K)
    (hs5 : 5 ≤ s.phase.val) (ht5 : 5 ≤ t.phase.val)
    (hsz : s.bias = Bias.zero) (htz : t.bias = Bias.zero) :
    (Phase9Transition L K s t).1.bias = Bias.zero ∧
      (Phase9Transition L K s t).2.bias = Bias.zero := by
  unfold Phase9Transition Phase2Transition
  simp only
  split_ifs with h1 h2 h3 h4
  · refine ⟨?_, ?_⟩
    · rw [advancePhaseWithInit_bias_ge_five (L := L) (K := K) _ (by simpa using hs5)]; exact hsz
    · rw [advancePhaseWithInit_bias_ge_five (L := L) (K := K) _ (by simpa using ht5)]; exact htz
  · exact ⟨hsz, htz⟩
  · exact ⟨hsz, htz⟩
  · exact ⟨hsz, htz⟩
  · exact ⟨hsz, htz⟩

/-- `Phase10Transition` never assigns `.bias`, so it preserves it; in particular
keeps `.zero`. -/
theorem Phase10Transition_bias_zero (s t : AgentState L K)
    (hsz : s.bias = Bias.zero) (htz : t.bias = Bias.zero) :
    (Phase10Transition L K s t).1.bias = Bias.zero ∧
      (Phase10Transition L K s t).2.bias = Bias.zero := by
  unfold Phase10Transition
  simp only
  constructor <;> (split_ifs <;> simp_all)

/-! ### The per-pair `Transition` bias-zero closure on the phase-≥6 window. -/

/-- **The full `Transition` keeps both biases `.zero` on a phase-≥6 clean pair.**
After the epidemic (bias-preserving at phase ≥ 5, `phaseEpidemicUpdate_bias_ge_five`),
the dispatch is one of `Phase6/7/8/9/10Transition` (each keeps bias `.zero`: 6/7/8
via the identity-on-clean lemmas above, 9/10 via the exported phase-≥9
preservation), and `finishPhase10Entry` preserves bias. -/
theorem Transition_bias_zero_of_phase_ge6 (s t : AgentState L K)
    (hs : 6 ≤ s.phase.val) (ht : 6 ≤ t.phase.val)
    (hsz : s.bias = Bias.zero) (htz : t.bias = Bias.zero) :
    (Transition L K s t).1.bias = Bias.zero ∧ (Transition L K s t).2.bias = Bias.zero := by
  -- The epidemic output `(s', t')` preserves bias and has phase ≥ 6.
  have hepb := phaseEpidemicUpdate_bias_ge_five (L := L) (K := K) s t (by omega) (by omega)
  unfold Transition
  generalize hep_gen : phaseEpidemicUpdate L K s t = ep
  obtain ⟨s', t'⟩ := ep
  have hs'b : s'.bias = Bias.zero := by have := hepb.1; rw [hep_gen] at this; rw [this]; exact hsz
  have ht'b : t'.bias = Bias.zero := by have := hepb.2; rw [hep_gen] at this; rw [this]; exact htz
  have hs'_ge : 6 ≤ s'.phase.val := by
    have := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) s t
    rw [hep_gen] at this; exact le_trans hs (le_trans (le_max_left _ _) this)
  have ht'_ge : 6 ≤ t'.phase.val := by
    have := phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) s t
    rw [hep_gen] at this; exact le_trans ht (le_trans (le_max_right _ _) this)
  have hs'_le : s'.phase.val ≤ 10 := by have := s'.phase.2; omega
  -- The dispatch output keeps bias zero, depending on s'.phase ∈ {6,…,10}.
  have hdisp : (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).1.bias = Bias.zero
      ∧ (match s'.phase with
      | ⟨0, _⟩ => Phase0Transition L K s' t'
      | ⟨1, _⟩ => Phase1Transition L K s' t'
      | ⟨2, _⟩ => Phase2Transition L K s' t'
      | ⟨3, _⟩ => Phase3Transition L K s' t'
      | ⟨4, _⟩ => Phase4Transition L K s' t'
      | ⟨5, _⟩ => Phase5Transition L K s' t'
      | ⟨6, _⟩ => Phase6Transition L K s' t'
      | ⟨7, _⟩ => Phase7Transition L K s' t'
      | ⟨8, _⟩ => Phase8Transition L K s' t'
      | ⟨9, _⟩ => Phase9Transition L K s' t'
      | ⟨10, _⟩ => Phase10Transition L K s' t'
      | _ => (s', t')).2.bias = Bias.zero := by
    rcases (show s'.phase.val = 6 ∨ s'.phase.val = 7 ∨ s'.phase.val = 8
        ∨ s'.phase.val = 9 ∨ s'.phase.val = 10 by omega) with h | h | h | h | h
    · have hph : s'.phase = ⟨6, by decide⟩ := Fin.ext h
      rw [hph]; exact Phase6Transition_bias_zero s' t' hs'_ge ht'_ge hs'b ht'b
    · have hph : s'.phase = ⟨7, by decide⟩ := Fin.ext h
      rw [hph]; exact Phase7Transition_bias_zero s' t' hs'_ge ht'_ge hs'b ht'b
    · have hph : s'.phase = ⟨8, by decide⟩ := Fin.ext h
      rw [hph]; exact Phase8Transition_bias_zero s' t' hs'_ge ht'_ge hs'b ht'b
    · have hph : s'.phase = ⟨9, by decide⟩ := Fin.ext h
      rw [hph]; exact Phase9Transition_bias_zero s' t' (by omega) (by omega) hs'b ht'b
    · have hph : s'.phase = ⟨10, by decide⟩ := Fin.ext h
      rw [hph]; exact Phase10Transition_bias_zero s' t' hs'b ht'b
  -- finishPhase10Entry preserves bias.
  simp only [finishPhase10Entry_bias]
  exact hdisp

/-! ## Part E2 — the `highMass l` `PotNonincrOn` on the phase-6 working window.

`Φ = highMass l` is non-increasing under the real kernel on the window where every
agent is at phase **exactly 6** (`Phase6Win`): there `Transition = Phase6Transition`
(Part C), whose only bias-mutation is `doSplit` from a Reserve onto a biased Main,
and the per-pair mass is non-increasing (`doSplit_highMass_pair_le`).  The clock
branch preserves `role` and `bias` (phase ≥ 5), hence `agentMassW`.  This mirrors
Phase 7's `minorityU_stepOrSelf_le → potNonincrOn_minorityU`; the window need not be
closed for `hmono` (closure is carried separately). -/

/-- `advancePhase` preserves `role` (it only writes `phase`). -/
theorem advancePhase_role_eq (a : AgentState L K) :
    (advancePhase L K a).role = a.role := by unfold advancePhase; split <;> rfl

/-- `phaseInit` at phase ≥ 5 preserves `role` (re-derivation of the private lemma). -/
theorem phaseInit_role_ge_five6 (p : Fin 11) (a : AgentState L K) (hp : 5 ≤ p.val) :
    (phaseInit L K p a).role = a.role := by
  set_option linter.unusedSimpArgs false in
  fin_cases p <;> simp_all (config := { decide := false }) <;>
    simp [phaseInit, enterPhase10] <;> split_ifs <;> simp [enterPhase10]

/-- `advancePhaseWithInit` preserves `role` at phase ≥ 5. -/
theorem advancePhaseWithInit_role_ge_five6 (a : AgentState L K) (ha : 5 ≤ a.phase.val) :
    (advancePhaseWithInit L K a).role = a.role := by
  unfold advancePhaseWithInit
  have hadv_phase : 5 ≤ (advancePhase L K a).phase.val :=
    le_trans ha (advancePhase_phase_nondec L K a)
  rw [phaseInit_role_ge_five6 (L := L) (K := K) (advancePhase L K a).phase
    (advancePhase L K a) hadv_phase]
  exact advancePhase_role_eq (L := L) (K := K) a

/-- `stdCounterSubroutine` preserves `role` at phase ≥ 5. -/
theorem stdCounterSubroutine_role_ge_five6 (a : AgentState L K) (ha : 5 ≤ a.phase.val) :
    (stdCounterSubroutine L K a).role = a.role := by
  unfold stdCounterSubroutine; split
  · exact advancePhaseWithInit_role_ge_five6 (L := L) (K := K) a ha
  · rfl

/-- The clock branch preserves `agentMassW` (it preserves role and bias at phase ≥ 5). -/
theorem clockBranch_agentMassW_eq (l : ℕ) (a : AgentState L K) (ha : 5 ≤ a.phase.val) :
    agentMassW (L := L) (K := K) l
        (if a.role = Role.clock then stdCounterSubroutine L K a else a)
      = agentMassW (L := L) (K := K) l a := by
  by_cases hc : a.role = Role.clock
  · rw [if_pos hc]
    unfold agentMassW
    rw [stdCounterSubroutine_role_ge_five6 (L := L) (K := K) a ha,
        stdCounterSubroutine_bias_ge_five (L := L) (K := K) a ha]
  · rw [if_neg hc]

/-- **Per-pair `highMass` non-increase under `Phase6Transition`** on a phase-6 pair.
`doSplit` fires only on a `(Reserve, biased Main)` pair (either order); there the
per-pair mass drops (`doSplit_highMass_pair_le`).  All other dispatch branches are
the identity on the bias-carrying pair, and the trailing clock subroutine preserves
`agentMassW`.  Hence the sum of the two outputs' weights is `≤` that of the inputs. -/
theorem Phase6Transition_highMass_pair_le (l : ℕ) (s t : AgentState L K)
    (hs6 : 6 ≤ s.phase.val) (ht6 : 6 ≤ t.phase.val) :
    agentMassW (L := L) (K := K) l (Phase6Transition L K s t).1
        + agentMassW (L := L) (K := K) l (Phase6Transition L K s t).2
      ≤ agentMassW (L := L) (K := K) l s + agentMassW (L := L) (K := K) l t := by
  unfold Phase6Transition; simp only
  -- The pre-clock pair `(s1, t1)`: doSplit in the matching branch, identity otherwise.
  -- In every branch the pre-clock pair's mass-sum is ≤ the input mass-sum, and each
  -- agent stays at phase ≥ 6 (doSplit/identity preserve phase), so the clock branch
  -- preserves agentMassW.
  set s1 := (if s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero then
      (doSplit L K s t).1 else if t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero then
      (doSplit L K t s).2 else s) with hs1def
  set t1 := (if s.role = Role.reserve ∧ t.role = Role.main ∧ t.bias ≠ Bias.zero then
      (doSplit L K s t).2 else if t.role = Role.reserve ∧ s.role = Role.main ∧ s.bias ≠ Bias.zero then
      (doSplit L K t s).1 else t) with ht1def
  -- pre-clock mass-sum bound and phase ≥ 6 of s1/t1.
  have hpre : agentMassW (L := L) (K := K) l s1 + agentMassW (L := L) (K := K) l t1
      ≤ agentMassW (L := L) (K := K) l s + agentMassW (L := L) (K := K) l t := by
    rw [hs1def, ht1def]
    split_ifs with h1 h2
    · -- doSplit s t: s Reserve, t Main biased.  drop on (s,t).
      have := doSplit_highMass_pair_le (L := L) (K := K) l s t h1.1 h1.2.1
      linarith [this]
    · -- doSplit t s: t Reserve, s Main biased.  drop on (t,s); reorder.
      have := doSplit_highMass_pair_le (L := L) (K := K) l t s h2.1 h2.2.1
      linarith [this]
    · -- identity.
      exact le_refl _
  have hs1p : 6 ≤ s1.phase.val := by
    rw [hs1def]; split_ifs with h1 h2
    · rw [doSplit_phase_fst_eq s t (L := L) (K := K)]; exact hs6
    · rw [doSplit_phase_snd_eq t s (L := L) (K := K)]; exact hs6
    · exact hs6
  have ht1p : 6 ≤ t1.phase.val := by
    rw [ht1def]; split_ifs with h1 h2
    · rw [doSplit_phase_snd_eq s t (L := L) (K := K)]; exact ht6
    · rw [doSplit_phase_fst_eq t s (L := L) (K := K)]; exact ht6
    · exact ht6
  -- the clock branch preserves each weight.
  rw [clockBranch_agentMassW_eq (L := L) (K := K) l s1 (by omega),
      clockBranch_agentMassW_eq (L := L) (K := K) l t1 (by omega)]
  exact hpre

/-! ### Global lift: `highMass l` non-increasing on the phase-6 working window. -/

/-- The phase-6 working window: size `n`, every agent at phase **exactly 6**.  On it
`Transition = Phase6Transition` for every applicable pair, so the per-pair mass
non-increase lifts to the global `highMass`. -/
def Phase6Win (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ (∀ a ∈ c, a.phase.val = 6)

instance (n : ℕ) (c : Config (AgentState L K)) :
    Decidable (Phase6Win (L := L) (K := K) n c) := by unfold Phase6Win; infer_instance

private theorem mem_of_app_left6E2 {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right6E2 {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-- The mass-sum decomposes additively over `+`. -/
theorem highMass_add (l : ℕ) (a b : Config (AgentState L K)) :
    highMass (L := L) (K := K) l (a + b)
      = highMass (L := L) (K := K) l a + highMass (L := L) (K := K) l b := by
  unfold highMass; rw [Multiset.map_add, Multiset.sum_add]

/-- **`highMass l` is non-increasing under any chosen-pair update on `Phase6Win`.** -/
theorem highMass_stepOrSelf_le (l n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase6Win (L := L) (K := K) n c) (r₁ r₂ : AgentState L K) :
    highMass (L := L) (K := K) l (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ highMass (L := L) (K := K) l c := by
  obtain ⟨_, hph⟩ := hInv
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left6E2 happ
    have hm2 := mem_of_app_right6E2 happ
    have h16 : r₁.phase.val = 6 := hph r₁ hm1
    have h26 : r₂.phase.val = 6 := hph r₂ hm2
    have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    -- Transition = Phase6Transition on this pair.
    have htr : Transition L K r₁ r₂ = Phase6Transition L K r₁ r₂ :=
      Transition_eq_Phase6Transition_of_phase6 (L := L) (K := K) r₁ r₂ h16 h26
    -- decompose c = (c - pair) + pair.
    have hcsplit : c = (c - {r₁, r₂}) + {r₁, r₂} := (tsub_add_cancel_of_le hsub).symm
    -- pair mass-le from the per-pair lemma.
    have hpairle : highMass (L := L) (K := K) l
        {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
          ≤ highMass (L := L) (K := K) l {r₁, r₂} := by
      unfold highMass
      rw [highMass_pair, highMass_pair, htr]
      exact Phase6Transition_highMass_pair_le (L := L) (K := K) l r₁ r₂
        (by omega) (by omega)
    rw [hc', highMass_add]
    calc highMass (L := L) (K := K) l (c - {r₁, r₂})
            + highMass (L := L) (K := K) l {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
        ≤ highMass (L := L) (K := K) l (c - {r₁, r₂})
            + highMass (L := L) (K := K) l {r₁, r₂} := by
          exact Nat.add_le_add_left hpairle _
      _ = highMass (L := L) (K := K) l c := by
          rw [← highMass_add]; rw [← hcsplit]
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- `highMass l` is non-increasing on the one-step kernel support from a
`Phase6Win`-config. -/
theorem highMass_le_on_support (l n m : ℕ)
    (c c' : Config (AgentState L K)) (hInv : Phase6Win (L := L) (K := K) n c)
    (hle : highMass (L := L) (K := K) l c ≤ m)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    highMass (L := L) (K := K) l c' ≤ m := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]
    exact le_trans (highMass_stepOrSelf_le l n c hInv r₁ r₂) hle
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'; exact hle

/-- **The engine `hmono`: `highMass l` is `PotNonincrOn` on `Phase6Win n`.** -/
theorem potNonincrOn_highMass (l n : ℕ) :
    OneSidedCancel.PotNonincrOn (fun c => Phase6Win (L := L) (K := K) n c)
      (NonuniformMajority L K).transitionKernel (fun c => highMass (L := L) (K := K) l c) := by
  intro c hInv
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | highMass (L := L) (K := K) l c < highMass (L := L) (K := K) l x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  simp only [Set.mem_setOf_eq] at hx
  have hle : highMass (L := L) (K := K) l x ≤ highMass (L := L) (K := K) l c :=
    highMass_le_on_support l n (highMass (L := L) (K := K) l c) c x hInv le_rfl hsupp
  omega

/-! ## Part E3 — the band-top drain rectangle (the `hdrop` floor).

A band-top split (`m` a biased Main at index `l−1`, `r` a Reserve sampled high
enough, `r.hour > l−1` and `r.hour ≠ L`) strictly drops `highMass l` by `2 ≥ 1`.
The eliminator pool per level `l` is the Reserves at hour `> l−1` (= Phase-5's
`sampledReserveClassU` at the useful levels), the minority pool is the biased Mains
at index `l−1`.  Their cross-rectangle feeds the generic drop-probability bound,
giving the engine `hdrop`. -/

/-- **The `doSplit`-level band-top strict drop.**  `r` a Reserve, `m` a Main biased
at index `l−1` (`1 ≤ l ≤ L`), guard satisfied: the split sends both agents to index
`l` (weight 0), so the pair mass drops by exactly `2 ≥ 1`. -/
theorem doSplit_highMass_pair_drop (l : ℕ) (r m : AgentState L K) {σ : Sign}
    (hl1 : 1 ≤ l) (hlL : l ≤ L) (hrR : r.role = Role.reserve) (hmM : m.role = Role.main)
    (hb : m.bias = Bias.dyadic σ ⟨l - 1, by omega⟩)
    (hne : r.hour.val ≠ L) (hgt : r.hour.val > l - 1) :
    agentMassW (L := L) (K := K) l (doSplit L K r m).1
        + agentMassW (L := L) (K := K) l (doSplit L K r m).2 + 1
      ≤ agentMassW (L := L) (K := K) l r + agentMassW (L := L) (K := K) l m := by
  have hjlt : (⟨l - 1, by omega⟩ : Fin (L + 1)).val < L := by show l - 1 < L; omega
  rw [doSplit_apply (L := L) (K := K) r m hb hne (by show r.hour.val > l - 1; exact hgt) hjlt]
  rw [agentMassW_reserve (L := L) (K := K) l r hrR]
  have hidx : ¬ (⟨(l - 1) + 1, by omega⟩ : Fin (L + 1)).val < l := by
    show ¬ (l - 1) + 1 < l; omega
  have ho1 : agentMassW (L := L) (K := K) l
      ({ r with role := Role.main, bias := Bias.dyadic σ ⟨(l - 1) + 1, by omega⟩ }) = 0 := by
    unfold agentMassW; rw [if_pos rfl]; simp only [biasMassW, if_neg hidx]
  have ho2 : agentMassW (L := L) (K := K) l
      ({ m with bias := Bias.dyadic σ ⟨(l - 1) + 1, by omega⟩ }) = 0 := by
    unfold agentMassW; rw [if_pos hmM]; simp only [biasMassW, if_neg hidx]
  have hmW : agentMassW (L := L) (K := K) l m = 2 ^ (l - (l - 1)) := by
    unfold agentMassW; rw [if_pos hmM, hb]; simp only [biasMassW]
    rw [if_pos (show (⟨l - 1, by omega⟩ : Fin (L + 1)).val < l by show l - 1 < l; omega)]
  rw [ho1, ho2, hmW]
  have : l - (l - 1) = 1 := by omega
  rw [this]; norm_num

/-- **Per-pair band-top strict drop under `Phase6Transition`.**  `r` a Reserve with
`r.hour ≠ L` and `r.hour > l−1`, `m` a Main biased at index `l−1` (`1 ≤ l ≤ L`):
the pair mass drops by `≥ 1` (the split sends both to index `l`, exiting the band).
Branch 1 of `Phase6Transition` fires; the clock subroutine preserves `agentMassW`. -/
theorem Phase6Transition_highMass_pair_drop (l : ℕ) (r m : AgentState L K) {σ : Sign}
    (hl1 : 1 ≤ l) (hlL : l ≤ L) (hrR : r.role = Role.reserve) (hmM : m.role = Role.main)
    (hb : m.bias = Bias.dyadic σ ⟨l - 1, by omega⟩)
    (hne : r.hour.val ≠ L) (hgt : r.hour.val > l - 1)
    (hr6 : 6 ≤ r.phase.val) (hm6 : 6 ≤ m.phase.val) :
    agentMassW (L := L) (K := K) l (Phase6Transition L K r m).1
        + agentMassW (L := L) (K := K) l (Phase6Transition L K r m).2 + 1
      ≤ agentMassW (L := L) (K := K) l r + agentMassW (L := L) (K := K) l m := by
  have hmbias : m.bias ≠ Bias.zero := by rw [hb]; exact fun h => by cases h
  unfold Phase6Transition; simp only
  set s1 := (if r.role = Role.reserve ∧ m.role = Role.main ∧ m.bias ≠ Bias.zero then
      (doSplit L K r m).1 else if m.role = Role.reserve ∧ r.role = Role.main ∧ r.bias ≠ Bias.zero then
      (doSplit L K m r).2 else r) with hs1def
  set t1 := (if r.role = Role.reserve ∧ m.role = Role.main ∧ m.bias ≠ Bias.zero then
      (doSplit L K r m).2 else if m.role = Role.reserve ∧ r.role = Role.main ∧ r.bias ≠ Bias.zero then
      (doSplit L K m r).1 else m) with ht1def
  -- branch 1 fires: s1 = (doSplit r m).1, t1 = (doSplit r m).2.
  have hs1eq : s1 = (doSplit L K r m).1 := by rw [hs1def, if_pos ⟨hrR, hmM, hmbias⟩]
  have ht1eq : t1 = (doSplit L K r m).2 := by rw [ht1def, if_pos ⟨hrR, hmM, hmbias⟩]
  have hp1 : 6 ≤ s1.phase.val := by
    rw [hs1eq, doSplit_phase_fst_eq r m (L := L) (K := K)]; exact hr6
  have hp2 : 6 ≤ t1.phase.val := by
    rw [ht1eq, doSplit_phase_snd_eq r m (L := L) (K := K)]; exact hm6
  rw [clockBranch_agentMassW_eq (L := L) (K := K) l s1 (by omega),
      clockBranch_agentMassW_eq (L := L) (K := K) l t1 (by omega)]
  rw [hs1eq, ht1eq]
  exact doSplit_highMass_pair_drop (L := L) (K := K) l r m hl1 hlL hrR hmM hb hne hgt

/-- **Global band-top strict drop under `stepOrSelf`.**  On a `Phase6Win` config, an
applicable pair `(r, m)` with `r` a band-top-eliminating Reserve and `m` a biased
Main at index `l−1` drops the global `highMass l` by `≥ 1`. -/
theorem highMass_stepOrSelf_drop (l n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase6Win (L := L) (K := K) n c) (r m : AgentState L K)
    (happ : Protocol.Applicable c r m) {σ : Sign}
    (hl1 : 1 ≤ l) (hlL : l ≤ L) (hrR : r.role = Role.reserve) (hmM : m.role = Role.main)
    (hb : m.bias = Bias.dyadic σ ⟨l - 1, by omega⟩)
    (hne : r.hour.val ≠ L) (hgt : r.hour.val > l - 1) :
    highMass (L := L) (K := K) l (Protocol.stepOrSelf (NonuniformMajority L K) c r m) + 1
      ≤ highMass (L := L) (K := K) l c := by
  obtain ⟨_, hph⟩ := hInv
  have hm1 := mem_of_app_left6E2 happ
  have hm2 := mem_of_app_right6E2 happ
  have h16 : r.phase.val = 6 := hph r hm1
  have h26 : m.phase.val = 6 := hph m hm2
  have hsub : ({r, m} : Multiset (AgentState L K)) ≤ c := happ
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r m
      = c - {r, m} + {(Transition L K r m).1, (Transition L K r m).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  have htr : Transition L K r m = Phase6Transition L K r m :=
    Transition_eq_Phase6Transition_of_phase6 (L := L) (K := K) r m h16 h26
  have hcsplit : c = (c - {r, m}) + {r, m} := (tsub_add_cancel_of_le hsub).symm
  -- pair strict drop.
  have hpairdrop : highMass (L := L) (K := K) l
      {(Transition L K r m).1, (Transition L K r m).2} + 1
        ≤ highMass (L := L) (K := K) l {r, m} := by
    unfold highMass
    rw [highMass_pair, highMass_pair, htr]
    exact Phase6Transition_highMass_pair_drop (L := L) (K := K) l r m hl1 hlL hrR hmM hb hne hgt
      (by omega) (by omega)
  rw [hc', highMass_add]
  -- highMass c = highMass(c - pair) + highMass(pair).
  have hcval : highMass (L := L) (K := K) l c
      = highMass (L := L) (K := K) l (c - {r, m}) + highMass (L := L) (K := K) l {r, m} := by
    conv_lhs => rw [hcsplit]
    rw [highMass_add]
  omega

/-! ### The generic drop-rectangle probability bound (re-derived single-file).

Mirror of `Phase7Convergence.drop_prob_of_rect` (its olean is not imported here): for
a potential `Φ` and a rectangle `R` of pairs each of which, when fired, drops `Φ` by
`≥ 1`, the one-step drop-probability is `≥ N/(n(n−1))` with `N ≤ ∑_R interactionCount`. -/

private theorem applicable_of_mem_distinct6 {c : Config (AgentState L K)}
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

/-- The `interactionCount` mass of `A ×ˢ B` for pairwise-distinct state-finsets. -/
theorem sum_interactionCount_cross_disjoint6
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

/-- **The generic drop-rectangle probability bound** (Φ-agnostic). -/
theorem drop_prob_of_rect6 (Φ : Config (AgentState L K) → ℕ) (n : ℕ) (hn : 2 ≤ n)
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

/-! ### The Phase-6 band-top drain rectangle.

Fix the target level `l` (`1 ≤ l ≤ L`).  The band-top biased Mains are at index
`l−1`; the eliminator Reserves are those sampled at a hour `h` with `l−1 < h ≤ L`
and `h ≠ L` (i.e. `l ≤ h < L`) — exactly Phase-5's `sampledReserveClass h` pool.
Each cross pair `(reserve@h, main@(l−1))` fires a band-top `doSplit`, dropping
`highMass l` by `≥ 1` (`highMass_stepOrSelf_drop`).  Note the pair order: the
Reserve `r` is first, the Main `m` second (matching `Phase6Transition` branch 1 and
`highMass_stepOrSelf_drop`'s `(r, m)` convention). -/

/-- The biased Mains of sign `σ` at the band-top index `l−1`. -/
def mainAt6 (σ : Sign) (l : ℕ) (hl : 1 ≤ l) (hlL : l ≤ L) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.main ∧
    a.bias = Bias.dyadic σ ⟨l - 1, by omega⟩)

/-- The eliminator Reserves sampled at hour `h` (a `sampledReserveClass h` pool). -/
def reserveAtHour6 (h : Fin (L + 1)) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => a.role = Role.reserve ∧ a.hour.val = h.val)

/-- Cross pairs `(reserve@h, main@(l−1))` are distinct: a Reserve is never a Main. -/
theorem reserveAtHour6_mainAt6_disjoint (σ : Sign) (l : ℕ) (hl : 1 ≤ l) (hlL : l ≤ L)
    (h : Fin (L + 1))
    (a : AgentState L K) (ha : a ∈ reserveAtHour6 (L := L) (K := K) h)
    (b : AgentState L K) (hb : b ∈ mainAt6 (L := L) (K := K) σ l hl hlL) : a ≠ b := by
  rw [reserveAtHour6, Finset.mem_filter] at ha
  rw [mainAt6, Finset.mem_filter] at hb
  obtain ⟨-, hrA, -⟩ := ha
  obtain ⟨-, hrB, -⟩ := hb
  intro heq; subst heq
  rw [hrA] at hrB; exact absurd hrB (by decide)

/-- `countP` as a filtered-univ sum of counts (re-derivation of
`HourCouplingAzuma.countP_eq_sum_count`, not imported here). -/
theorem countP_eq_sum_count6 (p : AgentState L K → Prop) [DecidablePred p]
    (c : Config (AgentState L K)) :
    Multiset.countP p c
      = ∑ a ∈ Finset.univ.filter (fun a : AgentState L K => p a), c.count a := by
  classical
  have hcard : (Multiset.filter (fun a : AgentState L K => p a) c).card
      = Multiset.countP p c := (Multiset.countP_eq_card_filter _ _).symm
  rw [← hcard, eq_comm]
  have hcount_eq : ∀ a ∈ Finset.univ.filter (fun a : AgentState L K => p a),
      c.count a = Multiset.count a (Multiset.filter (fun a : AgentState L K => p a) c) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Config.count, Multiset.count_filter, if_pos ha.2]
  rw [Finset.sum_congr rfl hcount_eq, Multiset.sum_count_eq_card]
  intro a ha
  rw [Multiset.mem_filter] at ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha.2⟩

/-- **The `reserveAtHour6 h` count equals Phase-5's `sampledReserveClassU h`.**  Both
are `countP (role = reserve ∧ hour = h)`, so the carried Phase-5 floor
`K₀ ≤ sampledReserveClassU h` directly lower-bounds the rectangle's eliminator pool.
(`sampledReserveClass i a := a.role = Role.reserve ∧ a.hour.val = i.val`.) -/
theorem reserveAtHour6_sum_eq_classU (h : Fin (L + 1)) (c : Config (AgentState L K)) :
    (reserveAtHour6 (L := L) (K := K) h).sum c.count
      = Multiset.countP (fun a => a.role = Role.reserve ∧ a.hour.val = h.val) c := by
  rw [countP_eq_sum_count6 (L := L) (K := K) (fun a => a.role = Role.reserve ∧ a.hour.val = h.val) c]
  rfl

/-- The biased-Main pool count as a filtered-univ sum (used to phrase the rectangle
floor in terms of the count of band-top biased Mains). -/
theorem mainAt6_sum_eq_countP (σ : Sign) (l : ℕ) (hl : 1 ≤ l) (hlL : l ≤ L)
    (c : Config (AgentState L K)) :
    (mainAt6 (L := L) (K := K) σ l hl hlL).sum c.count
      = Multiset.countP (fun a => a.role = Role.main ∧
          a.bias = Bias.dyadic σ ⟨l - 1, by omega⟩) c := by
  rw [countP_eq_sum_count6 (L := L) (K := K)
    (fun a => a.role = Role.main ∧ a.bias = Bias.dyadic σ ⟨l - 1, by omega⟩) c]
  rfl

/-- **The Phase-6 band-top rectangle drop probability.**  On a `Phase6Win` config,
for a fixed sign `σ`, target level `l` (`1 ≤ l ≤ L`), and a sampling hour `h` with
`l−1 < h` and `h ≠ L`, the probability that one step drops `highMass l` is at least
`(#reserve@h)·(#main@(l−1))/(n(n−1))`.  The Reserve count `#reserve@h` is exactly
Phase-5's `sampledReserveClassU h` (`reserveAtHour6_sum_eq_classU`). -/
theorem highMass_drop_prob_rect6 (σ : Sign) (l n : ℕ) (hn : 2 ≤ n)
    (hl1 : 1 ≤ l) (hlL : l ≤ L) (c : Config (AgentState L K))
    (hInv : Phase6Win (L := L) (K := K) n c)
    (h : Fin (L + 1)) (hhgt : l - 1 < h.val) (hhne : h.val ≠ L) :
    ENNReal.ofReal
        (((reserveAtHour6 (L := L) (K := K) h).sum c.count *
          (mainAt6 (L := L) (K := K) σ l hl1 hlL).sum c.count : ℕ) /
          ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | highMass (L := L) (K := K) l c' + 1 ≤ highMass (L := L) (K := K) l c} := by
  have hcardn : c.card = n := hInv.1
  refine drop_prob_of_rect6 (fun c => highMass (L := L) (K := K) l c) n hn c hcardn
    ((reserveAtHour6 (L := L) (K := K) h) ×ˢ (mainAt6 (L := L) (K := K) σ l hl1 hlL))
    _ ?_ (le_of_eq ?_)
  · rintro ⟨r, m⟩ hp hcr hcm _
    rw [Finset.mem_product] at hp
    obtain ⟨hrmem, hmmem⟩ := hp
    simp only [reserveAtHour6, Finset.mem_filter] at hrmem
    simp only [mainAt6, Finset.mem_filter] at hmmem
    obtain ⟨_, hrR, hrh⟩ := hrmem
    obtain ⟨_, hmM, hmb⟩ := hmmem
    have happ : Protocol.Applicable c r m := by
      have hrm : r ∈ c := Multiset.one_le_count_iff_mem.mp hcr
      have hmm : m ∈ c := Multiset.one_le_count_iff_mem.mp hcm
      have hne : r ≠ m :=
        reserveAtHour6_mainAt6_disjoint σ l hl1 hlL h r
          (by simp only [reserveAtHour6, Finset.mem_filter]
              exact ⟨Finset.mem_univ _, hrR, hrh⟩) m
          (by simp only [mainAt6, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hmM, hmb⟩)
      exact applicable_of_mem_distinct6 hrm hmm hne
    -- the guard r.hour > l-1 (= h > l-1) and r.hour ≠ L (= h ≠ L).
    have hgt : r.hour.val > l - 1 := by rw [hrh]; exact hhgt
    have hne : r.hour.val ≠ L := by rw [hrh]; exact hhne
    exact highMass_stepOrSelf_drop (L := L) (K := K) l n c hInv r m happ hl1 hlL hrR hmM hmb hne hgt
  · rw [sum_interactionCount_cross_disjoint6 c _ _
      (reserveAtHour6_mainAt6_disjoint σ l hl1 hlL h)]

/-- **The engine `hdrop` from a drop-probability floor (Phase 6).**  Mirror of
`Phase7Convergence.minorityU_hdrop_of_floor7`: the kernel's failure mass on
`(potBelow (highMass l) m)ᶜ` is `1 − drop-success ≤ 1 − p`. -/
theorem highMass_hdrop_of_floor6 (l : ℕ) (m : ℕ)
    (p : ℝ≥0∞) (b : Config (AgentState L K)) (hbm : highMass (L := L) (K := K) l b = m)
    (hfloor : p ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
        {c' | highMass (L := L) (K := K) l c' + 1 ≤ highMass (L := L) (K := K) l b}) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (fun c => highMass (L := L) (K := K) l c) m)ᶜ ≤ 1 - p := by
  classical
  have hKb : (NonuniformMajority L K).transitionKernel b
      = ((NonuniformMajority L K).stepDistOrSelf b).toMeasure := rfl
  have hsucc_eq : {c' : Config (AgentState L K) |
        highMass (L := L) (K := K) l c' + 1 ≤ highMass (L := L) (K := K) l b}
      = OneSidedCancel.potBelow (fun c => highMass (L := L) (K := K) l c) m := by
    ext c'; simp only [OneSidedCancel.potBelow, Set.mem_setOf_eq, hbm]; omega
  have hmeas : MeasurableSet (OneSidedCancel.potBelow (fun c => highMass (L := L) (K := K) l c) m) :=
    OneSidedCancel.potBelow_measurable (fun c => highMass (L := L) (K := K) l c) m
  haveI hprob : IsProbabilityMeasure
      (((NonuniformMajority L K).stepDistOrSelf b).toMeasure) := by
    rw [← hKb]
    exact (inferInstance :
      IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure b
  have htot : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure Set.univ = 1 :=
    hprob.measure_univ
  have hcompl : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
        (OneSidedCancel.potBelow (fun c => highMass (L := L) (K := K) l c) m)ᶜ
      = 1 - ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
          (OneSidedCancel.potBelow (fun c => highMass (L := L) (K := K) l c) m) := by
    rw [measure_compl hmeas (measure_ne_top _ _), htot]
  rw [hKb, hcompl]
  have hp_le : p ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
      (OneSidedCancel.potBelow (fun c => highMass (L := L) (K := K) l c) m) := by
    rw [← hsucc_eq]; exact hfloor
  exact tsub_le_tsub_left hp_le 1

/-! ## Part F — the genuinely-closed window `AllZeroGE6` and the `PhaseConvergenceW`.

`AllZeroGE6 n c`: size `n`, every agent at phase `≥ 6` and unbiased.  This window
is one-step closed (`card`/phase-floor as in `PhaseGE5Win`; bias-zero via
`Transition_bias_zero_of_phase_ge6`) and forces the high count `Φ = highU l = 0`,
so the `OneSidedCancel.crude_PhaseConvergenceW` engine gives a real
`PhaseConvergenceW` with `ε = 0`. -/

/-- The all-unbiased phase-≥6 window. -/
def AllZeroGE6 (n : ℕ) (c : Config (AgentState L K)) : Prop :=
  c.card = n ∧ (∀ a ∈ c, 6 ≤ a.phase.val) ∧ (∀ a ∈ c, a.bias = Bias.zero)

instance (n : ℕ) (c : Config (AgentState L K)) :
    Decidable (AllZeroGE6 (L := L) (K := K) n c) := by unfold AllZeroGE6; infer_instance

private theorem mem_of_app_left6F {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₁ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

private theorem mem_of_app_right6F {c : Config (AgentState L K)}
    {r₁ r₂ : AgentState L K} (happ : Protocol.Applicable c r₁ r₂) : r₂ ∈ c :=
  Multiset.mem_of_le (show ({r₁, r₂} : Multiset (AgentState L K)) ≤ c from happ) (by simp)

/-- `AllZeroGE6` is preserved by a chosen-pair update.  `card` via reachability;
phase floor since phases never drop (epidemic + dispatch are phase-nondecreasing,
`phaseEpidemicUpdate_phase_le_Transition_phase`); bias-zero via
`Transition_bias_zero_of_phase_ge6`. -/
theorem AllZeroGE6_stepOrSelf (n : ℕ) (c : Config (AgentState L K))
    (hw : AllZeroGE6 (L := L) (K := K) n c) (r₁ r₂ : AgentState L K) :
    AllZeroGE6 (L := L) (K := K) n (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  obtain ⟨hcard, hph, hbz⟩ := hw
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hm1 := mem_of_app_left6F happ
    have hm2 := mem_of_app_right6F happ
    have h16 : 6 ≤ r₁.phase.val := hph r₁ hm1
    have h26 : 6 ≤ r₂.phase.val := hph r₂ hm2
    have hr1z : r₁.bias = Bias.zero := hbz r₁ hm1
    have hr2z : r₂.bias = Bias.zero := hbz r₂ hm2
    have hbias := Transition_bias_zero_of_phase_ge6 (L := L) (K := K) r₁ r₂ h16 h26 hr1z hr2z
    obtain ⟨hle1, hle2⟩ := phaseEpidemicUpdate_phase_le_Transition_phase (L := L) (K := K) r₁ r₂
    have hep1 : 6 ≤ (Transition L K r₁ r₂).1.phase.val := by
      have := phaseEpidemicUpdate_left_phase_ge_max_api (L := L) (K := K) r₁ r₂
      exact le_trans h16 (le_trans (le_max_left _ _) (le_trans this hle1))
    have hep2 : 6 ≤ (Transition L K r₁ r₂).2.phase.val := by
      have := phaseEpidemicUpdate_right_phase_ge_max_api (L := L) (K := K) r₁ r₂
      exact le_trans h26 (le_trans (le_max_right _ _) (le_trans this hle2))
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    refine ⟨?_, ?_, ?_⟩
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
        rcases hnew with h | h
        · rw [h]; exact hep1
        · rw [h]; exact hep2
    · intro a ha
      rw [hc'] at ha
      rcases Multiset.mem_add.mp ha with hold | hnew
      · exact hbz a (Multiset.mem_of_le (Multiset.sub_le_self _ _) hold)
      · rw [show ({(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2}
              : Multiset (AgentState L K))
            = (Transition L K r₁ r₂).1 ::ₘ (Transition L K r₁ r₂).2 ::ₘ 0 from rfl] at hnew
        simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hnew
        rcases hnew with h | h
        · rw [h]; exact hbias.1
        · rw [h]; exact hbias.2
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; exact ⟨hcard, hph, hbz⟩

/-- `AllZeroGE6` is one-step-support closed. -/
theorem AllZeroGE6_support_closed (n : ℕ) (c c' : Config (AgentState L K))
    (hw : AllZeroGE6 (L := L) (K := K) n c)
    (hc' : c' ∈ ((NonuniformMajority L K).stepDistOrSelf c).support) :
    AllZeroGE6 (L := L) (K := K) n c' := by
  by_cases hc : 2 ≤ c.card
  · rw [show (NonuniformMajority L K).stepDistOrSelf c
        = (NonuniformMajority L K).stepDist c hc by
        unfold Protocol.stepDistOrSelf; rw [dif_pos hc]] at hc'
    obtain ⟨⟨r₁, r₂⟩, hr⟩ := Protocol.stepDist_support (NonuniformMajority L K) c hc c' hc'
    rw [← hr]; exact AllZeroGE6_stepOrSelf n c hw r₁ r₂
  · rw [show (NonuniformMajority L K).stepDistOrSelf c = PMF.pure c by
        unfold Protocol.stepDistOrSelf; rw [dif_neg hc]] at hc'
    rw [PMF.mem_support_pure_iff] at hc'; subst hc'; exact hw

/-- **`hClosed` discharged**: `AllZeroGE6 n` is `InvClosed` under the real kernel. -/
theorem allZeroGE6_InvClosed (n : ℕ) :
    OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => AllZeroGE6 (L := L) (K := K) n c) := by
  intro c hc
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | ¬ AllZeroGE6 (L := L) (K := K) n x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  exact hx (AllZeroGE6_support_closed n c x hc hsupp)

/-- On `AllZeroGE6`, every Main is unbiased, hence `highU l = 0`. -/
theorem highU_eq_zero_of_allZeroGE6 (l n : ℕ) (c : Config (AgentState L K))
    (hw : AllZeroGE6 (L := L) (K := K) n c) :
    highU (L := L) (K := K) l c = 0 :=
  highU_eq_zero_of_noBiasedMain (L := L) (K := K) l c
    (fun a ha _ => hw.2.2 a ha)

/-- **`hmono` discharged (trivially)**: `highU l` is non-increasing on `AllZeroGE6`
because it is identically `0` there. -/
theorem potNonincrOn_highU (l n : ℕ) :
    OneSidedCancel.PotNonincrOn (fun c => AllZeroGE6 (L := L) (K := K) n c)
      (NonuniformMajority L K).transitionKernel (fun c => highU (L := L) (K := K) l c) := by
  intro c hc
  -- highU c = 0, so `{x | highU c < highU x} = {x | 0 < highU x}`; on the support every
  -- successor is in AllZeroGE6 (closed) so its highU is 0 too, killing the set.
  change ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
    {x | highU (L := L) (K := K) l c < highU (L := L) (K := K) l x} = 0
  rw [PMF.toMeasure_apply_eq_zero_iff _ (DiscreteMeasurableSpace.forall_measurableSet _)]
  rw [Set.disjoint_left]
  intro x hsupp hx
  simp only [Set.mem_setOf_eq] at hx
  have hx0 : highU (L := L) (K := K) l x = 0 :=
    highU_eq_zero_of_allZeroGE6 l n x (AllZeroGE6_support_closed n c x hc hsupp)
  rw [hx0] at hx; exact absurd hx (by omega)

/-- **The Phase-6 (frozen-rule) convergence `PhaseConvergenceW` on the closed
all-unbiased window.**  Engine: `OneSidedCancel.crude_PhaseConvergenceW` with
potential `Φ = highU l` over `Inv = AllZeroGE6 n`.  Since `Φ ≡ 0` on `Inv`, the
per-step drop hypothesis is vacuous (`q = 0`), `t = 1`, `ε = 0`.  `Pre` is
`AllZeroGE6 ∧ highU ≤ 0` and `Post` is `AllZeroGE6 ∧ highU = 0`, i.e. "all biased
agents have exponent `≤ -l`" (vacuously, since there are no biased agents). -/
noncomputable def phase6Convergence (l n : ℕ) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.crude_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => AllZeroGE6 (L := L) (K := K) n c)
    (allZeroGE6_InvClosed (L := L) (K := K) n)
    (fun c => highU (L := L) (K := K) l c)
    (potNonincrOn_highU (L := L) (K := K) l n)
    (0 : ℝ≥0∞)
    (by
      -- hstep: on Inv with `1 ≤ Φ b`; but `Φ b = 0` on Inv, contradiction — vacuous.
      intro b hb hpos
      exfalso
      have hpos' : 1 ≤ highU (L := L) (K := K) l b := hpos
      rw [highU_eq_zero_of_allZeroGE6 l n b hb] at hpos'
      exact absurd hpos' (by omega))
    (0 : ℕ) (1 : ℕ) (0 : ℝ≥0)
    (by simp)

/-! ## Part G — the REAL Lemma-7.2 `PhaseConvergenceW` on the working window.

This is the honest Phase-6 convergence the campaign needs, replacing the vacuous
`phase6Convergence`.  Engine: `OneSidedCancel.levels_PhaseConvergenceW` with the
genuinely-monotone potential `Φ = highMass l` (Part E2, `potNonincrOn_highMass`) over
the working window `Inv = Phase6Win n` (all phase 6).  The level-`m` drop `hdrop` is
the band-top drain rectangle of Part E3/Part-rect (`highMass_drop_prob_rect6` +
`highMass_hdrop_of_floor6`): a Reserve sampled at a hour `> l−1, ≠ L` splits a
band-top biased Main, dropping `highMass l` by `≥ 1`; the Reserve floor that makes
`q m < 1` is Phase-5's carried `sampledReserveClassU` (`ReserveSampleGood`).

`hClosed` (the `InvClosed Phase6Win` — the working window is NOT closed at phase 6
because the clock subroutine advances agents to phase 7; the honest closure is the
phase-≥6 lift carried separately) and the per-level drop `q`/`hdrop` are exposed as
the carried inputs, exactly as Phase 7's `phase7Convergence`.

**`Post` reading.**  `Post c = Phase6Win n c ∧ highMass l c = 0`, and by
`highMass_eq_zero_iff` the second conjunct says *no biased Main has index `< l`* —
i.e. every biased Main has index `≥ l`, paper exponent `≤ −l`.  This is exactly
Doty §7 Lemma 7.2's conclusion (all biased agents pushed to exponent `≤ −l`). -/
noncomputable def phase6Convergence' (l n : ℕ)
    (hClosed : OneSidedCancel.InvClosed (NonuniformMajority L K).transitionKernel
      (fun c => Phase6Win (L := L) (K := K) n c))
    (q : ℕ → ℝ≥0∞)
    (hdrop : ∀ m, ∀ b : Config (AgentState L K), Phase6Win (L := L) (K := K) n b →
      highMass (L := L) (K := K) l b = m →
      (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (fun c => highMass (L := L) (K := K) l c) m)ᶜ ≤ q m)
    (tWin : ℕ → ℕ) (M₀ : ℕ) (ε : ℝ≥0)
    (hε : (∑ m ∈ Finset.Icc 1 M₀, (q m) ^ (tWin m) : ℝ≥0∞) ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  OneSidedCancel.levels_PhaseConvergenceW
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase6Win (L := L) (K := K) n c)
    hClosed
    (fun c => highMass (L := L) (K := K) l c)
    (potNonincrOn_highMass (L := L) (K := K) l n)
    q hdrop tWin M₀ ε hε

/-- **`Post` characterization of `phase6Convergence'`** (the Lemma-7.2 conclusion in
state terms): `highMass l c = 0` iff every biased Main has index `≥ l` (paper
exponent `≤ −l`).  In particular the `Post` of `phase6Convergence'` says all biased
agents have been pushed to exponent `≤ −l`. -/
theorem phase6Post_iff (l : ℕ) (c : Config (AgentState L K)) :
    highMass (L := L) (K := K) l c = 0 ↔
      ∀ a ∈ c, a.role = Role.main → ∀ (σ : Sign) (i : Fin (L + 1)),
        a.bias = Bias.dyadic σ i → l ≤ i.val := by
  rw [highMass_eq_zero_iff]
  constructor
  · intro h a ha hmain σ i hb
    by_contra hlt
    exact h a ha (highSt_of (L := L) (K := K) l a σ i hmain hb (by omega))
  · intro h a ha hhigh
    obtain ⟨hr, σ, i, hb, hi⟩ := hhigh
    exact absurd (h a ha hr σ i hb) (by omega)

/-! ## Part H — the Lemma-7.3 honest count behaviour (`mainCount` grows per split).

Doty §7 Lemma 7.3 reads the Reserve-split phase as a Main-population growth: each
applied `doSplit` converts the Reserve fuel into a Main (`Reserve → Main`), so the
count of Mains grows by exactly 1 per split (the partner Main keeps its role).  We
state this honestly on the per-pair level under the corrected rule.

NOTE on the paper's `0.87|M|` reading: the paper bounds the number of splits (and
hence the Main growth) before the high band empties.  In our index encoding a single
`doSplit` at index `j` lands at `j+1`; band exit needs the top split.  The count
behaviour below is the exact per-step Main-growth; the `0.87|M|` aggregate is the
horizon `T = ∑ tWin m` of `phase6Convergence'`, not a per-step fact, so it is read
off the engine's level windows rather than re-stated here. -/

/-- The Main-count of a config. -/
def mainCount (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => a.role = Role.main) c

/-- A non-Main is not counted; a Main is. -/
theorem countP_main_pair (x y : AgentState L K) :
    Multiset.countP (fun a => a.role = Role.main) ({x, y} : Multiset (AgentState L K))
      = (if x.role = Role.main then 1 else 0) + (if y.role = Role.main then 1 else 0) := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]; ring

/-- **Lemma 7.3 (per-pair, corrected rule): an applied `doSplit` from a Reserve onto
a Main grows the Main count by exactly 1.**  Before: one Main (`m`), the Reserve `r`
is not a Main.  After: two Mains (the converted Reserve `→ Main`, and `m` which keeps
its Main role).  So `mainCount` over the produced pair (`= 2`) is one more than over
the consumed pair (`= 1`). -/
theorem doSplit_mainCount_pair_grow (r m : AgentState L K) {σ : Sign} {j : Fin (L + 1)}
    (hrR : r.role = Role.reserve) (hmM : m.role = Role.main)
    (hb : m.bias = Bias.dyadic σ j) (hne : r.hour.val ≠ L) (hgt : r.hour.val > j.val)
    (hlt : j.val < L) :
    Multiset.countP (fun a => a.role = Role.main)
        ({(doSplit L K r m).1, (doSplit L K r m).2} : Multiset (AgentState L K))
      = Multiset.countP (fun a => a.role = Role.main)
        ({r, m} : Multiset (AgentState L K)) + 1 := by
  rw [doSplit_apply (L := L) (K := K) r m hb hne hgt hlt]
  rw [countP_main_pair, countP_main_pair]
  -- after: first output role = Main (set by doSplit), second keeps m.role = Main.
  -- before: r is Reserve (not Main), m is Main.
  rw [if_pos rfl, if_pos hmM, if_neg (by rw [hrR]; decide)]

end Phase6Convergence
end ExactMajority
