/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase 8 — witness-supply invariant transport across the 7→8 mixed seam

This file was commissioned to PUSH the `Phase8WitnessSupply` preservation group

  `{ BandClear σ (l+3) c ,  minorityU σ c + E8 ≤ majorityShallowCount σ l c }`

from the `Phase8AllMain` window to the mixed `AdvanceEpidemics.allPhaseGe 7` window
(where a chosen pair may still run the phase-7 reaction `cancelSplit`, not only the
phase-8 reaction `absorbConsume`).

## Ground-truth finding (this is the deliverable's headline)

The ADDITIVE COUNT invariant `minorityU σ + E8 ≤ majorityShallowCount σ l` is **NOT
preserved** across the mixed 7/8 seam.  There are TWO independent, machine-checked
obstructions, each of which alone breaks it:

* **Obstruction A — the LHS rises (`cancelSplit` gap-2).**  Lean's `cancelSplit`
  copies the SMALLER-index agent's sign onto BOTH outputs (Transition.lean:1334-1339).
  So when a `σ`-minority Main sits at the *smaller* index of an opposite-sign pair —
  which `BandClear σ (l+3)` does NOT forbid: a `σ`-Main at index `l+3` paired with a
  `≠σ`-Main at index `l+5` are BOTH deep, both allowed — the gap-2 branch makes BOTH
  outputs `σ`, so `minorityU` RISES by exactly `1` while `majorityShallowCount` over the
  pair is unchanged (`0`).  This is not a transcription slip: the phase-7 development
  already isolated and PROVED this exact rise
  (`Phase7Convergence.gap2_minorityU_rise_compatible_with_pos_sum`) and, precisely
  because of it, ABANDONED `minorityU` as a per-pair potential in favour of the σ-class
  dyadic MASS `classMass σ` (`Phase7Convergence`, Part J).  See
  `cancelSplit_gap2_breaks_pair_diff` below for the machine-checked violation.

* **Obstruction B — the RHS drops (phase-10 error entry).**  In the `allPhaseGe 7`
  window an agent can be promoted to the error phase 10 (`runInitsBetween` → `phaseInit
  10` → `enterPhase10`).  `enterPhase10` sets `full := true` (Transition.lean:77) while
  keeping `bias`/`role`.  `majorityShallowSt` REQUIRES `¬ full`, whereas `minoritySt` is
  `full`-blind, so a shallow `≠σ` eliminator promoted to phase 10 leaves `minorityU`
  unchanged but DROPS `majorityShallowCount` — again breaking `minorityU + E8 ≤
  majorityShallowCount`.  See `enterPhase10_drops_majorityShallow` /
  `enterPhase10_keeps_minoritySt` below.

## What DOES transport (the sound half + the fix currency)

* `BandClear σ (l+3)` itself IS robust: `cancelSplit` never manufactures a `σ`-bias at
  an index below its `σ`-inputs, and `absorbConsume`/`phaseInit`/`enterPhase10` never
  manufacture a `σ`-bias at all.  `cancelSplit_sigma_output_index_ge` /
  `bandClear_cancelSplit_pair` capture the phase-7 leg (the sound, reusable core).
* The CORRECT seam currency is `Phase7Convergence.classMass σ`, which reads only the
  bias and is per-pair non-increasing under `cancelSplit` in EVERY branch with no
  index-ordering hypothesis (`cancelSplit_classMass_pair_le`), and is invariant under the
  `full`-setting of `enterPhase10`/`absorbConsume` (`agentClassMass_enterPhase10`).  The
  recommended repair is to carry `classMass`, not the count, through the seam.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase8WitnessSupply
import Ripple.PopulationProtocol.ExactMajority.Probability.AdvanceEpidemics

namespace Ripple.PopulationProtocol.ExactMajority

namespace Phase78WitnessTransport

open scoped BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

open Phase7Convergence (minoritySt minorityU minoritySt_iff biasIsSigned)
open Phase8WitnessSupply (majorityShallowSt majorityShallowCount majorityShallowSt_dyadic
  minoritySt_dyadic countP_pair not_majShallow_bias_zero not_majShallow_full_true
  bandClear_index_deep bandCountN_eq_countP)

/-! **ROUND-1 NEGATIVE-RESULT RECORD** — Parts 1–5 below are kept verbatim as the machine-
checked record of why the v1 COUNT invariant fails on the mixed seam; the v2 MASS master
(the live seam-transport engine) lives in Parts 6 onward. -/

/-! ## Part 1 — phase/`full` sensitivity of the two count predicates.

The contract flags this as a point that "must be checked, not assumed": are the two
counting predicates phase-blind?  Answer:

* `minoritySt σ` = `role = main ∧ bias = dyadic σ _`:  phase-blind AND `full`-blind.
* `majorityShallowSt σ l` = `role = main ∧ ¬ full ∧ (shallow ≠σ bias)`:  phase-blind but
  `full`-SENSITIVE.

The `full`-sensitivity of `majorityShallowSt` is exactly what makes the phase-10 entry
(Obstruction B) break the count invariant. -/

/-- `minoritySt` ignores the `phase` field. -/
theorem minoritySt_phase_set (σ : Sign) (a : AgentState L K) (p : Fin 11) :
    minoritySt σ ({a with phase := p} : AgentState L K) ↔ minoritySt σ a := by
  rw [minoritySt_iff, minoritySt_iff]

/-- `minoritySt` ignores the `full` field. -/
theorem minoritySt_full_set (σ : Sign) (a : AgentState L K) (f : Bool) :
    minoritySt σ ({a with full := f} : AgentState L K) ↔ minoritySt σ a := by
  rw [minoritySt_iff, minoritySt_iff]

/-- `majorityShallowSt` ignores the `phase` field. -/
theorem majorityShallowSt_phase_set (σ : Sign) (l : ℕ) (a : AgentState L K) (p : Fin 11) :
    majorityShallowSt (L := L) (K := K) σ l ({a with phase := p} : AgentState L K)
      ↔ majorityShallowSt (L := L) (K := K) σ l a := by
  rw [Phase8WitnessSupply.majorityShallowSt_iff, Phase8WitnessSupply.majorityShallowSt_iff]

/-- `majorityShallowSt` is FALSE on a `full` agent — the `full`-sensitivity. -/
theorem not_majorityShallowSt_full (σ : Sign) (l : ℕ) (a : AgentState L K)
    (hf : a.full = true) : ¬ majorityShallowSt (L := L) (K := K) σ l a := by
  rw [Phase8WitnessSupply.majorityShallowSt_iff]; rintro ⟨_, hnf, _⟩; exact hnf hf

/-! ## Part 2 — the phase-10 error-entry obstruction (Obstruction B).

`enterPhase10` sets `full := true` and keeps `bias`/`role`.  Hence it preserves
`minoritySt` but destroys `majorityShallowSt`: a phase-10 promotion of a shallow `≠σ`
eliminator lowers `majorityShallowCount` without lowering `minorityU`. -/

/-- Phase-10 entry preserves the minority indicator (`bias`/`role` kept, `full`-blind). -/
theorem enterPhase10_keeps_minoritySt (σ : Sign) (a : AgentState L K) :
    minoritySt σ (enterPhase10 L K a) ↔ minoritySt σ a := by
  rw [minoritySt_iff, minoritySt_iff, enterPhase10_bias, enterPhase10_role]

/-- Phase-10 entry destroys the shallow-majority indicator (`full := true`). -/
theorem enterPhase10_drops_majorityShallow (σ : Sign) (l : ℕ) (a : AgentState L K) :
    ¬ majorityShallowSt (L := L) (K := K) σ l (enterPhase10 L K a) :=
  not_majorityShallowSt_full σ l _ (enterPhase10_full L K a)

/-! ## Part 3 — the `cancelSplit` gap-2 obstruction (Obstruction A).

`cancelSplit` on an opposite-sign pair with exponent gap exactly `2` copies the
smaller-index agent's sign onto BOTH outputs.  If that smaller-index agent is the
`σ`-minority — permitted by `BandClear σ (l+3)` whenever it and its `≠σ` partner are both
at index `≥ l+3` — then `minorityU` over the pair rises by `1`, `majorityShallowCount`
over the pair is unchanged at `0`, and the per-pair difference invariant
`shallow(in) + minority(out) ≤ shallow(out) + minority(in)` is VIOLATED. -/

/-- The exact gap-2 output shape of `cancelSplit` (mirror of the phase-7 development). -/
theorem cancelSplit_gap2_eq (σ st : Sign) (s t : AgentState L K)
    (i j : Fin (L + 1)) (hsb : s.bias = Bias.dyadic σ i) (htb : t.bias = Bias.dyadic st j)
    (hss : σ ≠ st) (hg2 : i.val + 2 = j.val) :
    cancelSplit L K s t
      = ({s with bias := .dyadic σ ⟨i.val + 1, by have := j.2; omega⟩},
         {t with bias := .dyadic σ ⟨i.val + 2, by have := j.2; omega⟩}) := by
  have hineq0 : ¬ i.val = j.val := by omega
  have hineq1 : ¬ i.val + 1 = j.val := by omega
  have hineq1' : ¬ j.val + 1 = i.val := by omega
  unfold cancelSplit
  rw [hsb, htb]
  simp only [if_pos (show σ ≠ st from hss), dif_neg hineq0, dif_neg hineq1,
    dif_neg hineq1', dif_pos hg2]

/-- **Obstruction A (machine-checked).**  Under `BandClear`-compatible hypotheses (`s`
is the `σ`-minority at a *deep* index `l+3 ≤ i`, `t` the `≠σ` partner at `j = i+2`), the
per-pair difference invariant carried by `Phase8WitnessSupply` FAILS.  The reason is that
`cancelSplit` raises the pair `minorityU` (gap-2 sign copy) while leaving the pair
`majorityShallowCount` at `0`.  This is exactly the phase-7
`gap2_minorityU_rise_compatible_with_pos_sum` phenomenon, now shown to be `BandClear`-
compatible. -/
theorem cancelSplit_gap2_breaks_pair_diff (σ st : Sign) (l : ℕ) (s t : AgentState L K)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (i j : Fin (L + 1)) (hsb : s.bias = Bias.dyadic σ i) (htb : t.bias = Bias.dyadic st j)
    (hss : σ ≠ st) (hg2 : i.val + 2 = j.val) (hdeep : l + 3 ≤ i.val) :
    ¬ (Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
          ({s, t} : Multiset (AgentState L K))
        + Multiset.countP (fun a => minoritySt σ a)
            ({(cancelSplit L K s t).1, (cancelSplit L K s t).2}
              : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
            ({(cancelSplit L K s t).1, (cancelSplit L K s t).2}
              : Multiset (AgentState L K))
        + Multiset.countP (fun a => minoritySt σ a)
            ({s, t} : Multiset (AgentState L K))) := by
  classical
  -- The minority pair-count strictly rises (the phase-7 lemma).
  have hrise := Phase7Convergence.gap2_minorityU_rise_compatible_with_pos_sum
    (L := L) (K := K) σ st s t hsM htM i j hsb htb hss hg2
  -- The shallow pair-count is `0` on the inputs.
  have hcs := cancelSplit_gap2_eq (L := L) (K := K) σ st s t i j hsb htb hss hg2
  have hshIn : Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
      ({s, t} : Multiset (AgentState L K)) = 0 := by
    rw [countP_pair]
    have h1 : ¬ majorityShallowSt (L := L) (K := K) σ l s := by
      rw [majorityShallowSt_dyadic σ l s σ i hsM hsb]; rintro ⟨_, hne, _⟩; exact hne rfl
    have h2 : ¬ majorityShallowSt (L := L) (K := K) σ l t := by
      rw [majorityShallowSt_dyadic σ l t st j htM htb]; rintro ⟨_, _, hk⟩; omega
    rw [if_neg h1, if_neg h2]
  -- The shallow pair-count is `0` on the outputs (both are `σ`-signed).
  have hshOut : Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
      ({(cancelSplit L K s t).1, (cancelSplit L K s t).2}
        : Multiset (AgentState L K)) = 0 := by
    rw [hcs, countP_pair]
    have h1 : ¬ majorityShallowSt (L := L) (K := K) σ l
        ({s with bias := (Bias.dyadic σ ⟨i.val + 1, by have := j.2; omega⟩ : Bias L)}) := by
      rw [majorityShallowSt_dyadic σ l _ σ ⟨i.val + 1, by have := j.2; omega⟩
        (by rw [hsM.symm]) rfl]
      rintro ⟨_, hne, _⟩; exact hne rfl
    have h2 : ¬ majorityShallowSt (L := L) (K := K) σ l
        ({t with bias := (Bias.dyadic σ ⟨i.val + 2, by have := j.2; omega⟩ : Bias L)}) := by
      rw [majorityShallowSt_dyadic σ l _ σ ⟨i.val + 2, by have := j.2; omega⟩
        (by rw [htM.symm]) rfl]
      rintro ⟨_, hne, _⟩; exact hne rfl
    rw [if_neg h1, if_neg h2]
  rw [hshIn, hshOut]
  omega

/-! ## Part 4 — the sound half: `BandClear` transports across the `cancelSplit` leg.

`cancelSplit` never produces a `σ`-signed bias at an index strictly below its
`σ`-signed inputs: same-index cancels to `zero`, gap-1/gap-2 move the surviving sign to a
LARGER index, and the copied sign (gap-2) lands at the larger index.  Hence, given all
`σ`-Mains in the config sit at index `≥ m`, both `cancelSplit` outputs still do — the
phase-7 leg of `BandClear`-preservation. -/

/-- If `cancelSplit`'s first output carries a `σ`-dyadic bias at index `k`, then some
input already carried a `σ`-dyadic bias at index `≤ k` (with the SAME sign `σ`).  Read
off the branches directly. -/
theorem cancelSplit_sigma_output_index_ge (σ : Sign) (m : ℕ) (s t : AgentState L K)
    (hs : ∀ k : Fin (L + 1), s.bias = Bias.dyadic σ k → m ≤ k.val)
    (ht : ∀ k : Fin (L + 1), t.bias = Bias.dyadic σ k → m ≤ k.val)
    (k : Fin (L + 1)) :
    ((cancelSplit L K s t).1.bias = Bias.dyadic σ k → m ≤ k.val)
      ∧ ((cancelSplit L K s t).2.bias = Bias.dyadic σ k → m ≤ k.val) := by
  classical
  -- The identity closer: whenever `cancelSplit = (s, t)`, both goals reduce to `hs`/`ht`.
  have hid_close : ∀ _hh : cancelSplit L K s t = (s, t),
      ((cancelSplit L K s t).1.bias = Bias.dyadic σ k → m ≤ k.val)
        ∧ ((cancelSplit L K s t).2.bias = Bias.dyadic σ k → m ≤ k.val) := by
    intro hh
    have hb1 : (cancelSplit L K s t).1.bias = s.bias := by rw [hh]
    have hb2 : (cancelSplit L K s t).2.bias = t.bias := by rw [hh]
    exact ⟨fun h => hs k (by rw [← hb1]; exact h), fun h => ht k (by rw [← hb2]; exact h)⟩
  rcases hsb : s.bias with _ | ⟨ss, i⟩
  · exact hid_close (by unfold cancelSplit; rw [hsb])
  · rcases htb : t.bias with _ | ⟨tt, j⟩
    · exact hid_close (by unfold cancelSplit; rw [hsb, htb])
    · by_cases hne : ss = tt
      · exact hid_close (by
          unfold cancelSplit
          simp only [hsb, htb, if_neg (show ¬ ss ≠ tt from by simpa using hne)])
      · have hnee : ss ≠ tt := hne
        have hjL : j.val < L + 1 := j.2
        have hiL : i.val < L + 1 := i.2
        by_cases h0 : i.val = j.val
        · have hb1 : (cancelSplit L K s t).1.bias = Bias.zero := by
            unfold cancelSplit; simp only [hsb, htb, if_pos hnee, dif_pos h0]
          have hb2 : (cancelSplit L K s t).2.bias = Bias.zero := by
            unfold cancelSplit; simp only [hsb, htb, if_pos hnee, dif_pos h0]
          refine ⟨fun h => ?_, fun h => ?_⟩
          · rw [hb1] at h; exact absurd h (by simp)
          · rw [hb2] at h; exact absurd h (by simp)
        by_cases h1 : i.val + 1 = j.val
        · -- s keeps sign `ss` at index `i+1`; t zeroes.
          have hb1 : (cancelSplit L K s t).1.bias
              = Bias.dyadic ss ⟨i.val + 1, by omega⟩ := by
            unfold cancelSplit; simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_pos h1]
          have hb2 : (cancelSplit L K s t).2.bias = Bias.zero := by
            unfold cancelSplit; simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_pos h1]
          refine ⟨fun h => ?_, fun h => ?_⟩
          · rw [hb1] at h; injection h with hsg hidx
            have hval : i.val + 1 = k.val := by simpa using congrArg Fin.val hidx
            have hm := hs i (by rw [hsb, hsg]); omega
          · rw [hb2] at h; exact absurd h (by simp)
        by_cases h1' : j.val + 1 = i.val
        · have hb1 : (cancelSplit L K s t).1.bias = Bias.zero := by
            unfold cancelSplit
            simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_pos h1']
          have hb2 : (cancelSplit L K s t).2.bias
              = Bias.dyadic tt ⟨j.val + 1, by omega⟩ := by
            unfold cancelSplit
            simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_pos h1']
          refine ⟨fun h => ?_, fun h => ?_⟩
          · rw [hb1] at h; exact absurd h (by simp)
          · rw [hb2] at h; injection h with hsg hidx
            have hval : j.val + 1 = k.val := by simpa using congrArg Fin.val hidx
            have hm := ht j (by rw [htb, hsg]); omega
        by_cases h2 : i.val + 2 = j.val
        · -- gap-2: BOTH outputs carry sign `ss` at indices `i+1`, `i+2`.
          have hb1 : (cancelSplit L K s t).1.bias
              = Bias.dyadic ss ⟨i.val + 1, by omega⟩ := by
            unfold cancelSplit
            simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_neg h1', dif_pos h2]
          have hb2 : (cancelSplit L K s t).2.bias
              = Bias.dyadic ss ⟨i.val + 2, by omega⟩ := by
            unfold cancelSplit
            simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_neg h1', dif_pos h2]
          refine ⟨fun h => ?_, fun h => ?_⟩
          · rw [hb1] at h; injection h with hsg hidx
            have hval : i.val + 1 = k.val := by simpa using congrArg Fin.val hidx
            have hm := hs i (by rw [hsb, hsg]); omega
          · rw [hb2] at h; injection h with hsg hidx
            have hval : i.val + 2 = k.val := by simpa using congrArg Fin.val hidx
            have hm := hs i (by rw [hsb, hsg]); omega
        by_cases h2' : j.val + 2 = i.val
        · -- gap-2 mirror: BOTH outputs carry sign `tt` at indices `j+2`, `j+1`.
          have hb1 : (cancelSplit L K s t).1.bias
              = Bias.dyadic tt ⟨j.val + 2, by omega⟩ := by
            unfold cancelSplit
            simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_neg h1', dif_neg h2,
              dif_pos h2']
          have hb2 : (cancelSplit L K s t).2.bias
              = Bias.dyadic tt ⟨j.val + 1, by omega⟩ := by
            unfold cancelSplit
            simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_neg h1', dif_neg h2,
              dif_pos h2']
          refine ⟨fun h => ?_, fun h => ?_⟩
          · rw [hb1] at h; injection h with hsg hidx
            have hval : j.val + 2 = k.val := by simpa using congrArg Fin.val hidx
            have hm := ht j (by rw [htb, hsg]); omega
          · rw [hb2] at h; injection h with hsg hidx
            have hval : j.val + 1 = k.val := by simpa using congrArg Fin.val hidx
            have hm := ht j (by rw [htb, hsg]); omega
        · exact hid_close (by
            unfold cancelSplit
            simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_neg h1', dif_neg h2,
              dif_neg h2'])

/-! ## Part 5 — the correct seam currency: σ-class MASS transports.

`Phase7Convergence.classMass σ` reads only the bias, is per-pair non-increasing under
`cancelSplit` in EVERY branch (`cancelSplit_classMass_pair_le`), and is invariant under
the `full`-setting that breaks the count (both `enterPhase10` and `absorbConsume` keep or
zero the bias).  This is the recommended repair for the seam invariant. -/

/-- Phase-10 entry preserves the σ-class mass (`bias`-only functional). -/
theorem agentClassMass_enterPhase10 (σ : Sign) (a : AgentState L K) :
    Phase7Convergence.agentClassMass (L := L) (K := K) σ (enterPhase10 L K a)
      = Phase7Convergence.agentClassMass (L := L) (K := K) σ a := by
  unfold Phase7Convergence.agentClassMass; rw [enterPhase10_bias]

/-! # ROUND 2 — the v2 MASS-currency seam master (the live engine)

The v1 count invariant is dead (Parts 1–5).  The v2 repair carries the σ-minority
DYADIC MASS `minorityMassL σ c = Σ_{a : σ-dyadic@i} 2^(L−i)` (`ℕ`, `phase`/`full`/`role`
blind) instead of the count:

  `{ BandClear σ (l+3) c ,  minorityMassL σ c + E8 ≤ majorityShallowCount σ l c }`

on the no-overshoot mixed window `allPhaseGe 7 n c ∧ (∀ a ∈ c, a.phase.val ≤ 8)`.
Both v1 obstructions die: the gap-2 sign copy RAISES the count but strictly LOWERS the
mass (`3·2^m < 4·2^m`), and the `phase ≤ 8` window hypothesis excludes the phase-10
error entry (`enterPhase10` is only reachable at phase caps `≥ 9`).  At the seam exit,
every σ-agent carries mass `≥ 1`, so the mass invariant DOMINATES the count invariant
and hands over seamlessly to `Phase8WitnessSupply` (`minorityU ≤ minorityMassL`). -/

/-! ## Part 6 — the v2 currency: σ-minority dyadic mass (`ℕ`, in units `2^{-L}`). -/

/-- The σ-mass a bias contributes, scaled by `2^L`: `2^(L−i)` for `dyadic σ i`,
`0` otherwise.  `ℕ`-valued mirror of `Phase7Convergence.biasClassMass`. -/
def biasMinMass (σ : Sign) (L : ℕ) : Bias L → ℕ
  | .zero => 0
  | .dyadic s i => if s = σ then 2 ^ (L - i.val) else 0

/-- The σ-mass of an agent: reads ONLY the bias (`phase`/`full`/`role` blind). -/
def agentMinMass (σ : Sign) (a : AgentState L K) : ℕ := biasMinMass σ L a.bias

/-- The σ-minority mass of a config (the v2 carried currency). -/
def minorityMassL (σ : Sign) (c : Config (AgentState L K)) : ℕ :=
  (c.map (fun a => agentMinMass σ a)).sum

theorem agentMinMass_of_dyadic (σ : Sign) (a : AgentState L K) (s : Sign) (i : Fin (L + 1))
    (hb : a.bias = Bias.dyadic s i) :
    agentMinMass σ a = if s = σ then 2 ^ (L - i.val) else 0 := by
  unfold agentMinMass; rw [hb]; rfl

theorem agentMinMass_of_zero (σ : Sign) (a : AgentState L K) (hb : a.bias = Bias.zero) :
    agentMinMass σ a = 0 := by
  unfold agentMinMass; rw [hb]; rfl

theorem agentMinMass_bias_zero (σ : Sign) (a : AgentState L K) :
    agentMinMass σ ({a with bias := Bias.zero} : AgentState L K) = 0 := rfl

theorem agentMinMass_full_set (σ : Sign) (a : AgentState L K) (f : Bool) :
    agentMinMass σ ({a with full := f} : AgentState L K) = agentMinMass σ a := rfl

/-- Every σ-minority agent carries mass at least `1` (`2^(L−i) ≥ 1`). -/
theorem one_le_agentMinMass_of_minoritySt (σ : Sign) (a : AgentState L K)
    (h : minoritySt σ a) : 1 ≤ agentMinMass σ a := by
  obtain ⟨-, i, hb⟩ := h
  rw [agentMinMass_of_dyadic σ a σ i hb, if_pos rfl]
  exact Nat.one_le_pow _ 2 (by norm_num)

/-- **Mass dominates count** — the seam-exit adapter: `minorityU σ c ≤ minorityMassL σ c`.
This is what converts the carried MASS invariant back into the COUNT invariant that
`Phase8WitnessSupply` consumes on the pure phase-8 window. -/
theorem minorityU_le_minorityMassL (σ : Sign) (c : Config (AgentState L K)) :
    minorityU σ c ≤ minorityMassL σ c := by
  classical
  refine Multiset.induction_on c ?_ ?_
  · simp [Phase7Convergence.minorityU, minorityMassL]
  · intro a s ih
    unfold Phase7Convergence.minorityU minorityMassL at ih ⊢
    rw [Multiset.countP_cons, Multiset.map_cons, Multiset.sum_cons]
    by_cases h : minoritySt σ a
    · have h1 := one_le_agentMinMass_of_minoritySt σ a h
      rw [if_pos h]; omega
    · rw [if_neg h]; omega

/-- Pair-multiset mass splits into the two agents' masses. -/
theorem massL_pair (σ : Sign) (x y : AgentState L K) :
    ((({x, y} : Multiset (AgentState L K)).map (fun a => agentMinMass σ a)).sum)
      = agentMinMass σ x + agentMinMass σ y := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  simp

/-! ## Part 7 — the `cancelSplit` mass ledger (the v2 replacement of Obstruction A).

The per-pair ledger `Sh(in) + Mass(out) ≤ Sh(out) + Mass(in)` holds for `cancelSplit`
in EVERY branch with NO deepness/BandClear hypothesis: whenever a shallow `≠σ`
eliminator is consumed the σ-mass drops by `≥ 1`, and the gap-2 sign copy (which
RAISES the σ-COUNT, Part 3) strictly LOWERS the σ-mass (`3·2^m < 4·2^m`). -/

theorem cancelSplit_massShallow_pair_diff (σ : Sign) (l : ℕ) (s t : AgentState L K)
    (hsM : s.role = Role.main) (htM : t.role = Role.main) :
    Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
        ({s, t} : Multiset (AgentState L K))
      + ((({(cancelSplit L K s t).1, (cancelSplit L K s t).2} : Multiset (AgentState L K)).map
          (fun a => agentMinMass σ a)).sum)
    ≤ Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
          ({(cancelSplit L K s t).1, (cancelSplit L K s t).2} : Multiset (AgentState L K))
      + ((({s, t} : Multiset (AgentState L K)).map (fun a => agentMinMass σ a)).sum) := by
  classical
  have hid : ∀ _hh : cancelSplit L K s t = (s, t),
      Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
          ({s, t} : Multiset (AgentState L K))
        + ((({(cancelSplit L K s t).1, (cancelSplit L K s t).2}
              : Multiset (AgentState L K)).map (fun a => agentMinMass σ a)).sum)
      ≤ Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
            ({(cancelSplit L K s t).1, (cancelSplit L K s t).2} : Multiset (AgentState L K))
        + ((({s, t} : Multiset (AgentState L K)).map (fun a => agentMinMass σ a)).sum) := by
    intro hh; rw [hh]
  rcases hsb : s.bias with _ | ⟨ss, i⟩
  · exact hid (by unfold cancelSplit; rw [hsb])
  · rcases htb : t.bias with _ | ⟨tt, j⟩
    · exact hid (by unfold cancelSplit; rw [hsb, htb])
    · by_cases hne : ss = tt
      · exact hid (by
          unfold cancelSplit
          simp only [hsb, htb, if_neg (show ¬ ss ≠ tt from by simpa using hne)])
      · have hnee : ss ≠ tt := hne
        have hiL : i.val < L + 1 := i.2
        have hjL : j.val < L + 1 := j.2
        have hmS := agentMinMass_of_dyadic σ s ss i hsb
        have hmT := agentMinMass_of_dyadic σ t tt j htb
        have hShS := majorityShallowSt_dyadic (L := L) (K := K) σ l s ss i hsM hsb
        have hShT := majorityShallowSt_dyadic (L := L) (K := K) σ l t tt j htM htb
        by_cases h0 : i.val = j.val
        · -- same index: both zero out.
          have hcs : cancelSplit L K s t
              = ({s with bias := .zero}, {t with bias := .zero}) := by
            unfold cancelSplit; simp only [hsb, htb, if_pos hnee, dif_pos h0]
          rw [hcs, countP_pair, countP_pair, massL_pair, massL_pair,
            agentMinMass_bias_zero, agentMinMass_bias_zero, hmS, hmT,
            if_neg (not_majShallow_bias_zero σ l s), if_neg (not_majShallow_bias_zero σ l t)]
          by_cases hss : ss = σ
          · have hs0 : ¬ majorityShallowSt (L := L) (K := K) σ l s := by
              rw [hShS]; rintro ⟨_, hne', _⟩; exact hne' hss
            have htne : ¬ tt = σ := fun h => hnee (hss.trans h.symm)
            have h1 : (1:ℕ) ≤ 2 ^ (L - i.val) := Nat.one_le_pow _ 2 (by norm_num)
            rw [if_neg hs0, if_pos hss, if_neg htne]
            split_ifs <;> omega
          · have htt : tt = σ := by revert hss hnee; cases σ <;> cases ss <;> cases tt <;> decide
            have ht0 : ¬ majorityShallowSt (L := L) (K := K) σ l t := by
              rw [hShT]; rintro ⟨_, hne', _⟩; exact hne' htt
            have h1 : (1:ℕ) ≤ 2 ^ (L - j.val) := Nat.one_le_pow _ 2 (by norm_num)
            rw [if_neg ht0, if_neg hss, if_pos htt]
            split_ifs <;> omega
        · by_cases h1 : i.val + 1 = j.val
          · -- gap-1, `s` at the smaller index: `s` moves to `i+1`, `t` zeroes.
            have hcs : cancelSplit L K s t
                = ({s with bias := .dyadic ss ⟨i.val + 1, by omega⟩},
                   {t with bias := .zero}) := by
              unfold cancelSplit; simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_pos h1]
            have hmO1 : agentMinMass σ
                ({s with bias := (Bias.dyadic ss ⟨i.val + 1, by omega⟩ : Bias L)})
                  = if ss = σ then 2 ^ (L - (i.val + 1)) else 0 :=
              agentMinMass_of_dyadic σ _ ss ⟨i.val + 1, by omega⟩ rfl
            have hShO1 := majorityShallowSt_dyadic (L := L) (K := K) σ l
              ({s with bias := (Bias.dyadic ss ⟨i.val + 1, by omega⟩ : Bias L)})
              ss ⟨i.val + 1, by omega⟩ hsM rfl
            rw [hcs, countP_pair, countP_pair, massL_pair, massL_pair,
              agentMinMass_bias_zero, hmO1, hmS, hmT,
              if_neg (not_majShallow_bias_zero σ l t)]
            by_cases hss : ss = σ
            · have hs0 : ¬ majorityShallowSt (L := L) (K := K) σ l s := by
                rw [hShS]; rintro ⟨_, hne', _⟩; exact hne' hss
              have ho10 : ¬ majorityShallowSt (L := L) (K := K) σ l
                  ({s with bias := (Bias.dyadic ss ⟨i.val + 1, by omega⟩ : Bias L)}) := by
                rw [hShO1]; rintro ⟨_, hne', _⟩; exact hne' hss
              have htne : ¬ tt = σ := fun h => hnee (hss.trans h.symm)
              have hpow : 2 ^ (L - i.val) = 2 * 2 ^ (L - (i.val + 1)) := by
                rw [show L - i.val = (L - (i.val + 1)) + 1 from by omega, pow_succ]; ring
              have hone : (1:ℕ) ≤ 2 ^ (L - (i.val + 1)) := Nat.one_le_pow _ 2 (by norm_num)
              rw [if_neg hs0, if_neg ho10, if_pos hss, if_pos hss, if_neg htne]
              split_ifs <;> omega
            · have htt : tt = σ := by
                revert hss hnee; cases σ <;> cases ss <;> cases tt <;> decide
              have ht0 : ¬ majorityShallowSt (L := L) (K := K) σ l t := by
                rw [hShT]; rintro ⟨_, hne', _⟩; exact hne' htt
              have hone : (1:ℕ) ≤ 2 ^ (L - j.val) := Nat.one_le_pow _ 2 (by norm_num)
              rw [if_neg ht0, if_neg hss, if_neg hss, if_pos htt]
              split_ifs <;> omega
          · by_cases h1' : j.val + 1 = i.val
            · -- gap-1 mirror, `t` at the smaller index: `t` moves to `j+1`, `s` zeroes.
              have hcs : cancelSplit L K s t
                  = ({s with bias := .zero},
                     {t with bias := .dyadic tt ⟨j.val + 1, by omega⟩}) := by
                unfold cancelSplit
                simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_pos h1']
              have hmO2 : agentMinMass σ
                  ({t with bias := (Bias.dyadic tt ⟨j.val + 1, by omega⟩ : Bias L)})
                    = if tt = σ then 2 ^ (L - (j.val + 1)) else 0 :=
                agentMinMass_of_dyadic σ _ tt ⟨j.val + 1, by omega⟩ rfl
              have hShO2 := majorityShallowSt_dyadic (L := L) (K := K) σ l
                ({t with bias := (Bias.dyadic tt ⟨j.val + 1, by omega⟩ : Bias L)})
                tt ⟨j.val + 1, by omega⟩ htM rfl
              rw [hcs, countP_pair, countP_pair, massL_pair, massL_pair,
                agentMinMass_bias_zero, hmO2, hmS, hmT,
                if_neg (not_majShallow_bias_zero σ l s)]
              by_cases htt : tt = σ
              · have ht0 : ¬ majorityShallowSt (L := L) (K := K) σ l t := by
                  rw [hShT]; rintro ⟨_, hne', _⟩; exact hne' htt
                have ho20 : ¬ majorityShallowSt (L := L) (K := K) σ l
                    ({t with bias := (Bias.dyadic tt ⟨j.val + 1, by omega⟩ : Bias L)}) := by
                  rw [hShO2]; rintro ⟨_, hne', _⟩; exact hne' htt
                have hsne : ¬ ss = σ := fun h => hnee (h.trans htt.symm)
                have hpow : 2 ^ (L - j.val) = 2 * 2 ^ (L - (j.val + 1)) := by
                  rw [show L - j.val = (L - (j.val + 1)) + 1 from by omega, pow_succ]; ring
                have hone : (1:ℕ) ≤ 2 ^ (L - (j.val + 1)) := Nat.one_le_pow _ 2 (by norm_num)
                rw [if_neg ht0, if_neg ho20, if_pos htt, if_pos htt, if_neg hsne]
                split_ifs <;> omega
              · have hss : ss = σ := by
                  revert htt hnee; cases σ <;> cases ss <;> cases tt <;> decide
                have hs0 : ¬ majorityShallowSt (L := L) (K := K) σ l s := by
                  rw [hShS]; rintro ⟨_, hne', _⟩; exact hne' hss
                have hone : (1:ℕ) ≤ 2 ^ (L - i.val) := Nat.one_le_pow _ 2 (by norm_num)
                rw [if_neg hs0, if_neg htt, if_neg htt, if_pos hss]
                split_ifs <;> omega
            · by_cases h2 : i.val + 2 = j.val
              · -- gap-2, `s` at the smaller index: BOTH outputs take sign `ss`.
                have hcs : cancelSplit L K s t
                    = ({s with bias := .dyadic ss ⟨i.val + 1, by omega⟩},
                       {t with bias := .dyadic ss ⟨i.val + 2, by omega⟩}) := by
                  unfold cancelSplit
                  simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_neg h1',
                    dif_pos h2]
                have hmO1 : agentMinMass σ
                    ({s with bias := (Bias.dyadic ss ⟨i.val + 1, by omega⟩ : Bias L)})
                      = if ss = σ then 2 ^ (L - (i.val + 1)) else 0 :=
                  agentMinMass_of_dyadic σ _ ss ⟨i.val + 1, by omega⟩ rfl
                have hmO2 : agentMinMass σ
                    ({t with bias := (Bias.dyadic ss ⟨i.val + 2, by omega⟩ : Bias L)})
                      = if ss = σ then 2 ^ (L - (i.val + 2)) else 0 :=
                  agentMinMass_of_dyadic σ _ ss ⟨i.val + 2, by omega⟩ rfl
                have hShO1 := majorityShallowSt_dyadic (L := L) (K := K) σ l
                  ({s with bias := (Bias.dyadic ss ⟨i.val + 1, by omega⟩ : Bias L)})
                  ss ⟨i.val + 1, by omega⟩ hsM rfl
                have hShO2 := majorityShallowSt_dyadic (L := L) (K := K) σ l
                  ({t with bias := (Bias.dyadic ss ⟨i.val + 2, by omega⟩ : Bias L)})
                  ss ⟨i.val + 2, by omega⟩ htM rfl
                rw [hcs, countP_pair, countP_pair, massL_pair, massL_pair,
                  hmO1, hmO2, hmS, hmT]
                by_cases hss : ss = σ
                · have hs0 : ¬ majorityShallowSt (L := L) (K := K) σ l s := by
                    rw [hShS]; rintro ⟨_, hne', _⟩; exact hne' hss
                  have ho10 : ¬ majorityShallowSt (L := L) (K := K) σ l
                      ({s with bias := (Bias.dyadic ss ⟨i.val + 1, by omega⟩ : Bias L)}) := by
                    rw [hShO1]; rintro ⟨_, hne', _⟩; exact hne' hss
                  have ho20 : ¬ majorityShallowSt (L := L) (K := K) σ l
                      ({t with bias := (Bias.dyadic ss ⟨i.val + 2, by omega⟩ : Bias L)}) := by
                    rw [hShO2]; rintro ⟨_, hne', _⟩; exact hne' hss
                  have htne : ¬ tt = σ := fun h => hnee (hss.trans h.symm)
                  have hp2 : 2 ^ (L - i.val) = 4 * 2 ^ (L - (i.val + 2)) := by
                    rw [show L - i.val = (L - (i.val + 2)) + 2 from by omega,
                      pow_succ, pow_succ]; ring
                  have hp1 : 2 ^ (L - (i.val + 1)) = 2 * 2 ^ (L - (i.val + 2)) := by
                    rw [show L - (i.val + 1) = (L - (i.val + 2)) + 1 from by omega,
                      pow_succ]; ring
                  have hone : (1:ℕ) ≤ 2 ^ (L - (i.val + 2)) := Nat.one_le_pow _ 2 (by norm_num)
                  rw [if_neg hs0, if_neg ho10, if_neg ho20, if_pos hss, if_pos hss,
                    if_pos hss, if_neg htne]
                  split_ifs <;> omega
                · have htt : tt = σ := by
                    revert hss hnee; cases σ <;> cases ss <;> cases tt <;> decide
                  have ht0 : ¬ majorityShallowSt (L := L) (K := K) σ l t := by
                    rw [hShT]; rintro ⟨_, hne', _⟩; exact hne' htt
                  have hone : (1:ℕ) ≤ 2 ^ (L - j.val) := Nat.one_le_pow _ 2 (by norm_num)
                  rw [if_neg ht0, if_neg hss, if_neg hss, if_neg hss, if_pos htt]
                  split_ifs <;> omega
              · by_cases h2' : j.val + 2 = i.val
                · -- gap-2 mirror, `t` at the smaller index: BOTH outputs take sign `tt`.
                  have hcs : cancelSplit L K s t
                      = ({s with bias := .dyadic tt ⟨j.val + 2, by omega⟩},
                         {t with bias := .dyadic tt ⟨j.val + 1, by omega⟩}) := by
                    unfold cancelSplit
                    simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_neg h1',
                      dif_neg h2, dif_pos h2']
                  have hmO1 : agentMinMass σ
                      ({s with bias := (Bias.dyadic tt ⟨j.val + 2, by omega⟩ : Bias L)})
                        = if tt = σ then 2 ^ (L - (j.val + 2)) else 0 :=
                    agentMinMass_of_dyadic σ _ tt ⟨j.val + 2, by omega⟩ rfl
                  have hmO2 : agentMinMass σ
                      ({t with bias := (Bias.dyadic tt ⟨j.val + 1, by omega⟩ : Bias L)})
                        = if tt = σ then 2 ^ (L - (j.val + 1)) else 0 :=
                    agentMinMass_of_dyadic σ _ tt ⟨j.val + 1, by omega⟩ rfl
                  have hShO1 := majorityShallowSt_dyadic (L := L) (K := K) σ l
                    ({s with bias := (Bias.dyadic tt ⟨j.val + 2, by omega⟩ : Bias L)})
                    tt ⟨j.val + 2, by omega⟩ hsM rfl
                  have hShO2 := majorityShallowSt_dyadic (L := L) (K := K) σ l
                    ({t with bias := (Bias.dyadic tt ⟨j.val + 1, by omega⟩ : Bias L)})
                    tt ⟨j.val + 1, by omega⟩ htM rfl
                  rw [hcs, countP_pair, countP_pair, massL_pair, massL_pair,
                    hmO1, hmO2, hmS, hmT]
                  by_cases htt : tt = σ
                  · have ht0 : ¬ majorityShallowSt (L := L) (K := K) σ l t := by
                      rw [hShT]; rintro ⟨_, hne', _⟩; exact hne' htt
                    have ho10 : ¬ majorityShallowSt (L := L) (K := K) σ l
                        ({s with bias := (Bias.dyadic tt ⟨j.val + 2, by omega⟩ : Bias L)}) := by
                      rw [hShO1]; rintro ⟨_, hne', _⟩; exact hne' htt
                    have ho20 : ¬ majorityShallowSt (L := L) (K := K) σ l
                        ({t with bias := (Bias.dyadic tt ⟨j.val + 1, by omega⟩ : Bias L)}) := by
                      rw [hShO2]; rintro ⟨_, hne', _⟩; exact hne' htt
                    have hsne : ¬ ss = σ := fun h => hnee (h.trans htt.symm)
                    have hp2 : 2 ^ (L - j.val) = 4 * 2 ^ (L - (j.val + 2)) := by
                      rw [show L - j.val = (L - (j.val + 2)) + 2 from by omega,
                        pow_succ, pow_succ]; ring
                    have hp1 : 2 ^ (L - (j.val + 1)) = 2 * 2 ^ (L - (j.val + 2)) := by
                      rw [show L - (j.val + 1) = (L - (j.val + 2)) + 1 from by omega,
                        pow_succ]; ring
                    have hone : (1:ℕ) ≤ 2 ^ (L - (j.val + 2)) :=
                      Nat.one_le_pow _ 2 (by norm_num)
                    rw [if_neg ht0, if_neg ho10, if_neg ho20, if_pos htt, if_pos htt,
                      if_pos htt, if_neg hsne]
                    split_ifs <;> omega
                  · have hss : ss = σ := by
                      revert htt hnee; cases σ <;> cases ss <;> cases tt <;> decide
                    have hs0 : ¬ majorityShallowSt (L := L) (K := K) σ l s := by
                      rw [hShS]; rintro ⟨_, hne', _⟩; exact hne' hss
                    have hone : (1:ℕ) ≤ 2 ^ (L - i.val) := Nat.one_le_pow _ 2 (by norm_num)
                    rw [if_neg hs0, if_neg htt, if_neg htt, if_neg htt, if_pos hss]
                    split_ifs <;> omega
                · exact hid (by
                    unfold cancelSplit
                    simp only [hsb, htb, if_pos hnee, dif_neg h0, dif_neg h1, dif_neg h1',
                      dif_neg h2, dif_neg h2'])

/-! ## Part 8 — the `absorbConsume` mass ledger (needs the σ-deep hypothesis).

Unlike `cancelSplit`, the `absorbConsume` ledger DOES need deepness: when the σ-agent
is the CONSUMER (smaller index), the consumed `≠σ` partner could be shallow and the
σ-mass would not drop.  Deepness (`σ` sits at index `≥ l+3`) pushes the strictly deeper
partner out of the shallow band, exactly as in the v1 count lemma. -/

theorem absorbConsume_massShallow_pair_diff (σ : Sign) (l : ℕ) (s t : AgentState L K)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (hs : ∀ k : Fin (L + 1), s.bias = Bias.dyadic σ k → l + 3 ≤ k.val)
    (ht : ∀ k : Fin (L + 1), t.bias = Bias.dyadic σ k → l + 3 ≤ k.val) :
    Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
        ({s, t} : Multiset (AgentState L K))
      + ((({(absorbConsume L K s t).1, (absorbConsume L K s t).2}
            : Multiset (AgentState L K)).map (fun a => agentMinMass σ a)).sum)
    ≤ Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
          ({(absorbConsume L K s t).1, (absorbConsume L K s t).2}
            : Multiset (AgentState L K))
      + ((({s, t} : Multiset (AgentState L K)).map (fun a => agentMinMass σ a)).sum) := by
  classical
  have hid : ∀ _hh : absorbConsume L K s t = (s, t),
      Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
          ({s, t} : Multiset (AgentState L K))
        + ((({(absorbConsume L K s t).1, (absorbConsume L K s t).2}
              : Multiset (AgentState L K)).map (fun a => agentMinMass σ a)).sum)
      ≤ Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
            ({(absorbConsume L K s t).1, (absorbConsume L K s t).2}
              : Multiset (AgentState L K))
        + ((({s, t} : Multiset (AgentState L K)).map (fun a => agentMinMass σ a)).sum) := by
    intro hh; rw [hh]
  -- The two firing shapes, handled once via a local closer.
  have hfire1 : ∀ (ss st : Sign) (i j : Fin (L + 1)),
      s.bias = Bias.dyadic ss i → t.bias = Bias.dyadic st j → ss ≠ st → i.val < j.val →
      absorbConsume L K s t = ({s with full := true}, {t with bias := Bias.zero}) →
      Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
          ({s, t} : Multiset (AgentState L K))
        + ((({(absorbConsume L K s t).1, (absorbConsume L K s t).2}
              : Multiset (AgentState L K)).map (fun a => agentMinMass σ a)).sum)
      ≤ Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
            ({(absorbConsume L K s t).1, (absorbConsume L K s t).2}
              : Multiset (AgentState L K))
        + ((({s, t} : Multiset (AgentState L K)).map (fun a => agentMinMass σ a)).sum) := by
    intro ss st i j hsb htb hopp hij habs
    have hmS := agentMinMass_of_dyadic σ s ss i hsb
    have hmT := agentMinMass_of_dyadic σ t st j htb
    have hShS := majorityShallowSt_dyadic (L := L) (K := K) σ l s ss i hsM hsb
    have hShT := majorityShallowSt_dyadic (L := L) (K := K) σ l t st j htM htb
    rw [habs, countP_pair, countP_pair, massL_pair, massL_pair,
      agentMinMass_full_set, agentMinMass_bias_zero, hmS, hmT,
      if_neg (not_majShallow_full_true σ l s), if_neg (not_majShallow_bias_zero σ l t)]
    by_cases hss : ss = σ
    · -- σ is the CONSUMER: deepness forces the (strictly deeper) partner non-shallow.
      have hdeep : l + 3 ≤ i.val := hs i (by rw [hsb, hss])
      have hs0 : ¬ majorityShallowSt (L := L) (K := K) σ l s := by
        rw [hShS]; rintro ⟨_, hne', _⟩; exact hne' hss
      have ht0 : ¬ majorityShallowSt (L := L) (K := K) σ l t := by
        rw [hShT]; rintro ⟨_, _, hk⟩; omega
      have htne : ¬ st = σ := fun h => hopp (hss.trans h.symm)
      rw [if_neg hs0, if_neg ht0, if_pos hss, if_neg htne]
    · -- σ is CONSUMED: the σ-mass drops by `2^(L−j) ≥ 1`, absorbing the shallow drop.
      have htt : st = σ := by revert hss hopp; cases σ <;> cases ss <;> cases st <;> decide
      have ht0 : ¬ majorityShallowSt (L := L) (K := K) σ l t := by
        rw [hShT]; rintro ⟨_, hne', _⟩; exact hne' htt
      have hone : (1:ℕ) ≤ 2 ^ (L - j.val) := Nat.one_le_pow _ 2 (by norm_num)
      rw [if_neg ht0, if_neg hss, if_pos htt]
      split_ifs <;> omega
  have hfire2 : ∀ (ss st : Sign) (i j : Fin (L + 1)),
      s.bias = Bias.dyadic ss i → t.bias = Bias.dyadic st j → ss ≠ st → j.val < i.val →
      absorbConsume L K s t = ({s with bias := Bias.zero}, {t with full := true}) →
      Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
          ({s, t} : Multiset (AgentState L K))
        + ((({(absorbConsume L K s t).1, (absorbConsume L K s t).2}
              : Multiset (AgentState L K)).map (fun a => agentMinMass σ a)).sum)
      ≤ Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
            ({(absorbConsume L K s t).1, (absorbConsume L K s t).2}
              : Multiset (AgentState L K))
        + ((({s, t} : Multiset (AgentState L K)).map (fun a => agentMinMass σ a)).sum) := by
    intro ss st i j hsb htb hopp hji habs
    have hmS := agentMinMass_of_dyadic σ s ss i hsb
    have hmT := agentMinMass_of_dyadic σ t st j htb
    have hShS := majorityShallowSt_dyadic (L := L) (K := K) σ l s ss i hsM hsb
    have hShT := majorityShallowSt_dyadic (L := L) (K := K) σ l t st j htM htb
    rw [habs, countP_pair, countP_pair, massL_pair, massL_pair,
      agentMinMass_bias_zero, agentMinMass_full_set, hmS, hmT,
      if_neg (not_majShallow_bias_zero σ l s), if_neg (not_majShallow_full_true σ l t)]
    by_cases htt : st = σ
    · -- σ is the CONSUMER (at the smaller index `j`).
      have hdeep : l + 3 ≤ j.val := ht j (by rw [htb, htt])
      have ht0 : ¬ majorityShallowSt (L := L) (K := K) σ l t := by
        rw [hShT]; rintro ⟨_, hne', _⟩; exact hne' htt
      have hs0 : ¬ majorityShallowSt (L := L) (K := K) σ l s := by
        rw [hShS]; rintro ⟨_, _, hk⟩; omega
      have hsne : ¬ ss = σ := fun h => hopp (h.trans htt.symm)
      rw [if_neg hs0, if_neg ht0, if_neg hsne, if_pos htt]
    · -- σ is CONSUMED (at the larger index `i`).
      have hss : ss = σ := by revert htt hopp; cases σ <;> cases ss <;> cases st <;> decide
      have hs0 : ¬ majorityShallowSt (L := L) (K := K) σ l s := by
        rw [hShS]; rintro ⟨_, hne', _⟩; exact hne' hss
      have hone : (1:ℕ) ≤ 2 ^ (L - i.val) := Nat.one_le_pow _ 2 (by norm_num)
      rw [if_neg hs0, if_pos hss, if_neg htt]
      split_ifs <;> omega
  rcases hsb : s.bias with _ | ⟨ss, i⟩
  · exact hid (by unfold absorbConsume; simp only [hsb])
  · rcases htb : t.bias with _ | ⟨tt, j⟩
    · exact hid (by unfold absorbConsume; simp only [hsb, htb])
    · rcases ss with _ | _ <;> rcases tt with _ | _
      · exact hid (by unfold absorbConsume; simp only [hsb, htb])
      · by_cases hcase : i.val < j.val ∧ ¬ s.full
        · exact hfire1 Sign.pos Sign.neg i j hsb htb (by decide) hcase.1
            (by unfold absorbConsume; simp only [hsb, htb]; rw [if_pos hcase])
        · by_cases hcase2 : j.val < i.val ∧ ¬ t.full
          · exact hfire2 Sign.pos Sign.neg i j hsb htb (by decide) hcase2.1
              (by unfold absorbConsume; simp only [hsb, htb]; rw [if_neg hcase, if_pos hcase2])
          · exact hid (by
              unfold absorbConsume
              simp only [hsb, htb]; rw [if_neg hcase, if_neg hcase2])
      · by_cases hcase : i.val < j.val ∧ ¬ s.full
        · exact hfire1 Sign.neg Sign.pos i j hsb htb (by decide) hcase.1
            (by unfold absorbConsume; simp only [hsb, htb]; rw [if_pos hcase])
        · by_cases hcase2 : j.val < i.val ∧ ¬ t.full
          · exact hfire2 Sign.neg Sign.pos i j hsb htb (by decide) hcase2.1
              (by unfold absorbConsume; simp only [hsb, htb]; rw [if_neg hcase, if_pos hcase2])
          · exact hid (by
              unfold absorbConsume
              simp only [hsb, htb]; rw [if_neg hcase, if_neg hcase2])
      · exact hid (by unfold absorbConsume; simp only [hsb, htb])

end Phase78WitnessTransport

end Ripple.PopulationProtocol.ExactMajority
