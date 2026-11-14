/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase 8 — slot-8 witness SUPPLY (producer side, Doty et al. Lemma 7.6)

`Phase8DrainReady.witness` (Slot678SurvivalInputs:336) requires, from a live
minority (`minorityU σ c ≥ 1`), a level `i` with a live minority *and* an
`E8`-floor of above-level eliminators (`elimAbove σ i`, index `< i`).  After the
2026-07-16 `elimAbove` semantic flip this witness is non-vacuous but has no
producer.  This file supplies it from a *pure config-layer* eliminator floor.

## What is delivered

* `majorityShallowCount σ l c` — the count of non-`full`, opposite-sign (`≠ σ`)
  Mains whose exponent index is `≤ l+2` (the paper's surviving majority block,
  Lemma 7.4/7.5).  Shape-aligned to `minorityU` (a `Multiset.countP`).
* `phase8DrainReady_witness_of_shallowFloor` — the **witness export theorem**:
  `BandClear σ (l+3) c` (all surviving minority at index `≥ l+3`)
  `+ E8 ≤ majorityShallowCount σ l c` `+ minorityU σ c ≥ 1`
  gives the `Phase8DrainReady.witness` conclusion.  Pure finset-count inclusion:
  every shallow (`index ≤ l+2`) majority member lies below the (`index ≥ l+3`)
  minority level, hence inside `elimAbove σ i`.  No probability content.
* The **preservation lemma group** (invariants closed under `Phase8Transition`):
  - `absorbConsume_shallowMinority_pair_diff` — under the `σ`-deep hypothesis, the
    pair effect `mShallow(in) + mMinority(out) ≤ mShallow(out) + mMinority(in)`
    (the difference `mShallow − mMinority` is non-decreasing on every pair);
  - `bandClear_stepOrSelf` — `BandClear σ (l+3)` is preserved by `stepOrSelf`;
  - `shallowMinority_diff_stepOrSelf` / `shallowMinorityReady_stepOrSelf` — the carried
    pair invariant `minorityU σ + E8 ≤ majorityShallowCount σ l` (together with
    `BandClear`) is preserved on the genuine phase-8 window.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.ExactMajority.Probability.Phase8Convergence
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase7BandDefs
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6Convergence

namespace Ripple.PopulationProtocol.ExactMajority

namespace Phase8WitnessSupply

open scoped BigOperators

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

open Phase7Convergence (minoritySt minorityU minoritySt_iff biasIsSigned
  countP_minoritySt_pair not_minoritySt_of_not_main)

/-! ## Part 1 — the shallow-majority floor count. -/

/-- A **shallow majority** agent (sign `σ` = the minority sign): a non-`full` Main
holding an opposite-sign (`≠ σ`) dyadic bias whose exponent index is `≤ l + 2`.
This is the paper's surviving majority block (Lemma 7.4/7.5: exponents in
`{−l, −(l+1), −(l+2)}`, i.e. Lean index `≤ l+2`), the pool that eliminates the
deep (`index ≥ l+3`) minority. -/
def majorityShallowSt (σ : Sign) (l : ℕ) (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ ¬ a.full ∧
    ∃ (st : Sign) (j : Fin (L + 1)), st ≠ σ ∧ j.val ≤ l + 2 ∧ a.bias = Bias.dyadic st j

/-- The shallow-majority count (the `E8` floor source, aligned to `minorityU`). -/
noncomputable def majorityShallowCount (σ : Sign) (l : ℕ) (c : Config (AgentState L K)) : ℕ :=
  Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a) c

/-- A bias-side characterization of `majorityShallowSt` (removes the existential,
so the indicator is a decidable `match` on `role`/`full`/`bias`). -/
def shallowBias (σ : Sign) (l : ℕ) (b : Bias L) : Prop :=
  match b with
  | .zero => False
  | .dyadic s j => s ≠ σ ∧ j.val ≤ l + 2

theorem majorityShallowSt_iff (σ : Sign) (l : ℕ) (a : AgentState L K) :
    majorityShallowSt (L := L) (K := K) σ l a ↔
      a.role = Role.main ∧ ¬ a.full ∧ shallowBias (L := L) σ l a.bias := by
  unfold majorityShallowSt shallowBias
  cases hb : a.bias with
  | zero =>
      constructor
      · rintro ⟨_, _, _, _, _, _, hbz⟩; exact absurd hbz (by simp)
      · rintro ⟨_, _, hf⟩; exact hf.elim
  | dyadic s j =>
      constructor
      · rintro ⟨hr, hf, st, k, hst, hk, hbias⟩
        injection hbias with hs hk'; subst hs; subst hk'
        exact ⟨hr, hf, hst, hk⟩
      · rintro ⟨hr, hf, hst, hk⟩
        exact ⟨hr, hf, s, j, hst, hk, rfl⟩

/-- `majorityShallowCount` as a sum of per-state count over the shallow filter. -/
theorem majorityShallowCount_eq_sum (σ : Sign) (l : ℕ) (c : Config (AgentState L K)) :
    majorityShallowCount (L := L) (K := K) σ l c =
      ∑ a ∈ Finset.univ.filter (fun a => majorityShallowSt (L := L) (K := K) σ l a),
        c.count a :=
  Phase6Convergence.countP_eq_sum_count6 (L := L) (K := K)
    (fun a => majorityShallowSt (L := L) (K := K) σ l a) c

/-! ## Part 2 — the witness export theorem (pure config-layer count inclusion). -/

/-- Every shallow-majority state lies in `elimAbove σ i` for any minority level
`i` with `l + 3 ≤ i.val` (its index `≤ l+2 < l+3 ≤ i.val`). -/
theorem majorityShallow_filter_subset_elimAbove (σ : Sign) (l : ℕ) (i : Fin (L + 1))
    (hi : l + 3 ≤ i.val) :
    Finset.univ.filter (fun a => majorityShallowSt (L := L) (K := K) σ l a) ⊆
      Phase8Convergence.elimAbove (L := L) (K := K) σ i := by
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  obtain ⟨hr, hf, st, j, hst, hj, hb⟩ := ha
  simp only [Phase8Convergence.elimAbove, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hr, hf, st, j, hst, by omega, hb⟩

/-- **Witness export.**  From band clearance (`BandClear σ (l+3) c`: every live
minority sits at index `≥ l+3`), a shallow-majority floor (`E8 ≤ majorityShallowCount`)
and a live minority (`minorityU σ c ≥ 1`), produce the `Phase8DrainReady.witness`
conclusion: a level `i` with a live minority and `E8` above-level eliminators.

Pure config-layer count inclusion (no probability).  Proof core: the minority
witness sits at some index `i`; `BandClear` forces `i.val ≥ l+3`; every shallow
majority member (index `≤ l+2 < i.val`, non-`full`, `≠ σ`) is an `elimAbove σ i`
eliminator, so the shallow floor lower-bounds the eliminator sum. -/
theorem phase8DrainReady_witness_of_shallowFloor (σ : Sign) (l E8 : ℕ)
    (c : Config (AgentState L K))
    (hclear : Phase7BandDefs.BandClear (L := L) (K := K) σ (l + 3) c)
    (hfloor : E8 ≤ majorityShallowCount (L := L) (K := K) σ l c)
    (hmin : minorityU σ c ≥ 1) :
    ∃ i : Fin (L + 1),
      1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count ∧
      E8 ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count := by
  classical
  -- Extract a live minority agent and its exponent index `i`.
  have hpos : 0 < Multiset.countP (fun a => minoritySt σ a) c := by
    rw [minorityU] at hmin; omega
  obtain ⟨a, hamem, hr, i, hb⟩ := Multiset.countP_pos.mp hpos
  have hc1 : 1 ≤ c.count a := Multiset.one_le_count_iff_mem.mpr hamem
  -- `BandClear` forces the minority index `≥ l+3`.
  have hi3 : l + 3 ≤ i.val := by
    by_contra hlt
    have hlt : i.val < l + 3 := not_le.mp hlt
    have hain7 : a ∈ Phase7Convergence.minorityAt7 (L := L) (K := K) σ i := by
      simp only [Phase7Convergence.minorityAt7, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hr, hb⟩
    have hband : 1 ≤ Phase7BandDefs.bandCountN (L := L) (K := K) σ i c := by
      rw [Phase7BandDefs.bandCountN]
      exact le_trans hc1 (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hain7)
    have hz := hclear i hlt
    omega
  refine ⟨i, ?_, ?_⟩
  · -- the minority witness gives `1 ≤ (minorityAt σ i).sum c.count`.
    have hain : a ∈ Phase8Convergence.minorityAt (L := L) (K := K) σ i := by
      simp only [Phase8Convergence.minorityAt, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hr, hb⟩
    exact le_trans hc1 (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hain)
  · -- the shallow floor lower-bounds the eliminator sum.
    calc E8 ≤ majorityShallowCount (L := L) (K := K) σ l c := hfloor
      _ = ∑ a ∈ Finset.univ.filter (fun a => majorityShallowSt (L := L) (K := K) σ l a),
            c.count a := majorityShallowCount_eq_sum σ l c
      _ ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count :=
          Finset.sum_le_sum_of_subset
            (majorityShallow_filter_subset_elimAbove σ l i hi3)

/-! ## Part 3 — the preservation lemma group (invariants closed under `Phase8Transition`).

`Phase8Transition` acts by `absorbConsume` on both-Main pairs (and by the clock
subroutine otherwise, which touches neither bias nor `full`).  Under band clearance
(`BandClear σ (l+3)`: no `σ`-Main below index `l+3`), the difference
`majorityShallowCount − minorityU` is non-decreasing per interaction, so the carried
invariant `minorityU σ + E8 ≤ majorityShallowCount σ l` closes on the genuine window. -/

/-- A two-element `countP` splits into per-element indicators. -/
theorem countP_pair (p : AgentState L K → Prop) [DecidablePred p] (x y : AgentState L K) :
    Multiset.countP p ({x, y} : Multiset (AgentState L K))
      = (if p x then 1 else 0) + (if p y then 1 else 0) := by
  rw [show ({x, y} : Multiset (AgentState L K)) = x ::ₘ y ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
  ring

/-! ### Indicator evaluation on concrete states. -/

/-- `minoritySt` on a `dyadic`-biased Main is exactly a sign match. -/
theorem minoritySt_dyadic (σ : Sign) (a : AgentState L K) (sgn : Sign) (k : Fin (L + 1))
    (hr : a.role = Role.main) (hb : a.bias = Bias.dyadic sgn k) :
    minoritySt σ a ↔ sgn = σ := by
  rw [minoritySt_iff, hb]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨hr, h⟩

/-- `majorityShallowSt` on a `dyadic`-biased Main is `¬full ∧ opposite sign ∧ shallow`. -/
theorem majorityShallowSt_dyadic (σ : Sign) (l : ℕ) (a : AgentState L K) (sgn : Sign)
    (k : Fin (L + 1)) (hr : a.role = Role.main) (hb : a.bias = Bias.dyadic sgn k) :
    majorityShallowSt (L := L) (K := K) σ l a
      ↔ (¬ a.full ∧ sgn ≠ σ ∧ k.val ≤ l + 2) := by
  rw [majorityShallowSt_iff, hb]
  constructor
  · rintro ⟨_, hf, hsh⟩; exact ⟨hf, hsh.1, hsh.2⟩
  · rintro ⟨hf, hne, hk⟩; exact ⟨hr, hf, hne, hk⟩

theorem not_minoritySt_bias_zero (σ : Sign) (a : AgentState L K) :
    ¬ minoritySt σ ({a with bias := Bias.zero} : AgentState L K) := by
  rw [minoritySt_iff]; rintro ⟨_, hb⟩; exact hb

theorem minoritySt_full_true (σ : Sign) (a : AgentState L K) :
    minoritySt σ ({a with full := true} : AgentState L K) ↔ minoritySt σ a := by
  rw [minoritySt_iff, minoritySt_iff]

theorem not_majShallow_bias_zero (σ : Sign) (l : ℕ) (a : AgentState L K) :
    ¬ majorityShallowSt (L := L) (K := K) σ l ({a with bias := Bias.zero} : AgentState L K) := by
  rw [majorityShallowSt_iff]; rintro ⟨_, _, hsh⟩; exact hsh

theorem not_majShallow_full_true (σ : Sign) (l : ℕ) (a : AgentState L K) :
    ¬ majorityShallowSt (L := L) (K := K) σ l ({a with full := true} : AgentState L K) := by
  rw [majorityShallowSt_iff]; rintro ⟨_, hf, _⟩; exact hf rfl

/-! ### The per-interaction difference bound. -/

/-- **Consume difference bound.**  For an eliminator `e` consuming a strictly higher-
index `m` (opposite signs, `e`'s index `< m`'s index), under the `σ`-deep hypothesis
on `e` (any `σ`-bias on `e` sits at index `≥ l+3`), the shallow-majority indicators of
the pair are dominated by the minority indicator of the consumed agent.  This is the
per-interaction seed of the carried invariant: the only breaking case (a `σ`-minority
as the consumer) is ruled out by `e`'s deep index. -/
theorem consume_diff_bound (σ : Sign) (l : ℕ) (e m : AgentState L K)
    (heM : e.role = Role.main) (hmM : m.role = Role.main)
    (es ms : Sign) (ei mi : Fin (L + 1))
    (heb : e.bias = Bias.dyadic es ei) (hmb : m.bias = Bias.dyadic ms mi)
    (hopp : es ≠ ms) (hlt : ei.val < mi.val)
    (hedeep : ∀ k : Fin (L + 1), e.bias = Bias.dyadic σ k → l + 3 ≤ k.val) :
    (if majorityShallowSt (L := L) (K := K) σ l e then (1 : ℕ) else 0)
        + (if majorityShallowSt (L := L) (K := K) σ l m then (1 : ℕ) else 0)
      ≤ (if minoritySt σ m then (1 : ℕ) else 0) := by
  have hem := majorityShallowSt_dyadic (L := L) (K := K) σ l e es ei heM heb
  have hmm := majorityShallowSt_dyadic (L := L) (K := K) σ l m ms mi hmM hmb
  have hminm := minoritySt_dyadic σ m ms mi hmM hmb
  by_cases hes : es = σ
  · -- `e` is `σ`; its deep index forces `m` (deeper) out of the shallow band.
    have hdeep : l + 3 ≤ ei.val := hedeep ei (by rw [heb, hes])
    have hme0 : ¬ majorityShallowSt (L := L) (K := K) σ l e := by
      rw [hem]; rintro ⟨_, hne, _⟩; exact hne hes
    have hmm0 : ¬ majorityShallowSt (L := L) (K := K) σ l m := by
      rw [hmm]; rintro ⟨_, _, hk⟩; omega
    rw [if_neg hme0, if_neg hmm0]; exact Nat.zero_le _
  · -- `e` is `σ.flip`; then `m` is `σ` (two signs), giving the minority indicator `1`.
    have hmsσ : ms = σ := by revert hes hopp; cases σ <;> cases es <;> cases ms <;> decide
    have hminm1 : minoritySt σ m := by rw [hminm]; exact hmsσ
    have hmm0 : ¬ majorityShallowSt (L := L) (K := K) σ l m := by
      rw [hmm]; rintro ⟨_, hne, _⟩; exact hne hmsσ
    rw [if_pos hminm1, if_neg hmm0]
    split_ifs <;> omega

/-- **Per-pair difference preservation under `absorbConsume`.**  Under the `σ`-deep
hypothesis on both agents (any `σ`-bias sits at index `≥ l+3`), the pair's
`shallow − minority` difference is non-decreasing:
`mShallow(in) + mMinority(out) ≤ mShallow(out) + mMinority(in)`. -/
theorem absorbConsume_shallowMinority_pair_diff (σ : Sign) (l : ℕ) (s t : AgentState L K)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (hs : ∀ k : Fin (L + 1), s.bias = Bias.dyadic σ k → l + 3 ≤ k.val)
    (ht : ∀ k : Fin (L + 1), t.bias = Bias.dyadic σ k → l + 3 ≤ k.val) :
    Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
        ({s, t} : Multiset (AgentState L K))
      + Multiset.countP (fun a => minoritySt σ a)
          ({(absorbConsume L K s t).1, (absorbConsume L K s t).2}
            : Multiset (AgentState L K))
    ≤ Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
          ({(absorbConsume L K s t).1, (absorbConsume L K s t).2}
            : Multiset (AgentState L K))
      + Multiset.countP (fun a => minoritySt σ a) ({s, t} : Multiset (AgentState L K)) := by
  classical
  -- The identity closer: whenever the output is `(s, t)`, both sides coincide.
  have hid : ∀ _hh : absorbConsume L K s t = (s, t),
      Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
          ({s, t} : Multiset (AgentState L K))
        + Multiset.countP (fun a => minoritySt σ a)
            ({(absorbConsume L K s t).1, (absorbConsume L K s t).2}
              : Multiset (AgentState L K))
      ≤ Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
            ({(absorbConsume L K s t).1, (absorbConsume L K s t).2}
              : Multiset (AgentState L K))
        + Multiset.countP (fun a => minoritySt σ a) ({s, t} : Multiset (AgentState L K)) := by
    intro hh; rw [hh]
  rcases hsb : s.bias with _ | ⟨ss, i⟩
  · exact hid (by unfold absorbConsume; simp only [hsb])
  · rcases htb : t.bias with _ | ⟨tt, j⟩
    · exact hid (by unfold absorbConsume; simp only [hsb, htb])
    · rcases ss with _ | _ <;> rcases tt with _ | _
      · -- pos, pos → identity
        exact hid (by unfold absorbConsume; simp only [hsb, htb])
      · -- pos, neg → firing branch
        by_cases hcase : i.val < j.val ∧ ¬ s.full
        · have habs : absorbConsume L K s t
              = ({s with full := true}, {t with bias := Bias.zero}) := by
            unfold absorbConsume; simp only [hsb, htb]; rw [if_pos hcase]
          obtain ⟨hij, _⟩ := hcase
          have hcdb := consume_diff_bound (L := L) (K := K) σ l s t hsM htM Sign.pos Sign.neg i j
            hsb htb (by decide) hij hs
          rw [habs]
          simp only [countP_pair, minoritySt_full_true, not_minoritySt_bias_zero,
            not_majShallow_full_true, not_majShallow_bias_zero]
          split_ifs at hcdb ⊢ <;> omega
        · by_cases hcase2 : j.val < i.val ∧ ¬ t.full
          · have habs : absorbConsume L K s t
                = ({s with bias := Bias.zero}, {t with full := true}) := by
              unfold absorbConsume; simp only [hsb, htb]; rw [if_neg hcase, if_pos hcase2]
            obtain ⟨hji, _⟩ := hcase2
            have hcdb := consume_diff_bound (L := L) (K := K) σ l t s htM hsM Sign.neg Sign.pos j i
              htb hsb (by decide) hji ht
            rw [habs]
            simp only [countP_pair, minoritySt_full_true, not_minoritySt_bias_zero,
              not_majShallow_full_true, not_majShallow_bias_zero]
            split_ifs at hcdb ⊢ <;> omega
          · have heq : absorbConsume L K s t = (s, t) := by
              unfold absorbConsume; simp only [hsb, htb]; rw [if_neg hcase, if_neg hcase2]
            exact hid heq
      · -- neg, pos → firing branch
        by_cases hcase : i.val < j.val ∧ ¬ s.full
        · have habs : absorbConsume L K s t
              = ({s with full := true}, {t with bias := Bias.zero}) := by
            unfold absorbConsume; simp only [hsb, htb]; rw [if_pos hcase]
          obtain ⟨hij, _⟩ := hcase
          have hcdb := consume_diff_bound (L := L) (K := K) σ l s t hsM htM Sign.neg Sign.pos i j
            hsb htb (by decide) hij hs
          rw [habs]
          simp only [countP_pair, minoritySt_full_true, not_minoritySt_bias_zero,
            not_majShallow_full_true, not_majShallow_bias_zero]
          split_ifs at hcdb ⊢ <;> omega
        · by_cases hcase2 : j.val < i.val ∧ ¬ t.full
          · have habs : absorbConsume L K s t
                = ({s with bias := Bias.zero}, {t with full := true}) := by
              unfold absorbConsume; simp only [hsb, htb]; rw [if_neg hcase, if_pos hcase2]
            obtain ⟨hji, _⟩ := hcase2
            have hcdb := consume_diff_bound (L := L) (K := K) σ l t s htM hsM Sign.pos Sign.neg j i
              htb hsb (by decide) hji ht
            rw [habs]
            simp only [countP_pair, minoritySt_full_true, not_minoritySt_bias_zero,
              not_majShallow_full_true, not_majShallow_bias_zero]
            split_ifs at hcdb ⊢ <;> omega
          · have heq : absorbConsume L K s t = (s, t) := by
              unfold absorbConsume; simp only [hsb, htb]; rw [if_neg hcase, if_neg hcase2]
            exact hid heq
      · -- neg, neg → identity
        exact hid (by unfold absorbConsume; simp only [hsb, htb])

/-! ### `BandClear` self-preservation. -/

/-- A live `σ`-Main in a band-cleared config sits at index `≥ l+3`. -/
theorem bandClear_index_deep (σ : Sign) (l : ℕ) (c : Config (AgentState L K))
    (hbc : Phase7BandDefs.BandClear (L := L) (K := K) σ (l + 3) c) (a : AgentState L K)
    (hamem : a ∈ c) (haM : a.role = Role.main) (k : Fin (L + 1))
    (hab : a.bias = Bias.dyadic σ k) : l + 3 ≤ k.val := by
  by_contra hlt
  have hlt : k.val < l + 3 := not_le.mp hlt
  have hain : a ∈ Phase7Convergence.minorityAt7 (L := L) (K := K) σ k := by
    simp only [Phase7Convergence.minorityAt7, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨haM, hab⟩
  have hc1 : 1 ≤ c.count a := Multiset.one_le_count_iff_mem.mpr hamem
  have hband : 1 ≤ Phase7BandDefs.bandCountN (L := L) (K := K) σ k c := by
    rw [Phase7BandDefs.bandCountN]
    exact le_trans hc1 (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hain)
  have hz := hbc k hlt
  omega

/-- The `bandCountN` count as a `countP` over a role/bias predicate. -/
theorem bandCountN_eq_countP (σ : Sign) (k : Fin (L + 1)) (c : Config (AgentState L K)) :
    Phase7BandDefs.bandCountN (L := L) (K := K) σ k c
      = Multiset.countP (fun a => a.role = Role.main ∧ a.bias = Bias.dyadic σ k) c := by
  rw [Phase7BandDefs.bandCountN, Phase7Convergence.minorityAt7,
    ← Phase6Convergence.countP_eq_sum_count6
      (L := L) (K := K) (fun a => a.role = Role.main ∧ a.bias = Bias.dyadic σ k) c]

/-- Either component of an `absorbConsume` output keeps the input bias or zeroes it. -/
theorem absorbConsume_fst_bias_cases (s t : AgentState L K) :
    (absorbConsume L K s t).1.bias = s.bias
      ∨ (absorbConsume L K s t).1.bias = Bias.zero := by
  unfold absorbConsume
  split <;> (try split_ifs) <;> simp

theorem absorbConsume_snd_bias_cases (s t : AgentState L K) :
    (absorbConsume L K s t).2.bias = t.bias
      ∨ (absorbConsume L K s t).2.bias = Bias.zero := by
  unfold absorbConsume
  split <;> (try split_ifs) <;> simp

/-- **`BandClear σ (l+3)` is preserved by any chosen-pair update** on the genuine
phase-8 window (`absorbConsume` never creates a `σ`-dyadic bias). -/
theorem bandClear_stepOrSelf (σ : Sign) (l n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase8Convergence.Phase8AllMain (L := L) (K := K) n c)
    (hbc : Phase7BandDefs.BandClear (L := L) (K := K) σ (l + 3) c) (r₁ r₂ : AgentState L K) :
    Phase7BandDefs.BandClear (L := L) (K := K) σ (l + 3)
      (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  classical
  intro jj hjj
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hm1 : r₁ ∈ c := Multiset.mem_of_le hsub (by simp)
    have hm2 : r₂ ∈ c := Multiset.mem_of_le hsub (by simp)
    obtain ⟨h18, h1M⟩ := hInv.2 r₁ hm1
    obtain ⟨h28, h2M⟩ := hInv.2 r₂ hm2
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    have habsT : Transition L K r₁ r₂ = absorbConsume L K r₁ r₂ :=
      Phase8Convergence.Transition_eq_absorbConsume_of_phase8_main r₁ r₂ h18 h28 h1M h2M
    -- Band-zero on `c`: no Main there holds bias `dyadic σ jj`.
    have h0 : ∀ a ∈ c, ¬ (a.role = Role.main ∧ a.bias = Bias.dyadic σ jj) := by
      have := hbc jj hjj
      rw [bandCountN_eq_countP, Multiset.countP_eq_zero] at this
      exact this
    rw [bandCountN_eq_countP, Multiset.countP_eq_zero]
    intro a ha hpred
    rw [hc', Multiset.mem_add] at ha
    rcases ha with hac | hao
    · exact h0 a (Multiset.mem_of_le tsub_le_self hac) hpred
    · -- `a` is an `absorbConsume` output; its role equals the input's, its bias is
      -- kept or zeroed, so `hpred` reduces to the (empty) band on `c`.
      rw [habsT] at hao
      obtain ⟨haM, hab⟩ := hpred
      have hbias1 := absorbConsume_fst_bias_cases (L := L) (K := K) r₁ r₂
      have hbias2 := absorbConsume_snd_bias_cases (L := L) (K := K) r₁ r₂
      have hrole1 := absorbConsume_role_fst L K r₁ r₂
      have hrole2 := absorbConsume_role_snd L K r₁ r₂
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hao
      rcases hao with rfl | rfl
      · rcases hbias1 with hb | hb
        · exact h0 r₁ hm1 ⟨hrole1 ▸ haM, hb ▸ hab⟩
        · rw [hb] at hab; exact absurd hab (by simp)
      · rcases hbias2 with hb | hb
        · exact h0 r₂ hm2 ⟨hrole2 ▸ haM, hb ▸ hab⟩
        · rw [hb] at hab; exact absurd hab (by simp)
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]; exact hbc jj hjj

/-! ### Config-level closure of the carried invariant. -/

/-- **Per-step difference preservation.**  On the genuine phase-8 window under band
clearance, `majorityShallowCount(c) + minorityU(step) ≤ majorityShallowCount(step)
+ minorityU(c)` — the `shallow − minority` difference is non-decreasing. -/
theorem shallowMinority_diff_stepOrSelf (σ : Sign) (l n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase8Convergence.Phase8AllMain (L := L) (K := K) n c)
    (hbc : Phase7BandDefs.BandClear (L := L) (K := K) σ (l + 3) c) (r₁ r₂ : AgentState L K) :
    majorityShallowCount (L := L) (K := K) σ l c
        + minorityU σ (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ≤ majorityShallowCount (L := L) (K := K) σ l
            (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
        + minorityU σ c := by
  classical
  by_cases happ : Protocol.Applicable c r₁ r₂
  · have hsub : ({r₁, r₂} : Multiset (AgentState L K)) ≤ c := happ
    have hm1 : r₁ ∈ c := Multiset.mem_of_le hsub (by simp)
    have hm2 : r₂ ∈ c := Multiset.mem_of_le hsub (by simp)
    obtain ⟨h18, h1M⟩ := hInv.2 r₁ hm1
    obtain ⟨h28, h2M⟩ := hInv.2 r₂ hm2
    have hs : ∀ k : Fin (L + 1), r₁.bias = Bias.dyadic σ k → l + 3 ≤ k.val :=
      fun k hk => bandClear_index_deep σ l c hbc r₁ hm1 h1M k hk
    have ht : ∀ k : Fin (L + 1), r₂.bias = Bias.dyadic σ k → l + 3 ≤ k.val :=
      fun k hk => bandClear_index_deep σ l c hbc r₂ hm2 h2M k hk
    have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂
        = c - {r₁, r₂} + {(Transition L K r₁ r₂).1, (Transition L K r₁ r₂).2} := by
      unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
    have hpair := absorbConsume_shallowMinority_pair_diff (L := L) (K := K) σ l r₁ r₂
      h1M h2M hs ht
    have hmS_le : Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => majorityShallowSt (L := L) (K := K) σ l a) c :=
      Multiset.countP_le_of_le _ hsub
    have hmU_le : Multiset.countP (fun a => minoritySt σ a)
        ({r₁, r₂} : Multiset (AgentState L K))
          ≤ Multiset.countP (fun a => minoritySt σ a) c :=
      Multiset.countP_le_of_le _ hsub
    unfold majorityShallowCount minorityU
    rw [hc', Multiset.countP_add, Multiset.countP_add, Multiset.countP_sub hsub,
      Multiset.countP_sub hsub,
      Phase8Convergence.Transition_eq_absorbConsume_of_phase8_main r₁ r₂ h18 h28 h1M h2M]
    omega
  · rw [Protocol.stepOrSelf_eq_self_of_not_applicable happ]

/-- **The carried invariant closes under one step.**  On the genuine phase-8 window,
if band clearance holds and `minorityU σ + E8 ≤ majorityShallowCount σ l`, both hold
after any chosen-pair update. -/
theorem shallowMinorityReady_stepOrSelf (σ : Sign) (l n E8 : ℕ) (c : Config (AgentState L K))
    (hInv : Phase8Convergence.Phase8AllMain (L := L) (K := K) n c)
    (hbc : Phase7BandDefs.BandClear (L := L) (K := K) σ (l + 3) c)
    (hle : minorityU σ c + E8 ≤ majorityShallowCount (L := L) (K := K) σ l c)
    (r₁ r₂ : AgentState L K) :
    Phase7BandDefs.BandClear (L := L) (K := K) σ (l + 3)
        (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂)
      ∧ minorityU σ (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) + E8
          ≤ majorityShallowCount (L := L) (K := K) σ l
              (Protocol.stepOrSelf (NonuniformMajority L K) c r₁ r₂) := by
  refine ⟨bandClear_stepOrSelf σ l n c hInv hbc r₁ r₂, ?_⟩
  have hdiff := shallowMinority_diff_stepOrSelf σ l n c hInv hbc r₁ r₂
  omega

end Phase8WitnessSupply

end Ripple.PopulationProtocol.ExactMajority
