/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Eliminator margins — the Phase-7/8 floor package (deterministic adapters + margin structures)

This file (Phase 7/8 floor package, per `HANDOFF_FOUR_FLOORS.md` §3/§4) delivers the
remaining structural inputs that `PhaseFloors.phase7_hdrop_wired` / `phase8_hdrop_wired`
consume, classified by the blueprint into three honest pieces:

1. **Deterministic adapters** (blueprint priority 1).  A nonzero minority count exposes a
   *level* with a minority agent — this is pure witness extraction from `countP > 0`, no new
   probability:
   * `exists_minorityAt_of_minorityU_pos`  (Phase 8, witness for `minorityAt`)
   * `exists_minorityAt7_of_minorityU_pos` (Phase 7, witness for `minorityAt7`)
   * `exists_minorityAt7_of_classMassN_pos` (Phase 7, witness directly from the MASS potential
     `classMassN σ ≥ 1`, the potential the Phase-7 drain actually tracks)
   Plus the Phase-1 arithmetic wrapper
   `phase1_pullPos_floor_of_mainCount_and_saturated_bound`, pure ℕ arithmetic from the landed
   `PhaseFloors.mainCount_eq_pullPos_add_saturatedPos`.

2. **The eliminator-margin package** (blueprint priority 3, §3+§4).  The eliminator floors
   `elimGap1 ≥ E` / `elimAbove ≥ E` are NOT derivable from the landed Phase-6/7 Posts: the
   landed `Invariants.lemma_7_5/7_6` are minority-survival UPPER bounds (absorbing-set zero
   mass), never eliminator-count LOWER bounds (verified, matching the `PhaseFloors` audit).
   Following the discipline "where the structural Post genuinely doesn't export the count,
   define the predicate honestly, prove what IS derivable, carry the precise remainder named":
   * `Phase6To7Structure` / `Phase7To8Structure` are honest carriers of EXACTLY the eliminator
     margin the true Doty Lemma 7.4 / 7.6 would export (the precise named remainder).
   * `lemma7_4_phase7_elimGap1_floor` / `lemma7_6_phase8_elimAbove_floor` then derive their
     full conclusion: the minority-witness half is PROVED from the landed potentials
     (`classMassN`/`minorityU` witness extraction); the eliminator half is the carried field.

3. **The wiring adapters** (blueprint §3/§4 exact shapes): `phase7_hdrop_wired_from_lemma7_4`,
   `phase8_hdrop_wired_from_lemma7_6`, repackaging the existential floor into
   `PhaseFloors.phase7_hdrop_wired` / `phase8_hdrop_wired`.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.PhaseFloors

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace EliminatorMargins

/-! ## Part 1 — deterministic minority-witness adapters.

A nonzero minority count/mass forces SOME agent to be a `σ`-signed dyadic Main; that agent's
exponent index `i` is a level with `≥ 1` minority mass in the per-level finset.  These are
pure witness extractions from `Multiset.countP_pos` (Phase 8 / Phase 7 count form) and from the
`classMass` ledger (Phase 7 mass form). -/

/-- **Deterministic witness (Phase 8): nonzero minority count gives a level with a minority.**
If `minorityU σ c ≥ 1` then some agent is a `σ`-signed dyadic Main at index `i`; that `i` is a
level with `1 ≤ minorityAt σ i .sum c.count`.  Pure `countP > 0` witness extraction. -/
theorem exists_minorityAt_of_minorityU_pos {L K : ℕ} (σ : Sign) (c : Config (AgentState L K))
    (hm : 1 ≤ Phase7Convergence.minorityU (L := L) (K := K) σ c) :
    ∃ i : Fin (L + 1),
      1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count := by
  classical
  have hpos : 0 < Multiset.countP (fun a => Phase7Convergence.minoritySt σ a) c := by
    rw [Phase7Convergence.minorityU] at hm; omega
  rw [Multiset.countP_pos] at hpos
  obtain ⟨a, hamem, hr, i, hb⟩ := hpos
  refine ⟨i, ?_⟩
  -- `a ∈ minorityAt σ i` and `count a c ≥ 1`, so the finset sum is `≥ 1`.
  have hain : a ∈ Phase8Convergence.minorityAt (L := L) (K := K) σ i := by
    simp only [Phase8Convergence.minorityAt, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hr, hb⟩
  have hcount : 1 ≤ c.count a := Multiset.one_le_count_iff_mem.mpr hamem
  calc (1 : ℕ) ≤ c.count a := hcount
    _ ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count :=
        Finset.single_le_sum (f := c.count) (fun _ _ => Nat.zero_le _) hain

/-- **Deterministic witness (Phase 7, count form): nonzero minority count gives a level with a
minority.**  Same extraction as Phase 8, targeting `minorityAt7` (the Phase-7 per-level
minority finset, definitionally the same filter shape). -/
theorem exists_minorityAt7_of_minorityU_pos {L K : ℕ} (σ : Sign) (c : Config (AgentState L K))
    (hm : 1 ≤ Phase7Convergence.minorityU (L := L) (K := K) σ c) :
    ∃ j : Fin (L + 1),
      1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count := by
  classical
  have hpos : 0 < Multiset.countP (fun a => Phase7Convergence.minoritySt σ a) c := by
    rw [Phase7Convergence.minorityU] at hm; omega
  rw [Multiset.countP_pos] at hpos
  obtain ⟨a, hamem, hr, j, hb⟩ := hpos
  refine ⟨j, ?_⟩
  have hain : a ∈ Phase7Convergence.minorityAt7 (L := L) (K := K) σ j := by
    simp only [Phase7Convergence.minorityAt7, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hr, hb⟩
  have hcount : 1 ≤ c.count a := Multiset.one_le_count_iff_mem.mpr hamem
  calc (1 : ℕ) ≤ c.count a := hcount
    _ ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count :=
        Finset.single_le_sum (f := c.count) (fun _ _ => Nat.zero_le _) hain

/-- A positive-mass agent is a `σ`-signed dyadic at some index. -/
theorem bias_dyadic_of_agentClassMass_pos {L K : ℕ} (σ : Sign) (a : AgentState L K)
    (h : 1 ≤ Phase7Convergence.agentClassMass (L := L) (K := K) σ a) :
    ∃ i : Fin (L + 1), a.bias = Bias.dyadic σ i := by
  unfold Phase7Convergence.agentClassMass Phase7Convergence.biasClassMass at h
  rcases hb : a.bias with _ | ⟨s, i⟩
  · rw [hb] at h; simp at h
  · rw [hb] at h
    by_cases hs : s = σ
    · exact ⟨i, by rw [hs]⟩
    · simp only [hs, if_false] at h; omega

/-- **Deterministic witness (Phase 7, mass form): nonzero σ-class MASS gives a level with a
minority.**  The Phase-7 drain tracks `classMassN σ` (not the count, which can rise under a
gap-2 fire).  On a `Phase7AllMain` window, `classMassN σ c ≥ 1` ⟹ `classMass σ c ≥ 1` ⟹ some
agent has positive `agentClassMass`, i.e. is a `σ`-signed dyadic at index `i`; the window
forces `role = main`, so that agent witnesses `minorityAt7 σ i`.  This is the form the Phase-7
floor lemma consumes (the potential the drain actually drives to `0`). -/
theorem exists_minorityAt7_of_classMassN_pos {L K n : ℕ} (σ : Sign)
    (c : Config (AgentState L K)) (hb7 : Phase7Convergence.Phase7AllMain n c)
    (hm : 1 ≤ Phase7Convergence.classMassN (L := L) (K := K) σ c) :
    ∃ j : Fin (L + 1),
      1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count := by
  classical
  -- `classMassN σ c ≥ 1` ⟹ `classMass σ c ≥ 1` (toNat ≥ 1 ⟹ underlying ℤ ≥ 1, it is `≥ 0`).
  have hZ : 1 ≤ Phase7Convergence.classMass (L := L) (K := K) σ c := by
    have hnn := Phase7Convergence.classMass_nonneg (L := L) (K := K) σ c
    unfold Phase7Convergence.classMassN at hm
    omega
  -- extract a positive-mass agent: if every per-agent mass were `0` the total would be `0 < 1`.
  have hex : ∃ a ∈ c, 1 ≤ Phase7Convergence.agentClassMass (L := L) (K := K) σ a := by
    by_contra hno
    simp only [not_exists, not_and, not_le] at hno
    -- each `agentClassMass ≥ 0` and `< 1` ⟹ `= 0`; the mass sum is then `0`, contradicting `≥ 1`.
    have hzero : Phase7Convergence.classMass (L := L) (K := K) σ c = 0 := by
      rw [Phase7Convergence.classMass]
      refine Multiset.sum_eq_zero ?_
      intro x hx
      rw [Multiset.mem_map] at hx
      obtain ⟨a, hamem, ha⟩ := hx
      have hnn := Phase7Convergence.agentClassMass_nonneg (L := L) (K := K) σ a
      have hlt := hno a hamem
      omega
    omega
  obtain ⟨a, hamem, hmass⟩ := hex
  obtain ⟨i, hb⟩ := bias_dyadic_of_agentClassMass_pos σ a hmass
  have hr : a.role = Role.main := (hb7.2 a hamem).2
  refine ⟨i, ?_⟩
  have hain : a ∈ Phase7Convergence.minorityAt7 (L := L) (K := K) σ i := by
    simp only [Phase7Convergence.minorityAt7, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hr, hb⟩
  have hcount : 1 ≤ c.count a := Multiset.one_le_count_iff_mem.mpr hamem
  calc (1 : ℕ) ≤ c.count a := hcount
    _ ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ i).sum c.count :=
        Finset.single_le_sum (f := c.count) (fun _ _ => Nat.zero_le _) hain

/-! ### Part 1b — the Phase-1 `pullPosSet` arithmetic wrapper.

The landed `PhaseFloors.mainCount_eq_pullPos_add_saturatedPos` splits the Main count exactly into
the partner pool plus the saturated-positive pool.  This wrapper is the pure ℕ arithmetic that
turns the RoleSplit count lower bound (`P + saturatedPos ≤ mainCount`) into the `pullPosSet`
floor — reducing the remaining missing link to the saturated-side bound. -/

/-- **Phase-1 `pullPosSet` floor (pure ℕ arithmetic).**  From the landed Main decomposition
`mainCount = pullPosSet + saturatedPosSet` and the saturated-side budget
`P + saturatedPos ≤ mainCount`, the partner pool floor `P ≤ pullPosSet .sum count` follows.
(The `P + saturatedPos ≤ mainCount` budget is exactly `mainCount ≥ n/3` plus the missing
saturated-side bound `saturatedPos ≤ mainCount − P`.) -/
theorem phase1_pullPos_floor_of_mainCount_and_saturated_bound {L K P : ℕ}
    {c : Config (AgentState L K)}
    (hbudget : P + (PhaseFloors.saturatedPosSet L K).sum c.count
      ≤ RoleSplitConcentration.mainCount (L := L) (K := K) c) :
    P ≤ (DrainThreading.pullPosSet L K).sum c.count := by
  have hsplit := PhaseFloors.mainCount_eq_pullPos_add_saturatedPos (L := L) (K := K) c
  omega

/-! ## Part 2 — the Phase-7/8 eliminator-margin structures and floor lemmas.

The eliminator floors `elimGap1 ≥ E` / `elimAbove ≥ E` are NOT derivable from the landed
Phase-6/7 Posts (`Invariants.lemma_7_5/7_6` are minority-survival UPPER bounds, not eliminator
LOWER bounds — verified).  Per discipline, the structural Post `Phase6To7Structure` /
`Phase7To8Structure` is the HONEST carrier of EXACTLY the eliminator margin the true Doty
Lemma 7.4 / 7.6 would export (the precise named remainder).  The floor lemmas then prove their
FULL conclusion: the minority-witness half is derived from the landed potentials (Part 1); the
eliminator half is supplied by the carried structure. -/

/-- **Phase 6→7 structural Post (honest carrier of the Lemma 7.4 eliminator margin).**  At every
exponent level `j` that still holds a minority, the gap-1 partner level `i = j − 1` carries at
least `E` σ-eliminators (the `0.8·|M|` majority eliminator supply of Doty Lemma 7.4, confined to
the minority band).  This is the precise named remainder: the eliminator-count LOWER bound that
the landed survival-UPPER-bound Posts do not export. -/
def Phase6To7Structure {L K : ℕ} (σ : Sign) (E : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ j : Fin (L + 1),
    1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count →
    ∃ i : Fin (L + 1),
      i.val + 1 = j.val ∧
      E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count

/-- **Phase 7→8 structural Post (honest carrier of the Lemma 7.6 eliminator margin).**  At every
exponent level `i` that still holds a minority, the levels strictly above carry at least `E`
non-`full` σ-eliminators (the Doty Lemma 7.4–7.6 `0.8|M| − 0.2|M|` eliminator-margin floor).
This is the precise named remainder for Phase 8. -/
def Phase7To8Structure {L K : ℕ} (σ : Sign) (E : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ i : Fin (L + 1),
    1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count →
    E ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count

/-- **Lemma 7.4 floor for Phase 7: every nonzero minority level has a large gap-1 eliminator
supply.**  From a `Phase7AllMain` window with positive σ-class MASS (`classMassN σ ≥ 1`, the
potential the drain drives to `0`), the deterministic witness (Part 1) produces a minority level
`j`; the carried `Phase6To7Structure` margin then supplies the gap-1 partner level `i = j − 1`
with `≥ E` eliminators.  The minority-witness half is PROVED; the eliminator half is the carried
named remainder. -/
theorem lemma7_4_phase7_elimGap1_floor {L K n : ℕ} (σ : Sign)
    {c : Config (AgentState L K)}
    (hb7 : Phase7Convergence.Phase7AllMain (L := L) (K := K) n c)
    (E : ℕ)
    (hPhase6Post : Phase6To7Structure (L := L) (K := K) σ E c)
    (hminor : 1 ≤ Phase7Convergence.classMassN (L := L) (K := K) σ c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    ∃ i j : Fin (L + 1),
      i.val + 1 = j.val ∧
      1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count ∧
      E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count := by
  obtain ⟨j, hj⟩ := exists_minorityAt7_of_classMassN_pos (n := n) σ c hb7 hminor
  obtain ⟨i, hg1, helim⟩ := hPhase6Post j hj
  exact ⟨i, j, hg1, hj, helim⟩

/-- **Lemma 7.6 floor for Phase 8: a minority level has a large above-level eliminator supply.**
The minority witness `i` is given (deterministic, from `exists_minorityAt_of_minorityU_pos`); the
carried `Phase7To8Structure` margin supplies the `≥ E` non-`full` eliminators above it.  The
eliminator half is the carried named remainder. -/
theorem lemma7_6_phase8_elimAbove_floor {L K n : ℕ} (σ : Sign)
    {c : Config (AgentState L K)}
    (hb8 : Phase8Convergence.Phase8AllMain (L := L) (K := K) n c)
    (E : ℕ)
    (hPhase7Post : Phase7To8Structure (L := L) (K := K) σ E c)
    (i : Fin (L + 1))
    (hmin : 1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count)
    (hE : (E : ℝ) ≤ (1 : ℝ) * (n : ℝ) / 5) :
    E ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count :=
  hPhase7Post i hmin

/-! ## Part 3 — the wiring adapters into `PhaseFloors.phase7/8_hdrop_wired`. -/

/-- **Phase 7 wiring (blueprint §3 shape).**  Repackages the existential gap-1 eliminator floor
(`lemma7_4_phase7_elimGap1_floor`'s conclusion) into `PhaseFloors.phase7_hdrop_wired`. -/
theorem phase7_hdrop_wired_from_lemma7_4 {L K : ℕ} (σ : Sign) (n m : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hb7 : Phase7Convergence.Phase7AllMain n b)
    (hbm : Phase7Convergence.classMassN σ b = m)
    (hmpos : 1 ≤ m)
    (E : ℕ)
    (hfloor : ∃ i j : Fin (L + 1),
      i.val + 1 = j.val ∧
      1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum b.count ∧
      E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.classMassN σ) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  rcases hfloor with ⟨i, j, hg1, hmin, helim⟩
  exact PhaseFloors.phase7_hdrop_wired σ n m hn b hb7 hbm i j hg1 E hmin helim

/-- **Phase 8 wiring (blueprint §4 shape).**  Repackages the existential above-level eliminator
floor (`exists_minorityAt_of_minorityU_pos` witness + `lemma7_6_phase8_elimAbove_floor` margin)
into `PhaseFloors.phase8_hdrop_wired`. -/
theorem phase8_hdrop_wired_from_lemma7_6 {L K : ℕ} (σ : Sign) (n m : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hb8 : Phase8Convergence.Phase8AllMain n b)
    (hbm : Phase7Convergence.minorityU σ b = m)
    (hmpos : 1 ≤ m)
    (E : ℕ)
    (hexists :
      ∃ i : Fin (L + 1),
        1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum b.count ∧
        E ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  rcases hexists with ⟨i, hmin, helim⟩
  exact PhaseFloors.phase8_hdrop_wired σ n m hn b hb8 hbm i E hmin helim

end EliminatorMargins

end ExactMajority
