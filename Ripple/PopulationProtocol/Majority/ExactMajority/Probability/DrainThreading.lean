/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Drain threading — feeding the carried structural floor into each phase's drop rectangle

`DrainCalibration.lean` (D-6) discharged the failure budget `hε` of every phase drain
instance but left the per-step drain bound `hstep`/`hdrop` carried as an abstract
hypothesis.  This file (D-7) THREADS the carried *structural* count floor (the
eliminator/reserve/main-count lower bound already present in each phase's `Pre`/`Inv`)
THROUGH the phase's existing drop-probability rectangle lemma
(`*_drop_prob_rect*`) to produce the CONCRETE drop-probability floor
`ofReal(α·m/(n(n−1))) ≤ drop-mass`, and then chains it through the existing engine
packagers (`*_hdrop_of_floor*` / `*_hstep_of_floor*`) to discharge the engine `hdrop`
(levels form a) / `hstep` (crude form b, at the honest level `m = 1`).

## The generic arithmetic bridge

`ofReal_div_le_of_num_le` : `a ≤ b`, `0 ≤ a`, `0 ≤ d` ⟹ `ofReal(a/d) ≤ ofReal(b/d)`.
This is the only new analytic content; everything else is honest count bookkeeping
(`Finset.sum`-monotonicity from the structural floor) plus the existing rectangle and
packager lemmas re-applied with a derived `p`.

## What is HONEST vs structurally vacuous

The CRUDE engine (`crude_PhaseConvergenceW`, form b) needs
`hstep : ∀ b, Inv b → 1 ≤ Φ b → K b (potDone Φ)ᶜ ≤ q`.  For `Φ b ≥ 2` a single drain
drops `Φ` by `≥ 1` but NOT to `0`, so `K b (potDone Φ)ᶜ = 1` — the crude `hstep` is
genuinely vacuous unless one restricts to `Φ b = 1`.  The HONEST multi-level drain is the
LEVELS engine (`levels_PhaseConvergenceW`, form a) whose `hdrop` is per-level
`K b (potBelow Φ m)ᶜ ≤ q m`, which the rectangle floor discharges at EVERY level `m`.
So the principal D-7 deliverables are the per-level `hdrop`s (the honest engine input);
the crude `hstep` is delivered only at the `m = 1` level (where the drop reaches `potDone`).

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DrainCalibration

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace DrainThreading

/-! ## Part A — the generic arithmetic bridge. -/

/-- **The drop-floor monotone bridge.**  A larger rectangle count `b` over the same
denominator `d` gives a larger `ofReal` drop floor.  Used to replace the rectangle's
exact count `(#min·#elim)` by the carried structural floor `(margin·m)`. -/
theorem ofReal_div_le_of_num_le {a b d : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    ENNReal.ofReal (a / d) ≤ ENNReal.ofReal (b / d) := by
  apply ENNReal.ofReal_le_ofReal
  rcases eq_or_lt_of_le hd with hd0 | hd0
  · simp [← hd0]
  · gcongr

/-! ## Part B — Phase 8 (`minorityU σ`, `Phase8AllMain`, α = 1/5).

The carried structural floor (Doty Lemma 7.4 `0.8|M|` majority minus Lemma 7.6 `0.2|M|`
minority) supplies, at some witness exponent level `i`, an eliminator margin
`(elimAbove σ i).sum count ≥ E` together with at least one minority agent at level `i`
(`(minorityAt σ i).sum count ≥ 1`).  Threaded through `minorityU_drop_prob_rect`, this
yields the drop-probability floor `ofReal(E/(n(n−1))) ≤ drop-mass`, which the existing
packager `minorityU_hdrop_of_floor` (levels) / the `m = 1` crude bridge turn into the
engine `hdrop` / `hstep`. -/

open Phase8Convergence

/-- **Phase 8 — structural floor ⟹ concrete drop-probability floor.**  At a witness level
`i` with `≥ 1` minority and eliminator margin `≥ E`, the one-step drop probability of
`minorityU σ` is `≥ ofReal(E/(n(n−1)))`. -/
theorem phase8_drop_floor_of_struct {L K : ℕ} (σ : Sign) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : Phase8Convergence.Phase8AllMain n c)
    (i : Fin (L + 1)) (E : ℕ)
    (hmin : 1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count)
    (helim : E ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count) :
    ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase7Convergence.minorityU σ c' + 1 ≤ Phase7Convergence.minorityU σ c} := by
  refine le_trans ?_ (Phase8Convergence.minorityU_drop_prob_rect σ n hn c hInv i)
  -- E ≤ (#min·#elim), since #min ≥ 1 and #elim ≥ E.
  have hprod : (E : ℕ) ≤
      (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count *
        (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count := by
    calc (E : ℕ) ≤ 1 * E := by omega
      _ ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count * E :=
          Nat.mul_le_mul_right _ hmin
      _ ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum c.count *
            (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum c.count :=
          Nat.mul_le_mul_left _ helim
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply DrainThreading.ofReal_div_le_of_num_le _ (by positivity) (by nlinarith)
  exact_mod_cast hprod

/-- **Phase 8 — the levels-engine `hdrop` from the structural floor.**  At a level `m`
with the carried witness floor (`≥ 1` minority and eliminator margin `≥ E` at some level
`i`), the level-`m` failure mass is `≤ 1 − ofReal(E/(n(n−1)))`. -/
theorem phase8_hdrop_of_struct {L K : ℕ} (σ : Sign) (n m : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hb8 : Phase8Convergence.Phase8AllMain n b)
    (hbm : Phase7Convergence.minorityU σ b = m)
    (i : Fin (L + 1)) (E : ℕ)
    (hmin : 1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum b.count)
    (helim : E ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  Phase8Convergence.minorityU_hdrop_of_floor σ n m
    (ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) b hb8 hbm
    (phase8_drop_floor_of_struct σ n hn b hb8 i E hmin helim)

/-- **Phase 8 — the crude-engine `hstep` from the structural floor, at `m = 1`.**  When
`minorityU σ b = 1` the strict-drop event reaches `potDone`, so the structural floor gives
the crude `hstep` failure `(potDone)ᶜ ≤ 1 − ofReal(E/(n(n−1)))`.  (For `minorityU σ b ≥ 2`
a single drain cannot reach `potDone`, so the crude `hstep` is structurally vacuous there;
the honest multi-level drain uses `phase8_hdrop_of_struct` + the levels engine.) -/
theorem phase8_hstep_of_struct_one {L K : ℕ} (σ : Sign) (n : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hb8 : Phase8Convergence.Phase8AllMain n b)
    (hb1 : Phase7Convergence.minorityU σ b = 1)
    (i : Fin (L + 1)) (E : ℕ)
    (hmin : 1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum b.count)
    (helim : E ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potDone (fun c => Phase7Convergence.minorityU σ c))ᶜ
      ≤ 1 - ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hdone_eq :
      (OneSidedCancel.potDone (fun c : Config (AgentState L K) =>
          Phase7Convergence.minorityU σ c))ᶜ
      = (OneSidedCancel.potBelow (fun c : Config (AgentState L K) =>
          Phase7Convergence.minorityU σ c) 1)ᶜ := by
    ext y
    simp only [OneSidedCancel.potDone, OneSidedCancel.potBelow,
      Set.mem_compl_iff, Set.mem_setOf_eq]; omega
  rw [hdone_eq]
  exact phase8_hdrop_of_struct σ n 1 hn b hb8 hb1 i E hmin helim

/-! ## Part C — Phase 7 (`classMassN σ`, `Inv7Sum`, α = 4/15).

The carried eliminator floor (Doty Lemma 7.4 `elimGap1 ≥ 0.8·mainCount ≥ 4n/15`) supplies,
at a gap-1 witness pair of levels `(i, j)` with `j = i + 1`, an eliminator margin
`(elimGap1 σ i).sum count ≥ E` and at least one minority at the larger level `j`
(`(minorityAt7 σ j).sum count ≥ 1`).  Threaded through `classMassN_drop_prob_rect7`, this
yields the drop floor `ofReal(E/(n(n−1))) ≤ classMass-drop-mass`, which the existing
packagers `classMassN_hdrop_of_floor7` (levels) / `classMassN_hstep_of_floor7` (crude
`m = 1`) turn into the engine `hdrop` / `hstep`. -/

/-- **Phase 7 — structural floor ⟹ concrete σ-class-mass drop floor.**  At a gap-1 witness
`(i, j=i+1)` with `≥ 1` minority at `j` and eliminator margin `≥ E` at `i`, the one-step
drop probability of `classMassN σ` is `≥ ofReal(E/(n(n−1)))`. -/
theorem phase7_drop_floor_of_struct {L K : ℕ} (σ : Sign) (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : Phase7Convergence.Phase7AllMain n c)
    (i j : Fin (L + 1)) (hg1 : i.val + 1 = j.val) (E : ℕ)
    (hmin : 1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count)
    (helim : E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count) :
    ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase7Convergence.classMassN σ c' + 1 ≤ Phase7Convergence.classMassN σ c} := by
  refine le_trans ?_ (Phase7Convergence.classMassN_drop_prob_rect7 σ n hn c hInv i j hg1)
  have hprod : (E : ℕ) ≤
      (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count *
        (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count := by
    calc (E : ℕ) ≤ E * 1 := by omega
      _ ≤ E * (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count :=
          Nat.mul_le_mul_left _ hmin
      _ ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum c.count *
            (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count :=
          Nat.mul_le_mul_right _ helim
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply DrainThreading.ofReal_div_le_of_num_le _ (by positivity) (by nlinarith)
  exact_mod_cast hprod

/-- **Phase 7 — the levels-engine `hdrop` from the structural floor.** -/
theorem phase7_hdrop_of_struct {L K : ℕ} (σ : Sign) (n m : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hb7 : Phase7Convergence.Phase7AllMain n b)
    (hbm : Phase7Convergence.classMassN σ b = m)
    (i j : Fin (L + 1)) (hg1 : i.val + 1 = j.val) (E : ℕ)
    (hmin : 1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum b.count)
    (helim : E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.classMassN σ) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  Phase7Convergence.classMassN_hdrop_of_floor7 σ m
    (ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) b hbm
    (phase7_drop_floor_of_struct σ n hn b hb7 i j hg1 E hmin helim)

/-- **Phase 7 — the crude-engine `hstep` from the structural floor, at `m = 1`.**  At
`classMassN σ b = 1` the strict-drop event reaches `potDone`, so the structural floor gives
the crude `hstep` failure `(potDone)ᶜ ≤ 1 − ofReal(E/(n(n−1)))`.  (For `classMassN σ b ≥ 2`
a single cancel drops the mass by `≥ 1` but not to `0`, so the crude `hstep` is structurally
vacuous there; the honest multi-level mass drain uses `phase7_hdrop_of_struct` + levels.) -/
theorem phase7_hstep_of_struct_one {L K : ℕ} (σ : Sign) (n : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hb7 : Phase7Convergence.Phase7AllMain n b)
    (hb1 : Phase7Convergence.classMassN σ b = 1)
    (i j : Fin (L + 1)) (hg1 : i.val + 1 = j.val) (E : ℕ)
    (hmin : 1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum b.count)
    (helim : E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potDone (fun c => Phase7Convergence.classMassN σ c))ᶜ
      ≤ 1 - ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  Phase7Convergence.classMassN_hstep_of_floor7 σ
    (ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) b hb1
    (phase7_drop_floor_of_struct σ n hn b hb7 i j hg1 E hmin helim)

/-! ## Part D — Phase 1 (`extremeU`, `Phase1AllMain`, α = 1/3).

Phase 1 had no drop-rectangle lemma; we build it here.  The drain event is the
`avgFin7` averaging fire that pulls a saturated-extreme Main off the boundary.  Reading
the actual rule (`Transition_eq_avg_of_phase1_main`), the HONEST drop cell is:

* a `+3`-extreme Main (`smallBias.val = 6`) averaged with a Main whose `smallBias.val ≤ 4`
  (any value not on the same `+2/+3` saturated side) — `avgFin7 6 y = (⌊(6+y)/2⌋, ⌈⌉)`,
  both outputs interior for `y ≤ 4`, so the pair `extremeU` drops by `≥ 1`;
* symmetrically a `−3`-extreme Main (`smallBias.val = 0`) with a partner `smallBias.val ≥ 2`.

The rate degrades only against the SAME-side neighbours (`+2,+3` for a `+3` extreme); the
honest partner floor is the OPPOSITE-half Main pool.  We expose the partner floor as a
named count (`pullPosSet` finset sum `≥ P`) — provenance `RoleSplitWindows mainCount ≥ n/3`
minus the (vanishing) same-side count.  Threading it through the generic
`Phase7Convergence.drop_prob_of_rect` (Φ-agnostic) yields the drop floor
`ofReal(P/(n(n−1)))`. -/

open Phase1Convergence

/-- A `+3`-extreme Main: a phase-1 Main pinned at `smallBias.val = 6`. -/
def extremePos {L K : ℕ} (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ a.smallBias.val = 6

instance {L K : ℕ} (a : AgentState L K) : Decidable (extremePos a) := by
  unfold extremePos; infer_instance

/-- The partner pool for a `+3` extreme: phase-1 Mains with `smallBias.val ≤ 4` (any value
not on the same `+2/+3` saturated side), which average a `+3` extreme to an interior pair. -/
def pullPos {L K : ℕ} (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ a.smallBias.val ≤ 4

instance {L K : ℕ} (a : AgentState L K) : Decidable (pullPos a) := by
  unfold pullPos; infer_instance

/-- The finset of `+3`-extreme Main states. -/
def extremePosSet (L K : ℕ) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => extremePos a)

/-- The finset of partner (`smallBias.val ≤ 4`) Main states. -/
def pullPosSet (L K : ℕ) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => pullPos a)

/-- An extreme-`+3` Main and a partner-pool Main are distinct states (their `smallBias`
values differ: `6` vs `≤ 4`). -/
theorem extremePos_pullPos_disjoint {L K : ℕ}
    (a : AgentState L K) (ha : a ∈ extremePosSet L K)
    (b : AgentState L K) (hb : b ∈ pullPosSet L K) : a ≠ b := by
  simp only [extremePosSet, pullPosSet, Finset.mem_filter, extremePos, pullPos] at ha hb
  obtain ⟨_, _, hav⟩ := ha
  obtain ⟨_, _, hbv⟩ := hb
  intro heq; rw [heq] at hav; omega

/-- **The avgFin7 strict-drop cell (`+3` × partner).**  When `x = 6` (`+3`) and `y ≤ 4`,
the averaged pair has STRICTLY fewer saturated extremes than the inputs (`+1 ≤`). -/
theorem avgFin7_extremeVal_pair_drop_pos (x y : Fin 7) (hx : x.val = 6) (hy : y.val ≤ 4) :
    (if Phase1Convergence.extremeVal (avgFin7 x y).1 then 1 else 0)
        + (if Phase1Convergence.extremeVal (avgFin7 x y).2 then 1 else 0) + 1
      ≤ (if Phase1Convergence.extremeVal x then 1 else 0)
          + (if Phase1Convergence.extremeVal y then 1 else 0) := by
  have hxv : x = (6 : Fin 7) := Fin.ext (by simp [hx])
  subst hxv
  fin_cases y <;> first | (exfalso; revert hy; decide) | decide

/-- **Per-pair `extremeU` strict drop (`+3`-extreme × partner).**  A `+3`-extreme Main `s`
averaged with a partner-pool Main `t` (`smallBias.val ≤ 4`), both phase-1 Mains, drops the
pair `extremeU` by `≥ 1`. -/
theorem Transition_extremeU_pair_drop_pos {L K : ℕ} (s t : AgentState L K)
    (hs1 : s.phase.val = 1) (ht1 : t.phase.val = 1)
    (hsE : extremePos s) (htP : pullPos t) :
    Multiset.countP (fun a => Phase1Convergence.extremeSt a)
        ({(Transition L K s t).1, (Transition L K s t).2} : Multiset (AgentState L K)) + 1
      ≤ Multiset.countP (fun a => Phase1Convergence.extremeSt a)
          ({s, t} : Multiset (AgentState L K)) := by
  obtain ⟨hsM, hsv⟩ := hsE
  obtain ⟨htM, htv⟩ := htP
  rw [Phase1Convergence.Transition_eq_avg_of_phase1_main s t hs1 ht1 hsM htM]
  rw [Phase1Convergence.countP_extremeSt_pair, Phase1Convergence.countP_extremeSt_pair]
  set o1 := ({s with smallBias := (avgFin7 s.smallBias t.smallBias).1} : AgentState L K) with ho1
  set o2 := ({t with smallBias := (avgFin7 s.smallBias t.smallBias).2} : AgentState L K) with ho2
  have hkey : ∀ a : AgentState L K, a.role = Role.main →
      (Phase1Convergence.extremeSt a ↔ Phase1Convergence.extremeVal a.smallBias = true) :=
    fun a ha => by unfold Phase1Convergence.extremeSt; exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
  have ho1M : o1.role = Role.main := by rw [ho1]; exact hsM
  have ho2M : o2.role = Role.main := by rw [ho2]; exact htM
  have ho1sb : o1.smallBias = (avgFin7 s.smallBias t.smallBias).1 := by rw [ho1]
  have ho2sb : o2.smallBias = (avgFin7 s.smallBias t.smallBias).2 := by rw [ho2]
  rw [if_congr (hkey o1 ho1M) rfl rfl, if_congr (hkey o2 ho2M) rfl rfl,
      if_congr (hkey s hsM) rfl rfl, if_congr (hkey t htM) rfl rfl,
      ho1sb, ho2sb]
  have h := avgFin7_extremeVal_pair_drop_pos s.smallBias t.smallBias hsv htv
  simpa using h

/-- **Config-level `extremeU` strict drop.**  On a `Phase1AllMain` window, an applicable
`(s, t)` with `s` a `+3`-extreme Main and `t` a partner Main drops `extremeU` by `≥ 1`. -/
theorem extremeU_stepOrSelf_drop_pos {L K : ℕ} (n : ℕ) (c : Config (AgentState L K))
    (hInv : Phase1Convergence.Phase1AllMain n c) (s t : AgentState L K)
    (happ : Protocol.Applicable c s t) (hsE : extremePos s) (htP : pullPos t) :
    Phase1Convergence.extremeU (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1
      ≤ Phase1Convergence.extremeU c := by
  obtain ⟨_, hph⟩ := hInv
  have hsub : ({s, t} : Multiset (AgentState L K)) ≤ c := happ
  have hsm : s ∈ c := Multiset.mem_of_le hsub (by simp)
  have htm : t ∈ c := Multiset.mem_of_le hsub (by simp)
  obtain ⟨hs1, _⟩ := hph s hsm
  obtain ⟨ht1, _⟩ := hph t htm
  have hc' : Protocol.stepOrSelf (NonuniformMajority L K) c s t
      = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
    unfold Protocol.stepOrSelf; rw [if_pos happ]; rfl
  unfold Phase1Convergence.extremeU
  rw [hc', Multiset.countP_add, Multiset.countP_sub hsub]
  have hpair := Transition_extremeU_pair_drop_pos s t hs1 ht1 hsE htP
  have hpair_le : Multiset.countP (fun a => Phase1Convergence.extremeSt a)
      ({s, t} : Multiset (AgentState L K))
        ≤ Multiset.countP (fun a => Phase1Convergence.extremeSt a) c :=
    Multiset.countP_le_of_le _ hsub
  -- countP {s,t} ≥ 1 (it contains the extreme s); unfolding extremeU back.
  change Multiset.countP _ c - Multiset.countP _ ({s, t} : Multiset _)
      + Multiset.countP _ ({(Transition L K s t).1, (Transition L K s t).2} : Multiset _) + 1
    ≤ Multiset.countP _ c
  omega

/-- **Phase 1 — the `+3`-extreme × partner rectangle drop probability.**  On a
`Phase1AllMain` window, the probability that one step drops `extremeU` is at least
`(#extreme@+3)·(#partner)/(n(n−1))`. -/
theorem extremeU_drop_prob_rect_pos {L K : ℕ} (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : Phase1Convergence.Phase1AllMain n c) :
    ENNReal.ofReal
        (((extremePosSet L K).sum c.count * (pullPosSet L K).sum c.count : ℕ) /
          ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase1Convergence.extremeU c' + 1 ≤ Phase1Convergence.extremeU c} := by
  have hcardn : c.card = n := hInv.1
  refine Phase7Convergence.drop_prob_of_rect (fun c => Phase1Convergence.extremeU c) n hn c
    hcardn ((extremePosSet L K) ×ˢ (pullPosSet L K)) _ ?_ (le_of_eq ?_)
  · rintro ⟨s, t⟩ hp hcs hct _
    rw [Finset.mem_product] at hp
    obtain ⟨hsmem, htmem⟩ := hp
    simp only [extremePosSet, Finset.mem_filter] at hsmem
    simp only [pullPosSet, Finset.mem_filter] at htmem
    obtain ⟨_, hsE⟩ := hsmem
    obtain ⟨_, htP⟩ := htmem
    have happ : Protocol.Applicable c s t := by
      have hsm : s ∈ c := Multiset.one_le_count_iff_mem.mp hcs
      have htm : t ∈ c := Multiset.one_le_count_iff_mem.mp hct
      have hne : s ≠ t := extremePos_pullPos_disjoint s
        (by simp only [extremePosSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hsE⟩) t
        (by simp only [pullPosSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _, htP⟩)
      exact Phase5Convergence.applicable_of_mem_distinct5 hsm htm hne
    exact extremeU_stepOrSelf_drop_pos n c hInv s t happ hsE htP
  · rw [Phase7Convergence.sum_interactionCount_cross_disjoint7 c _ _
      extremePos_pullPos_disjoint]

/-- **Phase 1 — the levels-engine `hdrop` from a drop-probability floor.**  Mirror of
`minorityU_hdrop_of_floor`: from a strict-drop floor `p` at a state with `extremeU b = m`,
the level-`m` failure mass is `≤ 1 − p` (`transitionKernel` Markov). -/
theorem extremeU_hdrop_of_floor {L K : ℕ} (m : ℕ) (p : ℝ≥0∞)
    (b : Config (AgentState L K)) (hbm : Phase1Convergence.extremeU b = m)
    (hfloor : p ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
        {c' | Phase1Convergence.extremeU c' + 1 ≤ Phase1Convergence.extremeU b}) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase1Convergence.extremeU) m)ᶜ ≤ 1 - p := by
  classical
  have hKb : (NonuniformMajority L K).transitionKernel b
      = ((NonuniformMajority L K).stepDistOrSelf b).toMeasure := rfl
  have hsucc_eq : {c' : Config (AgentState L K) |
        Phase1Convergence.extremeU c' + 1 ≤ Phase1Convergence.extremeU b}
      = OneSidedCancel.potBelow (Phase1Convergence.extremeU) m := by
    ext c'; simp only [OneSidedCancel.potBelow, Set.mem_setOf_eq, hbm]; omega
  have hmeas : MeasurableSet (OneSidedCancel.potBelow (Phase1Convergence.extremeU) m) :=
    OneSidedCancel.potBelow_measurable (Phase1Convergence.extremeU (L := L) (K := K)) m
  haveI hprob : IsProbabilityMeasure
      (((NonuniformMajority L K).stepDistOrSelf b).toMeasure) := by
    rw [← hKb]
    exact (inferInstance :
      IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure b
  have htot : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure Set.univ = 1 :=
    hprob.measure_univ
  have hcompl : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
        (OneSidedCancel.potBelow (Phase1Convergence.extremeU) m)ᶜ
      = 1 - ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
          (OneSidedCancel.potBelow (Phase1Convergence.extremeU) m) := by
    rw [measure_compl hmeas (measure_ne_top _ _), htot]
  rw [hKb, hcompl]
  have hp_le : p ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
      (OneSidedCancel.potBelow (Phase1Convergence.extremeU) m) := by
    rw [← hsucc_eq]; exact hfloor
  exact tsub_le_tsub_left hp_le 1

/-- **Phase 1 — structural floor ⟹ concrete drop-probability floor.**  With `≥ 1` extreme
at `+3` and a partner-pool margin `≥ P`, the one-step `extremeU` drop probability is
`≥ ofReal(P/(n(n−1)))`. -/
theorem phase1_drop_floor_of_struct {L K : ℕ} (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : Phase1Convergence.Phase1AllMain n c) (P : ℕ)
    (hext : 1 ≤ (extremePosSet L K).sum c.count)
    (hpull : P ≤ (pullPosSet L K).sum c.count) :
    ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase1Convergence.extremeU c' + 1 ≤ Phase1Convergence.extremeU c} := by
  refine le_trans ?_ (extremeU_drop_prob_rect_pos n hn c hInv)
  have hprod : (P : ℕ) ≤ (extremePosSet L K).sum c.count * (pullPosSet L K).sum c.count := by
    calc (P : ℕ) ≤ 1 * P := by omega
      _ ≤ (extremePosSet L K).sum c.count * P := Nat.mul_le_mul_right _ hext
      _ ≤ (extremePosSet L K).sum c.count * (pullPosSet L K).sum c.count :=
          Nat.mul_le_mul_left _ hpull
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply DrainThreading.ofReal_div_le_of_num_le _ (by positivity) (by nlinarith)
  exact_mod_cast hprod

/-- **Phase 1 — the levels-engine `hdrop` from the structural floor.** -/
theorem phase1_hdrop_of_struct {L K : ℕ} (n m : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hInv : Phase1Convergence.Phase1AllMain n b)
    (hbm : Phase1Convergence.extremeU b = m) (P : ℕ)
    (hext : 1 ≤ (extremePosSet L K).sum b.count)
    (hpull : P ≤ (pullPosSet L K).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase1Convergence.extremeU) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  extremeU_hdrop_of_floor m (ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) b hbm
    (phase1_drop_floor_of_struct n hn b hInv P hext hpull)

/-- **Phase 1 — the crude-engine `hstep` from the structural floor, at `m = 1`.** -/
theorem phase1_hstep_of_struct_one {L K : ℕ} (n : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hInv : Phase1Convergence.Phase1AllMain n b)
    (hb1 : Phase1Convergence.extremeU b = 1) (P : ℕ)
    (hext : 1 ≤ (extremePosSet L K).sum b.count)
    (hpull : P ≤ (pullPosSet L K).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potDone (fun c => Phase1Convergence.extremeU c))ᶜ
      ≤ 1 - ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hdone_eq :
      (OneSidedCancel.potDone (fun c : Config (AgentState L K) =>
          Phase1Convergence.extremeU c))ᶜ
      = (OneSidedCancel.potBelow (Phase1Convergence.extremeU (L := L) (K := K)) 1)ᶜ := by
    ext y
    simp only [OneSidedCancel.potDone, OneSidedCancel.potBelow,
      Set.mem_compl_iff, Set.mem_setOf_eq]; omega
  rw [hdone_eq]
  exact phase1_hdrop_of_struct n 1 hn b hInv hb1 P hext hpull

/-! ## Part E — Phase 5 (`unsampledReserveU`, `Phase5AllWin`, α = 23/75).

The carried structural floor (Theorem 6.2 biased structure `biasedMainLtL ≥ 0.92·mainCount
≥ 23n/75`) supplies the useful-Main margin `(usefulMains).sum count ≥ P` together with `≥ 1`
unsampled Reserve.  Threaded through the existing `unsampledReserveU_drop_prob_rect5`
(rect `unsampledReserves ×ˢ usefulMains`), this yields the drop floor `ofReal(P/(n(n−1)))`,
and the in-file generic packager gives the engine `hdrop` / `hstep`.  Phase 5's sampling
concentration `εConc`/`hConc` is a SEPARATE carried atom (not a drain budget) and is
untouched here. -/

open Phase5Convergence in
/-- **Phase 5 — the levels-engine `hdrop` from a drop-probability floor.**  Mirror of
`minorityU_hdrop_of_floor`, for `Φ = unsampledReserveU`. -/
theorem unsampledReserveU_hdrop_of_floor {L K : ℕ} (n m : ℕ) (p : ℝ≥0∞)
    (b : Config (AgentState L K))
    (hbm : ReserveSampling.unsampledReserveU (L := L) (K := K) b = m)
    (hfloor : p ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
        {c' | ReserveSampling.unsampledReserveU (L := L) (K := K) c' + 1
          ≤ ReserveSampling.unsampledReserveU (L := L) (K := K) b}) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow
          (ReserveSampling.unsampledReserveU (L := L) (K := K)) m)ᶜ ≤ 1 - p := by
  classical
  have hKb : (NonuniformMajority L K).transitionKernel b
      = ((NonuniformMajority L K).stepDistOrSelf b).toMeasure := rfl
  have hsucc_eq : {c' : Config (AgentState L K) |
        ReserveSampling.unsampledReserveU (L := L) (K := K) c' + 1
          ≤ ReserveSampling.unsampledReserveU (L := L) (K := K) b}
      = OneSidedCancel.potBelow (ReserveSampling.unsampledReserveU (L := L) (K := K)) m := by
    ext c'; simp only [OneSidedCancel.potBelow, Set.mem_setOf_eq, hbm]; omega
  have hmeas : MeasurableSet
      (OneSidedCancel.potBelow (ReserveSampling.unsampledReserveU (L := L) (K := K)) m) :=
    OneSidedCancel.potBelow_measurable
      (ReserveSampling.unsampledReserveU (L := L) (K := K)) m
  haveI hprob : IsProbabilityMeasure
      (((NonuniformMajority L K).stepDistOrSelf b).toMeasure) := by
    rw [← hKb]
    exact (inferInstance :
      IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure b
  have htot : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure Set.univ = 1 :=
    hprob.measure_univ
  have hcompl : ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
        (OneSidedCancel.potBelow (ReserveSampling.unsampledReserveU (L := L) (K := K)) m)ᶜ
      = 1 - ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
          (OneSidedCancel.potBelow (ReserveSampling.unsampledReserveU (L := L) (K := K)) m) := by
    rw [measure_compl hmeas (measure_ne_top _ _), htot]
  rw [hKb, hcompl]
  have hp_le : p ≤ ((NonuniformMajority L K).stepDistOrSelf b).toMeasure
      (OneSidedCancel.potBelow (ReserveSampling.unsampledReserveU (L := L) (K := K)) m) := by
    rw [← hsucc_eq]; exact hfloor
  exact tsub_le_tsub_left hp_le 1

/-- **Phase 5 — structural floor ⟹ concrete drop-probability floor.**  With `≥ 1` unsampled
Reserve and a useful-Main margin `≥ P`, the one-step `unsampledReserveU` drop probability is
`≥ ofReal(P/(n(n−1)))`. -/
theorem phase5_drop_floor_of_struct {L K : ℕ} (n : ℕ) (hn : 2 ≤ n)
    (c : Config (AgentState L K)) (hInv : ReserveSampling.Phase5AllWin n c) (P : ℕ)
    (hres : 1 ≤ (Phase5Convergence.unsampledReserves (L := L) (K := K)).sum c.count)
    (hmain : P ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count) :
    ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | ReserveSampling.unsampledReserveU (L := L) (K := K) c' + 1
          ≤ ReserveSampling.unsampledReserveU (L := L) (K := K) c} := by
  refine le_trans ?_ (Phase5Convergence.unsampledReserveU_drop_prob_rect5 n hn c hInv)
  have hprod : (P : ℕ) ≤
      (Phase5Convergence.unsampledReserves (L := L) (K := K)).sum c.count *
        (Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count := by
    calc (P : ℕ) ≤ 1 * P := by omega
      _ ≤ (Phase5Convergence.unsampledReserves (L := L) (K := K)).sum c.count * P :=
          Nat.mul_le_mul_right _ hres
      _ ≤ (Phase5Convergence.unsampledReserves (L := L) (K := K)).sum c.count *
            (Phase5Convergence.usefulMains (L := L) (K := K)).sum c.count :=
          Nat.mul_le_mul_left _ hmain
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply DrainThreading.ofReal_div_le_of_num_le _ (by positivity) (by nlinarith)
  exact_mod_cast hprod

/-- **Phase 5 — the levels-engine `hdrop` from the structural floor.** -/
theorem phase5_hdrop_of_struct {L K : ℕ} (n m : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hInv : ReserveSampling.Phase5AllWin n b)
    (hbm : ReserveSampling.unsampledReserveU (L := L) (K := K) b = m) (P : ℕ)
    (hres : 1 ≤ (Phase5Convergence.unsampledReserves (L := L) (K := K)).sum b.count)
    (hmain : P ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow
          (ReserveSampling.unsampledReserveU (L := L) (K := K)) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  unsampledReserveU_hdrop_of_floor n m
    (ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) b hbm
    (phase5_drop_floor_of_struct n hn b hInv P hres hmain)

/-- **Phase 5 — the crude-engine `hstep` from the structural floor, at `m = 1`.** -/
theorem phase5_hstep_of_struct_one {L K : ℕ} (n : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hInv : ReserveSampling.Phase5AllWin n b)
    (hb1 : ReserveSampling.unsampledReserveU (L := L) (K := K) b = 1) (P : ℕ)
    (hres : 1 ≤ (Phase5Convergence.unsampledReserves (L := L) (K := K)).sum b.count)
    (hmain : P ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potDone
          (fun c => ReserveSampling.unsampledReserveU (L := L) (K := K) c))ᶜ
      ≤ 1 - ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hdone_eq :
      (OneSidedCancel.potDone (fun c : Config (AgentState L K) =>
          ReserveSampling.unsampledReserveU (L := L) (K := K) c))ᶜ
      = (OneSidedCancel.potBelow
          (ReserveSampling.unsampledReserveU (L := L) (K := K)) 1)ᶜ := by
    ext y
    simp only [OneSidedCancel.potDone, OneSidedCancel.potBelow,
      Set.mem_compl_iff, Set.mem_setOf_eq]; omega
  rw [hdone_eq]
  exact phase5_hdrop_of_struct n 1 hn b hInv hb1 P hres hmain

/-! ## Part F — Phase 6 (`highMass l`, `Phase6Win`, per-level ρ₆ rates, LEVELS form a).

Phase 6 already runs on the LEVELS engine (`levels_PhaseConvergenceW`), so the honest
deliverable is the per-level `hdrop` directly (no crude `m = 1` restriction needed).  The
carried structural floor (`ReserveSampleGood K₀` / Phase-5 `sampledReserveClassU`, the
band-top reserve fraction `ρ₆`) supplies, at a witness hour `h` (`l−1 < h ≠ L`), the
reserve margin `(reserveAtHour6 h).sum count ≥ R` together with `≥ 1` band-`l` biased Main
(`(mainAt6 σ l).sum count ≥ 1`).  Threaded through `highMass_drop_prob_rect6`, this yields
the drop floor `ofReal(R/(n(n−1)))`, which `highMass_hdrop_of_floor6` turns into the
per-level engine `hdrop`. -/

/-- **Phase 6 — structural floor ⟹ concrete per-level drop-probability floor.**  At a
witness hour `h` (`l−1 < h ≠ L`) with `≥ 1` band-`l` Main and a reserve margin `≥ R`, the
one-step `highMass l` drop probability is `≥ ofReal(R/(n(n−1)))`. -/
theorem phase6_drop_floor_of_struct {L K : ℕ} (σ : Sign) (l n : ℕ) (hn : 2 ≤ n)
    (hl1 : 1 ≤ l) (hlL : l ≤ L) (c : Config (AgentState L K))
    (hInv : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (h : Fin (L + 1)) (hhgt : l - 1 < h.val) (hhne : h.val ≠ L) (R : ℕ)
    (hmain : 1 ≤ (Phase6Convergence.mainAt6 (L := L) (K := K) σ l hl1 hlL).sum c.count)
    (hres : R ≤ (Phase6Convergence.reserveAtHour6 (L := L) (K := K) h).sum c.count) :
    ENNReal.ofReal ((R : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) ≤
      ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | Phase6Convergence.highMass (L := L) (K := K) l c' + 1
          ≤ Phase6Convergence.highMass (L := L) (K := K) l c} := by
  refine le_trans ?_ (Phase6Convergence.highMass_drop_prob_rect6 σ l n hn hl1 hlL c hInv h hhgt hhne)
  have hprod : (R : ℕ) ≤
      (Phase6Convergence.reserveAtHour6 (L := L) (K := K) h).sum c.count *
        (Phase6Convergence.mainAt6 (L := L) (K := K) σ l hl1 hlL).sum c.count := by
    calc (R : ℕ) ≤ R * 1 := by omega
      _ ≤ R * (Phase6Convergence.mainAt6 (L := L) (K := K) σ l hl1 hlL).sum c.count :=
          Nat.mul_le_mul_left _ hmain
      _ ≤ (Phase6Convergence.reserveAtHour6 (L := L) (K := K) h).sum c.count *
            (Phase6Convergence.mainAt6 (L := L) (K := K) σ l hl1 hlL).sum c.count :=
          Nat.mul_le_mul_right _ hres
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply DrainThreading.ofReal_div_le_of_num_le _ (by positivity) (by nlinarith)
  exact_mod_cast hprod

/-- **Phase 6 — the per-level levels-engine `hdrop` from the structural floor.**  At a level
`m` with `highMass l b = m` and the carried reserve floor (`≥ R` reserves at witness hour
`h`, `≥ 1` band-`l` Main), the level-`m` failure mass is `≤ 1 − ofReal(R/(n(n−1)))`. -/
theorem phase6_hdrop_of_struct {L K : ℕ} (σ : Sign) (l n m : ℕ) (hn : 2 ≤ n)
    (hl1 : 1 ≤ l) (hlL : l ≤ L) (b : Config (AgentState L K))
    (hInv : Phase6Convergence.Phase6Win (L := L) (K := K) n b)
    (hbm : Phase6Convergence.highMass (L := L) (K := K) l b = m)
    (h : Fin (L + 1)) (hhgt : l - 1 < h.val) (hhne : h.val ≠ L) (R : ℕ)
    (hmain : 1 ≤ (Phase6Convergence.mainAt6 (L := L) (K := K) σ l hl1 hlL).sum b.count)
    (hres : R ≤ (Phase6Convergence.reserveAtHour6 (L := L) (K := K) h).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (fun c => Phase6Convergence.highMass (L := L) (K := K) l c) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((R : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  Phase6Convergence.highMass_hdrop_of_floor6 l m
    (ENNReal.ofReal ((R : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)))) b hbm
    (phase6_drop_floor_of_struct σ l n hn hl1 hlL b hInv h hhgt hhne R hmain hres)

end DrainThreading

end ExactMajority
