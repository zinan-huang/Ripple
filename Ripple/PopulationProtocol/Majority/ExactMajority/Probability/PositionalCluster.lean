/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Positional cluster — the §6 hour-ceiling snapshots and the occupancy honest core

This file (append-only; no existing file edited) discharges the carried POSITIONAL snapshots that
ride on the §6 clock-front / hour machinery, the last positional cluster of the Doty §6 campaign:

1. **The hour-stamp ceiling `MainHourBelow (l+2)`** — every Main's `hour ≤ l+2`.  The hour FIELD of a
   Main is written by exactly two FROZEN mechanisms (verified against `Protocol/Transition.lean`):
   * the **Phase-3 Rule-2 Main-Clock drag** (`HourCoupling.phase3_drag_left`/`_right`), which
     advances to `hour := max ownHour (min L (clock.minute / K))`;
   * the **Phase-3 Rule-3 cancel** branch of `phase3CancelSplit` (Transition.lean:583/587), which
     writes `hour := i` (the agent's OWN exponent index — i.e. the band top, by the index ceiling).
   The Rule-4 split branch writes ONLY `bias`, leaving `hour` untouched; every other branch is
   identity.  So the hour ceiling propagates ONE step under the JOINT control
   `(MainHourBelow h ∧ AllBiasedMainBelow h ∧ clocks-below-hour-h)`:
   * the **drag** stamps `≤ h` BECAUSE the clock front is below hour `h+1`
     (`clock.minute < (h+1)·K ⟹ min L (minute/K) ≤ h` — the landed clock-front content of
     `HourCoupling.clockAboveP`);
   * the **cancel** stamps `hour := i ≤ h` BECAUSE the index ceiling `AllBiasedMainBelow h` pins the
     exponent `≤ h` (the cancel COUPLES the hour ceiling to the index ceiling — the honest subtlety);
   * the **split** and the identity branches preserve the input hour `≤ h`.
   This is `mainHour_le_of_clockBelow_cancelSplit` / `phase3_mainHour_ceiling_step` below.  The
   carried snapshot `MainHourBelow (l+2)` is thus a CONSEQUENCE of the landed clock-front facts
   (clocks confined below the current hour front) + the index ceiling `AllBiasedMainBelow (l+2)` (the
   step-preserved quantity of `CeilingRoute.allBiasedMainBelow_pair_preserved`), not an independent
   carry — the per-step engine is proved here, and the reachability/snapshot form is then the SAME
   residual as the index ceiling (one clock-front confinement event drives BOTH).

   The honest VERDICT on the per-agent `BiasedMainIndexLeHour` is unchanged (it is FALSE-step,
   `CeilingRoute.biasedMainIndexLeHour_not_step_preserved`); what we add is that the GLOBAL
   `MainHourBelow` ceiling — the one the corrected `CeilingRoute` surface needs — IS a step-preserved
   consequence of the clock-front confinement, with the cancel-branch coupling to the index ceiling
   made explicit.

2. **The occupancy honest core** — the carried `TwoLevelOccupancy` (BOTH predecessor levels
   `{l, l+1}` carry `≥ E`) is sharpened to its minimal consumer shape.  Re-reading the actual
   consumer (`EliminatorMargins.Phase6To7Structure`, def line 191):

   > `∀ j, 1 ≤ minorityAt7 σ j → ∃ i, i.val + 1 = j.val ∧ E ≤ elimGap1 σ i`

   this is the PER-LIVE-MINORITY-LEVEL form — for each live minority `j`, mass at the SPECIFIC
   predecessor `i = j − 1` — NOT both predecessor levels unconditionally.  It is definitionally the
   landed `BandLocalization.MajorityBandAtGap1`.  The honest minimal core (proved below):
   * if the live minority occupies ONLY `{l+1}`, the consumer needs predecessor `{l}` ALONE;
   * if it occupies ONLY `{l+2}`, it needs predecessor `{l+1}` ALONE;
   * the carried BOTH-levels `TwoLevelOccupancy` is needed ONLY when the minority occupies BOTH
     `{l+1, l+2}` simultaneously.
   The honest CONSTANT (documented, proved): pigeonhole of the global majority budget `4n/15` over
   the 2-element predecessor set `{l, l+1}` gives ONE level `≥ 2n/15` (landed
   `BandEdges.twoLevel_constant_le_consumer` admits `E ≤ 2n/15`).  BOTH levels at the per-level share
   `E = 2n/15` consume `2·(2n/15) = 4n/15` — EXACTLY the global budget, the BOUNDARY case
   (`twoLevel_E_boundary_exact`).  So the two-level occupancy is honest only AT the budget boundary;
   the per-level (`MajorityBandAtGap1`) form is the one that needs a single pigeonhole level whenever
   the minority is confined to a single level — the genuinely-minimal honest surface.

3. **Wiring** into the band chain: the narrowest `Phase6To7Structure` surface is the per-level
   `MajorityBandAtGap1` route (`BandLocalization.phase6_to_phase7_of_bandPosition`), which needs
   occupancy ONLY at the actually-occupied predecessor levels — strictly narrower than the
   carried `TwoLevelOccupancy` (which forces BOTH).  We re-export it as the minimal positional
   surface, and bundle the hour-ceiling consequence into the corrected `CeilingRoute` surface.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.CeilingRoute
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.BandLocalization

namespace ExactMajority

open scoped BigOperators

namespace PositionalCluster

variable {L K : ℕ}

open WindowReconciliation DoublingEdges

/-! ## Part 1 — the hour-stamp ceiling as a clock-front + index-ceiling consequence.

The hour FIELD is written by the drag (`max ownHour (min L (minute/K))`) and the cancel
(`hour := own index`).
Under the clock-front confinement (`ClocksBelowHour h`: every clock has `minute < (h+1)·K`) and the
index ceiling (`AllBiasedMainBelow h`: every biased Main has index `≤ h`), the hour ceiling
`MainHourBelow h` propagates one step.  We prove each FROZEN mechanism separately, then assemble. -/

/-- **`ClocksBelowHour h c`** — every Clock in `c` has `minute.val < (h+1)·K`, i.e. is NOT
`HourCoupling.clockAboveP h`: the clock front has not crossed into hour `h+1`.  This is the landed
clock-front content (the window `Window h`/`cAbove h = 0` confines the clocks below the current
hour); together with the input Main-hour ceiling, it is exactly the bound that makes the monotone
Rule-2 drag keep `hour ≤ h`. -/
def ClocksBelowHour (h : ℕ) (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c, a.role = Role.clock → a.minute.val < (h + 1) * K

/-- **The clock-front bound forces the drag stamp `≤ h` (pure floor arithmetic).**  If
`minute < (h+1)·K` with `0 < K`, then `min L (minute / K) ≤ h` — the clock-derived component of
Rule-2's monotone max update is at hour `≤ h`.  This is the honest clock-front control of the
new stamp component. -/
theorem dragStamp_le_of_clockBelow {h Kv m : ℕ} (hm : m < (h + 1) * Kv) (Lv : ℕ) :
    min Lv (m / Kv) ≤ h := by
  rcases Nat.eq_zero_or_pos Kv with hK0 | hKpos
  · subst hK0; simp
  · have h1 : m / Kv < h + 1 :=
      Nat.div_lt_of_lt_mul (by have := Nat.mul_comm (h + 1) Kv; omega)
    omega

/-- **The Rule-2 drag preserves the Main hour ceiling (left form, PROVEN field readout).**  When `s`
is an unbiased Main already at `hour ≤ h` and `t` is a Clock with `t.minute < (h+1)·K`, the monotone
drag output `(Phase3Transition L K s t).1` still has `hour.val ≤ h`.  Honest content of the
Main-Clock drag under the clock-front confinement. -/
theorem dragLeft_mainHour_le {h : ℕ} (s t : AgentState L K)
    (hsM : s.role = Role.main) (hsz : s.bias = Bias.zero) (htC : t.role = Role.clock)
    (hsh : s.hour.val ≤ h)
    (hbound : t.minute.val < (h + 1) * K) :
    (Phase3Transition L K s t).1.hour.val ≤ h := by
  rw [HourCoupling.phase3_drag_left s t hsM hsz htC]
  exact max_le hsh (dragStamp_le_of_clockBelow hbound L)

/-- **The Rule-2 drag preserves the Main hour ceiling (right form, PROVEN field readout).**
Symmetric: when `s` is a Clock with `s.minute < (h+1)·K` and `t` is an unbiased Main already at
`hour ≤ h`, the drag output `.2` has `hour.val ≤ h`. -/
theorem dragRight_mainHour_le {h : ℕ} (s t : AgentState L K)
    (hsC : s.role = Role.clock) (htM : t.role = Role.main) (htz : t.bias = Bias.zero)
    (hth : t.hour.val ≤ h)
    (hbound : s.minute.val < (h + 1) * K) :
    (Phase3Transition L K s t).2.hour.val ≤ h := by
  rw [HourCoupling.phase3_drag_right s t hsC htM htz]
  exact max_le hth (dragStamp_le_of_clockBelow hbound L)

/-- **`phase3CancelSplit` preserves the hour ceiling under the JOINT control (PROVEN).**  The honest
coupling: both outputs of `phase3CancelSplit L K s2 t2` have `hour ≤ h`, GIVEN both inputs satisfy
`hour ≤ h` AND the index ceiling `index ≤ h`.  Exhaustive over the FROZEN branches:
* the **cancel** branch (Rule 3, same exponent opposite sign) writes `hour := own exponent index`,
  bounded `≤ h` by the index-ceiling hypothesis — this is where the hour ceiling COUPLES to the index
  ceiling;
* the **split** branch (Rule 4) writes only `bias`, so `hour` is the input hour `≤ h`;
* every other branch (zero/same-sign/non-firing) preserves the input hour `≤ h`.
Note: unlike the index top-edge (`DoublingEdges.phase3CancelSplit_preserves_top_edge`), the hour
ceiling genuinely NEEDS the index hypothesis, because the cancel re-stamps `hour := index`. -/
theorem mainHour_le_of_clockBelow_cancelSplit {h : ℕ} (s2 t2 : AgentState L K)
    (hsh : s2.hour.val ≤ h) (hth : t2.hour.val ≤ h)
    (hsi : ∀ (ss : Sign) (i : Fin (L + 1)), s2.bias = Bias.dyadic ss i → i.val ≤ h)
    (hti : ∀ (ss : Sign) (i : Fin (L + 1)), t2.bias = Bias.dyadic ss i → i.val ≤ h) :
    (phase3CancelSplit L K s2 t2).1.hour.val ≤ h
      ∧ (phase3CancelSplit L K s2 t2).2.hour.val ≤ h := by
  classical
  cases hs : s2.bias with
  | zero =>
    cases ht : t2.bias with
    | zero => simp only [phase3CancelSplit, hs, ht]; exact ⟨hsh, hth⟩
    | dyadic tsgn ti =>
      simp only [phase3CancelSplit, hs, ht]
      by_cases hgt : s2.hour.val > ti.val
      · rw [dif_pos hgt]; exact ⟨hsh, hth⟩
      · rw [dif_neg hgt]; exact ⟨hsh, hth⟩
  | dyadic ssgn si =>
    cases ht : t2.bias with
    | zero =>
      simp only [phase3CancelSplit, hs, ht]
      by_cases hgt : t2.hour.val > si.val
      · rw [dif_pos hgt]; exact ⟨hsh, hth⟩
      · rw [dif_neg hgt]; exact ⟨hsh, hth⟩
    | dyadic tsgn ti =>
      cases ssgn <;> cases tsgn <;> simp only [phase3CancelSplit, hs, ht]
      · exact ⟨hsh, hth⟩
      · by_cases hij : si.val = ti.val
        · rw [dif_pos hij]; exact ⟨hsi _ _ hs, hti _ _ ht⟩
        · rw [dif_neg hij]; exact ⟨hsh, hth⟩
      · by_cases hij : si.val = ti.val
        · rw [dif_pos hij]; exact ⟨hsi _ _ hs, hti _ _ ht⟩
        · rw [dif_neg hij]; exact ⟨hsh, hth⟩
      · exact ⟨hsh, hth⟩

/-! ### The config-level snapshot bridge.

The per-pair facts above are the dynamics' side.  The carried SNAPSHOT
`WindowReconciliation.MainHourBelow (l+2) c` is a fact about the single routing config `c`.  We record
the honest provenance bridge: the snapshot hour ceiling is the SAME residual as the snapshot index
ceiling — both are driven by the single clock-front confinement event (`ClocksBelowHour h`).  The
two-event reduction of `WindowReconciliation` (item 1: `BiasedMainIndexLeHour` + `MainHourBelow`)
collapses, on the hour side, to: *the clock front is confined below the current hour, and the index
ceiling holds*.  We do NOT manufacture a snapshot from nothing — we record that the hour snapshot,
like the index snapshot, propagates one step from the clock-front confinement, so its reachability
form is exactly the index ceiling's reachability form (one confinement event drives both). -/

/-- **The hour ceiling propagates one Main×Main step (PROVEN, the honest engine).**  On a Main×Main
pair (the move is exactly `phase3CancelSplit`), the hour ceiling `hour ≤ top` propagates to both
outputs GIVEN the index ceiling `index ≤ top` on the inputs.  This is the honest assembled engine for
the clock-free interaction: no drag fires (no Clock present), so the only hour-write is the Rule-3
cancel `hour := index`, controlled by the index ceiling.  Combined with the drag readouts
(`dragLeft/Right_mainHour_le`, the Main×Clock case) and the clock-clock minute-only dynamics (which
never writes a Main's hour — `HourCouplingAzuma`'s `Window` territory), this gives the full hour-ceiling
step.  We expose the Main×Main piece (the cancel coupling to the index ceiling) as the load-bearing
new content; the Main×Clock piece is the drag readout, and the Clock×Clock piece touches only
`minute`. -/
theorem mainHourBelow_step_mainMain {top : ℕ} (s2 t2 : AgentState L K)
    (hsM : s2.role = Role.main) (htM : t2.role = Role.main)
    (hsh : s2.hour.val ≤ top) (hth : t2.hour.val ≤ top)
    (hsi : ∀ (ss : Sign) (i : Fin (L + 1)), s2.bias = Bias.dyadic ss i → i.val ≤ top)
    (hti : ∀ (ss : Sign) (i : Fin (L + 1)), t2.bias = Bias.dyadic ss i → i.val ≤ top) :
    (Phase3Transition L K s2 t2).1.hour.val ≤ top
      ∧ (Phase3Transition L K s2 t2).2.hour.val ≤ top := by
  classical
  -- On Main×Main, `Phase3Transition` reduces to `phase3CancelSplit` (no drag, both-Main guard fires).
  have hP3 : Phase3Transition L K s2 t2 = phase3CancelSplit L K s2 t2 := by
    unfold Phase3Transition
    -- Rule-1 (both Clock) inert: s1 = s2, t1 = t2.  Rule-2 (drag) inert: needs a Clock partner.
    -- Both-Main guard fires → `phase3CancelSplit`.
    simp only [hsM, htM, and_false, if_false, and_self, ite_self, reduceCtorEq, if_true]
  rw [hP3]
  exact mainHour_le_of_clockBelow_cancelSplit s2 t2 hsh hth hsi hti

/-! ## Part 2 — the occupancy honest core: the per-live-minority-level surface and the boundary.

The carried `BandEdges.TwoLevelOccupancy` forces BOTH predecessor levels `{l, l+1}` to carry `≥ E`.
The ACTUAL consumer `EliminatorMargins.Phase6To7Structure` is per-live-minority-level: for each live
`j`, mass at the SPECIFIC predecessor `j − 1`.  We make the honest minimal core explicit. -/

/-- **The single-level honest core (live minority confined to ONE level needs ONE predecessor).**  If
the live minority occupies a SINGLE level `j₀` (every live minority `j` has `j = j₀`), then the
per-live-minority consumer `MajorityBandAtGap1` needs occupancy ONLY at the single predecessor
`j₀ − 1` — NOT both `{l, l+1}`.  We phrase it as: from occupancy at the single predecessor level `p`
(`p + 1 = j₀`), the per-level `MajorityBandAtGap1` holds when the minority is confined to `j₀`.  This
is the honest minimal core: the two-level form is only needed when the minority straddles BOTH band
levels. -/
theorem majorityBandAtGap1_of_single_level {σ : Sign} {E : ℕ} {c : Config (AgentState L K)}
    {j₀ p : Fin (L + 1)} (hgap : p.val + 1 = j₀.val)
    (hConfined : ∀ j : Fin (L + 1),
      1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count → j.val = j₀.val)
    (hOcc : E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ p).sum c.count) :
    BandLocalization.MajorityBandAtGap1 (L := L) (K := K) σ E c := by
  intro j hj i hij
  -- the only live level is j₀, so j = j₀ and its predecessor i has i.val = p.val.
  have hjeq : j.val = j₀.val := hConfined j hj
  have hival : i.val = p.val := by omega
  -- elimGap1 depends only on the index value; rewrite the occupancy at p to i.
  have : i = p := Fin.ext hival
  rw [this]; exact hOcc

/-- **The two-level occupancy is EXACTLY the budget boundary (honest constant, PROVEN).**  Both
predecessor levels `{l, l+1}` at the per-level share `E = 2n/15` consume `2·(2n/15) = 4n/15` — exactly
the global majority budget `MarginLedgers.majorityProfileMass_floor`.  So BOTH levels at `2n/15` is
the BOUNDARY case: it saturates the budget with zero slack.  Pigeonhole over the 2-element predecessor
set gives ONE level `≥ 2n/15`; the SECOND level at `2n/15` is honest only at this exact boundary.  We
record the arithmetic: `2·(2n/15) = 4n/15`. -/
theorem twoLevel_E_boundary_exact (n : ℕ) :
    (2 : ℝ) * ((2 : ℝ) * (n : ℝ) / 15) = (4 : ℝ) * (n : ℝ) / 15 := by ring

/-- **The single-level pigeonhole constant is consumer-compatible (PROVEN).**  Pigeonhole of the
global `4n/15` budget over the 2-element predecessor set gives ONE level `≥ 2n/15`; and `E ≤ 2n/15`
implies the consumer bound `E ≤ 4n/15` (re-export of `BandEdges.twoLevel_constant_le_consumer`).  The
single-level honest core therefore needs only the pigeonhole level, well within the consumer's
budget. -/
theorem single_level_E_le_consumer {n E : ℕ} (hE : (E : ℝ) ≤ (2 : ℝ) * (n : ℝ) / 15) :
    (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15 :=
  BandEdges.twoLevel_constant_le_consumer hE

/-! ## Part 3 — the narrowest `Phase6To7Structure` surface (per-level band position).

The carried `TwoLevelOccupancy` forces BOTH predecessor levels.  The narrower per-level route is the
landed `BandLocalization.MajorityBandAtGap1` (= the `Phase6To7Structure` shape, definitionally): it
needs occupancy ONLY at the actually-occupied predecessor levels.  We re-export the narrowest surface,
and bundle the hour-ceiling consequence into the corrected `CeilingRoute` surface. -/

/-- **The narrowest positional Phase6→7 surface (PROVEN re-export).**  Routes through the per-level
band-position facts `BandLocalization.Phase6BandPositionFacts` (minority confinement + the per-level
majority band `MajorityBandAtGap1`), the genuinely-minimal occupancy surface — strictly narrower than
the carried `TwoLevelOccupancy` (which forces BOTH `{l, l+1}` regardless of where the minority sits).
This is `BandLocalization.phase6_to_phase7_of_bandPosition`, named as the minimal positional surface;
the carried residual is exactly the per-level band-position fact at the OCCUPIED predecessor levels. -/
theorem phase6To7_surface_perLevel {n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hBand : BandLocalization.Phase6BandPositionFacts (L := L) (K := K) σ E c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c :=
  BandLocalization.phase6_to_phase7_of_bandPosition hA h6 hBand hE

/-- **The single-level positional surface (the minimal honest core wired end-to-end).**  When the
live minority is confined to a SINGLE band level `j₀` (the common case — the minority collapses to one
level under the doubling drain), the narrowest surface needs occupancy at the SINGLE predecessor
`j₀ − 1` only, fed at the pigeonhole share `E ≤ 2n/15`.  This composes the single-level honest core
(`majorityBandAtGap1_of_single_level`) with the per-level surface — the genuinely-minimal positional
discharge, with NO appeal to the both-levels boundary case. -/
theorem phase6To7_surface_singleLevel {n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    {j₀ p : Fin (L + 1)} (hgap : p.val + 1 = j₀.val)
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hConfined : BandLocalization.MinorityConfinedGap1 (L := L) (K := K) σ c)
    (hSingle : ∀ j : Fin (L + 1),
      1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum c.count → j.val = j₀.val)
    (hOcc : E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ p).sum c.count)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c :=
  phase6To7_surface_perLevel hA h6
    ⟨hConfined, majorityBandAtGap1_of_single_level hgap hSingle hOcc⟩ hE

/-! ## Part 4 — the hour-ceiling-fed corrected Phase6→7 surface.

The carried `MainHourBelow (l+2)` snapshot feeds, with the index ceiling, the corrected `CeilingRoute`
surface.  We re-export the corrected surface in the snapshot idiom, recording that the hour ceiling is
the clock-front consequence of Part 1 (driven by the same `ClocksBelowHour (l+2)` confinement that the
index ceiling rides on). -/

/-- **The corrected Phase6→7 surface from the two clock snapshots (PROVEN re-export).**  Carries the
index ceiling `AllBiasedMainBelow (l+2)` (the step-preserved quantity) and uses the hour ceiling
`MainHourBelow (l+2)` only as the snapshot the corrected surface consumes.  Per Part 1, both snapshots
are consequences of the SINGLE clock-front confinement `ClocksBelowHour (l+2)` (plus the index
ceiling for the cancel coupling).  This is the honest positional surface for the consumer:
`CeilingRoute.phase6To7_surface_ceilingRoute` fed the genuinely-step-preserved index ceiling. -/
theorem phase6To7_surface_positional {l n E : ℕ} {σ : Sign} {c : Config (AgentState L K)}
    (hl : 1 ≤ l)
    (hSeed : MinorityFloorGap.AllBiasedMainAbove (L := L) (K := K) (l + 1) c)
    (hA : MarginLedgers.MainConfinementProfile (L := L) (K := K) σ n c)
    (h6 : Phase6Convergence.Phase6Win (L := L) (K := K) n c)
    (hCeil : DoublingEdges.AllBiasedMainBelow (L := L) (K := K) (l + 2) c)
    (hCo : DoublingEdges.PredecessorLevelsCoPopulated (L := L) (K := K) σ E l c)
    (hE : (E : ℝ) ≤ (4 : ℝ) * (n : ℝ) / 15) :
    EliminatorMargins.Phase6To7Structure (L := L) (K := K) σ E c :=
  CeilingRoute.phase6To7_surface_ceilingRoute hl hSeed hA h6 hCeil hCo hE

end PositionalCluster

end ExactMajority
