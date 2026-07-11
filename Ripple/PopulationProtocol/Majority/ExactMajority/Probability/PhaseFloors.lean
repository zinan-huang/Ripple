/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase floors — wiring prior-phase Posts into the per-phase structural count floors

`DrainThreading.lean` (D-7) threaded each of the five drain phases' drop rectangles into a
concrete engine `hdrop`, where each `hdrop` carries ONE structural count floor as a NAMED
hypothesis (e.g. Phase 6's `R ≤ reserveAtHour6 h .sum count`).  Those named floors were left
abstract there — they are the per-phase numeric inputs the engine consumes.

This file (Phase D — composition residual) SUPPLIES each floor FROM ITS PROVENANCE SOURCE'S
POST, and re-delivers the `hdrop` with the floor wired in.  For each phase there are three
honest pieces:

1. **Floor extraction** — pull the count fact out of the provenance theorem's actual landed
   conclusion (where the conclusion's shape differs from the floor hypothesis shape, prove the
   adapter that bridges them).
2. **Seam transport** — the floor is a count over a state-filtered finset; the intervening
   advance-epidemic seam does not touch the attributes the count filters on (role / bias / hour
   are not the advancing attribute).  Recorded per phase against `Transition.lean` (FROZEN).
3. **Wired `hdrop`** — the `DrainThreading` packager with the floor supplied from the chain.

## Provenance landed-status (verified against the actual theorems, NOT comments)

| phase | floor                         | provenance theorem                       | landed? |
|-------|-------------------------------|------------------------------------------|---------|
| 6     | `reserveAtHour6 i ≥ K₀`       | Phase-5 Post `ReserveSampleGood i K₀`    | **YES** |
| 1     | `pullPosSet ≥ P`              | RoleSplit `mainCount ≥ n/3` (Lemma 5.2)  | partial: count-shape adapter |
| 5     | `usefulMains ≥ P`             | Thm 6.2 `biasedMainLtL ≥ 0.92·mainCount` | NO (carried) |
| 7     | `elimGap1 ≥ E`                | Lemma 7.4 `0.8·mainCount` eliminator     | NO (carried) |
| 8     | `elimAbove ≥ E`               | Lemma 7.4–7.6 eliminator majority        | NO (carried) |

Only Phase 6 has a fully landed provenance theorem that EXPORTS the needed count lower bound
(`Phase5Convergence.sampledFloor`, the literal `K₀ ≤ sampledReserveClassU i` conjunct of the
Phase-5 `Post`).  For Phases 1/5/7/8 the provenance is a count LOWER bound (`mainCount ≥ n/3`,
`biasedMainLtL ≥ 0.92·mainCount`, `elim ≥ 0.8·mainCount`) whose conclusion is NOT a landed
theorem in this campaign (Lemma 7.4 / Theorem 6.2 are referenced in the drain docs as the
intended source but the eliminator/useful-Main count lower bound itself is carried, never
proven).  Following the discipline "where a provenance theorem genuinely doesn't exist yet,
document precisely and deliver the adapter from the named missing theorem — do not fake", each
of those four phases gets the adapter from the named missing floor (the floor hypothesis stated
explicitly, with the wired `hdrop` produced from it) PLUS whatever genuine arithmetic bridge IS
available (e.g. the Phase-1 Main decomposition `mainCount = pullPosSet + saturatedPos`, which
reduces the missing link to a bound on the saturated-positive side).

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.DrainThreading
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RoleSplitConcentration

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace PhaseFloors

/-! ## Phase 6 — FULLY WIRED from the Phase-5 Post.

Provenance theorem: the Phase-5 `PhaseConvergenceW` instance
(`Phase5Convergence.phase5Convergence`) has
`Post c = Phase5AllWin n c ∧ ReserveSampleGood i K₀ c`, and
`ReserveSampleGood i K₀ c = ReserveSampled c ∧ sampledFloor i K₀ c`, where
`sampledFloor i K₀ c := K₀ ≤ sampledReserveClassU i c`.

Floor extraction: `Phase6Convergence.reserveAtHour6_sum_eq_classU` rewrites
`reserveAtHour6 i .sum count = countP (role = reserve ∧ hour = i)` and
`sampledReserveClassU i c = countP (sampledReserveClass i) = countP (role = reserve ∧ hour = i)`,
so at `h := i` the two counts are DEFINITIONALLY EQUAL.  Hence the Phase-5 `sampledFloor` is
EXACTLY the Phase-6 reserve floor with `R := K₀`.

Seam transport (Phase 5 → 6 advance epidemic): the count is `countP (role = reserve ∧ hour = i)`.
The advance epidemic changes only `phase` (and runs `phaseInit`, which on a Reserve leaves
`role`/`hour` untouched — `phaseInit_clock_role_eq` is the clock analogue; the Reserve `hour`
record is the sampled value, never re-initialised by a phase advance from 5).  The count is the
phase-advance-invariant Reserve attribute the seam does not touch. -/

/-- **Phase 6 floor extraction (provenance = Phase-5 Post).**  The Phase-5 output's
`sampledFloor i K₀` conjunct (`K₀ ≤ sampledReserveClassU i c`) IS the Phase-6 reserve floor
`K₀ ≤ reserveAtHour6 i .sum count` — the two counts are definitionally equal at `h := i`. -/
theorem phase6_reserve_floor_of_phase5Post {L K : ℕ} (i : Fin (L + 1)) (K₀ : ℕ)
    (c : Config (AgentState L K))
    (hPost : Phase5Convergence.ReserveSampleGood (L := L) (K := K) i K₀ c) :
    K₀ ≤ (Phase6Convergence.reserveAtHour6 (L := L) (K := K) i).sum c.count := by
  have hfloor : K₀ ≤ Phase5Convergence.sampledReserveClassU (L := L) (K := K) i c := hPost.2
  rw [Phase6Convergence.reserveAtHour6_sum_eq_classU (L := L) (K := K) i c]
  -- sampledReserveClassU i c = countP (sampledReserveClass i) = countP (role=reserve ∧ hour=i).
  -- `sampledReserveClass i a := a.role = Role.reserve ∧ a.hour.val = i.val` (definitional).
  exact hfloor

/-- **Phase 6 — the wired per-level `hdrop` (provenance fully discharged).**  At a level `m`
with `highMass l b = m`, with the Phase-5 output `ReserveSampleGood i K₀` (supplying the reserve
floor `R := K₀` at hour `h := i`) and `≥ 1` band-`l` Main, the level-`m` failure mass is
`≤ 1 − ofReal(K₀/(n(n−1)))`.  The reserve floor is taken DIRECTLY from the prior phase's Post —
no carried `R`. -/
theorem phase6_hdrop_wired {L K : ℕ} (σ : Sign) (l n m : ℕ) (hn : 2 ≤ n)
    (hl1 : 1 ≤ l) (hlL : l ≤ L) (b : Config (AgentState L K))
    (hInv : Phase6Convergence.Phase6Win (L := L) (K := K) n b)
    (hbm : Phase6Convergence.highMass (L := L) (K := K) l b = m)
    (i : Fin (L + 1)) (K₀ : ℕ)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (hPost : Phase5Convergence.ReserveSampleGood (L := L) (K := K) i K₀ b)
    (hmain : 1 ≤ (Phase6Convergence.mainAt6 (L := L) (K := K) σ l hl1 hlL).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (fun c => Phase6Convergence.highMass (L := L) (K := K) l c) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  DrainThreading.phase6_hdrop_of_struct σ l n m hn hl1 hlL b hInv hbm i hhgt hhne K₀
    hmain (phase6_reserve_floor_of_phase5Post i K₀ b hPost)

/-! ## Phase 1 — ADAPTER (partial provenance).

Floor: `P ≤ pullPosSet .sum count` (phase-1 Mains with `smallBias.val ≤ 4`), with `≥ 1` extreme
at `+3` (`1 ≤ extremePosSet .sum count`).

Provenance: RoleSplit Lemma 5.2 gives `n/3 ≤ mainCount c` (`mainCount = countP (role = main)`,
ALL Mains regardless of `smallBias`), landed as
`RoleSplitConcentration.mainCount_lower_of_RoleSplitGood`.  But `mainCount ≠ pullPosSet` —
`pullPosSet` excludes Mains with `smallBias.val ∈ {5, 6}` (the saturated `+2/+3` positive side).

GENUINE ADAPTER (delivered): the Main population splits as
`mainCount = pullPosSet .sum count + saturatedPosSet .sum count`
where `saturatedPosSet` = phase-1 Mains with `smallBias.val ≥ 5`.  Hence
`pullPosSet .sum count = mainCount − saturatedPos ≥ n/3 − saturatedPos`.  The MISSING link is
the bound `saturatedPos ≤ n/3 − P` (the saturated-positive side is small — exactly the quantity
Phase-1 averaging drives down; cf. `extremeU` non-increase).  We deliver the wired `hdrop` from
the named missing floor `P ≤ pullPosSet .sum count` directly (the adapter target), and prove the
genuine Main-decomposition that reduces the missing link to the saturated-side bound. -/

/-- A phase-1 Main saturated on the positive side: `role = main ∧ smallBias.val ≥ 5`
(the `+2/+3` saturated pool, the complement of `pullPos` within Mains). -/
def saturatedPos {L K : ℕ} (a : AgentState L K) : Prop :=
  a.role = Role.main ∧ 5 ≤ a.smallBias.val

instance {L K : ℕ} (a : AgentState L K) : Decidable (saturatedPos a) := by
  unfold saturatedPos; infer_instance

/-- The finset of saturated-positive (`smallBias.val ≥ 5`) Main states. -/
def saturatedPosSet (L K : ℕ) : Finset (AgentState L K) :=
  Finset.univ.filter (fun a => saturatedPos a)

/-- **The Main decomposition adapter (Phase 1).**  Over a fixed config, the Main count splits
exactly into the partner pool (`pullPos`, `smallBias ≤ 4`) and the saturated-positive pool
(`smallBias ≥ 5`): `mainCount c = pullPosSet .sum count + saturatedPosSet .sum count`.  This is
the genuine arithmetic bridge from the RoleSplit `mainCount` provenance to the `pullPosSet`
floor; the residual is the saturated-side bound. -/
theorem mainCount_eq_pullPos_add_saturatedPos {L K : ℕ} (c : Config (AgentState L K)) :
    RoleSplitConcentration.mainCount (L := L) (K := K) c
      = (DrainThreading.pullPosSet L K).sum c.count
        + (saturatedPosSet L K).sum c.count := by
  classical
  -- mainCount = countP (role = main) = ∑ over filter(role = main) of count.
  rw [RoleSplitConcentration.mainCount,
    Phase6Convergence.countP_eq_sum_count6 (fun a : AgentState L K => a.role = Role.main) c]
  -- the Main filter = pullPosSet ∪ saturatedPosSet (disjoint partition by smallBias ≤ 4 / ≥ 5).
  have hsplit :
      Finset.univ.filter (fun a : AgentState L K => a.role = Role.main)
        = DrainThreading.pullPosSet L K ∪ saturatedPosSet L K := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      DrainThreading.pullPosSet, DrainThreading.pullPos, saturatedPosSet, saturatedPos]
    constructor
    · intro hm
      by_cases h : a.smallBias.val ≤ 4
      · exact Or.inl ⟨hm, h⟩
      · exact Or.inr ⟨hm, by omega⟩
    · rintro (⟨hm, _⟩ | ⟨hm, _⟩) <;> exact hm
  have hdisj : Disjoint (DrainThreading.pullPosSet L K) (saturatedPosSet L K) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [DrainThreading.pullPosSet, DrainThreading.pullPos, saturatedPosSet, saturatedPos,
      Finset.mem_filter] at ha hb
    omega
  rw [hsplit, Finset.sum_union hdisj]

/-- **Phase 1 — the wired levels-engine `hdrop` from the named (partial-provenance) floor.**
The genuine adapter `mainCount_eq_pullPos_add_saturatedPos` reduces the floor to the
saturated-side bound; here we deliver the `hdrop` from the named floor
`hpull : P ≤ pullPosSet .sum count` (the missing-link target).  When the saturated-side bound is
landed, `hpull` follows from `n/3 ≤ mainCount` via the decomposition. -/
theorem phase1_hdrop_wired {L K : ℕ} (n m : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hInv : Phase1Convergence.Phase1AllMain n b)
    (hbm : Phase1Convergence.extremeU b = m) (P : ℕ)
    (hext : 1 ≤ (DrainThreading.extremePosSet L K).sum b.count)
    (hpull : P ≤ (DrainThreading.pullPosSet L K).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase1Convergence.extremeU) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  DrainThreading.phase1_hdrop_of_struct n m hn b hInv hbm P hext hpull

/-! ## Phase 5 — ADAPTER (provenance theorem NOT landed).

Floor: `P ≤ usefulMains .sum count` (biased Mains, exponent index `< L`), with `≥ 1` unsampled
Reserve (`1 ≤ unsampledReserves .sum count`).

Provenance (Theorem 6.2): `biasedMainLtL ≥ 0.92·mainCount ≥ 0.92·(n/3) = 23n/75`.  Theorem 6.2
is NOT a landed theorem in this campaign — it is referenced in `DrainCalibration`/`ReserveSampling`
doctrine as the intended source of the useful-Main floor, but the count lower bound itself is
carried, never proven.  `usefulMains := filter biasedMainLtL`, so the floor would be
`P ≤ usefulMains .sum count` with `P := ⌈23n/75⌉`.

We deliver the wired `hdrop` from the NAMED missing floor `hmain : P ≤ usefulMains .sum count`
(the Theorem-6.2-output target).  Adapter-pending = the Theorem-6.2 biased-Main concentration. -/

/-- **Phase 5 — the wired levels-engine `hdrop` from the named (missing-provenance) floor.**
Delivered from `hmain : P ≤ usefulMains .sum count` (the Theorem 6.2 biased-Main count lower
bound, NOT yet a landed theorem).  When Theorem 6.2 lands, `hmain` becomes
`P := ⌈23n/75⌉ ≤ usefulMains .sum count`. -/
theorem phase5_hdrop_wired {L K : ℕ} (n m : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hInv : ReserveSampling.Phase5AllWin n b)
    (hbm : ReserveSampling.unsampledReserveU (L := L) (K := K) b = m) (P : ℕ)
    (hres : 1 ≤ (Phase5Convergence.unsampledReserves (L := L) (K := K)).sum b.count)
    (hmain : P ≤ (Phase5Convergence.usefulMains (L := L) (K := K)).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow
          (ReserveSampling.unsampledReserveU (L := L) (K := K)) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((P : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  DrainThreading.phase5_hdrop_of_struct n m hn b hInv hbm P hres hmain

/-! ## Phase 7 — ADAPTER (provenance theorem NOT landed).

Floor: `E ≤ elimGap1 σ i .sum count` (gap-1 eliminators at level `i`), with `≥ 1` minority at
`j = i + 1` (`1 ≤ minorityAt7 σ j .sum count`).

Provenance (Lemma 7.4): the σ-eliminator majority floor `0.8·mainCount`.  Lemma 7.4 is NOT
landed as a count lower bound (Invariants.lean's `lemma_7_5_phase_seven_minority` /
`lemma_7_6_phase_eight_eliminates` are whp UPPER bounds on minority SURVIVAL, not eliminator
lower bounds; the `0.8|M|` eliminator floor is carried in the Phase-7 doc, never proven).

We deliver the wired `hdrop` from the NAMED missing floor `helim : E ≤ elimGap1 σ i .sum count`
(the Lemma-7.4-output target). -/

/-- **Phase 7 — the wired levels-engine `hdrop` from the named (missing-provenance) floor.**
Delivered from `helim : E ≤ elimGap1 σ i .sum count` (the Lemma 7.4 `0.8·mainCount` eliminator
floor, NOT yet landed). -/
theorem phase7_hdrop_wired {L K : ℕ} (σ : Sign) (n m : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hb7 : Phase7Convergence.Phase7AllMain n b)
    (hbm : Phase7Convergence.classMassN σ b = m)
    (i j : Fin (L + 1)) (hg1 : i.val + 1 = j.val) (E : ℕ)
    (hmin : 1 ≤ (Phase7Convergence.minorityAt7 (L := L) (K := K) σ j).sum b.count)
    (helim : E ≤ (Phase7Convergence.elimGap1 (L := L) (K := K) σ i).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.classMassN σ) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  DrainThreading.phase7_hdrop_of_struct σ n m hn b hb7 hbm i j hg1 E hmin helim

/-! ## Phase 8 — ADAPTER (provenance theorem NOT landed).

Floor: `E ≤ elimAbove σ i .sum count` (eliminators above level `i`), with `≥ 1` minority at `i`
(`1 ≤ minorityAt σ i .sum count`).

Provenance (Lemmas 7.4–7.6): `0.8|M|` majority minus `0.2|M|` minority eliminator margin.  As
with Phase 7, the eliminator count lower bound is NOT a landed theorem (the landed Lemma 7.5/7.6
are whp minority-survival upper bounds).

We deliver the wired `hdrop` from the NAMED missing floors `helim : E ≤ elimAbove σ i .sum count`
and `hmin : 1 ≤ minorityAt σ i .sum count` (the Lemmas-7.4–7.6-output targets). -/

/-- **Phase 8 — the wired levels-engine `hdrop` from the named (missing-provenance) floor.**
Delivered from `helim : E ≤ elimAbove σ i .sum count` + `hmin : 1 ≤ minorityAt σ i .sum count`
(the Lemmas 7.4–7.6 eliminator-margin floor, NOT yet landed). -/
theorem phase8_hdrop_wired {L K : ℕ} (σ : Sign) (n m : ℕ) (hn : 2 ≤ n)
    (b : Config (AgentState L K)) (hb8 : Phase8Convergence.Phase8AllMain n b)
    (hbm : Phase7Convergence.minorityU σ b = m)
    (i : Fin (L + 1)) (E : ℕ)
    (hmin : 1 ≤ (Phase8Convergence.minorityAt (L := L) (K := K) σ i).sum b.count)
    (helim : E ≤ (Phase8Convergence.elimAbove (L := L) (K := K) σ i).sum b.count) :
    (NonuniformMajority L K).transitionKernel b
        (OneSidedCancel.potBelow (Phase7Convergence.minorityU σ) m)ᶜ
      ≤ 1 - ENNReal.ofReal ((E : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
  DrainThreading.phase8_hdrop_of_struct σ n m hn b hb8 hbm i E hmin helim

end PhaseFloors

end ExactMajority
