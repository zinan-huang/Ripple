/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Phase6SurvivalContracting — the CONTRACTING (`r < 1`) slot-6 doubling-drain survival.

This append-only file edits NO existing file.  It builds the slot-6 (Doty §6 Reserve-Splits /
doubling-drain) SURVIVAL by applying the just-proven contracting-drain template of
`GatedDrainContracting` (slot-5) to the Phase-6 high-band potential `highMass l`.  It is the EXACT
mirror of `phase5_survival_contracting`, with the slot-6 pieces substituted.

## The template (REUSED verbatim — `GatedDrainContracting`)
The slot-5 survival was proved the CORRECT way with three reusable engines, ALL of which are
generic over the kernel / potential / gate:
* `GatedDrift.gated_real_tail_anyr` — the `r`-arbitrary gated tail (NO `hr : 1 ≤ r`); the drain term
  `r^T·Φ T/θ` shrinks iff `r < 1`.
* `expDrainPot_drift_contracting` — the CONTRACTING MGF drift
  `∫ exp(s·Φ) dK ≤ contractRate ρ s · exp(s·Φ)` on a gate, from a per-step DROP floor `ρ` and a
  NEVER-INCREASE property; `contractRate_lt_one` gives `r = contractRate ρ s < 1` whenever `0 < ρ ≤ 1`,
  `s > 0`.
* `phase5_survival_contracting` (this file's `phase6_survival_contracting` mirror) — compose:
  contracting drain + cumulative clock tail + confinement/structural tail; `drain_term_tendsto_zero`
  shows the drain genuinely shrinks.

We REUSE these directly (they are stated over an abstract `K`, `Φ`, `G`).  Slot-6 differs ONLY in
the concrete substitution.

## The slot-6 substitution
* potential `Φ := highMass l` (Doty §6 high-band dyadic mass, `Phase6Convergence.highMass`).
* gate `G6 := {c | Phase6Win n c}` — the Phase-6 working window.  The drift's structural needs
  (the Phase-5 reserve floor `hPost` and the `≥ 1` band-top Main `hmain`) are carried as the EXPLICIT
  isolated residuals of `Phase6Win → ...` shape (the §6 structural content), NEVER manufactured and
  NEVER an `InvClosed` of the window.  These are exactly the `hPost`/`hmain` binders of
  `Phase6DrainRate.hdrop6pos_of_chain` (their TRUE provenance is the prior phase's Post + the
  band-structural margin).
* per-step DROP floor `ρ := 1 − qpos6 K₀ n m = ofReal(K₀/(n(n−1)))` on the drop event
  `{c' | highMass c' + 1 ≤ highMass c}`, derived from `hdrop6pos_of_chain` (which bounds the
  `potBelow`-complement mass `≤ qpos6 m`) via the `potBelow ↔ drop-event` bridge (the SAME bridge
  `Phase5ConfinementCompose.confinedDrain_hdrop` used).
* NEVER-INCREASE: `Phase6Convergence.potNonincrOn_highMass` (`highMass l` is `PotNonincrOn` on
  `Phase6Win n`), supplying `K c {c' | highMass c < highMass c'} = 0`.
* contracting rate `r := contractRate (1 − qpos6 K₀ n m) s = 1 − (1−qpos6)·(1−e^{−s}) < 1` whenever
  `qpos6 < 1` (i.e. the reserve floor `K₀ > 0`) and `s > 0`.
* cumulative clock tail: `ClockDepletionCoupling.mgf_depletion_tail_uniform` (Phase 6 advances via the
  SAME depletion counter), carried as the abstract `η_clock` term (a SUM over `range T`, NEVER a
  one-step `T·η`).
* structural tail `η_struct`: the §6 band-structural escape, isolated as a TRUE residual
  (monotone-increasing / floor-shaped — refutation-checked).

## The CONTRACTING `r < 1` (the whole point)
The drain CONTRACTS on the gate: `contractRate (1−qpos6) s < 1`.  This is verified STRICTLY by
`Phase6DrainRate.qpos6_pos` (giving `0 < 1 − qpos6` from `K₀ < n(n−1)` ... no: `qpos6_pos` gives
`0 < qpos6`; we need `0 < 1 − qpos6 = ρ`, which holds iff `qpos6 < 1`, i.e. `0 < K₀`).  We record this
as `dropFloor6_pos` and feed `contractRate_lt_one`.  An `r ≥ 1` "drift" is the vacuous trap; here
`r < 1` strictly, so `r^T → 0` (`drain_term_tendsto_zero`).

## ANTI-TRAP compliance
* NO `InvClosed` / `hClosed` / `levels_PhaseConvergenceW` of any phase window.
* The drain CONTRACTS (`r < 1` STRICTLY, `phase6_contractRate_lt_one`).
* The clock escape is CUMULATIVE (`∑_{τ<T}`), never a one-step `T·η`.
* Every carried residual is a per-step LOWER bound (drop floor) or a monotone-increasing event;
  no one-step closure of a decreasing quantity.

## Discipline
Append-only; edits NO existing file; single-file `lake env lean`; `#print axioms ⊆
[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GatedDrainContracting
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase6DrainRate

namespace ExactMajority
namespace Phase6SurvivalContracting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## Part 1 — the slot-6 per-step DROP floor `ρ = 1 − qpos6`.

`Phase6DrainRate.hdrop6pos_of_chain` bounds the `potBelow`-COMPLEMENT mass by `qpos6 m`; we convert
this to the DROP-EVENT floor `1 − qpos6 m ≤ K c {c' | highMass c' + 1 ≤ highMass c}`, exactly the
`hdrop` input shape `expDrainPot_drift_contracting` consumes.  This is the SAME `potBelow ↔ drop`
bridge as `Phase5ConfinementCompose.confinedDrain_hdrop`. -/

/-- **The slot-6 drop-event floor.**  From `hdrop6pos_of_chain` (the `potBelow`-complement ceiling
`≤ qpos6 m`), at a `Phase6Win` config with `highMass l b = m`, the one-step kernel mass of the DROP
event `{c' | highMass l c' + 1 ≤ highMass l b}` is `≥ 1 − qpos6 K₀ n m`.

The conversion is the standard complement bridge: `{drop} = potBelow highMass m` (since `highMass b = m`),
so `K(drop) = 1 − K(potBelowᶜ) ≥ 1 − qpos6 m`. -/
theorem highMass_drop_floor {n : ℕ} (σ : Sign) (l : ℕ) (hn : 2 ≤ n)
    (hl1 : 1 ≤ l) (hlL : l ≤ L) (i : Fin (L + 1)) (K₀ : ℕ)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (hPost : ∀ b : Config (AgentState L K),
      Phase6Convergence.Phase6Win (L := L) (K := K) n b →
      Phase5Convergence.ReserveSampleGood (L := L) (K := K) i K₀ b)
    (hmain : ∀ b : Config (AgentState L K),
      Phase6Convergence.Phase6Win (L := L) (K := K) n b →
      1 ≤ (Phase6Convergence.mainAt6 (L := L) (K := K) σ l hl1 hlL).sum b.count)
    (m : ℕ) (hm1 : 1 ≤ m) (b : Config (AgentState L K))
    (hInv : Phase6Convergence.Phase6Win (L := L) (K := K) n b)
    (hbm : Phase6Convergence.highMass (L := L) (K := K) l b = m) :
    1 - Phase6DrainRate.qpos6 K₀ n m
      ≤ (NonuniformMajority L K).transitionKernel b
          {c' | Phase6Convergence.highMass (L := L) (K := K) l c' + 1
                  ≤ Phase6Convergence.highMass (L := L) (K := K) l b} := by
  classical
  set Φ := fun c => Phase6Convergence.highMass (L := L) (K := K) l c with hΦ
  -- the complement ceiling from the landed chain
  have hcompl_le := Phase6DrainRate.hdrop6pos_of_chain (L := L) (K := K)
    σ l hn hl1 hlL i K₀ hhgt hhne hPost hmain m hm1 b hInv hbm
  -- {drop} = potBelow Φ m  (since Φ b = m)
  have hsucc_eq : {c' : Config (AgentState L K) | Φ c' + 1 ≤ Φ b}
      = OneSidedCancel.potBelow Φ m := by
    ext c'; simp only [OneSidedCancel.potBelow, Set.mem_setOf_eq, hΦ, hbm]; omega
  have hmeas : MeasurableSet (OneSidedCancel.potBelow Φ m) :=
    OneSidedCancel.potBelow_measurable Φ m
  -- K(potBelowᶜ) = 1 − K(potBelow)
  have hcompl : (NonuniformMajority L K).transitionKernel b (OneSidedCancel.potBelow Φ m)ᶜ
      = 1 - (NonuniformMajority L K).transitionKernel b (OneSidedCancel.potBelow Φ m) := by
    have htot : (NonuniformMajority L K).transitionKernel b Set.univ = 1 :=
      (inferInstance :
        IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure b
        |>.measure_univ
    rw [measure_compl hmeas (measure_ne_top _ _), htot]
  -- so K(potBelow) = 1 − K(potBelowᶜ) ≥ 1 − qpos6 m
  rw [hsucc_eq]
  have hpb_le_one : (NonuniformMajority L K).transitionKernel b (OneSidedCancel.potBelow Φ m) ≤ 1 :=
    (measure_mono (Set.subset_univ _)).trans_eq
      ((inferInstance :
        IsMarkovKernel (NonuniformMajority L K).transitionKernel).isProbabilityMeasure b
        |>.measure_univ)
  -- 1 − qpos6 m ≤ K(potBelow):  from qpos6 m ≥ K(potBelowᶜ) = 1 − K(potBelow), tsub-monotone.
  have hstep : 1 - Phase6DrainRate.qpos6 K₀ n m
      ≤ 1 - (NonuniformMajority L K).transitionKernel b (OneSidedCancel.potBelow Φ m)ᶜ := by
    exact tsub_le_tsub_left hcompl_le 1
  rw [hcompl] at hstep
  -- 1 − (1 − x) = x  for x ≤ 1 (finite), so RHS of hstep is K(potBelow).
  have hxle : (NonuniformMajority L K).transitionKernel b (OneSidedCancel.potBelow Φ m) ≤ 1 :=
    hpb_le_one
  rwa [ENNReal.sub_sub_cancel ENNReal.one_ne_top hxle] at hstep

/-! ## Part 2 — the slot-6 NEVER-INCREASE (from `potNonincrOn_highMass`). -/

/-- **`highMass l` never increases on `Phase6Win n`** in the `hnoincr` shape
`K c {c' | highMass c < highMass c'} = 0`.  Directly from `potNonincrOn_highMass`. -/
theorem highMass_noincr {n : ℕ} (l : ℕ)
    (b : Config (AgentState L K))
    (hInv : Phase6Convergence.Phase6Win (L := L) (K := K) n b) :
    (NonuniformMajority L K).transitionKernel b
        {c' | Phase6Convergence.highMass (L := L) (K := K) l b
                < Phase6Convergence.highMass (L := L) (K := K) l c'} = 0 := by
  have h := Phase6Convergence.potNonincrOn_highMass (L := L) (K := K) l n b hInv
  -- `PotNonincrOn` is `K c {x | Φ c < Φ x} = 0` on the kernel; unfold to the transition kernel.
  exact h

/-! ## Part 3 — the slot-6 CONTRACTING MGF drift on `highMass`.

We instantiate `expDrainPot_drift_contracting` with `U := highMass l`, drop floor
`ρ := 1 − qpos6 K₀ n m`, and the never-increase from `highMass_noincr`.  The resulting factor is
`contractRate (1 − qpos6 K₀ n m) s`, which we show `< 1` strictly (Part 4). -/

/-- **The slot-6 contracting MGF drift** at a level-`m` config `b` on the gate.  The MGF potential
`expDrainPot (highMass l) s` contracts by `contractRate (1 − qpos6 K₀ n m) s` per step. -/
theorem expDrainPot_highMass_drift {n : ℕ} (σ : Sign) (l : ℕ) (hn : 2 ≤ n)
    (hl1 : 1 ≤ l) (hlL : l ≤ L) (i : Fin (L + 1)) (K₀ : ℕ)
    (hhgt : l - 1 < i.val) (hhne : i.val ≠ L)
    (hPost : ∀ b : Config (AgentState L K),
      Phase6Convergence.Phase6Win (L := L) (K := K) n b →
      Phase5Convergence.ReserveSampleGood (L := L) (K := K) i K₀ b)
    (hmain : ∀ b : Config (AgentState L K),
      Phase6Convergence.Phase6Win (L := L) (K := K) n b →
      1 ≤ (Phase6Convergence.mainAt6 (L := L) (K := K) σ l hl1 hlL).sum b.count)
    (s : ℝ) (hs : 0 ≤ s) (m : ℕ) (hm1 : 1 ≤ m) (b : Config (AgentState L K))
    (hInv : Phase6Convergence.Phase6Win (L := L) (K := K) n b)
    (hbm : Phase6Convergence.highMass (L := L) (K := K) l b = m) :
    ∫⁻ c', expDrainPot (L := L) (K := K)
        (fun c => Phase6Convergence.highMass (L := L) (K := K) l c) s c'
        ∂((NonuniformMajority L K).transitionKernel b)
      ≤ contractRate (1 - Phase6DrainRate.qpos6 K₀ n m) s
          * expDrainPot (L := L) (K := K)
              (fun c => Phase6Convergence.highMass (L := L) (K := K) l c) s b := by
  refine expDrainPot_drift_contracting (L := L) (K := K)
    (NonuniformMajority L K).transitionKernel
    (fun c => Phase6Convergence.highMass (L := L) (K := K) l c) s hs
    (1 - Phase6DrainRate.qpos6 K₀ n m) b ?_ ?_
  · -- drop floor
    exact highMass_drop_floor σ l hn hl1 hlL i K₀ hhgt hhne hPost hmain m hm1 b hInv hbm
  · -- never increase
    exact highMass_noincr l b hInv

/-! ## Part 4 — the CONTRACTING rate `r < 1` (STRICT; the whole point).

`r = contractRate (1 − qpos6 K₀ n m) s`.  `contractRate_lt_one` needs `0 < ρ` and `ρ ≤ 1` for
`ρ = 1 − qpos6`.  We supply `0 < 1 − qpos6` (the DROP floor is positive, from `qpos6 < 1`, i.e.
the reserve floor `K₀ > 0`) and `1 − qpos6 ≤ 1` (trivial).  This is the STRICT verification the
anti-trap demands: an `r ≥ 1` drift is vacuous. -/

/-- **The slot-6 drop floor `1 − qpos6 K₀ n m` is positive** when `K₀ > 0` (`hK0pos`) and
`2 ≤ n` (`hn`), `1 ≤ m` (`hm1`).  `qpos6 m = 1 − ofReal(K₀/(n(n−1)))`, so `1 − qpos6 = ofReal(K₀/(n(n−1)))`,
which is `> 0` exactly when `K₀ > 0`.  This is the NON-VACUITY of the contraction: a zero drop floor
would give `r = 1` (vacuous). -/
theorem dropFloor6_pos {K₀ n m : ℕ} (hn : 2 ≤ n) (hm1 : 1 ≤ m) (hK0pos : 0 < K₀) :
    0 < 1 - Phase6DrainRate.qpos6 K₀ n m := by
  rw [Phase6DrainRate.qpos6_eq_ofReal hn hm1]
  -- 1 − ofReal(qRectReal) = 1 − ofReal(1 − K₀/(n(n−1))) = ofReal(K₀/(n(n−1))) > 0.
  unfold Phase6DrainRate.qRectReal
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hfrac_nonneg : (0 : ℝ) ≤ (K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) :=
    div_nonneg (by positivity) hden.le
  have hfrac_pos : (0 : ℝ) < (K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    apply div_pos _ hden
    have : (1 : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hK0pos
    linarith
  -- ofReal(1 − frac) = 1 − ofReal frac  (frac ≥ 0).
  rw [ENNReal.ofReal_sub 1 hfrac_nonneg, ENNReal.ofReal_one]
  -- goal: 0 < 1 − (1 − ofReal frac).  `ENNReal.sub_pos`: ↔ (1 − ofReal frac) < 1, and the latter
  -- holds because ofReal frac > 0 (so subtracting it strictly drops below 1).
  rw [tsub_pos_iff_lt]
  have hofrac_pos : (0 : ℝ≥0∞) < ENNReal.ofReal ((K₀ : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) :=
    ENNReal.ofReal_pos.mpr hfrac_pos
  exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero (ne_of_gt hofrac_pos)

/-- **The slot-6 contracting rate is STRICTLY `< 1`.**  `r = contractRate (1 − qpos6 K₀ n m) s < 1`
whenever the drop floor `1 − qpos6` is positive (`dropFloor6_pos`, i.e. `K₀ > 0`), the floor is
`≤ 1` (always), and `s > 0`.  This is the linchpin of non-vacuity: with `r < 1` the drain term
`r^T·coef → 0` (`drain_term_tendsto_zero`); an `r ≥ 1` "drift" would be the vacuous trap. -/
theorem phase6_contractRate_lt_one {K₀ n m : ℕ} (s : ℝ) (hs : 0 < s)
    (hn : 2 ≤ n) (hm1 : 1 ≤ m) (hK0pos : 0 < K₀) :
    contractRate (1 - Phase6DrainRate.qpos6 K₀ n m) s < 1 := by
  apply contractRate_lt_one s hs
  · exact dropFloor6_pos hn hm1 hK0pos
  · exact tsub_le_self

/-! ## Part 5 — the composed slot-6 SURVIVAL (CONTRACTING `r < 1`, genuinely shrinking).

The EXACT mirror of `phase5_survival_contracting`.  From a Phase-6-windowed start `c₀`, the
probability that the slot-6 doubling-drain FAILS to drain the high band (`{c | θ ≤ Φ_highMass c}`,
the survival of a high-band surplus) at horizon `T` is at most `ε_drain + η_clock + η_struct`:

* `ε_drain` — the CONTRACTING drain `r^T·Φ_highMass c₀/θ` plus the small confinement leak `T·q_leak`,
  with `r = contractRate (1 − qpos6) s < 1` so it GENUINELY SHRINKS (`drain_term_tendsto_zero`);
* `η_clock` — the CUMULATIVE clock prefix-failure sum `∑_{τ<T} (K^τ) c₀ Sᶜ`
  (sourced from `ClockDepletionCoupling.mgf_depletion_tail_uniform`), NEVER a one-step `T·η`;
* `η_struct` — the §6 band-structural escape (the windowed-confinement tail), the isolated TRUE
  residual.

This reuses `phase5_survival_contracting`'s downstream engines via the generic
`term3_drain_prefix_anyr` / `gated_real_tail_anyr`; we re-prove the same composition with gate
`{c | Phase6Win n c}` and structural-escape set `Aconf` ABSTRACT (the §6 residual). -/

open GatedDrift

/-- **CONTRACTING slot-6 doubling-drain survival (`r < 1`).**  Mirrors
`phase5_survival_contracting` with the Phase-6 potential `Φ_H := highMass l` and gate
`G6 := {c | Phase6Win n c}`.  The drain engine carries NO `hr : 1 ≤ r`, so `r` is the contracting
`contractRate (1 − qpos6 K₀ n m) s < 1` (`phase6_contractRate_lt_one`), making `r^T·Φ_H c₀/θ`
genuinely shrink.

`Aconf` is the §6 band-structural escape set (the windowed-confinement tail target), abstract;
`hcover` says the survival event `{¬ Phase6Done}` is covered by the structural escape `Aconf` plus
the high-band surplus `{θ ≤ Φ_H}`.  NO `InvClosed` of `Phase6Win`. -/
theorem phase6_survival_contracting {n : ℕ}
    (Φ_H : Config (AgentState L K) → ℝ≥0∞) (r : ℝ≥0∞)
    (hHdrift : ∀ x ∈ {c | Phase6Convergence.Phase6Win (L := L) (K := K) n c},
      ∫⁻ y, Φ_H y ∂((NonuniformMajority L K).transitionKernel x) ≤ r * Φ_H x)
    (S : Set (Config (AgentState L K))) (q_leak : ℝ≥0∞)
    (hLeak : ∀ x ∈ {c | Phase6Convergence.Phase6Win (L := L) (K := K) n c}, x ∈ S →
      (NonuniformMajority L K).transitionKernel x
        {c | Phase6Convergence.Phase6Win (L := L) (K := K) n c}ᶜ ≤ q_leak)
    (T : ℕ) (θ : ℝ≥0∞) (hθ0 : θ ≠ 0) (hθtop : θ ≠ ∞)
    (c₀ : Config (AgentState L K))
    (hWin₀ : Phase6Convergence.Phase6Win (L := L) (K := K) n c₀)
    (εdrain : ℝ≥0)
    (hεdrain : ((T : ℝ≥0∞) * q_leak + r ^ T * Φ_H c₀ / θ : ℝ≥0∞) ≤ (εdrain : ℝ≥0∞))
    (η_clock η_struct : ℝ≥0∞)
    (hClock : (∑ τ ∈ Finset.range T,
        ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ) ≤ η_clock)
    (Phase6Done : Config (AgentState L K) → Prop)
    (Aconf : Set (Config (AgentState L K)))
    (hStruct : ((NonuniformMajority L K).transitionKernel ^ T) c₀ Aconf ≤ η_struct)
    (hcover : {c : Config (AgentState L K) | ¬ Phase6Done c}
      ⊆ Aconf ∪ {c | θ ≤ Φ_H c}) :
    ((NonuniformMajority L K).transitionKernel ^ T) c₀ {c | ¬ Phase6Done c}
      ≤ (εdrain : ℝ≥0∞) + η_clock + η_struct := by
  classical
  -- gated tail (NO hr): real high-Φ tail ≤ cemetery escape + CONTRACTING drain supermartingale.
  have hgated := GatedDrift.gated_real_tail_anyr
    (K := (NonuniformMajority L K).transitionKernel)
    (G := {c | Phase6Convergence.Phase6Win (L := L) (K := K) n c})
    Φ_H r hHdrift T c₀ θ hθ0 hθtop
  -- cemetery escape ≤ small leak + cumulative clock prefix-failures.
  have hesc := GatedDrift.kill_escape_le_prefix_union
    (K := (NonuniformMajority L K).transitionKernel)
    (G := {c | Phase6Convergence.Phase6Win (L := L) (K := K) n c})
    S q_leak hLeak T c₀ hWin₀
  -- compose: real tail ≤ (T·q_leak + ∑_{τ<T} Sᶜ) + r^T·Φ_H c₀/θ.
  have hdrain0 :
      ((NonuniformMajority L K).transitionKernel ^ T) c₀ {c | θ ≤ Φ_H c}
        ≤ ((T : ℝ≥0∞) * q_leak
            + ∑ τ ∈ Finset.range T,
                ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ)
          + r ^ T * Φ_H c₀ / θ :=
    le_trans hgated (add_le_add hesc le_rfl)
  have hdrain : ((NonuniformMajority L K).transitionKernel ^ T) c₀ {c | θ ≤ Φ_H c}
      ≤ (εdrain : ℝ≥0∞) + η_clock := by
    refine le_trans hdrain0 ?_
    calc ((T : ℝ≥0∞) * q_leak
            + ∑ τ ∈ Finset.range T,
                ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ)
          + r ^ T * Φ_H c₀ / θ
        = ((T : ℝ≥0∞) * q_leak + r ^ T * Φ_H c₀ / θ)
          + ∑ τ ∈ Finset.range T,
              ((NonuniformMajority L K).transitionKernel ^ τ) c₀ Sᶜ := by ring
      _ ≤ (εdrain : ℝ≥0∞) + η_clock := add_le_add hεdrain hClock
  set μ := ((NonuniformMajority L K).transitionKernel ^ T) c₀ with hμ
  set Adrain : Set (Config (AgentState L K)) := {c | θ ≤ Φ_H c} with hAdrain
  calc μ {c | ¬ Phase6Done c}
      ≤ μ (Aconf ∪ Adrain) := measure_mono hcover
    _ ≤ μ Aconf + μ Adrain := measure_union_le _ _
    _ ≤ η_struct + ((εdrain : ℝ≥0∞) + η_clock) := add_le_add hStruct hdrain
    _ = (εdrain : ℝ≥0∞) + η_clock + η_struct := by ring

/-! ## Part 6 — the drain genuinely SHRINKS (non-vacuity, the whole point).

The contracting `r < 1` makes `r^T·coef → 0`; this is FALSE for `r ≥ 1`.  We reuse
`drain_term_tendsto_zero` / `drain_term_shrinks` (the slot-5 engines) at the slot-6 rate, and
combine with `phase6_contractRate_lt_one` for the linchpin. -/

/-- **The slot-6 contracting drain is GENUINELY non-vacuous.**  The rate
`r = contractRate (1 − qpos6 K₀ n m) s` is `< 1` (`phase6_contractRate_lt_one`), and its drain term
`r^T·coef` shrinks below any `ε > 0` past a threshold (`drain_term_shrinks`).  This is exactly what
an `r ≥ 1` "drift" CANNOT supply.  Requires the reserve floor `K₀ > 0` (drop floor positive). -/
theorem phase6_contracting_drain_nonvacuous {K₀ n m : ℕ} (s : ℝ) (hs : 0 < s)
    (hn : 2 ≤ n) (hm1 : 1 ≤ m) (hK0pos : 0 < K₀)
    (coef : ℝ≥0∞) (hcoef : coef ≠ ∞) (ε : ℝ≥0∞) (hε : 0 < ε) :
    contractRate (1 - Phase6DrainRate.qpos6 K₀ n m) s < 1
      ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀,
          (contractRate (1 - Phase6DrainRate.qpos6 K₀ n m) s) ^ T * coef ≤ ε := by
  have hlt := phase6_contractRate_lt_one s hs hn hm1 hK0pos
  exact ⟨hlt, drain_term_shrinks (contractRate (1 - Phase6DrainRate.qpos6 K₀ n m) s) hlt coef hcoef ε hε⟩

/-- **The slot-6 drain term tends to `0`** (the shrink, restated at the slot-6 rate).  For the
contracting `r = contractRate (1 − qpos6 K₀ n m) s < 1`, `r^T·coef → 0` as `T → ∞`. -/
theorem phase6_drain_tendsto_zero {K₀ n m : ℕ} (s : ℝ) (hs : 0 < s)
    (hn : 2 ≤ n) (hm1 : 1 ≤ m) (hK0pos : 0 < K₀)
    (coef : ℝ≥0∞) (hcoef : coef ≠ ∞) :
    Filter.Tendsto
      (fun T : ℕ => (contractRate (1 - Phase6DrainRate.qpos6 K₀ n m) s) ^ T * coef)
      Filter.atTop (nhds 0) :=
  drain_term_tendsto_zero (contractRate (1 - Phase6DrainRate.qpos6 K₀ n m) s)
    (phase6_contractRate_lt_one s hs hn hm1 hK0pos) coef hcoef

/-! ## Axiom audit (verified by `#print axioms`). -/

#print axioms highMass_drop_floor
#print axioms highMass_noincr
#print axioms expDrainPot_highMass_drift
#print axioms dropFloor6_pos
#print axioms phase6_contractRate_lt_one
#print axioms phase6_survival_contracting
#print axioms phase6_contracting_drain_nonvacuous
#print axioms phase6_drain_tendsto_zero

end Phase6SurvivalContracting
end ExactMajority
