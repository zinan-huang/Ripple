/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ClockStoppedTransfer` — the stopped-kernel → markedK gate-exit transfer (Layer-D crux).

The Layer-B tails (`GhostSmallConc.ghostSmall_level_whp`, `ClockLayerB.epidemic_amplification_window_
budget`) live on STOPPED kernels (`piecewise(activeGate) markedK id`).  `ClockLayerD.windowBadMass_le`
needs the per-active-start bound on the REAL `markedK`.  This file bridges them by routing through the
immediate-kill cemetery `GatedDrift.killK_now`:

  `(markedK^t) x {bad} ≤ (stoppedK markedK G ^t) x {bad} + (killK_now markedK G ^t) (some x) {none}`,

the general `real_le_stopped_add_exit`.  The alive part of the killed walk is dominated by the
ordinary stopped walk (`killed_now_alive_le_stopped`), and the cemetery `{none}` mass IS the
first-exit probability from the gate `G` — bounded by `exit_le_prefix_union` (= `GatedDrift.
kill_now_escape_le_prefix_union`).  This works for BOTH the monotone ghost gate AND the non-monotone
amplification gate (`cleanCount` need not be monotone — no monotonicity is used).

Concrete adapters: `ghost_marked_tail_from_stopped_and_exit` (KghostStar) and
`amp_marked_tail_from_stopped_and_exit` (KampStar), each `markedK-tail ≤ εStop + εExit`, with the
prefix-union exit forms routing `εExit` to Layer-C gate-failure events.

Source: ChatGPT family2 draft @d1f2805 (task 7ef73b4b), audited + verified here (all cited GatedDrift
lemmas confirmed present + used across ClockKilledMinute/ClockWeakAssembly/Gap2Reachability).
NEW file; no existing file edited; no sorry/admit/axiom/native_decide.
Reference: `DOCTRINE_THM69_CA.md` Layer D; Doty et al. (arXiv:2106.10201v2) §6.
-/

import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ClockLayerBAmplification
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.GatedKillNow

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators
open Classical

namespace ClockStoppedTransfer

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α] [Inhabited α]

local instance instOptionMS : MeasurableSpace (Option α) := ⊤
local instance instOptionDMS : DiscreteMeasurableSpace (Option α) :=
  ⟨fun _ => trivial⟩

/-- The ordinary stopped kernel: run `K` on `G`, self-loop off `G`. -/
noncomputable def stoppedK (K : Kernel α α) (G : Set α) : Kernel α α :=
  Kernel.piecewise (DiscreteMeasurableSpace.forall_measurableSet G) K Kernel.id

instance (K : Kernel α α) [IsMarkovKernel K] (G : Set α) :
    IsMarkovKernel (stoppedK K G) := by
  unfold stoppedK
  infer_instance

/--
Alive part of the immediate-killed walk is dominated by the ordinary stopped walk.

Intuition: while the killed walk is alive, it has stayed in `G`, so it follows the same transitions
as the piecewise stopped kernel.  If it exits `G`, it is sent to `none` and contributes zero to the
alive target. -/
theorem killed_now_alive_le_stopped
    (K : Kernel α α) [IsMarkovKernel K] (G A : Set α)
    (t : ℕ) (x : α) :
    (GatedDrift.killK_now K G ^ t) (some x)
      {o | ∃ y ∈ A, o = some y}
      ≤ (stoppedK K G ^ t) x A := by
  classical
  induction t generalizing x with
  | zero =>
      rw [pow_zero, pow_zero]
      change Kernel.id (some x) {o : Option α | ∃ y ∈ A, o = some y}
        ≤ Kernel.id x A
      rw [Kernel.id_apply, Kernel.id_apply,
        Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _),
        Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
      by_cases hxA : x ∈ A
      · have hsome : (some x : Option α) ∈ {o | ∃ y ∈ A, o = some y} :=
          ⟨x, hxA, rfl⟩
        simp [Set.indicator_of_mem hsome, Set.indicator_of_mem hxA]
      · have hsome : (some x : Option α) ∉ {o | ∃ y ∈ A, o = some y} := by
          rintro ⟨y, hyA, hy⟩
          exact hxA ((Option.some.inj hy).symm ▸ hyA)
        simp [Set.indicator_of_notMem hsome, Set.indicator_of_notMem hxA]
  | succ t ih =>
      have hAlive : MeasurableSet {o : Option α | ∃ y ∈ A, o = some y} :=
        DiscreteMeasurableSpace.forall_measurableSet _
      have hA : MeasurableSet A := DiscreteMeasurableSpace.forall_measurableSet _
      rw [show t + 1 = 1 + t from by omega,
        Kernel.pow_add_apply_eq_lintegral (GatedDrift.killK_now K G) 1 t (some x) hAlive,
        Kernel.pow_add_apply_eq_lintegral (stoppedK K G) 1 t x hA,
        pow_one, pow_one]
      by_cases hxG : x ∈ G
      · rw [GatedDrift.killK_now_some_gated (K := K) (G := G) x hxG]
        unfold stoppedK
        rw [Kernel.piecewise_apply, if_pos hxG]
        rw [MeasureTheory.lintegral_map (Measurable.of_discrete)
          (GatedDrift.gateMap_measurable G)]
        refine lintegral_mono (fun y => ?_)
        unfold GatedDrift.gateMap
        by_cases hyG : y ∈ G
        · rw [if_pos hyG]
          exact ih y
        · rw [if_neg hyG]
          have hzero :
              (GatedDrift.killK_now K G ^ t) (none : Option α)
                {o | ∃ y ∈ A, o = some y} = 0 := by
            rw [GatedDrift.none_absorbing_now (K := K) (G := G) t,
              Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
            have hnone : (none : Option α) ∉ {o | ∃ y ∈ A, o = some y} := by
              rintro ⟨y, _, hy⟩
              exact absurd hy.symm (Option.some_ne_none y)
            simp [Set.indicator_of_notMem hnone]
          rw [hzero]
          exact zero_le'
      · rw [GatedDrift.killK_now_ungated (K := K) (G := G) x hxG,
          MeasureTheory.lintegral_dirac' _ (Measurable.of_discrete)]
        have hzero :
            (GatedDrift.killK_now K G ^ t) (none : Option α)
              {o | ∃ y ∈ A, o = some y} = 0 := by
          rw [GatedDrift.none_absorbing_now (K := K) (G := G) t,
            Measure.dirac_apply' _ (DiscreteMeasurableSpace.forall_measurableSet _)]
          have hnone : (none : Option α) ∉ {o | ∃ y ∈ A, o = some y} := by
            rintro ⟨y, _, hy⟩
            exact absurd hy.symm (Option.some_ne_none y)
          simp [Set.indicator_of_notMem hnone]
        rw [hzero]
        exact zero_le'

/--
Main stopped-kernel → real-kernel transfer.  The real `K`-tail is bounded by the stopped-kernel tail
plus the immediate-kill cemetery probability (the first-exit probability from `G`). -/
theorem real_le_stopped_add_exit
    (K : Kernel α α) [IsMarkovKernel K] (G : Set α)
    (bad : α → Prop) (t : ℕ) (x : α) :
    (K ^ t) x {y | bad y}
      ≤ (stoppedK K G ^ t) x {y | bad y}
        + (GatedDrift.killK_now K G ^ t) (some x) {(none : Option α)} := by
  classical
  have hkill :=
    GatedDrift.real_le_killed_now
      (K := K) (G := G) bad t x
  let AliveBad : Set (Option α) := {o | ∃ y ∈ ({y | bad y} : Set α), o = some y}
  let Dead : Set (Option α) := {(none : Option α)}
  let R : Set (Option α) := {o | o = none ∨ (∃ y, o = some y ∧ bad y)}
  have hRsub : R ⊆ Dead ∪ AliveBad := by
    intro o ho
    rcases ho with hnone | ⟨y, hy, hbad⟩
    · exact Or.inl hnone
    · exact Or.inr ⟨y, hbad, hy⟩
  have hsplit :
      (GatedDrift.killK_now K G ^ t) (some x) R
        ≤ (GatedDrift.killK_now K G ^ t) (some x) Dead
          + (GatedDrift.killK_now K G ^ t) (some x) AliveBad := by
    refine le_trans (measure_mono hRsub) ?_
    exact measure_union_le Dead AliveBad
  have halive :
      (GatedDrift.killK_now K G ^ t) (some x) AliveBad
        ≤ (stoppedK K G ^ t) x {y | bad y} := by
    simpa [AliveBad] using
      killed_now_alive_le_stopped (K := K) (G := G) ({y | bad y} : Set α) t x
  calc
    (K ^ t) x {y | bad y}
        ≤ (GatedDrift.killK_now K G ^ t) (some x) R := hkill
    _ ≤ (GatedDrift.killK_now K G ^ t) (some x) Dead
          + (GatedDrift.killK_now K G ^ t) (some x) AliveBad := hsplit
    _ ≤ (GatedDrift.killK_now K G ^ t) (some x) Dead
          + (stoppedK K G ^ t) x {y | bad y} := by
            exact add_le_add le_rfl halive
    _ = (stoppedK K G ^ t) x {y | bad y}
          + (GatedDrift.killK_now K G ^ t) (some x) Dead := by
            rw [add_comm]

/-- Prefix-union bound for the first-exit/cemetery term, reusing `kill_now_escape_le_prefix_union`. -/
theorem exit_le_prefix_union
    (K : Kernel α α) [IsMarkovKernel K] (G S : Set α) (q : ℝ≥0∞)
    (hstep : ∀ x ∈ G, x ∈ S → K x Gᶜ ≤ q)
    (M : ℕ) (x₀ : α) (hx₀ : x₀ ∈ G) :
    (GatedDrift.killK_now K G ^ M) (some x₀) {(none : Option α)}
      ≤ (M : ℝ≥0∞) * q + ∑ τ ∈ Finset.range M, (K ^ τ) x₀ Sᶜ :=
  GatedDrift.kill_now_escape_le_prefix_union
    (K := K) (G := G) S q hstep M x₀ hx₀

end ClockStoppedTransfer

namespace ClockLayerB

open ClockRealKernel EarlyDripMarked ClockFrontMixed ClockTaintMixed
open GhostSmallConc
open ClockStoppedTransfer

variable {L K : ℕ}

/-! ## GhostSmall stopped → markedK transfer -/

/-- Ghost tail bad set. -/
def GhostBadSet (T R : ℕ) : Set (MCfg L K) :=
  {mc | R ≤ clockTaintedCount (L := L) (K := K) T mc}

/--
Marked ghost tail is bounded by stopped `KghostStar` tail plus exit from the state-local
`GhostActive` gate.  Used when you already have `GhostSmallConc.ghostSmall_level_whp` on
`KghostStar`. -/
theorem ghost_marked_tail_le_stopped_add_exit
    (T θn R H : ℕ) (Aux : MCfg L K → Prop) (mc₀ : MCfg L K) :
    ((markedK (L := L) (K := K) T θn) ^ H) mc₀
      (GhostBadSet (L := L) (K := K) T R)
    ≤
      ((KghostStar (L := L) (K := K) T θn Aux) ^ H) mc₀
        (GhostBadSet (L := L) (K := K) T R)
      +
      (GatedDrift.killK_now
        (markedK (L := L) (K := K) T θn)
        (ghostActiveSet (L := L) (K := K) T θn Aux) ^ H) (some mc₀)
        {(none : Option (MCfg L K))} := by
  classical
  have h :=
    ClockStoppedTransfer.real_le_stopped_add_exit
      (K := markedK (L := L) (K := K) T θn)
      (G := ghostActiveSet (L := L) (K := K) T θn Aux)
      (bad := fun mc => R ≤ clockTaintedCount (L := L) (K := K) T mc)
      H mc₀
  simpa [GhostBadSet, ClockStoppedTransfer.stoppedK, KghostStar, ghostActiveSet] using h

/-- Budgeted ghost transfer: stopped tail plus gate-exit budget. -/
theorem ghost_marked_tail_from_stopped_and_exit
    (T θn R H : ℕ) (Aux : MCfg L K → Prop) (mc₀ : MCfg L K)
    (εStop εExit : ℝ≥0∞)
    (hStop :
      ((KghostStar (L := L) (K := K) T θn Aux) ^ H) mc₀
        (GhostBadSet (L := L) (K := K) T R) ≤ εStop)
    (hExit :
      (GatedDrift.killK_now
        (markedK (L := L) (K := K) T θn)
        (ghostActiveSet (L := L) (K := K) T θn Aux) ^ H) (some mc₀)
        {(none : Option (MCfg L K))} ≤ εExit) :
    ((markedK (L := L) (K := K) T θn) ^ H) mc₀
      (GhostBadSet (L := L) (K := K) T R)
      ≤ εStop + εExit := by
  calc
    ((markedK (L := L) (K := K) T θn) ^ H) mc₀
      (GhostBadSet (L := L) (K := K) T R)
        ≤ ((KghostStar (L := L) (K := K) T θn Aux) ^ H) mc₀
            (GhostBadSet (L := L) (K := K) T R)
          + (GatedDrift.killK_now
              (markedK (L := L) (K := K) T θn)
              (ghostActiveSet (L := L) (K := K) T θn Aux) ^ H) (some mc₀)
              {(none : Option (MCfg L K))} :=
          ghost_marked_tail_le_stopped_add_exit
            (L := L) (K := K) T θn R H Aux mc₀
    _ ≤ εStop + εExit := add_le_add hStop hExit

/-- Prefix-union form of the GhostActive exit. -/
theorem ghost_exit_le_prefix_union
    (T θn H : ℕ) (Aux : MCfg L K → Prop)
    (S : Set (MCfg L K)) (q : ℝ≥0∞)
    (hstep :
      ∀ x ∈ ghostActiveSet (L := L) (K := K) T θn Aux,
        x ∈ S →
          markedK (L := L) (K := K) T θn x
            (ghostActiveSet (L := L) (K := K) T θn Aux)ᶜ ≤ q)
    (mc₀ : MCfg L K)
    (hmc₀ : mc₀ ∈ ghostActiveSet (L := L) (K := K) T θn Aux) :
    (GatedDrift.killK_now
      (markedK (L := L) (K := K) T θn)
      (ghostActiveSet (L := L) (K := K) T θn Aux) ^ H) (some mc₀)
      {(none : Option (MCfg L K))}
    ≤ (H : ℝ≥0∞) * q
        + ∑ τ ∈ Finset.range H,
            ((markedK (L := L) (K := K) T θn) ^ τ) mc₀ Sᶜ :=
  ClockStoppedTransfer.exit_le_prefix_union
    (K := markedK (L := L) (K := K) T θn)
    (G := ghostActiveSet (L := L) (K := K) T θn Aux)
    S q hstep H mc₀ hmc₀

/-! ## Amplification stopped → markedK transfer -/

/-- Amplification bad endpoint for fixed budget. -/
def AmpBadSetBudget
    (C₀ T : ℕ) (γ : ℝ) (mc₀ : MCfg L K) (immFrac : ℝ) :
    Set (MCfg L K) :=
  {mc₁ | ¬ AmpGoodAtEndBudget (L := L) (K := K) C₀ T γ mc₀ immFrac mc₁}

/--
Non-monotone amplification transfer.  No monotonicity is assumed; the price is the first-exit/
cemetery mass from the state-local `AmpActive` gate. -/
theorem amp_marked_tail_le_stopped_add_exit
    (T θn C₀ Lwin : ℕ) (θ ρ η γ immFrac Rcap : ℝ)
    (Aux : MCfg L K → Prop) (mc₀ : MCfg L K) :
    ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
      (AmpBadSetBudget (L := L) (K := K) C₀ T γ mc₀ immFrac)
    ≤
      ((KampStar (L := L) (K := K) T θn C₀ θ ρ η Rcap Aux) ^ Lwin) mc₀
        (AmpBadSetBudget (L := L) (K := K) C₀ T γ mc₀ immFrac)
      +
      (GatedDrift.killK_now
        (markedK (L := L) (K := K) T θn)
        (ampActiveSet (L := L) (K := K) C₀ T θ ρ η Rcap Aux) ^ Lwin) (some mc₀)
        {(none : Option (MCfg L K))} := by
  classical
  have h :=
    ClockStoppedTransfer.real_le_stopped_add_exit
      (K := markedK (L := L) (K := K) T θn)
      (G := ampActiveSet (L := L) (K := K) C₀ T θ ρ η Rcap Aux)
      (bad := fun mc =>
        ¬ AmpGoodAtEndBudget (L := L) (K := K) C₀ T γ mc₀ immFrac mc)
      Lwin mc₀
  simpa [AmpBadSetBudget, ClockStoppedTransfer.stoppedK, KampStar, ampActiveSet] using h

/-- Budgeted amplification transfer. -/
theorem amp_marked_tail_from_stopped_and_exit
    (T θn C₀ Lwin : ℕ) (θ ρ η γ immFrac Rcap : ℝ)
    (Aux : MCfg L K → Prop) (mc₀ : MCfg L K)
    (εStop εExit : ℝ≥0∞)
    (hStop :
      ((KampStar (L := L) (K := K) T θn C₀ θ ρ η Rcap Aux) ^ Lwin) mc₀
        (AmpBadSetBudget (L := L) (K := K) C₀ T γ mc₀ immFrac) ≤ εStop)
    (hExit :
      (GatedDrift.killK_now
        (markedK (L := L) (K := K) T θn)
        (ampActiveSet (L := L) (K := K) C₀ T θ ρ η Rcap Aux) ^ Lwin) (some mc₀)
        {(none : Option (MCfg L K))} ≤ εExit) :
    ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
      (AmpBadSetBudget (L := L) (K := K) C₀ T γ mc₀ immFrac)
      ≤ εStop + εExit := by
  calc
    ((markedK (L := L) (K := K) T θn) ^ Lwin) mc₀
      (AmpBadSetBudget (L := L) (K := K) C₀ T γ mc₀ immFrac)
        ≤ ((KampStar (L := L) (K := K) T θn C₀ θ ρ η Rcap Aux) ^ Lwin) mc₀
            (AmpBadSetBudget (L := L) (K := K) C₀ T γ mc₀ immFrac)
          + (GatedDrift.killK_now
              (markedK (L := L) (K := K) T θn)
              (ampActiveSet (L := L) (K := K) C₀ T θ ρ η Rcap Aux) ^ Lwin) (some mc₀)
              {(none : Option (MCfg L K))} :=
          amp_marked_tail_le_stopped_add_exit
            (L := L) (K := K) T θn C₀ Lwin θ ρ η γ immFrac Rcap Aux mc₀
    _ ≤ εStop + εExit := add_le_add hStop hExit

/-- Prefix-union form of the AmpActive exit. -/
theorem amp_exit_le_prefix_union
    (T θn C₀ Lwin : ℕ) (θ ρ η Rcap : ℝ)
    (Aux : MCfg L K → Prop)
    (S : Set (MCfg L K)) (q : ℝ≥0∞)
    (hstep :
      ∀ x ∈ ampActiveSet (L := L) (K := K) C₀ T θ ρ η Rcap Aux,
        x ∈ S →
          markedK (L := L) (K := K) T θn x
            (ampActiveSet (L := L) (K := K) C₀ T θ ρ η Rcap Aux)ᶜ ≤ q)
    (mc₀ : MCfg L K)
    (hmc₀ : mc₀ ∈ ampActiveSet (L := L) (K := K) C₀ T θ ρ η Rcap Aux) :
    (GatedDrift.killK_now
      (markedK (L := L) (K := K) T θn)
      (ampActiveSet (L := L) (K := K) C₀ T θ ρ η Rcap Aux) ^ Lwin) (some mc₀)
      {(none : Option (MCfg L K))}
    ≤ (Lwin : ℝ≥0∞) * q
        + ∑ τ ∈ Finset.range Lwin,
            ((markedK (L := L) (K := K) T θn) ^ τ) mc₀ Sᶜ :=
  ClockStoppedTransfer.exit_le_prefix_union
    (K := markedK (L := L) (K := K) T θn)
    (G := ampActiveSet (L := L) (K := K) C₀ T θ ρ η Rcap Aux)
    S q hstep Lwin mc₀ hmc₀

end ClockLayerB

end ExactMajority
