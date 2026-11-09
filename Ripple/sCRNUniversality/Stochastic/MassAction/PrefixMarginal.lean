/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.sCRNUniversality.Stochastic.MassAction.FirstWrongBound

/-!
# One-step Markov property of the mass-action jump chain on prefix events

For the Ionescu-Tulcea law `rawLaw N hPos z0` of the mass-action jump chain: if a set `A` of
length-`n` label prefixes has a common current state `z` (`prefixToState` is constant on `A`),
then the next label is drawn from the mass-action distribution at `z`, independently of which
prefix in `A` occurred:

`P(prefix ∈ A ∧ ω (n+1) = o) = P(prefix ∈ A) · massActionPMF z o`  (`rawLaw_prefix_next`).

This is the bridge from `rawLaw` to occupation-measure recursions (`docs/audit/FIX3-SCWB.md` §1).
-/

namespace Ripple.sCRNUniversality.Stochastic.MassAction

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

universe u v

variable {S : Type u} [Fintype S] [DecidableEq S]
variable (N : Network.{u, v} S) [DecidableEq N.I]

omit [Fintype S] [DecidableEq S] [DecidableEq N.I] in
/-- Every set of finite label prefixes is measurable (finite discrete type). -/
theorem measurableSet_prefixSet (n : ℕ) (A : Set ((i : Finset.Iic n) → Option N.I)) :
    MeasurableSet A :=
  (Set.toFinite A).measurableSet

variable (hPos : N.hasPositiveRates) (z0 : State S)

/-- Probability of a prefix event under `rawLaw`, as a `partialTraj` marginal. -/
theorem rawLaw_prefix_eq (n : ℕ) (A : Set ((i : Finset.Iic n) → Option N.I)) :
    rawLaw N hPos z0 {ω | frestrictLe n ω ∈ A} =
      Kernel.partialTraj (X := fun _ => Option N.I) (fun k => stepKernel N hPos z0 k) 0 n
        (fun _ => none) A := by
  have hA := measurableSet_prefixSet N n A
  change rawLaw N hPos z0 (frestrictLe n ⁻¹' A) = _
  rw [← Measure.map_apply (measurable_frestrictLe _) hA]
  have hRawTraj : rawLaw N hPos z0 =
      Kernel.traj (X := fun _ => Option N.I) (fun k => stepKernel N hPos z0 k) 0
        (fun _ => none) := rfl
  rw [hRawTraj, Kernel.traj_map_frestrictLe_apply (X := fun _ => Option N.I)]

/-- **One-step Markov property on prefix events.** -/
theorem rawLaw_prefix_next (n : ℕ) (A : Set ((i : Finset.Iic n) → Option N.I)) (z : State S)
    (hA : ∀ p ∈ A, prefixToState N z0 n p = z) (o : Option N.I) :
    rawLaw N hPos z0 {ω | frestrictLe n ω ∈ A ∧ ω (n + 1) = o} =
      rawLaw N hPos z0 {ω | frestrictLe n ω ∈ A} * massActionPMF N hPos z o := by
  set κ := fun k => stepKernel N hPos z0 k with κ_def
  set x₀ : (j : Finset.Iic 0) → Option N.I := fun _ => none with x₀_def
  let last : Finset.Iic (n + 1) := ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩
  let B : Set ((i : Finset.Iic (n + 1)) → Option N.I) :=
    {q | frestrictLe₂ (π := fun _ => Option N.I) (Nat.le_succ n) q ∈ A ∧ q last = o}
  have hB : MeasurableSet B := measurableSet_prefixSet N (n + 1) B
  have hEq : {ω : (k : ℕ) → Option N.I | frestrictLe n ω ∈ A ∧ ω (n + 1) = o} =
      frestrictLe (n + 1) ⁻¹' B := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, B, frestrictLe_apply]
    rfl
  rw [hEq, ← Measure.map_apply (measurable_frestrictLe _) hB]
  have hRawTraj : rawLaw N hPos z0 = Kernel.traj (X := fun _ => Option N.I) κ 0 x₀ := rfl
  rw [hRawTraj, Kernel.traj_map_frestrictLe_apply (X := fun _ => Option N.I)]
  rw [Kernel.partialTraj_succ_eq_comp (X := fun _ => Option N.I) (Nat.zero_le n)]
  rw [Kernel.comp_apply' _ _ _ hB]
  have hpoint : ∀ p : (i : Finset.Iic n) → Option N.I,
      Kernel.partialTraj (X := fun _ => Option N.I) κ n (n + 1) p B =
        A.indicator (fun _ => massActionPMF N hPos z o) p := by
    intro p
    set μ := Kernel.partialTraj (X := fun _ => Option N.I) κ n (n + 1) p
    have h_map : μ.map (frestrictLe₂ (π := fun _ => Option N.I) (Nat.le_succ n)) =
        Measure.dirac p := by
      rw [← Kernel.map_apply _ (measurable_frestrictLe₂ (Nat.le_succ n)) p]
      rw [Kernel.partialTraj_succ_map_frestrictLe₂ (X := fun _ => Option N.I)]
      rw [Kernel.partialTraj_self (X := fun _ => Option N.I)]
      exact Kernel.id_apply p
    have hrestr : ∀ C : Set ((i : Finset.Iic n) → Option N.I),
        μ (frestrictLe₂ (π := fun _ => Option N.I) (Nat.le_succ n) ⁻¹' C) =
          Measure.dirac p C := by
      intro C
      rw [← h_map, Measure.map_apply (measurable_frestrictLe₂ _)
        (measurableSet_prefixSet N n C)]
    by_cases hp : p ∈ A
    · rw [Set.indicator_of_mem hp]
      have hnull : μ (frestrictLe₂ (π := fun _ => Option N.I) (Nat.le_succ n) ⁻¹' A)ᶜ = 0 := by
        rw [← Set.preimage_compl, hrestr, Measure.dirac_apply' _
          (measurableSet_prefixSet N n _)]
        simp [hp]
      have hBeq : B = ((fun q : (i : Finset.Iic (n + 1)) → Option N.I => q last) ⁻¹' {o}) ∩
          (frestrictLe₂ (π := fun _ => Option N.I) (Nat.le_succ n) ⁻¹' A) := by
        ext q; simp [B, and_comm]
      rw [hBeq, measure_inter_conull hnull]
      have hms : MeasurableSet ({o} : Set (Option N.I)) := trivial
      rw [← Measure.map_apply (measurable_pi_apply last) hms]
      have hmap2 : μ.map (fun q : (i : Finset.Iic (n + 1)) → Option N.I => q last) =
          κ n p := by
        rw [← Kernel.map_apply _ (measurable_pi_apply last) p]
        rw [Kernel.map_partialTraj_succ_self (X := fun _ => Option N.I)]
      rw [hmap2]
      change (massActionPMF N hPos (prefixToState N z0 n p)).toMeasure {o} = _
      rw [hA p hp, PMF.toMeasure_apply_singleton _ _ hms]
    · rw [Set.indicator_of_notMem hp]
      refine le_antisymm ?_ zero_le
      calc μ B ≤ μ (frestrictLe₂ (π := fun _ => Option N.I) (Nat.le_succ n) ⁻¹' A) :=
            measure_mono fun q hq => hq.1
        _ = Measure.dirac p A := hrestr A
        _ = 0 := by
          rw [Measure.dirac_apply' _ (measurableSet_prefixSet N n A)]
          exact Set.indicator_of_notMem hp 1
  simp_rw [hpoint]
  rw [lintegral_indicator_const (measurableSet_prefixSet N n A), ← hRawTraj, rawLaw_prefix_eq,
    mul_comm]

end Ripple.sCRNUniversality.Stochastic.MassAction
