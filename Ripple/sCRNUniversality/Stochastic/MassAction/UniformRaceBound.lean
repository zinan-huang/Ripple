/-
  Uniform race bound: bounds rawLaw coordinate events WITHOUT requiring
  deterministic states (∀ omega, state t = z).

  Instead, requires a UNIFORM bound on raceValue across ALL states.
  This is the correct formulation for combined comp+clock CRNs where
  the state at time t is random but the propensity bound holds everywhere.
-/
import Ripple.sCRNUniversality.Stochastic.MassAction.Traj
import Ripple.sCRNUniversality.Probability.MeasureBridge

namespace Ripple.sCRNUniversality.Stochastic.MassAction

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

universe u v

variable {S : Type u} [Fintype S] [DecidableEq S]
variable (N : Network.{u, v} S) [DecidableEq N.I]

/-- Uniform race bound: if the PMF complement is ≤ ε at EVERY state,
    then the rawLaw measure of the coordinate event is ≤ ε.

    Unlike rawLaw_coord_complement (which requires ∀ omega, state t = z),
    this only requires a uniform bound ∀ z, PMF(z){≠ some i} ≤ ε.
    This is satisfiable for combined comp+clock CRNs. -/
theorem rawLaw_coord_uniform_bound
    (hPos : N.hasPositiveRates) (z0 : State S)
    (t : Nat) (i : N.I) (ε : ENNReal)
    (hUniform : ∀ z : State S,
      (massActionPMF N hPos z).toMeasure {some i}ᶜ ≤ ε) :
    (rawLaw N hPos z0)
      {omega | omega (t + 1) ≠ some i} ≤ ε := by
  have hms : MeasurableSet ({some i}ᶜ : Set (Option N.I)) := trivial
  rw [show {omega : (n : Nat) → Option N.I | omega (t + 1) ≠ some i} =
    (fun x => x (t + 1)) ⁻¹' {some i}ᶜ from by ext; simp]
  rw [← Measure.map_apply (measurable_pi_apply (t + 1)) hms]
  rw [rawLaw_map_eval_succ N hPos z0 t]
  rw [Kernel.comp_apply' _ _ _ hms]
  calc ∫⁻ p, stepKernel N hPos z0 t p {some i}ᶜ
        ∂(Kernel.partialTraj (X := fun _ => Option N.I)
          (fun n => stepKernel N hPos z0 n) 0 t) (fun _ => none)
      ≤ ∫⁻ p, ε
        ∂(Kernel.partialTraj (X := fun _ => Option N.I)
          (fun n => stepKernel N hPos z0 n) 0 t) (fun _ => none) := by
        apply MeasureTheory.lintegral_mono
        intro p
        change (massActionPMF N hPos (prefixToState N z0 t p)).toMeasure {some i}ᶜ ≤ ε
        exact hUniform _
    _ = ε * (Kernel.partialTraj (X := fun _ => Option N.I)
          (fun n => stepKernel N hPos z0 n) 0 t) (fun _ => none) Set.univ := by
        rw [MeasureTheory.lintegral_const]
    _ = ε := by rw [measure_univ]; simp

/-- Multi-step uniform race bound: for each step k, if the PMF complement
    at reaction schedule(k) is ≤ ε at ALL states, then
    rawLaw {∃ k, omega(k+1) ≠ schedule(k)} ≤ n × ε. -/
theorem rawLaw_multistep_uniform_bound
    (hPos : N.hasPositiveRates) (z0 : State S)
    (n : Nat) (schedule : Fin n → N.I)
    (ε : ENNReal)
    (hUniform : ∀ k : Fin n, ∀ z : State S,
      (massActionPMF N hPos z).toMeasure {some (schedule k)}ᶜ ≤ ε) :
    (rawLaw N hPos z0)
      (⋃ k : Fin n, {omega | omega (k.val + 1) ≠ some (schedule k)}) ≤ n * ε := by
  calc (rawLaw N hPos z0) (⋃ k : Fin n, {omega | omega (k.val + 1) ≠ some (schedule k)})
      ≤ ∑' k : Fin n, (rawLaw N hPos z0) {omega | omega (k.val + 1) ≠ some (schedule k)} :=
        measure_iUnion_le _
    _ = ∑ k : Fin n, (rawLaw N hPos z0) {omega | omega (k.val + 1) ≠ some (schedule k)} :=
        tsum_fintype _
    _ ≤ ∑ _k : Fin n, ε := by
        apply Finset.sum_le_sum; intro k _
        exact rawLaw_coord_uniform_bound N hPos z0 k.val (schedule k) ε (hUniform k)
    _ = n * ε := by simp [Finset.sum_const]

/-- Reachable-state version of `rawLaw_coord_uniform_bound`: it suffices to
    bound the race complement on states obtained by `prefixToState` at time `t`.
    The proof only evaluates the uniform hypothesis on such states. -/
theorem rawLaw_coord_uniform_bound_reachable
    (hPos : N.hasPositiveRates) (z0 : State S)
    (t : Nat) (i : N.I) (ε : ENNReal)
    (hUniform : ∀ z : State S, z ∈ Set.range (prefixToState N z0 t) →
      (massActionPMF N hPos z).toMeasure {some i}ᶜ ≤ ε) :
    (rawLaw N hPos z0)
      {omega | omega (t + 1) ≠ some i} ≤ ε := by
  have hms : MeasurableSet ({some i}ᶜ : Set (Option N.I)) := trivial
  rw [show {omega : (n : Nat) → Option N.I | omega (t + 1) ≠ some i} =
    (fun x => x (t + 1)) ⁻¹' {some i}ᶜ from by ext; simp]
  rw [← Measure.map_apply (measurable_pi_apply (t + 1)) hms]
  rw [rawLaw_map_eval_succ N hPos z0 t]
  rw [Kernel.comp_apply' _ _ _ hms]
  calc ∫⁻ p, stepKernel N hPos z0 t p {some i}ᶜ
        ∂(Kernel.partialTraj (X := fun _ => Option N.I)
          (fun n => stepKernel N hPos z0 n) 0 t) (fun _ => none)
      ≤ ∫⁻ p, ε
        ∂(Kernel.partialTraj (X := fun _ => Option N.I)
          (fun n => stepKernel N hPos z0 n) 0 t) (fun _ => none) := by
        apply MeasureTheory.lintegral_mono
        intro p
        change (massActionPMF N hPos (prefixToState N z0 t p)).toMeasure {some i}ᶜ ≤ ε
        exact hUniform _ (Set.mem_range_self p)
    _ = ε * (Kernel.partialTraj (X := fun _ => Option N.I)
          (fun n => stepKernel N hPos z0 n) 0 t) (fun _ => none) Set.univ := by
        rw [MeasureTheory.lintegral_const]
    _ = ε := by rw [measure_univ]; simp

/-- Multi-step reachable-state uniform race bound: at each scheduled step `k`,
    it suffices to bound the PMF complement on states obtained by
    `prefixToState` at time `k.val`. -/
theorem rawLaw_multistep_uniform_bound_reachable
    (hPos : N.hasPositiveRates) (z0 : State S)
    (n : Nat) (schedule : Fin n → N.I)
    (ε : ENNReal)
    (hUniform : ∀ k : Fin n, ∀ z : State S,
      z ∈ Set.range (prefixToState N z0 k.val) →
      (massActionPMF N hPos z).toMeasure {some (schedule k)}ᶜ ≤ ε) :
    (rawLaw N hPos z0)
      (⋃ k : Fin n, {omega | omega (k.val + 1) ≠ some (schedule k)}) ≤ n * ε := by
  calc (rawLaw N hPos z0) (⋃ k : Fin n, {omega | omega (k.val + 1) ≠ some (schedule k)})
      ≤ ∑' k : Fin n, (rawLaw N hPos z0) {omega | omega (k.val + 1) ≠ some (schedule k)} :=
        measure_iUnion_le _
    _ = ∑ k : Fin n, (rawLaw N hPos z0) {omega | omega (k.val + 1) ≠ some (schedule k)} :=
        tsum_fintype _
    _ ≤ ∑ _k : Fin n, ε := by
        apply Finset.sum_le_sum; intro k _
        exact rawLaw_coord_uniform_bound_reachable N hPos z0 k.val (schedule k) ε (hUniform k)
    _ = n * ε := by simp [Finset.sum_const]

end Ripple.sCRNUniversality.Stochastic.MassAction
