/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.CTMC.DensityDependent
import Ripple.Kurtz.Defs

/-!
# Density-dependent CTMC bridge without NoAbsorbing

This file provides a `DensityProcess` constructor for density-dependent CTMCs
that may have absorbing states, under the hypothesis that the drift vanishes
at absorbing lattice states (`DriftZeroAtAbsorbingOnSimplex`).

The standard `DensityProcess` construction in `DensityDependent.lean` requires
`NoAbsorbing` (every state has positive exit rate) because the `CTMCPath.stateAt`
function returns `path.init` when times plateau at absorption time — a bug for
absorbing paths. This file works around the issue by:

1. Defining `frozenStateAt`: same as `stateAt` before absorption,
   returns the absorbing state after absorption.
2. Proving the density process using `frozenStateAt` is right-continuous.
3. Building the `DensityProcess` interface from right-continuity + bounded
   martingale estimates (no NoAbsorbing needed for integrability or QV).

## Main definitions

* `CTMCPath.frozenStateAt` — correct state readout for absorbing paths
* `DensityDepCTMC.DriftZeroAtAbsorbingOnSimplex` — drift vanishes at absorbing states
* `DensityDepCTMC.toFrozenDensityProcess` — `DensityProcess` without `NoAbsorbing`

-/

namespace Ripple.CTMC

open Classical MeasureTheory Topology

variable {d : ℕ}

/-! ### Frozen state readout -/

/-- The absorption index: the first `n` where `stateSeq n = stateSeq (n+1)`,
i.e., the state doesn't change at step `n`. For non-absorbing paths, no such
index exists. -/
noncomputable def CTMCPath.absorptionIndex (path : CTMCPath S) : Option ℕ :=
  open Classical in
  if h : ∃ n, path.stateSeq n = path.stateSeq (n + 1) then
    some (Nat.find h)
  else
    none

/-- Correct state readout that handles absorbing paths. Before absorption
(when `∃ n, t < times n`), this agrees with `stateAt`. After absorption
(when `∀ n, times n ≤ t`), this returns the absorbing state (the eventual
value of `stateSeq`) instead of `init`. -/
noncomputable def CTMCPath.frozenStateAt (path : CTMCPath S) (t : ℝ) : S :=
  open Classical in
  if h : ∃ n, t < path.times n then
    -- Standard case: t is before some jump time
    let n := Nat.find h
    if n = 0 then path.init else path.jumps (n - 1)
  else
    -- t is beyond all jump times (absorption or explosion).
    -- Return the eventual state if the sequence stabilizes.
    if h2 : ∃ n, path.stateSeq n = path.stateSeq (n + 1) then
      path.stateSeq (Nat.find h2)
    else
      path.init

/-- `frozenStateAt` agrees with `stateAt` when `∃ n, t < times n`. -/
theorem CTMCPath.frozenStateAt_eq_stateAt_of_lt_times
    (path : CTMCPath S) (t : ℝ) (h : ∃ n, t < path.times n) :
    path.frozenStateAt t = path.stateAt t := by
  simp only [frozenStateAt, stateAt, dif_pos h]

/-- If `n` is the first jump time strictly after `t`, then `frozenStateAt`
returns `stateSeq n`. -/
theorem CTMCPath.frozenStateAt_eq_stateSeq_of_first_time_gt
    (path : CTMCPath S) (t : ℝ) (n : ℕ)
    (hn : t < path.times n)
    (hmin : ∀ k ∈ Finset.range n, ¬ t < path.times k) :
    path.frozenStateAt t = path.stateSeq n := by
  simp only [frozenStateAt]
  have hex : ∃ m, t < path.times m := ⟨n, hn⟩
  rw [dif_pos hex]
  have hfind : Nat.find hex = n := by
    apply le_antisymm
    · exact Nat.find_min' hex hn
    · by_contra hle
      have hlt : Nat.find hex < n := Nat.lt_of_not_ge hle
      exact hmin (Nat.find hex) (Finset.mem_range.mpr hlt) (Nat.find_spec hex)
  rw [hfind]
  cases n with
  | zero => simp [CTMCPath.stateSeq]
  | succ n => simp [CTMCPath.stateSeq]

/-- If there is no future jump time and `n` is the first stable state-sequence
index, then `frozenStateAt` returns `stateSeq n`. -/
theorem CTMCPath.frozenStateAt_eq_stateSeq_of_first_stable
    (path : CTMCPath S) (t : ℝ) (n : ℕ)
    (hno : ∀ m, ¬ t < path.times m)
    (hn : path.stateSeq n = path.stateSeq (n + 1))
    (hmin : ∀ k ∈ Finset.range n,
      path.stateSeq k ≠ path.stateSeq (k + 1)) :
    path.frozenStateAt t = path.stateSeq n := by
  simp only [frozenStateAt]
  have hfuture : ¬ ∃ m, t < path.times m := by
    rintro ⟨m, hm⟩
    exact hno m hm
  have hstable : ∃ m, path.stateSeq m = path.stateSeq (m + 1) := ⟨n, hn⟩
  rw [dif_neg hfuture, dif_pos hstable]
  have hfind : Nat.find hstable = n := by
    apply le_antisymm
    · exact Nat.find_min' hstable hn
    · by_contra hle
      have hlt : Nat.find hstable < n := Nat.lt_of_not_ge hle
      exact hmin (Nat.find hstable) (Finset.mem_range.mpr hlt)
        (Nat.find_spec hstable)
  rw [hfind]

/-- If no jump time is after `t` and the state sequence never stabilizes,
`frozenStateAt` uses the fallback initial state. -/
theorem CTMCPath.frozenStateAt_eq_init_of_no_time_gt_of_no_stable
    (path : CTMCPath S) (t : ℝ)
    (hno : ∀ m, ¬ t < path.times m)
    (hstable : ∀ m, path.stateSeq m ≠ path.stateSeq (m + 1)) :
    path.frozenStateAt t = path.init := by
  simp only [frozenStateAt]
  have hfuture : ¬ ∃ m, t < path.times m := by
    rintro ⟨m, hm⟩
    exact hno m hm
  have hnostable : ¬ ∃ m, path.stateSeq m = path.stateSeq (m + 1) := by
    rintro ⟨m, hm⟩
    exact hstable m hm
  rw [dif_neg hfuture, dif_neg hnostable]

/-- Before the first jump, `frozenStateAt` returns `init`. -/
theorem CTMCPath.frozenStateAt_before_first
    (path : CTMCPath S) (t : ℝ) (ht : t < path.times 0) :
    path.frozenStateAt t = path.init := by
  have h : ∃ n, t < path.times n := ⟨0, ht⟩
  rw [path.frozenStateAt_eq_stateAt_of_lt_times t h]
  exact path.stateAt_before_first t ht

/-- The frozen readout is locally constant immediately to the right of every
clock time.  This uses only the definition by the first future jump time; no
strictness or non-explosion assumption is needed. -/
theorem CTMCPath.eventually_frozenStateAt_eq_nhdsWithin_Ici
    (path : CTMCPath S) (t : ℝ) :
    ∀ᶠ s in nhdsWithin t (Set.Ici t), path.frozenStateAt s = path.frozenStateAt t := by
  by_cases hex : ∃ n, t < path.times n
  · let n := Nat.find hex
    have hn : t < path.times n := Nat.find_spec hex
    let δ : ℝ := path.times n - t
    have hδ : 0 < δ := sub_pos.mpr hn
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨δ, hδ, ?_⟩
    intro s hs
    rcases hs with ⟨hball, hts⟩
    have hdist : dist s t < δ := by
      simpa [Metric.mem_ball] using hball
    have hslt : s < path.times n := by
      rw [Real.dist_eq] at hdist
      have habs : |s - t| < δ := by simpa [abs_sub_comm] using hdist
      have hsub : s - t < δ := lt_of_le_of_lt (le_abs_self (s - t)) habs
      dsimp [δ] at hsub
      linarith
    have hex_s : ∃ m, s < path.times m := ⟨n, hslt⟩
    have hfind_s : Nat.find hex_s = n := by
      apply le_antisymm
      · exact Nat.find_min' hex_s hslt
      · by_contra hle
        have hlt : Nat.find hex_s < n := Nat.lt_of_not_ge hle
        have ht_future : t < path.times (Nat.find hex_s) :=
          lt_of_le_of_lt hts (Nat.find_spec hex_s)
        exact Nat.find_min hex hlt ht_future
    show path.frozenStateAt s = path.frozenStateAt t
    have hmin_t : ∀ k ∈ Finset.range n, ¬ t < path.times k := by
      intro k hk
      exact Nat.find_min hex (Finset.mem_range.mp hk)
    have hmin_s : ∀ k ∈ Finset.range n, ¬ s < path.times k := by
      intro k hk
      exact Nat.find_min hex_s (hfind_s ▸ Finset.mem_range.mp hk)
    rw [path.frozenStateAt_eq_stateSeq_of_first_time_gt s n hslt hmin_s,
        path.frozenStateAt_eq_stateSeq_of_first_time_gt t n hn hmin_t]
  · rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨1, by norm_num, ?_⟩
    intro s hs
    have hts : t ≤ s := hs.2
    have hno_t : ∀ n, ¬ t < path.times n := by
      intro n hn
      exact hex ⟨n, hn⟩
    have hno_s : ∀ n, ¬ s < path.times n := by
      intro n hn
      exact hex ⟨n, lt_of_le_of_lt hts hn⟩
    have hex_s : ¬ ∃ n, s < path.times n := by
      rintro ⟨n, hn⟩
      exact hno_s n hn
    show path.frozenStateAt s = path.frozenStateAt t
    simp only [CTMCPath.frozenStateAt, dif_neg hex_s, dif_neg (show ¬∃ n, t < path.times n from hex)]

/-- Right-continuity of `frozenStateAt` in the discrete topology. -/
theorem CTMCPath.frozenStateAt_continuousWithinAt_Ici
    (path : CTMCPath S) [TopologicalSpace S] [DiscreteTopology S] (t : ℝ) :
    ContinuousWithinAt path.frozenStateAt (Set.Ici t) t :=
  tendsto_nhds_of_eventually_eq
    (path.eventually_frozenStateAt_eq_nhdsWithin_Ici t)

/-! ### DriftZeroAtAbsorbingOnSimplex predicate -/

variable (M : DensityDepCTMC d)

/-- The drift vanishes at every absorbing lattice state on the simplex.
This is the key condition for the frozen density process to have a well-behaved
martingale decomposition after absorption. The simplex restriction is necessary
because the continuous mass-action drift may be nonzero off-simplex even when
the integer-level exit rate is zero (e.g., self-reactions with one molecule). -/
def DensityDepCTMC.DriftZeroAtAbsorbingOnSimplex : Prop :=
  ∀ x : Fin d → Fin (M.N + 1),
    M.InSimplex x →
    M.toQMatrix.exitRate x = 0 →
      M.rateSpec.drift (fun i => (x i : ℝ) / M.N) = 0

/-- Stronger condition: all individual reaction rates vanish at absorbing states. -/
def DensityDepCTMC.RatesZeroAtAbsorbing : Prop :=
  ∀ x : Fin d → Fin (M.N + 1),
    M.toQMatrix.exitRate x = 0 →
      ∀ ℓ ∈ M.rateSpec.jumps, M.rateSpec.rate ℓ (fun i => (x i : ℝ) / M.N) = 0

/-! ### Frozen density process construction -/

/-- The density process using `frozenStateAt`. This gives the correct
density readout for paths with absorbing states. -/
noncomputable def DensityDepCTMC.frozenDensityProcess
    {Ω : Type*} (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (t : ℝ) (ω : Ω) : Fin d → ℝ :=
  fun i => ((pathMap ω).frozenStateAt t i : ℝ) / M.N

/-- The frozen initial condition: same as the standard one. -/
noncomputable def DensityDepCTMC.frozenInitialCondition
    {Ω : Type*} (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (ω : Ω) : Fin d → ℝ :=
  M.frozenDensityProcess pathMap 0 ω

/-- The frozen martingale part: the residual after subtracting init and
drift integral from the frozen density process. -/
noncomputable def DensityDepCTMC.frozenMartingalePart
    {Ω : Type*} (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (t : ℝ) (ω : Ω) : Fin d → ℝ :=
  M.frozenDensityProcess pathMap t ω -
    M.frozenInitialCondition pathMap ω -
    (fun i => ∫ s in Set.Icc (0 : ℝ) t,
      (M.rateSpec.drift (M.frozenDensityProcess pathMap s ω)) i)

/-- Generator-drift-centered frozen martingale part. Uses the actual CTMC
generator drift (from realizable transitions only) instead of the abstract
`rateSpec.drift`. Agrees with `frozenMartingalePart` when boundary
compatibility holds (see `generatorMartingalePart_eq_martingalePart_of_generatorDrift_eq`). -/
noncomputable def DensityDepCTMC.frozenGeneratorMartingalePart
    {Ω : Type*} (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (t : ℝ) (ω : Ω) : Fin d → ℝ :=
  M.frozenDensityProcess pathMap t ω -
    M.frozenInitialCondition pathMap ω -
    (fun i => ∫ s in Set.Icc (0 : ℝ) t,
      (M.generatorDrift ((pathMap ω).frozenStateAt s)) i)

/-- The frozenMartingalePart minus the frozenGeneratorMartingalePart equals
the integral of the drift mismatch. -/
theorem DensityDepCTMC.frozenMartingalePart_sub_frozenGeneratorMP
    {Ω : Type*} (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (t : ℝ) (ω : Ω) (i : Fin d) :
    M.frozenMartingalePart pathMap t ω i -
      M.frozenGeneratorMartingalePart pathMap t ω i =
    (∫ s in Set.Icc (0 : ℝ) t,
      (M.generatorDrift ((pathMap ω).frozenStateAt s)) i) -
    (∫ s in Set.Icc (0 : ℝ) t,
      (M.rateSpec.drift (M.frozenDensityProcess pathMap s ω)) i) := by
  unfold frozenMartingalePart frozenGeneratorMartingalePart frozenInitialCondition
  simp only [Pi.sub_apply]
  ring

/-! ### Key lemmas -/

section KeyLemmas

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- Each component of the frozen density process is in [0, 1]. -/
theorem DensityDepCTMC.frozenDensityProcess_mem_Icc
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (t : ℝ) (ω : Ω) (i : Fin d) :
    M.frozenDensityProcess pathMap t ω i ∈ Set.Icc 0 1 := by
  simp only [frozenDensityProcess]
  constructor
  · apply div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · rw [div_le_one (Nat.cast_pos.mpr M.hN)]
    exact Nat.cast_le.mpr (Fin.is_le _)

/-- The frozen density process is bounded by 1 in norm. -/
theorem DensityDepCTMC.frozenDensityProcess_norm_le
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (t : ℝ) (ω : Ω) :
    ‖M.frozenDensityProcess pathMap t ω‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (M.frozenDensityProcess_mem_Icc pathMap t ω i).1]
  exact (M.frozenDensityProcess_mem_Icc pathMap t ω i).2

/-- When `frozenStateAt` agrees with `stateAt` (before absorption),
the frozen density process equals the standard one. -/
theorem DensityDepCTMC.frozenDensityProcess_eq_densityProcess_of_lt_times
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1)))
    (t : ℝ) (ω : Ω)
    (h : ∃ n, t < (pathMap ω).times n) :
    M.frozenDensityProcess pathMap t ω = M.densityProcess pathMap t ω := by
  ext i
  simp only [frozenDensityProcess, densityProcess]
  congr 1
  rw [show ((pathMap ω).frozenStateAt t i : ℝ) =
    ((pathMap ω).stateAt t i : ℝ) from by
    rw [(pathMap ω).frozenStateAt_eq_stateAt_of_lt_times t h]]

/-- Drift integral bound for the frozen density process. -/
theorem DensityDepCTMC.exists_frozenDrift_setIntegral_norm_bound
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (T : ℝ) :
    ∃ C > 0, ∀ (t : ℝ) (ω : Ω), 0 ≤ t → t ≤ T →
      ‖(fun i => ∫ s in Set.Icc (0 : ℝ) t,
          (M.rateSpec.drift (M.frozenDensityProcess pathMap s ω)) i)‖ ≤ C * T := by
  obtain ⟨C, hC, hbound⟩ := M.rateSpec.exists_drift_bound_on_ball 1 zero_lt_one
  refine ⟨C, hC, ?_⟩
  intro t ω ht0 htT
  have hCT_nonneg : 0 ≤ C * T := mul_nonneg (le_of_lt hC) (le_trans ht0 htT)
  rw [pi_norm_le_iff_of_nonneg hCT_nonneg]
  intro i
  rw [Real.norm_eq_abs]
  let f : ℝ → ℝ := fun s => (M.rateSpec.drift (M.frozenDensityProcess pathMap s ω)) i
  have hnorm_bound : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖f s‖ ≤ C := by
    intro s _hs
    exact (norm_le_pi_norm (M.rateSpec.drift (M.frozenDensityProcess pathMap s ω)) i).trans
      (hbound (M.frozenDensityProcess pathMap s ω)
        (M.frozenDensityProcess_norm_le pathMap s ω))
  have hnorm :
      ‖∫ s in Set.Icc (0 : ℝ) t, f s‖ ≤ C * volume.real (Set.Icc (0 : ℝ) t) :=
    norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (0 : ℝ) t)
      (f := f) measure_Icc_lt_top hnorm_bound
  calc
    |∫ s in Set.Icc (0 : ℝ) t,
        (M.rateSpec.drift (M.frozenDensityProcess pathMap s ω)) i|
        = ‖∫ s in Set.Icc (0 : ℝ) t, f s‖ := by rw [Real.norm_eq_abs]
    _ ≤ C * volume.real (Set.Icc (0 : ℝ) t) := hnorm
    _ = C * t := by rw [Real.volume_real_Icc_of_le ht0]; ring
    _ ≤ C * T := by exact mul_le_mul_of_nonneg_left htT (le_of_lt hC)

/-- Deterministic bound on the frozen martingale norm. -/
theorem DensityDepCTMC.exists_frozenMartingalePart_norm_bound
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C > 0, ∀ (t : ℝ) (ω : Ω), 0 ≤ t → t ≤ T →
      ‖M.frozenMartingalePart pathMap t ω‖ ≤ C := by
  obtain ⟨D, hD, hD_bound⟩ := M.exists_frozenDrift_setIntegral_norm_bound pathMap T
  refine ⟨D * T + 3, by positivity, ?_⟩
  intro t ω ht0 htT
  have hproc : ‖M.frozenDensityProcess pathMap t ω‖ ≤ 1 :=
    M.frozenDensityProcess_norm_le pathMap t ω
  have hinit : ‖M.frozenInitialCondition pathMap ω‖ ≤ 1 :=
    M.frozenDensityProcess_norm_le pathMap 0 ω
  have hint : ‖(fun i => ∫ s in Set.Icc (0 : ℝ) t,
      (M.rateSpec.drift (M.frozenDensityProcess pathMap s ω)) i)‖ ≤ D * T :=
    hD_bound t ω ht0 htT
  calc
    ‖M.frozenMartingalePart pathMap t ω‖
        = ‖M.frozenDensityProcess pathMap t ω - M.frozenInitialCondition pathMap ω -
            (fun i => ∫ s in Set.Icc (0 : ℝ) t,
              (M.rateSpec.drift (M.frozenDensityProcess pathMap s ω)) i)‖ := rfl
    _ ≤ ‖M.frozenDensityProcess pathMap t ω - M.frozenInitialCondition pathMap ω‖ +
          ‖(fun i => ∫ s in Set.Icc (0 : ℝ) t,
              (M.rateSpec.drift (M.frozenDensityProcess pathMap s ω)) i)‖ := norm_sub_le _ _
    _ ≤ (‖M.frozenDensityProcess pathMap t ω‖ + ‖M.frozenInitialCondition pathMap ω‖) +
          ‖(fun i => ∫ s in Set.Icc (0 : ℝ) t,
              (M.rateSpec.drift (M.frozenDensityProcess pathMap s ω)) i)‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ (1 + 1) + D * T := by gcongr
    _ ≤ D * T + 3 := by linarith

/-- Pathwise bound for the generator-centered martingale M*.
Mirrors `exists_frozenMartingalePart_norm_bound` but for `frozenGeneratorMartingalePart`. -/
theorem DensityDepCTMC.exists_frozenGeneratorMP_norm_bound
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C > 0, ∀ (t : ℝ) (ω : Ω), 0 ≤ t → t ≤ T →
      ‖M.frozenGeneratorMartingalePart pathMap t ω‖ ≤ C := by
  let D : ℝ := ∑ i : Fin d, ∑ x : Fin d → Fin (M.N + 1), ‖M.generatorDrift x i‖
  have hD_nonneg : 0 ≤ D :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun x _ => norm_nonneg _
  refine ⟨D * T + 3, by positivity, ?_⟩
  intro t ω ht0 htT
  have hproc : ‖M.frozenDensityProcess pathMap t ω‖ ≤ 1 :=
    M.frozenDensityProcess_norm_le pathMap t ω
  have hinit : ‖M.frozenInitialCondition pathMap ω‖ ≤ 1 :=
    M.frozenDensityProcess_norm_le pathMap 0 ω
  have hint : ‖(fun i => ∫ s in Set.Icc (0 : ℝ) t,
      (M.generatorDrift ((pathMap ω).frozenStateAt s)) i)‖ ≤ D * T := by
    have hDT_nonneg : 0 ≤ D * T := mul_nonneg hD_nonneg (le_trans ht0 htT)
    rw [pi_norm_le_iff_of_nonneg hDT_nonneg]
    intro i
    rw [Real.norm_eq_abs]
    have hbd : ∀ s ∈ Set.Icc (0 : ℝ) t,
        ‖(M.generatorDrift ((pathMap ω).frozenStateAt s)) i‖ ≤ D := by
      intro s _
      calc ‖M.generatorDrift ((pathMap ω).frozenStateAt s) i‖
          ≤ ∑ x : Fin d → Fin (M.N + 1), ‖M.generatorDrift x i‖ :=
            Finset.single_le_sum (f := fun x => ‖M.generatorDrift x i‖)
              (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
        _ ≤ D := Finset.single_le_sum
              (f := fun j => ∑ x : Fin d → Fin (M.N + 1), ‖M.generatorDrift x j‖)
              (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
              (Finset.mem_univ i)
    have hnorm :
        ‖∫ s in Set.Icc (0 : ℝ) t,
          (M.generatorDrift ((pathMap ω).frozenStateAt s)) i‖ ≤
        D * volume.real (Set.Icc (0 : ℝ) t) :=
      norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top hbd
    calc |∫ s in Set.Icc (0 : ℝ) t,
            (M.generatorDrift ((pathMap ω).frozenStateAt s)) i|
        = ‖∫ s in Set.Icc (0 : ℝ) t,
            (M.generatorDrift ((pathMap ω).frozenStateAt s)) i‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ D * volume.real (Set.Icc (0 : ℝ) t) := hnorm
      _ = D * t := by rw [Real.volume_real_Icc_of_le ht0]; ring
      _ ≤ D * T := mul_le_mul_of_nonneg_left htT hD_nonneg
  calc ‖M.frozenGeneratorMartingalePart pathMap t ω‖
      = ‖M.frozenDensityProcess pathMap t ω - M.frozenInitialCondition pathMap ω -
          (fun i => ∫ s in Set.Icc (0 : ℝ) t,
            (M.generatorDrift ((pathMap ω).frozenStateAt s)) i)‖ := rfl
    _ ≤ ‖M.frozenDensityProcess pathMap t ω - M.frozenInitialCondition pathMap ω‖ +
          ‖(fun i => ∫ s in Set.Icc (0 : ℝ) t,
            (M.generatorDrift ((pathMap ω).frozenStateAt s)) i)‖ := norm_sub_le _ _
    _ ≤ (‖M.frozenDensityProcess pathMap t ω‖ + ‖M.frozenInitialCondition pathMap ω‖) +
          ‖(fun i => ∫ s in Set.Icc (0 : ℝ) t,
            (M.generatorDrift ((pathMap ω).frozenStateAt s)) i)‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ (1 + 1) + D * T := by gcongr
    _ ≤ D * T + 3 := by linarith

/-- The frozen martingale decomposition: tautological from the definition. -/
theorem DensityDepCTMC.frozen_martingale_decomposition
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) :
    ∀ t ≥ 0, ∀ᵐ ω ∂μ,
      M.frozenDensityProcess pathMap t ω =
        M.frozenInitialCondition pathMap ω +
        (fun i => ∫ s in Set.Icc (0:ℝ) t,
          (M.rateSpec.drift (M.frozenDensityProcess pathMap s ω)) i) +
        M.frozenMartingalePart pathMap t ω := by
  intro t _ht
  filter_upwards with ω
  simp only [frozenMartingalePart]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- M^N(0) = 0 for the frozen martingale. -/
theorem DensityDepCTMC.frozen_martingale_init
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) :
    ∀ᵐ ω ∂μ, M.frozenMartingalePart pathMap 0 ω = 0 := by
  filter_upwards with ω
  simp only [frozenMartingalePart, frozenInitialCondition]
  ext i
  simp only [Pi.sub_apply, sub_self, Pi.zero_apply, zero_sub, neg_eq_zero]
  exact setIntegral_measure_zero _ (by simp)

end KeyLemmas

/-! ### Right-continuity and measurability -/

section FrozenMeasurability

variable {S : Type*} [Fintype S] [DecidableEq S] [Countable S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

/-- In the product space of clock time and record trajectory, the event that
`n` is the first stable state-sequence index is measurable. -/
theorem QMatrix.measurableSet_prod_recordTrajectoryToPath_first_stable
    (n : ℕ) :
    MeasurableSet
      {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
        (QMatrix.recordTrajectoryToPath p.2).stateSeq n =
            (QMatrix.recordTrajectoryToPath p.2).stateSeq (n + 1) ∧
          ∀ k ∈ Finset.range n,
            (QMatrix.recordTrajectoryToPath p.2).stateSeq k ≠
              (QMatrix.recordTrajectoryToPath p.2).stateSeq (k + 1)} := by
  have hstable : MeasurableSet
      {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
        (QMatrix.recordTrajectoryToPath p.2).stateSeq n =
          (QMatrix.recordTrajectoryToPath p.2).stateSeq (n + 1)} :=
    measurableSet_eq_fun
      ((QMatrix.measurable_recordTrajectoryToPath_stateSeq (S := S) n).comp
        measurable_snd)
      ((QMatrix.measurable_recordTrajectoryToPath_stateSeq (S := S) (n + 1)).comp
        measurable_snd)
  have hprev : MeasurableSet
      {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
        ∀ k ∈ Finset.range n,
          (QMatrix.recordTrajectoryToPath p.2).stateSeq k ≠
            (QMatrix.recordTrajectoryToPath p.2).stateSeq (k + 1)} := by
    rw [show {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
        ∀ k ∈ Finset.range n,
          (QMatrix.recordTrajectoryToPath p.2).stateSeq k ≠
            (QMatrix.recordTrajectoryToPath p.2).stateSeq (k + 1)} =
        ⋂ k ∈ Finset.range n,
          {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
            (QMatrix.recordTrajectoryToPath p.2).stateSeq k ≠
              (QMatrix.recordTrajectoryToPath p.2).stateSeq (k + 1)} by
      ext p
      simp]
    refine Finset.measurableSet_biInter (Finset.range n) ?_
    intro k _hk
    exact (measurableSet_eq_fun
      ((QMatrix.measurable_recordTrajectoryToPath_stateSeq (S := S) k).comp
        measurable_snd)
      ((QMatrix.measurable_recordTrajectoryToPath_stateSeq (S := S) (k + 1)).comp
        measurable_snd)).compl
  exact hstable.inter hprev

/-- In the product space of clock time and record trajectory, the event that
the read-out state sequence never stabilizes is measurable. -/
theorem QMatrix.measurableSet_prod_recordTrajectoryToPath_no_stable :
    MeasurableSet
      {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
        ∀ n,
          (QMatrix.recordTrajectoryToPath p.2).stateSeq n ≠
            (QMatrix.recordTrajectoryToPath p.2).stateSeq (n + 1)} := by
  rw [show {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
        ∀ n,
          (QMatrix.recordTrajectoryToPath p.2).stateSeq n ≠
            (QMatrix.recordTrajectoryToPath p.2).stateSeq (n + 1)} =
      ⋂ n,
        {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
          (QMatrix.recordTrajectoryToPath p.2).stateSeq n ≠
            (QMatrix.recordTrajectoryToPath p.2).stateSeq (n + 1)} by
    ext p
    simp]
  refine MeasurableSet.iInter ?_
  intro n
  exact (measurableSet_eq_fun
    ((QMatrix.measurable_recordTrajectoryToPath_stateSeq (S := S) n).comp
      measurable_snd)
    ((QMatrix.measurable_recordTrajectoryToPath_stateSeq (S := S) (n + 1)).comp
      measurable_snd)).compl

/-- In the product space of clock time and record trajectory, the event
`frozenStateAt clock = a` is measurable. -/
theorem QMatrix.measurableSet_prod_recordTrajectoryToPath_frozenStateAt_eq
    (a : S) :
    MeasurableSet
      {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
        (QMatrix.recordTrajectoryToPath p.2).frozenStateAt p.1 = a} := by
  have h_state : ∀ n : ℕ, MeasurableSet
      {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
        (QMatrix.recordTrajectoryToPath p.2).stateSeq n = a} := by
    intro n
    exact ((QMatrix.measurable_recordTrajectoryToPath_stateSeq (S := S) n).comp
      measurable_snd) (measurableSet_singleton a)
  rw [show {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
        (QMatrix.recordTrajectoryToPath p.2).frozenStateAt p.1 = a} =
      ((⋃ n,
          {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
            (p.1 < (QMatrix.recordTrajectoryToPath p.2).times n ∧
              ∀ k ∈ Finset.range n,
                ¬ p.1 < (QMatrix.recordTrajectoryToPath p.2).times k) ∧
              (QMatrix.recordTrajectoryToPath p.2).stateSeq n = a}) ∪
        ({p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
            ∀ n, ¬ p.1 < (QMatrix.recordTrajectoryToPath p.2).times n} ∩
          ((⋃ n,
              {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
                ((QMatrix.recordTrajectoryToPath p.2).stateSeq n =
                    (QMatrix.recordTrajectoryToPath p.2).stateSeq (n + 1) ∧
                  ∀ k ∈ Finset.range n,
                    (QMatrix.recordTrajectoryToPath p.2).stateSeq k ≠
                      (QMatrix.recordTrajectoryToPath p.2).stateSeq (k + 1)) ∧
                  (QMatrix.recordTrajectoryToPath p.2).stateSeq n = a}) ∪
            ({p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
              ∀ n,
                (QMatrix.recordTrajectoryToPath p.2).stateSeq n ≠
                  (QMatrix.recordTrajectoryToPath p.2).stateSeq (n + 1)} ∩
              {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
                (QMatrix.recordTrajectoryToPath p.2).init = a})))) by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff]
    let path := QMatrix.recordTrajectoryToPath p.2
    let t := p.1
    change path.frozenStateAt t = a ↔
      (∃ n, (t < path.times n ∧
          ∀ k ∈ Finset.range n, ¬ t < path.times k) ∧
          path.stateSeq n = a) ∨
        (∀ n, ¬ t < path.times n) ∧
          ((∃ n, (path.stateSeq n = path.stateSeq (n + 1) ∧
              ∀ k ∈ Finset.range n,
                path.stateSeq k ≠ path.stateSeq (k + 1)) ∧
              path.stateSeq n = a) ∨
            (∀ n, path.stateSeq n ≠ path.stateSeq (n + 1)) ∧
              path.init = a)
    constructor
    · intro hstate
      by_cases hex : ∃ n, t < path.times n
      · left
        let n := Nat.find hex
        have hmin : ∀ k ∈ Finset.range n, ¬ t < path.times k := by
          intro k hk
          exact Nat.find_min hex (Finset.mem_range.mp hk)
        refine ⟨n, ⟨Nat.find_spec hex, hmin⟩, ?_⟩
        have hpath :=
          path.frozenStateAt_eq_stateSeq_of_first_time_gt t n
            (Nat.find_spec hex) hmin
        rw [← hpath]
        exact hstate
      · right
        have hno : ∀ n, ¬ t < path.times n := by
          intro n hn
          exact hex ⟨n, hn⟩
        refine ⟨hno, ?_⟩
        by_cases hstab : ∃ n, path.stateSeq n = path.stateSeq (n + 1)
        · left
          let n := Nat.find hstab
          have hmin : ∀ k ∈ Finset.range n,
              path.stateSeq k ≠ path.stateSeq (k + 1) := by
            intro k hk
            exact Nat.find_min hstab (Finset.mem_range.mp hk)
          refine ⟨n, ⟨Nat.find_spec hstab, hmin⟩, ?_⟩
          have hpath :=
            path.frozenStateAt_eq_stateSeq_of_first_stable t n hno
              (Nat.find_spec hstab) hmin
          rw [← hpath]
          exact hstate
        · right
          have hnostable : ∀ n, path.stateSeq n ≠ path.stateSeq (n + 1) := by
            intro n hn
            exact hstab ⟨n, hn⟩
          refine ⟨hnostable, ?_⟩
          have hpath :=
            path.frozenStateAt_eq_init_of_no_time_gt_of_no_stable t hno hnostable
          rw [← hpath]
          exact hstate
    · intro h
      rcases h with hfuture | htail
      · rcases hfuture with ⟨n, ⟨hn, hmin⟩, hseq⟩
        rw [path.frozenStateAt_eq_stateSeq_of_first_time_gt t n hn hmin, hseq]
      · rcases htail with ⟨hno, htail⟩
        rcases htail with hstable | hnostable
        · rcases hstable with ⟨n, ⟨hn, hmin⟩, hseq⟩
          rw [path.frozenStateAt_eq_stateSeq_of_first_stable t n hno hn hmin, hseq]
        · rcases hnostable with ⟨hnostable, hinit⟩
          rw [path.frozenStateAt_eq_init_of_no_time_gt_of_no_stable t hno hnostable,
            hinit]]
  refine (MeasurableSet.iUnion fun n => ?_).union ?_
  · exact
      (QMatrix.measurableSet_prod_recordTrajectoryToPath_first_time_gt (S := S) n).inter
        (h_state n)
  · refine (QMatrix.measurableSet_prod_recordTrajectoryToPath_no_time_gt (S := S)).inter ?_
    refine (MeasurableSet.iUnion fun n => ?_).union ?_
    · exact
        (QMatrix.measurableSet_prod_recordTrajectoryToPath_first_stable (S := S) n).inter
          (h_state n)
    · have hinit : MeasurableSet
          {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
            (QMatrix.recordTrajectoryToPath p.2).init = a} := by
        rw [show {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
            (QMatrix.recordTrajectoryToPath p.2).init = a} =
            {p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) |
              (QMatrix.recordTrajectoryToPath p.2).stateSeq 0 = a} by
          ext p
          simp [CTMCPath.stateSeq]]
        exact h_state 0
      exact QMatrix.measurableSet_prod_recordTrajectoryToPath_no_stable (S := S) |>.inter hinit

/-- The frozen canonical read-out state is jointly measurable in clock time
and record trajectory. -/
theorem QMatrix.measurable_prod_recordTrajectoryToPath_frozenStateAt :
    Measurable
      (fun p : ℝ × ((m : ℕ) → QMatrix.JumpHoldTrajectorySpace S m) =>
        (QMatrix.recordTrajectoryToPath p.2).frozenStateAt p.1) :=
  measurable_to_countable' fun a =>
    QMatrix.measurableSet_prod_recordTrajectoryToPath_frozenStateAt_eq (S := S) a

end FrozenMeasurability

/-- The canonical frozen state readout is jointly measurable. -/
theorem DensityDepCTMC.measurable_prod_canonicalPathMap_frozenStateAt
    (M : DensityDepCTMC d) :
    Measurable (fun p : ℝ × M.canonicalRecordΩ =>
      (M.canonicalPathMap p.2).frozenStateAt p.1) := by
  simpa [DensityDepCTMC.canonicalPathMap] using
    (QMatrix.measurable_prod_recordTrajectoryToPath_frozenStateAt
      (S := Fin d → Fin (M.N + 1)))

/-- The canonical frozen state readout is measurable at each fixed time. -/
theorem DensityDepCTMC.measurable_canonicalPathMap_frozenStateAt
    (M : DensityDepCTMC d) (t : ℝ) :
    Measurable (fun records : M.canonicalRecordΩ =>
      (M.canonicalPathMap records).frozenStateAt t) := by
  have hpair : Measurable (fun records : M.canonicalRecordΩ => (t, records)) :=
    Measurable.prodMk measurable_const measurable_id
  exact M.measurable_prod_canonicalPathMap_frozenStateAt.comp hpair

section FrozenRegularity

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The frozen density readout is eventually constant immediately to the right
of every time along every path. -/
theorem DensityDepCTMC.frozenDensityProcess_eventually_eq_nhdsWithin_Ici
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (ω : Ω)
    (t : ℝ) :
    ∀ᶠ s in nhdsWithin t (Set.Ici t),
      M.frozenDensityProcess pathMap s ω =
        M.frozenDensityProcess pathMap t ω := by
  exact ((pathMap ω).eventually_frozenStateAt_eq_nhdsWithin_Ici t).mono
    fun _ hs => by
      ext i
      simp [DensityDepCTMC.frozenDensityProcess, hs]

/-- Right-continuity of the frozen density readout. -/
theorem DensityDepCTMC.frozenDensityProcess_continuousWithinAt_Ici
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (ω : Ω)
    (t : ℝ) :
    ContinuousWithinAt
      (fun s => M.frozenDensityProcess pathMap s ω) (Set.Ici t) t :=
  tendsto_nhds_of_eventually_eq
    (M.frozenDensityProcess_eventually_eq_nhdsWithin_Ici pathMap ω t)

/-- The frozen drift readout is eventually constant immediately to the right
of every time. -/
theorem DensityDepCTMC.drift_frozenDensityProcess_eventually_eq_nhdsWithin_Ici
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (ω : Ω)
    (t : ℝ) :
    ∀ᶠ s in nhdsWithin t (Set.Ici t),
      M.rateSpec.drift (M.frozenDensityProcess pathMap s ω) =
        M.rateSpec.drift (M.frozenDensityProcess pathMap t ω) :=
  (M.frozenDensityProcess_eventually_eq_nhdsWithin_Ici pathMap ω t).mono
    fun _ hs => by rw [hs]

/-- Right-continuity of the frozen drift readout. -/
theorem DensityDepCTMC.drift_frozenDensityProcess_continuousWithinAt_Ici
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (ω : Ω)
    (t : ℝ) :
    ContinuousWithinAt
      (fun s => M.rateSpec.drift (M.frozenDensityProcess pathMap s ω))
      (Set.Ici t) t :=
  tendsto_nhds_of_eventually_eq
    (M.drift_frozenDensityProcess_eventually_eq_nhdsWithin_Ici pathMap ω t)

/-- On one full-measure event, the canonical frozen density path is
right-continuous at every time.  The event is deterministic here. -/
theorem DensityDepCTMC.canonical_frozenDensityProcess_forall_continuousWithinAt_Ici_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ∀ t : ℝ,
        ContinuousWithinAt
          (fun s => M.frozenDensityProcess M.canonicalPathMap s records)
          (Set.Ici t) t := by
  filter_upwards with records t
  exact M.frozenDensityProcess_continuousWithinAt_Ici M.canonicalPathMap records t

/-- The canonical frozen density process is measurable at a fixed time. -/
theorem DensityDepCTMC.measurable_canonicalFrozenDensityProcess
    (M : DensityDepCTMC d) (t : ℝ) :
    Measurable (fun records : M.canonicalRecordΩ =>
      M.frozenDensityProcess M.canonicalPathMap t records) := by
  rw [measurable_pi_iff]
  intro i
  unfold frozenDensityProcess
  have hstate_i : Measurable (fun records : M.canonicalRecordΩ =>
      ((M.canonicalPathMap records).frozenStateAt t) i) :=
    (measurable_pi_apply i).comp (M.measurable_canonicalPathMap_frozenStateAt t)
  exact (Measurable.of_discrete
    (f := fun x : Fin (M.N + 1) => (x : ℝ) / (M.N : ℝ))).comp hstate_i

/-- The canonical frozen density process is jointly measurable. -/
theorem DensityDepCTMC.measurable_prod_canonicalFrozenDensityProcess
    (M : DensityDepCTMC d) :
    Measurable (fun p : ℝ × M.canonicalRecordΩ =>
      M.frozenDensityProcess M.canonicalPathMap p.1 p.2) := by
  rw [measurable_pi_iff]
  intro i
  unfold frozenDensityProcess
  have hstate_i : Measurable (fun p : ℝ × M.canonicalRecordΩ =>
      ((M.canonicalPathMap p.2).frozenStateAt p.1) i) :=
    (measurable_pi_apply i).comp M.measurable_prod_canonicalPathMap_frozenStateAt
  exact (Measurable.of_discrete
    (f := fun x : Fin (M.N + 1) => (x : ℝ) / (M.N : ℝ))).comp hstate_i

/-- The canonical frozen initial condition is measurable. -/
theorem DensityDepCTMC.measurable_canonicalFrozenInitialCondition
    (M : DensityDepCTMC d) :
    Measurable (fun records : M.canonicalRecordΩ =>
      M.frozenInitialCondition M.canonicalPathMap records) := by
  simpa [frozenInitialCondition] using M.measurable_canonicalFrozenDensityProcess 0

/-- Joint measurability of a frozen drift component. -/
theorem DensityDepCTMC.measurable_prod_canonicalFrozenDrift_component
    (M : DensityDepCTMC d) (i : Fin d) :
    Measurable (fun p : ℝ × M.canonicalRecordΩ =>
      (M.rateSpec.drift
        (M.frozenDensityProcess M.canonicalPathMap p.1 p.2)) i) := by
  exact (measurable_pi_apply i).comp
    ((Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) =>
        M.rateSpec.drift (fun j => (x j : ℝ) / (M.N : ℝ)))).comp
          M.measurable_prod_canonicalPathMap_frozenStateAt)

set_option maxHeartbeats 400000 in
/-- The frozen drift-integral term is measurable for fixed terminal time and
component. -/
theorem DensityDepCTMC.measurable_canonicalFrozenDriftIntegral_component
    (M : DensityDepCTMC d) (t : ℝ) (i : Fin d) :
    Measurable (fun records : M.canonicalRecordΩ =>
      ∫ s in Set.Icc (0 : ℝ) t,
        (M.rateSpec.drift
          (M.frozenDensityProcess M.canonicalPathMap s records)) i) := by
  have hjoint : StronglyMeasurable
      (fun p : M.canonicalRecordΩ × ℝ =>
        (M.rateSpec.drift
          (M.frozenDensityProcess M.canonicalPathMap p.2 p.1)) i) :=
    ((M.measurable_prod_canonicalFrozenDrift_component i).comp
      measurable_swap).stronglyMeasurable
  exact (hjoint.integral_prod_right'
    (ν := MeasureTheory.Measure.restrict volume (Set.Icc 0 t))).measurable

/-- For a fixed canonical record, a frozen drift component is measurable in
time. -/
theorem DensityDepCTMC.measurable_canonicalFrozenDrift_component_section
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (i : Fin d) :
    Measurable (fun s : ℝ =>
      (M.rateSpec.drift
        (M.frozenDensityProcess M.canonicalPathMap s records)) i) := by
  have hpair : Measurable (fun s : ℝ => (s, records)) :=
    Measurable.prodMk measurable_id measurable_const
  have hstate : Measurable (fun s : ℝ =>
      (M.canonicalPathMap records).frozenStateAt s) :=
    M.measurable_prod_canonicalPathMap_frozenStateAt.comp hpair
  exact (measurable_pi_apply i).comp
    ((Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) =>
        M.rateSpec.drift (fun j => (x j : ℝ) / (M.N : ℝ)))).comp hstate)

/-- Frozen drift components are integrable on compact time intervals. -/
theorem DensityDepCTMC.integrableOn_canonicalFrozenDrift_component_Icc
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (i : Fin d)
    (a b : ℝ) :
    IntegrableOn
      (fun s : ℝ =>
        (M.rateSpec.drift
          (M.frozenDensityProcess M.canonicalPathMap s records)) i)
      (Set.Icc a b) volume := by
  obtain ⟨C, hC, hbound⟩ :=
    M.rateSpec.exists_drift_bound_on_ball 1 zero_lt_one
  refine MeasureTheory.IntegrableOn.of_bound measure_Icc_lt_top
    ((M.measurable_canonicalFrozenDrift_component_section records i).aestronglyMeasurable)
    C ?_
  filter_upwards with s
  exact (norm_le_pi_norm
    (M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap s records)) i).trans
      (hbound (M.frozenDensityProcess M.canonicalPathMap s records)
        (M.frozenDensityProcess_norm_le M.canonicalPathMap s records))

/-- The frozen drift-integral primitive is right-continuous at every time. -/
theorem DensityDepCTMC.canonicalFrozenDriftIntegral_component_continuousWithinAt_Ici
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (i : Fin d)
    (t : ℝ) :
    ContinuousWithinAt
      (fun u : ℝ =>
        ∫ s in Set.Icc (0 : ℝ) u,
          (M.rateSpec.drift
            (M.frozenDensityProcess M.canonicalPathMap s records)) i)
      (Set.Ici t) t := by
  let f : ℝ → ℝ := fun s =>
    (M.rateSpec.drift (M.frozenDensityProcess M.canonicalPathMap s records)) i
  by_cases ht0 : 0 ≤ t
  · let b : ℝ := t + 1
    have hb : t < b := by dsimp [b]; linarith
    have hcontOn :
        ContinuousOn (fun u : ℝ => ∫ s in Set.Icc (0 : ℝ) u, f s)
          (Set.Icc (0 : ℝ) b) :=
      intervalIntegral.continuousOn_primitive_Icc
        (M.integrableOn_canonicalFrozenDrift_component_Icc records i 0 b)
    have htmem : t ∈ Set.Icc (0 : ℝ) b := ⟨ht0, le_of_lt hb⟩
    have hwithin :
        ContinuousWithinAt (fun u : ℝ => ∫ s in Set.Icc (0 : ℝ) u, f s)
          (Set.Icc (0 : ℝ) b) t :=
      hcontOn.continuousWithinAt htmem
    have hmem : Set.Icc (0 : ℝ) b ∈ nhdsWithin t (Set.Ici t) := by
      have hIic : Set.Iic b ∈ nhds t := Iic_mem_nhds hb
      refine Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Ici t) hIic) ?_
      intro u hu
      exact ⟨le_trans ht0 hu.1, hu.2⟩
    exact hwithin.mono_of_mem_nhdsWithin hmem
  · have htneg : t < 0 := lt_of_not_ge ht0
    have hevent :
        (fun u : ℝ => ∫ s in Set.Icc (0 : ℝ) u, f s)
          =ᶠ[nhdsWithin t (Set.Ici t)] fun _ => (0 : ℝ) := by
      have hIio : Set.Iio (0 : ℝ) ∈ nhds t := Iio_mem_nhds htneg
      have hmem : Set.Iio (0 : ℝ) ∈ nhdsWithin t (Set.Ici t) :=
        Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Ici t) hIio)
          (fun _ hu => hu.2)
      filter_upwards [hmem] with u hu
      have hempty : Set.Icc (0 : ℝ) u = ∅ :=
        Set.Icc_eq_empty (not_le_of_gt hu)
      rw [hempty, setIntegral_empty]
    have htval :
        (∫ s in Set.Icc (0 : ℝ) t, f s) = (0 : ℝ) := by
      have hempty : Set.Icc (0 : ℝ) t = ∅ :=
        Set.Icc_eq_empty (not_le_of_gt htneg)
      rw [hempty, setIntegral_empty]
    exact (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq
      hevent htval

/-- Vector-valued frozen drift-integral right-continuity. -/
theorem DensityDepCTMC.canonicalFrozenDriftIntegral_continuousWithinAt_Ici
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (t : ℝ) :
    ContinuousWithinAt
      (fun u : ℝ => fun i : Fin d =>
        ∫ s in Set.Icc (0 : ℝ) u,
          (M.rateSpec.drift
            (M.frozenDensityProcess M.canonicalPathMap s records)) i)
      (Set.Ici t) t := by
  rw [continuousWithinAt_pi]
  intro i
  exact M.canonicalFrozenDriftIntegral_component_continuousWithinAt_Ici records i t

/-- The frozen drift-integral primitive is right-continuous at every time on a
deterministic full-measure event. -/
theorem DensityDepCTMC.canonical_frozenDriftIntegral_forall_continuousWithinAt_Ici_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ∀ t : ℝ,
        ContinuousWithinAt
          (fun u : ℝ => fun i : Fin d =>
            ∫ s in Set.Icc (0 : ℝ) u,
              (M.rateSpec.drift
                (M.frozenDensityProcess M.canonicalPathMap s records)) i)
          (Set.Ici t) t := by
  filter_upwards with records t
  exact M.canonicalFrozenDriftIntegral_continuousWithinAt_Ici records t

/-- Fixed-time measurability of the canonical frozen martingale residual. -/
theorem DensityDepCTMC.measurable_canonicalFrozenMartingalePart
    (M : DensityDepCTMC d) (t : ℝ) :
    Measurable (fun records : M.canonicalRecordΩ =>
      M.frozenMartingalePart M.canonicalPathMap t records) := by
  rw [measurable_pi_iff]
  intro i
  simp only [frozenMartingalePart, Pi.sub_apply]
  exact (((measurable_pi_apply i).comp
    (M.measurable_canonicalFrozenDensityProcess t)).sub
      ((measurable_pi_apply i).comp
        M.measurable_canonicalFrozenInitialCondition)).sub
      (M.measurable_canonicalFrozenDriftIntegral_component t i)

/-- Fixed-time measurability of `‖frozen M(t)‖²`. -/
theorem DensityDepCTMC.measurable_canonicalFrozenMartingalePart_norm_sq
    (M : DensityDepCTMC d) (t : ℝ) :
    Measurable (fun records : M.canonicalRecordΩ =>
      ‖M.frozenMartingalePart M.canonicalPathMap t records‖ ^ 2) :=
  (measurable_norm.comp (M.measurable_canonicalFrozenMartingalePart t)).pow measurable_const

/-- The rational-time frozen martingale sup-square is measurable. -/
theorem DensityDepCTMC.measurable_canonicalFrozenMartingalePart_ratSup
    (M : DensityDepCTMC d) (T : ℝ) :
    Measurable (fun records : M.canonicalRecordΩ =>
      ⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T),
        ‖M.frozenMartingalePart M.canonicalPathMap (q : ℝ) records‖ ^ 2) := by
  apply Measurable.iSup
  intro q
  exact (M.measurable_canonicalFrozenMartingalePart_norm_sq (q : ℝ)).iSup_Prop _

/-- Right-continuity of the frozen martingale residual follows from the frozen
density readout and frozen drift-integral primitive. -/
theorem DensityDepCTMC.frozenMartingalePart_continuousWithinAt_Ici_of_driftIntegral
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (ω : Ω) (t : ℝ)
    (hX : ContinuousWithinAt
      (fun s => M.frozenDensityProcess pathMap s ω) (Set.Ici t) t)
    (hI : ContinuousWithinAt
      (fun u : ℝ => fun i : Fin d =>
        ∫ s in Set.Icc (0 : ℝ) u,
          (M.rateSpec.drift (M.frozenDensityProcess pathMap s ω)) i)
      (Set.Ici t) t) :
    ContinuousWithinAt
      (fun s => M.frozenMartingalePart pathMap s ω) (Set.Ici t) t := by
  simpa [frozenMartingalePart] using
    (hX.sub continuousWithinAt_const).sub hI

/-- Canonical frozen martingale paths are right-continuous at every time on one
full-measure event. -/
theorem DensityDepCTMC.canonical_frozenMartingalePart_forall_continuousWithinAt_Ici_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ∀ t : ℝ,
        ContinuousWithinAt
          (fun s => M.frozenMartingalePart M.canonicalPathMap s records)
          (Set.Ici t) t := by
  filter_upwards
    [M.canonical_frozenDensityProcess_forall_continuousWithinAt_Ici_ae x₀,
     M.canonical_frozenDriftIntegral_forall_continuousWithinAt_Ici_ae x₀]
    with records hX hI t
  exact M.frozenMartingalePart_continuousWithinAt_Ici_of_driftIntegral
    M.canonicalPathMap records t (hX t) (hI t)

/-- The rational-time frozen supremum is bounded by the real-time frozen
supremum, pointwise. -/
theorem DensityDepCTMC.frozen_ratSup_le_realSup
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (T : ℝ) (hT : 0 ≤ T)
    (ω : Ω) :
    (⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T),
      ‖M.frozenMartingalePart pathMap (q : ℝ) ω‖ ^ 2) ≤
    (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
      ‖M.frozenMartingalePart pathMap s ω‖ ^ 2) := by
  obtain ⟨K, _hK, hK_bound⟩ :=
    M.exists_frozenMartingalePart_norm_bound pathMap T hT
  let B : ℝ := K ^ 2
  have hinner_bdd : ∀ s : ℝ,
      BddAbove (Set.range fun _ : 0 ≤ s ∧ s ≤ T =>
        ‖M.frozenMartingalePart pathMap s ω‖ ^ 2) := by
    intro s
    refine ⟨B, ?_⟩
    rintro y ⟨hs, rfl⟩
    have hnorm := hK_bound s ω hs.1 hs.2
    nlinarith [norm_nonneg (M.frozenMartingalePart pathMap s ω)]
  have houter_bdd : BddAbove (Set.range fun s : ℝ =>
      ⨆ (_ : 0 ≤ s ∧ s ≤ T), ‖M.frozenMartingalePart pathMap s ω‖ ^ 2) := by
    refine ⟨B, ?_⟩
    rintro y ⟨s, rfl⟩
    exact Real.iSup_le (fun hs => by
      have hnorm := hK_bound s ω hs.1 hs.2
      nlinarith [norm_nonneg (M.frozenMartingalePart pathMap s ω)])
      (by positivity)
  refine Real.iSup_le (fun q => ?_) (Real.iSup_nonneg fun s =>
    Real.iSup_nonneg fun _ => sq_nonneg ‖M.frozenMartingalePart pathMap s ω‖)
  refine Real.iSup_le (fun hq => ?_) (Real.iSup_nonneg fun s =>
    Real.iSup_nonneg fun _ => sq_nonneg ‖M.frozenMartingalePart pathMap s ω‖)
  exact le_trans
    (le_ciSup (hinner_bdd (q : ℝ)) hq)
    (le_ciSup houter_bdd (q : ℝ))

/-- Under right-continuity of the frozen martingale path, the real-time
supremum is the rational-time supremum plus the endpoint. -/
theorem DensityDepCTMC.frozen_martingale_realSup_eq_ratSup_max_endpoint_of_forall_continuousWithinAt
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (T : ℝ) (hT : 0 ≤ T)
    (ω : Ω)
    (hcont : ∀ t : ℝ,
      ContinuousWithinAt
        (fun s => M.frozenMartingalePart pathMap s ω) (Set.Ici t) t) :
    (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart pathMap s ω‖ ^ 2) =
      max
        (⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T),
          ‖M.frozenMartingalePart pathMap (q : ℝ) ω‖ ^ 2)
        (‖M.frozenMartingalePart pathMap T ω‖ ^ 2) := by
  let f : ℝ → ℝ := fun s => ‖M.frozenMartingalePart pathMap s ω‖ ^ 2
  obtain ⟨K, _hK, hK_bound⟩ :=
    M.exists_frozenMartingalePart_norm_bound pathMap T hT
  have hfcont : ∀ t : ℝ, ContinuousWithinAt f (Set.Ici t) t := by
    intro t
    exact (hcont t).norm.pow 2
  have hfbound : ∃ B : ℝ, ∀ s : ℝ, 0 ≤ s → s ≤ T → f s ≤ B := by
    refine ⟨K ^ 2, ?_⟩
    intro s hs0 hsT
    have hnorm := hK_bound s ω hs0 hsT
    dsimp [f]
    nlinarith [norm_nonneg (M.frozenMartingalePart pathMap s ω)]
  have hfnonneg : ∀ s : ℝ, 0 ≤ s → s ≤ T → 0 ≤ f s := by
    intro s _hs0 _hsT
    exact sq_nonneg _
  have hle :
      (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T), f s) ≤
        max
          (⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T), f (q : ℝ))
          (f T) :=
    realSup_le_ratSup_max_endpoint_of_right_continuous f T hT
      hfcont hfbound hfnonneg
  have hrat_le :
      (⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T),
        ‖M.frozenMartingalePart pathMap (q : ℝ) ω‖ ^ 2) ≤
      (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart pathMap s ω‖ ^ 2) :=
    M.frozen_ratSup_le_realSup pathMap T hT ω
  have hinner_bdd : ∀ s : ℝ,
      BddAbove (Set.range fun _ : 0 ≤ s ∧ s ≤ T => f s) := by
    intro s
    refine ⟨K ^ 2, ?_⟩
    rintro y ⟨hs, rfl⟩
    have hnorm := hK_bound s ω hs.1 hs.2
    dsimp [f]
    nlinarith [norm_nonneg (M.frozenMartingalePart pathMap s ω)]
  have houter_bdd : BddAbove (Set.range fun s : ℝ =>
      ⨆ (_ : 0 ≤ s ∧ s ≤ T), f s) := by
    refine ⟨K ^ 2, ?_⟩
    rintro y ⟨s, rfl⟩
    exact Real.iSup_le (fun hs => by
      have hnorm := hK_bound s ω hs.1 hs.2
      dsimp [f]
      nlinarith [norm_nonneg (M.frozenMartingalePart pathMap s ω)])
      (by positivity)
  have hend_le :
      ‖M.frozenMartingalePart pathMap T ω‖ ^ 2 ≤
      (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart pathMap s ω‖ ^ 2) := by
    dsimp [f] at hinner_bdd houter_bdd
    exact le_trans
      (le_ciSup (hinner_bdd T) ⟨hT, le_rfl⟩)
      (le_ciSup houter_bdd T)
  apply le_antisymm
  · simpa [f] using hle
  · exact max_le hrat_le hend_le

/-- Canonical a.e. real/rational supremum comparison for the frozen
martingale sup-square. -/
theorem DensityDepCTMC.canonical_frozen_martingale_realSup_eq_ratSup_max_endpoint_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (hT : 0 ≤ T) :
    (fun records : M.canonicalRecordΩ =>
      ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2) =ᵐ[M.canonicalRecordMeasure x₀]
    (fun records : M.canonicalRecordΩ =>
      max
        (⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T),
          ‖M.frozenMartingalePart M.canonicalPathMap (q : ℝ) records‖ ^ 2)
        (‖M.frozenMartingalePart M.canonicalPathMap T records‖ ^ 2)) := by
  filter_upwards
    [M.canonical_frozenMartingalePart_forall_continuousWithinAt_Ici_ae x₀]
    with records hcont
  exact M.frozen_martingale_realSup_eq_ratSup_max_endpoint_of_forall_continuousWithinAt
    M.canonicalPathMap T hT records hcont

/-- Frozen canonical martingale sup-square integrability from the rational-time
measurable proxy and deterministic boundedness. -/
theorem DensityDepCTMC.canonical_frozen_martingale_sup_sq_integrable
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) :
    ∀ T > 0,
      Integrable (fun records : M.canonicalRecordΩ =>
        ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
          ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2)
        (M.canonicalRecordMeasure x₀) := by
  intro T hT
  let ratProxy : M.canonicalRecordΩ → ℝ := fun records =>
    ⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T),
      ‖M.frozenMartingalePart M.canonicalPathMap (q : ℝ) records‖ ^ 2
  let endProxy : M.canonicalRecordΩ → ℝ := fun records =>
    ‖M.frozenMartingalePart M.canonicalPathMap T records‖ ^ 2
  let proxy : M.canonicalRecordΩ → ℝ := fun records =>
    max (ratProxy records) (endProxy records)
  have hproxy_meas : Measurable proxy := by
    exact (M.measurable_canonicalFrozenMartingalePart_ratSup T).max
      (M.measurable_canonicalFrozenMartingalePart_norm_sq T)
  obtain ⟨K, _hK, hK_bound⟩ := M.exists_frozenMartingalePart_norm_bound
    M.canonicalPathMap T (le_of_lt hT)
  let C : ℝ := K ^ 2
  have hC_nonneg : 0 ≤ C := by positivity
  have hproxy_int : Integrable proxy (M.canonicalRecordMeasure x₀) := by
    refine MeasureTheory.Integrable.of_bound
      hproxy_meas.aestronglyMeasurable C ?_
    filter_upwards with records
    have hrat_nonneg : 0 ≤ ratProxy records := by
      dsimp [ratProxy]
      exact Real.iSup_nonneg fun q =>
        Real.iSup_nonneg fun _ => sq_nonneg _
    have hend_nonneg : 0 ≤ endProxy records := by
      dsimp [endProxy]
      exact sq_nonneg _
    have hproxy_nonneg : 0 ≤ proxy records := by
      dsimp [proxy]
      exact le_trans hrat_nonneg (le_max_left (ratProxy records) (endProxy records))
    have hrat_le : ratProxy records ≤ C := by
      dsimp [ratProxy, C]
      refine Real.iSup_le (fun q => ?_) hC_nonneg
      refine Real.iSup_le (fun hq => ?_) hC_nonneg
      have hnorm := hK_bound (q : ℝ) records hq.1 hq.2
      nlinarith [norm_nonneg
        (M.frozenMartingalePart M.canonicalPathMap (q : ℝ) records)]
    have hend_le : endProxy records ≤ C := by
      dsimp [endProxy, C]
      have hnorm := hK_bound T records (le_of_lt hT) le_rfl
      nlinarith [norm_nonneg (M.frozenMartingalePart M.canonicalPathMap T records)]
    have hproxy_le : proxy records ≤ C := by
      dsimp [proxy]
      exact max_le hrat_le hend_le
    rw [Real.norm_eq_abs, abs_of_nonneg hproxy_nonneg]
    exact hproxy_le
  have heq :
      proxy =ᵐ[M.canonicalRecordMeasure x₀]
        (fun records : M.canonicalRecordΩ =>
          ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
            ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2) := by
    exact (M.canonical_frozen_martingale_realSup_eq_ratSup_max_endpoint_ae
      x₀ T (le_of_lt hT)).symm
  exact hproxy_int.congr heq

/-! ### frozenGeneratorMartingalePart (M*) measurability and integrability -/

/-- Joint measurability: `(s, records) ↦ generatorDrift(frozenStateAt(s, records)) i`. -/
theorem DensityDepCTMC.measurable_prod_canonicalFrozenGeneratorDrift_component
    (M : DensityDepCTMC d) (i : Fin d) :
    Measurable (fun p : ℝ × M.canonicalRecordΩ =>
      M.generatorDrift ((M.canonicalPathMap p.2).frozenStateAt p.1) i) :=
  (measurable_pi_apply i).comp
    ((Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) => M.generatorDrift x)).comp
        M.measurable_prod_canonicalPathMap_frozenStateAt)

set_option maxHeartbeats 400000 in
/-- The generator-drift integral `∫₀ᵗ generatorDrift(frozenStateAt(s)) i ds`
is measurable as a function of records. -/
theorem DensityDepCTMC.measurable_canonicalFrozenGeneratorDriftIntegral_component
    (M : DensityDepCTMC d) (t : ℝ) (i : Fin d) :
    Measurable (fun records : M.canonicalRecordΩ =>
      ∫ s in Set.Icc (0 : ℝ) t,
        M.generatorDrift ((M.canonicalPathMap records).frozenStateAt s) i) := by
  have hjoint : StronglyMeasurable
      (fun p : M.canonicalRecordΩ × ℝ =>
        M.generatorDrift ((M.canonicalPathMap p.1).frozenStateAt p.2) i) :=
    ((M.measurable_prod_canonicalFrozenGeneratorDrift_component i).comp
      measurable_swap).stronglyMeasurable
  exact (hjoint.integral_prod_right'
    (ν := MeasureTheory.Measure.restrict volume (Set.Icc 0 t))).measurable

/-- For fixed records, the generator-drift component is measurable in time. -/
theorem DensityDepCTMC.measurable_canonicalFrozenGeneratorDrift_component_section
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (i : Fin d) :
    Measurable (fun s : ℝ =>
      M.generatorDrift ((M.canonicalPathMap records).frozenStateAt s) i) := by
  have hpair : Measurable (fun s : ℝ => (s, records)) :=
    Measurable.prodMk measurable_id measurable_const
  exact (measurable_pi_apply i).comp
    ((Measurable.of_discrete
      (f := fun x : Fin d → Fin (M.N + 1) => M.generatorDrift x)).comp
        (M.measurable_prod_canonicalPathMap_frozenStateAt.comp hpair))

/-- Generator-drift components are integrable on compact time intervals. -/
theorem DensityDepCTMC.integrableOn_canonicalFrozenGeneratorDrift_component_Icc
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (i : Fin d)
    (a b : ℝ) :
    IntegrableOn
      (fun s : ℝ => M.generatorDrift ((M.canonicalPathMap records).frozenStateAt s) i)
      (Set.Icc a b) volume := by
  let C : ℝ := ∑ x : Fin d → Fin (M.N + 1), ‖M.generatorDrift x i‖
  refine MeasureTheory.IntegrableOn.of_bound measure_Icc_lt_top
    ((M.measurable_canonicalFrozenGeneratorDrift_component_section records i).aestronglyMeasurable)
    C ?_
  filter_upwards with s
  exact Finset.single_le_sum (f := fun x => ‖M.generatorDrift x i‖)
    (fun _ _ => norm_nonneg _)
    (Finset.mem_univ ((M.canonicalPathMap records).frozenStateAt s))

/-- Right-continuity of the generator-drift integral (component). -/
theorem DensityDepCTMC.canonicalFrozenGeneratorDriftIntegral_component_continuousWithinAt_Ici
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (i : Fin d)
    (t : ℝ) :
    ContinuousWithinAt
      (fun u : ℝ =>
        ∫ s in Set.Icc (0 : ℝ) u,
          M.generatorDrift ((M.canonicalPathMap records).frozenStateAt s) i)
      (Set.Ici t) t := by
  by_cases ht0 : 0 ≤ t
  · let b : ℝ := t + 1
    have hb : t < b := by dsimp [b]; linarith
    have hcontOn :
        ContinuousOn (fun u : ℝ => ∫ s in Set.Icc (0 : ℝ) u,
          M.generatorDrift ((M.canonicalPathMap records).frozenStateAt s) i)
          (Set.Icc (0 : ℝ) b) :=
      intervalIntegral.continuousOn_primitive_Icc
        (M.integrableOn_canonicalFrozenGeneratorDrift_component_Icc records i 0 b)
    exact (hcontOn.continuousWithinAt ⟨ht0, le_of_lt hb⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Ici t) (Iic_mem_nhds hb))
        fun u hu => ⟨le_trans ht0 hu.1, hu.2⟩)
  · have htneg : t < 0 := lt_of_not_ge ht0
    have hevent :
        (fun u : ℝ => ∫ s in Set.Icc (0 : ℝ) u,
          M.generatorDrift ((M.canonicalPathMap records).frozenStateAt s) i)
          =ᶠ[nhdsWithin t (Set.Ici t)] fun _ => (0 : ℝ) := by
      filter_upwards [Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Ici t)
          (Iio_mem_nhds htneg)) (fun _ hu => hu.2)] with u hu
      rw [Set.Icc_eq_empty (not_le_of_gt hu), setIntegral_empty]
    exact (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq hevent
      (by rw [Set.Icc_eq_empty (not_le_of_gt htneg), setIntegral_empty])

/-- Vector-valued generator-drift integral right-continuity. -/
theorem DensityDepCTMC.canonicalFrozenGeneratorDriftIntegral_continuousWithinAt_Ici
    (M : DensityDepCTMC d) (records : M.canonicalRecordΩ) (t : ℝ) :
    ContinuousWithinAt
      (fun u : ℝ => fun i : Fin d =>
        ∫ s in Set.Icc (0 : ℝ) u,
          M.generatorDrift ((M.canonicalPathMap records).frozenStateAt s) i)
      (Set.Ici t) t := by
  rw [continuousWithinAt_pi]
  intro i
  exact M.canonicalFrozenGeneratorDriftIntegral_component_continuousWithinAt_Ici records i t

/-- Fixed-time measurability of `M*(t)` as a function of records. -/
theorem DensityDepCTMC.measurable_canonicalFrozenGeneratorMartingalePart
    (M : DensityDepCTMC d) (t : ℝ) :
    Measurable (fun records : M.canonicalRecordΩ =>
      M.frozenGeneratorMartingalePart M.canonicalPathMap t records) := by
  rw [measurable_pi_iff]
  intro i
  simp only [frozenGeneratorMartingalePart, Pi.sub_apply]
  exact (((measurable_pi_apply i).comp
    (M.measurable_canonicalFrozenDensityProcess t)).sub
      ((measurable_pi_apply i).comp
        M.measurable_canonicalFrozenInitialCondition)).sub
      (M.measurable_canonicalFrozenGeneratorDriftIntegral_component t i)

/-- Fixed-time measurability of `‖M*(t)‖²`. -/
theorem DensityDepCTMC.measurable_canonicalFrozenGeneratorMartingalePart_norm_sq
    (M : DensityDepCTMC d) (t : ℝ) :
    Measurable (fun records : M.canonicalRecordΩ =>
      ‖M.frozenGeneratorMartingalePart M.canonicalPathMap t records‖ ^ 2) :=
  (measurable_norm.comp (M.measurable_canonicalFrozenGeneratorMartingalePart t)).pow measurable_const

/-- The rational-time sup of `‖M*(q)‖²` is measurable. -/
theorem DensityDepCTMC.measurable_canonicalFrozenGeneratorMartingalePart_ratSup
    (M : DensityDepCTMC d) (T : ℝ) :
    Measurable (fun records : M.canonicalRecordΩ =>
      ⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T),
        ‖M.frozenGeneratorMartingalePart M.canonicalPathMap (q : ℝ) records‖ ^ 2) := by
  apply Measurable.iSup
  intro q
  exact (M.measurable_canonicalFrozenGeneratorMartingalePart_norm_sq (q : ℝ)).iSup_Prop _

/-- M* is right-continuous in time (deterministic, all paths). -/
theorem DensityDepCTMC.frozenGeneratorMartingalePart_continuousWithinAt_Ici
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (ω : Ω) (t : ℝ)
    (hX : ContinuousWithinAt
      (fun s => M.frozenDensityProcess pathMap s ω) (Set.Ici t) t)
    (hI : ContinuousWithinAt
      (fun u : ℝ => fun i : Fin d =>
        ∫ s in Set.Icc (0 : ℝ) u,
          M.generatorDrift ((pathMap ω).frozenStateAt s) i)
      (Set.Ici t) t) :
    ContinuousWithinAt
      (fun s => M.frozenGeneratorMartingalePart pathMap s ω) (Set.Ici t) t := by
  simpa [frozenGeneratorMartingalePart] using
    (hX.sub continuousWithinAt_const).sub hI

/-- Canonical M* paths are right-continuous a.e. (actually deterministic). -/
theorem DensityDepCTMC.canonical_frozenGeneratorMartingalePart_forall_continuousWithinAt_Ici_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) :
    ∀ᵐ records ∂M.canonicalRecordMeasure x₀,
      ∀ t : ℝ,
        ContinuousWithinAt
          (fun s => M.frozenGeneratorMartingalePart M.canonicalPathMap s records)
          (Set.Ici t) t := by
  filter_upwards
    [M.canonical_frozenDensityProcess_forall_continuousWithinAt_Ici_ae x₀]
    with records hX t
  exact M.frozenGeneratorMartingalePart_continuousWithinAt_Ici
    M.canonicalPathMap records t (hX t)
    (M.canonicalFrozenGeneratorDriftIntegral_continuousWithinAt_Ici records t)

/-- Real sup of `‖M*(s)‖²` equals rational sup max endpoint, a.e. -/
theorem DensityDepCTMC.canonical_frozen_generatorMP_realSup_eq_ratSup_max_endpoint_ae
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (hT : 0 ≤ T) :
    (fun records : M.canonicalRecordΩ =>
      ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2)
    =ᵐ[M.canonicalRecordMeasure x₀]
    (fun records : M.canonicalRecordΩ =>
      max
        (⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T),
          ‖M.frozenGeneratorMartingalePart M.canonicalPathMap (q : ℝ) records‖ ^ 2)
        (‖M.frozenGeneratorMartingalePart M.canonicalPathMap T records‖ ^ 2)) := by
  filter_upwards
    [M.canonical_frozenGeneratorMartingalePart_forall_continuousWithinAt_Ici_ae x₀]
    with records hcont
  have hfcont : ∀ t : ℝ, ContinuousWithinAt
      (fun s => ‖M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2)
      (Set.Ici t) t := fun t => (hcont t).norm.pow 2
  obtain ⟨K, _hK, hK_bound⟩ :=
    M.exists_frozenGeneratorMP_norm_bound M.canonicalPathMap T hT
  have hfbound : ∀ s : ℝ, 0 ≤ s → s ≤ T →
      ‖M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2 ≤ K ^ 2 :=
    fun s hs0 hsT => pow_le_pow_left₀ (norm_nonneg _) (hK_bound s records hs0 hsT) 2
  have hle :=
    realSup_le_ratSup_max_endpoint_of_right_continuous
      (fun s => ‖M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2)
      T hT hfcont ⟨K ^ 2, fun s hs0 hsT => hfbound s hs0 hsT⟩
      (fun s _hs0 _hsT => sq_nonneg _)
  have hinner_bdd : ∀ s : ℝ,
      BddAbove (Set.range fun _ : 0 ≤ s ∧ s ≤ T =>
        ‖M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2) := by
    intro s
    refine ⟨K ^ 2, ?_⟩
    rintro y ⟨hs, rfl⟩
    exact hfbound s hs.1 hs.2
  have houter_bdd : BddAbove (Set.range fun s : ℝ =>
      ⨆ (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2) := by
    refine ⟨K ^ 2, ?_⟩
    rintro y ⟨s, rfl⟩
    exact Real.iSup_le (fun hs => hfbound s hs.1 hs.2) (by positivity)
  have hrat_le :
      (⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T),
        ‖M.frozenGeneratorMartingalePart M.canonicalPathMap (q : ℝ) records‖ ^ 2) ≤
      (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2) := by
    refine Real.iSup_le (fun q => ?_) (Real.iSup_nonneg fun s =>
      Real.iSup_nonneg fun _ => sq_nonneg _)
    refine Real.iSup_le (fun hq => ?_) (Real.iSup_nonneg fun s =>
      Real.iSup_nonneg fun _ => sq_nonneg _)
    exact le_trans (le_ciSup (hinner_bdd (q : ℝ)) hq) (le_ciSup houter_bdd (q : ℝ))
  have hend_le :
      ‖M.frozenGeneratorMartingalePart M.canonicalPathMap T records‖ ^ 2 ≤
      (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2) :=
    le_trans (le_ciSup (hinner_bdd T) ⟨hT, le_rfl⟩) (le_ciSup houter_bdd T)
  exact le_antisymm hle (max_le hrat_le hend_le)

/-- Frozen generator martingale sup-square integrability. -/
theorem DensityDepCTMC.canonical_frozen_generatorMP_sup_sq_integrable
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    (T : ℝ) (hT : 0 < T) :
    Integrable (fun records : M.canonicalRecordΩ =>
      ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenGeneratorMartingalePart M.canonicalPathMap s records‖ ^ 2)
      (M.canonicalRecordMeasure x₀) := by
  obtain ⟨K, _hK, hK_bound⟩ := M.exists_frozenGeneratorMP_norm_bound
    M.canonicalPathMap T (le_of_lt hT)
  let C : ℝ := K ^ 2
  let ratProxy : M.canonicalRecordΩ → ℝ := fun records =>
    ⨆ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T),
      ‖M.frozenGeneratorMartingalePart M.canonicalPathMap (q : ℝ) records‖ ^ 2
  let endProxy : M.canonicalRecordΩ → ℝ := fun records =>
    ‖M.frozenGeneratorMartingalePart M.canonicalPathMap T records‖ ^ 2
  let proxy : M.canonicalRecordΩ → ℝ := fun records =>
    max (ratProxy records) (endProxy records)
  have hproxy_meas : Measurable proxy :=
    (M.measurable_canonicalFrozenGeneratorMartingalePart_ratSup T).max
      (M.measurable_canonicalFrozenGeneratorMartingalePart_norm_sq T)
  have hproxy_int : Integrable proxy (M.canonicalRecordMeasure x₀) := by
    refine MeasureTheory.Integrable.of_bound
      hproxy_meas.aestronglyMeasurable C ?_
    filter_upwards with records
    have hrat_nonneg : 0 ≤ ratProxy records :=
      Real.iSup_nonneg fun q => Real.iSup_nonneg fun _ => sq_nonneg _
    have hend_nonneg : 0 ≤ endProxy records := sq_nonneg _
    have hrat_le : ratProxy records ≤ C := by
      dsimp [ratProxy, C]
      refine Real.iSup_le (fun q => ?_) (by positivity)
      refine Real.iSup_le (fun hq => ?_) (by positivity)
      exact pow_le_pow_left₀ (norm_nonneg _) (hK_bound (q : ℝ) records hq.1 hq.2) 2
    have hend_le : endProxy records ≤ C := by
      dsimp [endProxy, C]
      exact pow_le_pow_left₀ (norm_nonneg _) (hK_bound T records (le_of_lt hT) le_rfl) 2
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hrat_nonneg (le_max_left _ _))]
    exact max_le hrat_le hend_le
  exact hproxy_int.congr
    (M.canonical_frozen_generatorMP_realSup_eq_ratSup_max_endpoint_ae x₀ T (le_of_lt hT)).symm

/-- Deterministic finite-horizon bound for the frozen martingale sup-square. -/
theorem DensityDepCTMC.exists_frozen_martingale_sup_sq_bound
    (M : DensityDepCTMC d)
    (pathMap : Ω → CTMCPath (Fin d → Fin (M.N + 1))) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C > 0, ∀ ω : Ω,
      (⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart pathMap s ω‖ ^ 2) ≤ C := by
  obtain ⟨K, _hK, hK_bound⟩ := M.exists_frozenMartingalePart_norm_bound pathMap T hT
  refine ⟨K ^ 2 + 1, by positivity, ?_⟩
  intro ω
  refine Real.iSup_le ?_ (by positivity)
  intro s
  refine Real.iSup_le ?_ (by positivity)
  intro hs
  have hnorm := hK_bound s ω hs.1 hs.2
  have hnorm_nonneg : 0 ≤ ‖M.frozenMartingalePart pathMap s ω‖ := norm_nonneg _
  calc
    ‖M.frozenMartingalePart pathMap s ω‖ ^ 2 ≤ K ^ 2 := by nlinarith
    _ ≤ K ^ 2 + 1 := by linarith

/-- A crude canonical QV-style bound for the frozen martingale.  Since the
constant may depend on `T`, deterministic boundedness plus integrability
provides the `C * T / N` form required by the abstract interface. -/
theorem DensityDepCTMC.canonical_frozen_martingale_qv_bound
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1)) :
    ∀ T > 0, ∃ C > 0,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤ C * T / M.N := by
  intro T hT
  obtain ⟨K, _hK, hbound⟩ :=
    M.exists_frozen_martingale_sup_sq_bound M.canonicalPathMap T (le_of_lt hT)
  have hNpos : (0 : ℝ) < M.N := Nat.cast_pos.mpr M.hN
  refine ⟨K * M.N / T + 1, by positivity, ?_⟩
  calc
    ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀
        ≤ ∫ _records, K ∂M.canonicalRecordMeasure x₀ := by
          exact integral_mono_ae
            (M.canonical_frozen_martingale_sup_sq_integrable x₀ T hT)
            (integrable_const K)
            (ae_of_all _ fun records => hbound records)
    _ = K := by simp [measure_univ]
    _ ≤ (K * M.N / T + 1) * T / M.N := by
          have hT_ne : T ≠ 0 := ne_of_gt hT
          have hN_ne : (M.N : ℝ) ≠ 0 := ne_of_gt hNpos
          field_simp
          nlinarith [mul_pos hT hNpos]

/-- The O(T/N) QV bound for the frozen martingale, given the Doob inequality
as a hypothesis. The Doob hypothesis says:

  E[sup_{s ≤ T} ‖frozenM(s)‖²] ≤ A · E[∫₀ᵀ instantQVRate(frozenState(s)) ds]

This is the stopped-martingale version of the standard Doob L² inequality.
The `instantQVRate` is bounded by C₀/N (from `exists_instantQVRate_bound`),
so the RHS ≤ A · C₀ · T / N, giving the uniform O(T/N) QV bound.

The Doob hypothesis can be discharged via the guarded-compensator approach
in `FrozenRandomIndexDoob.lean`. -/
theorem DensityDepCTMC.canonical_frozen_martingale_qv_bound_of_doob
    (M : DensityDepCTMC d) (x₀ : Fin d → Fin (M.N + 1))
    {A : ℝ} (hA : 0 < A)
    (hDoob : ∀ T > 0,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤
      A * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
        ∂M.canonicalRecordMeasure x₀) :
    ∀ T > 0, ∃ C > 0,
      ∫ records, ⨆ (s : ℝ) (_ : 0 ≤ s ∧ s ≤ T),
        ‖M.frozenMartingalePart M.canonicalPathMap s records‖ ^ 2
        ∂M.canonicalRecordMeasure x₀ ≤ C * T / M.N := by
  intro T hT
  obtain ⟨C₀, hC₀, hqv_bound⟩ := M.exists_instantQVRate_bound
  have hNpos : (0 : ℝ) < M.N := Nat.cast_pos.mpr M.hN
  refine ⟨A * C₀, mul_pos hA hC₀, ?_⟩
  -- Step 1: hDoob gives LHS ≤ A * E[∫ QVRate]
  -- Step 2: pointwise ∫ QVRate ≤ C₀*T/N, so E[∫ QVRate] ≤ C₀*T/N
  -- Step 3: LHS ≤ A * C₀*T/N
  -- Pointwise: for each records, ∫ QVRate ≤ C₀/N * T
  have h_pointwise : ∀ records : M.canonicalRecordΩ,
      ∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)
      ≤ C₀ / ↑M.N * T := by
    intro records
    have h_vol : MeasureTheory.volume.real (Set.Icc (0 : ℝ) T) = T := by
      rw [Measure.real_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ T - 0)]
      ring
    calc ∫ s in Set.Icc (0 : ℝ) T,
          M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)
        ≤ ‖∫ s in Set.Icc (0 : ℝ) T,
            M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s)‖ :=
          le_abs_self _
      _ ≤ C₀ / ↑M.N * MeasureTheory.volume.real (Set.Icc (0 : ℝ) T) :=
          MeasureTheory.norm_setIntegral_le_of_norm_le_const
            measure_Icc_lt_top (fun s _hs => by
              rw [Real.norm_eq_abs, abs_of_nonneg (M.instantQVRate_nonneg _)]
              exact hqv_bound _)
      _ = C₀ / ↑M.N * T := by rw [h_vol]
  -- Take expectation: E[∫ QVRate] ≤ C₀*T/N
  have h_expect_bound :
      ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
        ∂M.canonicalRecordMeasure x₀ ≤ C₀ / ↑M.N * T := by
    calc _ ≤ ∫ _records, (C₀ / ↑M.N * T) ∂M.canonicalRecordMeasure x₀ :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun records =>
              MeasureTheory.setIntegral_nonneg measurableSet_Icc
                fun s _hs => M.instantQVRate_nonneg _)
            (integrable_const _)
            (Filter.Eventually.of_forall h_pointwise)
      _ = C₀ / ↑M.N * T := by simp [MeasureTheory.integral_const]
  calc _ ≤ A * ∫ records, (∫ s in Set.Icc (0 : ℝ) T,
        M.instantQVRate ((M.canonicalPathMap records).frozenStateAt s))
        ∂M.canonicalRecordMeasure x₀ := hDoob T hT
    _ ≤ A * (C₀ / M.N * T) :=
        mul_le_mul_of_nonneg_left h_expect_bound (le_of_lt hA)
    _ = A * C₀ * T / M.N := by ring

end FrozenRegularity

/-! ### The DensityProcess constructor -/

/-- Construct a `DensityProcess` from a density-dependent CTMC with absorbing
states, given that the drift vanishes at absorbing states.

This bypasses the `NoAbsorbing` requirement of the standard construction by
using `frozenStateAt` (which correctly handles absorption) and proving the
regularity inputs directly. -/
noncomputable def DensityDepCTMC.toFrozenDensityProcess
    (x₀ : Fin d → Fin (M.N + 1))
    (_hDrift : M.DriftZeroAtAbsorbingOnSimplex)
    (_hcons : M.ConservativeJumps)
    (_hinit : M.InSimplex x₀) :
    Ripple.Kurtz.DensityProcess d M.rateSpec M.N (M.canonicalRecordMeasure x₀) where
  process := M.frozenDensityProcess M.canonicalPathMap
  process_norm_le_one := M.frozenDensityProcess_norm_le M.canonicalPathMap
  init := M.frozenInitialCondition M.canonicalPathMap
  martingale_part := M.frozenMartingalePart M.canonicalPathMap
  decomposition := M.frozen_martingale_decomposition
    (M.canonicalRecordMeasure x₀) M.canonicalPathMap
  martingale_init := M.frozen_martingale_init
    (M.canonicalRecordMeasure x₀) M.canonicalPathMap
  martingale_sup_sq_nonneg := by
    intro T _hT
    filter_upwards with ω
    exact Real.iSup_nonneg fun s =>
      Real.iSup_nonneg fun _hs =>
        sq_nonneg ‖M.frozenMartingalePart M.canonicalPathMap s ω‖
  martingale_sup_sq_integrable := by
    exact M.canonical_frozen_martingale_sup_sq_integrable x₀
  martingale_qv_bound := by
    exact M.canonical_frozen_martingale_qv_bound x₀

end Ripple.CTMC
