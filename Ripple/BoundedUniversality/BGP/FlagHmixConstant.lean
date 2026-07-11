import Ripple.BoundedUniversality.BGP.SelectorGateMixDischarge
import Ripple.BoundedUniversality.BGP.SelectorStackGrowthActual
import Ripple.BoundedUniversality.BGP.SelectorReplicatorHStartHaltExact

/-!
Ripple.BoundedUniversality.BGP.FlagHmixConstant
-----------------------------

The halt-coordinate `hmix` from the u-independence of the halt branch target.

KEY FACT: `branchU_haltCoord_exact_independent` shows that
  `evalBranch(branchU v, Z, haltCoordU) = enc(step(localViewConfU v), haltCoordU)`
for ANY Z. So `selectorMixTarget` at `haltCoordU` evaluates to:
  `Σ_v λ_v(t) · halt_target(v)`
where `halt_target(v) ∈ {0, 1}` is a CONSTANT (no u-dependence).

Combined with `selectorF_onehot_bound`:
  `|mix(t, haltCoord) - halt_target(vstar)| ≤ card(V) · R · epsLam(t)`
where `R ≤ 1` (branch spread at haltCoord between constants in {0,1}).

This gives `hmix` at haltCoord = `card(V) · epsLam(t)`.
With replicator Duhamel decay: epsLam(t) → 0 → hmix → 0.

The off-phase leak at haltCoord is ZERO because the target is constant:
z' = A·α·gate·(constant_mix - z) → z always contracts toward the constant.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance UniversalMachine

/-- The halt-coordinate branch spread is at most 1: all branch targets are in {0, 1},
so the max difference between any two is |0 - 1| = 1 or |1 - 0| = 1. -/
theorem branchU_haltCoord_spread_le_one (v w : UniversalLocalView) (Z : Fin d_U → ℝ) :
    |BranchData.evalBranch (branchU v) Z haltCoordU -
      BranchData.evalBranch (branchU w) Z haltCoordU| ≤ 1 := by
  -- Both evalBranch at haltCoord are in {0, 1} (from branchU_halt_target_eq_zero_or_one)
  rcases branchU_halt_target_eq_zero_or_one v Z with hv | hv <;>
  rcases branchU_halt_target_eq_zero_or_one w Z with hw | hw <;>
  rw [hv, hw] <;> norm_num

/-- Halt-coordinate `BranchSpread` with the correct constant radius.

This is the useful spread shape for the flag coordinate: the branch values are
bounded by a fixed constant, while selector accuracy is handled separately.
-/
theorem branchU_haltCoord_branchSpread_le_one
    (Z : Fin d_U → ℝ) (vstar : UniversalLocalView) :
    BranchSpread branchU Z vstar haltCoordU 1 := by
  constructor
  · rcases branchU_halt_target_eq_zero_or_one vstar Z with hzero | hone
    · rw [hzero]
      norm_num
    · rw [hone]
      norm_num
  · intro v hv
    exact branchU_haltCoord_spread_le_one v vstar Z

#print axioms branchU_haltCoord_branchSpread_le_one

/-- **Flag-coordinate hmix from λ-concentration alone.**
  At haltCoordU, the selector mix target depends ONLY on λ (not on u).
  The mix-to-target error is bounded by `card(V) · epsLam`, where epsLam
  is the total wrong-view λ mass. No u-tube needed. -/
theorem flag_hmix_of_concentration
    {V : Type} [Fintype V] [DecidableEq V]
    (branch : V → BranchData d_U B_U) (u : Fin d_U → ℝ)
    (Λ : V → ℝ) (vstar : V) {epsLam : ℝ}
    (hepsLam : 0 ≤ epsLam)
    (hsum : (∑ v : V, Λ v) = 1)
    (hlam_nonneg : ∀ v, 0 ≤ Λ v)
    (hwrong : ∀ v, v ≠ vstar → Λ v ≤ epsLam)
    -- branch spread at haltCoord ≤ 1 (halt targets are 0 or 1)
    (hspread : ∀ v, v ≠ vstar →
      |BranchData.evalBranch (branch v) u haltCoordU -
        BranchData.evalBranch (branch vstar) u haltCoordU| ≤ 1) :
    |selectorF branch u Λ haltCoordU -
      BranchData.evalBranch (branch vstar) u haltCoordU| ≤
        (Fintype.card V : ℝ) * 1 * epsLam :=
  selectorF_onehot_bound branch u Λ vstar haltCoordU zero_le_one hepsLam
    hsum hlam_nonneg hwrong hspread

#print axioms flag_hmix_of_concentration

/-- Halt-coordinate mix-to-next from λ-concentration at the correct local view.

This is the shape needed by the flag read residual: at `haltCoordU`, the branch
target is independent of `u`, so concentration of λ alone controls the error to
the next discrete halt encoding.
-/
theorem flag_hmix_to_next_of_concentration
    (u : Fin d_U → ℝ) (Λ : UniversalLocalView → ℝ) (c : UConf) {epsLam : ℝ}
    (hepsLam : 0 ≤ epsLam)
    (hsum : (∑ v : UniversalLocalView, Λ v) = 1)
    (hlam_nonneg : ∀ v, 0 ≤ Λ v)
    (hwrong : ∀ v, v ≠ localViewU c → Λ v ≤ epsLam) :
    |selectorF branchU u Λ haltCoordU -
      stackMachineEncodingU.enc (M_U.step c) haltCoordU| ≤
        (Fintype.card UniversalLocalView : ℝ) * epsLam := by
  have hmix := flag_hmix_of_concentration
    (branch := branchU) (u := u) (Λ := Λ) (vstar := localViewU c)
    hepsLam hsum hlam_nonneg hwrong
    (fun v hv => branchU_haltCoord_spread_le_one v (localViewU c) u)
  have hexact := branchU_haltCoord_exact_independent c u
  calc
    |selectorF branchU u Λ haltCoordU -
      stackMachineEncodingU.enc (M_U.step c) haltCoordU|
        = |selectorF branchU u Λ haltCoordU -
            BranchData.evalBranch (branchU (localViewU c)) u haltCoordU| := by
          congr 1
          rw [hexact]
    _ ≤ (Fintype.card UniversalLocalView : ℝ) * 1 * epsLam := hmix
    _ = (Fintype.card UniversalLocalView : ℝ) * epsLam := by ring

#print axioms flag_hmix_to_next_of_concentration

/-- Time-indexed `selectorMixTarget` form of
`flag_hmix_to_next_of_concentration`. -/
theorem selectorMixTarget_halt_to_next_of_concentration
    (u : ℝ → Fin d_U → ℝ) (Λ : UniversalLocalView → ℝ → ℝ)
    (t : ℝ) (c : UConf) {epsLam : ℝ}
    (hepsLam : 0 ≤ epsLam)
    (hsum : (∑ v : UniversalLocalView, Λ v t) = 1)
    (hlam_nonneg : ∀ v, 0 ≤ Λ v t)
    (hwrong : ∀ v, v ≠ localViewU c → Λ v t ≤ epsLam) :
    |selectorMixTarget branchU u Λ t haltCoordU -
      stackMachineEncodingU.enc (M_U.step c) haltCoordU| ≤
        (Fintype.card UniversalLocalView : ℝ) * epsLam := by
  simpa [selectorMixTarget] using
    flag_hmix_to_next_of_concentration (u t) (fun v => Λ v t) c
      hepsLam hsum hlam_nonneg hwrong

/-- Halt-coordinate mix bound from a loser-mass sum rather than pointwise
wrong-view bounds. -/
theorem selectorMixTarget_halt_to_next_of_loser_sum
    (u : ℝ → Fin d_U → ℝ) (Λ : UniversalLocalView → ℝ → ℝ)
    (t : ℝ) (c : UConf) {epsLam : ℝ}
    (hsum : (∑ v : UniversalLocalView, Λ v t) = 1)
    (hlam_nonneg : ∀ v, 0 ≤ Λ v t)
    (hloser :
      (Finset.univ.filter (fun v : UniversalLocalView => v ≠ localViewU c)).sum
        (fun v => Λ v t) ≤ epsLam) :
    |selectorMixTarget branchU u Λ t haltCoordU -
      stackMachineEncodingU.enc (M_U.step c) haltCoordU| ≤
        (Fintype.card UniversalLocalView : ℝ) * epsLam := by
  classical
  have hloser_nonneg :
      0 ≤ (Finset.univ.filter (fun v : UniversalLocalView => v ≠ localViewU c)).sum
        (fun v => Λ v t) := by
    exact Finset.sum_nonneg (fun v _hv => hlam_nonneg v)
  have hepsLam : 0 ≤ epsLam := le_trans hloser_nonneg hloser
  have hwrong : ∀ v, v ≠ localViewU c → Λ v t ≤ epsLam := by
    intro v hv
    have hsingle :
        Λ v t ≤
          (Finset.univ.filter (fun u : UniversalLocalView => u ≠ localViewU c)).sum
            (fun u => Λ u t) :=
      Finset.single_le_sum (fun u _hu => hlam_nonneg u) (by simp [hv])
    exact le_trans hsingle hloser
  exact selectorMixTarget_halt_to_next_of_concentration
    u Λ t c hepsLam hsum hlam_nonneg hwrong

/-- Halt-coordinate mix bound from a safe set of views.

If every safe view has the same halt-coordinate branch target `M`, then the
halt mix error is controlled by the total selector mass outside the safe set.
This is sharper than one-hot concentration and is the right bridge for the
cross-boundary Hoff interval where both the previous and next local views have
the same halt target. -/
theorem selectorMixTarget_halt_to_const_of_safe_loser_sum
    (u : ℝ → Fin d_U → ℝ) (Λ : UniversalLocalView → ℝ → ℝ)
    (t M : ℝ) (safe : UniversalLocalView → Prop) [DecidablePred safe]
    (hsum : (∑ v : UniversalLocalView, Λ v t) = 1)
    (hlam_nonneg : ∀ v, 0 ≤ Λ v t)
    (hsafe : ∀ v, safe v →
      BranchData.evalBranch (branchU v) (u t) haltCoordU = M)
    (hspread : ∀ v,
      |BranchData.evalBranch (branchU v) (u t) haltCoordU - M| ≤ (1 : ℝ)) :
    |selectorMixTarget branchU u Λ t haltCoordU - M| ≤
      (Finset.univ.filter (fun v : UniversalLocalView => ¬ safe v)).sum
        (fun v => Λ v t) := by
  classical
  let A : UniversalLocalView → ℝ := fun v =>
    BranchData.evalBranch (branchU v) (u t) haltCoordU
  have hdecomp :
      selectorMixTarget branchU u Λ t haltCoordU - M =
        ∑ v : UniversalLocalView, Λ v t * (A v - M) := by
    dsimp [selectorMixTarget, selectorF, A]
    calc
      (∑ v : UniversalLocalView,
          Λ v t * BranchData.evalBranch (branchU v) (u t) haltCoordU) - M
          = (∑ v : UniversalLocalView,
              Λ v t * BranchData.evalBranch (branchU v) (u t) haltCoordU) -
              (∑ v : UniversalLocalView, Λ v t) * M := by
            rw [hsum]
            ring
      _ = ∑ v : UniversalLocalView,
            Λ v t *
              (BranchData.evalBranch (branchU v) (u t) haltCoordU - M) := by
            rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro v _hv
            ring
  have hterm :
      ∀ v : UniversalLocalView,
        |Λ v t * (A v - M)| ≤ if safe v then (0 : ℝ) else Λ v t := by
    intro v
    by_cases hv : safe v
    · have hzero : A v - M = 0 := by
        dsimp [A]
        rw [hsafe v hv]
        ring
      simp [hv, hzero]
    · have hΛ0 : 0 ≤ Λ v t := hlam_nonneg v
      have hle : |Λ v t * (A v - M)| ≤ Λ v t := by
        rw [abs_mul, abs_of_nonneg hΛ0]
        calc
          Λ v t * |A v - M| ≤ Λ v t * 1 :=
            mul_le_mul_of_nonneg_left (by simpa [A] using hspread v) hΛ0
          _ = Λ v t := by ring
      simpa [hv] using hle
  have hbad_sum :
      (∑ v : UniversalLocalView, if safe v then (0 : ℝ) else Λ v t) =
        (Finset.univ.filter (fun v : UniversalLocalView => ¬ safe v)).sum
          (fun v => Λ v t) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro v _hv
    by_cases hv : safe v <;> simp [hv]
  calc
    |selectorMixTarget branchU u Λ t haltCoordU - M|
        = |∑ v : UniversalLocalView, Λ v t * (A v - M)| := by
          rw [hdecomp]
    _ ≤ ∑ v : UniversalLocalView, |Λ v t * (A v - M)| := by
          simpa using
            (Finset.abs_sum_le_sum_abs
              (fun v : UniversalLocalView => Λ v t * (A v - M)) Finset.univ)
    _ ≤ ∑ v : UniversalLocalView, if safe v then (0 : ℝ) else Λ v t :=
          Finset.sum_le_sum (fun v _hv => hterm v)
    _ = (Finset.univ.filter (fun v : UniversalLocalView => ¬ safe v)).sum
          (fun v => Λ v t) := hbad_sum

/-- Sharp one-hot halt-coordinate mix bound from total loser mass.

The older `selectorMixTarget_halt_to_next_of_loser_sum` first converts the total
loser mass into pointwise loser bounds and then pays a cardinality factor.  At
the halt coordinate the branch values are constants in a unit interval, so the
mix error is directly controlled by the total loser mass. -/
theorem selectorMixTarget_halt_to_next_of_loser_sum_sharp
    (u : ℝ → Fin d_U → ℝ) (Λ : UniversalLocalView → ℝ → ℝ)
    (t : ℝ) (c : UConf) {epsLam : ℝ}
    (hsum : (∑ v : UniversalLocalView, Λ v t) = 1)
    (hlam_nonneg : ∀ v, 0 ≤ Λ v t)
    (hloser :
      (Finset.univ.filter (fun v : UniversalLocalView => v ≠ localViewU c)).sum
        (fun v => Λ v t) ≤ epsLam) :
    |selectorMixTarget branchU u Λ t haltCoordU -
      stackMachineEncodingU.enc (M_U.step c) haltCoordU| ≤ epsLam := by
  classical
  have hbase :=
    selectorMixTarget_halt_to_const_of_safe_loser_sum
      (u := u) (Λ := Λ) (t := t)
      (M := stackMachineEncodingU.enc (M_U.step c) haltCoordU)
      (safe := fun v : UniversalLocalView => v = localViewU c)
      hsum hlam_nonneg
      (hsafe := by
        intro v hv
        rw [hv]
        exact branchU_haltCoord_exact_independent c (u t))
      (hspread := by
        intro v
        have hexact := branchU_haltCoord_exact_independent c (u t)
        calc
          |BranchData.evalBranch (branchU v) (u t) haltCoordU -
              stackMachineEncodingU.enc (M_U.step c) haltCoordU|
              =
            |BranchData.evalBranch (branchU v) (u t) haltCoordU -
              BranchData.evalBranch (branchU (localViewU c)) (u t) haltCoordU| := by
                congr 1
                rw [hexact]
          _ ≤ 1 := branchU_haltCoord_spread_le_one v (localViewU c) (u t))
  exact hbase.trans (by simpa using hloser)

/-- Pairwise halt-coordinate mix variation from loser-mass sums at two times,
for the same selected configuration. -/
theorem selectorMixTarget_halt_pair_of_loser_sum
    (u : ℝ → Fin d_U → ℝ) (Λ : UniversalLocalView → ℝ → ℝ)
    (t s : ℝ) (c : UConf) {epsT epsS : ℝ}
    (hsumT : (∑ v : UniversalLocalView, Λ v t) = 1)
    (hsumS : (∑ v : UniversalLocalView, Λ v s) = 1)
    (hlam_nonnegT : ∀ v, 0 ≤ Λ v t)
    (hlam_nonnegS : ∀ v, 0 ≤ Λ v s)
    (hloserT :
      (Finset.univ.filter (fun v : UniversalLocalView => v ≠ localViewU c)).sum
        (fun v => Λ v t) ≤ epsT)
    (hloserS :
      (Finset.univ.filter (fun v : UniversalLocalView => v ≠ localViewU c)).sum
        (fun v => Λ v s) ≤ epsS) :
    |selectorMixTarget branchU u Λ t haltCoordU -
      selectorMixTarget branchU u Λ s haltCoordU| ≤
        (Fintype.card UniversalLocalView : ℝ) * epsT +
          (Fintype.card UniversalLocalView : ℝ) * epsS := by
  have ht :=
    selectorMixTarget_halt_to_next_of_loser_sum u Λ t c
      hsumT hlam_nonnegT hloserT
  have hs :=
    selectorMixTarget_halt_to_next_of_loser_sum u Λ s c
      hsumS hlam_nonnegS hloserS
  have htri := abs_sub_le
    (selectorMixTarget branchU u Λ t haltCoordU)
    (stackMachineEncodingU.enc (M_U.step c) haltCoordU)
    (selectorMixTarget branchU u Λ s haltCoordU)
  rw [abs_sub_comm (stackMachineEncodingU.enc (M_U.step c) haltCoordU)
    (selectorMixTarget branchU u Λ s haltCoordU)] at htri
  linarith

#print axioms selectorMixTarget_halt_to_next_of_concentration

/-- Read-band `hmix` from read-band lambda concentration, for an arbitrary
discrete orbit `cfg`.

This is the halt-coordinate bridge used by the final selector residual shape:
the bound is independent of the `u`-tube because `branchU`'s halt coordinate is
constant inside each branch target.
-/
theorem selectorMixTarget_halt_to_next_on_band_of_concentration
    {p : DynGateParams} {chiReset chiGate kappa gain : ℝ → ℝ}
    {readoutP : UniversalLocalView → (Fin d_U → ℝ) → ℝ}
    (sol : SelectorDynSol d_U B_U UniversalLocalView p selectorSchedule branchU
      chiReset chiGate kappa gain readoutP)
    (cfg : ℕ → UConf)
    (hcfg_step : ∀ j, M_U.step (cfg j) = cfg (j + 1))
    (epsLam : ℕ → ℝ)
    (hepsLam : ∀ j, 0 ≤ epsLam j)
    (hsum : ∀ (j : ℕ) (t : ℝ), t ∈ Set.Icc
        (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6) →
      (∑ v : UniversalLocalView, sol.lam v t) = 1)
    (hlam_nonneg : ∀ (j : ℕ) (t : ℝ), t ∈ Set.Icc
        (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6) →
      ∀ v : UniversalLocalView, 0 ≤ sol.lam v t)
    (hwrong : ∀ (j : ℕ) (t : ℝ), t ∈ Set.Icc
        (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6) →
      ∀ v, v ≠ localViewU (cfg j) → sol.lam v t ≤ epsLam j) :
    ∀ (j : ℕ) (t : ℝ), t ∈ Set.Icc
        (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6) →
      |selectorMixTarget branchU sol.u sol.lam t haltCoordU -
        stackMachineEncodingU.enc (cfg (j + 1)) haltCoordU| ≤
          (Fintype.card UniversalLocalView : ℝ) * epsLam j := by
  intro j t ht
  have h :=
    selectorMixTarget_halt_to_next_of_concentration sol.u sol.lam t (cfg j)
      (hepsLam j) (hsum j t ht) (fun v => hlam_nonneg j t ht v)
      (hwrong j t ht)
  simpa [hcfg_step j] using h

/-- Read-band `hmix` from lambda concentration, specialized to the concrete
`M_U` orbit of input `w`.
-/
theorem selectorMixTarget_halt_to_next_on_MU_orbit_band_of_concentration
    {p : DynGateParams} {chiReset chiGate kappa gain : ℝ → ℝ}
    {readoutP : UniversalLocalView → (Fin d_U → ℝ) → ℝ}
    (sol : SelectorDynSol d_U B_U UniversalLocalView p selectorSchedule branchU
      chiReset chiGate kappa gain readoutP)
    (w : ℕ) (epsLam : ℕ → ℝ)
    (hepsLam : ∀ j, 0 ≤ epsLam j)
    (hsum : ∀ (j : ℕ) (t : ℝ), t ∈ Set.Icc
        (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6) →
      (∑ v : UniversalLocalView, sol.lam v t) = 1)
    (hlam_nonneg : ∀ (j : ℕ) (t : ℝ), t ∈ Set.Icc
        (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6) →
      ∀ v : UniversalLocalView, 0 ≤ sol.lam v t)
    (hwrong : ∀ (j : ℕ) (t : ℝ), t ∈ Set.Icc
        (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6) →
      ∀ v, v ≠ localViewU (M_U.step^[j] (M_U.init w)) →
        sol.lam v t ≤ epsLam j) :
    ∀ (j : ℕ) (t : ℝ), t ∈ Set.Icc
        (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
        (2 * Real.pi * ((j : ℝ) + 1) + 5 * Real.pi / 6) →
      |selectorMixTarget branchU sol.u sol.lam t haltCoordU -
        stackMachineEncodingU.enc (M_U.step^[j + 1] (M_U.init w)) haltCoordU| ≤
          (Fintype.card UniversalLocalView : ℝ) * epsLam j := by
  refine
    selectorMixTarget_halt_to_next_on_band_of_concentration sol
      (fun j => M_U.step^[j] (M_U.init w)) ?_ epsLam hepsLam hsum
      hlam_nonneg hwrong
  intro j
  change M_U.step (M_U.step^[j] (M_U.init w)) =
    M_U.step^[j + 1] (M_U.init w)
  rw [Function.iterate_succ_apply']

#print axioms selectorMixTarget_halt_to_next_on_band_of_concentration
#print axioms selectorMixTarget_halt_to_next_on_MU_orbit_band_of_concentration

end Ripple.BoundedUniversality.BGP
