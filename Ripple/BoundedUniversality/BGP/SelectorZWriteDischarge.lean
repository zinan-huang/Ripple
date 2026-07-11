import Ripple.BoundedUniversality.BGP.SelectorZRead

/-!
Ripple.BoundedUniversality.BGP.SelectorZWriteDischarge
----------------------------------
Discharge of the carried `hzM` premise of the corrected selector headline
(`selector_MU_flag_read_all_next`), as the z-write Reach assembly (εwrite contraction #2).

Design from ChatGPT Pro `pbook` (2026-06-15, R1), ported to the real `SelectorDynSol`
telescope (the dispatched answer used `autoImplicit`-abbreviated signatures).

The headline carries `hzM : ∀ j i, ∀ t ∈ selectorReadWindow j, |z t i − Mtarget j i| ≤ δz j`.
This file produces it from `z_after_write_bound` (already landed) + an integral lower bound
`Λ j` (`write_Z_integral_lower`) + a uniform start-mismatch box radius `Bz0 j`, with the
EXPLICIT closed form

  `δz j := δzh j + (exp(−Λ j)·Bz0 j + δw j)`   (`selectorZReadDelta`),

and proves `δz j → 0` (antitone + tendsto), the satisfiability evidence for the budget
`δz j + δM j ≤ r_LE_U`.  The carried sub-premises (`hmix_stable_z_write`, `hz_post_write_drift`,
`hz_start_mismatch_bound`, `hwriteInt_lbd_z`) are honest finite-window Reach facts, not false
global smoothness assertions.
-/

noncomputable section

open Filter
open scoped Real Topology BigOperators

namespace Ripple.BoundedUniversality.BGP

/-- Start of the z-active write half in cycle `j`: `a = 2πj + π/6`. -/
def selectorZWriteStart (j : ℕ) : ℝ :=
  (2 : ℝ) * Real.pi * (j : ℝ) + Real.pi / 6

/-- Frozen hold time for the z-write target: `m = 2πj + π/2`. -/
def selectorZHold (j : ℕ) : ℝ :=
  (2 : ℝ) * Real.pi * (j : ℝ) + Real.pi / 2

/-- End of the post-z-write read window: `b = 2πj + 7π/6`. -/
def selectorZReadEnd (j : ℕ) : ℝ :=
  (2 : ℝ) * Real.pi * (j : ℝ) + (7 : ℝ) * Real.pi / 6

/-- `2πj + π/6 ≤ 2πj + π/2`. -/
lemma selectorZWriteStart_le_hold (j : ℕ) :
    selectorZWriteStart j ≤ selectorZHold j := by
  dsimp [selectorZWriteStart, selectorZHold]
  nlinarith [Real.pi_pos]

/-- The headline read window `[2πj+5π/6, 2πj+7π/6]` is contained in the post-write interval
`[2πj+π/2, 2πj+7π/6]`. -/
lemma selectorReadWindow_subset_zAfterWrite (j : ℕ) :
    selectorReadWindow j ⊆ Set.Icc (selectorZHold j) (selectorZReadEnd j) := by
  intro t ht
  have ht' :
      t ∈
        Set.Icc
          ((2 : ℝ) * Real.pi * (j : ℝ) + (5 : ℝ) * Real.pi / 6)
          ((2 : ℝ) * Real.pi * (j : ℝ) + (7 : ℝ) * Real.pi / 6) := by
    simpa [selectorReadWindow] using ht
  rcases ht' with ⟨ht_lo, ht_hi⟩
  constructor
  · have hhold_le_readStart :
        selectorZHold j ≤
          (2 : ℝ) * Real.pi * (j : ℝ) + (5 : ℝ) * Real.pi / 6 := by
      dsimp [selectorZHold]
      nlinarith [Real.pi_pos]
    exact le_trans hhold_le_readStart ht_lo
  · simpa [selectorZReadEnd] using ht_hi

/-- If `Λ ≤ I`, then `exp(−I)·|X| ≤ exp(−Λ)·B` whenever `|X| ≤ B`. -/
lemma exp_neg_mul_abs_le_exp_neg_lbd_mul
    {I Λ X B : ℝ} (hΛ : Λ ≤ I) (hX : |X| ≤ B) :
    Real.exp (-I) * |X| ≤ Real.exp (-Λ) * B := by
  have hExp : Real.exp (-I) ≤ Real.exp (-Λ) := Real.exp_le_exp.mpr (neg_le_neg hΛ)
  exact mul_le_mul hExp hX (abs_nonneg X) (le_of_lt (Real.exp_pos (-Λ)))

/-- The explicit z-write contraction term: `exp(−Λ j)·Bz0 j`. -/
def selectorZWriteContraction (Λ Bz0 : ℕ → ℝ) (j : ℕ) : ℝ :=
  Real.exp (-(Λ j)) * Bz0 j

/-- The scalar z-read radius: `δz j = δzh j + (exp(−Λ j)·Bz0 j + δw j)`. -/
def selectorZReadDelta (Λ Bz0 δw δzh : ℕ → ℝ) (j : ℕ) : ℝ :=
  δzh j + (selectorZWriteContraction Λ Bz0 j + δw j)

/-- The contraction term is antitone when `Λ` is monotone and `Bz0` antitone nonneg. -/
lemma selectorZWriteContraction_antitone
    {Λ Bz0 : ℕ → ℝ} (hΛ : Monotone Λ) (hB : Antitone Bz0) (hB_nonneg : ∀ j, 0 ≤ Bz0 j) :
    Antitone (selectorZWriteContraction Λ Bz0) := by
  intro j k hjk
  dsimp [selectorZWriteContraction]
  have hExp : Real.exp (-(Λ k)) ≤ Real.exp (-(Λ j)) :=
    Real.exp_le_exp.mpr (neg_le_neg (hΛ hjk))
  exact mul_le_mul hExp (hB hjk) (hB_nonneg k) (le_of_lt (Real.exp_pos (-(Λ j))))

/-- The closed-form `δz` is antitone whenever its three summands are. -/
lemma selectorZReadDelta_antitone
    {Λ Bz0 δw δzh : ℕ → ℝ}
    (hδzh : Antitone δzh)
    (hctr : Antitone (selectorZWriteContraction Λ Bz0))
    (hδw : Antitone δw) :
    Antitone (selectorZReadDelta Λ Bz0 δw δzh) := by
  intro j k hjk
  dsimp [selectorZReadDelta]
  exact add_le_add (hδzh hjk) (add_le_add (hctr hjk) (hδw hjk))

/-- Sufficient monotonicity check for the closed-form `δz`. -/
lemma selectorZReadDelta_antitone_of_lbd
    {Λ Bz0 δw δzh : ℕ → ℝ}
    (hΛ : Monotone Λ) (hB : Antitone Bz0) (hB_nonneg : ∀ j, 0 ≤ Bz0 j)
    (hδw : Antitone δw) (hδzh : Antitone δzh) :
    Antitone (selectorZReadDelta Λ Bz0 δw δzh) :=
  selectorZReadDelta_antitone hδzh
    (selectorZWriteContraction_antitone hΛ hB hB_nonneg) hδw

/-- `δz j → 0` when its three summands do (the budget-satisfiability evidence). -/
lemma selectorZReadDelta_tendsto_zero
    {Λ Bz0 δw δzh : ℕ → ℝ}
    (hδzh : Tendsto δzh atTop (𝓝 0))
    (hctr : Tendsto (selectorZWriteContraction Λ Bz0) atTop (𝓝 0))
    (hδw : Tendsto δw atTop (𝓝 0)) :
    Tendsto (selectorZReadDelta Λ Bz0 δw δzh) atTop (𝓝 0) := by
  simpa [selectorZReadDelta] using hδzh.add (hctr.add hδw)

/-- With the M-decoding error also tending to zero, the total z/M headline error → 0, hence the
fixed budget `r_LE_U` is eventually satisfiable. -/
lemma selectorZReadDelta_add_error_tendsto_zero
    {Λ Bz0 δw δzh δM : ℕ → ℝ}
    (hδzh : Tendsto δzh atTop (𝓝 0))
    (hctr : Tendsto (selectorZWriteContraction Λ Bz0) atTop (𝓝 0))
    (hδw : Tendsto δw atTop (𝓝 0))
    (hδM : Tendsto δM atTop (𝓝 0)) :
    Tendsto (fun j => selectorZReadDelta Λ Bz0 δw δzh j + δM j) atTop (𝓝 0) := by
  simpa using (selectorZReadDelta_tendsto_zero hδzh hctr hδw).add hδM

/-- **Coordinatewise discharged z-read estimate.**  Direct consequence of `z_after_write_bound`
plus the z-write integral lower bound `Λ j`.  The radius still carries the true coordinate
mismatch `|z a i − M i|`; the scalar lemma below replaces it by the uniform `Bz0 j`.

Carried premises (all honest finite-window Reach facts):
* `hdom1`/`hgZ_cont`/`hgZ0` — the regularity/domain premises of `z_after_write_bound`;
* `hmix_stable_z_write` — mixture stability on the z-active half `[2πj+π/6, 2πj+π/2]`;
* `hz_post_write_drift` — z-drift on the read half `[2πj+π/2, 2πj+7π/6]`;
* `hwriteInt_lbd_z` — the instantiated `write_Z_integral_lower` lower bound `Λ j`. -/
theorem selector_MU_hzM_of_writeReach_coord
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (Λ δw δzh : ℕ → ℝ) (j : ℕ)
    (hdom1 : ∀ t ∈ Set.Icc (selectorZWriteStart j) (selectorZHold j), t ∈ sched.domain)
    (hgZ_cont : Continuous (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t))
    (hgZ0 : ∀ t ∈ Set.Icc (selectorZWriteStart j) (selectorZHold j),
      0 ≤ p.A * sol.α t * bGateZ p.L (sol.μ t) t)
    (hmix_stable_z_write :
      ∀ i, ∀ t ∈ Set.Icc (selectorZWriteStart j) (selectorZHold j),
        |selectorMixTarget branch sol.u sol.lam t i -
          selectorMixTarget branch sol.u sol.lam (selectorZHold j) i| ≤ δw j)
    (hz_post_write_drift :
      ∀ i, ∀ t ∈ Set.Icc (selectorZHold j) (selectorZReadEnd j),
        |sol.z t i - sol.z (selectorZHold j) i| ≤ δzh j)
    (hwriteInt_lbd_z :
      Λ j ≤ ∫ τ in selectorZWriteStart j..selectorZHold j,
          p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ) :
    ∀ i, ∀ t ∈ selectorReadWindow j,
      |sol.z t i - selectorMixTarget branch sol.u sol.lam (selectorZHold j) i|
        ≤ δzh j + (Real.exp (-(Λ j)) *
            |sol.z (selectorZWriteStart j) i -
              selectorMixTarget branch sol.u sol.lam (selectorZHold j) i| + δw j) := by
  intro i t ht
  have ht_post : t ∈ Set.Icc (selectorZHold j) (selectorZReadEnd j) :=
    selectorReadWindow_subset_zAfterWrite j ht
  have hz_after :=
    (z_after_write_bound (sol := sol) (s := i)
      (a := selectorZWriteStart j) (m := selectorZHold j) (b := selectorZReadEnd j)
      (M := selectorMixTarget branch sol.u sol.lam (selectorZHold j) i)
      (δw := δw j) (δzh := δzh j)
      (selectorZWriteStart_le_hold j) hdom1 hgZ_cont hgZ0
      (hmix_stable_z_write i) (hz_post_write_drift i)) t ht_post
  have hctr :
      Real.exp (-(∫ τ in selectorZWriteStart j..selectorZHold j,
            p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ)) *
          |sol.z (selectorZWriteStart j) i -
            selectorMixTarget branch sol.u sol.lam (selectorZHold j) i|
        ≤ Real.exp (-(Λ j)) *
          |sol.z (selectorZWriteStart j) i -
            selectorMixTarget branch sol.u sol.lam (selectorZHold j) i| :=
    exp_neg_mul_abs_le_exp_neg_lbd_mul hwriteInt_lbd_z le_rfl
  refine hz_after.trans ?_
  linarith [hctr]

/-- **Scalar headline form — the replacement for the carried `hzM`.**  Target
`Mtarget j i = selectorMixTarget branch sol.u sol.lam (2πj+π/2) i`, radius
`δz j = selectorZReadDelta Λ Bz0 δw δzh j`.  The extra premise `hz_start_mismatch_bound` is the
genuine finite-cycle box radius `|z (2πj+π/6) i − Mtarget j i| ≤ Bz0 j`, not a global assertion. -/
theorem selector_MU_hzM_of_writeReach
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (Λ Bz0 δw δzh : ℕ → ℝ) (j : ℕ)
    (hdom1 : ∀ t ∈ Set.Icc (selectorZWriteStart j) (selectorZHold j), t ∈ sched.domain)
    (hgZ_cont : Continuous (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t))
    (hgZ0 : ∀ t ∈ Set.Icc (selectorZWriteStart j) (selectorZHold j),
      0 ≤ p.A * sol.α t * bGateZ p.L (sol.μ t) t)
    (hmix_stable_z_write :
      ∀ i, ∀ t ∈ Set.Icc (selectorZWriteStart j) (selectorZHold j),
        |selectorMixTarget branch sol.u sol.lam t i -
          selectorMixTarget branch sol.u sol.lam (selectorZHold j) i| ≤ δw j)
    (hz_post_write_drift :
      ∀ i, ∀ t ∈ Set.Icc (selectorZHold j) (selectorZReadEnd j),
        |sol.z t i - sol.z (selectorZHold j) i| ≤ δzh j)
    (hz_start_mismatch_bound :
      ∀ i, |sol.z (selectorZWriteStart j) i -
          selectorMixTarget branch sol.u sol.lam (selectorZHold j) i| ≤ Bz0 j)
    (hwriteInt_lbd_z :
      Λ j ≤ ∫ τ in selectorZWriteStart j..selectorZHold j,
          p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ) :
    ∀ i, ∀ t ∈ selectorReadWindow j,
      |sol.z t i -
        selectorMixTarget branch sol.u sol.lam
          ((2 : ℝ) * Real.pi * (j : ℝ) + Real.pi / 2) i|
        ≤ selectorZReadDelta Λ Bz0 δw δzh j := by
  intro i t ht
  have hcoord :
      |sol.z t i - selectorMixTarget branch sol.u sol.lam (selectorZHold j) i|
        ≤ δzh j + (Real.exp (-(Λ j)) *
            |sol.z (selectorZWriteStart j) i -
              selectorMixTarget branch sol.u sol.lam (selectorZHold j) i| + δw j) :=
    selector_MU_hzM_of_writeReach_coord (sol := sol) (Λ := Λ) (δw := δw) (δzh := δzh) (j := j)
      hdom1 hgZ_cont hgZ0 hmix_stable_z_write hz_post_write_drift hwriteInt_lbd_z i t ht
  have hmul :
      Real.exp (-(Λ j)) *
          |sol.z (selectorZWriteStart j) i -
            selectorMixTarget branch sol.u sol.lam (selectorZHold j) i|
        ≤ Real.exp (-(Λ j)) * Bz0 j :=
    mul_le_mul_of_nonneg_left (hz_start_mismatch_bound i) (le_of_lt (Real.exp_pos (-(Λ j))))
  have htarget :
      selectorMixTarget branch sol.u sol.lam
          ((2 : ℝ) * Real.pi * (j : ℝ) + Real.pi / 2) i
        = selectorMixTarget branch sol.u sol.lam (selectorZHold j) i := rfl
  rw [htarget]
  refine hcoord.trans ?_
  dsimp [selectorZReadDelta, selectorZWriteContraction]
  linarith [hmul]

end Ripple.BoundedUniversality.BGP
