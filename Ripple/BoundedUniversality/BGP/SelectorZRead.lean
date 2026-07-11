import Ripple.BoundedUniversality.BGP.SelectorFinalAssembly
import Ripple.BoundedUniversality.BGP.SelectorTubeWiring

/-!
Ripple.BoundedUniversality.BGP.SelectorZRead
------------------------
The z-read tube building blocks (ChatGPT `life`, 2026-06-15) toward the CORRECT replacement of the
mis-stated `hztube_of_utube` and the `hinit_weighted` discharge.

ChatGPT's faithfulness catch: the carried `hztube_of_utube` of
`selector_MU_flag_read_of_tracking_concrete` is IMPOSSIBLE as stated — the z-channel tracks
`enc(j+1)` (the NEXT config: `z_hasDeriv` targets `selectorMixTarget`, and `hdiag` compares to
`enc(j+1)`), NOT `enc j`, and `zActiveWindow = Set.univ` asks z near `enc j` for ALL t.  The correct
shape is a post-z-write read-window theorem reading `enc(j+1)` on `[2πj+5π/6, 2πj+7π/6]`.

These are the clean algebraic + Reach building blocks for that correct theorem (the FinalAssembly
restructure is a separate senior-author decision):
- `z_after_write_bound` — the z-read half of `write_reach`, exposed (z near the mixTarget after the
  write contraction).
- `mixTarget_near_next` — the mixTarget tracks `enc(j+1)` (one-hot mix error + branch diagonal + u-tube).
- `z_read_near_next` — triangle: z near mixTarget + mixTarget near enc(j+1) ⇒ z near enc(j+1).
- `MUWeighted_init_of_initial_tube_and_early_drift` — discharges `hinit_weighted` from an initial
  config tube + the early `[0,π/6]` drift.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open Set

/-- **z-read half of `write_reach`, exposed.**  After the z-write contraction on `[a,m]` (z reaches
the mixTarget `M`), z stays near `M` on `[m,b]` up to the post-write drift `δzh`: for `t ∈ [m,b]`,
`|z t − M| ≤ δzh + (exp(−∫_a^m A·α·bGateZ)·|z a − M| + δw)`.  Triangle + `z_reach_bound`. -/
theorem z_after_write_bound
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (s : Fin d) {a m b M δw δzh : ℝ} (ham : a ≤ m)
    (hdom1 : ∀ t ∈ Icc a m, t ∈ sched.domain)
    (hgZ_cont : Continuous (fun t => p.A * sol.α t * bGateZ p.L (sol.μ t) t))
    (hgZ0 : ∀ t ∈ Icc a m, 0 ≤ p.A * sol.α t * bGateZ p.L (sol.μ t) t)
    (hstab : ∀ t ∈ Icc a m, |selectorMixTarget branch sol.u sol.lam t s - M| ≤ δw)
    (hzh : ∀ t ∈ Icc m b, |sol.z t s - sol.z m s| ≤ δzh) :
    ∀ t ∈ Icc m b, |sol.z t s - M| ≤
      δzh + (Real.exp (-(∫ τ in a..m, p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ))
        * |sol.z a s - M| + δw) := by
  intro t ht
  have hzm := sol.z_reach_bound s ham hdom1 hgZ_cont hgZ0 hstab
  calc |sol.z t s - M| ≤ |sol.z t s - sol.z m s| + |sol.z m s - M| := abs_sub_le _ _ _
    _ ≤ δzh + (Real.exp (-(∫ τ in a..m, p.A * sol.α τ * bGateZ p.L (sol.μ τ) τ))
          * |sol.z a s - M| + δw) := add_le_add (hzh t ht) hzm

/-- **z-read defect bound (contraction × box radius).**  Collapses the `z_after_write_bound`
output `|z − M| ≤ δzh + (κ·|z a − M| + δw)` to the per-cycle defect `δz := δzh + κ·Rz + δw` using
the carried z box radius `|z a − M| ≤ Rz`.  With the contraction `κ = exp(−I_Z) → 0`
(`write_contraction_tendsto_zero`), `δz → δzh + δw` — the carried hold/variation defects, exactly the
contract-status Reach.  This supplies the `hzM` (z near mixTarget) input to
`selector_MU_ztube_next_of_write`. -/
theorem z_read_defect_bound {zt za M δzh κ Rz δw : ℝ}
    (hafter : |zt - M| ≤ δzh + (κ * |za - M| + δw)) (hRz : |za - M| ≤ Rz) (hκ0 : 0 ≤ κ) :
    |zt - M| ≤ δzh + κ * Rz + δw := by
  have hcontr : κ * |za - M| ≤ κ * Rz := mul_le_mul_of_nonneg_left hRz hκ0
  linarith

/-- **The mixTarget tracks the NEXT encoded config.**  `|mixTarget − enc(j+1)| ≤ εmix + mult·ρ`
from the one-hot mixture error (`|mixTarget − A_vstar(u)| ≤ εmix`), the branch diagonal
(`|A_vstar(u) − enc(j+1)| ≤ mult·|u − enc j|`), and the u-tube (`|u − enc j| ≤ ρ`).  Pure algebra. -/
theorem mixTarget_near_next {M Av encJ encNext uval εmix mult ρ : ℝ}
    (hmult : 0 ≤ mult) (hmix : |M - Av| ≤ εmix)
    (hdiag : |Av - encNext| ≤ mult * |uval - encJ|) (hutube : |uval - encJ| ≤ ρ) :
    |M - encNext| ≤ εmix + mult * ρ := by
  calc |M - encNext| ≤ |M - Av| + |Av - encNext| := abs_sub_le _ _ _
    _ ≤ εmix + mult * |uval - encJ| := add_le_add hmix hdiag
    _ ≤ εmix + mult * ρ := by
        have := mul_le_mul_of_nonneg_left hutube hmult; linarith

/-- **z near the next config (the z-read tube).**  Triangle: `|z − enc(j+1)| ≤ ρ` from
`|z − M| ≤ δz` (z near mixTarget, `z_after_write_bound`) and `|M − enc(j+1)| ≤ δM`
(`mixTarget_near_next`), with the radius budget `δz + δM ≤ ρ`. -/
theorem z_read_near_next {z M encNext δz δM ρ : ℝ}
    (hzM : |z - M| ≤ δz) (hM : |M - encNext| ≤ δM) (hbudget : δz + δM ≤ ρ) :
    |z - encNext| ≤ ρ := by
  calc |z - encNext| ≤ |z - M| + |M - encNext| := abs_sub_le _ _ _
    _ ≤ δz + δM := add_le_add hzM hM
    _ ≤ ρ := hbudget

/-- **`hinit_weighted` discharge.**  `MUWeighted 0` from an initial config tube
`|u 0 − enc 0| ≤ r0` + the early `[0,π/6]` drift `|u(π/6) − u 0| ≤ drift0` + the budget
`k^(dep 0)·(r0 + drift0) ≤ Wbound 0`.  (The two extra facts are smaller contract-status
hypotheses — `SelectorDynSol` alone does not tie `init_u` to `enc 0`, per ChatGPT Q3.) -/
theorem MUWeighted_init_of_initial_tube_and_early_drift
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V p selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (enc : ℕ → Fin MachineInstance.d_U → ℝ) {k : ℝ} (hk : 1 < k)
    (dep : ℕ → Fin MachineInstance.d_U → ℤ) (Wbound : ℕ → Fin MachineInstance.d_U → ℝ)
    (r0 drift0 : Fin MachineInstance.d_U → ℝ)
    (hinit0 : ∀ i, |sol.u 0 i - enc 0 i| ≤ r0 i)
    (hdrift : ∀ i, |sol.u (Real.pi / 6) i - sol.u 0 i| ≤ drift0 i)
    (hW0 : ∀ i, k ^ dep 0 i * (r0 i + drift0 i) ≤ Wbound 0 i) :
    MUWeighted sol enc k dep Wbound 0 := by
  intro i
  have hk0 : (0 : ℝ) ≤ k := (zero_lt_one.trans hk).le
  have h0 : muBoundaryError sol enc 0 i = |sol.u (Real.pi / 6) i - enc 0 i| := by
    unfold muBoundaryError; norm_num
  have htri : muBoundaryError sol enc 0 i ≤ r0 i + drift0 i := by
    rw [h0]
    calc |sol.u (Real.pi / 6) i - enc 0 i|
        ≤ |sol.u (Real.pi / 6) i - sol.u 0 i| + |sol.u 0 i - enc 0 i| := abs_sub_le _ _ _
      _ ≤ drift0 i + r0 i := add_le_add (hdrift i) (hinit0 i)
      _ = r0 i + drift0 i := by ring
  exact (mul_le_mul_of_nonneg_left htri (zpow_nonneg hk0 _)).trans (hW0 i)

/-- The post-z-write **read window** of cycle `j`: `[2πj+5π/6, 2πj+7π/6]`, where the z-write
contraction has already driven `z` to the mixture (so `z` reads the NEXT config `enc(j+1)`).  The
correct replacement for the impossible `zActiveWindow = Set.univ`. -/
def selectorReadWindow (j : ℕ) : Set ℝ :=
  Set.Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6) (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6)

/-- **The next-config z-read tube (the CORRECT `hztube` replacement).**  On the post-z-write read
window of cycle `j`, the z-register is in the `UTube` of the NEXT encoded config `cfg (j+1)`,
discharged from: `z` near the mixTarget `M` (`hzM`, from `z_after_write_bound`) + `M` near
`enc(j+1)` (`hMnext`, from `mixTarget_near_next`) + the radius budget `δz + δM ≤ r_LE_U`.  Unlike the
impossible carried `hztube_of_utube` (z near `enc j` for ALL t), this is SATISFIABLE: the right
target (`enc(j+1)`) on the right (finite, post-write) window. -/
theorem selector_MU_ztube_next_of_write
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V p selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (cfg : ℕ → MachineInstance.UConf) (j : ℕ) (Mtarget : Fin MachineInstance.d_U → ℝ) {δz δM : ℝ}
    (hzM : ∀ i, ∀ t ∈ selectorReadWindow j, |sol.z t i - Mtarget i| ≤ δz)
    (hMnext : ∀ i, |Mtarget i
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1)) i| ≤ δM)
    (hbudget : δz + δM ≤ MachineInstance.r_LE_U) :
    ∀ t ∈ selectorReadWindow j,
      MachineInstance.UTube MachineInstance.r_LE_U (cfg (j + 1)) (sol.z t) := by
  intro t ht i
  exact z_read_near_next (hzM i t ht) (hMnext i) hbudget

/-- **Flag read from the next-config z-tube.**  Since `r_LE_U = 1/1000 ≤ 1/4`, the next-config
z-tube on the read window gives the halt-flag read `|z haltCoord − enc(j+1) haltCoord| ≤ 1/4` — the
margin the latch consumes.  The thin bridge from `selector_MU_ztube_next_of_write` to the flag. -/
theorem selector_MU_flag_read_next_of_ztube
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V p selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (cfg : ℕ → MachineInstance.UConf) (j : ℕ)
    (hztube : ∀ t ∈ selectorReadWindow j,
      MachineInstance.UTube MachineInstance.r_LE_U (cfg (j + 1)) (sol.z t)) :
    ∀ t ∈ selectorReadWindow j,
      |sol.z t MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1)) MachineInstance.haltCoordU| ≤ 1 / 4 := by
  intro t ht
  have h := hztube t ht MachineInstance.haltCoordU
  have hr : MachineInstance.r_LE_U ≤ 1 / 4 := by unfold MachineInstance.r_LE_U; norm_num
  exact le_trans h hr

/-- **All-cycle budget invariant by simultaneous induction.**  `MUWeighted j` holds for EVERY `j`,
from the initial bound (`MUWeighted 0`, via `MUWeighted_init_…`) and the per-cycle step
`MUWeighted j → MUWeighted (j+1)` — the latter is `mu_weighted_step` composed with the recurrence
engine producing `MURecur j` from `MUWeighted j` (the discharged margins).  This is the inductive
tube-closing core: combined with `selector_MU_hwin_of_weighted` it yields the u-tube on every gate
window. -/
theorem MUWeighted_all_of_init_step
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V p selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (enc : ℕ → Fin MachineInstance.d_U → ℝ) {k : ℝ} (hk : 1 < k)
    (dep delta : ℕ → Fin MachineInstance.d_U → ℤ)
    (η Wbound : ℕ → Fin MachineInstance.d_U → ℝ)
    (hdepth : ∀ j i, dep (j + 1) i = dep j i - delta j i)
    (hWstep : ∀ j i, Wbound j i + k ^ dep (j + 1) i * η j i ≤ Wbound (j + 1) i)
    (hinit : MUWeighted sol enc k dep Wbound 0)
    (hrecur : ∀ j, MUWeighted sol enc k dep Wbound j → MURecur sol enc k delta η j) :
    ∀ j, MUWeighted sol enc k dep Wbound j := by
  intro j
  induction j with
  | zero => exact hinit
  | succ n ih =>
      exact mu_weighted_step sol enc hk dep delta η Wbound hdepth hWstep n ih (hrecur n ih)

/-- **The all-cycle u-tube.**  From the all-cycle budget invariant (`MUWeighted j` for every `j`)
plus the per-cycle hold drift and radius budget, the held config `sol.u t` is in the `UTube` of
`cfg j` on EVERY gate window.  Combines `MUWeighted_all_of_init_step`'s output with
`selector_MU_hwin_of_weighted` (the `MUWeighted j i` IS the weighted bound `hw` it needs). -/
theorem selector_MU_utube_all
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V p selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (cfg : ℕ → MachineInstance.UConf) {k : ℝ} (hk1 : 1 < k)
    (dep : ℕ → Fin MachineInstance.d_U → ℤ) (Wbound : ℕ → Fin MachineInstance.d_U → ℝ) {εhold : ℝ}
    (hMU : ∀ j, MUWeighted sol
      (fun j => MachineInstance.stackMachineEncodingU.enc (cfg j)) k dep Wbound j)
    (hhold : ∀ (j : ℕ), ∀ i, ∀ t ∈ Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi / 2),
        |sol.u t i - sol.u (2 * Real.pi * (j : ℝ) + Real.pi / 6) i| ≤ εhold)
    (hradius : ∀ j, ∀ i, Wbound j i / k ^ dep j i + εhold ≤ MachineInstance.r_LE_U) :
    ∀ (j : ℕ), ∀ t ∈ Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6) (2 * Real.pi * (j : ℝ) + Real.pi / 2),
      MachineInstance.UTube MachineInstance.r_LE_U (cfg j) (sol.u t) := by
  intro j
  exact selector_MU_hwin_of_weighted sol cfg hk1 dep Wbound j (hhold j) (hradius j) (hMU j)

/-- **The all-cycle corrected flag read (the `hztube`-path headline conclusion).**  On every
post-z-write read window, the halt flag reads `|z haltCoord − enc(j+1) haltCoord| ≤ 1/4`, from the
next-config z-tube (`selector_MU_ztube_next_of_write`) + the flag bridge.  Carries the SATISFIABLE
z-write facts (`Mtarget`/`δz`/`δM`/budget) per cycle — the contract-status Reach analog, in the
CORRECT `enc(j+1)`-on-read-window form (replacing the impossible `hztube_of_utube`).  This is the
dischargeable flag read the corrected headline consumes. -/
theorem selector_MU_flag_read_all_next
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V p selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (cfg : ℕ → MachineInstance.UConf) (Mtarget : ℕ → Fin MachineInstance.d_U → ℝ) (δz δM : ℕ → ℝ)
    (hzM : ∀ j, ∀ i, ∀ t ∈ selectorReadWindow j, |sol.z t i - Mtarget j i| ≤ δz j)
    (hMnext : ∀ j, ∀ i, |Mtarget j i
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1)) i| ≤ δM j)
    (hbudget : ∀ j, δz j + δM j ≤ MachineInstance.r_LE_U) :
    ∀ (j : ℕ), ∀ t ∈ selectorReadWindow j,
      |sol.z t MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1)) MachineInstance.haltCoordU| ≤ 1 / 4 := by
  intro j
  exact selector_MU_flag_read_next_of_ztube sol cfg j
    (selector_MU_ztube_next_of_write sol cfg j (Mtarget j) (hzM j) (hMnext j) (hbudget j))

/-- **The recurrence → `MURecur` bridge (uniform unit depth).**  With the concrete unit-decrement
schedule `muDeltaSchema` (`delta j i = 1`), the per-coordinate weight `k^(delta j i) = k`, so the
recurrence's UNIFORM `mult = k` matches `MURecur` exactly.  Given the per-cycle boundary-error
recurrence in `muBoundaryError` form (from `selector_MU_recur_concrete` with `tStart j = 2πj+π/6`,
`tEnd j = 2π(j+1)+π/6`, `mult = k`), this produces `MURecur sol enc k muDeltaSchema η j`. -/
theorem mu_recur_of_concrete
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V p selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (enc : ℕ → Fin MachineInstance.d_U → ℝ) (j : ℕ) {k : ℝ} (η : ℕ → Fin MachineInstance.d_U → ℝ)
    (hrec : ∀ i, muBoundaryError sol enc (j + 1) i
      ≤ k * muBoundaryError sol enc j i + η j i) :
    MURecur sol enc k muDeltaSchema η j := by
  intro i
  have hk1 : k ^ (muDeltaSchema j i) = k := by
    simp only [muDeltaSchema]; exact zpow_one k
  rw [hk1]
  exact hrec i

/-- **The branch diagonal for M_U, DISCHARGED concretely (#3).**  From the proven
`branchU_contract_clause` (the `BranchContractClause` for `branchU`) via `.diagonal`:
`|evalBranch (branchU (localViewU c)) Z i − enc (M_U.step c) i| ≤ coordMultiplier c i · |Z i − enc c i|`,
bounded by a UNIFORM `mult` via the carried `coordMultiplier c i ≤ mult` (satisfiable with `mult = k`:
a stack step changes depth by ≤ 1, so `coordMultiplier = k^coordDelta ≤ k`).  This is the recurrence's
`hdiag`, discharged from the branch contract rather than assumed. -/
theorem selector_MU_hdiag (c : MachineInstance.UConf) (Z : Fin MachineInstance.d_U → ℝ) {mult : ℝ}
    (hmultbound : ∀ i, MachineInstance.stackMachineEncodingU.coordMultiplier c i ≤ mult) :
    ∀ i, |BranchData.evalBranch (MachineInstance.branchU (MachineInstance.localViewU c)) Z i
        - MachineInstance.stackMachineEncodingU.enc (MachineInstance.M_U.step c) i|
      ≤ mult * |Z i - MachineInstance.stackMachineEncodingU.enc c i| := by
  intro i
  calc |BranchData.evalBranch (MachineInstance.branchU (MachineInstance.localViewU c)) Z i
          - MachineInstance.stackMachineEncodingU.enc (MachineInstance.M_U.step c) i|
      ≤ MachineInstance.stackMachineEncodingU.coordMultiplier c i
          * |Z i - MachineInstance.stackMachineEncodingU.enc c i| :=
        (MachineInstance.branchU_contract_clause c).diagonal Z i
    _ ≤ mult * |Z i - MachineInstance.stackMachineEncodingU.enc c i| :=
        mul_le_mul_of_nonneg_right (hmultbound i) (abs_nonneg _)

/-- **`hMnext` for M_U, DISCHARGED.**  The mixTarget at the write reference time `th` is within
`εmix + mult·r_LE_U` of the NEXT encoded config `enc (M_U.step c)`, combining the one-hot mixture
error (`hmix`, the gate-phase content) + the branch diagonal (`selector_MU_hdiag`, from #3) + the
u-tube at `th` (`hutube`) via `mixTarget_near_next`.  This is the `hMnext` input to the z-read tube
(`selector_MU_ztube_next_of_write`), discharged for M_U modulo the carried gate-phase mix error. -/
theorem selector_MU_hMnext
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V p selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (c : MachineInstance.UConf) (th : ℝ) {εmix mult : ℝ} (hmult0 : 0 ≤ mult)
    (hmultbound : ∀ i, MachineInstance.stackMachineEncodingU.coordMultiplier c i ≤ mult)
    (hmix : ∀ i, |selectorMixTarget branch sol.u sol.lam th i
        - BranchData.evalBranch (MachineInstance.branchU (MachineInstance.localViewU c))
            (sol.u th) i| ≤ εmix)
    (hutube : ∀ i, |sol.u th i - MachineInstance.stackMachineEncodingU.enc c i|
        ≤ MachineInstance.r_LE_U) :
    ∀ i, |selectorMixTarget branch sol.u sol.lam th i
        - MachineInstance.stackMachineEncodingU.enc (MachineInstance.M_U.step c) i|
      ≤ εmix + mult * MachineInstance.r_LE_U := by
  intro i
  exact mixTarget_near_next hmult0 (hmix i)
    (selector_MU_hdiag c (sol.u th) hmultbound i) (hutube i)

/-- **The corrected all-cycle flag read, ASSEMBLED.**  Composes the corrected z-read path end to
end: per cycle, `selector_MU_hMnext` gives `hMnext` (mixTarget → `enc(j+1)`, from #3 + gate εmix +
u-tube), the carried z-read gives `hzM` (z near mixTarget), and `selector_MU_flag_read_all_next`
turns these into the halt-flag read on every post-write read window.  Carries ONLY the shared
contract-status Reach (gate εmix, the z-read defect `δz`, the u-tube, `coordMultiplier ≤ mult`, the
orbit property `cfg(j+1) = M_U.step (cfg j)`) — the facts the contract itself carries.  The
unsatisfiable `hztube_of_utube` is fully replaced. -/
theorem selector_MU_flag_read_corrected
    {V : Type} [Fintype V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V p selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (cfg : ℕ → MachineInstance.UConf)
    (hcfg : ∀ j, cfg (j + 1) = MachineInstance.M_U.step (cfg j))
    {mult : ℝ} (hmult0 : 0 ≤ mult) (εmix δz : ℕ → ℝ)
    (hmultbound : ∀ j, ∀ i, MachineInstance.stackMachineEncodingU.coordMultiplier (cfg j) i ≤ mult)
    (hmix : ∀ (j : ℕ), ∀ i, |selectorMixTarget branch sol.u sol.lam (2 * Real.pi * (j : ℝ) + Real.pi / 2) i
        - BranchData.evalBranch (MachineInstance.branchU (MachineInstance.localViewU (cfg j)))
            (sol.u (2 * Real.pi * (j : ℝ) + Real.pi / 2)) i| ≤ εmix j)
    (hutube : ∀ (j : ℕ), ∀ i, |sol.u (2 * Real.pi * (j : ℝ) + Real.pi / 2) i
        - MachineInstance.stackMachineEncodingU.enc (cfg j) i| ≤ MachineInstance.r_LE_U)
    (hzM : ∀ (j : ℕ), ∀ i, ∀ t ∈ selectorReadWindow j,
        |sol.z t i - selectorMixTarget branch sol.u sol.lam (2 * Real.pi * (j : ℝ) + Real.pi / 2) i|
          ≤ δz j)
    (hbudget : ∀ j, δz j + (εmix j + mult * MachineInstance.r_LE_U) ≤ MachineInstance.r_LE_U) :
    ∀ (j : ℕ), ∀ t ∈ selectorReadWindow j,
      |sol.z t MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc (cfg (j + 1)) MachineInstance.haltCoordU| ≤ 1 / 4 := by
  refine selector_MU_flag_read_all_next sol cfg
    (fun j => selectorMixTarget branch sol.u sol.lam (2 * Real.pi * (j : ℝ) + Real.pi / 2))
    δz (fun j => εmix j + mult * MachineInstance.r_LE_U) hzM ?_ hbudget
  intro j i
  have hMnext_j := selector_MU_hMnext sol (cfg j) (2 * Real.pi * (j : ℝ) + Real.pi / 2)
    hmult0 (hmultbound j) (hmix j) (hutube j) i
  rwa [hcfg j]

end Ripple.BoundedUniversality.BGP
