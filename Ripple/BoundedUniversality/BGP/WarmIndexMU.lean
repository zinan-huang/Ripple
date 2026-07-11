/-
Ripple.BoundedUniversality.BGP.WarmIndexMU
----------------------
The warm-index data layer for the `htracking_inputs` wiring of the de-axiom
warmed headline (Option A).

The exposure-weighted reserve (`mu_weighted_reserve_of_warm` +
`EpsWarmBound.mu_xi_warm_of_clock_expEps`) closes only after a per-input warm-up
shift `mWarm w ~ N w` that suppresses the residual by `B^(-N w)`.  Here:

* `N w = inputDepthU w (+ C_U buffer)` — the initial structural exposure depth of
  the encoded input (max over coordinates of `depthU (cU w) 0`), NOT `Nat.log w`.
* `warmCyclesU` pays the ε and χ linear warm rates (`Nat.ceil` of `N·log B / rate`)
  and the κ cascade obligation (supplied as `kappaWarmCycles`, the explicit
  cascade lower-bound supplier consumed by `ClockWarmBounds.dynKappa_warm_bound`).
* the warmed schedules read `dynKappa/dynChi` at the shifted index `mWarm w + j`.

Design cross-checked with the repo-connected channel (pbook1, R-WARMIDX); the
arithmetic/data is verified here by build.  The remaining wiring (the producer
discharges + the shifted `PhaseSchedule` + the warm-phase `hinit_weighted`) sits
on top of this data layer.
-/

import Ripple.BoundedUniversality.BGP.MachineInstance
import Ripple.BoundedUniversality.BGP.DynamicGate

namespace Ripple.BoundedUniversality.BGP

noncomputable section

namespace MachineInstance

/-- The universal orbit for input `w`. -/
def cU (w : ℕ) : ℕ → UConf :=
  fun j => M_U.step^[j] (M_U.init w)

/-- Coordinate exposure height at cycle `j` (the height schedule feeding the
reserve; `Int.toNat` is harmless since `depthU` is a stack length or `0`). -/
def depthHeightU (w j : ℕ) (i : Fin d_U) : ℕ :=
  Int.toNat (depthU (cU w) j i)

/-- Initial exposure depth of the encoded input: the max initial stack-depth
exposure over all coordinates.  This is the analog "input length" `N` for the
reserve, NOT `Nat.log w`. -/
def inputDepthU (w : ℕ) : ℕ :=
  Finset.univ.sup (fun i : Fin d_U => depthHeightU w 0 i)

/-- Reserve input length, with the one-step growth buffer `C_U` (use when the
growth lemma is `depth(j+1) ≤ inputDepth + C·(j+1)`). -/
def inputLenU (C_U : ℕ) (w : ℕ) : ℕ :=
  inputDepthU w + C_U

end MachineInstance

/-- Bundle of the warm-up parameters: base `B`, clock rates `cμ`/`cα`, logical
cycle period, gate level `L`, the depth buffer `C_U`, and the κ cascade warm-cycle
supplier. -/
structure WarmConfig where
  A : ℝ
  B : ℝ
  cμ : ℝ
  cα : ℝ
  period : ℝ
  L : ℕ
  C_U : ℕ
  /-- κ cascade warm-cycle supplier (the lower-bound index for
  `dynKappa_warm_bound`'s explicit cascade hypothesis). -/
  kappaWarmCycles : ℕ → ℕ

namespace WarmConfig

/-- Epsilon warm rate `cμ·period` (binding among ε/χ for the checked-in params). -/
def epsWarmRate (W : WarmConfig) : ℝ := W.cμ * W.period

/-- Chi warm rate `2π·(cμ·2^{-L} − cα)`. -/
def chiWarmRate (W : WarmConfig) : ℝ :=
  2 * Real.pi * (W.cμ * (1 / 2 : ℝ) ^ W.L - W.cα)

/-- The common linear warm rate for the ε and χ payments. -/
def epsChiWarmRate (W : WarmConfig) : ℝ :=
  min W.epsWarmRate W.chiWarmRate

/-- Linear warm cycles paying both ε and χ (does not pay the κ cascade). -/
def epsChiWarmCycles (W : WarmConfig) (N : ℕ) : ℕ :=
  Nat.ceil (((N : ℝ) * Real.log W.B) / W.epsChiWarmRate)

/-- Final warm cycles: pay ε, χ, and κ. -/
def warmCyclesU (W : WarmConfig) (N : ℕ) : ℕ :=
  max (W.epsChiWarmCycles N) (W.kappaWarmCycles N)

/-- Input-dependent warm-up shift `mWarm w` for the universal machine. -/
def mWarmU (W : WarmConfig) (w : ℕ) : ℕ :=
  W.warmCyclesU (MachineInstance.inputLenU W.C_U w)

/-- Warmed cycle index: logical cycle `j` is physical defect cycle `mWarm w + j`. -/
def warmCycleIndexU (W : WarmConfig) (w j : ℕ) : ℕ :=
  W.mWarmU w + j

/-- Warmed κ schedule: `dynKappa` read at the shifted index. -/
def kappaWarmU (W : WarmConfig) (w j : ℕ) : ℝ :=
  dynKappa W.A W.L W.cμ W.cα (W.warmCycleIndexU w j)

/-- Warmed χ schedule: `dynChi` read at the shifted index. -/
def chiWarmU (W : WarmConfig) (w j : ℕ) : ℝ :=
  dynChi W.A W.L W.cμ W.cα (W.warmCycleIndexU w j)

end WarmConfig

end

end Ripple.BoundedUniversality.BGP
