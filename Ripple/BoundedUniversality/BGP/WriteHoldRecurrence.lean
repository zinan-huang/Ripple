import Ripple.BoundedUniversality.BGP.DirectTrackingInduction
import Ripple.BoundedUniversality.BGP.GeometricDecayRecurrence
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Ripple.BoundedUniversality.BGP.WriteHoldRecurrence
-------------------------------

Endpoint geometric decay from a one-cycle recurrence sampled at the
**write-hold** time `selectorMUWriteHoldTime j = 2πj + π/2` (NOT at the write
start `2πj + π/6`).

**Why the hold time.**  The recurrence at `writeStart` fails: the inter-read
z-source cap contains the half-phase growth term `exp(50·writeStart(j+1))`
(`selector_replicator_gateZ_integrand_le_halfphase_exp`), which *grows* in `j`
and cannot be beaten at the write start.  Sampling at `writeHold` instead
routes that growing cap through the early-write contraction
`exp(-selectorEarlyWriteIntLower(j+1))` of the *next* cycle, which is
doubly-exponentially small — the growth is annihilated with a full geometric
margin to spare (`selectorEarlyWriteIntLower_succ_ge_interRead_growth`).

**The recurrence.**  With
`holdErr(j,i) = |z(writeHoldTime j, i) - enc(cfg(j+1), i)|`, one cycle
(`hold j → read j → writeStart (j+1) → hold (j+1)`) gives

  `holdErr(j+1) ≤ q(j)·holdErr(j) + r(j)`,

where `q(j) = exp(-(earlyWriteInt(j+1) + settledWriteInt(j)))` (the combined
settled-write and early-write contraction — `≤ e⁻³ < e⁻²` uniformly) and
`r(j) = exp(-earlyWriteInt(j+1))·(δw(j) + Dinter(j) + Benc) + δearly(j+1)`
(the settled mixture radius, the *crude growing* inter-read cap killed by the
early contraction, the one-step encoding jump, and the early-write source).
`GeometricDecayRecurrence.geometric_bound_of_contracting_recurrence` then
yields `holdErr(j) ≤ C·exp(-2j)` with `lam = 2 > log B_U = log 6`.

**Transport.**  The hold-error decay is transported to the write-start
endpoints consumed by `Paper3F1EndpointGeometricInputs`
(`HeadlineUnconditional`, sorry 3426):

* `hzerr_geo`: `|z(ws(j+1)) - enc(cfg(j+1))| ≤ (C + Cw + Cf)·exp(-2j)` via the
  settled read endpoint plus a *fine* (geometric) inter-read displacement;
* `hzu_geo`: `|u(ws(j+1)) - z(ws(j+1))| ≤ (e⁸·CB + Cs)·exp(-2j)` via the
  inter-read u-active kernel mass (`selectorInterReadUActiveMassLower`, which
  dominates `2j - 8`, see `selectorInterReadUActiveMassLower_ge_linear`).

**Where the hypotheses come from.**  All dynamical inputs enter in the exact
shapes produced by the existing settled-window lemmas:

* `hsettle` — `z_write_settled_endpoint` with `Bz j := holdErr z cfg j i`
  (the start bound is then `le_rfl`) and
  `Λ := selectorSettledWriteIntLower` via
  `selector_settled_writeIntegral_lower_lbd_repl`; the radius `δw` is
  `weightedMixRadius` via `hmix_settled_of_weighted_tracking`
  (`DirectTrackingInduction`), with decay from concentration;
* `hearly` — the same Duhamel bound (`z_after_write_bound_repl` shape) on the
  early write window `[ws(j+1), hold(j+1)]`, with
  `selector_early_writeIntegral_lower_lbd_repl` for the mass;
* `hinter` (crude cap, may grow like `exp(50·ws(j+1))`) — the raw inter-read
  z-source estimate through the half-phase envelope;
* `htrans` — `selector_replicator_writeStart_zu_of_read_zu_and_interRead_source`
  with the kernel mass lower-bounded by `selectorInterRead_kernel_le_uActiveMass`.

Everything in this file is elementary real analysis and explicit numerics; no
`sorry`, no axioms.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance

/-! ## The hold-time tracking error -/

/-- Hold-time tracking error toward the *next* configuration:
`|z(writeHoldTime j) - enc(cfg (j+1))|`.  At the hold time `2πj + π/2` the
selector has settled and the write target of cycle `j` is `cfg (j+1)`, so this
is the natural per-cycle state variable. -/
def holdErr (z : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf) (j : ℕ) (i : Fin d_U) : ℝ :=
  |z (selectorMUWriteHoldTime j) i - stackMachineEncodingU.enc (cfg (j + 1)) i|

theorem holdErr_nonneg (z : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf)
    (j : ℕ) (i : Fin d_U) : 0 ≤ holdErr z cfg j i :=
  abs_nonneg _

/-- `holdErr` is the `trackingErr` of `DirectTrackingInduction` at the
hold-time marks, tracking the shifted configuration orbit. -/
theorem holdErr_eq_trackingErr (z : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf)
    (j : ℕ) (i : Fin d_U) :
    holdErr z cfg j i =
      trackingErr z (fun m => cfg (m + 1)) selectorMUWriteHoldTime j i := rfl

/-! ## Numeric core: the early-write contraction beats the inter-read growth

`bgpParamsBase` (`A=1, L=1, cμ=1000, cα=300`): the early-write integral lower
bound is `selectorEarlyWriteIntLower (j+1) = (π/4)·exp(s(j+1) + c₀)` with
`s = 2π(300 - 1000·rmax) ≥ 300π` and `c₀ ≥ 0` (`rmax = (1-√2/2)/2 ≤ 3/20`).
This double exponential dominates the singly-exponential inter-read growth
exponent `50·writeStart(j+1) = 100π(j+1) + 25π/3` with a `2j` margin. -/

/-- **The rate inequality (review Q4070).**  The early-write contraction
integral of cycle `j+1` dominates the inter-read half-phase growth exponent
with a full geometric margin:
`50·writeStart(j+1) + 2j ≤ earlyWriteIntLower(j+1)`. -/
theorem selectorEarlyWriteIntLower_succ_ge_interRead_growth (j : ℕ) :
    50 * selectorMUWriteStartTime (j + 1) + 2 * (j : ℝ) ≤
      selectorEarlyWriteIntLower (j + 1) := by
  set rmax : ℝ := (1 - Real.sqrt 2 / 2) / 2 with hrmax
  set s : ℝ := 2 * Real.pi * ((300 : ℝ) - (1000 : ℝ) * rmax) with hs
  set c0 : ℝ := (300 : ℝ) * (Real.pi / 4) -
    (1000 : ℝ) * (Real.pi / 2) * rmax with hc0
  have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hπ315 : Real.pi < 3.15 := Real.pi_lt_d2
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  -- `√2 ≥ 7/5`, hence `rmax ≤ 3/20`
  have hsqrt_ge : (7 / 5 : ℝ) ≤ Real.sqrt 2 := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hsqr : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
      rw [Real.sq_sqrt] <;> norm_num
    nlinarith
  have hrmax_le : rmax ≤ (3 / 20 : ℝ) := by
    rw [hrmax]
    linarith
  -- closed exponential form at index `j+1`
  have hrw : selectorEarlyWriteIntLower (j + 1) =
      (Real.pi / 4) * Real.exp (s * ((j : ℝ) + 1) + c0) := by
    unfold selectorEarlyWriteIntLower selectorMUEarlyWriteSubStart
      selectorMUWriteHoldTime
    rw [← Real.exp_add, hs, hc0, hrmax]
    push_cast
    ring_nf
  -- rate and offset bounds
  have hπrmax : 0 ≤ Real.pi * ((3 / 20 : ℝ) - rmax) :=
    mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hrmax_le)
  have hc0_nonneg : 0 ≤ c0 := by
    rw [hc0]
    nlinarith [hπrmax]
  have hs_ge : 2 * Real.pi * 150 ≤ s := by
    rw [hs]
    nlinarith [hπrmax]
  have hs_nonneg : 0 ≤ s := by nlinarith [hs_ge, Real.pi_pos]
  -- the exponent dominates `300π(j+1)`
  have hX0 : (0 : ℝ) ≤ (j : ℝ) + 1 := by linarith
  have hx_ge : 300 * Real.pi * ((j : ℝ) + 1) ≤ s * ((j : ℝ) + 1) + c0 := by
    have hmul := mul_le_mul_of_nonneg_right hs_ge hX0
    nlinarith [hmul, hc0_nonneg]
  -- `(π/4)·exp(x) ≥ (π/4)·x ≥ 75π²(j+1) ≥ 675(j+1)`
  have hexp_ge : s * ((j : ℝ) + 1) + c0 ≤
      Real.exp (s * ((j : ℝ) + 1) + c0) := by
    have h := Real.add_one_le_exp (s * ((j : ℝ) + 1) + c0)
    linarith
  have hπsq : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [hπ3]
  have hΛ_ge : 675 * ((j : ℝ) + 1) ≤ selectorEarlyWriteIntLower (j + 1) := by
    rw [hrw]
    have h1 : 300 * Real.pi * ((j : ℝ) + 1) ≤
        Real.exp (s * ((j : ℝ) + 1) + c0) := le_trans hx_ge hexp_ge
    have h2 : (Real.pi / 4) * (300 * Real.pi * ((j : ℝ) + 1)) ≤
        (Real.pi / 4) * Real.exp (s * ((j : ℝ) + 1) + c0) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have hid : (Real.pi / 4) * (300 * Real.pi * ((j : ℝ) + 1)) =
        75 * (Real.pi ^ 2 * ((j : ℝ) + 1)) := by ring
    have h9 : 9 * ((j : ℝ) + 1) ≤ Real.pi ^ 2 * ((j : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hπsq hX0
    rw [hid] at h2
    linarith
  -- the left side is at most `675(j+1)`
  have hLHS : 50 * selectorMUWriteStartTime (j + 1) + 2 * (j : ℝ) ≤
      675 * ((j : ℝ) + 1) := by
    unfold selectorMUWriteStartTime
    push_cast
    have hprod : 0 ≤ (3.15 - Real.pi) * (j : ℝ) :=
      mul_nonneg (by linarith) hj0
    nlinarith [hprod, hπ315, hj0]
  linarith

/-- The early-write contraction alone already beats the geometric envelope:
`exp(-earlyWriteInt(j+1)) ≤ exp(-2j)`. -/
theorem exp_neg_selectorEarlyWriteIntLower_succ_le_geometric (j : ℕ) :
    Real.exp (-(selectorEarlyWriteIntLower (j + 1))) ≤
      Real.exp (-(2 : ℝ) * (j : ℝ)) := by
  apply Real.exp_le_exp.mpr
  have h := selectorEarlyWriteIntLower_succ_ge_interRead_growth j
  have hws : 0 ≤ selectorMUWriteStartTime (j + 1) :=
    selectorMUWriteStartTime_nonneg (j + 1)
  linarith

/-- **Growth annihilation.**  The early-write contraction kills the
inter-read half-phase growth `exp(50·writeStart(j+1))` with a full geometric
factor to spare.  This is the reason the recurrence must be run at
`writeHold`, not `writeStart`. -/
theorem exp_neg_selectorEarlyWriteIntLower_mul_growth_le_geometric (j : ℕ) :
    Real.exp (-(selectorEarlyWriteIntLower (j + 1))) *
      Real.exp (50 * selectorMUWriteStartTime (j + 1)) ≤
      Real.exp (-(2 : ℝ) * (j : ℝ)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := selectorEarlyWriteIntLower_succ_ge_interRead_growth j
  linarith

theorem three_le_selectorEarlyWriteIntLower_succ (j : ℕ) :
    (3 : ℝ) ≤ selectorEarlyWriteIntLower (j + 1) := by
  have h := selectorEarlyWriteIntLower_succ_ge_interRead_growth j
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hws : Real.pi / 6 ≤ selectorMUWriteStartTime (j + 1) := by
    unfold selectorMUWriteStartTime
    have h0 : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hπj : 0 ≤ Real.pi * ((j + 1 : ℕ) : ℝ) :=
      mul_nonneg Real.pi_pos.le h0
    nlinarith [hπj]
  linarith [Real.pi_gt_three]

/-! ## The one-cycle contraction and source -/

/-- Combined one-cycle hold contraction: the settled-write contraction of
cycle `j` followed by the early-write contraction of cycle `j+1`.  Both
integral lower bounds are doubly exponential in `j`, so this factor is
super-exponentially small; uniformly it is below `e⁻³ < e⁻²`. -/
def selectorHoldContraction (j : ℕ) : ℝ :=
  Real.exp (-(selectorEarlyWriteIntLower (j + 1) +
    selectorSettledWriteIntLower j))

theorem selectorHoldContraction_pos (j : ℕ) :
    0 < selectorHoldContraction j :=
  Real.exp_pos _

theorem selectorHoldContraction_eq_mul (j : ℕ) :
    selectorHoldContraction j =
      Real.exp (-(selectorEarlyWriteIntLower (j + 1))) *
        Real.exp (-(selectorSettledWriteIntLower j)) := by
  unfold selectorHoldContraction
  rw [← Real.exp_add]
  congr 1
  ring

/-- Uniform contraction bound `q₀ = e⁻³`. -/
theorem selectorHoldContraction_le_exp_neg_three (j : ℕ) :
    selectorHoldContraction j ≤ Real.exp (-(3 : ℝ)) := by
  unfold selectorHoldContraction
  apply Real.exp_le_exp.mpr
  have h1 := three_le_selectorEarlyWriteIntLower_succ j
  have h2 := (selectorSettledWriteIntLower_pos j).le
  linarith

/-- The contraction beats the geometric rate `lam = 2` strictly:
`q₀ = e⁻³ < e⁻² = exp(-lam)`. -/
theorem selectorHoldContraction_lt_exp_neg_two (j : ℕ) :
    selectorHoldContraction j < Real.exp (-(2 : ℝ)) :=
  lt_of_le_of_lt (selectorHoldContraction_le_exp_neg_three j)
    (Real.exp_lt_exp.mpr (by norm_num))

/-- One-cycle hold source: the early contraction applied to the settled
mixture radius `δw j`, the crude (possibly growing) inter-read displacement
cap `Dinter j`, and the encoding jump `Benc`, plus the early-write source
`δearly (j+1)`. -/
def holdSource (δw Dinter δearly : ℕ → ℝ) (Benc : ℝ) (j : ℕ) : ℝ :=
  Real.exp (-(selectorEarlyWriteIntLower (j + 1))) *
    (δw j + Dinter j + Benc) + δearly (j + 1)

/-- **The source is geometric at rate 2**, even though the inter-read cap
`Dinter` is allowed to *grow* like `exp(50·writeStart(j+1))`: the early-write
contraction annihilates the growth
(`exp_neg_selectorEarlyWriteIntLower_mul_growth_le_geometric`). -/
theorem holdSource_le_geometric
    {δw Dinter δearly : ℕ → ℝ} {Benc Cw Cd Ce : ℝ}
    (hBenc : 0 ≤ Benc) (hCd : 0 ≤ Cd)
    (hδw_nonneg : ∀ j, 0 ≤ δw j)
    (hδw : ∀ j, δw j ≤ Cw * Real.exp (-(2 : ℝ) * (j : ℝ)))
    (hDinter : ∀ j, Dinter j ≤
      Cd * Real.exp (50 * selectorMUWriteStartTime (j + 1)))
    (hδearly : ∀ j, δearly (j + 1) ≤ Ce * Real.exp (-(2 : ℝ) * (j : ℝ))) :
    ∀ j, holdSource δw Dinter δearly Benc j ≤
      (Cw + Cd + Benc + Ce) * Real.exp (-(2 : ℝ) * (j : ℝ)) := by
  intro j
  have hexp_nonneg : (0 : ℝ) ≤
      Real.exp (-(selectorEarlyWriteIntLower (j + 1))) := (Real.exp_pos _).le
  have h1 : Real.exp (-(selectorEarlyWriteIntLower (j + 1))) * δw j ≤
      Cw * Real.exp (-(2 : ℝ) * (j : ℝ)) := by
    have hexp_le_one : Real.exp (-(selectorEarlyWriteIntLower (j + 1))) ≤ 1 := by
      calc Real.exp (-(selectorEarlyWriteIntLower (j + 1)))
          ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr
              (by linarith [selectorEarlyWriteIntLower_pos (j + 1)])
        _ = 1 := Real.exp_zero
    calc Real.exp (-(selectorEarlyWriteIntLower (j + 1))) * δw j
        ≤ 1 * δw j := mul_le_mul_of_nonneg_right hexp_le_one (hδw_nonneg j)
      _ = δw j := one_mul _
      _ ≤ Cw * Real.exp (-(2 : ℝ) * (j : ℝ)) := hδw j
  have h2 : Real.exp (-(selectorEarlyWriteIntLower (j + 1))) * Dinter j ≤
      Cd * Real.exp (-(2 : ℝ) * (j : ℝ)) := by
    calc Real.exp (-(selectorEarlyWriteIntLower (j + 1))) * Dinter j
        ≤ Real.exp (-(selectorEarlyWriteIntLower (j + 1))) *
            (Cd * Real.exp (50 * selectorMUWriteStartTime (j + 1))) :=
          mul_le_mul_of_nonneg_left (hDinter j) hexp_nonneg
      _ = Cd * (Real.exp (-(selectorEarlyWriteIntLower (j + 1))) *
            Real.exp (50 * selectorMUWriteStartTime (j + 1))) := by ring
      _ ≤ Cd * Real.exp (-(2 : ℝ) * (j : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (exp_neg_selectorEarlyWriteIntLower_mul_growth_le_geometric j) hCd
  have h3 : Real.exp (-(selectorEarlyWriteIntLower (j + 1))) * Benc ≤
      Benc * Real.exp (-(2 : ℝ) * (j : ℝ)) := by
    calc Real.exp (-(selectorEarlyWriteIntLower (j + 1))) * Benc
        ≤ Real.exp (-(2 : ℝ) * (j : ℝ)) * Benc :=
          mul_le_mul_of_nonneg_right
            (exp_neg_selectorEarlyWriteIntLower_succ_le_geometric j) hBenc
      _ = Benc * Real.exp (-(2 : ℝ) * (j : ℝ)) := by ring
  have h4 : δearly (j + 1) ≤ Ce * Real.exp (-(2 : ℝ) * (j : ℝ)) := hδearly j
  calc holdSource δw Dinter δearly Benc j
      = Real.exp (-(selectorEarlyWriteIntLower (j + 1))) * δw j +
          Real.exp (-(selectorEarlyWriteIntLower (j + 1))) * Dinter j +
          Real.exp (-(selectorEarlyWriteIntLower (j + 1))) * Benc +
          δearly (j + 1) := by
        unfold holdSource
        ring
    _ ≤ Cw * Real.exp (-(2 : ℝ) * (j : ℝ)) +
          Cd * Real.exp (-(2 : ℝ) * (j : ℝ)) +
          Benc * Real.exp (-(2 : ℝ) * (j : ℝ)) +
          Ce * Real.exp (-(2 : ℝ) * (j : ℝ)) :=
        add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = (Cw + Cd + Benc + Ce) * Real.exp (-(2 : ℝ) * (j : ℝ)) := by ring

/-! ## Layer 1: the one-cycle recurrence at the hold time -/

/-- Triangle transport of the settled read endpoint to the next write
start. -/
theorem writeStart_zerr_le_of_settled_and_interRead
    (z : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf) (i : Fin d_U)
    {a b : ℝ} (j : ℕ)
    (hsettle : |z (selectorMUWriteReadTime j) i -
        stackMachineEncodingU.enc (cfg (j + 1)) i| ≤ a)
    (hinter : |z (selectorMUWriteStartTime (j + 1)) i -
        z (selectorMUWriteReadTime j) i| ≤ b) :
    |z (selectorMUWriteStartTime (j + 1)) i -
        stackMachineEncodingU.enc (cfg (j + 1)) i| ≤ b + a := by
  calc |z (selectorMUWriteStartTime (j + 1)) i -
      stackMachineEncodingU.enc (cfg (j + 1)) i|
      ≤ |z (selectorMUWriteStartTime (j + 1)) i -
          z (selectorMUWriteReadTime j) i| +
        |z (selectorMUWriteReadTime j) i -
          stackMachineEncodingU.enc (cfg (j + 1)) i| :=
        abs_sub_le _ _ _
    _ ≤ b + a := add_le_add hinter hsettle

/-- **One-cycle recurrence at the hold time.**  Chain
`hold j → read j → ws(j+1) → hold(j+1)`:

* `hsettle` — settled write contraction on `[hold j, read j]`
  (`z_write_settled_endpoint` with `Bz j := holdErr z cfg j i`);
* `hinter` — crude inter-read displacement cap on `[read j, ws(j+1)]`;
* `henc` — one-step encoding jump;
* `hearly` — early write contraction on `[ws(j+1), hold(j+1)]` toward
  `enc(cfg(j+2))`.

The conclusion is the affine recurrence
`holdErr(j+1) ≤ q(j)·holdErr(j) + r(j)` with `q = selectorHoldContraction`
and `r = holdSource`. -/
theorem holdErr_succ_le_of_cycle_estimates
    (z : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf) (i : Fin d_U)
    (δw Dinter δearly : ℕ → ℝ) (Benc : ℝ) (j : ℕ)
    (hsettle : |z (selectorMUWriteReadTime j) i -
        stackMachineEncodingU.enc (cfg (j + 1)) i| ≤
      Real.exp (-(selectorSettledWriteIntLower j)) * holdErr z cfg j i + δw j)
    (hinter : |z (selectorMUWriteStartTime (j + 1)) i -
        z (selectorMUWriteReadTime j) i| ≤ Dinter j)
    (henc : |stackMachineEncodingU.enc (cfg (j + 1)) i -
        stackMachineEncodingU.enc (cfg (j + 2)) i| ≤ Benc)
    (hearly : |z (selectorMUWriteHoldTime (j + 1)) i -
        stackMachineEncodingU.enc (cfg (j + 2)) i| ≤
      Real.exp (-(selectorEarlyWriteIntLower (j + 1))) *
        |z (selectorMUWriteStartTime (j + 1)) i -
          stackMachineEncodingU.enc (cfg (j + 2)) i| + δearly (j + 1)) :
    holdErr z cfg (j + 1) i ≤
      selectorHoldContraction j * holdErr z cfg j i +
        holdSource δw Dinter δearly Benc j := by
  have hexpE_nonneg : (0 : ℝ) ≤
      Real.exp (-(selectorEarlyWriteIntLower (j + 1))) := (Real.exp_pos _).le
  -- transport the read endpoint to the next write start
  have h1 : |z (selectorMUWriteStartTime (j + 1)) i -
      stackMachineEncodingU.enc (cfg (j + 1)) i| ≤
      Dinter j +
        (Real.exp (-(selectorSettledWriteIntLower j)) * holdErr z cfg j i +
          δw j) :=
    writeStart_zerr_le_of_settled_and_interRead z cfg i j hsettle hinter
  -- switch the target to the next configuration
  have h2 : |z (selectorMUWriteStartTime (j + 1)) i -
      stackMachineEncodingU.enc (cfg (j + 2)) i| ≤
      Real.exp (-(selectorSettledWriteIntLower j)) * holdErr z cfg j i +
        (δw j + Dinter j + Benc) := by
    calc |z (selectorMUWriteStartTime (j + 1)) i -
        stackMachineEncodingU.enc (cfg (j + 2)) i|
        ≤ |z (selectorMUWriteStartTime (j + 1)) i -
            stackMachineEncodingU.enc (cfg (j + 1)) i| +
          |stackMachineEncodingU.enc (cfg (j + 1)) i -
            stackMachineEncodingU.enc (cfg (j + 2)) i| := abs_sub_le _ _ _
      _ ≤ (Dinter j +
            (Real.exp (-(selectorSettledWriteIntLower j)) *
              holdErr z cfg j i + δw j)) + Benc := add_le_add h1 henc
      _ = Real.exp (-(selectorSettledWriteIntLower j)) * holdErr z cfg j i +
            (δw j + Dinter j + Benc) := by ring
  -- early-write contraction on cycle `j+1`
  have h3 := mul_le_mul_of_nonneg_left h2 hexpE_nonneg
  calc holdErr z cfg (j + 1) i
      = |z (selectorMUWriteHoldTime (j + 1)) i -
          stackMachineEncodingU.enc (cfg (j + 2)) i| := rfl
    _ ≤ Real.exp (-(selectorEarlyWriteIntLower (j + 1))) *
          |z (selectorMUWriteStartTime (j + 1)) i -
            stackMachineEncodingU.enc (cfg (j + 2)) i| +
          δearly (j + 1) := hearly
    _ ≤ Real.exp (-(selectorEarlyWriteIntLower (j + 1))) *
          (Real.exp (-(selectorSettledWriteIntLower j)) *
            holdErr z cfg j i + (δw j + Dinter j + Benc)) +
          δearly (j + 1) := by linarith [h3]
    _ = selectorHoldContraction j * holdErr z cfg j i +
          holdSource δw Dinter δearly Benc j := by
        rw [selectorHoldContraction_eq_mul]
        unfold holdSource
        ring

/-! ## Layer 2: geometric decay of the hold error -/

/-- **Geometric decay from the hold recurrence.**  Any sequence satisfying
the one-cycle hold recurrence with a rate-2 geometric source decays
geometrically at rate `lam = 2`: the contraction is uniformly `≤ e⁻³ <
e⁻² = exp(-lam)`, so `geometric_bound_of_contracting_recurrence`
applies. -/
theorem holdErr_geometric_of_recurrence
    (z : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf) (i : Fin d_U)
    {r : ℕ → ℝ} {C_r : ℝ} (hCr : 0 ≤ C_r)
    (hstep : ∀ j, holdErr z cfg (j + 1) i ≤
      selectorHoldContraction j * holdErr z cfg j i + r j)
    (hr : ∀ j, r j ≤ C_r * Real.exp (-(2 : ℝ) * (j : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      holdErr z cfg j i ≤ C * Real.exp (-(2 : ℝ) * (j : ℝ)) := by
  have hf0 : ∀ j, 0 ≤ holdErr z cfg j i := fun j => holdErr_nonneg z cfg j i
  have hstep' : ∀ j, holdErr z cfg (j + 1) i ≤
      Real.exp (-(3 : ℝ)) * holdErr z cfg j i +
        C_r * Real.exp (-(2 : ℝ) * (j : ℝ)) := by
    intro j
    have hcontr : selectorHoldContraction j * holdErr z cfg j i ≤
        Real.exp (-(3 : ℝ)) * holdErr z cfg j i :=
      mul_le_mul_of_nonneg_right
        (selectorHoldContraction_le_exp_neg_three j) (hf0 j)
    linarith [hstep j, hr j]
  exact geometric_bound_of_contracting_recurrence
    (f := fun j => holdErr z cfg j i) (q₀ := Real.exp (-(3 : ℝ)))
    (C_r := C_r) (lam := 2)
    hf0 hstep' (Real.exp_pos _).le
    (Real.exp_lt_exp.mpr (by norm_num)) hCr (by norm_num)

/-- **Layers 1+2 combined.**  From the four per-cycle window estimates and
the geometric/growth caps on their radii, the hold error decays geometrically
at rate `2`. -/
theorem holdErr_geometric_of_cycle_estimates
    (z : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf) (i : Fin d_U)
    (δw Dinter δearly : ℕ → ℝ) (Benc : ℝ)
    {Cw Cd Ce : ℝ}
    (hBenc : 0 ≤ Benc) (hCw : 0 ≤ Cw) (hCd : 0 ≤ Cd) (hCe : 0 ≤ Ce)
    (hδw_nonneg : ∀ j, 0 ≤ δw j)
    (hδw : ∀ j, δw j ≤ Cw * Real.exp (-(2 : ℝ) * (j : ℝ)))
    (hDinter : ∀ j, Dinter j ≤
      Cd * Real.exp (50 * selectorMUWriteStartTime (j + 1)))
    (hδearly : ∀ j, δearly (j + 1) ≤ Ce * Real.exp (-(2 : ℝ) * (j : ℝ)))
    (hsettle : ∀ j, |z (selectorMUWriteReadTime j) i -
        stackMachineEncodingU.enc (cfg (j + 1)) i| ≤
      Real.exp (-(selectorSettledWriteIntLower j)) * holdErr z cfg j i + δw j)
    (hinter : ∀ j, |z (selectorMUWriteStartTime (j + 1)) i -
        z (selectorMUWriteReadTime j) i| ≤ Dinter j)
    (henc : ∀ j, |stackMachineEncodingU.enc (cfg (j + 1)) i -
        stackMachineEncodingU.enc (cfg (j + 2)) i| ≤ Benc)
    (hearly : ∀ j, |z (selectorMUWriteHoldTime (j + 1)) i -
        stackMachineEncodingU.enc (cfg (j + 2)) i| ≤
      Real.exp (-(selectorEarlyWriteIntLower (j + 1))) *
        |z (selectorMUWriteStartTime (j + 1)) i -
          stackMachineEncodingU.enc (cfg (j + 2)) i| + δearly (j + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      holdErr z cfg j i ≤ C * Real.exp (-(2 : ℝ) * (j : ℝ)) := by
  refine holdErr_geometric_of_recurrence z cfg i
    (r := holdSource δw Dinter δearly Benc)
    (C_r := Cw + Cd + Benc + Ce)
    (by linarith) (fun j => ?_) (fun j => ?_)
  · exact holdErr_succ_le_of_cycle_estimates z cfg i δw Dinter δearly Benc j
      (hsettle j) (hinter j) (henc j) (hearly j)
  · exact holdSource_le_geometric hBenc hCd hδw_nonneg hδw hDinter hδearly j

/-! ## Layer 3: transport to the write-start endpoints

These produce verbatim the `hzerr_geo` / `hzu_geo` bounds of
`Paper3F1EndpointGeometricInputs` (`HeadlineUnconditional`), at rate
`lam = 2 > log B_U`. -/

/-- **Layer 3a: the `z` encoding endpoint at the next write start.**  The
transport back to `writeStart` uses the settled read endpoint plus a *fine*
(geometric) inter-read displacement `DinterFine`; the crude growing cap
`Dinter` is only ever used inside the recurrence, where the early contraction
kills it. -/
theorem writeStart_zerr_geometric_of_holdErr_geometric
    (z : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf) (i : Fin d_U)
    {C Cw Cf : ℝ} {δw DinterFine : ℕ → ℝ}
    (hhold : ∀ j, holdErr z cfg j i ≤ C * Real.exp (-(2 : ℝ) * (j : ℝ)))
    (hsettle : ∀ j, |z (selectorMUWriteReadTime j) i -
        stackMachineEncodingU.enc (cfg (j + 1)) i| ≤
      Real.exp (-(selectorSettledWriteIntLower j)) * holdErr z cfg j i + δw j)
    (hδw : ∀ j, δw j ≤ Cw * Real.exp (-(2 : ℝ) * (j : ℝ)))
    (hinterFine : ∀ j, |z (selectorMUWriteStartTime (j + 1)) i -
        z (selectorMUWriteReadTime j) i| ≤ DinterFine j)
    (hDf : ∀ j, DinterFine j ≤ Cf * Real.exp (-(2 : ℝ) * (j : ℝ))) :
    ∀ j, |z (selectorMUWriteStartTime (j + 1)) i -
        stackMachineEncodingU.enc (cfg (j + 1)) i| ≤
      (C + Cw + Cf) * Real.exp (-(2 : ℝ) * (j : ℝ)) := by
  intro j
  have htri := writeStart_zerr_le_of_settled_and_interRead z cfg i j
    (hsettle j) (hinterFine j)
  have hexp1 : Real.exp (-(selectorSettledWriteIntLower j)) ≤ 1 := by
    calc Real.exp (-(selectorSettledWriteIntLower j)) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr
            (by linarith [selectorSettledWriteIntLower_pos j])
      _ = 1 := Real.exp_zero
  have hcontr : Real.exp (-(selectorSettledWriteIntLower j)) *
      holdErr z cfg j i ≤ C * Real.exp (-(2 : ℝ) * (j : ℝ)) := by
    calc Real.exp (-(selectorSettledWriteIntLower j)) * holdErr z cfg j i
        ≤ 1 * holdErr z cfg j i :=
          mul_le_mul_of_nonneg_right hexp1 (holdErr_nonneg z cfg j i)
      _ = holdErr z cfg j i := one_mul _
      _ ≤ C * Real.exp (-(2 : ℝ) * (j : ℝ)) := hhold j
  have hsum : |z (selectorMUWriteStartTime (j + 1)) i -
      stackMachineEncodingU.enc (cfg (j + 1)) i| ≤
      C * Real.exp (-(2 : ℝ) * (j : ℝ)) +
        Cw * Real.exp (-(2 : ℝ) * (j : ℝ)) +
        Cf * Real.exp (-(2 : ℝ) * (j : ℝ)) := by
    linarith [hδw j, hDf j]
  calc |z (selectorMUWriteStartTime (j + 1)) i -
      stackMachineEncodingU.enc (cfg (j + 1)) i|
      ≤ C * Real.exp (-(2 : ℝ) * (j : ℝ)) +
          Cw * Real.exp (-(2 : ℝ) * (j : ℝ)) +
          Cf * Real.exp (-(2 : ℝ) * (j : ℝ)) := hsum
    _ = (C + Cw + Cf) * Real.exp (-(2 : ℝ) * (j : ℝ)) := by ring

/-- The inter-read u-active kernel mass dominates a linear function of the
cycle index: `2j - 8 ≤ selectorInterReadUActiveMassLower j`.  (For `j ≤ 4`
this is trivial from nonnegativity; from `j ≥ 5` on, the mass is doubly
exponential.) -/
theorem selectorInterReadUActiveMassLower_ge_linear (j : ℕ) :
    2 * (j : ℝ) - 8 ≤ selectorInterReadUActiveMassLower j := by
  have hK0 := selectorInterReadUActiveMassLower_nonneg j
  by_cases hj : (j : ℝ) ≤ 4
  · linarith
  · push_neg at hj
    have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hπ315 : Real.pi < 3.15 := Real.pi_lt_d2
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hrw : selectorInterReadUActiveMassLower j =
        (2 * Real.pi / 3) *
          Real.exp (100 * Real.pi * (j : ℝ) - 325 * Real.pi / 3) := by
      unfold selectorInterReadUActiveMassLower selectorMUUActiveStart
        selectorMUUActiveEnd
      rw [← Real.exp_add]
      ring_nf
    have hprod : 0 ≤ (Real.pi - 3) * (j : ℝ) :=
      mul_nonneg (by linarith) hj0
    have hθ_ge : 300 * (j : ℝ) - 342 ≤
        100 * Real.pi * (j : ℝ) - 325 * Real.pi / 3 := by
      nlinarith [hprod, hπ315]
    have hθpos : 0 ≤ 1 + (100 * Real.pi * (j : ℝ) - 325 * Real.pi / 3) := by
      nlinarith [hθ_ge, hj]
    have hexpθ : 1 + (100 * Real.pi * (j : ℝ) - 325 * Real.pi / 3) ≤
        Real.exp (100 * Real.pi * (j : ℝ) - 325 * Real.pi / 3) := by
      have h := Real.add_one_le_exp
        (100 * Real.pi * (j : ℝ) - 325 * Real.pi / 3)
      linarith
    have h23 : (2 : ℝ) ≤ 2 * Real.pi / 3 := by linarith
    have hchain : 2 * (1 + (100 * Real.pi * (j : ℝ) - 325 * Real.pi / 3)) ≤
        selectorInterReadUActiveMassLower j := by
      rw [hrw]
      calc 2 * (1 + (100 * Real.pi * (j : ℝ) - 325 * Real.pi / 3))
          ≤ (2 * Real.pi / 3) *
              (1 + (100 * Real.pi * (j : ℝ) - 325 * Real.pi / 3)) :=
            mul_le_mul_of_nonneg_right h23 hθpos
        _ ≤ (2 * Real.pi / 3) *
              Real.exp (100 * Real.pi * (j : ℝ) - 325 * Real.pi / 3) :=
            mul_le_mul_of_nonneg_left hexpθ (by positivity)
    linarith [hchain, hθ_ge, hj]

/-- The inter-read u-kernel contraction is geometric at rate `2` (with a
uniform prefactor `e⁸` covering the first cycles, where the mass is still
tiny). -/
theorem exp_neg_selectorInterReadUActiveMassLower_le_geometric (j : ℕ) :
    Real.exp (-(selectorInterReadUActiveMassLower j)) ≤
      Real.exp (8 : ℝ) * Real.exp (-(2 : ℝ) * (j : ℝ)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := selectorInterReadUActiveMassLower_ge_linear j
  linarith

/-- **Layer 3b: the `z-u` endpoint at the next write start.**  Input shape
from `selector_replicator_writeStart_zu_of_read_zu_and_interRead_source`
with the kernel mass lower-bounded through
`selectorInterRead_kernel_le_uActiveMass`: a merely *bounded* read-time
`|z-u|` box suffices, because the u-active kernel mass itself supplies the
geometric factor. -/
theorem writeStart_zu_geometric_of_transport
    (u z : ℝ → Fin d_U → ℝ) (i : Fin d_U)
    {Bread Bsrc : ℕ → ℝ} {CB Cs : ℝ}
    (htrans : ∀ j, |z (selectorMUWriteStartTime (j + 1)) i -
        u (selectorMUWriteStartTime (j + 1)) i| ≤
      Real.exp (-(selectorInterReadUActiveMassLower j)) * Bread j + Bsrc j)
    (hBread_nonneg : ∀ j, 0 ≤ Bread j)
    (hBread : ∀ j, Bread j ≤ CB)
    (hBsrc : ∀ j, Bsrc j ≤ Cs * Real.exp (-(2 : ℝ) * (j : ℝ))) :
    ∀ j, |u (selectorMUWriteStartTime (j + 1)) i -
        z (selectorMUWriteStartTime (j + 1)) i| ≤
      (Real.exp (8 : ℝ) * CB + Cs) * Real.exp (-(2 : ℝ) * (j : ℝ)) := by
  intro j
  have h2 : Real.exp (-(selectorInterReadUActiveMassLower j)) * Bread j ≤
      (Real.exp (8 : ℝ) * CB) * Real.exp (-(2 : ℝ) * (j : ℝ)) := by
    calc Real.exp (-(selectorInterReadUActiveMassLower j)) * Bread j
        ≤ (Real.exp (8 : ℝ) * Real.exp (-(2 : ℝ) * (j : ℝ))) * CB :=
          mul_le_mul
            (exp_neg_selectorInterReadUActiveMassLower_le_geometric j)
            (hBread j) (hBread_nonneg j) (by positivity)
      _ = (Real.exp (8 : ℝ) * CB) * Real.exp (-(2 : ℝ) * (j : ℝ)) := by ring
  rw [abs_sub_comm]
  calc |z (selectorMUWriteStartTime (j + 1)) i -
      u (selectorMUWriteStartTime (j + 1)) i|
      ≤ Real.exp (-(selectorInterReadUActiveMassLower j)) * Bread j +
          Bsrc j := htrans j
    _ ≤ (Real.exp (8 : ℝ) * CB) * Real.exp (-(2 : ℝ) * (j : ℝ)) +
          Cs * Real.exp (-(2 : ℝ) * (j : ℝ)) := add_le_add h2 (hBsrc j)
    _ = (Real.exp (8 : ℝ) * CB + Cs) * Real.exp (-(2 : ℝ) * (j : ℝ)) := by
        ring

/-- The rate `lam = 2` beats the depth weight: `log B_U = log 6 < 2`.  This
is the `hβlt` field of `Paper3F1EndpointGeometricInputs`. -/
theorem log_B_U_lt_two : Real.log (B_U : ℝ) < 2 := by
  have h6 : (B_U : ℝ) = 6 := by norm_num [B_U]
  rw [h6]
  have hexp2 : (6 : ℝ) < Real.exp 2 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [h1, Real.exp_pos 1]
  calc Real.log 6 < Real.log (Real.exp 2) :=
        Real.log_lt_log (by norm_num) hexp2
    _ = 2 := Real.log_exp 2

/-! ## The endpoint geometric package -/

/-- **Endpoint geometric package from the write-hold recurrence.**  Given the
per-cycle window estimates (in the shapes of `z_write_settled_endpoint`, the
early-write Duhamel bound, and
`selector_replicator_writeStart_zu_of_read_zu_and_interRead_source`) together
with the radius caps — geometric for the settled mixture radius, the early
source, the fine inter-read displacement and the inter-read `z-u` source;
merely *bounded* for the read-time `z-u` box; and allowed to *grow* like
`exp(50·writeStart)` for the crude inter-read cap — this produces verbatim
the `hzu_geo` / `hzerr_geo` bounds of `Paper3F1EndpointGeometricInputs`
at rate `lam = 2 > log B_U` (see `log_B_U_lt_two`). -/
theorem writeStart_endpoint_geometric_package
    (u z : ℝ → Fin d_U → ℝ) (cfg : ℕ → UConf) (i : Fin d_U)
    (δw Dinter δearly DinterFine Bread Bsrc : ℕ → ℝ) (Benc : ℝ)
    {Cw Cd Ce Cf CB Cs : ℝ}
    (hBenc : 0 ≤ Benc) (hCw : 0 ≤ Cw) (hCd : 0 ≤ Cd) (hCe : 0 ≤ Ce)
    (hCf : 0 ≤ Cf) (hCB : 0 ≤ CB) (hCs : 0 ≤ Cs)
    (hδw_nonneg : ∀ j, 0 ≤ δw j)
    (hδw : ∀ j, δw j ≤ Cw * Real.exp (-(2 : ℝ) * (j : ℝ)))
    (hDinter_cap : ∀ j, Dinter j ≤
      Cd * Real.exp (50 * selectorMUWriteStartTime (j + 1)))
    (hδearly : ∀ j, δearly (j + 1) ≤ Ce * Real.exp (-(2 : ℝ) * (j : ℝ)))
    (hDf : ∀ j, DinterFine j ≤ Cf * Real.exp (-(2 : ℝ) * (j : ℝ)))
    (hBread_nonneg : ∀ j, 0 ≤ Bread j)
    (hBread : ∀ j, Bread j ≤ CB)
    (hBsrc : ∀ j, Bsrc j ≤ Cs * Real.exp (-(2 : ℝ) * (j : ℝ)))
    (hsettle : ∀ j, |z (selectorMUWriteReadTime j) i -
        stackMachineEncodingU.enc (cfg (j + 1)) i| ≤
      Real.exp (-(selectorSettledWriteIntLower j)) * holdErr z cfg j i + δw j)
    (hinter : ∀ j, |z (selectorMUWriteStartTime (j + 1)) i -
        z (selectorMUWriteReadTime j) i| ≤ Dinter j)
    (hinterFine : ∀ j, |z (selectorMUWriteStartTime (j + 1)) i -
        z (selectorMUWriteReadTime j) i| ≤ DinterFine j)
    (henc : ∀ j, |stackMachineEncodingU.enc (cfg (j + 1)) i -
        stackMachineEncodingU.enc (cfg (j + 2)) i| ≤ Benc)
    (hearly : ∀ j, |z (selectorMUWriteHoldTime (j + 1)) i -
        stackMachineEncodingU.enc (cfg (j + 2)) i| ≤
      Real.exp (-(selectorEarlyWriteIntLower (j + 1))) *
        |z (selectorMUWriteStartTime (j + 1)) i -
          stackMachineEncodingU.enc (cfg (j + 2)) i| + δearly (j + 1))
    (htrans : ∀ j, |z (selectorMUWriteStartTime (j + 1)) i -
        u (selectorMUWriteStartTime (j + 1)) i| ≤
      Real.exp (-(selectorInterReadUActiveMassLower j)) * Bread j + Bsrc j) :
    ∃ Czu Cz : ℝ, 0 ≤ Czu ∧ 0 ≤ Cz ∧
      (∀ j, |u (selectorMUWriteStartTime (j + 1)) i -
          z (selectorMUWriteStartTime (j + 1)) i| ≤
        Czu * Real.exp (-(2 : ℝ) * (j : ℝ))) ∧
      (∀ j, |z (selectorMUWriteStartTime (j + 1)) i -
          stackMachineEncodingU.enc (cfg (j + 1)) i| ≤
        Cz * Real.exp (-(2 : ℝ) * (j : ℝ))) := by
  obtain ⟨C, hC0, hCbound⟩ :=
    holdErr_geometric_of_cycle_estimates z cfg i δw Dinter δearly Benc
      hBenc hCw hCd hCe hδw_nonneg hδw hDinter_cap hδearly
      hsettle hinter henc hearly
  refine ⟨Real.exp (8 : ℝ) * CB + Cs, C + Cw + Cf, ?_, ?_, ?_, ?_⟩
  · exact add_nonneg (mul_nonneg (Real.exp_pos _).le hCB) hCs
  · linarith
  · exact writeStart_zu_geometric_of_transport u z i
      htrans hBread_nonneg hBread hBsrc
  · exact writeStart_zerr_geometric_of_holdErr_geometric z cfg i
      hCbound hsettle hδw hinterFine hDf

/-- MU replicator family instantiation of the endpoint geometric package —
the consumption point for `bgpF1_endpoint_geometric_inputs` in
`HeadlineUnconditional` (package the scalars as constant coordinate
functions, `lam := fun _ => 2`, and `hβlt` from `log_B_U_lt_two`). -/
theorem mu_writeStart_endpoint_geometric_of_hold_recurrence
    {eta : ℚ} {heta : 0 < eta} {Mcy : ℕ} {κ₀ g₀ : ℚ}
    (sol : MUReplicatorSolFamily eta heta Mcy κ₀ g₀) (w : ℕ)
    (cfg : ℕ → UConf) (i : Fin d_U)
    (δw Dinter δearly DinterFine Bread Bsrc : ℕ → ℝ) (Benc : ℝ)
    {Cw Cd Ce Cf CB Cs : ℝ}
    (hBenc : 0 ≤ Benc) (hCw : 0 ≤ Cw) (hCd : 0 ≤ Cd) (hCe : 0 ≤ Ce)
    (hCf : 0 ≤ Cf) (hCB : 0 ≤ CB) (hCs : 0 ≤ Cs)
    (hδw_nonneg : ∀ j, 0 ≤ δw j)
    (hδw : ∀ j, δw j ≤ Cw * Real.exp (-(2 : ℝ) * (j : ℝ)))
    (hDinter_cap : ∀ j, Dinter j ≤
      Cd * Real.exp (50 * selectorMUWriteStartTime (j + 1)))
    (hδearly : ∀ j, δearly (j + 1) ≤ Ce * Real.exp (-(2 : ℝ) * (j : ℝ)))
    (hDf : ∀ j, DinterFine j ≤ Cf * Real.exp (-(2 : ℝ) * (j : ℝ)))
    (hBread_nonneg : ∀ j, 0 ≤ Bread j)
    (hBread : ∀ j, Bread j ≤ CB)
    (hBsrc : ∀ j, Bsrc j ≤ Cs * Real.exp (-(2 : ℝ) * (j : ℝ)))
    (hsettle : ∀ j, |(sol w).z (selectorMUWriteReadTime j) i -
        stackMachineEncodingU.enc (cfg (j + 1)) i| ≤
      Real.exp (-(selectorSettledWriteIntLower j)) *
        holdErr (sol w).z cfg j i + δw j)
    (hinter : ∀ j, |(sol w).z (selectorMUWriteStartTime (j + 1)) i -
        (sol w).z (selectorMUWriteReadTime j) i| ≤ Dinter j)
    (hinterFine : ∀ j, |(sol w).z (selectorMUWriteStartTime (j + 1)) i -
        (sol w).z (selectorMUWriteReadTime j) i| ≤ DinterFine j)
    (henc : ∀ j, |stackMachineEncodingU.enc (cfg (j + 1)) i -
        stackMachineEncodingU.enc (cfg (j + 2)) i| ≤ Benc)
    (hearly : ∀ j, |(sol w).z (selectorMUWriteHoldTime (j + 1)) i -
        stackMachineEncodingU.enc (cfg (j + 2)) i| ≤
      Real.exp (-(selectorEarlyWriteIntLower (j + 1))) *
        |(sol w).z (selectorMUWriteStartTime (j + 1)) i -
          stackMachineEncodingU.enc (cfg (j + 2)) i| + δearly (j + 1))
    (htrans : ∀ j, |(sol w).z (selectorMUWriteStartTime (j + 1)) i -
        (sol w).u (selectorMUWriteStartTime (j + 1)) i| ≤
      Real.exp (-(selectorInterReadUActiveMassLower j)) * Bread j + Bsrc j) :
    ∃ Czu Cz : ℝ, 0 ≤ Czu ∧ 0 ≤ Cz ∧
      (∀ j, |(sol w).u (selectorMUWriteStartTime (j + 1)) i -
          (sol w).z (selectorMUWriteStartTime (j + 1)) i| ≤
        Czu * Real.exp (-(2 : ℝ) * (j : ℝ))) ∧
      (∀ j, |(sol w).z (selectorMUWriteStartTime (j + 1)) i -
          stackMachineEncodingU.enc (cfg (j + 1)) i| ≤
        Cz * Real.exp (-(2 : ℝ) * (j : ℝ))) :=
  writeStart_endpoint_geometric_package (sol w).u (sol w).z cfg i
    δw Dinter δearly DinterFine Bread Bsrc Benc
    hBenc hCw hCd hCe hCf hCB hCs
    hδw_nonneg hδw hDinter_cap hδearly hDf
    hBread_nonneg hBread hBsrc
    hsettle hinter hinterFine henc hearly htrans

#print axioms selectorEarlyWriteIntLower_succ_ge_interRead_growth
#print axioms exp_neg_selectorEarlyWriteIntLower_succ_le_geometric
#print axioms exp_neg_selectorEarlyWriteIntLower_mul_growth_le_geometric
#print axioms three_le_selectorEarlyWriteIntLower_succ
#print axioms selectorHoldContraction_le_exp_neg_three
#print axioms selectorHoldContraction_lt_exp_neg_two
#print axioms holdSource_le_geometric
#print axioms holdErr_succ_le_of_cycle_estimates
#print axioms holdErr_geometric_of_recurrence
#print axioms holdErr_geometric_of_cycle_estimates
#print axioms writeStart_zerr_geometric_of_holdErr_geometric
#print axioms selectorInterReadUActiveMassLower_ge_linear
#print axioms exp_neg_selectorInterReadUActiveMassLower_le_geometric
#print axioms writeStart_zu_geometric_of_transport
#print axioms log_B_U_lt_two
#print axioms writeStart_endpoint_geometric_package
#print axioms mu_writeStart_endpoint_geometric_of_hold_recurrence

end Ripple.BoundedUniversality.BGP
