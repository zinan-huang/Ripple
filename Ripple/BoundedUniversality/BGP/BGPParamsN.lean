import Ripple.BoundedUniversality.BGP.ContractTracking
import Ripple.BoundedUniversality.BGP.DynChiLeak
import Ripple.BoundedUniversality.BGP.MachineInstance
import Ripple.BoundedUniversality.BGP.WarmIndexMU

/-!
Ripple.BoundedUniversality.BGP.BGPParamsN
---------------------

**N-parametric clock parameters** for the BGP headline migration.

## Why N-parametric

`c_f = Classical.choose` makes
`N₀ := Fintype.card (Option (SuppLabel c_f) × Option Γ')` an opaque-but-fixed
natural with NO derivable numeric upper bound.  The displacement scale
`D_U = max 8 (2·N₀ + 2)` therefore cannot be compared against any fixed
numeral, which is exactly why the 12 remaining analytic sorries in
`HeadlineUnconditional` (all of which need `O(D_U) ≤ fixed numeral`) are
unprovable with the fixed `bgpParams38 = (cμ, cα) = (1000, 300)`.

The fix: every budget-bearing constant becomes a function of the master scale

  `bgpScale := N₀ + 4  (≥ 5)`

* `cμ := 1000 · bgpScale`, `cα := 300 · bgpScale` — the cycle-0 ctrl drift
  `~ D_U / cμ² ≤ 2·bgpScale / (10⁶·bgpScale²) = 2/(10⁶·bgpScale) < r_LE_U/4`
  becomes provable symbolically (`bgpParamsN_ctrl_drift`).
* warm gain `g₀ = bgpWarmGainCN · 6^w` with
  `bgpWarmGainCN := 1734736490 · bgpScale⁶`, which dominates every
  N-dependent polynomial bound in the chain:
  `Fintype.card UniversalLocalView ≤ N₀⁶ ≤ bgpScale⁶` (the local-view card is
  at most the sixth power of the control card, `cardUniversalLocalView_le`),
  and `cμ³ ≤ bgpWarmGainCN` (`bgpParamsN_cμ_cubed_le_warmGainCN`).

## Why `cα` scales too (deviation from the one-line spec "cα stays 300")

`cα` CANNOT stay fixed at `300` while `cμ` scales: the strict-cascade window
requires `cμ/4 < cα < cμ/2` (`bgpParamsN_regime_window`), and the S2 u-active
growth sub-window requires `cα − cμ·qPulse > 0` with `qPulse ≤ 1/15`.  Both
put `cμ`-proportional LOWER bounds on `cα`, so a fixed `cα = 300` is falsified
already at `bgpScale ≥ 2`.  Homogeneous scaling `(cμ, cα) = (1000, 300)·bgpScale`
preserves every sign and ratio fact of the checked-in `(1000, 300)` design;
all margins multiply by `bgpScale ≥ 4`:

* χ leak margin: `cμ/2 − cα = 200·bgpScale ≥ 200` (was `200`);
* κ cascade margin: `cα − cμ/4 = 50·bgpScale ≥ 50` (was `50`);
* settled u-rate: `cμ·(3/4) − cα = 450·bgpScale ≥ 450` (was `450`).

Downstream exponent comparisons of the form `a·cα ≥ b·(cμ/2 − cα)` (Hoff
budget vs gain anchors) are homogeneous of degree 1 in the scale, so they
divide through by `bgpScale` and reduce to the already-proved `(1000, 300)`
arithmetic.

`bgpParams38` is left untouched: this file is the parallel N-parametric hook;
the headline chain migrates consumer by consumer.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance UniversalMachine
open Turing.PartrecToTM2

/-! ## The opaque control card and the master scale -/

/-- The opaque packed control-coordinate cardinality `N₀`.  This is the
quantity `D_U` is built from; `c_f = Classical.choose` makes it fixed but
numerically unbounded. -/
def bgpCtrlCard : ℕ := Fintype.card (Option (SuppLabel c_f) × Option Γ')

theorem bgpCtrlCard_pos : 0 < bgpCtrlCard :=
  Fintype.card_pos_iff.mpr ⟨(none, none)⟩

/-- Master N-parametric scale: `N₀ + 4`. -/
def bgpScale : ℕ := bgpCtrlCard + 4

theorem bgpScale_ge_four : 4 ≤ bgpScale :=
  Nat.le_add_left 4 bgpCtrlCard

theorem bgpScale_pos : 0 < bgpScale :=
  lt_of_lt_of_le (by norm_num) bgpScale_ge_four

theorem bgpScaleR_ge_four : (4 : ℝ) ≤ (bgpScale : ℝ) := by
  exact_mod_cast bgpScale_ge_four

theorem bgpScaleR_ge_one : (1 : ℝ) ≤ (bgpScale : ℝ) :=
  le_trans (by norm_num) bgpScaleR_ge_four

theorem bgpScaleR_pos : (0 : ℝ) < (bgpScale : ℝ) :=
  lt_of_lt_of_le (by norm_num) bgpScaleR_ge_four

theorem bgpScaleQ_ge_one : (1 : ℚ) ≤ (bgpScale : ℚ) := by
  exact_mod_cast le_trans (by norm_num : 1 ≤ 4) bgpScale_ge_four

theorem bgpScaleQ_pos : (0 : ℚ) < (bgpScale : ℚ) :=
  lt_of_lt_of_le one_pos bgpScaleQ_ge_one

/-! ## Bridges to the machine-instance scales -/

/-- The displacement scale is dominated by twice the master scale:
`D_U = max 8 (2·N₀ + 2) ≤ 2·N₀ + 8 = 2·bgpScale`. -/
theorem D_U_le_two_bgpScale : D_U ≤ 2 * (bgpScale : ℝ) := by
  have hs : (bgpScale : ℝ) = (bgpCtrlCard : ℝ) + 4 := by
    unfold bgpScale
    push_cast
    ring
  have h8 : (8 : ℝ) ≤ 2 * (bgpScale : ℝ) := by
    have h4 := bgpScaleR_ge_four
    linarith
  have hkey :
      2 * ((Fintype.card (Option (SuppLabel c_f) × Option Γ') : ℕ) : ℝ) + 2 ≤
        2 * (bgpScale : ℝ) := by
    have hc :
        ((Fintype.card (Option (SuppLabel c_f) × Option Γ') : ℕ) : ℝ) =
          (bgpCtrlCard : ℝ) := by
      norm_num [bgpCtrlCard]
    rw [hc, hs]
    have hc0 : (0 : ℝ) ≤ (bgpCtrlCard : ℝ) := Nat.cast_nonneg _
    linarith
  exact max_le h8 hkey

/-- Injection of the finite local view into six copies of the packed control
coordinate: `(label, var)` in the first copy, each stack-top field paired with
`none` in the remaining five. -/
private def viewToCtrlPairs (v : UniversalLocalView) :
    (Option (SuppLabel c_f) × Option Γ') × (Option (SuppLabel c_f) × Option Γ') ×
      (Option (SuppLabel c_f) × Option Γ') × (Option (SuppLabel c_f) × Option Γ') ×
      (Option (SuppLabel c_f) × Option Γ') × (Option (SuppLabel c_f) × Option Γ') :=
  ((v.label, v.var), (none, v.mainTop), (none, v.mainSecond),
    (none, v.revTop), (none, v.auxTop), (none, v.dataTop))

private theorem viewToCtrlPairs_injective :
    Function.Injective viewToCtrlPairs := by
  intro a b h
  cases a
  cases b
  simp only [viewToCtrlPairs, Prod.mk.injEq] at h
  simp only [UniversalLocalView.mk.injEq]
  tauto

/-- The local-view cardinality is at most the sixth power of the opaque
control card (each of the seven fields embeds into a factor of
`Option (SuppLabel c_f) × Option Γ'`, packing `(label, var)` together). -/
theorem cardUniversalLocalView_le_ctrlCard_pow_six :
    Fintype.card UniversalLocalView ≤ bgpCtrlCard ^ 6 := by
  classical
  have h := Fintype.card_le_of_injective _ viewToCtrlPairs_injective
  have hcard :
      Fintype.card
          ((Option (SuppLabel c_f) × Option Γ') × (Option (SuppLabel c_f) × Option Γ') ×
            (Option (SuppLabel c_f) × Option Γ') × (Option (SuppLabel c_f) × Option Γ') ×
            (Option (SuppLabel c_f) × Option Γ') × (Option (SuppLabel c_f) × Option Γ')) =
        bgpCtrlCard ^ 6 := by
    simp only [Fintype.card_prod, bgpCtrlCard]
    ring
  exact hcard ▸ h

/-- Local-view cardinality is dominated by the sixth power of the master
scale. -/
theorem cardUniversalLocalView_le_bgpScale_pow_six :
    Fintype.card UniversalLocalView ≤ bgpScale ^ 6 :=
  le_trans cardUniversalLocalView_le_ctrlCard_pow_six
    (Nat.pow_le_pow_left (Nat.le_add_right _ _) 6)

/-! ## N-parametric strict-cascade parameters -/

/-- N-parametric strict-cascade parameters: the `(1000, 300)` design scaled
homogeneously by the master scale `bgpScale = N₀ + 4`. -/
def bgpParamsN : DynGateParams where
  A := 1
  L := 1
  cμ := 1000 * (bgpScale : ℝ)
  cα := 300 * (bgpScale : ℝ)

theorem bgpParamsN_A_eq : bgpParamsN.A = 1 := rfl

theorem bgpParamsN_L_eq : bgpParamsN.L = 1 := rfl

theorem bgpParamsN_cμ_def : bgpParamsN.cμ = 1000 * (bgpScale : ℝ) := rfl

theorem bgpParamsN_cα_def : bgpParamsN.cα = 300 * (bgpScale : ℝ) := rfl

theorem bgpParamsN_A_rat : bgpParamsN.A = ((1 : ℚ) : ℝ) := by
  norm_num [bgpParamsN]

/-- Rational presentability of `cμ` (the scale is a natural). -/
theorem bgpParamsN_cμ_rat :
    bgpParamsN.cμ = ((1000 * (bgpScale : ℚ) : ℚ) : ℝ) := by
  rw [bgpParamsN_cμ_def]
  push_cast
  ring

/-- Rational presentability of `cα` (the scale is a natural). -/
theorem bgpParamsN_cα_rat :
    bgpParamsN.cα = ((300 * (bgpScale : ℚ) : ℚ) : ℝ) := by
  rw [bgpParamsN_cα_def]
  push_cast
  ring

theorem bgpParamsN_cμ_pos : 0 < bgpParamsN.cμ := by
  rw [bgpParamsN_cμ_def]
  nlinarith [bgpScaleR_pos]

theorem bgpParamsN_cα_pos : 0 < bgpParamsN.cα := by
  rw [bgpParamsN_cα_def]
  nlinarith [bgpScaleR_pos]

/-- Numeric floors matching the old fixed design (`bgpScale ≥ 1`). -/
theorem bgpParamsN_cμ_ge_1000 : (1000 : ℝ) ≤ bgpParamsN.cμ := by
  rw [bgpParamsN_cμ_def]
  nlinarith [bgpScaleR_ge_one]

theorem bgpParamsN_cα_ge_300 : (300 : ℝ) ≤ bgpParamsN.cα := by
  rw [bgpParamsN_cα_def]
  nlinarith [bgpScaleR_ge_one]

/-- Full regime window, scale-uniform:
`cμ/4 = 250·s < cα = 300·s < cμ/2 = 500·s`. -/
theorem bgpParamsN_regime_window :
    bgpParamsN.cμ * (1 / 4 : ℝ) ^ bgpParamsN.L < bgpParamsN.cα ∧
      bgpParamsN.cα < bgpParamsN.cμ * (1 / 2 : ℝ) ^ bgpParamsN.L := by
  rw [bgpParamsN_cμ_def, bgpParamsN_cα_def, bgpParamsN_L_eq]
  constructor <;> nlinarith [bgpScaleR_pos]

/-- χ leak margin, exact value: `cμ/2 − cα = 200·bgpScale`. -/
theorem bgpParamsN_chi_leak_eq :
    bgpParamsN.cμ * (1 / 2 : ℝ) ^ bgpParamsN.L - bgpParamsN.cα =
      200 * (bgpScale : ℝ) := by
  rw [bgpParamsN_cμ_def, bgpParamsN_cα_def, bgpParamsN_L_eq]
  ring

/-- χ leak regime is strict: `200·bgpScale > 0`. -/
theorem bgpParamsN_chi_leak_strict :
    0 < bgpParamsN.cμ * (1 / 2 : ℝ) ^ bgpParamsN.L - bgpParamsN.cα := by
  rw [bgpParamsN_chi_leak_eq]
  nlinarith [bgpScaleR_pos]

/-- The leak margin dominates the old fixed value `200`. -/
theorem bgpParamsN_chi_leak_ge_200 :
    (200 : ℝ) ≤ bgpParamsN.cμ * (1 / 2 : ℝ) ^ bgpParamsN.L - bgpParamsN.cα := by
  rw [bgpParamsN_chi_leak_eq]
  nlinarith [bgpScaleR_ge_one]

/-- Compatibility alias matching the `bgpParams38` theorem name. -/
theorem bgpParamsN_chi_regime :
    0 < bgpParamsN.cμ * (1 / 2 : ℝ) ^ bgpParamsN.L - bgpParamsN.cα :=
  bgpParamsN_chi_leak_strict

theorem bgpParamsN_leakLambda_pos :
    0 < DynChiLeak.leakLambda bgpParamsN.cμ bgpParamsN.cα bgpParamsN.L := by
  simpa [DynChiLeak.leakLambda] using bgpParamsN_chi_leak_strict

/-- κ cascade margin, exact value: `cα − cμ/4 = 50·bgpScale`. -/
theorem bgpParamsN_kappa_cascade_eq :
    bgpParamsN.cα - bgpParamsN.cμ * (1 / 4 : ℝ) ^ bgpParamsN.L =
      50 * (bgpScale : ℝ) := by
  rw [bgpParamsN_cμ_def, bgpParamsN_cα_def, bgpParamsN_L_eq]
  ring

/-- κ cascade regime is strict: `50·bgpScale > 0`. -/
theorem bgpParamsN_kappa_cascade_strict :
    0 < bgpParamsN.cα - bgpParamsN.cμ * (1 / 4 : ℝ) ^ bgpParamsN.L := by
  rw [bgpParamsN_kappa_cascade_eq]
  nlinarith [bgpScaleR_pos]

/-- The cascade margin dominates the old fixed value `50`. -/
theorem bgpParamsN_kappa_cascade_ge_50 :
    (50 : ℝ) ≤ bgpParamsN.cα - bgpParamsN.cμ * (1 / 4 : ℝ) ^ bgpParamsN.L := by
  rw [bgpParamsN_kappa_cascade_eq]
  nlinarith [bgpScaleR_ge_one]

/-- Compatibility alias matching the `bgpParams38` theorem name. -/
theorem bgpParamsN_kappa_growth_regime :
    0 < bgpParamsN.cα - bgpParamsN.cμ * (1 / 4 : ℝ) ^ bgpParamsN.L :=
  bgpParamsN_kappa_cascade_strict

/-- Settled u-rate, exact value: `cμ·(3/4) − cα = 450·bgpScale`. -/
theorem bgpParamsN_settled_rate_eq :
    bgpParamsN.cμ * (3 / 4 : ℝ) ^ bgpParamsN.L - bgpParamsN.cα =
      450 * (bgpScale : ℝ) := by
  rw [bgpParamsN_cμ_def, bgpParamsN_cα_def, bgpParamsN_L_eq]
  ring

theorem bgpParamsN_settled_rate_pos :
    0 < bgpParamsN.cμ * (3 / 4 : ℝ) ^ bgpParamsN.L - bgpParamsN.cα := by
  rw [bgpParamsN_settled_rate_eq]
  nlinarith [bgpScaleR_pos]

/-- The settled rate dominates the old fixed value `450`. -/
theorem bgpParamsN_settled_rate_ge_450 :
    (450 : ℝ) ≤ bgpParamsN.cμ * (3 / 4 : ℝ) ^ bgpParamsN.L - bgpParamsN.cα := by
  rw [bgpParamsN_settled_rate_eq]
  nlinarith [bgpScaleR_ge_one]

/-- Parallel settled u-drift rate for `bgpParamsN`; the existing
`selectorUSettledRate` remains the `bgpParams38` specialization. -/
def selectorUSettledRate_N : ℝ :=
  bgpParamsN.cμ * (3 / 4 : ℝ) ^ bgpParamsN.L - bgpParamsN.cα

theorem selectorUSettledRate_N_eq :
    selectorUSettledRate_N = 450 * (bgpScale : ℝ) := by
  simpa [selectorUSettledRate_N] using bgpParamsN_settled_rate_eq

theorem selectorUSettledRate_N_pos : 0 < selectorUSettledRate_N := by
  simpa [selectorUSettledRate_N] using bgpParamsN_settled_rate_pos

theorem selectorUSettledRate_N_ge_450 : (450 : ℝ) ≤ selectorUSettledRate_N := by
  simpa [selectorUSettledRate_N] using bgpParamsN_settled_rate_ge_450

/-! ## The headline drift budgets (the previously unprovable comparisons) -/

/-- Displacement is beaten by the clock rate with the full old margin:
`2·D_U ≤ 4·bgpScale ≤ cμ`. -/
theorem two_D_U_le_bgpParamsN_cμ : 2 * D_U ≤ bgpParamsN.cμ := by
  have hD := D_U_le_two_bgpScale
  rw [bgpParamsN_cμ_def]
  nlinarith [bgpScaleR_pos]

/-- Multiplicative form of the cycle-0 ctrl drift budget:
`4·D_U ≤ 8·bgpScale ≤ 1000·bgpScale² = r_LE_U · cμ²`. -/
theorem bgpParamsN_ctrl_drift_mul :
    4 * D_U ≤ r_LE_U * bgpParamsN.cμ ^ 2 := by
  have hD := D_U_le_two_bgpScale
  have hs4 := bgpScaleR_ge_four
  have hs0 := bgpScaleR_pos
  rw [bgpParamsN_cμ_def]
  unfold r_LE_U
  nlinarith [mul_pos hs0 hs0, sq_nonneg ((bgpScale : ℝ) - 1)]

/-- **The headline ctrl-drift comparison**, provable only N-parametrically:
`D_U / cμ² ≤ 2/(10⁶·bgpScale) < 1/4000 = r_LE_U / 4`. -/
theorem bgpParamsN_ctrl_drift :
    D_U / bgpParamsN.cμ ^ 2 ≤ r_LE_U / 4 := by
  have hcμ2 : (0 : ℝ) < bgpParamsN.cμ ^ 2 := pow_pos bgpParamsN_cμ_pos 2
  rw [div_le_div_iff₀ hcμ2 (by norm_num : (0 : ℝ) < 4)]
  nlinarith [bgpParamsN_ctrl_drift_mul, hcμ2, r_LE_U_pos]

/-! ## N-parametric warm gain

The diagonal warm-gain constant scales with `bgpScale⁶`, dominating every
polynomial-in-`N₀` quantity in the chain (`card UniversalLocalView ≤ bgpScale⁶`,
`cμ³ ≤ 1734736490·bgpScale⁶`) while keeping the checked-in numeric floor
`1734736490` (so every proved `g₀ ≥ 1734736490`-shaped consumer migrates by
transitivity).  The per-word factor `6^w` is unchanged.  The presenters (the
computability surface) live next to the old ones in `HeadlineUnconditional`;
`Computable.const` does not require the constant to be a closed numeral. -/

/-- N-parametric diagonal warm-gain constant. -/
def bgpWarmGainCN : ℚ := 1734736490 * (bgpScale : ℚ) ^ 6

/-- N-parametric warm gain at word length `w`. -/
def bgpWarmGainQN (w : ℕ) : ℚ :=
  bgpWarmGainCN * (6 : ℚ) ^ w

/-- Natural-number presentation of the constant (for the computable
presenter). -/
theorem bgpWarmGainCN_nat_eq :
    bgpWarmGainCN = ((1734736490 * bgpScale ^ 6 : ℕ) : ℚ) := by
  unfold bgpWarmGainCN
  push_cast
  ring

theorem bgpWarmGainCN_pos : 0 < bgpWarmGainCN := by
  unfold bgpWarmGainCN
  nlinarith [pow_pos bgpScaleQ_pos 6]

theorem bgpWarmGainCN_nonneg : 0 ≤ bgpWarmGainCN :=
  bgpWarmGainCN_pos.le

/-- The N-parametric constant keeps the checked-in numeric floor. -/
theorem bgpWarmGainCN_ge_base : (1734736490 : ℚ) ≤ bgpWarmGainCN := by
  have hpow : (1 : ℚ) ≤ (bgpScale : ℚ) ^ 6 := one_le_pow₀ bgpScaleQ_ge_one
  unfold bgpWarmGainCN
  nlinarith [hpow]

theorem bgpWarmGainQN_pos (w : ℕ) : 0 < bgpWarmGainQN w := by
  unfold bgpWarmGainQN
  exact mul_pos bgpWarmGainCN_pos (pow_pos (by norm_num) w)

theorem bgpWarmGainQN_nonneg (w : ℕ) : 0 ≤ bgpWarmGainQN w :=
  (bgpWarmGainQN_pos w).le

theorem bgpWarmGainCN_le_warmGainQN (w : ℕ) :
    bgpWarmGainCN ≤ bgpWarmGainQN w := by
  have hpow_ge : (1 : ℚ) ≤ (6 : ℚ) ^ w :=
    one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 6)
  unfold bgpWarmGainQN
  nlinarith [bgpWarmGainCN_nonneg, hpow_ge]

/-- The warm gain dominates the local-view cardinality (the `1/card` floors
and the card-linear budget sums are all beaten by `g₀`):
`card ≤ bgpScale⁶ ≤ bgpWarmGainCN`. -/
theorem cardUniversalLocalView_le_warmGainCN :
    ((Fintype.card UniversalLocalView : ℚ)) ≤ bgpWarmGainCN := by
  have hq : ((Fintype.card UniversalLocalView : ℚ)) ≤ ((bgpScale : ℚ)) ^ 6 := by
    exact_mod_cast cardUniversalLocalView_le_bgpScale_pow_six
  have hpow : (0 : ℚ) ≤ ((bgpScale : ℚ)) ^ 6 := (pow_pos bgpScaleQ_pos 6).le
  unfold bgpWarmGainCN
  nlinarith [hq, hpow]

/-- The warm gain dominates the CUBE of the clock rate:
`cμ³ = 10⁹·bgpScale³ ≤ 1734736490·bgpScale⁶`.  (Headroom for any
`cμ`-polynomial transient of degree ≤ 3 in the warm-phase estimates.) -/
theorem bgpParamsN_cμ_cubed_le_warmGainCN :
    bgpParamsN.cμ ^ 3 ≤ ((bgpWarmGainCN : ℚ) : ℝ) := by
  have hsR := bgpScaleR_ge_one
  have hs0 := bgpScaleR_pos
  have hcast : ((bgpWarmGainCN : ℚ) : ℝ) =
      1734736490 * (bgpScale : ℝ) ^ 6 := by
    unfold bgpWarmGainCN
    push_cast
    ring
  rw [bgpParamsN_cμ_def, hcast]
  have h36 : (bgpScale : ℝ) ^ 3 ≤ (bgpScale : ℝ) ^ 6 :=
    pow_le_pow_right₀ hsR (by norm_num)
  nlinarith [h36, pow_pos hs0 3, pow_pos hs0 6]

/-- Real-cast floor for the migrated `bgpS13_g0_ge`-shaped consumers. -/
theorem bgpWarmGainQN_ge_base (w : ℕ) :
    (1734736490 : ℝ) ≤ ((bgpWarmGainQN w : ℚ) : ℝ) := by
  have h : (1734736490 : ℚ) ≤ bgpWarmGainQN w :=
    le_trans bgpWarmGainCN_ge_base (bgpWarmGainCN_le_warmGainQN w)
  exact_mod_cast h

/-! ## Word-coupled clock head start (the F1 (4/5)/(5/5) falsity fix)

### Why a head start is needed

At the input-stack coordinate the F1 cycle-0 weighted boundary is
`W0 = B_U^{dep(0,i)}·|u(π/6) − enc|_i` with depth weight
`6^{inputLenU+1}`, while the cycle-0 u-gate leak on `[0, π/6]` is
`w`-INDEPENDENT for any FIXED clock rates (the u-kernel
`e^{cα·τ − μ(τ)·qPulse}` has mass `≈ 1/(cμ/2 − cα)`, and the early
`|z−u|` box is `O(bgpScale·e^{199})`, both blind to the word).  So the
gate suppression must be COUPLED to the word.

### Why the two briefed fixes are NOT implementable, and what is

* **Clock head start as an initial condition `μ(0) = μ₀(w) > 0`
  (RUN_LOG option (a)): IMPOSSIBLE in the rational-PIVP frame.**  The
  gate values are PIVP coordinates with
  `gate(0) = e^{−μ(0)·pulse(0)}` and `pulse(0) = 1/2` at `L = 1`; any
  `μ(0) > 0` makes the initial gate value transcendental, violating
  `EventualThresholdSimulation.encoder_presented` (the init vector must
  be presented as computable `ℤ × ℕ` rationals).  This is precisely the
  design constraint recorded in `DynamicGate.lean` ("any μ(0) > 0 start
  would give a transcendental initial gate value").
* **Per-word params as FIELD coefficients (RUN_LOG option (b)):
  ILLEGAL at the headline.**  `EventualThresholdSimulation (P : PIVP ℚ)`
  fixes ONE vector field; the input `w` enters only through `P.init w`.
  A `w`-dependent `cμ` as a polynomial coefficient would make the field
  itself `w`-dependent.
* **THE FIX (implemented here): word-coupled clock SPEED-UP with the
  rates realized as constant PIVP coordinates.**  Scale BOTH clock rates
  homogeneously, `(cμ, cα) = (1000, 300)·bgpScaleW w` with
  `bgpScaleW w = bgpScale·6^(inputLenU 1 w + 220)`.  In the eventual
  single-PIVP realization `cμ`/`cα` become coordinates with derivative
  `0` and `w`-dependent RATIONAL initial values (exactly the existing
  warm-gain pattern: `g₀ = C·6^w` already enters as the init of the
  warm-gain coordinate, never as a coefficient), so the field stays
  fixed and the init stays rational.  At the ANALYTIC layer (the
  `SelectorReplicatorDynSol` chain, which is already fully parametric in
  `DynGateParams`) this is just the params family `bgpParamsNW w` below.

### Why homogeneous scaling delivers the head start

`μ(t) = 1000·bgpScaleW w·t`: by any fixed positive time the clock has
outrun any prescribed `w`-linear head-start value — the head start is
delivered inside `[0, ε]` instead of at `0`.  Quantitatively, on
`[0, π/6]` (`qPulse ≥ 1/2`, `L = 1`) the u-kernel is
`≤ e^{(cα − cμ/2)τ} = e^{−200·bgpScaleW w·τ}`, with mass
`≤ 1/(200·bgpScaleW w)`; against the `O(bgpScale·e^{199})` early box
(which does NOT scale with the clock — hull trapping is
rate-independent) this beats the depth weight `6^{inputLenU+1}` with
`6^{−190}`-headroom (`bgpScaleW_beats_depth_weight` below).  Every
sign/ratio fact of the `(1000, 300)` design is degree-1 homogeneous in
the scale, so the whole `bgpParamsN` lemma surface clones verbatim. -/

/-- S-generic strict-cascade parameters: the `(1000, 300)` design at an
arbitrary natural master scale `S`.  `bgpParamsN = bgpParamsNS bgpScale`
(definitionally); the word-coupled family is `bgpParamsNW w =
bgpParamsNS (bgpScaleW w)`. -/
def bgpParamsNS (S : ℕ) : DynGateParams where
  A := 1
  L := 1
  cμ := 1000 * (S : ℝ)
  cα := 300 * (S : ℝ)

theorem bgpParamsN_eq_NS : bgpParamsN = bgpParamsNS bgpScale := rfl

theorem bgpParamsNS_A_eq (S : ℕ) : (bgpParamsNS S).A = 1 := rfl

theorem bgpParamsNS_L_eq (S : ℕ) : (bgpParamsNS S).L = 1 := rfl

theorem bgpParamsNS_cμ_def (S : ℕ) :
    (bgpParamsNS S).cμ = 1000 * (S : ℝ) := rfl

theorem bgpParamsNS_cα_def (S : ℕ) :
    (bgpParamsNS S).cα = 300 * (S : ℝ) := rfl

theorem bgpParamsNS_A_rat (S : ℕ) : (bgpParamsNS S).A = ((1 : ℚ) : ℝ) := by
  norm_num [bgpParamsNS]

theorem bgpParamsNS_cμ_rat (S : ℕ) :
    (bgpParamsNS S).cμ = ((1000 * (S : ℚ) : ℚ) : ℝ) := by
  rw [bgpParamsNS_cμ_def]
  push_cast
  ring

theorem bgpParamsNS_cα_rat (S : ℕ) :
    (bgpParamsNS S).cα = ((300 * (S : ℚ) : ℚ) : ℝ) := by
  rw [bgpParamsNS_cα_def]
  push_cast
  ring

/-! ### The word-coupled master scale -/

/-- Word-coupled head-start factor: `6^(inputLenU 1 w + 220)`.  The
`inputLenU`-exponent beats the F1 depth weight `6^{inputLenU+O(1)}`; the
`+220` buffer absorbs the crude `e^{200}`-sized window hulls
(`e^{200} ≤ 3^{200} ≤ 6^{190}/20`, see
`bgpScaleW_beats_depth_weight`). -/
def bgpHeadStartN (w : ℕ) : ℕ :=
  6 ^ (MachineInstance.inputLenU 1 w + 220)

theorem bgpHeadStartN_ge_one (w : ℕ) : 1 ≤ bgpHeadStartN w :=
  Nat.one_le_pow _ _ (by norm_num)

/-- The word-coupled master scale: `bgpScale · 6^(inputLenU 1 w + 220)`. -/
def bgpScaleW (w : ℕ) : ℕ := bgpScale * bgpHeadStartN w

theorem bgpScale_le_bgpScaleW (w : ℕ) : bgpScale ≤ bgpScaleW w :=
  Nat.le_mul_of_pos_right _ (lt_of_lt_of_le (by norm_num) (bgpHeadStartN_ge_one w))

theorem bgpScaleW_ge_four (w : ℕ) : 4 ≤ bgpScaleW w :=
  le_trans bgpScale_ge_four (bgpScale_le_bgpScaleW w)

theorem bgpScaleW_pos (w : ℕ) : 0 < bgpScaleW w :=
  lt_of_lt_of_le (by norm_num) (bgpScaleW_ge_four w)

theorem bgpScaleWR_ge_four (w : ℕ) : (4 : ℝ) ≤ (bgpScaleW w : ℝ) := by
  exact_mod_cast bgpScaleW_ge_four w

theorem bgpScaleWR_ge_one (w : ℕ) : (1 : ℝ) ≤ (bgpScaleW w : ℝ) :=
  le_trans (by norm_num) (bgpScaleWR_ge_four w)

theorem bgpScaleWR_pos (w : ℕ) : (0 : ℝ) < (bgpScaleW w : ℝ) :=
  lt_of_lt_of_le (by norm_num) (bgpScaleWR_ge_four w)

theorem bgpScaleQW_ge_one (w : ℕ) : (1 : ℚ) ≤ (bgpScaleW w : ℚ) := by
  exact_mod_cast le_trans (by norm_num : 1 ≤ 4) (bgpScaleW_ge_four w)

theorem bgpScaleQW_pos (w : ℕ) : (0 : ℚ) < (bgpScaleW w : ℚ) :=
  lt_of_lt_of_le one_pos (bgpScaleQW_ge_one w)

theorem bgpScaleR_le_bgpScaleWR (w : ℕ) :
    (bgpScale : ℝ) ≤ (bgpScaleW w : ℝ) := by
  exact_mod_cast bgpScale_le_bgpScaleW w

/-- Displacement bridge at the word-coupled scale. -/
theorem D_U_le_two_bgpScaleW (w : ℕ) : D_U ≤ 2 * (bgpScaleW w : ℝ) :=
  le_trans D_U_le_two_bgpScale (by nlinarith [bgpScaleR_le_bgpScaleWR w])

/-! ### The word-coupled params family -/

/-- **Word-coupled strict-cascade parameters** (the F1 (4/5)/(5/5) fix):
the `(1000, 300)` design scaled homogeneously by `bgpScaleW w`. -/
def bgpParamsNW (w : ℕ) : DynGateParams := bgpParamsNS (bgpScaleW w)

theorem bgpParamsNW_A_eq (w : ℕ) : (bgpParamsNW w).A = 1 := rfl

theorem bgpParamsNW_L_eq (w : ℕ) : (bgpParamsNW w).L = 1 := rfl

theorem bgpParamsNW_cμ_def (w : ℕ) :
    (bgpParamsNW w).cμ = 1000 * (bgpScaleW w : ℝ) := rfl

theorem bgpParamsNW_cα_def (w : ℕ) :
    (bgpParamsNW w).cα = 300 * (bgpScaleW w : ℝ) := rfl

theorem bgpParamsNW_cμ_pos (w : ℕ) : 0 < (bgpParamsNW w).cμ := by
  rw [bgpParamsNW_cμ_def]
  nlinarith [bgpScaleWR_pos w]

theorem bgpParamsNW_cα_pos (w : ℕ) : 0 < (bgpParamsNW w).cα := by
  rw [bgpParamsNW_cα_def]
  nlinarith [bgpScaleWR_pos w]

theorem bgpParamsNW_cμ_ge_1000 (w : ℕ) : (1000 : ℝ) ≤ (bgpParamsNW w).cμ := by
  rw [bgpParamsNW_cμ_def]
  nlinarith [bgpScaleWR_ge_one w]

theorem bgpParamsNW_cα_ge_300 (w : ℕ) : (300 : ℝ) ≤ (bgpParamsNW w).cα := by
  rw [bgpParamsNW_cα_def]
  nlinarith [bgpScaleWR_ge_one w]

/-- Full regime window at the word-coupled scale:
`cμ/4 = 250·sW < cα = 300·sW < cμ/2 = 500·sW`. -/
theorem bgpParamsNW_regime_window (w : ℕ) :
    (bgpParamsNW w).cμ * (1 / 4 : ℝ) ^ (bgpParamsNW w).L < (bgpParamsNW w).cα ∧
      (bgpParamsNW w).cα < (bgpParamsNW w).cμ * (1 / 2 : ℝ) ^ (bgpParamsNW w).L := by
  rw [bgpParamsNW_cμ_def, bgpParamsNW_cα_def, bgpParamsNW_L_eq]
  constructor <;> nlinarith [bgpScaleWR_pos w]

/-- χ leak margin at the word-coupled scale: `cμ/2 − cα = 200·bgpScaleW`. -/
theorem bgpParamsNW_chi_leak_eq (w : ℕ) :
    (bgpParamsNW w).cμ * (1 / 2 : ℝ) ^ (bgpParamsNW w).L - (bgpParamsNW w).cα =
      200 * (bgpScaleW w : ℝ) := by
  rw [bgpParamsNW_cμ_def, bgpParamsNW_cα_def, bgpParamsNW_L_eq]
  ring

theorem bgpParamsNW_chi_leak_strict (w : ℕ) :
    0 < (bgpParamsNW w).cμ * (1 / 2 : ℝ) ^ (bgpParamsNW w).L - (bgpParamsNW w).cα := by
  rw [bgpParamsNW_chi_leak_eq]
  nlinarith [bgpScaleWR_pos w]

theorem bgpParamsNW_leakLambda_pos (w : ℕ) :
    0 < DynChiLeak.leakLambda (bgpParamsNW w).cμ (bgpParamsNW w).cα (bgpParamsNW w).L := by
  simpa [DynChiLeak.leakLambda] using bgpParamsNW_chi_leak_strict w

/-- κ cascade margin at the word-coupled scale: `cα − cμ/4 = 50·bgpScaleW`. -/
theorem bgpParamsNW_kappa_cascade_eq (w : ℕ) :
    (bgpParamsNW w).cα - (bgpParamsNW w).cμ * (1 / 4 : ℝ) ^ (bgpParamsNW w).L =
      50 * (bgpScaleW w : ℝ) := by
  rw [bgpParamsNW_cμ_def, bgpParamsNW_cα_def, bgpParamsNW_L_eq]
  ring

theorem bgpParamsNW_kappa_cascade_strict (w : ℕ) :
    0 < (bgpParamsNW w).cα - (bgpParamsNW w).cμ * (1 / 4 : ℝ) ^ (bgpParamsNW w).L := by
  rw [bgpParamsNW_kappa_cascade_eq]
  nlinarith [bgpScaleWR_pos w]

/-- Settled u-rate at the word-coupled scale:
`cμ·(3/4) − cα = 450·bgpScaleW`. -/
theorem bgpParamsNW_settled_rate_eq (w : ℕ) :
    (bgpParamsNW w).cμ * (3 / 4 : ℝ) ^ (bgpParamsNW w).L - (bgpParamsNW w).cα =
      450 * (bgpScaleW w : ℝ) := by
  rw [bgpParamsNW_cμ_def, bgpParamsNW_cα_def, bgpParamsNW_L_eq]
  ring

theorem bgpParamsNW_settled_rate_pos (w : ℕ) :
    0 < (bgpParamsNW w).cμ * (3 / 4 : ℝ) ^ (bgpParamsNW w).L - (bgpParamsNW w).cα := by
  rw [bgpParamsNW_settled_rate_eq]
  nlinarith [bgpScaleWR_pos w]

/-- Word-coupled settled u-drift rate (the `selectorUSettledRate_N` sibling). -/
def selectorUSettledRate_NW (w : ℕ) : ℝ :=
  (bgpParamsNW w).cμ * (3 / 4 : ℝ) ^ (bgpParamsNW w).L - (bgpParamsNW w).cα

theorem selectorUSettledRate_NW_eq (w : ℕ) :
    selectorUSettledRate_NW w = 450 * (bgpScaleW w : ℝ) :=
  bgpParamsNW_settled_rate_eq w

theorem selectorUSettledRate_NW_pos (w : ℕ) : 0 < selectorUSettledRate_NW w :=
  bgpParamsNW_settled_rate_pos w

/-- The word-coupled settled rate dominates the N rate (`bgpScale ≤ bgpScaleW`),
so every fixed-rate-`450·bgpScale` drift envelope transfers to the NW family
for free. -/
theorem selectorUSettledRate_N_le_NW (w : ℕ) :
    selectorUSettledRate_N ≤ selectorUSettledRate_NW w := by
  rw [selectorUSettledRate_N_eq, selectorUSettledRate_NW_eq]
  nlinarith [bgpScaleR_le_bgpScaleWR w, bgpScaleR_pos]

/-- Ctrl-drift budget at the word-coupled scale (monotone transfer of
`bgpParamsN_ctrl_drift`). -/
theorem bgpParamsNW_ctrl_drift (w : ℕ) :
    D_U / (bgpParamsNW w).cμ ^ 2 ≤ r_LE_U / 4 := by
  have hD := D_U_le_two_bgpScale
  have hs4 := bgpScaleWR_ge_four w
  have hsN : (bgpScale : ℝ) ≤ (bgpScaleW w : ℝ) := bgpScaleR_le_bgpScaleWR w
  have hs0 := bgpScaleWR_pos w
  have hcμ2 : (0 : ℝ) < (bgpParamsNW w).cμ ^ 2 := pow_pos (bgpParamsNW_cμ_pos w) 2
  rw [div_le_div_iff₀ hcμ2 (by norm_num : (0 : ℝ) < 4)]
  rw [bgpParamsNW_cμ_def] at hcμ2 ⊢
  unfold r_LE_U
  nlinarith [mul_pos hs0 hs0, sq_nonneg ((bgpScaleW w : ℝ) - 1), bgpScaleR_pos]

/-! ### Word-coupled warm gain -/

/-- Word-coupled diagonal warm-gain constant (the `bgpWarmGainCN` sibling
at scale `bgpScaleW w`; keeps `cμ³ ≤ C` and `card ≤ C` at the new scale). -/
def bgpWarmGainCNW (w : ℕ) : ℚ := 1734736490 * (bgpScaleW w : ℚ) ^ 6

/-- Word-coupled warm gain at word `w` (diagonal: the scale index and the
`6^w` index are the same word). -/
def bgpWarmGainQNW (w : ℕ) : ℚ := bgpWarmGainCNW w * (6 : ℚ) ^ w

theorem bgpWarmGainCNW_nat_eq (w : ℕ) :
    bgpWarmGainCNW w = ((1734736490 * bgpScaleW w ^ 6 : ℕ) : ℚ) := by
  unfold bgpWarmGainCNW
  push_cast
  ring

theorem bgpWarmGainCNW_pos (w : ℕ) : 0 < bgpWarmGainCNW w := by
  unfold bgpWarmGainCNW
  nlinarith [pow_pos (bgpScaleQW_pos w) 6]

theorem bgpWarmGainCNW_nonneg (w : ℕ) : 0 ≤ bgpWarmGainCNW w :=
  (bgpWarmGainCNW_pos w).le

theorem bgpWarmGainCNW_ge_base (w : ℕ) :
    (1734736490 : ℚ) ≤ bgpWarmGainCNW w := by
  have hpow : (1 : ℚ) ≤ (bgpScaleW w : ℚ) ^ 6 := one_le_pow₀ (bgpScaleQW_ge_one w)
  unfold bgpWarmGainCNW
  nlinarith [hpow]

theorem bgpWarmGainQNW_pos (w : ℕ) : 0 < bgpWarmGainQNW w := by
  unfold bgpWarmGainQNW
  exact mul_pos (bgpWarmGainCNW_pos w) (pow_pos (by norm_num) w)

theorem bgpWarmGainQNW_nonneg (w : ℕ) : 0 ≤ bgpWarmGainQNW w :=
  (bgpWarmGainQNW_pos w).le

/-- The N warm gain is dominated by the word-coupled one (diagonal index). -/
theorem bgpWarmGainQN_le_QNW (w : ℕ) :
    bgpWarmGainQN w ≤ bgpWarmGainQNW w := by
  have hCN : bgpWarmGainCN ≤ bgpWarmGainCNW w := by
    have hs : (bgpScale : ℚ) ≤ (bgpScaleW w : ℚ) := by
      exact_mod_cast bgpScale_le_bgpScaleW w
    have hs0 : (0 : ℚ) ≤ (bgpScale : ℚ) := bgpScaleQ_pos.le
    have hpow : (bgpScale : ℚ) ^ 6 ≤ (bgpScaleW w : ℚ) ^ 6 :=
      pow_le_pow_left₀ hs0 hs 6
    unfold bgpWarmGainCN bgpWarmGainCNW
    nlinarith [hpow]
  have hpow6 : (0 : ℚ) ≤ (6 : ℚ) ^ w := pow_nonneg (by norm_num) w
  unfold bgpWarmGainQN bgpWarmGainQNW
  exact mul_le_mul_of_nonneg_right hCN hpow6

theorem bgpWarmGainQNW_ge_base (w : ℕ) :
    (1734736490 : ℝ) ≤ ((bgpWarmGainQNW w : ℚ) : ℝ) := by
  have h : (1734736490 : ℚ) ≤ bgpWarmGainQNW w := by
    have hpow_ge : (1 : ℚ) ≤ (6 : ℚ) ^ w :=
      one_le_pow₀ (by norm_num : (1 : ℚ) ≤ 6)
    have := bgpWarmGainCNW_ge_base w
    unfold bgpWarmGainQNW
    nlinarith [bgpWarmGainCNW_nonneg w]
  exact_mod_cast h

/-- The word-coupled warm gain dominates the local-view cardinality. -/
theorem cardUniversalLocalView_le_warmGainCNW (w : ℕ) :
    ((Fintype.card UniversalLocalView : ℚ)) ≤ bgpWarmGainCNW w := by
  refine le_trans cardUniversalLocalView_le_warmGainCN ?_
  have hs : (bgpScale : ℚ) ≤ (bgpScaleW w : ℚ) := by
    exact_mod_cast bgpScale_le_bgpScaleW w
  have hpow : (bgpScale : ℚ) ^ 6 ≤ (bgpScaleW w : ℚ) ^ 6 :=
    pow_le_pow_left₀ bgpScaleQ_pos.le hs 6
  unfold bgpWarmGainCN bgpWarmGainCNW
  nlinarith [hpow]

/-- The word-coupled warm gain dominates the cube of the word-coupled clock
rate (headroom for degree-≤3 `cμ`-polynomial warm-phase transients). -/
theorem bgpParamsNW_cμ_cubed_le_warmGainCNW (w : ℕ) :
    (bgpParamsNW w).cμ ^ 3 ≤ ((bgpWarmGainCNW w : ℚ) : ℝ) := by
  have hsR := bgpScaleWR_ge_one w
  have hs0 := bgpScaleWR_pos w
  have hcast : ((bgpWarmGainCNW w : ℚ) : ℝ) =
      1734736490 * (bgpScaleW w : ℝ) ^ 6 := by
    unfold bgpWarmGainCNW
    push_cast
    ring
  rw [bgpParamsNW_cμ_def, hcast]
  have h36 : (bgpScaleW w : ℝ) ^ 3 ≤ (bgpScaleW w : ℝ) ^ 6 :=
    pow_le_pow_right₀ hsR (by norm_num)
  nlinarith [h36, pow_pos hs0 3, pow_pos hs0 6]

/-! ### The head-start budget: the arithmetic heart of the (5/5) fix -/

/-- `e^{200} ≤ 3^{200}` (numeric anchor for the crude window hulls). -/
theorem real_exp_200_le_three_pow : Real.exp (200 : ℝ) ≤ (3 : ℝ) ^ (200 : ℕ) := by
  have h1 : Real.exp (200 : ℝ) = Real.exp 1 ^ (200 : ℕ) := by
    rw [show (200 : ℝ) = ((200 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  rw [h1]
  refine pow_le_pow_left₀ (Real.exp_pos 1).le ?_ 200
  exact le_trans Real.exp_one_lt_d9.le (by norm_num)

/-- `20·3^{200} ≤ 6^{190}` (the `+220` buffer wins with `2^{190}/(20·3^{10})`
to spare). -/
theorem twenty_three_pow_le_six_pow :
    (20 : ℝ) * (3 : ℝ) ^ (200 : ℕ) ≤ (6 : ℝ) ^ (190 : ℕ) := by
  have h3 : (3 : ℝ) ^ (200 : ℕ) = (3 : ℝ) ^ (190 : ℕ) * (3 : ℝ) ^ (10 : ℕ) := by
    rw [← pow_add]
  have hsmall : (20 : ℝ) * (3 : ℝ) ^ (10 : ℕ) ≤ (2 : ℝ) ^ (190 : ℕ) := by
    norm_num
  calc (20 : ℝ) * (3 : ℝ) ^ (200 : ℕ)
      = (3 : ℝ) ^ (190 : ℕ) * ((20 : ℝ) * (3 : ℝ) ^ (10 : ℕ)) := by
        rw [h3]; ring
    _ ≤ (3 : ℝ) ^ (190 : ℕ) * (2 : ℝ) ^ (190 : ℕ) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = (6 : ℝ) ^ (190 : ℕ) := by
        rw [← mul_pow]; norm_num

/-- **The head-start W0 budget.**  The F1 depth weight `6^{inputLenU+O(1)}`
(with a `6^{30}` safety margin) times the crude `bgpScale·e^{200}` window
hull is beaten by the word-coupled kernel-mass denominator
`200·bgpScaleW w` against the readout budget `r_LE_U/4`:

`6^{L+30}·(bgpScale·e^{200}) ≤ (200·bgpScaleW w)·(r_LE_U/4)`.

This is the pure-arithmetic core of the now-TRUE F1-NW input (5/5)
(`W0 ≤ 6^{L+O(1)}·Box·mass` with `Box ≤ bgpScale·e^{200}` from the
rate-independent hull trapping and `mass ≤ 1/(200·bgpScaleW w)` from the
`[0, π/6]` u-kernel at the word-coupled rates). -/
theorem bgpScaleW_beats_depth_weight (w : ℕ) :
    (6 : ℝ) ^ (MachineInstance.inputLenU 1 w + 30) *
        ((bgpScale : ℝ) * Real.exp (200 : ℝ)) ≤
      200 * (bgpScaleW w : ℝ) * (r_LE_U / 4) := by
  set L := MachineInstance.inputLenU 1 w with hLdef
  have hsW : (bgpScaleW w : ℝ) = (bgpScale : ℝ) * (6 : ℝ) ^ (L + 220) := by
    unfold bgpScaleW bgpHeadStartN
    push_cast
    ring
  have hpow_split : (6 : ℝ) ^ (L + 220) =
      (6 : ℝ) ^ (L + 30) * (6 : ℝ) ^ (190 : ℕ) := by
    rw [← pow_add]
  have hp0 : (0 : ℝ) < (6 : ℝ) ^ (L + 30) := by positivity
  have hs0 : (0 : ℝ) < (bgpScale : ℝ) := bgpScaleR_pos
  have hb : (0 : ℝ) ≤ (6 : ℝ) ^ (L + 30) * (bgpScale : ℝ) :=
    (mul_pos hp0 hs0).le
  have h1 : (6 : ℝ) ^ (L + 30) * ((bgpScale : ℝ) * Real.exp (200 : ℝ)) ≤
      (6 : ℝ) ^ (L + 30) * (bgpScale : ℝ) * (3 : ℝ) ^ (200 : ℕ) := by
    calc (6 : ℝ) ^ (L + 30) * ((bgpScale : ℝ) * Real.exp (200 : ℝ))
        = ((6 : ℝ) ^ (L + 30) * (bgpScale : ℝ)) * Real.exp (200 : ℝ) := by
          ring
      _ ≤ ((6 : ℝ) ^ (L + 30) * (bgpScale : ℝ)) * (3 : ℝ) ^ (200 : ℕ) :=
          mul_le_mul_of_nonneg_left real_exp_200_le_three_pow hb
  have h2 : (6 : ℝ) ^ (L + 30) * (bgpScale : ℝ) * (3 : ℝ) ^ (200 : ℕ) ≤
      (6 : ℝ) ^ (L + 30) * (bgpScale : ℝ) * ((6 : ℝ) ^ (190 : ℕ) / 20) := by
    have hcap : (3 : ℝ) ^ (200 : ℕ) ≤ (6 : ℝ) ^ (190 : ℕ) / 20 := by
      linarith [twenty_three_pow_le_six_pow]
    exact mul_le_mul_of_nonneg_left hcap hb
  have hRHS : 200 * (bgpScaleW w : ℝ) * (r_LE_U / 4) =
      (6 : ℝ) ^ (L + 30) * (bgpScale : ℝ) * ((6 : ℝ) ^ (190 : ℕ) / 20) := by
    rw [hsW, hpow_split]
    unfold r_LE_U
    ring
  rw [hRHS]
  exact le_trans h1 h2

/-- `600·3^{200} ≤ 6^{190}` (sharp sibling of `twenty_three_pow_le_six_pow`:
the same `+220` buffer still wins with `2^{190}/(600·3^{10})` to spare;
this is the 30× tightening feeding the `r_LE_U/120` head-start row). -/
theorem six_hundred_three_pow_le_six_pow :
    (600 : ℝ) * (3 : ℝ) ^ (200 : ℕ) ≤ (6 : ℝ) ^ (190 : ℕ) := by
  have h3 : (3 : ℝ) ^ (200 : ℕ) = (3 : ℝ) ^ (190 : ℕ) * (3 : ℝ) ^ (10 : ℕ) := by
    rw [← pow_add]
  have hsmall : (600 : ℝ) * (3 : ℝ) ^ (10 : ℕ) ≤ (2 : ℝ) ^ (190 : ℕ) := by
    norm_num
  calc (600 : ℝ) * (3 : ℝ) ^ (200 : ℕ)
      = (3 : ℝ) ^ (190 : ℕ) * ((600 : ℝ) * (3 : ℝ) ^ (10 : ℕ)) := by
        rw [h3]; ring
    _ ≤ (3 : ℝ) ^ (190 : ℕ) * (2 : ℝ) ^ (190 : ℕ) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = (6 : ℝ) ^ (190 : ℕ) := by
        rw [← mul_pow]; norm_num

/-- **The sharp head-start W0 budget** (30× sibling of
`bgpScaleW_beats_depth_weight`, against `r_LE_U/120` instead of `r_LE_U/4`):

`6^{L+30}·(bgpScale·e^{200}) ≤ (200·bgpScaleW w)·(r_LE_U/120)`.

Same proof, with the `6^{190}/20` cap replaced by `6^{190}/600` via
`six_hundred_three_pow_le_six_pow`.  This is the arithmetic core of the
sharp F1 write-start export (`epsIn := r_LE_U/60` for the S2 `M₁`
interface). -/
theorem bgpScaleW_beats_depth_weight_sharp (w : ℕ) :
    (6 : ℝ) ^ (MachineInstance.inputLenU 1 w + 30) *
        ((bgpScale : ℝ) * Real.exp (200 : ℝ)) ≤
      200 * (bgpScaleW w : ℝ) * (r_LE_U / 120) := by
  set L := MachineInstance.inputLenU 1 w with hLdef
  have hsW : (bgpScaleW w : ℝ) = (bgpScale : ℝ) * (6 : ℝ) ^ (L + 220) := by
    unfold bgpScaleW bgpHeadStartN
    push_cast
    ring
  have hpow_split : (6 : ℝ) ^ (L + 220) =
      (6 : ℝ) ^ (L + 30) * (6 : ℝ) ^ (190 : ℕ) := by
    rw [← pow_add]
  have hp0 : (0 : ℝ) < (6 : ℝ) ^ (L + 30) := by positivity
  have hs0 : (0 : ℝ) < (bgpScale : ℝ) := bgpScaleR_pos
  have hb : (0 : ℝ) ≤ (6 : ℝ) ^ (L + 30) * (bgpScale : ℝ) :=
    (mul_pos hp0 hs0).le
  have h1 : (6 : ℝ) ^ (L + 30) * ((bgpScale : ℝ) * Real.exp (200 : ℝ)) ≤
      (6 : ℝ) ^ (L + 30) * (bgpScale : ℝ) * (3 : ℝ) ^ (200 : ℕ) := by
    calc (6 : ℝ) ^ (L + 30) * ((bgpScale : ℝ) * Real.exp (200 : ℝ))
        = ((6 : ℝ) ^ (L + 30) * (bgpScale : ℝ)) * Real.exp (200 : ℝ) := by
          ring
      _ ≤ ((6 : ℝ) ^ (L + 30) * (bgpScale : ℝ)) * (3 : ℝ) ^ (200 : ℕ) :=
          mul_le_mul_of_nonneg_left real_exp_200_le_three_pow hb
  have h2 : (6 : ℝ) ^ (L + 30) * (bgpScale : ℝ) * (3 : ℝ) ^ (200 : ℕ) ≤
      (6 : ℝ) ^ (L + 30) * (bgpScale : ℝ) * ((6 : ℝ) ^ (190 : ℕ) / 600) := by
    have hcap : (3 : ℝ) ^ (200 : ℕ) ≤ (6 : ℝ) ^ (190 : ℕ) / 600 := by
      linarith [six_hundred_three_pow_le_six_pow]
    exact mul_le_mul_of_nonneg_left hcap hb
  have hRHS : 200 * (bgpScaleW w : ℝ) * (r_LE_U / 120) =
      (6 : ℝ) ^ (L + 30) * (bgpScale : ℝ) * ((6 : ℝ) ^ (190 : ℕ) / 600) := by
    rw [hsW, hpow_split]
    unfold r_LE_U
    ring
  rw [hRHS]
  exact le_trans h1 h2

end Ripple.BoundedUniversality.BGP
