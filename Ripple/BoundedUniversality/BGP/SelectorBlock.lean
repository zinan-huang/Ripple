import Ripple.BoundedUniversality.BGP.LogisticSharpen
import Ripple.BoundedUniversality.BGP.SelectorPolynomial

/-!
Ripple.BoundedUniversality.BGP.SelectorBlock
------------------------
Polynomial realization of the clock-driven selector gate phase.

Design source: `notes/gpt-clock-driven-selector-r2.md`, §6 (autonomous polynomial
ODE with phase-clock gates) and §7 (where `μ` enters).  The gate-phase weight
dynamics

  `λ_v' = gain · P_v(x_hold) · λ_v (1 - λ_v)`,   `G' = gain`,

are realized by an honest polynomial vector field over the extended state:
`gain` is a polynomial in the clock/precision coordinates, `P_v` is the coarse
Bernstein readout polynomial in the held configuration, and `λ_v (1 - λ_v)` is
the polynomial `X λ_v - X λ_v ^ 2`.  No coordinate carries variable degree and
no coefficient depends non-polynomially on `μ`; the exponential precision
`e^{-α ΔG}` comes purely from the integrated gain `ΔG = G b - G a`.

This file is the bridge from the self-contained selector MATH layer
(`LogisticSharpen.lean`, deliverables 1–6) to the autonomous dynamic field: it
shows a *solution* of the polynomial gate block achieves the clock-driven
mixture error `card · R · e^{-α ΔG}`, hence `≤ e^{-μ}` once the gain meets the
budget.  Deliverables 7 (Hold/Spec) and 8 (Cycle/RobustStep) compose on top.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open MvPolynomial Set

variable {N : ℕ}

/-- Polynomial RHS realizing the logistic gate-phase ODE for one selector weight
coordinate: `gain · P_v · λ_v (1 - λ_v)`, expressed over the extended state with
`λ_v (1 - λ_v) = X λ_v - X λ_v ^ 2`. -/
def selectorGateFieldPoly (gainPoly Ppoly : MvPolynomial (Fin N) ℚ)
    (lamCoord : Fin N) : MvPolynomial (Fin N) ℚ :=
  gainPoly * Ppoly * (X lamCoord - X lamCoord ^ 2)

/-- Realization identity: evaluating the polynomial gate field at the state gives
exactly the logistic RHS `gain · P_v · λ_v (1 - λ_v)`. -/
@[simp] theorem eval₂_selectorGateFieldPoly
    (gainPoly Ppoly : MvPolynomial (Fin N) ℚ) (lamCoord : Fin N)
    (x : Fin N → ℝ) :
    eval₂ (algebraMap ℚ ℝ) x (selectorGateFieldPoly gainPoly Ppoly lamCoord) =
      eval₂ (algebraMap ℚ ℝ) x gainPoly * eval₂ (algebraMap ℚ ℝ) x Ppoly *
        (x lamCoord * (1 - x lamCoord)) := by
  simp only [selectorGateFieldPoly, eval₂_mul, eval₂_sub, eval₂_pow, eval₂_X]
  ring

/-- Full `λ_v` field of the autonomous selector system (W2): the phase-clock-gated
sum of the reset Reach term `χ_reset · κ · (1/2 - λ_v)` and the gate logistic term
`χ_gate · gain · P_v · λ_v (1 - λ_v)`.  Polynomial in the extended state; the phase
gates `χ_reset, χ_gate` are polynomials in the clock coordinates, so on the reset
window (`χ_reset = 1, χ_gate = 0`) this is the Reach field of `reset_to_half_bound`
and on the gate window (`χ_reset = 0, χ_gate = 1`) it is the logistic gate field. -/
def selectorResetGateFieldPoly
    (chiReset chiGate kappa gainPoly Ppoly : MvPolynomial (Fin N) ℚ)
    (lamCoord : Fin N) : MvPolynomial (Fin N) ℚ :=
  chiReset * kappa * (C (1 / 2 : ℚ) - X lamCoord)
    + chiGate * selectorGateFieldPoly gainPoly Ppoly lamCoord

/-- Realization identity for the full `λ_v` field. -/
@[simp] theorem eval₂_selectorResetGateFieldPoly
    (chiReset chiGate kappa gainPoly Ppoly : MvPolynomial (Fin N) ℚ)
    (lamCoord : Fin N) (x : Fin N → ℝ) :
    eval₂ (algebraMap ℚ ℝ) x
        (selectorResetGateFieldPoly chiReset chiGate kappa gainPoly Ppoly lamCoord) =
      eval₂ (algebraMap ℚ ℝ) x chiReset * eval₂ (algebraMap ℚ ℝ) x kappa *
          (1 / 2 - x lamCoord)
        + eval₂ (algebraMap ℚ ℝ) x chiGate *
          (eval₂ (algebraMap ℚ ℝ) x gainPoly * eval₂ (algebraMap ℚ ℝ) x Ppoly *
            (x lamCoord * (1 - x lamCoord))) := by
  simp only [selectorResetGateFieldPoly, eval₂_add, eval₂_mul, eval₂_sub, eval₂_C,
    eval₂_X, eval₂_selectorGateFieldPoly, map_div₀, map_one, map_ofNat]

/-- Polynomial realizing the dynamic mixture target `∑_v λ_v · A_v(u)` as the
config Reach target: the weight `λ_v` is read from coordinate `lamCoords v`, and
the branch values `A_v(u)` from the `u`-block coordinates `uCoords` (via `rename`).
This is the config Reach target whose evaluation is `selectorMixTarget`. -/
def selectorMixFieldPoly {V : Type*} [Fintype V] {d : ℕ} {B : ℕ}
    (branch : V → BranchData d B) (lamCoords : V → Fin N) (uCoords : Fin d → Fin N)
    (i : Fin d) : MvPolynomial (Fin N) ℚ :=
  ∑ v, X (lamCoords v) * MvPolynomial.rename uCoords (BranchData.branchPoly (branch v) i)

/-- Realization identity for the mixture field: evaluation gives the weighted
branch mixture `∑_v λ_v · evalBranch (branch v) u`. -/
@[simp] theorem eval₂_selectorMixFieldPoly {V : Type*} [Fintype V] {d B : ℕ}
    (branch : V → BranchData d B) (lamCoords : V → Fin N) (uCoords : Fin d → Fin N)
    (i : Fin d) (x : Fin N → ℝ) :
    eval₂ (algebraMap ℚ ℝ) x (selectorMixFieldPoly branch lamCoords uCoords i) =
      ∑ v, x (lamCoords v) *
        BranchData.evalBranch (branch v) (fun j => x (uCoords j)) i := by
  unfold selectorMixFieldPoly
  rw [← MvPolynomial.coe_eval₂Hom, map_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp only [MvPolynomial.coe_eval₂Hom, eval₂_mul, eval₂_X, MvPolynomial.eval₂_rename,
    BranchData.eval₂_branchPoly]
  rfl

/-- Integrated-gain coordinate field: `G' = χ_gate · gain` — the gain accumulates
only during the gate phase. -/
def selectorGainFieldPoly (chiGate gainPoly : MvPolynomial (Fin N) ℚ) :
    MvPolynomial (Fin N) ℚ :=
  chiGate * gainPoly

@[simp] theorem eval₂_selectorGainFieldPoly
    (chiGate gainPoly : MvPolynomial (Fin N) ℚ) (x : Fin N → ℝ) :
    eval₂ (algebraMap ℚ ℝ) x (selectorGainFieldPoly chiGate gainPoly) =
      eval₂ (algebraMap ℚ ℝ) x chiGate * eval₂ (algebraMap ℚ ℝ) x gainPoly := by
  simp only [selectorGainFieldPoly, eval₂_mul]

/-- **Gate-window reduction.**  Where the phase gates read `χ_reset = 0`,
`χ_gate = 1`, the combined `λ_v` field equals the pure logistic gate field — so a
solution restricted to the gate window is a `SelectorGateBlock`. -/
theorem eval₂_selectorResetGateFieldPoly_gate
    (chiReset chiGate kappa gainPoly Ppoly : MvPolynomial (Fin N) ℚ)
    (lamCoord : Fin N) (x : Fin N → ℝ)
    (hreset0 : eval₂ (algebraMap ℚ ℝ) x chiReset = 0)
    (hgate1 : eval₂ (algebraMap ℚ ℝ) x chiGate = 1) :
    eval₂ (algebraMap ℚ ℝ) x
        (selectorResetGateFieldPoly chiReset chiGate kappa gainPoly Ppoly lamCoord) =
      eval₂ (algebraMap ℚ ℝ) x (selectorGateFieldPoly gainPoly Ppoly lamCoord) := by
  rw [eval₂_selectorResetGateFieldPoly, eval₂_selectorGateFieldPoly, hreset0, hgate1]
  ring

/-- **Reset-window reduction.**  Where the phase gates read `χ_reset = 1`,
`χ_gate = 0`, the combined `λ_v` field equals the Reach field toward `1/2`
(`κ · (1/2 - λ_v)`) — so a solution restricted to the reset window obeys
`reset_to_half_bound`. -/
theorem eval₂_selectorResetGateFieldPoly_reset
    (chiReset chiGate kappa gainPoly Ppoly : MvPolynomial (Fin N) ℚ)
    (lamCoord : Fin N) (x : Fin N → ℝ)
    (hreset1 : eval₂ (algebraMap ℚ ℝ) x chiReset = 1)
    (hgate0 : eval₂ (algebraMap ℚ ℝ) x chiGate = 0) :
    eval₂ (algebraMap ℚ ℝ) x
        (selectorResetGateFieldPoly chiReset chiGate kappa gainPoly Ppoly lamCoord) =
      eval₂ (algebraMap ℚ ℝ) x kappa * (1 / 2 - x lamCoord) := by
  rw [eval₂_selectorResetGateFieldPoly, hreset1, hgate0]
  ring

/-- A solution of the polynomial selector-gate block over `[a, b]`.

The integrated gain `G = state · Gcoord` and the weights `λ_v = state · lamCoord v`
evolve by the realized polynomial field (`gainPoly`, `selectorGateFieldPoly`); the
coarse-margin readouts `P_v = eval Ppoly v` and the gain rate `eval gainPoly` are
themselves polynomials in the extended state. -/
structure SelectorGateBlock (V : Type*) [Fintype V] (N : ℕ) where
  state : ℝ → Fin N → ℝ
  Gcoord : Fin N
  lamCoord : V → Fin N
  gainPoly : MvPolynomial (Fin N) ℚ
  Ppoly : V → MvPolynomial (Fin N) ℚ
  a : ℝ
  b : ℝ
  hab : a ≤ b
  /-- The integrated gain coordinate evolves by `G' = gain`. -/
  G_ode : ∀ t ∈ Ico a b,
    HasDerivWithinAt (fun τ => state τ Gcoord)
      (eval₂ (algebraMap ℚ ℝ) (state t) gainPoly) (Ici t) t
  /-- Each selector weight evolves by the realized polynomial gate field. -/
  lam_ode : ∀ v, ∀ t ∈ Ico a b,
    HasDerivWithinAt (fun τ => state τ (lamCoord v))
      (eval₂ (algebraMap ℚ ℝ) (state t)
        (selectorGateFieldPoly gainPoly (Ppoly v) (lamCoord v))) (Ici t) t
  G_cont : ContinuousOn (fun t => state t Gcoord) (Icc a b)
  lam_cont : ∀ v, ContinuousOn (fun t => state t (lamCoord v)) (Icc a b)

namespace SelectorGateBlock

variable {V : Type*} [Fintype V]

/-- Gain rate readout. -/
def gainRate (blk : SelectorGateBlock V N) (t : ℝ) : ℝ :=
  eval₂ (algebraMap ℚ ℝ) (blk.state t) blk.gainPoly

/-- Coarse-margin readout for view `v`. -/
def Pval (blk : SelectorGateBlock V N) (v : V) (t : ℝ) : ℝ :=
  eval₂ (algebraMap ℚ ℝ) (blk.state t) (blk.Ppoly v)

/-- Selector weight trajectory for view `v`. -/
def lam (blk : SelectorGateBlock V N) (v : V) (t : ℝ) : ℝ :=
  blk.state t (blk.lamCoord v)

/-- Integrated gain trajectory. -/
def gain (blk : SelectorGateBlock V N) (t : ℝ) : ℝ := blk.state t blk.Gcoord

/-- The realized field puts each weight ODE in the logistic form
`λ_v' = gainRate · Pval v · λ_v (1 - λ_v)`. -/
theorem lam_logistic (blk : SelectorGateBlock V N) (v : V) :
    ∀ t ∈ Ico blk.a blk.b,
      HasDerivWithinAt (blk.lam v)
        (blk.gainRate t * blk.Pval v t * (blk.lam v t * (1 - blk.lam v t)))
        (Ici t) t := by
  intro t ht
  have h := blk.lam_ode v t ht
  rwa [eval₂_selectorGateFieldPoly] at h

end SelectorGateBlock

/-- **Avenue (e) capstone, gate block.**  A solution of the polynomial selector
gate block achieves the clock-driven mixture error: after the gate phase the
weighted branch mixture is within `card · R · e^{-α ΔG}` of the true branch value,
where `ΔG = G b - G a` is the integrated gain.  The vector field is polynomial;
the precision comes entirely from `ΔG`. -/
theorem selectorGateBlock_mix_error
    {V : Type*} [Fintype V] [DecidableEq V]
    (blk : SelectorGateBlock V N) (vstar : V) {α R : ℝ} (A : V → ℝ)
    (hα : 0 < α) (hR : 0 ≤ R)
    (hgain_nonneg : ∀ t ∈ Ico blk.a blk.b, 0 ≤ blk.gainRate t)
    (hunit : ∀ v, ∀ t ∈ Icc blk.a blk.b, 0 < blk.lam v t ∧ blk.lam v t < 1)
    (hreset : ∀ v, blk.lam v blk.a = 1 / 2)
    (hPtrue : ∀ t ∈ Ico blk.a blk.b, α ≤ blk.Pval vstar t)
    (hPfalse : ∀ v, v ≠ vstar → ∀ t ∈ Ico blk.a blk.b, blk.Pval v t ≤ -α)
    (hA : ∀ v, |A v| ≤ R) :
    |(∑ v, blk.lam v blk.b * A v) - A vstar| ≤
      (Fintype.card V : ℝ) * R *
        Real.exp (-α * (blk.gain blk.b - blk.gain blk.a)) :=
  selector_mix_error vstar A blk.hab hα hR hgain_nonneg blk.G_ode blk.G_cont
    blk.lam_logistic blk.lam_cont hunit hreset hPtrue hPfalse hA

/-- **Budget met (gate block).**  Once the integrated gain satisfies the
logarithmic lower bound, the polynomial selector gate block drives the per-step
selector error below `e^{-μ}` — the threshold a fixed-degree polynomial selector
cannot meet. -/
theorem selectorGateBlock_per_step_error
    {V : Type*} [Fintype V] [DecidableEq V]
    (blk : SelectorGateBlock V N) (vstar : V) {α R μ : ℝ} (A : V → ℝ)
    (hα : 0 < α) (hR : 0 ≤ R)
    (hgain_nonneg : ∀ t ∈ Ico blk.a blk.b, 0 ≤ blk.gainRate t)
    (hunit : ∀ v, ∀ t ∈ Icc blk.a blk.b, 0 < blk.lam v t ∧ blk.lam v t < 1)
    (hreset : ∀ v, blk.lam v blk.a = 1 / 2)
    (hPtrue : ∀ t ∈ Ico blk.a blk.b, α ≤ blk.Pval vstar t)
    (hPfalse : ∀ v, v ≠ vstar → ∀ t ∈ Ico blk.a blk.b, blk.Pval v t ≤ -α)
    (hA : ∀ v, |A v| ≤ R)
    (hcardR : 0 < (Fintype.card V : ℝ) * R)
    (hgain : Real.log ((Fintype.card V : ℝ) * R) + μ ≤
      α * (blk.gain blk.b - blk.gain blk.a)) :
    |(∑ v, blk.lam v blk.b * A v) - A vstar| ≤ Real.exp (-μ) :=
  per_step_error_le_exp_of_mix
    (selectorGateBlock_mix_error blk vstar A hα hR hgain_nonneg hunit hreset
      hPtrue hPfalse hA)
    hcardR hgain

/-- **Coarse margin bridge (deliverable 4 → gate block).**  When the block's
readout `Pval v` is the fixed Bernstein SEL1 weight `Λ v` shifted by `1/2`, the
separation `errSel < 1/2` supplies the gate-phase margins consumed by
`selectorGateBlock_mix_error`: `Pval vstar ≥ α` and `Pval v ≤ -α` with
`α = 1/2 - errSel`.  The margin is fixed; the exponential precision comes from the
logistic gate phase, not from this readout.  (r2 §6: `P_v = Λ_N(v) - 1/2`,
`α = 1/2 - errSel`, require `errSel < 1/2`.) -/
theorem selectorGateBlock_margin_of_sel1
    {V : Type*} [Fintype V] (blk : SelectorGateBlock V N) (vstar : V)
    {Λ : V → ℝ → ℝ} {errSel : ℝ}
    (herr : errSel < 1 / 2)
    (hPdef : ∀ v t, blk.Pval v t = Λ v t - 1 / 2)
    (htrue : ∀ t ∈ Ico blk.a blk.b, 1 - errSel ≤ Λ vstar t)
    (hoff : ∀ v, v ≠ vstar → ∀ t ∈ Ico blk.a blk.b, Λ v t ≤ errSel) :
    (0 < 1 / 2 - errSel) ∧
      (∀ t ∈ Ico blk.a blk.b, 1 / 2 - errSel ≤ blk.Pval vstar t) ∧
      (∀ v, v ≠ vstar → ∀ t ∈ Ico blk.a blk.b,
        blk.Pval v t ≤ -(1 / 2 - errSel)) := by
  refine ⟨by linarith, ?_, ?_⟩
  · intro t ht
    have hm := (coarse_margin_of_sel1 vstar (fun v => Λ v t) herr (htrue t ht)
      (fun v hv => hoff v hv t ht)).2.1
    rw [hPdef]; linarith
  · intro v hv t ht
    have hm := (coarse_margin_of_sel1 vstar (fun v => Λ v t) herr (htrue t ht)
      (fun v hv => hoff v hv t ht)).2.2 v hv
    rw [hPdef]; linarith

/-- **`hunit` discharge (DOCTRINE avenue d).**  The logistic gate field keeps each
weight strictly inside `(0,1)`: given the two-sided gate ODE for `λ_v` (available
once the global solution is built) and any bounds on the gate coefficient
`gain · P_v` over the compact window, `0 < λ_v < 1` throughout.  This eliminates
`hunit` as a hypothesis — it is automatic for the realized polynomial gate. -/
theorem selectorGateBlock_unit_invariant
    {V : Type*} [Fintype V] (blk : SelectorGateBlock V N) (v : V) {K0 K1 δ : ℝ}
    (hder : ∀ t ∈ Icc blk.a blk.b,
      HasDerivAt (blk.lam v)
        (blk.gainRate t * blk.Pval v t * (blk.lam v t * (1 - blk.lam v t))) t)
    (hK0 : ∀ t ∈ Icc blk.a blk.b,
      |blk.gainRate t * blk.Pval v t * (1 - blk.lam v t)| ≤ K0)
    (hK1 : ∀ t ∈ Icc blk.a blk.b,
      |blk.gainRate t * blk.Pval v t * blk.lam v t| ≤ K1)
    (hδ : δ < 1 / 2) (hreset : |blk.lam v blk.a - 1 / 2| ≤ δ) :
    ∀ t ∈ Icc blk.a blk.b, 0 < blk.lam v t ∧ blk.lam v t < 1 := by
  refine logistic_unit_interval_invariant
    (A := fun t => blk.gainRate t * blk.Pval v t) (K0 := K0) (K1 := K1)
    blk.hab ?_ (blk.lam_cont v) ?_ ?_ hδ hreset
  · intro t ht; simpa only [] using hder t ht
  · intro t ht; simpa only [] using hK0 t ht
  · intro t ht; simpa only [] using hK1 t ht

end Ripple.BoundedUniversality.BGP
