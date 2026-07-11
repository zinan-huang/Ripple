import Ripple.BoundedUniversality.BGP.SelectorDyn
import Ripple.BoundedUniversality.BGP.SelectorBlock
import Ripple.BoundedUniversality.BGP.ContractField

/-!
Ripple.BoundedUniversality.BGP.SelectorField
------------------------
Extended polynomial field realizing the heterogeneous clock-driven selector
solution `SelectorDynSol` as an honest autonomous PIVP (keystone (B)).

This mirrors `ContractField.lean`'s `contractAssembledField` / `contractTupleTraj`
layout, but adds the two heterogeneous blocks the contract layout cannot host:

* the selector weights `λ_v` (one coordinate per view `v : V`), evolving by the
  reset+gate logistic field `selectorResetGateFieldPoly`, and
* the integrated gain `G`, evolving by `selectorGainFieldPoly` (`G' = χ_gate · gain`).

The config `z` block's Reach target is changed from the contract step polynomial
`F` to the dynamic mixture `selectorMixFieldPoly = ∑_v λ_v · A_v(u)` (which reads
both the held config `u` and the live selector state `λ_v`).  Everything else —
the sin/cos clock, `μ`,`α`, the dynamic gates `bGateZ`,`bGateU`, the held config
`u`, and the halt latch `a` — is identical to the contract layout.

Coordinate layout (`selectorDim d V = contractDim d + (card V + 1)`):
`[ contract block : s c μ α | bZ bU | z(d) | u(d) | a ] [ λ_v (card V) | G | warmGain ]`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Ripple.BoundedUniversality.Core
open scoped BigOperators
open MvPolynomial Set

variable {d B : ℕ}

/-! ## Selector phase schedule (period 2π, aligned with the sin/cos gate clock) -/

/-- The clock-driven selector's cycle schedule: cycles `[2πj, 2π(j+1)]` aligned with the
`sin`/`cos` gate clock (period `2π`), unlike the contract's period-1 `bgpSchedule`.  The
reset/gate/hold/write sub-windows live inside each `2π`-cycle; `cycleMid = 2πj + π` separates
the mixture-read half from the write half.  The read window is all of `ℝ`. -/
def selectorSchedule : PhaseSchedule where
  domain := Set.Ici 0
  cycleStart := fun j => 2 * Real.pi * (j : ℝ)
  cycleMid := fun j => 2 * Real.pi * (j : ℝ) + Real.pi
  cycleEnd := fun j => 2 * Real.pi * ((j : ℝ) + 1)
  -- The z-active window is the post-z-write READ window per cycle (NOT univ): the §3.3-faithful value.
  -- With `univ`, the headline's `hflag_read` is UNSATISFIABLE for halting w (it would demand z[haltCoord]
  -- be near every cycle's sticky flag at every t — impossible). The read window is the satisfiable value;
  -- the latch proofs only consume the premise on this window (via `stableWindow_subset_zActiveWindow`).
  zActiveWindow := fun j => Set.Icc (2 * Real.pi * (j : ℝ) + 5 * Real.pi / 6)
    (2 * Real.pi * (j : ℝ) + 7 * Real.pi / 6)
  stableWindow_subset_zActiveWindow := fun _ => subset_refl _
  cycleEnd_start_next := fun j => by push_cast; ring

/-! ## Extended coordinate layout -/

/-- The selector tail dimension: `card V` weight coordinates, the gain, and warmGain. -/
abbrev selectorTailDim (V : Type) [Fintype V] : ℕ := Fintype.card V + 2

/-- Extended state dimension: the contract layout plus the selector tail. -/
abbrev selectorDim (d : ℕ) (V : Type) [Fintype V] : ℕ :=
  contractDim d + selectorTailDim V

/-- Embed a contract coordinate into the extended state. -/
def selOfContract {d : ℕ} (V : Type) [Fintype V] (j : Fin (contractDim d)) :
    Fin (selectorDim d V) := Fin.castAdd (selectorTailDim V) j

/-- The selector-weight coordinate for view `v`. -/
def selLamCoord {d : ℕ} {V : Type} [Fintype V] (v : V) :
    Fin (selectorDim d V) :=
  Fin.natAdd (contractDim d) (Fin.castAdd 2 (Fintype.equivFin V v))

/-- The integrated-gain coordinate. -/
def selGCoord (d : ℕ) (V : Type) [Fintype V] :
    Fin (selectorDim d V) :=
  Fin.natAdd (contractDim d) (Fin.natAdd (Fintype.card V) (Fin.castAdd 1 (0 : Fin 1)))

/-- The warm-gain coordinate (derivative 0, init = g₀ · B^|w|).
Promotes the gain coefficient from a polynomial constant to a state variable,
making the PIVP vector field w-independent. -/
def selWarmGainCoord (d : ℕ) (V : Type) [Fintype V] :
    Fin (selectorDim d V) :=
  Fin.natAdd (contractDim d) (Fin.natAdd (Fintype.card V) (Fin.natAdd 1 (0 : Fin 1)))

/-- Embedded `z`-coordinate. -/
def selZ {d : ℕ} (V : Type) [Fintype V] (i : Fin d) : Fin (selectorDim d V) :=
  selOfContract V (contractZ i)

/-- Embedded `u`-coordinate. -/
def selU {d : ℕ} (V : Type) [Fintype V] (i : Fin d) : Fin (selectorDim d V) :=
  selOfContract V (contractU i)

/-! ## Clock polynomials over the extended state -/

noncomputable def selRP (d : ℕ) (V : Type) [Fintype V] (L : ℕ) :
    MvPolynomial (Fin (selectorDim d V)) ℚ :=
  (C (1 / 2 : ℚ) * (1 - X (selOfContract V (contractS d)))) ^ L

noncomputable def selQP (d : ℕ) (V : Type) [Fintype V] (L : ℕ) :
    MvPolynomial (Fin (selectorDim d V)) ℚ :=
  (C (1 / 2 : ℚ) * (1 + X (selOfContract V (contractS d)))) ^ L

noncomputable def selRPderiv (d : ℕ) (V : Type) [Fintype V] (L : ℕ) :
    MvPolynomial (Fin (selectorDim d V)) ℚ :=
  C (L : ℚ) * (C (1 / 2 : ℚ) * (1 - X (selOfContract V (contractS d)))) ^ (L - 1) *
    (-(C (1 / 2 : ℚ)) * X (selOfContract V (contractC d)))

noncomputable def selQPderiv (d : ℕ) (V : Type) [Fintype V] (L : ℕ) :
    MvPolynomial (Fin (selectorDim d V)) ℚ :=
  C (L : ℚ) * (C (1 / 2 : ℚ) * (1 + X (selOfContract V (contractS d)))) ^ (L - 1) *
    (C (1 / 2 : ℚ) * X (selOfContract V (contractC d)))

/-! ### Selector gate polynomials (realizable approximate gates) — the ordered 4-phase clock

`χ_reset = ((1+cos t)/2)^M` (≈1 at cycle start `2πj`, where `cos t ≈ 1`); `χ_gate =
((1+sin t)/2)^M` (≈1 at `2πj+π/2`, where `sin t ≈ 1`).  Within each `[2πj, 2π(j+1)]` cycle the
four phases occur IN ORDER — reset (`cos≈1`, `t≈2πj`) → gate (`sin≈1`, `t≈2πj+π/2`) → z-write
(config `bGateZ≈1` at `sin≈1`, `t≈2πj+π/2`) → u-write (`bGateU≈1` at `sin≈−1`, `t≈2πj+3π/2`).
The gate is `sin`-based (peak `2πj+π/2`) so it COMPLETES by the z-write, ensuring the gated
selection is captured by both config writes — the cos-based gate (peak `2πj+π`) would fire AFTER
the z-write and miss it.  The reset/gate overlap is harmless: the approximate-gate analysis
(`gate_mix_error_approx`) tracks the `χ_reset` residual `ρb`, which the growing gate gain
suppresses (`ρb·Cb·Kint·e^{−αΔG} → 0`).  `χ_reset` in the `cos` coordinate `contractC`,
`χ_gate` in the `sin` coordinate `contractS`. -/

noncomputable def selChiGatePoly (d : ℕ) (V : Type) [Fintype V] (M : ℕ) :
    MvPolynomial (Fin (selectorDim d V)) ℚ :=
  (C (1 / 2 : ℚ) * (1 + X (selOfContract V (contractS d)))) ^ M

noncomputable def selChiResetPoly (d : ℕ) (V : Type) [Fintype V] (M : ℕ) :
    MvPolynomial (Fin (selectorDim d V)) ℚ :=
  (C (1 / 2 : ℚ) * (1 + X (selOfContract V (contractC d)))) ^ M

/-- Reset-rate polynomial: the constant `κ₀` (the reset Reach rate). -/
noncomputable def selKappaPoly (d : ℕ) (V : Type) [Fintype V] (κ₀ : ℚ) :
    MvPolynomial (Fin (selectorDim d V)) ℚ :=
  C κ₀

/-- Gate-gain polynomial: `warmGain · α` — the warm-gain state coordinate times
the GROWING precision coordinate `α` (`α' = cα·α`, so `α = exp(cα·t)` grows),
giving the integrated gain `ΔG_j → ∞` that drives the per-cycle selector error
to zero.  The warm-gain coordinate is constant (`derivative = 0`) with initial
value `g₀ · B^|w|`, promoted from a polynomial coefficient to a state variable
to make the PIVP field w-independent. -/
noncomputable def selGainPoly (d : ℕ) (V : Type) [Fintype V] :
    MvPolynomial (Fin (selectorDim d V)) ℚ :=
  X (selWarmGainCoord d V) * X (selOfContract V (contractAlpha d))

/-- Rename a config-space polynomial into the extended state via the `z` block. -/
noncomputable def selRenameZ {d : ℕ} (V : Type) [Fintype V]
    (p : MvPolynomial (Fin d) ℚ) : MvPolynomial (Fin (selectorDim d V)) ℚ :=
  MvPolynomial.rename (selZ V) p

/-- The config Reach target polynomial: the dynamic branch mixture `∑_v λ_v · A_v(u)`
read off the extended state (weights from the `λ`-block, branch values from the
`u`-block). -/
noncomputable def selectorMixField {V : Type} [Fintype V]
    (branch : V → BranchData d B) (i : Fin d) :
    MvPolynomial (Fin (selectorDim d V)) ℚ :=
  selectorMixFieldPoly branch (fun v => selLamCoord v)
    (fun i => selU V i) i

/-! ## The extended polynomial field -/

/-- Extended assembled rational field over `Fin (selectorDim d V)`.  The contract
block is identical to `contractAssembledField` except the `z` Reach target is the
dynamic mixture `selectorMixField`; the appended tail carries the `λ_v` reset+gate
fields and the gain field.  The phase gates `chiReset`,`chiGate`,`kappa`,`gainPoly`
and the coarse readouts `Ppoly v` are polynomials in the extended state (clock and
held-config coordinates), supplied as data. -/
def selectorAssembledField (d B : ℕ) (V : Type) [Fintype V]
    (branch : V → BranchData d B)
    (chiReset chiGate kappa gainPoly : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (Ppoly : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) :
    Fin (selectorDim d V) → MvPolynomial (Fin (selectorDim d V)) ℚ :=
  Fin.append
    (Fin.append
      (fun k : Fin 4 =>
        if k = 0 then X (selOfContract V (contractC d)) else
        if k = 1 then -X (selOfContract V (contractS d)) else
        if k = 2 then C cμ else
          C cα * X (selOfContract V (contractAlpha d)))
      (Fin.append
        (fun k : Fin 2 =>
          if k = 0 then
            -((C cμ * selRP d V L + X (selOfContract V (contractMu d)) * selRPderiv d V L) *
              X (selOfContract V (contractGateZ d)))
          else
            -((C cμ * selQP d V L + X (selOfContract V (contractMu d)) * selQPderiv d V L) *
              X (selOfContract V (contractGateU d))))
        (Fin.append
          (fun i : Fin d =>
            C A * X (selOfContract V (contractAlpha d)) *
              X (selOfContract V (contractGateZ d)) *
              (selectorMixField branch i - X (selZ V i)))
          (Fin.append
            (fun i : Fin d =>
              C A * X (selOfContract V (contractAlpha d)) *
                X (selOfContract V (contractGateU d)) *
                (X (selZ V i) - X (selU V i)))
            (fun _ : Fin 1 =>
              C K * ((C (1 / 2 : ℚ) * (1 - X (selOfContract V (contractC d)))) ^ R) *
                (selRenameZ V HP - X (selOfContract V (contractA d))))))))
    (Fin.append
      (fun k : Fin (Fintype.card V) =>
        selectorResetGateFieldPoly chiReset chiGate kappa gainPoly
          (Ppoly ((Fintype.equivFin V).symm k)) (selLamCoord ((Fintype.equivFin V).symm k)))
      (Fin.append
        (fun _ : Fin 1 => selectorGainFieldPoly chiGate gainPoly)
        (fun _ : Fin 1 => 0)))

/-! ## Per-coordinate evaluation lemmas -/

variable {V : Type} [Fintype V] (branch : V → BranchData d B)
  (chiReset chiGate kappa gainPoly : MvPolynomial (Fin (selectorDim d V)) ℚ)
  (Ppoly : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
  (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ)

private lemma selectorAssembledField_s :
    selectorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selOfContract V (contractS d)) = X (selOfContract V (contractC d)) := by
  simp [selectorAssembledField, selOfContract, contractS]

private lemma selectorAssembledField_c :
    selectorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selOfContract V (contractC d)) = -X (selOfContract V (contractS d)) := by
  simp [selectorAssembledField, selOfContract, contractC, contractS]

private lemma selectorAssembledField_mu :
    selectorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selOfContract V (contractMu d)) = C cμ := by
  simp [selectorAssembledField, selOfContract, contractMu, contractS]

private lemma selectorAssembledField_alpha :
    selectorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selOfContract V (contractAlpha d)) =
      C cα * X (selOfContract V (contractAlpha d)) := by
  simp [selectorAssembledField, selOfContract, contractAlpha, contractS]

private lemma selectorAssembledField_bz :
    selectorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selOfContract V (contractGateZ d)) =
      -((C cμ * selRP d V L + X (selOfContract V (contractMu d)) * selRPderiv d V L) *
        X (selOfContract V (contractGateZ d))) := by
  simp [selectorAssembledField, selOfContract, contractGateZ]

private lemma selectorAssembledField_bu :
    selectorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selOfContract V (contractGateU d)) =
      -((C cμ * selQP d V L + X (selOfContract V (contractMu d)) * selQPderiv d V L) *
        X (selOfContract V (contractGateU d))) := by
  simp [selectorAssembledField, selOfContract, contractGateU]

private lemma selectorAssembledField_z (i : Fin d) :
    selectorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selZ V i) =
      C A * X (selOfContract V (contractAlpha d)) *
        X (selOfContract V (contractGateZ d)) *
        (selectorMixField branch i - X (selZ V i)) := by
  simp [selectorAssembledField, selZ, selOfContract, contractZ, contractTailZ]

private lemma selectorAssembledField_u (i : Fin d) :
    selectorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selU V i) =
      C A * X (selOfContract V (contractAlpha d)) *
        X (selOfContract V (contractGateU d)) *
        (X (selZ V i) - X (selU V i)) := by
  simp [selectorAssembledField, selU, selZ, selOfContract, contractU, contractTailU]

private lemma selectorAssembledField_a :
    selectorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selOfContract V (contractA d)) =
      C K * ((C (1 / 2 : ℚ) * (1 - X (selOfContract V (contractC d)))) ^ R) *
        (selRenameZ V HP - X (selOfContract V (contractA d))) := by
  simp [selectorAssembledField, selOfContract, contractA, contractTailA]

private lemma selectorAssembledField_lam (v : V) :
    selectorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selLamCoord v) =
      selectorResetGateFieldPoly chiReset chiGate kappa gainPoly (Ppoly v) (selLamCoord v) := by
  simp only [selectorAssembledField, selLamCoord, Fin.append_right, Fin.append_left,
    Equiv.symm_apply_apply]

private lemma selectorAssembledField_G :
    selectorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selGCoord d V) =
      selectorGainFieldPoly chiGate gainPoly := by
  simp [selectorAssembledField, selGCoord, Fin.append_right]
  rfl

private lemma selectorAssembledField_warmGain :
    selectorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selWarmGainCoord d V) = 0 := by
  simp [selectorAssembledField, selWarmGainCoord, Fin.append_right]
  rfl

/-! ## Halt latch over the heterogeneous selector solution -/

/-- A halt latch riding on the selector solution's config `z` (parallel to
`ContractHaltLatchSol`, which only reads `sol.z`). -/
structure SelectorHaltLatchSol
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    (Hval : (Fin d → ℝ) → ℝ) (K : ℝ) (R : ℕ) where
  a : ℝ → ℝ
  init_a : a 0 = 0
  ode_a : ∀ t : ℝ, HasDerivAt a (K * gPulse R t * (Hval (sol.z t) - a t)) t

/-! ## The selector trajectory -/

section Trajectory

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}

/-- The extended-state trajectory of a selector solution: the contract block
(`sin`,`cos`,`μ`,`α`,`bZ`,`bU`,`z`,`u`,`a`) followed by the selector weights
`λ_v` and the integrated gain `G`. -/
def selectorTupleTraj
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : SelectorHaltLatchSol sol Hval K R)
    (warmGainVal : ℝ) (t : ℝ) :
    Fin (selectorDim d V) → ℝ :=
  Fin.append
    (Fin.append
      (fun k : Fin 4 =>
        if k = 0 then Real.sin t else
        if k = 1 then Real.cos t else
        if k = 2 then sol.μ t else sol.α t)
      (Fin.append
        (fun k : Fin 2 =>
          if k = 0 then bGateZ p.L (sol.μ t) t else bGateU p.L (sol.μ t) t)
        (Fin.append (sol.z t) (Fin.append (sol.u t) (fun _ : Fin 1 => La.a t)))))
    (Fin.append
      (fun k : Fin (Fintype.card V) => sol.lam ((Fintype.equivFin V).symm k) t)
      (Fin.append
        (fun _ : Fin 1 => sol.G t)
        (fun _ : Fin 1 => warmGainVal)))

variable {sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv}
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : SelectorHaltLatchSol sol Hval K R)
    (warmGainVal : ℝ) (t : ℝ)

@[simp] lemma selectorTupleTraj_s :
    selectorTupleTraj sol La warmGainVal t (selOfContract V (contractS d)) = Real.sin t := by
  simp [selectorTupleTraj, selOfContract, contractS]

@[simp] lemma selectorTupleTraj_c :
    selectorTupleTraj sol La warmGainVal t (selOfContract V (contractC d)) = Real.cos t := by
  simp [selectorTupleTraj, selOfContract, contractC, contractS]

@[simp] lemma selectorTupleTraj_mu :
    selectorTupleTraj sol La warmGainVal t (selOfContract V (contractMu d)) = sol.μ t := by
  simp [selectorTupleTraj, selOfContract, contractMu]

@[simp] lemma selectorTupleTraj_alpha :
    selectorTupleTraj sol La warmGainVal t (selOfContract V (contractAlpha d)) = sol.α t := by
  simp [selectorTupleTraj, selOfContract, contractAlpha]

@[simp] lemma selectorTupleTraj_bz :
    selectorTupleTraj sol La warmGainVal t (selOfContract V (contractGateZ d)) =
      bGateZ p.L (sol.μ t) t := by
  simp [selectorTupleTraj, selOfContract, contractGateZ]

@[simp] lemma selectorTupleTraj_bu :
    selectorTupleTraj sol La warmGainVal t (selOfContract V (contractGateU d)) =
      bGateU p.L (sol.μ t) t := by
  simp [selectorTupleTraj, selOfContract, contractGateU]

@[simp] lemma selectorTupleTraj_z (i : Fin d) :
    selectorTupleTraj sol La warmGainVal t (selZ V i) = sol.z t i := by
  simp [selectorTupleTraj, selZ, selOfContract, contractZ, contractTailZ]

@[simp] lemma selectorTupleTraj_u (i : Fin d) :
    selectorTupleTraj sol La warmGainVal t (selU V i) = sol.u t i := by
  simp [selectorTupleTraj, selU, selOfContract, contractU, contractTailU]

@[simp] lemma selectorTupleTraj_a :
    selectorTupleTraj sol La warmGainVal t (selOfContract V (contractA d)) = La.a t := by
  simp [selectorTupleTraj, selOfContract, contractA, contractTailA]

@[simp] lemma selectorTupleTraj_lam (v : V) :
    selectorTupleTraj sol La warmGainVal t (selLamCoord v) = sol.lam v t := by
  simp [selectorTupleTraj, selLamCoord, Fin.append_right, Fin.append_left]

@[simp] lemma selectorTupleTraj_G :
    selectorTupleTraj sol La warmGainVal t (selGCoord d V) = sol.G t := by
  simp [selectorTupleTraj, selGCoord, Fin.append_right]
  rfl

@[simp] lemma selectorTupleTraj_warmGain :
    selectorTupleTraj sol La warmGainVal t (selWarmGainCoord d V) = warmGainVal := by
  simp [selectorTupleTraj, selWarmGainCoord, Fin.append_right]
  rfl

/-- Evaluating a `z`-renamed config polynomial along the trajectory recovers its
config-space evaluation at `sol.z t`. -/
lemma eval_selRenameZ_tuple (q : MvPolynomial (Fin d) ℚ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t) (selRenameZ V q) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) q := by
  rw [selRenameZ, MvPolynomial.eval₂_rename]
  exact MvPolynomial.eval₂_congr
    (f := algebraMap ℚ ℝ) (p := q)
    (g₁ := selectorTupleTraj sol La warmGainVal t ∘ selZ V) (g₂ := sol.z t)
    (fun {i} {_c} _hi _hc => selectorTupleTraj_z La warmGainVal t i)

/-- The mixture field evaluates along the trajectory to the dynamic mixture
target `selectorMixTarget = ∑_v λ_v · A_v(u)`. -/
lemma eval_selectorMixField (i : Fin d) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t)
        (selectorMixField branch i) =
      selectorMixTarget branch sol.u sol.lam t i := by
  rw [selectorMixField, eval₂_selectorMixFieldPoly]
  simp only [selectorTupleTraj_lam, selectorTupleTraj_u, selectorMixTarget, selectorF]

/-- Realization: the gate polynomial evaluates along the trajectory to `((1−cos t)/2)^M`. -/
theorem eval_selChiGatePoly (M : ℕ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t) (selChiGatePoly d V M) =
      ((1 + Real.sin t) / 2) ^ M := by
  simp only [selChiGatePoly, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_add, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, MvPolynomial.eval₂_one,
    selectorTupleTraj_s, map_div₀, map_one, map_ofNat]
  ring_nf

/-- Realization: the reset polynomial evaluates to `((1+cos t)/2)^M`. -/
theorem eval_selChiResetPoly (M : ℕ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t) (selChiResetPoly d V M) =
      ((1 + Real.cos t) / 2) ^ M := by
  simp only [selChiResetPoly, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_add, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, MvPolynomial.eval₂_one,
    selectorTupleTraj_c, map_div₀, map_one, map_ofNat]
  ring_nf

/-- Realization: the reset-rate polynomial evaluates to the constant `κ₀`. -/
theorem eval_selKappaPoly (κ₀ : ℚ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t) (selKappaPoly d V κ₀) =
      (κ₀ : ℝ) := by
  simp [selKappaPoly]

/-- Realization: the gain polynomial evaluates to `warmGainVal · α t`. -/
theorem eval_selGainPoly :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t) (selGainPoly d V) =
      warmGainVal * sol.α t := by
  simp [selGainPoly, selectorTupleTraj_warmGain, selectorTupleTraj_alpha]

end Trajectory

/-! ## The extended trajectory ODE (keystone (B)) -/

private lemma sel_hasDerivAt_fin_append {m n : ℕ}
    {f : ℝ → Fin m → ℝ} {g : ℝ → Fin n → ℝ}
    {f' : Fin m → ℝ} {g' : Fin n → ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun τ => Fin.append (f τ) (g τ)) (Fin.append f' g') t := by
  apply hasDerivAt_pi.mpr
  intro i
  refine Fin.addCases (m := m) (n := n) ?_ ?_ i
  · intro k
    simpa [Fin.append_left] using hasDerivAt_pi.mp hf k
  · intro k
    simpa [Fin.append_right] using hasDerivAt_pi.mp hg k

private noncomputable def selRPulseDeriv (L : ℕ) (t : ℝ) : ℝ :=
  (L : ℝ) * ((1 - Real.sin t) / 2) ^ (L - 1) * (-(Real.cos t / 2))

private noncomputable def selQPulseDeriv (L : ℕ) (t : ℝ) : ℝ :=
  (L : ℝ) * ((1 + Real.sin t) / 2) ^ (L - 1) * (Real.cos t / 2)

private lemma sel_hasDerivAt_rPulse (L : ℕ) (t : ℝ) :
    HasDerivAt (fun τ => rPulse L τ) (selRPulseDeriv L t) t := by
  unfold rPulse selRPulseDeriv
  have hbase : HasDerivAt (fun τ : ℝ => (1 - Real.sin τ) / 2) (-(Real.cos t / 2)) t := by
    convert ((hasDerivAt_const (x := t) (c := (1 : ℝ))).sub
      (Real.hasDerivAt_sin t)).div_const 2 using 1 <;> ring
  simpa using hbase.pow L

private lemma sel_hasDerivAt_qPulse (L : ℕ) (t : ℝ) :
    HasDerivAt (fun τ => qPulse L τ) (selQPulseDeriv L t) t := by
  unfold qPulse selQPulseDeriv
  have hbase : HasDerivAt (fun τ : ℝ => (1 + Real.sin τ) / 2) (Real.cos t / 2) t := by
    convert ((hasDerivAt_const (x := t) (c := (1 : ℝ))).add
      (Real.hasDerivAt_sin t)).div_const 2 using 1 <;> ring
  simpa using hbase.pow L

section ODE

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}

private lemma sel_hasDerivAt_bGateZ
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {cμ : ℚ} (hcμ : p.cμ = (cμ : ℝ)) (t : ℝ) (ht : t ∈ sched.domain) :
    HasDerivAt (fun τ => bGateZ p.L (sol.μ τ) τ)
      (-( (cμ : ℝ) * rPulse p.L t + sol.μ t * selRPulseDeriv p.L t) *
        bGateZ p.L (sol.μ t) t) t := by
  unfold bGateZ
  have hμ : HasDerivAt sol.μ (cμ : ℝ) t := by
    simpa [hcμ] using sol.μ_hasDeriv t ht
  have hmul := hμ.mul (sel_hasDerivAt_rPulse p.L t)
  have hneg : HasDerivAt (fun τ : ℝ => -(sol.μ τ * rPulse p.L τ))
      (-((cμ : ℝ) * rPulse p.L t + sol.μ t * selRPulseDeriv p.L t)) t := by
    simpa [neg_add_rev] using hmul.neg
  have h := hneg.exp
  convert h using 1 <;> ring

private lemma sel_hasDerivAt_bGateU
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {cμ : ℚ} (hcμ : p.cμ = (cμ : ℝ)) (t : ℝ) (ht : t ∈ sched.domain) :
    HasDerivAt (fun τ => bGateU p.L (sol.μ τ) τ)
      (-( (cμ : ℝ) * qPulse p.L t + sol.μ t * selQPulseDeriv p.L t) *
        bGateU p.L (sol.μ t) t) t := by
  unfold bGateU
  have hμ : HasDerivAt sol.μ (cμ : ℝ) t := by
    simpa [hcμ] using sol.μ_hasDeriv t ht
  have hmul := hμ.mul (sel_hasDerivAt_qPulse p.L t)
  have hneg : HasDerivAt (fun τ : ℝ => -(sol.μ τ * qPulse p.L τ))
      (-((cμ : ℝ) * qPulse p.L t + sol.μ t * selQPulseDeriv p.L t)) t := by
    simpa [neg_add_rev] using hmul.neg
  have h := hneg.exp
  convert h using 1 <;> ring

/-- **Keystone (B).**  The selector trajectory is a solution of the extended
polynomial field `selectorAssembledField`: at every `t ≥ 0`, the time-derivative of
each coordinate equals the field evaluated along the trajectory.  The phase gates
(`chiResetP`,`chiGateP`,`kappaP`,`gainP`) and coarse readouts (`PpolyP v`) are
polynomials realizing the solution's scalar clock functions; the config Reach
target is the dynamic mixture `selectorMixField`. -/
theorem selectorTupleTraj_ode
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : SelectorHaltLatchSol sol Hval K R)
    (warmGainVal : ℝ)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    {Aq Kq cμq cαq : ℚ} {L : ℕ}
    (hA : p.A = (Aq : ℝ)) (hK : K = (Kq : ℝ))
    (hcμ : p.cμ = (cμq : ℝ)) (hcα : p.cα = (cαq : ℝ)) (hL : p.L = L)
    (hdomain : ∀ t : ℝ, 0 ≤ t → t ∈ sched.domain)
    (h_chiReset : ∀ t : ℝ, 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t) chiResetP = chiResetF t)
    (h_chiGate : ∀ t : ℝ, 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t) chiGateP = chiGateF t)
    (h_kappa : ∀ t : ℝ, 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t) kappaP = kappaF t)
    (h_gain : ∀ t : ℝ, 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t) gainP = gainF t)
    (h_P : ∀ (v : V) (t : ℝ), 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t) (PpolyP v) = Pv v (sol.u t))
    (h_HP : ∀ t : ℝ,
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) HP = Hval (sol.z t)) :
    ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (selectorTupleTraj sol La warmGainVal)
        (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
          (selectorTupleTraj sol La warmGainVal t)
          (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
            Aq Kq cμq cαq L R i)) t := by
  intro t ht
  have htd : t ∈ sched.domain := hdomain t ht
  let core' : Fin 4 → ℝ := fun k =>
    if k = 0 then Real.cos t else
    if k = 1 then -Real.sin t else
    if k = 2 then (cμq : ℝ) else (cαq : ℝ) * sol.α t
  let gate' : Fin 2 → ℝ := fun k =>
    if k = 0 then
      -(((cμq : ℝ) * rPulse L t + sol.μ t * selRPulseDeriv L t) * bGateZ L (sol.μ t) t)
    else
      -(((cμq : ℝ) * qPulse L t + sol.μ t * selQPulseDeriv L t) * bGateU L (sol.μ t) t)
  let z' : Fin d → ℝ := fun i =>
    (Aq : ℝ) * sol.α t * bGateZ L (sol.μ t) t *
      (selectorMixTarget branch sol.u sol.lam t i - sol.z t i)
  let u' : Fin d → ℝ := fun i =>
    (Aq : ℝ) * sol.α t * bGateU L (sol.μ t) t * (sol.z t i - sol.u t i)
  let a' : Fin 1 → ℝ := fun _ =>
    (Kq : ℝ) * gPulse R t * (Hval (sol.z t) - La.a t)
  let lam' : Fin (Fintype.card V) → ℝ := fun k =>
    chiResetF t * kappaF t * (1 / 2 - sol.lam ((Fintype.equivFin V).symm k) t)
      + chiGateF t * (gainF t * Pv ((Fintype.equivFin V).symm k) (sol.u t) *
        (sol.lam ((Fintype.equivFin V).symm k) t *
          (1 - sol.lam ((Fintype.equivFin V).symm k) t)))
  let G' : Fin 1 → ℝ := fun _ => chiGateF t * gainF t
  let warmGain' : Fin 1 → ℝ := fun _ => 0
  have hcore :
      HasDerivAt
        (fun τ => fun k : Fin 4 =>
          if k = 0 then Real.sin τ else
          if k = 1 then Real.cos τ else
          if k = 2 then sol.μ τ else sol.α τ)
        core' t := by
    apply hasDerivAt_pi.mpr
    intro k
    fin_cases k
    · simpa [core'] using Real.hasDerivAt_sin t
    · simpa [core'] using Real.hasDerivAt_cos t
    · simpa [core', hcμ] using sol.μ_hasDeriv t htd
    · have hα : HasDerivAt sol.α ((cαq : ℝ) * sol.α t) t := by
        simpa [hcα] using sol.α_hasDeriv t htd
      simpa [core'] using hα
  have hgate :
      HasDerivAt
        (fun τ => fun k : Fin 2 =>
          if k = 0 then bGateZ L (sol.μ τ) τ else bGateU L (sol.μ τ) τ)
        gate' t := by
    subst L
    apply hasDerivAt_pi.mpr
    intro k
    fin_cases k
    · convert sel_hasDerivAt_bGateZ sol hcμ t htd using 1
      simp [gate']
      ring_nf
    · convert sel_hasDerivAt_bGateU sol hcμ t htd using 1
      simp [gate']
      ring_nf
  have hz : HasDerivAt (fun τ => sol.z τ) z' t := by
    apply hasDerivAt_pi.mpr
    intro i
    have hz_i := sol.z_hasDeriv t htd i
    convert hz_i using 1
    simp [z', hA, hL]
  have hu : HasDerivAt (fun τ => sol.u τ) u' t := by
    apply hasDerivAt_pi.mpr
    intro i
    have hu_i := sol.u_hasDeriv t htd i
    convert hu_i using 1
    simp [u', hA, hL]
  have ha : HasDerivAt (fun τ => fun _ : Fin 1 => La.a τ) a' t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    have ha0 := La.ode_a t
    convert ha0 using 1
    simp [a', hK]
  have hlam :
      HasDerivAt
        (fun τ => fun k : Fin (Fintype.card V) =>
          sol.lam ((Fintype.equivFin V).symm k) τ)
        lam' t := by
    apply hasDerivAt_pi.mpr
    intro k
    have hd := sol.lam_hasDeriv ((Fintype.equivFin V).symm k) t htd
    simpa [lam'] using hd
  have hG : HasDerivAt (fun τ => fun _ : Fin 1 => sol.G τ) G' t := by
    apply hasDerivAt_pi.mpr
    intro k
    fin_cases k
    have hd := sol.G_hasDeriv t htd
    simpa [G'] using hd
  have hWG : HasDerivAt (fun _ => fun _ : Fin 1 => warmGainVal) warmGain' t := by
    apply hasDerivAt_pi.mpr
    intro k
    fin_cases k
    simpa [warmGain'] using hasDerivAt_const t warmGainVal
  have hraw :
      HasDerivAt (selectorTupleTraj sol La warmGainVal)
        (Fin.append
          (Fin.append core' (Fin.append gate' (Fin.append z' (Fin.append u' a'))))
          (Fin.append lam' (Fin.append G' warmGain'))) t := by
    subst L
    simpa [selectorTupleTraj, core', gate', z', u', a', lam', G', warmGain'] using
      sel_hasDerivAt_fin_append
        (sel_hasDerivAt_fin_append hcore
          (sel_hasDerivAt_fin_append hgate
            (sel_hasDerivAt_fin_append hz (sel_hasDerivAt_fin_append hu ha))))
        (sel_hasDerivAt_fin_append hlam (sel_hasDerivAt_fin_append hG hWG))
  refine hraw.congr_deriv ?_
  funext j
  refine Fin.addCases (m := contractDim d) (n := selectorTailDim V) ?_ ?_ j
  · intro jc
    simp only [Fin.append_left]
    refine Fin.addCases (m := 4) (n := contractGateTailDim d) ?_ ?_ jc
    · intro k
      fin_cases k
      · change core' 0 =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t)
            (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
              Aq Kq cμq cαq L R (selOfContract V (contractS d)))
        simp [core', selectorAssembledField_s]
      · change core' 1 =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t)
            (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
              Aq Kq cμq cαq L R (selOfContract V (contractC d)))
        simp [core', selectorAssembledField_c]
      · change core' 2 =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t)
            (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
              Aq Kq cμq cαq L R (selOfContract V (contractMu d)))
        simp [core', selectorAssembledField_mu]
      · change core' 3 =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t)
            (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
              Aq Kq cμq cαq L R (selOfContract V (contractAlpha d)))
        simp [core', selectorAssembledField_alpha]
    · intro tail0
      refine Fin.addCases (m := 2) (n := contractTailDim d) ?_ ?_ tail0
      · intro k
        fin_cases k
        · simp only [Fin.append_left, Fin.append_right]
          change gate' 0 =
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t)
              (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
                Aq Kq cμq cαq L R (selOfContract V (contractGateZ d)))
          subst L
          simp [gate', selectorAssembledField_bz, selRP, selRPderiv, rPulse, selRPulseDeriv]
          left
          ring_nf
        · simp only [Fin.append_left, Fin.append_right]
          change gate' 1 =
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t)
              (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
                Aq Kq cμq cαq L R (selOfContract V (contractGateU d)))
          subst L
          simp [gate', selectorAssembledField_bu, selQP, selQPderiv, qPulse, selQPulseDeriv]
          left
          ring_nf
      · intro tail
        refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
        · intro i
          simp only [Fin.append_left, Fin.append_right]
          change z' i =
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t)
              (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
                Aq Kq cμq cαq L R (selZ V i))
          simp [z', selectorAssembledField_z, eval_selectorMixField, hL]
        · intro tail2
          refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
          · intro i
            simp only [Fin.append_left, Fin.append_right]
            change u' i =
              MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t)
                (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
                  Aq Kq cμq cαq L R (selU V i))
            simp [u', selectorAssembledField_u, hL]
          · intro k
            fin_cases k
            simp only [Fin.append_left, Fin.append_right]
            change a' 0 =
              MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t)
                (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
                  Aq Kq cμq cαq L R (selOfContract V (contractA d)))
            simp [a', selectorAssembledField_a, gPulse, eval_selRenameZ_tuple, h_HP]
            left
            left
            ring_nf
  · intro jt
    simp only [Fin.append_right]
    refine Fin.addCases (m := Fintype.card V) (n := 1 + 1) ?_ ?_ jt
    · intro k
      simp only [Fin.append_left]
      have hfield :
          selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
              Aq Kq cμq cαq L R (Fin.natAdd (contractDim d) (Fin.castAdd 2 k)) =
            selectorResetGateFieldPoly chiResetP chiGateP kappaP gainP
              (PpolyP ((Fintype.equivFin V).symm k)) (selLamCoord ((Fintype.equivFin V).symm k)) := by
        simp only [selectorAssembledField, Fin.append_right, Fin.append_left]
      rw [hfield, eval₂_selectorResetGateFieldPoly]
      simp only [selectorTupleTraj_lam, h_chiReset t ht, h_chiGate t ht, h_kappa t ht,
        h_gain t ht, h_P _ t ht, lam']
    · intro jGwG
      refine Fin.addCases (m := 1) (n := 1) ?_ ?_ jGwG
      · intro k
        fin_cases k
        simp only [Fin.append_right, Fin.append_left]
        change G' 0 =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t)
            (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
              Aq Kq cμq cαq L R (selGCoord d V))
        rw [selectorAssembledField_G, eval₂_selectorGainFieldPoly]
        simp only [h_chiGate t ht, h_gain t ht, G']
      · intro k
        fin_cases k
        simp only [Fin.append_right]
        change warmGain' 0 =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t)
            (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
              Aq Kq cμq cαq L R (selWarmGainCoord d V))
        rw [selectorAssembledField_warmGain]
        simp [warmGain']

end ODE

/-! ## Initial value of the trajectory and the field package -/

section Package

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}

/-- The trajectory at `t = 0`, in terms of the solution's initial data.  Requires
the clock initial conditions `μ 0 = 0`, `α 0 = 1` (so both gates read `1`). -/
theorem selectorTupleTraj_zero
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : SelectorHaltLatchSol sol Hval K R)
    (warmGainVal : ℝ)
    (hμ0 : sol.μ 0 = 0) (hα0 : sol.α 0 = 1) :
    selectorTupleTraj sol La warmGainVal 0 =
      Fin.append
        (Fin.append
          (fun k : Fin 4 =>
            if k = 0 then 0 else if k = 1 then 1 else if k = 2 then 0 else 1)
          (Fin.append
            (fun _ : Fin 2 => 1)
            (Fin.append (sol.z 0) (Fin.append (sol.u 0) (fun _ : Fin 1 => La.a 0)))))
        (Fin.append
          (fun k : Fin (Fintype.card V) => sol.lam ((Fintype.equivFin V).symm k) 0)
          (Fin.append
            (fun _ : Fin 1 => sol.G 0)
            (fun _ : Fin 1 => warmGainVal))) := by
  funext j
  refine Fin.addCases (m := contractDim d) (n := selectorTailDim V) ?_ ?_ j
  · intro jc
    simp only [Fin.append_left]
    refine Fin.addCases (m := 4) (n := contractGateTailDim d) ?_ ?_ jc
    · intro k
      fin_cases k <;>
        simp [selectorTupleTraj, selOfContract, contractS, contractC, contractMu,
          contractAlpha, hμ0, hα0]
    · intro tail0
      refine Fin.addCases (m := 2) (n := contractTailDim d) ?_ ?_ tail0
      · intro k
        fin_cases k <;>
          simp [selectorTupleTraj, selOfContract, contractGateZ, contractGateU,
            bGateZ, bGateU, hμ0]
      · intro tail
        refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
        · intro i
          simp [selectorTupleTraj, selOfContract, contractZ, contractTailZ]
        · intro tail2
          refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
          · intro i
            simp [selectorTupleTraj, selOfContract, contractU, contractTailU]
          · intro a
            fin_cases a
            simp [selectorTupleTraj, selOfContract, contractA, contractTailA]
  · intro jt
    simp only [Fin.append_right]
    refine Fin.addCases (m := Fintype.card V) (n := 1 + 1) ?_ ?_ jt
    · intro k
      simp only [Fin.append_left]
      simp [selectorTupleTraj, Fin.append_right, Fin.append_left]
    · intro jGwG
      refine Fin.addCases (m := 1) (n := 1) ?_ ?_ jGwG
      · intro a
        fin_cases a
        simp [selectorTupleTraj, Fin.append_right, Fin.append_left]
      · intro a
        fin_cases a
        simp [selectorTupleTraj, Fin.append_right]

/-- Rational Euclidean initial vector for the selector layout: config blocks from the
encoder initial `x₀ w`, latch `0`, all selector weights `1/2`, gain `0`. -/
def selectorEuclInitQ (d : ℕ) (V : Type) [Fintype V] (x₀ : ℕ → Fin d → ℚ) (w : ℕ)
    (warmGainInit : ℚ) :
    Fin (selectorDim d V) → ℚ :=
  Fin.append
    (Fin.append
      (fun k : Fin 4 =>
        if k = 0 then 0 else if k = 1 then 1 else if k = 2 then 0 else 1)
      (Fin.append
        (fun _ : Fin 2 => 1)
        (Fin.append (x₀ w) (Fin.append (x₀ w) (fun _ : Fin 1 => 0)))))
    (Fin.append
      (fun _ : Fin (Fintype.card V) => (1 / 2 : ℚ))
      (Fin.append
        (fun _ : Fin 1 => 0)
        (fun _ : Fin 1 => warmGainInit)))

/-- Compactified rational initial vector induced by `selectorEuclInitQ`. -/
def selectorSphereInitQ (d : ℕ) (V : Type) [Fintype V] (x₀ : ℕ → Fin d → ℚ) (w : ℕ)
    (warmGainInit : ℚ) :
    Fin (selectorDim d V + 1) → ℚ :=
  let x := selectorEuclInitQ d V x₀ w warmGainInit
  let den : ℚ := (∑ i : Fin (selectorDim d V), x i ^ 2) + 1
  Fin.cases (((∑ i : Fin (selectorDim d V), x i ^ 2) - 1) / den)
    (fun i => 2 * x i / den)

theorem selectorTupleTraj_zero_eq_selectorEuclInitQ
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : SelectorHaltLatchSol sol Hval K R)
    (warmGainVal : ℝ)
    (hμ0 : sol.μ 0 = 0) (hα0 : sol.α 0 = 1)
    (hz0 : ∀ i : Fin d, sol.z 0 i = ((x₀ w i : ℚ) : ℝ))
    (hu0 : ∀ i : Fin d, sol.u 0 i = ((x₀ w i : ℚ) : ℝ))
    (hlam0 : ∀ v : V, sol.lam v 0 = (1 / 2 : ℝ))
    (hG0 : sol.G 0 = 0) (ha0 : La.a 0 = 0)
    (hwG : warmGainVal = (warmGainInit : ℝ)) :
    selectorTupleTraj sol La warmGainVal 0 =
      fun i => ((selectorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ) := by
  rw [selectorTupleTraj_zero sol La warmGainVal hμ0 hα0]
  funext j
  refine Fin.addCases (m := contractDim d) (n := selectorTailDim V) ?_ ?_ j
  · intro jc
    simp only [Fin.append_left]
    refine Fin.addCases (m := 4) (n := contractGateTailDim d) ?_ ?_ jc
    · intro k
      fin_cases k <;> simp [selectorEuclInitQ]
    · intro tail0
      refine Fin.addCases (m := 2) (n := contractTailDim d) ?_ ?_ tail0
      · intro k
        fin_cases k <;> simp [selectorEuclInitQ]
      · intro tail
        refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
        · intro i
          simp [selectorEuclInitQ, hz0 i]
        · intro tail2
          refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
          · intro i
            simp [selectorEuclInitQ, hu0 i]
          · intro a
            fin_cases a
            simp [selectorEuclInitQ, ha0]
  · intro jt
    simp only [Fin.append_right]
    refine Fin.addCases (m := Fintype.card V) (n := 1 + 1) ?_ ?_ jt
    · intro k
      simp [selectorEuclInitQ, hlam0]
    · intro jGwG
      refine Fin.addCases (m := 1) (n := 1) ?_ ?_ jGwG
      · intro a
        fin_cases a
        simp [Fin.addCases, Fin.append, selectorEuclInitQ, hG0]
      · intro a
        fin_cases a
        simp [Fin.addCases, Fin.append, selectorEuclInitQ, hwG]

/-- Polynomial field package for the heterogeneous selector layer (analog of
`ContractPolynomialFieldPackage`): the Euclidean tuple field, the trajectory ODE,
honest rational initial presentation data, and the ambient latch coordinate. -/
structure SelectorPolynomialFieldPackage
    (d B : ℕ) (V : Type) [Fintype V]
    (p : DynGateParams) (sched : PhaseSchedule) (branch : V → BranchData d B)
    (chiResetF chiGateF kappaF gainF : ℝ → ℝ) (Pv : V → (Fin d → ℝ) → ℝ)
    (Hval : (Fin d → ℝ) → ℝ) (K : ℝ) (R : ℕ) where
  nE : ℕ
  field : Fin nE → MvPolynomial (Fin nE) ℚ
  tuple :
    ∀ (_w : ℕ)
      (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv),
      SelectorHaltLatchSol sol Hval K R → ℝ → Fin nE → ℝ
  tuple_ode :
    ∀ (w : ℕ)
      (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
      (La : SelectorHaltLatchSol sol Hval K R) (t : ℝ), 0 ≤ t →
        HasDerivAt (tuple w sol La)
          (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
            (tuple w sol La t) (field i)) t
  init : ℕ → Fin (nE + 1) → ℚ
  init_presented : ∃ f : ℕ → Fin (nE + 1) → ℤ × ℕ, Computable f ∧
    ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ)
  init_zero :
    ∀ (w : ℕ)
      (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
      (La : SelectorHaltLatchSol sol Hval K R),
        ((init w 0 : ℚ) : ℝ) =
          ((∑ i : Fin nE, tuple w sol La 0 i ^ 2) - 1) /
            ((∑ i : Fin nE, tuple w sol La 0 i ^ 2) + 1)
  init_succ :
    ∀ (w : ℕ)
      (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
      (La : SelectorHaltLatchSol sol Hval K R) (i : Fin nE),
        ((init w i.succ : ℚ) : ℝ) =
          2 * tuple w sol La 0 i /
            ((∑ k : Fin nE, tuple w sol La 0 k ^ 2) + 1)
  latchCoord : Fin nE
  latch_value :
    ∀ (w : ℕ)
      (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
      (La : SelectorHaltLatchSol sol Hval K R) (t : ℝ),
        tuple w sol La t latchCoord = La.a t

section PackageBuild

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}

/-- Package constructor for the selector polynomial field layer.  The machine
instance supplies the phase-gate/readout polynomials and their evaluation
identities, the rational parameter equalities, and a computable presentation of
the rational sphere initial vector. -/
def selectorPolynomialFieldPackage
    (warmGainFn : ℕ → ℝ)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L : ℕ)
    (hA : p.A = (Aq : ℝ)) (hK : K = (Kq : ℝ))
    (hcμ : p.cμ = (cμq : ℝ)) (hcα : p.cα = (cαq : ℝ)) (hL : p.L = L)
    (hdomain : ∀ t : ℝ, 0 ≤ t → t ∈ sched.domain)
    (h_chiReset :
      ∀ (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorHaltLatchSol sol Hval K R) (wgv : ℝ) (t : ℝ), 0 ≤ t →
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La wgv t) chiResetP = chiResetF t)
    (h_chiGate :
      ∀ (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorHaltLatchSol sol Hval K R) (wgv : ℝ) (t : ℝ), 0 ≤ t →
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La wgv t) chiGateP = chiGateF t)
    (h_kappa :
      ∀ (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorHaltLatchSol sol Hval K R) (wgv : ℝ) (t : ℝ), 0 ≤ t →
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La wgv t) kappaP = kappaF t)
    (h_gain :
      ∀ (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorHaltLatchSol sol Hval K R) (w : ℕ) (t : ℝ), 0 ≤ t →
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La (warmGainFn w) t) gainP = gainF t)
    (h_P :
      ∀ (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorHaltLatchSol sol Hval K R) (wgv : ℝ) (v : V) (t : ℝ), 0 ≤ t →
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La wgv t) (PpolyP v) = Pv v (sol.u t))
    (h_HP :
      ∀ (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorHaltLatchSol sol Hval K R) (t : ℝ),
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) HP = Hval (sol.z t))
    (init : ℕ → Fin (selectorDim d V + 1) → ℚ)
    (init_presented : ∃ f : ℕ → Fin (selectorDim d V + 1) → ℤ × ℕ, Computable f ∧
      ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorHaltLatchSol sol Hval K R),
          ((init w 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim d V), selectorTupleTraj sol La (warmGainFn w) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim d V), selectorTupleTraj sol La (warmGainFn w) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorHaltLatchSol sol Hval K R) (i : Fin (selectorDim d V)),
          ((init w i.succ : ℚ) : ℝ) =
            2 * selectorTupleTraj sol La (warmGainFn w) 0 i /
              ((∑ k : Fin (selectorDim d V), selectorTupleTraj sol La (warmGainFn w) 0 k ^ 2) + 1)) :
    SelectorPolynomialFieldPackage d B V p sched branch chiResetF chiGateF kappaF gainF Pv
      Hval K R :=
  { nE := selectorDim d V
    field := selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
      Aq Kq cμq cαq L R
    tuple := fun w sol La => selectorTupleTraj sol La (warmGainFn w)
    tuple_ode := by
      intro w sol La t ht
      exact selectorTupleTraj_ode sol La (warmGainFn w) chiResetP chiGateP kappaP gainP PpolyP HP
        hA hK hcμ hcα hL hdomain
        (fun t ht => h_chiReset sol La _ t ht) (fun t ht => h_chiGate sol La _ t ht)
        (fun t ht => h_kappa sol La _ t ht) (fun t ht => h_gain sol La w t ht)
        (fun v t ht => h_P sol La _ v t ht) (fun t => h_HP sol La t) t ht
    init := init
    init_presented := init_presented
    init_zero := init_zero
    init_succ := init_succ
    latchCoord := selOfContract V (contractA d)
    latch_value := by
      intro w sol La t
      simp [selectorTupleTraj_a] }

end PackageBuild

/-! ## Euclidean simulation interface and the assembled main theorem -/

/-- Euclidean (pre-compactification) simulation for the selector layer: per input,
a selector solution and a latch whose value eventually reports halting.  This is
the interface the per-cycle recurrence / all-time tube / margins layer must
supply; it is consumed by `main_assembled_dyn_selector`. -/
structure SelectorDynAssembledEuclideanSimulation
    {d B : ℕ} {Conf : Type} [Primcodable Conf]
    (M : DiscreteMachine Conf)
    (p : DynGateParams) (sched : PhaseSchedule)
    {V : Type} [Fintype V] (branch : V → BranchData d B)
    (chiResetF chiGateF kappaF gainF : ℝ → ℝ) (Pv : V → (Fin d → ℝ) → ℝ)
    (Hval : (Fin d → ℝ) → ℝ) (K : ℝ) (R : ℕ) where
  K_pos : 0 < K
  per_input :
    ∀ w : ℕ,
      ∃ (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorHaltLatchSol sol Hval K R),
        (M.haltsOn w →
          ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1) ∧
        (¬ M.haltsOn w →
          ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4)

private theorem sel_stereo_sum_sq {nE : ℕ} (x : Fin nE → ℝ) :
    (∑ j : Fin (nE + 1), stereo x j ^ 2) = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [stereo, Fin.cases_zero, Fin.cases_succ]
  set r : ℝ := ∑ i : Fin nE, x i ^ 2 with hr
  have hden : r + 1 ≠ 0 := by
    have hr0 : 0 ≤ r := by
      dsimp [r]
      exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)
    nlinarith
  have htail :
      (∑ i : Fin nE, (2 * x i / (r + 1)) ^ 2) = 4 * r / (r + 1) ^ 2 := by
    simp only [div_pow, mul_pow]
    calc
      (∑ i : Fin nE, (2 ^ 2 * x i ^ 2) / (r + 1) ^ 2)
          = (∑ i : Fin nE, (4 / (r + 1) ^ 2) * x i ^ 2) := by
            apply Finset.sum_congr rfl; intro i _hi; ring
      _ = (4 / (r + 1) ^ 2) * r := by rw [← Finset.mul_sum]
      _ = 4 * r / (r + 1) ^ 2 := by ring
  simp only [stereoDenom, ← hr]
  rw [htail]
  field_simp [hden]
  ring

private theorem sel_stereo_abs_le_one {nE : ℕ} (x : Fin nE → ℝ)
    (j : Fin (nE + 1)) : |stereo x j| ≤ 1 := by
  have hterm : stereo x j ^ 2 ≤ ∑ k : Fin (nE + 1), stereo x k ^ 2 :=
    Finset.single_le_sum (fun k _hk => sq_nonneg (stereo x k)) (Finset.mem_univ j)
  have hsq : stereo x j ^ 2 ≤ 1 := by
    simpa [sel_stereo_sum_sq x] using hterm
  exact (sq_le_one_iff_abs_le_one (stereo x j)).mp hsq

/-- **Assembled selector main theorem.**  From a Euclidean selector simulation and
the selector polynomial field package, build the compactified sphere PIVP and the
chart-readout transfer — yielding a single PIVP that eventually-threshold simulates
`M`.  Mirrors `main_assembled_dyn_contract`; the per-cycle/tube/margins work is
isolated entirely in the `SelectorDynAssembledEuclideanSimulation` argument. -/
theorem main_assembled_dyn_selector
    {d B : ℕ} {Conf : Type} [Primcodable Conf]
    (M : UndecidableMachine Conf)
    (p : DynGateParams) (sched : PhaseSchedule)
    {V : Type} [Fintype V] (branch : V → BranchData d B)
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (euclidean :
      SelectorDynAssembledEuclideanSimulation M.toDiscreteMachine p sched branch
        chiResetF chiGateF kappaF gainF Pv Hval K R)
    (fieldPkg :
      SelectorPolynomialFieldPackage d B V p sched branch
        chiResetF chiGateF kappaF gainF Pv Hval K R) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P M) := by
  classical
  choose sol La hhalt hnonhalt using euclidean.per_input
  obtain ⟨Y, _htang, htransfer⟩ :=
    compactification_exists fieldPkg.nE fieldPkg.field
  let P : Ripple.BoundedUniversality.GPAC.PIVP ℚ :=
    { n := fieldPkg.nE + 1
      vf := Y
      init := fieldPkg.init }
  have htrans : ∀ w,
      ∃ s : ℝ → ℝ, s 0 = 0 ∧ StrictMonoOn s (Set.Ici 0) ∧
        Filter.Tendsto s Filter.atTop Filter.atTop ∧
        ∀ τ : ℝ, 0 ≤ τ → HasDerivAt
          (fun σ => stereo (fieldPkg.tuple w (sol w) (La w) (s σ)))
          (fun j => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
            (stereo (fieldPkg.tuple w (sol w) (La w) (s τ))) (Y j)) τ := by
    intro w
    exact htransfer (fieldPkg.tuple w (sol w) (La w))
      (fieldPkg.tuple_ode w (sol w) (La w))
  choose s hs0 _hsmono hstend hsphere using htrans
  refine ⟨P, ⟨{
    traj := fun w τ => stereo (fieldPkg.tuple w (sol w) (La w) (s w τ))
    init_at_zero := ?_
    solves_ode := ?_
    bounded := ?_
    encoder_presented := fieldPkg.init_presented
    readout := ?_
    correct_halt := ?_
    correct_nonhalt := ?_
  }⟩⟩
  · intro w
    funext j
    rw [hs0 w]
    dsimp [P, Ripple.BoundedUniversality.GPAC.PIVP.realInit]
    refine Fin.cases ?_ ?_ j
    · simp [stereo, stereoDenom, fieldPkg.init_zero w (sol w) (La w)]
    · intro i
      simp [stereo, stereoDenom, fieldPkg.init_succ w (sol w) (La w) i]
  · intro w τ hτ
    simpa [P, Ripple.BoundedUniversality.GPAC.PIVP.evalVF] using hsphere w τ hτ
  · refine ⟨1, by norm_num, ?_⟩
    intro w τ i hτ
    exact sel_stereo_abs_le_one _ _
  · exact { hA := fieldPkg.latchCoord.succ, h0 := 0, ne := by simp }
  · intro w hw
    obtain ⟨T, hT⟩ := hhalt w hw
    have hev : ∀ᶠ τ in Filter.atTop, max T 0 ≤ s w τ :=
      (hstend w).eventually (Filter.eventually_ge_atTop (max T 0))
    obtain ⟨Θ, hΘ⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max Θ 0, ?_⟩
    intro τ hτ
    have hΘτ : Θ ≤ τ := le_trans (le_max_left Θ 0) hτ
    have hsge : max T 0 ≤ s w τ := hΘ τ hΘτ
    have hTle : T ≤ s w τ := le_trans (le_max_left T 0) hsge
    have hLatch := hT (s w τ) hTle
    have hreg :=
      (stereo_readout_transfer
        (fieldPkg.tuple w (sol w) (La w) (s w τ)) fieldPkg.latchCoord).1
        (by simpa [fieldPkg.latch_value w (sol w) (La w) (s w τ)] using hLatch)
    simpa [ChartThresholdReadout.HaltRegion, P] using hreg
  · intro w hw
    obtain ⟨T, hT⟩ := hnonhalt w hw
    have hev : ∀ᶠ τ in Filter.atTop, max T 0 ≤ s w τ :=
      (hstend w).eventually (Filter.eventually_ge_atTop (max T 0))
    obtain ⟨Θ, hΘ⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max Θ 0, ?_⟩
    intro τ hτ
    have hΘτ : Θ ≤ τ := le_trans (le_max_left Θ 0) hτ
    have hsge : max T 0 ≤ s w τ := hΘ τ hΘτ
    have hTle : T ≤ s w τ := le_trans (le_max_left T 0) hsge
    have hLatch := hT (s w τ) hTle
    have hreg :=
      (stereo_readout_transfer
        (fieldPkg.tuple w (sol w) (La w) (s w τ)) fieldPkg.latchCoord).2
        (by simpa [fieldPkg.latch_value w (sol w) (La w) (s w τ)] using hLatch)
    simpa [ChartThresholdReadout.NonhaltRegion, P] using hreg

/-! ## Latch convergence kernel + flag readout + euclidean assembly -/

section Readout

/-- Analytic latch convergence for the selector solution (analog of
`ContractLatchConvergenceKernel`): eventual indicator-high in read windows drives the
latch high; all-window indicator-low drives it low. -/
structure SelectorLatchConvergenceKernel
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    (flagCoord : Fin d) (I : ContractFlagIndicatorPackage flagCoord)
    {K : ℝ} {R : ℕ} (La : SelectorHaltLatchSol sol I.Hval K R) where
  K_pos : 0 < K
  high_from_eventual_indicator :
    (∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ sched.zActiveWindow j,
      1 - I.eta ≤ I.Hval (sol.z t)) →
      ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1
  low_from_all_indicator :
    (∀ j : ℕ, ∀ t ∈ sched.zActiveWindow j,
      I.Hval (sol.z t) ≤ I.eta) →
      ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4

private lemma sel_discrete_halted_of_step_orbit
    {Conf : Type} [Primcodable Conf] (M : DiscreteMachine Conf)
    {c : ℕ → Conf}
    (hc_step : ∀ j, c (j + 1) = M.step (c j))
    {n : ℕ} (hn : M.halted (c n) = true) :
    ∀ m : ℕ, n ≤ m → M.halted (c m) = true := by
  intro m hnm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction k with
  | zero => simpa using hn
  | succ k ih =>
      rw [Nat.add_succ, hc_step]
      have ih' : M.halted (c (n + k)) = true := ih (Nat.le_add_right n k)
      have hfix : M.step (c (n + k)) = c (n + k) := M.halted_absorbing _ ih'
      simpa [hfix] using ih'

private lemma sel_haltsOn_iff_orbit_halted
    {Conf : Type} [Primcodable Conf] (M : DiscreteMachine Conf) (w : ℕ) :
    M.haltsOn w ↔ ∃ N : ℕ, M.halted (M.step^[N] (M.init w)) = true := by
  rfl

/-- **Selector halt-flag readout.**  From the per-cycle flag-coordinate tube
(`|z flag − enc flag| ≤ 1/4` in read windows) and the latch convergence kernel,
the latch reads the halting status: halting ⇒ latch eventually high, non-halting ⇒
latch eventually low.  Abstract analog of `contract_halt_flag_readout`. -/
theorem selector_halt_flag_readout
    {d B nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    {E : StackMachineEncoding d nS M}
    {V : Type} [Fintype V] {p : DynGateParams} {sched : PhaseSchedule}
    {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    (c : ℕ → Conf) (hc_step : ∀ j, c (j + 1) = M.step (c j))
    (flagCoord : Fin d)
    (flagPkg : HaltFlagPackage E flagCoord)
    (I : ContractFlagIndicatorPackage flagCoord)
    {K : ℝ} {R : ℕ} (La : SelectorHaltLatchSol sol I.Hval K R)
    (kernel : SelectorLatchConvergenceKernel sol flagCoord I La)
    (hflag_read : ∀ j t, t ∈ sched.zActiveWindow j →
      |sol.z t flagCoord - E.enc (c j) flagCoord| ≤ 1 / 4)
    (hflag_domain : ∀ j t, t ∈ sched.zActiveWindow j →
      sol.z t flagCoord ∈ Set.Icc (0 : ℝ) 1) :
    ContractFlagReadout (fun j => M.halted (c j) = true) La.a := by
  classical
  refine { correct_halt := ?_, correct_nonhalt := ?_ }
  · rintro ⟨N, hN⟩
    apply kernel.high_from_eventual_indicator
    refine ⟨N, ?_⟩
    intro j hj t ht
    have hhalt_j : M.halted (c j) = true :=
      sel_discrete_halted_of_step_orbit M hc_step hN j hj
    have hflag_eq : E.enc (c j) flagCoord = 1 := flagPkg.halted_flag (c j) hhalt_j
    have hclose : |sol.z t flagCoord - 1| ≤ 1 / 4 := by
      have h := hflag_read j t ht; rwa [hflag_eq] at h
    exact I.on_flag_one (sol.z t) (hflag_domain j t ht) hclose
  · intro hnonhalt
    apply kernel.low_from_all_indicator
    intro j t ht
    have hhalt_false : M.halted (c j) = false := by
      cases h : M.halted (c j) with
      | false => rfl
      | true => exact False.elim (hnonhalt j h)
    have hflag_eq : E.enc (c j) flagCoord = 0 := flagPkg.running_flag (c j) hhalt_false
    have hclose : |sol.z t flagCoord - 0| ≤ 1 / 4 := by
      have h := hflag_read j t ht; rwa [hflag_eq] at h
    exact I.on_flag_zero (sol.z t) (hflag_domain j t ht) hclose

/-- **Selector Euclidean simulation assembly.**  From a per-input supply of a
selector solution + latch + convergence kernel + the per-cycle flag-coordinate tube,
build the `SelectorDynAssembledEuclideanSimulation`.  The supply hypothesis bundles
exactly the output of the per-cycle recurrence / all-time tube layer; this theorem
is the assembly that turns it into the readout interface `main_assembled_dyn_selector`
consumes. -/
theorem selector_dyn_assembled_euclidean_simulation
    {d B nS : ℕ} {Conf : Type} [Primcodable Conf] (M : DiscreteMachine Conf)
    (E : StackMachineEncoding d nS M)
    {V : Type} [Fintype V] (branch : V → BranchData d B)
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}
    (p : DynGateParams) (sched : PhaseSchedule)
    (flagCoord : Fin d)
    (flagPkg : HaltFlagPackage E flagCoord)
    (I : ContractFlagIndicatorPackage flagCoord)
    {K : ℝ} {R : ℕ} (hK : 0 < K)
    (hsupply : ∀ w : ℕ,
      ∃ (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorHaltLatchSol sol I.Hval K R),
        SelectorLatchConvergenceKernel sol flagCoord I La ∧
        (∀ j t, t ∈ sched.zActiveWindow j →
          |sol.z t flagCoord - E.enc (M.step^[j] (M.init w)) flagCoord| ≤ 1 / 4) ∧
        (∀ j t, t ∈ sched.zActiveWindow j →
          sol.z t flagCoord ∈ Set.Icc (0 : ℝ) 1)) :
    SelectorDynAssembledEuclideanSimulation M p sched branch
      chiResetF chiGateF kappaF gainF Pv I.Hval K R := by
  classical
  refine { K_pos := hK, per_input := ?_ }
  intro w
  obtain ⟨sol, La, kernel, hread, hdom⟩ := hsupply w
  let c : ℕ → Conf := fun j => M.step^[j] (M.init w)
  have hc_step : ∀ j, c (j + 1) = M.step (c j) := by
    intro j; show M.step^[j + 1] (M.init w) = M.step (M.step^[j] (M.init w))
    rw [Function.iterate_succ_apply']
  have readout :
      ContractFlagReadout (fun j => M.halted (c j) = true) La.a :=
    selector_halt_flag_readout sol c hc_step flagCoord flagPkg I La kernel hread hdom
  refine ⟨sol, La, ?_, ?_⟩
  · intro hw
    exact readout.correct_halt ((sel_haltsOn_iff_orbit_halted M w).mp hw)
  · intro hw
    apply readout.correct_nonhalt
    intro N hN
    exact hw ((sel_haltsOn_iff_orbit_halted M w).mpr ⟨N, hN⟩)

end Readout

/-! ## Per-cycle recurrence and the all-time boundary tube -/

/-- **The growing gate gain removes the fixed-precision floor.**  The per-cycle gate
mixture error has the form `epsmix j = C₀·exp(−α·ΔG j)` (`gate_mix_error_approx`), where
`ΔG j = G(tHold j) − G(a j)` is the integrated gate gain accumulated in cycle `j`.  When
the gain grows at least linearly (`c·j ≤ ΔG j`, which holds for the exponential clock gain
`gainF = g₀·exp(cα·t)` integrated over the gate sub-windows), the defect decays
GEOMETRICALLY: `epsmix j ≤ C₀·exp(−(α·c)·j)`.  This is the exact `hdecay` shape (with
`eta = α·c`) that `selector_boundary_tube_decay` consumes — and the reason the clock-driven
selector closes the tube with NO fixed floor (contrast the fixed-precision selector, whose
constant per-step error `δ` cannot be made summable).  `α = αmar = 1/2 − errSel`. -/
theorem selector_epsmix_decay_of_gain_linear
    {C₀ α c : ℝ} (hC₀ : 0 ≤ C₀) (hα : 0 ≤ α) (ΔG : ℕ → ℝ)
    (hΔG : ∀ j : ℕ, (c : ℝ) * (j : ℝ) ≤ ΔG j) :
    ∀ j : ℕ, C₀ * Real.exp (-α * ΔG j) ≤ C₀ * Real.exp (-(α * c) * (j : ℝ)) := by
  intro j
  refine mul_le_mul_of_nonneg_left ?_ hC₀
  refine Real.exp_le_exp.mpr ?_
  nlinarith [mul_le_mul_of_nonneg_left (hΔG j) hα]

/-- **εmix summability (why the clock selector closes the tube).**  When the integrated
gain grows at least linearly across cycles (`c·j ≤ ΔG j`, `c > 0`), the per-cycle gate
mixture error `K·exp(−αmar·ΔG j)` is summable — the exponential gate precision turns the
per-cycle defect into a convergent series, which is exactly what the all-time budget needs
(unlike the fixed selector's constant floor, which is non-summable).  `αmar = 1/2 − errSel`. -/
theorem eps_mix_summable_of_gain_linear {K αmar c : ℝ} (hK : 0 ≤ K) (hαmar : 0 ≤ αmar)
    (hαc : 0 < αmar * c) (ΔG : ℕ → ℝ) (hΔG : ∀ j : ℕ, (c : ℝ) * (j : ℝ) ≤ ΔG j) :
    Summable (fun j : ℕ => K * Real.exp (-αmar * ΔG j)) := by
  have hgeom : Summable (fun j : ℕ => K * Real.exp (-(αmar * c)) ^ j) := by
    refine Summable.mul_left K ?_
    refine summable_geometric_of_lt_one (le_of_lt (Real.exp_pos _)) ?_
    exact Real.exp_lt_one_iff.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hgeom
  have hexp : Real.exp (-(αmar * c)) ^ j = Real.exp (-(αmar * c) * (j : ℝ)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [hexp]
  have hle : -αmar * ΔG j ≤ -(αmar * c) * (j : ℝ) := by
    have := mul_le_mul_of_nonneg_left (hΔG j) hαmar
    nlinarith [this]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) hK

section Tube

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}

/-- **Gain accumulation (FTC lower bound).**  Since `G' = χ_gate·gain` (`G_hasDeriv`), any
continuous pointwise lower bound `lb t ≤ χ_gate t · gain t` on `[a,b]` integrates to a lower
bound on the accumulated gain: `∫_a^b lb ≤ G(b) − G(a)`.  Instantiated with
`lb = ℓ·g₀·exp(cα·t)` over the gate sub-window (where `χ_gate ≥ ℓ` and `gain = g₀·exp(cα·t)`),
this gives `ΔG_j ≥ ℓ·g₀·(exp(cα·b)−exp(cα·a))/cα`, which grows exponentially in the cycle
index — the engine behind `ΔG_j ≥ c·j` (hence `eps_mix_summable_of_gain_linear` /
`selector_epsmix_decay_of_gain_linear`). -/
theorem selector_gain_accumulation
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {a b : ℝ} (hab : a ≤ b) (lb : ℝ → ℝ)
    (hdom : ∀ t ∈ Set.Icc a b, t ∈ sched.domain)
    (hcont : Continuous (fun t => chiGateF t * gainF t))
    (hlbcont : Continuous lb)
    (hlb : ∀ t ∈ Set.Icc a b, lb t ≤ chiGateF t * gainF t) :
    (∫ t in a..b, lb t) ≤ sol.G b - sol.G a := by
  have huicc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hG : (∫ t in a..b, chiGateF t * gainF t) = sol.G b - sol.G a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_)
      (hcont.intervalIntegrable a b)
    rw [huicc] at ht
    exact sol.G_hasDeriv t (hdom t ht)
  rw [← hG]
  exact intervalIntegral.integral_mono_on hab (hlbcont.intervalIntegrable a b)
    (hcont.intervalIntegrable a b) hlb

/-- **Gain accumulation, exponential growth.**  For the M_U gate gain `gain = g₀·exp(cα·t)`
and a gate window `[a,b]` on which `χ_gate ≥ ℓ ≥ 0`, the accumulated gain is bounded below by
`ΔG ≥ ℓ·g₀·exp(cα·a)·(b−a)` (using the window-minimum `exp(cα·a)` of the gain).  Over the gate
sub-window of cycle `j` (`a ≈ 2πj+2π/3`) the factor `exp(cα·a) ~ exp(2πcα·j)` grows
exponentially, so `ΔG_j ≥ c·j` for a positive `c` — the linear-growth premise of the
tube-closing decay (`selector_epsmix_decay_of_gain_linear`). -/
theorem selector_gain_lower_exp
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {a b g₀ cα ℓ : ℝ} (hab : a ≤ b) (hcα : 0 < cα) (hℓ : 0 ≤ ℓ) (hg₀ : 0 ≤ g₀)
    (hdom : ∀ t ∈ Set.Icc a b, t ∈ sched.domain)
    (hgain : ∀ t, gainF t = g₀ * Real.exp (cα * t))
    (hcont : Continuous (fun t => chiGateF t * gainF t))
    (hchi : ∀ t ∈ Set.Icc a b, ℓ ≤ chiGateF t) :
    ℓ * g₀ * Real.exp (cα * a) * (b - a) ≤ sol.G b - sol.G a := by
  have hlb : ∀ t ∈ Set.Icc a b, ℓ * g₀ * Real.exp (cα * a) ≤ chiGateF t * gainF t := by
    intro t ht
    have h1 : ℓ ≤ chiGateF t := hchi t ht
    have h2 : Real.exp (cα * a) ≤ Real.exp (cα * t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.1 hcα.le)
    calc ℓ * g₀ * Real.exp (cα * a)
        = ℓ * (g₀ * Real.exp (cα * a)) := by ring
      _ ≤ chiGateF t * (g₀ * Real.exp (cα * t)) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 hg₀)
            (mul_nonneg hg₀ (Real.exp_pos _).le) (le_trans hℓ h1)
      _ = chiGateF t * gainF t := by rw [hgain t]
  have hconst : (∫ _t in a..b, ℓ * g₀ * Real.exp (cα * a))
      = ℓ * g₀ * Real.exp (cα * a) * (b - a) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have := selector_gain_accumulation sol hab (fun _ => ℓ * g₀ * Real.exp (cα * a))
    hdom hcont continuous_const hlb
  rwa [hconst] at this

/-- **Per-cycle gain grows at least linearly.**  Combining `selector_gain_lower_exp` (the
exponential window-minimum bound `ΔG_j ≥ ℓ·g₀·exp(cα·a_j)·(b_j−a_j)`) with `exp(x) ≥ x` and the
cycle timing `a_j ≥ 2π·j + a₀`, the accumulated gate gain in cycle `j` grows at least linearly:
`c·j ≤ ΔG_j` with `c = ℓ·g₀·exp(cα·a₀)·w·(2π·cα) > 0`.  This is EXACTLY the `hΔG` premise of
`selector_epsmix_decay_of_gain_linear`, completing the gain → geometric-decay pipeline that
removes the fixed-precision floor. -/
theorem selector_gain_linear_growth
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {g₀ cα ℓ a₀ w : ℝ} (aw bw : ℕ → ℝ)
    (hcα : 0 < cα) (hℓ : 0 < ℓ) (hg₀ : 0 < g₀) (hw : 0 < w) (ha₀ : 0 ≤ a₀)
    (ha : ∀ j : ℕ, 2 * Real.pi * (j : ℝ) + a₀ ≤ aw j)
    (hbw : ∀ j, w ≤ bw j - aw j)
    (hab : ∀ j, aw j ≤ bw j)
    (hdom : ∀ j, ∀ t ∈ Set.Icc (aw j) (bw j), t ∈ sched.domain)
    (hgain : ∀ t, gainF t = g₀ * Real.exp (cα * t))
    (hcont : Continuous (fun t => chiGateF t * gainF t))
    (hchi : ∀ j, ∀ t ∈ Set.Icc (aw j) (bw j), ℓ ≤ chiGateF t) :
    ∀ j : ℕ, (ℓ * g₀ * Real.exp (cα * a₀) * w * (2 * Real.pi * cα)) * (j : ℝ)
        ≤ sol.G (bw j) - sol.G (aw j) := by
  intro j
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hglb := selector_gain_lower_exp sol (hab j) hcα hℓ.le hg₀.le
    (fun t ht => hdom j t ht) hgain hcont (fun t ht => hchi j t ht)
  refine le_trans ?_ hglb
  have he1 : Real.exp (cα * a₀) * (2 * Real.pi * cα * (j : ℝ)) ≤ Real.exp (cα * aw j) := by
    calc Real.exp (cα * a₀) * (2 * Real.pi * cα * (j : ℝ))
        ≤ Real.exp (cα * a₀) * Real.exp (2 * Real.pi * cα * (j : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          have := Real.add_one_le_exp (2 * Real.pi * cα * (j : ℝ))
          linarith
      _ = Real.exp (cα * a₀ + 2 * Real.pi * cα * (j : ℝ)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (cα * aw j) := by
          refine Real.exp_le_exp.mpr ?_
          have heq : cα * a₀ + 2 * Real.pi * cα * (j : ℝ)
              = cα * (2 * Real.pi * (j : ℝ) + a₀) := by ring
          rw [heq]
          exact mul_le_mul_of_nonneg_left (ha j) hcα.le
  calc (ℓ * g₀ * Real.exp (cα * a₀) * w * (2 * Real.pi * cα)) * (j : ℝ)
      = (ℓ * g₀) * (Real.exp (cα * a₀) * (2 * Real.pi * cα * (j : ℝ))) * w := by ring
    _ ≤ (ℓ * g₀) * Real.exp (cα * aw j) * w := by
        refine mul_le_mul_of_nonneg_right ?_ hw.le
        exact mul_le_mul_of_nonneg_left he1 (by positivity)
    _ ≤ (ℓ * g₀) * Real.exp (cα * aw j) * (bw j - aw j) := by
        refine mul_le_mul_of_nonneg_left (hbw j) ?_
        positivity
    _ = ℓ * g₀ * Real.exp (cα * aw j) * (bw j - aw j) := by ring

/-- **Selector per-cycle recurrence.**  Lifting `SelectorDynSol.cycle_step` to every
cycle `j`: with the cycle timepoints `tStart j`, `tHold j`, and the next start
`tStart (j+1)` as the cycle end, the held config's boundary error contracts by
`mult j` plus the per-cycle defect `ε_mix + ε_write + mult·ε_hold`.  This is the
recurrence consumed by `DepthBudget.all_time_tube`. -/
theorem selector_per_cycle_recurrence
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    (i : Fin d) (vstar : ℕ → V)
    (tStart tHold : ℕ → ℝ) (enc : ℕ → Fin d → ℝ)
    (mult : ℕ → ℝ) (epsmix epswrite epshold : ℕ → ℝ)
    (hmult : ∀ j, 0 ≤ mult j)
    (hmix : ∀ j,
      |selectorMixTarget branch sol.u sol.lam (tHold j) i
          - BranchData.evalBranch (branch (vstar j)) (sol.u (tHold j)) i| ≤ epsmix j)
    (hdiag : ∀ j,
      |BranchData.evalBranch (branch (vstar j)) (sol.u (tHold j)) i - enc (j + 1) i|
        ≤ mult j * |sol.u (tHold j) i - enc j i|)
    (hhold : ∀ j,
      |sol.u (tHold j) i - enc j i| ≤ |sol.u (tStart j) i - enc j i| + epshold j)
    (hwrite : ∀ j,
      |sol.u (tStart (j + 1)) i - selectorMixTarget branch sol.u sol.lam (tHold j) i|
        ≤ epswrite j) :
    ∀ j,
      |sol.u (tStart (j + 1)) i - enc (j + 1) i| ≤
        mult j * |sol.u (tStart j) i - enc j i|
          + (epsmix j + epswrite j + mult j * epshold j) :=
  fun j =>
    sol.cycle_step (vstar j) i (tStart j) (tHold j) (tStart (j + 1)) (enc j) (enc (j + 1))
      (hmult j) (hmix j) (hdiag j) (hhold j) (hwrite j)

/-- **Selector all-time boundary tube.**  Feeding the per-cycle recurrence (with
contraction `mult j = k^{delta j}` from a depth budget) to `DepthBudget.all_time_tube`,
the held config's boundary error stays in the radius `r` for all cycles. -/
theorem selector_boundary_tube
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    (i : Fin d) (vstar : ℕ → V)
    (tStart tHold : ℕ → ℝ) (enc : ℕ → Fin d → ℝ)
    (dep delta : ℕ → ℤ) (epsmix epswrite epshold : ℕ → ℝ) {k r : ℝ} (hk : 1 < k)
    (hmix : ∀ j,
      |selectorMixTarget branch sol.u sol.lam (tHold j) i
          - BranchData.evalBranch (branch (vstar j)) (sol.u (tHold j)) i| ≤ epsmix j)
    (hdiag : ∀ j,
      |BranchData.evalBranch (branch (vstar j)) (sol.u (tHold j)) i - enc (j + 1) i|
        ≤ k ^ delta j * |sol.u (tHold j) i - enc j i|)
    (hhold : ∀ j,
      |sol.u (tHold j) i - enc j i| ≤ |sol.u (tStart j) i - enc j i| + epshold j)
    (hwrite : ∀ j,
      |sol.u (tStart (j + 1)) i - selectorMixTarget branch sol.u sol.lam (tHold j) i|
        ≤ epswrite j)
    (hdepth : ∀ j, dep (j + 1) = dep j - delta j)
    (hdnn : ∀ j, 0 ≤ dep j)
    (hbound : ∀ j,
      DepthBudget.W k dep (fun j => |sol.u (tStart j) i - enc j i|) 0
        + DepthBudget.partialBudget k dep
          (fun j => epsmix j + epswrite j + k ^ delta j * epshold j) j ≤ r) :
    ∀ j, |sol.u (tStart j) i - enc j i| ≤ r := by
  have hkpow : ∀ j, (0 : ℝ) ≤ k ^ delta j := fun j => le_of_lt (zpow_pos (by linarith) _)
  have hrec := selector_per_cycle_recurrence sol i vstar tStart tHold enc
    (fun j => k ^ delta j) epsmix epswrite epshold hkpow hmix hdiag hhold hwrite
  exact DepthBudget.all_time_tube
    (fun j => |sol.u (tStart j) i - enc j i|) dep delta
    (fun j => epsmix j + epswrite j + k ^ delta j * epshold j) hk hrec hdepth
    (fun j => abs_nonneg _) hdnn hbound

/-- **Per-cycle step with explicit gate-phase precision.**  One cycle of the iterator:
the gate window `[a, tHold]` (`χ_reset=0`, `χ_gate=1`) drives the mixture error to
`card·R·C_reset(δ)·e^{−αmar·ΔG}` (`gate_mix_error`), and `cycle_step` composes this with the
branch contraction, the hold drift, and the write Reach to give the boundary-error recurrence
with the gate-phase `εmix` made explicit.  This is `cycle_step ∘ gate_mix_error` — the per-cycle
bound whose `εmix→0` (via the gain `ΔG`) closes the all-time tube. -/
theorem selector_cycle_step_gate
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    [DecidableEq V] (vstar : V) (i : Fin d) (tStart a tHold tEnd : ℝ)
    (encC encStepC : Fin d → ℝ) {αmar δ R εwrite εhold mult : ℝ}
    (hmult : 0 ≤ mult)
    (hab : a ≤ tHold) (hαmar : 0 < αmar) (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2) (hR : 0 ≤ R)
    (hdom : ∀ t ∈ Set.Icc a tHold, t ∈ sched.domain)
    (hreset0 : ∀ t ∈ Set.Icc a tHold, chiResetF t = 0)
    (hgate1 : ∀ t ∈ Set.Icc a tHold, chiGateF t = 1)
    (hgain_nonneg : ∀ t ∈ Set.Ico a tHold, 0 ≤ gainF t)
    (hunit : ∀ v, ∀ t ∈ Set.Icc a tHold, 0 < sol.lam v t ∧ sol.lam v t < 1)
    (hlama : ∀ v, |sol.lam v a - 1 / 2| ≤ δ)
    (hPtrue : ∀ t ∈ Set.Ico a tHold, αmar ≤ sol.Pval vstar t)
    (hPfalse : ∀ v, v ≠ vstar → ∀ t ∈ Set.Ico a tHold, sol.Pval v t ≤ -αmar)
    (hA : ∀ v, |BranchData.evalBranch (branch v) (sol.u tHold) i| ≤ R)
    (hdiag : |BranchData.evalBranch (branch vstar) (sol.u tHold) i - encStepC i|
              ≤ mult * |sol.u tHold i - encC i|)
    (hhold : |sol.u tHold i - encC i| ≤ |sol.u tStart i - encC i| + εhold)
    (hwrite : |sol.u tEnd i - selectorMixTarget branch sol.u sol.lam tHold i| ≤ εwrite) :
    |sol.u tEnd i - encStepC i| ≤
      mult * |sol.u tStart i - encC i| +
        ((Fintype.card V : ℝ) * R * (Creset δ * Real.exp (-αmar * (sol.G tHold - sol.G a)))
          + εwrite + mult * εhold) :=
  sol.cycle_step vstar i tStart tHold tEnd encC encStepC hmult
    (sol.gate_mix_error vstar i hab hαmar hδ hδhalf hR hdom hreset0 hgate1 hgain_nonneg
      hunit hlama hPtrue hPfalse hA)
    hdiag hhold hwrite

/-- **Selector all-time boundary tube (decay form).**  The clean tube-closing: from the
per-cycle recurrence (contraction `k^{delta j}`) and the per-cycle defect decaying
geometrically (`η_j ≤ C·exp(−eta·j)`, which holds because the gate gain grows so
`εmix→0` — see `eps_mix_summable_of_gain_linear`), with the depth growing at most linearly
and `beta·log k < eta`, the held config's boundary error stays in the explicit all-time tube
`W k dep e 0 + geometricBudgetConstant`.  Direct `DepthBudget.depth_aware_all_time_tube`. -/
theorem selector_boundary_tube_decay
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    (i : Fin d) (vstar : ℕ → V)
    (tStart tHold : ℕ → ℝ) (enc : ℕ → Fin d → ℝ)
    (dep delta : ℕ → ℤ) (epsmix epswrite epshold : ℕ → ℝ)
    {k d0 beta eta C : ℝ} (hk : 1 < k)
    (hmix : ∀ j,
      |selectorMixTarget branch sol.u sol.lam (tHold j) i
          - BranchData.evalBranch (branch (vstar j)) (sol.u (tHold j)) i| ≤ epsmix j)
    (hdiag : ∀ j,
      |BranchData.evalBranch (branch (vstar j)) (sol.u (tHold j)) i - enc (j + 1) i|
        ≤ k ^ delta j * |sol.u (tHold j) i - enc j i|)
    (hhold : ∀ j,
      |sol.u (tHold j) i - enc j i| ≤ |sol.u (tStart j) i - enc j i| + epshold j)
    (hwrite : ∀ j,
      |sol.u (tStart (j + 1)) i - selectorMixTarget branch sol.u sol.lam (tHold j) i|
        ≤ epswrite j)
    (hdepth : ∀ j, dep (j + 1) = dep j - delta j)
    (hdnn : ∀ j, 0 ≤ dep j)
    (hgrow : ∀ j, (dep j : ℝ) ≤ d0 + beta * (j : ℝ))
    (hdecay : ∀ j, epsmix j + epswrite j + k ^ delta j * epshold j ≤ C * Real.exp (-eta * (j : ℝ)))
    (heta : beta * Real.log k < eta) (hC : 0 ≤ C) (hbeta : 0 ≤ beta) :
    ∀ j, |sol.u (tStart j) i - enc j i| ≤
      DepthBudget.W k dep (fun j => |sol.u (tStart j) i - enc j i|) 0
        + DepthBudget.geometricBudgetConstant k d0 beta eta C := by
  have hkpow : ∀ j, (0 : ℝ) ≤ k ^ delta j := fun j => le_of_lt (zpow_pos (by linarith) _)
  have hrec := selector_per_cycle_recurrence sol i vstar tStart tHold enc
    (fun j => k ^ delta j) epsmix epswrite epshold hkpow hmix hdiag hhold hwrite
  exact DepthBudget.depth_aware_all_time_tube
    (fun j => |sol.u (tStart j) i - enc j i|) dep delta
    (fun j => epsmix j + epswrite j + k ^ delta j * epshold j) hk hrec hdepth
    (fun j => abs_nonneg _) hdnn hgrow hdecay heta hC hbeta

/-- **Selector flag-window tube.**  From the all-time boundary tube on the held
config (`|u(tStart j) flag − enc j flag| ≤ r`) and a window-hold bound (the live
config `z` stays within `slack` of that boundary error throughout the read window),
the flag coordinate stays within `1/4` of the true encoded flag in every read
window — exactly the `hflag_read` hypothesis `selector_dyn_assembled_euclidean_simulation`
consumes. -/
theorem selector_flag_window_tube
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    (flagCoord : Fin d) (enc : ℕ → Fin d → ℝ) (tStart : ℕ → ℝ) {r slack : ℝ}
    (htube : ∀ j, |sol.u (tStart j) flagCoord - enc j flagCoord| ≤ r)
    (hwindow : ∀ j t, t ∈ sched.zActiveWindow j →
      |sol.z t flagCoord - enc j flagCoord| ≤
        |sol.u (tStart j) flagCoord - enc j flagCoord| + slack)
    (hsmall : r + slack ≤ 1 / 4) :
    ∀ j t, t ∈ sched.zActiveWindow j →
      |sol.z t flagCoord - enc j flagCoord| ≤ 1 / 4 := by
  intro j t ht
  calc |sol.z t flagCoord - enc j flagCoord|
      ≤ |sol.u (tStart j) flagCoord - enc j flagCoord| + slack := hwindow j t ht
    _ ≤ r + slack := by linarith [htube j]
    _ ≤ 1 / 4 := hsmall

/-- **(D-tube core) Selector flag-read from the per-cycle recurrence.**  Composes
`selector_boundary_tube_decay` (the held config's all-time boundary tube on the flag
coordinate, from the per-cycle recurrence with geometrically-decaying defect) with
`selector_flag_window_tube` (lifting the held-config tube to the live config `z` via the
window-hold) to obtain the flag-read `|z flag − enc flag| ≤ 1/4` in every read window — exactly
the `hflag_read` of `bgp_unconditional_selector_assembled`.  The per-cycle premises (`hmix` from
`gate_mix_error_approx`, `hdiag`/`hhold`/`hwrite` from the Reach lemmas, `hdecay` from the gain
growth, `hwindow` from the `z`-Reach) are discharged by the concrete M_U solution. -/
theorem selector_flag_read_of_recurrence
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    (flagCoord : Fin d) (vstar : ℕ → V)
    (tStart tHold : ℕ → ℝ) (enc : ℕ → Fin d → ℝ)
    (dep delta : ℕ → ℤ) (epsmix epswrite epshold : ℕ → ℝ)
    {k d0 beta eta C slack : ℝ} (hk : 1 < k)
    (hmix : ∀ j,
      |selectorMixTarget branch sol.u sol.lam (tHold j) flagCoord
          - BranchData.evalBranch (branch (vstar j)) (sol.u (tHold j)) flagCoord| ≤ epsmix j)
    (hdiag : ∀ j,
      |BranchData.evalBranch (branch (vstar j)) (sol.u (tHold j)) flagCoord - enc (j + 1) flagCoord|
        ≤ k ^ delta j * |sol.u (tHold j) flagCoord - enc j flagCoord|)
    (hhold : ∀ j,
      |sol.u (tHold j) flagCoord - enc j flagCoord|
        ≤ |sol.u (tStart j) flagCoord - enc j flagCoord| + epshold j)
    (hwrite : ∀ j,
      |sol.u (tStart (j + 1)) flagCoord
          - selectorMixTarget branch sol.u sol.lam (tHold j) flagCoord| ≤ epswrite j)
    (hdepth : ∀ j, dep (j + 1) = dep j - delta j) (hdnn : ∀ j, 0 ≤ dep j)
    (hgrow : ∀ j, (dep j : ℝ) ≤ d0 + beta * (j : ℝ))
    (hdecay : ∀ j,
      epsmix j + epswrite j + k ^ delta j * epshold j ≤ C * Real.exp (-eta * (j : ℝ)))
    (heta : beta * Real.log k < eta) (hC : 0 ≤ C) (hbeta : 0 ≤ beta)
    (hwindow : ∀ j t, t ∈ sched.zActiveWindow j →
      |sol.z t flagCoord - enc j flagCoord| ≤
        |sol.u (tStart j) flagCoord - enc j flagCoord| + slack)
    (hsmall :
      DepthBudget.W k dep (fun j => |sol.u (tStart j) flagCoord - enc j flagCoord|) 0
        + DepthBudget.geometricBudgetConstant k d0 beta eta C + slack ≤ 1 / 4) :
    ∀ j t, t ∈ sched.zActiveWindow j →
      |sol.z t flagCoord - enc j flagCoord| ≤ 1 / 4 := by
  have htube := selector_boundary_tube_decay sol flagCoord vstar tStart tHold enc dep delta
    epsmix epswrite epshold hk hmix hdiag hhold hwrite hdepth hdnn hgrow hdecay heta hC hbeta
  exact selector_flag_window_tube sol flagCoord enc tStart htube hwindow hsmall

/-- **Selector simultaneous-induction skeleton** (the `contract_all_time_tracking` pattern,
abstracted).  Given the loop-invariant components `Weighted`/`Window`/`Branch`/`Recur` as
predicates on the cycle index, the initial weighted bound, and the four per-step
implications (weighted → window [via hold-slack], window → branch [margins-from-tube],
weighted∧window∧branch → recurrence [cycle_step + margins], weighted∧recurrence → weighted′
[depth budget]), the full invariant bundle holds at every cycle.  The M_U instantiation
plugs in concrete invariants and discharges the implications — `window → branch` via
`universal_selector_margins_on_window`, `… → recurrence` via `SelectorDynSol.cycle_step`. -/
theorem selector_simultaneous_induction
    (Weighted Window Branch Recur : ℕ → Prop)
    (hinit : Weighted 0)
    (hwin_of_weighted : ∀ j, Weighted j → Window j)
    (hbranch_of_window : ∀ j, Window j → Branch j)
    (hrecur_of_branch : ∀ j, Weighted j → Window j → Branch j → Recur j)
    (hweighted_step : ∀ j, Weighted j → Recur j → Weighted (j + 1)) :
    ∀ j, Weighted j ∧ Window j ∧ Branch j ∧ Recur j := by
  intro j
  induction j with
  | zero =>
      have hw := hinit
      have hwin := hwin_of_weighted 0 hw
      have hb := hbranch_of_window 0 hwin
      exact ⟨hw, hwin, hb, hrecur_of_branch 0 hw hwin hb⟩
  | succ j ih =>
      have hw := hweighted_step j ih.1 ih.2.2.2
      have hwin := hwin_of_weighted (j + 1) hw
      have hb := hbranch_of_window (j + 1) hwin
      exact ⟨hw, hwin, hb, hrecur_of_branch (j + 1) hw hwin hb⟩

end Tube

/-! ## IVP → solution bridge (solution existence) -/

section Bridge

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule}

/-- **Field solution → `SelectorDynSol`.**  A solution `y` of the extended polynomial
field `selectorAssembledField` (with the clock gate-coordinate identities) is a
`SelectorDynSol`, reading the config/selector/gain coordinates off `y` and taking the
clock scalar functions to be the field-polynomial evaluations along `y`.  Analog of
`dynContractIteratorSol_of_contractAssembledField_solution`; the dynamic mixture is
intrinsic to `y`, so no external field-evaluation identity is needed. -/
noncomputable def selectorDynSol_of_selectorAssembledField_solution
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    {Aq Kq cμq cαq : ℚ} {L R : ℕ}
    (hA : p.A = (Aq : ℝ)) (hcμ : p.cμ = (cμq : ℝ)) (hcα : p.cα = (cαq : ℝ))
    (hL : p.L = L)
    (hdomain_nonneg : ∀ t : ℝ, t ∈ sched.domain → 0 ≤ t)
    (y : ℝ → Fin (selectorDim d V) → ℝ)
    (hyode : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt y
        (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
          (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
            Aq Kq cμq cαq L R i)) t)
    (hycont : Continuous y)
    (hgateZ : ∀ t : ℝ, 0 ≤ t →
      y t (selOfContract V (contractGateZ d)) =
        bGateZ L (y t (selOfContract V (contractMu d))) t)
    (hgateU : ∀ t : ℝ, 0 ≤ t →
      y t (selOfContract V (contractGateU d)) =
        bGateU L (y t (selOfContract V (contractMu d))) t)
    (readoutP : V → (Fin d → ℝ) → ℝ)
    (hα0 : y 0 (selOfContract V (contractAlpha d)) = 1)
    (hμ0 : y 0 (selOfContract V (contractMu d)) = 0)
    (h_P : ∀ (v : V) (t : ℝ), 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (PpolyP v) =
        readoutP v (fun i => y t (selU V i))) :
    SelectorDynSol d B V p sched branch
      (fun t => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) chiResetP)
      (fun t => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) chiGateP)
      (fun t => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) kappaP)
      (fun t => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) gainP)
      readoutP := by
  classical
  refine
    { z := fun t i => y t (selZ V i)
      u := fun t i => y t (selU V i)
      lam := fun v t => y t (selLamCoord v)
      G := fun t => y t (selGCoord d V)
      μ := fun t => y t (selOfContract V (contractMu d))
      α := fun t => y t (selOfContract V (contractAlpha d))
      init_z := fun i => y 0 (selZ V i)
      init_u := fun i => y 0 (selU V i)
      z_at_zero := rfl
      u_at_zero := rfl
      α_at_zero := hα0
      μ_at_zero := hμ0
      cont_z := fun i => (continuous_apply (selZ V i)).comp hycont
      cont_u := fun i => (continuous_apply (selU V i)).comp hycont
      cont_lam := fun v => (continuous_apply (selLamCoord v)).comp hycont
      cont_G := (continuous_apply (selGCoord d V)).comp hycont
      z_hasDeriv := ?_
      u_hasDeriv := ?_
      lam_hasDeriv := ?_
      G_hasDeriv := ?_
      μ_hasDeriv := ?_
      α_hasDeriv := ?_ }
  · intro t ht i
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (selZ V i)
    have heq :
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
              Aq Kq cμq cαq L R (selZ V i)) =
          p.A * y t (selOfContract V (contractAlpha d)) *
            bGateZ p.L (y t (selOfContract V (contractMu d))) t *
            (selectorMixTarget branch (fun t i => y t (selU V i))
                (fun v t => y t (selLamCoord v)) t i - y t (selZ V i)) := by
      rw [selectorAssembledField_z]
      simp [selectorMixField, selectorMixTarget, selectorF, hgateZ t ht0, hA, hL]
    exact heq ▸ hcoord
  · intro t ht i
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (selU V i)
    have heq :
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
              Aq Kq cμq cαq L R (selU V i)) =
          p.A * y t (selOfContract V (contractAlpha d)) *
            bGateU p.L (y t (selOfContract V (contractMu d))) t *
            (y t (selZ V i) - y t (selU V i)) := by
      rw [selectorAssembledField_u]
      simp [hgateU t ht0, hA, hL]
    exact heq ▸ hcoord
  · intro v t ht
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (selLamCoord v)
    have heq :
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
              Aq Kq cμq cαq L R (selLamCoord v)) =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) chiResetP *
              MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) kappaP *
              (1 / 2 - y t (selLamCoord v))
            + MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) chiGateP *
              (MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) gainP *
                readoutP v (fun i => y t (selU V i)) *
                (y t (selLamCoord v) * (1 - y t (selLamCoord v)))) := by
      rw [selectorAssembledField_lam, eval₂_selectorResetGateFieldPoly, h_P v t ht0]
    exact heq ▸ hcoord
  · intro t ht
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (selGCoord d V)
    have heq :
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
              Aq Kq cμq cαq L R (selGCoord d V)) =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) chiGateP *
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) gainP := by
      rw [selectorAssembledField_G, eval₂_selectorGainFieldPoly]
    exact heq ▸ hcoord
  · intro t ht
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (selOfContract V (contractMu d))
    have heq :
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
              Aq Kq cμq cαq L R (selOfContract V (contractMu d))) = p.cμ := by
      rw [selectorAssembledField_mu]
      simp [hcμ]
    exact heq ▸ hcoord
  · intro t ht
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (selOfContract V (contractAlpha d))
    have heq :
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selectorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
              Aq Kq cμq cαq L R (selOfContract V (contractAlpha d))) =
          p.cα * y t (selOfContract V (contractAlpha d)) := by
      rw [selectorAssembledField_alpha]
      simp [hcα]
    exact heq ▸ hcoord

end Bridge

/-! ## Latch existence -/

section Latch

/-- The scalar latch ODE `a' = K·gPulse·(g − a)` has an explicit solution with
`a 0 = 0`, for any continuous driving signal `g`.  Generic integrating-factor
construction (copied from `contract_latch_solution_exists`, abstracted over the
driving signal). -/
theorem gPulse_linear_ode_exists (g : ℝ → ℝ) (hg : Continuous g) (K : ℝ) (R : ℕ) :
    ∃ a : ℝ → ℝ, a 0 = 0 ∧
      ∀ t : ℝ, HasDerivAt a (K * gPulse R t * (g t - a t)) t := by
  classical
  set φ : ℝ → ℝ := fun t => K * gPulse R t with hφdef
  have hφcont : Continuous φ := by
    have hgp : Continuous (gPulse R) := gPulse_continuous R
    fun_prop
  set Φ : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, φ s with hΦdef
  have hΦderiv : ∀ t : ℝ, HasDerivAt Φ (φ t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hφcont.intervalIntegrable 0 t)
      (hφcont.stronglyMeasurableAtFilter _ _) hφcont.continuousAt
  have hΦcont : Continuous Φ :=
    continuous_iff_continuousAt.mpr (fun t => (hΦderiv t).continuousAt)
  set Bb : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, φ s * g s * Real.exp (Φ s) with hBdef
  have hBcont_integrand : Continuous (fun s : ℝ => φ s * g s * Real.exp (Φ s)) :=
    (hφcont.mul hg).mul (Real.continuous_exp.comp hΦcont)
  have hBderiv : ∀ t : ℝ, HasDerivAt Bb (φ t * g t * Real.exp (Φ t)) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hBcont_integrand.intervalIntegrable 0 t)
      (hBcont_integrand.stronglyMeasurableAtFilter _ _) hBcont_integrand.continuousAt
  set a : ℝ → ℝ := fun t => Real.exp (-(Φ t)) * Bb t with hadef
  refine ⟨a, ?_, ?_⟩
  · simp [hadef, hBdef]
  · intro t
    have hExpDeriv : HasDerivAt (fun τ : ℝ => Real.exp (-(Φ τ)))
        (-(φ t) * Real.exp (-(Φ t))) t := by
      have hneg : HasDerivAt (fun τ : ℝ => -(Φ τ)) (-(φ t)) t := (hΦderiv t).neg
      have h := hneg.exp
      convert h using 1
      ring
    have hprod := hExpDeriv.mul (hBderiv t)
    convert hprod using 1
    simp only [hadef, hφdef, hBdef]
    have hexp : Real.exp (-(Φ t)) * Real.exp (Φ t) = 1 := by rw [← Real.exp_add]; simp
    have hterm :
        Real.exp (-(Φ t)) * (K * gPulse R t * g t * Real.exp (Φ t)) =
          K * gPulse R t * g t := by
      calc
        Real.exp (-(Φ t)) * (K * gPulse R t * g t * Real.exp (Φ t))
            = (Real.exp (-(Φ t)) * Real.exp (Φ t)) * (K * gPulse R t * g t) := by ring
        _ = K * gPulse R t * g t := by rw [hexp]; ring
    rw [hterm]; ring

/-- **Selector latch existence.**  Given continuity of the driving signal
`t ↦ Hval (sol.z t)`, the selector solution carries a halt latch. -/
theorem selector_latch_solution_exists
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    (Hval : (Fin d → ℝ) → ℝ)
    (hHcont : Continuous fun t => Hval (sol.z t))
    (K : ℝ) (R : ℕ) :
    Nonempty (SelectorHaltLatchSol sol Hval K R) := by
  obtain ⟨a, ha0, hode⟩ := gPulse_linear_ode_exists (fun t => Hval (sol.z t)) hHcont K R
  exact ⟨{ a := a, init_a := ha0, ode_a := hode }⟩

/-- **Dummy selector latch.**  With zero driver and zero gain, the constant-zero
latch solves the selector latch ODE without any continuity hypothesis. -/
noncomputable def selector_zero_latch_solution
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    (R : ℕ) :
    SelectorHaltLatchSol sol (fun _ : (Fin d → ℝ) => (0 : ℝ)) 0 R := by
  refine { a := fun _ => 0, init_a := rfl, ode_a := ?_ }
  intro t
  simpa using (hasDerivAt_const (x := t) (c := (0 : ℝ)))

#print axioms selector_zero_latch_solution

/-- **Assembled selector main theorem with direct `z`-coordinate readout.**  This is the
same compactification package as `main_assembled_dyn_selector`, but the chart readout is
attached to an arbitrary Euclidean coordinate `readCoordE` whose value is the selector
configuration coordinate `sol.z readCoord`.  It is the packaging lemma needed by the
corrected next-config flag endpoint, whose region conclusions are already stated on
`sol.z haltCoord` rather than on the auxiliary latch `La.a`. -/
theorem main_assembled_dyn_selector_zreadout
    {d B : ℕ} {Conf : Type} [Primcodable Conf]
    (M : UndecidableMachine Conf)
    (p : DynGateParams) (sched : PhaseSchedule)
    {V : Type} [Fintype V] (branch : V → BranchData d B)
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (fieldPkg :
      SelectorPolynomialFieldPackage d B V p sched branch
        chiResetF chiGateF kappaF gainF Pv Hval K R)
    (sol : ℕ → SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    (hHcont : ∀ w, Continuous fun t => Hval ((sol w).z t))
    (readCoord : Fin d) (readCoordE : Fin fieldPkg.nE)
    (hread_value :
      ∀ (w : ℕ)
        (s : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorHaltLatchSol s Hval K R) (t : ℝ),
          fieldPkg.tuple w s La t readCoordE = s.z t readCoord)
    (correct_halt_z : ∀ w, M.toDiscreteMachine.haltsOn w →
      ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ (sol w).z t readCoord ∧ (sol w).z t readCoord ≤ 1)
    (correct_nonhalt_z : ∀ w, ¬ M.toDiscreteMachine.haltsOn w →
      ∃ T : ℝ, ∀ t ≥ T, 0 ≤ (sol w).z t readCoord ∧ (sol w).z t readCoord ≤ 1 / 4) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P M) := by
  classical
  let La := fun w =>
    Classical.choice (selector_latch_solution_exists (sol w) Hval (hHcont w) K R)
  obtain ⟨Y, _htang, htransfer⟩ :=
    compactification_exists fieldPkg.nE fieldPkg.field
  let P : Ripple.BoundedUniversality.GPAC.PIVP ℚ :=
    { n := fieldPkg.nE + 1
      vf := Y
      init := fieldPkg.init }
  have htrans : ∀ w,
      ∃ s : ℝ → ℝ, s 0 = 0 ∧ StrictMonoOn s (Set.Ici 0) ∧
        Filter.Tendsto s Filter.atTop Filter.atTop ∧
        ∀ τ : ℝ, 0 ≤ τ → HasDerivAt
          (fun σ => stereo (fieldPkg.tuple w (sol w) (La w) (s σ)))
          (fun j => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
            (stereo (fieldPkg.tuple w (sol w) (La w) (s τ))) (Y j)) τ := by
    intro w
    exact htransfer (fieldPkg.tuple w (sol w) (La w))
      (fieldPkg.tuple_ode w (sol w) (La w))
  choose s hs0 _hsmono hstend hsphere using htrans
  refine ⟨P, ⟨{
    traj := fun w τ => stereo (fieldPkg.tuple w (sol w) (La w) (s w τ))
    init_at_zero := ?_
    solves_ode := ?_
    bounded := ?_
    encoder_presented := fieldPkg.init_presented
    readout := ?_
    correct_halt := ?_
    correct_nonhalt := ?_
  }⟩⟩
  · intro w
    funext j
    rw [hs0 w]
    dsimp [P, Ripple.BoundedUniversality.GPAC.PIVP.realInit]
    refine Fin.cases ?_ ?_ j
    · simp [stereo, stereoDenom, fieldPkg.init_zero w (sol w) (La w)]
    · intro i
      simp [stereo, stereoDenom, fieldPkg.init_succ w (sol w) (La w) i]
  · intro w τ hτ
    simpa [P, Ripple.BoundedUniversality.GPAC.PIVP.evalVF] using hsphere w τ hτ
  · refine ⟨1, by norm_num, ?_⟩
    intro w τ i hτ
    exact sel_stereo_abs_le_one _ _
  · exact { hA := readCoordE.succ, h0 := 0, ne := by simp }
  · intro w hw
    obtain ⟨T, hT⟩ := correct_halt_z w hw
    have hev : ∀ᶠ τ in Filter.atTop, max T 0 ≤ s w τ :=
      (hstend w).eventually (Filter.eventually_ge_atTop (max T 0))
    obtain ⟨Θ, hΘ⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max Θ 0, ?_⟩
    intro τ hτ
    have hΘτ : Θ ≤ τ := le_trans (le_max_left Θ 0) hτ
    have hsge : max T 0 ≤ s w τ := hΘ τ hΘτ
    have hTle : T ≤ s w τ := le_trans (le_max_left T 0) hsge
    have hz := hT (s w τ) hTle
    have hcoord :
        3 / 4 ≤ fieldPkg.tuple w (sol w) (La w) (s w τ) readCoordE ∧
          fieldPkg.tuple w (sol w) (La w) (s w τ) readCoordE ≤ 1 := by
      simpa [hread_value w (sol w) (La w) (s w τ)] using hz
    have hreg :=
      (stereo_readout_transfer
        (fieldPkg.tuple w (sol w) (La w) (s w τ)) readCoordE).1 hcoord
    simpa [ChartThresholdReadout.HaltRegion, P] using hreg
  · intro w hw
    obtain ⟨T, hT⟩ := correct_nonhalt_z w hw
    have hev : ∀ᶠ τ in Filter.atTop, max T 0 ≤ s w τ :=
      (hstend w).eventually (Filter.eventually_ge_atTop (max T 0))
    obtain ⟨Θ, hΘ⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max Θ 0, ?_⟩
    intro τ hτ
    have hΘτ : Θ ≤ τ := le_trans (le_max_left Θ 0) hτ
    have hsge : max T 0 ≤ s w τ := hΘ τ hΘτ
    have hTle : T ≤ s w τ := le_trans (le_max_left T 0) hsge
    have hz := hT (s w τ) hTle
    have hcoord :
        0 ≤ fieldPkg.tuple w (sol w) (La w) (s w τ) readCoordE ∧
          fieldPkg.tuple w (sol w) (La w) (s w τ) readCoordE ≤ 1 / 4 := by
      simpa [hread_value w (sol w) (La w) (s w τ)] using hz
    have hreg :=
      (stereo_readout_transfer
        (fieldPkg.tuple w (sol w) (La w) (s w τ)) readCoordE).2 hcoord
    simpa [ChartThresholdReadout.NonhaltRegion, P] using hreg

#print axioms main_assembled_dyn_selector_zreadout

/-- **Assembled selector main theorem with direct `z`-coordinate readout and no real
halt latch.**  The compactified Euclidean tuple still has the selector layout's `a`
slot, but it is filled by the dummy zero latch for the dummy field data
`Hval := 0`, `K := 0`.  Since the readout is on a `z` coordinate, correctness uses
only `selectorTupleTraj_z` through `hread_value`; no continuity of the real halt
indicator is needed. -/
theorem main_assembled_dyn_selector_zreadout_nolatch
    {d B : ℕ} {Conf : Type} [Primcodable Conf]
    (M : UndecidableMachine Conf)
    (p : DynGateParams) (sched : PhaseSchedule)
    {V : Type} [Fintype V] (branch : V → BranchData d B)
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}
    {R : ℕ}
    (fieldPkg :
      SelectorPolynomialFieldPackage d B V p sched branch
        chiResetF chiGateF kappaF gainF Pv
        (fun _ : (Fin d → ℝ) => (0 : ℝ)) 0 R)
    (sol : ℕ → SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    (readCoord : Fin d) (readCoordE : Fin fieldPkg.nE)
    (hread_value :
      ∀ (w : ℕ)
        (s : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorHaltLatchSol s (fun _ : (Fin d → ℝ) => (0 : ℝ)) 0 R) (t : ℝ),
          fieldPkg.tuple w s La t readCoordE = s.z t readCoord)
    (correct_halt_z : ∀ w, M.toDiscreteMachine.haltsOn w →
      ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ (sol w).z t readCoord ∧ (sol w).z t readCoord ≤ 1)
    (correct_nonhalt_z : ∀ w, ¬ M.toDiscreteMachine.haltsOn w →
      ∃ T : ℝ, ∀ t ≥ T, 0 ≤ (sol w).z t readCoord ∧ (sol w).z t readCoord ≤ 1 / 4) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P M) := by
  classical
  let La := fun w => selector_zero_latch_solution (sol w) R
  obtain ⟨Y, _htang, htransfer⟩ :=
    compactification_exists fieldPkg.nE fieldPkg.field
  let P : Ripple.BoundedUniversality.GPAC.PIVP ℚ :=
    { n := fieldPkg.nE + 1
      vf := Y
      init := fieldPkg.init }
  have htrans : ∀ w,
      ∃ s : ℝ → ℝ, s 0 = 0 ∧ StrictMonoOn s (Set.Ici 0) ∧
        Filter.Tendsto s Filter.atTop Filter.atTop ∧
        ∀ τ : ℝ, 0 ≤ τ → HasDerivAt
          (fun σ => stereo (fieldPkg.tuple w (sol w) (La w) (s σ)))
          (fun j => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
            (stereo (fieldPkg.tuple w (sol w) (La w) (s τ))) (Y j)) τ := by
    intro w
    exact htransfer (fieldPkg.tuple w (sol w) (La w))
      (fieldPkg.tuple_ode w (sol w) (La w))
  choose s hs0 _hsmono hstend hsphere using htrans
  refine ⟨P, ⟨{
    traj := fun w τ => stereo (fieldPkg.tuple w (sol w) (La w) (s w τ))
    init_at_zero := ?_
    solves_ode := ?_
    bounded := ?_
    encoder_presented := fieldPkg.init_presented
    readout := ?_
    correct_halt := ?_
    correct_nonhalt := ?_
  }⟩⟩
  · intro w
    funext j
    rw [hs0 w]
    dsimp [P, Ripple.BoundedUniversality.GPAC.PIVP.realInit]
    refine Fin.cases ?_ ?_ j
    · simp [stereo, stereoDenom, fieldPkg.init_zero w (sol w) (La w)]
    · intro i
      simp [stereo, stereoDenom, fieldPkg.init_succ w (sol w) (La w) i]
  · intro w τ hτ
    simpa [P, Ripple.BoundedUniversality.GPAC.PIVP.evalVF] using hsphere w τ hτ
  · refine ⟨1, by norm_num, ?_⟩
    intro w τ i hτ
    exact sel_stereo_abs_le_one _ _
  · exact { hA := readCoordE.succ, h0 := 0, ne := by simp }
  · intro w hw
    obtain ⟨T, hT⟩ := correct_halt_z w hw
    have hev : ∀ᶠ τ in Filter.atTop, max T 0 ≤ s w τ :=
      (hstend w).eventually (Filter.eventually_ge_atTop (max T 0))
    obtain ⟨Θ, hΘ⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max Θ 0, ?_⟩
    intro τ hτ
    have hΘτ : Θ ≤ τ := le_trans (le_max_left Θ 0) hτ
    have hsge : max T 0 ≤ s w τ := hΘ τ hΘτ
    have hTle : T ≤ s w τ := le_trans (le_max_left T 0) hsge
    have hz := hT (s w τ) hTle
    have hcoord :
        3 / 4 ≤ fieldPkg.tuple w (sol w) (La w) (s w τ) readCoordE ∧
          fieldPkg.tuple w (sol w) (La w) (s w τ) readCoordE ≤ 1 := by
      simpa [hread_value w (sol w) (La w) (s w τ)] using hz
    have hreg :=
      (stereo_readout_transfer
        (fieldPkg.tuple w (sol w) (La w) (s w τ)) readCoordE).1 hcoord
    simpa [ChartThresholdReadout.HaltRegion, P] using hreg
  · intro w hw
    obtain ⟨T, hT⟩ := correct_nonhalt_z w hw
    have hev : ∀ᶠ τ in Filter.atTop, max T 0 ≤ s w τ :=
      (hstend w).eventually (Filter.eventually_ge_atTop (max T 0))
    obtain ⟨Θ, hΘ⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max Θ 0, ?_⟩
    intro τ hτ
    have hΘτ : Θ ≤ τ := le_trans (le_max_left Θ 0) hτ
    have hsge : max T 0 ≤ s w τ := hΘ τ hΘτ
    have hTle : T ≤ s w τ := le_trans (le_max_left T 0) hsge
    have hz := hT (s w τ) hTle
    have hcoord :
        0 ≤ fieldPkg.tuple w (sol w) (La w) (s w τ) readCoordE ∧
          fieldPkg.tuple w (sol w) (La w) (s w τ) readCoordE ≤ 1 / 4 := by
      simpa [hread_value w (sol w) (La w) (s w τ)] using hz
    have hreg :=
      (stereo_readout_transfer
        (fieldPkg.tuple w (sol w) (La w) (s w τ)) readCoordE).2 hcoord
    simpa [ChartThresholdReadout.NonhaltRegion, P] using hreg

#print axioms main_assembled_dyn_selector_zreadout_nolatch

section KernelAdapter

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}

/-- Constructor wrapper for the selector convergence kernel (analog of
`contract_latch_kernel_of_readout_bounds`). -/
theorem selector_latch_kernel_of_readout_bounds
    (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {flagCoord : Fin d} (I : ContractFlagIndicatorPackage flagCoord)
    {K : ℝ} {R : ℕ} (La : SelectorHaltLatchSol sol I.Hval K R) (hK : 0 < K)
    (hhigh :
      (∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ sched.zActiveWindow j,
        1 - I.eta ≤ I.Hval (sol.z t)) →
        ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1)
    (hlow :
      (∀ j : ℕ, ∀ t ∈ sched.zActiveWindow j, I.Hval (sol.z t) ≤ I.eta) →
        ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4) :
    SelectorLatchConvergenceKernel sol flagCoord I La :=
  { K_pos := hK
    high_from_eventual_indicator := hhigh
    low_from_all_indicator := hlow }

/-- **Selector latch adapter.**  Per solution, a latch and convergence kernel, given
continuity of the driving signal and the scalar read-window convergence bounds (the
analytic latch convergence is supplied as a hypothesis, exactly as in the contract
`hlatch_adapter`). -/
theorem selector_hlatch_adapter
    {flagCoord : Fin d} (I : ContractFlagIndicatorPackage flagCoord)
    {K : ℝ} {R : ℕ} (hK : 0 < K)
    (hHcont :
      ∀ sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv,
        Continuous fun t => I.Hval (sol.z t))
    (hhigh :
      ∀ (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorHaltLatchSol sol I.Hval K R),
        (∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ sched.zActiveWindow j,
          1 - I.eta ≤ I.Hval (sol.z t)) →
          ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1)
    (hlow :
      ∀ (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorHaltLatchSol sol I.Hval K R),
        (∀ j : ℕ, ∀ t ∈ sched.zActiveWindow j, I.Hval (sol.z t) ≤ I.eta) →
          ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4) :
    ∀ sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv,
      ∃ La : SelectorHaltLatchSol sol I.Hval K R,
        SelectorLatchConvergenceKernel sol flagCoord I La := by
  intro sol
  obtain ⟨La⟩ := selector_latch_solution_exists sol I.Hval (hHcont sol) K R
  exact ⟨La, selector_latch_kernel_of_readout_bounds sol I La hK (hhigh sol La) (hlow sol La)⟩

/-- **hsupply assembly.**  Builds the per-input supply that `bgp_unconditional_selector`
consumes, from: a per-input selector solution, continuity of the driving signal, the
scalar latch convergence bounds, and the per-input flag tube + flag domain.  Pure
composition of `selector_latch_solution_exists` + `selector_latch_kernel_of_readout_bounds`.
Reduces the headline to the per-input solution/flag/convergence facts. -/
theorem selector_hsupply_assemble
    {nS : ℕ} {Conf : Type} [Primcodable Conf] {M : DiscreteMachine Conf}
    (E : StackMachineEncoding d nS M)
    {flagCoord : Fin d} (I : ContractFlagIndicatorPackage flagCoord)
    {K : ℝ} {R : ℕ} (hK : 0 < K)
    (sol : ℕ → SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    (hHcont : ∀ w, Continuous fun t => I.Hval ((sol w).z t))
    (hhigh : ∀ (w : ℕ) (La : SelectorHaltLatchSol (sol w) I.Hval K R),
      (∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ sched.zActiveWindow j,
        1 - I.eta ≤ I.Hval ((sol w).z t)) →
        ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1)
    (hlow : ∀ (w : ℕ) (La : SelectorHaltLatchSol (sol w) I.Hval K R),
      (∀ j : ℕ, ∀ t ∈ sched.zActiveWindow j, I.Hval ((sol w).z t) ≤ I.eta) →
        ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4)
    (hflag_read : ∀ w j t, t ∈ sched.zActiveWindow j →
      |(sol w).z t flagCoord - E.enc (M.step^[j] (M.init w)) flagCoord| ≤ 1 / 4)
    (hflag_dom : ∀ w j t, t ∈ sched.zActiveWindow j →
      (sol w).z t flagCoord ∈ Set.Icc (0 : ℝ) 1) :
    ∀ w : ℕ,
      ∃ (s : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorHaltLatchSol s I.Hval K R),
        SelectorLatchConvergenceKernel s flagCoord I La ∧
        (∀ j t, t ∈ sched.zActiveWindow j →
          |s.z t flagCoord - E.enc (M.step^[j] (M.init w)) flagCoord| ≤ 1 / 4) ∧
        (∀ j t, t ∈ sched.zActiveWindow j → s.z t flagCoord ∈ Set.Icc (0 : ℝ) 1) := by
  intro w
  obtain ⟨La⟩ := selector_latch_solution_exists (sol w) I.Hval (hHcont w) K R
  exact ⟨sol w, La,
    selector_latch_kernel_of_readout_bounds (sol w) I La hK (hhigh w La) (hlow w La),
    hflag_read w, hflag_dom w⟩

end KernelAdapter

end Latch

/-! ## Conditional unconditional headline (architecture capstone) -/

/-- **Selector simulation headline (conditional).**  Composing the full chain: given
the selector polynomial field package and a per-input supply of a selector solution +
latch + convergence kernel + the per-cycle flag tube, there is a single PIVP that
eventually-threshold simulates `M`.  The supply hypothesis is exactly the output of the
per-cycle recurrence / all-time tube / margins layer (`selector_flag_window_tube` +
`selector_boundary_tube` + the latch construction); discharging it for the universal
machine `M_U` makes the headline `bgp_unconditional` truly unconditional, since the
clock-driven selector's mixture error `ε_mix → 0` makes the step-contract obligations
satisfiable. -/
theorem bgp_unconditional_selector
    {d B nS : ℕ} {Conf : Type} [Primcodable Conf]
    (M : UndecidableMachine Conf)
    (E : StackMachineEncoding d nS M.toDiscreteMachine)
    {V : Type} [Fintype V] (branch : V → BranchData d B)
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}
    (p : DynGateParams) (sched : PhaseSchedule)
    (flagCoord : Fin d)
    (flagPkg : HaltFlagPackage E flagCoord)
    (I : ContractFlagIndicatorPackage flagCoord)
    {K : ℝ} {R : ℕ} (hK : 0 < K)
    (fieldPkg : SelectorPolynomialFieldPackage d B V p sched branch
      chiResetF chiGateF kappaF gainF Pv I.Hval K R)
    (hsupply : ∀ w : ℕ,
      ∃ (sol : SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorHaltLatchSol sol I.Hval K R),
        SelectorLatchConvergenceKernel sol flagCoord I La ∧
        (∀ j t, t ∈ sched.zActiveWindow j →
          |sol.z t flagCoord
            - E.enc (M.toDiscreteMachine.step^[j] (M.toDiscreteMachine.init w)) flagCoord|
            ≤ 1 / 4) ∧
        (∀ j t, t ∈ sched.zActiveWindow j →
          sol.z t flagCoord ∈ Set.Icc (0 : ℝ) 1)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P M) :=
  main_assembled_dyn_selector M p sched branch
    (selector_dyn_assembled_euclidean_simulation M.toDiscreteMachine E branch p sched
      flagCoord flagPkg I hK hsupply)
    fieldPkg

/-- **Selector headline, fully assembled (conditional).**  Threads the entire chain: from
the field package, a per-input selector solution, driving-signal continuity, scalar latch
convergence, and the per-input flag tube + flag domain, there is a PIVP that
eventually-threshold simulates `M`.  This is `bgp_unconditional_selector` with `hsupply`
discharged via `selector_hsupply_assemble`; the remaining inputs are exactly the
M_U-specific facts (solution existence + the flag tube from the simultaneous induction +
latch convergence + the field package realization). -/
theorem bgp_unconditional_selector_assembled
    {d B nS : ℕ} {Conf : Type} [Primcodable Conf]
    (M : UndecidableMachine Conf)
    (E : StackMachineEncoding d nS M.toDiscreteMachine)
    {V : Type} [Fintype V] (branch : V → BranchData d B)
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}
    (p : DynGateParams) (sched : PhaseSchedule)
    (flagCoord : Fin d)
    (flagPkg : HaltFlagPackage E flagCoord)
    (I : ContractFlagIndicatorPackage flagCoord)
    {K : ℝ} {R : ℕ} (hK : 0 < K)
    (fieldPkg : SelectorPolynomialFieldPackage d B V p sched branch
      chiResetF chiGateF kappaF gainF Pv I.Hval K R)
    (sol : ℕ → SelectorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    (hHcont : ∀ w, Continuous fun t => I.Hval ((sol w).z t))
    (hhigh : ∀ (w : ℕ) (La : SelectorHaltLatchSol (sol w) I.Hval K R),
      (∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ sched.zActiveWindow j,
        1 - I.eta ≤ I.Hval ((sol w).z t)) →
        ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1)
    (hlow : ∀ (w : ℕ) (La : SelectorHaltLatchSol (sol w) I.Hval K R),
      (∀ j : ℕ, ∀ t ∈ sched.zActiveWindow j, I.Hval ((sol w).z t) ≤ I.eta) →
        ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4)
    (hflag_read : ∀ w j t, t ∈ sched.zActiveWindow j →
      |(sol w).z t flagCoord
        - E.enc (M.toDiscreteMachine.step^[j] (M.toDiscreteMachine.init w)) flagCoord| ≤ 1 / 4)
    (hflag_dom : ∀ w j t, t ∈ sched.zActiveWindow j →
      (sol w).z t flagCoord ∈ Set.Icc (0 : ℝ) 1) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P M) :=
  bgp_unconditional_selector M E branch p sched flagCoord flagPkg I hK fieldPkg
    (selector_hsupply_assemble (M := M.toDiscreteMachine) E I hK sol hHcont hhigh hlow
      hflag_read hflag_dom)

end Package

end Ripple.BoundedUniversality.BGP
