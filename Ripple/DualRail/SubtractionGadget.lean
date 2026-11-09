/-
  Ripple.DualRail.SubtractionGadget — DNA25 Lemma 8 two-stage gadget

  Formalizes the DNA25 Lemma 8 two-stage reciprocal/subtraction gadget. Given
  two PIVPs already computing `α` and `β` respectively (with `α > β ≥ 0`,
  both bounded in `(0, 1)`), we build a new PIVP whose designated output
  converges to `α − β`, using **only non-negative rational coefficients** in
  both the `prod` and `degr` parts of the resulting `PolyCRNDecomposition`.
  This is the subtraction closure missing from the raw `realtime_field_sub`
  theorem, which relies on multiplication by `-1` and therefore breaks the
  PCD non-negativity invariant.

  The construction (DNA25 Lemma 8, two-stage):

    Stage A.   z_r' = (1 + y · z_r) − x · z_r         z_r(0) = 0
    Stage B.   z'   = 1 − z_r · z                     z(0)   = 0

  where `x` and `y` are the already-computing input species (components of the
  original PIVPs, referenced at their respective output indices). Convergence:

    z_r(t)  →  1 / (α − β)
    z(t)    →   (α − β)

  and both stages are PCD-compatible:

    z_r row.   prod = 1 + y · z_r  (non-neg coefficients),
               degr = x
               field = prod − degr · z_r = (1 + y·z_r) − x·z_r  ✓

    z row.     prod = 1,
               degr = z_r
               field = prod − degr · z = 1 − z_r·z  ✓

  This file provides:
    * `subtractionPIVP`        — the syntactic `PolyPIVP (d₁ + d₂ + 2)`
    * `subtractionPCD`         — its `PolyCRNDecomposition` (non-neg prod/degr)
    * `subtraction_cbtc_pcd`   — the main CBTC+PCD assembly theorem.

  Reference: [RTCRN2] Huang–Klinge–Lathrop, DNA 25 (2019), Lemma 8.
-/

import Ripple.Core.BoundedTime
import Ripple.LPP.Defs
import Ripple.LPP.AddRationalPos
import Ripple.DualRail.Lemma8ReciprocalTracker
import Ripple.DualRail.Lemma8SubtractionTracker
import Mathlib.Algebra.MvPolynomial.Rename

-- Some reductions between syntactic field/init projections and their explicit
-- `Fin.snoc` representations go through a definitionally equal `show`.  This is
-- the natural idiom for these index-plumbing proofs.
set_option linter.style.show false

namespace Ripple
namespace DualRail

open MvPolynomial
open Ripple.Algebraic (coeff_rename_castSucc_nonneg)

/-! ## Index plumbing

The combined state has dimension `(d₁ + d₂) + 1 + 1`:
  * first `d₁ + d₂` slots : input PIVPs (PIVP₁ then PIVP₂, via `Fin.append`),
  * penultimate slot      : `z_r`,
  * last slot             : `z`.

We use the injection `iₓ : Fin d₁ ↪ Fin ((d₁ + d₂) + 1 + 1)` for species of the
first input PIVP and `iᵧ : Fin d₂ ↪ Fin ((d₁ + d₂) + 1 + 1)` for species of
the second, realised as
  `iₓ := Fin.castSucc ∘ Fin.castSucc ∘ Fin.castAdd d₂`
  `iᵧ := Fin.castSucc ∘ Fin.castSucc ∘ Fin.natAdd d₁`.
-/

section Indexing

variable {d₁ d₂ : ℕ}

/-- Embed a species index of the first input PIVP into the combined state. -/
def injX (d₁ d₂ : ℕ) (i : Fin d₁) : Fin ((d₁ + d₂) + 1 + 1) :=
  (Fin.castAdd d₂ i).castSucc.castSucc

/-- Embed a species index of the second input PIVP into the combined state. -/
def injY (d₁ d₂ : ℕ) (j : Fin d₂) : Fin ((d₁ + d₂) + 1 + 1) :=
  (Fin.natAdd d₁ j).castSucc.castSucc

/-- The index of `z_r` (the reciprocal tracker). -/
def idxZR (d₁ d₂ : ℕ) : Fin ((d₁ + d₂) + 1 + 1) :=
  (Fin.last (d₁ + d₂)).castSucc

/-- The index of `z` (the subtraction output). -/
def idxZ (d₁ d₂ : ℕ) : Fin ((d₁ + d₂) + 1 + 1) :=
  Fin.last ((d₁ + d₂) + 1)

lemma injX_injective (d₁ d₂ : ℕ) : Function.Injective (injX d₁ d₂) := by
  intro i j h
  unfold injX at h
  have h₁ := (Fin.castSucc_injective _) ((Fin.castSucc_injective _) h)
  exact Fin.castAdd_injective d₁ d₂ h₁

lemma injY_injective (d₁ d₂ : ℕ) : Function.Injective (injY d₁ d₂) := by
  intro i j h
  unfold injY at h
  have h₁ := (Fin.castSucc_injective _) ((Fin.castSucc_injective _) h)
  exact Fin.natAdd_injective d₂ d₁ h₁

/-- Rename a polynomial over `Fin d₁` to one over the combined state, along `injX`. -/
noncomputable def liftX (d₁ d₂ : ℕ) (p : MvPolynomial (Fin d₁) ℚ) :
    MvPolynomial (Fin ((d₁ + d₂) + 1 + 1)) ℚ :=
  rename (injX d₁ d₂) p

/-- Rename a polynomial over `Fin d₂` to one over the combined state, along `injY`. -/
noncomputable def liftY (d₁ d₂ : ℕ) (p : MvPolynomial (Fin d₂) ℚ) :
    MvPolynomial (Fin ((d₁ + d₂) + 1 + 1)) ℚ :=
  rename (injY d₁ d₂) p

/-- Non-negativity of coefficients is preserved by `rename` along `injX`. -/
lemma coeff_liftX_nonneg (d₁ d₂ : ℕ) (p : MvPolynomial (Fin d₁) ℚ)
    (hp : ∀ σ, 0 ≤ p.coeff σ) : ∀ σ, 0 ≤ (liftX d₁ d₂ p).coeff σ := by
  classical
  intro σ
  unfold liftX
  by_cases h : ∃ u : Fin d₁ →₀ ℕ, u.mapDomain (injX d₁ d₂) = σ
  · obtain ⟨u, hu⟩ := h
    subst hu
    rw [coeff_rename_mapDomain (injX d₁ d₂) (injX_injective d₁ d₂)]
    exact hp u
  · rw [coeff_rename_eq_zero (injX d₁ d₂) p σ (by
      intro u hu; exact absurd ⟨u, hu⟩ h)]

/-- Non-negativity of coefficients is preserved by `rename` along `injY`. -/
lemma coeff_liftY_nonneg (d₁ d₂ : ℕ) (p : MvPolynomial (Fin d₂) ℚ)
    (hp : ∀ σ, 0 ≤ p.coeff σ) : ∀ σ, 0 ≤ (liftY d₁ d₂ p).coeff σ := by
  classical
  intro σ
  unfold liftY
  by_cases h : ∃ u : Fin d₂ →₀ ℕ, u.mapDomain (injY d₁ d₂) = σ
  · obtain ⟨u, hu⟩ := h
    subst hu
    rw [coeff_rename_mapDomain (injY d₁ d₂) (injY_injective d₁ d₂)]
    exact hp u
  · rw [coeff_rename_eq_zero (injY d₁ d₂) p σ (by
      intro u hu; exact absurd ⟨u, hu⟩ h)]

end Indexing

/-! ## Stage A: z_r production/degradation

    z_r' = (1 + y · z_r) − x · z_r,  z_r(0) = 0.

Here `x` is the output species of the first input PIVP (at index `injX (·.output)`)
and `y` is the output species of the second (at index `injY (·.output)`).
-/

section StageA

variable {d₁ d₂ : ℕ}

/-- Production polynomial for `z_r`: `1 + X_y · X_{z_r}` (non-neg coefficients). -/
noncomputable def zrProd (d₁ d₂ : ℕ) (iy : Fin d₂) :
    MvPolynomial (Fin ((d₁ + d₂) + 1 + 1)) ℚ :=
  1 + X (injY d₁ d₂ iy) * X (idxZR d₁ d₂)

/-- Degradation polynomial for `z_r`: `X_x` (non-neg). -/
noncomputable def zrDegr (d₁ d₂ : ℕ) (ix : Fin d₁) :
    MvPolynomial (Fin ((d₁ + d₂) + 1 + 1)) ℚ :=
  X (injX d₁ d₂ ix)

/-- Field polynomial for `z_r`: prod − degr · X_{z_r}. -/
noncomputable def zrField (d₁ d₂ : ℕ) (ix : Fin d₁) (iy : Fin d₂) :
    MvPolynomial (Fin ((d₁ + d₂) + 1 + 1)) ℚ :=
  zrProd d₁ d₂ iy - zrDegr d₁ d₂ ix * X (idxZR d₁ d₂)

lemma zrProd_coeff_nonneg (d₁ d₂ : ℕ) (iy : Fin d₂) :
    ∀ σ, 0 ≤ (zrProd d₁ d₂ iy).coeff σ := by
  classical
  intro σ
  unfold zrProd
  rw [MvPolynomial.coeff_add]
  have h1 : 0 ≤ (1 : MvPolynomial (Fin ((d₁+d₂)+1+1)) ℚ).coeff σ := by
    rw [show (1 : MvPolynomial (Fin ((d₁+d₂)+1+1)) ℚ) = C 1 from (map_one _).symm,
        MvPolynomial.coeff_C]
    split_ifs
    · norm_num
    · exact le_refl _
  have h2 : 0 ≤ ((X (injY d₁ d₂ iy) * X (idxZR d₁ d₂) :
      MvPolynomial (Fin ((d₁+d₂)+1+1)) ℚ)).coeff σ := by
    -- Coefficient of a product of two monomials X_a * X_b at σ is 1 if
    -- σ = single a 1 + single b 1, else 0.  Either way ≥ 0.
    rw [MvPolynomial.coeff_mul]
    apply Finset.sum_nonneg
    intro ⟨σ₁, σ₂⟩ _
    apply mul_nonneg
    · rw [MvPolynomial.coeff_X']; split_ifs <;> norm_num
    · rw [MvPolynomial.coeff_X']; split_ifs <;> norm_num
  linarith

lemma zrDegr_coeff_nonneg (d₁ d₂ : ℕ) (ix : Fin d₁) :
    ∀ σ, 0 ≤ (zrDegr d₁ d₂ ix).coeff σ := by
  classical
  intro σ
  unfold zrDegr
  rw [MvPolynomial.coeff_X']
  split_ifs <;> norm_num

end StageA

/-! ## Stage B: z production/degradation

    z' = 1 − z_r · z,  z(0) = 0.
-/

section StageB

variable {d₁ d₂ : ℕ}

/-- Production polynomial for `z`: `1`. -/
noncomputable def zProd (d₁ d₂ : ℕ) :
    MvPolynomial (Fin ((d₁ + d₂) + 1 + 1)) ℚ := 1

/-- Degradation polynomial for `z`: `X_{z_r}`. -/
noncomputable def zDegr (d₁ d₂ : ℕ) :
    MvPolynomial (Fin ((d₁ + d₂) + 1 + 1)) ℚ := X (idxZR d₁ d₂)

/-- Field polynomial for `z`: `1 − X_{z_r} · X_z`. -/
noncomputable def zField (d₁ d₂ : ℕ) :
    MvPolynomial (Fin ((d₁ + d₂) + 1 + 1)) ℚ :=
  zProd d₁ d₂ - zDegr d₁ d₂ * X (idxZ d₁ d₂)

lemma zProd_coeff_nonneg (d₁ d₂ : ℕ) :
    ∀ σ, 0 ≤ (zProd d₁ d₂).coeff σ := by
  classical
  intro σ
  unfold zProd
  rw [show (1 : MvPolynomial (Fin ((d₁+d₂)+1+1)) ℚ) = C 1 from (map_one _).symm,
      MvPolynomial.coeff_C]
  split_ifs
  · norm_num
  · exact le_refl _

lemma zDegr_coeff_nonneg (d₁ d₂ : ℕ) :
    ∀ σ, 0 ≤ (zDegr d₁ d₂).coeff σ := by
  classical
  intro σ
  unfold zDegr
  rw [MvPolynomial.coeff_X']
  split_ifs <;> norm_num

end StageB

/-! ## The combined `PolyPIVP`

We package the two input PIVPs + Stages A and B into a single `PolyPIVP` of
dimension `(d₁ + d₂) + 1 + 1`, with the designated output the final slot
(`idxZ`, i.e. `z`), which converges to `α − β`.
-/

/-- The fields on the first `d₁ + d₂` slots (input PIVPs), packed as
`Fin.append (liftX P_x.field) (liftY P_y.field)`. -/
noncomputable def inputFields {d₁ d₂ : ℕ} (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    Fin (d₁ + d₂) → MvPolynomial (Fin ((d₁ + d₂) + 1 + 1)) ℚ :=
  Fin.append (fun i => liftX d₁ d₂ (Px.field i))
             (fun j => liftY d₁ d₂ (Py.field j))

/-- The combined field, built by two `Fin.snoc` layers on top of `inputFields`. -/
noncomputable def subtractionField {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    Fin ((d₁ + d₂) + 1 + 1) → MvPolynomial (Fin ((d₁ + d₂) + 1 + 1)) ℚ :=
  Fin.snoc
    (Fin.snoc (inputFields Px Py) (zrField d₁ d₂ Px.output Py.output))
    (zField d₁ d₂)

/-- The combined initial condition: inputs at their natural initial values, and
`z_r(0) = z(0) = 0` (both are freshly-introduced species). -/
noncomputable def subtractionInit {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    Fin ((d₁ + d₂) + 1 + 1) → ℚ :=
  Fin.snoc (Fin.snoc (Fin.append Px.init Py.init) (0 : ℚ)) (0 : ℚ)

/-- The two-stage subtraction/reciprocal gadget as a syntactic `PolyPIVP`. -/
noncomputable def subtractionPIVP {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) : PolyPIVP ((d₁ + d₂) + 1 + 1) where
  field := subtractionField Px Py
  init := subtractionInit Px Py
  output := idxZ d₁ d₂

@[simp] lemma subtractionPIVP_output {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    (subtractionPIVP Px Py).output = idxZ d₁ d₂ := rfl

@[simp] lemma subtractionPIVP_field_last {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    (subtractionPIVP Px Py).field (idxZ d₁ d₂) = zField d₁ d₂ := by
  show subtractionField Px Py (idxZ d₁ d₂) = _
  unfold subtractionField idxZ
  rw [Fin.snoc_last]

@[simp] lemma subtractionPIVP_field_zr {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    (subtractionPIVP Px Py).field (idxZR d₁ d₂) =
      zrField d₁ d₂ Px.output Py.output := by
  show subtractionField Px Py (idxZR d₁ d₂) = _
  unfold subtractionField idxZR
  -- idxZR = (Fin.last (d₁+d₂)).castSucc; outer snoc is at castSucc, inner at last.
  rw [show ((Fin.last (d₁+d₂)).castSucc :
      Fin ((d₁+d₂)+1+1)) = Fin.castSucc (Fin.last (d₁+d₂)) from rfl]
  rw [Fin.snoc_castSucc, Fin.snoc_last]

@[simp] lemma subtractionPIVP_init_zr {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    (subtractionPIVP Px Py).init (idxZR d₁ d₂) = 0 := by
  show subtractionInit Px Py (idxZR d₁ d₂) = 0
  unfold subtractionInit idxZR
  rw [show ((Fin.last (d₁+d₂)).castSucc :
      Fin ((d₁+d₂)+1+1)) = Fin.castSucc (Fin.last (d₁+d₂)) from rfl]
  rw [Fin.snoc_castSucc, Fin.snoc_last]

@[simp] lemma subtractionPIVP_init_z {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂) :
    (subtractionPIVP Px Py).init (idxZ d₁ d₂) = 0 := by
  show subtractionInit Px Py (idxZ d₁ d₂) = 0
  unfold subtractionInit idxZ
  rw [Fin.snoc_last]

/-! ## The `PolyCRNDecomposition` of the combined system

We assemble the per-species `prod`, `degr` from:
  * `inputFieldsProd`, `inputFieldsDegr` — the lifted original PCDs, sharing
    the same index-embedding as `inputFields`;
  * Stage-A polynomials `zrProd`, `zrDegr`;
  * Stage-B polynomials `zProd`, `zDegr`.

The key coefficient non-negativity lemmas (`coeff_liftX_nonneg`,
`coeff_liftY_nonneg`, `zrProd_coeff_nonneg`, etc.) were proven above.
-/

/-- `prod` for the input-PIVP block, lifted along `injX` / `injY`. -/
noncomputable def inputProdRow {d₁ d₂ : ℕ}
    {Px : PolyPIVP d₁} {Py : PolyPIVP d₂}
    (pcdX : PolyCRNDecomposition d₁ Px)
    (pcdY : PolyCRNDecomposition d₂ Py) :
    Fin (d₁ + d₂) → MvPolynomial (Fin ((d₁ + d₂) + 1 + 1)) ℚ :=
  Fin.append (fun i => liftX d₁ d₂ (pcdX.prod i))
             (fun j => liftY d₁ d₂ (pcdY.prod j))

/-- `degr` for the input-PIVP block, lifted along `injX` / `injY`. -/
noncomputable def inputDegrRow {d₁ d₂ : ℕ}
    {Px : PolyPIVP d₁} {Py : PolyPIVP d₂}
    (pcdX : PolyCRNDecomposition d₁ Px)
    (pcdY : PolyCRNDecomposition d₂ Py) :
    Fin (d₁ + d₂) → MvPolynomial (Fin ((d₁ + d₂) + 1 + 1)) ℚ :=
  Fin.append (fun i => liftX d₁ d₂ (pcdX.degr i))
             (fun j => liftY d₁ d₂ (pcdY.degr j))

/-- Combined `prod`: input block, then `zrProd`, then `zProd`. -/
noncomputable def subtractionProd {d₁ d₂ : ℕ}
    {Px : PolyPIVP d₁} {Py : PolyPIVP d₂}
    (pcdX : PolyCRNDecomposition d₁ Px)
    (pcdY : PolyCRNDecomposition d₂ Py) :
    Fin ((d₁ + d₂) + 1 + 1) → MvPolynomial (Fin ((d₁ + d₂) + 1 + 1)) ℚ :=
  Fin.snoc (Fin.snoc (inputProdRow pcdX pcdY) (zrProd d₁ d₂ Py.output))
           (zProd d₁ d₂)

/-- Combined `degr`: input block, then `zrDegr`, then `zDegr`. -/
noncomputable def subtractionDegr {d₁ d₂ : ℕ}
    {Px : PolyPIVP d₁} {Py : PolyPIVP d₂}
    (pcdX : PolyCRNDecomposition d₁ Px)
    (pcdY : PolyCRNDecomposition d₂ Py) :
    Fin ((d₁ + d₂) + 1 + 1) → MvPolynomial (Fin ((d₁ + d₂) + 1 + 1)) ℚ :=
  Fin.snoc (Fin.snoc (inputDegrRow pcdX pcdY) (zrDegr d₁ d₂ Px.output))
           (zDegr d₁ d₂)

/-! ### field_eq: the renamed input PIVP fields still decompose as prod − degr · X.

This is the key algebraic fact that allows the lifted input block to participate
in the combined PCD.  We use that `rename` is a ring hom (so it commutes with
`-` and `*`) and sends `X_i` to `X_{inj i}`.
-/

lemma liftX_field_eq {d₁ d₂ : ℕ}
    {Px : PolyPIVP d₁} (pcdX : PolyCRNDecomposition d₁ Px) (i : Fin d₁) :
    liftX d₁ d₂ (Px.field i) =
      liftX d₁ d₂ (pcdX.prod i) -
        liftX d₁ d₂ (pcdX.degr i) * X (injX d₁ d₂ i) := by
  unfold liftX
  rw [pcdX.field_eq i]
  rw [map_sub, map_mul, rename_X]

lemma liftY_field_eq {d₁ d₂ : ℕ}
    {Py : PolyPIVP d₂} (pcdY : PolyCRNDecomposition d₂ Py) (j : Fin d₂) :
    liftY d₁ d₂ (Py.field j) =
      liftY d₁ d₂ (pcdY.prod j) -
        liftY d₁ d₂ (pcdY.degr j) * X (injY d₁ d₂ j) := by
  unfold liftY
  rw [pcdY.field_eq j]
  rw [map_sub, map_mul, rename_X]

/-- The `PolyCRNDecomposition` of the combined subtraction PIVP. -/
noncomputable def subtractionPCD {d₁ d₂ : ℕ}
    {Px : PolyPIVP d₁} {Py : PolyPIVP d₂}
    (pcdX : PolyCRNDecomposition d₁ Px)
    (pcdY : PolyCRNDecomposition d₂ Py) :
    PolyCRNDecomposition ((d₁ + d₂) + 1 + 1) (subtractionPIVP Px Py) where
  prod := subtractionProd pcdX pcdY
  degr := subtractionDegr pcdX pcdY
  prod_nonneg := by
    intro i σ
    unfold subtractionProd
    -- Case split on the outermost Fin.snoc.
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · -- i = Fin.last ((d₁+d₂)+1): zProd
      rw [Fin.snoc_last]
      exact zProd_coeff_nonneg d₁ d₂ σ
    · -- i = i'.castSucc : either zrProd (inner last) or input block.
      rw [Fin.snoc_castSucc]
      refine Fin.lastCases ?_ (fun i'' => ?_) i'
      · rw [Fin.snoc_last]
        exact zrProd_coeff_nonneg d₁ d₂ Py.output σ
      · rw [Fin.snoc_castSucc]
        -- input block: append, distinguish castAdd / natAdd
        unfold inputProdRow
        refine Fin.addCases (fun iL => ?_) (fun iR => ?_) i''
        · rw [Fin.append_left]
          exact coeff_liftX_nonneg d₁ d₂ (pcdX.prod iL) (pcdX.prod_nonneg iL) σ
        · rw [Fin.append_right]
          exact coeff_liftY_nonneg d₁ d₂ (pcdY.prod iR) (pcdY.prod_nonneg iR) σ
  degr_nonneg := by
    intro i σ
    unfold subtractionDegr
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · rw [Fin.snoc_last]
      exact zDegr_coeff_nonneg d₁ d₂ σ
    · rw [Fin.snoc_castSucc]
      refine Fin.lastCases ?_ (fun i'' => ?_) i'
      · rw [Fin.snoc_last]
        exact zrDegr_coeff_nonneg d₁ d₂ Px.output σ
      · rw [Fin.snoc_castSucc]
        unfold inputDegrRow
        refine Fin.addCases (fun iL => ?_) (fun iR => ?_) i''
        · rw [Fin.append_left]
          exact coeff_liftX_nonneg d₁ d₂ (pcdX.degr iL) (pcdX.degr_nonneg iL) σ
        · rw [Fin.append_right]
          exact coeff_liftY_nonneg d₁ d₂ (pcdY.degr iR) (pcdY.degr_nonneg iR) σ
  init_nonneg := by
    intro i
    show 0 ≤ subtractionInit Px Py i
    unfold subtractionInit
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · rw [Fin.snoc_last]
    · rw [Fin.snoc_castSucc]
      refine Fin.lastCases ?_ (fun i'' => ?_) i'
      · rw [Fin.snoc_last]
      · rw [Fin.snoc_castSucc]
        refine Fin.addCases (fun iL => ?_) (fun iR => ?_) i''
        · rw [Fin.append_left]
          exact pcdX.init_nonneg iL
        · rw [Fin.append_right]
          exact pcdY.init_nonneg iR
  field_eq := by
    intro i
    show subtractionField Px Py i =
      subtractionProd pcdX pcdY i - subtractionDegr pcdX pcdY i * X i
    unfold subtractionField subtractionProd subtractionDegr
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · -- i = Fin.last ((d₁+d₂)+1): the z row.
      rw [Fin.snoc_last, Fin.snoc_last, Fin.snoc_last]
      -- field = zField d₁ d₂ = zProd - zDegr * X (Fin.last _)
      rfl
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
      refine Fin.lastCases ?_ (fun i'' => ?_) i'
      · -- i = (Fin.last (d₁+d₂)).castSucc : the z_r row.
        rw [Fin.snoc_last, Fin.snoc_last, Fin.snoc_last]
        -- zrField = zrProd - zrDegr * X(idxZR)
        show zrField d₁ d₂ Px.output Py.output =
          zrProd d₁ d₂ Py.output - zrDegr d₁ d₂ Px.output *
            X ((Fin.last (d₁+d₂)).castSucc)
        rfl
      · rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        unfold inputFields inputProdRow inputDegrRow
        refine Fin.addCases (fun iL => ?_) (fun iR => ?_) i''
        · rw [Fin.append_left, Fin.append_left, Fin.append_left]
          -- goal: liftX ... (Px.field iL) = liftX (pcdX.prod iL)
          --       - liftX (pcdX.degr iL) * X (iL.castAdd d₂).castSucc.castSucc
          -- Note X ((iL.castAdd d₂).castSucc.castSucc) = X (injX d₁ d₂ iL)
          exact liftX_field_eq pcdX iL
        · rw [Fin.append_right, Fin.append_right, Fin.append_right]
          exact liftY_field_eq pcdY iR

/-! ## Main theorem

Given two CBTC+PCD witnesses for `α, β ∈ (0, 1)` with `α > β ≥ 0`, the
DNA25 two-stage gadget defined above is itself a CBTC+PCD witness for
`α − β`.  The PCD non-negativity is fully proved (above).  The analytic
content — existence of a bounded solution, trajectory continuity, and
exponential convergence of `z(t)` to `α − β` — is now also fully proved
by glueing the two scalar-level stages from `Lemma8StageA` (reciprocal
tracker `z_r → 1/γ`) and `Lemma8StageB` (subtraction layer `z → γ`),
where `γ := α − β`, into a full `PIVP.Solution` on the combined system.
-/

/-- **DNA25 Lemma 8 analytic content (loosened hypothesis, axiom-clean).**

The analytic core of DNA25 Lemma 8.  Per [RTCRN2] Lemma 8, the hypothesis
needed is *not* that each of `x(t)` and `y(t)` individually converges to
its target (with individual moduli), but only that the *difference*
`x(t) − y(t)` converges to `α − β`.  The two-stage Duhamel argument only
ever uses the convergence of the difference `x − y`, never the two
components separately.

Inputs:
  * `Px`, `Py` : syntactic polynomial PIVPs computing `α`, `β`
    (semantically — via `solX`, `solY`) and both bounded;
  * `diffMod`  : a joint-difference modulus: past `diffMod r`, the
    trajectory difference `x − y` is within `exp(-r)` of `α − β`;
  * the hypotheses `0 < α < 1`, `0 ≤ β < 1`, `β < α` that ensure the
    reciprocal stage is well-conditioned (`γ := α − β ∈ (0, 1)`).

Proof structure (fully formalised):

  Stage A (`z_r`):  `z_r' = 1 − (x − y) · z_r`.  The scalar Duhamel/
    integrating-factor analysis lives in `Lemma8ReciprocalTracker.zr_tracker_exists`,
    producing a continuous, nonneg, uniformly bounded `z_r → 1/γ`.

  Stage B (`z`):    `z' = 1 − z_r · z`.  A second Duhamel analysis
    (`Lemma8SubtractionTracker.z_tracker_exists`) produces a continuous, nonneg,
    uniformly bounded `z → γ`, given the Stage A output.

  Combined PIVP solution:  using `Fin.snoc`, we glue the two new scalar
    trajectories on top of the appended `solX`/`solY` input trajectories
    (on the `d₁ + d₂` sub-block), producing a full `PIVP.Solution` on the
    combined `(d₁+d₂)+1+1`-dimensional system.  Each coordinate's ODE is
    verified componentwise via `hasDerivAt_pi` + `MvPolynomial.eval₂_rename`
    for the lifted input block.

Downstream consumers (`subtraction_cbtc_pcd`) build the joint-difference
convergence `h_diff_conv` from two individual CBTC convergences via
triangle inequality.

[RTCRN2] Huang–Klinge–Lathrop, DNA 25 (2019), Lemma 8. -/
theorem subtraction_lemma8_analytic {α β : ℝ} {d₁ d₂ : ℕ}
    (Px : PolyPIVP d₁) (Py : PolyPIVP d₂)
    (solX : PIVP.Solution Px.toPIVP) (solY : PIVP.Solution Py.toPIVP)
    (_hXbd : Px.toPIVP.IsBounded solX.trajectory)
    (_hYbd : Py.toPIVP.IsBounded solY.trajectory)
    (_hXcont : Continuous solX.trajectory)
    (_hYcont : Continuous solY.trajectory)
    (_diffMod : TimeModulus)
    (_h_diff_conv : ∀ r : ℕ, ∀ t : ℝ, 0 ≤ t → t > _diffMod r →
      |solX.trajectory t Px.output - solY.trajectory t Py.output - (α - β)|
      < Real.exp (-(r : ℝ)))
    (_hα_lo : 0 < α) (_hα_hi : α < 1)
    (_hβ_lo : 0 ≤ β) (_hβ_hi : β < 1)
    (_hαβ : β < α) :
    ∃ (sol' : PIVP.Solution (subtractionPIVP Px Py).toPIVP)
      (modulus' : TimeModulus),
      (subtractionPIVP Px Py).toPIVP.IsBounded sol'.trajectory ∧
      (∀ r : ℕ, ∀ t : ℝ, t > modulus' r →
        |sol'.trajectory t (idxZ d₁ d₂) - (α - β)| < Real.exp (-(r : ℝ))) ∧
      Continuous sol'.trajectory := by
  -- Set γ = α − β, verify 0 < γ < 1.
  set γ : ℝ := α - β with hγ_def
  have hγ_lo : 0 < γ := by rw [hγ_def]; linarith
  have hγ_hi : γ < 1 := by rw [hγ_def]; linarith
  -- Extract bounds on solX, solY.
  obtain ⟨Mx, hMx_pos, hMx_bd⟩ := _hXbd
  obtain ⟨My, hMy_pos, hMy_bd⟩ := _hYbd
  -- Build Stage-A DriverData.
  let driver : ℝ → ℝ := fun t =>
    solX.trajectory t Px.output - solY.trajectory t Py.output
  have driver_cont : Continuous driver :=
    ((continuous_apply Px.output).comp _hXcont).sub
      ((continuous_apply Py.output).comp _hYcont)
  -- The driver is bounded by Mx + My on [0,∞).
  have driver_abs_bd : ∀ t, 0 ≤ t → |driver t| ≤ Mx + My := by
    intro t ht
    have hxle : |solX.trajectory t Px.output| ≤ Mx := by
      have := norm_le_pi_norm (solX.trajectory t) Px.output
      rw [Real.norm_eq_abs] at this
      exact le_trans this (hMx_bd t ht)
    have hyle : |solY.trajectory t Py.output| ≤ My := by
      have := norm_le_pi_norm (solY.trajectory t) Py.output
      rw [Real.norm_eq_abs] at this
      exact le_trans this (hMy_bd t ht)
    -- |x - y| ≤ |x| + |y|
    have habs_tri : |driver t| ≤ |solX.trajectory t Px.output| +
            |solY.trajectory t Py.output| :=
      abs_sub (solX.trajectory t Px.output) (solY.trajectory t Py.output)
    linarith
  let D : Lemma8ReciprocalTracker.DriverData γ :=
    { driver := driver
      driver_cont := driver_cont
      driver_bound := Mx + My
      driver_bound_nn := by linarith
      driver_abs_bd := driver_abs_bd
      diffMod := _diffMod
      diffMod_conv := fun r t ht ht' => _h_diff_conv r t ht ht' }
  -- Run Stage A.
  obtain ⟨zr, B_zr, zrMod, hBzr_pos, hzr_cont, hzr_zero,
      hzr_ode, hzr_nn, hzr_bd, hzr_conv, -⟩ :=
    Lemma8ReciprocalTracker.zr_tracker_exists hγ_lo hγ_hi D
  -- Build Stage-B ZrData.
  let Z : Lemma8SubtractionTracker.ZrData γ :=
    { zr := zr
      zr_cont := hzr_cont
      zr_nonneg := hzr_nn
      zr_bound := B_zr
      zr_bound_pos := hBzr_pos
      zr_abs_bd := hzr_bd
      zrModulus := zrMod
      zr_conv := fun r t _ht ht' => hzr_conv r t ht' }
  -- Run Stage B.
  obtain ⟨z, B_z, zMod, hBz_pos, hz_cont, hz_zero, hz_ode, hz_nn, hz_bd, hz_conv, -⟩ :=
    Lemma8SubtractionTracker.z_tracker_exists hγ_lo hγ_hi Z
  -- Build the full trajectory.
  let xyBlock : ℝ → Fin (d₁ + d₂) → ℝ := fun t =>
    Fin.append (fun i => solX.trajectory t i) (fun j => solY.trajectory t j)
  let T : ℝ → Fin ((d₁ + d₂) + 1 + 1) → ℝ := fun t =>
    Fin.snoc (Fin.snoc (xyBlock t) (zr t)) (z t)
  -- Unfolding lemmas. We use the non-dependent specialisation of Fin.snoc.
  have T_idxZ : ∀ t, T t (idxZ d₁ d₂) = z t := by
    intro t
    change (Fin.snoc (α := fun _ => ℝ)
              (Fin.snoc (α := fun _ => ℝ) (xyBlock t) (zr t)) (z t))
              (idxZ d₁ d₂) = z t
    unfold idxZ
    exact Fin.snoc_last _ _
  have T_idxZR : ∀ t, T t (idxZR d₁ d₂) = zr t := by
    intro t
    change (Fin.snoc (α := fun _ => ℝ)
              (Fin.snoc (α := fun _ => ℝ) (xyBlock t) (zr t)) (z t))
              (idxZR d₁ d₂) = zr t
    unfold idxZR
    rw [show ((Fin.last (d₁+d₂)).castSucc : Fin ((d₁+d₂)+1+1))
          = Fin.castSucc (Fin.last (d₁+d₂)) from rfl]
    rw [Fin.snoc_castSucc]
    exact Fin.snoc_last _ _
  have T_injX : ∀ t (i : Fin d₁),
      T t (injX d₁ d₂ i) = solX.trajectory t i := by
    intro t i
    change (Fin.snoc (α := fun _ => ℝ)
              (Fin.snoc (α := fun _ => ℝ) (xyBlock t) (zr t)) (z t))
              (injX d₁ d₂ i) = solX.trajectory t i
    unfold injX
    rw [show ((Fin.castAdd d₂ i).castSucc.castSucc : Fin ((d₁+d₂)+1+1))
          = Fin.castSucc (Fin.castSucc (Fin.castAdd d₂ i)) from rfl]
    rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    change Fin.append (fun i => solX.trajectory t i)
              (fun j => solY.trajectory t j) (Fin.castAdd d₂ i)
          = solX.trajectory t i
    rw [Fin.append_left]
  have T_injY : ∀ t (j : Fin d₂),
      T t (injY d₁ d₂ j) = solY.trajectory t j := by
    intro t j
    change (Fin.snoc (α := fun _ => ℝ)
              (Fin.snoc (α := fun _ => ℝ) (xyBlock t) (zr t)) (z t))
              (injY d₁ d₂ j) = solY.trajectory t j
    unfold injY
    rw [show ((Fin.natAdd d₁ j).castSucc.castSucc : Fin ((d₁+d₂)+1+1))
          = Fin.castSucc (Fin.castSucc (Fin.natAdd d₁ j)) from rfl]
    rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    change Fin.append (fun i => solX.trajectory t i)
              (fun j => solY.trajectory t j) (Fin.natAdd d₁ j)
          = solY.trajectory t j
    rw [Fin.append_right]
  -- Helper: subtractionInit on inputs equals the respective PIVPs' init on
  -- the corresponding index.
  have subInit_injX : ∀ (iL : Fin d₁),
      subtractionInit Px Py (injX d₁ d₂ iL) = Px.init iL := by
    intro iL
    change (Fin.snoc (α := fun _ => ℚ)
              (Fin.snoc (α := fun _ => ℚ) (Fin.append Px.init Py.init) (0 : ℚ))
              (0 : ℚ)) (injX d₁ d₂ iL) = Px.init iL
    unfold injX
    rw [show ((Fin.castAdd d₂ iL).castSucc.castSucc : Fin ((d₁+d₂)+1+1))
          = Fin.castSucc (Fin.castSucc (Fin.castAdd d₂ iL)) from rfl]
    rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    rw [Fin.append_left]
  have subInit_injY : ∀ (iR : Fin d₂),
      subtractionInit Px Py (injY d₁ d₂ iR) = Py.init iR := by
    intro iR
    change (Fin.snoc (α := fun _ => ℚ)
              (Fin.snoc (α := fun _ => ℚ) (Fin.append Px.init Py.init) (0 : ℚ))
              (0 : ℚ)) (injY d₁ d₂ iR) = Py.init iR
    unfold injY
    rw [show ((Fin.natAdd d₁ iR).castSucc.castSucc : Fin ((d₁+d₂)+1+1))
          = Fin.castSucc (Fin.castSucc (Fin.natAdd d₁ iR)) from rfl]
    rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    rw [Fin.append_right]
  -- Initial condition: T 0 = subtractionInit Px Py (as real-valued).
  have T_init : T 0 = (subtractionPIVP Px Py).toPIVP.init := by
    funext k
    show T 0 k = ((subtractionInit Px Py k : ℚ) : ℝ)
    -- Case split on k.
    refine Fin.lastCases ?_ (fun i' => ?_) k
    · -- k = Fin.last ((d₁+d₂)+1) = idxZ
      have h1 : T 0 (idxZ d₁ d₂) = z 0 := T_idxZ 0
      have h2 := subtractionPIVP_init_z Px Py
      show T 0 (idxZ d₁ d₂) = ((subtractionInit Px Py (idxZ d₁ d₂) : ℚ) : ℝ)
      rw [h1, hz_zero]
      -- h2 : (subtractionPIVP Px Py).init (idxZ d₁ d₂) = 0
      -- which is subtractionInit Px Py (idxZ d₁ d₂) = 0
      have h2' : subtractionInit Px Py (idxZ d₁ d₂) = 0 := h2
      rw [h2']; simp
    · refine Fin.lastCases ?_ (fun i'' => ?_) i'
      · -- i'.castSucc = idxZR
        have h1 : T 0 (idxZR d₁ d₂) = zr 0 := T_idxZR 0
        have h2' : subtractionInit Px Py (idxZR d₁ d₂) = 0 :=
          subtractionPIVP_init_zr Px Py
        show T 0 (idxZR d₁ d₂) = ((subtractionInit Px Py (idxZR d₁ d₂) : ℚ) : ℝ)
        rw [h1, hzr_zero, h2']; simp
      · -- i''.castSucc.castSucc : input block
        refine Fin.addCases (fun iL => ?_) (fun iR => ?_) i''
        · -- injX iL
          have h1 : T 0 (injX d₁ d₂ iL) = solX.trajectory 0 iL := T_injX 0 iL
          have h2 : subtractionInit Px Py (injX d₁ d₂ iL) = Px.init iL :=
            subInit_injX iL
          show T 0 (injX d₁ d₂ iL) = ((subtractionInit Px Py (injX d₁ d₂ iL) : ℚ) : ℝ)
          rw [h1, h2]
          have hsx := solX.init_cond
          have hxy : solX.trajectory 0 iL = ((Px.init iL : ℚ) : ℝ) := by
            rw [hsx]; rfl
          exact hxy
        · -- injY iR
          have h1 : T 0 (injY d₁ d₂ iR) = solY.trajectory 0 iR := T_injY 0 iR
          have h2 : subtractionInit Px Py (injY d₁ d₂ iR) = Py.init iR :=
            subInit_injY iR
          show T 0 (injY d₁ d₂ iR) = ((subtractionInit Px Py (injY d₁ d₂ iR) : ℚ) : ℝ)
          rw [h1, h2]
          have hsy := solY.init_cond
          have hxy : solY.trajectory 0 iR = ((Py.init iR : ℚ) : ℝ) := by
            rw [hsy]; rfl
          exact hxy
  -- is_solution: for each t ≥ 0, HasDerivAt T ((subtractionPIVP Px Py).toPIVP.field (T t)) t.
  have T_is_solution : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt T ((subtractionPIVP Px Py).toPIVP.field (T t)) t := by
    intro t ht
    refine hasDerivAt_pi.mpr ?_
    intro k
    -- Establish the per-coord derivative, matching each case.
    refine Fin.lastCases ?_ (fun i' => ?_) k
    · -- k = Fin.last ((d₁+d₂)+1) = idxZ: derivative from z_ode.
      -- Goal: HasDerivAt (fun s => T s (Fin.last ((d₁+d₂)+1)))
      --   ((subtractionPIVP Px Py).toPIVP.field (T t) (Fin.last ((d₁+d₂)+1))) t
      have hFz : (fun s => T s (Fin.last ((d₁+d₂)+1)))
          = fun s => z s := by
        funext s; exact T_idxZ s
      rw [hFz]
      have hFval : (subtractionPIVP Px Py).toPIVP.field (T t)
            (Fin.last ((d₁+d₂)+1)) = 1 - zr t * z t := by
        show ((subtractionPIVP Px Py).field (Fin.last ((d₁+d₂)+1))).eval₂
              (Rat.castHom ℝ) (T t) = _
        rw [show (Fin.last ((d₁+d₂)+1) : Fin ((d₁+d₂)+1+1))
              = idxZ d₁ d₂ from rfl]
        rw [subtractionPIVP_field_last]
        unfold zField zProd zDegr
        simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
                   MvPolynomial.eval₂_X, MvPolynomial.eval₂_one]
        rw [T_idxZR t, T_idxZ t]
      rw [hFval]
      exact hz_ode t ht
    · refine Fin.lastCases ?_ (fun i'' => ?_) i'
      · -- i'.castSucc = (Fin.last (d₁+d₂)).castSucc = idxZR: derivative from zr_ode.
        have hFzr : (fun s => T s (Fin.castSucc (Fin.last (d₁+d₂))))
            = fun s => zr s := by
          funext s
          show T s ((Fin.last (d₁+d₂)).castSucc) = zr s
          have := T_idxZR s
          exact this
        rw [hFzr]
        have hFval : (subtractionPIVP Px Py).toPIVP.field (T t)
              (Fin.castSucc (Fin.last (d₁+d₂))) = 1 - driver t * zr t := by
          show ((subtractionPIVP Px Py).field (Fin.castSucc (Fin.last (d₁+d₂)))).eval₂
                (Rat.castHom ℝ) (T t) = _
          rw [show (Fin.castSucc (Fin.last (d₁+d₂)) : Fin ((d₁+d₂)+1+1))
                = idxZR d₁ d₂ from rfl]
          rw [subtractionPIVP_field_zr]
          unfold zrField zrProd zrDegr
          simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add,
                     MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
                     MvPolynomial.eval₂_one]
          rw [T_idxZR t, T_injX t, T_injY t]
          -- Goal: 1 + solY.traj(Py.output) * zr t - solX.traj(Px.output) * zr t
          --       = 1 - (solX.traj(Px.output) - solY.traj(Py.output)) * zr t
          show (1 : ℝ) + solY.trajectory t Py.output * zr t
              - solX.trajectory t Px.output * zr t = 1 - driver t * zr t
          show (1 : ℝ) + solY.trajectory t Py.output * zr t
              - solX.trajectory t Px.output * zr t
            = 1 - (solX.trajectory t Px.output - solY.trajectory t Py.output) * zr t
          ring
        rw [hFval]
        -- hzr_ode gives HasDerivAt zr (1 - D.driver t * zr t) t; D.driver = driver.
        have := hzr_ode t ht
        exact this
      · -- i''.castSucc.castSucc: input block via Fin.addCases
        refine Fin.addCases (fun iL => ?_) (fun iR => ?_) i''
        · -- injX iL: inherit from solX.is_solution
          have hF : (fun s => T s ((Fin.castAdd d₂ iL).castSucc.castSucc))
              = fun s => solX.trajectory s iL := by
            funext s
            show T s ((Fin.castAdd d₂ iL).castSucc.castSucc) = _
            have := T_injX s iL
            show T s (injX d₁ d₂ iL) = solX.trajectory s iL
            exact this
          rw [hF]
          -- Original solution gives HasDerivAt (fun s => solX.trajectory s iL)
          --    ((Px.field iL).eval₂ (Rat.castHom ℝ) (solX.trajectory t)) t.
          have hDer_orig := hasDerivAt_pi.mp (solX.is_solution t ht) iL
          -- Match the field on the combined system.
          have hFval :
              (subtractionPIVP Px Py).toPIVP.field (T t)
                  ((Fin.castAdd d₂ iL).castSucc.castSucc)
                = (Px.field iL).eval₂ (Rat.castHom ℝ) (solX.trajectory t) := by
            show ((subtractionPIVP Px Py).field ((Fin.castAdd d₂ iL).castSucc.castSucc)).eval₂
                  (Rat.castHom ℝ) (T t) = _
            -- subtractionField at injX iL = liftX (Px.field iL).
            have h_fe :
                (subtractionPIVP Px Py).field ((Fin.castAdd d₂ iL).castSucc.castSucc)
                  = liftX d₁ d₂ (Px.field iL) := by
              show subtractionField Px Py ((Fin.castAdd d₂ iL).castSucc.castSucc) = _
              unfold subtractionField
              rw [show ((Fin.castAdd d₂ iL).castSucc.castSucc : Fin ((d₁+d₂)+1+1))
                    = Fin.castSucc (Fin.castSucc (Fin.castAdd d₂ iL)) from rfl,
                  Fin.snoc_castSucc, Fin.snoc_castSucc]
              show inputFields Px Py (Fin.castAdd d₂ iL) = _
              unfold inputFields
              rw [Fin.append_left]
            rw [h_fe]
            unfold liftX
            rw [MvPolynomial.eval₂_rename]
            congr 1
            funext j
            show T t ((injX d₁ d₂) j) = solX.trajectory t j
            exact T_injX t j
          rw [hFval]
          -- Cast Px.toPIVP.field (solX.trajectory t) iL to eval₂ form.
          show HasDerivAt (fun s => solX.trajectory s iL)
              ((Px.field iL).eval₂ (Rat.castHom ℝ) (solX.trajectory t)) t
          -- hDer_orig gives this directly, since Px.toPIVP.field = evalField.
          have : Px.toPIVP.field (solX.trajectory t) iL
              = (Px.field iL).eval₂ (Rat.castHom ℝ) (solX.trajectory t) := rfl
          rw [← this]
          exact hDer_orig
        · -- injY iR: inherit from solY.is_solution
          have hF : (fun s => T s ((Fin.natAdd d₁ iR).castSucc.castSucc))
              = fun s => solY.trajectory s iR := by
            funext s
            show T s ((Fin.natAdd d₁ iR).castSucc.castSucc) = _
            have := T_injY s iR
            show T s (injY d₁ d₂ iR) = solY.trajectory s iR
            exact this
          rw [hF]
          have hDer_orig := hasDerivAt_pi.mp (solY.is_solution t ht) iR
          have hFval :
              (subtractionPIVP Px Py).toPIVP.field (T t)
                  ((Fin.natAdd d₁ iR).castSucc.castSucc)
                = (Py.field iR).eval₂ (Rat.castHom ℝ) (solY.trajectory t) := by
            show ((subtractionPIVP Px Py).field ((Fin.natAdd d₁ iR).castSucc.castSucc)).eval₂
                  (Rat.castHom ℝ) (T t) = _
            have h_fe :
                (subtractionPIVP Px Py).field ((Fin.natAdd d₁ iR).castSucc.castSucc)
                  = liftY d₁ d₂ (Py.field iR) := by
              show subtractionField Px Py ((Fin.natAdd d₁ iR).castSucc.castSucc) = _
              unfold subtractionField
              rw [show ((Fin.natAdd d₁ iR).castSucc.castSucc : Fin ((d₁+d₂)+1+1))
                    = Fin.castSucc (Fin.castSucc (Fin.natAdd d₁ iR)) from rfl,
                  Fin.snoc_castSucc, Fin.snoc_castSucc]
              show inputFields Px Py (Fin.natAdd d₁ iR) = _
              unfold inputFields
              rw [Fin.append_right]
            rw [h_fe]
            unfold liftY
            rw [MvPolynomial.eval₂_rename]
            congr 1
            funext j
            show T t ((injY d₁ d₂) j) = solY.trajectory t j
            exact T_injY t j
          rw [hFval]
          show HasDerivAt (fun s => solY.trajectory s iR)
              ((Py.field iR).eval₂ (Rat.castHom ℝ) (solY.trajectory t)) t
          have : Py.toPIVP.field (solY.trajectory t) iR
              = (Py.field iR).eval₂ (Rat.castHom ℝ) (solY.trajectory t) := rfl
          rw [← this]
          exact hDer_orig
  -- Build the PIVP.Solution.
  let sol' : PIVP.Solution (subtractionPIVP Px Py).toPIVP :=
    { trajectory := T
      init_cond := T_init
      is_solution := T_is_solution }
  refine ⟨sol', zMod, ?_, ?_, ?_⟩
  · -- IsBounded: ‖T t‖ ≤ Mx + My + B_zr + B_z + 1 for t ≥ 0.
    refine ⟨Mx + My + B_zr + B_z + 1, by linarith, ?_⟩
    intro t ht
    -- Pi-norm is sup over components.
    rw [pi_norm_le_iff_of_nonneg (by linarith)]
    intro k
    rw [Real.norm_eq_abs]
    -- Case split.
    refine Fin.lastCases ?_ (fun i' => ?_) k
    · -- k = idxZ: |z t| = z t ≤ B_z.
      show |T t (Fin.last ((d₁+d₂)+1))| ≤ _
      rw [show (Fin.last ((d₁+d₂)+1) : Fin ((d₁+d₂)+1+1)) = idxZ d₁ d₂ from rfl,
          T_idxZ]
      have h_nn := hz_nn t ht
      have h_bd := hz_bd t ht
      rw [abs_of_nonneg h_nn]
      linarith
    · refine Fin.lastCases ?_ (fun i'' => ?_) i'
      · -- k = idxZR: |zr t| ≤ B_zr.
        show |T t ((Fin.last (d₁+d₂)).castSucc)| ≤ _
        rw [show ((Fin.last (d₁+d₂)).castSucc : Fin ((d₁+d₂)+1+1))
              = idxZR d₁ d₂ from rfl, T_idxZR]
        have h_nn := hzr_nn t ht
        have h_bd := hzr_bd t ht
        rw [abs_of_nonneg h_nn]
        linarith
      · refine Fin.addCases (fun iL => ?_) (fun iR => ?_) i''
        · -- k = injX iL: |solX.traj t iL| ≤ ‖solX.traj t‖ ≤ Mx.
          show |T t ((Fin.castAdd d₂ iL).castSucc.castSucc)| ≤ _
          rw [show ((Fin.castAdd d₂ iL).castSucc.castSucc : Fin ((d₁+d₂)+1+1))
                = injX d₁ d₂ iL from rfl, T_injX]
          have hx_coord : |solX.trajectory t iL| ≤ Mx := by
            have := norm_le_pi_norm (solX.trajectory t) iL
            rw [Real.norm_eq_abs] at this
            exact le_trans this (hMx_bd t ht)
          linarith
        · -- k = injY iR: |solY.traj t iR| ≤ My.
          show |T t ((Fin.natAdd d₁ iR).castSucc.castSucc)| ≤ _
          rw [show ((Fin.natAdd d₁ iR).castSucc.castSucc : Fin ((d₁+d₂)+1+1))
                = injY d₁ d₂ iR from rfl, T_injY]
          have hy_coord : |solY.trajectory t iR| ≤ My := by
            have := norm_le_pi_norm (solY.trajectory t) iR
            rw [Real.norm_eq_abs] at this
            exact le_trans this (hMy_bd t ht)
          linarith
  · -- Convergence at idxZ: from hz_conv.
    intro r t ht_gt
    show |sol'.trajectory t (idxZ d₁ d₂) - (α - β)| < Real.exp (-(r : ℝ))
    have h1 : sol'.trajectory t (idxZ d₁ d₂) = z t := T_idxZ t
    rw [h1, ← hγ_def]
    exact hz_conv r t ht_gt
  · -- Continuity: componentwise via continuous_pi.
    refine continuous_pi (fun k => ?_)
    refine Fin.lastCases ?_ (fun i' => ?_) k
    · -- idxZ
      have hF : (fun t : ℝ => sol'.trajectory t (Fin.last ((d₁+d₂)+1)))
          = z := by
        funext t; exact T_idxZ t
      rw [hF]; exact hz_cont
    · refine Fin.lastCases ?_ (fun i'' => ?_) i'
      · -- idxZR
        have hF : (fun t : ℝ => sol'.trajectory t ((Fin.last (d₁+d₂)).castSucc))
            = zr := by
          funext t; exact T_idxZR t
        rw [hF]; exact hzr_cont
      · refine Fin.addCases (fun iL => ?_) (fun iR => ?_) i''
        · -- injX iL
          have hF : (fun t : ℝ =>
              sol'.trajectory t ((Fin.castAdd d₂ iL).castSucc.castSucc))
              = fun t : ℝ => solX.trajectory t iL := by
            funext t; exact T_injX t iL
          rw [hF]
          exact (continuous_apply iL).comp _hXcont
        · -- injY iR
          have hF : (fun t : ℝ =>
              sol'.trajectory t ((Fin.natAdd d₁ iR).castSucc.castSucc))
              = fun t : ℝ => solY.trajectory t iR := by
            funext t; exact T_injY t iR
          rw [hF]
          exact (continuous_apply iR).comp _hYcont

/-- **DNA25 Lemma 8, subtraction gadget with CBTC + PCD.**

Given CBTC witnesses `btcX` for `α` and `btcY` for `β` (and their PCDs),
under the hypothesis `α > β ≥ 0` with both in `(0, 1)` (the DNA25 hypothesis
ensuring the reciprocal stage is well-conditioned), there exists a
CBTC+PCD witness for `α − β`, using the subtraction PIVP + PCD defined
above.

The PCD construction is fully certified; only the semantic solution +
convergence proof is scoped out (see `Ripple.Algebraic.relaxation_tracker_solution`
for the analogous single-stage proof). -/
theorem subtraction_cbtc_pcd {α β : ℝ} {d₁ d₂ : ℕ}
    (btcX : CertifiedBoundedTimeComputable d₁ α)
    (btcY : CertifiedBoundedTimeComputable d₂ β)
    (pcdX : PolyCRNDecomposition d₁ btcX.pivp)
    (pcdY : PolyCRNDecomposition d₂ btcY.pivp)
    (_hα_lo : 0 < α) (_hα_hi : α < 1)
    (_hβ_lo : 0 ≤ β) (_hβ_hi : β < 1)
    (_hαβ : β < α) :
    ∃ (d' : ℕ) (cbtc' : CertifiedBoundedTimeComputable d' (α - β))
      (_ : PolyCRNDecomposition d' cbtc'.pivp), True := by
  -- Build the joint-difference modulus via triangle inequality from the two
  -- individual CBTC convergences.  At precision level `r`, we use each
  -- sub-CBTC at level `r + 1`; then
  --   |x(t) − y(t) − (α − β)| ≤ |x(t) − α| + |y(t) − β|
  --                           < 2 · exp(-(r+1)) ≤ exp(-r)   (since 2 ≤ e).
  let diffMod : TimeModulus := fun r => max (btcX.modulus (r+1)) (btcY.modulus (r+1))
  have h_diff_conv : ∀ r : ℕ, ∀ t : ℝ, 0 ≤ t → t > diffMod r →
      |btcX.sol.trajectory t btcX.pivp.output
        - btcY.sol.trajectory t btcY.pivp.output - (α - β)|
      < Real.exp (-(r : ℝ)) := by
    intro r t _ht_nn ht_gt
    have htX : btcX.modulus (r+1) < t := lt_of_le_of_lt (le_max_left _ _) ht_gt
    have htY : btcY.modulus (r+1) < t := lt_of_le_of_lt (le_max_right _ _) ht_gt
    have hXc : |btcX.sol.trajectory t btcX.pivp.output - α|
                < Real.exp (-((r+1 : ℕ) : ℝ)) := btcX.convergence (r+1) t htX
    have hYc : |btcY.sol.trajectory t btcY.pivp.output - β|
                < Real.exp (-((r+1 : ℕ) : ℝ)) := btcY.convergence (r+1) t htY
    -- Triangle: the difference bound is ≤ sum of the two individual bounds.
    have h_triangle :
        |btcX.sol.trajectory t btcX.pivp.output
          - btcY.sol.trajectory t btcY.pivp.output - (α - β)|
        ≤ |btcX.sol.trajectory t btcX.pivp.output - α|
          + |btcY.sol.trajectory t btcY.pivp.output - β| := by
      have hrw :
          btcX.sol.trajectory t btcX.pivp.output
            - btcY.sol.trajectory t btcY.pivp.output - (α - β)
          = (btcX.sol.trajectory t btcX.pivp.output - α)
            - (btcY.sol.trajectory t btcY.pivp.output - β) := by ring
      rw [hrw, sub_eq_add_neg]
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_neg]
    -- Combine: 2 · exp(-(r+1)) ≤ exp(-r) because 2 ≤ e.
    have h_sum : |btcX.sol.trajectory t btcX.pivp.output - α|
                  + |btcY.sol.trajectory t btcY.pivp.output - β|
                  < 2 * Real.exp (-((r+1 : ℕ) : ℝ)) := by linarith
    have h_rewrite : 2 * Real.exp (-((r+1 : ℕ) : ℝ)) ≤ Real.exp (-(r : ℝ)) := by
      -- 2·e^{-(r+1)} = 2·e^{-r}·e^{-1} = (2/e)·e^{-r} ≤ e^{-r} since 2 ≤ e.
      have h_cancel :
          Real.exp (-((r + 1 : ℕ) : ℝ)) = Real.exp (-(r : ℝ)) * Real.exp (-1) := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      rw [h_cancel]
      have h_2_le_e : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_lt_exp (x := (1 : ℝ)) (by norm_num)
        linarith
      have h_exp_neg_1_le_half : Real.exp (-1) ≤ (1 : ℝ) / 2 := by
        rw [Real.exp_neg, show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by ring]
        exact (inv_anti₀ (by norm_num : (0 : ℝ) < 2) h_2_le_e)
      have hr_nn : 0 ≤ Real.exp (-(r : ℝ)) := (Real.exp_pos _).le
      calc 2 * (Real.exp (-(r : ℝ)) * Real.exp (-1))
          = Real.exp (-(r : ℝ)) * (2 * Real.exp (-1)) := by ring
        _ ≤ Real.exp (-(r : ℝ)) * (2 * (1 / 2)) :=
              mul_le_mul_of_nonneg_left
                (by linarith [h_exp_neg_1_le_half]) hr_nn
        _ = Real.exp (-(r : ℝ)) := by ring
    linarith [h_triangle, h_sum, h_rewrite]
  obtain ⟨sol', mod', hbd, hconv, hcont⟩ :=
    subtraction_lemma8_analytic btcX.pivp btcY.pivp btcX.sol btcY.sol
      btcX.bounded btcY.bounded
      btcX.trajectory_continuous btcY.trajectory_continuous
      diffMod h_diff_conv
      _hα_lo _hα_hi _hβ_lo _hβ_hi _hαβ
  refine ⟨(d₁ + d₂) + 1 + 1,
    { pivp := subtractionPIVP btcX.pivp btcY.pivp
      sol := sol'
      modulus := mod'
      bounded := hbd
      trajectory_continuous := hcont
      convergence := by
        intro r t ht
        show |sol'.trajectory t (subtractionPIVP btcX.pivp btcY.pivp).output
            - (α - β)| < _
        rw [subtractionPIVP_output]
        exact hconv r t ht },
    subtractionPCD pcdX pcdY, trivial⟩

end DualRail
end Ripple
