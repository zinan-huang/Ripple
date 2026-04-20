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

/-! ## Main theorem (statement)

Given two CBTC+PCD witnesses for `α, β ∈ (0, 1)` with `α > β ≥ 0`, the
DNA25 two-stage gadget defined above is itself a CBTC+PCD witness for
`α − β`.  The PCD non-negativity is fully proved; the analytic content —
existence of a bounded solution, trajectory continuity, and exponential
convergence of `z(t)` to `α − β` — is the DNA25 Lemma 8 statement, whose
Duhamel-style proof mirrors `Ripple.Algebraic.relaxation_tracker_convergence`
in `AddRationalPos.lean` but for a *coupled* two-stage non-linear ODE and is
considerably heavier.  We state the full assembly below and leave the
semantic-solution component as a single clearly-scoped `sorry`.
-/

/-- **DNA25 Lemma 8 analytic content (scoped `sorry`).**

Given two CBTC inputs `btcX` for `α`, `btcY` for `β`, under
`0 < α < 1`, `0 ≤ β < 1`, `β < α`, the subtraction gadget's combined
PIVP admits a semantic solution that is bounded, continuous, and whose
output species (`z`) converges exponentially to `α − β`.

Proof: Duhamel-style stability of the two coupled scalar stages
(`z_r` reciprocal, `z` subtraction), analogous to
`Ripple.Algebraic.relaxation_tracker_convergence` in `AddRationalPos.lean`
but with two stages and time-varying coefficients.  See [RTCRN2] Lemma 8.

Leaving this as a single clearly-scoped `sorry`: the non-analytic, structural
core of the gadget (PIVP, PCD, field_eq, non-negativity of coefficients,
output index assignment) is fully proved above.  Downstream consumers can
build CBTC+PCD witnesses for `α − β` assuming this analytic content. -/
-- TODO (per [RTCRN2] / Dad, 2026-04-20): when filling this sorry, loosen
-- the hypotheses.  Lemma 8 only requires `|x(t) − y(t) − (α−β)|` to
-- converge, not `x(t)` and `y(t)` individually.  Reformulate the analytic
-- statement around the CBTC witnesses' difference trajectory only, plus
-- boundedness of each input — drop the per-input modulus requirement.
theorem subtraction_lemma8_analytic {α β : ℝ} {d₁ d₂ : ℕ}
    (btcX : CertifiedBoundedTimeComputable d₁ α)
    (btcY : CertifiedBoundedTimeComputable d₂ β)
    (_hα_lo : 0 < α) (_hα_hi : α < 1)
    (_hβ_lo : 0 ≤ β) (_hβ_hi : β < 1)
    (_hαβ : β < α) :
    ∃ (sol' : PIVP.Solution (subtractionPIVP btcX.pivp btcY.pivp).toPIVP)
      (modulus' : TimeModulus),
      (subtractionPIVP btcX.pivp btcY.pivp).toPIVP.IsBounded sol'.trajectory ∧
      (∀ r : ℕ, ∀ t : ℝ, t > modulus' r →
        |sol'.trajectory t (idxZ d₁ d₂) - (α - β)| < Real.exp (-(r : ℝ))) ∧
      Continuous sol'.trajectory := by
  sorry

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
  -- Analytic content (boundedness + continuity + convergence) deferred to a
  -- clearly-scoped `sorry`; see `subtraction_lemma8_analytic` below for the
  -- precise statement.  The PIVP + PCD are constructed fully above.
  obtain ⟨sol', mod', hbd, hconv, hcont⟩ :=
    subtraction_lemma8_analytic btcX btcY _hα_lo _hα_hi _hβ_lo _hβ_hi _hαβ
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
