import Ripple.BoundedUniversality.BGP.SelectorGates
import Ripple.BoundedUniversality.BGP.BernsteinSeparator

/-!
Ripple.BoundedUniversality.BGP.SelectorAtoms
------------------------

Concrete Bernstein-backed atomic selectors on one coordinate, with explicit
degree-indexed error schedules.

The checked-in `GateSelectorAtoms` interface uses a working-domain range
contract.  The Bernstein separator in `BernsteinSeparator.lean` proves exactly
that statement on a rational coordinate slab, so the concrete slab atoms below
now instantiate the gate interface directly.
-/

namespace Ripple.BoundedUniversality.BGP

open BigOperators
open Polynomial

noncomputable section

/-! ## Degree-indexed atom error -/

/-- Atom error used by the selector layer at Bernstein degree/schedule index `N`. -/
def selectorAtomEps (N : ℕ) : ℝ :=
  1 / ((N : ℝ) + 1)

theorem selectorAtomEps_pos (N : ℕ) : 0 < selectorAtomEps N := by
  unfold selectorAtomEps
  positivity

theorem selectorAtomEps_nonneg (N : ℕ) : 0 ≤ selectorAtomEps N :=
  (selectorAtomEps_pos N).le

/-- Given any positive target, some degree/schedule index makes `selectorAtomEps` small enough. -/
theorem selectorAtomEps_eventually_below {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, selectorAtomEps N ≤ ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, le_of_lt ?_⟩
  have hden : 0 < (N : ℝ) + 1 := by positivity
  have hmul : 1 < ε * ((N : ℝ) + 1) := by
    have hN' : 1 / ε < (N : ℝ) + 1 := by linarith
    have := mul_lt_mul_of_pos_left hN' hε
    field_simp [hε.ne'] at this
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  unfold selectorAtomEps
  exact (div_lt_iff₀ hden).mpr hmul

/--
Selector-budget schedule: any nonnegative linear prefactor can be absorbed by
choosing a sufficiently accurate atom.
-/
theorem selectorAtom_budget_schedule_exists
    {scale ε : ℝ} (hscale : 0 ≤ scale) (hε : 0 < ε) :
    ∃ N : ℕ, scale * selectorAtomEps N ≤ ε := by
  rcases eq_or_lt_of_le hscale with hscale0 | hscale_pos
  · refine ⟨0, ?_⟩
    rw [← hscale0, zero_mul]
    exact hε.le
  · obtain ⟨N, hN⟩ := selectorAtomEps_eventually_below
      (ε := ε / scale) (by positivity)
    refine ⟨N, ?_⟩
    have := mul_le_mul_of_nonneg_left hN hscale
    field_simp [ne_of_gt hscale_pos] at this
    simpa [mul_comm, mul_left_comm, mul_assoc] using this

/-! ## Lifting univariate separators to a selected coordinate -/

/-- Substitute a rational univariate polynomial into one multivariate coordinate. -/
def coordinatePolynomial {d : ℕ} (coord : Fin d) (H : Polynomial ℚ) : Poly4 d :=
  Polynomial.aeval (MvPolynomial.X coord) H

theorem evalPoly4_coordinatePolynomial {d : ℕ} (coord : Fin d)
    (H : Polynomial ℚ) (x : Fin d → ℝ) :
    evalPoly4 x (coordinatePolynomial coord H) = evalR H (x coord) := by
  rw [show evalR H (x coord) =
      Polynomial.eval₂ (algebraMap ℚ ℝ) (x coord) H by
        simp [evalR, Polynomial.eval₂_eq_eval_map]]
  induction H using Polynomial.induction_on' with
  | add p q hp hq =>
      have hp' :
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) x
              ((Polynomial.aeval (MvPolynomial.X coord)) p) =
            Polynomial.eval₂ (algebraMap ℚ ℝ) (x coord) p := by
        simpa [evalPoly4, coordinatePolynomial] using hp
      have hq' :
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) x
              ((Polynomial.aeval (MvPolynomial.X coord)) q) =
            Polynomial.eval₂ (algebraMap ℚ ℝ) (x coord) q := by
        simpa [evalPoly4, coordinatePolynomial] using hq
      simp [evalPoly4, coordinatePolynomial, hp', hq']
  | monomial n a =>
      simp [evalPoly4, coordinatePolynomial]

/-! ## Slab-range finite coordinate atoms -/

/--
Finite-level atom data on a rational coordinate slab.

This is the concrete range statement supplied by
`rational_bernstein_separator`: range is proved on `|x coord| <= C`, not
globally on all real inputs.
-/
structure SlabAtomicSelectorData (d : ℕ) (A : Type) where
  poly : A → Poly4 d
  err : ℝ
  err_nonneg : 0 ≤ err
  coord : Fin d
  C : ℚ
  C_pos : 0 < C
  rho : ℚ
  rho_pos : 0 < rho
  rho_le_quarter : rho ≤ 1 / 4
  code : A → ℝ
  range_on_slab :
    ∀ a x, |x coord| ≤ (C : ℝ) →
      0 ≤ evalPoly4 x (poly a) ∧ evalPoly4 x (poly a) ≤ 1
  on_tube :
    ∀ a x, |x coord - code a| ≤ (rho : ℝ) →
      1 - err ≤ evalPoly4 x (poly a)
  off_tube :
    ∀ a b x, a ≠ b → |x coord - code b| ≤ (rho : ℝ) →
      evalPoly4 x (poly a) ≤ err

namespace SlabAtomicSelectorData

/-- A slab atom as a checked-in atom with its own coordinate-slab working domain. -/
def toAtomicSelectorData {d : ℕ} {A : Type} (S : SlabAtomicSelectorData d A) :
    AtomicSelectorData d A where
  poly := S.poly
  err := S.err
  err_nonneg := S.err_nonneg
  domain := fun x => |x S.coord| ≤ (S.C : ℝ)
  range := S.range_on_slab

end SlabAtomicSelectorData

private def singletonReal (x : ℝ) : Finset ℝ :=
  {x}

private def otherCodes {A : Type} [Fintype A] [DecidableEq A]
    (code : A → ℝ) (a : A) : Finset ℝ :=
  (Finset.univ.erase a).image code

private def finiteCoordinateAtomPoly
    {A : Type} [Fintype A] [DecidableEq A]
    (code : A → ℝ) (C rho eta : ℚ) (a : A) : Polynomial ℚ :=
  rationalBernsteinSeparatorPoly C eta (singletonReal (code a)) rho

private theorem finite_atom_separator_poly_spec
    {A : Type} [Fintype A] [DecidableEq A]
    (code : A → ℝ)
    (hgap : ∀ a b, a ≠ b → 1 ≤ |code a - code b|)
    (C : ℚ) (hC : 0 < C)
    (hCbound : ∀ a, |code a| + 1 ≤ (C : ℝ))
    (rho eta : ℚ) (hrho : 0 < rho) (hrho4 : rho ≤ 1 / 4) (heta : 0 < eta)
    (a : A) :
    (∀ x : ℝ, |x| ≤ (C : ℝ) →
        0 ≤ evalR (finiteCoordinateAtomPoly code C rho eta a) x ∧
          evalR (finiteCoordinateAtomPoly code C rho eta a) x ≤ 1) ∧
      (∀ x : ℝ, |x - code a| ≤ (rho : ℝ) →
        1 - (eta : ℝ) ≤ evalR (finiteCoordinateAtomPoly code C rho eta a) x) ∧
      (∀ b : A, b ≠ a → ∀ x : ℝ, |x - code b| ≤ (rho : ℝ) →
        evalR (finiteCoordinateAtomPoly code C rho eta a) x ≤ (eta : ℝ)) := by
  classical
  let ones : Finset ℝ := singletonReal (code a)
  let zeros : Finset ℝ := otherCodes code a
  have hsep :
      ∀ u ∈ ones, ∀ v ∈ zeros, 1 ≤ |u - v| := by
    intro u hu v hv
    have hu' : u = code a := by simpa [ones, singletonReal] using hu
    rcases Finset.mem_image.mp hv with ⟨b, hb, rfl⟩
    have hba : b ≠ a := by
      exact (Finset.mem_erase.mp hb).1
    rw [hu']
    simpa [abs_sub_comm] using hgap b a hba
  have hin :
      ∀ v ∈ ones ∪ zeros, |v| + 1 ≤ (C : ℝ) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvone | hvzero
    · have hv' : v = code a := by simpa [ones, singletonReal] using hvone
      simpa [hv'] using hCbound a
    · rcases Finset.mem_image.mp hvzero with ⟨b, _hb, rfl⟩
      exact hCbound b
  have hspec :=
    rationalBernsteinSeparatorPoly_spec C hC ones zeros hsep hin rho eta hrho hrho4 heta
  change
    (∀ x : ℝ, |x| ≤ (C : ℝ) →
        0 ≤ evalR (rationalBernsteinSeparatorPoly C eta ones rho) x ∧
          evalR (rationalBernsteinSeparatorPoly C eta ones rho) x ≤ 1) ∧
      (∀ x : ℝ, |x - code a| ≤ (rho : ℝ) →
        1 - (eta : ℝ) ≤ evalR (rationalBernsteinSeparatorPoly C eta ones rho) x) ∧
      (∀ b : A, b ≠ a → ∀ x : ℝ, |x - code b| ≤ (rho : ℝ) →
        evalR (rationalBernsteinSeparatorPoly C eta ones rho) x ≤ (eta : ℝ))
  refine ⟨hspec.1, ?_, ?_⟩
  · intro x hx
    exact hspec.2.1 (code a) (by simp [ones, singletonReal]) x hx
  · intro b hba x hx
    have hb : code b ∈ zeros := by
      exact Finset.mem_image.mpr ⟨b, by simpa using hba, rfl⟩
    exact hspec.2.2 (code b) hb x hx

private theorem finite_atom_separator_exists
    {A : Type} [Fintype A] [DecidableEq A]
    (code : A → ℝ)
    (hgap : ∀ a b, a ≠ b → 1 ≤ |code a - code b|)
    (C : ℚ) (hC : 0 < C)
    (hCbound : ∀ a, |code a| + 1 ≤ (C : ℝ))
    (rho eta : ℚ) (hrho : 0 < rho) (hrho4 : rho ≤ 1 / 4) (heta : 0 < eta)
    (a : A) :
    ∃ H : Polynomial ℚ,
      (∀ x : ℝ, |x| ≤ (C : ℝ) → 0 ≤ evalR H x ∧ evalR H x ≤ 1) ∧
      (∀ x : ℝ, |x - code a| ≤ (rho : ℝ) → 1 - (eta : ℝ) ≤ evalR H x) ∧
      (∀ b : A, b ≠ a → ∀ x : ℝ, |x - code b| ≤ (rho : ℝ) →
        evalR H x ≤ (eta : ℝ)) := by
  classical
  let ones : Finset ℝ := singletonReal (code a)
  let zeros : Finset ℝ := otherCodes code a
  have hsep :
      ∀ u ∈ ones, ∀ v ∈ zeros, 1 ≤ |u - v| := by
    intro u hu v hv
    have hu' : u = code a := by simpa [ones, singletonReal] using hu
    rcases Finset.mem_image.mp hv with ⟨b, hb, rfl⟩
    have hba : b ≠ a := by
      exact (Finset.mem_erase.mp hb).1
    rw [hu']
    simpa [abs_sub_comm] using hgap b a hba
  have hin :
      ∀ v ∈ ones ∪ zeros, |v| + 1 ≤ (C : ℝ) := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvone | hvzero
    · have hv' : v = code a := by simpa [ones, singletonReal] using hvone
      simpa [hv'] using hCbound a
    · rcases Finset.mem_image.mp hvzero with ⟨b, _hb, rfl⟩
      exact hCbound b
  obtain ⟨H, hrange, hon, hoff⟩ :=
    rational_bernstein_separator C hC ones zeros hsep hin rho eta hrho hrho4 heta
  refine ⟨H, hrange, ?_, ?_⟩
  · intro x hx
    exact hon (code a) (by simp [ones, singletonReal]) x hx
  · intro b hba x hx
    have hb : code b ∈ zeros := by
      exact Finset.mem_image.mpr ⟨b, by simpa using hba, rfl⟩
    exact hoff (code b) hb x hx

/--
Concrete finite-level coordinate atoms from `rational_bernstein_separator`.

The finite labels are separated by margin `1` in the selected coordinate.
Control labels and flag labels are direct instances of this construction after
choosing their finite value sets.
-/
def finiteCoordinateAtoms
    {d : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (coord : Fin d) (code : A → ℝ)
    (hgap : ∀ a b, a ≠ b → 1 ≤ |code a - code b|)
    (C : ℚ) (hC : 0 < C)
    (hCbound : ∀ a, |code a| + 1 ≤ (C : ℝ))
    (rho eta : ℚ) (hrho : 0 < rho) (hrho4 : rho ≤ 1 / 4) (heta : 0 < eta) :
    SlabAtomicSelectorData d A where
  poly := fun a =>
    coordinatePolynomial coord
      (finiteCoordinateAtomPoly code C rho eta a)
  err := (eta : ℝ)
  err_nonneg := by exact_mod_cast heta.le
  coord := coord
  C := C
  C_pos := hC
  rho := rho
  rho_pos := hrho
  rho_le_quarter := hrho4
  code := code
  range_on_slab := by
    intro a x hx
    rw [evalPoly4_coordinatePolynomial]
    exact (finite_atom_separator_poly_spec code hgap C hC hCbound rho eta hrho hrho4 heta a).1
        (x coord) hx
  on_tube := by
    intro a x hx
    rw [evalPoly4_coordinatePolynomial]
    exact (finite_atom_separator_poly_spec code hgap C hC hCbound rho eta hrho hrho4 heta a).2.1
        (x coord) hx
  off_tube := by
    intro a b x hba hx
    rw [evalPoly4_coordinatePolynomial]
    exact (finite_atom_separator_poly_spec code hgap C hC hCbound rho eta hrho hrho4 heta a).2.2
        b hba.symm (x coord) hx

/-- Public expansion of the deterministic polynomial used by finite coordinate atoms. -/
theorem finiteCoordinateAtoms_poly_eq
    {d : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (coord : Fin d) (code : A → ℝ)
    (hgap : ∀ a b, a ≠ b → 1 ≤ |code a - code b|)
    (C : ℚ) (hC : 0 < C)
    (hCbound : ∀ a, |code a| + 1 ≤ (C : ℝ))
    (rho eta : ℚ) (hrho : 0 < rho) (hrho4 : rho ≤ 1 / 4) (heta : 0 < eta)
    (a : A) :
    (finiteCoordinateAtoms coord code hgap C hC hCbound rho eta hrho hrho4 heta).poly a =
      coordinatePolynomial coord
        (rationalBernsteinSeparatorPoly C eta ({code a} : Finset ℝ) rho) := by
  simp [finiteCoordinateAtoms, finiteCoordinateAtomPoly, singletonReal]

/-! ## Gate sharpness and budget adapters -/

/-- Direct Bernstein/slab-backed gate selector atom package. -/
def gateSelectorAtomsBernstein
    {d : ℕ}
    (control : SlabAtomicSelectorData d ℤ)
    (left : SlabAtomicSelectorData d (Option (Fin 2)))
    (right : SlabAtomicSelectorData d (Option (Fin 2))) :
    GateSelectorAtoms d where
  control := control.toAtomicSelectorData
  left := left.toAtomicSelectorData
  right := right.toAtomicSelectorData

theorem gateSelectorAtomsBernstein_inWorkingDomain
    {d : ℕ}
    (control : SlabAtomicSelectorData d ℤ)
    (left : SlabAtomicSelectorData d (Option (Fin 2)))
    (right : SlabAtomicSelectorData d (Option (Fin 2)))
    {x : Fin d → ℝ}
    (hcontrol : |x control.coord| ≤ (control.C : ℝ))
    (hleft : |x left.coord| ≤ (left.C : ℝ))
    (hright : |x right.coord| ≤ (right.C : ℝ)) :
    (gateSelectorAtomsBernstein control left right).inWorkingDomain x :=
  ⟨hcontrol, hleft, hright⟩

/--
Machine-generic sharpness adapter from three slab atom families to the checked
`GateAtomSharpness` proposition.

The hypotheses are exactly the tube-to-coordinate facts that an encoding layer
must provide: the selected view's codes are within the atom radii, while every
different view is within the corresponding wrong-label tube.
-/
theorem gateAtomSharpness_of_slab_atoms
    {d : ℕ} {V : Type} (spec : GateViewSpec V)
    (control : SlabAtomicSelectorData d ℤ)
    (left : SlabAtomicSelectorData d (Option (Fin 2)))
    (right : SlabAtomicSelectorData d (Option (Fin 2)))
    {x : Fin d → ℝ} {vstar : V}
    (hctrl_on : |x control.coord - control.code (spec.q vstar)| ≤ (control.rho : ℝ))
    (hleft_on : |x left.coord - left.code (spec.leftTop vstar)| ≤ (left.rho : ℝ))
    (hright_on : |x right.coord - right.code (spec.rightTop vstar)| ≤ (right.rho : ℝ)) :
    GateAtomSharpness spec (gateSelectorAtomsBernstein control left right) x vstar := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact control.on_tube (spec.q vstar) x hctrl_on
  · exact left.on_tube (spec.leftTop vstar) x hleft_on
  · exact right.on_tube (spec.rightTop vstar) x hright_on
  · intro v hv
    exact control.off_tube (spec.q v) (spec.q vstar) x hv hctrl_on
  · intro v hv
    exact left.off_tube (spec.leftTop v) (spec.leftTop vstar) x hv hleft_on
  · intro v hv
    exact right.off_tube (spec.rightTop v) (spec.rightTop vstar) x hv hright_on

/-! ## N-atom slab assembly -/

/-- Assemble an `n`-family of slab atoms into the `n`-atom gate selector. -/
def gateSelectorAtomsBernsteinN {d n : ℕ}
    (atomData : Fin n → SlabAtomicSelectorData d ℤ) : GateSelectorAtomsN d n where
  atom := fun k => (atomData k).toAtomicSelectorData

/-- `GateAtomSharpnessN` from per-component slab tube facts. -/
theorem gateAtomSharpnessN_of_slab_atoms {d n : ℕ} {V : Type}
    (spec : GateViewSpecN V n)
    (atomData : Fin n → SlabAtomicSelectorData d ℤ)
    {x : Fin d → ℝ} {vstar : V}
    (hon : ∀ k, |x (atomData k).coord -
      (atomData k).code (spec.comp k vstar)| ≤ ((atomData k).rho : ℝ)) :
    GateAtomSharpnessN spec (gateSelectorAtomsBernsteinN atomData) x vstar where
  on := fun k => (atomData k).on_tube (spec.comp k vstar) x (hon k)
  off := fun k v hkv =>
    (atomData k).off_tube (spec.comp k v) (spec.comp k vstar) x hkv (hon k)

/-- `inWorkingDomain` for the assembled `n`-atom family from per-coordinate
slab bounds. -/
theorem gateSelectorAtomsBernsteinN_inWorkingDomain {d n : ℕ}
    (atomData : Fin n → SlabAtomicSelectorData d ℤ) {x : Fin d → ℝ}
    (hdom : ∀ k, |x (atomData k).coord| ≤ ((atomData k).C : ℝ)) :
    (gateSelectorAtomsBernsteinN atomData).inWorkingDomain x :=
  fun k => hdom k

/-! ## Generic membership-driven coordinate atoms (point or interval) -/

/--
A single-coordinate atom whose on/off behaviour is governed by an abstract
membership predicate `mem a x` ("x sits at code `a`").  Both the point-tube
slab atoms and the interval atoms are instances; bundling them through this
interface lets a gate mix point atoms (finite control coordinates) and
interval atoms (stack-top coordinates) in one `GateSelectorAtomsN`.
-/
structure CoordAtomData (d : ℕ) (A : Type) where
  poly : A → Poly4 d
  err : ℝ
  err_nonneg : 0 ≤ err
  domain : (Fin d → ℝ) → Prop
  mem : A → (Fin d → ℝ) → Prop
  range : ∀ a x, domain x → 0 ≤ evalPoly4 x (poly a) ∧ evalPoly4 x (poly a) ≤ 1
  on_mem : ∀ a x, domain x → mem a x → 1 - err ≤ evalPoly4 x (poly a)
  off_mem : ∀ a b x, a ≠ b → domain x → mem b x → evalPoly4 x (poly a) ≤ err

namespace CoordAtomData

/-- Forget the membership data, keeping the checked-in atom interface. -/
def toAtomicSelectorData {d : ℕ} {A : Type} (S : CoordAtomData d A) :
    AtomicSelectorData d A where
  poly := S.poly
  err := S.err
  err_nonneg := S.err_nonneg
  domain := S.domain
  range := S.range

end CoordAtomData

/-- Assemble an `n`-atom family from per-coordinate membership atoms. -/
def gateSelectorAtomsCoordN {d n : ℕ}
    (atomData : Fin n → CoordAtomData d ℤ) : GateSelectorAtomsN d n where
  atom := fun k => (atomData k).toAtomicSelectorData

/-- `GateAtomSharpnessN` from per-component membership facts at the true view. -/
theorem gateAtomSharpnessN_of_coord_atoms {d n : ℕ} {V : Type}
    (spec : GateViewSpecN V n)
    (atomData : Fin n → CoordAtomData d ℤ)
    {x : Fin d → ℝ} {vstar : V}
    (hdom : ∀ k, (atomData k).domain x)
    (hon : ∀ k, (atomData k).mem (spec.comp k vstar) x) :
    GateAtomSharpnessN spec (gateSelectorAtomsCoordN atomData) x vstar where
  on := fun k => (atomData k).on_mem (spec.comp k vstar) x (hdom k) (hon k)
  off := fun k v hkv =>
    (atomData k).off_mem (spec.comp k v) (spec.comp k vstar) x hkv (hdom k) (hon k)

/-- `inWorkingDomain` for the membership-atom family. -/
theorem gateSelectorAtomsCoordN_inWorkingDomain {d n : ℕ}
    (atomData : Fin n → CoordAtomData d ℤ) {x : Fin d → ℝ}
    (hdom : ∀ k, (atomData k).domain x) :
    (gateSelectorAtomsCoordN atomData).inWorkingDomain x :=
  hdom

/-- A point-tube slab atom is a membership atom (membership = in the tube). -/
def SlabAtomicSelectorData.toCoordAtomData {d : ℕ} {A : Type}
    (S : SlabAtomicSelectorData d A) : CoordAtomData d A where
  poly := S.poly
  err := S.err
  err_nonneg := S.err_nonneg
  domain := fun x => |x S.coord| ≤ (S.C : ℝ)
  mem := fun a x => |x S.coord - S.code a| ≤ (S.rho : ℝ)
  range := S.range_on_slab
  on_mem := fun a x _ hmem => S.on_tube a x hmem
  off_mem := fun a b x hab _ hmem => S.off_tube a b x hab hmem

theorem evalPoly4_zero {d : ℕ} (x : Fin d → ℝ) :
    evalPoly4 x (0 : Poly4 d) = 0 := by
  simp [evalPoly4]

open Classical in
/-- Relabel a membership atom along an injective code map `f : A → B`.  Codes
outside the image of `f` get the zero polynomial (range `[0,1]`, never on). -/
noncomputable def CoordAtomData.relabel {d : ℕ} {A B : Type}
    (S : CoordAtomData d A) (f : A → B) (hf : Function.Injective f) :
    CoordAtomData d B where
  poly := fun c => if h : ∃ a, f a = c then S.poly h.choose else 0
  err := S.err
  err_nonneg := S.err_nonneg
  domain := S.domain
  mem := fun c x => ∃ a, f a = c ∧ S.mem a x
  range := by
    intro c x hx
    by_cases h : ∃ a, f a = c
    · simp only [dif_pos h]; exact S.range _ x hx
    · simp only [dif_neg h, evalPoly4_zero]; constructor <;> norm_num
  on_mem := by
    intro c x hdom hmem
    obtain ⟨a, hfa, hma⟩ := hmem
    have hex : ∃ a, f a = c := ⟨a, hfa⟩
    simp only [dif_pos hex]
    have hchoose : hex.choose = a := hf (hex.choose_spec.trans hfa.symm)
    rw [hchoose]; exact S.on_mem a x hdom hma
  off_mem := by
    intro c c' x hcc hdom hmem'
    obtain ⟨a', hfa', hma'⟩ := hmem'
    by_cases h : ∃ a, f a = c
    · simp only [dif_pos h]
      have hne : h.choose ≠ a' := by
        intro heq
        apply hcc
        rw [← h.choose_spec, heq, hfa']
      exact S.off_mem h.choose a' x hne hdom hma'
    · simp only [dif_neg h, evalPoly4_zero]; exact S.err_nonneg

/-! ## Interval atoms as membership atoms -/

/--
Specification of an interval-atom family on one coordinate: code `a` occupies
`[lo a, hi a]`, distinct codes are `gap`-separated, the working slab is
`|x coord| ≤ C`, and the atom accuracy is `eta`.
-/
structure IntervalAtomSpec (d : ℕ) (A : Type) where
  coord : Fin d
  C : ℚ
  C_pos : 0 < C
  lo : A → ℝ
  hi : A → ℝ
  gap : ℝ
  gap_pos : 0 < gap
  sep : ∀ a b : A, a ≠ b → hi a + gap ≤ lo b ∨ hi b + gap ≤ lo a
  eta : ℚ
  eta_pos : 0 < eta

namespace IntervalAtomSpec

/-- The interval atom for code `a`, chosen from
`rational_bernstein_interval_atom_family`. -/
noncomputable def chosen {d : ℕ} {A : Type} (S : IntervalAtomSpec d A) (a : A) :
    Polynomial ℚ :=
  rationalBernsteinIntervalAtomFamilyPoly S.C S.lo S.hi S.gap S.eta a

theorem chosen_spec {d : ℕ} {A : Type} (S : IntervalAtomSpec d A) (a : A) :
    (∀ x : ℝ, |x| ≤ (S.C : ℝ) → 0 ≤ evalR (S.chosen a) x ∧ evalR (S.chosen a) x ≤ 1) ∧
    (∀ x : ℝ, |x| ≤ (S.C : ℝ) → S.lo a ≤ x → x ≤ S.hi a →
      1 - 2 * (S.eta : ℝ) ≤ evalR (S.chosen a) x) ∧
    (∀ b : A, b ≠ a → ∀ x : ℝ, |x| ≤ (S.C : ℝ) → S.lo b ≤ x → x ≤ S.hi b →
      evalR (S.chosen a) x ≤ (S.eta : ℝ)) :=
  rationalBernsteinIntervalAtomFamilyPoly_spec
    S.C S.C_pos S.lo S.hi S.gap S.gap_pos S.sep S.eta S.eta_pos a

/-- An interval-atom family as a membership atom (membership = in `[lo a, hi a]`). -/
noncomputable def toCoordAtomData {d : ℕ} {A : Type}
    (S : IntervalAtomSpec d A) : CoordAtomData d A where
  poly := fun a => coordinatePolynomial S.coord (S.chosen a)
  err := 2 * (S.eta : ℝ)
  err_nonneg := by
    have : (0 : ℝ) ≤ (S.eta : ℝ) := by exact_mod_cast S.eta_pos.le
    positivity
  domain := fun x => |x S.coord| ≤ (S.C : ℝ)
  mem := fun a x => S.lo a ≤ x S.coord ∧ x S.coord ≤ S.hi a
  range := by
    intro a x hx
    rw [evalPoly4_coordinatePolynomial]
    exact (S.chosen_spec a).1 (x S.coord) hx
  on_mem := by
    intro a x hdom hmem
    rw [evalPoly4_coordinatePolynomial]
    exact (S.chosen_spec a).2.1 (x S.coord) hdom hmem.1 hmem.2
  off_mem := by
    intro a b x hab hdom hmem
    rw [evalPoly4_coordinatePolynomial]
    have hpos : (0 : ℝ) ≤ (S.eta : ℝ) := by exact_mod_cast S.eta_pos.le
    have hle := (S.chosen_spec a).2.2 b (fun h => hab h.symm) (x S.coord) hdom hmem.1 hmem.2
    linarith

/-- Public expansion of the deterministic polynomial used by interval atoms. -/
theorem toCoordAtomData_poly_eq {d : ℕ} {A : Type}
    (S : IntervalAtomSpec d A) (a : A) :
    (S.toCoordAtomData).poly a =
      coordinatePolynomial S.coord
        (rationalBernsteinIntervalAtomFamilyPoly S.C S.lo S.hi S.gap S.eta a) := by
  simp [toCoordAtomData, chosen]

end IntervalAtomSpec


/--
Closed-form selector coefficient when all three atom errors are bounded by the
same `δ`.
-/
theorem selector_budget_of_uniform_atom_error
    {V : Type} [Fintype V] {δ spread ε : ℝ}
    (_hδ : 0 ≤ δ) (_hspread : 0 ≤ spread)
    (hbudget : (6 + 2 * offViewCount V) * δ * spread ≤ ε) :
    selectorEpsTotal (V := V) (3 * δ) δ ((3 + offViewCount V) * δ) spread ≤ ε := by
  unfold selectorEpsTotal selectorReassemblyCoeff
  nlinarith

/--
Existence of a degree schedule sufficient for the selector error budget with
uniform atom error `selectorAtomEps N`.
-/
theorem selector_budget_schedule_exists
    {V : Type} [Fintype V] {spread ε : ℝ}
    (hspread : 0 ≤ spread) (hε : 0 < ε) :
    ∃ N : ℕ,
      selectorEpsTotal (V := V)
        (3 * selectorAtomEps N)
        (selectorAtomEps N)
        ((3 + offViewCount V) * selectorAtomEps N)
        spread ≤ ε := by
  have hscale : 0 ≤ (6 + 2 * offViewCount V) * spread := by
    have hoff : 0 ≤ offViewCount V := by simp [offViewCount]
    nlinarith
  obtain ⟨N, hN⟩ := selectorAtom_budget_schedule_exists
    (scale := (6 + 2 * offViewCount V) * spread) (ε := ε) hscale hε
  refine ⟨N, ?_⟩
  apply selector_budget_of_uniform_atom_error
  · exact selectorAtomEps_nonneg N
  · exact hspread
  · simpa [mul_comm, mul_left_comm, mul_assoc] using hN

/-- Stable AN1/N4 handle for the direct Bernstein-backed gate atom package. -/
theorem N4_gateSelectorAtomsBernstein_sharpness
    {d : ℕ} {V : Type} (spec : GateViewSpec V)
    (control : SlabAtomicSelectorData d ℤ)
    (left : SlabAtomicSelectorData d (Option (Fin 2)))
    (right : SlabAtomicSelectorData d (Option (Fin 2)))
    {x : Fin d → ℝ} {vstar : V}
    (hctrl_on : |x control.coord - control.code (spec.q vstar)| ≤ (control.rho : ℝ))
    (hleft_on : |x left.coord - left.code (spec.leftTop vstar)| ≤ (left.rho : ℝ))
    (hright_on : |x right.coord - right.code (spec.rightTop vstar)| ≤ (right.rho : ℝ)) :
    GateAtomSharpness spec (gateSelectorAtomsBernstein control left right) x vstar :=
  gateAtomSharpness_of_slab_atoms spec control left right hctrl_on hleft_on hright_on

/-- Stable AN1/N4 handle for the direct Bernstein-backed working domain. -/
theorem N4_gateSelectorAtomsBernstein_inWorkingDomain
    {d : ℕ}
    (control : SlabAtomicSelectorData d ℤ)
    (left : SlabAtomicSelectorData d (Option (Fin 2)))
    (right : SlabAtomicSelectorData d (Option (Fin 2)))
    {x : Fin d → ℝ}
    (hcontrol : |x control.coord| ≤ (control.C : ℝ))
    (hleft : |x left.coord| ≤ (left.C : ℝ))
    (hright : |x right.coord| ≤ (right.C : ℝ)) :
    (gateSelectorAtomsBernstein control left right).inWorkingDomain x :=
  gateSelectorAtomsBernstein_inWorkingDomain control left right hcontrol hleft hright

/-- Budget clause restated against the direct Bernstein-backed gate atom package. -/
theorem N4_gateSelectorAtomsBernstein_budget_of_uniform_error
    {d : ℕ} {V : Type} [Fintype V]
    (control : SlabAtomicSelectorData d ℤ)
    (left : SlabAtomicSelectorData d (Option (Fin 2)))
    (right : SlabAtomicSelectorData d (Option (Fin 2)))
    {δ spread ε : ℝ}
    (hcontrol : control.err = δ)
    (hleft : left.err = δ)
    (hright : right.err = δ)
    (hδ : 0 ≤ δ) (hspread : 0 ≤ spread)
    (hbudget : (6 + 2 * offViewCount V) * δ * spread ≤ ε) :
    selectorEpsTotal (V := V)
        (gateSelectorAtomsBernstein control left right).errSel
        (gateSelectorAtomsBernstein control left right).errOff
        ((gateSelectorAtomsBernstein control left right).errSum V)
        spread ≤ ε := by
  have herrSel :
      (gateSelectorAtomsBernstein control left right).errSel = 3 * δ := by
    change control.err + left.err + right.err = 3 * δ
    rw [hcontrol, hleft, hright]
    ring
  have herrOff :
      (gateSelectorAtomsBernstein control left right).errOff = δ := by
    change max control.err (max left.err right.err) = δ
    rw [hcontrol, hleft, hright]
    simp
  have herrSum :
      (gateSelectorAtomsBernstein control left right).errSum V =
        (3 + offViewCount V) * δ := by
    simp [GateSelectorAtoms.errSum, herrSel, herrOff]
    ring
  rw [herrSel, herrOff, herrSum]
  exact selector_budget_of_uniform_atom_error (V := V) hδ hspread hbudget

/-- Stable AN1/N5 handle for the selector-budget degree schedule. -/
theorem N5_selector_budget_schedule_exists
    {V : Type} [Fintype V] {spread ε : ℝ}
    (hspread : 0 ≤ spread) (hε : 0 < ε) :
    ∃ N : ℕ,
      selectorEpsTotal (V := V)
        (3 * selectorAtomEps N)
        (selectorAtomEps N)
        ((3 + offViewCount V) * selectorAtomEps N)
        spread ≤ ε :=
  selector_budget_schedule_exists hspread hε

end

end Ripple.BoundedUniversality.BGP
