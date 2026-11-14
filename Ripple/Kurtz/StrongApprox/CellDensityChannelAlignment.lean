-- Ripple/Kurtz/StrongApprox/CellDensityChannelAlignment.lean
import Ripple.Kurtz.StrongApprox.CellExtendedRecordSequence
import Ripple.Kurtz.StrongApprox.DensityDependentRecordLaw

noncomputable section

namespace Ripple.Kurtz.StrongApprox.CellDensityChannelAlignment

open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal NNReal BigOperators Classical
open Ripple.CTMC
open Ripple.Kurtz

variable {d : ℕ} {ι : Type*}
variable [Fintype ι] [DecidableEq ι]

/-- The fixed channel names are exactly the listed nonzero jump vectors.
The zero jump is omitted from the Poisson family. -/
abbrev ListedNonzeroJump (Gamma : RateSpec d) :=
  {ell : Fin d → ℤ // ell ∈ Gamma.jumps ∧ ell ≠ 0}

/-- Explicit Γ/β/v alignment used by the cell construction.

`boundary` is the ambient-cube version.  It may be weakened to
`BoundaryCompatibleOnSimplex` only after the corrected recursion also carries
and preserves `InSimplex` at every record. -/
structure DensityChannelAlignment
    (Gamma : RateSpec d)
    (beta : ι → (Fin d → ℝ) → ℝ)
    (v : ι → Fin d → ℝ)
    (xDensity : Fin d → ℝ)
    (latticeStart : ∀ n : ℕ, 0 < n → Fin d → Fin (n + 1)) : Type _ where
  channelEquiv : ι ≃ ListedNonzeroJump Gamma
  beta_eq : ∀ l y,
    beta l y = Gamma.rate (channelEquiv l).1 y
  vector_eq : ∀ l i,
    v l i = ((channelEquiv l).1 i : ℝ)
  boundary : ∀ n : ℕ, ∀ hn : 0 < n,
    (DensityDepCTMC.mk n hn Gamma).BoundaryCompatible
  zero_jump_rate : Gamma.rate (0 : Fin d → ℤ) = 0
  initial_alignment : ∀ n : ℕ, ∀ hn : 0 < n,
    (DensityDepCTMC.mk n hn Gamma).scaledState
        (latticeStart n hn) = xDensity

namespace DensityChannelAlignment

variable {Gamma : RateSpec d}
variable {beta : ι → (Fin d → ℝ) → ℝ}
variable {v : ι → Fin d → ℝ}
variable {xDensity : Fin d → ℝ}
variable {latticeStart : ∀ n : ℕ, 0 < n → Fin d → Fin (n + 1)}

/-- Integer jump carried by a channel. -/
def jump
    (A : DensityChannelAlignment Gamma beta v xDensity latticeStart)
    (l : ι) : Fin d → ℤ :=
  (A.channelEquiv l).1

@[simp]
theorem jump_mem
    (A : DensityChannelAlignment Gamma beta v xDensity latticeStart)
    (l : ι) : A.jump l ∈ Gamma.jumps :=
  (A.channelEquiv l).2.1

@[simp]
theorem jump_ne_zero
    (A : DensityChannelAlignment Gamma beta v xDensity latticeStart)
    (l : ι) : A.jump l ≠ 0 :=
  (A.channelEquiv l).2.2

/-- The real density-dependent rate at lattice scale `n`.
This is the convention used by `DensityDepCTMC.mk`. -/
noncomputable def densityRate
    (A : DensityChannelAlignment Gamma beta v xDensity latticeStart)
    (n : ℕ) (hn : 0 < n)
    (x : Fin d → Fin (n + 1)) (l : ι) : ℝ :=
  (n : ℝ) * beta l ((DensityDepCTMC.mk n hn Gamma).scaledState x)

/-- Nonnegative rate passed to a cell-clock recursion. -/
noncomputable def latticeRate
    (A : DensityChannelAlignment Gamma beta v xDensity latticeStart)
    (n : ℕ) (hn : 0 < n)
    (x : Fin d → Fin (n + 1)) (l : ι) : ℝ≥0 :=
  Real.toNNReal (A.densityRate n hn x l)

/-- A jump is lattice-valid at `x` when it has a target in the ambient cube. -/
def hasLatticeTarget
    (A : DensityChannelAlignment Gamma beta v xDensity latticeStart)
    (n : ℕ) (hn : 0 < n)
    (x : Fin d → Fin (n + 1)) (l : ι) : Prop :=
  ∃ y : Fin d → Fin (n + 1),
    ∀ i, (y i : ℤ) - (x i : ℤ) = A.jump l i

/-- Total lattice step.  The invalid branch is an identity branch, but
boundary compatibility proves that branch has rate zero. -/
noncomputable def latticeStep
    (A : DensityChannelAlignment Gamma beta v xDensity latticeStart)
    (n : ℕ) (hn : 0 < n)
    (x : Fin d → Fin (n + 1)) (l : ι) :
    Fin d → Fin (n + 1) :=
  if h : A.hasLatticeTarget n hn x l then Classical.choose h else x

/-- Boundary compatibility makes every invalid aligned channel inactive. -/
theorem latticeRate_eq_zero_of_no_target
    (A : DensityChannelAlignment Gamma beta v xDensity latticeStart)
    (n : ℕ) (hn : 0 < n)
    (x : Fin d → Fin (n + 1)) (l : ι)
    (hno : ¬ A.hasLatticeTarget n hn x l) :
    A.latticeRate n hn x l = 0 := by
  have hz :
      Gamma.rate (A.jump l)
          ((DensityDepCTMC.mk n hn Gamma).scaledState x) = 0 :=
    A.boundary n hn x (A.jump l) (A.jump_mem l) hno
  have hz' :
      Gamma.rate (A.channelEquiv l).1
          ((DensityDepCTMC.mk n hn Gamma).scaledState x) = 0 := hz
  simp [latticeRate, densityRate, A.beta_eq, hz']

/-- A positive channel really takes the advertised integer jump. -/
theorem latticeStep_spec_of_positive
    (A : DensityChannelAlignment Gamma beta v xDensity latticeStart)
    (n : ℕ) (hn : 0 < n)
    (x : Fin d → Fin (n + 1)) (l : ι)
    (hpositive : 0 < A.latticeRate n hn x l) :
    ∀ i,
      (A.latticeStep n hn x l i : ℤ) - (x i : ℤ) = A.jump l i := by
  by_cases htarget : A.hasLatticeTarget n hn x l
  · intro i
    simp only [latticeStep, dif_pos htarget]
    exact Classical.choose_spec htarget i
  · have hz := A.latticeRate_eq_zero_of_no_target n hn x l htarget
    rw [hz] at hpositive
    exact (lt_irrefl 0 hpositive).elim

/-- Formal obstruction to instantiating the global positivity hypothesis of `CellActiveRaceRecordKernel`.
Any aligned channel that is invalid at one state has zero rate there. -/
theorem not_everywhere_positive_of_invalid
    (A : DensityChannelAlignment Gamma beta v xDensity latticeStart)
    (n : ℕ) (hn : 0 < n)
    (x : Fin d → Fin (n + 1)) (l : ι)
    (hno : ¬ A.hasLatticeTarget n hn x l) :
    ¬ (∀ y : Fin d → Fin (n + 1), ∀ q : ι,
        0 < A.latticeRate n hn y q) := by
  intro hall
  have hp := hall x l
  have hz := A.latticeRate_eq_zero_of_no_target n hn x l hno
  rw [hz] at hp
  exact (lt_irrefl 0) hp

/-!
THEOREM LIST
* `DensityChannelAlignment.jump_mem`
* `DensityChannelAlignment.jump_ne_zero`
* `DensityChannelAlignment.latticeRate_eq_zero_of_no_target`
* `DensityChannelAlignment.latticeStep_spec_of_positive`
* `DensityChannelAlignment.not_everywhere_positive_of_invalid`

CLOSES
* Explicit equivalence between `ι` and Γ's listed nonzero jumps.
* Exact β and v alignment.
* Boundary compatibility and zero-jump removal.
* Exact initial-density alignment at every scale.
* The scale-`n` rate and total lattice step.
* Formal refutation of that global positivity premise at an invalid boundary
  channel.

UNFINISHED
* If only `BoundaryCompatibleOnSimplex` is available, transport and preserve
  `InSimplex` in the corrected record recursion.
* Derive the active-channel/active-target equivalence used in the next file.
END
-/

end DensityChannelAlignment

end Ripple.Kurtz.StrongApprox.CellDensityChannelAlignment

end
