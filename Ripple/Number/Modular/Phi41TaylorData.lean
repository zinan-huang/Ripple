import Ripple.Number.Modular.ModularPoly41Terms

/-!
# Taylor data of `Φ₄₁` at the CM point `(j₀, j₀)`, `j₀ = −640320³`

`partialAt a b terms` is the partial derivative `∂ₓᵃ ∂ᵧᵇ Φ (j₀, j₀)` of the sparse integer
polynomial `Φ = Σ c Xˣ Yʸ`, i.e. `Σ c · x(x-1)⋯(x-a+1) · y(y-1)⋯(y-b+1) · j₀^(x-a+y-b)`.
The kernel facts below are the finite computations K1–K6 of `docs/audit/CHUD-PAPER.md` §3.1
for Ripple's `phi41SparseTerms`; `Ripple.Number.Modular.Phi41Node` turns them into the value
of `s₂(τ₁₆₃)`. The module imports only the coefficient data, so the kernel checks run without
the analytic library. The power `|j₀|^k` is one GMP `Nat.pow` step.
-/

namespace Ripple.Number.Modular

/-- Falling factorial `n (n-1) ⋯ (n-k+1)` as an integer (zero when `k > n`). -/
def phi41Dfac (n : Nat) : Nat → Int
  | 0 => 1
  | k + 1 => ((n : Int) - k) * phi41Dfac n k

/-- `|j₀| = 640320³`. -/
def phi41AbsJ0 : Nat := 262537412640768000

/-- `j₀^k = (-640320³)^k`, with the power computed on `Nat`. -/
def phi41J0Pow (k : Nat) : Int :=
  if k % 2 = 0 then ((phi41AbsJ0 ^ k : Nat) : Int) else -((phi41AbsJ0 ^ k : Nat) : Int)

/-- `∂ₓᵃ ∂ᵧᵇ Φ (j₀, j₀)` for a sparse term list `Φ = Σ c Xˣ Yʸ`. -/
def phi41PartialAt (a b : Nat) : List SparseBivarTerm → Int
  | [] => 0
  | t :: ts =>
      t.coeff * phi41Dfac t.xPow a * phi41Dfac t.yPow b *
          phi41J0Pow (t.xPow + t.yPow - a - b) +
        phi41PartialAt a b ts

/-- K1: `Φ₄₁(j₀, j₀) = 0`. -/
theorem phi41Partial00 : phi41PartialAt 0 0 phi41SparseTerms = 0 := by decide +kernel

/-- K2: both first partials vanish at `(j₀, j₀)` (a singular point of `Φ₄₁ = 0`). -/
theorem phi41Partial10 : phi41PartialAt 1 0 phi41SparseTerms = 0 := by decide +kernel

theorem phi41Partial01 : phi41PartialAt 0 1 phi41SparseTerms = 0 := by decide +kernel

/-- K3: symmetry of the second and third partials. -/
theorem phi41Partial20_eq_02 :
    phi41PartialAt 2 0 phi41SparseTerms = phi41PartialAt 0 2 phi41SparseTerms := by
  decide +kernel

theorem phi41Partial21_eq_12 :
    phi41PartialAt 2 1 phi41SparseTerms = phi41PartialAt 1 2 phi41SparseTerms := by
  decide +kernel

theorem phi41Partial30_eq_03 :
    phi41PartialAt 3 0 phi41SparseTerms = phi41PartialAt 0 3 phi41SparseTerms := by
  decide +kernel

/-- K4: `82 ∂ₓ∂ᵧΦ = 81 ∂ₓ²Φ` at `(j₀, j₀)` (Taylor form `41 β₁₁ = 81 β₂₀`). -/
theorem phi41Partial11 :
    82 * phi41PartialAt 1 1 phi41SparseTerms = 81 * phi41PartialAt 2 0 phi41SparseTerms := by
  decide +kernel

/-- K5: the node is ordinary: `∂ₓ²Φ (j₀, j₀) ≠ 0`. -/
theorem phi41Partial20_ne_zero : phi41PartialAt 2 0 phi41SparseTerms ≠ 0 := by decide +kernel

/-- K6, cross-multiplied: with `Pₐᵦ = ∂ₓᵃ∂ᵧᵇΦ (j₀, j₀)`,
`(7j₀ − 6912)/(j₀ − 1728) + 2 j₀ (244 P₃₀ − 246 P₂₁)/(163 P₂₀) = 77265280/90856689`. -/
theorem phi41PartialK6 :
    90856689 * ((7 * phi41J0Pow 1 - 6912) * (163 * phi41PartialAt 2 0 phi41SparseTerms) +
      2 * phi41J0Pow 1 *
        (244 * phi41PartialAt 3 0 phi41SparseTerms - 246 * phi41PartialAt 2 1 phi41SparseTerms) *
        (phi41J0Pow 1 - 1728)) =
    77265280 * ((phi41J0Pow 1 - 1728) * (163 * phi41PartialAt 2 0 phi41SparseTerms)) := by
  decide +kernel

end Ripple.Number.Modular
