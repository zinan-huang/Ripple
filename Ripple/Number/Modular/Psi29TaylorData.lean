import Ripple.Number.Modular.Psi29Terms
import Ripple.Number.Modular.Phi41TaylorData

/-!
# Taylor data of `Ψ₂₉` at `(T₀, T₀)`, `T₀ = 256·99⁴ − 104`

`psi29PartialAt a b terms` is `∂ₓᵃ ∂ᵧᵇ Ψ (T₀, T₀)` for `Ψ = Σ c Xˣ Yʸ`. Kernel facts for the
second-order (Masser) argument of `docs/audit/CHUD-PAPER.md` §4.4: `Ψ(T₀,T₀) = 0`,
`Ψ_X = Ψ_Y ≠ 0`, `Ψ_XX = Ψ_YY` and `−2(Ψ_XX − Ψ_XY)/Ψ_X = 66716347/787408797714739200`
(`lvl58/masser58.gp`). No Mathlib.
-/

namespace Ripple.Number.Modular

/-- `T₀ = 256·99⁴ − 104`. -/
def psi29T0 : Nat := 256 * 99 ^ 4 - 104

/-- `∂ₓᵃ ∂ᵧᵇ Ψ (T₀, T₀)`. -/
def psi29PartialAt (a b : Nat) : List SparseBivarTerm → Int
  | [] => 0
  | t :: ts =>
      t.coeff * phi41Dfac t.xPow a * phi41Dfac t.yPow b *
          ((psi29T0 ^ (t.xPow + t.yPow - a - b) : Nat) : Int) +
        psi29PartialAt a b ts

theorem psi29Partial00 : psi29PartialAt 0 0 psi29SparseTerms = 0 := by
  decide +kernel

theorem psi29Partial10_eq_01 :
    psi29PartialAt 1 0 psi29SparseTerms = psi29PartialAt 0 1 psi29SparseTerms := by
  decide +kernel

theorem psi29Partial10_ne_zero : psi29PartialAt 1 0 psi29SparseTerms ≠ 0 := by
  decide +kernel

theorem psi29Partial20_eq_02 :
    psi29PartialAt 2 0 psi29SparseTerms = psi29PartialAt 0 2 psi29SparseTerms := by
  decide +kernel

/-- `−2(Ψ_XX − Ψ_XY) · 787408797714739200 = 66716347 · Ψ_X`. -/
theorem psi29_masser_ratio :
    -2 * (psi29PartialAt 2 0 psi29SparseTerms - psi29PartialAt 1 1 psi29SparseTerms) *
        787408797714739200 =
      66716347 * psi29PartialAt 1 0 psi29SparseTerms := by
  decide +kernel

end Ripple.Number.Modular
