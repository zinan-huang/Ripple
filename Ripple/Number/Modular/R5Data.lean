import Ripple.Number.Modular.Psi29Terms

/-!
# Kernel data for R5: the root `T₀` of `Ψ₂₉(X, X)`

With `a = 1.1·10¹⁰`, `T₀ = 256·99⁴ − 104` and `b = T₀ − a`, the shifted diagonal
`Ψ₂₉(a + h, a + h) = Σ_k δ_k h^k` (`r5Delta`) factors as `(h − b) · Σ_k d_k h^k` with all
`d_k ≤ 0` and `d_0 < 0` (`r5Cof`, the Taylor coefficients at `a` of `Ψ₂₉(X,X)/(X − T₀)`; all
roots of that cofactor have real part below `1.062·10¹⁰`, `lvl58/r5cofactor.gp`). The
coefficients `d_k` are computed here from the `δ_k` by `d_k = (d_{k−1} − δ_k)/b`, and the kernel
checks that every division is exact and every sign is right (`r5Check_eq_true`). No Mathlib.
-/

namespace Ripple.Number.Modular

def r5A : Int := 11000000000

def r5T0 : Int := 256 * 99 ^ 4 - 104

def r5B : Int := r5T0 - r5A

def factN : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factN n

def chooseN (n k : Nat) : Nat :=
  if k ≤ n then factN n / (factN k * factN (n - k)) else 0

/-- `δ_k = Σ c · C(i + j, k) · a^(i + j − k)`: the coefficient of `h^k` in `Ψ₂₉(a + h, a + h)`. -/
def r5Delta (k : Nat) : Int :=
  (psi29SparseTerms.map fun t =>
    t.coeff * (chooseN (t.xPow + t.yPow) k : Int) * r5A ^ (t.xPow + t.yPow - k)).sum

def r5DeltaL : List Int := (List.range 61).map r5Delta

/-- `d_k = (d_{k−1} − δ_k)/b` for `k < 58`. -/
def r5CofAux : List Int → Int → Nat → List Int
  | _, _, 0 => []
  | δs, prev, n + 1 =>
      let dk := (prev - δs.headD 0) / r5B
      dk :: r5CofAux δs.tail dk n

def r5Cof : List Int := r5CofAux r5DeltaL 0 58

/-- `δ_k = d_{k−1} − b d_k` for all `k < 61` (with `d_{−1} = 0`, `d_k = 0` for `k ≥ 58`), all
`d_k ≤ 0`, `d_0 < 0`. -/
def r5Check : Bool :=
  r5Cof.length == 58 &&
  ((List.range 61).all fun k =>
    r5DeltaL.getD k 0 == (if k = 0 then 0 else r5Cof.getD (k - 1) 0) - r5B * r5Cof.getD k 0) &&
  r5Cof.all (fun d => decide (d ≤ 0)) && decide (r5Cof.getD 0 0 < 0)

theorem r5Check_eq_true : r5Check = true := by
  decide +kernel

theorem psi29SparseTerms_diag_le_60 :
    (psi29SparseTerms.all fun t => decide (t.xPow + t.yPow ≤ 60)) = true := by
  decide +kernel

end Ripple.Number.Modular
