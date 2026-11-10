import Ripple.Number.Modular.SturmPackedNat
import Ripple.Number.Modular.Psi29Terms

/-!
# Kernel evaluation of the packed cleared `Ψ₂₉`

The first `3601` coefficients (the `Γ₀(58)` Sturm bound `480 · 90 / 12 + 1`) of

  `Σ c_{xy} P(29τ)^x Q(29τ)^{30−x} P(τ)^y Q(τ)^{30−y}`,
  `P = 248 e² − 616 e f + 3968 f²`, `Q = −e² + 17 e f − 16 f²`, `e = E₄(τ)`, `f = E₄(2τ)`,

Kronecker-packed at `2 ^ p29S` modulo `2 ^ (p29S · 3601)`. The `q²⁹` side (`T_y = Σ_x c_{xy}
P^x Q^{30−x}` in the variable `q²⁹`, `125` coefficients) is computed in a compact ring of width
`p29CW`, biased, and spread to the slots `29 m` of the wide ring; the sum over `y` is a Horner
sum in `P`. `p29Final_eq_zero` is checked by the kernel with GMP arithmetic.

The slot widths come from a priori coefficient bounds (`Psi29Certificate`), checked here as
inequalities between natural numbers: weighted sums `Σ_{m<n} e4(m) a^m 2^(k(n-1-m))` of the
`E₄` coefficients (`p29W*_le`) and the resulting bounds for the cleared expansion
(`p29WideBound_lt`) and for the `T_y` (`p29CompactBound_lt`).

The module imports only the definitions and the term data, not Mathlib; `Psi29Certificate`
proves that these numbers are what they claim to be.
-/

namespace Ripple.Number.Modular

/-! ### The packed evaluation -/

/-- Wide slot width in bits. -/
def p29S : Nat := 3232

/-- Number of wide slots: the Sturm bound for weight `480` on `Γ₀(58)`. -/
def p29N : Nat := 3601

/-- The wide modulus `2 ^ (p29S * p29N)`. -/
def p29M : Nat := 1 <<< (p29S * p29N)

/-- The wide mask. -/
def p29Mask : Nat := p29M - 1

theorem p29Mask_eq : p29Mask = p29M - 1 := rfl

/-- Packed `E₄(τ)`. -/
def p29E : Nat := spread 72 p29S (e4Pack 72 p29N) 12 0 p29N

/-- Packed `E₄(2τ)`: the `E₄` digits spread to every other slot. -/
def p29F : Nat := spread 72 (2 * p29S) (e4Pack 72 1801) 12 0 1801 &&& p29Mask

def p29EE : Nat := mulM p29Mask p29E p29E
def p29EF : Nat := mulM p29Mask p29E p29F
def p29FF : Nat := mulM p29Mask p29F p29F

/-- Packed `P = 248 e² − 616 e f + 3968 f²`. -/
def p29P : Nat := subM p29Mask (248 * p29EE + 3968 * p29FF) (616 * p29EF)

/-- Packed `Q = −e² + 17 e f − 16 f²`. -/
def p29Q : Nat := subM p29Mask (17 * p29EF) (p29EE + 16 * p29FF)

/-- Compact slot width. -/
def p29CW : Nat := 1700

/-- Number of compact slots (`29 · 125 ≥ 3601`). -/
def p29K : Nat := 125

/-- The compact modulus. -/
def p29CM : Nat := 1 <<< (p29CW * p29K)

/-- The compact mask. -/
def p29CMask : Nat := p29CM - 1

theorem p29CMask_eq : p29CMask = p29CM - 1 := rfl

def c29E : Nat := e4Pack p29CW p29K
def c29F : Nat := e4Pack (2 * p29CW) 63 &&& p29CMask
def c29EE : Nat := mulM p29CMask c29E c29E
def c29EF : Nat := mulM p29CMask c29E c29F
def c29FF : Nat := mulM p29CMask c29F c29F
def c29P : Nat := subM p29CMask (248 * c29EE + 3968 * c29FF) (616 * c29EF)
def c29Q : Nat := subM p29CMask (17 * c29EF) (c29EE + 16 * c29FF)

def c29PowP : List Nat := powTab p29CMask c29P 1 31
def c29PowQ : List Nat := powTab p29CMask c29Q 1 31

/-- Compact `P ^ x · Q ^ (30 - x)`. -/
def c29L : List Nat :=
  (List.range 31).map fun x => mulM p29CMask (c29PowP.getD x 0) (c29PowQ.getD (30 - x) 0)

/-- Positive and negative parts of every `T_y`, in one pass over the terms. -/
def c29Ts : List (Nat × Nat) := bucketPN c29L 31 psi29SparseTerms

/-- Compact `T_y = Σ_{yPow = y} c · P ^ xPow · Q ^ (30 - xPow)`. -/
def c29T (y : Nat) : Nat := subM p29CMask (c29Ts.getD y (0, 0)).1 (c29Ts.getD y (0, 0)).2

/-- `2 ^ (p29CW - 1)` in each of the `125` compact slots. -/
def c29Bias : Nat := 2 ^ (p29CW - 1) * (1 + geomF p29CW 7 124)

/-- `T_y` plus the bias. -/
def c29U (y : Nat) : Nat := (c29T y + c29Bias) % p29CM

/-- Minus the bias, spread to the wide slots `29 m`. -/
def p29NegBias : Nat := negM p29Mask (spread p29CW (29 * p29S) c29Bias 7 0 p29K)

/-- `T_y(q²⁹)` in the wide ring. -/
def p29SY (y : Nat) : Nat := spread p29CW (29 * p29S) (c29U y) 7 0 p29K + p29NegBias

def p29PowQ : List Nat := powTab p29Mask p29Q 1 31

/-- The packed cleared expansion `Σ_y P ^ y · Q ^ (30 - y) · T_y(q²⁹)`, by Horner's rule in `P`. -/
def p29Final : Nat :=
  hornerM p29Mask p29P (fun j => p29SY (30 - j)) (fun j => p29PowQ.getD j 0) 31

theorem p29Final_eq_zero : p29Final = 0 := by
  decide +kernel

/-! ### Scalar bounds -/

/-- `Σ_{m<n} d(m) a^m 2^(k(n-1-m))`, `d(m)` the `m`-th `72`-bit slot of `V`. -/
def wsumDig (V a k n : Nat) : Nat :=
  treeSum (fun m => ((V >>> (72 * m)) % 2 ^ 72 * a ^ m) <<< (k * (n - 1 - m))) 12 0 n

/-- Scale of the rational bounds: `U / 2 ^ p29SC`. -/
def p29SC : Nat := 20

def p29UE : Nat := 5140269310162
def p29UE2 : Nat := 321266831886
def p29U29 : Nat := 11358303
def p29U58 : Nat := 1171997
def c29UE : Nat := 87404364
def c29UE2 : Nat := 5561702

/-- `Σ_{m<3601} e4(m) (7/8)^m ≤ p29UE / 2^20`. -/
theorem p29WE_le :
    wsumDig (e4Pack 72 p29N) 7 3 p29N <<< p29SC ≤ p29UE <<< (3 * (p29N - 1)) := by
  decide +kernel

/-- `Σ_{m<3601} e4(m) (49/64)^m ≤ p29UE2 / 2^20`. -/
theorem p29WE2_le :
    wsumDig (e4Pack 72 p29N) 49 6 p29N <<< p29SC ≤ p29UE2 <<< (6 * (p29N - 1)) := by
  decide +kernel

/-- `Σ_{m<3601} e4(m) (1/32)^m ≤ p29U29 / 2^20`. -/
theorem p29W29_le :
    wsumDig (e4Pack 72 p29N) 1 5 p29N <<< p29SC ≤ p29U29 <<< (5 * (p29N - 1)) := by
  decide +kernel

/-- `Σ_{m<3601} e4(m) (1/2048)^m ≤ p29U58 / 2^20`. -/
theorem p29W58_le :
    wsumDig (e4Pack 72 p29N) 1 11 p29N <<< p29SC ≤ p29U58 <<< (11 * (p29N - 1)) := by
  decide +kernel

/-- `Σ_{m<125} e4(m) (1/8)^m ≤ c29UE / 2^20`. -/
theorem c29WE_le :
    wsumDig (e4Pack 72 p29K) 1 3 p29K <<< p29SC ≤ c29UE <<< (3 * (p29K - 1)) := by
  decide +kernel

/-- `Σ_{m<125} e4(m) (1/64)^m ≤ c29UE2 / 2^20`. -/
theorem c29WE2_le :
    wsumDig (e4Pack 72 p29K) 1 6 p29K <<< p29SC ≤ c29UE2 <<< (6 * (p29K - 1)) := by
  decide +kernel

/-- `a u² + b u v + c v²` on natural numbers. -/
def quadNat (a b c u v : Nat) : Nat := a * u ^ 2 + b * u * v + c * v ^ 2

/-- `Σ |c| a^x b^(xMax-x) c^y d^(yMax-y)` over the terms. -/
def absEvalNat (xMax yMax a b c d : Nat) : List SparseBivarTerm → Nat
  | [] => 0
  | t :: ts => t.coeff.natAbs * a ^ t.xPow * b ^ (xMax - t.xPow) * c ^ t.yPow *
      d ^ (yMax - t.yPow) + absEvalNat xMax yMax a b c d ts

/-- The a priori bound for the cleared expansion, scaled: below `2 ^ p29S` after dividing by
`2 ^ (120 · p29SC) · (7/8)^3600`. -/
theorem p29WideBound_lt :
    absEvalNat 30 30 (quadNat 248 616 3968 p29U29 p29U58) (quadNat 1 17 16 p29U29 p29U58)
        (quadNat 248 616 3968 p29UE p29UE2) (quadNat 1 17 16 p29UE p29UE2) psi29SparseTerms *
        8 ^ (p29N - 1) <
      7 ^ (p29N - 1) <<< (p29S + 120 * p29SC) := by
  decide +kernel

/-- The a priori bound for the `T_y`, scaled: below `2 ^ (p29CW - 1)` after dividing by
`2 ^ (60 · p29SC) · (1/8)^124`. -/
theorem p29CompactBound_lt :
    absEvalNat 30 0 (quadNat 248 616 3968 c29UE c29UE2) (quadNat 1 17 16 c29UE c29UE2) 1 1
        psi29SparseTerms <<< (3 * (p29K - 1)) <
      1 <<< (p29CW - 1 + 60 * p29SC) := by
  decide +kernel

end Ripple.Number.Modular
