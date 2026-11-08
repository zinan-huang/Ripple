import Ripple.Number.Modular.SturmPackedNat

/-!
# Kernel evaluation of the packed level-41 expansion

The numbers below are Kronecker-packed images: `1728 E₄³` and `1728 Δ` in the wide ring (slot
width `packSlot`, modulus `2 ^ (packSlot * packN)`, `packN = 1766` slots), the `q⁴¹` side in a
compact ring (`44` slots of width `packCW`), and `1728 ^ 84` times the cleared level-41 expansion.
Only the first `1765` coefficients are needed: the Fricke involution halves the level-41 Sturm
bound (`Phi41Fricke`).
`packFinal_eq_zero` is checked by the kernel with GMP arithmetic; `SturmPacked` proves that these
numbers are the packed series.

Memory: the kernel keeps every intermediate number it computes, so the evaluation builds as few
full-width (1.65 MB) numbers as possible. `E₄` and `Σ σ₅` are summed in narrow slots and spread
once; `1728 Δ` comes from `E₄³ - E₆²`; the whole `q⁴¹` side, including the `1766`
coefficient products, is computed in the compact ring and grouped by `y` in one pass over the
terms; each group `T_y` is spread once to the wide layout; the final sum over `y` is a Horner
sum. The module imports only the definitions and the term data (`SturmPackedNat`), not
Mathlib.
-/

namespace Ripple.Number.Modular

/-! ### The kernel computation -/

/-- Slot width in bits. -/
def packSlot : Nat := 7469

/-- Number of slots: the Fricke-halved Sturm bound `phi41FrickeSturmBound = 1765` plus one spare
slot that absorbs the `1728 ^ 84` scaling (`SturmPacked` checks
`packN = phi41FrickeSturmBound + 1`). -/
def packN : Nat := 1766

/-- The modulus `2 ^ (packSlot * packN)`, written with a shift so that the kernel computes it
by GMP (`Nat.pow` is not accelerated for an exponent this large). -/
def packM : Nat := 1 <<< (packSlot * packN)

/-- The mask `packM - 1`. -/
def packMask : Nat := packM - 1

theorem packMask_eq : packMask = packM - 1 := rfl

/-- Packed `E₄`: computed in `72`-bit slots (sharing the geometric sums with `packS5`), then
spread to `packSlot`-bit slots. -/
def packE4 : Nat := spread 72 packSlot (e4Pack 72 packN) 12 0 packN

/-- Packed `Σ σ₅(m) qᵐ`: computed in `72`-bit slots, then spread. -/
def packS5 : Nat := spread 72 packSlot (sigmaPack 5 72 packN) 12 0 packN

/-- Packed `E₆ = 1 - 504 Σ σ₅(m) qᵐ`. -/
def packE6 : Nat := subM packMask 1 (504 * packS5)

/-- Packed `E₄³`. -/
def packC0 : Nat := mulM packMask (mulM packMask packE4 packE4) packE4

/-- Packed `1728 E₄³`. -/
def packC : Nat := 1728 * packC0

/-- Packed `1728 Δ = E₄³ - E₆²`. -/
def packD : Nat := subM packMask packC0 (mulM packMask packE6 packE6)

/-! The `q⁴¹` side lives in a compact ring: `44` slots of width `packCW` (`41 · 44 ≥ packN`),
modulus `2 ^ (packCW * 44)`. -/

/-- Compact slot width: `1 + log₂` of the proved bound on the coefficients of the grouped sums
`T_y` (`phi41TSer_coeff_lt` in `SturmPacked`). -/
def packCW : Nat := 4280

/-- The compact modulus `2 ^ (packCW * 44)`. -/
def packCM : Nat := 1 <<< (packCW * 44)

/-- The compact mask. -/
def packCMask : Nat := packCM - 1

theorem packCMask_eq : packCMask = packCM - 1 := rfl

/-- Compact `E₄`. -/
def compE4 : Nat := e4Pack packCW 44

/-- Compact `E₆`. -/
def compE6 : Nat := subM packCMask 1 (504 * sigmaPack 5 packCW 44)

/-- Compact `E₄³`. -/
def compA0 : Nat := mulM packCMask (mulM packCMask compE4 compE4) compE4

/-- Compact `1728 E₄³`. -/
def compA : Nat := 1728 * compA0

/-- Compact `1728 Δ = E₄³ - E₆²`. -/
def compB : Nat := subM packCMask compA0 (mulM packCMask compE6 compE6)

def compPowA : List Nat := powTab packCMask compA 1 43
def compPowB : List Nat := powTab packCMask compB 1 43

/-- Compact `A ^ x · B ^ (42 - x)`. -/
def compL : List Nat :=
  (List.range 43).map fun x => mulM packCMask (compPowA.getD x 0) (compPowB.getD (42 - x) 0)

/-- Positive and negative parts of every `T_y`, in one pass over the terms. -/
def compTs : List (Nat × Nat) := bucketPN compL 43 phi41SparseTerms

/-- Compact `T_y = Σ_{yPow = y} c · A ^ xPow · B ^ (42 - xPow)`. -/
def compT (y : Nat) : Nat := subM packCMask (compTs.getD y (0, 0)).1 (compTs.getD y (0, 0)).2

/-- `2 ^ (packCW - 1)` in each of the `44` compact slots. -/
def compBias : Nat := 2 ^ (packCW - 1) * (1 + geomF packCW 7 43)

/-- `T_y` plus the bias: its compact digits are the coefficients of `T_y` plus
`2 ^ (packCW - 1)`. -/
def compU (y : Nat) : Nat := (compT y + compBias) % packCM

/-- Minus the bias spread to slots `41 m` of width `packSlot`. -/
def packNegBias : Nat := negM packMask (spread packCW (41 * packSlot) compBias 7 0 44)

/-- `T_y(q⁴¹)` in the wide ring: `compU y` spread to slots `41 m` by one product and one mask. -/
def packSY (y : Nat) : Nat := combSpread (41 * packSlot - packCW) packCW 44 (compU y) + packNegBias

def packPowD : List Nat := powTab packMask packD 1 43

/-- The packed cleared level-41 expansion, scaled by `1728 ^ 84`:
`Σ_y C ^ y · D ^ (42 - y) · T_y(q⁴¹)` by Horner's rule in `C`. -/
def packFinal : Nat :=
  hornerM packMask packC (fun j => packSY (42 - j)) (fun j => packPowD.getD j 0) 43

theorem packFinal_eq_zero : packFinal = 0 := by
  decide +kernel

end Ripple.Number.Modular
