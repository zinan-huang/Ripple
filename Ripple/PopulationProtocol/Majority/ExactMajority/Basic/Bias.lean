/-
Dyadic bias representation.

A biased agent holds bias = ± 2^(exponent) where exponent ∈ {-L, ..., -1, 0}
and L = ⌈log₂ n⌉. Unbiased agents have bias = 0. The "mass" of an agent is
|bias|. The population-wide invariant is g = Σ v.bias = (initial #A) − (initial #B).

This file abstracts the bias as a sign × exponent pair, plus a separate "zero"
case. We parametrize by L : ℕ (the bound on |exponent|).

Reference: Doty et al., §3.1 high-level overview; §3.4 Phase 3.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Rat.Defs

namespace ExactMajority

inductive Sign | pos | neg
  deriving DecidableEq, Repr

instance : Fintype Sign where
  elems := {.pos, .neg}
  complete s := by cases s <;> simp

/-- A bias is either zero, or a signed dyadic ±2^(-i) with 0 ≤ i ≤ L.
We encode `i` as `Fin (L+1)` so that `i = 0` corresponds to bias = ±1
and `i = L` corresponds to bias = ±2^(-L). -/
inductive Bias (L : ℕ) where
  | zero
  | dyadic (s : Sign) (i : Fin (L + 1))
  deriving DecidableEq, Repr

/-- Encode a `Bias L` as `Option (Sign × Fin (L+1))`: zero ↔ none,
dyadic s i ↔ some (s, i). Used to derive `Fintype`. -/
def Bias.toOption {L : ℕ} : Bias L → Option (Sign × Fin (L + 1))
  | .zero => none
  | .dyadic s i => some (s, i)

def Bias.ofOption {L : ℕ} : Option (Sign × Fin (L + 1)) → Bias L
  | none => .zero
  | some (s, i) => .dyadic s i

@[simp] lemma Bias.ofOption_toOption {L : ℕ} (b : Bias L) :
    Bias.ofOption (Bias.toOption b) = b := by
  cases b <;> rfl

@[simp] lemma Bias.toOption_ofOption {L : ℕ} (o : Option (Sign × Fin (L + 1))) :
    Bias.toOption (Bias.ofOption o) = o := by
  rcases o with _ | ⟨s, i⟩ <;> rfl

instance {L : ℕ} : Fintype (Bias L) :=
  Fintype.ofEquiv (Option (Sign × Fin (L + 1)))
    { toFun := Bias.ofOption
      invFun := Bias.toOption
      left_inv := Bias.toOption_ofOption
      right_inv := Bias.ofOption_toOption }

namespace Bias

variable {L : ℕ}

/-- Numerical value of a bias as a rational. -/
def toRat : Bias L → ℚ
  | .zero => 0
  | .dyadic .pos i => (1 : ℚ) / (2 ^ (i : ℕ))
  | .dyadic .neg i => -(1 : ℚ) / (2 ^ (i : ℕ))

/-- Sign of a bias: +1, 0, or -1. -/
def signInt : Bias L → Int
  | .zero => 0
  | .dyadic .pos _ => 1
  | .dyadic .neg _ => -1

/-- Exponent magnitude of a biased agent (undefined for `zero`). -/
def exponentMag? : Bias L → Option ℕ
  | .zero => none
  | .dyadic _ i => some i

end Bias
end ExactMajority
