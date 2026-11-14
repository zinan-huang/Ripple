/-
  Ripple.LPP.NAPProtocol — protocol-level non-autocatalytic protocols (NAP)

  A protocol is a finite list of bimolecular reactions `r1 + r2 → p1 + p2` with a positive
  rational rate; its balance field is the mass-action field `Σ_R rate · v_{r1} v_{r2} · (ν_R − μ_R)`.
  `IsNAP` is the protocol-level predicate: no reaction produces (net) a species that it consumes.

  Main content:
  * `Protocol`, `IsNAP`, `balanceField`, `balanceField_conservative` (the field sums to zero
    identically in the free variables, which is what a per-monomial rewriting of a lifted field
    does not give);
  * `transfer_isNAP`: the elementary transfer reaction `s + c → t + c` (t ∉ {s, c}) used by the
    transportation construction of the paper write-up;
  * `cf24Cubing`: an explicit 141-reaction NAP on the 20 cubed variables of the CF'24 example,
    with `cf24Cubing_isNAP` (decided) and `cf24Cubing_faithful` : on the Veronese image
    `v = cubedLift x` its balance field equals the chain-rule derivative of the cubed variables
    along the r²-trick field, i.e. the same polynomials as `napField_chain_v*` in
    `Ripple.LPP.CF24Example` (`cf24Cubing_eq_napField_on_cubed`).

  The reaction list was produced by the transportation (supply/demand) construction of
  the PP-to-NAP write-up.
-/

import Ripple.LPP.CF24Example

namespace Ripple
namespace NAPProtocol

/-- A bimolecular reaction `r1 + r2 → p1 + p2` with rate constant `rate`. -/
structure Reaction (S : Type) where
  r1 : S
  r2 : S
  p1 : S
  p2 : S
  rate : ℚ

variable {S : Type} [DecidableEq S]

/-- Net stoichiometric change of species `s` in reaction `R` (products minus reactants). -/
def Reaction.net (R : Reaction S) (s : S) : ℤ :=
  (if R.p1 = s then 1 else 0) + (if R.p2 = s then 1 else 0)
    - (if R.r1 = s then 1 else 0) - (if R.r2 = s then 1 else 0)

/-- A reaction is non-autocatalytic if every species it consumes is not net-produced:
each reactant appears among the products at most as often as among the reactants. -/
def Reaction.IsNAP (R : Reaction S) : Prop :=
  R.net R.r1 ≤ 0 ∧ R.net R.r2 ≤ 0

instance (R : Reaction S) : Decidable R.IsNAP := by unfold Reaction.IsNAP; infer_instance

/-- A protocol: a finite list of reactions. -/
abbrev Protocol (S : Type) := List (Reaction S)

/-- Protocol-level NAP predicate: every reaction is non-autocatalytic. -/
def IsNAP (P : Protocol S) : Prop := ∀ R ∈ P, R.IsNAP

/-- All rate constants positive. -/
def RatesPos (P : Protocol S) : Prop := ∀ R ∈ P, 0 < R.rate

instance (P : Protocol S) : Decidable (IsNAP P) := by unfold IsNAP; infer_instance

/-- Mass-action balance field of a protocol in the free variables `v`. -/
def balanceField (P : Protocol S) (v : S → ℝ) (s : S) : ℝ :=
  (P.map fun R => (R.rate : ℝ) * v R.r1 * v R.r2 * (R.net s : ℝ)).sum

theorem Reaction.sum_net [Fintype S] (R : Reaction S) : ∑ s, R.net s = 0 := by
  simp [Reaction.net, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- The balance field of any protocol is conservative as an identity in the free variables. -/
theorem balanceField_conservative [Fintype S] (P : Protocol S) (v : S → ℝ) :
    ∑ s, balanceField P v s = 0 := by
  induction P with
  | nil => simp [balanceField]
  | cons R P ih =>
    have h : ∑ s, ((R.rate : ℝ) * v R.r1 * v R.r2 * (R.net s : ℝ)) = 0 := by
      rw [← Finset.mul_sum]
      have : ∑ s, (R.net s : ℝ) = 0 := by
        rw [← Int.cast_sum, R.sum_net]; simp
      rw [this, mul_zero]
    simp only [balanceField, List.map_cons, List.sum_cons] at ih ⊢
    rw [Finset.sum_add_distrib, h, zero_add]
    exact ih

/-- A NAP reaction never net-produces one of its reactants: the field-level NAP condition
(no positive term containing `v_s` in `v̇_s`) holds for its contribution. -/
theorem Reaction.IsNAP.net_nonpos_of_reactant {R : Reaction S} (h : R.IsNAP) {s : S}
    (hs : R.r1 = s ∨ R.r2 = s) : R.net s ≤ 0 := by
  rcases hs with rfl | rfl
  · exact h.1
  · exact h.2

/-- The elementary transfer reaction `s + c → t + c` used by the transportation construction. -/
def transfer (s c t : S) (k : ℚ) : Reaction S := ⟨s, c, t, c, k⟩

/-- A transfer `s + c → t + c` with `t ∉ {s, c}` is non-autocatalytic (also when `s = c`). -/
theorem transfer_isNAP {s c t : S} (k : ℚ) (hts : t ≠ s) (htc : t ≠ c) :
    (transfer s c t k).IsNAP := by
  unfold transfer Reaction.IsNAP Reaction.net
  simp only
  by_cases hsc : s = c
  · subst hsc
    simp [hts, hts.symm]
  · constructor
    · simp [hts, hts.symm, hsc, Ne.symm hsc]
    · simp [htc, htc.symm, hsc, Ne.symm hsc]

/-! ## The CF'24 cubing protocol

Species `Fin 20` are the paper's `v_1, …, v_20` (0-based: `i ↔ v_{i+1}`), see `CF24.cubedIndex`.
Each reaction below is a transfer `v_s + v_c → v_t + v_c` with `t ∉ {s, c}`. -/

/-- The 141-reaction NAP on the 20 cubed variables of the CF'24 example. -/
def cf24Cubing : Protocol (Fin 20) := [
  ⟨1, 1, 2, 1, (4/3)⟩,
  ⟨2, 1, 0, 1, (14/3)⟩,
  ⟨2, 1, 3, 1, (2/3)⟩,
  ⟨3, 1, 2, 1, (28/3)⟩,
  ⟨1, 3, 2, 3, (2/3)⟩,
  ⟨2, 3, 0, 3, (1/3)⟩,
  ⟨0, 4, 2, 4, 4⟩,
  ⟨4, 1, 5, 1, (8/3)⟩,
  ⟨1, 4, 5, 4, (8/3)⟩,
  ⟨2, 4, 0, 4, (7/9)⟩,
  ⟨2, 4, 1, 4, (7/9)⟩,
  ⟨2, 4, 6, 4, (2/9)⟩,
  ⟨2, 4, 7, 4, (8/9)⟩,
  ⟨4, 3, 5, 3, (16/15)⟩,
  ⟨3, 4, 5, 4, (32/15)⟩,
  ⟨4, 3, 8, 3, (4/15)⟩,
  ⟨3, 4, 8, 4, (8/15)⟩,
  ⟨4, 4, 11, 4, (4/3)⟩,
  ⟨0, 5, 1, 5, (7/2)⟩,
  ⟨5, 1, 0, 1, (35/18)⟩,
  ⟨5, 1, 4, 1, (35/18)⟩,
  ⟨5, 1, 6, 1, (5/9)⟩,
  ⟨5, 1, 7, 1, (20/9)⟩,
  ⟨5, 3, 0, 3, (1/7)⟩,
  ⟨5, 3, 6, 3, (8/49)⟩,
  ⟨5, 3, 7, 3, (32/49)⟩,
  ⟨5, 3, 9, 3, (2/49)⟩,
  ⟨5, 4, 1, 4, (7/24)⟩,
  ⟨5, 4, 10, 4, (7/24)⟩,
  ⟨5, 4, 12, 4, (1/12)⟩,
  ⟨5, 4, 13, 4, (2/3)⟩,
  ⟨0, 6, 2, 6, 1⟩,
  ⟨6, 1, 5, 1, (128/15)⟩,
  ⟨1, 6, 5, 6, (8/15)⟩,
  ⟨6, 1, 8, 1, (32/15)⟩,
  ⟨1, 6, 8, 6, (2/15)⟩,
  ⟨2, 6, 0, 6, (16/147)⟩,
  ⟨2, 6, 3, 6, (2/21)⟩,
  ⟨2, 6, 7, 6, (64/147)⟩,
  ⟨2, 6, 9, 6, (4/147)⟩,
  ⟨6, 3, 8, 3, (2/3)⟩,
  ⟨3, 6, 8, 6, (2/3)⟩,
  ⟨6, 4, 11, 4, (8/9)⟩,
  ⟨4, 6, 11, 6, (2/9)⟩,
  ⟨6, 4, 14, 4, (4/9)⟩,
  ⟨4, 6, 14, 6, (1/9)⟩,
  ⟨5, 6, 1, 6, (14/339)⟩,
  ⟨5, 6, 12, 6, (5/113)⟩,
  ⟨5, 6, 13, 6, (64/339)⟩,
  ⟨5, 6, 15, 6, (4/339)⟩,
  ⟨5, 6, 17, 6, (16/339)⟩,
  ⟨6, 6, 14, 6, (8/27)⟩,
  ⟨6, 6, 18, 6, (1/27)⟩,
  ⟨7, 1, 2, 1, (14/3)⟩,
  ⟨7, 1, 5, 1, (14/3)⟩,
  ⟨7, 1, 8, 1, (4/3)⟩,
  ⟨7, 3, 8, 3, (2/3)⟩,
  ⟨7, 4, 5, 4, (7/15)⟩,
  ⟨7, 4, 11, 4, (7/15)⟩,
  ⟨7, 4, 14, 4, (2/15)⟩,
  ⟨7, 4, 16, 4, (4/15)⟩,
  ⟨7, 6, 8, 6, (7/99)⟩,
  ⟨7, 6, 14, 6, (8/99)⟩,
  ⟨7, 6, 16, 6, (16/99)⟩,
  ⟨7, 6, 18, 6, (2/99)⟩,
  ⟨0, 8, 3, 8, (1/2)⟩,
  ⟨8, 1, 3, 1, (44/21)⟩,
  ⟨8, 1, 6, 1, (352/147)⟩,
  ⟨8, 1, 7, 1, (1408/147)⟩,
  ⟨8, 1, 9, 1, (88/147)⟩,
  ⟨8, 3, 9, 3, (1/3)⟩,
  ⟨8, 4, 6, 4, (56/339)⟩,
  ⟨8, 4, 12, 4, (20/113)⟩,
  ⟨8, 4, 13, 4, (256/339)⟩,
  ⟨8, 4, 15, 4, (16/339)⟩,
  ⟨8, 4, 17, 4, (64/339)⟩,
  ⟨8, 6, 9, 6, (7/246)⟩,
  ⟨8, 6, 15, 6, (3/82)⟩,
  ⟨8, 6, 17, 6, (32/123)⟩,
  ⟨8, 6, 19, 6, (1/123)⟩,
  ⟨9, 1, 8, 1, (56/3)⟩,
  ⟨9, 4, 14, 4, (32/27)⟩,
  ⟨9, 4, 18, 4, (4/27)⟩,
  ⟨9, 6, 18, 6, (1/3)⟩,
  ⟨10, 1, 11, 1, 4⟩,
  ⟨10, 3, 11, 3, (4/3)⟩,
  ⟨10, 3, 14, 3, (2/3)⟩,
  ⟨0, 11, 1, 11, (35/3)⟩,
  ⟨0, 11, 4, 11, (7/3)⟩,
  ⟨11, 1, 4, 1, (7/4)⟩,
  ⟨11, 1, 10, 1, (7/4)⟩,
  ⟨1, 11, 4, 11, (7/12)⟩,
  ⟨11, 1, 12, 1, (1/2)⟩,
  ⟨11, 1, 13, 1, 4⟩,
  ⟨11, 3, 6, 3, (70/339)⟩,
  ⟨11, 3, 12, 3, (25/113)⟩,
  ⟨11, 3, 13, 3, (320/339)⟩,
  ⟨11, 3, 15, 3, (20/339)⟩,
  ⟨11, 3, 17, 3, (80/339)⟩,
  ⟨12, 1, 11, 1, 8⟩,
  ⟨12, 1, 14, 1, 4⟩,
  ⟨12, 3, 14, 3, (32/27)⟩,
  ⟨12, 3, 18, 3, (4/27)⟩,
  ⟨13, 1, 5, 1, (21/5)⟩,
  ⟨13, 1, 11, 1, (21/5)⟩,
  ⟨13, 1, 14, 1, (6/5)⟩,
  ⟨13, 1, 16, 1, (12/5)⟩,
  ⟨13, 3, 8, 3, (28/99)⟩,
  ⟨13, 3, 14, 3, (32/99)⟩,
  ⟨13, 3, 16, 3, (64/99)⟩,
  ⟨13, 3, 18, 3, (8/99)⟩,
  ⟨0, 14, 3, 14, (3/7)⟩,
  ⟨0, 14, 6, 14, (16/49)⟩,
  ⟨14, 1, 6, 1, (224/113)⟩,
  ⟨14, 1, 12, 1, (240/113)⟩,
  ⟨14, 1, 13, 1, (1024/113)⟩,
  ⟨1, 14, 6, 14, (28/339)⟩,
  ⟨14, 1, 15, 1, (64/113)⟩,
  ⟨14, 1, 17, 1, (256/113)⟩,
  ⟨14, 3, 9, 3, (7/82)⟩,
  ⟨14, 3, 15, 3, (9/82)⟩,
  ⟨14, 3, 17, 3, (32/41)⟩,
  ⟨14, 3, 19, 3, (1/41)⟩,
  ⟨15, 1, 14, 1, (160/9)⟩,
  ⟨15, 1, 18, 1, (20/9)⟩,
  ⟨15, 3, 18, 3, (2/3)⟩,
  ⟨16, 1, 7, 1, 7⟩,
  ⟨16, 1, 13, 1, 7⟩,
  ⟨16, 1, 17, 1, 2⟩,
  ⟨16, 3, 17, 3, 1⟩,
  ⟨17, 1, 8, 1, (140/33)⟩,
  ⟨17, 1, 14, 1, (160/33)⟩,
  ⟨17, 1, 16, 1, (320/33)⟩,
  ⟨17, 1, 18, 1, (40/33)⟩,
  ⟨17, 3, 18, 3, (2/3)⟩,
  ⟨18, 1, 9, 1, (84/41)⟩,
  ⟨18, 1, 15, 1, (108/41)⟩,
  ⟨18, 1, 17, 1, (768/41)⟩,
  ⟨18, 1, 19, 1, (24/41)⟩,
  ⟨18, 3, 19, 3, (1/3)⟩,
  ⟨19, 1, 18, 1, 28⟩]

theorem cf24Cubing_length : cf24Cubing.length = 141 := by rfl

set_option maxRecDepth 100000 in
/-- Every reaction of `cf24Cubing` is non-autocatalytic. -/
theorem cf24Cubing_isNAP : IsNAP cf24Cubing := by
  first
    | decide
    | simp (config := {decide := true}) [IsNAP, Reaction.IsNAP, Reaction.net, cf24Cubing]

/-- All rates of `cf24Cubing` are positive. -/
theorem cf24Cubing_ratesPos : RatesPos cf24Cubing := by
  simp only [RatesPos, cf24Cubing, List.forall_mem_cons]
  norm_num

/-! ### Faithfulness on the Veronese image

For each cubed variable, the balance field of `cf24Cubing` evaluated at `v = cubedLift x`
equals the chain-rule derivative `Σ_j α_j (v_α / x_j) · r2Field x j` expanded as a polynomial
(these are exactly the right-hand sides of `CF24.napField_chain_v1 … v20`). -/

theorem cf24Cubing_faithful_1 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 0 = -12*(x 0)^4*(x 1)^2 + 21*(x 0)^4*(x 1)*(x 2) - 6*(x 0)^4*(x 1)*(x 3) := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

theorem cf24Cubing_faithful_2 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 1 = -12*(x 0)^4*(x 1)^2 + 21*(x 0)^4*(x 1)*(x 2) - 6*(x 0)^4*(x 1)*(x 3) - 24*(x 0)^3*(x 1)^3 + 42*(x 0)^3*(x 1)^2*(x 2) - 12*(x 0)^3*(x 1)^2*(x 3) := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

theorem cf24Cubing_faithful_3 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 2 = 24*(x 0)^4*(x 1)^2 - 48*(x 0)^4*(x 1)*(x 2) + 96*(x 0)^4*(x 1)*(x 3) - 3*(x 0)^4*(x 2)*(x 3) - 24*(x 0)^3*(x 1)^2*(x 2) + 42*(x 0)^3*(x 1)*(x 2)^2 - 12*(x 0)^3*(x 1)*(x 2)*(x 3) := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

theorem cf24Cubing_faithful_4 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 3 = 6*(x 0)^4*(x 1)*(x 2) - 84*(x 0)^4*(x 1)*(x 3) + 3*(x 0)^4*(x 2)*(x 3) - 24*(x 0)^3*(x 1)^2*(x 3) + 42*(x 0)^3*(x 1)*(x 2)*(x 3) - 12*(x 0)^3*(x 1)*(x 3)^2 := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

theorem cf24Cubing_faithful_5 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 4 = -24*(x 0)^3*(x 1)^3 + 42*(x 0)^3*(x 1)^2*(x 2) - 12*(x 0)^3*(x 1)^2*(x 3) - 12*(x 0)^2*(x 1)^4 + 21*(x 0)^2*(x 1)^3*(x 2) - 6*(x 0)^2*(x 1)^3*(x 3) := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

theorem cf24Cubing_faithful_6 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 5 = 48*(x 0)^3*(x 1)^3 - 120*(x 0)^3*(x 1)^2*(x 2) + 192*(x 0)^3*(x 1)^2*(x 3) + 42*(x 0)^3*(x 1)*(x 2)^2 - 18*(x 0)^3*(x 1)*(x 2)*(x 3) - 24*(x 0)^2*(x 1)^3*(x 2) + 42*(x 0)^2*(x 1)^2*(x 2)^2 - 12*(x 0)^2*(x 1)^2*(x 2)*(x 3) := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

theorem cf24Cubing_faithful_7 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 6 = 12*(x 0)^3*(x 1)^2*(x 2) - 192*(x 0)^3*(x 1)^2*(x 3) + 48*(x 0)^3*(x 1)*(x 2)*(x 3) - 12*(x 0)^3*(x 1)*(x 3)^2 - 24*(x 0)^2*(x 1)^3*(x 3) + 42*(x 0)^2*(x 1)^2*(x 2)*(x 3) - 12*(x 0)^2*(x 1)^2*(x 3)^2 := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

theorem cf24Cubing_faithful_8 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 7 = 48*(x 0)^3*(x 1)^2*(x 2) - 96*(x 0)^3*(x 1)*(x 2)^2 + 192*(x 0)^3*(x 1)*(x 2)*(x 3) - 6*(x 0)^3*(x 2)^2*(x 3) - 12*(x 0)^2*(x 1)^2*(x 2)^2 + 21*(x 0)^2*(x 1)*(x 2)^3 - 6*(x 0)^2*(x 1)*(x 2)^2*(x 3) := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

theorem cf24Cubing_faithful_9 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 8 = 48*(x 0)^3*(x 1)^2*(x 3) + 12*(x 0)^3*(x 1)*(x 2)^2 - 264*(x 0)^3*(x 1)*(x 2)*(x 3) + 192*(x 0)^3*(x 1)*(x 3)^2 + 6*(x 0)^3*(x 2)^2*(x 3) - 6*(x 0)^3*(x 2)*(x 3)^2 - 24*(x 0)^2*(x 1)^2*(x 2)*(x 3) + 42*(x 0)^2*(x 1)*(x 2)^2*(x 3) - 12*(x 0)^2*(x 1)*(x 2)*(x 3)^2 := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

theorem cf24Cubing_faithful_10 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 9 = 12*(x 0)^3*(x 1)*(x 2)*(x 3) - 168*(x 0)^3*(x 1)*(x 3)^2 + 6*(x 0)^3*(x 2)*(x 3)^2 - 12*(x 0)^2*(x 1)^2*(x 3)^2 + 21*(x 0)^2*(x 1)*(x 2)*(x 3)^2 - 6*(x 0)^2*(x 1)*(x 3)^3 := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

theorem cf24Cubing_faithful_11 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 10 = -12*(x 0)^2*(x 1)^4 + 21*(x 0)^2*(x 1)^3*(x 2) - 6*(x 0)^2*(x 1)^3*(x 3) := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

theorem cf24Cubing_faithful_12 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 11 = 24*(x 0)^2*(x 1)^4 - 72*(x 0)^2*(x 1)^3*(x 2) + 96*(x 0)^2*(x 1)^3*(x 3) + 42*(x 0)^2*(x 1)^2*(x 2)^2 - 15*(x 0)^2*(x 1)^2*(x 2)*(x 3) := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

theorem cf24Cubing_faithful_13 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 12 = 6*(x 0)^2*(x 1)^3*(x 2) - 108*(x 0)^2*(x 1)^3*(x 3) + 45*(x 0)^2*(x 1)^2*(x 2)*(x 3) - 12*(x 0)^2*(x 1)^2*(x 3)^2 := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

theorem cf24Cubing_faithful_14 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 13 = 48*(x 0)^2*(x 1)^3*(x 2) - 108*(x 0)^2*(x 1)^2*(x 2)^2 + 192*(x 0)^2*(x 1)^2*(x 2)*(x 3) + 21*(x 0)^2*(x 1)*(x 2)^3 - 12*(x 0)^2*(x 1)*(x 2)^2*(x 3) := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

theorem cf24Cubing_faithful_15 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 14 = 48*(x 0)^2*(x 1)^3*(x 3) + 12*(x 0)^2*(x 1)^2*(x 2)^2 - 288*(x 0)^2*(x 1)^2*(x 2)*(x 3) + 192*(x 0)^2*(x 1)^2*(x 3)^2 + 48*(x 0)^2*(x 1)*(x 2)^2*(x 3) - 18*(x 0)^2*(x 1)*(x 2)*(x 3)^2 := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

theorem cf24Cubing_faithful_16 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 15 = 12*(x 0)^2*(x 1)^2*(x 2)*(x 3) - 180*(x 0)^2*(x 1)^2*(x 3)^2 + 27*(x 0)^2*(x 1)*(x 2)*(x 3)^2 - 6*(x 0)^2*(x 1)*(x 3)^3 := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

theorem cf24Cubing_faithful_17 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 16 = 24*(x 0)^2*(x 1)^2*(x 2)^2 - 48*(x 0)^2*(x 1)*(x 2)^3 + 96*(x 0)^2*(x 1)*(x 2)^2*(x 3) - 3*(x 0)^2*(x 2)^3*(x 3) := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

theorem cf24Cubing_faithful_18 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 17 = 48*(x 0)^2*(x 1)^2*(x 2)*(x 3) + 6*(x 0)^2*(x 1)*(x 2)^3 - 180*(x 0)^2*(x 1)*(x 2)^2*(x 3) + 192*(x 0)^2*(x 1)*(x 2)*(x 3)^2 + 3*(x 0)^2*(x 2)^3*(x 3) - 6*(x 0)^2*(x 2)^2*(x 3)^2 := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

theorem cf24Cubing_faithful_19 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 18 = 24*(x 0)^2*(x 1)^2*(x 3)^2 + 12*(x 0)^2*(x 1)*(x 2)^2*(x 3) - 216*(x 0)^2*(x 1)*(x 2)*(x 3)^2 + 96*(x 0)^2*(x 1)*(x 3)^3 + 6*(x 0)^2*(x 2)^2*(x 3)^2 - 3*(x 0)^2*(x 2)*(x 3)^3 := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

theorem cf24Cubing_faithful_20 (x : Fin 4 → ℝ) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) 19 = 6*(x 0)^2*(x 1)*(x 2)*(x 3)^2 - 84*(x 0)^2*(x 1)*(x 3)^3 + 3*(x 0)^2*(x 2)*(x 3)^3 := by
  simp (config := {decide := true}) [balanceField, cf24Cubing, Reaction.net, CF24.cubedLift]
  push_cast
  ring

/-- On the Veronese image the certified protocol agrees with the per-monomial rewriting
`CF24.napField` of the paper (which is not itself a protocol: its pair sums do not vanish). -/
theorem cf24Cubing_eq_napField_on_cubed (x : Fin 4 → ℝ) (i : Fin 20) :
    balanceField cf24Cubing (fun j => CF24.cubedLift j x) i
      = CF24.napField (fun j => CF24.cubedLift j x) i := by
  fin_cases i
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 0 = CF24.napField (fun j => CF24.cubedLift j x) 0
    linear_combination (cf24Cubing_faithful_1 x) - (CF24.napField_chain_v1 x)
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 1 = CF24.napField (fun j => CF24.cubedLift j x) 1
    linear_combination (cf24Cubing_faithful_2 x) - (CF24.napField_chain_v2 x)
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 2 = CF24.napField (fun j => CF24.cubedLift j x) 2
    linear_combination (cf24Cubing_faithful_3 x) - (CF24.napField_chain_v3 x)
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 3 = CF24.napField (fun j => CF24.cubedLift j x) 3
    linear_combination (cf24Cubing_faithful_4 x) - (CF24.napField_chain_v4 x)
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 4 = CF24.napField (fun j => CF24.cubedLift j x) 4
    linear_combination (cf24Cubing_faithful_5 x) - (CF24.napField_chain_v5 x)
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 5 = CF24.napField (fun j => CF24.cubedLift j x) 5
    linear_combination (cf24Cubing_faithful_6 x) - (CF24.napField_chain_v6 x)
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 6 = CF24.napField (fun j => CF24.cubedLift j x) 6
    linear_combination (cf24Cubing_faithful_7 x) - (CF24.napField_chain_v7 x)
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 7 = CF24.napField (fun j => CF24.cubedLift j x) 7
    linear_combination (cf24Cubing_faithful_8 x) - (CF24.napField_chain_v8 x)
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 8 = CF24.napField (fun j => CF24.cubedLift j x) 8
    linear_combination (cf24Cubing_faithful_9 x) - (CF24.napField_chain_v9 x)
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 9 = CF24.napField (fun j => CF24.cubedLift j x) 9
    linear_combination (cf24Cubing_faithful_10 x) - (CF24.napField_chain_v10 x)
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 10 = CF24.napField (fun j => CF24.cubedLift j x) 10
    linear_combination (cf24Cubing_faithful_11 x) - (CF24.napField_chain_v11 x)
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 11 = CF24.napField (fun j => CF24.cubedLift j x) 11
    linear_combination (cf24Cubing_faithful_12 x) - (CF24.napField_chain_v12 x)
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 12 = CF24.napField (fun j => CF24.cubedLift j x) 12
    linear_combination (cf24Cubing_faithful_13 x) - (CF24.napField_chain_v13 x)
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 13 = CF24.napField (fun j => CF24.cubedLift j x) 13
    linear_combination (cf24Cubing_faithful_14 x) - (CF24.napField_chain_v14 x)
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 14 = CF24.napField (fun j => CF24.cubedLift j x) 14
    linear_combination (cf24Cubing_faithful_15 x) - (CF24.napField_chain_v15 x)
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 15 = CF24.napField (fun j => CF24.cubedLift j x) 15
    linear_combination (cf24Cubing_faithful_16 x) - (CF24.napField_chain_v16 x)
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 16 = CF24.napField (fun j => CF24.cubedLift j x) 16
    linear_combination (cf24Cubing_faithful_17 x) - (CF24.napField_chain_v17 x)
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 17 = CF24.napField (fun j => CF24.cubedLift j x) 17
    linear_combination (cf24Cubing_faithful_18 x) - (CF24.napField_chain_v18 x)
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 18 = CF24.napField (fun j => CF24.cubedLift j x) 18
    linear_combination (cf24Cubing_faithful_19 x) - (CF24.napField_chain_v19 x)
  · show balanceField cf24Cubing (fun j => CF24.cubedLift j x) 19 = CF24.napField (fun j => CF24.cubedLift j x) 19
    linear_combination (cf24Cubing_faithful_20 x) - (CF24.napField_chain_v20 x)

end NAPProtocol
end Ripple
