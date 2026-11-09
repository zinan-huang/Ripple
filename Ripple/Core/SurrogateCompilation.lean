/-
  Ripple.Core.SurrogateCompilation — joint bounded surrogate compilation ([BAC] §3, §4.2)

  [BAC] = Chen and Huang, *Bounded Analog Complexity* (DNA 32). Result numbers are those of the
  DNA 32 version, as in `docs/refactor/BC.md`. The journal draft renumbers them;
  `docs/papers/BAC-journal.md` keys each result by its LaTeX label: Prop 3.2 = `prop:dcr-limit`,
  Thm 3.3 = `thm:same-class`, Thm 3.4 = `thm:pole-computable`, Lemma 4.1 = `thm:time-length`,
  Lemma 4.3 = `lem:state-bound`, Thm 4.5 = `thm:compilation` (product-clock form
  `thm:compilation-product`), Thm 4.6 = `thm:poly-equiv`.
  Paper proofs, repairs and the choice of route: `docs/refactor/BC.md`.

  Construction (BC.md §1.4, the joint form of [BAC] Construction 3.1). For a ℚ-PIVP
  `y' = F(y)` in dimension `d` and an even `N ≥ deg F`:
  - one time change for all coordinates, `dt/dτ = 1/P(y)`, `P(y) = 1 + Σᵢ yᵢ^N ≥ 1`;
  - surrogates `W_a = y^a / P(y)` for every multi-index `a` with `|a| ≤ N`; `|W_a| ≤ 1`;
  - the compiled field (a ℚ-polynomial, cubic in the surrogates):
      `W_a' = Σᵢ aᵢ W_{a−eᵢ} Fᵢ^W − N W_a Σᵢ W_{(N−1)eᵢ} Fᵢ^W`, with `q^W = Σ_β c_β W_β`
      (so `q^W(W(y)) = q(y)/P(y)`);
  - the output is kept as `x̄ = y_o ∘ s` with `x̄' = F_o^W` (`jointSurrogateCompile`).
  The solution of the compiled system is the explicit composition `τ ↦ Φ(y(s(τ)))`, where `s`
  inverts the clock `θ(t) = ∫₀ᵗ P(y)` (`exists_inverse_timeChange`); it exists on all of
  `[0, ∞)` and `s → ∞`, so the output keeps its limit ([BAC] Prop 3.2, `T* = ∞`).

  Main results: `PolyPIVP.jointSurrogateCompile_solution` (Construction 3.1 + Prop 3.2),
  `bounded_compilation_certified` ([BAC] Thm 3.3), `bounded_compilation_polyTime_certified`
  ([BAC] Thm 4.5) and `jointDim_le` (its dimension clause).
-/

import Ripple.Core.TimeChange
import Ripple.Core.ArcLength
import Ripple.LPP.VVariable
import Mathlib.Data.Sym.Card
import Mathlib.Data.Finsupp.Multiset

namespace Ripple

open MvPolynomial Filter

variable {d : ℕ}

/-! ## Surrogate indices, clock and surrogates -/

/-- Multi-indices of total degree `≤ N` on `d` variables (BC.md §1.4.1). -/
abbrev SurrogateIndex (d N : ℕ) := {a : MIndex d N // a.degree ≤ N}

/-- Coordinates of the compiled system: `none` is the kept output (or the physical time in
`jointClockCompile`), `some a` the surrogate `W_a`. -/
abbrev CompiledIndex (d N : ℕ) := Option (SurrogateIndex d N)

/-- Dimension of the compiled system: one extra coordinate plus one surrogate per multi-index. -/
abbrev jointDim (d N : ℕ) : ℕ := Fintype.card (CompiledIndex d N)

/-- The joint clock `P(y) = 1 + Σᵢ yᵢ^N`, so that `dt/dτ = 1/P`. -/
noncomputable def jointClock (N : ℕ) (y : Fin d → ℝ) : ℝ := 1 + ∑ i, y i ^ N

/-- The surrogate `W_a(y) = y^a / P(y)`. -/
noncomputable def jointSurrogate (N : ℕ) (a : SurrogateIndex d N) (y : Fin d → ℝ) : ℝ :=
  a.1.eval y / jointClock N y

theorem jointClock_ge_one {N : ℕ} (hN : Even N) (y : Fin d → ℝ) : 1 ≤ jointClock N y := by
  unfold jointClock
  have : 0 ≤ ∑ i, y i ^ N := Finset.sum_nonneg fun i _ => hN.pow_nonneg (y i)
  linarith

theorem jointClock_pos {N : ℕ} (hN : Even N) (y : Fin d → ℝ) : 0 < jointClock N y :=
  lt_of_lt_of_le one_pos (jointClock_ge_one hN y)

theorem continuous_jointClock (N : ℕ) : Continuous (jointClock (d := d) N) :=
  continuous_const.add (continuous_finset_sum _ fun i _ => (continuous_apply i).pow N)

/-- `|y^a| ≤ P(y)` for `|a| ≤ N`, `N` even (BC.md §1.4.2). -/
theorem abs_eval_le_jointClock {N : ℕ} (hN : Even N) (a : MIndex d N) (ha : a.degree ≤ N)
    (y : Fin d → ℝ) : |a.eval y| ≤ jointClock N y := by
  by_cases hy : ‖y‖ ≤ 1
  · have h1 : |a.eval y| ≤ 1 := by
      have := a.eval_bounded y 1 one_pos fun i =>
        (by simpa [Real.norm_eq_abs] using norm_le_pi_norm y i : |y i| ≤ ‖y‖).trans hy
      simpa using this
    exact h1.trans (jointClock_ge_one hN y)
  · push Not at hy
    have hM : 0 < ‖y‖ := lt_trans one_pos hy
    have hb := a.eval_bounded y ‖y‖ hM fun i => by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm y i
    have hpow : ‖y‖ ^ a.degree ≤ ‖y‖ ^ N := pow_le_pow_right₀ hy.le ha
    obtain ⟨j, hj⟩ : ∃ j, ‖y‖ ≤ |y j| := by
      by_contra h
      push Not at h
      have : ‖y‖ < ‖y‖ := (pi_norm_lt_iff hM).2 fun i => by
        simpa [Real.norm_eq_abs] using h i
      exact lt_irrefl _ this
    have hjN : ‖y‖ ^ N ≤ y j ^ N :=
      (pow_le_pow_left₀ (norm_nonneg _) hj N).trans_eq (hN.pow_abs (y j))
    have hsum : y j ^ N ≤ ∑ i, y i ^ N :=
      Finset.single_le_sum (fun i _ => hN.pow_nonneg (y i)) (Finset.mem_univ j)
    unfold jointClock
    linarith

/-- The surrogates lie in `[-1, 1]` ([BAC] Construction 3.1 Step 1, repaired for signs: BC.md
§1.2 erratum E1; nonnegativity needs `y ≥ 0` or an even index, boundedness does not). -/
theorem jointSurrogate_abs_le_one {N : ℕ} (hN : Even N) (a : SurrogateIndex d N)
    (y : Fin d → ℝ) : |jointSurrogate N a y| ≤ 1 := by
  unfold jointSurrogate
  rw [abs_div, abs_of_pos (jointClock_pos hN y), div_le_one (jointClock_pos hN y)]
  exact abs_eval_le_jointClock hN a.1 a.2 y

theorem continuous_jointSurrogate {N : ℕ} (hN : Even N) (a : SurrogateIndex d N) :
    Continuous (jointSurrogate N a) := by
  unfold jointSurrogate MIndex.eval
  exact (continuous_finsetProd _ fun i _ => (continuous_apply i).pow _).div
    (continuous_jointClock N) fun y => ne_of_gt (jointClock_pos hN y)

/-! ## The special indices `0`, `a − eᵢ`, `(N−1)eᵢ` -/

/-- The zero multi-index; `W₀ = 1/P = dt/dτ`. -/
def SurrogateIndex.zero (d N : ℕ) : SurrogateIndex d N :=
  ⟨MIndex.zero' d N, by simp [MIndex.degree, MIndex.zero']⟩

/-- `a − eᵢ` (exponent `aᵢ − 1` in `ℕ`, so `a` itself when `aᵢ = 0`; its coefficient `aᵢ`
then vanishes). -/
def SurrogateIndex.decr {N : ℕ} (a : SurrogateIndex d N) (i : Fin d) : SurrogateIndex d N :=
  ⟨fun j => if j = i then ⟨(a.1 i : ℕ) - 1, by have := (a.1 i).isLt; omega⟩ else a.1 j, by
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) a.2
    dsimp only
    split_ifs with h
    · subst h; exact Nat.sub_le _ _
    · exact le_rfl⟩

theorem SurrogateIndex.decr_eval {N : ℕ} (a : SurrogateIndex d N) (i : Fin d)
    (x : Fin d → ℝ) :
    (a.decr i).1.eval x =
      (∏ j ∈ Finset.univ.erase i, x j ^ (a.1 j : ℕ)) * x i ^ ((a.1 i : ℕ) - 1) := by
  simp only [MIndex.eval, SurrogateIndex.decr]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm]
  refine congr_arg₂ (· * ·) ?_ ?_
  · apply Finset.prod_congr rfl
    intro j hj; simp [(Finset.mem_erase.mp hj).1]
  · simp

/-- `(N − 1) eᵢ`; `y^{(N−1)eᵢ} = yᵢ^{N−1}` enters through `∂ᵢ P = N yᵢ^{N−1}`. -/
def SurrogateIndex.powIdx (N : ℕ) (i : Fin d) : SurrogateIndex d N :=
  ⟨fun j => if j = i then ⟨N - 1, by omega⟩ else 0, by
    unfold MIndex.degree
    calc ∑ j, ((if j = i then (⟨N - 1, by omega⟩ : Fin (N + 1)) else 0 : Fin (N + 1)) : ℕ)
        = ∑ j, (if j = i then N - 1 else 0) :=
          Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
      _ = N - 1 := by simp
      _ ≤ N := Nat.sub_le _ _⟩

theorem SurrogateIndex.powIdx_eval (N : ℕ) (i : Fin d) (x : Fin d → ℝ) :
    (SurrogateIndex.powIdx N i).1.eval x = x i ^ (N - 1) := by
  simp only [MIndex.eval, SurrogateIndex.powIdx]
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

theorem SurrogateIndex.zero_eval (d N : ℕ) (x : Fin d → ℝ) :
    (SurrogateIndex.zero d N).1.eval x = 1 :=
  MIndex.eval_zero' x

/-! ## The lifted field `q^W` -/

/-- `q^W = Σ_{|β| ≤ N} c_β W_β` for `q = Σ_β c_β y^β`. -/
noncomputable def surrogateLift (N : ℕ) (q : MvPolynomial (Fin d) ℚ) :
    MvPolynomial (CompiledIndex d N) ℚ :=
  ∑ a : SurrogateIndex d N, C (q.coeff a.1.toFinsupp) * X (some a)

theorem coeff_toFinsupp_eq_zero {N : ℕ} {q : MvPolynomial (Fin d) ℚ}
    (hq : q.totalDegree ≤ N) {b : MIndex d N} (hb : ¬ b.degree ≤ N) :
    q.coeff b.toFinsupp = 0 := by
  by_contra h
  apply hb
  have hmem : b.toFinsupp ∈ q.support := MvPolynomial.mem_support_iff.mpr h
  have h1 := MvPolynomial.le_totalDegree hmem
  have h2 : (b.toFinsupp.sum fun _ e => e) = b.degree := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simp [MIndex.degree]
  omega

/-- `q^W(W(y)) = q(y)/P(y)` when `deg q ≤ N`. -/
theorem surrogateLift_eval₂ {N : ℕ} {q : MvPolynomial (Fin d) ℚ} (hq : q.totalDegree ≤ N)
    (y : Fin d → ℝ) (v : CompiledIndex d N → ℝ)
    (hv : ∀ a, v (some a) = jointSurrogate N a y) :
    (surrogateLift N q).eval₂ (Rat.castHom ℝ) v = q.eval₂ (Rat.castHom ℝ) y / jointClock N y := by
  rw [eval₂_as_mindex_sum q hq y, Finset.sum_div,
    ← Fintype.sum_subtype_add_sum_subtype (fun b : MIndex d N => b.degree ≤ N)
      (fun b => (↑(q.coeff b.toFinsupp) * b.eval y) / jointClock N y)]
  have h2 : ∑ b : {b : MIndex d N // ¬ b.degree ≤ N},
      (↑(q.coeff b.1.toFinsupp) * b.1.eval y) / jointClock N y = 0 :=
    Finset.sum_eq_zero fun b _ => by rw [coeff_toFinsupp_eq_zero hq b.2]; simp
  rw [h2, add_zero]
  simp only [surrogateLift, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_X, hv]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [jointSurrogate, mul_div_assoc]

/-! ## The compiled field -/

/-- The compiled surrogate line ([BAC] Construction 3.1 Steps 2–3, joint form, BC.md §1.4.1):
`W_a' = Σᵢ aᵢ W_{a−eᵢ} Fᵢ^W − N W_a Σᵢ W_{(N−1)eᵢ} Fᵢ^W`. -/
noncomputable def surrogateField (P : PolyPIVP d) (N : ℕ) (a : SurrogateIndex d N) :
    MvPolynomial (CompiledIndex d N) ℚ :=
  ∑ i, C (((a.1 i : ℕ) : ℚ)) * X (some (a.decr i)) * surrogateLift N (P.field i) -
    C ((N : ℚ)) * X (some a) *
      ∑ i, X (some (SurrogateIndex.powIdx N i)) * surrogateLift N (P.field i)

/-- The rational initial value of the surrogate `W_a`: `y₀^a / (1 + Σ y₀ᵢ^N)`. -/
noncomputable def surrogateInit (P : PolyPIVP d) (N : ℕ) (a : SurrogateIndex d N) : ℚ :=
  (∏ i, P.init i ^ (a.1 i : ℕ)) / (1 + ∑ i, P.init i ^ N)

theorem surrogateInit_cast (P : PolyPIVP d) (N : ℕ) (a : SurrogateIndex d N) :
    ((surrogateInit P N a : ℚ) : ℝ) = jointSurrogate N a (fun i => (P.init i : ℝ)) := by
  simp [surrogateInit, jointSurrogate, jointClock, MIndex.eval]

/-- Field algebra used at the end of `hasDerivAt_jointSurrogate`. -/
theorem jointSurrogate_deriv_algebra (A B m Pz N : ℝ) (hP0 : Pz ≠ 0) :
    A / Pz ^ 2 - N * (m / Pz) * (B / Pz ^ 2) =
      ((A / Pz) * Pz - m * (N * B / Pz)) / Pz ^ 2 := by
  field_simp

/-- The derivative identity (BC.md §1.4.4): along a curve with `z' = F(z)/P(z)`, every
surrogate `W_a(z)` satisfies the compiled surrogate line. -/
theorem hasDerivAt_jointSurrogate (P : PolyPIVP d) {N : ℕ} (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N) (a : SurrogateIndex d N)
    (z : ℝ → Fin d → ℝ) (τ : ℝ)
    (hz : ∀ i, HasDerivAt (fun σ => z σ i)
      (P.evalField (z τ) i / jointClock N (z τ)) τ)
    (v : CompiledIndex d N → ℝ) (hv : ∀ b, v (some b) = jointSurrogate N b (z τ)) :
    HasDerivAt (fun σ => jointSurrogate N a (z σ))
      ((surrogateField P N a).eval₂ (Rat.castHom ℝ) v) τ := by
  have hP0 : jointClock N (z τ) ≠ 0 := ne_of_gt (jointClock_pos hN (z τ))
  have hm := hasDerivAt_monomial a.1 z
    (fun i => P.evalField (z τ) i / jointClock N (z τ)) τ hz
  have hP : HasDerivAt (fun σ => jointClock N (z σ))
      (∑ i, ((N : ℕ) : ℝ) * z τ i ^ (N - 1) *
        (P.evalField (z τ) i / jointClock N (z τ))) τ := by
    have := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hz i).fun_pow N)).const_add 1
    exact this
  have hq := hm.div hP hP0
  have hl : ∀ i, (surrogateLift N (P.field i)).eval₂ (Rat.castHom ℝ) v =
      P.evalField (z τ) i / jointClock N (z τ) :=
    fun i => surrogateLift_eval₂ (hdeg i) (z τ) v hv
  have s1 : ∑ k, ((a.1 k : ℕ) : ℝ) * ((a.decr k).1.eval (z τ) / jointClock N (z τ)) *
        (P.evalField (z τ) k / jointClock N (z τ)) =
      (∑ k, ((a.1 k : ℕ) : ℝ) * (a.decr k).1.eval (z τ) * P.evalField (z τ) k) /
        jointClock N (z τ) ^ 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring
  have s2 : ∑ i, ((SurrogateIndex.powIdx N i).1.eval (z τ) / jointClock N (z τ)) *
        (P.evalField (z τ) i / jointClock N (z τ)) =
      (∑ i, (SurrogateIndex.powIdx N i).1.eval (z τ) * P.evalField (z τ) i) /
        jointClock N (z τ) ^ 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by ring
  have s3 : (∑ k, (∏ j ∈ Finset.univ.erase k, z τ j ^ (a.1 j : ℕ)) *
      (((a.1 k : ℕ) : ℝ) * z τ k ^ ((a.1 k : ℕ) - 1) *
        (P.evalField (z τ) k / jointClock N (z τ)))) =
      (∑ k, ((a.1 k : ℕ) : ℝ) * (a.decr k).1.eval (z τ) * P.evalField (z τ) k) /
        jointClock N (z τ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [SurrogateIndex.decr_eval]
    ring
  have s4 : (∑ i, ((N : ℕ) : ℝ) * z τ i ^ (N - 1) *
        (P.evalField (z τ) i / jointClock N (z τ))) =
      (N : ℝ) * (∑ i, (SurrogateIndex.powIdx N i).1.eval (z τ) * P.evalField (z τ) i) /
        jointClock N (z τ) := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SurrogateIndex.powIdx_eval]
    ring
  have hval : (surrogateField P N a).eval₂ (Rat.castHom ℝ) v =
      (∑ k, ((a.1 k : ℕ) : ℝ) * (a.decr k).1.eval (z τ) * P.evalField (z τ) k) /
          jointClock N (z τ) ^ 2 -
        (N : ℝ) * (a.1.eval (z τ) / jointClock N (z τ)) *
          ((∑ i, (SurrogateIndex.powIdx N i).1.eval (z τ) * P.evalField (z τ) i) /
            jointClock N (z τ) ^ 2) := by
    simp only [surrogateField, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_sum, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, hv, hl,
      jointSurrogate, eq_ratCast, Rat.cast_natCast]
    rw [s1, s2]
  rw [hval, jointSurrogate_deriv_algebra _ _ _ _ _ hP0, ← s3, ← s4]
  exact hq

/-! ## Reindexing a system over a finite index type to `Fin` -/

/-- A `PolyPIVP` from a field, initial value and output over a finite index type, reindexed by
`Fintype.equivFin`. -/
noncomputable def PolyPIVP.ofIndexed {ι : Type*} [Fintype ι] (G : ι → MvPolynomial ι ℚ)
    (x₀ : ι → ℚ) (o : ι) : PolyPIVP (Fintype.card ι) where
  field j := rename (Fintype.equivFin ι) (G ((Fintype.equivFin ι).symm j))
  init j := x₀ ((Fintype.equivFin ι).symm j)
  output := Fintype.equivFin ι o

/-- A curve over the index type that solves the indexed system gives a solution of the
reindexed `PolyPIVP`. -/
theorem PolyPIVP.ofIndexed_solution {ι : Type*} [Fintype ι] (G : ι → MvPolynomial ι ℚ)
    (x₀ : ι → ℚ) (o : ι) (Z : ℝ → ι → ℝ) (h0 : ∀ k, Z 0 k = (x₀ k : ℝ))
    (hZ : ∀ τ, 0 ≤ τ → ∀ k, HasDerivAt (fun σ => Z σ k)
      ((G k).eval₂ (Rat.castHom ℝ) (Z τ)) τ) :
    ∃ sol : PIVP.Solution (PolyPIVP.ofIndexed G x₀ o).toPIVP,
      sol.trajectory = fun τ j => Z τ ((Fintype.equivFin ι).symm j) := by
  refine ⟨{
    trajectory := fun τ j => Z τ ((Fintype.equivFin ι).symm j)
    init_cond := by
      funext j
      simp [PolyPIVP.toPIVP, PolyPIVP.ofIndexed, h0]
    is_solution := fun τ hτ => by
      refine hasDerivAt_pi.mpr fun j => ?_
      show HasDerivAt (fun σ => Z σ ((Fintype.equivFin ι).symm j))
        ((rename (Fintype.equivFin ι) (G ((Fintype.equivFin ι).symm j))).eval₂
          (Rat.castHom ℝ) (fun j => Z τ ((Fintype.equivFin ι).symm j))) τ
      rw [MvPolynomial.eval₂_rename]
      convert hZ τ hτ ((Fintype.equivFin ι).symm j) using 2
      funext k
      simp [Function.comp] }, rfl⟩

/-! ## The compiled system with the kept output ([BAC] Construction 3.1, joint form) -/

/-- Compiled field: the kept output `x̄' = F_o^W` and the surrogate lines. -/
noncomputable def jointField (P : PolyPIVP d) (N : ℕ) :
    CompiledIndex d N → MvPolynomial (CompiledIndex d N) ℚ
  | none => surrogateLift N (P.field P.output)
  | some a => surrogateField P N a

/-- Compiled initial value: `y₀,o` and `y₀^a / P(y₀)`, all rational. -/
noncomputable def jointInit (P : PolyPIVP d) (N : ℕ) : CompiledIndex d N → ℚ
  | none => P.init P.output
  | some a => surrogateInit P N a

/-- [BAC] Construction 3.1, joint form (BC.md §1.4.1): the bounded surrogate compilation of `P`
with the kept output. ℚ-polynomial field (cubic in the surrogates), rational initial value
`(y₀,o, (y₀^a / P(y₀))_a)`, output the kept copy of `P`'s output. -/
noncomputable def PolyPIVP.jointSurrogateCompile (P : PolyPIVP d) (N : ℕ) :
    PolyPIVP (jointDim d N) :=
  PolyPIVP.ofIndexed (jointField P N) (jointInit P N) none

/-- The coordinate of the surrogate `W_a` in the compiled system. -/
noncomputable def surrogateCoord {N : ℕ} (a : SurrogateIndex d N) : Fin (jointDim d N) :=
  Fintype.equivFin (CompiledIndex d N) (some a)

theorem jointSurrogateCompile_output (P : PolyPIVP d) (N : ℕ) :
    (P.jointSurrogateCompile N).output = Fintype.equivFin (CompiledIndex d N) none := rfl

/-- [BAC] Thm 4.5 (journal draft `thm:compilation`, Thm 4.4), dimension clause: the compiled
dimension is polynomial in `N` for fixed `d`. The exact count is `jointDim_eq`. -/
theorem jointDim_le (d N : ℕ) : jointDim d N ≤ 1 + (N + 1) ^ d := by
  have h : Fintype.card (SurrogateIndex d N) ≤ Fintype.card (MIndex d N) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  simp only [jointDim, CompiledIndex, Fintype.card_option]
  simp only [MIndex, Fintype.card_fun, Fintype.card_fin] at h
  omega

/-- Multi-indices of degree `≤ N` on `d` variables are the multi-indices of degree exactly `N`
on `d + 1` variables: the slack `N − |a|` is the coordinate `0`. -/
def SurrogateIndex.equivSum (d N : ℕ) :
    SurrogateIndex d N ≃ {P : Fin (d + 1) → ℕ // ∑ i, P i = N} where
  toFun a := ⟨Fin.cons (N - a.1.degree) (fun i => (a.1 i : ℕ)), by
    have h := a.2
    simp only [MIndex.degree] at h ⊢
    rw [Fin.sum_cons]
    omega⟩
  invFun P := ⟨fun i => ⟨P.1 i.succ, by
      have h := P.2
      rw [Fin.sum_univ_succ] at h
      have hi : P.1 i.succ ≤ ∑ j : Fin d, P.1 j.succ :=
        Finset.single_le_sum (f := fun j : Fin d => P.1 j.succ) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i)
      omega⟩, by
      have h := P.2
      rw [Fin.sum_univ_succ] at h
      show ∑ i : Fin d, P.1 i.succ ≤ N
      omega⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    simp
  right_inv P := by
    apply Subtype.ext
    funext i
    have h := P.2
    rw [Fin.sum_univ_succ] at h
    refine Fin.cases ?_ (fun j => ?_) i
    · show N - ∑ k : Fin d, P.1 k.succ = P.1 0
      omega
    · simp

/-- The number of multi-indices of degree `≤ N` on `d` variables is `C(d+N, N)`. -/
theorem card_surrogateIndex (d N : ℕ) :
    Fintype.card (SurrogateIndex d N) = (d + N).choose N := by
  classical
  rw [Fintype.card_congr ((SurrogateIndex.equivSum d N).trans
    (Sym.equivNatSumOfFintype (Fin (d + 1)) N).symm), Sym.card_sym_eq_choose, Fintype.card_fin]
  congr 1
  omega

/-- [BAC] Construction 3.1 and Thm 4.4 (journal draft `constr:surrogates`,
`thm:compilation`), exact dimension: the compiled system has the kept output and one surrogate
per multi-index of degree `≤ N`, so its dimension is `1 + C(d+N, N)`. -/
theorem jointDim_eq (d N : ℕ) : jointDim d N = 1 + (d + N).choose N := by
  simp only [jointDim, CompiledIndex, Fintype.card_option, card_surrogateIndex]
  omega

/-! ## Degree of the compiled field ([BAC] Lemma 3.3, `lem:closure`) -/

/-- `q^W` is linear in the surrogates. -/
theorem surrogateLift_totalDegree_le (N : ℕ) (q : MvPolynomial (Fin d) ℚ) :
    (surrogateLift N q).totalDegree ≤ 1 := by
  unfold surrogateLift
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun a _ => ?_)
  refine (totalDegree_mul _ _).trans (le_of_eq ?_)
  rw [totalDegree_C, totalDegree_X]

/-- A constant times a variable has degree `≤ 1`. -/
theorem totalDegree_C_mul_X_le {σ : Type*} (c : ℚ) (v : σ) :
    (C c * X v : MvPolynomial σ ℚ).totalDegree ≤ 1 :=
  (totalDegree_mul _ _).trans (le_of_eq (by rw [totalDegree_C, totalDegree_X]))

/-- The surrogate lines are cubic: `aᵢ W_{a−eᵢ} Fᵢ^W` has degree `≤ 2` and
`N W_a W_{(N−1)eᵢ} Fᵢ^W` degree `≤ 3`. -/
theorem surrogateField_totalDegree_le (P : PolyPIVP d) (N : ℕ) (a : SurrogateIndex d N) :
    (surrogateField P N a).totalDegree ≤ 3 := by
  unfold surrogateField
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
    have h1 := totalDegree_C_mul_X_le (((a.1 i : ℕ) : ℚ)) (some (a.decr i))
    have h2 := surrogateLift_totalDegree_le N (P.field i)
    exact (totalDegree_mul _ _).trans (by omega)
  · have h1 := totalDegree_C_mul_X_le ((N : ℚ)) (some a)
    have h2 : (∑ i, X (some (SurrogateIndex.powIdx N i)) * surrogateLift N (P.field i) :
        MvPolynomial (CompiledIndex d N) ℚ).totalDegree ≤ 2 := by
      refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
      have h3 := surrogateLift_totalDegree_le N (P.field i)
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X]
      omega
    exact (totalDegree_mul _ _).trans (by omega)

/-- Every line of the compiled field has degree `≤ 3`. -/
theorem jointField_totalDegree_le (P : PolyPIVP d) (N : ℕ) (k : CompiledIndex d N) :
    (jointField P N k).totalDegree ≤ 3 := by
  cases k with
  | none => exact (surrogateLift_totalDegree_le N _).trans (by norm_num)
  | some a => exact surrogateField_totalDegree_le P N a

/-- [BAC] Lemma 3.3 (journal draft `lem:closure`), degree clause: the compiled vector field is a
ℚ-polynomial of total degree at most `3` in every coordinate. (Rational coefficients and the
rational initial value hold by the type `PolyPIVP`; the pushforward identity is
`surrogateLift_eval₂` with `hasDerivAt_jointSurrogate`.) -/
theorem jointSurrogateCompile_totalDegree_le (P : PolyPIVP d) (N : ℕ)
    (j : Fin (jointDim d N)) :
    ((P.jointSurrogateCompile N).field j).totalDegree ≤ 3 :=
  (totalDegree_rename_le _ _).trans (jointField_totalDegree_le P N _)

/-- Every coordinate of the compiled system is the output or a surrogate. -/
theorem jointCoord_cases {N : ℕ} (j : Fin (jointDim d N)) :
    j = Fintype.equivFin (CompiledIndex d N) none ∨ ∃ a, j = surrogateCoord a := by
  obtain ⟨k, rfl⟩ := (Fintype.equivFin (CompiledIndex d N)).surjective j
  cases k with
  | none => exact Or.inl rfl
  | some a => exact Or.inr ⟨a, rfl⟩

/-- The compiled curve over the index type: the output coordinate and the surrogates of
`z τ`. -/
noncomputable def jointCurve (N : ℕ) (o : Fin d) (z : ℝ → Fin d → ℝ) (τ : ℝ) :
    CompiledIndex d N → ℝ
  | none => z τ o
  | some a => jointSurrogate N a (z τ)

/-- [BAC] Construction 3.1 Steps 2–3, joint form (BC.md §1.4.4): a curve `z` with
`z(0) = y₀` and `z' = F(z)/P(z)` on `[0, ∞)` gives the solution
`τ ↦ (z_o(τ), (W_a(z(τ)))_a)` of the compiled system. -/
theorem PolyPIVP.jointSurrogateCompile_solution_of_curve (P : PolyPIVP d) {N : ℕ}
    (hN : Even N) (hdeg : ∀ i, (P.field i).totalDegree ≤ N) (z : ℝ → Fin d → ℝ)
    (hz0 : z 0 = fun i => (P.init i : ℝ))
    (hz : ∀ τ, 0 ≤ τ → ∀ i, HasDerivAt (fun σ => z σ i)
      (P.evalField (z τ) i / jointClock N (z τ)) τ) :
    ∃ sol' : PIVP.Solution (P.jointSurrogateCompile N).toPIVP,
      (∀ τ, sol'.trajectory τ (P.jointSurrogateCompile N).output = z τ P.output) ∧
      (∀ τ (a : SurrogateIndex d N),
        sol'.trajectory τ (surrogateCoord a) = jointSurrogate N a (z τ)) ∧
      (Continuous z → Continuous sol'.trajectory) := by
  have hZ0 : ∀ k, jointCurve N P.output z 0 k = (jointInit P N k : ℝ) := by
    intro k
    cases k with
    | none => simp [jointCurve, jointInit, hz0]
    | some a => simp only [jointCurve, jointInit, hz0, surrogateInit_cast]
  have hZd : ∀ τ, 0 ≤ τ → ∀ k, HasDerivAt (fun σ => jointCurve N P.output z σ k)
      ((jointField P N k).eval₂ (Rat.castHom ℝ) (jointCurve N P.output z τ)) τ := by
    intro τ hτ k
    cases k with
    | none =>
      change HasDerivAt (fun σ => z σ P.output)
        ((surrogateLift N (P.field P.output)).eval₂ (Rat.castHom ℝ)
          (jointCurve N P.output z τ)) τ
      rw [surrogateLift_eval₂ (hdeg _) (z τ) _ (fun _ => rfl)]
      exact hz τ hτ P.output
    | some a =>
      exact hasDerivAt_jointSurrogate P hN hdeg a z τ (hz τ hτ) _ (fun _ => rfl)
  obtain ⟨sol', hsol'⟩ := PolyPIVP.ofIndexed_solution (jointField P N) (jointInit P N) none
    _ hZ0 hZd
  refine ⟨sol', fun τ => ?_, fun τ a => ?_, fun hzc => ?_⟩
  · rw [hsol']
    simp only [jointSurrogateCompile_output, Equiv.symm_apply_apply]
    rfl
  · rw [hsol']
    simp only [surrogateCoord, Equiv.symm_apply_apply]
    rfl
  · rw [hsol']
    refine continuous_pi fun j => ?_
    cases h : (Fintype.equivFin (CompiledIndex d N)).symm j with
    | none => simpa [jointCurve, h] using (continuous_apply P.output).comp hzc
    | some a => simpa [jointCurve, h] using (continuous_jointSurrogate hN a).comp hzc

/-- [BAC] Construction 3.1 + Prop 3.2 (`T* = ∞`), joint form (BC.md §1.4.3–1.4.4): the
compiled system has the solution `τ ↦ (y_o(s τ), (W_a(y(s τ)))_a)` on `[0, ∞)`, where `s`
inverts the clock `θ(t) = ∫₀ᵗ P(y)`; `s(0) = 0`, `s` is strictly increasing and `s → ∞`. -/
theorem PolyPIVP.jointSurrogateCompile_solution (P : PolyPIVP d) {N : ℕ} (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N) (sol : PIVP.Solution P.toPIVP) :
    ∃ (sol' : PIVP.Solution (P.jointSurrogateCompile N).toPIVP) (s : ℝ → ℝ),
      Continuous sol'.trajectory ∧ s 0 = 0 ∧ StrictMono s ∧
      Tendsto s atTop atTop ∧
      (∀ t, 0 ≤ t → s (∫ u in (0 : ℝ)..t, jointClock N (sol.trajectory u)) = t) ∧
      (∀ τ, 0 ≤ τ → sol'.trajectory τ (P.jointSurrogateCompile N).output
          = sol.trajectory (s τ) P.output) ∧
      (∀ τ, 0 ≤ τ → ∀ a : SurrogateIndex d N,
          sol'.trajectory τ (surrogateCoord a) = jointSurrogate N a (sol.trajectory (s τ))) := by
  obtain ⟨solc, hcont, heq⟩ := sol.exists_continuous
  have hyd : ∀ t, 0 ≤ t →
      HasDerivAt solc.trajectory (P.evalField (solc.trajectory t)) t := solc.is_solution
  have hρc : Continuous fun t => jointClock N (solc.trajectory t) :=
    (continuous_jointClock N).comp hcont
  have hρ1 : ∀ u, 1 ≤ (fun t => jointClock N (solc.trajectory t)) u :=
    fun u => jointClock_ge_one hN (solc.trajectory u)
  obtain ⟨s, hs0, hsd, hsc, hsm, hst, hsθ, -⟩ := exists_inverse_timeChange hρc hρ1
  have hs_nn : ∀ τ, 0 ≤ τ → 0 ≤ s τ := fun τ hτ => hs0 ▸ hsm.monotone hτ
  -- `z = y ∘ s` satisfies `z' = F(z)/P(z)` at every `τ ≥ 0`
  have hz : ∀ τ, 0 ≤ τ → ∀ i, HasDerivAt (fun σ => solc.trajectory (s σ) i)
      (P.evalField (solc.trajectory (s τ)) i / jointClock N (solc.trajectory (s τ))) τ := by
    intro τ hτ i
    have h := (hyd (s τ) (hs_nn τ hτ)).scomp τ (hsd τ)
    refine (hasDerivAt_pi.mp h i).congr_deriv ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [div_eq_inv_mul]
  have hz0 : solc.trajectory (s 0) = fun i => (P.init i : ℝ) := by
    rw [hs0, solc.init_cond]; rfl
  obtain ⟨sol', hout, hsur, hcont'⟩ :=
    P.jointSurrogateCompile_solution_of_curve hN hdeg (fun σ => solc.trajectory (s σ)) hz0 hz
  refine ⟨sol', s, hcont' (hcont.comp hsc), hs0, hsm, hst, ?_, ?_, ?_⟩
  · intro t ht
    have hint : (∫ u in (0 : ℝ)..t, jointClock N (sol.trajectory u)) =
        clockIntegral (fun t => jointClock N (solc.trajectory t)) t := by
      unfold clockIntegral
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le ht] at hu
      change jointClock N (sol.trajectory u) = jointClock N (solc.trajectory u)
      rw [heq u hu.1]
    rw [hint, hsθ]
  · intro τ hτ
    rw [hout τ]
    change solc.trajectory (s τ) P.output = _
    rw [heq (s τ) (hs_nn τ hτ)]
  · intro τ hτ a
    rw [hsur τ a]
    change jointSurrogate N a (solc.trajectory (s τ)) = _
    rw [heq (s τ) (hs_nn τ hτ)]

/-! ## Boundedness and the certificates -/

/-- A function continuous on `[0, ∞)` with a limit at `∞` is bounded on `[0, ∞)`. -/
theorem exists_abs_le_of_tendsto {f : ℝ → ℝ} {α : ℝ} (hc : ∀ t, 0 ≤ t → ContinuousAt f t)
    (hlim : Tendsto f atTop (nhds α)) : ∃ M, 0 < M ∧ ∀ t, 0 ≤ t → |f t| ≤ M := by
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.mp hlim) 1 one_pos
  have hcont : ContinuousOn f (Set.Icc 0 (max T 0)) := fun t ht => (hc t ht.1).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max (max C (|α| + 1)) 1, lt_max_of_lt_right one_pos, fun t ht => ?_⟩
  by_cases htT : t ≤ max T 0
  · have h := hC t ⟨ht, htT⟩
    rw [Real.norm_eq_abs] at h
    exact h.trans ((le_max_left _ _).trans (le_max_left _ _))
  · push Not at htT
    have h1 := hT t ((le_max_left T 0).trans htT.le)
    rw [Real.dist_eq] at h1
    have h2 : |f t| ≤ |α| + 1 := by
      have := abs_sub_abs_le_abs_sub (f t) α
      linarith
    exact h2.trans ((le_max_right _ _).trans (le_max_left _ _))

/-- The compiled trajectory is bounded on `[0, ∞)` when the kept output is (the surrogates are
in `[-1, 1]`). -/
theorem jointSurrogateCompile_isBounded (P : PolyPIVP d) {N : ℕ} (hN : Even N)
    (sol' : PIVP.Solution (P.jointSurrogateCompile N).toPIVP) (z : ℝ → Fin d → ℝ)
    (hout : ∀ τ, 0 ≤ τ → sol'.trajectory τ (P.jointSurrogateCompile N).output = z τ P.output)
    (hsur : ∀ τ, 0 ≤ τ → ∀ a : SurrogateIndex d N,
      sol'.trajectory τ (surrogateCoord a) = jointSurrogate N a (z τ))
    {M : ℝ} (hM : ∀ τ, 0 ≤ τ → |z τ P.output| ≤ M) :
    (P.jointSurrogateCompile N).toPIVP.IsBounded sol'.trajectory := by
  refine ⟨max M 1, lt_max_of_lt_right one_pos, fun τ hτ => ?_⟩
  refine (pi_norm_le_iff_of_nonneg (le_trans zero_le_one (le_max_right _ _))).2 fun j => ?_
  rw [Real.norm_eq_abs]
  rcases jointCoord_cases j with rfl | ⟨a, rfl⟩
  · rw [← jointSurrogateCompile_output, hout τ hτ]
    exact (hM τ hτ).trans (le_max_left _ _)
  · rw [hsur τ hτ a]
    exact (jointSurrogate_abs_le_one hN a _).trans (le_max_right _ _)

/-- [BAC] Thm 3.3 (bounded GPACs compute the same real numbers), certified form, BC.md §1.4:
a ℚ-PIVP with a solution on `[0, ∞)` whose output tends to `α` compiles, for every even `N`
at least the degree of the field, to the bounded ℚ-PIVP `P.jointSurrogateCompile N`, which
computes `α` with a time modulus ([BAC] Def 2.1 + 2.3). -/
theorem bounded_compilation_certified {α : ℝ} (P : PolyPIVP d) {N : ℕ} (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N) (sol : PIVP.Solution P.toPIVP)
    (hlim : Tendsto (fun t => sol.trajectory t P.output) atTop (nhds α)) :
    ∃ btc : CertifiedBoundedTimeComputable (jointDim d N) α,
      btc.pivp = P.jointSurrogateCompile N := by
  obtain ⟨sol', s, hcont, hs0, hsm, hst, -, hout, hsur⟩ :=
    P.jointSurrogateCompile_solution hN hdeg sol
  have hs_nn : ∀ τ, 0 ≤ τ → 0 ≤ s τ := fun τ hτ => hs0 ▸ hsm.monotone hτ
  obtain ⟨M, -, hM⟩ := exists_abs_le_of_tendsto
    (fun t ht => (continuous_apply P.output).continuousAt.comp
      ((sol.is_solution t ht).continuousAt)) hlim
  have hbd := jointSurrogateCompile_isBounded P hN sol' (fun τ => sol.trajectory (s τ)) hout hsur
    (fun τ hτ => hM _ (hs_nn τ hτ))
  have hlim' : Tendsto (fun τ => sol'.trajectory τ (P.jointSurrogateCompile N).output)
      atTop (nhds α) := by
    refine (hlim.comp hst).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact (hout τ hτ).symm
  obtain ⟨btc, hbtc, -⟩ :=
    CertifiedBoundedTimeComputable.exists_of_tendsto _ sol' hbd hcont hlim'
  exact ⟨btc, hbtc⟩

/-- Convergence with a modulus implies the limit. -/
theorem tendsto_of_modulus {f : ℝ → ℝ} {α : ℝ} (μ : TimeModulus)
    (h : ∀ r : ℕ, ∀ t : ℝ, t > μ r → |f t - α| < Real.exp (-(r : ℝ))) :
    Tendsto f atTop (nhds α) := by
  rw [Metric.tendsto_atTop']
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (-Real.log ε)
  have hr : Real.exp (-(n : ℝ)) < ε := by
    rw [← Real.lt_log_iff_exp_lt hε, neg_lt]; exact hn
  exact ⟨μ n, fun t ht => by rw [Real.dist_eq]; exact (h n t ht).trans hr⟩

/-- [BAC] Thm 4.5 (iterative bounded compilation), joint form, BC.md §1.6: if the output is
`e^{-r}`-close after `μ r`, with `μ r` and the arc length `L(μ r)` at most `C (r+1)^k`, then the
bounded compiled system `P.jointSurrogateCompile N` computes `α` with a time modulus at most
`C' (r+1)^{k(N+1)}` (the clock `θ(μ r) = ∫₀^{μ r} P(y)`), and its own trajectory length grows at
most linearly ([BAC] Lemma 4.1), hence polynomially at the precision-`r` time. The dimension
clause of Thm 4.5 is `jointDim_le`. -/
theorem bounded_compilation_polyTime_certified {α : ℝ} (P : PolyPIVP d)
    (sol : PIVP.Solution P.toPIVP) (μ : TimeModulus) (k : ℕ) (C : ℝ)
    (hconv : ∀ r : ℕ, ∀ t : ℝ, t > μ r →
      |sol.trajectory t P.output - α| < Real.exp (-(r : ℝ)))
    (hμ : ∀ r : ℕ, 0 ≤ μ r ∧ μ r ≤ C * ((r : ℝ) + 1) ^ k)
    (hL : ∀ r : ℕ, P.arcLength sol.trajectory (μ r) ≤ C * ((r : ℝ) + 1) ^ k)
    {N : ℕ} (hN : Even N) (hdeg : ∀ i, (P.field i).totalDegree ≤ N) :
    ∃ btc : CertifiedBoundedTimeComputable (jointDim d N) α,
      btc.pivp = P.jointSurrogateCompile N ∧
      (∃ C' : ℝ, 0 < C' ∧ ∀ r : ℕ, btc.modulus r ≤ C' * ((r : ℝ) + 1) ^ (k * (N + 1))) ∧
      (∃ v : ℝ, 0 ≤ v ∧ ∀ τ, 0 ≤ τ → btc.pivp.arcLength btc.sol.trajectory τ ≤ v * τ) := by
  obtain ⟨sol', s, -, hs0, hsm, -, hclock, hout, hsur⟩ :=
    P.jointSurrogateCompile_solution hN hdeg sol
  have hs_nn : ∀ τ, 0 ≤ τ → 0 ≤ s τ := fun τ hτ => hs0 ▸ hsm.monotone hτ
  have hlim := tendsto_of_modulus μ hconv
  obtain ⟨M, -, hM⟩ := exists_abs_le_of_tendsto
    (fun t ht => (continuous_apply P.output).continuousAt.comp
      ((sol.is_solution t ht).continuousAt)) hlim
  have hbd := jointSurrogateCompile_isBounded P hN sol' (fun τ => sol.trajectory (s τ)) hout hsur
    (fun τ hτ => hM _ (hs_nn τ hτ))
  -- the clock and the compiled modulus
  have hclk_cont : ∀ a b, 0 ≤ a →
      ContinuousOn (fun u => jointClock N (sol.trajectory u)) (Set.Icc a b) :=
    fun a b ha u hu => ((continuous_jointClock N).continuousAt.comp
      (P.solution_continuousAt sol (ha.trans hu.1))).continuousWithinAt
  have hθ_nn : ∀ t, 0 ≤ t → 0 ≤ ∫ u in (0 : ℝ)..t, jointClock N (sol.trajectory u) :=
    fun t ht => intervalIntegral.integral_nonneg ht
      fun u _ => zero_le_one.trans (jointClock_ge_one hN _)
  have hconv' : ∀ r : ℕ, ∀ τ : ℝ,
      τ > (fun r : ℕ => ∫ u in (0 : ℝ)..(μ r), jointClock N (sol.trajectory u)) r →
      |sol'.trajectory τ (P.jointSurrogateCompile N).output - α| < Real.exp (-(r : ℝ)) := by
    intro r τ hτ
    have hτ0 : 0 ≤ τ := (hθ_nn _ (hμ r).1).trans hτ.le
    have hsτ : μ r < s τ := by
      have := hsm hτ
      rwa [hclock _ (hμ r).1] at this
    rw [hout τ hτ0]
    exact hconv r (s τ) hsτ
  obtain ⟨btc, hbtc, hmod, -⟩ :=
    CertifiedBoundedTimeComputable.exists_of_solution _ sol' hbd _ hconv'
  refine ⟨btc, hbtc, ?_, ?_⟩
  · -- the modulus bound ([BAC] Lemma 4.4 / Thm 4.5, joint accounting, BC.md §1.6)
    have hC : 0 ≤ C := by
      have := (hμ 0).1.trans (hμ 0).2
      simpa using this
    obtain ⟨c₀, hc₀⟩ : ∃ c : ℝ, c = ∑ i, |(P.init i : ℝ)| := ⟨_, rfl⟩
    have hc₀_nn : 0 ≤ c₀ := hc₀ ▸ Finset.sum_nonneg fun i _ => abs_nonneg _
    obtain ⟨K, hK⟩ : ∃ K : ℝ, K = C * (1 + (d : ℝ) * (c₀ + C) ^ N) := ⟨_, rfl⟩
    refine ⟨max K 1, lt_max_of_lt_right one_pos, fun r => ?_⟩
    rw [hmod r, max_eq_right (hθ_nn _ (hμ r).1)]
    obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ((r : ℝ) + 1) ^ k := ⟨_, rfl⟩
    have hr1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) r; linarith
    have hq1 : 1 ≤ q := hq ▸ one_le_pow₀ hr1
    obtain ⟨B, hB⟩ : ∃ B : ℝ, B = c₀ + C * q := ⟨_, rfl⟩
    have hLr : P.arcLength sol.trajectory (μ r) ≤ C * q := hq ▸ hL r
    -- every coordinate is bounded by `B` on `[0, μ r]` ([BAC] Lemma 4.3)
    have hcoord : ∀ u ∈ Set.Icc 0 (μ r), ∀ i, |sol.trajectory u i| ≤ B := by
      intro u hu i
      have h1 := P.abs_sub_init_le_arcLength sol i hu.1
      have h2 := P.arcLength_mono sol hu.1 hu.2
      have h3 : |(P.init i : ℝ)| ≤ c₀ := hc₀ ▸
        Finset.single_le_sum (f := fun i => |(P.init i : ℝ)|) (fun i _ => abs_nonneg _)
          (Finset.mem_univ i)
      have h4 := abs_sub_abs_le_abs_sub (sol.trajectory u i) (P.init i : ℝ)
      rw [hB]
      linarith
    have hclk_le : ∀ u ∈ Set.Icc 0 (μ r),
        jointClock N (sol.trajectory u) ≤ 1 + (d : ℝ) * B ^ N := by
      intro u hu
      unfold jointClock
      have : ∑ i, sol.trajectory u i ^ N ≤ ∑ _i : Fin d, B ^ N :=
        Finset.sum_le_sum fun i _ => by
          rw [← hN.pow_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hcoord u hu i) N
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      linarith
    have hθle : (∫ u in (0 : ℝ)..(μ r), jointClock N (sol.trajectory u)) ≤
        μ r * (1 + (d : ℝ) * B ^ N) := by
      have h := intervalIntegral.integral_mono_on (hμ r).1
        ((hclk_cont 0 (μ r) le_rfl).intervalIntegrable_of_Icc
          (μ := MeasureTheory.volume) (hμ r).1)
        ((continuous_const : Continuous fun _ : ℝ => 1 + (d : ℝ) * B ^ N).intervalIntegrable
          (μ := MeasureTheory.volume) _ _)
        hclk_le
      simpa [mul_comm] using h
    have hB_le : B ≤ (c₀ + C) * q := by
      have : c₀ ≤ c₀ * q := le_mul_of_one_le_right hc₀_nn hq1
      rw [hB]; nlinarith
    have hB_nn : 0 ≤ B := by rw [hB]; positivity
    have hBN : B ^ N ≤ (c₀ + C) ^ N * q ^ N := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hB_nn hB_le N
    have hqN : q * q ^ N = ((r : ℝ) + 1) ^ (k * (N + 1)) := by
      rw [hq, ← pow_succ', ← pow_mul, mul_comm]
    have hq_le : q ≤ ((r : ℝ) + 1) ^ (k * (N + 1)) := by
      rw [hq]; exact pow_le_pow_right₀ hr1 (Nat.le_mul_of_pos_right k (Nat.succ_pos N))
    have hμr : μ r ≤ C * q := hq ▸ (hμ r).2
    have hq0 : 0 ≤ q := le_trans zero_le_one hq1
    calc (∫ u in (0 : ℝ)..(μ r), jointClock N (sol.trajectory u))
        ≤ μ r * (1 + (d : ℝ) * B ^ N) := hθle
      _ ≤ (C * q) * (1 + (d : ℝ) * ((c₀ + C) ^ N * q ^ N)) := by
          gcongr
      _ = C * q + C * (d : ℝ) * (c₀ + C) ^ N * (q * q ^ N) := by ring
      _ ≤ C * ((r : ℝ) + 1) ^ (k * (N + 1)) +
            C * (d : ℝ) * (c₀ + C) ^ N * ((r : ℝ) + 1) ^ (k * (N + 1)) := by
          rw [hqN]; gcongr
      _ = K * ((r : ℝ) + 1) ^ (k * (N + 1)) := by rw [hK]; ring
      _ ≤ max K 1 * ((r : ℝ) + 1) ^ (k * (N + 1)) := by
          gcongr; exact le_max_left _ _
  · -- [BAC] Lemma 4.1 on the compiled bounded system
    exact btc.pivp.arcLength_le_of_bounded btc.sol btc.bounded

end Ripple
