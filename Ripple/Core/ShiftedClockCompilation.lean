/-
  Ripple.Core.ShiftedClockCompilation — bounded computation of functions ([BAC] Def 2.4) and
  the function part of [BAC] Thm 4.4 via the shifted clock ([BAC] Remark 3.8)

  [BAC] = Chen and Huang, *Bounded Analog Complexity*, journal draft (repository `Bounded`,
  branch `BAC-Journal`). Labels: Def 2.4 `def:bounded-function`; Remark 3.7 `rmk:subset` (clock
  over a subset of the coordinates); Remark 3.8 `rmk:shifted-clock`; Thm 4.4 `thm:compilation`
  (second part: functions on a compact domain).

  The shifted clock. For `y' = p(y)`, `y(0) = y₀(x)` with `y₀ ∈ ℚ[x]^d`, adjoin constant states
  `c` with `c' = 0`, `c(0) = y₀(x)`, and put `z = y − c`, so `z' = p(z + c)`, `z(0) = 0`. Clock
  only `z` (Remark 3.7 with `S = z`, `R = c`): `P(z) = 1 + Σᵢ zᵢ^N`, surrogates
  `W_a = z^a / P(z)` for `|a| ≤ N`. Writing `p_i(z + c) = Σ_{β,γ} c_{i,β,γ} c^γ z^β`, the
  compiled system is
      `c' = 0`,
      `x̄_j' = Σ_{β,γ} c_{o_j,β,γ} c^γ w_β`                         (kept output copies),
      `w_a' = Σᵢ aᵢ w_{a−eᵢ} pᵢ^W − N w_a Σᵢ w_{(N−1)eᵢ} pᵢ^W`,  `pᵢ^W = Σ_{β,γ} c_{i,β,γ} c^γ w_β`,
  with the initial value `c(0) = y₀(x)`, `x̄_j(0) = y₀,o_j(x)`, `w₀(0) = 1`, `w_a(0) = 0`
  (`a ≠ 0`), polynomial in `x`. Dimension `d + m + C(d+N, N)`, degree `≤ 3 + D`.

  Only the case of Remark 3.7 used by the paper (the constant coordinates `R = c`) is built; the
  general subset clock is not formalized.
-/

import Ripple.Core.BGPPolyLength

namespace Ripple

open MvPolynomial Filter MeasureTheory Topology

/-! ## [BAC] Def 2.4: bounded-time computation of a function on a compact domain -/

/-- A family of ℚ-PIVPs with polynomial initial value: `y' = p(y)`, `p ∈ ℚ[y]^d`,
`y(0) = y₀(x)`, `y₀ ∈ ℚ[x]^d` for an input `x ∈ ℝ^n`, and `m` designated output coordinates
(the paper's `y_{1..m}`, up to a renaming of the coordinates). -/
structure PolyPIVPFamily (n d m : ℕ) where
  /-- The ℚ-polynomial vector field. -/
  field : Fin d → MvPolynomial (Fin d) ℚ
  /-- The initial value, a ℚ-polynomial in the input. -/
  init : Fin d → MvPolynomial (Fin n) ℚ
  /-- The output coordinates. -/
  output : Fin m → Fin d

namespace PolyPIVPFamily

variable {n d m : ℕ}

/-- The evaluated vector field. -/
noncomputable def evalField (S : PolyPIVPFamily n d m) (y : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (S.field i).eval₂ (Rat.castHom ℝ) y

/-- The initial value at the input `x`. -/
noncomputable def evalInit (S : PolyPIVPFamily n d m) (x : Fin n → ℝ) : Fin d → ℝ :=
  fun i => (S.init i).eval₂ (Rat.castHom ℝ) x

/-- `y` solves the system at input `x` on `[0, ∞)`. -/
def IsSolution (S : PolyPIVPFamily n d m) (x : Fin n → ℝ) (y : ℝ → Fin d → ℝ) : Prop :=
  y 0 = S.evalInit x ∧ ∀ t, 0 ≤ t → HasDerivAt y (S.evalField (y t)) t

/-- The output vector `y_{o}(t) ∈ ℝ^m`. -/
def outputAt (S : PolyPIVPFamily n d m) (y : ℝ → Fin d → ℝ) (t : ℝ) : Fin m → ℝ :=
  fun j => y t (S.output j)

/-- Trajectory length `L(t) = ∫₀ᵗ ‖p(y(u))‖ du` (sup norm). -/
noncomputable def arcLength (S : PolyPIVPFamily n d m) (y : ℝ → Fin d → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, ‖S.evalField (y u)‖

/-- [BAC] Def 2.4 (journal draft `def:bounded-function`): the system computes `f` on `K` with
time modulus `μ` if for every `x ∈ K` the solution `y_x` exists on `[0, ∞)`, the state is
bounded uniformly, `sup_{x ∈ K, t ≥ 0} ‖y_x(t)‖ < ∞`, and `‖(y_x)_o(t) − f(x)‖ < e^{−r}`
whenever `t > μ(r)` (sup norm on `ℝ^m`). -/
def ComputesOn (S : PolyPIVPFamily n d m) (f : (Fin n → ℝ) → Fin m → ℝ)
    (K : Set (Fin n → ℝ)) (μ : TimeModulus) : Prop :=
  ∃ y : (Fin n → ℝ) → ℝ → Fin d → ℝ,
    (∀ x ∈ K, S.IsSolution x (y x)) ∧
    (∃ M : ℝ, ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → ‖y x t‖ ≤ M) ∧
    (∀ x ∈ K, ∀ r : ℕ, ∀ t : ℝ, t > μ r →
      ‖S.outputAt (y x) t - f x‖ < Real.exp (-(r : ℝ)))

theorem continuous_evalField (S : PolyPIVPFamily n d m) : Continuous S.evalField := by
  refine continuous_pi fun i => ?_
  show Continuous fun x => (S.field i).eval₂ (Rat.castHom ℝ) x
  convert MvPolynomial.continuous_eval (p := MvPolynomial.map (Rat.castHom ℝ) (S.field i))
    using 1
  ext x
  exact MvPolynomial.eval₂_eq_eval_map (Rat.castHom ℝ) x (S.field i)

theorem continuous_evalInit (S : PolyPIVPFamily n d m) : Continuous S.evalInit := by
  refine continuous_pi fun i => ?_
  show Continuous fun x => (S.init i).eval₂ (Rat.castHom ℝ) x
  convert MvPolynomial.continuous_eval (p := MvPolynomial.map (Rat.castHom ℝ) (S.init i))
    using 1
  ext x
  exact MvPolynomial.eval₂_eq_eval_map (Rat.castHom ℝ) x (S.init i)

theorem speed_continuousOn (S : PolyPIVPFamily n d m) {x : Fin n → ℝ} {y : ℝ → Fin d → ℝ}
    (hy : S.IsSolution x y) (a b : ℝ) (ha : 0 ≤ a) :
    ContinuousOn (fun u => ‖S.evalField (y u)‖) (Set.Icc a b) :=
  fun u hu => ((S.continuous_evalField.continuousAt.comp
    (hy.2 u (ha.trans hu.1)).continuousAt).norm).continuousWithinAt

theorem arcLength_mono (S : PolyPIVPFamily n d m) {x : Fin n → ℝ} {y : ℝ → Fin d → ℝ}
    (hy : S.IsSolution x y) {t₁ t₂ : ℝ} (h₀ : 0 ≤ t₁) (h : t₁ ≤ t₂) :
    S.arcLength y t₁ ≤ S.arcLength y t₂ := by
  have hi1 : IntervalIntegrable (fun u => ‖S.evalField (y u)‖) volume 0 t₁ :=
    (S.speed_continuousOn hy 0 t₁ le_rfl).intervalIntegrable_of_Icc h₀
  have hi2 : IntervalIntegrable (fun u => ‖S.evalField (y u)‖) volume t₁ t₂ :=
    (S.speed_continuousOn hy t₁ t₂ h₀).intervalIntegrable_of_Icc h
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have hnn : 0 ≤ ∫ u in t₁..t₂, ‖S.evalField (y u)‖ :=
    intervalIntegral.integral_nonneg h fun _ _ => norm_nonneg _
  unfold arcLength
  linarith

/-- [BAC] Lemma 4.3 for the family: `|yᵢ(t) − yᵢ(0)| ≤ L(t)`. -/
theorem abs_sub_init_le_arcLength (S : PolyPIVPFamily n d m) {x : Fin n → ℝ}
    {y : ℝ → Fin d → ℝ} (hy : S.IsSolution x y) (i : Fin d) {t : ℝ} (ht : 0 ≤ t) :
    |y t i - y 0 i| ≤ S.arcLength y t := by
  have hderiv : ∀ u ∈ Set.uIcc 0 t, HasDerivAt (fun u => y u i) (S.evalField (y u) i) u := by
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    exact hasDerivAt_pi.mp (hy.2 u hu.1) i
  have hci : ContinuousOn (fun u => S.evalField (y u) i) (Set.Icc 0 t) :=
    fun u hu => ((continuous_apply i).continuousAt.comp
      (S.continuous_evalField.continuousAt.comp
        (hy.2 u hu.1).continuousAt)).continuousWithinAt
  have hint : IntervalIntegrable (fun u => S.evalField (y u) i) volume 0 t :=
    hci.intervalIntegrable_of_Icc ht
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [← hftc]
  calc |∫ u in (0 : ℝ)..t, S.evalField (y u) i|
      ≤ ∫ u in (0 : ℝ)..t, |S.evalField (y u) i| :=
        intervalIntegral.abs_integral_le_integral_abs ht
    _ ≤ ∫ u in (0 : ℝ)..t, ‖S.evalField (y u)‖ := by
        refine intervalIntegral.integral_mono_on ht ?_ ?_ ?_
        · exact (hci.abs).intervalIntegrable_of_Icc ht
        · exact (S.speed_continuousOn hy 0 t le_rfl).intervalIntegrable_of_Icc ht
        · intro u _
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm (S.evalField (y u)) i

/-- A system over a finite index type, reindexed to `Fin` by `Fintype.equivFin`. -/
noncomputable def ofIndexed {ι : Type*} [Fintype ι] (G : ι → MvPolynomial ι ℚ)
    (y₀ : ι → MvPolynomial (Fin n) ℚ) (o : Fin m → ι) : PolyPIVPFamily n (Fintype.card ι) m where
  field j := rename (Fintype.equivFin ι) (G ((Fintype.equivFin ι).symm j))
  init j := y₀ ((Fintype.equivFin ι).symm j)
  output j := Fintype.equivFin ι (o j)

theorem ofIndexed_isSolution {ι : Type*} [Fintype ι] (G : ι → MvPolynomial ι ℚ)
    (y₀ : ι → MvPolynomial (Fin n) ℚ) (o : Fin m → ι) (x : Fin n → ℝ) (Z : ℝ → ι → ℝ)
    (h0 : ∀ k, Z 0 k = (y₀ k).eval₂ (Rat.castHom ℝ) x)
    (hZ : ∀ τ, 0 ≤ τ → ∀ k, HasDerivAt (fun σ => Z σ k)
      ((G k).eval₂ (Rat.castHom ℝ) (Z τ)) τ) :
    (ofIndexed G y₀ o).IsSolution x (fun τ j => Z τ ((Fintype.equivFin ι).symm j)) := by
  refine ⟨?_, fun τ hτ => ?_⟩
  · funext j
    simp [evalInit, ofIndexed, h0]
  · refine hasDerivAt_pi.mpr fun j => ?_
    show HasDerivAt (fun σ => Z σ ((Fintype.equivFin ι).symm j))
      ((rename (Fintype.equivFin ι) (G ((Fintype.equivFin ι).symm j))).eval₂
        (Rat.castHom ℝ) (fun j => Z τ ((Fintype.equivFin ι).symm j))) τ
    rw [MvPolynomial.eval₂_rename]
    convert hZ τ hτ ((Fintype.equivFin ι).symm j) using 2
    funext k
    simp [Function.comp]

end PolyPIVPFamily

/-- [BAC] Def 2.4: `f` is computed on the compact set `K` by some family of bounded ℚ-PIVPs
with polynomial initial value, with time modulus `μ`. -/
def IsBoundedTimeComputableOn {n m : ℕ} (f : (Fin n → ℝ) → Fin m → ℝ) (K : Set (Fin n → ℝ))
    (μ : TimeModulus) : Prop :=
  IsCompact K ∧ ∃ d : ℕ, ∃ S : PolyPIVPFamily n d m, S.ComputesOn f K μ

/-- [BAC] Def 2.4, polynomial time: a time modulus `μ(r) ≤ C (r+1)^k`. -/
def IsPolyTimeComputableOn {n m : ℕ} (f : (Fin n → ℝ) → Fin m → ℝ) (K : Set (Fin n → ℝ))
    (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ IsBoundedTimeComputableOn f K (fun r => C * ((r : ℝ) + 1) ^ k)

/-! ## The shifted polynomial `p(z + c)` and its lift -/

variable {d : ℕ}

/-- `q(z + c)` as a polynomial in the constants `c` (`Sum.inl`) and the displacement `z`
(`Sum.inr`). -/
noncomputable def shiftPoly (q : MvPolynomial (Fin d) ℚ) : MvPolynomial (Fin d ⊕ Fin d) ℚ :=
  aeval (fun j => X (Sum.inl j) + X (Sum.inr j)) q

theorem shiftPoly_eval (q : MvPolynomial (Fin d) ℚ) (c z : Fin d → ℝ) :
    (shiftPoly q).eval₂ (Rat.castHom ℝ) (Sum.elim c z) =
      q.eval₂ (Rat.castHom ℝ) (fun j => c j + z j) := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [shiftPoly, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
    simp only [shiftPoly, map_add, eval₂_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p j hp =>
    simp only [shiftPoly, map_mul, aeval_X, eval₂_mul, eval₂_add, eval₂_X, Sum.elim_inl,
      Sum.elim_inr] at hp ⊢
    rw [hp]

/-- Substituting linear forms does not raise the degree. -/
theorem totalDegree_shiftPoly_le (q : MvPolynomial (Fin d) ℚ) :
    (shiftPoly q).totalDegree ≤ q.totalDegree := by
  have hlin : ∀ i : Fin d,
      (X (Sum.inl i) + X (Sum.inr i) : MvPolynomial (Fin d ⊕ Fin d) ℚ).totalDegree ≤ 1 :=
    fun i => (totalDegree_add _ _).trans (max_le (totalDegree_X _).le (totalDegree_X _).le)
  conv_lhs => rw [q.as_sum]
  rw [shiftPoly, map_sum]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun e he => ?_)
  rw [aeval_monomial, MvPolynomial.algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  calc (e.prod fun i k => (X (Sum.inl i) + X (Sum.inr i) :
          MvPolynomial (Fin d ⊕ Fin d) ℚ) ^ k).totalDegree
      ≤ ∑ i ∈ e.support, ((X (Sum.inl i) + X (Sum.inr i) :
          MvPolynomial (Fin d ⊕ Fin d) ℚ) ^ e i).totalDegree :=
        totalDegree_finset_prod _ _
    _ ≤ ∑ i ∈ e.support, e i := Finset.sum_le_sum fun i _ =>
        (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (e i) (hlin i))
    _ = e.sum fun _ k => k := rfl
    _ ≤ q.totalDegree := le_totalDegree he

/-- Coordinates of the shifted compilation: the constants `c` (`Sum.inl`), the kept output
copies (`Sum.inr ∘ Sum.inl`), the surrogates `w_a` (`Sum.inr ∘ Sum.inr`). -/
abbrev ShiftIndex (d m N : ℕ) := Fin d ⊕ (Fin m ⊕ SurrogateIndex d N)

/-- The surrogate variable `w_β` of the `z`-part `β` of an exponent `(γ, β)` of degree `≤ N`
(`0` otherwise; never used with larger degree). -/
noncomputable def zMon {m : ℕ} (N : ℕ) (e : (Fin d ⊕ Fin d) →₀ ℕ) :
    MvPolynomial (ShiftIndex d m N) ℚ :=
  if h : ∑ i, e (Sum.inr i) ≤ N then
    X (Sum.inr (Sum.inr ⟨fun i => ⟨e (Sum.inr i), Nat.lt_succ_of_le
      ((Finset.single_le_sum (f := fun j => e (Sum.inr j)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)).trans h)⟩, by unfold MIndex.degree; exact h⟩))
  else 0

/-- The lift `Q^W = Σ_{(γ,β)} c_{β,γ} c^γ w_β` of `Q = Σ c_{β,γ} c^γ z^β`. -/
noncomputable def liftShift {m : ℕ} (N : ℕ) (Q : MvPolynomial (Fin d ⊕ Fin d) ℚ) :
    MvPolynomial (ShiftIndex d m N) ℚ :=
  ∑ e ∈ Q.support, C (Q.coeff e) * (∏ i, X (Sum.inl i) ^ e (Sum.inl i)) * zMon N e

theorem degree_split_le {Q : MvPolynomial (Fin d ⊕ Fin d) ℚ} {e : (Fin d ⊕ Fin d) →₀ ℕ}
    (he : e ∈ Q.support) :
    ∑ i, e (Sum.inl i) + ∑ i, e (Sum.inr i) ≤ Q.totalDegree := by
  have h1 := le_totalDegree he
  rwa [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sum_type] at h1

/-- `Q^W(c, W(z)) = Q(c, z) / P(z)` when `deg Q ≤ N`. -/
theorem liftShift_eval {m N : ℕ} {Q : MvPolynomial (Fin d ⊕ Fin d) ℚ} (hQ : Q.totalDegree ≤ N)
    (c z : Fin d → ℝ) (v : ShiftIndex d m N → ℝ) (hc : ∀ i, v (Sum.inl i) = c i)
    (hw : ∀ a, v (Sum.inr (Sum.inr a)) = jointSurrogate N a z) :
    (liftShift N Q).eval₂ (Rat.castHom ℝ) v =
      Q.eval₂ (Rat.castHom ℝ) (Sum.elim c z) / jointClock N z := by
  rw [MvPolynomial.eval₂_eq' (Rat.castHom ℝ) (Sum.elim c z) Q, Finset.sum_div]
  unfold liftShift
  rw [eval₂_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hdeg : ∑ i, e (Sum.inr i) ≤ N := by
    have := degree_split_le he
    omega
  simp only [zMon, dif_pos hdeg, eval₂_mul, eval₂_C, eval₂_prod, eval₂_pow, eval₂_X, hc, hw,
    jointSurrogate, MIndex.eval, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  ring

theorem liftShift_totalDegree_le {m N : ℕ} (Q : MvPolynomial (Fin d ⊕ Fin d) ℚ) :
    (liftShift (m := m) N Q).totalDegree ≤ Q.totalDegree + 1 := by
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun e he => ?_)
  have h1 := degree_split_le he
  have hp : (∏ i, X (Sum.inl i) ^ e (Sum.inl i) :
      MvPolynomial (ShiftIndex d m N) ℚ).totalDegree ≤ ∑ i, e (Sum.inl i) :=
    (totalDegree_finset_prod _ _).trans (Finset.sum_le_sum fun i _ => (totalDegree_X_pow _ _).le)
  have hz : (zMon (m := m) N e).totalDegree ≤ 1 := by
    unfold zMon
    split_ifs
    · exact (totalDegree_X _).le
    · simp
  refine (totalDegree_mul _ _).trans ?_
  have h2 := (totalDegree_mul (C (Q.coeff e)) (∏ i, X (Sum.inl i) ^ e (Sum.inl i) :
      MvPolynomial (ShiftIndex d m N) ℚ))
  rw [totalDegree_C, zero_add] at h2
  omega

/-! ## The shifted compilation ([BAC] Remark 3.8) -/

namespace PolyPIVPFamily

variable {n m : ℕ}

/-- The lifted shifted field `pᵢ^W = (pᵢ(z + c))^W`. -/
noncomputable def shiftLift (S : PolyPIVPFamily n d m) (N : ℕ) (i : Fin d) :
    MvPolynomial (ShiftIndex d m N) ℚ :=
  liftShift N (shiftPoly (S.field i))

/-- The compiled field of the shifted clock: `c' = 0`, `x̄_j' = p_{o_j}^W`,
`w_a' = Σᵢ aᵢ w_{a−eᵢ} pᵢ^W − N w_a Σᵢ w_{(N−1)eᵢ} pᵢ^W`. -/
noncomputable def shiftField (S : PolyPIVPFamily n d m) (N : ℕ) :
    ShiftIndex d m N → MvPolynomial (ShiftIndex d m N) ℚ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl j) => S.shiftLift N (S.output j)
  | Sum.inr (Sum.inr a) =>
      ∑ i, C (((a.1 i : ℕ) : ℚ)) * X (Sum.inr (Sum.inr (a.decr i))) * S.shiftLift N i -
        C ((N : ℚ)) * X (Sum.inr (Sum.inr a)) *
          ∑ i, X (Sum.inr (Sum.inr (SurrogateIndex.powIdx N i))) * S.shiftLift N i

/-- The compiled initial value, polynomial in `x`: `c(0) = y₀(x)`, `x̄_j(0) = y₀,o_j(x)`,
`w₀(0) = 1`, `w_a(0) = 0` for `a ≠ 0`. -/
noncomputable def shiftInit (S : PolyPIVPFamily n d m) (N : ℕ) :
    ShiftIndex d m N → MvPolynomial (Fin n) ℚ
  | Sum.inl i => S.init i
  | Sum.inr (Sum.inl j) => S.init (S.output j)
  | Sum.inr (Sum.inr a) => if a = SurrogateIndex.zero d N then 1 else 0

/-- [BAC] Remark 3.8 (journal draft `rmk:shifted-clock`): the shifted-clock compilation of the
family `S`, with output the kept copies `x̄`. -/
noncomputable def shiftedCompile (S : PolyPIVPFamily n d m) (N : ℕ) :
    PolyPIVPFamily n (Fintype.card (ShiftIndex d m N)) m :=
  ofIndexed (S.shiftField N) (S.shiftInit N) (fun j => Sum.inr (Sum.inl j))

/-- [BAC] Remark 3.8 / Thm 4.4, dimension: `d + m + C(d+N, N)`. -/
theorem card_shiftIndex (d m N : ℕ) :
    Fintype.card (ShiftIndex d m N) = d + (m + (d + N).choose N) := by
  simp [Fintype.card_sum, card_surrogateIndex]

/-- [BAC] Remark 3.8 / Thm 4.4, degree: every line of the shifted compiled field has degree
`≤ 3 + D` when the original field has degree `≤ D`. -/
theorem shiftedCompile_totalDegree_le (S : PolyPIVPFamily n d m) (N : ℕ) {D : ℕ}
    (hdeg : ∀ i, (S.field i).totalDegree ≤ D) (j : Fin (Fintype.card (ShiftIndex d m N))) :
    ((S.shiftedCompile N).field j).totalDegree ≤ 3 + D := by
  refine (totalDegree_rename_le _ _).trans ?_
  have hl : ∀ i, (S.shiftLift N i).totalDegree ≤ D + 1 := fun i =>
    (liftShift_totalDegree_le _).trans
      (Nat.add_le_add_right ((totalDegree_shiftPoly_le _).trans (hdeg i)) 1)
  generalize (Fintype.equivFin (ShiftIndex d m N)).symm j = k
  rcases k with i | j | a
  · simp [shiftField]
  · exact (hl (S.output j)).trans (by omega)
  · show (∑ i, C (((a.1 i : ℕ) : ℚ)) * X (Sum.inr (Sum.inr (a.decr i))) * S.shiftLift N i -
        C ((N : ℚ)) * X (Sum.inr (Sum.inr a)) *
          ∑ i, X (Sum.inr (Sum.inr (SurrogateIndex.powIdx N i))) * S.shiftLift N i :
        MvPolynomial (ShiftIndex d m N) ℚ).totalDegree ≤ 3 + D
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
      have h1 := totalDegree_C_mul_X_le (((a.1 i : ℕ) : ℚ))
        (Sum.inr (Sum.inr (a.decr i)) : ShiftIndex d m N)
      have h2 := hl i
      exact (totalDegree_mul _ _).trans (by omega)
    · have h1 := totalDegree_C_mul_X_le ((N : ℚ)) (Sum.inr (Sum.inr a) : ShiftIndex d m N)
      have h2 : (∑ i, X (Sum.inr (Sum.inr (SurrogateIndex.powIdx N i))) * S.shiftLift N i :
          MvPolynomial (ShiftIndex d m N) ℚ).totalDegree ≤ D + 2 := by
        refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
        have h3 := hl i
        refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]
        omega
      exact (totalDegree_mul _ _).trans (by omega)

end PolyPIVPFamily

/-! ## The derivative identity for a general numerator -/

/-- Along a curve with `z' = F/P(z)` (any numerator `F`), every surrogate `W_a(z)` satisfies the
compiled surrogate line `W_a' = Σᵢ aᵢ W_{a−eᵢ} Fᵢ/P − N W_a Σᵢ W_{(N−1)eᵢ} Fᵢ/P`. -/
theorem hasDerivAt_jointSurrogate_of {N : ℕ} (hN : Even N) (a : SurrogateIndex d N)
    (z : ℝ → Fin d → ℝ) (τ : ℝ) (F : Fin d → ℝ)
    (hz : ∀ i, HasDerivAt (fun σ => z σ i) (F i / jointClock N (z τ)) τ) :
    HasDerivAt (fun σ => jointSurrogate N a (z σ))
      (∑ k, ((a.1 k : ℕ) : ℝ) * jointSurrogate N (a.decr k) (z τ) *
          (F k / jointClock N (z τ)) -
        (N : ℝ) * jointSurrogate N a (z τ) *
          ∑ i, jointSurrogate N (SurrogateIndex.powIdx N i) (z τ) *
            (F i / jointClock N (z τ))) τ := by
  have hP0 : jointClock N (z τ) ≠ 0 := ne_of_gt (jointClock_pos hN (z τ))
  have hm := hasDerivAt_monomial a.1 z (fun i => F i / jointClock N (z τ)) τ hz
  have hP : HasDerivAt (fun σ => jointClock N (z σ))
      (∑ i, ((N : ℕ) : ℝ) * z τ i ^ (N - 1) * (F i / jointClock N (z τ))) τ := by
    have := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hz i).fun_pow N)).const_add 1
    exact this
  have hq := hm.div hP hP0
  have s1 : ∑ k, ((a.1 k : ℕ) : ℝ) * jointSurrogate N (a.decr k) (z τ) *
        (F k / jointClock N (z τ)) =
      (∑ k, ((a.1 k : ℕ) : ℝ) * (a.decr k).1.eval (z τ) * F k) / jointClock N (z τ) ^ 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by unfold jointSurrogate; ring
  have s2 : ∑ i, jointSurrogate N (SurrogateIndex.powIdx N i) (z τ) *
        (F i / jointClock N (z τ)) =
      (∑ i, (SurrogateIndex.powIdx N i).1.eval (z τ) * F i) / jointClock N (z τ) ^ 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by unfold jointSurrogate; ring
  have s3 : (∑ k, (∏ j ∈ Finset.univ.erase k, z τ j ^ (a.1 j : ℕ)) *
      (((a.1 k : ℕ) : ℝ) * z τ k ^ ((a.1 k : ℕ) - 1) * (F k / jointClock N (z τ)))) =
      (∑ k, ((a.1 k : ℕ) : ℝ) * (a.decr k).1.eval (z τ) * F k) / jointClock N (z τ) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [SurrogateIndex.decr_eval]
    ring
  have s4 : (∑ i, ((N : ℕ) : ℝ) * z τ i ^ (N - 1) * (F i / jointClock N (z τ))) =
      (N : ℝ) * (∑ i, (SurrogateIndex.powIdx N i).1.eval (z τ) * F i) / jointClock N (z τ) := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [SurrogateIndex.powIdx_eval]
    ring
  have hWa : jointSurrogate N a (z τ) = a.1.eval (z τ) / jointClock N (z τ) := rfl
  rw [s1, s2, hWa, jointSurrogate_deriv_algebra _ _ _ _ _ hP0, ← s3, ← s4]
  exact hq

/-! ## The solution of the shifted compilation -/

namespace PolyPIVPFamily

variable {n m : ℕ}

/-- `0^a = 1` if `a = 0` and `0` otherwise. -/
theorem surrogateIndex_eval_zero {N : ℕ} (a : SurrogateIndex d N) :
    a.1.eval (0 : Fin d → ℝ) = if a = SurrogateIndex.zero d N then 1 else 0 := by
  split_ifs with ha
  · subst ha; exact SurrogateIndex.zero_eval d N 0
  · have hex : ∃ i, (a.1 i : ℕ) ≠ 0 := by
      by_contra h
      push_neg at h
      apply ha
      apply Subtype.ext
      funext i
      apply Fin.ext
      simp [SurrogateIndex.zero, MIndex.zero', h i]
    obtain ⟨i, hi⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [zero_pow hi])

/-- The compiled curve over the index type: `c`, the output copies `y_o(s σ)`, and the
surrogates `W_a(y(s σ) − c)`. -/
noncomputable def shiftCurve (N : ℕ) (o : Fin m → Fin d) (c : Fin d → ℝ)
    (y : ℝ → Fin d → ℝ) (s : ℝ → ℝ) (σ : ℝ) : ShiftIndex d m N → ℝ
  | Sum.inl i => c i
  | Sum.inr (Sum.inl j) => y (s σ) (o j)
  | Sum.inr (Sum.inr a) => jointSurrogate N a (fun i => y (s σ) i - c i)

/-- [BAC] Remark 3.8 with Prop 3.4 (`T* = ∞`): for a solution `y` of `S` at input `x` on
`[0, ∞)`, the shifted compilation has the solution `τ ↦ (c, y_o(s τ), W_a(y(s τ) − c))` with
`c = y₀(x)`, where `s` inverts the clock `θ(t) = ∫₀ᵗ (1 + Σᵢ (yᵢ(u) − cᵢ)^N) du`. -/
theorem shiftedCompile_solution (S : PolyPIVPFamily n d m) {N : ℕ} (hN : Even N)
    (hN2 : 2 ≤ N) (hdeg : ∀ i, (S.field i).totalDegree ≤ N) {x : Fin n → ℝ}
    {y : ℝ → Fin d → ℝ} (hy : S.IsSolution x y) :
    ∃ (Y : ℝ → Fin (Fintype.card (ShiftIndex d m N)) → ℝ) (s : ℝ → ℝ),
      (S.shiftedCompile N).IsSolution x Y ∧ s 0 = 0 ∧ StrictMono s ∧
      (∀ t, 0 ≤ t →
        s (∫ u in (0 : ℝ)..t, jointClock N (fun i => y u i - S.evalInit x i)) = t) ∧
      (∀ τ k, Y τ (Fintype.equivFin (ShiftIndex d m N) k) =
        shiftCurve N S.output (S.evalInit x) y s τ k) := by
  set c := S.evalInit x with hc
  have hyc : ContinuousOn y (Set.Ici 0) :=
    fun t ht => (hy.2 t ht).continuousAt.continuousWithinAt
  have hyt : Continuous fun u => y (max u 0) :=
    hyc.comp_continuous (continuous_id.max continuous_const) (fun u => le_max_right u 0)
  have hρc : Continuous fun u => jointClock N (fun i => y (max u 0) i - c i) :=
    (continuous_jointClock N).comp
      (continuous_pi fun i => ((continuous_apply i).comp hyt).sub continuous_const)
  have hρ1 : ∀ u, 1 ≤ (fun u => jointClock N (fun i => y (max u 0) i - c i)) u :=
    fun u => jointClock_ge_one hN _
  obtain ⟨s, hs0, hsd, -, hsm, -, hsθ, -⟩ := exists_inverse_timeChange hρc hρ1
  have hs_nn : ∀ τ, 0 ≤ τ → 0 ≤ s τ := fun τ hτ => hs0 ▸ hsm.monotone hτ
  set z : ℝ → Fin d → ℝ := fun σ i => y (s σ) i - c i with hz_def
  have hyz : ∀ σ, (fun j => c j + z σ j) = y (s σ) := by
    intro σ; funext j; simp [hz_def]
  have hys : ∀ τ, 0 ≤ τ → ∀ i, HasDerivAt (fun σ => y (s σ) i)
      (S.evalField (y (s τ)) i / jointClock N (z τ)) τ := by
    intro τ hτ i
    have h := (hy.2 (s τ) (hs_nn τ hτ)).scomp τ (hsd τ)
    refine (hasDerivAt_pi.mp h i).congr_deriv ?_
    simp only [Pi.smul_apply, smul_eq_mul, max_eq_left (hs_nn τ hτ)]
    rw [div_eq_inv_mul]
  have hz : ∀ τ, 0 ≤ τ → ∀ i, HasDerivAt (fun σ => z σ i)
      (S.evalField (y (s τ)) i / jointClock N (z τ)) τ :=
    fun τ hτ i => (hys τ hτ i).sub_const (c i)
  set Z := shiftCurve (m := m) N S.output c y s with hZ_def
  have hlift : ∀ τ i, (S.shiftLift N i).eval₂ (Rat.castHom ℝ) (Z τ) =
      S.evalField (y (s τ)) i / jointClock N (z τ) := by
    intro τ i
    rw [shiftLift, liftShift_eval ((totalDegree_shiftPoly_le _).trans (hdeg i)) c (z τ) (Z τ)
      (fun _ => rfl) (fun _ => rfl), shiftPoly_eval, hyz]
    rfl
  have hZ0 : ∀ k, Z 0 k = (S.shiftInit N k).eval₂ (Rat.castHom ℝ) x := by
    have hy0 : y (s 0) = c := by rw [hs0, hy.1]
    intro k
    rcases k with i | j | a
    · rfl
    · show y (s 0) (S.output j) = (S.init (S.output j)).eval₂ (Rat.castHom ℝ) x
      rw [hy0]; rfl
    · show jointSurrogate N a (fun i => y (s 0) i - c i) =
        (if a = SurrogateIndex.zero d N then 1 else 0 : MvPolynomial (Fin n) ℚ).eval₂
          (Rat.castHom ℝ) x
      have hz0 : (fun i => y (s 0) i - c i) = (0 : Fin d → ℝ) := by
        funext i; simp [hy0]
      have hP : jointClock N (0 : Fin d → ℝ) = 1 := by
        simp [jointClock, zero_pow (by omega : N ≠ 0)]
      rw [hz0, jointSurrogate, hP, div_one, surrogateIndex_eval_zero]
      split_ifs <;> simp
  have hZd : ∀ τ, 0 ≤ τ → ∀ k, HasDerivAt (fun σ => Z σ k)
      ((S.shiftField N k).eval₂ (Rat.castHom ℝ) (Z τ)) τ := by
    intro τ hτ k
    rcases k with i | j | a
    · simpa [shiftField, hZ_def, shiftCurve] using hasDerivAt_const τ (c i)
    · show HasDerivAt (fun σ => y (s σ) (S.output j))
        ((S.shiftLift N (S.output j)).eval₂ (Rat.castHom ℝ) (Z τ)) τ
      rw [hlift]
      exact hys τ hτ (S.output j)
    · have h := hasDerivAt_jointSurrogate_of hN a z τ (S.evalField (y (s τ))) (hz τ hτ)
      convert h using 1
      simp only [shiftField, eval₂_sub, eval₂_mul, eval₂_sum, eval₂_C, eval₂_X, hlift,
        eq_ratCast, Rat.cast_natCast]
      rfl
  refine ⟨fun τ j => Z τ ((Fintype.equivFin (ShiftIndex d m N)).symm j), s,
    ofIndexed_isSolution _ _ _ x Z hZ0 hZd, hs0, hsm, fun t ht => ?_, fun τ k => ?_⟩
  · have hint : (∫ u in (0 : ℝ)..t, jointClock N (fun i => y u i - c i)) =
        clockIntegral (fun u => jointClock N (fun i => y (max u 0) i - c i)) t := by
      unfold clockIntegral
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le ht] at hu
      simp only [max_eq_left hu.1]
    rw [hint, hsθ]
  · simp only [Equiv.symm_apply_apply, hZ_def]

end PolyPIVPFamily

/-! ## [BAC] Thm 4.4, second part: functions on a compact domain -/

namespace PolyPIVPFamily

variable {n m : ℕ}

/-- [BAC] Thm 4.4, second part (journal draft `thm:compilation`, functions): let `K` be compact
and let `y' = p(y)`, `y(0) = y₀(x)` (`y₀ ∈ ℚ[x]^d`) have, for every `x ∈ K`, a solution `y_x` on
`[0, ∞)` with a time modulus `μ_x` for `f(x)` such that `μ_x(r) ≤ C (r+1)^k` and
`L_x(μ_x(r)) ≤ C (r+1)^k` (one `C` and `k` for all `x`). Then for every even `N ≥ 2` at least the
degree of the field, the shifted compilation (`shiftedCompile`, [BAC] Remark 3.8; polynomial
initial value, dimension `d + m + C(d+N, N)` by `card_shiftIndex`, degree `≤ 3 + D` by
`shiftedCompile_totalDegree_le`) computes `f` on `K` in the sense of [BAC] Def 2.4 with the time
modulus `C'_f (r+1)^{k(N+1)}`, `C'_f = C (1 + d C^N)`, independent of `x`. -/
theorem shiftedCompile_computesOn (S : PolyPIVPFamily n d m) {f : (Fin n → ℝ) → Fin m → ℝ}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (y : (Fin n → ℝ) → ℝ → Fin d → ℝ)
    (hy : ∀ x ∈ K, S.IsSolution x (y x)) (μ : (Fin n → ℝ) → TimeModulus) (k : ℕ) (C : ℝ)
    (hconv : ∀ x ∈ K, ∀ r : ℕ, ∀ t : ℝ, t > μ x r →
      ‖S.outputAt (y x) t - f x‖ < Real.exp (-(r : ℝ)))
    (hμ : ∀ x ∈ K, ∀ r : ℕ, 0 ≤ μ x r ∧ μ x r ≤ C * ((r : ℝ) + 1) ^ k)
    (hL : ∀ x ∈ K, ∀ r : ℕ, S.arcLength (y x) (μ x r) ≤ C * ((r : ℝ) + 1) ^ k)
    {N : ℕ} (hN : Even N) (hN2 : 2 ≤ N) (hdeg : ∀ i, (S.field i).totalDegree ≤ N) :
    (S.shiftedCompile N).ComputesOn f K
      (fun r => C * (1 + (d : ℝ) * C ^ N) * ((r : ℝ) + 1) ^ (k * (N + 1))) := by
  classical
  set e := Fintype.equivFin (ShiftIndex d m N)
  have hex : ∀ x, ∃ (Y : ℝ → Fin (Fintype.card (ShiftIndex d m N)) → ℝ) (s : ℝ → ℝ),
      x ∈ K → ((S.shiftedCompile N).IsSolution x Y ∧ s 0 = 0 ∧ StrictMono s ∧
        (∀ t, 0 ≤ t →
          s (∫ u in (0 : ℝ)..t, jointClock N (fun i => y x u i - S.evalInit x i)) = t) ∧
        (∀ τ k, Y τ (e k) = shiftCurve N S.output (S.evalInit x) (y x) s τ k)) := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨Y, s, h⟩ := S.shiftedCompile_solution hN hN2 hdeg (hy x hx)
      exact ⟨Y, s, fun _ => h⟩
    · exact ⟨fun _ _ => 0, id, fun h => absurd h hx⟩
  choose Y s hYs using hex
  obtain ⟨Mc, hMc⟩ := hK.exists_bound_of_continuousOn S.continuous_evalInit.continuousOn
  -- per input: `C ≥ 0` and the bound on the output coordinates
  have hC : ∀ x ∈ K, 0 ≤ C := fun x hx => by
    have := (hμ x hx 0).1.trans (hμ x hx 0).2
    simpa using this
  have hy0 : ∀ x ∈ K, ∀ i, |y x 0 i| ≤ Mc := fun x hx i => by
    rw [(hy x hx).1]
    exact (norm_le_pi_norm (S.evalInit x) i).trans (hMc x hx)
  have hout : ∀ x ∈ K, ∀ t, 0 ≤ t → ∀ j, |y x t (S.output j)| ≤ Mc + C + 2 := by
    intro x hx t ht j
    have h0 := (hμ x hx 0).1
    have hL0 : S.arcLength (y x) (μ x 0) ≤ C := by simpa using hL x hx 0
    have hcoord : ∀ u, 0 ≤ u → u ≤ μ x 0 → |y x u (S.output j)| ≤ Mc + C := by
      intro u hu hu'
      have h1 := S.abs_sub_init_le_arcLength (hy x hx) (S.output j) hu
      have h2 := S.arcLength_mono (hy x hx) hu hu'
      have h3 := hy0 x hx (S.output j)
      have h4 := abs_sub_abs_le_abs_sub (y x u (S.output j)) (y x 0 (S.output j))
      linarith
    have hnear : ∀ u, u > μ x 0 → |y x u (S.output j) - f x j| < 1 := by
      intro u hu
      have h1 := hconv x hx 0 u hu
      have h2 := norm_le_pi_norm (S.outputAt (y x) u - f x) j
      simp only [Nat.cast_zero, neg_zero, Real.exp_zero] at h1
      rw [Pi.sub_apply, Real.norm_eq_abs] at h2
      exact lt_of_le_of_lt h2 h1
    by_cases htμ : t ≤ μ x 0
    · have := hcoord t ht htμ
      linarith [hC x hx]
    · push_neg at htμ
      have hca : ContinuousAt (fun u => |y x u (S.output j) - f x j|) (μ x 0) :=
        ((((continuous_apply (S.output j)).continuousAt.comp
          ((hy x hx).2 (μ x 0) h0).continuousAt)).sub continuousAt_const).abs
      have hev : ∀ᶠ u in 𝓝[>] (μ x 0), |y x u (S.output j) - f x j| ≤ 1 :=
        eventually_nhdsWithin_of_forall fun u hu => (hnear u hu).le
      have hlim : |y x (μ x 0) (S.output j) - f x j| ≤ 1 :=
        le_of_tendsto (hca.tendsto.mono_left nhdsWithin_le_nhds) hev
      have h1 := hnear t htμ
      have h2 := hcoord (μ x 0) h0 le_rfl
      have h3 := abs_sub_abs_le_abs_sub (y x t (S.output j)) (f x j)
      have h4 := abs_sub_abs_le_abs_sub (f x j) (y x (μ x 0) (S.output j))
      rw [abs_sub_comm (f x j)] at h4
      linarith
  refine ⟨Y, fun x hx => (hYs x hx).1, ⟨max (Mc + |C| + 2) 1, fun x hx τ hτ => ?_⟩,
    fun x hx r τ hτ => ?_⟩
  · -- uniform bound on the compiled state
    obtain ⟨-, hs0, hsm, -, hcurve⟩ := hYs x hx
    have hsτ : 0 ≤ s x τ := hs0 ▸ hsm.monotone hτ
    refine (pi_norm_le_iff_of_nonneg (le_trans zero_le_one (le_max_right _ _))).2 fun j => ?_
    rw [Real.norm_eq_abs]
    obtain ⟨k, rfl⟩ := e.surjective j
    rw [hcurve τ k]
    rcases k with i | j | a
    · show |S.evalInit x i| ≤ _
      have := (norm_le_pi_norm (S.evalInit x) i).trans (hMc x hx)
      rw [Real.norm_eq_abs] at this
      refine this.trans ((le_max_left _ _).trans' ?_)
      linarith [abs_nonneg C]
    · show |y x (s x τ) (S.output j)| ≤ _
      refine (hout x hx _ hsτ j).trans ((le_max_left _ _).trans' ?_)
      linarith [le_abs_self C]
    · show |jointSurrogate N a _| ≤ _
      exact (jointSurrogate_abs_le_one hN a _).trans (le_max_right _ _)
  · -- the uniform modulus
    obtain ⟨-, hs0, hsm, hθ, hcurve⟩ := hYs x hx
    have hC0 := hC x hx
    set c := S.evalInit x
    obtain ⟨q, hq⟩ : ∃ q : ℝ, q = ((r : ℝ) + 1) ^ k := ⟨_, rfl⟩
    have hr1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) r; linarith
    have hq1 : 1 ≤ q := hq ▸ one_le_pow₀ hr1
    have hμr : μ x r ≤ C * q := hq ▸ (hμ x hx r).2
    have hμ0 : 0 ≤ μ x r := (hμ x hx r).1
    have hLr : S.arcLength (y x) (μ x r) ≤ C * q := hq ▸ hL x hx r
    -- `|yᵢ(u) − cᵢ| ≤ L(u) ≤ C q` on `[0, μ_x(r)]`
    have hcoord : ∀ u ∈ Set.Icc 0 (μ x r), ∀ i, |y x u i - c i| ≤ C * q := by
      intro u hu i
      have h1 := S.abs_sub_init_le_arcLength (hy x hx) i hu.1
      have h2 := S.arcLength_mono (hy x hx) hu.1 hu.2
      rw [(hy x hx).1] at h1
      linarith
    have hclk_le : ∀ u ∈ Set.Icc 0 (μ x r),
        jointClock N (fun i => y x u i - c i) ≤ 1 + (d : ℝ) * (C * q) ^ N := by
      intro u hu
      unfold jointClock
      have : ∑ i, (y x u i - c i) ^ N ≤ ∑ _i : Fin d, (C * q) ^ N :=
        Finset.sum_le_sum fun i _ => by
          rw [← hN.pow_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hcoord u hu i) N
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      linarith
    have hclk_cont : ContinuousOn (fun u => jointClock N (fun i => y x u i - c i))
        (Set.Icc 0 (μ x r)) :=
      fun u hu => ((continuous_jointClock N).continuousAt.comp
        (continuousAt_pi.mpr fun i => ((continuous_apply i).continuousAt.comp
          ((hy x hx).2 u hu.1).continuousAt).sub continuousAt_const)).continuousWithinAt
    have hθle : (∫ u in (0 : ℝ)..(μ x r), jointClock N (fun i => y x u i - c i)) ≤
        μ x r * (1 + (d : ℝ) * (C * q) ^ N) := by
      have h := intervalIntegral.integral_mono_on hμ0
        (hclk_cont.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hμ0)
        ((continuous_const : Continuous fun _ : ℝ => 1 + (d : ℝ) * (C * q) ^ N).intervalIntegrable
          (μ := MeasureTheory.volume) _ _)
        hclk_le
      simpa [mul_comm] using h
    have hqN : q * q ^ N = ((r : ℝ) + 1) ^ (k * (N + 1)) := by
      rw [hq, ← pow_succ', ← pow_mul, mul_comm]
    have hq_le : q ≤ ((r : ℝ) + 1) ^ (k * (N + 1)) := by
      rw [hq]; exact pow_le_pow_right₀ hr1 (Nat.le_mul_of_pos_right k (Nat.succ_pos N))
    have hq0 : 0 ≤ q := le_trans zero_le_one hq1
    have hbound : (∫ u in (0 : ℝ)..(μ x r), jointClock N (fun i => y x u i - c i)) ≤
        C * (1 + (d : ℝ) * C ^ N) * ((r : ℝ) + 1) ^ (k * (N + 1)) :=
      calc (∫ u in (0 : ℝ)..(μ x r), jointClock N (fun i => y x u i - c i))
          ≤ μ x r * (1 + (d : ℝ) * (C * q) ^ N) := hθle
        _ ≤ (C * q) * (1 + (d : ℝ) * (C * q) ^ N) := by gcongr
        _ = C * q + C * (d : ℝ) * C ^ N * (q * q ^ N) := by ring
        _ ≤ C * ((r : ℝ) + 1) ^ (k * (N + 1)) +
              C * (d : ℝ) * C ^ N * ((r : ℝ) + 1) ^ (k * (N + 1)) := by
            rw [hqN]; gcongr
        _ = C * (1 + (d : ℝ) * C ^ N) * ((r : ℝ) + 1) ^ (k * (N + 1)) := by ring
    have hsτ : μ x r < s x τ := by
      have := hsm (lt_of_le_of_lt hbound hτ)
      rwa [hθ _ hμ0] at this
    have hoa : (S.shiftedCompile N).outputAt (Y x) τ = S.outputAt (y x) (s x τ) := by
      funext j
      show Y x τ (e (Sum.inr (Sum.inl j))) = y x (s x τ) (S.output j)
      rw [hcurve τ]
      rfl
    rw [hoa]
    exact hconv x hx r (s x τ) hsτ

/-- [BAC] Thm 4.4, second part, as a class statement ([BAC] Def 2.4, polynomial time):
under the hypotheses of `shiftedCompile_computesOn`, `f` is computed on `K` by a bounded
ℚ-PIVP family with polynomial initial value in time `O((r+1)^{k(N+1)})`. -/
theorem isPolyTimeComputableOn_of_modulus (S : PolyPIVPFamily n d m)
    {f : (Fin n → ℝ) → Fin m → ℝ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (y : (Fin n → ℝ) → ℝ → Fin d → ℝ) (hy : ∀ x ∈ K, S.IsSolution x (y x))
    (μ : (Fin n → ℝ) → TimeModulus) (k : ℕ) (C : ℝ)
    (hconv : ∀ x ∈ K, ∀ r : ℕ, ∀ t : ℝ, t > μ x r →
      ‖S.outputAt (y x) t - f x‖ < Real.exp (-(r : ℝ)))
    (hμ : ∀ x ∈ K, ∀ r : ℕ, 0 ≤ μ x r ∧ μ x r ≤ C * ((r : ℝ) + 1) ^ k)
    (hL : ∀ x ∈ K, ∀ r : ℕ, S.arcLength (y x) (μ x r) ≤ C * ((r : ℝ) + 1) ^ k)
    {N : ℕ} (hN : Even N) (hN2 : 2 ≤ N) (hdeg : ∀ i, (S.field i).totalDegree ≤ N) :
    IsPolyTimeComputableOn f K (k * (N + 1)) := by
  have h := S.shiftedCompile_computesOn hK y hy μ k C hconv hμ hL hN hN2 hdeg
  refine ⟨max (C * (1 + (d : ℝ) * C ^ N)) 1, lt_max_of_lt_right one_pos, hK, _,
    S.shiftedCompile N, ?_⟩
  obtain ⟨Y, hY, hb, hc⟩ := h
  refine ⟨Y, hY, hb, fun x hx r t ht => hc x hx r t (lt_of_le_of_lt ?_ ht)⟩
  have hr : (0 : ℝ) ≤ ((r : ℝ) + 1) ^ (k * (N + 1)) := by positivity
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) hr

end PolyPIVPFamily

/-! ## [BAC] Thm 4.6 for functions, from [BGP, Def 2.3] -/

namespace PolyPIVPFamily

variable {n m : ℕ}

theorem arcLength_continuousOn (S : PolyPIVPFamily n d m) {x : Fin n → ℝ}
    {y : ℝ → Fin d → ℝ} (hy : S.IsSolution x y) {b : ℝ} (hb : 0 ≤ b) :
    ContinuousOn (S.arcLength y) (Set.Icc 0 b) := by
  have h : IntegrableOn (fun u => ‖S.evalField (y u)‖) (Set.Icc 0 b) :=
    (S.speed_continuousOn hy 0 b le_rfl).integrableOn_Icc
  rw [← Set.uIcc_of_le hb] at h ⊢
  exact intervalIntegral.continuousOn_primitive_interval h

@[simp] theorem arcLength_zero (S : PolyPIVPFamily n d m) (y : ℝ → Fin d → ℝ) :
    S.arcLength y 0 = 0 :=
  intervalIntegral.integral_same

end PolyPIVPFamily

/-- [BAC] §2.3 (journal draft `subsec:bgp`) = [BGP, Def 2.3] on a domain `K`: `f` is
*poly-length-computable* on `K` if there are `p ∈ ℚ[y]^d`, `q ∈ ℚ[x]^d` (a `PolyPIVPFamily`)
and a polynomial `Ω` in two variables (real coefficients) such that for every `x ∈ K` the
solution `y_x` of `y' = p(y)`, `y(0) = q(x)` exists on `[0, ∞)` and, for all `t, μ ≥ 0`,
`L_x(t) ≥ Ω(‖x‖, μ) ⇒ ‖(y_x)_o(t) − f(x)‖ ≤ e^{−μ}` and `L_x(t) ≥ t` (sup norms). -/
def IsBGPPolyLengthComputableOn {n m : ℕ} (f : (Fin n → ℝ) → Fin m → ℝ)
    (K : Set (Fin n → ℝ)) : Prop :=
  ∃ d : ℕ, ∃ S : PolyPIVPFamily n d m, ∃ y : (Fin n → ℝ) → ℝ → Fin d → ℝ,
    ∃ Ω : MvPolynomial (Fin 2) ℝ, ∀ x ∈ K, S.IsSolution x (y x) ∧
      (∀ t μ : ℝ, 0 ≤ t → 0 ≤ μ → Ω.eval ![‖x‖, μ] ≤ S.arcLength (y x) t →
        ‖S.outputAt (y x) t - f x‖ ≤ Real.exp (-μ)) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ S.arcLength (y x) t)

/-- `Ω⁺(R, b) = Σ_e |c_e| R^{e₀} b^{e₁}`; `Ω(a, b) ≤ Ω⁺(R, b)` for `0 ≤ a ≤ R`, `b ≥ 0`. -/
noncomputable def absCoeffEval₂ (Ω : MvPolynomial (Fin 2) ℝ) (R b : ℝ) : ℝ :=
  ∑ e ∈ Ω.support, |Ω.coeff e| * (R ^ e 0 * b ^ e 1)

theorem eval_le_absCoeffEval₂ (Ω : MvPolynomial (Fin 2) ℝ) {a R b : ℝ} (ha : 0 ≤ a)
    (haR : a ≤ R) (hb : 0 ≤ b) : Ω.eval ![a, b] ≤ absCoeffEval₂ Ω R b := by
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_le_sum fun e _ => ?_
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have h1 : a ^ e 0 * b ^ e 1 ≤ R ^ e 0 * b ^ e 1 :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha haR _) (pow_nonneg hb _)
  calc Ω.coeff e * (a ^ e 0 * b ^ e 1) ≤ |Ω.coeff e| * (a ^ e 0 * b ^ e 1) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |Ω.coeff e| * (R ^ e 0 * b ^ e 1) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

theorem absCoeffEval₂_nonneg (Ω : MvPolynomial (Fin 2) ℝ) {R b : ℝ} (hR : 0 ≤ R)
    (hb : 0 ≤ b) : 0 ≤ absCoeffEval₂ Ω R b :=
  Finset.sum_nonneg fun e _ => by positivity

/-- `Ω⁺(R, b) ≤ (Σ_e |c_e| R^{e₀}) b^{deg Ω}` for `b ≥ 1`. -/
theorem absCoeffEval₂_le (Ω : MvPolynomial (Fin 2) ℝ) {R b : ℝ} (hR : 0 ≤ R) (hb : 1 ≤ b) :
    absCoeffEval₂ Ω R b ≤
      (∑ e ∈ Ω.support, |Ω.coeff e| * R ^ e 0) * b ^ Ω.totalDegree := by
  rw [absCoeffEval₂, Finset.sum_mul]
  refine Finset.sum_le_sum fun e he => ?_
  have h1 : e 1 ≤ Ω.totalDegree := by
    have h := le_totalDegree he
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at h
    omega
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb h1) (pow_nonneg hR _)) (abs_nonneg _)

/-- [BAC] Thm 4.6 (journal draft `thm:poly-equiv`) for functions on a compact domain, from the
BGP definition itself: if `f` is poly-length-computable on the compact set `K` in the sense of
[BGP, Def 2.3], then `f` is computed on `K` by a bounded ℚ-PIVP family with polynomial initial
value in polynomial time ([BAC] Def 2.4), via the shifted compilation (Thm 4.4, second part).
The proof sets `R = max_K ‖x‖`, `ω(r) = Ω⁺(R, r+1)` and, for each `x`, a time `μ_x(r)` with
`L_x(μ_x(r)) = ω(r)` (so `μ_x(r) ≤ ω(r)` by the normalization). -/
theorem isPolyTimeComputableOn_of_isBGPPolyLengthComputableOn {n m : ℕ}
    {f : (Fin n → ℝ) → Fin m → ℝ} {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (h : IsBGPPolyLengthComputableOn f K) : ∃ k : ℕ, IsPolyTimeComputableOn f K k := by
  obtain ⟨d, S, y, Ω, hS⟩ := h
  obtain ⟨R₀, hR₀⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  set R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hxR : ∀ x ∈ K, ‖x‖ ≤ R := fun x hx => by
    have := hR₀ x hx
    rw [norm_norm] at this
    exact this.trans (le_max_left _ _)
  set ω : ℕ → ℝ := fun r => absCoeffEval₂ Ω R ((r : ℝ) + 1)
  have hω0 : ∀ r : ℕ, 0 ≤ ω r := fun r => absCoeffEval₂_nonneg Ω hR (by positivity)
  have hex : ∀ x, ∀ r : ℕ, ∃ t₀ : ℝ, x ∈ K →
      (t₀ ∈ Set.Icc (0 : ℝ) (ω r) ∧ S.arcLength (y x) t₀ = ω r) := by
    intro x r
    by_cases hx : x ∈ K
    · obtain ⟨hsol, -, hnorm⟩ := hS x hx
      have hivt := intermediate_value_Icc (hω0 r) (S.arcLength_continuousOn hsol (hω0 r))
      have hmem : ω r ∈ Set.Icc (S.arcLength (y x) 0) (S.arcLength (y x) (ω r)) :=
        ⟨by rw [PolyPIVPFamily.arcLength_zero]; exact hω0 r, hnorm _ (hω0 r)⟩
      obtain ⟨t₀, ht₀, hL⟩ := hivt hmem
      exact ⟨t₀, fun _ => ⟨ht₀, hL⟩⟩
    · exact ⟨0, fun h => absurd h hx⟩
  choose μ hμ using hex
  set C := ∑ e ∈ Ω.support, |Ω.coeff e| * R ^ e 0
  have hωC : ∀ r : ℕ, ω r ≤ C * ((r : ℝ) + 1) ^ Ω.totalDegree := fun r =>
    absCoeffEval₂_le Ω hR (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])
  have hconv : ∀ x ∈ K, ∀ r : ℕ, ∀ t : ℝ, t > μ x r →
      ‖S.outputAt (y x) t - f x‖ < Real.exp (-(r : ℝ)) := by
    intro x hx r t ht
    obtain ⟨hsol, hc, -⟩ := hS x hx
    obtain ⟨hI, hL⟩ := hμ x r hx
    have ht0 : 0 ≤ t := hI.1.trans ht.le
    have hle : Ω.eval ![‖x‖, (r : ℝ) + 1] ≤ S.arcLength (y x) t :=
      calc Ω.eval ![‖x‖, (r : ℝ) + 1] ≤ ω r :=
            eval_le_absCoeffEval₂ Ω (norm_nonneg x) (hxR x hx) (by positivity)
        _ = S.arcLength (y x) (μ x r) := hL.symm
        _ ≤ S.arcLength (y x) t := S.arcLength_mono hsol hI.1 ht.le
    calc ‖S.outputAt (y x) t - f x‖ ≤ Real.exp (-((r : ℝ) + 1)) :=
          hc t _ ht0 (by positivity) hle
      _ < Real.exp (-(r : ℝ)) := Real.exp_lt_exp.mpr (by linarith)
  have hdeg : ∀ i, (S.field i).totalDegree ≤
      2 * (Finset.univ.sup fun j => (S.field j).totalDegree) + 2 :=
    fun i => by
      have := Finset.le_sup (f := fun j => (S.field j).totalDegree) (Finset.mem_univ i)
      simp only at this
      omega
  have hNe : Even (2 * (Finset.univ.sup fun j => (S.field j).totalDegree) + 2) :=
    ⟨(Finset.univ.sup fun j => (S.field j).totalDegree) + 1, by ring⟩
  exact ⟨_, S.isPolyTimeComputableOn_of_modulus hK y (fun x hx => (hS x hx).1) μ
    Ω.totalDegree C hconv
    (fun x hx r => ⟨(hμ x r hx).1.1, (hμ x r hx).1.2.trans (hωC r)⟩)
    (fun x hx r => (hμ x r hx).2.le.trans (hωC r)) hNe (by omega) hdeg⟩

/-! ## Non-vacuity: `f(x) = x` on the unit ball, with an unbounded clock -/

/-- `c' = 0`, `c(0) = x`; `s' = 1`, `s(0) = 0` (unbounded); `u' = c − u`, `u(0) = 0`; output
`u = x (1 − e^{−t}) → x`. The clock `s` makes the sup-norm speed `1`, so `L(t) = t`. -/
noncomputable def idTrackSys : PolyPIVPFamily 1 3 1 where
  field := ![0, 1, X 0 - X 2]
  init := ![X 0, 0, 0]
  output := ![2]

/-- The explicit solution `(x₀, t, x₀(1 − e^{−t}))`. -/
noncomputable def idTrackSol (x : Fin 1 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  ![x 0, t, x 0 * (1 - Real.exp (-t))]

theorem idTrackSys_evalField (x : Fin 1 → ℝ) (t : ℝ) :
    idTrackSys.evalField (idTrackSol x t) = ![0, 1, x 0 * Real.exp (-t)] := by
  funext i
  fin_cases i <;> simp [idTrackSys, idTrackSol, PolyPIVPFamily.evalField] <;> ring

theorem idTrackSys_isSolution (x : Fin 1 → ℝ) : idTrackSys.IsSolution x (idTrackSol x) := by
  refine ⟨?_, fun t _ => ?_⟩
  · funext i
    fin_cases i <;> simp [idTrackSys, idTrackSol, PolyPIVPFamily.evalInit]
  · rw [idTrackSys_evalField]
    refine hasDerivAt_pi.mpr fun i => ?_
    fin_cases i
    · simpa [idTrackSol] using hasDerivAt_const t (x 0)
    · simpa [idTrackSol] using hasDerivAt_id t
    · have h := ((((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).const_sub 1).const_mul
        (x 0))
      convert h using 1
      simp

theorem idTrackSys_arcLength {x : Fin 1 → ℝ} (hx : ‖x‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    idTrackSys.arcLength (idTrackSol x) t = t := by
  have hx0 : |x 0| ≤ 1 := by simpa using (norm_le_pi_norm x 0).trans hx
  have h : ∀ u ∈ Set.uIcc (0 : ℝ) t,
      ‖idTrackSys.evalField (idTrackSol x u)‖ = (1 : ℝ) := by
    intro u hu
    rw [Set.uIcc_of_le ht] at hu
    rw [idTrackSys_evalField]
    have he : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hu.1])
    have hb : |x 0 * Real.exp (-u)| ≤ 1 := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      nlinarith [abs_nonneg (x 0), Real.exp_pos (-u)]
    refine le_antisymm ((pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_) ?_
    · fin_cases i
      · simp
      · simp
      · simpa using hb
    · have := norm_le_pi_norm (![0, 1, x 0 * Real.exp (-u)] : Fin 3 → ℝ) 1
      simpa using this
  unfold PolyPIVPFamily.arcLength
  rw [intervalIntegral.integral_congr h]
  simp

theorem idTrackSys_output_err {x : Fin 1 → ℝ} (hx : ‖x‖ ≤ 1) {t : ℝ} :
    ‖idTrackSys.outputAt (idTrackSol x) t - x‖ ≤ Real.exp (-t) := by
  have hx0 : |x 0| ≤ 1 := by simpa using (norm_le_pi_norm x 0).trans hx
  refine (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).mpr fun j => ?_
  fin_cases j
  simp only [PolyPIVPFamily.outputAt, idTrackSys, idTrackSol, Pi.sub_apply]
  simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, Real.norm_eq_abs]
  rw [show x 0 * (1 - Real.exp (-t)) - x 0 = -(x 0 * Real.exp (-t)) by ring, abs_neg, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  nlinarith [Real.exp_pos (-t), abs_nonneg (x 0)]

/-- Non-vacuity of the function part of [BAC] Thm 4.4 and of [BAC] Def 2.4: the identity on the
closed unit ball of `ℝ¹` is computed by the shifted compilation of `idTrackSys` (an unbounded
system) in time `O((r+1)^3)`. -/
theorem idTrackSys_polyTime :
    IsPolyTimeComputableOn (fun x : Fin 1 → ℝ => x) (Metric.closedBall 0 1) 3 := by
  have hdeg : ∀ i, (idTrackSys.field i).totalDegree ≤ 2 := by
    intro i
    fin_cases i
    · simp [idTrackSys]
    · simp [idTrackSys]
    · show (X 0 - X 2 : MvPolynomial (Fin 3) ℚ).totalDegree ≤ 2
      refine (totalDegree_sub _ _).trans ?_
      rw [totalDegree_X, totalDegree_X]; norm_num
  have h := idTrackSys.isPolyTimeComputableOn_of_modulus (isCompact_closedBall 0 1)
    (fun x => idTrackSol x) (fun x _ => idTrackSys_isSolution x) (fun _ r => (r : ℝ)) 1 1
    (fun x hx r t ht => by
      have hx' : ‖x‖ ≤ 1 := by simpa using hx
      calc _ ≤ Real.exp (-t) := idTrackSys_output_err hx'
        _ < Real.exp (-(r : ℝ)) := Real.exp_lt_exp.mpr (by linarith))
    (fun x _ r => ⟨Nat.cast_nonneg r, by simp⟩)
    (fun x hx r => by
      have hx' : ‖x‖ ≤ 1 := by simpa using hx
      rw [idTrackSys_arcLength hx' (Nat.cast_nonneg r)]
      simp)
    (N := 2) even_two le_rfl hdeg
  simpa using h

/-- Non-vacuity of `IsBGPPolyLengthComputableOn`: the identity on the unit ball, by
`idTrackSys` with `Ω(a, μ) = μ`. -/
theorem idTrackSys_isBGPPolyLengthComputableOn :
    IsBGPPolyLengthComputableOn (fun x : Fin 1 → ℝ => x) (Metric.closedBall 0 1) := by
  refine ⟨3, idTrackSys, fun x => idTrackSol x, X 1, fun x hx => ⟨idTrackSys_isSolution x,
    fun t μ ht _ hL => ?_, fun t ht => ?_⟩⟩
  · have hx' : ‖x‖ ≤ 1 := by simpa using hx
    rw [idTrackSys_arcLength hx' ht] at hL
    have hμ : μ ≤ t := by simpa using hL
    exact (idTrackSys_output_err hx').trans (Real.exp_le_exp.mpr (by linarith))
  · have hx' : ‖x‖ ≤ 1 := by simpa using hx
    rw [idTrackSys_arcLength hx' ht]

end Ripple
