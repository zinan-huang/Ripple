/-
  Ripple.LPP.Compiler — the faithful GPAC ⇒ PLPP compiler ([LPP] Main Theorem, hard direction)

  For `α ∈ [0, 1]`, a bounded ℚ-PIVP computing `α` with a CRN decomposition
  (`CertifiedBoundedTimeComputable` + `PolyCRNDecomposition`) gives `IsPLPPComputable α`
  (`isPLPPComputable_of_certified`), hence `IsLPPComputable α` by [LPP] Theorem 17
  (`isLPPComputable_of_certified`).

  Route ([LPP] §3, with the repairs recorded in `docs/refactor/S1-LPP-PAPER.md`):

  * preprocessing (existing): the saturating surrogate (`Saturating.saturating_surrogate_cbtc`)
    bounds the output by a rational `U < 1`; the zero-init wrapper
    (`Algebraic.certified_zero_init_wrapper_sharp`) makes the output start at `0`;
  * Stage 1, [LPP] Theorem 12: the v-variable system, here with ℚ coefficients
    (`stage1_vvariable_rat`; the existing `stage1_vvariable*` only state real coefficients);
  * Stage 2, [LPP] Theorem 13: λ-trick, ε-dilation and balancing dilation with rational `ε, c`
    (existing analysis `stage2_ode_from_room`), read as a rational cubic transfer tensor
    (`CubicTransfers.ofBalancingDilation`);
  * Stage 3, [LPP] Theorem 15 (repaired): the upper-triangular half-product lift
    `CubicTransfers.symmetricLift`, formally conservative;
  * Stage 4, [LPP] Construction 1: `SynPPBalance.toPLPPTransitions`, whose balance field is the
    normalisation constant `κ ∈ ℚ` times the lifted field, so time is rescaled by `κ`;
  * readout: the half-products read `x_o = z_{oo} + ½ Σ_{j ≠ o} z_{oj}`, a fractional
    readout, turned into a marked set by 2-fold replication
    (`isPLPPComputable_of_fractional_readout`).
-/

import Ripple.LPP.Computation
import Ripple.LPP.Determinization
import Ripple.LPP.Replication
import Ripple.LPP.SymmetricSquaring
import Ripple.LPP.Stage2Convergence
import Ripple.LPP.ZeroInitWrapper
import Ripple.LPP.SaturatingSurrogate

namespace Ripple

open Filter Topology

/-! ## Stage 1 with rational coefficients ([LPP] Theorem 12) -/

section VVariableRational

variable {d : ℕ} {P : PolyPIVP d} (pcd : PolyCRNDecomposition d P) (D : ℕ)

/-- Rational form of the production coefficient `vCoeffA`. -/
noncomputable def vCoeffAQ (α a b : MIndex d D) : ℚ :=
  ∑ k : Fin d,
    if hk : 0 < (α k : ℕ) then
      if a = α.sub_basis k hk then
        ((α k : ℕ) : ℚ) * (pcd.prod k).coeff b.toFinsupp
      else 0
    else 0

/-- Rational form of the degradation coefficient `vCoeffB`. -/
noncomputable def vCoeffBQ (α a : MIndex d D) : ℚ :=
  ∑ k : Fin d, ((α k : ℕ) : ℚ) * (pcd.degr k).coeff a.toFinsupp

theorem vCoeffA_eq_cast (α a b : MIndex d D) :
    vCoeffA pcd D α a b = (vCoeffAQ pcd D α a b : ℝ) := by
  unfold vCoeffA vCoeffAQ
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

theorem vCoeffB_eq_cast (α a : MIndex d D) :
    vCoeffB pcd D α a = (vCoeffBQ pcd D α a : ℝ) := by
  unfold vCoeffB vCoeffBQ
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp

theorem vCoeffAQ_nonneg (α a b : MIndex d D) : 0 ≤ vCoeffAQ pcd D α a b := by
  have h := vCoeffA_nonneg pcd D α a b
  rw [vCoeffA_eq_cast] at h
  exact_mod_cast h

theorem vCoeffBQ_nonneg (α a : MIndex d D) : 0 ≤ vCoeffBQ pcd D α a := by
  have h := vCoeffB_nonneg pcd D α a
  rw [vCoeffB_eq_cast] at h
  exact_mod_cast h

end VVariableRational

/-- **Stage 1 with rational coefficients** ([LPP] Theorem 12). The v-variable system of a
certified CRN computation: a quadratic CRN-form field with nonnegative *rational* coefficients
`A`, `B`, nonnegative rational initial values, whose output trajectory *is* the input's output
trajectory and whose modulus is the input's. Strengthens `stage1_vvariable_with_output_eq_and_modulus`
(real `A`, `B`) to the coefficient field the PLPP compiler needs. -/
theorem stage1_vvariable_rat {d : ℕ} {α : ℝ}
    (btc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d btc.pivp) :
    ∃ (d' : ℕ) (btc' : SemanticBTC d' α)
      (A : Fin d' → Fin d' → Fin d' → ℚ) (B : Fin d' → Fin d' → ℚ),
      (∀ i a b, 0 ≤ A i a b) ∧
      (∀ i a, 0 ≤ B i a) ∧
      (∀ i x, btc'.pivp.field x i =
        (∑ a, ∑ b, (A i a b : ℝ) * x a * x b) - (∑ a, (B i a : ℝ) * x a) * x i) ∧
      (∀ i, 0 ≤ btc'.pivp.init i) ∧
      (∀ i, ∃ q : ℚ, btc'.pivp.init i = ↑q) ∧
      (∀ t : ℝ, btc'.sol.trajectory t btc'.pivp.output
          = btc.sol.trajectory t btc.pivp.output) ∧
      (∀ r : ℕ, btc'.modulus r = btc.modulus r) := by
  by_cases hd : d = 0
  · subst hd
    exact Fin.elim0 btc.pivp.output
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
  let D := max 1 (Finset.sup' Finset.univ
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    (fun i => max ((pcd.prod i).totalDegree) ((pcd.degr i).totalDegree)))
  have hD : 1 ≤ D := le_max_left 1 _
  let d' := Fintype.card (MIndex d D)
  let enc : MIndex d D ≃ Fin d' := Fintype.equivFin (MIndex d D)
  let A : Fin d' → Fin d' → Fin d' → ℝ :=
    fun i a b => vCoeffA pcd D (enc.symm i) (enc.symm a) (enc.symm b)
  let B : Fin d' → Fin d' → ℝ :=
    fun i a => vCoeffB pcd D (enc.symm i) (enc.symm a)
  let vfield : (Fin d' → ℝ) → Fin d' → ℝ := fun x i =>
    (∑ a : Fin d', ∑ b : Fin d', A i a b * x a * x b) -
    (∑ a : Fin d', B i a * x a) * x i
  let vinit : Fin d' → ℝ := fun i => vInit btc.pivp (enc.symm i)
  let voutput : Fin d' := enc (MIndex.basis hD btc.pivp.output)
  let vpivp : PIVP d' := ⟨vfield, vinit, voutput⟩
  let vtraj : ℝ → Fin d' → ℝ := fun t i => (enc.symm i).eval (btc.sol.trajectory t)
  have vinit_eq : vtraj 0 = vinit := by
    ext i
    simp only [vtraj, vinit, vInit]
    congr 1
    have := btc.sol.init_cond
    ext k
    simp [PolyPIVP.toPIVP] at this
    exact congr_fun this k
  let vsol : PIVP.Solution vpivp := {
    trajectory := vtraj
    init_cond := vinit_eq
    is_solution := fun t ht => by
      rw [hasDerivAt_pi]
      intro i
      have hx_k := fun k => (hasDerivAt_pi.mp (btc.sol.is_solution t ht)) k
      have hmon := hasDerivAt_monomial (enc.symm i) btc.sol.trajectory _ t hx_k
      change HasDerivAt (fun s => (enc.symm i).eval (btc.sol.trajectory s))
        (vpivp.field (vtraj t) i) t
      have hDprod : ∀ k, (pcd.prod k).totalDegree ≤ D := fun k =>
        le_trans (le_max_left _ _)
          (le_trans (Finset.le_sup'
            (fun i => max ((pcd.prod i).totalDegree) ((pcd.degr i).totalDegree))
            (Finset.mem_univ k)) (le_max_right 1 _))
      have hDdegr : ∀ k, (pcd.degr k).totalDegree ≤ D := fun k =>
        le_trans (le_max_right _ _)
          (le_trans (Finset.le_sup'
            (fun i => max ((pcd.prod i).totalDegree) ((pcd.degr i).totalDegree))
            (Finset.mem_univ k)) (le_max_right 1 _))
      have halg : vpivp.field (vtraj t) i =
        ∑ k : Fin d, (∏ j ∈ Finset.univ.erase k,
          btc.sol.trajectory t j ^ ((enc.symm i j : ℕ))) *
          (((enc.symm i k : ℕ) : ℝ) * btc.sol.trajectory t k ^ ((enc.symm i k : ℕ) - 1) *
            btc.pivp.toPIVP.field (btc.sol.trajectory t) k) := by
        simp only [vpivp, vfield, A, B, vtraj]
        rw [Equiv.sum_comp enc.symm (fun α =>
              ∑ b : Fin d',
                vCoeffA pcd D (enc.symm i) α (enc.symm b) *
                  α.eval (btc.sol.trajectory t) *
                  (enc.symm b).eval (btc.sol.trajectory t)),
            Equiv.sum_comp enc.symm (fun α =>
              vCoeffB pcd D (enc.symm i) α *
                α.eval (btc.sol.trajectory t))]
        conv_lhs =>
          arg 1; arg 2; ext α
          rw [Equiv.sum_comp enc.symm (fun β =>
                vCoeffA pcd D (enc.symm i) α β *
                  α.eval (btc.sol.trajectory t) *
                  β.eval (btc.sol.trajectory t))]
        have hcr := vfield_chain_rule_eq pcd D hDprod hDdegr
            (enc.symm i) (btc.sol.trajectory t)
        simp only [PolyPIVP.evalField] at hcr
        convert hcr using 2
      rw [halg]
      exact hmon }
  have vbounded : vpivp.IsBounded vsol.trajectory := by
    obtain ⟨M₀, hM₀_pos, hM₀_bound⟩ := btc.bounded
    let M := max 1 M₀
    have hM1 : 1 ≤ M := le_max_left 1 M₀
    have hM_pos : 0 < M := lt_of_lt_of_le one_pos hM1
    refine ⟨M ^ (d * D), by positivity, fun t ht => ?_⟩
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rw [Real.norm_eq_abs]
    calc |(enc.symm i).eval (btc.sol.trajectory t)|
        ≤ M ^ (enc.symm i).degree := by
          apply MIndex.eval_bounded _ _ M hM_pos
          intro k
          calc |btc.sol.trajectory t k|
              = ‖btc.sol.trajectory t k‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖btc.sol.trajectory t‖ := norm_le_pi_norm _ k
            _ ≤ M₀ := hM₀_bound t ht
            _ ≤ M := le_max_right 1 M₀
      _ ≤ M ^ (d * D) := pow_le_pow_right₀ hM1 (MIndex.degree_le _)
  have vconv : ∀ r : ℕ, ∀ t : ℝ, t > btc.modulus r →
      |vsol.trajectory t vpivp.output - α| < Real.exp (-(r : ℝ)) := by
    intro r t ht
    simp only [vsol, vtraj, vpivp, voutput]
    rw [Equiv.symm_apply_apply, MIndex.eval_basis]
    exact btc.convergence r t ht
  let btc' : SemanticBTC d' α :=
    ⟨vpivp, vsol, btc.modulus, vbounded, vconv⟩
  have h_output_eq : ∀ t : ℝ,
      btc'.sol.trajectory t btc'.pivp.output
        = btc.sol.trajectory t btc.pivp.output := by
    intro t
    show vsol.trajectory t vpivp.output = _
    simp only [vsol, vtraj, vpivp, voutput]
    rw [Equiv.symm_apply_apply, MIndex.eval_basis]
  refine ⟨d', btc',
    fun i a b => vCoeffAQ pcd D (enc.symm i) (enc.symm a) (enc.symm b),
    fun i a => vCoeffBQ pcd D (enc.symm i) (enc.symm a),
    fun i a b => vCoeffAQ_nonneg pcd D _ _ _,
    fun i a => vCoeffBQ_nonneg pcd D _ _,
    fun i x => ?_,
    fun i => vInit_nonneg btc.pivp pcd.init_nonneg _,
    fun i => vInit_rational btc.pivp _,
    h_output_eq, fun r => rfl⟩
  show vfield x i = _
  simp only [vfield, A, B, vCoeffA_eq_cast, vCoeffB_eq_cast]

/-! ## Half-products on the simplex -/

/-- Each half-product is the sum of the ordered products in its fibre:
`z_{ij} = Σ_{(r,p) ↦ {i,j}} x_r x_p`. -/
theorem halfProduct_eq_sum_fibre {d : ℕ} (x : Fin d → ℝ) (k : Fin (upperPairDim d)) :
    halfProduct x k = ∑ r, ∑ p, if k = upperPairFin r p then x r * x p else 0 := by
  obtain ⟨i, j, rfl⟩ : ∃ i j, upperPairFin i j = k := ⟨_, _, CubicTransfers.upperPairFin_decode k⟩
  rw [halfProduct_upperPairFin]
  have hr : ∀ r : Fin d,
      (∑ p, if upperPairFin i j = upperPairFin r p then x r * x p else 0) =
        x r * ((pairScale i j : ℝ) *
          ((if i = r then x j else 0) + if j = r then x i else 0)) / 2 := by
    intro r
    rw [← sum_partner_upperPair_indicator x i j r, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun r _ => hr r]
  have hsplit : ∀ r : Fin d,
      x r * ((pairScale i j : ℝ) * ((if i = r then x j else 0) + if j = r then x i else 0)) / 2 =
        (if i = r then (pairScale i j : ℝ) * x i * x j / 2 else 0) +
          (if j = r then (pairScale i j : ℝ) * x i * x j / 2 else 0) := by
    intro r
    split_ifs with h1 h2 h2 <;> subst_vars <;> ring
  rw [Finset.sum_congr rfl fun r _ => hsplit r, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  ring

/-- The half-products of `x` sum to `(Σ x)²`; on the simplex the lift stays on the simplex. -/
theorem sum_halfProduct {d : ℕ} (x : Fin d → ℝ) :
    ∑ k, halfProduct x k = (∑ i, x i) ^ 2 := by
  rw [Finset.sum_congr rfl fun k _ => halfProduct_eq_sum_fibre x k, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun r _ => Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [sq, Finset.sum_mul_sum]

theorem halfProduct_nonneg {d : ℕ} {x : Fin d → ℝ} (hx : ∀ i, 0 ≤ x i)
    (k : Fin (upperPairDim d)) : 0 ≤ halfProduct x k := by
  obtain ⟨i, j, rfl⟩ : ∃ i j, upperPairFin i j = k := ⟨_, _, CubicTransfers.upperPairFin_decode k⟩
  rw [halfProduct_upperPairFin]
  have := pairScale_pos i j
  exact mul_nonneg (mul_nonneg (by exact_mod_cast this.le) (hx _)) (hx _)

theorem halfProduct_rational {d : ℕ} {x : Fin d → ℝ} (hx : ∀ i, ∃ q : ℚ, x i = (q : ℝ))
    (k : Fin (upperPairDim d)) : ∃ q : ℚ, halfProduct x k = (q : ℝ) := by
  choose q hq using hx
  obtain ⟨i, j, rfl⟩ : ∃ i j, upperPairFin i j = k := ⟨_, _, CubicTransfers.upperPairFin_decode k⟩
  rw [halfProduct_upperPairFin, hq i, hq j]
  exact ⟨pairScale i j * q i * q j, by push_cast; ring⟩

/-- The readout weights of the half-product lift for the output `o` (out of `2`): `2` on
`z_{oo}`, `1` on `z_{oj}` for `j ≠ o`, `0` elsewhere, written as the count
`#{p | k = ⟨o, p⟩} + [k = ⟨o, o⟩]`. -/
noncomputable def halfProductReadoutWeight {d : ℕ} (o : Fin d) (k : Fin (upperPairDim d)) : ℕ :=
  (∑ p, if k = upperPairFin o p then 1 else 0) + if k = upperPairFin o o then 1 else 0

theorem upperPairFin_left_injective {d : ℕ} (o : Fin d) :
    Function.Injective (upperPairFin o) := by
  intro p q h
  rcases (upperPairFin_eq_iff o p o q).mp h with ⟨_, h⟩ | ⟨h₁, h₂⟩
  · exact h
  · exact h₂.trans h₁

theorem halfProductReadoutWeight_le_two {d : ℕ} (o : Fin d) (k : Fin (upperPairDim d)) :
    halfProductReadoutWeight o k ≤ 2 := by
  unfold halfProductReadoutWeight
  have h1 : (∑ p, if k = upperPairFin o p then 1 else 0) ≤ 1 := by
    by_cases hk : ∃ p, k = upperPairFin o p
    · obtain ⟨p₀, rfl⟩ := hk
      rw [Finset.sum_eq_single p₀
        (fun b _ hb => if_neg fun h => hb (upperPairFin_left_injective o h).symm) (by simp)]
      simp
    · push Not at hk
      rw [Finset.sum_eq_zero fun p _ => if_neg (hk p)]
      norm_num
  have h2 : (if k = upperPairFin o o then 1 else 0) ≤ 1 := by split_ifs <;> norm_num
  omega

/-- The weighted half-product readout is the output coordinate times the total mass:
`z_{oo} + ½ Σ_{j ≠ o} z_{oj} = x_o (Σ x)`. -/
theorem halfProduct_readout {d : ℕ} (o : Fin d) (x : Fin d → ℝ) :
    ∑ k, ((halfProductReadoutWeight o k : ℕ) : ℝ) / 2 * halfProduct x k =
      x o * ∑ i, x i := by
  have hw : ∀ k, ((halfProductReadoutWeight o k : ℕ) : ℝ) / 2 * halfProduct x k =
      (∑ p, if k = upperPairFin o p then halfProduct x k / 2 else 0) +
        (if k = upperPairFin o o then halfProduct x k / 2 else 0) := by
    intro k
    unfold halfProductReadoutWeight
    push_cast
    rw [add_div, add_mul, Finset.sum_div, Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring
    · split_ifs <;> ring
  rw [Finset.sum_congr rfl fun k _ => hw k, Finset.sum_add_distrib, Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, halfProduct_upperPairFin]
  rw [Finset.mul_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ o),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ o)]
  have hoff : ∀ p ∈ (Finset.univ : Finset (Fin d)).erase o,
      (pairScale o p : ℝ) * x o * x p / 2 = x o * x p := by
    intro p hp
    have hp' : o ≠ p := Ne.symm (Finset.ne_of_mem_erase hp)
    simp only [pairScale, hp', if_false]
    push_cast
    ring
  rw [Finset.sum_congr rfl hoff]
  simp only [pairScale, if_true, Rat.cast_one]
  ring

/-! ## Stages 2-4 and the readout -/

/-- A modulus statement on `t ≥ 0` gives convergence. -/
theorem tendsto_of_modulus_nonneg {x : ℝ → ℝ} {α : ℝ} (μ : ℕ → ℝ)
    (h : ∀ r : ℕ, ∀ t : ℝ, 0 ≤ t → t > μ r → |x t - α| < Real.exp (-(r : ℝ))) :
    Tendsto x atTop (𝓝 α) := by
  rw [Metric.tendsto_atTop']
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (-Real.log ε)
  have hr : Real.exp (-(n : ℝ)) < ε := by
    rwa [← Real.lt_log_iff_exp_lt hε, neg_lt]
  refine ⟨max (μ n) 0, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := (le_max_right _ _).trans ht.le
  have htμ : t > μ n := lt_of_le_of_lt (le_max_left _ _) ht
  rw [Real.dist_eq]
  exact (h n t ht0 htμ).trans hr

/-- **Stages 2-4 with the readout.** A Stage 1 system (quadratic CRN form with nonnegative
rational coefficients, rational nonnegative initial value, output starting at `0`) that satisfies
the Remark 14 room condition for a rational `c ∈ (0, 1]` is computed by a PLPP.

Stage 2 is the existing analysis `stage2_ode_from_room` with `ε = 1/c`; its field is the
rational cubic transfer tensor `ofBalancingDilation A' B'`; Stage 3 lifts the trajectory to
half-products (`symmetricLift`), Stage 4 is `toPLPPTransitions` with the time rescaled by the
normalisation `κ`, and the readout `z_{oo} + ½ Σ_{j ≠ o} z_{oj}` is realised by 2-fold
replication. -/
theorem isPLPPComputable_of_stage1 {d : ℕ} [NeZero d] {α : ℝ}
    (btc : SemanticBTC d α)
    (A : Fin d → Fin d → Fin d → ℚ) (B : Fin d → Fin d → ℚ)
    (hA : ∀ i a b, 0 ≤ A i a b) (hB : ∀ i a, 0 ≤ B i a)
    (h_field : ∀ i x, btc.pivp.field x i =
      (∑ a, ∑ b, (A i a b : ℝ) * x a * x b) - (∑ a, (B i a : ℝ) * x a) * x i)
    (h_init_nn : ∀ i, 0 ≤ btc.pivp.init i)
    (h_init_rat : ∀ i, ∃ q : ℚ, btc.pivp.init i = ↑q)
    (c : ℚ) (hc_pos : 0 < c) (hc_le_1 : c ≤ 1)
    (h_sum_le : (c : ℝ) * ∑ j, btc.pivp.init j ≤ 1)
    (h_zero_init : btc.pivp.init btc.pivp.output = 0)
    (h_room : ∀ σ, 0 ≤ σ →
      btc.sol.trajectory σ btc.pivp.output
        + (c : ℝ) * ∑ j ∈ Finset.univ.erase btc.pivp.output, btc.sol.trajectory σ j
          ≤ 1 - c) :
    IsPLPPComputable α := by
  set o := btc.pivp.output with ho
  set εQ : ℚ := 1 / c with hεQ
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc_pos
  have hcR1 : (c : ℝ) ≤ 1 := by exact_mod_cast hc_le_1
  have hεR : (0 : ℝ) < (εQ : ℝ) := by
    have : (0 : ℚ) < εQ := by rw [hεQ]; exact one_div_pos.mpr hc_pos
    exact_mod_cast this
  have hεc : (1 : ℝ) ≤ (εQ : ℝ) * c := by
    have h1 : εQ * c = 1 := by rw [hεQ, one_div, inv_mul_cancel₀ hc_pos.ne']
    have h2 : ((εQ : ℝ) * c) = 1 := by exact_mod_cast h1
    exact h2.ge
  -- real coefficient views
  let AR : Fin d → Fin d → Fin d → ℝ := fun i a b => (A i a b : ℝ)
  let BR : Fin d → Fin d → ℝ := fun i a => (B i a : ℝ)
  have hAR : ∀ i a b, 0 ≤ AR i a b := fun i a b => Rat.cast_nonneg.mpr (hA i a b)
  have hBR : ∀ i a, 0 ≤ BR i a := fun i a => Rat.cast_nonneg.mpr (hB i a)
  -- Stage 2: the trajectory
  obtain ⟨sol, h_conv⟩ :=
    stage2_ode_from_room btc (εQ : ℝ) (c : ℝ) (c : ℝ) hεR hcR hcR1 hcR le_rfl hεc
      AR BR hAR hBR h_field h_init_nn h_sum_le h_zero_init h_room
  let P := stage2_pivp (εQ : ℝ) (c : ℝ) btc.pivp
  have crn : IsCRNImplementable d btc.pivp.field := {
    prod := fun i x => ∑ a, ∑ b, AR i a b * x a * x b
    degr := fun i x => ∑ a, BR i a * x a
    prod_pos := fun i x hx => Finset.sum_nonneg fun a _ =>
      Finset.sum_nonneg fun b _ => mul_nonneg (mul_nonneg (hAR i a b) (hx a)) (hx b)
    degr_pos := fun i x hx => Finset.sum_nonneg fun a _ => mul_nonneg (hBR i a) (hx a)
    field_eq := fun x i => h_field i x }
  have tpp' : IsTPPImplementable (d + 1) P.field :=
    stage2_field_tpp (o := o) hεR.le hcR crn
  have s' : Stage2CubicForm (d + 1) P.field :=
    stage2_field_cubicForm (o := o) hεR.le hcR AR BR hAR hBR h_field
  have h_simplex : ∀ t, 0 ≤ t → ∑ i, sol.trajectory t i = 1 :=
    fun t ht => conservative_trajectory_simplex sol tpp'.conservative
      (stage2_init_simplex (c : ℝ) btc.pivp.init) ht
  have h_nn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ sol.trajectory t i :=
    fun t ht => crn_nonneg_invariance sol tpp'.toIsCRNImplementable
      (stage2_init_nonneg hcR.le h_init_nn h_sum_le)
      (cubicForm_locally_lipschitz s') t ht
  -- the Stage 2 field as a rational cubic transfer tensor
  let cf : Fin d → ℚ := fun j => if j = o then 1 else c
  have hcf : ∀ j, 0 < cf j := fun j => by
    simp only [cf]; split_ifs
    · exact one_pos
    · exact hc_pos
  let A' : Fin d → Fin d → Fin d → ℚ := fun i a b =>
    (if i = o then 1 else c) * εQ * A i a b / (cf a * cf b)
  let B' : Fin d → Fin d → ℚ := fun i a => εQ * B i a / cf a
  have hεQ0 : 0 ≤ εQ := by exact_mod_cast hεR.le
  have hA' : ∀ i a b, 0 ≤ A' i a b := fun i a b => by
    apply div_nonneg _ (mul_pos (hcf a) (hcf b)).le
    apply mul_nonneg (mul_nonneg _ hεQ0) (hA i a b)
    split_ifs
    · exact zero_le_one
    · exact hc_pos.le
  have hB' : ∀ i a, 0 ≤ B' i a := fun i a =>
    div_nonneg (mul_nonneg hεQ0 (hB i a)) (hcf a).le
  let C := CubicTransfers.ofBalancingDilation A' B' hA' hB'
  have hquad := selectiveLambdaTrick_quadratic_form (o := o) (ε := (εQ : ℝ)) hcR.ne' AR BR
    h_field
  have hA'cast : ∀ i a b, ((A' i a b : ℚ) : ℝ) =
      (if i = o then 1 else (c : ℝ)) * (εQ : ℝ) * AR i a b /
        ((if a = o then 1 else (c : ℝ)) * (if b = o then 1 else (c : ℝ))) := by
    intro i a b
    simp only [A', cf, AR]
    split_ifs <;> (push_cast; try ring)
  have hB'cast : ∀ i a, ((B' i a : ℚ) : ℝ) =
      (εQ : ℝ) * BR i a / (if a = o then 1 else (c : ℝ)) := by
    intro i a
    simp only [B', cf, BR]
    split_ifs <;> (push_cast; try ring)
  have hfield' : ∀ i x,
      selectiveLambdaTrick o (c : ℝ) (constantDilation (εQ : ℝ) btc.pivp.field) x i =
        (∑ a, ∑ b, (A' i a b : ℝ) * x a * x b) - (∑ a, (B' i a : ℝ) * x a) * x i := by
    intro i x
    rw [hquad i x]
    simp only [hA'cast, hB'cast]
  have hC : C.toField = P.field :=
    CubicTransfers.ofBalancingDilation_toField A' B' hA' hB' hfield'
  have hx : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt sol.trajectory (C.toField (sol.trajectory t)) t := by
    intro t ht
    rw [hC]
    exact sol.is_solution t ht
  -- Stages 3-4: the half-product lift, run at the PLPP time scale
  let mf := C.symmetricMeanFieldSolution sol.trajectory hx
  let tr := C.symmetricSynPP.toPLPPTransitions
  set κ : ℝ := (C.symmetricLift.toQuadField.normalization : ℝ) with hκ
  have hκ_pos : 0 < κ := Rat.cast_pos.mpr C.symmetricLift.toQuadField.normalization_pos
  have hz : ∀ t, mf.sol t = halfProduct (sol.trajectory (κ * t)) := fun t => rfl
  have hode : ∀ t, 0 ≤ t → HasDerivAt mf.sol (tr.balanceField (mf.sol t)) t := by
    intro t ht
    have h := mf.sol_ode t ht
    have hdrift : C.symmetricRateSpec.drift = tr.balanceField :=
      PLPPTransitions.toRateSpec_drift_eq_balanceField _
    rw [hdrift] at h
    exact h
  have hκt : ∀ t, 0 ≤ t → 0 ≤ κ * t := fun t ht => mul_nonneg hκ_pos.le ht
  have hx0 : sol.trajectory 0 = stage2_init (c : ℝ) btc.pivp.init := sol.init_cond
  have hx0_rat : ∀ i, ∃ q : ℚ, sol.trajectory 0 i = (q : ℝ) := by
    rw [hx0]
    exact stage2_init_rational ⟨c, rfl⟩ h_init_rat
  have hsimp : ∀ t, 0 ≤ t → ∑ k, mf.sol t k = 1 := by
    intro t ht
    rw [hz, sum_halfProduct, h_simplex _ (hκt t ht)]
    norm_num
  have hnn : ∀ t, 0 ≤ t → ∀ k, 0 ≤ mf.sol t k := by
    intro t ht k
    rw [hz]
    exact halfProduct_nonneg (h_nn _ (hκt t ht)) k
  have hz0 : mf.sol 0 = halfProduct (sol.trajectory 0) := by rw [hz, mul_zero]
  -- the output converges
  have hout : Tendsto (fun t => sol.trajectory t o.succ) atTop (𝓝 α) :=
    tendsto_of_modulus_nonneg btc.modulus fun r t ht0 htμ => h_conv r t ht0 htμ
  have hread : Tendsto
      (fun t => ∑ k, ((halfProductReadoutWeight o.succ k : ℕ) : ℝ) / 2 * mf.sol t k)
      atTop (𝓝 α) := by
    have hcomp := tendsto_comp_const_mul hκ_pos hout
    refine hcomp.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hz, halfProduct_readout, h_simplex _ (hκt t ht), mul_one]
  exact isPLPPComputable_of_fractional_readout tr mf.sol
    (by rw [hz0]; exact halfProduct_rational hx0_rat)
    (hsimp 0 le_rfl)
    (by rw [hz0]; exact halfProduct_nonneg (h_nn 0 le_rfl))
    hsimp hnn hode 2 two_pos (halfProductReadoutWeight o.succ)
    (halfProductReadoutWeight_le_two o.succ) (by exact_mod_cast hread)

/-! ## The compiler -/

/-- **The compiler on `[0, 1)`.** For `0 ≤ α < 1`, a certified bounded CRN computation of `α`
with a CRN decomposition gives a PLPP computation of `α`. -/
theorem isPLPPComputable_of_certified_of_lt_one {α : ℝ} {d : ℕ}
    (hα_nn : 0 ≤ α) (hα_lt : α < 1)
    (cbtc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d cbtc.pivp) :
    IsPLPPComputable α := by
  -- preprocessing: output bounded by `M_out < 1`, then output initialised at `0`
  obtain ⟨d₁, cbtc₁, pcd₁, M_out, hαM, hM_lt, h_bound₁⟩ :=
    Saturating.saturating_surrogate_cbtc cbtc pcd hα_nn hα_lt
  have hM_nn : 0 ≤ M_out := hα_nn.trans hαM
  obtain ⟨d₂, cbtc₂, pcd₂, h_zero₂, h_bound₂⟩ :=
    Algebraic.certified_zero_init_wrapper_sharp (U := M_out) cbtc₁ pcd₁ hM_nn h_bound₁
  -- Stage 1 with rational coefficients
  obtain ⟨d', btc', A, B, hA, hB, h_field, h_init_nn, h_init_rat, h_out_eq, -⟩ :=
    stage1_vvariable_rat cbtc₂ pcd₂
  rcases Nat.eq_zero_or_pos d' with hd0 | hdpos
  · subst hd0
    exact Fin.elim0 btc'.pivp.output
  haveI : NeZero d' := ⟨hdpos.ne'⟩
  have h_zero' : btc'.pivp.init btc'.pivp.output = 0 := by
    have h0 := h_out_eq 0
    have h_btc'_init : btc'.sol.trajectory 0 btc'.pivp.output
        = btc'.pivp.init btc'.pivp.output :=
      congr_fun btc'.sol.init_cond btc'.pivp.output
    rw [← h_btc'_init, h0]
    have h_cbtc_init : cbtc₂.sol.trajectory 0 cbtc₂.pivp.output
        = cbtc₂.pivp.toPIVP.init cbtc₂.pivp.output :=
      congr_fun cbtc₂.sol.init_cond cbtc₂.pivp.output
    change cbtc₂.sol.trajectory 0 cbtc₂.pivp.output = 0
    rw [h_cbtc_init, PolyPIVP.toPIVP_init, h_zero₂]
    simp
  have h_M_out : ∀ σ, 0 ≤ σ → btc'.sol.trajectory σ btc'.pivp.output ≤ M_out :=
    fun σ hσ => by rw [h_out_eq σ]; exact h_bound₂ σ hσ
  obtain ⟨M_rest, hM_rest_nn, h_rest_nn, h_rest_le⟩ :=
    stage1_rest_bound_and_nonneg btc' (fun i a b => (A i a b : ℝ)) (fun i a => (B i a : ℝ))
      (fun i a b => Rat.cast_nonneg.mpr (hA i a b)) (fun i a => Rat.cast_nonneg.mpr (hB i a))
      h_field h_init_nn
  -- the λ-trick constant: a rational `c` with `c · (d' M_rest + 1) ≤ (1 - M_out) / 2`
  set K : ℝ := (d' : ℝ) * M_rest + 1 with hK_def
  have hdM : 0 ≤ (d' : ℝ) * M_rest := mul_nonneg (Nat.cast_nonneg _) hM_rest_nn
  have hK : 1 ≤ K := by rw [hK_def]; linarith
  have hgap : 0 < (1 - M_out) / (2 * K) := div_pos (by linarith) (by linarith)
  obtain ⟨c, hc_pos, hc_lt⟩ := exists_rat_btwn hgap
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc_pos
  have hcK : (c : ℝ) * K ≤ (1 - M_out) / 2 := by
    have h2K : (0 : ℝ) < 2 * K := by linarith
    have := (lt_div_iff₀ h2K).mp hc_lt
    linarith
  have hc_le_K : (c : ℝ) ≤ c * K := by nlinarith
  have hc_le_1 : c ≤ 1 := by
    have : (c : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  have h_sum_le_rest : ∀ σ, 0 ≤ σ → ∑ j, btc'.sol.trajectory σ j ≤ (d' : ℝ) * M_rest := by
    intro σ hσ
    calc ∑ j, btc'.sol.trajectory σ j ≤ ∑ _j : Fin d', M_rest :=
          Finset.sum_le_sum fun j _ => h_rest_le σ hσ j
      _ = (d' : ℝ) * M_rest := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h_sum_le : (c : ℝ) * ∑ j, btc'.pivp.init j ≤ 1 := by
    have h0 : ∑ j, btc'.pivp.init j = ∑ j, btc'.sol.trajectory 0 j := by
      rw [btc'.sol.init_cond]
    rw [h0]
    have := mul_le_mul_of_nonneg_left (h_sum_le_rest 0 le_rfl) hcR.le
    nlinarith
  have h_room : ∀ σ, 0 ≤ σ →
      btc'.sol.trajectory σ btc'.pivp.output
        + (c : ℝ) * ∑ j ∈ Finset.univ.erase btc'.pivp.output, btc'.sol.trajectory σ j
          ≤ 1 - c := by
    intro σ hσ
    have herase : ∑ j ∈ Finset.univ.erase btc'.pivp.output, btc'.sol.trajectory σ j
        ≤ ∑ j, btc'.sol.trajectory σ j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        fun j _ _ => h_rest_nn σ hσ j
    have h1 := mul_le_mul_of_nonneg_left (herase.trans (h_sum_le_rest σ hσ)) hcR.le
    have h2 := h_M_out σ hσ
    nlinarith
  exact isPLPPComputable_of_stage1 btc' A B hA hB h_field h_init_nn h_init_rat c
    (by exact_mod_cast hc_pos) hc_le_1 h_sum_le h_zero' h_room

/-- **The faithful compiler** ([LPP] Main Theorem, GPAC ⇒ PLPP direction). Every `α ∈ [0, 1]`
computed by a bounded ℚ-PIVP with a CRN decomposition is computed by a PLPP in the sense of
[LPP] Definition 9. -/
theorem isPLPPComputable_of_certified {α : ℝ} {d : ℕ}
    (hα : 0 ≤ α ∧ α ≤ 1)
    (cbtc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d cbtc.pivp) :
    IsPLPPComputable α := by
  rcases eq_or_lt_of_le hα.2 with h1 | hlt
  · subst h1
    exact_mod_cast (isLPPComputable_rat 1 zero_le_one le_rfl).isPLPPComputable
  · exact isPLPPComputable_of_certified_of_lt_one hα.1 hlt cbtc pcd

/-- **The faithful compiler, deterministic form** ([LPP] Main Theorem with Theorem 17). -/
theorem isLPPComputable_of_certified {α : ℝ} {d : ℕ}
    (hα : 0 ≤ α ∧ α ≤ 1)
    (cbtc : CertifiedBoundedTimeComputable d α)
    (pcd : PolyCRNDecomposition d cbtc.pivp) :
    IsLPPComputable α :=
  (isPLPPComputable_of_certified hα cbtc pcd).isLPPComputable

end Ripple
