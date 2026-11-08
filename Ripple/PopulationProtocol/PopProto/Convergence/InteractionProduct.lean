import Ripple.PopulationProtocol.PopProto.Convergence.OccupationAssembly

/-! # Interaction-count bound on the original occupation chain
The original-chain product moment and blank conservation are transported by
an exact marginal identity. No regional stopping assumption is introduced.
-/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Ripple.PopulationProtocol.PopProto.Config
variable {n : ℕ}

/-- The cumulative VB/XY product appearing in the global supermartingale. -/
noncomputable def interactionProduct (a : AugConfig n) : ℝ≥0∞ :=
  (((16 * n + 7 : ℕ) : ℝ≥0∞) ^ a.2.1 * ((16 * n - 5 : ℕ) : ℝ≥0∞) ^ a.2.2) /
    ((16 * n : ℕ) : ℝ≥0∞) ^ (a.2.1 + a.2.2)

/-- Ratio form of the product, with natural subtraction justified by n≥2. -/
theorem interactionProduct_eq (hn : n ≥ 2) (a : AugConfig n) :
    interactionProduct a = ENNReal.ofReal (
      ((16 * (n : ℝ) + 7) / (16 * n)) ^ a.2.1 *
      ((16 * (n : ℝ) - 5) / (16 * n)) ^ a.2.2) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h16 : (0 : ℝ) < 16 * n := by positivity
  have hβ : (0 : ℝ) ≤ (16 * n - 5) / (16 * n) := div_nonneg (by linarith) h16.le
  have hz : ((16 * n : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : 16*n ≠ 0)
  have ht : ((16 * n : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.ofReal_mul (pow_nonneg (div_nonneg (by positivity) h16.le) _),
    ENNReal.ofReal_pow (div_nonneg (by positivity) h16.le), ENNReal.ofReal_pow hβ,
    ENNReal.ofReal_div_of_pos h16, ENNReal.ofReal_div_of_pos h16,
    show (16 * (n : ℝ) + 7) = ↑(16*n+7 : ℕ) from by push_cast; ring,
    show (16 * (n : ℝ) - 5) = ↑(16*n-5 : ℕ) from by
      rw [Nat.cast_sub (by omega)]; push_cast; ring]
  simp only [show (16 * (n : ℝ)) = ↑(16*n : ℕ) from by push_cast; ring,
    ENNReal.ofReal_natCast]
  simp only [interactionProduct, div_eq_mul_inv, mul_pow, pow_add]
  rw [ENNReal.mul_inv (Or.inl (pow_ne_zero _ hz)) (Or.inl (ENNReal.pow_ne_top ht))]
  simp only [ENNReal.inv_pow, mul_comm, mul_left_comm, mul_assoc]

/-- Sufficiently many cumulative interactions force a large product. -/
theorem interactionProduct_lower (hn : n ≥ 2) (a : AugConfig n) (k : ℕ)
    (hbal : a.2.2 ≤ a.2.1 + n) (hcount : k < 260 * a.2.1 + 516 * a.2.2) :
    1 ≤ 2 * ENNReal.ofReal ((1 - 1 / (15000 * (n : ℝ))) ^ k) * interactionProduct a := by
  have h := interaction_count_product_lower_bound hn a.2.1 a.2.2 k hbal hcount
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : 0 ≤ (1 : ℝ) - 1 / (15000 * n) := by
    apply sub_nonneg.mpr
    apply (div_le_one (by positivity)).mpr
    nlinarith
  rw [interactionProduct_eq hn]
  have heq : (2 : ℝ≥0∞) * ENNReal.ofReal ((1 - 1 / (15000 * (n : ℝ))) ^ k) =
      ENNReal.ofReal (2 * (1 - 1 / (15000 * (n : ℝ))) ^ k) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [heq, ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (pow_nonneg hr k))]
  simpa only [ENNReal.ofReal_one, mul_assoc] using ENNReal.ofReal_le_ofReal h

/-- Exact augmented marginal of the occupation-chain distribution. -/
theorem occupation_map_aug (hn : n ≥ 2) (a₀ : OccupationConfig n) (t : ℕ) :
    (((occupationKernel hn ^ t) a₀).map (Prod.fst : OccupationConfig n → AugConfig n)) =
      ((augTransitionKernel hn ^ t) a₀.1) := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply Measurable.of_discrete hS]
  exact occupationKernel_proj_pow hn a₀ t S hS

/-- Product expectation on the actual occupation chain. -/
theorem occupation_product_moment (hn : n ≥ 2) (c₀ : Config n) (t : ℕ) :
    ∫⁻ a, interactionProduct a.1
      ∂((occupationKernel hn ^ t) ((c₀, 0, 0), ⟨0, 0, 0, 0⟩)) ≤
      ((n^2 + 2*n : ℕ) : ℝ≥0∞) / (c₀.potential : ℝ≥0∞) := by
  rw [← lintegral_map (Measurable.of_discrete : Measurable
    (interactionProduct : AugConfig n → ℝ≥0∞)) Measurable.of_discrete,
    occupation_map_aug]
  exact original_expected_product_bound hn c₀ t

/-- Blank conservation also holds on the occupation chain. -/
theorem occupation_blank_conservation (hn : n ≥ 2) (c₀ : Config n) (t : ℕ) :
    ∀ᵐ a ∂((occupationKernel hn ^ t) ((c₀, 0, 0), ⟨0, 0, 0, 0⟩)),
      a.1.2.2 ≤ a.1.2.1 + n := by
  have h := original_blank_conservation hn c₀ t
  rw [← occupation_map_aug hn (((c₀, 0, 0), ⟨0, 0, 0, 0⟩) : OccupationConfig n) t,
    ae_map_iff Measurable.of_discrete.aemeasurable
      (DiscreteMeasurableSpace.forall_measurableSet _)] at h
  exact h

/-- The final non-consensus event is exactly the original protocol's event. -/
theorem occupation_nonconsensus_eq (hn : n ≥ 2) (c₀ : Config n) (t : ℕ) :
    ((occupationKernel hn ^ t) ((c₀, 0, 0), ⟨0, 0, 0, 0⟩))
      {a : OccupationConfig n | ¬a.1.1.isConsensus} =
      ((transitionKernel hn ^ t) c₀) {c : Config n | ¬c.isConsensus} := by
  change ((occupationKernel hn ^ t) (((c₀, 0, 0), ⟨0, 0, 0, 0⟩) : OccupationConfig n))
    (Prod.fst ⁻¹' (Prod.fst ⁻¹' {c : Config n | ¬c.isConsensus})) = _
  rw [occupationKernel_proj_pow hn _ t _ (DiscreteMeasurableSpace.forall_measurableSet _),
    augTransitionKernel_proj_pow hn _ t _ (DiscreteMeasurableSpace.forall_measurableSet _)]

end Ripple.PopulationProtocol.PopProto.Config
