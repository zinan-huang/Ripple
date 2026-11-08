import Ripple.PopulationProtocol.PopProto.Convergence.BlankOccupation
import Ripple.PopulationProtocol.PopProto.Convergence.InteractionProduct

/-! # Quantitative convergence of the original approximate-majority chain

The proof sums cumulative occupation counts, not regional exit times.
Large cumulative interaction counts are bounded by the product supermartingale;
otherwise one of the four occupation charges is large. All auxiliary chains
project exactly to the original transition kernel. Constants are conservative
and are not claimed to match the constants in the source paper.
-/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Ripple.PopulationProtocol.PopProto.Config
variable {n : ℕ}

/-- Sum of the four global occupation supermartingales. -/
noncomputable def aggregateOccupation (a : OccupationConfig n) : ℝ≥0∞ :=
  centralOccupationW a +
  weightedOccupation (fun c => (c.potentialLargeX : ℝ≥0∞)) (fun s => (s.left : ℝ)/8) 16 8 a +
  weightedOccupation (fun c => (c.potentialLargeY : ℝ≥0∞)) (fun s => (s.right : ℝ)/8) 16 8 a +
  weightedOccupation blankOccupationPotential (fun s => (s.blank : ℝ)/8) 0 16 a

/-- The initial total charge is explicit and at most linear in population size. -/
noncomputable def initialOccupationBound (c : Config n) : ℝ≥0∞ :=
  1 + (c.potentialLargeX : ℝ≥0∞) + (c.potentialLargeY : ℝ≥0∞) + blankOccupationPotential c

/-- The aggregate exponential moment is bounded by its initial value. -/
theorem aggregateOccupation_moment (hn : n ≥ 16) (c₀ : Config n) (t : ℕ) :
    ∫⁻ a, aggregateOccupation a
      ∂((occupationKernel (show n ≥ 2 by omega) ^ t) ((c₀, 0, 0), ⟨0, 0, 0, 0⟩)) ≤
      initialOccupationBound c₀ := by
  unfold aggregateOccupation initialOccupationBound
  rw [lintegral_add_left Measurable.of_discrete,
    lintegral_add_left Measurable.of_discrete, lintegral_add_left Measurable.of_discrete]
  exact add_le_add (add_le_add
    (add_le_add (centralOccupationW_iteration (by omega) c₀ t)
      (cornerX_occupation_moment (by omega) c₀ t))
    (cornerY_occupation_moment (by omega) c₀ t)) (blank_occupation_moment hn c₀ t)

/-- A large linear occupation charge forces a large exponential weight,
provided the concrete compensating potential is at least one. -/
theorem weightedOccupation_ge_exp (φ : Config n → ℝ≥0∞) (w : RegionCounts → ℝ)
    (vb xy u : ℝ) (a : OccupationConfig n) (hφ : 1 ≤ φ a.1.1)
    (hcharge : u ≤ w a.2 - vb*(a.1.2.1 : ℝ) - xy*(a.1.2.2 : ℝ)) :
    ENNReal.ofReal (Real.exp (u/(n : ℝ))) ≤ weightedOccupation φ w vb xy a := by
  unfold weightedOccupation
  calc _ ≤ ENNReal.ofReal (Real.exp
        ((w a.2 - vb*(a.1.2.1 : ℝ) - xy*(a.1.2.2 : ℝ))/(n : ℝ))) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        exact div_le_div_of_nonneg_right hcharge (Nat.cast_nonneg' n)
    _ ≤ _ := le_mul_of_one_le_right (zero_le') hφ

/-- If the interaction counter is small at time 4k, some region's cumulative
charge must be large. This deterministic step is the global assembly. -/
theorem aggregateOccupation_large (hn : n ≥ 16) (a : OccupationConfig n) (k : ℕ)
    (hclock : a.2.total = 4*k) (hcount : ¬k < 260*a.1.2.1 + 516*a.1.2.2) :
    ENNReal.ofReal (Real.exp ((2*(k : ℝ)/25)/(n : ℝ))) ≤ aggregateOccupation a := by
  let u : ℝ := 2*(k : ℝ)/25
  let wx := weightedOccupation (fun c : Config n => (c.potentialLargeX : ℝ≥0∞))
    (fun s => (s.left : ℝ)/8) 16 8 a
  let wy := weightedOccupation (fun c : Config n => (c.potentialLargeY : ℝ≥0∞))
    (fun s => (s.right : ℝ)/8) 16 8 a
  let wb := weightedOccupation blankOccupationPotential (fun s => (s.blank : ℝ)/8) 0 16 a
  have hcx : centralOccupationW a ≤ aggregateOccupation a := by
    unfold aggregateOccupation
    calc centralOccupationW a = centralOccupationW a + 0 + 0 + 0 := by simp
      _ ≤ _ := by gcongr <;> exact zero_le'
  have hxx : wx ≤ aggregateOccupation a := by
    change wx ≤ centralOccupationW a + wx + wy + wb
    calc wx = 0 + wx + 0 + 0 := by simp
      _ ≤ _ := by gcongr <;> exact zero_le'
  have hyy : wy ≤ aggregateOccupation a := by
    change wy ≤ centralOccupationW a + wx + wy + wb
    calc wy = 0 + 0 + wy + 0 := by simp
      _ ≤ _ := by gcongr <;> exact zero_le'
  have hbb : wb ≤ aggregateOccupation a := by
    change wb ≤ centralOccupationW a + wx + wy + wb
    calc wb = 0 + 0 + 0 + wb := by simp
      _ ≤ _ := by gcongr <;> exact zero_le'
  by_cases hc : u ≤ (a.2.central : ℝ) - 130*(a.1.2.1 : ℝ) - 258*(a.1.2.2 : ℝ)
  · apply le_trans _ hcx
    rw [centralOccupationW_eq]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right hc (Nat.cast_nonneg' n)
  by_cases hx : u ≤ (a.2.left : ℝ)/8 - 16*(a.1.2.1 : ℝ) - 8*(a.1.2.2 : ℝ)
  · apply le_trans _ hxx
    apply weightedOccupation_ge_exp _ _ 16 8 u a _ hx
    exact_mod_cast (show 1 ≤ a.1.1.potentialLargeX from by unfold potentialLargeX; omega)
  by_cases hy : u ≤ (a.2.right : ℝ)/8 - 16*(a.1.2.1 : ℝ) - 8*(a.1.2.2 : ℝ)
  · apply le_trans _ hyy
    apply weightedOccupation_ge_exp _ _ 16 8 u a _ hy
    exact_mod_cast (show 1 ≤ a.1.1.potentialLargeY from by unfold potentialLargeY; omega)
  by_cases hb : u ≤ (a.2.blank : ℝ)/8 - 16*(a.1.2.2 : ℝ)
  · apply le_trans _ hbb
    apply weightedOccupation_ge_exp _ _ 0 16 u a
      (one_le_blankOccupationPotential (by omega) a.1.1)
    simpa using hb
  have ht : (a.2.central : ℝ) + (a.2.blank : ℝ) + (a.2.left : ℝ) + (a.2.right : ℝ) =
      4*(k : ℝ) := by exact_mod_cast hclock
  have hk : 260*(a.1.2.1 : ℝ) + 516*(a.1.2.2 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (Nat.le_of_not_gt hcount)
  dsimp [u] at hc hx hy hb
  nlinarith [Nat.cast_nonneg (α := ℝ) a.1.2.1, Nat.cast_nonneg (α := ℝ) a.1.2.2]

/-- **Original-chain global convergence bound.** For every opinionated
initial configuration and n≥16, the probability of remaining non-consensus
after 4k interactions is bounded by two explicit exponentially decaying terms.
There are no regional, trajectory, or supermartingale premises to discharge. -/
theorem convergence_time_bound (hn : n ≥ 16) (c₀ : Config n)
    (hop : c₀.hasOpinion) (k : ℕ) :
    ((transitionKernel (show n ≥ 2 by omega) ^ (4*k)) c₀)
      {c : Config n | ¬c.isConsensus} ≤
      ENNReal.ofReal (Real.exp (-(2*(k : ℝ)/25)/(n : ℝ))) * initialOccupationBound c₀ +
      2 * ENNReal.ofReal ((1 - 1/(15000*(n : ℝ)))^k) *
        (((n^2+2*n : ℕ) : ℝ≥0∞) / (c₀.potential : ℝ≥0∞)) := by
  let hn2 : n ≥ 2 := by omega
  let μ := (occupationKernel hn2 ^ (4*k)) ((c₀, 0, 0), ⟨0, 0, 0, 0⟩)
  let e := ENNReal.ofReal (Real.exp (-(2*(k : ℝ)/25)/(n : ℝ)))
  let r := ENNReal.ofReal ((1 - 1/(15000*(n : ℝ)))^k)
  rw [← occupation_nonconsensus_eq hn2 c₀ (4*k)]
  have hp : ∀ᵐ a ∂μ, ¬a.1.1.isConsensus →
      1 ≤ e * aggregateOccupation a + 2*r*interactionProduct a.1 := by
    filter_upwards [occupation_clock hn2 c₀ hop (4*k),
      occupation_blank_conservation hn2 c₀ (4*k)] with a ha hbal
    intro hnot
    by_cases hcount : k < 260*a.1.2.1 + 516*a.1.2.2
    · have h := interactionProduct_lower hn2 a.1 k hbal hcount
      exact h.trans (le_add_of_nonneg_left (zero_le'))
    · have h := aggregateOccupation_large hn a k (ha.2 hnot) hcount
      have he : e * ENNReal.ofReal (Real.exp ((2*(k : ℝ)/25)/(n : ℝ))) = 1 := by
        dsimp [e]
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        simp [neg_div]
      have h' := mul_le_mul_left' h e
      rw [he] at h'
      exact h'.trans (le_add_of_nonneg_right (zero_le'))
  calc μ {a : OccupationConfig n | ¬a.1.1.isConsensus}
      = ∫⁻ a, {a : OccupationConfig n | ¬a.1.1.isConsensus}.indicator (fun _ => (1 : ℝ≥0∞)) a ∂μ :=
        (lintegral_indicator_one (DiscreteMeasurableSpace.forall_measurableSet _)).symm
    _ ≤ ∫⁻ a, e * aggregateOccupation a + 2*r*interactionProduct a.1 ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hp] with a ha
      by_cases hc : a.1.1.isConsensus
      · simp only [Set.indicator_apply, Set.mem_setOf_eq, hc, not_true_eq_false, if_false]
        exact zero_le'
      · simp only [Set.indicator_apply, Set.mem_setOf_eq, hc, not_false_eq_true, if_true]
        exact ha hc
    _ = e * (∫⁻ a, aggregateOccupation a ∂μ) +
        2*r*(∫⁻ a, interactionProduct a.1 ∂μ) := by
      rw [lintegral_add_left Measurable.of_discrete,
        lintegral_const_mul _ Measurable.of_discrete,
        lintegral_const_mul _ Measurable.of_discrete]
    _ ≤ _ := add_le_add
      (mul_le_mul_left' (aggregateOccupation_moment hn c₀ (4*k)) e)
      (mul_le_mul_left' (occupation_product_moment hn2 c₀ (4*k)) (2*r))

end Ripple.PopulationProtocol.PopProto.Config
