import Ripple.Stochastic.StrongSDESolutionSpace
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Passing from consistent integer horizons to one process

The input is a countable collection of finite-horizon
processes and their proved indistinguishability on overlaps. The construction
uses their original probability space and filtration. It performs no shifted
integration or recursion at random endpoints.

This module does not assert that independently selected SDE solutions are
consistent: the application must first prove integral restriction and apply
finite-horizon uniqueness. Those are substantive premises, displayed below.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Ripple.Stochastic.ConsistentHorizonProcess

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A deterministic integer horizon strictly beyond the requested time. -/
def horizon (t : ℝ≥0) : ℕ := Nat.ceil t + 1

theorem le_horizon (t : ℝ≥0) : t ≤ (horizon t : ℝ≥0) := by
  exact (Nat.le_ceil t).trans (by simp [horizon])

def diagonal (Z : ℕ → ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) : E :=
  Z (horizon t) t ω

/-- Every overlap is valid on one event, before the time-dependent selection
is made. This is a countable intersection over horizons, not over real times. -/
theorem common_consistency (Z : ℕ → ℝ≥0 → Ω → E)
    (hc : ∀ m n : ℕ, m ≤ n → ∀ᵐ ω ∂μ, ∀ t ≤ (m : ℝ≥0), Z m t ω = Z n t ω) :
    ∀ᵐ ω ∂μ, ∀ m n : ℕ, m ≤ n → ∀ t ≤ (m : ℝ≥0), Z m t ω = Z n t ω := by
  apply ae_all_iff.mpr
  intro m
  apply ae_all_iff.mpr
  intro n
  by_cases hmn : m ≤ n
  · filter_upwards [hc m n hmn] with ω hω
    exact fun _ => hω
  · exact ae_of_all _ fun _ h => (hmn h).elim

/-- On the common event, the diagonal equals each finite solution throughout
that solution's window, including both endpoints. -/
theorem diagonal_agrees (Z : ℕ → ℝ≥0 → Ω → E) (ω : Ω)
    (hc : ∀ m n : ℕ, m ≤ n → ∀ t ≤ (m : ℝ≥0), Z m t ω = Z n t ω) :
    ∀ (n : ℕ) t, t ≤ (n : ℝ≥0) → diagonal Z t ω = Z n t ω := by
  intro n t htn
  rcases le_total (horizon t) n with hkn | hnk
  · exact hc (horizon t) n hkn t (le_horizon t)
  · exact (hc n (horizon t) hnk t htn).symm

theorem diagonal_agrees_ae (Z : ℕ → ℝ≥0 → Ω → E)
    (hc : ∀ m n : ℕ, m ≤ n → ∀ᵐ ω ∂μ, ∀ t ≤ (m : ℝ≥0), Z m t ω = Z n t ω) :
    ∀ᵐ ω ∂μ, ∀ (n : ℕ) t, t ≤ (n : ℝ≥0) → diagonal Z t ω = Z n t ω := by
  filter_upwards [common_consistency Z hc] with ω hω
  exact diagonal_agrees Z ω hω

/-- Deterministic time selection preserves exact adaptation. -/
theorem diagonal_adapted (F : Filtration ℝ≥0 mΩ) (Z : ℕ → ℝ≥0 → Ω → E)
    (ha : ∀ n, StronglyAdapted F (Z n)) : StronglyAdapted F (diagonal Z) := by
  intro t
  exact ha (horizon t) t

/-- Local agreement with a longer horizon proves continuity even at integer
boundaries, where the index selected by `horizon` changes. -/
theorem diagonal_continuous (Z : ℕ → ℝ≥0 → Ω → E) (ω : Ω)
    (hc : ∀ n, Continuous (fun t => Z n t ω))
    (heq : ∀ (n : ℕ) t, t ≤ (n : ℝ≥0) → diagonal Z t ω = Z n t ω) :
    Continuous (fun t => diagonal Z t ω) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt t
  apply (hc n).continuousAt.congr_of_eventuallyEq
  filter_upwards [isOpen_Iio.mem_nhds hn] with s hs
  exact heq n s (le_of_lt hs)

theorem diagonal_continuous_ae (Z : ℕ → ℝ≥0 → Ω → E)
    (hc : ∀ n, ∀ᵐ ω ∂μ, Continuous (fun t => Z n t ω))
    (heq : ∀ m n : ℕ, m ≤ n → ∀ᵐ ω ∂μ, ∀ t ≤ (m : ℝ≥0), Z m t ω = Z n t ω) :
    ∀ᵐ ω ∂μ, Continuous (fun t => diagonal Z t ω) := by
  filter_upwards [ae_all_iff.mpr hc, diagonal_agrees_ae Z heq] with ω hcω heqω
  exact diagonal_continuous Z ω hcω heqω

/-- An all-time continuous adapted realization on the original space, with
one common event witnessing every finite-window identification. -/
theorem exists_global_process (F : Filtration ℝ≥0 mΩ)
    (hnull : ∀ t A, MeasurableSet A → μ A = 0 → MeasurableSet[F t] A)
    (Z : ℕ → ℝ≥0 → Ω → E) (ha : ∀ n, StronglyAdapted F (Z n))
    (hc : ∀ n, ∀ᵐ ω ∂μ, Continuous (fun t => Z n t ω))
    (heq : ∀ m n : ℕ, m ≤ n → ∀ᵐ ω ∂μ, ∀ t ≤ (m : ℝ≥0), Z m t ω = Z n t ω) :
    ∃ Y : ℝ≥0 → Ω → E, StronglyAdapted F Y ∧
      (∀ ω, Continuous (fun t => Y t ω)) ∧
      (∀ᵐ ω ∂μ, ∀ (n : ℕ) t, t ≤ (n : ℝ≥0) → Y t ω = Z n t ω) := by
  obtain ⟨Y, hYa, hYc, hYeq⟩ :=
    StrongSDESolutionSpace.exists_continuous_adapted_modification F hnull
      (diagonal Z) (diagonal_adapted F Z ha) (diagonal_continuous_ae Z hc heq)
  refine ⟨Y, hYa, hYc, ?_⟩
  filter_upwards [hYeq, diagonal_agrees_ae Z heq] with ω hω hdiag
  exact fun n t ht => (hω t).trans (hdiag n t ht)

/-- Finite-window indistinguishability implies all-time indistinguishability
without an uncountable intersection of null sets. -/
theorem indistinguishable_of_integer_windows (X Y : ℝ≥0 → Ω → E)
    (h : ∀ n : ℕ, ∀ᵐ ω ∂μ, ∀ t ≤ (n : ℝ≥0), X t ω = Y t ω) :
    ∀ᵐ ω ∂μ, ∀ t, X t ω = Y t ω := by
  filter_upwards [ae_all_iff.mpr h] with ω hω
  exact fun t => hω (horizon t) t (le_horizon t)

end Ripple.Stochastic.ConsistentHorizonProcess
