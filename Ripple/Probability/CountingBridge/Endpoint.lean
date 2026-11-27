import Ripple.Probability.CountingBridge.Hitting

/-!
# Endpoint weights and stopping trees

A stopping tree over the alphabet `α` has active nodes carrying a state and two absorbing
outcomes. `StoppingTree.treeWeight` sums a terminal weight over all continuations of
length `T`, branching over every letter at each active node. Specialized to a tree that
never stops, it computes the total endpoint weight `endpointSum`, the sum over words `u`
of length `T` of the weight of the state reached from `x` along `u`. Under the uniform
letter law, the expected endpoint weight after `T` letters is `endpointSum` divided by
`card α ^ T`.
-/

namespace Ripple.CountingBridge

namespace StoppingTree

/-- A node of a stopping tree: an active state, or one of two absorbing outcomes. -/
inductive StopNode (S : Type*) where
  | active : S → StopNode S
  | success : StopNode S
  | failure : StopNode S

/-- One letter moves an active node by `step`; absorbing nodes stay put. -/
def stepNode {S α : Type*}
    (step : S → α → StopNode S) : StopNode S → α → StopNode S
  | .active s, e => step s e
  | .success, _ => .success
  | .failure, _ => .failure

/-- The total terminal weight over all continuations of length `T` from a node. -/
def treeWeight {S α : Type*} [Fintype α]
    (step : S → α → StopNode S) (weight : StopNode S → ℕ) :
    StopNode S → ℕ → ℕ
  | x, 0 => weight x
  | x, T + 1 => ∑ e : α, treeWeight step weight (stepNode step x e) T

/-- A deterministic transition, viewed as a stopping tree that never stops. -/
def activeStep {S α : Type*} (step : S → α → S) (x : S) (e : α) : StopNode S :=
  .active (step x e)

/-- The weight `w` on active nodes, and zero on absorbing outcomes. -/
def activeWeight {S : Type*} (w : S → ℕ) : StopNode S → ℕ
  | .active x => w x
  | .success => 0
  | .failure => 0

/-- The sum, over all words of length `T`, of the weight of the state reached from `x`. -/
def endpointSum {S α : Type*} [Fintype α] (step : S → α → S)
    (w : S → ℕ) (x : S) (T : ℕ) : ℕ :=
  treeWeight (activeStep step) (activeWeight w) (.active x) T

@[simp] theorem endpointSum_zero {S α : Type*} [Fintype α]
    (step : S → α → S) (w : S → ℕ) (x : S) :
    endpointSum step w x 0 = w x := rfl

@[simp] theorem endpointSum_succ {S α : Type*} [Fintype α]
    (step : S → α → S) (w : S → ℕ) (x : S) (T : ℕ) :
    endpointSum step w x (T + 1) = ∑ e : α, endpointSum step w (step x e) T := rfl

end StoppingTree

open MeasureTheory Words StoppingTree
open scoped ENNReal

/-- The word sum of the endpoint weight is the stopping-tree endpoint sum. -/
theorem wordSum_foldl_eq_endpointSum {S α : Type*} [Fintype α] (next : S → α → S)
    (w : S → ℕ) (x : S) (T : ℕ) :
    wordSum α T (fun es => w (es.foldl next x)) = endpointSum next w x T := by
  induction T generalizing x with
  | zero => simp [wordSum, allWords]
  | succ T ih =>
    rw [wordSum_succ, endpointSum_succ]
    simp only [List.foldl_cons, ih]

/-- The expected weight of the state after `T` uniform letters is the endpoint sum
divided by `card α ^ T`. -/
theorem lintegral_endpointSum {S α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (next : S → α → S) (w : S → ℕ) (x : S) (T : ℕ) :
    (∫⁻ ω, (w (run next x ω T) : ℝ≥0∞) ∂μ α) =
      (endpointSum next w x T : ℝ≥0∞) / (Fintype.card α : ℝ≥0∞) ^ T := by
  change (∫⁻ ω, ((fun es => w (es.foldl next x)) («prefix» T ω) : ℝ≥0∞) ∂μ α) = _
  calc
    _ = (wordSum α T (fun es => w (es.foldl next x)) : ℝ≥0∞) /
          (Fintype.card α : ℝ≥0∞) ^ T :=
      lintegral_word_function T (fun es => w (es.foldl next x))
    _ = _ := by rw [wordSum_foldl_eq_endpointSum]

end Ripple.CountingBridge
