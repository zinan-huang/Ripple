import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Defs

/-!
# Counting first hits in finite words over a finite alphabet

Let `α` be a finite alphabet. A word of length `T` is a list of `T` letters; its head is
the letter drawn at time zero. A deterministic transition `next : S → α → S` and a
target predicate `P : S → Prop` drive a run from an initial state `x` along a word.
This file counts the words of length `T` on which the run survives, first hits the
target at the endpoint, or has a given truncated hitting time. Dividing these counts by
`Fintype.card α ^ T` gives the corresponding probabilities for a uniformly random word.

The words of length `T` are enumerated as the multiset `allWords α T`, built by
appending one letter at a time to every shorter word. The word sum `wordSum α T f`
evaluates `f` on the reverse of each enumerated word. The reversed enumeration grows at
the head, which gives the recursion `wordSum_succ` on the first letter. Since reversal
permutes the words of length `T`, the word sum is the plain sum of `f` over all words of
length `T` (`wordSum_eq_sum_tuples`).
-/

namespace Ripple.CountingBridge

namespace Words

/-- A finite word over the alphabet `α`. Its head is the letter at time zero. -/
abbrev Word (α : Type*) := List α

/-- The words of length `T`, each with multiplicity one, enumerated by appending every
letter to every word of length `T - 1`. -/
def allWords (α : Type*) [Fintype α] : ℕ → Multiset (Word α)
  | 0 => {[]}
  | t + 1 => (allWords α t).bind fun s => (Finset.univ : Finset α).val.map fun e => s ++ [e]

/-- The sum of a natural-valued word observable over the words of length `T`. Each
enumerated word is reversed before evaluation; reversal permutes the words of length `T`,
so this is the sum of `f` over all words of length `T`. -/
def wordSum (α : Type*) [Fintype α] (T : ℕ) (f : Word α → ℕ) : ℕ :=
  ((allWords α T).map fun u => f u.reverse).sum

variable {α : Type*} [Fintype α]

private theorem multiset_sum_map_sum {β : Type*} (m : Multiset β) (g : β → α → ℕ) :
    (m.map fun s => ∑ e, g s e).sum = ∑ e, (m.map fun s => g s e).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => simp [ih, Finset.sum_add_distrib]

/-- Splitting off the first letter of the evaluated word. -/
theorem wordSum_succ (T : ℕ) (f : Word α → ℕ) :
    wordSum α (T + 1) f = ∑ e : α, wordSum α T (fun u => f (e :: u)) := by
  simp only [wordSum, allWords, Multiset.map_bind, Multiset.sum_bind, Multiset.map_map,
    Function.comp_def, List.reverse_append, List.reverse_singleton, List.singleton_append,
    Finset.sum_map_val]
  exact multiset_sum_map_sum (allWords α T) (fun s e => f (e :: s.reverse))

/-- The word sum is the sum of the observable over all letter tuples of length `T`. -/
theorem wordSum_eq_sum_tuples (T : ℕ) (f : Word α → ℕ) :
    wordSum α T f = ∑ v : Fin T → α, f (List.ofFn v) := by
  classical
  induction T generalizing f with
  | zero => simp [wordSum, allWords]
  | succ T ih =>
    rw [wordSum_succ, ← (Fin.consEquiv (fun _ : Fin (T + 1) => α)).sum_comp
        (fun v => f (List.ofFn v)), Fintype.sum_prod_type]
    simp only [ih]
    refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun v _ => ?_
    change f (e :: List.ofFn v) = f (List.ofFn (Fin.cons e v))
    rw [List.ofFn_cons]

end Words

namespace FirstHit

open Words

variable {S α : Type*} (next : S → α → S) (P : S → Prop)

open Classical in
/-- The number of letters the run from `x` consumes before its first visit to `P`,
capped at the word length. The initial state is tested before any letter is read. -/
noncomputable def costWord : S → Word α → ℕ
  | _, [] => 0
  | x, e :: es => if P x then 0 else 1 + costWord (next x e) es

open Classical in
/-- Indicator that the run from `x` avoids `P` at every time up to and including the
end of the word. -/
noncomputable def survivalWord : S → Word α → ℕ
  | x, [] => if P x then 0 else 1
  | x, e :: es => if P x then 0 else survivalWord (next x e) es

open Classical in
/-- Indicator that the run from `x` visits `P` for the first time at the end of the word. -/
noncomputable def firstHitWord : S → Word α → ℕ
  | x, [] => if P x then 1 else 0
  | x, e :: es => if P x then 0 else firstHitWord (next x e) es

variable [Fintype α]

/-- Total truncated hitting time over the words of length `T`. -/
noncomputable def costNumerator (x : S) (T : ℕ) : ℕ :=
  wordSum α T (costWord next P x)

/-- Number of words of length `t` along which the run avoids `P` through time `t`. -/
noncomputable def survivalNumerator (x : S) (t : ℕ) : ℕ :=
  wordSum α t (survivalWord next P x)

/-- Number of words of length `k` along which the run first visits `P` at time `k`. -/
noncomputable def firstHitNumerator (x : S) (k : ℕ) : ℕ :=
  wordSum α k (firstHitWord next P x)

/-- Probability, under the uniform law on words, that the hitting time exceeds `t`. -/
noncomputable def survivalProb (x : S) (t : ℕ) : ℚ :=
  (survivalNumerator next P x t : ℚ) / (Fintype.card α : ℚ) ^ t

/-- Probability, under the uniform law on words, that the hitting time equals `k`. -/
noncomputable def firstHitProb (x : S) (k : ℕ) : ℚ :=
  (firstHitNumerator next P x k : ℚ) / (Fintype.card α : ℚ) ^ k

/-- Expectation of the hitting time truncated at `T`. -/
noncomputable def truncatedExpectation (x : S) (T : ℕ) : ℚ :=
  (costNumerator next P x T : ℚ) / (Fintype.card α : ℚ) ^ T

/-- The partial first moment `∑_{t ≤ K} t * firstHitProb t` of the hitting time. -/
noncomputable def partialExpectation (x : S) : ℕ → ℚ
  | 0 => 0
  | K + 1 => partialExpectation x K + ((K + 1 : ℕ) : ℚ) * firstHitProb next P x (K + 1)

/-- The survival probabilities tend to zero. -/
def AlmostSurelyHits (x : S) : Prop :=
  ∀ m : ℕ, ∃ K : ℕ, (m : ℚ) * survivalProb next P x K ≤ 1

/-- The hitting time is almost surely finite and its partial first moments are bounded
by `B`, so its expectation is at most `B`. -/
def ExpectedHittingTimeAtMost (x : S) (B : ℚ) : Prop :=
  AlmostSurelyHits next P x ∧ ∀ K : ℕ, partialExpectation next P x K ≤ B

end FirstHit

end Ripple.CountingBridge
