/-
  Ripple.Kurtz.StrongApprox.WordCount — the number of words of length `K` over an alphabet of
  size `L` with prescribed letter multiplicities `k` is the multinomial coefficient `K!/∏ (k p)!`.

  Used to split a Poisson block count into
  independent unit-cell counts by uniform placement (`PoissonSplitting`).
-/

import Mathlib

namespace Ripple.Kurtz.StrongApprox

open Finset

/-- Number of positions of the word `f` carrying the letter `p`. -/
def fibCount {K L : ℕ} (f : Fin K → Fin L) (p : Fin L) : ℕ :=
  (univ.filter (fun m => f m = p)).card

/-- Words of length `K` over `Fin L` with letter multiplicities `k`. -/
def wordSet (K L : ℕ) (k : Fin L → ℕ) : Finset (Fin K → Fin L) :=
  univ.filter (fun f => ∀ p, fibCount f p = k p)

theorem sum_fibCount {K L : ℕ} (f : Fin K → Fin L) : ∑ p, fibCount f p = K := by
  unfold fibCount
  rw [← Finset.card_eq_sum_card_fiberwise (fun m _ => mem_univ (f m))]
  simp

theorem fibCount_cons {K L : ℕ} (p₀ : Fin L) (g : Fin K → Fin L) (p : Fin L) :
    fibCount (Fin.cons p₀ g) p = (if p₀ = p then 1 else 0) + fibCount g p := by
  unfold fibCount
  rw [card_filter, card_filter, Fin.sum_univ_succ]
  simp

theorem fibCount_eq_tail {K L : ℕ} (f : Fin (K + 1) → Fin L) (p : Fin L) :
    fibCount f p = (if f 0 = p then 1 else 0) + fibCount (Fin.tail f) p := by
  conv_lhs => rw [← Fin.cons_self_tail f]
  exact fibCount_cons _ _ _

/-- The multinomial recursion `M(k) = Σ_{p : k p ≥ 1} M(k − e_p)` when `Σ k = K + 1`. -/
theorem multinomial_succ {L K : ℕ} (k : Fin L → ℕ) (hk : ∑ p, k p = K + 1) :
    Nat.multinomial univ k =
      ∑ p ∈ univ.filter (fun p => 1 ≤ k p),
        Nat.multinomial univ (Function.update k p (k p - 1)) := by
  have hprod : 0 < ∏ p, (k p).factorial := prod_pos (fun p _ => Nat.factorial_pos _)
  apply Nat.eq_of_mul_eq_mul_left hprod
  rw [Nat.multinomial_spec, hk, mul_sum]
  have hterm : ∀ p ∈ univ.filter (fun p => 1 ≤ k p),
      (∏ q, (k q).factorial) * Nat.multinomial univ (Function.update k p (k p - 1)) =
        k p * K.factorial := by
    intro p hp
    have hp1 : 1 ≤ k p := (mem_filter.mp hp).2
    have hsplit : k p + ∑ q ∈ univ.erase p, k q = ∑ q, k q :=
      Finset.add_sum_erase _ _ (mem_univ p)
    have hsum' : ∑ q, Function.update k p (k p - 1) q = K := by
      rw [Finset.sum_update_of_mem (mem_univ p), Finset.sdiff_singleton_eq_erase]
      omega
    have hfac : ∏ q, (k q).factorial =
        k p * ∏ q, (Function.update k p (k p - 1) q).factorial := by
      have e : ∀ q, (Function.update k p (k p - 1) q).factorial =
          Function.update (fun q => (k q).factorial) p (k p - 1).factorial q := fun q =>
        Function.apply_update (fun _ n => n.factorial) k p (k p - 1) q
      simp_rw [e]
      rw [Finset.prod_update_of_mem (mem_univ p), Finset.sdiff_singleton_eq_erase, ← mul_assoc,
        Nat.mul_factorial_pred (by omega),
        Finset.mul_prod_erase univ (fun q => (k q).factorial) (mem_univ p)]
    rw [hfac, mul_assoc, Nat.multinomial_spec, hsum']
  rw [sum_congr rfl hterm, ← sum_mul]
  have hfilt : ∑ p ∈ univ.filter (fun p => 1 ≤ k p), k p = ∑ p, k p := by
    rw [sum_filter]
    refine sum_congr rfl fun p _ => ?_
    split_ifs with h
    · rfl
    · omega
  rw [hfilt, hk, Nat.factorial_succ]

/-- **Word count**: `#{f : Fin K → Fin L | ∀ p, #f⁻¹(p) = k p} = K!/∏ (k p)!` when `Σ k = K`,
and `0` otherwise. -/
theorem card_wordSet (K L : ℕ) (k : Fin L → ℕ) :
    (wordSet K L k).card = if ∑ p, k p = K then Nat.multinomial univ k else 0 := by
  induction K generalizing k with
  | zero =>
    by_cases hk : ∑ p, k p = 0
    · rw [if_pos hk]
      have hk0 : ∀ p, k p = 0 := fun p => (Finset.sum_eq_zero_iff.mp hk) p (mem_univ p)
      have hall : wordSet 0 L k = univ := by
        ext f
        simp [wordSet, fibCount, hk0]
      have hM : Nat.multinomial univ k = 1 := by
        simpa [hk0] using Nat.multinomial_spec univ k
      rw [hall, Finset.card_univ, Fintype.card_fun, hM]
      simp
    · rw [if_neg hk, Finset.card_eq_zero]
      ext f
      simp only [wordSet, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro h
      exact hk ((sum_congr rfl fun p _ => (h p).symm).trans (sum_fibCount f))
  | succ K ih =>
    classical
    rw [Finset.card_eq_sum_card_fiberwise (f := fun f : Fin (K + 1) → Fin L => f 0) (t := univ)
      (fun f _ => mem_univ _)]
    have hfib : ∀ p₀ : Fin L, ((wordSet (K + 1) L k).filter (fun f => f 0 = p₀)).card =
        if 1 ≤ k p₀ then (wordSet K L (Function.update k p₀ (k p₀ - 1))).card else 0 := by
      intro p₀
      split_ifs with hp₀
      · refine Finset.card_bij' (fun f _ => Fin.tail f) (fun g _ => Fin.cons p₀ g) ?_ ?_ ?_ ?_
        · intro f hf
          simp only [wordSet, mem_filter, mem_univ, true_and] at hf ⊢
          obtain ⟨hfk, hf0⟩ := hf
          intro p
          have hp := hfk p
          rw [fibCount_eq_tail, hf0] at hp
          by_cases hpp : p₀ = p
          · subst hpp
            simp only [if_true, Function.update_self] at hp ⊢
            omega
          · simp only [hpp, if_false, zero_add] at hp
            rw [Function.update_of_ne (Ne.symm hpp)]
            exact hp
        · intro g hg
          simp only [wordSet, mem_filter, mem_univ, true_and] at hg ⊢
          refine ⟨fun p => ?_, Fin.cons_zero _ _⟩
          rw [fibCount_cons, hg p]
          by_cases hpp : p₀ = p
          · subst hpp
            simp only [if_true, Function.update_self]
            omega
          · simp only [hpp, if_false, zero_add]
            rw [Function.update_of_ne (Ne.symm hpp)]
        · intro f hf
          simp only [wordSet, mem_filter, mem_univ, true_and] at hf
          show Fin.cons p₀ (Fin.tail f) = f
          rw [← hf.2]
          exact Fin.cons_self_tail f
        · intro g _
          funext i
          simp [Fin.tail]
      · rw [Finset.card_eq_zero]
        ext f
        simp only [wordSet, mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨hfk, hf0⟩
        have hp := hfk p₀
        rw [fibCount_eq_tail, hf0] at hp
        simp only [if_true] at hp
        omega
    rw [sum_congr rfl fun p₀ _ => hfib p₀]
    simp_rw [ih]
    by_cases hk : ∑ p, k p = K + 1
    · rw [if_pos hk, multinomial_succ k hk, sum_filter]
      refine sum_congr rfl fun p₀ _ => ?_
      by_cases h1 : 1 ≤ k p₀
      · have hsplit : k p₀ + ∑ q ∈ univ.erase p₀, k q = ∑ q, k q :=
          Finset.add_sum_erase _ _ (mem_univ p₀)
        have h2 : ∑ q, Function.update k p₀ (k p₀ - 1) q = K := by
          rw [Finset.sum_update_of_mem (mem_univ p₀), Finset.sdiff_singleton_eq_erase]
          omega
        simp [h1, h2]
      · simp [h1]
    · rw [if_neg hk]
      refine sum_eq_zero fun p₀ _ => ?_
      by_cases h1 : 1 ≤ k p₀
      · have hsplit : k p₀ + ∑ q ∈ univ.erase p₀, k q = ∑ q, k q :=
          Finset.add_sum_erase _ _ (mem_univ p₀)
        have h2 : ∑ q, Function.update k p₀ (k p₀ - 1) q ≠ K := by
          rw [Finset.sum_update_of_mem (mem_univ p₀), Finset.sdiff_singleton_eq_erase]
          omega
        simp [h1, h2]
      · simp [h1]

end Ripple.Kurtz.StrongApprox
