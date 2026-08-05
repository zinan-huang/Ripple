/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Compose
import Tri.Counting

/-!
# One guarded rung: ruin safety plus a productive-reaction deadline

This module combines the two phase-1 engines without sharing their potential
bases.  The safety error comes directly from `Tri.tri_feller`; the deadline
error comes from `Tri.count_tail_bernoulli`, instantiated through
`Tri.triCount_decomp`, `Tri.triCount_masses`, and
`Tri.count_step_of_masses`.  The final bound is their `ℝ≥0∞` sum, obtained by a
union bound.

The deadline estimate needs a one-step lower bound on productive mass only
while the run is live.  The guarded chain below freezes the `X`-coordinate once
the bad set is reached and advances the auxiliary counter there.  It also
advances the counter at consensus and outside the physical range.  These
artificial increments cannot create a successful run: a run in the bad set
already pays the safety error, while consensus is already beyond the purpose of
the productive-reaction deadline.  Off those guarded states the counter is
exactly `Tri.triCount`.

Thus `rung_bound` is a probabilistic Hoare-style checkpoint: within `T`
interaction events, the run remains above `aLo` and its productive counter
exceeds `m`, except for the sum of the independently parameterized safety and
deadline terms.  No conditioning and no product of the two bounds is used.
-/

namespace Tri

open scoped ENNReal

variable {α β : Type*}

/-- The productive-count chain guarded at ruin and at the non-interior upper
boundary.  On live physical states this is exactly `triCount`. -/
noncomputable def rungCount (n aLo : ℕ) : ℕ × ℕ → PMF (ℕ × ℕ) := fun s =>
  if s.1 ≤ aLo then PMF.pure (s.1, s.2 + 1)
  else if n ≤ s.1 then PMF.pure (s.1, s.2 + 1)
  else triCount n s

/-- Projecting one `triCount` step to its first coordinate recovers
`triChain`. -/
theorem triCount_map_fst (n : ℕ) (s : ℕ × ℕ) :
    (triCount n s).map Prod.fst = triChain n s.1 := by
  unfold triCount
  rw [PMF.map_comp]
  convert PMF.map_id (triChain n s.1) using 1

/-- A pointwise map of Markov kernels commutes with every deterministic
iterate. -/
theorem iter_map_of_step_map (K : α → PMF α) (L : β → PMF β) (f : α → β)
    (hmap : ∀ s, (K s).map f = L (f s)) (T : ℕ) (s : α) :
    (iter K T s).map f = iter L T (f s) := by
  induction T generalizing s with
  | zero => exact PMF.pure_map f s
  | succ T ih =>
      rw [iter_succ, iter_succ, PMF.map_bind]
      simp_rw [ih]
      change (K s).bind ((iter L T) ∘ f) = _
      rw [← PMF.bind_map, hmap]

/-- The first-coordinate marginal of one guarded step is the base chain frozen
on the ruin set. -/
theorem rungCount_map_fst (n aLo : ℕ) (h3 : 3 ≤ n) (s : ℕ × ℕ) :
    (rungCount n aLo s).map Prod.fst =
      freeze (fun x : ℕ => x ≤ aLo) (triChain n) s.1 := by
  by_cases hbad : s.1 ≤ aLo
  · rw [freeze_of_mem s.1 hbad]
    simp only [rungCount, if_pos hbad]
    exact PMF.pure_map Prod.fst (s.1, s.2 + 1)
  · rw [freeze_of_not_mem s.1 hbad]
    by_cases hn : n ≤ s.1
    · by_cases heq : s.1 = n
      · subst heq
        rw [triChain_consensus h3]
        simp only [rungCount, if_neg hbad, if_pos hn]
        exact PMF.pure_map Prod.fst (s.1, s.2 + 1)
      · have hlt : n < s.1 := lt_of_le_of_ne hn (Ne.symm heq)
        unfold triChain
        rw [dif_neg (by omega)]
        simp only [rungCount, if_neg hbad, if_pos hn]
        exact PMF.pure_map Prod.fst (s.1, s.2 + 1)
    · simp only [rungCount, if_neg hbad, if_neg hn]
      exact triCount_map_fst n s

/-- Terminal bad mass for the guarded count chain is exactly the base-chain
hitting probability. -/
theorem rungCount_bad_eq_hitProb (n aLo : ℕ) (h3 : 3 ≤ n) (T x c : ℕ) :
    expect (iter (rungCount n aLo) T (x, c))
        (ind (fun z : ℕ × ℕ => z.1 ≤ aLo)) =
      hitProb (fun z : ℕ => z ≤ aLo) (triChain n) T x := by
  unfold hitProb
  calc
    expect (iter (rungCount n aLo) T (x, c))
        (ind (fun z : ℕ × ℕ => z.1 ≤ aLo)) =
        expect (iter (rungCount n aLo) T (x, c))
          (fun z => ind (fun y : ℕ => y ≤ aLo) z.1) := by rfl
    _ = expect ((iter (rungCount n aLo) T (x, c)).map Prod.fst)
        (ind (fun y : ℕ => y ≤ aLo)) := by rw [expect_map]
    _ = expect (iter (freeze (fun y : ℕ => y ≤ aLo) (triChain n)) T x)
        (ind (fun y : ℕ => y ≤ aLo)) := by
          rw [iter_map_of_step_map (rungCount n aLo)
            (freeze (fun y : ℕ => y ≤ aLo) (triChain n)) Prod.fst
            (rungCount_map_fst n aLo h3)]

/-- A productive-mass lower bound gives the one-step counter contraction at an
interior Tri state. -/
theorem triCount_step_of_productive_lower {n a b c : ℕ} {w p p' : ℝ≥0∞}
    (hb : a + b + 2 = n) (h3 : 3 ≤ n) (hp : p + p' = 1) (hw : w ≤ 1)
    (hpq : p ≤ triStep (a + 1) (b + 1) (by omega) a +
      triStep (a + 1) (b + 1) (by omega) (a + 2)) :
    expect (triCount n (a + 1, c)) (fun z => w ^ z.2) ≤
      (p' + p * w) * w ^ c := by
  apply count_step_of_masses
      (q := triStep (a + 1) (b + 1) (by omega) a +
        triStep (a + 1) (b + 1) (by omega) (a + 2))
      (q' := triStep (a + 1) (b + 1) (by omega) (a + 1))
      (p := p) (p' := p')
  · simpa [add_comm] using triCount_masses a b (by omega)
  · exact hp
  · exact hw
  · exact hpq
  · exact triCount_decomp n a b c hb h3 w

/-- Every guarded step contracts the counter potential by the Bernoulli factor
provided productive mass is uniformly at least `p` on the live region. -/
theorem rungCount_step (n aLo : ℕ) (h3 : 3 ≤ n) (w p p' : ℝ≥0∞)
    (hp : p + p' = 1) (hw : w ≤ 1)
    (hprod : ∀ (a b : ℕ) (hb : a + b + 2 = n), aLo ≤ a →
      p ≤ triStep (a + 1) (b + 1) (by omega) a +
        triStep (a + 1) (b + 1) (by omega) (a + 2)) :
    ∀ s, expect (rungCount n aLo s) (fun z => w ^ z.2) ≤
      (p' + p * w) * w ^ s.2 := by
  rintro ⟨x, c⟩
  by_cases hlo : x ≤ aLo
  · apply count_step_of_masses
        (K := rungCount n aLo) (count := Prod.snd) (s := (x, c))
        (w := w) (q := 1) (q' := 0) (p := p) (p' := p')
    · simp
    · exact hp
    · exact hw
    · rw [← hp]
      exact le_add_right le_rfl
    · rw [rungCount, if_pos hlo, expect_pure]
      simp
  · by_cases hhi : n ≤ x
    · apply count_step_of_masses
          (K := rungCount n aLo) (count := Prod.snd) (s := (x, c))
          (w := w) (q := 1) (q' := 0) (p := p) (p' := p')
      · simp
      · exact hp
      · exact hw
      · rw [← hp]
        exact le_add_right le_rfl
      · rw [rungCount, if_neg hlo, if_pos hhi, expect_pure]
        simp
    · obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := ⟨x - 1, by omega⟩
      obtain ⟨b, hb⟩ : ∃ b, a + b + 2 = n := ⟨n - a - 2, by omega⟩
      rw [rungCount, if_neg (by omega), if_neg (by omega)]
      exact triCount_step_of_productive_lower hb h3 hp hw
        (hprod a b hb (by omega))

/-- The safety half of one rung, on the guarded counting chain.  Its potential
base is the Feller ratio `bHi / aLo` and is independent of the deadline base. -/
theorem rung_safety (n aLo bHi k T c₀ : ℕ) (h3 : 3 ≤ n)
    (hpop : aLo + bHi + 2 = n) (haLo : 0 < aLo) (hbHi : 0 < bHi)
    (hmaj : bHi ≤ aLo) :
    ∑' z : ℕ × ℕ, (if aLo < z.1 then 0
      else iter (rungCount n aLo) T (aLo + k, c₀) z) ≤
      ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k := by
  calc
    ∑' z : ℕ × ℕ, (if aLo < z.1 then 0
        else iter (rungCount n aLo) T (aLo + k, c₀) z) =
        expect (iter (rungCount n aLo) T (aLo + k, c₀))
          (ind (fun z : ℕ × ℕ => z.1 ≤ aLo)) := by
            unfold expect ind
            apply tsum_congr
            intro z
            by_cases hz : z.1 ≤ aLo <;> simp [hz]
    _ = hitProb (fun z : ℕ => z ≤ aLo) (triChain n) T (aLo + k) :=
      rungCount_bad_eq_hitProb n aLo h3 T (aLo + k) c₀
    _ ≤ ⨆ t : ℕ, hitProb (fun z : ℕ => z ≤ aLo) (triChain n) t (aLo + k) :=
      le_iSup (fun t : ℕ => hitProb (fun z : ℕ => z ≤ aLo)
        (triChain n) t (aLo + k)) T
    _ ≤ ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k :=
      tri_feller n aLo bHi k h3 hpop haLo hbHi hmaj

/-- The deadline half of one rung.  It bounds the probability that the guarded
productive counter has not exceeded `m` after `T` interactions. -/
theorem rung_deadline (n aLo T m c₀ : ℕ) (h3 : 3 ≤ n) (w p p' : ℝ≥0∞)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hp : p + p' = 1)
    (hprod : ∀ (a b : ℕ) (hb : a + b + 2 = n), aLo ≤ a →
      p ≤ triStep (a + 1) (b + 1) (by omega) a +
        triStep (a + 1) (b + 1) (by omega) (a + 2))
    (x₀ : ℕ) :
    ∑' z, (if z.2 ≤ m then iter (rungCount n aLo) T (x₀, c₀) z else 0) ≤
      (p' + p * w) ^ T * w ^ c₀ / w ^ m := by
  exact count_tail_bernoulli (rungCount n aLo) Prod.snd w p p' hw1 hw0
    (rungCount_step n aLo h3 w p p' hp hw1 hprod) T m (x₀, c₀)

/-- Combining two postconditions at the same horizon costs the sum of their
failure bounds. -/
theorem Reaches.inter {K : α → PMF α} {P Q R : α → Prop}
    [DecidablePred Q] [DecidablePred R] {T : ℕ} {ε₁ ε₂ : ℝ≥0∞}
    (hQ : Reaches K T P Q ε₁) (hR : Reaches K T P R ε₂) :
    Reaches K T P (fun z => Q z ∧ R z) (ε₁ + ε₂) := by
  intro s hs
  calc
    ∑' z, (if Q z ∧ R z then 0 else iter K T s z) ≤
        ∑' z, ((if Q z then 0 else iter K T s z) +
          (if R z then 0 else iter K T s z)) := by
            refine ENNReal.tsum_le_tsum fun z => ?_
            by_cases hq : Q z <;> by_cases hr : R z <;> simp [hq, hr]
    _ = (∑' z, (if Q z then 0 else iter K T s z)) +
        ∑' z, (if R z then 0 else iter K T s z) := ENNReal.tsum_add
    _ ≤ ε₁ + ε₂ := add_le_add (hQ s hs) (hR s hs)

/-- One guarded rung combines the Feller safety error and the independent
productive-count deadline error by a union bound. -/
theorem rung_bound (n aLo bHi k T m c₀ : ℕ) (h3 : 3 ≤ n)
    (hpop : aLo + bHi + 2 = n) (haLo : 0 < aLo) (hbHi : 0 < bHi)
    (hmaj : bHi ≤ aLo) (w p p' : ℝ≥0∞) (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hp : p + p' = 1)
    (hprod : ∀ (a b : ℕ) (hb : a + b + 2 = n), aLo ≤ a →
      p ≤ triStep (a + 1) (b + 1) (by omega) a +
        triStep (a + 1) (b + 1) (by omega) (a + 2)) :
    Reaches (rungCount n aLo) T
      (fun s => s = (aLo + k, c₀))
      (fun z => aLo < z.1 ∧ m < z.2)
      (((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k +
        (p' + p * w) ^ T * w ^ c₀ / w ^ m) := by
  apply Reaches.inter
  · intro s hs
    subst s
    exact rung_safety n aLo bHi k T c₀ h3 hpop haLo hbHi hmaj
  · intro s hs
    subst s
    calc
      ∑' z, (if m < z.2 then 0
          else iter (rungCount n aLo) T (aLo + k, c₀) z) =
          ∑' z, (if z.2 ≤ m then
            iter (rungCount n aLo) T (aLo + k, c₀) z else 0) := by
              apply tsum_congr
              intro z
              by_cases hz : z.2 ≤ m
              · simp [hz, Nat.not_lt.mpr hz]
              · simp [hz, Nat.lt_of_not_ge hz]
      _ ≤ (p' + p * w) ^ T * w ^ c₀ / w ^ m :=
        rung_deadline n aLo T m c₀ h3 w p p' hw1 hw0 hp hprod (aLo + k)

end Tri
