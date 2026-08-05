/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Progress
import Tri.RelaxedChain
import Tri.RelaxedDrift

/-!
# Counting productive reactions for unequal reaction rates

The counter increments exactly when the `X` count changes.  It relates the raw
interaction clock to the productive-reaction clock without conditioning on a
future productive event.
-/

namespace Tri

open scoped ENNReal

/-- The relaxed chain augmented with a productive-reaction counter. -/
noncomputable def relaxedCount
    (r : RelaxedRate) (n : ℕ) : ℕ × ℕ → PMF (ℕ × ℕ) := fun s =>
  (relaxedTriChain r n s.1).map
    (fun x' => (x', if x' = s.1 then s.2 else s.2 + 1))

/-- Projecting away the productive counter recovers the relaxed chain. -/
theorem relaxedCount_map_fst
    (r : RelaxedRate) (n : ℕ) (s : ℕ × ℕ) :
    (relaxedCount r n s).map Prod.fst = relaxedTriChain r n s.1 := by
  unfold relaxedCount
  rw [PMF.map_comp]
  convert PMF.map_id (relaxedTriChain r n s.1) using 1

/-- Counter potentials transport through the augmentation map. -/
theorem expect_relaxedCount
    (r : RelaxedRate) (n x c : ℕ) (w : ℝ≥0∞) :
    expect (relaxedCount r n (x, c)) (fun z => w ^ z.2) =
      expect (relaxedTriChain r n x)
        (fun x' => w ^ (if x' = x then c else c + 1)) := by
  unfold relaxedCount
  rw [expect_map]

/-- At an interior state, the counter either stays or increments once. -/
theorem relaxedCount_decomp
    (r : RelaxedRate) (n a b c : ℕ)
    (hpop : a + b + 2 = n) (h3 : 3 ≤ n) (w : ℝ≥0∞) :
    expect (relaxedCount r n (a + 1, c)) (fun z => w ^ z.2) =
      relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 1) * w ^ c +
        (relaxedTriStep r (a + 1) (b + 1) (by omega) a +
          relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) *
            w ^ (c + 1) := by
  rw [expect_relaxedCount, relaxedTriChain_apply r hpop h3,
    expect_relaxedTriStep]
  have h0 : (if a = a + 1 then c else c + 1) = c + 1 :=
    if_neg (by omega)
  have h1 : (if a + 1 = a + 1 then c else c + 1) = c :=
    if_pos rfl
  have h2 : (if a + 2 = a + 1 then c else c + 1) = c + 1 :=
    if_neg (by omega)
  rw [h0, h1, h2]
  ring

/-- Stay and productive masses form a normalized two-way split. -/
theorem relaxedCount_masses
    (r : RelaxedRate) (a b : ℕ)
    (h : 3 ≤ (a + 1) + (b + 1)) :
    relaxedTriStep r (a + 1) (b + 1) h (a + 1) +
        (relaxedTriStep r (a + 1) (b + 1) h a +
          relaxedTriStep r (a + 1) (b + 1) h (a + 2)) = 1 := by
  have hsum := relaxedTriStep_masses_sum r a (b + 1) h
  rw [← hsum]
  ring

/-- A productive-mass lower bound gives the one-step counter contraction. -/
theorem relaxedCount_step_of_productive_lower
    (r : RelaxedRate) {n a b c : ℕ} {w p p' : ℝ≥0∞}
    (hpop : a + b + 2 = n) (h3 : 3 ≤ n)
    (hp : p + p' = 1) (hw : w ≤ 1)
    (hpq :
      p ≤ relaxedTriStep r (a + 1) (b + 1) (by omega) a +
        relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2)) :
    expect (relaxedCount r n (a + 1, c)) (fun z => w ^ z.2) ≤
      (p' + p * w) * w ^ c := by
  apply count_step_of_masses
    (q := relaxedTriStep r (a + 1) (b + 1) (by omega) a +
      relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 2))
    (q' := relaxedTriStep r (a + 1) (b + 1) (by omega) (a + 1))
    (p := p) (p' := p')
  · simpa only [add_comm] using relaxedCount_masses r a b (by omega)
  · exact hp
  · exact hw
  · exact hpq
  · exact relaxedCount_decomp r n a b c hpop h3 w

end Tri

#print axioms Tri.relaxedCount_map_fst
#print axioms Tri.relaxedCount_decomp
#print axioms Tri.relaxedCount_step_of_productive_lower
