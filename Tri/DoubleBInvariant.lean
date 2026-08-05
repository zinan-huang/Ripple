/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.BiChain

/-!
# The Double-B invariant subtype (Theorem 2)

Theorem 2's Double-B analysis is cleanest on the invariant subtype
`DoubleState n = {s : BiCfg // x + y + b = n}`, where the effective level
`doubleLevel = 2x + b` and its co-level `2y + b` partition `2n`.  This file
lifts the `doubleBStep` kernel to `DoubleState n`, records that every supported
reaction preserves the invariant, and proves the projection back to
`doubleBChain`.  Following the design in `data/theorem2_design_Q319.md`.
-/

namespace Tri

open scoped ENNReal

/-- Configurations of the Double-B system with total population `n`. -/
abbrev DoubleState (n : ℕ) := {s : BiCfg // s.DoubleInv n}

namespace BiCfg

/-- The effective `Y`-level of the Double-B system: `2y + b`. -/
def doubleCoLevel (s : BiCfg) : ℕ := 2 * s.y + s.b

end BiCfg

/-- Level and co-level partition the doubled population `2n`. -/
theorem doubleLevel_add_doubleCoLevel {n : ℕ} (s : DoubleState n) :
    s.1.doubleLevel + s.1.doubleCoLevel = 2 * n := by
  rcases s with ⟨⟨x, y, b⟩, h⟩
  simp only [BiCfg.doubleLevel, BiCfg.doubleCoLevel, BiCfg.DoubleInv] at h ⊢; omega

/-- Every reaction with positive weight preserves the population invariant.  The
weight hypothesis is essential: a zero-weight composition may involve a truncated
subtraction and need not preserve `n`. -/
theorem PairComp.next_doubleInv (n : ℕ) (s : BiCfg) (k : PairComp)
    (hs : s.DoubleInv n) (hk : PairComp.weight s.x s.y s.b k ≠ 0) :
    (PairComp.next s k).DoubleInv n := by
  rcases s with ⟨x, y, b⟩
  cases k <;>
    simp only [PairComp.next, PairComp.weight, BiCfg.DoubleInv] at hs hk ⊢ <;>
    first | omega | (rw [Nat.mul_ne_zero_iff] at hk; omega)

/-- Two maps that differ only on the zero-mass fibre induce the same pushforward. -/
theorem PMF.map_change_on_zero_mass {α β : Type*} (p : PMF α) (f g : α → β)
    (h : ∀ a, f a ≠ g a → p a = 0) : p.map f = p.map g := by
  ext z
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr; intro a
  by_cases hfg : f a = g a
  · rw [hfg]
  · rw [h a hfg]; simp

/-- A zero-weight composition carries no `dbPairPMF` mass. -/
theorem dbPairPMF_zero_of_weight_zero {x y b : ℕ} {h : 2 ≤ x + y + b} {k : PairComp}
    (hk : PairComp.weight x y b k = 0) : dbPairPMF x y b h k = 0 := by
  have hrfl : dbPairPMF x y b h k
      = (PairComp.weight x y b k : ℝ≥0∞) / (Nat.choose (x + y + b) 2 : ℝ≥0∞) := rfl
  rw [hrfl, hk]; simp

/-- The next state on the invariant subtype: zero-weight compositions (which
would break the invariant) are sent to the current state, and carry no mass. -/
noncomputable def PairComp.nextDoubleState {n : ℕ} (s : DoubleState n) (k : PairComp) :
    DoubleState n :=
  if hk : PairComp.weight s.1.x s.1.y s.1.b k = 0 then s
  else ⟨PairComp.next s.1 k, PairComp.next_doubleInv n s.1 k s.2 hk⟩

/-- The Double-B step lifted to the invariant subtype. -/
noncomputable def doubleStateStep (n : ℕ) (hn : 2 ≤ n) (s : DoubleState n) :
    PMF (DoubleState n) :=
  (dbPairPMF s.1.x s.1.y s.1.b
    (by have := s.2; simp only [BiCfg.DoubleInv] at this; omega)).map
      (PairComp.nextDoubleState s)

/-- The lifted step projects back to the physical `doubleBChain`. -/
theorem doubleStateStep_map_val (n : ℕ) (hn : 2 ≤ n) (s : DoubleState n) :
    (doubleStateStep n hn s).map Subtype.val = doubleBChain s.1 := by
  have hs2 : 2 ≤ s.1.x + s.1.y + s.1.b := by
    have := s.2; simp only [BiCfg.DoubleInv] at this; omega
  unfold doubleStateStep doubleBChain doubleBStep
  rw [dif_pos hs2, PMF.map_comp]
  apply PMF.map_change_on_zero_mass
  intro k hkdiff
  unfold Function.comp PairComp.nextDoubleState at hkdiff
  split_ifs at hkdiff with hk
  · exact dbPairPMF_zero_of_weight_zero hk
  · exact absurd rfl hkdiff

/-- All-`X` consensus on the invariant subtype. -/
def DoubleXConsensus {n : ℕ} (s : DoubleState n) : Prop :=
  s.1.x = n ∧ s.1.y = 0 ∧ s.1.b = 0

/-- `doubleLevel = 2n` characterises all-`X` consensus. -/
theorem doubleLevel_eq_top_iff {n : ℕ} (s : DoubleState n) :
    s.1.doubleLevel = 2 * n ↔ DoubleXConsensus s := by
  rcases s with ⟨⟨x, y, b⟩, h⟩
  simp only [BiCfg.doubleLevel, BiCfg.DoubleInv, DoubleXConsensus] at h ⊢; omega

end Tri
