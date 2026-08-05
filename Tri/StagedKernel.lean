/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17Error

/-!
# Sequential composition of heterogeneous kernels

Unlike an ordinary iterate, a staged process may use a different Markov kernel
at every rung.  The construction below composes those kernels and union-bounds
their endpoint failures.
-/

namespace Tri

open scoped ENNReal

variable {α : Type*}

/-- Sequential composition of a finite list of possibly different Markov
kernels. -/
noncomputable def stagedIter
    (K : ℕ → α → PMF α) : ℕ → α → PMF α
  | 0, s => PMF.pure s
  | j + 1, s => (stagedIter K j s).bind (K j)

/-- A common superharmonic potential is preserved by a finite sequence of
possibly different kernels. -/
theorem expect_stagedIter_le
    (K : ℕ → α → PMF α)
    (V : α → ℝ≥0∞)
    (hstep : ∀ j s, expect (K j s) V ≤ V s) :
    ∀ m s, expect (stagedIter K m s) V ≤ V s := by
  intro m
  induction m with
  | zero =>
      intro s
      simp [stagedIter]
  | succ m ih =>
      intro s
      rw [show
        stagedIter K (m + 1) s =
          (stagedIter K m s).bind (K m) by rfl]
      rw [expect_bind]
      calc
        (∑' z,
            stagedIter K m s z *
              expect (K m z) V)
            ≤
          ∑' z,
            stagedIter K m s z * V z := by
              exact ENNReal.tsum_le_tsum fun z =>
                mul_le_mul_left' (hstep m z) _
        _ = expect (stagedIter K m s) V := rfl
        _ ≤ V s := ih s

/-- Bounded form of `expect_stagedIter_le`, requiring the one-stage estimate
only for kernels that occur before the displayed horizon. -/
theorem expect_stagedIter_le_of_lt
    (K : ℕ → α → PMF α)
    (V : α → ℝ≥0∞)
    (m : ℕ)
    (hstep :
      ∀ j < m, ∀ s, expect (K j s) V ≤ V s) :
    ∀ s, expect (stagedIter K m s) V ≤ V s := by
  intro s
  induction m with
  | zero =>
      simp [stagedIter]
  | succ m ih =>
      rw [show
        stagedIter K (m + 1) s =
          (stagedIter K m s).bind (K m) by rfl]
      rw [expect_bind]
      calc
        (∑' z,
            stagedIter K m s z *
              expect (K m z) V)
            ≤
          ∑' z,
            stagedIter K m s z * V z := by
              exact ENNReal.tsum_le_tsum fun z =>
                mul_le_mul_left'
                  (hstep m (Nat.lt_succ_self m) z) _
        _ = expect (stagedIter K m s) V := rfl
        _ ≤ V s := by
          apply ih
          intro j hj z
          exact hstep j (hj.trans (Nat.lt_succ_self m)) z

/-- Heterogeneous stage kernels compose by a union bound. -/
theorem terminalFailureMass_stagedIter
    (K : ℕ → α → PMF α)
    (P : ℕ → α → Prop)
    [∀ j, DecidablePred (P j)]
    (ε : ℕ → ℝ≥0∞)
    (m : ℕ)
    (hstage :
      ∀ j < m, ∀ s, P j s →
        terminalFailureMass (K j s) (P (j + 1)) ≤
          ε j)
    (s : α) (hs : P 0 s) :
    terminalFailureMass (stagedIter K m s) (P m) ≤
      ∑ j ∈ Finset.range m, ε j := by
  induction m with
  | zero =>
      rw [show stagedIter K 0 s = PMF.pure s by rfl,
        terminalFailureMass_pure]
      simp [hs]
  | succ m ih =>
      let μ := stagedIter K m s
      let Good := P m
      let f : α → ℝ≥0∞ :=
        fun z => terminalFailureMass (K m z) (P (m + 1))
      have hprefix :
          terminalFailureMass μ Good ≤
            ∑ j ∈ Finset.range m, ε j := by
        apply ih
        intro j hj
        exact hstage j (hj.trans (Nat.lt_succ_self m))
      have hgood :
          ∀ z, Good z → f z ≤ ε m := by
        intro z hz
        exact hstage m (Nat.lt_succ_self m) z hz
      have hpoint :
          ∀ z, μ z * f z ≤
            (if Good z then μ z * ε m else μ z) := by
        intro z
        by_cases hz : Good z
        · simp only [hz, if_true]
          exact mul_le_mul_left' (hgood z hz) _
        · simp only [hz, if_false]
          calc
            μ z * f z ≤ μ z * 1 :=
              mul_le_mul_left'
                (terminalFailureMass_le_one
                  (K m z) (P (m + 1))) _
            _ = μ z := mul_one _
      rw [show stagedIter K (m + 1) s = μ.bind (K m) by
        rfl]
      rw [terminalFailureMass_bind]
      calc
        expect μ f ≤
            ∑' z,
              (if Good z then μ z * ε m else μ z) := by
          unfold expect
          exact ENNReal.tsum_le_tsum hpoint
        _ =
            terminalFailureMass μ Good +
              ∑' z, if Good z then μ z * ε m else 0 := by
          unfold terminalFailureMass
          rw [← ENNReal.tsum_add]
          apply tsum_congr
          intro z
          by_cases hz : Good z <;> simp [hz]
        _ ≤ terminalFailureMass μ Good + ε m := by
          apply add_le_add le_rfl
          calc
            (∑' z, if Good z then μ z * ε m else 0)
                ≤ ∑' z, μ z * ε m := by
              exact ENNReal.tsum_le_tsum fun z => by
                by_cases hz : Good z <;> simp [hz]
            _ = (∑' z, μ z) * ε m :=
              ENNReal.tsum_mul_right
            _ = ε m := by rw [PMF.tsum_coe, one_mul]
        _ ≤ (∑ j ∈ Finset.range m, ε j) + ε m :=
          add_le_add hprefix le_rfl
        _ = ∑ j ∈ Finset.range (m + 1), ε j := by
          rw [Finset.sum_range_succ]

/-- Heterogeneous kernels compose when their primary postcondition is
pointwise, while an auxiliary random-anchor condition is controlled only in
the aggregate at each split time. -/
theorem terminalFailureMass_stagedIter_of_anchors
    (K : ℕ → α → PMF α)
    (P Anchor : ℕ → α → Prop)
    [∀ j, DecidablePred (P j)]
    [∀ j, DecidablePred (Anchor j)]
    (ε δ : ℕ → ℝ≥0∞)
    (m : ℕ)
    (s : α)
    (hs : P 0 s)
    (hstage :
      ∀ j < m, ∀ z, P j z → Anchor j z →
        terminalFailureMass (K j z) (P (j + 1)) ≤
          ε j)
    (hanchor :
      ∀ j < m,
        terminalFailureMass
          (stagedIter K j s) (Anchor j) ≤ δ j) :
    terminalFailureMass (stagedIter K m s) (P m) ≤
      ∑ j ∈ Finset.range m, (ε j + δ j) := by
  induction m with
  | zero =>
      rw [show stagedIter K 0 s = PMF.pure s by rfl,
        terminalFailureMass_pure]
      simp [hs]
  | succ m ih =>
      let μ := stagedIter K m s
      let Good := P m
      let AnchorGood := Anchor m
      let f : α → ℝ≥0∞ :=
        fun z => terminalFailureMass (K m z) (P (m + 1))
      have hprefix :
          terminalFailureMass μ Good ≤
            ∑ j ∈ Finset.range m, (ε j + δ j) := by
        apply ih
        · intro j hj z hzP hzA
          exact hstage j
            (hj.trans (Nat.lt_succ_self m)) z hzP hzA
        · intro j hj
          exact hanchor j
            (hj.trans (Nat.lt_succ_self m))
      have hanchorM :
          terminalFailureMass μ AnchorGood ≤ δ m := by
        exact hanchor m (Nat.lt_succ_self m)
      have hgood :
          ∀ z, Good z → AnchorGood z →
            f z ≤ ε m := by
        intro z hzP hzA
        exact hstage m (Nat.lt_succ_self m) z hzP hzA
      have hpoint :
          ∀ z, μ z * f z ≤
            ((if Good z then 0 else μ z) +
              (if AnchorGood z then 0 else μ z)) +
              (if Good z ∧ AnchorGood z then
                μ z * ε m
              else 0) := by
        intro z
        by_cases hzP : Good z
        · by_cases hzA : AnchorGood z
          · simp only [hzP, hzA, if_pos, and_self,
              zero_add]
            exact mul_le_mul_left' (hgood z hzP hzA) _
          · simp only [hzP, if_pos, hzA, if_false,
              zero_add, and_false, add_zero]
            calc
              μ z * f z ≤ μ z * 1 :=
                mul_le_mul_left'
                  (terminalFailureMass_le_one
                    (K m z) (P (m + 1))) _
              _ = μ z := mul_one _
        · simp only [hzP, if_false, false_and, add_zero]
          calc
            μ z * f z ≤ μ z * 1 :=
              mul_le_mul_left'
                (terminalFailureMass_le_one
                  (K m z) (P (m + 1))) _
            _ = μ z := mul_one _
            _ ≤ μ z +
                (if AnchorGood z then 0 else μ z) :=
              self_le_add_right _ _
      rw [show stagedIter K (m + 1) s = μ.bind (K m) by
        rfl]
      rw [terminalFailureMass_bind]
      calc
        expect μ f ≤
            ∑' z,
              (((if Good z then 0 else μ z) +
                (if AnchorGood z then 0 else μ z)) +
                (if Good z ∧ AnchorGood z then
                  μ z * ε m
                else 0)) := by
          unfold expect
          exact ENNReal.tsum_le_tsum hpoint
        _ =
            terminalFailureMass μ Good +
              terminalFailureMass μ AnchorGood +
              ∑' z,
                if Good z ∧ AnchorGood z then
                  μ z * ε m
                else 0 := by
          unfold terminalFailureMass
          rw [ENNReal.tsum_add, ENNReal.tsum_add]
        _ ≤ terminalFailureMass μ Good +
              terminalFailureMass μ AnchorGood +
              ε m := by
          apply add_le_add le_rfl
          calc
            (∑' z,
                if Good z ∧ AnchorGood z then
                  μ z * ε m
                else 0)
                ≤ ∑' z, μ z * ε m := by
              exact ENNReal.tsum_le_tsum fun z => by
                by_cases hz : Good z ∧ AnchorGood z <;>
                  simp [hz]
            _ = (∑' z, μ z) * ε m :=
              ENNReal.tsum_mul_right
            _ = ε m := by rw [PMF.tsum_coe, one_mul]
        _ ≤
            (∑ j ∈ Finset.range m, (ε j + δ j)) +
              δ m + ε m :=
          add_le_add
            (add_le_add hprefix hanchorM) le_rfl
        _ =
            ∑ j ∈ Finset.range (m + 1),
              (ε j + δ j) := by
          rw [Finset.sum_range_succ]
          ac_rfl

/-- Distributional form of heterogeneous staged composition.  The initial
law may already have a failure budget, and auxiliary anchor events are
charged under the actual prefix law obtained by binding that initial law to
the first `j` stages. -/
theorem terminalFailureMass_bind_stagedIter_of_anchors
    (p : PMF α)
    (K : ℕ → α → PMF α)
    (P Anchor : ℕ → α → Prop)
    [∀ j, DecidablePred (P j)]
    [∀ j, DecidablePred (Anchor j)]
    (εpre : ℝ≥0∞)
    (ε δ : ℕ → ℝ≥0∞)
    (m : ℕ)
    (hpre : terminalFailureMass p (P 0) ≤ εpre)
    (hstage :
      ∀ j < m, ∀ z, P j z → Anchor j z →
        terminalFailureMass (K j z) (P (j + 1)) ≤
          ε j)
    (hanchor :
      ∀ j < m,
        terminalFailureMass
          (p.bind (fun s => stagedIter K j s))
          (Anchor j) ≤ δ j) :
    terminalFailureMass
        (p.bind (fun s => stagedIter K m s))
        (P m)
      ≤
    εpre +
      ∑ j ∈ Finset.range m, (ε j + δ j) := by
  induction m with
  | zero =>
      simpa [stagedIter] using hpre
  | succ m ih =>
      let μ :=
        p.bind (fun s => stagedIter K m s)
      let Good := P m
      let AnchorGood := Anchor m
      let f : α → ℝ≥0∞ :=
        fun z => terminalFailureMass (K m z) (P (m + 1))
      have hprefix :
          terminalFailureMass μ Good ≤
            εpre +
              ∑ j ∈ Finset.range m, (ε j + δ j) := by
        apply ih
        · intro j hj z hzP hzA
          exact hstage j
            (hj.trans (Nat.lt_succ_self m)) z hzP hzA
        · intro j hj
          exact hanchor j
            (hj.trans (Nat.lt_succ_self m))
      have hanchorM :
          terminalFailureMass μ AnchorGood ≤ δ m := by
        exact hanchor m (Nat.lt_succ_self m)
      have hgood :
          ∀ z, Good z → AnchorGood z →
            f z ≤ ε m := by
        intro z hzP hzA
        exact hstage m (Nat.lt_succ_self m) z hzP hzA
      have hpoint :
          ∀ z, μ z * f z ≤
            ((if Good z then 0 else μ z) +
              (if AnchorGood z then 0 else μ z)) +
              (if Good z ∧ AnchorGood z then
                μ z * ε m
              else 0) := by
        intro z
        by_cases hzP : Good z
        · by_cases hzA : AnchorGood z
          · simp only [hzP, hzA, if_pos, and_self,
              zero_add]
            exact mul_le_mul_left' (hgood z hzP hzA) _
          · simp only [hzP, if_pos, hzA, if_false,
              zero_add, and_false, add_zero]
            calc
              μ z * f z ≤ μ z * 1 :=
                mul_le_mul_left'
                  (terminalFailureMass_le_one
                    (K m z) (P (m + 1))) _
              _ = μ z := mul_one _
        · simp only [hzP, if_false, false_and, add_zero]
          calc
            μ z * f z ≤ μ z * 1 :=
              mul_le_mul_left'
                (terminalFailureMass_le_one
                  (K m z) (P (m + 1))) _
            _ = μ z := mul_one _
            _ ≤ μ z +
                (if AnchorGood z then 0 else μ z) :=
              self_le_add_right _ _
      rw [show
        p.bind (fun s => stagedIter K (m + 1) s) =
          μ.bind (K m) by
            dsimp only [μ]
            exact
              (PMF.bind_bind p
                (fun s => stagedIter K m s) (K m)).symm]
      rw [terminalFailureMass_bind]
      calc
        expect μ f ≤
            ∑' z,
              (((if Good z then 0 else μ z) +
                (if AnchorGood z then 0 else μ z)) +
                (if Good z ∧ AnchorGood z then
                  μ z * ε m
                else 0)) := by
          unfold expect
          exact ENNReal.tsum_le_tsum hpoint
        _ =
            terminalFailureMass μ Good +
              terminalFailureMass μ AnchorGood +
              ∑' z,
                if Good z ∧ AnchorGood z then
                  μ z * ε m
                else 0 := by
          unfold terminalFailureMass
          rw [ENNReal.tsum_add, ENNReal.tsum_add]
        _ ≤ terminalFailureMass μ Good +
              terminalFailureMass μ AnchorGood +
              ε m := by
          apply add_le_add le_rfl
          calc
            (∑' z,
                if Good z ∧ AnchorGood z then
                  μ z * ε m
                else 0)
                ≤ ∑' z, μ z * ε m := by
              exact ENNReal.tsum_le_tsum fun z => by
                by_cases hz : Good z ∧ AnchorGood z <;>
                  simp [hz]
            _ = (∑' z, μ z) * ε m :=
              ENNReal.tsum_mul_right
            _ = ε m := by rw [PMF.tsum_coe, one_mul]
        _ ≤
            (εpre +
                ∑ j ∈ Finset.range m, (ε j + δ j)) +
              δ m + ε m :=
          add_le_add
            (add_le_add hprefix hanchorM) le_rfl
        _ =
            εpre +
              ∑ j ∈ Finset.range (m + 1),
                (ε j + δ j) := by
          rw [Finset.sum_range_succ]
          ac_rfl

end Tri

#print axioms Tri.terminalFailureMass_stagedIter
#print axioms Tri.terminalFailureMass_stagedIter_of_anchors
#print axioms Tri.terminalFailureMass_bind_stagedIter_of_anchors
#print axioms Tri.expect_stagedIter_le
#print axioms Tri.expect_stagedIter_le_of_lt
