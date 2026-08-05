/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.DoubleBInvariant

/-!
# The Single-B interaction kernel

The two `X+Y` reactions have rate `1/2`.  We therefore use the common integer
denominator `2 * C(n,2)`, giving seven integral event weights.  Forgetting
which fair `X+Y` branch fired recovers the shared unordered-pair scheduler
exactly, but not the Double-B state update.
-/

namespace Tri

open scoped ENNReal

/-- The seven reaction classes of Single-B. -/
inductive SingleComp
  | xx
  | xyToX
  | xyToY
  | yy
  | xb
  | yb
  | bb
  deriving DecidableEq, Fintype, Repr

namespace SingleComp

/-- Integer event weights over the common denominator `2 * C(n,2)`. -/
def weight (x y b : ℕ) : SingleComp → ℕ
  | .xx => 2 * Nat.choose x 2
  | .xyToX => x * y
  | .xyToY => x * y
  | .yy => 2 * Nat.choose y 2
  | .xb => 2 * x * b
  | .yb => 2 * y * b
  | .bb => 2 * Nat.choose b 2

/-- Forget which of the two fair `X+Y` reactions fired. -/
def toPairComp : SingleComp → PairComp
  | .xx => .xx
  | .xyToX | .xyToY => .xy
  | .yy => .yy
  | .xb => .xb
  | .yb => .yb
  | .bb => .bb

/-- Physical Single-B state update. -/
def next (s : BiCfg) : SingleComp → BiCfg
  | .xx | .yy | .bb => s
  | .xyToX => ⟨s.x, s.y - 1, s.b + 1⟩
  | .xyToY => ⟨s.x - 1, s.y, s.b + 1⟩
  | .xb => ⟨s.x + 1, s.y, s.b - 1⟩
  | .yb => ⟨s.x, s.y + 1, s.b - 1⟩

end SingleComp

/-- The seven integer weights partition twice the unordered-pair count. -/
theorem singleComp_sum_weight (x y b : ℕ) :
    ∑ k : SingleComp, SingleComp.weight x y b k =
      2 * Nat.choose (x + y + b) 2 := by
  calc
    ∑ k : SingleComp, SingleComp.weight x y b k =
        2 * (Nat.choose x 2 + Nat.choose y 2 + Nat.choose b 2 +
          x * y + x * b + y * b) := by
            rw [show (Finset.univ : Finset SingleComp) =
              {SingleComp.xx, SingleComp.xyToX, SingleComp.xyToY,
                SingleComp.yy, SingleComp.xb, SingleComp.yb,
                SingleComp.bb} from rfl]
            simp [SingleComp.weight]
            ring
    _ = 2 * Nat.choose (x + y + b) 2 := by
          rw [three_pair_split]

/-- The normalized seven-event Single-B scheduler. -/
noncomputable def singleCompPMF
    (x y b : ℕ) (h : 2 ≤ x + y + b) : PMF SingleComp :=
  PMF.ofFintype
    (fun k =>
      (SingleComp.weight x y b k : ℝ≥0∞) /
        (2 * Nat.choose (x + y + b) 2 : ℝ≥0∞))
    (by
      have hpos : 0 < 2 * Nat.choose (x + y + b) 2 :=
        Nat.mul_pos (by omega) (Nat.choose_pos h)
      have hne :
          (((2 * Nat.choose (x + y + b) 2 : ℕ) : ℝ≥0∞)) ≠ 0 := by
        simpa using (Nat.cast_ne_zero (R := ℝ≥0∞)).mpr hpos.ne'
      have htop :
          (((2 * Nat.choose (x + y + b) 2 : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
        ENNReal.natCast_ne_top _
      simp only [div_eq_mul_inv, ← Finset.sum_mul]
      rw [show ∑ k : SingleComp,
          ((SingleComp.weight x y b k : ℕ) : ℝ≥0∞) =
          ((∑ k : SingleComp, SingleComp.weight x y b k : ℕ) : ℝ≥0∞) by
            push_cast
            rfl]
      rw [singleComp_sum_weight, ← div_eq_mul_inv]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        ENNReal.div_self hne htop)

@[simp] theorem singleCompPMF_apply
    (x y b : ℕ) (h : 2 ≤ x + y + b) (k : SingleComp) :
    singleCompPMF x y b h k =
      (SingleComp.weight x y b k : ℝ≥0∞) /
        (2 * Nat.choose (x + y + b) 2 : ℝ≥0∞) :=
  rfl

/-- Cancelling the common factor two in `ℝ≥0∞`. -/
theorem ennreal_two_mul_div_two_mul (a c : ℝ≥0∞) :
    2 * a / (2 * c) = a / c := by
  exact ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)

/-- The two half-rate `X+Y` branches recombine to the ordinary `X+Y`
pair-composition mass. -/
theorem ennreal_half_pair_add (a c : ℝ≥0∞) :
    a / (2 * c) + a / (2 * c) = a / c := by
  rw [ENNReal.div_add_div_same]
  simpa [two_mul] using ennreal_two_mul_div_two_mul a c

/-- The Single-B scheduler quotient is exactly the shared unordered-pair
scheduler.  This is a one-step event quotient, not a state-chain coupling. -/
theorem singleCompPMF_map_pairComp
    (x y b : ℕ) (h : 2 ≤ x + y + b) :
    (singleCompPMF x y b h).map SingleComp.toPairComp =
      dbPairPMF x y b h := by
  ext k
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset SingleComp) =
    {SingleComp.xx, SingleComp.xyToX, SingleComp.xyToY,
      SingleComp.yy, SingleComp.xb, SingleComp.yb,
      SingleComp.bb} from rfl]
  cases k
  · simpa [SingleComp.toPairComp, SingleComp.weight, PairComp.weight,
      singleCompPMF_apply, dbPairPMF_apply] using
        ennreal_two_mul_div_two_mul
          (Nat.choose x 2 : ℝ≥0∞)
          (Nat.choose (x + y + b) 2 : ℝ≥0∞)
  · simpa [SingleComp.toPairComp, SingleComp.weight, PairComp.weight,
      singleCompPMF_apply, dbPairPMF_apply] using
        ennreal_half_pair_add
          (x * y : ℝ≥0∞)
          (Nat.choose (x + y + b) 2 : ℝ≥0∞)
  · simpa [SingleComp.toPairComp, SingleComp.weight, PairComp.weight,
      singleCompPMF_apply, dbPairPMF_apply] using
        ennreal_two_mul_div_two_mul
          (Nat.choose y 2 : ℝ≥0∞)
          (Nat.choose (x + y + b) 2 : ℝ≥0∞)
  · simpa [SingleComp.toPairComp, SingleComp.weight, PairComp.weight,
      singleCompPMF_apply, dbPairPMF_apply, mul_assoc] using
        ennreal_two_mul_div_two_mul
          (x * b : ℝ≥0∞)
          (Nat.choose (x + y + b) 2 : ℝ≥0∞)
  · simpa [SingleComp.toPairComp, SingleComp.weight, PairComp.weight,
      singleCompPMF_apply, dbPairPMF_apply, mul_assoc] using
        ennreal_two_mul_div_two_mul
          (y * b : ℝ≥0∞)
          (Nat.choose (x + y + b) 2 : ℝ≥0∞)
  · simpa [SingleComp.toPairComp, SingleComp.weight, PairComp.weight,
      singleCompPMF_apply, dbPairPMF_apply] using
        ennreal_two_mul_div_two_mul
          (Nat.choose b 2 : ℝ≥0∞)
          (Nat.choose (x + y + b) 2 : ℝ≥0∞)

/-- One raw Single-B interaction. -/
noncomputable def singleBStep
    (s : BiCfg) (h : 2 ≤ s.x + s.y + s.b) : PMF BiCfg :=
  (singleCompPMF s.x s.y s.b h).map (SingleComp.next s)

/-- Every positive-weight Single-B event preserves total population. -/
theorem SingleComp.next_doubleInv
    (n : ℕ) (s : BiCfg) (k : SingleComp)
    (hs : s.DoubleInv n)
    (hk : SingleComp.weight s.x s.y s.b k ≠ 0) :
    (SingleComp.next s k).DoubleInv n := by
  rcases s with ⟨x, y, b⟩
  cases k <;>
    simp only [SingleComp.next, SingleComp.weight, BiCfg.DoubleInv] at hs hk ⊢ <;>
    first
    | omega
    | (rw [Nat.mul_ne_zero_iff] at hk; omega)

/-- A zero-weight Single-B event has zero scheduler mass. -/
theorem singleCompPMF_zero_of_weight_zero
    {x y b : ℕ} {h : 2 ≤ x + y + b} {k : SingleComp}
    (hk : SingleComp.weight x y b k = 0) :
    singleCompPMF x y b h k = 0 := by
  rw [singleCompPMF_apply, hk]
  simp

/-- Single-B states at fixed total population. -/
abbrev SingleState (n : ℕ) := DoubleState n

/-- Guarded Single-B transition on the invariant subtype. -/
noncomputable def SingleComp.nextSingleState
    {n : ℕ} (s : SingleState n) (k : SingleComp) : SingleState n :=
  if hk : SingleComp.weight s.1.x s.1.y s.1.b k = 0 then
    s
  else
    ⟨SingleComp.next s.1 k,
      SingleComp.next_doubleInv n s.1 k s.2 hk⟩

/-- One Single-B interaction on the fixed-population subtype. -/
noncomputable def singleStateStep
    (n : ℕ) (hn : 2 ≤ n) (s : SingleState n) : PMF (SingleState n) :=
  (singleCompPMF s.1.x s.1.y s.1.b (by
    have hs := s.2
    simp only [BiCfg.DoubleInv] at hs
    omega)).map (SingleComp.nextSingleState s)

/-- Total physical Single-B chain, frozen only below population two. -/
noncomputable def singleBChain : BiCfg → PMF BiCfg := fun s =>
  if h : 2 ≤ s.x + s.y + s.b then
    singleBStep s h
  else
    PMF.pure s

/-- The lifted Single-B step projects to the physical chain. -/
theorem singleStateStep_map_val
    (n : ℕ) (hn : 2 ≤ n) (s : SingleState n) :
    (singleStateStep n hn s).map Subtype.val = singleBChain s.1 := by
  have hs2 : 2 ≤ s.1.x + s.1.y + s.1.b := by
    have hs := s.2
    simp only [BiCfg.DoubleInv] at hs
    omega
  unfold singleStateStep singleBChain singleBStep
  rw [dif_pos hs2, PMF.map_comp]
  apply PMF.map_change_on_zero_mass
  intro k hkdiff
  unfold Function.comp SingleComp.nextSingleState at hkdiff
  split_ifs at hkdiff with hk
  · exact singleCompPMF_zero_of_weight_zero hk
  · exact absurd rfl hkdiff

/-- All-`X` consensus is absorbing for the Single-B state kernel. -/
theorem singleStateStep_consensusX
    (n : ℕ) (hn : 2 ≤ n) (s : SingleState n)
    (hs : DoubleXConsensus s) :
    singleStateStep n hn s = PMF.pure s := by
  have hconst : ∀ k, SingleComp.nextSingleState s k = s := by
    intro k
    unfold SingleComp.nextSingleState
    split_ifs with hk
    · rfl
    · apply Subtype.ext
      rcases s with ⟨⟨x, y, b⟩, hinv⟩
      simp only [DoubleXConsensus] at hs
      rcases hs with ⟨rfl, rfl, rfl⟩
      cases k <;>
        simp [SingleComp.weight, SingleComp.next] at hk ⊢
  unfold singleStateStep
  rw [show SingleComp.nextSingleState s = (fun _ => s) from funext hconst]
  exact PMF.map_const _ _

/-- All-`Y` consensus for the shared fixed-population state. -/
def SingleYConsensus {n : ℕ} (s : SingleState n) : Prop :=
  s.1.x = 0 ∧ s.1.y = n ∧ s.1.b = 0

/-- All-`Y` consensus is absorbing for the Single-B state kernel. -/
theorem singleStateStep_consensusY
    (n : ℕ) (hn : 2 ≤ n) (s : SingleState n)
    (hs : SingleYConsensus s) :
    singleStateStep n hn s = PMF.pure s := by
  have hconst : ∀ k, SingleComp.nextSingleState s k = s := by
    intro k
    unfold SingleComp.nextSingleState
    split_ifs with hk
    · rfl
    · apply Subtype.ext
      rcases s with ⟨⟨x, y, b⟩, hinv⟩
      simp only [SingleYConsensus] at hs
      rcases hs with ⟨rfl, rfl, rfl⟩
      cases k <;>
        simp [SingleComp.weight, SingleComp.next] at hk ⊢
  unfold singleStateStep
  rw [show SingleComp.nextSingleState s = (fun _ => s) from funext hconst]
  exact PMF.map_const _ _

end Tri

#print axioms Tri.singleComp_sum_weight
#print axioms Tri.singleCompPMF_map_pairComp
#print axioms Tri.SingleComp.next_doubleInv
#print axioms Tri.singleStateStep_map_val
#print axioms Tri.singleStateStep_consensusX
#print axioms Tri.singleStateStep_consensusY
