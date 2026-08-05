/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase3Level
import Tri.EscapeSplit
import Tri.DoubleBAssembly

/-!
# Paper Corollary 3

> *Corollary 3.* Since phase 3 starts with `y ≤ γ lg n ≤ n/6` it completes
> properly, within at most `3 γ lg n` **productive** reaction events, with
> probability at least `1 − exp(−Θ(γ lg n))`.

`Tri.corollary3` is that statement, on the productive-event clock, with the
explicit exponent `1/72`.

The proof is a two-branch failure analysis on the tight internal guard
`2 y ≤ 3 d` (`d = γ lg n`), where a productive event decreases the minority
with probability at least `3/4`.  The paper's own band `y ≤ 2d` gives only
`p_down ≥ 2/3`, and at `2/3` the mean number of down-moves in `3d` events is
exactly `2d` — no Chernoff slack, so the printed deadline cannot close there.
The `3/4` bound is what makes both branches work, and it is tight in both.

| branch | tool | bound |
|---|---|---|
| escape below the guard | `feller_ruin_u`, `u = 1/3` | `(1/3)^b ≤ exp(−d/2)` |
| miss the `3d` deadline | `count_tail_frozen`, `w = 3/4`, `φ = 43/48` | `(φ³/w)^d ≤ exp(−d/72)` |

`count = id` with `m = x₀ + d` makes `count_tail_frozen`'s `count z ≤ m`
conjunct vacuous (the chain never leaves `x ≤ n ≤ x₀ + d`), which removes any
need for a trace chain or a `PMF.map` equivariance layer.
-/

namespace Tri

open scoped ENNReal

variable {α : Type*}

theorem freeze_congr (K : α → PMF α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ s, P s ↔ Q s) :
    freeze P K = freeze Q K := by
  funext s
  unfold freeze
  by_cases hs : P s
  · rw [if_pos hs, if_pos ((h s).1 hs)]
  · rw [if_neg hs, if_neg (fun hq => hs ((h s).2 hq))]

theorem terminalFailureMass_congr (p : PMF α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ s, P s ↔ Q s) :
    terminalFailureMass p P = terminalFailureMass p Q := by
  unfold terminalFailureMass
  refine tsum_congr fun z => ?_
  by_cases hz : P z
  · rw [if_pos hz, if_pos ((h z).1 hz)]
  · rw [if_neg hz, if_neg (fun hq => hz ((h z).2 hq))]

/-- All-`X` consensus is absorbing for the productive chain, so freezing on it
changes nothing. -/
theorem freeze_phase3Done (n : ℕ) :
    freeze (Phase3Done n) (productiveTriChain n) = productiveTriChain n := by
  funext x
  unfold freeze Phase3Done
  by_cases hx : x = n
  · rw [if_pos hx]
    subst hx
    unfold productiveTriChain
    rw [dif_neg (by omega)]
  · rw [if_neg hx]

/-- The phase-3 escape event, in the `level ≤ m` shape. -/
def Phase3EscapeLevel (n γ z : ℕ) : Prop :=
  phase3Level n z ≤ phase3EscapeBound n γ

instance phase3EscapeLevelDecidable (n γ : ℕ) :
    DecidablePred (Phase3EscapeLevel n γ) := by
  intro z; unfold Phase3EscapeLevel; infer_instance

/-- `Phase3Stop` is exactly "done or escaped". -/
theorem phase3Stop_iff (n γ z : ℕ) (h3 : 3 ≤ n)
    (hsize : 6 * phase3Scale n γ ≤ n) :
    Phase3Stop n γ z ↔ (Phase3Done n z ∨ Phase3EscapeLevel n γ z) := by
  unfold Phase3Stop Phase3Done Phase3EscapeLevel
  rw [phase3Level_le_iff n γ z h3 hsize]

end Tri

namespace Tri

open scoped ENNReal

/-- **Paper Corollary 3**, on the productive-event clock.  From the paper's
phase-3 entry `y ≤ γ lg n`, `3 γ lg n` productive reaction events reach all-`X`
consensus except with mass `2 exp (-(γ lg n)/72)`. -/
theorem corollary3 (n γ : ℕ) (h3 : 3 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * phase3Scale n γ ≤ n) :
    Reaches (productiveTriChain n) (3 * phase3Scale n γ)
      (Phase3EntryProductive n γ) (Phase3Done n)
      (2 * ENNReal.ofReal
        (Real.exp (-((phase3Scale n γ : ℝ) / 72)))) := by
  classical
  rintro x₀ ⟨hx₀n, hentry⟩
  have hlog : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) (by omega)
  have hd1 : 1 ≤ phase3Scale n γ := by
    unfold phase3Scale
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have hbound : 2 * phase3EscapeBound n γ + 3 * phase3Scale n γ < 2 * n := by
    unfold phase3EscapeBound; omega
  have hbound' :
      2 * n ≤ 2 * (phase3EscapeBound n γ + 1) + 3 * phase3Scale n γ := by
    unfold phase3EscapeBound; omega
  have hmx : phase3EscapeBound n γ < x₀ := by omega
  set b := x₀ - phase3EscapeBound n γ with hb
  have hbpos : phase3EscapeBound n γ + b = x₀ := by omega
  have hdb : phase3Scale n γ ≤ 2 * b := by omega
  have hlvl0 : phase3Level n x₀ = x₀ := by
    simp [phase3Level, show ¬ n < x₀ by omega]
  -- the escape branch
  have hfeller :
      hitProb (Phase3EscapeLevel n γ) (productiveTriChain n)
          (3 * phase3Scale n γ) x₀
        ≤ ENNReal.ofReal (Real.exp (-((phase3Scale n γ : ℝ) / 72))) := by
    refine le_trans (le_iSup
      (fun T => hitProb (Phase3EscapeLevel n γ) (productiveTriChain n) T x₀)
      (3 * phase3Scale n γ)) ?_
    refine le_trans ?_ (phase3_feller_ruin_le_exp _ b hdb)
    exact feller_ruin_u (K := productiveTriChain n) (phase3Level n)
      (phase3EscapeBound n γ) b (1 / 3) (by norm_num) (by simp)
      (fun z => ((1 : ℝ≥0∞) / 3) ^ phase3Level n z) (fun _ => rfl)
      (phase3_feller_hfroz_level n γ h3 hsize) x₀
      (by rw [hlvl0]; omega)
  -- the live branch
  have hstopeq : ∀ s, (Phase3Done n s ∨ Phase3EscapeLevel n γ s)
      ↔ Phase3Stop n γ s := fun s => (phase3Stop_iff n γ s h3 hsize).symm
  have hsupp : ∀ z,
      iter (freeze (Phase3Stop n γ) (productiveTriChain n))
        (3 * phase3Scale n γ) x₀ z ≠ 0 → z ≤ n := by
    intro z hz
    exact iter_support_closed _ (fun s => s ≤ n)
      (freeze_support_closed (productiveTriChain n) (Phase3Stop n γ)
        (fun s => s ≤ n) (productiveTriChain_support_le n))
      (3 * phase3Scale n γ) x₀ z hx₀n hz
  have hcount := count_tail_frozen (productiveTriChain n) (Phase3Stop n γ)
    id ((3 : ℝ≥0∞) / 4) ((43 : ℝ≥0∞) / 48)
    (by rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num))
        (Or.inl (by norm_num))]; norm_num) (by simp)
    (phase3_stopped_potential_step n γ h3 hsize)
    (3 * phase3Scale n γ) (x₀ + phase3Scale n γ) x₀
  have hlive :
      terminalFailureMass
          (iter (freeze (Phase3Stop n γ) (productiveTriChain n))
            (3 * phase3Scale n γ) x₀) (Phase3Stop n γ)
        ≤ ENNReal.ofReal (Real.exp (-((phase3Scale n γ : ℝ) / 72))) := by
    refine le_trans ?_ (le_trans hcount ?_)
    · unfold terminalFailureMass
      refine ENNReal.tsum_le_tsum fun z => ?_
      by_cases hz : Phase3Stop n γ z
      · simp [hz]
      · by_cases hzero :
            iter (freeze (Phase3Stop n γ) (productiveTriChain n))
              (3 * phase3Scale n γ) x₀ z = 0
        · simp [hz, hzero]
        · have := hsupp z hzero
          simp only [hz, if_false, id, not_false_eq_true, and_true]
          rw [if_pos (show z ≤ x₀ + phase3Scale n γ by omega)]
    · refine le_trans ?_ (phase3_count_tail_le_exp (phase3Scale n γ) x₀)
      refine ENNReal.div_le_div_right ?_ _
      refine mul_le_mul_right ?_ _
      split <;> simp
  have hsplit := terminalFailureMass_le_escape_add_live (productiveTriChain n)
    (Phase3Done n) (Phase3EscapeLevel n γ) (3 * phase3Scale n γ) x₀
  rw [freeze_phase3Done] at hsplit
  rw [freeze_congr (productiveTriChain n)
      (fun s => Phase3Done n s ∨ Phase3EscapeLevel n γ s)
      (Phase3Stop n γ) hstopeq,
    terminalFailureMass_congr _
      (fun s => Phase3Done n s ∨ Phase3EscapeLevel n γ s)
      (Phase3Stop n γ) hstopeq] at hsplit
  show terminalFailureMass
      (iter (productiveTriChain n) (3 * phase3Scale n γ) x₀)
      (Phase3Done n) ≤ _
  refine le_trans hsplit ?_
  rw [two_mul]
  exact add_le_add hfeller hlive

end Tri

#print axioms Tri.freeze_congr
#print axioms Tri.terminalFailureMass_congr
#print axioms Tri.freeze_phase3Done
#print axioms Tri.phase3Stop_iff
#print axioms Tri.corollary3
