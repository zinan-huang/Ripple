/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBEarlyLadder

/-!
# Single-B middle gap extension

This file continues the proven early ladder at the fixed unit `u = n / 2^18`.
The reusable gap-chain theorem is kept at the physical doubled-level
checkpoint interface.
-/

namespace Tri

open scoped ENNReal

/-- Fixed middle unit from the Single-B campaign notes. -/
def singleMiddleUnit (n : ℕ) : ℕ := n / 262144

/-- Structural creation quota for the middle extension. -/
def singleMiddleQuota (n : ℕ) : ℕ := n / 30

/-- Short bootstrap from the early target `132u` to the wider-rung threshold
`258u`. -/
def singleMiddleBootstrapRungs : ℕ := 126

/-- Main fixed-unit middle rungs using the `g = 256u` structural rung. -/
def singleMiddleMainRungs : ℕ := 98074

/-- Total fixed-unit middle rungs.  This lands at gap `98332·(n/2^18)`,
just above the `3n/8` late-ladder entry scale. -/
def singleMiddleRungs : ℕ :=
  singleMiddleBootstrapRungs + singleMiddleMainRungs

/-- Public middle checkpoint, still in physical doubled-level gap form. -/
def SingleMiddleCheckpoint (n : ℕ) (s : SingleState n) : Prop :=
  SingleGapCheckpoint n (132 * singleMiddleUnit n +
    singleMiddleRungs * singleMiddleUnit n) s

instance (n : ℕ) : DecidablePred (SingleMiddleCheckpoint n) := fun _ =>
  inferInstanceAs (Decidable (_ ≤ _))

/-- Middle-extension horizon. -/
def singleMiddleHorizon (n : ℕ) : ℕ :=
  singleMiddleBootstrapRungs * singleWideHorizon n (n / 8) +
    singleMiddleMainRungs * singleWideHorizon n (singleMiddleQuota n)

/-- Middle-extension error. -/
noncomputable def singleMiddleError (n : ℕ) : ℝ≥0∞ :=
  singleMiddleBootstrapRungs *
      (8 * singleGapEnvelope n (singleMiddleUnit n)) +
    singleMiddleMainRungs *
      (8 * singleGapEnvelope n (singleMiddleUnit n))

/-- A logarithmic lower bound makes the fixed middle unit nonzero. -/
theorem singleMiddleUnit_pos {n : ℕ} (hlog : 30 ≤ Nat.log 2 n) :
    0 < singleMiddleUnit n := by
  unfold singleMiddleUnit
  have hn : 262144 ≤ n := by
    calc
      262144 = 2 ^ 18 := by norm_num
      _ ≤ 2 ^ Nat.log 2 n :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ n := Nat.pow_log_le_self 2 (by
        intro h0
        rw [h0, Nat.log_zero_right] at hlog
        omega)
  exact Nat.div_pos hn (by norm_num)

/-- The fixed-unit middle chain reaches the public middle checkpoint. -/
theorem singleMiddle_reaches
    (n : ℕ) (hn : 2 ≤ n) (hlog : 30 ≤ Nat.log 2 n) :
    Reaches (singleStateStep n hn) (singleMiddleHorizon n)
      (SingleEarlyTarget n)
      (SingleMiddleCheckpoint n)
      (singleMiddleError n) := by
  set u : ℕ := singleMiddleUnit n with huDef
  have hu : 0 < u := by
    simpa [huDef] using singleMiddleUnit_pos hlog
  have hlar : 131072 * u ≤ n := by
    rw [huDef]
    unfold singleMiddleUnit
    have hmul := Nat.mul_div_le n 262144
    omega
  have hbootSmall :
      4 * (132 * u + singleMiddleBootstrapRungs * u) +
          1032 * u + 8 ≤ n := by
    unfold singleMiddleBootstrapRungs
    omega
  have hMdir :
      32 * n ≤ 1000 * singleMiddleQuota n := by
    unfold singleMiddleQuota
    have h30 := Nat.div_add_mod n 30
    have h30mod := Nat.mod_lt n (by norm_num : 0 < 30)
    have hnlarge : 725 ≤ n := by
      calc
        725 ≤ 2 ^ 10 := by norm_num
        _ ≤ 2 ^ Nat.log 2 n :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ n := Nat.pow_log_le_self 2 (by
          intro h0
          rw [h0, Nat.log_zero_right] at hlog
          omega)
    omega
  have hM8 :
      8 * singleMiddleQuota n ≤ n := by
    unfold singleMiddleQuota
    calc
      8 * (n / 30) ≤ 30 * (n / 30) :=
        Nat.mul_le_mul_right (n / 30) (by norm_num : 8 ≤ 30)
      _ ≤ n := Nat.mul_div_le n 30
  have hsmall :
      2 * ((132 * u + singleMiddleBootstrapRungs * u) +
          singleMiddleMainRungs * u) + 1024 * u +
          4 * singleMiddleQuota n ≤ n := by
    rw [huDef]
    unfold singleMiddleUnit singleMiddleBootstrapRungs
      singleMiddleMainRungs singleMiddleQuota
    have hdiv := Nat.div_add_mod n 262144
    have hmod := Nat.mod_lt n (by norm_num : 0 < 262144)
    have h30le : 30 * (n / 30) ≤ n := Nat.mul_div_le n 30
    have huLarge : 1000 ≤ n / 262144 := by
      have hnLarge : 1000 * 262144 ≤ n := by
        calc
          1000 * 262144 ≤ 2 ^ 28 := by norm_num
          _ ≤ 2 ^ Nat.log 2 n :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          _ ≤ n := Nat.pow_log_le_self 2 (by
            intro h0
            rw [h0, Nat.log_zero_right] at hlog
            omega)
      exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 262144)).2 hnLarge
    omega
  have hboot := singleGapChain n u (132 * u) singleMiddleBootstrapRungs
    hn hu hlar (by omega) hbootSmall
  have hmain := singleGapChain_structural256 n u (singleMiddleQuota n)
    (132 * u + singleMiddleBootstrapRungs * u) singleMiddleMainRungs
    hn hu hlar (by unfold singleMiddleBootstrapRungs; omega) hMdir hM8 hsmall
  have hchain := hboot.comp hmain
  have htarget :
      132 * u + singleMiddleBootstrapRungs * u + singleMiddleMainRungs * u =
        132 * u + singleMiddleRungs * u := by
    unfold singleMiddleRungs
    ring
  have htargetN :
      132 * (n / 262144) + singleMiddleBootstrapRungs * (n / 262144) +
          singleMiddleMainRungs * (n / 262144) =
        132 * (n / 262144) + singleMiddleRungs * (n / 262144) := by
    unfold singleMiddleRungs
    ring
  intro s hs
  simpa [singleMiddleHorizon, singleMiddleError, SingleMiddleCheckpoint,
    SingleEarlyTarget, huDef, singleMiddleUnit, htarget, htargetN] using
    hchain s (by
      simpa [SingleEarlyTarget, huDef, singleMiddleUnit] using hs)

section Inhabitation

example : singleMiddleUnit (2 ^ 30) = 4096 := by
  norm_num [singleMiddleUnit]

example : singleMiddleQuota (2 ^ 30) = 35791394 := by
  norm_num [singleMiddleQuota]

example :
    ∃ s : SingleState (2 ^ 30), SingleMiddleCheckpoint (2 ^ 30) s := by
  refine ⟨⟨⟨2 ^ 30, 0, 0⟩, by norm_num [BiCfg.DoubleInv]⟩, ?_⟩
  norm_num [SingleMiddleCheckpoint, SingleGapCheckpoint, singleMiddleUnit,
    singleMiddleRungs, singleMiddleBootstrapRungs, singleMiddleMainRungs,
    BiCfg.doubleLevel]

end Inhabitation

end Tri

#print axioms Tri.singleMiddleUnit_pos
#print axioms Tri.singleMiddle_reaches
