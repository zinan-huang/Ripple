/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase0

/-!
# Conditional assembly of Theorem 1(a)

This file isolates the sole new probabilistic input needed for Theorem 1(a).
Phase 0 starts from an arbitrary physical configuration and reaches a
square-root gap in either direction.  The already proved phase-1--3 assembly
then reaches the corresponding consensus.  The `X`-majority assembly is reused
verbatim; the `Y`-majority copy follows from the exact `X`/`Y` symmetry of
`triChain`, proved below.

`Phase0Hyp C₀` is deliberately only the phase-0 interface.  It asserts a
`C₀ * γ * n * lg n` horizon and failure at most `n⁻¹^(γ/100)`.  The
theorem `theorem1a_of_phase0` absorbs that error together with the existing
phase-1--3 error into the headline exponent `γ/200`.
-/

namespace Tri

open scoped ENNReal

set_option exponentiation.threshold 500

/-- Exchange the two species counts inside the physical interval `[0,n]`.
Outside that interval it is the identity, matching the inert extension used by
`triChain`. -/
def populationFlip (n x : ℕ) : ℕ :=
  if x ≤ n then n - x else x

/-- Species exchange is an involution on the full state space. -/
@[simp] theorem populationFlip_involutive (n x : ℕ) :
    populationFlip n (populationFlip n x) = x := by
  unfold populationFlip
  split_ifs <;> omega

/-- Species exchange preserves physical states. -/
theorem populationFlip_le {n x : ℕ} (hx : x ≤ n) : populationFlip n x ≤ n := by
  simp only [populationFlip, if_pos hx]
  omega

/-- A physical count and its exchanged count sum to the population. -/
theorem add_populationFlip {n x : ℕ} (hx : x ≤ n) :
    x + populationFlip n x = n := by
  simp only [populationFlip, if_pos hx]
  omega

/-- The exchanged count is characterized without exposing natural subtraction. -/
theorem populationFlip_eq_of_add {n x y : ℕ} (hxy : x + y = n) :
    populationFlip n x = y := by
  have hx : x ≤ n := by omega
  simp only [populationFlip, if_pos hx]
  omega

@[simp] theorem populationFlip_zero (n : ℕ) : populationFlip n 0 = n := by
  exact populationFlip_eq_of_add (Nat.zero_add n)

@[simp] theorem populationFlip_self (n : ℕ) : populationFlip n n = 0 := by
  exact populationFlip_eq_of_add (Nat.add_zero n)

namespace TripleKind

/-- Exchange `X` and `Y` in a sampled triple. -/
def flip : TripleKind → TripleKind
  | .xxx => .yyy
  | .xxy => .xyy
  | .xyy => .xxy
  | .yyy => .xxx

@[simp] theorem flip_involutive (k : TripleKind) : flip (flip k) = k := by
  cases k <;> rfl

end TripleKind

/-- Exchanging the species pushes the interaction-composition distribution to
the distribution with exchanged population counts. -/
theorem interactionPMF_flip (x y : ℕ) (hxy : 3 ≤ x + y) (hyx : 3 ≤ y + x) :
    (interactionPMF x y hxy).map TripleKind.flip = interactionPMF y x hyx := by
  ext k
  rw [PMF.map_apply, tsum_fintype]
  rw [show (Finset.univ : Finset TripleKind) =
      {TripleKind.xxx, TripleKind.xxy, TripleKind.xyy, TripleKind.yyy} from rfl]
  cases k <;>
    simp [TripleKind.flip, TripleKind.weight, interactionPMF_apply, Nat.add_comm,
      Nat.mul_comm]

/-- At an interior state, exchanging species pushes one CRN step to the step
with exchanged counts. -/
theorem triStep_flip {n a b : ℕ} (hpop : a + b + 2 = n) (h3 : 3 ≤ n) :
    (triStep (a + 1) (b + 1) (by omega)).map (populationFlip n) =
      triStep (b + 1) (a + 1) (by omega) := by
  unfold triStep
  rw [PMF.map_comp]
  have hfun : populationFlip n ∘ nextX (a + 1) =
      nextX (b + 1) ∘ TripleKind.flip := by
    funext k
    cases k <;> simp only [Function.comp_apply, nextX, TripleKind.flip] <;>
      unfold populationFlip <;> split <;> omega
  rw [hfun, ← PMF.map_comp]
  rw [interactionPMF_flip (a + 1) (b + 1) (by omega) (by omega)]

/-- The `X`-count chain is exactly invariant under exchange of `X` and `Y`.
The statement is global because both `populationFlip` and `triChain` are the
identity outside the physical interval. -/
theorem triChain_flip (n x : ℕ) :
    (triChain n x).map (populationFlip n) = triChain n (populationFlip n x) := by
  by_cases h3 : 3 ≤ n
  · by_cases hx : x ≤ n
    · rcases Nat.eq_zero_or_pos x with rfl | hxpos
      · rw [consensus_absorbing n 0 (Or.inl rfl), PMF.pure_map]
        have hn : populationFlip n 0 = n := populationFlip_eq_of_add (Nat.zero_add n)
        rw [hn, triChain_consensus h3]
      · by_cases hxn : x = n
        · subst x
          rw [triChain_consensus h3, PMF.pure_map]
          have hn : populationFlip n n = 0 := populationFlip_eq_of_add (Nat.add_zero n)
          rw [hn, consensus_absorbing n 0 (Or.inl rfl)]
        · obtain ⟨a, rfl⟩ : ∃ a : ℕ, x = a + 1 := ⟨x - 1, by omega⟩
          obtain ⟨b, hpop⟩ : ∃ b : ℕ, a + b + 2 = n :=
            ⟨n - (a + 2), by omega⟩
          have hflip : populationFlip n (a + 1) = b + 1 := by
            apply populationFlip_eq_of_add
            omega
          rw [triChain_apply hpop h3, hflip]
          rw [triChain_apply (by omega : b + a + 2 = n) h3]
          exact triStep_flip hpop h3
    · have hflip : populationFlip n x = x := by simp [populationFlip, hx]
      rw [hflip]
      unfold triChain
      rw [dif_neg (by omega), PMF.pure_map, hflip]
  · have hchain : ∀ z : ℕ, triChain n z = PMF.pure z := by
      intro z
      unfold triChain
      rw [dif_neg (by omega)]
    rw [hchain, PMF.pure_map, hchain]

/-- Species exchange commutes with every deterministic iterate of the chain. -/
theorem iter_triChain_flip (n T x : ℕ) :
    (iter (triChain n) T x).map (populationFlip n) =
      iter (triChain n) T (populationFlip n x) :=
  iter_map_of_step_map (triChain n) (triChain n) (populationFlip n)
    (triChain_flip n) T x

/-- A reachability estimate for one species orientation transports, with the
same horizon and error, to the exchanged orientation. -/
theorem Reaches.flip {n T : ℕ} {P Q : ℕ → Prop} [DecidablePred Q]
    {ε : ℝ≥0∞} (h : Reaches (triChain n) T P Q ε) :
    Reaches (triChain n) T
      (fun x => P (populationFlip n x))
      (fun x => Q (populationFlip n x)) ε := by
  classical
  intro s hs
  have hbound := h (populationFlip n s) hs
  let V : ℕ → ℝ≥0∞ := fun z => if Q z then 0 else 1
  calc
    ∑' z, (if Q (populationFlip n z) then 0 else iter (triChain n) T s z) =
        expect (iter (triChain n) T s) (fun z => V (populationFlip n z)) := by
          apply tsum_congr
          intro z
          simp only [V]
          split_ifs <;> simp
    _ = expect ((iter (triChain n) T s).map (populationFlip n)) V := by
          rw [expect_map]
    _ = expect (iter (triChain n) T (populationFlip n s)) V := by
          rw [iter_triChain_flip]
    _ = ∑' z, (if Q z then 0 else
          iter (triChain n) T (populationFlip n s) z) := by
          apply tsum_congr
          intro z
          simp only [V]
          split_ifs <;> simp
    _ ≤ ε := hbound

/-- On physical states, a `Y`-directed gap is exactly an `X`-directed gap after
species exchange. -/
theorem hasYInitialGap_iff_flip {n γ x : ℕ} (hx : x ≤ n) :
    HasYInitialGap n γ x ↔ HasXInitialGap n γ (populationFlip n x) := by
  constructor
  · rintro ⟨gap, hgap, hsq⟩
    refine ⟨gap, ?_, hsq⟩
    have hsum := add_populationFlip hx
    omega
  · rintro ⟨gap, hgap, hsq⟩
    refine ⟨gap, ?_, hsq⟩
    have hsum := add_populationFlip hx
    omega

/-- The already proved phases 1--3, exposed as one reusable exact-time
reachability theorem.  The padding hidden in the reconciled schedule is valid
because all-`X` is absorbing. -/
theorem phase123_reaches_X (n γ : ℕ) (hn : 2 ^ 420 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) :
    Reaches (triChain n) (48 * γ * n * Nat.log 2 n)
      (AssemblyInitial n γ) (IsXMajority n) (phase0Error n γ) := by
  have hn128 : 128 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num)
      (le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num : 128 ≤ 420)) hn)
  have hn96 : 96 ≤ n :=
    le_trans (le_trans (by norm_num : (96 : ℕ) ≤ 2 ^ 7)
      (Nat.pow_le_pow_right (by norm_num) (by norm_num : 7 ≤ 420))) hn
  have hphi : Phase1PhiRateHyp n :=
    ⟨phase1_progress_field n, fun γ j => phase1_gap_lower_field n γ j⟩
  have h₁ := phase1_reaches_corrected 24 n γ hn hγ hsize hphi (by norm_num)
  have h₂ := phase2_reaches_additive n γ (by omega) hn96 hγ hsize hn128
  have h₃ : Reaches (triChain n) (phase3HorizonScaled 16 n γ)
      (Phase3Entry n γ) (IsXMajority n) (canonicalPhase3Error n γ) := by
    obtain ⟨h3, _⟩ := theorem1bN₀_package hn hγ
    exact phase3_reaches_scaled_canonical n γ h3 hγ hsize
  have hreach := Reaches.three h₁ h₂ h₃
  obtain ⟨U, hU⟩ := reconciled_schedule 24 n γ hγ
  have hpadded := hreach.pad_of_absorbing (fun s hs => by
    exact consensus_absorbing n s (Or.inr hs)) U
  norm_num only at hU
  rw [hU] at hpadded
  apply hpadded.mono_error
  obtain ⟨h3, h46, _, h8, ht1, ht2, ht3⟩ := theorem1bN₀_package hn hγ
  have h1 : phase1RefactoredError 24 n γ ≤
      4 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 34 : ℝ) * (γ : ℝ)) :=
    phase1RefactoredError_le_of_log_ge_fortysix 24 n γ h46 hγ
  have h2 : (∑ i ∈ Finset.range (phase2StageCount n γ),
        phase2AdditiveRungError n (2 + i)) ≤
      6 * (n : ℝ≥0∞)⁻¹ ^ ((1 / 50 : ℝ) * (γ : ℝ)) :=
    phase2_additive_error_le n γ hγ (by omega) hn96 hsize hn128
  have h3e : canonicalPhase3Error n γ ≤
      2 * (n : ℝ≥0∞)⁻¹ ^ ((1 : ℝ) * (γ : ℝ)) :=
    canonicalPhase3Error_le_two_inverse n γ h3 hγ hsize h8
  unfold phase0Error
  refine reconciled_budget n γ (by omega) hγ _ _ _ h1 h2 h3e ?_ ?_ ?_
  · rw [show (1 / 34 : ℝ) * (γ : ℝ) - (1 / 100 : ℝ) * (γ : ℝ) =
        (33 / 1700 : ℝ) * (γ : ℝ) by ring]
    exact_mod_cast ht1
  · rw [show (1 / 50 : ℝ) * (γ : ℝ) - (1 / 100 : ℝ) * (γ : ℝ) =
        (1 / 100 : ℝ) * (γ : ℝ) by ring]
    exact_mod_cast ht2
  · rw [show (1 : ℝ) * (γ : ℝ) - (1 / 100 : ℝ) * (γ : ℝ) =
        (99 / 100 : ℝ) * (γ : ℝ) by ring]
    exact_mod_cast ht3

/-- The fixed threshold `2^420` clears the factor needed to combine two
`n⁻¹^(γ/100)` errors under the shallower exponent `γ/200`. -/
theorem three_le_rpow_one_twohundred {n γ : ℕ} (hn : 2 ^ 420 ≤ n) (hγ : 1 ≤ γ) :
    3 ≤ (n : ℝ≥0∞) ^ ((1 / 200 : ℝ) * (γ : ℝ)) := by
  have hn1 : (1 : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
    exact_mod_cast le_trans (Nat.one_le_pow 420 2 (by norm_num)) hn
  have hmono : (n : ℝ≥0∞) ^ (1 / 200 : ℝ) ≤
      (n : ℝ≥0∞) ^ ((1 / 200 : ℝ) * (γ : ℝ)) := by
    apply ENNReal.rpow_le_rpow_of_exponent_le hn1
    have hγR : (1 : ℝ) ≤ (γ : ℝ) := by exact_mod_cast hγ
    nlinarith
  have hpow : (3 : ℕ) ^ 200 ≤ n := by
    exact le_trans (by norm_num : (3 : ℕ) ^ 200 ≤ 2 ^ 420) hn
  have hbase : (((3 : ℝ≥0∞) ^ (200 : ℕ)) : ℝ≥0∞) ^ (1 / 200 : ℝ) ≤
      (n : ℝ≥0∞) ^ (1 / 200 : ℝ) := by
    apply ENNReal.rpow_le_rpow
    · exact_mod_cast hpow
    · norm_num
  have hthree : (((3 : ℝ≥0∞) ^ (200 : ℕ)) : ℝ≥0∞) ^
      (1 / 200 : ℝ) = 3 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [hthree] at hbase
  exact hbase.trans hmono

/-- The phase-0 error and the complete phase-1--3 error fit the final
Theorem 1(a) power-law budget. -/
theorem phase0_add_phase123_error_le (n γ : ℕ) (hn : 2 ^ 420 ≤ n)
    (hγ : 1 ≤ γ) :
    phase0Error n γ + phase0Error n γ ≤
      (n : ℝ≥0∞)⁻¹ ^ ((1 / 200 : ℝ) * (γ : ℝ)) := by
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow 420 2 (by norm_num)) hn
  have hexp : (1 / 200 : ℝ) * (γ : ℝ) ≤ (1 / 100 : ℝ) * (γ : ℝ) := by
    have hγ0 : (0 : ℝ) ≤ (γ : ℝ) := Nat.cast_nonneg γ
    nlinarith
  have hthreshold : (3 : ℝ≥0∞) * 1 ≤
      (n : ℝ≥0∞) ^ ((1 / 100 : ℝ) * (γ : ℝ) -
        (1 / 200 : ℝ) * (γ : ℝ)) := by
    rw [show (1 / 100 : ℝ) * (γ : ℝ) - (1 / 200 : ℝ) * (γ : ℝ) =
        (1 / 200 : ℝ) * (γ : ℝ) by ring, mul_one]
    exact three_le_rpow_one_twohundred hn hγ
  have hpiece : phase0Error n γ ≤
      (1 / 3 : ℝ≥0∞) *
        (n : ℝ≥0∞)⁻¹ ^ ((1 / 200 : ℝ) * (γ : ℝ)) := by
    unfold phase0Error
    simpa only [one_mul] using inv_rpow_third 1
      ((1 / 100 : ℝ) * (γ : ℝ)) ((1 / 200 : ℝ) * (γ : ℝ))
      n hexp hn1 hthreshold
  simpa using three_thirds_le hpiece hpiece
    (show (0 : ℝ≥0∞) ≤ (1 / 3) *
      (n : ℝ≥0∞)⁻¹ ^ ((1 / 200 : ℝ) * (γ : ℝ)) from bot_le)

/-- **Theorem 1(a) reduced to phase 0 alone.**

Once phase 0 supplies a square-root gap in either direction, the unconditional
phase-1--3 chain reaches the corresponding absorbing consensus. -/
theorem theorem1a_of_phase0 (C₀ : ℕ) (hphase0 : Phase0Hyp C₀) :
    Theorem1a_statement := by
  have hn₀3 : 3 ≤ 2 ^ 420 :=
    le_trans (by norm_num : (3 : ℕ) ≤ 2 ^ 2)
      (Nat.pow_le_pow_right (by norm_num) (by norm_num : 2 ≤ 420))
  refine ⟨C₀ + 48, 2 ^ 420, 1 / 200, by omega, by norm_num, hn₀3, ?_⟩
  intro n γ x₀ hn hγ hsize hx₀
  have hX := phase123_reaches_X n γ hn hγ hsize
  have hXconsensus : Reaches (triChain n) (48 * γ * n * Nat.log 2 n)
      (AssemblyInitial n γ) (IsConsensus n) (phase0Error n γ) :=
    hX.mono_post (fun z hz => Or.inr hz)
  have hYraw := hX.flip
  have hYconsensus : Reaches (triChain n) (48 * γ * n * Nat.log 2 n)
      (fun x => AssemblyInitial n γ (populationFlip n x))
      (IsConsensus n) (phase0Error n γ) :=
    hYraw.mono_post (by
      intro z hz
      left
      change populationFlip n z = n at hz
      have h := congrArg (populationFlip n) hz
      simpa using h)
  have hfinish : Reaches (triChain n) (48 * γ * n * Nat.log 2 n)
      (Phase0Seed n γ) (IsConsensus n) (phase0Error n γ) := by
    intro x hx
    rcases hx with ⟨hxPhysical, hxGap | hyGap⟩
    · exact hXconsensus x ⟨hxPhysical, hxGap⟩
    · exact hYconsensus x
        ⟨populationFlip_le hxPhysical, (hasYInitialGap_iff_flip hxPhysical).mp hyGap⟩
  have hreach := (hphase0.reaches n γ hn hγ hsize).comp hfinish
  have htime : C₀ * γ * n * Nat.log 2 n + 48 * γ * n * Nat.log 2 n =
      (C₀ + 48) * γ * n * Nat.log 2 n := by ring
  rw [htime] at hreach
  exact (hreach x₀ hx₀).trans (phase0_add_phase123_error_le n γ hn hγ)

/-- **Theorem 1(a).**  From any initial configuration the tri-molecular
Approximate-Majority CRN reaches consensus within `O(γ n lg n)` interaction
events, except for a failure mass `exp(-Ω(γ lg n))`. -/
theorem theorem1a : Theorem1a_statement :=
  theorem1a_of_phase0 exists_phase0Hyp.choose exists_phase0Hyp.choose_spec

end Tri

#print axioms Tri.populationFlip_involutive
#print axioms Tri.triChain_flip
#print axioms Tri.Reaches.flip
#print axioms Tri.phase123_reaches_X
#print axioms Tri.theorem1a_of_phase0
#print axioms Tri.theorem1a
