/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Counting

/-!
# Direction-sensitive phase-1 progress

**An unsigned productive-reaction count does not imply gap progress.**  This is
already false in one step.  At population `5`, from `x = 3`, `y = 2`, the
productive direction is biased upward by exactly `2 : 1`, but the downward
reaction still has mass `3 / 10`.  On that branch `triCount` moves from
`(3, 0)` to `(2, 1)`: the productive counter grows while the signed gap falls.
The theorem `phase1_productive_direction_false` proves this counterexample.

The correct state variable is the `X`-count itself.  At fixed population `n`,
the signed gap is `2*x - n`; an up reaction increments `x`, a down reaction
decrements it, and a homogeneous interaction leaves it fixed.  Thus `x` is a
signed progress counter, unlike the second coordinate of `triCount`.

`directionStop` freezes this signed level at both the lower ruin boundary and
the upper success boundary.  Its killed geometric potential is zero on both
boundaries and is `w^x` in the live band.  A strict one-step contraction of
this potential gives the finite-time live-band tail; `ruin_le_u` separately
pays for the lower boundary.  Their union is
`DirectionProgress.phase1_direction_progress`.

The contraction premise is deliberately explicit.  `odds_cross_mul` fixes the
up/down ratio, but a quantitative finite-time contraction also needs a live
region, a tilt, and productive mass.  Feller's bound alone controls downward
ruin and cannot prove that a higher checkpoint is reached by a deadline.

## Main results

* `triCount_down_counterexample` -- the bad productive branch has mass `3/10`.
* `phase1_productive_direction_false` -- productive count plus exact odds does
  not deterministically force gap progress.
* `directionStop_step` -- the direction-sensitive three-atom contraction.
* `directionStop_safety` -- Feller safety for the doubly stopped signed level.
* `DirectionProgress.phase1_direction_progress` -- a true guarded progress
  bound: by time `T`, either the upper checkpoint has been reached, or one pays
  a ruin term plus a direction-sensitive finite-time term.
-/

namespace Tri

open scoped ENNReal

/-- At `n = 5`, `x = 3`, `y = 2`, the downward productive branch increments
the unsigned counter but decreases the `X`-count.  Its exact mass is `3/10`. -/
theorem triCount_down_counterexample :
    triCount 5 (3, 0) (2, 1) = (3 : ℝ≥0∞) / 10 := by
  unfold triCount
  rw [PMF.map_apply]
  simp only [Prod.mk.injEq]
  rw [tsum_eq_single 2]
  · rw [triChain_apply (n := 5) (a := 2) (b := 1) (by norm_num) (by norm_num)]
    rw [triStep_down]
    norm_num [Nat.choose]
  · intro x hx
    have hne : 2 ≠ x := Ne.symm hx
    simp [hne]

/-- **FALSE: productive count plus the exact direction odds does not force gap
progress.**

At `x = 3`, `y = 2`, `odds_cross_mul` says that the up/down odds are exactly
`2 : 1`.  Nevertheless, with mass `3/10`, one productive reaction reaches
`(x, count) = (2, 1)`.  The subtraction-free target `5 + 2 ≤ 2*x` says that
the final signed gap is at least `2`; it fails on this branch. -/
theorem phase1_productive_direction_false :
    ¬ (upCount 2 1 * 1 = downCount 2 1 * 2 →
      ∀ z : ℕ × ℕ, triCount 5 (3, 0) z ≠ 0 →
        1 ≤ z.2 → 5 + 2 ≤ 2 * z.1) := by
  intro h
  have hall := h (odds_cross_mul 2 1)
  have hmass : triCount 5 (3, 0) (2, 1) ≠ 0 := by
    rw [triCount_down_counterexample]
    norm_num
  have hbad := hall (2, 1) hmass (by norm_num)
  omega

/-- The Tri chain stopped once its signed level reaches either the lower ruin
region `x ≤ lower` or the upper success region `target ≤ x`. -/
noncomputable def directionStop (n lower target : ℕ) : ℕ → PMF ℕ :=
  freeze (fun x : ℕ => x ≤ lower ∨ target ≤ x) (triChain n)

/-- On either boundary, the direction-stopped chain is absorbed. -/
theorem directionStop_of_boundary (n lower target x : ℕ)
    (hx : x ≤ lower ∨ target ≤ x) :
    directionStop n lower target x = PMF.pure x := by
  exact freeze_of_mem x hx

/-- Inside the open band, the direction-stopped chain is the original Tri
chain. -/
theorem directionStop_of_live (n lower target x : ℕ)
    (hlo : lower < x) (hhi : x < target) :
    directionStop n lower target x = triChain n x := by
  exact freeze_of_not_mem x (by omega)

/-- The killed geometric potential for signed progress.  It is `w^x` in the
live band and zero after either boundary has been reached.  Killing the
potential at the upper boundary is what makes a strict contraction compatible
with an absorbing success state. -/
noncomputable def directionPotential (lower target : ℕ) (w : ℝ≥0∞) :
    ℕ → ℝ≥0∞ := fun x =>
  if lower < x ∧ x < target then w ^ x else 0

/-- In the live band, the killed potential is the ordinary geometric
potential. -/
theorem directionPotential_of_live (lower target x : ℕ) (w : ℝ≥0∞)
    (hlo : lower < x) (hhi : x < target) :
    directionPotential lower target w x = w ^ x := by
  simp [directionPotential, hlo, hhi]

/-- Outside the live band, the killed potential vanishes. -/
theorem directionPotential_of_boundary (lower target x : ℕ) (w : ℝ≥0∞)
    (hx : x ≤ lower ∨ target ≤ x) :
    directionPotential lower target w x = 0 := by
  simp [directionPotential]
  omega

/-- The killed potential is pointwise bounded by the ordinary geometric
potential. -/
theorem directionPotential_le_pow (lower target x : ℕ) (w : ℝ≥0∞) :
    directionPotential lower target w x ≤ w ^ x := by
  by_cases hx : lower < x ∧ x < target
  · simp [directionPotential, hx]
  · simp [directionPotential, hx]

/-- **One-step contraction of signed progress.**

At a live state `x = a+1`, factor `w^a` from the three directional atoms.  The
down, stay, and up branches then carry the distinct weights `1`, `w`, and
`w²`.  This is the direction-sensitive datum missing from the unsigned counter,
where both productive directions receive the same weight.

The displayed three-mass inequality is the precise quantitative premise still
needed after `odds_cross_mul`: it combines the chosen tilt with whatever live
productive-mass lower bound is available. -/
theorem directionStop_step (n lower target : ℕ) (h3 : 3 ≤ n)
    (htarget : target ≤ n) (w φ : ℝ≥0∞)
    (hdir : ∀ (a b : ℕ) (hab : a + b + 2 = n),
      lower < a + 1 → a + 1 < target →
      triStep (a + 1) (b + 1) (by omega) a
          + triStep (a + 1) (b + 1) (by omega) (a + 1) * w
          + triStep (a + 1) (b + 1) (by omega) (a + 2) * w ^ 2
        ≤ φ * w) :
    ∀ x, expect (directionStop n lower target x)
      (directionPotential lower target w)
        ≤ φ * directionPotential lower target w x := by
  intro x
  by_cases hx : lower < x ∧ x < target
  · obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := ⟨x - 1, by omega⟩
    obtain ⟨b, hab⟩ : ∃ b, a + b + 2 = n := ⟨n - a - 2, by omega⟩
    rw [directionStop_of_live n lower target (a + 1) hx.1 hx.2]
    rw [directionPotential_of_live lower target (a + 1) w hx.1 hx.2]
    calc
      expect (triChain n (a + 1)) (directionPotential lower target w)
          ≤ expect (triChain n (a + 1)) (fun z => w ^ z) := by
            unfold expect
            exact ENNReal.tsum_le_tsum fun z =>
              mul_le_mul_right (directionPotential_le_pow lower target z w) _
      _ = triStep (a + 1) (b + 1) (by omega) a * w ^ a
          + triStep (a + 1) (b + 1) (by omega) (a + 1) * w ^ (a + 1)
          + triStep (a + 1) (b + 1) (by omega) (a + 2) * w ^ (a + 2) := by
            rw [triChain_apply hab h3, expect_triStep]
      _ = w ^ a *
          (triStep (a + 1) (b + 1) (by omega) a
            + triStep (a + 1) (b + 1) (by omega) (a + 1) * w
            + triStep (a + 1) (b + 1) (by omega) (a + 2) * w ^ 2) := by
            ring
      _ ≤ w ^ a * (φ * w) :=
        mul_le_mul_right (hdir a b hab hx.1 hx.2) _
      _ = φ * w ^ (a + 1) := by ring
  · have hboundary : x ≤ lower ∨ target ≤ x := by omega
    rw [directionStop_of_boundary n lower target x hboundary, expect_pure]
    rw [directionPotential_of_boundary lower target x w hboundary]
    simp

/-- **Finite-time tail for the signed level while it remains live.**

Starting at `x₀`, the mass still strictly between the two boundaries after
`T` stopped steps is at most `φ^T / w^d`, where the upper checkpoint is
`x₀+d`.  Unlike `ruin_le_u`, this is a forward deadline estimate; its strict
contraction premise is supplied by `directionStop_step`. -/
theorem directionStop_live_tail (n lower x₀ d T : ℕ) (h3 : 3 ≤ n)
    (hlo : lower < x₀) (hd : 0 < d) (htarget : x₀ + d ≤ n)
    (w φ : ℝ≥0∞) (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hdir : ∀ (a b : ℕ) (hab : a + b + 2 = n),
      lower < a + 1 → a + 1 < x₀ + d →
      triStep (a + 1) (b + 1) (by omega) a
          + triStep (a + 1) (b + 1) (by omega) (a + 1) * w
          + triStep (a + 1) (b + 1) (by omega) (a + 2) * w ^ 2
        ≤ φ * w) :
    ∑' z, (if lower < z ∧ z < x₀ + d then
      iter (directionStop n lower (x₀ + d)) T x₀ z else 0)
        ≤ φ ^ T * w ^ x₀ / w ^ (x₀ + d) := by
  have hwtop : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  set V : ℕ → ℝ≥0∞ := directionPotential lower (x₀ + d) w
  set θ : ℝ≥0∞ := w ^ (x₀ + d)
  have hθ : θ ≠ 0 := pow_ne_zero _ hw0
  have hθtop : θ ≠ ⊤ := ENNReal.pow_ne_top hwtop
  have hsub : ∀ z,
      (if lower < z ∧ z < x₀ + d then
        iter (directionStop n lower (x₀ + d)) T x₀ z else 0)
      ≤ (if θ ≤ V z then
        iter (directionStop n lower (x₀ + d)) T x₀ z else 0) := by
    intro z
    by_cases hz : lower < z ∧ z < x₀ + d
    · have hzle : z ≤ x₀ + d := by omega
      have hpw : θ ≤ V z := by
        rw [show V z = w ^ z by
          simp [V, directionPotential, hz], show θ = w ^ (x₀ + d) by rfl]
        exact pow_le_pow_right_of_le_one' hw1 hzle
      simp [hz, hpw]
    · simp [hz]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans (markov_div
    (iter (directionStop n lower (x₀ + d)) T x₀) V θ hθ hθtop) ?_
  have hiter := expect_iter_le (directionStop n lower (x₀ + d)) V φ
    (directionStop_step n lower (x₀ + d) h3 htarget w φ hdir) T x₀
  have hVstart : V x₀ = w ^ x₀ := by
    simp [V, directionPotential, hlo, hd]
  exact ENNReal.div_le_div_right (by simpa [hVstart] using hiter) θ

/-- **Feller safety for the doubly stopped signed level.**  Freezing also at
the upper checkpoint does not invalidate the geometric conservation proof:
the potential is preserved exactly on both frozen regions and is controlled by
`odds_uniform` in the live band. -/
theorem directionStop_safety (n lower target bHi k T : ℕ) (h3 : 3 ≤ n)
    (hpop : lower + bHi + 2 = n) (hlower : 0 < lower) (hbHi : 0 < bHi)
    (hmaj : bHi ≤ lower) (htarget : target ≤ n) :
    ∑' z, (if z ≤ lower then
      iter (directionStop n lower target) T (lower + k) z else 0)
        ≤ ((bHi : ℝ≥0∞) / (lower : ℝ≥0∞)) ^ k := by
  set u : ℝ≥0∞ := (bHi : ℝ≥0∞) / (lower : ℝ≥0∞) with hu
  have hlower0 : (lower : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hlowerTop : (lower : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top lower
  have hu1 : u ≤ 1 := by
    rw [hu]
    calc
      (bHi : ℝ≥0∞) / (lower : ℝ≥0∞)
          ≤ (lower : ℝ≥0∞) / (lower : ℝ≥0∞) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hmaj) _
      _ = 1 := ENNReal.div_self hlower0 hlowerTop
  have hu0 : u ≠ 0 := by
    rw [hu]
    simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨by simp only [Nat.cast_eq_zero]; omega, hlowerTop⟩
  have hstep : ∀ x,
      expect (directionStop n lower target x) (fun z => u ^ z) ≤ u ^ x := by
    intro x
    by_cases hlo : x ≤ lower
    · rw [directionStop_of_boundary n lower target x (Or.inl hlo), expect_pure]
    · by_cases hhi : target ≤ x
      · rw [directionStop_of_boundary n lower target x (Or.inr hhi), expect_pure]
      · obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := ⟨x - 1, by omega⟩
        obtain ⟨b, hab⟩ : ∃ b, a + b + 2 = n := ⟨n - a - 2, by omega⟩
        have hbb : b ≤ bHi := by omega
        rw [directionStop_of_live n lower target (a + 1) (by omega) (by omega)]
        rw [triChain_apply hab h3, hu]
        exact triStep_conserve_on_region a b lower bHi (by omega) (by omega)
          hbb hlower hmaj
  have hruin := ruin_le_u (directionStop n lower target) id u hu1 hu0
    (fun z => u ^ z) (fun _ => rfl) hstep T lower k (lower + k) rfl
  simpa [hu] using hruin

namespace DirectionProgress

/-- **True direction-sensitive phase-1 progress bound.**

Start from signed level `lower+k` and stop at ruin `x ≤ lower` or success
`lower+k+d ≤ x`.  By time `T`, failure to have reached the upper checkpoint
is the disjoint union of lower ruin and remaining in the live band.  Feller's
term pays for ruin; the strict directional contraction pays for the live mass.

Since increasing `x` by `d` increases the fixed-population signed gap by `2d`,
the upper boundary is genuine gap progress.  The conclusion concerns this
guarded band-exit chain; transferring an upper hit to an exact-time statement
about the unfrozen chain requires a separate return-probability argument. -/
theorem phase1_direction_progress
    (n lower bHi k d T : ℕ) (h3 : 3 ≤ n)
    (hpop : lower + bHi + 2 = n) (hlower : 0 < lower) (hbHi : 0 < bHi)
    (hmaj : bHi ≤ lower) (hk : 0 < k) (hd : 0 < d)
    (htarget : lower + k + d ≤ n) (w φ : ℝ≥0∞)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hdir : ∀ (a b : ℕ) (hab : a + b + 2 = n),
      lower < a + 1 → a + 1 < lower + k + d →
      triStep (a + 1) (b + 1) (by omega) a
          + triStep (a + 1) (b + 1) (by omega) (a + 1) * w
          + triStep (a + 1) (b + 1) (by omega) (a + 2) * w ^ 2
        ≤ φ * w) :
    ∑' z, (if lower + k + d ≤ z then 0 else
      iter (directionStop n lower (lower + k + d)) T (lower + k) z)
        ≤ ((bHi : ℝ≥0∞) / (lower : ℝ≥0∞)) ^ k
          + φ ^ T * w ^ (lower + k) / w ^ (lower + k + d) := by
  calc
    ∑' z, (if lower + k + d ≤ z then 0 else
        iter (directionStop n lower (lower + k + d)) T (lower + k) z)
      = ∑' z, ((if z ≤ lower then
          iter (directionStop n lower (lower + k + d)) T (lower + k) z else 0)
        + (if lower < z ∧ z < lower + k + d then
          iter (directionStop n lower (lower + k + d)) T (lower + k) z else 0)) := by
          apply tsum_congr
          intro z
          by_cases hlo : z ≤ lower
          · have hnlo : ¬ lower < z := by omega
            by_cases hhi : lower + k + d ≤ z
            · exfalso
              omega
            · simp [hlo, hnlo, hhi]
          · have hlive : lower < z := by omega
            by_cases hhi : lower + k + d ≤ z
            · simp [hlo, hlive, hhi]
            · have hzhi : z < lower + k + d := by omega
              simp [hlo, hlive, hhi, hzhi]
    _ = (∑' z, (if z ≤ lower then
          iter (directionStop n lower (lower + k + d)) T (lower + k) z else 0))
        + ∑' z, (if lower < z ∧ z < lower + k + d then
          iter (directionStop n lower (lower + k + d)) T (lower + k) z else 0) :=
      ENNReal.tsum_add
    _ ≤ ((bHi : ℝ≥0∞) / (lower : ℝ≥0∞)) ^ k
          + φ ^ T * w ^ (lower + k) / w ^ (lower + k + d) := by
      apply add_le_add
      · exact directionStop_safety n lower (lower + k + d) bHi k T h3 hpop
          hlower hbHi hmaj htarget
      · exact directionStop_live_tail n lower (lower + k) d T h3 (by omega) hd
          htarget w φ hw1 hw0 hdir

/-- The direction-contraction premise is nonvacuous.  At `n=5`, in the live
band `2 < x < 4`, choosing `w=2/3` gives the exact contraction factor
`φ=19/20`, even though the down branch has positive mass. -/
theorem direction_contraction_five :
    ∀ (a b : ℕ) (hab : a + b + 2 = 5),
      2 < a + 1 → a + 1 < 4 →
      triStep (a + 1) (b + 1) (by omega) a
          + triStep (a + 1) (b + 1) (by omega) (a + 1) * ((2 : ℝ≥0∞) / 3)
          + triStep (a + 1) (b + 1) (by omega) (a + 2) * ((2 : ℝ≥0∞) / 3) ^ 2
        ≤ ((19 : ℝ≥0∞) / 20) * ((2 : ℝ≥0∞) / 3) := by
  intro a b hab hlo hhi
  have ha : a = 2 := by omega
  have hb : b = 1 := by omega
  subst a
  subst b
  rw [triStep_down, triStep_stay, triStep_up]
  norm_num [Nat.choose]
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow]

/-- A closed, numerically checked instance of `phase1_direction_progress`.
Starting at `x=3` in population `5`, the stopped process reaches `x≥4` by
time `T` except for the displayed Feller and directional-tail terms. -/
theorem phase1_direction_progress_five (T : ℕ) :
    ∑' z, (if 4 ≤ z then 0 else iter (directionStop 5 2 4) T 3 z)
      ≤ ((1 : ℝ≥0∞) / 2) ^ 1
        + ((19 : ℝ≥0∞) / 20) ^ T * ((2 : ℝ≥0∞) / 3) ^ 3
          / ((2 : ℝ≥0∞) / 3) ^ 4 := by
  simpa using phase1_direction_progress 5 2 1 1 1 T (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((2 : ℝ≥0∞) / 3) ((19 : ℝ≥0∞) / 20)
    (by
      calc
        (2 : ℝ≥0∞) / 3 ≤ (3 : ℝ≥0∞) / 3 :=
          ENNReal.div_le_div_right (by norm_num) _
        _ = 1 := ENNReal.div_self (by norm_num) (by norm_num))
    (by norm_num) direction_contraction_five

end DirectionProgress

end Tri
