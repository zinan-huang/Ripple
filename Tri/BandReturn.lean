/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.BandRung

/-!
# Returning from the upper boundary of a stopped band

`Tri.band_rung_transfer` compares the original chain with the chain stopped at
both band boundaries, but only for targets strictly inside the open band.  At
the lower boundary this restriction is harmless: stopping there preserves
failure.  At the upper boundary it excludes the phase-success event itself,
because the stopped chain remains successful while the original chain can
later move down again.

The missing comparison therefore has an additive return term.  If the upper
boundary is at least `k` states above a return threshold `returnLo`, then
`triChain_upper_return` applies `tri_feller` at `returnLo` and bounds the chance
of ever returning to `returnLo` or below by

    (bHi / returnLo) ^ k.

The theorem `band_rung_transfer_upper` uses exactly the hypotheses needed to
charge every discrepancy to that event.  The target must exclude the lower
freeze region, and every state outside the target must be at or below
`returnLo`.  Unlike `band_rung_transfer`, the target may include the upper
boundary.  In particular, the exact upper target `aHi ≤ x` is obtained by
writing `aHi = returnLo + 1` and taking `k = 1`; choosing a lower return
threshold gives the stronger bound associated with the larger gap.
-/

namespace Tri

open scoped ENNReal

variable {α : Type*}

/-- Freezing may turn a successful state into an absorbing success.  If the
original chain started from every such frozen success has terminal failure
mass at most `δ`, then frozen failure mass still dominates original failure
mass up to the single additive term `δ`, uniformly in the horizon. -/
theorem failure_le_failure_freeze_add {B A : α → Prop}
    [DecidablePred B] [DecidablePred A] {K : α → PMF α} {δ : ℝ≥0∞}
    (hreturn : ∀ s, B s → A s → ∀ T,
      (∑' z, if A z then 0 else iter K T s z) ≤ δ) :
    ∀ T s,
      (∑' z, if A z then 0 else iter K T s z) ≤
        (∑' z, if A z then 0 else iter (freeze B K) T s z) + δ := by
  let V : α → ℝ≥0∞ := fun z => if A z then 0 else 1
  have hmass (q : PMF α) :
      (∑' z, if A z then 0 else q z) = expect q V := by
    unfold expect V
    apply tsum_congr
    intro z
    by_cases hz : A z <;> simp [hz]
  have hprob (q : PMF α) :
      (∑' z, if A z then 0 else q z) ≤ 1 := by
    calc
      (∑' z, if A z then 0 else q z) ≤ ∑' z, q z :=
        ENNReal.tsum_le_tsum fun z => by
          by_cases hz : A z <;> simp [hz]
      _ = 1 := PMF.tsum_coe q
  intro T
  induction T with
  | zero =>
      intro s
      rw [hmass, hmass]
      change expect (PMF.pure s) V ≤ expect (PMF.pure s) V + δ
      exact le_add_right le_rfl
  | succ T ih =>
      intro s
      rw [hmass, hmass]
      by_cases hsB : B s
      · rw [iter_freeze_of_mem s hsB (T + 1), expect_pure]
        by_cases hsA : A s
        · have hr := hreturn s hsB hsA (T + 1)
          rw [hmass] at hr
          simpa [V, hsA] using hr
        · calc
            expect (iter K (T + 1) s) V =
                ∑' z, (if A z then 0 else iter K (T + 1) s z) :=
              (hmass _).symm
            _ ≤ 1 := hprob _
            _ ≤ V s + δ := by simp [V, hsA]
      · rw [iter_succ, iter_succ, freeze_of_not_mem s hsB,
          expect_bind, expect_bind]
        calc
          expect (K s) (fun a => expect (iter K T a) V) ≤
              expect (K s) (fun a =>
                expect (iter (freeze B K) T a) V + δ) := by
            have ihV (a : α) :
                expect (iter K T a) V ≤
                  expect (iter (freeze B K) T a) V + δ := by
              rw [← hmass, ← hmass]
              exact ih a
            unfold expect
            exact ENNReal.tsum_le_tsum fun a =>
              mul_le_mul_right (ihV a) _
          _ = expect (K s) (fun a =>
                expect (iter (freeze B K) T a) V) + δ := by
            unfold expect
            simp_rw [mul_add]
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe,
              one_mul]

/-- Starting at least `k` states above `returnLo`, the original Tri chain ever
returns to `returnLo` or below with probability at most
`(bHi / returnLo) ^ k`.  The starting state need not equal the lower edge of
the upper region; starting still higher can only improve the Feller bound. -/
theorem triChain_upper_return (n returnLo bHi k x : ℕ) (h3 : 3 ≤ n)
    (hpop : returnLo + bHi + 2 = n) (hreturnLo : 0 < returnLo)
    (hbHi : 0 < bHi) (hmaj : bHi ≤ returnLo)
    (hx : returnLo + k ≤ x) :
    ⨆ T : ℕ, hitProb (fun z => z ≤ returnLo) (triChain n) T x ≤
      ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k := by
  obtain ⟨d, rfl⟩ : ∃ d, x = returnLo + d :=
    ⟨x - returnLo, by omega⟩
  have hkd : k ≤ d := by omega
  have hne : (returnLo : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have htop : (returnLo : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top returnLo
  have hbase : (bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞) ≤ 1 := by
    calc
      (bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞) ≤
          (returnLo : ℝ≥0∞) / (returnLo : ℝ≥0∞) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hmaj) _
      _ = 1 := ENNReal.div_self hne htop
  calc
    (⨆ T : ℕ, hitProb (fun z => z ≤ returnLo) (triChain n) T
        (returnLo + d)) ≤
        ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ d :=
      tri_feller n returnLo bHi d h3 hpop hreturnLo hbHi hmaj
    _ ≤ ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k :=
      pow_le_pow_right_of_le_one' hbase hkd

/-- If failure of `A` can occur only at `returnLo` or below, then every
terminal failure starting `k` states above `returnLo` is covered by the
unbounded return event and hence by `triChain_upper_return`. -/
theorem triChain_upper_target_failure (n returnLo bHi k x T : ℕ)
    (h3 : 3 ≤ n) (hpop : returnLo + bHi + 2 = n)
    (hreturnLo : 0 < returnLo) (hbHi : 0 < bHi)
    (hmaj : bHi ≤ returnLo) (hx : returnLo + k ≤ x)
    (A : ℕ → Prop) [DecidablePred A]
    (hfailure : ∀ z, ¬ A z → z ≤ returnLo) :
    (∑' z, if A z then 0 else iter (triChain n) T x z) ≤
      ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k := by
  calc
    (∑' z, if A z then 0 else iter (triChain n) T x z) ≤
        ∑' z, if returnLo < z then 0 else iter (triChain n) T x z := by
      refine ENNReal.tsum_le_tsum fun z => ?_
      by_cases hz : A z
      · simp [hz]
      · have hzLo := hfailure z hz
        simp [hz, Nat.not_lt.mpr hzLo]
    _ ≤ ∑' z, if returnLo < z then 0 else
          iter (freeze (fun y => y ≤ returnLo) (triChain n)) T x z := by
      exact failure_le_failure_freeze (B := fun y : ℕ => y ≤ returnLo)
        (A := fun y : ℕ => returnLo < y) (by omega) T x
    _ = hitProb (fun y => y ≤ returnLo) (triChain n) T x := by
      unfold hitProb expect ind
      apply tsum_congr
      intro z
      by_cases hz : z ≤ returnLo
      · simp [hz, Nat.not_lt.mpr hz]
      · simp [hz, Nat.lt_of_not_ge hz]
    _ ≤ ⨆ t : ℕ,
          hitProb (fun y => y ≤ returnLo) (triChain n) t x :=
      le_iSup (fun t : ℕ =>
        hitProb (fun y => y ≤ returnLo) (triChain n) t x) T
    _ ≤ ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k :=
      triChain_upper_return n returnLo bHi k x h3 hpop hreturnLo hbHi
        hmaj hx

/-- Transfer from the stopped band-counting chain to the original chain for a
target that may contain the upper boundary.  Successes of `A` must exclude the
lower frozen region, while failures of `A` must lie below `returnLo`.  If the
upper boundary is at least `k` above that threshold, the only discrepancy not
already charged by frozen failure mass costs at most
`(bHi / returnLo) ^ k`.  This is the upper-boundary case excluded from
`band_rung_transfer`. -/
theorem band_rung_transfer_upper
    (n bandLo aHi returnLo bHi k T x₀ c₀ : ℕ) (h3 : 3 ≤ n)
    (hpop : returnLo + bHi + 2 = n) (hreturnLo : 0 < returnLo)
    (hbHi : 0 < bHi) (hmaj : bHi ≤ returnLo)
    (hgap : returnLo + k ≤ aHi)
    (A : ℕ → Prop) [DecidablePred A]
    (hlower : ∀ x, A x → bandLo < x)
    (hfailure : ∀ x, ¬ A x → x ≤ returnLo) :
    (∑' x, if A x then 0 else iter (triChain n) T x₀ x) ≤
      (∑' s, if A s.1 then 0 else
        iter (bandCount n bandLo aHi) T (x₀, c₀) s) +
          ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k := by
  let B : ℕ → Prop := fun x => x ≤ bandLo ∨ aHi ≤ x
  let V : ℕ → ℝ≥0∞ := fun x => if A x then 0 else 1
  have hcompare :
      (∑' x, if A x then 0 else iter (triChain n) T x₀ x) ≤
        (∑' x, if A x then 0 else
          iter (freeze B (triChain n)) T x₀ x) +
            ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k := by
    apply failure_le_failure_freeze_add
    intro x hxB hxA U
    rcases hxB with hxLo | hxHi
    · exact False.elim ((Nat.not_lt_of_ge hxLo) (hlower x hxA))
    · exact triChain_upper_target_failure n returnLo bHi k x U h3 hpop
        hreturnLo hbHi hmaj (hgap.trans hxHi) A hfailure
  have hmap :
      (iter (bandCount n bandLo aHi) T (x₀, c₀)).map Prod.fst =
        iter (bandChain n bandLo aHi) T x₀ :=
    iter_map_of_step_map _ _ _ (bandCount_map_fst n bandLo aHi) T _
  have hmass_nat (q : PMF ℕ) :
      (∑' z, if A z then 0 else q z) = expect q V := by
    unfold expect V
    apply tsum_congr
    intro z
    by_cases hz : A z <;> simp [hz]
  have hmass_pair (q : PMF (ℕ × ℕ)) :
      (∑' z, if A z.1 then 0 else q z) = expect q (fun z => V z.1) := by
    unfold expect V
    apply tsum_congr
    intro z
    by_cases hz : A z.1 <;> simp [hz]
  have hprojection :
      (∑' x, if A x then 0 else iter (bandChain n bandLo aHi) T x₀ x) =
        ∑' s, if A s.1 then 0 else
          iter (bandCount n bandLo aHi) T (x₀, c₀) s := by
    calc
      (∑' x, if A x then 0 else
          iter (bandChain n bandLo aHi) T x₀ x) =
          expect (iter (bandChain n bandLo aHi) T x₀) V := hmass_nat _
      _ = expect ((iter (bandCount n bandLo aHi) T
          (x₀, c₀)).map Prod.fst) V := by rw [hmap]
      _ = expect (iter (bandCount n bandLo aHi) T (x₀, c₀))
          (fun z => V z.1) := expect_map _ _ _
      _ = ∑' s, if A s.1 then 0 else
          iter (bandCount n bandLo aHi) T (x₀, c₀) s :=
        (hmass_pair _).symm
  rw [show freeze B (triChain n) = bandChain n bandLo aHi by
    rfl] at hcompare
  exact hcompare.trans_eq (congrArg
    (fun q => q + ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k)
    hprojection)

/-- The exact upper-boundary instance of `band_rung_transfer_upper`.  With the
band stopped at `returnLo + 1`, its upper success event is
`returnLo + 1 ≤ x`; the original chain pays one Feller ratio for possibly
returning below that boundary after first reaching it. -/
theorem band_rung_transfer_upper_boundary
    (n bandLo returnLo bHi T x₀ c₀ : ℕ) (h3 : 3 ≤ n)
    (hpop : returnLo + bHi + 2 = n) (hreturnLo : 0 < returnLo)
    (hbHi : 0 < bHi) (hmaj : bHi ≤ returnLo)
    (hlower : bandLo < returnLo + 1) :
    (∑' x, if returnLo + 1 ≤ x then 0 else
      iter (triChain n) T x₀ x) ≤
      (∑' s, if returnLo + 1 ≤ s.1 then 0 else
        iter (bandCount n bandLo (returnLo + 1)) T (x₀, c₀) s) +
          (bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞) := by
  simpa using band_rung_transfer_upper n bandLo (returnLo + 1) returnLo
    bHi 1 T x₀ c₀ h3 hpop hreturnLo hbHi hmaj le_rfl
    (fun x => returnLo + 1 ≤ x) (by omega) (by omega)

/-- A stopped-band reachability estimate for an upper-boundary target transfers
to the original Tri chain with the Feller return term added to its error. -/
theorem Reaches.of_bandCount_upper
    (n bandLo aHi returnLo bHi k T x₀ c₀ : ℕ) (h3 : 3 ≤ n)
    (hpop : returnLo + bHi + 2 = n) (hreturnLo : 0 < returnLo)
    (hbHi : 0 < bHi) (hmaj : bHi ≤ returnLo)
    (hgap : returnLo + k ≤ aHi)
    (A : ℕ → Prop) [DecidablePred A] (ε : ℝ≥0∞)
    (hlower : ∀ x, A x → bandLo < x)
    (hfailure : ∀ x, ¬ A x → x ≤ returnLo)
    (hband : Reaches (bandCount n bandLo aHi) T
      (fun s => s = (x₀, c₀)) (fun s => A s.1) ε) :
    Reaches (triChain n) T (fun x => x = x₀) A
      (ε + ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k) := by
  intro x hx
  subst x
  exact (band_rung_transfer_upper n bandLo aHi returnLo bHi k T x₀ c₀
    h3 hpop hreturnLo hbHi hmaj hgap A hlower hfailure).trans
      (add_le_add (hband (x₀, c₀) rfl) le_rfl)

#print axioms failure_le_failure_freeze_add
#print axioms triChain_upper_return
#print axioms triChain_upper_target_failure
#print axioms band_rung_transfer_upper
#print axioms band_rung_transfer_upper_boundary
#print axioms Reaches.of_bandCount_upper

end Tri
