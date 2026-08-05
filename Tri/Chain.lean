/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Drift
import Tri.Freeze

/-!
# The Tri CRN as a chain, and Feller's Lemma 1 for it

`Tri.triStep` takes the two species counts separately. With the population `n`
fixed the second is determined by the first, so the CRN is a chain on the
`X`-count alone: `Tri.triChain`.

The payoff is `Tri.tri_feller` — the paper's Lemma 1 **instantiated for this
CRN**. Its hypotheses mention only arithmetic: the population, the region
bounds, and the majority condition. No potential, no expectation, no freeze set
appears in its statement, so nothing is assumed that `Tri` has not been shown to
satisfy.

## On natural subtraction

`triChain` uses `n - x` inside its *definition*, guarded by `x ≤ n`. That is
permitted; the house rule bans truncated subtraction from *statements*, because
it silently changes meaning at the degenerate populations the endgame visits.
`triChain_apply` is what enforces the rule downstream: it rewrites the chain in
terms of `a` and `b` with `a + b + 2 = n`, so no later statement mentions `n - x`.

## Main results

* `triChain` — the CRN as a chain on the `X`-count.
* `triChain_apply` — the subtraction-free rewriting rule.
* `tri_feller` — **Lemma 1 for the Tri CRN**: from `aLo + k` copies of `X`, the
  probability that the `X`-count *ever* falls to `aLo` or below is at most
  `(bHi/aLo) ^ k`.

Reference: A. Condon, M. Hajiaghayi, D. Kirkpatrick, J. Mañuch,
*Approximate Majority Analyses using Tri-molecular Chemical Reaction Networks*,
Lemma 1 and Section 3.1.
-/

namespace Tri

open scoped ENNReal

/-- The CRN as a chain on the `X`-count alone, with the population `n` fixed.
Outside the physical range the chain is inert. -/
noncomputable def triChain (n : ℕ) : ℕ → PMF ℕ := fun x =>
  if h : 3 ≤ n ∧ x ≤ n then triStep x (n - x) (by omega) else PMF.pure x

/-- The subtraction-free rewriting rule: on the physical range the chain is
`triStep` at the two species counts. Every downstream statement is phrased with
`a` and `b`, never with `n - x`. -/
theorem triChain_apply {n a b : ℕ} (hn : a + b + 2 = n) (h3 : 3 ≤ n) :
    triChain n (a + 1) = triStep (a + 1) (b + 1) (by omega) := by
  unfold triChain
  rw [dif_pos ⟨h3, by omega⟩]
  congr 1
  omega

/-- At `X`-consensus the chain is absorbed. -/
theorem triChain_consensus {n : ℕ} (h3 : 3 ≤ n) : triChain n n = PMF.pure n := by
  unfold triChain
  rw [dif_pos ⟨h3, le_rfl⟩]
  simp only [Nat.sub_self]
  exact triStep_consensus_X n (by omega)

/-- **Feller's Lemma 1 for the Tri CRN.**

Fix a population `n` and a region of the state space on which `X` is in the
majority: the `X`-count is at least `aLo + 1` and hence the `Y`-count is at most
`bHi + 1`, where `aLo + bHi + 2 = n`. Starting from `aLo + k` copies of `X`, the
probability that the `X`-count **ever** falls to `aLo` or below is at most

    (bHi / aLo) ^ k.

Every hypothesis is arithmetic — the population identity, the majority condition
`bHi ≤ aLo`, and positivity. No potential, expectation, or freeze set appears,
so the statement assumes nothing about the chain that has not been proved.

The bound is exactly the paper's `((1-p)/p)^b` with `p` the conditional
probability of the majority-increasing reaction: by `Tri.odds_cross_mul` the odds
ratio is `(x-1)/(y-1)`, so `(1-p)/p` is `(y-1)/(x-1)`, uniformly bounded on the
region by `bHi/aLo`.

No positivity hypothesis on `k` is needed: at `k = 0` the chain starts already in
the bad set, so the hitting probability is `1` and the bound `u^0 = 1` holds. -/
theorem tri_feller (n aLo bHi k : ℕ) (h3 : 3 ≤ n) (hpop : aLo + bHi + 2 = n)
    (haLo : 0 < aLo) (hbHi : 0 < bHi) (hmaj : bHi ≤ aLo) :
    ⨆ T : ℕ, hitProb (fun z => z ≤ aLo) (triChain n) T (aLo + k)
      ≤ ((bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)) ^ k := by
  set u : ℝ≥0∞ := (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞) with hu
  have hane : (aLo : ℝ≥0∞) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hatop : (aLo : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top aLo
  have hu1 : u ≤ 1 := by
    rw [hu]
    calc (bHi : ℝ≥0∞) / (aLo : ℝ≥0∞)
        ≤ (aLo : ℝ≥0∞) / (aLo : ℝ≥0∞) := ENNReal.div_le_div_right (Nat.cast_le.mpr hmaj) _
      _ = 1 := ENNReal.div_self hane hatop
  have hu0 : u ≠ 0 := by
    rw [hu]
    simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
    exact ⟨by simp only [Nat.cast_eq_zero]; omega, hatop⟩
  -- conservation off the bad set, from the region drift bound
  have hoff : ∀ s : ℕ, ¬ (s ≤ aLo) → expect (triChain n s) (fun z => u ^ z) ≤ u ^ s := by
    intro s hs
    rw [Nat.not_le] at hs
    -- `s = a + 1` with `aLo ≤ a`
    obtain ⟨a, rfl⟩ : ∃ a, s = a + 1 := ⟨s - 1, by omega⟩
    have haa : aLo ≤ a := by omega
    by_cases hle : a + 2 ≤ n
    · -- interior: at least one `Y` remains, so the region drift bound applies
      obtain ⟨b, hb⟩ : ∃ b, a + b + 2 = n := ⟨n - a - 2, by omega⟩
      have hbb : b ≤ bHi := by omega
      rw [triChain_apply hb h3]
      exact triStep_conserve_on_region a b aLo bHi (by omega) haa hbb haLo hmaj
    · by_cases hcons : a + 1 = n
      · -- `X`-consensus: no `Y` remains, the chain is absorbed
        subst hcons
        rw [triChain_consensus h3, expect_pure]
      · -- outside the physical range the chain is inert
        unfold triChain
        rw [dif_neg (by omega), expect_pure]
  refine feller_ruin_u (K := triChain n) id aLo k u hu1 hu0 (fun z => u ^ z)
    (fun _ => rfl) (freeze_conserve hoff) (aLo + k) rfl

end Tri
