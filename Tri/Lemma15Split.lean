/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Compose
import Tri.Lemma15Window

/-!
# Lemma 15, part P3 — the recentred bind-split

Paper Lemma 15 applies paper Lemma 14 **twice**, and the two applications
cannot be fused into one.  The quantitative reason is that a single budget
telescope spanning the whole run optimises to an exponent
`−Θ(γ lg n · s/(s'+s))`, which VANISHES when the window `s` is short relative
to the prefix `s'`.  Recentring at the START of the window is genuine content,
not bookkeeping.

## Why `Reaches.comp` is not enough

`Reaches.comp` (`Tri/Compose.lean`) already splits an iterate at a
deterministic time and charges the two stages separately.  But its second
stage's target predicate is FIXED.  Here the continuation's bad set is
recentred at the random prefix endpoint — the window measures deviation from
the red fraction *as it stands when the window opens*, which is a different
number for each prefix endpoint.  So the bad set is a RELATION `Bad : α → α →
Prop`, and the split has to carry the endpoint through.

There is no conditioning anywhere in this framework, and none is needed.  The
mechanism is purely `iter_add` plus a tsum split:

```text
iter K (a+b) q₀ = (iter K a q₀).bind (iter K b)
  ↓  split the prefix-endpoint tsum on Good / ¬Good
  ¬Good  →  charge the whole endpoint mass to εpre
   Good  →  apply the pointwise continuation bound, recentred at that endpoint
  ↓  tsum linearity
εpre + ε
```

The `Good` branch is where `urn_window_ville` enters, and it enters
POINTWISE — once per good endpoint, each at its own centre.  That is exactly
why the two Lemma 14 applications stay separate.
-/

open scoped ENNReal

namespace Tri

variable {α : Type*}

/-- The continuation quantity is bounded by `1`, uniformly: `hitProb` is the
mass of an indicator under a probability measure. -/
theorem hitProb_le_one (B : α → Prop) [DecidablePred B] (K : α → PMF α)
    (T : ℕ) (s₀ : α) : hitProb B K T s₀ ≤ 1 := by
  unfold hitProb expect ind
  calc ∑' z, iter (freeze B K) T s₀ z * (if B z then 1 else 0)
      ≤ ∑' z, iter (freeze B K) T s₀ z := by
        refine ENNReal.tsum_le_tsum fun z => ?_
        by_cases hz : B z <;> simp [hz]
    _ = 1 := PMF.tsum_coe _

/-- **P3, the engine.**  Split an iterate at a deterministic time `a`, charge
the prefix endpoints outside `Good` wholesale, and on the good endpoints apply
a continuation bound that may be RECENTRED at each endpoint.

The conclusion is a bound on the mass of the *pair* (prefix endpoint, window
excursion) — it cannot be stated on the final state alone, because `Bad`
depends on the endpoint.  That is the honest shape of a recentred estimate,
and it is what Lemma 15 consumes. -/
theorem recentred_split
    (K : α → PMF α) (a b : ℕ) (q₀ : α)
    (Good : α → Prop) [DecidablePred Good]
    (Bad : α → α → Prop) [∀ q, DecidablePred (Bad q)]
    (εpre ε : ℝ≥0∞)
    (hpre : (∑' q, if Good q then 0 else iter K a q₀ q) ≤ εpre)
    (hgood : ∀ q, Good q → hitProb (Bad q) K b q ≤ ε) :
    ∑' q, iter K a q₀ q * hitProb (Bad q) K b q ≤ εpre + ε := by
  have hgoodsum :
      ∑' q, (if Good q then iter K a q₀ q * ε else 0) ≤ ε := by
    calc ∑' q, (if Good q then iter K a q₀ q * ε else 0)
        ≤ ∑' q, iter K a q₀ q * ε :=
          ENNReal.tsum_le_tsum fun q => by split_ifs <;> simp
      _ = (∑' q, iter K a q₀ q) * ε := ENNReal.tsum_mul_right
      _ = ε := by rw [PMF.tsum_coe, one_mul]
  calc ∑' q, iter K a q₀ q * hitProb (Bad q) K b q
      ≤ ∑' q, ((if Good q then 0 else iter K a q₀ q)
                + (if Good q then iter K a q₀ q * ε else 0)) := by
        refine ENNReal.tsum_le_tsum fun q => ?_
        by_cases hq : Good q
        · simp only [if_pos hq, zero_add]
          exact mul_le_mul_right (hgood q hq) _
        · simp only [if_neg hq, add_zero]
          calc iter K a q₀ q * hitProb (Bad q) K b q ≤ iter K a q₀ q * 1 :=
                mul_le_mul_right (hitProb_le_one _ _ _ _) _
            _ = iter K a q₀ q := mul_one _
    _ = (∑' q, (if Good q then 0 else iter K a q₀ q))
        + ∑' q, (if Good q then iter K a q₀ q * ε else 0) := ENNReal.tsum_add
    _ ≤ εpre + ε := add_le_add hpre hgoodsum

/-- The same bound with the prefix failure supplied in `Reaches` form, which
is how the first Lemma 14 application will arrive: the prefix estimate says
the endpoint lands in `Good` except with mass `εpre`. -/
theorem recentred_split_of_reaches
    (K : α → PMF α) (a b : ℕ) (q₀ : α)
    (P Good : α → Prop) [DecidablePred Good]
    (Bad : α → α → Prop) [∀ q, DecidablePred (Bad q)]
    (εpre ε : ℝ≥0∞)
    (hP : P q₀)
    (hpre : Reaches K a P Good εpre)
    (hgood : ∀ q, Good q → hitProb (Bad q) K b q ≤ ε) :
    ∑' q, iter K a q₀ q * hitProb (Bad q) K b q ≤ εpre + ε :=
  recentred_split K a b q₀ Good Bad εpre ε (hpre q₀ hP) hgood

/-- **P3 specialised to the urn.**  The prefix runs `a` reveals from the
initial pool; each good endpoint `q` opens a window whose bad set is
`UrnWindowBad` recentred at `q`'s own red fraction, with the window's end
budget `u`.

`ε` is supplied uniformly by `urn_window_ville`, whose bound depends on the
endpoint only through `urnG (centre q) lam q` — and at the recentred start
that potential collapses to the pure variance term, which is the SAME for
every endpoint with the same remaining total.  That collapse is what makes a
single uniform `ε` correct here rather than an endpoint-dependent one. -/
theorem urn_recentred_split
    (a b : ℕ) (q₀ : α) (δ lam : ℝ) (u : ℕ)
    (K : α → PMF α)
    (Good : α → Prop) [DecidablePred Good]
    (centre : α → ℝ) (embed : α → ℕ × ℕ)
    (εpre ε : ℝ≥0∞)
    (hpre : (∑' q, if Good q then 0 else iter K a q₀ q) ≤ εpre)
    (hgood : ∀ q, Good q →
      hitProb (fun z => UrnWindowBad (centre q) δ lam u (embed z)) K b q ≤ ε) :
    ∑' q, iter K a q₀ q
        * hitProb (fun z => UrnWindowBad (centre q) δ lam u (embed z)) K b q
      ≤ εpre + ε :=
  recentred_split K a b q₀ Good
    (fun q z => UrnWindowBad (centre q) δ lam u (embed z)) εpre ε hpre hgood

end Tri

#print axioms Tri.hitProb_le_one
#print axioms Tri.recentred_split
#print axioms Tri.recentred_split_of_reaches
#print axioms Tri.urn_recentred_split
