/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma15Prefix

/-!
# Lemma 15's glue: the recentring identity and the 2/3 + 1/3 split

The two halves of Lemma 15 are proved (`Lemma15Window` for the maximal windowed
bound, `Lemma15Prefix` for the fixed-time prefix bound, `Lemma15Split` for the
engine that combines them). What was missing is the DETERMINISTIC glue relating
the window's excess against the GLOBAL red fraction to its excess against the
prefix endpoint's CONDITIONAL fraction. That is this file.

## The identity

With `w` red balls revealed in the window, `k` the window length, `t` the total
remaining, `q = (r₀,b₀)` the prefix endpoint and `z = (r,b)` the window
endpoint:

```text
w − k·c  =  t · urnM cq z  −  k · urnM c q
```

Everything is an additive witness — `r + w = r₀`, `k + t = ν₂` — so no ℕ
subtraction enters, and the real subtractions are only in the ℝ-valued
observables where they are harmless.

## The split

The window target is `2Δ/3` against the conditional centre, and the prefix must
hold its drift to `Δ/(3s)`; since `k ≤ s`, the prefix contributes at most `Δ/3`
and the two add to `Δ`.

## One load-bearing warning, recorded here so it is not lost

The `Bad q` handed to `recentred_split` must be the **global-centred** window
event anchored at `q`. `UrnWindowBad` centred at `q`'s own conditional fraction
is the *dominating* event used to discharge `hgood` — it is not the conclusion.
Passing `UrnWindowBad` itself as the final `Bad q` would prove a
conditional-centre statement, which is true but is **not** paper Lemma 15.

The identity below is exactly what converts one into the other, which is why it
is the piece that had to exist.
-/

namespace Tri
open scoped ENNReal


/-- **The exact recentring identity.**  The window's red count measured against
the GLOBAL fraction `c` decomposes into its count against the prefix endpoint's
CONDITIONAL fraction, plus the prefix's own drift.

`w` = red revealed in the window, `k` = window length, `t` = total remaining,
`q = (r₀,b₀)` the prefix endpoint, `z = (r,b)` the window endpoint. -/
theorem urn_recentre_identity
    (c : ℝ) (r w k t r₀ b₀ b : ℕ)
    (hw : r + w = r₀) (hk : k + t = r₀ + b₀) (ht : t = r + b)
    (hν2 : (r₀ : ℝ) + (b₀ : ℝ) ≠ 0) (htpos : (t : ℝ) ≠ 0) :
    (w : ℝ) - (k : ℝ) * c
      = (t : ℝ) * urnM ((r₀ : ℝ) / ((r₀ : ℝ) + (b₀ : ℝ))) (r, b)
        - (k : ℝ) * urnM c (r₀, b₀) := by
  unfold urnM
  simp only
  have hrb : (r : ℝ) + (b : ℝ) = (t : ℝ) := by
    rw [ht]; push_cast; ring
  rw [hrb]
  have hdiv : (t : ℝ) * ((r : ℝ) / (t : ℝ)) = (r : ℝ) := by
    field_simp
  have hq : ((r₀ : ℝ) + (b₀ : ℝ)) * ((r₀ : ℝ) / ((r₀ : ℝ) + (b₀ : ℝ)))
      = (r₀ : ℝ) := by field_simp
  have hkt : (k : ℝ) + (t : ℝ) = (r₀ : ℝ) + (b₀ : ℝ) := by exact_mod_cast hk
  have hrw : (r : ℝ) + (w : ℝ) = (r₀ : ℝ) := by exact_mod_cast hw
  set cq : ℝ := (r₀ : ℝ) / ((r₀ : ℝ) + (b₀ : ℝ)) with hcq
  have hnu2cq : ((r₀ : ℝ) + (b₀ : ℝ)) * cq = (r₀ : ℝ) := hq
  have hexp : (t : ℝ) * (cq - (r : ℝ) / (t : ℝ)) = (t : ℝ) * cq - (r : ℝ) := by
    rw [mul_sub, hdiv]
  rw [hexp]
  have : (t : ℝ) * cq = ((r₀ : ℝ) + (b₀ : ℝ)) * cq - (k : ℝ) * cq := by
    have : (t : ℝ) = ((r₀ : ℝ) + (b₀ : ℝ)) - (k : ℝ) := by linarith
    rw [this]; ring
  rw [this, hnu2cq]
  linarith

/-- **The 2/3 + 1/3 split**, deterministic form.

If the global-centred excess has reached `Δ` and the prefix drift is held to
`Δ/(3s)`, then the conditional-centred excess has reached `2Δ/3` — which is what
the windowed application is asked to rule out.

The `k ≤ s` hypothesis is what makes the prefix's contribution at most `Δ/3`
however long the window runs. -/
theorem urn_split_two_thirds (Δ c cq wr : ℝ) (k s : ℕ) (hs : 0 < s)
    (hks : (k : ℝ) ≤ (s : ℝ)) (hΔ0 : 0 ≤ Δ)
    (hΔ : Δ ≤ wr - (k : ℝ) * c)
    (hpre : cq - c ≤ Δ / (3 * (s : ℝ))) :
    2 * Δ / 3 ≤ wr - (k : ℝ) * cq := by
  have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hdrift : (k : ℝ) * (cq - c) ≤ Δ / 3 := by
    by_cases h : cq - c ≤ 0
    · nlinarith
    · push Not at h
      have : (k : ℝ) * (cq - c) ≤ (s : ℝ) * (Δ / (3 * (s : ℝ))) := by
        nlinarith
      calc (k : ℝ) * (cq - c) ≤ (s : ℝ) * (Δ / (3 * (s : ℝ))) := this
        _ = Δ / 3 := by field_simp
  nlinarith [hΔ, hdrift]

end Tri

#print axioms Tri.urn_recentre_identity
#print axioms Tri.urn_split_two_thirds
