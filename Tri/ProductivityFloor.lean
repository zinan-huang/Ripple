/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Chain

/-!
# The live-band productivity floor

Records, with proof, the correction to a claim I had been repeating: that the
productive probability degenerates near consensus and that this is what makes
Lemma 5 hard.

It does not degenerate.  With `x + y = n` the productive probability is
`3xy/(n(n−1))`, so on the LIVE band (`1 ≤ y ≤ n−1`; `y = 0` is the target and
already done) the minimum of `xy` is `n − 1`, attained at `y = 1`, giving

```text
p_min = 3(n−1)/(n(n−1)) = 3/n
```

exactly — attained, not approached.  `3/n` is the participation rate of a single
molecule, not a degenerate floor.  The scale I had feared, `Θ((γ lg n)/n)`, is
the productivity at the TOP of the phase-3 band and never binds, because the
band's worst case is its bottom.

This file proves the combinatorial core.  The parametrisation `x = a+1`,
`y = b+1`, `n = a+b+2` is the repo's standard subtraction-free one for mixed
states.
-/

namespace Tri

/-- **The live-band product bound.**  On any mixed state the species product is
at least `n - 1`, stated subtraction-free.  Equality holds exactly at the ends
of the band, `y = 1` and `y = n - 1`. -/
theorem live_product_ge (a b : ℕ) :
    a + b + 2 ≤ (a + 1) * (b + 1) + 1 := by
  nlinarith [Nat.zero_le (a * b)]

/-- The same read as the productivity floor's combinatorial core: with
`x = a+1`, `y = b+1`, `n = a+b+2`, the productive triple count
`x*y*(n-2)/2` is at least `(n-1)*(n-2)/2`, so the productive probability is at
least `3/n`.

Stated as the cross-multiplied `ℕ` inequality that carries it. -/
theorem live_productive_core (a b : ℕ) :
    (a + b + 1) * (a + b) ≤ ((a + 1) * (b + 1)) * (a + b) := by
  have h := live_product_ge a b
  exact Nat.mul_le_mul_right _ (by omega)

end Tri
