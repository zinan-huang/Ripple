/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Relative Change Lemma (Lemma 1)

Lemma 1 from Angluin-Aspnes-Eisenstat 2008, Section 4.3:

For positive reals `f` with `f + Δf > 0`:

  Δ(1/f) = 1/(f+Δf) - 1/f = -Δf / (f(f+Δf))

and the relative change satisfies:

  Δ(1/f) / (1/f) = -Δf / (f+Δf) = -Δf/f · 1/(1 + Δf/f)

When `|Δf/f|` is small, this is approximately `-Δf/f`.

The lemmas are stated and proved once, in `Ripple.PopulationProtocol.PopProtoCommon.Convergence.RelativeChange`
(`Ripple.PopulationProtocol.PopProtoCommon.inv_change`, `inv_relative_change`, ...); this module imports them for PopProto.
-/

import Mathlib.Tactic
import Ripple.PopulationProtocol.PopProtoCommon.Convergence.RelativeChange
