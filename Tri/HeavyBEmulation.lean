/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBKernel
import Tri.Emulation

/-!
# Heavy-B does NOT lump onto Double-B, and the reason is a time change

`Tri/Emulation.lean` supplies exact-intertwining transport: if
`(K₁ s).map φ = K₂ (φ s)` then every `Reaches`/`hitProb`/expectation bound
transfers with the same horizon and the same constant. It was built after the
paper's abstract corrected my framing of Theorem 2 ("three bimolecular
protocols … **emulate** the tri-molecular protocol"), on the expectation that
"emulate" would mean exactly that.

**It does not**, and this file records the obstruction so that no later pass —
mine or a dispatched one — tries to route the Heavy-B clause through
`Intertwines`.

## The natural lumping, and how far it gets

A Heavy-B blank is worth two units, so the natural map replaces it by two
Double-B blanks:

```text
heavyToDouble (x, y, b) = (x, y, 2b)
```

This is not a bad guess. It carries `HeavyInv` to `DoubleInv` exactly, it sends
`heavyLevel` to half of `doubleLevel`, and — the encouraging part — the
**creation commutes on the nose**: Heavy's `X+Y → B` produces `(x−1, y−1, b+1)`,
whose image is `(x−1, y−1, 2b+2)`, and that is precisely Double's
`X+Y → B+B` applied to the image.

## Where it breaks

At a resolution. One Heavy `X+B → 3X` raises `heavyLevel` by one, hence raises
the image's `doubleLevel` by **two** — while one Double `X+B → 2X` raises
`doubleLevel` by **one**. So a single Heavy resolution is *two* Double
resolutions: the correspondence is a TIME CHANGE, not a one-step Markov
homomorphism, and `Intertwines heavyToDouble _ _` is false.

A second, independent obstruction: interactions draw a pair of entities, and
the two protocols do not have the same number of entities. Heavy-B has
`x + y + b`, its image has `x + y + 2b`. Whenever `b > 0` the denominators
differ, so even the creation — which maps correctly on *states* — fires with a
different *probability*.

## What this settles

* The Heavy-B clause of Theorem 2 cannot be obtained by transport along this
  map, and no reweighting fixes it: a time change is not a leak term.
* It also retroactively justifies the Double-B development having rebuilt the
  two-parameter potential engine directly rather than transporting it. That was
  the right call, not wasted work.
* `Tri/Emulation.lean` remains correct and reusable — it is simply not the tool
  for this clause. Its hypothesis is exact, and exactness is what fails here.
-/

namespace Tri

open scoped ENNReal

/-- The natural lumping: one heavy blank becomes two light ones. -/
def heavyToDouble (s : BiCfg) : BiCfg := ⟨s.x, s.y, 2 * s.b⟩

/-- The lumping carries the Heavy-B population invariant to the Double-B one.
This much works perfectly. -/
theorem heavyToDouble_doubleInv {n : ℕ} {s : BiCfg}
    (h : BiCfg.HeavyInv n s) : BiCfg.DoubleInv n (heavyToDouble s) := by
  obtain ⟨x, y, b⟩ := s
  simp only [BiCfg.HeavyInv] at h
  simp only [BiCfg.DoubleInv, heavyToDouble]
  omega

/-- And it doubles the level, as it must. -/
theorem doubleLevel_heavyToDouble (s : BiCfg) :
    BiCfg.doubleLevel (heavyToDouble s) = 2 * BiCfg.heavyLevel s := by
  obtain ⟨x, y, b⟩ := s
  simp only [BiCfg.doubleLevel, BiCfg.heavyLevel, heavyToDouble]
  omega

/-- **The creation commutes on the nose.**  Heavy's `X+Y → B` and Double's
`X+Y → B+B` agree under the lumping.  This is the part that made the map look
promising. -/
theorem heavyToDouble_creation (s : BiCfg) :
    heavyToDouble (PairComp.heavyNext s PairComp.xy)
      = PairComp.next (heavyToDouble s) PairComp.xy := by
  obtain ⟨x, y, b⟩ := s
  simp only [heavyToDouble, PairComp.heavyNext, PairComp.next]
  congr 1

/-- **The obstruction.**  One Heavy `X`-resolution moves the image's Double
level by TWO, whereas one Double `X`-resolution moves it by one.

So the correspondence is a time change on resolutions and cannot be a one-step
homomorphism. -/
theorem heavy_resolution_is_two_double_steps (s : BiCfg)
    (hk : PairComp.weight s.x s.y s.b PairComp.xb ≠ 0) :
    BiCfg.doubleLevel (heavyToDouble (PairComp.heavyNext s PairComp.xb))
      = BiCfg.doubleLevel (heavyToDouble s) + 2 := by
  rw [doubleLevel_heavyToDouble, doubleLevel_heavyToDouble,
    heavyLevel_heavyNext_xb s hk]
  omega

/-- The same on the `Y` side, stated subtraction-free. -/
theorem heavy_resolution_is_two_double_steps_down (s : BiCfg)
    (hk : PairComp.weight s.x s.y s.b PairComp.yb ≠ 0) :
    BiCfg.doubleLevel (heavyToDouble (PairComp.heavyNext s PairComp.yb)) + 2
      = BiCfg.doubleLevel (heavyToDouble s) := by
  rw [doubleLevel_heavyToDouble, doubleLevel_heavyToDouble]
  have h := heavyLevel_heavyNext_yb s hk
  omega

/-- **The one-step maps genuinely differ**, exhibited rather than argued: on a
state where an `X`-resolution is possible, the lumped Heavy successor and the
Double successor of the lumped state are not equal.

Concretely at `(1, 0, 1)` (population 3): Heavy's resolution gives `(3, 0, 0)`,
whose image is `(3, 0, 0)`; Double's gives `(2, 0, 1)`. -/
theorem heavyToDouble_next_ne :
    heavyToDouble (PairComp.heavyNext ⟨1, 0, 1⟩ PairComp.xb)
      ≠ PairComp.next (heavyToDouble ⟨1, 0, 1⟩) PairComp.xb := by
  simp only [heavyToDouble, PairComp.heavyNext, PairComp.next]
  decide

/-- **The second, independent obstruction: the entity counts differ.**

Interactions draw a pair of entities.  Heavy-B has `x + y + b` of them; its
image has `x + y + 2b`.  So whenever `b > 0` the pair distributions have
different denominators, and even the creation — which maps correctly on states
— fires with a different probability.

No reweighting repairs this together with the time change: an exact
intertwining is an equality of laws at every step, and both halves fail. -/
theorem heavyToDouble_entity_count (s : BiCfg) (hb : 0 < s.b) :
    s.x + s.y + s.b
      < (heavyToDouble s).x + (heavyToDouble s).y + (heavyToDouble s).b := by
  obtain ⟨x, y, b⟩ := s
  simp only [heavyToDouble] at *
  omega

/-! ### The direction the paper actually claims: Heavy-B onto the tri chain

The obstruction above is for Heavy-B onto Double-B.  The paper's own claim is
that each bimolecular protocol emulates the TRI-molecular one, so that is the
comparison that matters, and it fails too — sharply, and for a reason worth
knowing.

Under the only sensible lumping the tri state is the Heavy level `L = x + b`,
with co-level `y + b` (these sum to `n` by `heavyLevel_add_coLevel`).  The
productive tri chain at level `L` moves up:down with odds `(L−1) : (y+b−1)`,
because the drawn triple must contain two of the majority label and the
minority of the triple flips.  Heavy-B's resolutions move up:down with odds
`x : y`, the blank having cancelled.

Those are different numbers.  Writing `b = c + 1` to clear the subtractions,
they agree exactly when `x·c = y·c` — that is, **only** when `b = 1` or
`x = y`. -/

/-- **The Heavy-B and tri-molecular odds agree only degenerately.**

With `b = c + 1`, matching Heavy's resolution odds `x : y` against the tri
chain's `(x+b−1) : (y+b−1)` requires `x * (y + c) = y * (x + c)`, which holds
iff `c = 0` (a single blank) or `x = y` (a tie).

Stated subtraction-free by carrying `c` rather than `b − 1`. -/
theorem heavy_tri_odds_agree_iff (x y c : ℕ) :
    x * (y + c) = y * (x + c) ↔ c = 0 ∨ x = y := by
  constructor
  · intro h
    have hxc : x * c = y * c := by nlinarith [h]
    rcases Nat.eq_zero_or_pos c with hc | hc
    · exact Or.inl hc
    · exact Or.inr (Nat.eq_of_mul_eq_mul_right hc hxc)
  · rintro (rfl | rfl) <;> ring

/-- The same, read as a refutation: away from the two degenerate cases the odds
genuinely differ, so no state-only lumping can intertwine Heavy-B with the
productive tri chain either. -/
theorem heavy_tri_odds_differ {x y c : ℕ} (hc : c ≠ 0) (hxy : x ≠ y) :
    x * (y + c) ≠ y * (x + c) := fun h =>
  (heavy_tri_odds_agree_iff x y c).mp h |>.elim hc hxy

/-- A concrete witness: at `x = 3`, `y = 1`, `b = 3` (so `c = 2`) the two odds
disagree, `3 * 3 = 9` against `1 * 5 = 5`. -/
example : (3 : ℕ) * (1 + 2) ≠ 1 * (3 + 2) := by decide

end Tri

#print axioms Tri.heavyToDouble_doubleInv
#print axioms Tri.doubleLevel_heavyToDouble
#print axioms Tri.heavyToDouble_creation
#print axioms Tri.heavy_resolution_is_two_double_steps
#print axioms Tri.heavy_resolution_is_two_double_steps_down
#print axioms Tri.heavyToDouble_next_ne
#print axioms Tri.heavyToDouble_entity_count
#print axioms Tri.heavy_tri_odds_agree_iff
#print axioms Tri.heavy_tri_odds_differ
