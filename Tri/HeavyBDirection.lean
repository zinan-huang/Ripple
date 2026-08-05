/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBTrace
import Tri.DoubleBDirection

/-!
# Heavy-B's direction step, instantiated from the Double-B scalar core

`Tri/HeavyBEmulation.lean` ruled out transporting the Heavy-B clause along a
lumping. What ports instead is the *scalar core*: `doubleDir_scalar`
(`Tri/DoubleBDirection.lean`) is stated over abstract `ℝ≥0∞` masses
`dn, neu, up` and abstract parameters `u, w, η`, with no reference to any
protocol. So the Double-B engine's arithmetic is reusable verbatim; only the
masses and the guard have to be supplied.

That is a sharper statement than "Heavy-B is a port". The *dynamics* do not
transport — that is the content of `HeavyBEmulation` — but the *inequality*
does, because it was already protocol-free.

## One real difference: the denominator is state-dependent

Double-B has `x + y + b = n`, so its masses can be written over the constant
`C(n,2)`. Heavy-B has `x + y + 2b = n`: the entity count `x + y + b` SHRINKS as
blanks form, so the denominator varies along the trajectory and must be carried
per state.

This does not weaken anything — the direction guard is a ratio, and the shared
denominator cancels — but it is why the mass definitions below take the entity
count from the state rather than from `n`.

## The guard

`doubleDir_scalar` wants `dn ≤ up · u`. Here `dn = y·b/C` and `up = x·b/C`, so
the blank cancels and it reduces to `y ≤ x·u`, which follows from the natural
guard `u·y ≤ x` once `1 ≤ u`. The `b` never appears — that is the cancellation
`heavy_resolution_odds` records, doing its job.
-/

namespace Tri

open scoped ENNReal

variable {n : ℕ}

/-- The entity count: what a pair is drawn from.  Not `n` — a heavy blank is one
entity worth two units. -/
def heavyEntities (s : HeavyState n) : ℕ := s.1.x + s.1.y + s.1.b

theorem heavyEntities_two (hn : 3 ≤ n) (s : HeavyState n) :
    2 ≤ heavyEntities s := heavy_two_entities hn s

/-- Resolution-up mass: `x·b / C(entities, 2)`. -/
noncomputable def heavyResolveUp (s : HeavyState n) : ℝ≥0∞ :=
  ((s.1.x * s.1.b : ℕ) : ℝ≥0∞) / (Nat.choose (heavyEntities s) 2 : ℝ≥0∞)

/-- Resolution-down mass: `y·b / C(entities, 2)`. -/
noncomputable def heavyResolveDown (s : HeavyState n) : ℝ≥0∞ :=
  ((s.1.y * s.1.b : ℕ) : ℝ≥0∞) / (Nat.choose (heavyEntities s) 2 : ℝ≥0∞)

/-- Everything that does not move the level: the creation and the three inert
compositions. -/
noncomputable def heavyNeutralMass (h : 2 ≤ heavyEntities s) : ℝ≥0∞ :=
  dbPairPMF s.1.x s.1.y s.1.b h .xy + dbPairPMF s.1.x s.1.y s.1.b h .xx
    + dbPairPMF s.1.x s.1.y s.1.b h .yy + dbPairPMF s.1.x s.1.y s.1.b h .bb

theorem heavyResolveUp_eq (s : HeavyState n) (h : 2 ≤ heavyEntities s) :
    dbPairPMF s.1.x s.1.y s.1.b h .xb = heavyResolveUp s := by
  unfold heavyResolveUp heavyEntities
  rw [dbPairPMF_apply]
  rfl

theorem heavyResolveDown_eq (s : HeavyState n) (h : 2 ≤ heavyEntities s) :
    dbPairPMF s.1.x s.1.y s.1.b h .yb = heavyResolveDown s := by
  unfold heavyResolveDown heavyEntities
  rw [dbPairPMF_apply]
  rfl

/-- **The three masses partition one step.** -/
theorem heavy_mass_sum (s : HeavyState n) (h : 2 ≤ heavyEntities s) :
    heavyResolveDown s + heavyNeutralMass h + heavyResolveUp s = 1 := by
  have htot : ∑ k : PairComp, dbPairPMF s.1.x s.1.y s.1.b h k = 1 := by
    have h' := (dbPairPMF s.1.x s.1.y s.1.b h).tsum_coe
    rwa [tsum_fintype] at h'
  rw [← heavyResolveUp_eq s h, ← heavyResolveDown_eq s h]
  unfold heavyNeutralMass
  rw [show (Finset.univ : Finset PairComp)
      = {PairComp.xx, PairComp.xy, PairComp.yy, PairComp.xb, PairComp.yb,
         PairComp.bb} from rfl,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at htot
  rw [← htot]; ring

/-- **The direction guard, with the blank cancelled.**  `u·y ≤ x` gives
`dn ≤ up · u`, and `b` never appears. -/
theorem heavy_dir_guard {u : ℕ} (s : HeavyState n)
    (hu : 1 ≤ u) (hguard : u * s.1.y ≤ s.1.x) :
    heavyResolveDown s ≤ heavyResolveUp s * (u : ℝ≥0∞) := by
  unfold heavyResolveDown heavyResolveUp
  have hyx : s.1.y ≤ s.1.x :=
    le_trans (by simpa using Nat.mul_le_mul_right s.1.y hu) hguard
  have hnat : s.1.y * s.1.b ≤ s.1.x * s.1.b * u := by
    refine le_trans (Nat.mul_le_mul_right s.1.b hyx) ?_
    calc s.1.x * s.1.b = s.1.x * s.1.b * 1 := (mul_one _).symm
      _ ≤ s.1.x * s.1.b * u := Nat.mul_le_mul_left _ hu
  have hcast : ((s.1.y * s.1.b : ℕ) : ℝ≥0∞)
      ≤ ((s.1.x * s.1.b : ℕ) : ℝ≥0∞) * (u : ℝ≥0∞) := by
    have : ((s.1.y * s.1.b : ℕ) : ℝ≥0∞) ≤ ((s.1.x * s.1.b * u : ℕ) : ℝ≥0∞) := by
      exact_mod_cast Nat.cast_le.mpr hnat
    simpa [Nat.cast_mul] using this
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
  gcongr

/-- **Heavy-B's direction step.**  A direct instantiation of the protocol-free
scalar core with Heavy-B's masses and guard.

Nothing is re-derived: the whole content is `doubleDir_scalar`, and this
supplies the four hypotheses it needs. -/
theorem heavy_dir_scalar {u : ℕ} (s : HeavyState n) (h : 2 ≤ heavyEntities s)
    (w η : ℝ≥0∞) (hu : 1 ≤ u) (hguard : u * s.1.y ≤ s.1.x)
    (hrel : η * ((u : ℝ≥0∞) + w ^ 2) = w * ((u : ℝ≥0∞) + 1))
    (hwη : w ≤ η) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤) :
    heavyNeutralMass h * w
        + η * (heavyResolveDown s + heavyResolveUp s * w ^ 2)
      ≤ w := by
  refine doubleDir_scalar (heavyResolveDown s) (heavyNeutralMass h)
    (heavyResolveUp s) (u : ℝ≥0∞) w η (heavy_mass_sum s h)
    (heavy_dir_guard s hu hguard) hrel hwη ?_ ?_ ?_ hwt hηt
    (ENNReal.natCast_ne_top u)
  · rw [← heavyResolveDown_eq s h]; exact PMF.apply_ne_top _ _
  · unfold heavyNeutralMass
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩,
          PMF.apply_ne_top _ _⟩,
        PMF.apply_ne_top _ _⟩
  · rw [← heavyResolveUp_eq s h]; exact PMF.apply_ne_top _ _

/-! ### The direction parameters always exist

`heavy_dir_scalar` carries the direction optimum `η(u+w²) = w(u+1)` and `w ≤ η`
as hypotheses.  That leaves open whether any such pair EXISTS at Heavy-B's
constants — the kind of question that turned out to hide a real gap in Lemma 12.

It does not hide one here, and the reason is clean: solving the relation for `η`
gives `η = w(u+1)/(u+w²)`, and `w ≤ η` is then equivalent to `u + w² ≤ u + 1`,
i.e. to `w ≤ 1`.  So EVERY `w ≤ 1` has a partner, with no constraint linking `w`
to `u` at all.

The fact is protocol-free — it is about `doubleDir_scalar`'s hypotheses, not
about Heavy-B — and it applies equally to the Double-B and relaxed engines. -/

/-- **The direction optimum is always solvable.**  For every `w ≤ 1` the partner
`η = w(u+1)/(u+w²)` satisfies both the optimum relation and `w ≤ η`.

There is no constant gap to check: the constraint is `w ≤ 1` and nothing more. -/
theorem dir_params_exist (u w : ℝ≥0∞) (hu : u ≠ ⊤) (hu0 : u ≠ 0)
    (hw1 : w ≤ 1) (hwt : w ≠ ⊤) :
    ∃ η : ℝ≥0∞, η ≠ ⊤ ∧ w ≤ η ∧ η * (u + w ^ 2) = w * (u + 1) := by
  have hden0 : u + w ^ 2 ≠ 0 := by
    intro h
    rw [add_eq_zero] at h
    exact hu0 h.1
  have hdent : u + w ^ 2 ≠ ⊤ := by finiteness
  refine ⟨w * (u + 1) / (u + w ^ 2), ?_, ?_, ?_⟩
  · exact ENNReal.div_ne_top (by finiteness) hden0
  · rw [ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdent)]
    have hw2 : w ^ 2 ≤ 1 := by
      calc w ^ 2 = w * w := sq w
        _ ≤ 1 * 1 := mul_le_mul' hw1 hw1
        _ = 1 := one_mul 1
    gcongr
  · exact ENNReal.div_mul_cancel hden0 hdent

/-- **Heavy-B's direction step, with the parameters supplied rather than
assumed.**  Closes the open question above: for every `w ≤ 1` there is a partner
`η` making the step hold, so the engine's hypotheses are satisfiable at every
Heavy-B state meeting the guard. -/
theorem heavy_dir_scalar_exists {u : ℕ} (s : HeavyState n)
    (h : 2 ≤ heavyEntities s) (w : ℝ≥0∞)
    (hu : 1 ≤ u) (hguard : u * s.1.y ≤ s.1.x)
    (hw1 : w ≤ 1) (hwt : w ≠ ⊤) :
    ∃ η : ℝ≥0∞, η ≠ ⊤ ∧ w ≤ η ∧
      heavyNeutralMass h * w
          + η * (heavyResolveDown s + heavyResolveUp s * w ^ 2)
        ≤ w := by
  have hu0 : (u : ℝ≥0∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  obtain ⟨η, hηt, hwη, hrel⟩ :=
    dir_params_exist (u : ℝ≥0∞) w (ENNReal.natCast_ne_top u) hu0 hw1 hwt
  exact ⟨η, hηt, hwη,
    heavy_dir_scalar s h w η hu hguard hrel hwη hwt hηt⟩

/-! ### When is `η ≥ 1`?  Exactly in the strong-majority regime

`dir_params_exist` gives a partner `η` for every `w ≤ 1`, but the direction TAIL
additionally needs `1 ≤ η` — that is what makes `η^resolve` grow with the
resolution count and the bound exponentially small.

The two are NOT simultaneously free.  At `u = 1`, `w = 1/2` the partner is
`η = (1/2)(2)/(1 + 1/4) = 4/5 < 1`, so a careless choice of `w` gives a true but
vacuous tail.

The condition is exactly the strong-majority one.  Solving,

```text
η ≥ 1  ⟺  w(u+1) ≥ u + w²  ⟺  (1−w)(w−u) ≥ 0
```

so under `w ≤ 1` it is `u ≤ w`.  That is precisely the `u < w < 1` regime the
Double-B development names, arrived at here independently. -/

theorem dir_num_ge_den {u w : ℝ≥0∞} (hu : u ≠ ⊤) (hw1 : w ≤ 1) (huw : u ≤ w) :
    u + w ^ 2 ≤ w * (u + 1) := by
  have hwt : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  rw [ENNReal.toReal_add hu (by finiteness), ENNReal.toReal_pow,
    ENNReal.toReal_mul, ENNReal.toReal_add hu ENNReal.one_ne_top,
    ENNReal.toReal_one]
  have h1 : w.toReal ≤ 1 := by
    simpa using (ENNReal.toReal_le_toReal hwt ENNReal.one_ne_top).mpr hw1
  have h2 : u.toReal ≤ w.toReal := (ENNReal.toReal_le_toReal hu hwt).mpr huw
  have h3 : 0 ≤ u.toReal := ENNReal.toReal_nonneg
  nlinarith

theorem dir_eta_ge_one {u w : ℝ≥0∞} (hu : u ≠ ⊤) (hu0 : u ≠ 0)
    (hw1 : w ≤ 1) (huw : u ≤ w) :
    1 ≤ w * (u + 1) / (u + w ^ 2) := by
  have hwt : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  have hden0 : u + w ^ 2 ≠ 0 := by
    intro h; rw [add_eq_zero] at h; exact hu0 h.1
  have hdent : u + w ^ 2 ≠ ⊤ := by finiteness
  rw [ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdent), one_mul]
  exact dir_num_ge_den hu hw1 huw

/-- **The direction parameters, with the tail's extra requirement.**  For
`u ≤ w ≤ 1` the partner `η` satisfies `1 ≤ η` as well, so the whole tail
argument is available. -/
theorem dir_params_exist_strong (u w : ℝ≥0∞) (hu : u ≠ ⊤) (hu0 : u ≠ 0)
    (hw1 : w ≤ 1) (huw : u ≤ w) (hwt : w ≠ ⊤) :
    ∃ η : ℝ≥0∞, η ≠ ⊤ ∧ w ≤ η ∧ 1 ≤ η ∧ η * (u + w ^ 2) = w * (u + 1) := by
  obtain ⟨η, hηt, hwη, hrel⟩ := dir_params_exist u w hu hu0 hw1 hwt
  refine ⟨η, hηt, hwη, ?_, hrel⟩
  have hden0 : u + w ^ 2 ≠ 0 := by
    intro h; rw [add_eq_zero] at h; exact hu0 h.1
  have hdent : u + w ^ 2 ≠ ⊤ := by finiteness
  rw [← ENNReal.mul_le_mul_iff_left hden0 hdent, one_mul, hrel]
  exact dir_num_ge_den hu hw1 huw

/-! ### CORRECTION: the natural-number guard cannot compose with the tail

`heavy_dir_guard` above is stated for a NATURAL `u` with `1 ≤ u`, and it is
true.  But it cannot be used together with the direction tail, and the reason is
forced rather than incidental:

* the tail needs `1 ≤ η` (else `η^resolve` shrinks and the bound is vacuous);
* `dir_eta_ge_one` shows `1 ≤ η` needs `u ≤ w`;
* the potential needs `w ≤ 1`.

Together these give `1 ≤ u ≤ w ≤ 1`, so `u = w = 1`, hence `η = 1` and the
potential is identically `1`.  Completely degenerate.

So the direction parameter must be a RATIO strictly below one, and the guard
must be the reciprocal odds condition: the minority is at most a `p/q` fraction
of the majority.  A dispatched audit flagged exactly this, and the degeneracy
above is the check I ran before accepting it.

This is recorded rather than deleted: `heavy_dir_guard` is a true lemma about a
regime that turns out to be empty, and knowing the regime is empty is the useful
fact. -/

/-- **The composition is degenerate at a natural `u`.**  With `1 ≤ u`, `u ≤ w`
and `w ≤ 1` the parameters collapse to `u = w = 1`. -/
theorem heavy_nat_u_degenerate {u w : ℝ≥0∞}
    (hu : 1 ≤ u) (huw : u ≤ w) (hw1 : w ≤ 1) : u = 1 ∧ w = 1 :=
  ⟨le_antisymm (le_trans huw hw1) hu,
   le_antisymm hw1 (le_trans hu huw)⟩


/-- **The corrected direction guard.**  `u` must be a ratio `p/q < 1`, and the
guard is the RECIPROCAL odds condition `q*y <= p*x` -- the minority is at most a
`p/q` fraction of the majority.

The earlier `heavy_dir_guard`, stated for a NATURAL `u >= 1`, is true but cannot
compose with the tail: the tail needs `1 <= eta`, which needs `u <= w <= 1`,
which at `u : ℕ, 1 <= u` forces `u = w = 1` and a constant potential. -/
theorem heavy_dir_guard_ratio {p q : ℕ} (s : HeavyState n)
    (hq : q ≠ 0) (hguard : q * s.1.y ≤ p * s.1.x) :
    heavyResolveDown s
      ≤ heavyResolveUp s * ((p : ℝ≥0∞) / (q : ℝ≥0∞)) := by
  unfold heavyResolveDown heavyResolveUp
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by simpa using hq
  have hqt : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top q
  have hnat : q * (s.1.y * s.1.b) ≤ p * (s.1.x * s.1.b) := by
    calc q * (s.1.y * s.1.b) = (q * s.1.y) * s.1.b := by ring
      _ ≤ (p * s.1.x) * s.1.b := Nat.mul_le_mul_right _ hguard
      _ = p * (s.1.x * s.1.b) := by ring
  have hcast : (q : ℝ≥0∞) * ((s.1.y * s.1.b : ℕ) : ℝ≥0∞)
      ≤ (p : ℝ≥0∞) * ((s.1.x * s.1.b : ℕ) : ℝ≥0∞) := by
    have : ((q * (s.1.y * s.1.b) : ℕ) : ℝ≥0∞)
        ≤ ((p * (s.1.x * s.1.b) : ℕ) : ℝ≥0∞) := Nat.cast_le.mpr hnat
    simpa [Nat.cast_mul] using this
  rw [← ENNReal.mul_le_mul_iff_left hq0 hqt, mul_assoc,
    ENNReal.div_mul_cancel hq0 hqt]
  calc ((s.1.y * s.1.b : ℕ) : ℝ≥0∞)
        / (Nat.choose (heavyEntities s) 2 : ℝ≥0∞) * (q : ℝ≥0∞)
      = ((q : ℝ≥0∞) * ((s.1.y * s.1.b : ℕ) : ℝ≥0∞))
          / (Nat.choose (heavyEntities s) 2 : ℝ≥0∞) := by
        simp only [div_eq_mul_inv]; ring
    _ ≤ ((p : ℝ≥0∞) * ((s.1.x * s.1.b : ℕ) : ℝ≥0∞))
          / (Nat.choose (heavyEntities s) 2 : ℝ≥0∞) := by gcongr
    _ = ((s.1.x * s.1.b : ℕ) : ℝ≥0∞)
          / (Nat.choose (heavyEntities s) 2 : ℝ≥0∞) * (p : ℝ≥0∞) := by
        simp only [div_eq_mul_inv]; ring


/-- **The direction step at a ratio parameter.**  The usable form: `u = p/q`
with the reciprocal guard, so `u < 1` is available and the tail's `1 ≤ η` is
reachable. -/
theorem heavy_dir_scalar_ratio {p q : ℕ} (s : HeavyState n)
    (h : 2 ≤ heavyEntities s) (w η : ℝ≥0∞)
    (hq : q ≠ 0) (hp : p ≠ 0) (hguard : q * s.1.y ≤ p * s.1.x)
    (hrel : η * ((p : ℝ≥0∞) / (q : ℝ≥0∞) + w ^ 2)
      = w * ((p : ℝ≥0∞) / (q : ℝ≥0∞) + 1))
    (hwη : w ≤ η) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤) :
    heavyNeutralMass h * w
        + η * (heavyResolveDown s + heavyResolveUp s * w ^ 2)
      ≤ w := by
  have hq0 : (q : ℝ≥0∞) ≠ 0 := by simpa using hq
  have hut : (p : ℝ≥0∞) / (q : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top p) hq0
  refine doubleDir_scalar (heavyResolveDown s) (heavyNeutralMass h)
    (heavyResolveUp s) ((p : ℝ≥0∞) / (q : ℝ≥0∞)) w η (heavy_mass_sum s h)
    (heavy_dir_guard_ratio s hq hguard) hrel hwη ?_ ?_ ?_ hwt hηt hut
  · rw [← heavyResolveDown_eq s h]; exact PMF.apply_ne_top _ _
  · unfold heavyNeutralMass
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩,
          PMF.apply_ne_top _ _⟩,
        PMF.apply_ne_top _ _⟩
  · rw [← heavyResolveUp_eq s h]; exact PMF.apply_ne_top _ _

end Tri

#print axioms Tri.heavy_mass_sum
#print axioms Tri.heavy_dir_guard
#print axioms Tri.heavy_dir_scalar
#print axioms Tri.dir_params_exist
#print axioms Tri.heavy_dir_scalar_exists
#print axioms Tri.dir_num_ge_den
#print axioms Tri.dir_eta_ge_one
#print axioms Tri.dir_params_exist_strong
#print axioms Tri.heavy_nat_u_degenerate
#print axioms Tri.heavy_dir_guard_ratio
#print axioms Tri.heavy_dir_scalar_ratio
