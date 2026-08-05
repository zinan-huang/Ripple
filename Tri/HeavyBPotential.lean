/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBExpect
import Tri.PaperCorollary3

/-!
# The Heavy-B two-parameter potential

```text
Θ(q) = w^{heavyLevel} · η^{up + down}
```

the same shape as Double-B's `w^level · η^resolve`, now on Heavy-B's level and
its two separated resolution counters.

## Why the algebra lines up

Substituting `G := fun L u d => w^L · η^(u+d)` into `heavyTraceStep_expect`, the
two resolution branches BOTH land at `η` exponent `r+1` — the `X`-resolution
because it increments `up`, the `Y`-resolution because it increments `down`.
Factoring out `w^a · η^r` therefore leaves exactly

```text
neu·w + η·(dn + up·w²)
```

which is the left-hand side of `heavy_dir_scalar` on the nose. Nothing has to be
massaged: the potential was designed so that this is what falls out.

## The frozen form is the usable one

`heavyPotential_step` needs a live state — level at least one, the direction
guard `u·y ≤ x`, and enough entities to interact. Freezing on the complement
makes the supermartingale property hold at EVERY state, which is what
`expect_iter_le` and the Markov tail want. Frozen states are `pure`, so they
satisfy the inequality with equality.
-/

namespace Tri
open scoped ENNReal


noncomputable def heavyPotential (w η : ℝ≥0∞) {n : ℕ} (q : HeavyTrace n) : ℝ≥0∞ :=
  w ^ BiCfg.heavyLevel q.cfg.1 * η ^ (q.up + q.down)

theorem heavyPotential_step {n : ℕ} (q : HeavyTrace n)
    (h : 2 ≤ heavyEntities q.cfg) (a : ℕ)
    (ha : BiCfg.heavyLevel q.cfg.1 = a + 1) {u : ℕ}
    (w η : ℝ≥0∞) (hu : 1 ≤ u) (hguard : u * q.cfg.1.y ≤ q.cfg.1.x)
    (hrel : η * ((u : ℝ≥0∞) + w ^ 2) = w * ((u : ℝ≥0∞) + 1))
    (hwη : w ≤ η) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤) :
    expect (heavyTraceStep n q) (heavyPotential w η) ≤ heavyPotential w η q := by
  have hexp := heavyTraceStep_expect n q h a ha (fun L u' d => w ^ L * η ^ (u' + d))
  have hscalar := heavy_dir_scalar q.cfg h w η hu hguard hrel hwη hwt hηt
  unfold heavyPotential
  rw [hexp, ha]
  set dn := heavyResolveDown q.cfg
  set up := heavyResolveUp q.cfg
  set neu := heavyNeutralMass h
  set r := q.up + q.down with hr
  have e1 : q.up + (q.down + 1) = r + 1 := by omega
  have e2 : q.up + 1 + q.down = r + 1 := by omega
  rw [e1, e2]
  calc dn * (w ^ a * η ^ (r + 1)) + neu * (w ^ (a + 1) * η ^ r)
        + up * (w ^ (a + 2) * η ^ (r + 1))
      = (w ^ a * η ^ r) * (neu * w + η * (dn + up * w ^ 2)) := by
        rw [pow_succ, pow_succ, pow_succ, pow_succ]
        ring
    _ ≤ (w ^ a * η ^ r) * w := by gcongr
    _ = w ^ (a + 1) * η ^ r := by rw [pow_succ]; ring

/-! ### The frozen form -/

/-- The live region: the level can still fall, the direction guard holds, and
there are enough entities to draw a pair. -/
def HeavyLive (u : ℕ) {n : ℕ} (q : HeavyTrace n) : Prop :=
  1 ≤ BiCfg.heavyLevel q.cfg.1 ∧ u * q.cfg.1.y ≤ q.cfg.1.x
    ∧ 2 ≤ heavyEntities q.cfg

instance (u : ℕ) {n : ℕ} : DecidablePred (HeavyLive u (n := n)) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **The supermartingale step at every state.**  On the live region it is
`heavyPotential_step`; outside, the chain is frozen and the inequality is an
equality. -/
theorem heavyPotential_step_frozen {n : ℕ} {u : ℕ} (w η : ℝ≥0∞)
    (hu : 1 ≤ u)
    (hrel : η * ((u : ℝ≥0∞) + w ^ 2) = w * ((u : ℝ≥0∞) + 1))
    (hwη : w ≤ η) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤) (q : HeavyTrace n) :
    expect (freeze (fun z => ¬ HeavyLive u z) (heavyTraceStep n) q)
        (heavyPotential w η)
      ≤ heavyPotential w η q := by
  unfold freeze
  by_cases hq : ¬ HeavyLive u q
  · rw [if_pos hq, expect_pure]
  · rw [if_neg hq]
    push Not at hq
    obtain ⟨hlev, hguard, hent⟩ := hq
    obtain ⟨a, ha⟩ : ∃ a, BiCfg.heavyLevel q.cfg.1 = a + 1 :=
      ⟨BiCfg.heavyLevel q.cfg.1 - 1, by omega⟩
    exact heavyPotential_step q hent a ha w η hu hguard hrel hwη hwt hηt

/-- **The iterated bound.**  Contraction factor exactly `1`: the decay lives in
`η^{−resolutions}`, not in the horizon, which is the whole point of the
two-parameter design — there is no time-change coupling to pay for. -/
theorem heavyPotential_iter_le {n : ℕ} {u : ℕ} (w η : ℝ≥0∞)
    (hu : 1 ≤ u)
    (hrel : η * ((u : ℝ≥0∞) + w ^ 2) = w * ((u : ℝ≥0∞) + 1))
    (hwη : w ≤ η) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤) (T : ℕ) (q : HeavyTrace n) :
    expect (iter (freeze (fun z => ¬ HeavyLive u z) (heavyTraceStep n)) T q)
        (heavyPotential w η)
      ≤ heavyPotential w η q := by
  have hstep := heavyPotential_step_frozen (n := n) (u := u) w η hu hrel hwη hwt hηt
  have h := expect_iter_le
    (freeze (fun z => ¬ HeavyLive u z) (heavyTraceStep n))
    (heavyPotential w η) 1 (fun s => by simpa using hstep s) T q
  simpa using h

/-- **The Markov tail.**  The mass of traces whose potential has reached `θ` is
at most `Θ(start)/θ`.  With `θ = w^{L} · η^{M}` this is the exponential tail in
the number of resolutions the direction argument is aiming at. -/
theorem heavyPotential_markov {n : ℕ} {u : ℕ} (w η : ℝ≥0∞)
    (hu : 1 ≤ u)
    (hrel : η * ((u : ℝ≥0∞) + w ^ 2) = w * ((u : ℝ≥0∞) + 1))
    (hwη : w ≤ η) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤) (T : ℕ) (q : HeavyTrace n)
    (θ : ℝ≥0∞) (hθ : θ ≠ 0) (htop : θ ≠ ⊤) :
    ∑' z, (if θ ≤ heavyPotential w η z then
        iter (freeze (fun z => ¬ HeavyLive u z) (heavyTraceStep n)) T q z else 0)
      ≤ heavyPotential w η q / θ := by
  refine le_trans (markov_div _ (heavyPotential w η) θ hθ htop) ?_
  exact ENNReal.div_le_div_right
    (heavyPotential_iter_le w η hu hrel hwη hwt hηt T q) θ

/-! ### The entity condition is vacuous at `3 ≤ n`

`HeavyLive` bundles three conditions and the chain is frozen off all of them, so
it halts as soon as ANY fails — including the entity count, which is structural
rather than a band condition.  That is coarse: a run stopped for lack of
entities would be charged as a failure by any downstream tail.

At `3 ≤ n` it never happens (`heavy_two_entities`), and this makes that usable
rather than merely true: the freeze on the three-part set is EQUAL to the freeze
on the two-part band set, so every statement above can be read on the band alone.

This matters because `3 ≤ n` is forced anyway — `heavy_stuck_not_consensus`
shows Heavy-B genuinely fails at `n = 2`. -/

/-- The band-only live set. -/
def HeavyLiveBand (u : ℕ) {n : ℕ} (q : HeavyTrace n) : Prop :=
  1 ≤ BiCfg.heavyLevel q.cfg.1 ∧ u * q.cfg.1.y ≤ q.cfg.1.x

instance (u : ℕ) {n : ℕ} : DecidablePred (HeavyLiveBand u (n := n)) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

theorem heavyLive_iff_band {n u : ℕ} (hn : 3 ≤ n) (q : HeavyTrace n) :
    HeavyLive u q ↔ HeavyLiveBand u q := by
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2, heavy_two_entities hn q.cfg⟩

/-- **The two freezes coincide at `3 ≤ n`.**  So the structural conjunct costs
nothing and every bound above holds on the band-only stopped chain. -/
theorem heavy_freeze_eq {n u : ℕ} (hn : 3 ≤ n) :
    freeze (fun z : HeavyTrace n => ¬ HeavyLive u z) (heavyTraceStep n)
      = freeze (fun z : HeavyTrace n => ¬ HeavyLiveBand u z)
          (heavyTraceStep n) :=
  freeze_congr _ _ _ (fun s => not_congr (heavyLive_iff_band hn s))

/-- The iterated bound on the band-only stopped chain. -/
theorem heavyPotential_iter_le_band {n : ℕ} {u : ℕ} (hn : 3 ≤ n) (w η : ℝ≥0∞)
    (hu : 1 ≤ u)
    (hrel : η * ((u : ℝ≥0∞) + w ^ 2) = w * ((u : ℝ≥0∞) + 1))
    (hwη : w ≤ η) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤) (T : ℕ) (q : HeavyTrace n) :
    expect (iter (freeze (fun z => ¬ HeavyLiveBand u z) (heavyTraceStep n)) T q)
        (heavyPotential w η)
      ≤ heavyPotential w η q := by
  rw [← heavy_freeze_eq (u := u) hn]
  exact heavyPotential_iter_le w η hu hrel hwη hwt hηt T q

/-! ### The direction tail

The bad event is a LOW LEVEL together with MANY RESOLUTIONS: the level should
have risen by now and has not.  Containment needs both parameters pointed the
right way — `w ≤ 1` so that `w^level ≥ w^thr` below the threshold, and `1 ≤ η`
so that `η^resolve ≥ η^M` above it.  The second is the strong-majority regime,
and it is where the exponential smallness in `M` comes from.

Getting either orientation backwards would give a true but vacuous bound, so
both are hypotheses rather than derived. -/

/-- **The Heavy-B direction tail.**  From a fresh trace at level `L₀`, the mass
that after `T` frozen steps has both level `≤ thr` and at least `M` resolutions
is at most `w^{L₀} / (w^{thr} · η^{M})` — exponentially small in `M` once
`η > 1`. -/
theorem heavyDirStop_tail {n : ℕ} {u : ℕ} (hn : 3 ≤ n) (thr M T : ℕ)
    (w η : ℝ≥0∞) (hu : 1 ≤ u)
    (hrel : η * ((u : ℝ≥0∞) + w ^ 2) = w * ((u : ℝ≥0∞) + 1)) (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (q₀ : HeavyTrace n) (hr0 : q₀.up + q₀.down = 0) :
    ∑' q, (if BiCfg.heavyLevel q.cfg.1 ≤ thr ∧ M ≤ q.up + q.down then
        iter (freeze (fun z => ¬ HeavyLiveBand u z) (heavyTraceStep n)) T q₀ q
      else 0)
      ≤ w ^ BiCfg.heavyLevel q₀.cfg.1 / (w ^ thr * η ^ M) := by
  have hwt : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  set θ : ℝ≥0∞ := w ^ thr * η ^ M with hθdef
  have hθ0 : θ ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ hw0)
    exact pow_ne_zero _ (by rintro rfl; simp at hη1)
  have hθtop : θ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hwt) (ENNReal.pow_ne_top hηt)
  have hsub : ∀ q : HeavyTrace n,
      (if BiCfg.heavyLevel q.cfg.1 ≤ thr ∧ M ≤ q.up + q.down then
        iter (freeze (fun z => ¬ HeavyLiveBand u z) (heavyTraceStep n)) T q₀ q
      else 0)
      ≤ (if θ ≤ heavyPotential w η q then
        iter (freeze (fun z => ¬ HeavyLiveBand u z) (heavyTraceStep n)) T q₀ q
      else 0) := by
    intro q
    by_cases hq : BiCfg.heavyLevel q.cfg.1 ≤ thr ∧ M ≤ q.up + q.down
    · have hle : θ ≤ heavyPotential w η q := by
        rw [hθdef, heavyPotential]
        exact mul_le_mul' (pow_le_pow_right_of_le_one' hw1 hq.1)
          (pow_le_pow_right₀ hη1 hq.2)
      simp [hq, hle]
    · simp [hq]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans (markov_div _ (heavyPotential w η) θ hθ0 hθtop) ?_
  have hiter := heavyPotential_iter_le_band (u := u) hn w η hu hrel hwη hwt hηt T q₀
  have hΘ0 : heavyPotential w η q₀ = w ^ BiCfg.heavyLevel q₀.cfg.1 := by
    simp [heavyPotential, hr0]
  rw [hΘ0] at hiter
  exact ENNReal.div_le_div_right hiter θ

end Tri

#print axioms Tri.heavyPotential_step
#print axioms Tri.heavyPotential_step_frozen
#print axioms Tri.heavyPotential_iter_le
#print axioms Tri.heavyPotential_markov
#print axioms Tri.heavyLive_iff_band
#print axioms Tri.heavy_freeze_eq
#print axioms Tri.heavyPotential_iter_le_band
#print axioms Tri.heavyDirStop_tail
