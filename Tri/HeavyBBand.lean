/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBPotential
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Heavy-B's phase-1 band parameters

The direction layer needs `0 < u < w < 1`, which by `dir_eta_ge_one` gives
`1 ≤ η` and hence a non-vacuous tail. This file exhibits parameters that meet it.

In the subtraction-free parametrisation `a + 2B = n`:

```text
u = a/(a + 4B)        w = (a + 2B)/(a + 3B)
```

## `u < w` needs less than was claimed

`u < w` reduces to `a(a+3B) < (a+2B)(a+4B)`, i.e. to `0 < 3aB + 8B²`. So it
holds for **every** positive band width — it does NOT need the first-quarter
restriction `4B ≤ n`, which enters only through `u > 0` (equivalently `a > 0`,
i.e. `2B < n`).

I checked this numerically first, at `B = n/3` and `B = n/2 − 1` — both beyond
the restriction, both satisfying `u < w` — before proving it. The independent
verification round had flagged the same thing.

## What this does and does not settle

It settles that the tail regime is reachable at Heavy-B's band, so the direction
machinery is not vacuous there. It also converts the two exact terms to
exponentials and combines them into the band error.  On a raw clock, the
separate resolution-shortage event described below still needs its own bound.
-/

namespace Tri
open scoped ENNReal


/-- Heavy-B phase-1 band parameters, in the subtraction-free parametrisation
`a + 2B = n`.  `u` is the resolution-odds ratio, `w` the level tilt. -/
noncomputable def heavyBandU (a B : ℕ) : ℝ := (a : ℝ) / ((a : ℝ) + 4 * (B : ℝ))
noncomputable def heavyBandW (a B : ℕ) : ℝ :=
  ((a : ℝ) + 2 * (B : ℝ)) / ((a : ℝ) + 3 * (B : ℝ))

theorem heavyBandU_pos {a B : ℕ} (ha : 0 < a) : 0 < heavyBandU a B := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  unfold heavyBandU
  have : (0 : ℝ) < (a : ℝ) + 4 * (B : ℝ) := by positivity
  positivity

theorem heavyBandW_lt_one {a B : ℕ} (hB : 0 < B) : heavyBandW a B < 1 := by
  have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have haR : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  unfold heavyBandW
  rw [div_lt_one (by positivity)]
  linarith

/-- **The strong-majority condition holds for every positive band width.**
`u < w` reduces to `0 < 3aB + 8B²`, so it needs only `a, B > 0` -- in
particular it does NOT need the first-quarter restriction `4B ≤ n`. -/
theorem heavyBandU_lt_W {a B : ℕ} (ha : 0 < a) (hB : 0 < B) :
    heavyBandU a B < heavyBandW a B := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  unfold heavyBandU heavyBandW
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [haR, hBR]

/-- Hence the tail regime `u < w < 1` is available at every positive band
width, which by `dir_eta_ge_one` gives `1 ≤ η`. -/
theorem heavyBand_tail_regime {a B : ℕ} (ha : 0 < a) (hB : 0 < B) :
    0 < heavyBandU a B ∧ heavyBandU a B < heavyBandW a B
      ∧ heavyBandW a B < 1 :=
  ⟨heavyBandU_pos ha, heavyBandU_lt_W ha hB, heavyBandW_lt_one hB⟩
/-- The partner tilt at the band parameters.

Sanity-checked against the `(n, B)` form: with `a = n − 2B` the definitions
agree (`u = (n−2B)/(n+2B)`, `w = n/(n+B)`), and at `n = 1000` the tilt evaluates
to `1.095890` at `B = n/4`, `1.179917` at `B = n/3` and `1.497133` at
`B = n/2 − 1` — matching the values computed independently from that form to
six decimal places.  Scanning the whole range `0 < B < n/2` gives zero
violations of `1 ≤ η`. -/
noncomputable def heavyBandEta (a B : ℕ) : ℝ :=
  heavyBandW a B * (heavyBandU a B + 1)
    / (heavyBandU a B + heavyBandW a B ^ 2)

/-- **The real-valued form of the `η ≥ 1` criterion.**  The identity
`w(u+1) − (u + w²) = (1 − w)(w − u)` makes it immediate from `u < w < 1`.

The `ℝ≥0∞` version (`dir_eta_ge_one`) cannot be used directly here because the
band parameters are real-valued; the algebra is the same and is short enough to
redo. -/
theorem eta_ge_one_real {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1) :
    1 ≤ w * (u + 1) / (u + w ^ 2) := by
  have hden : 0 < u + w ^ 2 := by positivity
  rw [le_div_iff₀ hden, one_mul]
  nlinarith [mul_pos (sub_pos.mpr hw) (sub_pos.mpr huw)]

/-- **The band's tilt exceeds one**, so the direction tail is non-vacuous at
Heavy-B's phase-1 parameters. -/
theorem heavyBandEta_ge_one {a B : ℕ} (ha : 0 < a) (hB : 0 < B) :
    1 ≤ heavyBandEta a B := by
  obtain ⟨hu, huw, hw⟩ := heavyBand_tail_regime ha hB
  exact eta_ge_one_real hu huw hw

/-- And it dominates `w`, the second hypothesis the scalar step needs. -/
theorem heavyBandW_le_eta {a B : ℕ} (ha : 0 < a) (hB : 0 < B) :
    heavyBandW a B ≤ heavyBandEta a B := by
  obtain ⟨hu, huw, hw⟩ := heavyBand_tail_regime ha hB
  have hden : 0 < heavyBandU a B + heavyBandW a B ^ 2 := by positivity
  unfold heavyBandEta
  rw [le_div_iff₀ hden]
  have hwpos : 0 < heavyBandW a B := lt_trans hu huw
  nlinarith [hwpos, hw]

/-! ### The backslide term of the band error

The Heavy-B band error is a sum of two terms: a BACKSLIDE term, bounding the
mass that has dropped `B` levels, and a DEADLINE term, bounding the mass that
has not accumulated enough resolutions.  This section does the first.

It is `heavyDirStop_tail` at `M = 0`: with no resolution requirement the
`η^M` factor is `1` and the bound is the pure level ratio.  Writing the start
level subtraction-free as `thr + B = L₀` collapses it to `w ^ B`.
-/

/-- **The backslide error.**  Taking `M = 0` in the direction tail leaves the
pure level term, and with the start level written subtraction-free as
`thr + B = L₀` the bound collapses to `w ^ B`.

This is one of the two terms the Heavy-B band error is the sum of. -/
theorem heavy_backslide_tail {n : ℕ} {u : ℕ} (hn : 3 ≤ n) (thr Bw T : ℕ)
    (w η : ℝ≥0∞) (hu : 1 ≤ u)
    (hrel : η * ((u : ℝ≥0∞) + w ^ 2) = w * ((u : ℝ≥0∞) + 1)) (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (q₀ : HeavyTrace n) (hr0 : q₀.up + q₀.down = 0)
    (hlev : BiCfg.heavyLevel q₀.cfg.1 = thr + Bw) :
    ∑' q, (if BiCfg.heavyLevel q.cfg.1 ≤ thr then
        iter (freeze (fun z => ¬ HeavyLiveBand u z) (heavyTraceStep n)) T q₀ q
      else 0)
      ≤ w ^ Bw := by
  have hwt : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  have hmain := heavyDirStop_tail (u := u) hn thr 0 T w η hu hrel hwη hw1 hw0
    hη1 hηt q₀ hr0
  simp only [pow_zero, mul_one, Nat.zero_le, and_true] at hmain
  refine le_trans hmain (le_of_eq ?_)
  rw [hlev, pow_add, div_eq_mul_inv]
  calc w ^ thr * w ^ Bw * (w ^ thr)⁻¹
      = w ^ Bw * (w ^ thr * (w ^ thr)⁻¹) := by ring
    _ = w ^ Bw := by
        rw [ENNReal.mul_inv_cancel (pow_ne_zero _ hw0)
          (ENNReal.pow_ne_top hwt), mul_one]

/-! ### The deadline term, and what the tail does NOT bound

My objection to the offered figure `1/(w^{2B} · η^{2n})` was that it seemed to
need numerator `1`, i.e. `L₀ = 0`, which is not the band's start.  That was
looking at the wrong end: the cancellation comes from the THRESHOLD, taken at
the stage's top with `L₀ + 2B = L_hi`, giving

```text
w^{L₀} / (w^{L₀ + 2B} · η^{2n})  =  1 / (w^{2B} · η^{2n})
```

**The semantic point matters more than the algebra.**  `heavyDirStop_tail` does
NOT bound "too few resolutions".  Its event contains `M ≤ up + down`, so what it
bounds is *failure to make level progress DESPITE having many resolutions*.
A resolution SHORTAGE is a clock event and needs its own theorem — on the
productive clock the ledger makes the floor deterministic and no such term
arises, but on a raw horizon it is a genuine separate obligation.

So the two-term band estimate `w^B + 1/(w^{2B} η^{2n})` is complete for the
productive-clock directional phase, and is the band part only for a raw-clock
phase whose clock error has been discharged separately.
-/

/-- The ledger floor with no quota equation: `2K + 2b₀ ≤ n + 4R` where
`K = fuel + up + down` is read off the trace. -/
theorem heavyTrace_floor_raw {n x₀ y₀ b₀ : ℕ} (q : HeavyTrace n)
    (hx : q.XLedger x₀) (hy : q.YLedger y₀)
    (hinv : x₀ + y₀ + 2 * b₀ = n) :
    2 * (q.fuel + q.up + q.down) + 2 * b₀ ≤ n + 4 * (q.up + q.down) := by
  simp only [HeavyTrace.XLedger, HeavyTrace.YLedger] at hx hy
  omega

/-- **The directional deadline event.**  The productive quota has been met but
the level has still not crossed the stage's upper target. -/
def HeavyQuotaDeadline (n Lhi : ℕ) (q : HeavyTrace n) : Prop :=
  BiCfg.heavyLevel q.cfg.1 ≤ Lhi ∧ 7 * n ≤ q.fuel + q.up + q.down

noncomputable instance (n Lhi : ℕ) : DecidablePred (HeavyQuotaDeadline n Lhi) :=
  fun _ => Classical.dec _

/-- **The containment the tail needs.**  Meeting the quota forces `3n`
resolutions via the two exact ledgers, so the deadline event sits inside the
`{level ≤ thr ∧ M ≤ resolutions}` shape at `M = 2n`.

Note what this does NOT say: `heavyDirStop_tail` bounds failure to make level
progress DESPITE many resolutions.  It does not bound "too few resolutions" --
that is a clock event and needs its own theorem. -/
theorem heavyQuotaDeadline_subset {n Lhi x₀ y₀ b₀ : ℕ} (q : HeavyTrace n)
    (hx : q.XLedger x₀) (hy : q.YLedger y₀)
    (hinv : x₀ + y₀ + 2 * b₀ = n)
    (hq : HeavyQuotaDeadline n Lhi q) :
    BiCfg.heavyLevel q.cfg.1 ≤ Lhi ∧ 2 * n ≤ q.up + q.down := by
  obtain ⟨hlev, hquota⟩ := hq
  refine ⟨hlev, ?_⟩
  have h := heavyTrace_floor_raw q hx hy hinv
  omega

/-- **The deadline term.**  With the threshold at the stage top
(`L₀ + 2B = Lhi`) the level ratio cancels and the bound is
`1 / (w^(2B) · η^(2n))`. -/
theorem heavy_deadline_tail {n : ℕ} {u : ℕ} (hn : 3 ≤ n) (Lhi Bw T : ℕ)
    (w η : ℝ≥0∞) (hu : 1 ≤ u)
    (hrel : η * ((u : ℝ≥0∞) + w ^ 2) = w * ((u : ℝ≥0∞) + 1)) (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (q₀ : HeavyTrace n) (hr0 : q₀.up + q₀.down = 0)
    (hLhi : BiCfg.heavyLevel q₀.cfg.1 + 2 * Bw = Lhi) :
    ∑' q, (if BiCfg.heavyLevel q.cfg.1 ≤ Lhi ∧ 2 * n ≤ q.up + q.down then
        iter (freeze (fun z => ¬ HeavyLiveBand u z) (heavyTraceStep n)) T q₀ q
      else 0)
      ≤ 1 / (w ^ (2 * Bw) * η ^ (2 * n)) := by
  have hwt : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  refine le_trans (heavyDirStop_tail (u := u) hn Lhi (2 * n) T w η hu hrel hwη
    hw1 hw0 hη1 hηt q₀ hr0) (le_of_eq ?_)
  rw [← hLhi, pow_add, mul_assoc, div_eq_mul_inv, one_div,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ hw0))
      (Or.inl (ENNReal.pow_ne_top hwt)), ← mul_assoc,
    ENNReal.mul_inv_cancel (pow_ne_zero _ hw0) (ENNReal.pow_ne_top hwt),
    one_mul]


/-! ### The tilt identity, and an honest note on the constant

The deadline term is `D_B = 1/(w^{2B} η^{2n})`, whose `1/w^{2B}` factor exceeds
one — so ALL of its smallness has to come from `η^{2n}`. Writing `x = B/n`,

```text
D_B = exp(−2n(log η − x·log(1+x)))
```

and the bracket is bounded below via the identity proved here plus
`log z ≥ 1 − 1/z`:

```text
log η − x·log(1+x) ≥ x²/2      hence      D_B ≤ exp(−B²/n)
```

Verified numerically on the whole range `0 < B < n/2` at `n = 1000` and
`n = 10⁵`: zero violations, and the ratio to `x²/2` bottoms out at `0.999999`,
so `x²/2` is essentially sharp. **The `1/w^{2B}` blow-up is beaten everywhere**;
no restriction beyond `a, B > 0` is needed for the deadline term. The
first-quarter condition `4B ≤ n` is needed only for the backslide coefficient.

Summing, `w^B + D_B ≤ 2 exp(−4 log(5/4) · B²/n)`, and under
`16B² ≥ γ n lg n` this is `2 exp(−(log(5/4)/4)·γ lg n)`.

## The constant is real but weak, and the asymptotic notation hides it

At `n = 10⁶`, `γ = 1` and the minimal admissible `B = 1117`:

```text
w^B = 0.2874     D_B = 0.2872     sum = 0.5745
bound 2exp(−(log(5/4)/4)·γ lg n) = 0.6579
```

The bound holds, and is **greater than 1/2**. Since `log(5/4)/4 ≈ 0.0558`, the
statement has content only once `γ lg n > 4 log 2 / log(5/4) ≈ 24.8` — at
`n = 10⁶` that means `γ ≥ 2`.

So `exp(−Ω(γ lg n))` is honest, but the paper's "for every constant `γ ≥ 1`"
should be read with the threshold in mind. This is the same category as the
Lemma 12 erratum: an `Ω(·)` that is true and whose constant matters.
-/

/-- **The exact tilt identity.**  At the band parameters, in terms of `x = B/n`
(equivalently `2B` against `a + 2B = n`),

`1 − 1/η = x²(3+2x)/(2(1+x))`

This is the algebraic core of the deadline bound: with `log z ≥ 1 − 1/z` it
gives `log η ≥ x²(3+2x)/(2(1+x))`, which is what beats the `1/w^{2B}`
blow-up. -/
theorem heavyBandEta_inv_identity {a B : ℕ} (ha : 0 < a) (hB : 0 < B) :
    1 - 1 / heavyBandEta a B
      = ((B : ℝ) / ((a : ℝ) + 2 * (B : ℝ))) ^ 2
          * (3 + 2 * ((B : ℝ) / ((a : ℝ) + 2 * (B : ℝ))))
        / (2 * (1 + (B : ℝ) / ((a : ℝ) + 2 * (B : ℝ)))) := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  unfold heavyBandEta heavyBandW heavyBandU
  have h1 : (0 : ℝ) < (a : ℝ) + 4 * (B : ℝ) := by positivity
  have h2 : (0 : ℝ) < (a : ℝ) + 3 * (B : ℝ) := by positivity
  have h3 : (0 : ℝ) < (a : ℝ) + 2 * (B : ℝ) := by positivity
  field_simp
  ring

/-! ### The deadline exponent, derivative-free

The sharp route needs `log(1+x) ≤ x(2+x)/(2(1+x))`, which is a derivative
argument.  It is not necessary.  Using only the CRUDE `log(1+x) ≤ x` together
with the tilt identity and `log z ≥ 1 − 1/z`:

```text
log η − x·log(1+x)  ≥  x²(3+2x)/(2(1+x)) − x²  =  x²/(2(1+x))
```

and the middle step is an **equality**, not an estimate — multiplying by
`2(1+x)` gives `x²` on both sides.

The crude route loses nothing as `x → 0` (both give `x²/2` in the limit) and at
worst a factor `2/3` at `x = 1/2`.  Verified numerically on `0 < B < n/2` at two
scales: zero violations, and the margin against `x²/3` bottoms out at exactly
`1.5`, i.e. the bound `x²/(2(1+x))` is attained.

Trading a factor `2/3` on an already-weak exponent to avoid a derivative
argument entirely is the right trade here.
-/

/-- Mathlib already has this as `Real.one_sub_inv_le_log_of_pos`; kept as a
`1/z`-shaped alias because the tilt identity is stated with `1/η`. -/
theorem log_ge_one_sub_inv {z : ℝ} (hz : 0 < z) : 1 - 1 / z ≤ Real.log z := by
  have h := Real.one_sub_inv_le_log_of_pos hz
  rwa [← one_div] at h

theorem heavyBandEta_pos {a B : ℕ} (ha : 0 < a) (hB : 0 < B) :
    0 < heavyBandEta a B := by
  obtain ⟨hu, huw, hw⟩ := heavyBand_tail_regime ha hB
  have hwpos : 0 < heavyBandW a B := lt_trans hu huw
  unfold heavyBandEta
  have : 0 < heavyBandU a B + heavyBandW a B ^ 2 := by positivity
  positivity

/-- **The deadline exponent, derivative-free.**

`log η − x·log(1+x) ≥ x²/(2(1+x))`, using only the exact tilt identity,
`log z ≥ 1 − 1/z`, and the CRUDE `log(1+x) ≤ x`.

The sharper `log(1+x) ≤ x(2+x)/(2(1+x))` would give `x²/2` instead, but it
needs a derivative argument.  The crude route loses nothing as `x → 0` (both
give `x²/2` in the limit) and at worst a factor `2/3` at `x = 1/2`, which is
cheap against an exponent that is already the weak link. -/
theorem heavyBand_deadline_exponent {a B : ℕ} (ha : 0 < a) (hB : 0 < B) :
    (((B : ℝ) / ((a : ℝ) + 2 * (B : ℝ))) ^ 2)
        / (2 * (1 + (B : ℝ) / ((a : ℝ) + 2 * (B : ℝ))))
      ≤ Real.log (heavyBandEta a B)
        - ((B : ℝ) / ((a : ℝ) + 2 * (B : ℝ)))
          * Real.log (1 + (B : ℝ) / ((a : ℝ) + 2 * (B : ℝ))) := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  set x : ℝ := (B : ℝ) / ((a : ℝ) + 2 * (B : ℝ)) with hx
  have hxpos : 0 < x := by rw [hx]; positivity
  have h1x : (0 : ℝ) < 1 + x := by linarith
  -- lower bound on log eta via the identity
  have hlog : x ^ 2 * (3 + 2 * x) / (2 * (1 + x)) ≤ Real.log (heavyBandEta a B) := by
    have := log_ge_one_sub_inv (heavyBandEta_pos ha hB)
    rwa [heavyBandEta_inv_identity ha hB] at this
  -- crude upper bound on log (1+x)
  have hlog1x : Real.log (1 + x) ≤ x := by
    have := Real.log_le_sub_one_of_pos h1x
    linarith
  have hmul : x * Real.log (1 + x) ≤ x * x :=
    mul_le_mul_of_nonneg_left hlog1x (le_of_lt hxpos)
  -- this is in fact an EQUALITY: multiplying by 2(1+x) gives x² on both sides
  have hkey : x ^ 2 / (2 * (1 + x))
      = x ^ 2 * (3 + 2 * x) / (2 * (1 + x)) - x * x := by
    field_simp
    ring
  linarith

/-! ### The SHARP exponent, still derivative-free

The crude route above trades a factor `2/3`.  It need not: `log(1+x) ≤ x` can be
replaced by the Padé-type bound

```text
log(1+x) ≤ x(2+x)/(2(1+x))
```

with **no derivative argument**, via `y ≤ sinh y` for `y ≥ 0`:

```text
log(1+x) ≤ sinh(log(1+x)) = ((1+x) − (1+x)⁻¹)/2 = x(2+x)/(2(1+x))
```

using `Real.self_le_sinh_iff` and `Real.sinh_log`.  That recovers the full
`x²/2`, so the deadline bound is `exp(−B²/n)` after all.

I had derived this substitution independently — `t = 1+x`, then `t = e^y`
reduces the claim to `y ≤ sinh y` — but abandoned it after failing to locate the
Mathlib lemma.  A dispatched round supplied the name.  The crude version is kept
below it because it documents what the trade would have cost.
-/

/-- **The sharp Pade-type bound, derivative-free.**  `log(1+x) ≤ sinh(log(1+x))`
because `log(1+x) ≥ 0`, and `sinh ∘ log` has the closed form `(z − z⁻¹)/2`. -/
theorem log_one_add_le_pade {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x * (2 + x) / (2 * (1 + x)) := by
  have hx1 : (0 : ℝ) < 1 + x := by linarith
  calc Real.log (1 + x) ≤ Real.sinh (Real.log (1 + x)) := by
        rw [Real.self_le_sinh_iff]
        exact Real.log_nonneg (by linarith)
    _ = ((1 + x) - (1 + x)⁻¹) / 2 := Real.sinh_log hx1
    _ = x * (2 + x) / (2 * (1 + x)) := by field_simp; ring

/-- **The sharp deadline exponent.**  `log η − x·log(1+x) ≥ x²/2`, recovering
the factor `3/2` the crude route gave away. -/
theorem heavyBand_deadline_exponent_sharp {a B : ℕ} (ha : 0 < a) (hB : 0 < B) :
    ((B : ℝ) / ((a : ℝ) + 2 * (B : ℝ))) ^ 2 / 2
      ≤ Real.log (heavyBandEta a B)
        - ((B : ℝ) / ((a : ℝ) + 2 * (B : ℝ)))
          * Real.log (1 + (B : ℝ) / ((a : ℝ) + 2 * (B : ℝ))) := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  set x : ℝ := (B : ℝ) / ((a : ℝ) + 2 * (B : ℝ)) with hx
  have hxpos : 0 < x := by rw [hx]; positivity
  have h1x : (0 : ℝ) < 1 + x := by linarith
  have hlog : x ^ 2 * (3 + 2 * x) / (2 * (1 + x)) ≤ Real.log (heavyBandEta a B) := by
    have h := Real.one_sub_inv_le_log_of_pos (heavyBandEta_pos ha hB)
    rw [← one_div] at h
    rwa [heavyBandEta_inv_identity ha hB] at h
  have hpade := log_one_add_le_pade (le_of_lt hxpos)
  have hmul : x * Real.log (1 + x) ≤ x * (x * (2 + x) / (2 * (1 + x))) :=
    mul_le_mul_of_nonneg_left hpade (le_of_lt hxpos)
  have hkey : x ^ 2 / 2
      = x ^ 2 * (3 + 2 * x) / (2 * (1 + x)) - x * (x * (2 + x) / (2 * (1 + x))) := by
    field_simp
    ring
  linarith

/-! ### From the exponent to the complete band error

The remaining bookkeeping is now explicit.  With
`n = a + 2B` and `x = B/n`,

```text
w = 1/(1+x)
1/(w^(2B) η^(2n))
  = exp(-2n (log η - x log(1+x)))
  ≤ exp(-B²/n).
```

On the first-quarter range, concavity of `log` on the chord from `1` to
`5/4` gives the matching backslide estimate

```text
w^B ≤ exp(-4 log(5/4) B²/n).
```

Since `4 log(5/4) ≤ 1`, the backslide exponent is the common bottleneck.
-/

/-- The chord bound for `log` between `1` and `5/4`. -/
theorem log_one_add_ge_quarter_chord {x : ℝ}
    (hx0 : 0 ≤ x) (hxq : x ≤ 1 / 4) :
    4 * Real.log ((5 : ℝ) / 4) * x ≤ Real.log (1 + x) := by
  have hconc := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show ((5 : ℝ) / 4) ∈ Set.Ioi 0 by norm_num)
    (show 0 ≤ 1 - 4 * x by linarith)
    (show 0 ≤ 4 * x by positivity)
    (show (1 - 4 * x) + 4 * x = (1 : ℝ) by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at hconc
  calc
    4 * Real.log ((5 : ℝ) / 4) * x
        = 4 * x * Real.log ((5 : ℝ) / 4) := by ring
    _ ≤ Real.log ((1 - 4 * x) * 1 + 4 * x * ((5 : ℝ) / 4)) := hconc
    _ = Real.log (1 + x) := by
      congr 1
      ring

/-- At the band parameters, `w = 1/(1+B/n)` with `n = a+2B`. -/
theorem heavyBandW_eq_one_div {a B : ℕ} (ha : 0 < a) (hB : 0 < B) :
    heavyBandW a B =
      1 / (1 + (B : ℝ) / ((a : ℝ) + 2 * (B : ℝ))) := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  unfold heavyBandW
  field_simp
  ring

/-- **The deadline term.**  The exact power quotient is at most
`exp(-B²/n)` throughout the full admissible range `a,B > 0`. -/
theorem heavyBand_deadline_term {n a B : ℕ} (ha : 0 < a) (hB : 0 < B)
    (hparam : a + 2 * B = n) :
    1 / (heavyBandW a B ^ (2 * B) * heavyBandEta a B ^ (2 * n))
      ≤ Real.exp (-((B : ℝ) ^ 2 / (n : ℝ))) := by
  subst n
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  let x : ℝ := (B : ℝ) / ((a : ℝ) + 2 * (B : ℝ))
  let nR : ℝ := (a : ℝ) + 2 * (B : ℝ)
  have hnR : 0 < nR := by
    dsimp [nR]
    positivity
  have hx : x = (B : ℝ) / nR := by rfl
  have hw : heavyBandW a B = 1 / (1 + x) := by
    dsimp only [x]
    exact heavyBandW_eq_one_div ha hB
  have hxpos : 0 < x := by
    rw [hx]
    positivity
  have hwpos : 0 < heavyBandW a B := by
    rw [hw]
    positivity
  have hηpos : 0 < heavyBandEta a B := heavyBandEta_pos ha hB
  have hdenpos :
      0 < heavyBandW a B ^ (2 * B) *
        heavyBandEta a B ^ (2 * (a + 2 * B)) := by
    positivity
  have hlog :
      Real.log
          (1 / (heavyBandW a B ^ (2 * B) *
            heavyBandEta a B ^ (2 * (a + 2 * B))))
        = -2 * nR *
            (Real.log (heavyBandEta a B) - x * Real.log (1 + x)) := by
    rw [Real.log_div one_ne_zero (ne_of_gt hdenpos), Real.log_one,
      Real.log_mul (pow_ne_zero _ (ne_of_gt hwpos))
        (pow_ne_zero _ (ne_of_gt hηpos)),
      Real.log_pow, Real.log_pow, hw, one_div, Real.log_inv]
    push_cast
    rw [hx]
    field_simp
    ring
  have hexponent :
      -2 * nR *
          (Real.log (heavyBandEta a B) - x * Real.log (1 + x))
        ≤ -((B : ℝ) ^ 2 / nR) := by
    have hsharp := heavyBand_deadline_exponent_sharp ha hB
    change x ^ 2 / 2 ≤
      Real.log (heavyBandEta a B) - x * Real.log (1 + x) at hsharp
    have hmul := mul_le_mul_of_nonpos_left hsharp
      (by nlinarith [hnR] : -2 * nR ≤ 0)
    rw [hx] at hmul
    calc
      -2 * nR *
          (Real.log (heavyBandEta a B) - x * Real.log (1 + x))
          ≤ -2 * nR * (((B : ℝ) / nR) ^ 2 / 2) := hmul
      _ = -((B : ℝ) ^ 2 / nR) := by field_simp
  calc
    1 / (heavyBandW a B ^ (2 * B) *
          heavyBandEta a B ^ (2 * (a + 2 * B)))
        = Real.exp
            (Real.log
              (1 / (heavyBandW a B ^ (2 * B) *
                heavyBandEta a B ^ (2 * (a + 2 * B))))) := by
            rw [Real.exp_log]
            positivity
    _ = Real.exp
          (-2 * nR *
            (Real.log (heavyBandEta a B) - x * Real.log (1 + x))) := by
          rw [hlog]
    _ ≤ Real.exp (-((B : ℝ) ^ 2 / nR)) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.exp
          (-((B : ℝ) ^ 2 / ((a : ℝ) + 2 * (B : ℝ)))) := by rfl

/-- **The backslide term.**  On `4B ≤ n`, the chord bound for `log` yields
the uniform coefficient `4 log(5/4)`. -/
theorem heavyBand_backslide_term {n a B : ℕ} (ha : 0 < a) (hB : 0 < B)
    (hparam : a + 2 * B = n) (hquarter : 4 * B ≤ n) :
    heavyBandW a B ^ B
      ≤ Real.exp
          (-(4 * Real.log ((5 : ℝ) / 4)) *
            ((B : ℝ) ^ 2 / (n : ℝ))) := by
  subst n
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hBR : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  let x : ℝ := (B : ℝ) / ((a : ℝ) + 2 * (B : ℝ))
  let nR : ℝ := (a : ℝ) + 2 * (B : ℝ)
  have hnR : 0 < nR := by
    dsimp [nR]
    positivity
  have hx : x = (B : ℝ) / nR := by rfl
  have hw : heavyBandW a B = 1 / (1 + x) := by
    dsimp only [x]
    exact heavyBandW_eq_one_div ha hB
  have hwpos : 0 < heavyBandW a B := by
    rw [hw]
    positivity
  have hx0 : 0 ≤ x := by
    rw [hx]
    positivity
  have hquarterR : (4 : ℝ) * (B : ℝ) ≤ nR := by
    dsimp only [nR]
    exact_mod_cast hquarter
  have hxq : x ≤ 1 / 4 := by
    rw [hx, div_le_iff₀ hnR]
    nlinarith
  have hchord := log_one_add_ge_quarter_chord hx0 hxq
  have hexponent :
      -(B : ℝ) * Real.log (1 + x)
        ≤ -(4 * Real.log ((5 : ℝ) / 4)) *
            ((B : ℝ) ^ 2 / nR) := by
    have hmul := mul_le_mul_of_nonpos_left hchord
      (neg_nonpos.mpr (Nat.cast_nonneg B))
    rw [hx] at hmul
    calc
      -(B : ℝ) * Real.log (1 + x)
          ≤ -(B : ℝ) *
              (4 * Real.log ((5 : ℝ) / 4) * ((B : ℝ) / nR)) := hmul
      _ = -(4 * Real.log ((5 : ℝ) / 4)) *
            ((B : ℝ) ^ 2 / nR) := by ring
  calc
    heavyBandW a B ^ B
        = Real.exp ((B : ℝ) * Real.log (heavyBandW a B)) := by
            rw [Real.exp_nat_mul, Real.exp_log hwpos]
    _ = Real.exp (-(B : ℝ) * Real.log (1 + x)) := by
          congr 1
          rw [hw, one_div, Real.log_inv]
          ring
    _ ≤ Real.exp
          (-(4 * Real.log ((5 : ℝ) / 4)) *
            ((B : ℝ) ^ 2 / nR)) := Real.exp_le_exp.mpr hexponent
    _ = Real.exp
          (-(4 * Real.log ((5 : ℝ) / 4)) *
            ((B : ℝ) ^ 2 / ((a : ℝ) + 2 * (B : ℝ)))) := by rfl

/-- The two exact Heavy-B band terms have the common backslide exponent. -/
theorem heavyBand_terms_exp {n a B : ℕ} (ha : 0 < a) (hB : 0 < B)
    (hparam : a + 2 * B = n) (hquarter : 4 * B ≤ n) :
    heavyBandW a B ^ B +
        1 / (heavyBandW a B ^ (2 * B) * heavyBandEta a B ^ (2 * n))
      ≤ 2 * Real.exp
          (-(4 * Real.log ((5 : ℝ) / 4)) *
            ((B : ℝ) ^ 2 / (n : ℝ))) := by
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hback := heavyBand_backslide_term ha hB hparam hquarter
  have hdeadline := heavyBand_deadline_term ha hB hparam
  have hc : 4 * Real.log ((5 : ℝ) / 4) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 5 / 4)
    norm_num at h ⊢
    linarith
  have hq0 : 0 ≤ (B : ℝ) ^ 2 / (n : ℝ) := by positivity
  have hexponent :
      -((B : ℝ) ^ 2 / (n : ℝ))
        ≤ -(4 * Real.log ((5 : ℝ) / 4)) *
            ((B : ℝ) ^ 2 / (n : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hc hq0
    nlinarith
  have hdeadline' :
      Real.exp (-((B : ℝ) ^ 2 / (n : ℝ)))
        ≤ Real.exp
            (-(4 * Real.log ((5 : ℝ) / 4)) *
              ((B : ℝ) ^ 2 / (n : ℝ))) :=
    Real.exp_le_exp.mpr hexponent
  calc
    heavyBandW a B ^ B +
          1 / (heavyBandW a B ^ (2 * B) *
            heavyBandEta a B ^ (2 * n))
        ≤ Real.exp
              (-(4 * Real.log ((5 : ℝ) / 4)) *
                ((B : ℝ) ^ 2 / (n : ℝ))) +
            Real.exp (-((B : ℝ) ^ 2 / (n : ℝ))) :=
      add_le_add hback hdeadline
    _ ≤ Real.exp
            (-(4 * Real.log ((5 : ℝ) / 4)) *
              ((B : ℝ) ^ 2 / (n : ℝ))) +
          Real.exp
            (-(4 * Real.log ((5 : ℝ) / 4)) *
              ((B : ℝ) ^ 2 / (n : ℝ)) ) :=
      add_le_add (le_refl _) hdeadline'
    _ = 2 * Real.exp
          (-(4 * Real.log ((5 : ℝ) / 4)) *
            ((B : ℝ) ^ 2 / (n : ℝ))) := by ring

/-- Under `γ lgN · n ≤ 16B²`, the two terms have exponent
`-(log(5/4)/4) γ lgN`. -/
theorem heavyBand_terms_exp_scale {n a B : ℕ} (gamma lgN : ℝ)
    (ha : 0 < a) (hB : 0 < B) (hparam : a + 2 * B = n)
    (hquarter : 4 * B ≤ n)
    (hstage : gamma * lgN * (n : ℝ) ≤ 16 * (B : ℝ) ^ 2) :
    heavyBandW a B ^ B +
        1 / (heavyBandW a B ^ (2 * B) * heavyBandEta a B ^ (2 * n))
      ≤ 2 * Real.exp
          (-(Real.log ((5 : ℝ) / 4) / 4) * (gamma * lgN)) := by
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hterms := heavyBand_terms_exp ha hB hparam hquarter
  have hrate' :
      gamma * lgN ≤ (16 * (B : ℝ) ^ 2) / (n : ℝ) :=
    (le_div_iff₀ hnR).2 hstage
  have hrate :
      gamma * lgN ≤ 16 * ((B : ℝ) ^ 2 / (n : ℝ)) := by
    calc
      gamma * lgN ≤ (16 * (B : ℝ) ^ 2) / (n : ℝ) := hrate'
      _ = 16 * ((B : ℝ) ^ 2 / (n : ℝ)) := by ring
  have hlog0 : 0 ≤ Real.log ((5 : ℝ) / 4) :=
    Real.log_nonneg (by norm_num)
  have hcoeff : -(Real.log ((5 : ℝ) / 4) / 4) ≤ 0 :=
    neg_nonpos.mpr (div_nonneg hlog0 (by norm_num : (0 : ℝ) ≤ 4))
  have hmul := mul_le_mul_of_nonpos_left hrate hcoeff
  have hexponent :
      -(4 * Real.log ((5 : ℝ) / 4)) * ((B : ℝ) ^ 2 / (n : ℝ))
        ≤ -(Real.log ((5 : ℝ) / 4) / 4) * (gamma * lgN) := by
    calc
      -(4 * Real.log ((5 : ℝ) / 4)) *
            ((B : ℝ) ^ 2 / (n : ℝ))
          = -(Real.log ((5 : ℝ) / 4) / 4) *
              (16 * ((B : ℝ) ^ 2 / (n : ℝ))) := by ring
      _ ≤ -(Real.log ((5 : ℝ) / 4) / 4) * (gamma * lgN) := hmul
  calc
    heavyBandW a B ^ B +
          1 / (heavyBandW a B ^ (2 * B) *
            heavyBandEta a B ^ (2 * n))
        ≤ 2 * Real.exp
            (-(4 * Real.log ((5 : ℝ) / 4)) *
              ((B : ℝ) ^ 2 / (n : ℝ))) :=
      hterms
    _ ≤ 2 * Real.exp
          (-(Real.log ((5 : ℝ) / 4) / 4) * (gamma * lgN)) := by
      gcongr

/-! The probability tails live in `ℝ≥0∞`; the following lemmas transfer the
real estimates through `ENNReal.ofReal` and expose the final union-bound
interface. -/

/-- The exact sum of the two real terms commutes with `ENNReal.ofReal`. -/
theorem heavyBand_terms_ofReal {n a B : ℕ} (ha : 0 < a) (hB : 0 < B) :
    ENNReal.ofReal
        (heavyBandW a B ^ B +
          1 / (heavyBandW a B ^ (2 * B) * heavyBandEta a B ^ (2 * n)))
      = ENNReal.ofReal (heavyBandW a B) ^ B +
          1 / (ENNReal.ofReal (heavyBandW a B) ^ (2 * B) *
            ENNReal.ofReal (heavyBandEta a B) ^ (2 * n)) := by
  have hwpos : 0 < heavyBandW a B := by
    obtain ⟨hu, huw, -⟩ := heavyBand_tail_regime ha hB
    exact hu.trans huw
  have hw0 : 0 ≤ heavyBandW a B := hwpos.le
  have hηpos : 0 < heavyBandEta a B := heavyBandEta_pos ha hB
  have hη0 : 0 ≤ heavyBandEta a B := hηpos.le
  have hdenpos :
      0 < heavyBandW a B ^ (2 * B) *
        heavyBandEta a B ^ (2 * n) :=
    mul_pos (pow_pos hwpos _) (pow_pos hηpos _)
  calc
    ENNReal.ofReal
          (heavyBandW a B ^ B +
            1 / (heavyBandW a B ^ (2 * B) *
              heavyBandEta a B ^ (2 * n)))
        = ENNReal.ofReal (heavyBandW a B ^ B) +
            ENNReal.ofReal
              (1 / (heavyBandW a B ^ (2 * B) *
                heavyBandEta a B ^ (2 * n))) := by
          rw [ENNReal.ofReal_add (pow_nonneg hw0 B)]
          positivity
    _ = ENNReal.ofReal (heavyBandW a B) ^ B +
          1 / (ENNReal.ofReal (heavyBandW a B) ^ (2 * B) *
            ENNReal.ofReal (heavyBandEta a B) ^ (2 * n)) := by
          rw [ENNReal.ofReal_pow hw0,
            ENNReal.ofReal_div_of_pos hdenpos, ENNReal.ofReal_one,
            ENNReal.ofReal_mul (pow_nonneg hw0 (2 * B)),
            ENNReal.ofReal_pow hw0, ENNReal.ofReal_pow hη0]

/-- The deadline estimate in the probability codomain. -/
theorem heavyBand_deadline_term_ennreal {n a B : ℕ}
    (ha : 0 < a) (hB : 0 < B) (hparam : a + 2 * B = n) :
    1 / (ENNReal.ofReal (heavyBandW a B) ^ (2 * B) *
        ENNReal.ofReal (heavyBandEta a B) ^ (2 * n))
      ≤ ENNReal.ofReal (Real.exp (-((B : ℝ) ^ 2 / (n : ℝ)))) := by
  have hwpos : 0 < heavyBandW a B := by
    obtain ⟨hu, huw, -⟩ := heavyBand_tail_regime ha hB
    exact hu.trans huw
  have hw0 : 0 ≤ heavyBandW a B := hwpos.le
  have hηpos : 0 < heavyBandEta a B := heavyBandEta_pos ha hB
  have hη0 : 0 ≤ heavyBandEta a B := hηpos.le
  have hdenpos :
      0 < heavyBandW a B ^ (2 * B) *
        heavyBandEta a B ^ (2 * n) :=
    mul_pos (pow_pos hwpos _) (pow_pos hηpos _)
  have h := ENNReal.ofReal_le_ofReal
    (heavyBand_deadline_term ha hB hparam)
  rw [ENNReal.ofReal_div_of_pos hdenpos, ENNReal.ofReal_one,
    ENNReal.ofReal_mul (pow_nonneg hw0 (2 * B)),
    ENNReal.ofReal_pow hw0, ENNReal.ofReal_pow hη0] at h
  exact h

/-- The backslide estimate in the probability codomain. -/
theorem heavyBand_backslide_term_ennreal {n a B : ℕ}
    (ha : 0 < a) (hB : 0 < B) (hparam : a + 2 * B = n)
    (hquarter : 4 * B ≤ n) :
    ENNReal.ofReal (heavyBandW a B) ^ B
      ≤ ENNReal.ofReal
          (Real.exp
            (-(4 * Real.log ((5 : ℝ) / 4)) *
              ((B : ℝ) ^ 2 / (n : ℝ)))) := by
  have hw0 : 0 ≤ heavyBandW a B := by
    obtain ⟨hu, huw, -⟩ := heavyBand_tail_regime ha hB
    exact (hu.trans huw).le
  have h := ENNReal.ofReal_le_ofReal
    (heavyBand_backslide_term ha hB hparam hquarter)
  rw [ENNReal.ofReal_pow hw0] at h
  exact h

/-- The exact two-term estimate in the probability codomain. -/
theorem heavyBand_terms_exp_ennreal {n a B : ℕ}
    (ha : 0 < a) (hB : 0 < B) (hparam : a + 2 * B = n)
    (hquarter : 4 * B ≤ n) :
    ENNReal.ofReal (heavyBandW a B) ^ B +
        1 / (ENNReal.ofReal (heavyBandW a B) ^ (2 * B) *
          ENNReal.ofReal (heavyBandEta a B) ^ (2 * n))
      ≤ ENNReal.ofReal
          (2 * Real.exp
            (-(4 * Real.log ((5 : ℝ) / 4)) *
              ((B : ℝ) ^ 2 / (n : ℝ)))) := by
  rw [← heavyBand_terms_ofReal ha hB]
  exact ENNReal.ofReal_le_ofReal
    (heavyBand_terms_exp ha hB hparam hquarter)

/-- **Heavy-B's assembled band error.**  Any backslide and deadline masses
bounded by the two exact terms inherit the scaled common exponential bound. -/
theorem heavy_band_error_exp {n a B : ℕ} (gamma lgN : ℝ)
    (backMass deadlineMass : ENNReal)
    (ha : 0 < a) (hB : 0 < B) (hparam : a + 2 * B = n)
    (hquarter : 4 * B ≤ n)
    (hstage : gamma * lgN * (n : ℝ) ≤ 16 * (B : ℝ) ^ 2)
    (hback : backMass ≤ ENNReal.ofReal (heavyBandW a B) ^ B)
    (hdeadline :
      deadlineMass ≤
        1 / (ENNReal.ofReal (heavyBandW a B) ^ (2 * B) *
          ENNReal.ofReal (heavyBandEta a B) ^ (2 * n))) :
    backMass + deadlineMass ≤
      ENNReal.ofReal
        (2 * Real.exp
          (-(Real.log ((5 : ℝ) / 4) / 4) * (gamma * lgN))) := by
  refine (add_le_add hback hdeadline).trans ?_
  rw [← heavyBand_terms_ofReal ha hB]
  exact ENNReal.ofReal_le_ofReal
    (heavyBand_terms_exp_scale gamma lgN ha hB hparam hquarter hstage)

end Tri

#print axioms Tri.heavyBandU_lt_W
#print axioms Tri.heavyBand_tail_regime
#print axioms Tri.eta_ge_one_real
#print axioms Tri.heavyBandEta_ge_one
#print axioms Tri.heavyBandW_le_eta
#print axioms Tri.heavy_backslide_tail
#print axioms Tri.heavyQuotaDeadline_subset
#print axioms Tri.heavy_deadline_tail
#print axioms Tri.heavyBandEta_inv_identity
#print axioms Tri.log_ge_one_sub_inv
#print axioms Tri.heavyBand_deadline_exponent
#print axioms Tri.log_one_add_le_pade
#print axioms Tri.heavyBand_deadline_exponent_sharp
#print axioms Tri.log_one_add_ge_quarter_chord
#print axioms Tri.heavyBandW_eq_one_div
#print axioms Tri.heavyBand_deadline_term
#print axioms Tri.heavyBand_backslide_term
#print axioms Tri.heavyBand_terms_exp
#print axioms Tri.heavyBand_terms_exp_scale
#print axioms Tri.heavyBand_terms_ofReal
#print axioms Tri.heavyBand_deadline_term_ennreal
#print axioms Tri.heavyBand_backslide_term_ennreal
#print axioms Tri.heavyBand_terms_exp_ennreal
#print axioms Tri.heavy_band_error_exp
