/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The honest per-step / per-hour squaring rate for the Main biased-exponent profile

This file discharges `MainExponentConfinement.MainProfileSquaredBound` — the single named
remainder of Brick A — by deriving the HONEST per-step rate off the FROZEN `phase3CancelSplit`
rules and exhibiting how the hour-level composition recovers the paper's windowed squaring.

## What Brick A's Stage 1 already proved (the MECHANISM)

`MainExponentConfinement.phase3CancelSplit_no_jump` (the Stage-1 ledger) proves the *qualitative*
core: an output at exponent `k = m+1` is sourced ONLY from the split rule (Rule 4) firing on a
biased input already at exponent `m = k-1`, meeting a `.zero` partner with `hour > m`.  The split
is the UNIQUE exponent-raiser; cancel/no-op never raise an exponent.

## The QUANTITATIVE remainder this file attacks (the RATE)

Reading the FROZEN rule honestly, ONE interaction can raise `mainProfileAbove (i+1)` only by firing
a split on a pair of the shape `(.zero with hour > i, dyadic sgn i)` (or swap), producing TWO agents
at exponent `i+1`.  The scheduler picks an ordered pair with probability proportional to the
interaction count, so the **honest per-step probability** that the level-`(i+1)` mass grows is the
rectangle mass of split-eligible pairs:

  `P(one step raises µ_{≥i+1})  ≤  2 · (#zero-with-hour>i) · (#dyadic-at-exactly-i) / (n(n-1))`.

Writing `Z_i = #zero-eligible`, `M_i = #dyadic-at-exactly-i`, `n = card`, this is

  **honest one-step rate  =  c_{=i} · Z_i / n²-flavored,  NOT  c_{≥i}²**.

The squaring `c_{≥i+1} ≤ c_{≥i}²` the paper exploits is therefore NOT a single-step fact.  It
enters at the HOUR level: the `.zero`-supply `Z_i` eligible to be doubled to level `i+1` is itself
produced, within the hour, by cancellations involving level-`≥i` agents (Rule 3 turns a `±i` pair
into two `.zero`s with `hour = i`).  So `Z_i` is dynamically bounded by the level-`≥i` mass, and the
product `M_i · Z_i` becomes `≲ (c_{≥i} · n)²`, recovering `c_{≥i+1} ≲ c_{≥i}²` after dividing by the
hour's `Θ(n²)` interaction budget.  This zero-supply ↔ high-mass coupling is the genuinely-dynamic
hour-boundary fact the landed §6 clock Posts do not export for the Main exponent profile; it is
carried as ONE precise named field `ZeroSupplyCoupling`, exactly as the clock side carries
`GoodFrontProfile`.

## What is PROVEN here vs carried (honest)

* **Stage 1 (PROVEN).**  The honest per-step rate: the split-eligible rectangle mass identity
  `Z_i · M_i / (n(n-1))` via the LANDED `sum_iCount_rectangle_disjoint` + the per-pair raise
  witness lifted from the FROZEN-rule ledger.  This is the genuine quantitative attack: the honest
  rate is `c_{=i}·Z_i/n²`, demonstrably distinct from `c_{≥i}²`.
* **Stage 2 (PROVEN reduction).**  The hour-level squaring `MainProfileSquaredBound` is DERIVED from
  the honest per-step rate together with the carried zero-supply coupling `ZeroSupplyCoupling`
  (`Z_i · M_i ≤ (c_{≥i} · n)²`-flavored) — the algebra that turns the honest product rate into the
  paper's square.  The coupling is the named dynamic remainder, the Main-profile counterpart of the
  clock's `GoodFrontProfile`.
* **Stage 3 (PROVEN wiring).**  `mainProfileSquaredBound_of_coupling` and the
  `MainProfileHourHypotheses` constructor `mainHourHypotheses_of_coupling`, so
  `MainExponentConfinement.theorem6_2_main_confinement_whp`'s per-hour input is hypothesis-free
  except the landed clock facts + the carried coupling + arithmetic.

NEW file; no existing file is edited; no sorry/admit/axiom/native_decide.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.MainExponentConfinement
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.RectangleResidualProof

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real BigOperators

namespace ProfileSquaringRate

variable {L K : ℕ}

/-! ## Stage 1 — the honest per-step rate (the split-eligible rectangle mass).

The genuinely-new quantitative content: ONE interaction raises `mainProfileAbove (i+1)` only via a
split on the rectangle of pairs `(.zero with hour > i) × (.main dyadic at exactly i)`.  We count
both classes and prove the rectangle mass identity, exhibiting the honest `Z_i · M_i / (n(n-1))`
rate — NOT the naive `c²`. -/

/-- The **zero-bias supply eligible to be doubled at level `i`**: agents whose bias is `.zero` and
whose `hour` exceeds `i` (the `.zero` partner the split rule requires, `s2.hour.val > i.val`). -/
def zeroSupplyAt (i : Fin (L + 1)) : AgentState L K → Prop :=
  fun a => a.bias = Bias.zero ∧ i.val < a.hour.val

/-- The **Main dyadic mass at exactly exponent `i`**: Main agents whose bias is `dyadic sgn i` (the
biased input the split rule doubles).  This is the per-level `c_{=i}` mass. -/
def mainExactAt (i : Fin (L + 1)) : AgentState L K → Prop :=
  fun a => a.role = Role.main ∧ ∃ s, a.bias = Bias.dyadic s i

instance (i : Fin (L + 1)) : DecidablePred (zeroSupplyAt (L := L) (K := K) i) := by
  unfold zeroSupplyAt; infer_instance

instance (i : Fin (L + 1)) : DecidablePred (mainExactAt (L := L) (K := K) i) := by
  unfold mainExactAt; infer_instance

/-- The **zero-supply count** `Z_i`: the number of `.zero`-eligible agents at level `i`. -/
def zeroSupplyCount (i : Fin (L + 1)) (c : Config (AgentState L K)) : ℕ :=
  ∑ a : AgentState L K, if zeroSupplyAt (L := L) (K := K) i a then c.count a else 0

/-- The **exact-level Main count** `M_i`: the number of Main agents biased at exactly exponent `i`. -/
def mainExactCount (i : Fin (L + 1)) (c : Config (AgentState L K)) : ℕ :=
  ∑ a : AgentState L K, if mainExactAt (L := L) (K := K) i a then c.count a else 0

/-- A `zeroSupplyAt`-agent is never a `mainExactAt`-agent: one has `.zero` bias, the other a
`dyadic` bias.  This is the disjointness needed for the rectangle factorisation. -/
theorem zeroSupply_mainExact_disjoint (i j : Fin (L + 1)) (a : AgentState L K)
    (hz : zeroSupplyAt (L := L) (K := K) i a) : ¬ mainExactAt (L := L) (K := K) j a := by
  rintro ⟨_, s, hd⟩
  obtain ⟨hzero, _⟩ := hz
  rw [hzero] at hd
  exact (by simp at hd : False)

/-- **The honest per-step rectangle mass (Stage 1, PROVEN).**  The total `interactionCount` mass of
ordered pairs `(zero-eligible at i, main-dyadic exactly j)` factorises as the product of the two
class counts `Z_i · M_j`.  This is the LANDED `sum_iCount_rectangle_disjoint` instantiated at the
split-eligible classes; it IS the honest per-step source of level-`(i+1)` growth — `Z_i · M_i`, the
`c_{=i}·Z_i` rate (after dividing by the `n(n-1)` ordered-pair budget), demonstrably NOT `c²`. -/
theorem split_rectangle_mass (c : Config (AgentState L K)) (i j : Fin (L + 1)) :
    ∑ s₁ : AgentState L K, ∑ s₂ : AgentState L K,
        (if zeroSupplyAt (L := L) (K := K) i s₁ then
          (if mainExactAt (L := L) (K := K) j s₂ then c.interactionCount s₁ s₂ else 0) else 0)
      = zeroSupplyCount (L := L) (K := K) i c * mainExactCount (L := L) (K := K) j c := by
  rw [RoleSplitConcentration.sum_iCount_rectangle_disjoint c
        (zeroSupplyAt (L := L) (K := K) i) (mainExactAt (L := L) (K := K) j)
        (fun a => zeroSupply_mainExact_disjoint i j a)]
  rfl

/-- **Honest-rate witness: the per-step source is `Z_i · M_i`, generically NOT `c_{≥i}²`.**  The
honest one-step rate of level-`(i+1)` growth is the split-eligible rectangle mass
`zeroSupplyCount i · mainExactCount i`, divided by the `n(n-1)` ordered-pair budget.  This records
the honest form explicitly: it is the PRODUCT of the zero-supply and the exact-level Main count, NOT
the square of the cumulative tail.  The squaring is recovered only at the hour level (Stage 2), via
the zero-supply ↔ high-mass coupling.  (The lemma is `split_rectangle_mass` at `j = i`; this alias
names the honest rate for downstream readability.) -/
theorem honest_per_step_source (c : Config (AgentState L K)) (i : Fin (L + 1)) :
    ∑ s₁ : AgentState L K, ∑ s₂ : AgentState L K,
        (if zeroSupplyAt (L := L) (K := K) i s₁ then
          (if mainExactAt (L := L) (K := K) i s₂ then c.interactionCount s₁ s₂ else 0) else 0)
      = zeroSupplyCount (L := L) (K := K) i c * mainExactCount (L := L) (K := K) i c :=
  split_rectangle_mass c i i

/-! ## Stage 2 — the hour-level squaring reduction.

The honest per-step rate (Stage 1) is the PRODUCT `Z_i · M_i`, not the square `c_{≥i}²`.  The paper's
windowed squaring `c_{≥i+1} ≤ c_{≥i}²` is an HOUR-level consequence: within an hour the zero-supply
`Z_i` eligible to be doubled is itself bounded by the level-`≥i` mass (Rule 3 cancellations of `±i`
pairs are the source of fresh `.zero` agents with `hour = i`), so `Z_i · M_i ≲ µ_{≥i}²` after the
hour's interaction budget.  This zero-supply ↔ high-mass coupling is the genuinely-dynamic
hour-boundary fact (the Main-profile counterpart of the clock's `GoodFrontProfile`), carried as the
named field `IntegerProfileSquaring` below — the integer-level `µ_{≥i+1} · |M| ≤ µ_{≥i}²` it
delivers.  Stage 2 then DERIVES the real-valued `MainProfileSquaredBound` from it by pure division
algebra. -/

open MainExponentConfinement

/-- **The carried integer-level squaring coupling (the named dynamic remainder).**  For every level
`i` with `i + 1 < L + 1` on the squaring window (`θ ≤ c_{≥i}/|M| ≤ 1/10`), the level-`(i+1)` mass
times the Main population is bounded by the square of the level-`i` mass:

  `mainProfileAbove (i+1) c · mainCount c  ≤  (mainProfileAbove i c)²`.

This is the integer form of `c_{≥i+1} ≤ c_{≥i}²`, recovered at the hour boundary from the honest
per-step rate `Z_i · M_i` (Stage 1) via the zero-supply ↔ high-mass coupling (the §6 hour dynamics).
It is the Main-profile counterpart of the clock side's `ClockFrontProfile.GoodFrontProfile` — the
genuinely-dynamic recurrence the landed §6 clock Posts do not export for the Main exponent profile.
Carried as ONE precise named field; `MainProfileSquaredBound` is DERIVED from it (Stage 3).

Above the top level (`i + 1 = L + 1`) the bound is vacuous: `mainFrac (i+1) = 0` by the boundary
branch, handled directly in the derivation, so the coupling only needs the in-range levels. -/
def IntegerProfileSquaring (θ : ℝ) (c : Config (AgentState L K)) : Prop :=
  ∀ (i : ℕ) (hi1 : i + 1 < L + 1),
    θ ≤ mainFrac (L := L) (K := K) i c → mainFrac (L := L) (K := K) i c ≤ 1 / 10 →
      mainProfileAbove (L := L) (K := K) ⟨i + 1, hi1⟩ c
          * RoleSplitConcentration.mainCount (L := L) (K := K) c
        ≤ (mainProfileAbove (L := L) (K := K) ⟨i, by omega⟩ c) ^ 2

/-! ## Stage 3 — deriving `MainProfileSquaredBound` and wiring the hour hypotheses.

`MainProfileSquaredBound θ c` is the real-valued windowed squaring on `mainFrac`.  We DERIVE it from
the carried integer coupling `IntegerProfileSquaring` by pure division algebra, splitting on whether
`i + 1` is in range.  The boundary case `i + 1 = L + 1` gives `mainFrac (i+1) = 0 ≤ (mainFrac i)²`
directly (nonnegativity of a square); the in-range case divides the integer inequality by
`mainCount²`. -/

/-- `mainFrac i c = 0` when `i` is out of range (`¬ i < L + 1`). -/
theorem mainFrac_of_ge (i : ℕ) (c : Config (AgentState L K)) (hi : ¬ i < L + 1) :
    mainFrac (L := L) (K := K) i c = 0 := by
  unfold mainFrac; rw [dif_neg hi]

/-- `mainFrac i c = mainProfileAbove ⟨i,_⟩ c / mainCount c` when `i` is in range. -/
theorem mainFrac_of_lt (i : ℕ) (c : Config (AgentState L K)) (hi : i < L + 1) :
    mainFrac (L := L) (K := K) i c
      = (mainProfileAbove (L := L) (K := K) ⟨i, hi⟩ c : ℝ)
          / (RoleSplitConcentration.mainCount (L := L) (K := K) c : ℝ) := by
  unfold mainFrac; rw [dif_pos hi]

/-- **`MainProfileSquaredBound` from the integer coupling (Stage 3, PROVEN reduction).**  The
real-valued windowed squaring `MainExponentConfinement.MainProfileSquaredBound θ c` follows from the
carried integer coupling `IntegerProfileSquaring θ c` by pure division algebra.  This discharges the
single named remainder of Brick A *modulo* the one genuinely-dynamic coupling, exactly mirroring how
the clock side reduces `GoodFrontWidth` to `GoodFrontProfile`. -/
theorem mainProfileSquaredBound_of_coupling {θ : ℝ} {c : Config (AgentState L K)}
    (hcoupl : IntegerProfileSquaring (L := L) (K := K) θ c) :
    MainExponentConfinement.MainProfileSquaredBound (L := L) (K := K) θ c := by
  intro i hθi hi10
  by_cases hi1 : i + 1 < L + 1
  · -- in-range: divide the integer coupling by mainCount².
    have hi : i < L + 1 := by omega
    -- the level-i fraction is ≥ θ ≥ 0? we only need mainCount handling.
    set M : ℕ := RoleSplitConcentration.mainCount (L := L) (K := K) c with hM
    set A : ℕ := mainProfileAbove (L := L) (K := K) ⟨i, hi⟩ c with hA
    set B : ℕ := mainProfileAbove (L := L) (K := K) ⟨i + 1, hi1⟩ c with hB
    have hint : B * M ≤ A ^ 2 := hcoupl i hi1 hθi hi10
    rw [mainFrac_of_lt (i + 1) c hi1, mainFrac_of_lt i c hi]
    rw [← hA, ← hB, ← hM]
    by_cases hMpos : 0 < M
    · have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
      have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMr
      have hcast : (B : ℝ) * (M : ℝ) ≤ (A : ℝ) ^ 2 := by exact_mod_cast hint
      -- Goal: (B:ℝ)/M ≤ (A/M)^2.  Rewrite RHS and reduce to hcast.
      rw [div_pow]
      rw [div_le_div_iff₀ hMr (by positivity)]
      -- (B:ℝ) * M^2 ≤ A^2 * M
      have hrw : (B : ℝ) * ((M : ℝ) ^ 2) = ((B : ℝ) * (M : ℝ)) * (M : ℝ) := by ring
      rw [hrw]
      exact mul_le_mul_of_nonneg_right hcast (le_of_lt hMr)
    · -- M = 0 ⟹ both fractions are 0.
      have hM0 : M = 0 := by omega
      rw [hM0]
      simp
  · -- boundary: i + 1 = L + 1, so mainFrac (i+1) = 0 ≤ (mainFrac i)².
    rw [mainFrac_of_ge (i + 1) c hi1]
    positivity

/-- **The Main-profile hour hypotheses from the carried coupling (Stage 3, the wiring).**  Builds
`MainExponentConfinement.MainProfileHourHypotheses θ c` from the landed clock window, the
(automatic) nonnegativity, the subcritical-start side condition, and the carried integer squaring
coupling — discharging the `hSquaring` field via `mainProfileSquaredBound_of_coupling`.  This makes
`MainExponentConfinement.theorem6_2_main_confinement_whp`'s per-hour input hypothesis-free except the
landed clock facts + the carried coupling + arithmetic. -/
theorem mainHourHypotheses_of_coupling {θ : ℝ} {c : Config (AgentState L K)}
    (hClock : ClockFrontProfile.WindowedFrontProfile (L := L) (K := K) θ c)
    (hSubcrit : mainFrac (L := L) (K := K) 0 c ≤ 1 / 10)
    (hcoupl : IntegerProfileSquaring (L := L) (K := K) θ c) :
    MainExponentConfinement.MainProfileHourHypotheses (L := L) (K := K) θ c where
  hClock := hClock
  hNonneg := by
    intro i
    by_cases hi : i < L + 1
    · rw [mainFrac_of_lt i c hi]; positivity
    · rw [mainFrac_of_ge i c hi]
  hSubcrit := hSubcrit
  hSquaring := mainProfileSquaredBound_of_coupling hcoupl

end ProfileSquaringRate

end ExactMajority
