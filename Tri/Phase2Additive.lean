/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Phase2Reconciled
import Tri.Phase2Contract
import Tri.Phase2Inhabit
import Tri.BandReturn
import Tri.DirectionProgress

/-!
# The additive phase-2 stage (replaces the false single-`hfail` bridge)

The single-potential `Phase2Bridge.hfail` demands `actualFailure ≤ Markov`, which
is false because the upper-success freeze undercounts failure.  This
module builds the sound exact-time phase-2 stage as a two-sided stopped band with
three additive errors — `live + lowerRuin + upperReturn`:

* the buffered upper boundary sits at minority `q - q/16` (`q = n/2^(s+1)`), one
  half-stage-ish beyond the public checkpoint, so the upper-return width is
  `q/16` rather than `1`;
* the block is `8 n` interactions with the weakened band contraction
  `phase2BufferedDecay s = 1 - 21/2^(s+8)`;
* the first rung keeps precondition `Phase1Exit n` (nonzero lower safety width).

This file provides the definitions and the elementary geometry; the analytic
kernel and the composition follow.
-/

namespace Tri

open scoped ENNReal

/-! ## Section 1 — definitions -/

/-- Current dyadic minority scale `⌊n / 2^s⌋`. -/
def phase2Scale (n s : ℕ) : ℕ := n / 2 ^ s

/-- Next dyadic minority scale `q = ⌊n / 2^(s+1)⌋`. -/
def phase2NextScale (n s : ℕ) : ℕ := n / 2 ^ (s + 1)

/-- Lower boundary (guard failure `y ≥ ⌊n/4⌋+1`, i.e. `x ≤ n - ⌊n/4⌋ - 1`). -/
def phase2LowerLo (n : ℕ) : ℕ := n - n / 4 - 1

/-- Minority at the lower boundary. -/
def phase2LowerBHi (n : ℕ) : ℕ := n / 4 - 1

/-- Uniform lower safety width. -/
def phase2LowerGap (n : ℕ) : ℕ := n / 16

/-- Public next-stage lower boundary (checkpoint failure `y ≥ q+1`). -/
def phase2ReturnLo (n s : ℕ) : ℕ := n - phase2NextScale n s - 1

/-- Minority at the public checkpoint boundary. -/
def phase2ReturnBHi (n s : ℕ) : ℕ := phase2NextScale n s - 1

/-- Buffered upper-return width `q/16 + 1`. -/
def phase2UpperGap (n s : ℕ) : ℕ := phase2NextScale n s / 16 + 1

/-- Buffered upper boundary `x = (n - q - 1) + (q/16 + 1) = n - q + q/16`. -/
def phase2UpperHi (n s : ℕ) : ℕ := phase2ReturnLo n s + phase2UpperGap n s

/-- The buffered checkpoint `y ≤ q - q/16`, strictly stronger than
`Phase2Stage n (s+1)`. -/
def Phase2BufferedStage (n s x : ℕ) : Prop :=
  x ≤ n ∧ n + phase2NextScale n s / 16 ≤ x + phase2NextScale n s

instance (n s : ℕ) : DecidablePred (Phase2BufferedStage n s) := by
  intro x; unfold Phase2BufferedStage; infer_instance

/-- Weakened band contraction: productive mass `≥ 21/2^(s+5)` on the extended
band, times the base-two loss `1/8`, gives loss `21/2^(s+8)`. -/
noncomputable def phase2BufferedDecay (s : ℕ) : ℝ := 1 - 21 / (2 : ℝ) ^ (s + 8)

noncomputable def phase2BufferedDecayENN (s : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (phase2BufferedDecay s)

theorem phase2BufferedDecay_nonneg (s : ℕ) : 0 ≤ phase2BufferedDecay s := by
  unfold phase2BufferedDecay
  have h : (21 : ℝ) / 2 ^ (s + 8) ≤ 21 / 2 ^ 8 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have : (21 : ℝ) / 2 ^ 8 < 1 := by norm_num
  linarith

/-! ## Section 2 — elementary geometry -/

theorem phase2_lower_pop (n : ℕ) (h4 : 4 ≤ n) :
    phase2LowerLo n + phase2LowerBHi n + 2 = n := by
  unfold phase2LowerLo phase2LowerBHi
  have hq : 1 ≤ n / 4 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  have hq2 : n / 4 ≤ n := Nat.div_le_self _ _
  omega

theorem phase2_return_pop (n s : ℕ) (hq : 1 ≤ phase2NextScale n s)
    (hqn : phase2NextScale n s + 1 ≤ n) :
    phase2ReturnLo n s + phase2ReturnBHi n s + 2 = n := by
  unfold phase2ReturnLo phase2ReturnBHi; omega

theorem phase2_upper_hi_eq (n s : ℕ) (hq : phase2NextScale n s + 1 ≤ n) :
    phase2UpperHi n s = n - phase2NextScale n s + phase2NextScale n s / 16 := by
  unfold phase2UpperHi phase2ReturnLo phase2UpperGap
  have h16 : phase2NextScale n s / 16 ≤ phase2NextScale n s := Nat.div_le_self _ _
  omega

theorem phase2_buffered_iff_upper_hi (n s x : ℕ)
    (hq : phase2NextScale n s + 1 ≤ n) :
    Phase2BufferedStage n s x ↔ x ≤ n ∧ phase2UpperHi n s ≤ x := by
  rw [phase2_upper_hi_eq n s hq]
  unfold Phase2BufferedStage
  have h16 : phase2NextScale n s / 16 ≤ phase2NextScale n s := Nat.div_le_self _ _
  omega

theorem phase2_guard_of_lowerLo_lt {n x : ℕ} (hxn : x ≤ n)
    (hlo : phase2LowerLo n < x) : Phase2Guard n x := by
  refine ⟨hxn, ?_⟩
  unfold phase2LowerLo at hlo
  have hdiv : 4 * (n / 4) ≤ n := Nat.mul_div_le n 4
  have hmod : n < 4 * (n / 4) + 4 := by
    have := Nat.div_add_mod n 4
    have hlt : n % 4 < 4 := Nat.mod_lt n (by norm_num)
    omega
  omega

/-! ## Section 3 — the buffered productive-mass kernel -/

set_option maxHeartbeats 800000 in
-- Normalizing the buffered combinatorial mass in `ℝ≥0∞` exceeds the default budget.
/-- **The buffered productive-mass lower bound.**  On the `q/16`-extended band
(minority `b+1 ≥ q - q/16`, guard `4(a+1) ≥ 3n`, `q ≥ 32`), the productive mass
is at least `21/2^(s+5)`.  This is the only new CRN-analytic fact; everything
downstream is stopping/Feller infrastructure. -/
theorem phase2_buffered_productive_lower
    (a b n s : ℕ) (h3 : 3 ≤ n) (hpop : a + b + 2 = n)
    (hguard : Phase2Guard n (a + 1))
    (hhi : a + 1 < phase2UpperHi n s)
    (hq : 32 ≤ phase2NextScale n s) :
    (21 : ℝ) / (2 : ℝ) ^ (s + 5) ≤
      ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) a) +
        ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) (a + 2)) := by
  set Q : ℕ := phase2NextScale n s with hQ
  set P : ℕ := 2 ^ (s + 1) with hP
  -- Closed form of the productive mass.
  have f0 : triStep (a + 1) (b + 1) (by omega) a ≠ ⊤ := PMF.apply_ne_top _ _
  have f2 : triStep (a + 1) (b + 1) (by omega) (a + 2) ≠ ⊤ := PMF.apply_ne_top _ _
  have hqeq :
      ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) a) +
          ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) (a + 2)) =
        (3 * ((a + 1 : ℕ) * (b + 1)) : ℝ) / ((n : ℝ) * (a + b + 1 : ℝ)) := by
    have hmass := productive_mass_closed a b n h3 hpop
    have hreal := congrArg ENNReal.toReal hmass
    rw [ENNReal.toReal_add f0 f2, ENNReal.toReal_div] at hreal
    simpa using hreal
  -- Nat facts.
  have hguard4 : 3 * n ≤ 4 * (a + 1) := by
    have := hguard.2; unfold Phase2Guard at *; omega
  have hPpos : 0 < P := by rw [hP]; positivity
  have h2P : 2 ≤ P := by
    rw [hP]
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmod : P * Q + n % P = n := Nat.div_add_mod n P
  have hmlt : n % P < P := Nat.mod_lt n hPpos
  have hPQ : P * Q ≤ n := by omega
  have hPQ2 : n < P * Q + P := by omega
  have hQn : Q + 1 ≤ n := by
    have h2Q : 2 * Q ≤ P * Q := Nat.mul_le_mul_right Q h2P
    omega
  have hUeq : phase2UpperHi n s = n - Q + Q / 16 := phase2_upper_hi_eq n s hQn
  have hdiv16 : Q / 16 * 16 ≤ Q := Nat.div_mul_le_self Q 16
  have hb16 : 15 * Q ≤ 16 * (b + 1) := by
    have hUx : a + 1 < n - Q + Q / 16 := by rw [← hUeq]; exact hhi
    omega
  have hpow5 : (2 : ℕ) ^ (s + 5) = 16 * P := by
    rw [hP, show s + 5 = (s + 1) + 4 by omega, pow_add]; ring
  have han : a + b + 1 ≤ n := by omega
  -- 64·(a+1)(b+1) ≥ (4(a+1))·(16(b+1)) ≥ 3n·15Q = 45nQ.
  have hprod : 45 * (n * Q) ≤ 64 * ((a + 1) * (b + 1)) := by
    have hmm := Nat.mul_le_mul hguard4 hb16
    calc 45 * (n * Q) = (3 * n) * (15 * Q) := by ring
      _ ≤ (4 * (a + 1)) * (16 * (b + 1)) := hmm
      _ = 64 * ((a + 1) * (b + 1)) := by ring
  -- 32P ≤ n, hence 28n ≤ 45PQ (linear in the atom P*Q).
  have hn32P : 32 * P ≤ n := by
    have := Nat.mul_le_mul_left P hq; omega
  have h28 : 28 * n ≤ 45 * (P * Q) := by omega
  -- 28n² ≤ 45PQn ≤ 64P(a+1)(b+1), so 7n² ≤ 16P(a+1)(b+1).
  have h1 : 28 * (n * n) ≤ 45 * (P * Q) * n := by
    have := Nat.mul_le_mul_right n h28
    calc 28 * (n * n) = 28 * n * n := by ring
      _ ≤ 45 * (P * Q) * n := this
  have h2 : 45 * (P * Q) * n ≤ 64 * (P * ((a + 1) * (b + 1))) := by
    have hP1 := Nat.mul_le_mul_left P hprod
    calc 45 * (P * Q) * n = P * (45 * (n * Q)) := by ring
      _ ≤ P * (64 * ((a + 1) * (b + 1))) := hP1
      _ = 64 * (P * ((a + 1) * (b + 1))) := by ring
  have h7n2 : 7 * (n * n) ≤ 16 * P * ((a + 1) * (b + 1)) := by
    have h28n2 : 28 * (n * n) ≤ 64 * (P * ((a + 1) * (b + 1))) := le_trans h1 h2
    have h4 : 4 * (7 * (n * n)) ≤ 4 * (16 * P * ((a + 1) * (b + 1))) := by
      calc 4 * (7 * (n * n)) = 28 * (n * n) := by ring
        _ ≤ 64 * (P * ((a + 1) * (b + 1))) := h28n2
        _ = 4 * (16 * P * ((a + 1) * (b + 1))) := by ring
    exact Nat.le_of_mul_le_mul_left h4 (by norm_num)
  have hkey : 7 * (n * (a + b + 1)) ≤ 2 ^ (s + 5) * ((a + 1) * (b + 1)) := by
    rw [hpow5, mul_assoc]
    calc 7 * (n * (a + b + 1)) = 7 * n * (a + b + 1) := by ring
      _ ≤ 7 * n * n := Nat.mul_le_mul_left (7 * n) han
      _ = 7 * (n * n) := by ring
      _ ≤ 16 * P * ((a + 1) * (b + 1)) := h7n2
      _ = 16 * (P * ((a + 1) * (b + 1))) := by ring
  -- Cross-multiply to the real bound.
  rw [hqeq, div_le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (s + 5))
    (by positivity : (0 : ℝ) < (n : ℝ) * (a + b + 1 : ℝ))]
  have hkey3 : 21 * (n * (a + b + 1)) ≤ 3 * ((a + 1) * (b + 1)) * 2 ^ (s + 5) := by
    calc 21 * (n * (a + b + 1)) = 3 * (7 * (n * (a + b + 1))) := by ring
      _ ≤ 3 * (2 ^ (s + 5) * ((a + 1) * (b + 1))) := Nat.mul_le_mul_left 3 hkey
      _ = 3 * ((a + 1) * (b + 1)) * 2 ^ (s + 5) := by ring
  exact_mod_cast hkey3

/-! ## Section 4 — the buffered one-step contraction -/

set_option maxHeartbeats 800000 in
-- The one-step contraction expands the buffered mass bound and its ENNReal scalar algebra.
/-- The buffered-band one-step base-two contraction with the weakened factor
`phase2BufferedDecayENN s = ofReal(1 - 21/2^(s+8))`.  Identical to
`phase2_hcontract_of_live` except that the productive lower bound is the buffered
`21/2^(s+5)` (valid down to minority `q - q/16`), giving loss `21/2^(s+8)`. -/
theorem phase2_buffered_hcontract (a b n s : ℕ)
    (hlocal : 3 ≤ (a + 1) + (b + 1)) (hpop : a + b + 2 = n)
    (hguard : Phase2Guard n (a + 1))
    (hhi : a + 1 < phase2UpperHi n s)
    (hq : 32 ≤ phase2NextScale n s) :
    triStep (a + 1) (b + 1) hlocal a +
          triStep (a + 1) (b + 1) hlocal (a + 1) *
            ((1 : ℝ≥0∞) / 2) +
          triStep (a + 1) (b + 1) hlocal (a + 2) *
            ((1 : ℝ≥0∞) / 2) ^ 2 ≤
        phase2BufferedDecayENN s * ((1 : ℝ≥0∞) / 2) := by
  have h3 : 3 ≤ n := by omega
  have hquarter : 3 * n ≤ 4 * (a + 1) := by
    have := hguard.2; unfold Phase2Guard at *; omega
  have hab : b ≤ a := by omega
  have hdirection := direction_ge_cross (a := a) (b := b) hab
  rw [hpop] at hdirection
  have hscaledDirection : n * (3 * (a + b)) ≤ n * (4 * a) := by
    calc
      n * (3 * (a + b)) = (3 * n) * (a + b) := by ring
      _ ≤ (4 * (a + 1)) * (a + b) := Nat.mul_le_mul_right (a + b) hquarter
      _ ≤ 4 * (n * a) := by
        calc
          (4 * (a + 1)) * (a + b) = 4 * ((a + 1) * (a + b)) := by ring
          _ ≤ 4 * (n * a) := Nat.mul_le_mul_left 4 hdirection
      _ = n * (4 * a) := by ring
  have habDirection : 3 * (a + b) ≤ 4 * a :=
    Nat.le_of_mul_le_mul_left hscaledDirection (by omega)
  have hcross := direction_cross_mul a b
  have hscaledCounts :
      (3 * (upCount a b + downCount a b)) * (a + b) ≤
        (4 * upCount a b) * (a + b) := by
    calc
      (3 * (upCount a b + downCount a b)) * (a + b) =
          (3 * (a + b)) * (upCount a b + downCount a b) := by ring
      _ ≤ (4 * a) * (upCount a b + downCount a b) :=
        Nat.mul_le_mul_right (upCount a b + downCount a b) habDirection
      _ = 4 * (a * (upCount a b + downCount a b)) := by ring
      _ = 4 * (upCount a b * (a + b)) := by rw [hcross]
      _ = (4 * upCount a b) * (a + b) := by ring
  have hdirectionCounts :
      3 * (upCount a b + downCount a b) ≤ 4 * upCount a b :=
    Nat.le_of_mul_le_mul_right hscaledCounts (by omega)
  have hdownUp : 3 * downCount a b ≤ upCount a b := by omega
  have hcountsE :
      (3 : ℝ≥0∞) * (downCount a b : ℝ≥0∞) ≤ (upCount a b : ℝ≥0∞) := by
    exact_mod_cast hdownUp
  push_cast at hcountsE
  have hdirectionE :
      (3 : ℝ≥0∞) * triStep (a + 1) (b + 1) hlocal a ≤
        triStep (a + 1) (b + 1) hlocal (a + 2) := by
    rw [triStep_down, triStep_up]
    push_cast
    simpa only [div_eq_mul_inv, mul_assoc] using
      mul_le_mul_left hcountsE (Nat.choose ((a + 1) + (b + 1)) 3 : ℝ≥0∞)⁻¹
  have htwoDown :
      (2 : ℝ≥0∞) * triStep (a + 1) (b + 1) hlocal a ≤
        triStep (a + 1) (b + 1) hlocal (a + 2) := by
    calc
      (2 : ℝ≥0∞) * triStep (a + 1) (b + 1) hlocal a ≤
          3 * triStep (a + 1) (b + 1) hlocal a := by gcongr; norm_num
      _ ≤ triStep (a + 1) (b + 1) hlocal (a + 2) := hdirectionE
  have hdrift :
      triStep (a + 1) (b + 1) hlocal a ≤
        triStep (a + 1) (b + 1) hlocal (a + 2) * ((1 : ℝ≥0∞) / 2) := by
    have hhalf : triStep (a + 1) (b + 1) hlocal a ≤
        triStep (a + 1) (b + 1) hlocal (a + 2) / 2 := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
      simpa [mul_comm] using htwoDown
    simpa only [div_eq_mul_inv, one_mul] using hhalf
  have hsum := triStep_masses_sum a (b + 1) hlocal
  have hweak := three_term_drift_ennreal hsum (by norm_num) hdrift
  have fhalf : ((1 : ℝ≥0∞) / 2) ≠ ⊤ := by norm_num
  have fleft :
      triStep (a + 1) (b + 1) hlocal a +
            triStep (a + 1) (b + 1) hlocal (a + 1) * ((1 : ℝ≥0∞) / 2) +
            triStep (a + 1) (b + 1) hlocal (a + 2) * ((1 : ℝ≥0∞) / 2) ^ 2 ≠ ⊤ :=
    ne_top_of_le_ne_top fhalf hweak
  have fright : phase2BufferedDecayENN s * ((1 : ℝ≥0∞) / 2) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top fhalf
  let p0 : ℝ := ENNReal.toReal (triStep (a + 1) (b + 1) hlocal a)
  let p1 : ℝ := ENNReal.toReal (triStep (a + 1) (b + 1) hlocal (a + 1))
  let p2 : ℝ := ENNReal.toReal (triStep (a + 1) (b + 1) hlocal (a + 2))
  have f0 : triStep (a + 1) (b + 1) hlocal a ≠ ⊤ := PMF.apply_ne_top _ _
  have f1 : triStep (a + 1) (b + 1) hlocal (a + 1) ≠ ⊤ := PMF.apply_ne_top _ _
  have f2 : triStep (a + 1) (b + 1) hlocal (a + 2) ≠ ⊤ := PMF.apply_ne_top _ _
  have hsumR : p0 + p1 + p2 = 1 := by
    have hreal := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨f0, f1⟩) f2,
      ENNReal.toReal_add f0 f1, ENNReal.toReal_one] at hreal
    simpa [p0, p1, p2] using hreal
  have hdirectionR : 3 * p0 ≤ p2 := by
    have hreal := ENNReal.toReal_mono f2 hdirectionE
    rw [ENNReal.toReal_mul] at hreal
    simpa [p0, p2] using hreal
  have hproductiveR : (21 : ℝ) / (2 : ℝ) ^ (s + 5) ≤ p0 + p2 := by
    simpa [p0, p2] using
      phase2_buffered_productive_lower a b n s h3 hpop hguard hhi hq
  have hbracket :
      2 * p0 + p1 + p2 / 2 ≤ 1 - (1 / 8 : ℝ) * (p0 + p2) := by nlinarith
  have hloss : (1 / 8 : ℝ) * (21 / (2 : ℝ) ^ (s + 5)) = 21 / (2 : ℝ) ^ (s + 8) := by
    rw [show s + 8 = (s + 5) + 3 by omega, pow_add]; norm_num; ring
  have hrate :
      1 - (1 / 8 : ℝ) * (p0 + p2) ≤ 1 - 21 / (2 : ℝ) ^ (s + 8) := by
    have hscaled := mul_le_mul_of_nonneg_left hproductiveR (by norm_num : (0 : ℝ) ≤ 1 / 8)
    calc
      1 - (1 / 8 : ℝ) * (p0 + p2) ≤
          1 - (1 / 8 : ℝ) * (21 / (2 : ℝ) ^ (s + 5)) := sub_le_sub_left hscaled 1
      _ = 1 - 21 / (2 : ℝ) ^ (s + 8) := by rw [hloss]
  rw [← ENNReal.toReal_le_toReal fleft fright,
    ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨f0, ENNReal.mul_ne_top f1 fhalf⟩)
      (ENNReal.mul_ne_top f2 (ENNReal.pow_ne_top fhalf)),
    ENNReal.toReal_add f0 (ENNReal.mul_ne_top f1 fhalf)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_one, phase2BufferedDecayENN,
    ENNReal.toReal_ofReal (phase2BufferedDecay_nonneg s)]
  norm_num only [ENNReal.toReal_ofNat]
  change p0 + p1 * (1 / 2 : ℝ) + p2 * (1 / 4 : ℝ) ≤
    phase2BufferedDecay s * (1 / 2 : ℝ)
  calc
    p0 + p1 * (1 / 2 : ℝ) + p2 * (1 / 4 : ℝ) =
        (1 / 2 : ℝ) * (2 * p0 + p1 + p2 / 2) := by ring
    _ ≤ (1 / 2 : ℝ) * (1 - (1 / 8 : ℝ) * (p0 + p2)) :=
      mul_le_mul_of_nonneg_left hbracket (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (1 - 21 / (2 : ℝ) ^ (s + 8)) :=
      mul_le_mul_of_nonneg_left hrate (by norm_num)
    _ = phase2BufferedDecay s * (1 / 2 : ℝ) := by unfold phase2BufferedDecay; ring


/-! ## Section 5 — lower safety width -/

theorem phase1Exit_lower_gap {n x : ℕ} (hn : 96 ≤ n) (hx : Phase1Exit n x) :
    phase2LowerLo n + phase2LowerGap n ≤ x := by
  obtain ⟨hxn, hfive⟩ := hx
  unfold phase2LowerLo phase2LowerGap
  omega

theorem phase2Stage_lower_gap {n s x : ℕ} (hn : 96 ≤ n) (hs : 3 ≤ s)
    (hx : Phase2Stage n s x) : phase2LowerLo n + phase2LowerGap n ≤ x := by
  have hxn : x ≤ n := hx.1
  have hpow : (8 : ℕ) ≤ 2 ^ s := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  have hsplit : 2 ^ s * (n - x) + 2 ^ s * x = 2 ^ s * n := by
    rw [← Nat.mul_add]; congr 1; omega
  have hbound : 2 ^ s * (n - x) ≤ n := by
    have hs2 := hx.2; omega
  have h8nx : 8 * (n - x) ≤ n :=
    le_trans (Nat.mul_le_mul_right (n - x) hpow) hbound
  unfold phase2LowerLo phase2LowerGap
  omega

/-! ## Section 6 — the three additive error terms -/

/-- Live-band Markov error over the buffered block, measured from the stage
minority floor `n - n/2^s` (the least `X`-count in `Phase2Stage n s`). -/
noncomputable def phase2BufferedLiveError (n s : ℕ) : ℝ≥0∞ :=
  phase2BufferedDecayENN s ^ (8 * n) *
      ((1 : ℝ≥0∞) / 2) ^ (n - n / 2 ^ s) /
      ((1 : ℝ≥0∞) / 2) ^ phase2UpperHi n s

/-- Lower ruin (Feller) error through the `y ≤ n/4` guard. -/
noncomputable def phase2LowerRuinError (n : ℕ) : ℝ≥0∞ :=
  ((phase2LowerBHi n : ℝ≥0∞) / (phase2LowerLo n : ℝ≥0∞)) ^ phase2LowerGap n

/-- Upper return (Feller) error from the buffered upper boundary. -/
noncomputable def phase2UpperReturnError (n s : ℕ) : ℝ≥0∞ :=
  ((phase2ReturnBHi n s : ℝ≥0∞) / (phase2ReturnLo n s : ℝ≥0∞)) ^ phase2UpperGap n s

/-- The additive per-stage error. -/
noncomputable def phase2AdditiveRungError (n s : ℕ) : ℝ≥0∞ :=
  phase2BufferedLiveError n s + phase2LowerRuinError n + phase2UpperReturnError n s


/-! ## Section 7 — stage/predicate glue and stage-count arithmetic -/

theorem phase2_buffered_to_stage {n s x : ℕ} (h : Phase2BufferedStage n s x) :
    Phase2Stage n (s + 1) x := by
  obtain ⟨hxn, hbuf⟩ := h
  refine ⟨hxn, ?_⟩
  have hnx : n ≤ x + phase2NextScale n s := by
    have h16 : 0 ≤ phase2NextScale n s / 16 := Nat.zero_le _
    omega
  have hqmul : 2 ^ (s + 1) * phase2NextScale n s ≤ n := by
    show 2 ^ (s + 1) * (n / 2 ^ (s + 1)) ≤ n
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self n _
  have hmul := Nat.mul_le_mul_left (2 ^ (s + 1)) hnx
  rw [Nat.mul_add] at hmul
  omega

theorem phase2_stage_failure_le_returnLo {n s x : ℕ}
    (hx : ¬ Phase2Upper n (s + 1) x) : x ≤ phase2ReturnLo n s := by
  unfold Phase2Upper at hx
  push_neg at hx
  unfold phase2ReturnLo phase2NextScale
  by_contra hc
  push_neg at hc
  have hKq : 2 ^ (s + 1) * (n / 2 ^ (s + 1)) ≤ n := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self n _
  have hxge : n - n / 2 ^ (s + 1) ≤ x := by omega
  have hmul := Nat.mul_le_mul_left (2 ^ (s + 1)) hxge
  rw [Nat.mul_sub] at hmul
  omega

theorem phase2StageCount_minimal {n γ i : ℕ} (hi : i < phase2StageCount n γ) :
    γ * Nat.log 2 n < 2 * (n / 2 ^ (2 + i)) := by
  have hnot := Nat.find_min (phase2StageCount_exists n γ) hi
  omega

theorem phase2StageCount_pos (n γ : ℕ) (hlog : 8 ≤ Nat.log 2 n)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) (hγ : 1 ≤ γ) : 0 < phase2StageCount n γ := by
  rcases Nat.eq_zero_or_pos (phase2StageCount n γ) with hk | hk
  · exfalso
    have hs := phase2StageCount_spec n γ
    rw [hk] at hs
    -- 2*(n/2^(2+0)) ≤ γ*lg n, i.e. 2*(n/4) ≤ γ*lg n; but 6γlg≤n gives n/4 large.
    have h4 : 2 ^ (2 + 0) = 4 := by norm_num
    rw [h4] at hs
    have hquarter : 4 * (n / 4) ≤ n := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self n 4
    have hmod : n < 4 * (n / 4) + 4 := by
      have := Nat.div_add_mod n 4; have : n % 4 < 4 := Nat.mod_lt n (by norm_num); omega
    nlinarith [hs, hsize, hquarter, hmod, hlog, hγ]
  · exact hk



/-! ## Section 8 — predicate glue for the upper boundary -/

theorem phase2_upperHi_to_upper {n s z : ℕ} (hqn : phase2NextScale n s + 1 ≤ n)
    (hz : phase2UpperHi n s ≤ z) : Phase2Upper n (s + 1) z := by
  unfold Phase2Upper
  rw [phase2_upper_hi_eq n s hqn] at hz
  have hqmul : 2 ^ (s + 1) * phase2NextScale n s ≤ n := by
    show 2 ^ (s + 1) * (n / 2 ^ (s + 1)) ≤ n
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self n _
  have hnz : n ≤ z + phase2NextScale n s := by
    have h16 : phase2NextScale n s / 16 ≤ phase2NextScale n s := Nat.div_le_self _ _
    omega
  have hmul := Nat.mul_le_mul_left (2 ^ (s + 1)) hnz
  rw [Nat.mul_add] at hmul
  omega

theorem phase2_upper_lowerLo_lt {n s z : ℕ} (hs : 2 ≤ s)
    (hqn : phase2NextScale n s + 1 ≤ n) (hz : Phase2Upper n (s + 1) z) :
    phase2LowerLo n < z := by
  unfold Phase2Upper at hz
  unfold phase2LowerLo
  have hqmul : 2 ^ (s + 1) * phase2NextScale n s ≤ n := by
    show 2 ^ (s + 1) * (n / 2 ^ (s + 1)) ≤ n
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self n _
  have hq8 : phase2NextScale n s ≤ n / 8 := by
    show n / 2 ^ (s + 1) ≤ n / 8
    exact Nat.div_le_div_left
      (by calc (8:ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) (by norm_num)
  -- z ≥ n - q (from Phase2Upper, when z ≤ n; if z > n trivially > lowerLo)
  rcases Nat.lt_or_ge n z with hzn | hzn
  · omega
  · have hnz : 2 ^ (s + 1) * (n - z) ≤ n := by
      have hsplit : 2 ^ (s + 1) * (n - z) + 2 ^ (s + 1) * z = 2 ^ (s + 1) * n := by
        rw [← Nat.mul_add]; congr 1; omega
      omega
    have h8 : (8 : ℕ) ≤ 2 ^ (s + 1) := by
      calc (8:ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h8nz : 8 * (n - z) ≤ n := le_trans (Nat.mul_le_mul_right (n - z) h8) hnz
    omega


/-! ## Section 9 — the one-rung band composition -/

set_option maxHeartbeats 1000000 in
-- Composing the stopped kernels unfolds three error terms and a large arithmetic certificate.
/-- One additive phase-2 rung.  From any start region `P ⊆ Phase2Stage n s` with
lower safety width `≥ phase2LowerGap n`, an `8n` block reaches
`Phase2Stage n (s+1)` with the three-term additive error. -/
theorem phase2_buffered_rung_of_start (n s : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (h3 : 3 ≤ n) (hn : 96 ≤ n) (hs : 2 ≤ s) (hq : 32 ≤ phase2NextScale n s)
    (hPstage : ∀ x, P x → Phase2Stage n s x)
    (hPlower : ∀ x, P x → phase2LowerLo n + phase2LowerGap n ≤ x) :
    Reaches (triChain n) (8 * n) P (Phase2Stage n (s + 1))
      (phase2AdditiveRungError n s) := by
  have hq8 : phase2NextScale n s ≤ n / 8 := by
    show n / 2 ^ (s + 1) ≤ n / 8
    exact Nat.div_le_div_left
      (by calc (8:ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) (by norm_num)
  have hn8 : n / 8 ≤ n := Nat.div_le_self _ _
  have hqn : phase2NextScale n s + 1 ≤ n := by omega
  have hlowerPop : phase2LowerLo n + phase2LowerBHi n + 2 = n :=
    phase2_lower_pop n (by omega)
  have hreturnPop : phase2ReturnLo n s + phase2ReturnBHi n s + 2 = n :=
    phase2_return_pop n s (by omega) hqn
  have hquarter : 4 * (n / 4) ≤ n := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self n 4
  have hquartermod : n < 4 * (n / 4) + 4 := by
    have := Nat.div_add_mod n 4; have : n % 4 < 4 := Nat.mod_lt n (by norm_num); omega
  have hlowerLoPos : 0 < phase2LowerLo n := by unfold phase2LowerLo; omega
  have hlowerBHiPos : 0 < phase2LowerBHi n := by unfold phase2LowerBHi; omega
  have hlowerMaj : phase2LowerBHi n ≤ phase2LowerLo n := by
    unfold phase2LowerLo phase2LowerBHi; omega
  have hbase1 : (phase2LowerBHi n : ℝ≥0∞) / (phase2LowerLo n : ℝ≥0∞) ≤ 1 := by
    have h := ENNReal.div_le_div_right
      (show (phase2LowerBHi n : ℝ≥0∞) ≤ (phase2LowerLo n : ℝ≥0∞) by
        exact_mod_cast hlowerMaj) (phase2LowerLo n : ℝ≥0∞)
    rwa [ENNReal.div_self (by exact_mod_cast hlowerLoPos.ne')
      (ENNReal.natCast_ne_top _)] at h
  have hUpperHi_le : phase2LowerLo n ≤ phase2UpperHi n s := by
    unfold phase2UpperHi phase2ReturnLo phase2LowerLo
    have hq16 : phase2NextScale n s / 16 ≤ phase2NextScale n s := Nat.div_le_self _ _
    omega
  have hUpperLen : phase2UpperHi n s ≤ n := by
    rw [phase2_upper_hi_eq n s hqn]
    have hq16 : phase2NextScale n s / 16 ≤ phase2NextScale n s := Nat.div_le_self _ _
    omega
  intro x hx
  have hxstage := hPstage x hx
  have hxphysical : x ≤ n := hxstage.1
  have hxlower := hPlower x hx
  have hlgpos : 1 ≤ phase2LowerGap n := by unfold phase2LowerGap; omega
  -- The two error weakenings, valid in both cases.
  have hlowerWeak : ((phase2LowerBHi n : ℝ≥0∞) / (phase2LowerLo n : ℝ≥0∞))
      ^ (x - phase2LowerLo n) ≤ phase2LowerRuinError n := by
    unfold phase2LowerRuinError
    exact pow_le_pow_right_of_le_one' hbase1 (by unfold phase2LowerGap at hxlower ⊢; omega)
  have hstageFloor : n - n / 2 ^ s ≤ x := by
    have hsplit : 2 ^ s * (n - x) + 2 ^ s * x = 2 ^ s * n := by
      rw [← Nat.mul_add]; congr 1; omega
    have hbound : 2 ^ s * (n - x) ≤ n := by have := hxstage.2; omega
    have hd : n - x ≤ n / 2 ^ s := by
      apply (Nat.le_div_iff_mul_le (by positivity)).2; rw [Nat.mul_comm]; omega
    omega
  have hliveWeak : phase2BufferedDecayENN s ^ (8 * n) *
      ((1 : ℝ≥0∞) / 2) ^ x / ((1 : ℝ≥0∞) / 2) ^ phase2UpperHi n s ≤
      phase2BufferedLiveError n s := by
    unfold phase2BufferedLiveError
    have hpx : ((1 : ℝ≥0∞) / 2) ^ x ≤ ((1 : ℝ≥0∞) / 2) ^ (n - n / 2 ^ s) :=
      pow_le_pow_right_of_le_one' (by norm_num) hstageFloor
    exact ENNReal.div_le_div_right (mul_le_mul_left' hpx _) _
  by_cases hdeep : phase2UpperHi n s ≤ x
  · -- Already beyond the buffered boundary: only the upper-return term is needed.
    have hret := triChain_upper_target_failure n (phase2ReturnLo n s)
      (phase2ReturnBHi n s) (phase2UpperGap n s) x (8 * n) h3 hreturnPop
      (by unfold phase2ReturnLo; omega) (by unfold phase2ReturnBHi; omega)
      (by unfold phase2ReturnLo phase2ReturnBHi; omega)
      (by show phase2ReturnLo n s + phase2UpperGap n s ≤ x
          have : phase2ReturnLo n s + phase2UpperGap n s = phase2UpperHi n s := rfl
          omega)
      (Phase2Upper n (s + 1)) (fun z hz => phase2_stage_failure_le_returnLo hz)
    have hreaches : Reaches (triChain n) (8 * n) (fun y => y = x)
        (Phase2Upper n (s + 1)) (phase2UpperReturnError n s) := by
      intro y hy; subst y; simpa only [phase2UpperReturnError] using hret
    have hstage := hreaches.phase2Stage_of_upper h3
      (by intro y hy; subst y; exact hxphysical)
    refine (hstage.mono_error ?_) x rfl
    unfold phase2AdditiveRungError
    exact le_add_left le_rfl
  · -- Genuine band case.
    have hxhi : x < phase2UpperHi n s := Nat.lt_of_not_ge hdeep
    set bandGap := x - phase2LowerLo n with hbandGapDef
    set upperGap := phase2UpperHi n s - x with hupperGapDef
    have hbandStart : phase2LowerLo n + bandGap = x := by rw [hbandGapDef]; omega
    have hbandPos : 0 < bandGap := by rw [hbandGapDef]; omega
    have hupperPos : 0 < upperGap := by rw [hupperGapDef]; omega
    have htarget : phase2LowerLo n + bandGap + upperGap = phase2UpperHi n s := by
      rw [hbandGapDef, hupperGapDef]; omega
    have hdir : ∀ (a b : ℕ) (hab : a + b + 2 = n),
        phase2LowerLo n < a + 1 → a + 1 < phase2LowerLo n + bandGap + upperGap →
        triStep (a + 1) (b + 1) (by omega) a +
              triStep (a + 1) (b + 1) (by omega) (a + 1) * ((1 : ℝ≥0∞) / 2) +
              triStep (a + 1) (b + 1) (by omega) (a + 2) * ((1 : ℝ≥0∞) / 2) ^ 2 ≤
          phase2BufferedDecayENN s * ((1 : ℝ≥0∞) / 2) := by
      intro a b hab hlo hhi
      have hguard := phase2_guard_of_lowerLo_lt (n := n) (x := a + 1) (by omega) hlo
      exact phase2_buffered_hcontract a b n s (by omega) hab hguard
        (by rw [htarget] at hhi; exact hhi) hq
    have hstop := DirectionProgress.phase1_direction_progress n (phase2LowerLo n) (phase2LowerBHi n)
      bandGap upperGap (8 * n) h3 hlowerPop hlowerLoPos hlowerBHiPos hlowerMaj
      hbandPos hupperPos (by rw [htarget]; exact hUpperLen)
      ((1 : ℝ≥0∞) / 2) (phase2BufferedDecayENN s) (by norm_num) (by norm_num) hdir
    rw [htarget, hbandStart] at hstop
    have hbandChain : Reaches (bandChain n (phase2LowerLo n) (phase2UpperHi n s))
        (8 * n) (fun y => y = x) (fun z => phase2UpperHi n s ≤ z)
        (((phase2LowerBHi n : ℝ≥0∞) / (phase2LowerLo n : ℝ≥0∞)) ^ bandGap +
          phase2BufferedDecayENN s ^ (8 * n) *
            ((1 : ℝ≥0∞) / 2) ^ x / ((1 : ℝ≥0∞) / 2) ^ phase2UpperHi n s) := by
      intro y hy; subst y
      simpa only [directionStop, bandChain] using hstop
    have hupperBand := hbandChain.mono_post
      (fun z hz => phase2_upperHi_to_upper hqn hz)
    have hcount := hupperBand.bandCount_of_bandChain n (phase2LowerLo n)
      (phase2UpperHi n s) (8 * n) x 0 (Phase2Upper n (s + 1)) _
    have horiginal := Reaches.of_bandCount_upper n (phase2LowerLo n)
      (phase2UpperHi n s) (phase2ReturnLo n s) (phase2ReturnBHi n s)
      (phase2UpperGap n s) (8 * n) x 0 h3 hreturnPop
      (by unfold phase2ReturnLo; omega) (by unfold phase2ReturnBHi; omega)
      (by unfold phase2ReturnLo phase2ReturnBHi; omega)
      (by show phase2ReturnLo n s + phase2UpperGap n s ≤ phase2UpperHi n s
          exact le_of_eq rfl)
      (Phase2Upper n (s + 1)) _
      (fun z hz => phase2_upper_lowerLo_lt hs hqn hz)
      (fun z hz => phase2_stage_failure_le_returnLo hz) hcount
    have hstage := horiginal.phase2Stage_of_upper h3
      (by intro y hy; subst y; exact hxphysical)
    refine (hstage.mono_error ?_) x rfl
    unfold phase2AdditiveRungError phase2UpperReturnError
    refine add_le_add ?_ le_rfl
    calc ((phase2LowerBHi n : ℝ≥0∞) / (phase2LowerLo n : ℝ≥0∞)) ^ bandGap +
          phase2BufferedDecayENN s ^ (8 * n) *
            ((1 : ℝ≥0∞) / 2) ^ x / ((1 : ℝ≥0∞) / 2) ^ phase2UpperHi n s
        ≤ phase2LowerRuinError n + phase2BufferedLiveError n s :=
          add_le_add hlowerWeak hliveWeak
      _ = phase2BufferedLiveError n s + phase2LowerRuinError n := add_comm _ _


/-! ## Section 10 — rung wrappers and per-rung buffer availability -/

theorem phase2_first_additive_rung (n : ℕ) (h3 : 3 ≤ n) (hn : 96 ≤ n)
    (hq : 32 ≤ phase2NextScale n 2) :
    Reaches (triChain n) (8 * n) (Phase1Exit n) (Phase2Stage n 3)
      (phase2AdditiveRungError n 2) := by
  exact phase2_buffered_rung_of_start n 2 (Phase1Exit n) h3 hn (by norm_num) hq
    (fun x hx => phase1_exit_to_phase2_stage hx)
    (fun x hx => phase1Exit_lower_gap hn hx)

theorem phase2_later_additive_rung (n s : ℕ) (h3 : 3 ≤ n) (hn : 96 ≤ n)
    (hs : 3 ≤ s) (hq : 32 ≤ phase2NextScale n s) :
    Reaches (triChain n) (8 * n) (Phase2Stage n s) (Phase2Stage n (s + 1))
      (phase2AdditiveRungError n s) := by
  exact phase2_buffered_rung_of_start n s (Phase2Stage n s) h3 hn (by omega) hq
    (fun x hx => hx) (fun x hx => phase2Stage_lower_gap hn hs hx)

theorem phase2_active_nextScale_ge_32 {n γ i : ℕ} (hγ : 1 ≤ γ)
    (hlog : 128 ≤ Nat.log 2 n) (hi : i < phase2StageCount n γ) :
    32 ≤ phase2NextScale n (2 + i) := by
  have hmin := phase2StageCount_minimal hi
  have hns : phase2NextScale n (2 + i) = n / 2 ^ (2 + i) / 2 := by
    unfold phase2NextScale
    rw [show 2 + i + 1 = (2 + i) + 1 by omega, pow_succ, Nat.div_div_eq_div_mul]
  rw [hns]
  have hm : n / 2 ^ (2 + i) ≤ 2 * (n / 2 ^ (2 + i) / 2) + 1 := by omega
  have hlogγ : 128 ≤ γ * Nat.log 2 n :=
    le_trans hlog (Nat.le_mul_of_pos_left _ (by omega))
  omega


/-! ## Section 11 — the phase-2 additive ladder -/

set_option maxHeartbeats 800000 in
-- The ladder induction normalizes the staged horizon and accumulated error at every rung.
/-- **The additive phase-2 ladder.**  From `Phase1Exit n`, `phase2StageCount n γ`
buffered `8n` rungs reach `Phase3Entry n γ` with the summed additive error.  The
first rung starts from `Phase1Exit` (nonzero lower width); the rest chain through
`Phase2Stage`. -/
theorem phase2_reaches_additive (n γ : ℕ) (h3 : 3 ≤ n) (hn : 96 ≤ n) (hγ : 1 ≤ γ)
    (hsize : 6 * γ * Nat.log 2 n ≤ n) (hlog : 128 ≤ Nat.log 2 n) :
    Reaches (triChain n) (8 * n * phase2StageCount n γ) (Phase1Exit n)
      (Phase3Entry n γ)
      (∑ i ∈ Finset.range (phase2StageCount n γ),
        phase2AdditiveRungError n (2 + i)) := by
  set k := phase2StageCount n γ with hk
  have hkpos : 0 < k := phase2StageCount_pos n γ (by omega) hsize hγ
  -- later rungs, indexed by j < k-1, from Phase2Stage n (3+j).
  have hlater : ∀ j < k - 1,
      Reaches (triChain n) (8 * n) (Phase2Stage n (3 + j))
        (Phase2Stage n (3 + (j + 1))) (phase2AdditiveRungError n (3 + j)) := by
    intro j hj
    have hqj : 32 ≤ phase2NextScale n (3 + j) := by
      have := phase2_active_nextScale_ge_32 (n := n) (γ := γ) hγ hlog
        (show j + 1 < k by omega)
      rwa [show 2 + (j + 1) = 3 + j by omega] at this
    exact phase2_later_additive_rung n (3 + j) h3 hn (by omega) hqj
  have hchain := Reaches.chain (K := triChain n)
    (P := fun j => Phase2Stage n (3 + j)) (T := fun _ => 8 * n)
    (ε := fun j => phase2AdditiveRungError n (3 + j)) hlater
  simp only [] at hchain
  -- first rung: Phase1Exit → Phase2Stage n 3.
  have hfirst := phase2_first_additive_rung n h3 hn
    (by have := phase2_active_nextScale_ge_32 (n := n) (γ := γ) hγ hlog
          (show 0 < k by omega)
        simpa using this)
  -- compose.
  have hcomp := hfirst.comp hchain
  -- rewrite horizon and error into the closed forms.
  have hTeq : 8 * n + (∑ _j ∈ Finset.range (k - 1), 8 * n) = 8 * n * k := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have hk1 : (k - 1) + 1 = k := Nat.succ_pred_eq_of_pos hkpos
    calc 8 * n + (k - 1) * (8 * n) = ((k - 1) + 1) * (8 * n) := by ring
      _ = k * (8 * n) := by rw [hk1]
      _ = 8 * n * k := by ring
  have hEeq : phase2AdditiveRungError n 2 +
      (∑ j ∈ Finset.range (k - 1), phase2AdditiveRungError n (3 + j)) =
      ∑ i ∈ Finset.range k, phase2AdditiveRungError n (2 + i) := by
    rw [show k = (k - 1) + 1 by omega, Finset.sum_range_succ', Nat.add_zero,
      add_comm (phase2AdditiveRungError n 2)]
    congr 1
    apply Finset.sum_congr rfl
    intro j _; congr 1; omega
  rw [hTeq] at hcomp
  have hPk : (3 + (k - 1)) = 2 + k := by omega
  rw [hPk] at hcomp
  have hpost := hcomp.mono_post (fun z hz =>
    phase2_stage_to_phase3Entry (phase2StageCount_spec n γ) hz)
  intro x hx
  calc ∑' z, (if Phase3Entry n γ z then 0 else iter (triChain n) (8 * n * k) x z)
      ≤ phase2AdditiveRungError n 2 +
          ∑ j ∈ Finset.range (k - 1), phase2AdditiveRungError n (3 + j) := hpost x hx
    _ = ∑ i ∈ Finset.range k, phase2AdditiveRungError n (2 + i) := hEeq


end Tri
