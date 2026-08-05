/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Chain
import Tri.LazyHitting
import Tri.PaperLemma2
import Tri.RatioExp

/-!
# Paper Lemma 3: binary gap amplification in productive-event time

This file constructs the binary Tri chain embedded at productive reactions.
The paper's Lemma 3 is then proved by its two separate engines: Feller safety
against a half-gap downcrossing and an adapted Chernoff bound for reaching the
doubled gap within `2n` productive reactions.
-/

namespace Tri

open scoped ENNReal NNReal

/-- Multiplicative lower-tail bound for an adapted Bernoulli counter.  Unlike
`lemma2_lower_tail`, the trials may depend on the current state; the only input
is the pointwise one-step moment bound at the chosen tilt. -/
theorem adapted_multiplicative_lower_tail
    {α : Type*} (K : α → PMF α) (count : α → ℕ) (s₀ : α)
    (p : ℝ≥0) (hp : p ≤ 1)
    (delta : ℝ) (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (N k : ℕ)
    (hk :
      (k : ℝ) ≤
        (1 - delta) * ((N : ℝ) * (p : ℝ)))
    (hcount0 : count s₀ = 0)
    (hstep : ∀ s,
      expect (K s)
          (fun z => ENNReal.ofReal (Real.exp (-delta)) ^ count z) ≤
        (((1 - p : ℝ≥0) : ℝ≥0∞) +
            (p : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-delta))) *
          ENNReal.ofReal (Real.exp (-delta)) ^ count s) :
    (∑' z : α,
        (if count z ≤ k then iter K N s₀ z else 0)) ≤
      ENNReal.ofReal
        (Real.exp
          (-(delta ^ 2 * ((N : ℝ) * (p : ℝ))) / 2)) := by
  let w : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-delta))
  have hw1 : w ≤ 1 := by
    dsimp only [w]
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal <|
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hdelta0)
  have hw0 : w ≠ 0 := by
    dsimp only [w]
    exact ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hraw :=
    count_tail_bernoulli K count w (p : ℝ≥0∞)
      ((1 - p : ℝ≥0) : ℝ≥0∞) hw1 hw0
      (by simpa only [w] using hstep) N k s₀
  rw [hcount0, pow_zero, mul_one] at hraw
  refine hraw.trans ?_
  have hp0R : 0 ≤ (p : ℝ) := p.2
  have hp1R : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hp'0R : 0 ≤ ((1 - p : ℝ≥0) : ℝ) :=
    (1 - p : ℝ≥0).2
  have hsumR :
      (p : ℝ) + ((1 - p : ℝ≥0) : ℝ) = 1 := by
    rw [NNReal.coe_sub hp]
    exact add_tsub_cancel_of_le hp
  have hbase :
      (((1 - p : ℝ≥0) : ℝ≥0∞) + (p : ℝ≥0∞) * w) =
        ENNReal.ofReal
          (((1 - p : ℝ≥0) : ℝ) +
            (p : ℝ) * Real.exp (-delta)) := by
    dsimp only [w]
    rw [ENNReal.coe_nnreal_eq, ENNReal.coe_nnreal_eq,
      ← ENNReal.ofReal_mul hp0R,
      ← ENNReal.ofReal_add hp'0R
        (mul_nonneg hp0R (Real.exp_nonneg _))]
  rw [hbase,
    ← ENNReal.ofReal_pow
      (add_nonneg hp'0R
        (mul_nonneg hp0R (Real.exp_nonneg _))),
    ← ENNReal.ofReal_pow (Real.exp_nonneg _),
    ← ENNReal.ofReal_div_of_pos (pow_pos (Real.exp_pos _) k)]
  exact ENNReal.ofReal_le_ofReal <|
    bernoulli_multiplicative_lower_ratio
      hp0R hp1R hsumR hdelta0 hdelta1 N k hk

/-- The direction of one productive binary Tri reaction at the interior state
`x = a+1`, `y = b+1`.  `true` is the `X`-increasing reaction. -/
noncomputable def productiveDirectionPMF
    (a b : ℕ) (hprod : 0 < a + b) : PMF Bool := by
  classical
  refine PMF.ofFintype
    (fun up =>
      if up then
        (a : ℝ≥0∞) / (a + b : ℝ≥0∞)
      else
        (b : ℝ≥0∞) / (a + b : ℝ≥0∞)) ?_
  have hne : (a : ℝ≥0∞) + (b : ℝ≥0∞) ≠ 0 := by
    have hpos : (0 : ℝ≥0∞) < (a : ℝ≥0∞) + (b : ℝ≥0∞) := by
      exact_mod_cast hprod
    exact hpos.ne'
  have htop : (a : ℝ≥0∞) + (b : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.natCast_ne_top _, ENNReal.natCast_ne_top _⟩
  rw [show (Finset.univ : Finset Bool) = {false, true} by
    ext up
    cases up <;> simp]
  simp only [Bool.false_eq_true, if_false, if_true, Finset.sum_insert,
    Finset.mem_singleton, Bool.false_eq_true, not_false_eq_true,
    Finset.sum_singleton]
  calc
    (b : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) +
          (a : ℝ≥0∞) / ((a : ℝ≥0∞) + (b : ℝ≥0∞)) =
        ((b : ℝ≥0∞) + (a : ℝ≥0∞)) /
          ((a : ℝ≥0∞) + (b : ℝ≥0∞)) :=
      ENNReal.div_add_div_same
    _ = ((a : ℝ≥0∞) + (b : ℝ≥0∞)) /
          ((a : ℝ≥0∞) + (b : ℝ≥0∞)) := by rw [add_comm]
    _ = 1 := ENNReal.div_self hne htop

@[simp] theorem productiveDirectionPMF_false
    (a b : ℕ) (hprod : 0 < a + b) :
    productiveDirectionPMF a b hprod false =
      (b : ℝ≥0∞) / (a + b : ℝ≥0∞) := by
  rfl

@[simp] theorem productiveDirectionPMF_true
    (a b : ℕ) (hprod : 0 < a + b) :
    productiveDirectionPMF a b hprod true =
      (a : ℝ≥0∞) / (a + b : ℝ≥0∞) := by
  rfl

/-- One productive reaction, expressed on the `X` count. -/
noncomputable def productiveTriInterior
    (a b : ℕ) (hprod : 0 < a + b) : PMF ℕ :=
  (productiveDirectionPMF a b hprod).map fun up =>
    if up then a + 2 else a

/-- The binary Tri chain embedded at productive reactions.  Consensus,
nonphysical states, and the population-two degeneracy are totalized by a
self-loop. -/
noncomputable def productiveTriChain (n : ℕ) : ℕ → PMF ℕ := fun x =>
  if h : 3 ≤ n ∧ 0 < x ∧ x < n then
    productiveTriInterior (x - 1) (n - x - 1) (by omega)
  else
    PMF.pure x

/-- Subtraction-free rewriting of the productive chain on an interior state. -/
theorem productiveTriChain_apply
    {n a b : ℕ} (hpop : a + b + 2 = n) (hprod : 0 < a + b) :
    productiveTriChain n (a + 1) =
      productiveTriInterior a b hprod := by
  unfold productiveTriChain
  rw [dif_pos]
  · congr 2
    all_goals omega
  · omega

/-- Exact two-atom expectation for an embedded productive reaction. -/
theorem expect_productiveTriInterior
    (a b : ℕ) (hprod : 0 < a + b) (V : ℕ → ℝ≥0∞) :
    expect (productiveTriInterior a b hprod) V =
      (b : ℝ≥0∞) / (a + b : ℝ≥0∞) * V a +
      (a : ℝ≥0∞) / (a + b : ℝ≥0∞) * V (a + 2) := by
  rw [productiveTriInterior, expect_map]
  unfold expect
  rw [tsum_fintype]
  rw [show (Finset.univ : Finset Bool) = {false, true} by
    ext up
    cases up <;> simp]
  simp

/-- The two productive-direction masses sum to one. -/
theorem productiveTriInterior_masses
    (a b : ℕ) (hprod : 0 < a + b) :
    (b : ℝ≥0∞) / (a + b : ℝ≥0∞) +
      (a : ℝ≥0∞) / (a + b : ℝ≥0∞) = 1 := by
  have hsum := PMF.tsum_coe (productiveDirectionPMF a b hprod)
  rw [tsum_fintype] at hsum
  rw [show (Finset.univ : Finset Bool) = {false, true} by
    ext up
    cases up <;> simp] at hsum
  simpa using hsum

/-- The embedded up mass is exactly the raw Tri up-count conditioned on the
two productive reaction counts.  This is the physical bridge from the
two-atom kernel to the original uniformly sampled reaction kernel. -/
theorem productiveDirectionPMF_true_eq_count_ratio
    (a b : ℕ) (hprod : 0 < a + b) :
    productiveDirectionPMF a b hprod true =
      (upCount a b : ℝ≥0∞) /
        (upCount a b + downCount a b : ℝ≥0∞) := by
  rw [productiveDirectionPMF_true]
  have hsumPos : 0 < upCount a b + downCount a b :=
    productive_pos hprod
  have hsum0 :
      (upCount a b + downCount a b : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hsumPos.ne'
  have hsumTop :
      (upCount a b + downCount a b : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.natCast_ne_top _, ENNReal.natCast_ne_top _⟩
  have hden0 : (a + b : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hprod.ne'
  have hdenTop : (a + b : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.natCast_ne_top _, ENNReal.natCast_ne_top _⟩
  apply (ENNReal.div_eq_div_iff hsum0 hsumTop hden0 hdenTop).2
  have hcross := (direction_cross_mul a b).symm
  exact_mod_cast (show
    (upCount a b + downCount a b) * a =
      (a + b) * upCount a b by simpa [mul_comm] using hcross)

/-- The embedded down mass is the complementary raw productive count. -/
theorem productiveDirectionPMF_false_eq_count_ratio
    (a b : ℕ) (hprod : 0 < a + b) :
    productiveDirectionPMF a b hprod false =
      (downCount a b : ℝ≥0∞) /
        (upCount a b + downCount a b : ℝ≥0∞) := by
  rw [productiveDirectionPMF_false]
  have hsumPos : 0 < upCount a b + downCount a b :=
    productive_pos hprod
  have hsum0 :
      (upCount a b + downCount a b : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hsumPos.ne'
  have hsumTop :
      (upCount a b + downCount a b : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.natCast_ne_top _, ENNReal.natCast_ne_top _⟩
  have hden0 : (a + b : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast hprod.ne'
  have hdenTop : (a + b : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr
      ⟨ENNReal.natCast_ne_top _, ENNReal.natCast_ne_top _⟩
  apply (ENNReal.div_eq_div_iff hsum0 hsumTop hden0 hdenTop).2
  have hcross :
      downCount a b * (a + b) =
        b * (upCount a b + downCount a b) := by
    have hup := direction_cross_mul a b
    nlinarith
  exact_mod_cast (show
    (upCount a b + downCount a b) * b =
      (a + b) * downCount a b by simpa [mul_comm] using hcross.symm)

/-- Paper Lemma 3's doubled (and population-capped) signed-gap target. -/
def Lemma3Target (n Δ x : ℕ) : Prop :=
  n + min (2 * Δ) n ≤ 2 * x

/-- The integral quarter-gap width `⌈Δ/4⌉`. -/
def lemma3Quarter (Δ : ℕ) : ℕ :=
  (Δ + 3) / 4

/-- The lower half-gap guard used by the Feller part of Lemma 3. -/
def Lemma3Bad (x₀ Δ x : ℕ) : Prop :=
  x ≤ x₀ - lemma3Quarter Δ

noncomputable instance lemma3TargetDecidable (n Δ x : ℕ) :
    Decidable (Lemma3Target n Δ x) := by
  unfold Lemma3Target
  infer_instance

noncomputable instance lemma3BadDecidable (x₀ Δ x : ℕ) :
    Decidable (Lemma3Bad x₀ Δ x) := by
  unfold Lemma3Bad
  infer_instance

/-- State of the stopped productive-event proof: current `X` count, number of
up reactions, and number of consumed productive slots. -/
structure Lemma3Trace where
  x : ℕ
  success : ℕ
  clock : ℕ
  deriving DecidableEq

/-- The proof lift pauses physically on either boundary.  Boundary and
nonphysical states consume a slot and receive an artificial success; this
makes the global Chernoff premise total without changing the projected state.
On a live physical state it is exactly the embedded productive Tri step. -/
noncomputable def lemma3TraceStep
    (n x₀ Δ : ℕ) : Lemma3Trace → PMF Lemma3Trace := fun q =>
  if Lemma3Bad x₀ Δ q.x ∨ Lemma3Target n Δ q.x then
    PMF.pure ⟨q.x, q.success + 1, q.clock + 1⟩
  else if h : 3 ≤ n ∧ 0 < q.x ∧ q.x < n then
    (productiveDirectionPMF (q.x - 1) (n - q.x - 1) (by omega)).map
      fun up =>
        ⟨if up then q.x + 1 else q.x - 1,
          if up then q.success + 1 else q.success,
          q.clock + 1⟩
  else
    PMF.pure ⟨q.x, q.success + 1, q.clock + 1⟩

/-- The initial counted state. -/
def lemma3Initial (x₀ : ℕ) : Lemma3Trace :=
  { x := x₀, success := 0, clock := 0 }

/-- Forget the proof counters. -/
def Lemma3Trace.toX (q : Lemma3Trace) : ℕ :=
  q.x

/-- The ceiling quarter is positive for every positive gap. -/
theorem lemma3Quarter_pos {Δ : ℕ} (hΔ : 0 < Δ) :
    0 < lemma3Quarter Δ := by
  unfold lemma3Quarter
  omega

/-- Exact integral bounds for `⌈Δ/4⌉`. -/
theorem lemma3Quarter_bounds (Δ : ℕ) :
    Δ ≤ 4 * lemma3Quarter Δ ∧
      4 * lemma3Quarter Δ ≤ Δ + 3 := by
  unfold lemma3Quarter
  omega

theorem lemma3Quarter_le {Δ : ℕ} (hΔ : 0 < Δ) :
    lemma3Quarter Δ ≤ Δ := by
  have h := lemma3Quarter_bounds Δ
  omega

/-- Static path invariant for the counted lift.  Before a boundary is reached,
signed displacement equals successes minus failures. -/
def Lemma3Trace.Inv (n x₀ Δ : ℕ) (q : Lemma3Trace) : Prop :=
  Lemma3Bad x₀ Δ q.x ∨
    Lemma3Target n Δ q.x ∨
      q.x + q.clock = x₀ + 2 * q.success

/-- The initial counted state satisfies the displacement invariant. -/
theorem lemma3Initial_inv (n x₀ Δ : ℕ) :
    (lemma3Initial x₀).Inv n x₀ Δ := by
  right
  right
  simp [lemma3Initial]

/-- Away from both boundaries the trace is a genuine interior productive
state. -/
theorem lemma3_live_physical
    {n x₀ y₀ Δ : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    {x : ℕ} (hbad : ¬ Lemma3Bad x₀ Δ x)
    (htarget : ¬ Lemma3Target n Δ x) :
    3 ≤ n ∧ 0 < x ∧ x < n := by
  have hk : lemma3Quarter Δ ≤ x₀ :=
    (lemma3Quarter_le hΔ0).trans (by omega)
  have hx0 : x₀ - lemma3Quarter Δ < x := by
    simpa [Lemma3Bad] using hbad
  have hn3 : 3 ≤ n := by omega
  have hxn : x < n := by
    unfold Lemma3Target at htarget
    omega
  exact ⟨hn3, by omega, hxn⟩

/-- Boundary states pause physically and consume one artificial-success slot. -/
theorem lemma3TraceStep_of_boundary
    (n x₀ Δ : ℕ) (q : Lemma3Trace)
    (hq : Lemma3Bad x₀ Δ q.x ∨ Lemma3Target n Δ q.x) :
    lemma3TraceStep n x₀ Δ q =
      PMF.pure ⟨q.x, q.success + 1, q.clock + 1⟩ := by
  unfold lemma3TraceStep
  rw [if_pos hq]

/-- Off the boundaries, a physical trace step is exactly the two-direction
productive sampler. -/
theorem lemma3TraceStep_of_live
    (n x₀ Δ : ℕ) (q : Lemma3Trace)
    (hbound : ¬ (Lemma3Bad x₀ Δ q.x ∨ Lemma3Target n Δ q.x))
    (hphys : 3 ≤ n ∧ 0 < q.x ∧ q.x < n) :
    lemma3TraceStep n x₀ Δ q =
      (productiveDirectionPMF (q.x - 1) (n - q.x - 1)
        (by omega)).map
        (fun up =>
          ⟨if up then q.x + 1 else q.x - 1,
            if up then q.success + 1 else q.success,
            q.clock + 1⟩) := by
  unfold lemma3TraceStep
  rw [if_neg hbound, dif_pos hphys]

/-- One supported trace step preserves the displacement invariant and advances
the slot clock exactly once. -/
theorem lemma3TraceStep_support
    {n x₀ y₀ Δ : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (q : Lemma3Trace) (hq : q.Inv n x₀ Δ)
    (z : Lemma3Trace)
    (hqz : lemma3TraceStep n x₀ Δ q z ≠ 0) :
    z.Inv n x₀ Δ ∧ z.clock = q.clock + 1 := by
  classical
  by_cases hbound :
      Lemma3Bad x₀ Δ q.x ∨ Lemma3Target n Δ q.x
  · rw [lemma3TraceStep_of_boundary n x₀ Δ q hbound,
      PMF.pure_apply] at hqz
    by_cases hz :
        z = (⟨q.x, q.success + 1, q.clock + 1⟩ : Lemma3Trace)
    · subst z
      constructor
      · rcases hbound with hbad | htarget
        · exact Or.inl hbad
        · exact Or.inr (Or.inl htarget)
      · rfl
    · simp [hz] at hqz
  · have hbad : ¬ Lemma3Bad x₀ Δ q.x := by
      exact fun h => hbound (Or.inl h)
    have htarget : ¬ Lemma3Target n Δ q.x := by
      exact fun h => hbound (Or.inr h)
    have hphys :=
      lemma3_live_physical hpop hgap hΔ0 hΔn hbad htarget
    rw [lemma3TraceStep_of_live n x₀ Δ q hbound hphys,
      PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
    push Not at hqz
    obtain ⟨up, hup⟩ := hqz
    let next : Lemma3Trace :=
      ⟨if up then q.x + 1 else q.x - 1,
        if up then q.success + 1 else q.success,
        q.clock + 1⟩
    by_cases hz : z = next
    · subst z
      have hrel :
          q.x + q.clock = x₀ + 2 * q.success := by
        rcases hq with hq | hq | hq
        · exact False.elim (hbad hq)
        · exact False.elim (htarget hq)
        · exact hq
      constructor
      · right
        right
        cases up <;> simp [next] at hrel ⊢ <;> omega
      · simp [next]
    · simp [next, hz] at hup

/-- The clock component advances on every supported lifted step, independently
of the displacement invariant. -/
theorem lemma3TraceStep_clock_of_apply_ne_zero
    (n x₀ Δ : ℕ) (q z : Lemma3Trace)
    (hqz : lemma3TraceStep n x₀ Δ q z ≠ 0) :
    z.clock = q.clock + 1 := by
  classical
  by_cases hbound :
      Lemma3Bad x₀ Δ q.x ∨ Lemma3Target n Δ q.x
  · rw [lemma3TraceStep_of_boundary n x₀ Δ q hbound,
      PMF.pure_apply] at hqz
    by_cases hz :
        z = (⟨q.x, q.success + 1, q.clock + 1⟩ : Lemma3Trace)
    · subst z
      rfl
    · simp [hz] at hqz
  · by_cases hphys : 3 ≤ n ∧ 0 < q.x ∧ q.x < n
    · rw [lemma3TraceStep_of_live n x₀ Δ q hbound hphys,
        PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
      push Not at hqz
      obtain ⟨up, hup⟩ := hqz
      let next : Lemma3Trace :=
        ⟨if up then q.x + 1 else q.x - 1,
          if up then q.success + 1 else q.success,
          q.clock + 1⟩
      by_cases hz : z = next
      · subst z
        rfl
      · simp [next, hz] at hup
    · unfold lemma3TraceStep at hqz
      rw [if_neg hbound, dif_neg hphys, PMF.pure_apply] at hqz
      by_cases hz :
          z = (⟨q.x, q.success + 1, q.clock + 1⟩ : Lemma3Trace)
      · subst z
        rfl
      · simp [hz] at hqz

private theorem iter_support_closed_local
    {α : Type*} (K : α → PMF α) (P : α → Prop)
    (hstep : ∀ s, P s → ∀ z, K s z ≠ 0 → P z) :
    ∀ T s z, P s → iter K T s z ≠ 0 → P z := by
  intro T
  induction T with
  | zero =>
      intro s z hs hz
      simp only [iter, PMF.pure_apply] at hz
      by_cases h : z = s
      · rwa [h]
      · simp [h] at hz
  | succ T ih =>
      intro s z hs hz
      rw [iter_succ, PMF.bind_apply] at hz
      by_contra hzP
      apply hz
      rw [ENNReal.tsum_eq_zero]
      intro a
      by_cases hKa : K s a = 0
      · simp [hKa]
      · have haP := hstep s hs a hKa
        have hiaz : iter K T a z = 0 := by
          by_contra hne
          exact hzP (ih a z haP hne)
        simp [hiaz]

private theorem iter_support_count_add_one
    {α : Type*} (K : α → PMF α) (count : α → ℕ)
    (hstep : ∀ s z, K s z ≠ 0 → count z = count s + 1) :
    ∀ T s z, iter K T s z ≠ 0 → count z = count s + T := by
  intro T
  induction T with
  | zero =>
      intro s z hz
      simp only [iter, PMF.pure_apply] at hz
      by_cases h : z = s
      · subst z
        simp
      · simp [h] at hz
  | succ T ih =>
      intro s z hz
      rw [iter_succ, PMF.bind_apply, Ne, ENNReal.tsum_eq_zero] at hz
      push Not at hz
      obtain ⟨a, ha⟩ := hz
      have hK : K s a ≠ 0 := by
        intro hzero
        simp [hzero] at ha
      have hiter : iter K T a z ≠ 0 := by
        intro hzero
        simp [hzero] at ha
      rw [ih a z hiter, hstep s a hK]
      omega

/-- The displacement invariant holds at every supported terminal trace. -/
theorem lemma3Trace_iter_inv
    {n x₀ y₀ Δ T : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (z : Lemma3Trace)
    (hz :
      iter (lemma3TraceStep n x₀ Δ) T (lemma3Initial x₀) z ≠ 0) :
    z.Inv n x₀ Δ := by
  apply iter_support_closed_local
    (lemma3TraceStep n x₀ Δ) (Lemma3Trace.Inv n x₀ Δ)
      (fun q hq z hqz =>
        (lemma3TraceStep_support hpop hgap hΔ0 hΔn q hq z hqz).1)
      T (lemma3Initial x₀) z
  · exact lemma3Initial_inv n x₀ Δ
  · exact hz

/-- After `T` supported lifted steps, the explicit slot clock is exactly `T`. -/
theorem lemma3Trace_iter_clock
    {n x₀ Δ T : ℕ}
    (z : Lemma3Trace)
    (hz :
      iter (lemma3TraceStep n x₀ Δ) T (lemma3Initial x₀) z ≠ 0) :
    z.clock = T := by
  have hclock :=
    iter_support_count_add_one
      (lemma3TraceStep n x₀ Δ) Lemma3Trace.clock
      (lemma3TraceStep_clock_of_apply_ne_zero n x₀ Δ)
      T (lemma3Initial x₀) z hz
  simpa [lemma3Initial] using hclock

/-- Forgetting the proof counters makes every lifted step either one genuine
embedded productive reaction or a physical self-loop. -/
theorem lemma3TraceStep_isLazyProjection
    (n x₀ Δ : ℕ) :
    IsLazyProjection (productiveTriChain n)
      (lemma3TraceStep n x₀ Δ) Lemma3Trace.toX := by
  classical
  intro q
  by_cases hbound :
      Lemma3Bad x₀ Δ q.x ∨ Lemma3Target n Δ q.x
  · rw [lemma3TraceStep_of_boundary n x₀ Δ q hbound]
    right
    exact PMF.pure_map Lemma3Trace.toX
      ⟨q.x, q.success + 1, q.clock + 1⟩
  · by_cases hphys : 3 ≤ n ∧ 0 < q.x ∧ q.x < n
    · rw [lemma3TraceStep_of_live n x₀ Δ q hbound hphys]
      left
      change _ = productiveTriChain n q.x
      unfold productiveTriChain
      rw [dif_pos hphys]
      unfold productiveTriInterior
      rw [PMF.map_comp]
      apply congrArg
        (fun f =>
          PMF.map f
            (productiveDirectionPMF (q.x - 1) (n - q.x - 1)
              (by omega)))
      funext up
      cases up
      · simp [Lemma3Trace.toX]
      · simp [Lemma3Trace.toX]
        omega
    · unfold lemma3TraceStep
      rw [if_neg hbound, dif_neg hphys]
      right
      exact PMF.pure_map Lemma3Trace.toX
        ⟨q.x, q.success + 1, q.clock + 1⟩

/-- Uniform productive-up probability used in the paper's Lemma 3 proof. -/
noncomputable def lemma3SuccessP (n Δ : ℕ) : ℝ≥0 :=
  ((2 * n + Δ : ℕ) : ℝ≥0) / ((4 * n : ℕ) : ℝ≥0)

/-- Harmonic safety base for the half-gap downcrossing. -/
noncomputable def lemma3SafetyBase (n Δ : ℕ) : ℝ≥0∞ :=
  ((2 * n - Δ : ℕ) : ℝ≥0∞) /
    ((2 * n + Δ : ℕ) : ℝ≥0∞)

/-- Multiplicative Chernoff deviation used at the `2n` deadline. -/
noncomputable def lemma3ChernoffDelta (n Δ : ℕ) : ℝ :=
  (Δ : ℝ) / (4 * (n : ℝ) + 2 * (Δ : ℝ))

theorem lemma3SuccessP_le_one
    {n Δ : ℕ} (hΔn : Δ < n) :
    lemma3SuccessP n Δ ≤ 1 := by
  unfold lemma3SuccessP
  rw [div_le_one]
  · exact_mod_cast (show 2 * n + Δ ≤ 4 * n by omega)
  · exact_mod_cast (show 0 < 4 * n by omega)

/-- Shared division-free live-state arithmetic.  It simultaneously implies
the productive up-probability floor and the Feller odds bound. -/
theorem lemma3_live_cross
    {n x₀ y₀ Δ a b : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ)
    (hstate : a + b + 2 = n)
    (hbad : ¬ Lemma3Bad x₀ Δ (a + 1)) :
    (2 * n + Δ) * (a + b) ≤ (4 * n) * a := by
  have hkBounds := lemma3Quarter_bounds Δ
  have hkx : lemma3Quarter Δ ≤ x₀ :=
    (lemma3Quarter_le hΔ0).trans (by omega)
  have hax : x₀ - lemma3Quarter Δ ≤ a := by
    unfold Lemma3Bad at hbad
    omega
  have hcur : 2 * b + Δ ≤ 2 * a := by
    omega
  have hmul1 := Nat.mul_le_mul_left n hcur
  have habn : a + b ≤ n := by omega
  have hmul2 := Nat.mul_le_mul_left Δ habn
  nlinarith

/-- The live productive-up probability is at least the fixed paper floor. -/
theorem lemma3SuccessP_le_live
    {n x₀ y₀ Δ a b : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hstate : a + b + 2 = n)
    (hbad : ¬ Lemma3Bad x₀ Δ (a + 1)) :
    lemma3SuccessP n Δ ≤
      ((a : ℝ≥0) / ((a + b : ℕ) : ℝ≥0)) := by
  unfold lemma3SuccessP
  rw [div_le_div_iff₀]
  · have hcross :=
      lemma3_live_cross hpop hgap hΔ0 hstate hbad
    exact_mod_cast (show
      (2 * n + Δ) * (a + b) ≤ a * (4 * n) by
        simpa [mul_comm] using hcross)
  · exact_mod_cast (show 0 < 4 * n by omega)
  · exact_mod_cast (show 0 < a + b by omega)

/-- The same live arithmetic in the harmonic-odds form used for safety. -/
theorem lemma3_live_safety_cross
    {n x₀ y₀ Δ a b : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hstate : a + b + 2 = n)
    (hbad : ¬ Lemma3Bad x₀ Δ (a + 1)) :
    b * (2 * n + Δ) ≤ a * (2 * n - Δ) := by
  have hcross :=
    lemma3_live_cross hpop hgap hΔ0 hstate hbad
  have hsplit : (2 * n - Δ) + (2 * n + Δ) = 4 * n := by
    omega
  nlinarith

/-- On every live productive state, the down mass is at most the up mass
times the fixed harmonic safety base. -/
theorem lemma3_down_le_up_mul_safety
    {n x₀ y₀ Δ a b : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (hstate : a + b + 2 = n)
    (hbad : ¬ Lemma3Bad x₀ Δ (a + 1)) :
    (b : ℝ≥0∞) / (a + b : ℝ≥0∞) ≤
      (a : ℝ≥0∞) / (a + b : ℝ≥0∞) *
        lemma3SafetyBase n Δ := by
  have hA0 : (((2 * n + Δ : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast (show 2 * n + Δ ≠ 0 by omega)
  have hAtop : (((2 * n + Δ : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hba :
      (b : ℝ≥0∞) ≤
        (a : ℝ≥0∞) * lemma3SafetyBase n Δ := by
    unfold lemma3SafetyBase
    rw [← mul_div_assoc,
      ENNReal.le_div_iff_mul_le (Or.inl hA0) (Or.inl hAtop)]
    exact_mod_cast
      lemma3_live_safety_cross hpop hgap hΔ0 hΔn hstate hbad
  calc
    (b : ℝ≥0∞) / (a + b : ℝ≥0∞) ≤
        ((a : ℝ≥0∞) * lemma3SafetyBase n Δ) /
          (a + b : ℝ≥0∞) :=
      ENNReal.div_le_div_right hba _
    _ = (a : ℝ≥0∞) / (a + b : ℝ≥0∞) *
        lemma3SafetyBase n Δ := by
      simp only [div_eq_mul_inv]
      ac_rfl

theorem lemma3SafetyBase_le_one
    {n Δ : ℕ} (hΔn : Δ < n) :
    lemma3SafetyBase n Δ ≤ 1 := by
  unfold lemma3SafetyBase
  have hden0 : (((2 * n + Δ : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast (show 2 * n + Δ ≠ 0 by omega)
  have hdenTop : (((2 * n + Δ : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  apply (ENNReal.div_le_iff hden0 hdenTop).2
  simpa using (show
    (((2 * n - Δ : ℕ) : ℝ≥0∞)) ≤
      (((2 * n + Δ : ℕ) : ℝ≥0∞)) by
        exact_mod_cast (show 2 * n - Δ ≤ 2 * n + Δ by omega))

theorem lemma3SafetyBase_ne_zero
    {n Δ : ℕ} (hΔn : Δ < n) :
    lemma3SafetyBase n Δ ≠ 0 := by
  unfold lemma3SafetyBase
  simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
  constructor
  · exact_mod_cast (show 2 * n - Δ ≠ 0 by omega)
  · exact ENNReal.natCast_ne_top _

/-- The fixed success floor and its NNReal complement form a probability pair. -/
theorem lemma3SuccessP_add_complement
    {n Δ : ℕ} (hΔn : Δ < n) :
    (lemma3SuccessP n Δ : ℝ≥0∞) +
      ((1 - lemma3SuccessP n Δ : ℝ≥0) : ℝ≥0∞) = 1 := by
  have hp := lemma3SuccessP_le_one hΔn
  have hnn :
      lemma3SuccessP n Δ +
        (1 - lemma3SuccessP n Δ) = (1 : ℝ≥0) :=
    add_tsub_cancel_of_le hp
  exact_mod_cast hnn

/-- Every lifted slot satisfies the adapted Bernoulli moment inequality at any
lower-tail base `w ≤ 1`. -/
theorem lemma3TraceStep_count_moment
    {n x₀ y₀ Δ : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (w : ℝ≥0∞) (hw : w ≤ 1) :
    ∀ q,
      expect (lemma3TraceStep n x₀ Δ q)
          (fun z => w ^ z.success) ≤
        (((1 - lemma3SuccessP n Δ : ℝ≥0) : ℝ≥0∞) +
            (lemma3SuccessP n Δ : ℝ≥0∞) * w) *
          w ^ q.success := by
  intro q
  have hpSum := lemma3SuccessP_add_complement hΔn
  have hpOne :
      (lemma3SuccessP n Δ : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast lemma3SuccessP_le_one hΔn
  by_cases hbound :
      Lemma3Bad x₀ Δ q.x ∨ Lemma3Target n Δ q.x
  · apply count_step_of_masses
      (K := lemma3TraceStep n x₀ Δ)
      (count := Lemma3Trace.success) (s := q) (w := w)
      (q := 1) (q' := 0)
      (p := (lemma3SuccessP n Δ : ℝ≥0∞))
      (p' := ((1 - lemma3SuccessP n Δ : ℝ≥0) : ℝ≥0∞))
    · simp
    · exact hpSum
    · exact hw
    · exact hpOne
    · rw [lemma3TraceStep_of_boundary n x₀ Δ q hbound,
        expect_pure]
      simp
  · have hbad : ¬ Lemma3Bad x₀ Δ q.x :=
      fun h => hbound (Or.inl h)
    have htarget : ¬ Lemma3Target n Δ q.x :=
      fun h => hbound (Or.inr h)
    have hphys :=
      lemma3_live_physical hpop hgap hΔ0 hΔn hbad htarget
    obtain ⟨a, ha⟩ : ∃ a, q.x = a + 1 :=
      ⟨q.x - 1, by omega⟩
    obtain ⟨b, hstate⟩ : ∃ b, a + b + 2 = n :=
      ⟨n - a - 2, by omega⟩
    have hprod : 0 < a + b := by omega
    have hbadA : ¬ Lemma3Bad x₀ Δ (a + 1) := by
      simpa [ha] using hbad
    have hpLiveNN :
        lemma3SuccessP n Δ ≤
          ((a : ℝ≥0) / ((a + b : ℕ) : ℝ≥0)) :=
      lemma3SuccessP_le_live hpop hgap hΔ0 hΔn hstate hbadA
    have hpLive :
        (lemma3SuccessP n Δ : ℝ≥0∞) ≤
          (a : ℝ≥0∞) / (a + b : ℝ≥0∞) := by
      have hdenNN : (((a + b : ℕ) : ℝ≥0)) ≠ 0 := by
        exact_mod_cast hprod.ne'
      rw [← Nat.cast_add]
      change
        ((lemma3SuccessP n Δ : ℝ≥0) : ℝ≥0∞) ≤
          (((a : ℝ≥0) : ℝ≥0∞) /
            (((a + b : ℕ) : ℝ≥0) : ℝ≥0∞))
      rw [← ENNReal.coe_div hdenNN]
      exact ENNReal.coe_le_coe.mpr hpLiveNN
    have haq : q.x - 1 = a := by omega
    have hbq : n - q.x - 1 = b := by omega
    apply count_step_of_masses
      (K := lemma3TraceStep n x₀ Δ)
      (count := Lemma3Trace.success) (s := q) (w := w)
      (q := (a : ℝ≥0∞) / (a + b : ℝ≥0∞))
      (q' := (b : ℝ≥0∞) / (a + b : ℝ≥0∞))
      (p := (lemma3SuccessP n Δ : ℝ≥0∞))
      (p' := ((1 - lemma3SuccessP n Δ : ℝ≥0) : ℝ≥0∞))
    · simpa [add_comm] using
        productiveTriInterior_masses a b hprod
    · exact hpSum
    · exact hw
    · exact hpLive
    · rw [lemma3TraceStep_of_live n x₀ Δ q hbound hphys,
        expect_map]
      simp only [haq, hbq]
      unfold expect
      rw [tsum_fintype]
      rw [show (Finset.univ : Finset Bool) = {false, true} by
        ext up
        cases up <;> simp]
      simp

/-- The harmonic potential is a supermartingale for every lifted productive
slot, including the artificial boundary slots. -/
theorem lemma3TraceStep_safety_moment
    {n x₀ y₀ Δ : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    ∀ q,
      expect (lemma3TraceStep n x₀ Δ q)
          (fun z => lemma3SafetyBase n Δ ^ z.x) ≤
        lemma3SafetyBase n Δ ^ q.x := by
  intro q
  by_cases hbound :
      Lemma3Bad x₀ Δ q.x ∨ Lemma3Target n Δ q.x
  · rw [lemma3TraceStep_of_boundary n x₀ Δ q hbound,
      expect_pure]
  · have hbad : ¬ Lemma3Bad x₀ Δ q.x :=
      fun h => hbound (Or.inl h)
    have htarget : ¬ Lemma3Target n Δ q.x :=
      fun h => hbound (Or.inr h)
    have hphys :=
      lemma3_live_physical hpop hgap hΔ0 hΔn hbad htarget
    obtain ⟨a, ha⟩ : ∃ a, q.x = a + 1 :=
      ⟨q.x - 1, by omega⟩
    obtain ⟨b, hstate⟩ : ∃ b, a + b + 2 = n :=
      ⟨n - a - 2, by omega⟩
    have hprod : 0 < a + b := by omega
    have haq : q.x - 1 = a := by omega
    have hbq : n - q.x - 1 = b := by omega
    have hbadA : ¬ Lemma3Bad x₀ Δ (a + 1) := by
      simpa [ha] using hbad
    have hsum :
        (b : ℝ≥0∞) / (a + b : ℝ≥0∞) + 0 +
            (a : ℝ≥0∞) / (a + b : ℝ≥0∞) = 1 := by
      simpa using productiveTriInterior_masses a b hprod
    have hdrift :
        (b : ℝ≥0∞) / (a + b : ℝ≥0∞) ≤
          (a : ℝ≥0∞) / (a + b : ℝ≥0∞) *
            lemma3SafetyBase n Δ :=
      lemma3_down_le_up_mul_safety
        hpop hgap hΔ0 hΔn hstate hbadA
    have hcore :
        (b : ℝ≥0∞) / (a + b : ℝ≥0∞) +
              0 * lemma3SafetyBase n Δ +
              (a : ℝ≥0∞) / (a + b : ℝ≥0∞) *
                lemma3SafetyBase n Δ ^ 2 ≤
            lemma3SafetyBase n Δ :=
      three_term_drift_ennreal hsum
        (lemma3SafetyBase_le_one hΔn) hdrift
    have hdecomp :
        expect (lemma3TraceStep n x₀ Δ q)
            (fun z => lemma3SafetyBase n Δ ^ z.x) =
          (b : ℝ≥0∞) / (a + b : ℝ≥0∞) *
              lemma3SafetyBase n Δ ^ a +
            (a : ℝ≥0∞) / (a + b : ℝ≥0∞) *
              lemma3SafetyBase n Δ ^ (a + 2) := by
      rw [lemma3TraceStep_of_live n x₀ Δ q hbound hphys,
        expect_map]
      simp only [haq, hbq]
      unfold expect
      rw [tsum_fintype]
      rw [show (Finset.univ : Finset Bool) = {false, true} by
        ext up
        cases up <;> simp]
      simp [ha]
    rw [hdecomp, ha]
    calc
      (b : ℝ≥0∞) / (a + b : ℝ≥0∞) *
              lemma3SafetyBase n Δ ^ a +
            (a : ℝ≥0∞) / (a + b : ℝ≥0∞) *
              lemma3SafetyBase n Δ ^ (a + 2) =
          lemma3SafetyBase n Δ ^ a *
            ((b : ℝ≥0∞) / (a + b : ℝ≥0∞) +
              0 * lemma3SafetyBase n Δ +
              (a : ℝ≥0∞) / (a + b : ℝ≥0∞) *
                lemma3SafetyBase n Δ ^ 2) := by
            rw [pow_add]
            ring
      _ ≤ lemma3SafetyBase n Δ ^ a *
            lemma3SafetyBase n Δ :=
        mul_le_mul_right hcore _
      _ = lemma3SafetyBase n Δ ^ (a + 1) := by
        rw [pow_succ]

/-- Feller half-gap safety bound for the counted lift, uniformly in the
productive-slot horizon. -/
theorem lemma3Trace_bad_mass
    {n x₀ y₀ Δ T : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    (∑' z : Lemma3Trace,
        if Lemma3Bad x₀ Δ z.x then
          iter (lemma3TraceStep n x₀ Δ) T
            (lemma3Initial x₀) z
        else 0) ≤
      lemma3SafetyBase n Δ ^ lemma3Quarter Δ := by
  have hkx : lemma3Quarter Δ ≤ x₀ :=
    (lemma3Quarter_le hΔ0).trans (by omega)
  have hxsplit :
      (lemma3Initial x₀).x =
        (x₀ - lemma3Quarter Δ) + lemma3Quarter Δ := by
    simp [lemma3Initial]
    omega
  simpa [Lemma3Bad] using
    ruin_le_u
      (lemma3TraceStep n x₀ Δ) Lemma3Trace.x
      (lemma3SafetyBase n Δ)
      (lemma3SafetyBase_le_one hΔn)
      (lemma3SafetyBase_ne_zero hΔn)
      (fun q => lemma3SafetyBase n Δ ^ q.x)
      (fun _ => rfl)
      (lemma3TraceStep_safety_moment hpop hgap hΔ0 hΔn)
      T (x₀ - lemma3Quarter Δ) (lemma3Quarter Δ)
      (lemma3Initial x₀) hxsplit

/-- The Feller safety power has the first explicit exponential error printed
in paper Lemma 3. -/
theorem lemma3Safety_power_exp
    {n Δ : ℕ} (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    lemma3SafetyBase n Δ ^ lemma3Quarter Δ ≤
      ENNReal.ofReal
        (Real.exp
          (-((Δ : ℝ) ^ 2 /
            (4 * (n : ℝ) + 2 * (Δ : ℝ))))) := by
  unfold lemma3SafetyBase
  apply ratio_pow_le_ofReal_exp
      (2 * n + Δ) (2 * n - Δ) (lemma3Quarter Δ)
      ((Δ : ℝ) ^ 2 /
        (4 * (n : ℝ) + 2 * (Δ : ℝ)))
  · omega
  · omega
  · have hq := (lemma3Quarter_bounds Δ).1
    have hqR :
        (Δ : ℝ) ≤ 4 * (lemma3Quarter Δ : ℝ) := by
      exact_mod_cast hq
    have hnR : (0 : ℝ) < n := by
      exact_mod_cast (lt_trans hΔ0 hΔn)
    have hΔR : (0 : ℝ) ≤ Δ := by positivity
    have hden :
        (0 : ℝ) < 2 * (n : ℝ) + (Δ : ℝ) := by
      positivity
    have hfactor :
        0 ≤ (Δ : ℝ) /
          (2 * (n : ℝ) + (Δ : ℝ)) :=
      div_nonneg hΔR hden.le
    have hrewrite :
        (Δ : ℝ) ^ 2 /
            (4 * (n : ℝ) + 2 * (Δ : ℝ)) =
          ((Δ : ℝ) / 2) *
            ((Δ : ℝ) /
              (2 * (n : ℝ) + (Δ : ℝ))) := by
      field_simp
      ring
    rw [hrewrite]
    calc
      ((Δ : ℝ) / 2) *
            ((Δ : ℝ) /
              (2 * (n : ℝ) + (Δ : ℝ))) ≤
          (2 * (lemma3Quarter Δ : ℝ)) *
            ((Δ : ℝ) /
              (2 * (n : ℝ) + (Δ : ℝ))) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hfactor
      _ = (lemma3Quarter Δ : ℝ) *
          (((2 * n + Δ : ℕ) : ℝ) -
            ((2 * n - Δ : ℕ) : ℝ)) /
          ((2 * n + Δ : ℕ) : ℝ) := by
        rw [Nat.cast_sub (show Δ ≤ 2 * n by omega)]
        norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        field_simp
        ring

/-- The Chernoff deviation is nonnegative. -/
theorem lemma3ChernoffDelta_nonneg (n Δ : ℕ) :
    0 ≤ lemma3ChernoffDelta n Δ := by
  unfold lemma3ChernoffDelta
  positivity

/-- Under the hypotheses of paper Lemma 3, the Chernoff deviation is at most
one. -/
theorem lemma3ChernoffDelta_le_one
    {n Δ : ℕ} (hΔn : Δ < n) :
    lemma3ChernoffDelta n Δ ≤ 1 := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (Nat.zero_lt_of_lt hΔn)
  unfold lemma3ChernoffDelta
  rw [div_le_iff₀ (by positivity : (0 : ℝ) <
    4 * (n : ℝ) + 2 * (Δ : ℝ))]
  norm_num
  nlinarith

/-- Real coercion of the fixed productive-up probability. -/
theorem lemma3SuccessP_coe
    {n Δ : ℕ} :
    (lemma3SuccessP n Δ : ℝ) =
      ((2 * n + Δ : ℕ) : ℝ) / ((4 * n : ℕ) : ℝ) := by
  unfold lemma3SuccessP
  rw [NNReal.coe_div]
  norm_num

/-- Exact real mean after `2n` trials at the fixed productive-up floor. -/
theorem lemma3Deadline_mean
    {n Δ : ℕ} (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    (1 - lemma3ChernoffDelta n Δ) *
        (((2 * n : ℕ) : ℝ) * (lemma3SuccessP n Δ : ℝ)) =
      (n : ℝ) + (Δ : ℝ) / 4 := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_trans hΔ0 hΔn)
  rw [lemma3SuccessP_coe]
  unfold lemma3ChernoffDelta
  norm_num [Nat.cast_mul, Nat.cast_add]
  field_simp
  ring

/-- The integral cutoff lies below the multiplicative-Chernoff threshold. -/
theorem lemma3Deadline_cutoff
    {n Δ : ℕ} (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    ((n + lemma3Quarter Δ - 1 : ℕ) : ℝ) ≤
      (1 - lemma3ChernoffDelta n Δ) *
        (((2 * n : ℕ) : ℝ) * (lemma3SuccessP n Δ : ℝ)) := by
  have hfour : 4 * (lemma3Quarter Δ - 1) ≤ Δ := by
    have hq := lemma3Quarter_bounds Δ
    omega
  have hfourR :
      (4 : ℝ) * ((lemma3Quarter Δ - 1 : ℕ) : ℝ) ≤ (Δ : ℝ) := by
    exact_mod_cast hfour
  have hk : 0 < lemma3Quarter Δ := lemma3Quarter_pos hΔ0
  rw [show n + lemma3Quarter Δ - 1 =
      n + (lemma3Quarter Δ - 1) by omega,
    Nat.cast_add, lemma3Deadline_mean hΔ0 hΔn]
  nlinarith

/-- The adapted Chernoff exponent simplifies to the explicit constant printed
in paper Lemma 3. -/
theorem lemma3Deadline_exponent
    {n Δ : ℕ} (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    lemma3ChernoffDelta n Δ ^ 2 *
          (((2 * n : ℕ) : ℝ) * (lemma3SuccessP n Δ : ℝ)) / 2 =
      (Δ : ℝ) ^ 2 /
        (32 * (n : ℝ) + 16 * (Δ : ℝ)) := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_trans hΔ0 hΔn)
  rw [lemma3SuccessP_coe]
  unfold lemma3ChernoffDelta
  norm_num [Nat.cast_mul, Nat.cast_add]
  field_simp
  ring

/-- Deadline half of paper Lemma 3: after `2n` lifted productive slots, the
mass with too few productive-up directions has the printed Chernoff bound. -/
theorem lemma3Trace_low_success
    {n x₀ y₀ Δ : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    (∑' z : Lemma3Trace,
        if z.success ≤ n + lemma3Quarter Δ - 1 then
          iter (lemma3TraceStep n x₀ Δ) (2 * n)
            (lemma3Initial x₀) z
        else 0) ≤
      ENNReal.ofReal
        (Real.exp
          (-((Δ : ℝ) ^ 2 /
            (32 * (n : ℝ) + 16 * (Δ : ℝ))))) := by
  have hraw :=
    adapted_multiplicative_lower_tail
      (lemma3TraceStep n x₀ Δ) Lemma3Trace.success
      (lemma3Initial x₀)
      (lemma3SuccessP n Δ) (lemma3SuccessP_le_one hΔn)
      (lemma3ChernoffDelta n Δ)
      (lemma3ChernoffDelta_nonneg n Δ)
      (lemma3ChernoffDelta_le_one hΔn)
      (2 * n) (n + lemma3Quarter Δ - 1)
      (lemma3Deadline_cutoff hΔ0 hΔn)
      (by rfl)
      (lemma3TraceStep_count_moment hpop hgap hΔ0 hΔn
        (ENNReal.ofReal
          (Real.exp (-lemma3ChernoffDelta n Δ)))
        (by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal <|
            Real.exp_le_one_iff.mpr
              (neg_nonpos.mpr
                (lemma3ChernoffDelta_nonneg n Δ))))
  have hneg :
      -(lemma3ChernoffDelta n Δ ^ 2 *
          (((2 * n : ℕ) : ℝ) *
            (lemma3SuccessP n Δ : ℝ))) / 2 =
        -((Δ : ℝ) ^ 2 /
          (32 * (n : ℝ) + 16 * (Δ : ℝ))) := by
    rw [neg_div, lemma3Deadline_exponent hΔ0 hΔn]
  rw [hneg] at hraw
  exact hraw

/-- Every supported terminal trace that misses the target has either crossed
the Feller safety boundary or belongs to the Chernoff low-success event. -/
theorem lemma3Trace_terminal_cover
    {n x₀ y₀ Δ : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n)
    (z : Lemma3Trace)
    (hz :
      iter (lemma3TraceStep n x₀ Δ) (2 * n)
        (lemma3Initial x₀) z ≠ 0)
    (htarget : ¬ Lemma3Target n Δ z.x) :
    Lemma3Bad x₀ Δ z.x ∨
      z.success ≤ n + lemma3Quarter Δ - 1 := by
  have hinv :=
    lemma3Trace_iter_inv hpop hgap hΔ0 hΔn z hz
  have hclock :=
    lemma3Trace_iter_clock z hz
  rcases hinv with hbad | hhit | hrel
  · exact Or.inl hbad
  · exact False.elim (htarget hhit)
  · right
    by_contra hsuccess
    have hk0 : 0 < lemma3Quarter Δ :=
      lemma3Quarter_pos hΔ0
    have hs :
        n + lemma3Quarter Δ ≤ z.success := by
      omega
    have hquarter := (lemma3Quarter_bounds Δ).1
    have hdouble :
        n + 2 * Δ ≤ 2 * z.x := by
      omega
    apply htarget
    unfold Lemma3Target
    exact (Nat.add_le_add_left (min_le_left (2 * Δ) n) n).trans
      hdouble

/-- Terminal target failure for the counted lift splits into exactly the two
paper events: the Feller bad boundary and the low-success deadline event. -/
theorem lemma3Trace_failure_split
    {n x₀ y₀ Δ : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    terminalFailureMass
        (iter (lemma3TraceStep n x₀ Δ) (2 * n)
          (lemma3Initial x₀))
        (fun z => Lemma3Target n Δ z.x) ≤
      (∑' z : Lemma3Trace,
        if Lemma3Bad x₀ Δ z.x then
          iter (lemma3TraceStep n x₀ Δ) (2 * n)
            (lemma3Initial x₀) z
        else 0) +
      ∑' z : Lemma3Trace,
        if z.success ≤ n + lemma3Quarter Δ - 1 then
          iter (lemma3TraceStep n x₀ Δ) (2 * n)
            (lemma3Initial x₀) z
        else 0 := by
  rw [← ENNReal.tsum_add]
  unfold terminalFailureMass
  refine ENNReal.tsum_le_tsum fun z => ?_
  let mass :=
    iter (lemma3TraceStep n x₀ Δ) (2 * n)
      (lemma3Initial x₀) z
  by_cases hmass : mass = 0
  · simp [mass, hmass]
  · have hmass' :
        iter (lemma3TraceStep n x₀ Δ) (2 * n)
          (lemma3Initial x₀) z ≠ 0 := by
      simpa [mass] using hmass
    by_cases htarget : Lemma3Target n Δ z.x
    · simp [htarget]
    · rcases lemma3Trace_terminal_cover
          hpop hgap hΔ0 hΔn z hmass' htarget with hbad | hlow
      · simp [htarget, hbad]
      · simp [htarget, hlow]

/-- The counted trace misses the doubled-gap target only through the two
explicit error events displayed in the proof of paper Lemma 3. -/
theorem lemma3Trace_failure_explicit
    {n x₀ y₀ Δ : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    terminalFailureMass
        (iter (lemma3TraceStep n x₀ Δ) (2 * n)
          (lemma3Initial x₀))
        (fun z => Lemma3Target n Δ z.x) ≤
      ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (4 * (n : ℝ) + 2 * (Δ : ℝ))))) +
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (32 * (n : ℝ) + 16 * (Δ : ℝ))))) := by
  calc
    terminalFailureMass
        (iter (lemma3TraceStep n x₀ Δ) (2 * n)
          (lemma3Initial x₀))
        (fun z => Lemma3Target n Δ z.x) ≤
      (∑' z : Lemma3Trace,
        if Lemma3Bad x₀ Δ z.x then
          iter (lemma3TraceStep n x₀ Δ) (2 * n)
            (lemma3Initial x₀) z
        else 0) +
      ∑' z : Lemma3Trace,
        if z.success ≤ n + lemma3Quarter Δ - 1 then
          iter (lemma3TraceStep n x₀ Δ) (2 * n)
            (lemma3Initial x₀) z
        else 0 :=
      lemma3Trace_failure_split hpop hgap hΔ0 hΔn
    _ ≤ lemma3SafetyBase n Δ ^ lemma3Quarter Δ +
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (32 * (n : ℝ) + 16 * (Δ : ℝ))))) :=
      add_le_add
        (lemma3Trace_bad_mass
          (T := 2 * n) hpop hgap hΔ0 hΔn)
        (lemma3Trace_low_success hpop hgap hΔ0 hΔn)
    _ ≤ ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (4 * (n : ℝ) + 2 * (Δ : ℝ))))) +
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (32 * (n : ℝ) + 16 * (Δ : ℝ))))) :=
      add_le_add (lemma3Safety_power_exp hΔ0 hΔn) le_rfl

/-- The two explicit errors are both bounded by the single weaker envelope
used in the statement of paper Lemma 3. -/
theorem lemma3_explicit_errors_le_common
    {n Δ : ℕ} (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (4 * (n : ℝ) + 2 * (Δ : ℝ))))) +
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (32 * (n : ℝ) + 16 * (Δ : ℝ))))) ≤
      (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 / (48 * (n : ℝ))))) := by
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast (lt_trans hΔ0 hΔn)
  have hΔnR : (Δ : ℝ) < n := by
    exact_mod_cast hΔn
  have h48 : (0 : ℝ) < 48 * (n : ℝ) := by
    positivity
  have hsafe :
      (0 : ℝ) < 4 * (n : ℝ) + 2 * (Δ : ℝ) := by
    positivity
  have hdeadline :
      (0 : ℝ) < 32 * (n : ℝ) + 16 * (Δ : ℝ) := by
    positivity
  have hsafeDen :
      4 * (n : ℝ) + 2 * (Δ : ℝ) ≤
        48 * (n : ℝ) := by
    linarith
  have hdeadlineDen :
      32 * (n : ℝ) + 16 * (Δ : ℝ) ≤
        48 * (n : ℝ) := by
    linarith
  have hcommonSafety :
      (Δ : ℝ) ^ 2 / (48 * (n : ℝ)) ≤
        (Δ : ℝ) ^ 2 /
          (4 * (n : ℝ) + 2 * (Δ : ℝ)) := by
    rw [div_le_div_iff₀ h48 hsafe]
    exact mul_le_mul_of_nonneg_left hsafeDen (sq_nonneg (Δ : ℝ))
  have hcommonDeadline :
      (Δ : ℝ) ^ 2 / (48 * (n : ℝ)) ≤
        (Δ : ℝ) ^ 2 /
          (32 * (n : ℝ) + 16 * (Δ : ℝ)) := by
    rw [div_le_div_iff₀ h48 hdeadline]
    exact
      mul_le_mul_of_nonneg_left hdeadlineDen (sq_nonneg (Δ : ℝ))
  have hsafety :
      ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (4 * (n : ℝ) + 2 * (Δ : ℝ))))) ≤
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 / (48 * (n : ℝ))))) :=
    ENNReal.ofReal_le_ofReal <|
      Real.exp_le_exp.mpr (neg_le_neg hcommonSafety)
  have hdeadline' :
      ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (32 * (n : ℝ) + 16 * (Δ : ℝ))))) ≤
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 / (48 * (n : ℝ))))) :=
    ENNReal.ofReal_le_ofReal <|
      Real.exp_le_exp.mpr (neg_le_neg hcommonDeadline)
  calc
    ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (4 * (n : ℝ) + 2 * (Δ : ℝ))))) +
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 /
              (32 * (n : ℝ) + 16 * (Δ : ℝ))))) ≤
      ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 / (48 * (n : ℝ))))) +
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 / (48 * (n : ℝ))))) :=
      add_le_add hsafety hdeadline'
    _ = (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 / (48 * (n : ℝ))))) := by
      ring

/-- **Paper Lemma 3.** Starting from signed binary gap `Δ`, the productive
Tri chain reaches signed gap at least `min (2Δ) n` within `2n` productive
reactions except with probability at most the displayed exponential error. -/
theorem lemma3_productive_gap_doubling
    {n x₀ y₀ Δ : ℕ}
    (hpop : x₀ + y₀ = n) (hgap : y₀ + Δ = x₀)
    (hΔ0 : 0 < Δ) (hΔn : Δ < n) :
    terminalFailureMass
        (iter
          (freeze (Lemma3Target n Δ) (productiveTriChain n))
          (2 * n) x₀)
        (Lemma3Target n Δ) ≤
      (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 / (48 * (n : ℝ))))) := by
  have hprojection :=
    targetFreeze_failure_le_lazy_projection
      (Lemma3Target n Δ)
      (productiveTriChain n)
      (lemma3TraceStep n x₀ Δ)
      Lemma3Trace.toX
      (lemma3TraceStep_isLazyProjection n x₀ Δ)
      (2 * n) (lemma3Initial x₀)
  have htrace :
      terminalFailureMass
          (iter (lemma3TraceStep n x₀ Δ) (2 * n)
            (lemma3Initial x₀))
          (fun z => Lemma3Target n Δ z.x) ≤
        (2 : ℝ≥0∞) *
          ENNReal.ofReal
            (Real.exp
              (-((Δ : ℝ) ^ 2 / (48 * (n : ℝ))))) :=
    (lemma3Trace_failure_explicit hpop hgap hΔ0 hΔn).trans
      (lemma3_explicit_errors_le_common hΔ0 hΔn)
  calc
    terminalFailureMass
        (iter
          (freeze (Lemma3Target n Δ) (productiveTriChain n))
          (2 * n) x₀)
        (Lemma3Target n Δ) ≤
      terminalFailureMass
          (iter (lemma3TraceStep n x₀ Δ) (2 * n)
            (lemma3Initial x₀))
          (fun z => Lemma3Target n Δ z.x) := by
      simpa [Lemma3Trace.toX, lemma3Initial] using hprojection
    _ ≤ (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-((Δ : ℝ) ^ 2 / (48 * (n : ℝ))))) :=
      htrace

end Tri
