/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.PaperLemma3

/-!
# Paper Lemma 4: minority extinction in productive-event time

The printed proof uses the false implication that throughout the band
`y ≤ n / k + d`, the productive probability of decreasing `y` remains larger
than `1 - 1 / k`.  It already fails after one adverse productive reaction.

This file proves the claimed asymptotic conclusion with a corrected stopped
argument.  Write `P = n / k` for the initial minority.  We use the smaller
buffer `B = ⌊P / 8⌋`; throughout that band the exact productive kernel has a
uniform adaptive success floor.  A Feller bound controls escape from the band,
and an adapted Chernoff bound controls failure to reach consensus by the
paper's productive deadline.
-/

namespace Tri

open scoped ENNReal NNReal

/-- Corrected safety buffer for paper Lemma 4. -/
def lemma4Buffer (P : ℕ) : ℕ :=
  P / 8

/-- The natural-number floor of the paper's real-valued `2n/(k-2)` horizon.
This is a deliberately stronger integer reading: success by the floor implies
success within the paper's real-valued deadline. -/
def lemma4Horizon (n k : ℕ) : ℕ :=
  (2 * n) / (k - 2)

/-- Minority extinction, expressed on the `X` count. -/
def Lemma4Target (n x : ℕ) : Prop :=
  n ≤ x

/-- Escape upward by one corrected safety buffer in the minority count. -/
def Lemma4Bad (x₀ P x : ℕ) : Prop :=
  x ≤ x₀ - lemma4Buffer P

noncomputable instance lemma4TargetDecidable (n x : ℕ) :
    Decidable (Lemma4Target n x) := by
  unfold Lemma4Target
  infer_instance

noncomputable instance lemma4BadDecidable (x₀ P x : ℕ) :
    Decidable (Lemma4Bad x₀ P x) := by
  unfold Lemma4Bad
  infer_instance

/-- Exact floor bounds for the corrected buffer. -/
theorem lemma4Buffer_bounds (P : ℕ) :
    8 * lemma4Buffer P ≤ P ∧
      P ≤ 8 * lemma4Buffer P + 7 := by
  unfold lemma4Buffer
  omega

theorem lemma4Buffer_pos {P : ℕ} (hP : 8 ≤ P) :
    0 < lemma4Buffer P := by
  unfold lemma4Buffer
  omega

theorem lemma4Buffer_le {P : ℕ} :
    lemma4Buffer P ≤ P := by
  unfold lemma4Buffer
  omega

/-- The floor buffer still contains a fixed fraction of the initial
minority. -/
theorem lemma4_le_sixteen_buffer {P : ℕ} (hP : 8 ≤ P) :
    P ≤ 16 * lemma4Buffer P := by
  have hbounds := lemma4Buffer_bounds P
  have hpos := lemma4Buffer_pos hP
  omega

/-- Fixed adaptive success floor on the corrected live band. -/
noncomputable def lemma4SuccessP (k : ℕ) : ℝ≥0 :=
  ((7 * k - 6 : ℕ) : ℝ≥0) / ((8 * k : ℕ) : ℝ≥0)

/-- Harmonic base for the corrected lower-boundary safety argument. -/
noncomputable def lemma4SafetyBase (x₀ P : ℕ) : ℝ≥0∞ :=
  ((P + lemma4Buffer P - 2 : ℕ) : ℝ≥0∞) /
    ((x₀ - lemma4Buffer P : ℕ) : ℝ≥0∞)

/-- Multiplicative Chernoff deviation for the productive deadline. -/
noncomputable def lemma4ChernoffDelta (k : ℕ) : ℝ :=
  ((k - 2 : ℕ) : ℝ) / (16 * (k : ℝ))

/-- Outside the two stopped boundaries, the state is a genuine interior
productive state. -/
theorem lemma4_live_physical
    {n k P x₀ x : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P)
    (hbad : ¬ Lemma4Bad x₀ P x)
    (htarget : ¬ Lemma4Target n x) :
    3 ≤ n ∧ 0 < x ∧ x < n := by
  have hB : lemma4Buffer P ≤ x₀ := by
    have hBP := lemma4Buffer_le (P := P)
    have h3P : 3 * P ≤ k * P := by
      exact Nat.mul_le_mul_right P hk
    omega
  have hx : x₀ - lemma4Buffer P < x := by
    simpa [Lemma4Bad] using hbad
  have hn : 24 ≤ n := by
    have h3P : 3 * P ≤ k * P := by
      exact Nat.mul_le_mul_right P hk
    omega
  exact ⟨by omega, by omega, by simpa [Lemma4Target] using htarget⟩

/-- Division-free form of the live productive-success floor. -/
theorem lemma4_live_success_cross
    {n k P x₀ a b : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P)
    (hstate : a + b + 2 = n)
    (hbad : ¬ Lemma4Bad x₀ P (a + 1)) :
    (7 * k - 6) * (a + b) ≤ (8 * k) * a := by
  have hB := (lemma4Buffer_bounds P).1
  have hBP : lemma4Buffer P ≤ P := lemma4Buffer_le
  have h3P : 3 * P ≤ k * P := by
    exact Nat.mul_le_mul_right P hk
  have hBx : lemma4Buffer P ≤ x₀ := by
    omega
  have hA : x₀ - lemma4Buffer P ≤ a := by
    unfold Lemma4Bad at hbad
    omega
  have hb : b ≤ P + lemma4Buffer P - 2 := by
    omega
  have hk0 : 0 < k := by omega
  have hscaled :
      8 * k * lemma4Buffer P ≤ k * P := by
    nlinarith [Nat.mul_le_mul_left k hB]
  have hslack :
      (7 * k - 6) * (P + lemma4Buffer P - 2) ≤
        (k + 6) * (x₀ - lemma4Buffer P) := by
    have hkZ : (3 : ℤ) ≤ (k : ℤ) := by
      exact_mod_cast hk
    have hPZ : (0 : ℤ) ≤ (P : ℤ) := by positivity
    have hk0Z : (0 : ℤ) ≤ (k : ℤ) := by positivity
    have hnonneg :
        0 ≤ (P : ℤ) * (k : ℤ) * ((k : ℤ) - 3) :=
      mul_nonneg (mul_nonneg hPZ hk0Z) (by omega)
    have hscaledZ :
        (8 : ℤ) * (k : ℤ) * (lemma4Buffer P : ℤ) ≤
          (k : ℤ) * (P : ℤ) := by
      exact_mod_cast hscaled
    have hpopZ :
        (x₀ : ℤ) + (P : ℤ) = (n : ℤ) := by
      exact_mod_cast hpop
    have hquotZ :
        (k : ℤ) * (P : ℤ) = (n : ℤ) := by
      exact_mod_cast hquot
    have hmainZ :
        (((7 * k - 6 : ℕ) : ℤ) *
            ((P + lemma4Buffer P - 2 : ℕ) : ℤ)) ≤
          (((k + 6 : ℕ) : ℤ) *
            ((x₀ - lemma4Buffer P : ℕ) : ℤ)) := by
      rw [Nat.cast_sub (by omega : 6 ≤ 7 * k),
        Nat.cast_sub (by omega : 2 ≤ P + lemma4Buffer P),
        Nat.cast_sub hBx]
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      nlinarith
    exact_mod_cast hmainZ
  have hbmul :
      (7 * k - 6) * b ≤
        (7 * k - 6) * (P + lemma4Buffer P - 2) :=
    Nat.mul_le_mul_left _ hb
  have hAmul :
      (k + 6) * (x₀ - lemma4Buffer P) ≤
        (k + 6) * a :=
    Nat.mul_le_mul_left _ hA
  calc
    (7 * k - 6) * (a + b) =
        (7 * k - 6) * a + (7 * k - 6) * b := by
      rw [Nat.mul_add]
    _ ≤ (7 * k - 6) * a + (k + 6) * a :=
      Nat.add_le_add_left (hbmul.trans (hslack.trans hAmul)) _
    _ = ((7 * k - 6) + (k + 6)) * a :=
      (Nat.add_mul (7 * k - 6) (k + 6) a).symm
    _ = (8 * k) * a := by
      congr 1
      omega

/-- The live productive-up mass is at least the corrected fixed floor. -/
theorem lemma4SuccessP_le_live
    {n k P x₀ a b : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P)
    (hstate : a + b + 2 = n)
    (hbad : ¬ Lemma4Bad x₀ P (a + 1)) :
    lemma4SuccessP k ≤
      ((a : ℝ≥0) / ((a + b : ℕ) : ℝ≥0)) := by
  unfold lemma4SuccessP
  rw [div_le_div_iff₀]
  · exact_mod_cast (show
      (7 * k - 6) * (a + b) ≤ a * (8 * k) by
        simpa [mul_comm] using
          lemma4_live_success_cross
            hpop hquot hk hP hstate hbad)
  · exact_mod_cast (show 0 < 8 * k by omega)
  · exact_mod_cast (show 0 < a + b by omega)

/-- State of the stopped productive proof: physical `X` count, successful
directions, and consumed productive slots. -/
structure Lemma4Trace where
  x : ℕ
  success : ℕ
  clock : ℕ
  deriving DecidableEq

/-- Corrected stopped lift for paper Lemma 4.  Boundary and nonphysical
states pause physically and receive an artificial success while the clock
continues. -/
noncomputable def lemma4TraceStep
    (n x₀ P : ℕ) : Lemma4Trace → PMF Lemma4Trace := fun q =>
  if Lemma4Bad x₀ P q.x ∨ Lemma4Target n q.x then
    PMF.pure ⟨q.x, q.success + 1, q.clock + 1⟩
  else if h : 3 ≤ n ∧ 0 < q.x ∧ q.x < n then
    (productiveDirectionPMF (q.x - 1) (n - q.x - 1) (by omega)).map
      fun up =>
        ⟨if up then q.x + 1 else q.x - 1,
          if up then q.success + 1 else q.success,
          q.clock + 1⟩
  else
    PMF.pure ⟨q.x, q.success + 1, q.clock + 1⟩

def lemma4Initial (x₀ : ℕ) : Lemma4Trace :=
  { x := x₀, success := 0, clock := 0 }

def Lemma4Trace.toX (q : Lemma4Trace) : ℕ :=
  q.x

/-- Before either boundary is reached, displacement is the difference between
successful and adverse productive directions. -/
def Lemma4Trace.Inv (n x₀ P : ℕ) (q : Lemma4Trace) : Prop :=
  Lemma4Bad x₀ P q.x ∨
    Lemma4Target n q.x ∨
      q.x + q.clock = x₀ + 2 * q.success

theorem lemma4Initial_inv (n x₀ P : ℕ) :
    (lemma4Initial x₀).Inv n x₀ P := by
  right
  right
  simp [lemma4Initial]

theorem lemma4TraceStep_of_boundary
    (n x₀ P : ℕ) (q : Lemma4Trace)
    (hq : Lemma4Bad x₀ P q.x ∨ Lemma4Target n q.x) :
    lemma4TraceStep n x₀ P q =
      PMF.pure ⟨q.x, q.success + 1, q.clock + 1⟩ := by
  unfold lemma4TraceStep
  rw [if_pos hq]

theorem lemma4TraceStep_of_live
    (n x₀ P : ℕ) (q : Lemma4Trace)
    (hbound : ¬ (Lemma4Bad x₀ P q.x ∨ Lemma4Target n q.x))
    (hphys : 3 ≤ n ∧ 0 < q.x ∧ q.x < n) :
    lemma4TraceStep n x₀ P q =
      (productiveDirectionPMF (q.x - 1) (n - q.x - 1)
        (by omega)).map
        (fun up =>
          ⟨if up then q.x + 1 else q.x - 1,
            if up then q.success + 1 else q.success,
            q.clock + 1⟩) := by
  unfold lemma4TraceStep
  rw [if_neg hbound, dif_pos hphys]

/-- One supported trace step preserves the stopped displacement invariant and
advances the productive clock once. -/
theorem lemma4TraceStep_support
    {n k P x₀ : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P)
    (q : Lemma4Trace) (hq : q.Inv n x₀ P)
    (z : Lemma4Trace)
    (hqz : lemma4TraceStep n x₀ P q z ≠ 0) :
    z.Inv n x₀ P ∧ z.clock = q.clock + 1 := by
  classical
  by_cases hbound :
      Lemma4Bad x₀ P q.x ∨ Lemma4Target n q.x
  · rw [lemma4TraceStep_of_boundary n x₀ P q hbound,
      PMF.pure_apply] at hqz
    by_cases hz :
        z = (⟨q.x, q.success + 1, q.clock + 1⟩ : Lemma4Trace)
    · subst z
      constructor
      · rcases hbound with hbad | htarget
        · exact Or.inl hbad
        · exact Or.inr (Or.inl htarget)
      · rfl
    · simp [hz] at hqz
  · have hbad : ¬ Lemma4Bad x₀ P q.x := by
      exact fun h => hbound (Or.inl h)
    have htarget : ¬ Lemma4Target n q.x := by
      exact fun h => hbound (Or.inr h)
    have hphys :=
      lemma4_live_physical hpop hquot hk hP hbad htarget
    rw [lemma4TraceStep_of_live n x₀ P q hbound hphys,
      PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
    push Not at hqz
    obtain ⟨up, hup⟩ := hqz
    let next : Lemma4Trace :=
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

theorem lemma4TraceStep_clock_of_apply_ne_zero
    (n x₀ P : ℕ) (q z : Lemma4Trace)
    (hqz : lemma4TraceStep n x₀ P q z ≠ 0) :
    z.clock = q.clock + 1 := by
  classical
  by_cases hbound :
      Lemma4Bad x₀ P q.x ∨ Lemma4Target n q.x
  · rw [lemma4TraceStep_of_boundary n x₀ P q hbound,
      PMF.pure_apply] at hqz
    by_cases hz :
        z = (⟨q.x, q.success + 1, q.clock + 1⟩ : Lemma4Trace)
    · subst z
      rfl
    · simp [hz] at hqz
  · by_cases hphys : 3 ≤ n ∧ 0 < q.x ∧ q.x < n
    · rw [lemma4TraceStep_of_live n x₀ P q hbound hphys,
        PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hqz
      push Not at hqz
      obtain ⟨up, hup⟩ := hqz
      let next : Lemma4Trace :=
        ⟨if up then q.x + 1 else q.x - 1,
          if up then q.success + 1 else q.success,
          q.clock + 1⟩
      by_cases hz : z = next
      · subst z
        rfl
      · simp [next, hz] at hup
    · unfold lemma4TraceStep at hqz
      rw [if_neg hbound, dif_neg hphys, PMF.pure_apply] at hqz
      by_cases hz :
          z = (⟨q.x, q.success + 1, q.clock + 1⟩ : Lemma4Trace)
      · subst z
        rfl
      · simp [hz] at hqz

private theorem lemma4_iter_support_closed
    {α : Type*} (K : α → PMF α) (Q : α → Prop)
    (hstep : ∀ s, Q s → ∀ z, K s z ≠ 0 → Q z) :
    ∀ T s z, Q s → iter K T s z ≠ 0 → Q z := by
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
      by_contra hzQ
      apply hz
      rw [ENNReal.tsum_eq_zero]
      intro a
      by_cases hKa : K s a = 0
      · simp [hKa]
      · have haQ := hstep s hs a hKa
        have hiaz : iter K T a z = 0 := by
          by_contra hne
          exact hzQ (ih a z haQ hne)
        simp [hiaz]

private theorem lemma4_iter_support_count_add_one
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

theorem lemma4Trace_iter_inv
    {n k P x₀ T : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P)
    (z : Lemma4Trace)
    (hz :
      iter (lemma4TraceStep n x₀ P) T (lemma4Initial x₀) z ≠ 0) :
    z.Inv n x₀ P := by
  apply lemma4_iter_support_closed
    (lemma4TraceStep n x₀ P) (Lemma4Trace.Inv n x₀ P)
      (fun q hq z hqz =>
        (lemma4TraceStep_support hpop hquot hk hP q hq z hqz).1)
      T (lemma4Initial x₀) z
  · exact lemma4Initial_inv n x₀ P
  · exact hz

theorem lemma4Trace_iter_clock
    {n x₀ P T : ℕ}
    (z : Lemma4Trace)
    (hz :
      iter (lemma4TraceStep n x₀ P) T (lemma4Initial x₀) z ≠ 0) :
    z.clock = T := by
  have hclock :=
    lemma4_iter_support_count_add_one
      (lemma4TraceStep n x₀ P) Lemma4Trace.clock
      (lemma4TraceStep_clock_of_apply_ne_zero n x₀ P)
      T (lemma4Initial x₀) z hz
  simpa [lemma4Initial] using hclock

/-- Forgetting the counters makes a lifted step either the physical
productive reaction or a self-loop. -/
theorem lemma4TraceStep_isLazyProjection
    (n x₀ P : ℕ) :
    IsLazyProjection (productiveTriChain n)
      (lemma4TraceStep n x₀ P) Lemma4Trace.toX := by
  classical
  intro q
  by_cases hbound :
      Lemma4Bad x₀ P q.x ∨ Lemma4Target n q.x
  · rw [lemma4TraceStep_of_boundary n x₀ P q hbound]
    right
    exact PMF.pure_map Lemma4Trace.toX
      ⟨q.x, q.success + 1, q.clock + 1⟩
  · by_cases hphys : 3 ≤ n ∧ 0 < q.x ∧ q.x < n
    · rw [lemma4TraceStep_of_live n x₀ P q hbound hphys]
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
      · simp [Lemma4Trace.toX]
      · simp [Lemma4Trace.toX]
        omega
    · unfold lemma4TraceStep
      rw [if_neg hbound, dif_neg hphys]
      right
      exact PMF.pure_map Lemma4Trace.toX
        ⟨q.x, q.success + 1, q.clock + 1⟩

/-- The corrected adaptive success floor is a probability. -/
theorem lemma4SuccessP_le_one
    {k : ℕ} (hk : 3 ≤ k) :
    lemma4SuccessP k ≤ 1 := by
  unfold lemma4SuccessP
  rw [div_le_one]
  · exact_mod_cast (show 7 * k - 6 ≤ 8 * k by omega)
  · exact_mod_cast (show 0 < 8 * k by omega)

theorem lemma4SuccessP_add_complement
    {k : ℕ} (hk : 3 ≤ k) :
    (lemma4SuccessP k : ℝ≥0∞) +
      ((1 - lemma4SuccessP k : ℝ≥0) : ℝ≥0∞) = 1 := by
  have hp := lemma4SuccessP_le_one hk
  have hnn :
      lemma4SuccessP k +
        (1 - lemma4SuccessP k) = (1 : ℝ≥0) :=
    add_tsub_cancel_of_le hp
  exact_mod_cast hnn

/-- Every stopped slot satisfies the adaptive Bernoulli moment inequality. -/
theorem lemma4TraceStep_count_moment
    {n k P x₀ : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P)
    (w : ℝ≥0∞) (hw : w ≤ 1) :
    ∀ q,
      expect (lemma4TraceStep n x₀ P q)
          (fun z => w ^ z.success) ≤
        (((1 - lemma4SuccessP k : ℝ≥0) : ℝ≥0∞) +
            (lemma4SuccessP k : ℝ≥0∞) * w) *
          w ^ q.success := by
  intro q
  have hpSum := lemma4SuccessP_add_complement hk
  have hpOne :
      (lemma4SuccessP k : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast lemma4SuccessP_le_one hk
  by_cases hbound :
      Lemma4Bad x₀ P q.x ∨ Lemma4Target n q.x
  · apply count_step_of_masses
      (K := lemma4TraceStep n x₀ P)
      (count := Lemma4Trace.success) (s := q) (w := w)
      (q := 1) (q' := 0)
      (p := (lemma4SuccessP k : ℝ≥0∞))
      (p' := ((1 - lemma4SuccessP k : ℝ≥0) : ℝ≥0∞))
    · simp
    · exact hpSum
    · exact hw
    · exact hpOne
    · rw [lemma4TraceStep_of_boundary n x₀ P q hbound,
        expect_pure]
      simp
  · have hbad : ¬ Lemma4Bad x₀ P q.x :=
      fun h => hbound (Or.inl h)
    have htarget : ¬ Lemma4Target n q.x :=
      fun h => hbound (Or.inr h)
    have hphys :=
      lemma4_live_physical hpop hquot hk hP hbad htarget
    obtain ⟨a, ha⟩ : ∃ a, q.x = a + 1 :=
      ⟨q.x - 1, by omega⟩
    obtain ⟨b, hstate⟩ : ∃ b, a + b + 2 = n :=
      ⟨n - a - 2, by omega⟩
    have hprod : 0 < a + b := by omega
    have hbadA : ¬ Lemma4Bad x₀ P (a + 1) := by
      simpa [ha] using hbad
    have hpLiveNN :
        lemma4SuccessP k ≤
          ((a : ℝ≥0) / ((a + b : ℕ) : ℝ≥0)) :=
      lemma4SuccessP_le_live hpop hquot hk hP hstate hbadA
    have hpLive :
        (lemma4SuccessP k : ℝ≥0∞) ≤
          (a : ℝ≥0∞) / (a + b : ℝ≥0∞) := by
      have hdenNN : (((a + b : ℕ) : ℝ≥0)) ≠ 0 := by
        exact_mod_cast hprod.ne'
      rw [← Nat.cast_add]
      change
        ((lemma4SuccessP k : ℝ≥0) : ℝ≥0∞) ≤
          (((a : ℝ≥0) : ℝ≥0∞) /
            (((a + b : ℕ) : ℝ≥0) : ℝ≥0∞))
      rw [← ENNReal.coe_div hdenNN]
      exact ENNReal.coe_le_coe.mpr hpLiveNN
    have haq : q.x - 1 = a := by omega
    have hbq : n - q.x - 1 = b := by omega
    apply count_step_of_masses
      (K := lemma4TraceStep n x₀ P)
      (count := Lemma4Trace.success) (s := q) (w := w)
      (q := (a : ℝ≥0∞) / (a + b : ℝ≥0∞))
      (q' := (b : ℝ≥0∞) / (a + b : ℝ≥0∞))
      (p := (lemma4SuccessP k : ℝ≥0∞))
      (p' := ((1 - lemma4SuccessP k : ℝ≥0) : ℝ≥0∞))
    · simpa [add_comm] using
        productiveTriInterior_masses a b hprod
    · exact hpSum
    · exact hw
    · exact hpLive
    · rw [lemma4TraceStep_of_live n x₀ P q hbound hphys,
        expect_map]
      simp only [haq, hbq]
      unfold expect
      rw [tsum_fintype]
      rw [show (Finset.univ : Finset Bool) = {false, true} by
        ext up
        cases up <;> simp]
      simp

/-- Static numerator and denominator facts for the safety ratio. -/
theorem lemma4Safety_arith
    {n k P x₀ : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P) :
    0 < P + lemma4Buffer P - 2 ∧
      P + lemma4Buffer P - 2 ≤ x₀ - lemma4Buffer P ∧
      0 < x₀ - lemma4Buffer P := by
  have hB := (lemma4Buffer_bounds P).1
  have hBpos := lemma4Buffer_pos hP
  have hBP : lemma4Buffer P ≤ P := lemma4Buffer_le
  have h3P : 3 * P ≤ k * P := Nat.mul_le_mul_right P hk
  omega

/-- Live down/up odds are bounded by the fixed harmonic safety ratio. -/
theorem lemma4_live_safety_cross
    {n P x₀ a b : ℕ}
    (hpop : x₀ + P = n)
    (hstate : a + b + 2 = n)
    (hbad : ¬ Lemma4Bad x₀ P (a + 1)) :
    b * (x₀ - lemma4Buffer P) ≤
      a * (P + lemma4Buffer P - 2) := by
  have hA : x₀ - lemma4Buffer P ≤ a := by
    unfold Lemma4Bad at hbad
    omega
  have hb : b ≤ P + lemma4Buffer P - 2 := by
    omega
  calc
    b * (x₀ - lemma4Buffer P) ≤
        (P + lemma4Buffer P - 2) *
          (x₀ - lemma4Buffer P) :=
      Nat.mul_le_mul_right _ hb
    _ = (x₀ - lemma4Buffer P) *
        (P + lemma4Buffer P - 2) := by
      rw [mul_comm]
    _ ≤ a * (P + lemma4Buffer P - 2) :=
      Nat.mul_le_mul_right _ hA

theorem lemma4_down_le_up_mul_safety
    {n k P x₀ a b : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P)
    (hstate : a + b + 2 = n)
    (hbad : ¬ Lemma4Bad x₀ P (a + 1)) :
    (b : ℝ≥0∞) / (a + b : ℝ≥0∞) ≤
      (a : ℝ≥0∞) / (a + b : ℝ≥0∞) *
        lemma4SafetyBase x₀ P := by
  have hden0 :
      (((x₀ - lemma4Buffer P : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast
      (lemma4Safety_arith hpop hquot hk hP).2.2.ne'
  have hdenTop :
      (((x₀ - lemma4Buffer P : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hba :
      (b : ℝ≥0∞) ≤
        (a : ℝ≥0∞) * lemma4SafetyBase x₀ P := by
    unfold lemma4SafetyBase
    rw [← mul_div_assoc,
      ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdenTop)]
    exact_mod_cast
      lemma4_live_safety_cross hpop hstate hbad
  calc
    (b : ℝ≥0∞) / (a + b : ℝ≥0∞) ≤
        ((a : ℝ≥0∞) * lemma4SafetyBase x₀ P) /
          (a + b : ℝ≥0∞) :=
      ENNReal.div_le_div_right hba _
    _ = (a : ℝ≥0∞) / (a + b : ℝ≥0∞) *
        lemma4SafetyBase x₀ P := by
      simp only [div_eq_mul_inv]
      ac_rfl

theorem lemma4SafetyBase_le_one
    {n k P x₀ : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P) :
    lemma4SafetyBase x₀ P ≤ 1 := by
  unfold lemma4SafetyBase
  have hden0 :
      (((x₀ - lemma4Buffer P : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast
      (lemma4Safety_arith hpop hquot hk hP).2.2.ne'
  have hdenTop :
      (((x₀ - lemma4Buffer P : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  apply (ENNReal.div_le_iff hden0 hdenTop).2
  simpa using
    (show
      (((P + lemma4Buffer P - 2 : ℕ) : ℝ≥0∞)) ≤
        (((x₀ - lemma4Buffer P : ℕ) : ℝ≥0∞)) by
      exact_mod_cast
        (lemma4Safety_arith hpop hquot hk hP).2.1)

theorem lemma4SafetyBase_ne_zero
    {n k P x₀ : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P) :
    lemma4SafetyBase x₀ P ≠ 0 := by
  unfold lemma4SafetyBase
  simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
  constructor
  · exact_mod_cast
      (lemma4Safety_arith hpop hquot hk hP).1.ne'
  · exact ENNReal.natCast_ne_top _

/-- The harmonic potential is a supermartingale for every lifted productive
slot, including artificial boundary slots. -/
theorem lemma4TraceStep_safety_moment
    {n k P x₀ : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P) :
    ∀ q,
      expect (lemma4TraceStep n x₀ P q)
          (fun z => lemma4SafetyBase x₀ P ^ z.x) ≤
        lemma4SafetyBase x₀ P ^ q.x := by
  intro q
  by_cases hbound :
      Lemma4Bad x₀ P q.x ∨ Lemma4Target n q.x
  · rw [lemma4TraceStep_of_boundary n x₀ P q hbound,
      expect_pure]
  · have hbad : ¬ Lemma4Bad x₀ P q.x :=
      fun h => hbound (Or.inl h)
    have htarget : ¬ Lemma4Target n q.x :=
      fun h => hbound (Or.inr h)
    have hphys :=
      lemma4_live_physical hpop hquot hk hP hbad htarget
    obtain ⟨a, ha⟩ : ∃ a, q.x = a + 1 :=
      ⟨q.x - 1, by omega⟩
    obtain ⟨b, hstate⟩ : ∃ b, a + b + 2 = n :=
      ⟨n - a - 2, by omega⟩
    have hprod : 0 < a + b := by omega
    have haq : q.x - 1 = a := by omega
    have hbq : n - q.x - 1 = b := by omega
    have hbadA : ¬ Lemma4Bad x₀ P (a + 1) := by
      simpa [ha] using hbad
    have hsum :
        (b : ℝ≥0∞) / (a + b : ℝ≥0∞) + 0 +
            (a : ℝ≥0∞) / (a + b : ℝ≥0∞) = 1 := by
      simpa using productiveTriInterior_masses a b hprod
    have hdrift :
        (b : ℝ≥0∞) / (a + b : ℝ≥0∞) ≤
          (a : ℝ≥0∞) / (a + b : ℝ≥0∞) *
            lemma4SafetyBase x₀ P :=
      lemma4_down_le_up_mul_safety
        hpop hquot hk hP hstate hbadA
    have hcore :
        (b : ℝ≥0∞) / (a + b : ℝ≥0∞) +
              0 * lemma4SafetyBase x₀ P +
              (a : ℝ≥0∞) / (a + b : ℝ≥0∞) *
                lemma4SafetyBase x₀ P ^ 2 ≤
            lemma4SafetyBase x₀ P :=
      three_term_drift_ennreal hsum
        (lemma4SafetyBase_le_one hpop hquot hk hP) hdrift
    have hdecomp :
        expect (lemma4TraceStep n x₀ P q)
            (fun z => lemma4SafetyBase x₀ P ^ z.x) =
          (b : ℝ≥0∞) / (a + b : ℝ≥0∞) *
              lemma4SafetyBase x₀ P ^ a +
            (a : ℝ≥0∞) / (a + b : ℝ≥0∞) *
              lemma4SafetyBase x₀ P ^ (a + 2) := by
      rw [lemma4TraceStep_of_live n x₀ P q hbound hphys,
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
              lemma4SafetyBase x₀ P ^ a +
            (a : ℝ≥0∞) / (a + b : ℝ≥0∞) *
              lemma4SafetyBase x₀ P ^ (a + 2) =
          lemma4SafetyBase x₀ P ^ a *
            ((b : ℝ≥0∞) / (a + b : ℝ≥0∞) +
              0 * lemma4SafetyBase x₀ P +
              (a : ℝ≥0∞) / (a + b : ℝ≥0∞) *
                lemma4SafetyBase x₀ P ^ 2) := by
            rw [pow_add]
            ring
      _ ≤ lemma4SafetyBase x₀ P ^ a *
            lemma4SafetyBase x₀ P :=
        mul_le_mul_right hcore _
      _ = lemma4SafetyBase x₀ P ^ (a + 1) := by
        rw [pow_succ]

/-- Uniform safety bound for every productive deadline. -/
theorem lemma4Trace_bad_mass
    {n k P x₀ T : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P) :
    (∑' z : Lemma4Trace,
        if Lemma4Bad x₀ P z.x then
          iter (lemma4TraceStep n x₀ P) T
            (lemma4Initial x₀) z
        else 0) ≤
      lemma4SafetyBase x₀ P ^ lemma4Buffer P := by
  have hBx :
      lemma4Buffer P ≤ x₀ := by
    have hBP : lemma4Buffer P ≤ P := lemma4Buffer_le
    have h3P : 3 * P ≤ k * P := Nat.mul_le_mul_right P hk
    omega
  have hxsplit :
      (lemma4Initial x₀).x =
        (x₀ - lemma4Buffer P) + lemma4Buffer P := by
    simp [lemma4Initial]
    omega
  simpa [Lemma4Bad] using
    ruin_le_u
      (lemma4TraceStep n x₀ P) Lemma4Trace.x
      (lemma4SafetyBase x₀ P)
      (lemma4SafetyBase_le_one hpop hquot hk hP)
      (lemma4SafetyBase_ne_zero hpop hquot hk hP)
      (fun q => lemma4SafetyBase x₀ P ^ q.x)
      (fun _ => rfl)
      (lemma4TraceStep_safety_moment hpop hquot hk hP)
      T (x₀ - lemma4Buffer P) (lemma4Buffer P)
      (lemma4Initial x₀) hxsplit

/-- Cross-multiplied lower bound on the harmonic drift. -/
theorem lemma4Safety_drift_cross
    {n k P x₀ : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P) :
    (k - 2) * (x₀ - lemma4Buffer P) ≤
      2 * k *
        ((x₀ - lemma4Buffer P) -
          (P + lemma4Buffer P - 2)) := by
  let A := x₀ - lemma4Buffer P
  let C := P + lemma4Buffer P - 2
  have hCA : C ≤ A := by
    simpa [A, C] using
      (lemma4Safety_arith hpop hquot hk hP).2.1
  have hB8 := (lemma4Buffer_bounds P).1
  have hB4 : 4 * lemma4Buffer P ≤ P := by omega
  have h2Pk : 2 * P ≤ k * P :=
    Nat.mul_le_mul_right P (by omega : 2 ≤ k)
  have h3Pk : 3 * P ≤ k * P :=
    Nat.mul_le_mul_right P hk
  have h2Px : 2 * P ≤ x₀ := by
    omega
  have hdk :
      (k - 2) * P + 2 * P = k * P := by
    rw [Nat.sub_mul]
    omega
  have htwice :
      (k - 2) * P + 2 * C ≤ 2 * A := by
    dsimp only [A, C]
    omega
  have hdiff :
      (k - 2) * P ≤ 2 * (A - C) := by
    omega
  have hAle : A ≤ k * P := by
    dsimp only [A]
    omega
  calc
    (k - 2) * A ≤ (k - 2) * (k * P) :=
      Nat.mul_le_mul_left _ hAle
    _ = k * ((k - 2) * P) := by ring
    _ ≤ k * (2 * (A - C)) :=
      Nat.mul_le_mul_left _ hdiff
    _ = 2 * k * (A - C) := by ring

/-- The safety escape term is exponentially small at the core
`(k-2)P/k` scale. -/
theorem lemma4Safety_power_exp
    {n k P x₀ : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P) :
    lemma4SafetyBase x₀ P ^ lemma4Buffer P ≤
      ENNReal.ofReal
        (Real.exp
          (-((((k - 2 : ℕ) : ℝ) * (P : ℝ)) /
            (32 * (k : ℝ))))) := by
  let A := x₀ - lemma4Buffer P
  let C := P + lemma4Buffer P - 2
  have hC0 : 0 < C := by
    simpa [C] using
      (lemma4Safety_arith hpop hquot hk hP).1
  have hCA : C ≤ A := by
    simpa [A, C] using
      (lemma4Safety_arith hpop hquot hk hP).2.1
  have hA0 : 0 < A := lt_of_lt_of_le hC0 hCA
  have hPB : (P : ℝ) ≤ 16 * (lemma4Buffer P : ℝ) := by
    exact_mod_cast lemma4_le_sixteen_buffer hP
  have hcrossNat :
      (k - 2) * A ≤ 2 * k * (A - C) := by
    simpa [A, C] using
      lemma4Safety_drift_cross hpop hquot hk hP
  have hcross :
      (((k - 2 : ℕ) : ℝ) * (A : ℝ)) ≤
        2 * (k : ℝ) * ((A : ℝ) - (C : ℝ)) := by
    rw [← Nat.cast_sub hCA]
    exact_mod_cast hcrossNat
  have hdiff : (0 : ℝ) ≤ (A : ℝ) - (C : ℝ) := by
    apply sub_nonneg.mpr
    exact_mod_cast hCA
  have hprod :
      (((k - 2 : ℕ) : ℝ) * (P : ℝ)) * (A : ℝ) ≤
        ((lemma4Buffer P : ℝ) *
          ((A : ℝ) - (C : ℝ))) * (32 * (k : ℝ)) := by
    calc
      (((k - 2 : ℕ) : ℝ) * (P : ℝ)) * (A : ℝ) =
          (P : ℝ) *
            (((k - 2 : ℕ) : ℝ) * (A : ℝ)) := by ring
      _ ≤ (P : ℝ) *
          (2 * (k : ℝ) * ((A : ℝ) - (C : ℝ))) :=
        mul_le_mul_of_nonneg_left hcross (by positivity)
      _ ≤ (16 * (lemma4Buffer P : ℝ)) *
          (2 * (k : ℝ) * ((A : ℝ) - (C : ℝ))) :=
        mul_le_mul_of_nonneg_right hPB (by positivity)
      _ = ((lemma4Buffer P : ℝ) *
          ((A : ℝ) - (C : ℝ))) * (32 * (k : ℝ)) := by ring
  unfold lemma4SafetyBase
  apply ratio_pow_le_ofReal_exp
      A C (lemma4Buffer P)
      ((((k - 2 : ℕ) : ℝ) * (P : ℝ)) /
        (32 * (k : ℝ)))
  · exact hC0
  · exact hCA
  · rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 32 * (k : ℝ))
      (by positivity : (0 : ℝ) < (A : ℝ))]
    exact hprod

/-- Low-success cutoff forced by missing extinction at the productive
deadline. -/
def lemma4Cutoff (n k P : ℕ) : ℕ :=
  (lemma4Horizon n k + P - 1) / 2

theorem lemma4ChernoffDelta_nonneg (k : ℕ) :
    0 ≤ lemma4ChernoffDelta k := by
  unfold lemma4ChernoffDelta
  positivity

theorem lemma4ChernoffDelta_le_one
    {k : ℕ} (hk : 3 ≤ k) :
    lemma4ChernoffDelta k ≤ 1 := by
  unfold lemma4ChernoffDelta
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 16 * (k : ℝ))]
  rw [Nat.cast_sub (by omega : 2 ≤ k)]
  norm_num
  nlinarith [show (0 : ℝ) ≤ k by positivity]

theorem lemma4SuccessP_coe
    {k : ℕ} (hk : 3 ≤ k) :
    (lemma4SuccessP k : ℝ) =
      (7 * (k : ℝ) - 6) / (8 * (k : ℝ)) := by
  unfold lemma4SuccessP
  rw [NNReal.coe_div]
  simp only [NNReal.coe_natCast]
  norm_num only [Nat.cast_mul,
    Nat.cast_sub (by omega : 6 ≤ 7 * k), Nat.cast_ofNat]

/-- The corrected success floor is at least one half. -/
theorem lemma4SuccessP_half
    {k : ℕ} (hk : 3 ≤ k) :
    (1 / 2 : ℝ) ≤ (lemma4SuccessP k : ℝ) := by
  rw [lemma4SuccessP_coe hk]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (k : ℝ))]
  norm_num
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hk
  nlinarith

/-- The floor horizon retains enough of the real paper deadline. -/
theorem lemma4Horizon_product_lower
    {n k P : ℕ}
    (hquot : k * P = n) (hk : 3 ≤ k) (hP : 8 ≤ P) :
    8 * k * P ≤
      5 * lemma4Horizon n k * (k - 2) := by
  have hd : 0 < k - 2 := by omega
  have hupper :
      2 * n <
        (lemma4Horizon n k + 1) * (k - 2) := by
    apply (Nat.div_lt_iff_lt_mul hd).mp
    unfold lemma4Horizon
    omega
  have hupper' :
      2 * (k * P) ≤
        lemma4Horizon n k * (k - 2) + (k - 2) := by
    have hupperN :
        2 * (k * P) <
          (lemma4Horizon n k + 1) * (k - 2) := by
      simpa only [hquot] using hupper
    rw [Nat.add_mul] at hupperN
    omega
  have hkP : 8 * k ≤ k * P := by
    have := Nat.mul_le_mul_left k hP
    nlinarith
  have hdsmall :
      5 * (k - 2) ≤ 2 * (k * P) := by
    have hdk : 5 * (k - 2) ≤ 8 * k := by omega
    omega
  have hfive := Nat.mul_le_mul_left 5 hupper'
  nlinarith

/-- Polynomial form of the exact mean slack needed by the cutoff. -/
theorem lemma4Horizon_mean_slack
    {n k P : ℕ}
    (hquot : k * P = n) (hk : 3 ≤ k) (hP : 8 ≤ P) :
    64 * k ^ 2 * P ≤
      lemma4Horizon n k * (k - 2) * (41 * k + 6) := by
  have hH := lemma4Horizon_product_lower hquot hk hP
  have hscale :
      8 * k * (8 * k * P) ≤
        8 * k *
          (5 * lemma4Horizon n k * (k - 2)) :=
    Nat.mul_le_mul_left (8 * k) hH
  have hcoef : 40 * k ≤ 41 * k + 6 := by omega
  have hcoefMul :=
    Nat.mul_le_mul_right
      (lemma4Horizon n k * (k - 2)) hcoef
  nlinarith

/-- The terminal low-success cutoff lies below the adapted multiplicative
Chernoff threshold. -/
theorem lemma4Deadline_cutoff
    {n k P : ℕ}
    (hquot : k * P = n) (hk : 3 ≤ k) (hP : 8 ≤ P) :
    ((lemma4Cutoff n k P : ℕ) : ℝ) ≤
      (1 - lemma4ChernoffDelta k) *
        (((lemma4Horizon n k : ℕ) : ℝ) *
          (lemma4SuccessP k : ℝ)) := by
  let H := lemma4Horizon n k
  let d := k - 2
  have hkR : (0 : ℝ) < k := by positivity
  have hslackNat :
      64 * k ^ 2 * P ≤ H * d * (41 * k + 6) := by
    simpa [H, d] using
      lemma4Horizon_mean_slack hquot hk hP
  have hslack :
      (P : ℝ) ≤
        ((H : ℝ) * (d : ℝ) * (41 * (k : ℝ) + 6)) /
          (64 * (k : ℝ) ^ 2) := by
    rw [le_div_iff₀ (by positivity :
      (0 : ℝ) < 64 * (k : ℝ) ^ 2)]
    have hslackR :
        ((64 * k ^ 2 * P : ℕ) : ℝ) ≤
          ((H * d * (41 * k + 6) : ℕ) : ℝ) := by
      exact_mod_cast hslackNat
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
      Nat.cast_ofNat, mul_assoc, mul_comm, mul_left_comm] using hslackR
  have hidentity :
      2 *
          ((1 - lemma4ChernoffDelta k) *
            ((H : ℝ) * (lemma4SuccessP k : ℝ))) =
        (H : ℝ) +
          ((H : ℝ) * (d : ℝ) * (41 * (k : ℝ) + 6)) /
            (64 * (k : ℝ) ^ 2) := by
    rw [lemma4SuccessP_coe hk]
    unfold lemma4ChernoffDelta
    dsimp only [d]
    rw [Nat.cast_sub (by omega : 2 ≤ k)]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    ring
  have hcutNat :
      2 * lemma4Cutoff n k P ≤ H + P := by
    unfold lemma4Cutoff
    dsimp only [H]
    have hdiv :=
      Nat.div_mul_le_self
        (lemma4Horizon n k + P - 1) 2
    omega
  have hcut :
      (lemma4Cutoff n k P : ℝ) ≤
        ((H : ℝ) + (P : ℝ)) / 2 := by
    have hcutR :
        2 * (lemma4Cutoff n k P : ℝ) ≤
          (H : ℝ) + (P : ℝ) := by
      exact_mod_cast hcutNat
    nlinarith
  calc
    (lemma4Cutoff n k P : ℝ) ≤
        ((H : ℝ) + (P : ℝ)) / 2 := hcut
    _ ≤ ((H : ℝ) +
          ((H : ℝ) * (d : ℝ) * (41 * (k : ℝ) + 6)) /
            (64 * (k : ℝ) ^ 2)) / 2 := by
      linarith
    _ = (1 - lemma4ChernoffDelta k) *
        ((H : ℝ) * (lemma4SuccessP k : ℝ)) := by
      linarith [hidentity]

/-- Explicit lower bound on the adapted Chernoff exponent. -/
theorem lemma4Deadline_exponent_lower
    {n k P : ℕ}
    (hquot : k * P = n) (hk : 3 ≤ k) (hP : 8 ≤ P) :
    (((k - 2 : ℕ) : ℝ) * (P : ℝ)) /
        (1024 * (k : ℝ)) ≤
      lemma4ChernoffDelta k ^ 2 *
          (((lemma4Horizon n k : ℕ) : ℝ) *
            (lemma4SuccessP k : ℝ)) / 2 := by
  let H := lemma4Horizon n k
  let d := k - 2
  have hkR : (0 : ℝ) < k := by positivity
  have hdR : (0 : ℝ) ≤ d := by positivity
  have hHlowerNat :
      k * P ≤ H * d := by
    have h := lemma4Horizon_product_lower hquot hk hP
    nlinarith
  have hHlower :
      (k : ℝ) * (P : ℝ) ≤ (H : ℝ) * (d : ℝ) := by
    exact_mod_cast hHlowerNat
  have hp := lemma4SuccessP_half hk
  have hp' : (1 : ℝ) ≤ 2 * (lemma4SuccessP k : ℝ) := by
    nlinarith
  have hnum :
      (d : ℝ) * (k : ℝ) * (P : ℝ) ≤
        2 * (d : ℝ) ^ 2 * (H : ℝ) *
          (lemma4SuccessP k : ℝ) := by
    calc
      (d : ℝ) * (k : ℝ) * (P : ℝ) =
          (d : ℝ) * ((k : ℝ) * (P : ℝ)) := by ring
      _ ≤ (d : ℝ) * ((H : ℝ) * (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hHlower hdR
      _ = (d : ℝ) ^ 2 * (H : ℝ) := by ring
      _ ≤ (d : ℝ) ^ 2 * (H : ℝ) *
          (2 * (lemma4SuccessP k : ℝ)) := by
        have hmul :=
          mul_le_mul_of_nonneg_left hp'
            (show (0 : ℝ) ≤ (d : ℝ) ^ 2 * (H : ℝ) by positivity)
        simpa only [mul_one] using hmul
      _ = 2 * (d : ℝ) ^ 2 * (H : ℝ) *
          (lemma4SuccessP k : ℝ) := by ring
  calc
    (((k - 2 : ℕ) : ℝ) * (P : ℝ)) /
          (1024 * (k : ℝ)) =
        ((d : ℝ) * (k : ℝ) * (P : ℝ)) /
          (1024 * (k : ℝ) ^ 2) := by
      dsimp only [d]
      field_simp
    _ ≤ (2 * (d : ℝ) ^ 2 * (H : ℝ) *
          (lemma4SuccessP k : ℝ)) /
          (1024 * (k : ℝ) ^ 2) :=
      (div_le_div_iff_of_pos_right (by positivity)).2 hnum
    _ = lemma4ChernoffDelta k ^ 2 *
          (((lemma4Horizon n k : ℕ) : ℝ) *
            (lemma4SuccessP k : ℝ)) / 2 := by
      unfold lemma4ChernoffDelta
      dsimp only [H, d]
      field_simp
      ring

/-- Deadline branch of corrected paper Lemma 4. -/
theorem lemma4Trace_low_success
    {n k P x₀ : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P) :
    (∑' z : Lemma4Trace,
        if z.success ≤ lemma4Cutoff n k P then
          iter (lemma4TraceStep n x₀ P) (lemma4Horizon n k)
            (lemma4Initial x₀) z
        else 0) ≤
      ENNReal.ofReal
        (Real.exp
          (-((((k - 2 : ℕ) : ℝ) * (P : ℝ)) /
            (1024 * (k : ℝ))))) := by
  have hraw :=
    adapted_multiplicative_lower_tail
      (lemma4TraceStep n x₀ P) Lemma4Trace.success
      (lemma4Initial x₀)
      (lemma4SuccessP k) (lemma4SuccessP_le_one hk)
      (lemma4ChernoffDelta k)
      (lemma4ChernoffDelta_nonneg k)
      (lemma4ChernoffDelta_le_one hk)
      (lemma4Horizon n k) (lemma4Cutoff n k P)
      (lemma4Deadline_cutoff hquot hk hP)
      (by rfl)
      (lemma4TraceStep_count_moment hpop hquot hk hP
        (ENNReal.ofReal
          (Real.exp (-lemma4ChernoffDelta k)))
        (by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal <|
            Real.exp_le_one_iff.mpr
              (neg_nonpos.mpr
                (lemma4ChernoffDelta_nonneg k))))
  have hexp :
      ENNReal.ofReal
          (Real.exp
            (-(lemma4ChernoffDelta k ^ 2 *
              (((lemma4Horizon n k : ℕ) : ℝ) *
                (lemma4SuccessP k : ℝ))) / 2)) ≤
        ENNReal.ofReal
          (Real.exp
            (-((((k - 2 : ℕ) : ℝ) * (P : ℝ)) /
              (1024 * (k : ℝ))))) :=
    ENNReal.ofReal_le_ofReal <|
      Real.exp_le_exp.mpr <|
        (by
          simpa only [neg_div] using
            neg_le_neg
              (lemma4Deadline_exponent_lower hquot hk hP))
  exact hraw.trans hexp

/-- Every supported terminal trace that misses extinction has either crossed
the safety boundary or has too few successful productive directions. -/
theorem lemma4Trace_terminal_cover
    {n k P x₀ : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P)
    (z : Lemma4Trace)
    (hz :
      iter (lemma4TraceStep n x₀ P) (lemma4Horizon n k)
        (lemma4Initial x₀) z ≠ 0)
    (htarget : ¬ Lemma4Target n z.x) :
    Lemma4Bad x₀ P z.x ∨
      z.success ≤ lemma4Cutoff n k P := by
  have hinv :=
    lemma4Trace_iter_inv hpop hquot hk hP z hz
  have hclock :=
    lemma4Trace_iter_clock z hz
  rcases hinv with hbad | hhit | hrel
  · exact Or.inl hbad
  · exact False.elim (htarget hhit)
  · right
    have hxn : z.x < n := by
      simpa [Lemma4Target] using htarget
    have htwo :
        2 * z.success ≤
          lemma4Horizon n k + P - 1 := by
      omega
    unfold lemma4Cutoff
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    simpa [mul_comm] using htwo

/-- The stopped trace failure splits into the Feller and Chernoff events. -/
theorem lemma4Trace_failure_split
    {n k P x₀ : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P) :
    terminalFailureMass
        (iter (lemma4TraceStep n x₀ P) (lemma4Horizon n k)
          (lemma4Initial x₀))
        (fun z => Lemma4Target n z.x) ≤
      (∑' z : Lemma4Trace,
        if Lemma4Bad x₀ P z.x then
          iter (lemma4TraceStep n x₀ P) (lemma4Horizon n k)
            (lemma4Initial x₀) z
        else 0) +
      ∑' z : Lemma4Trace,
        if z.success ≤ lemma4Cutoff n k P then
          iter (lemma4TraceStep n x₀ P) (lemma4Horizon n k)
            (lemma4Initial x₀) z
        else 0 := by
  rw [← ENNReal.tsum_add]
  unfold terminalFailureMass
  refine ENNReal.tsum_le_tsum fun z => ?_
  let mass :=
    iter (lemma4TraceStep n x₀ P) (lemma4Horizon n k)
      (lemma4Initial x₀) z
  by_cases hmass : mass = 0
  · simp [mass, hmass]
  · have hmass' :
        iter (lemma4TraceStep n x₀ P) (lemma4Horizon n k)
          (lemma4Initial x₀) z ≠ 0 := by
      simpa [mass] using hmass
    by_cases htarget : Lemma4Target n z.x
    · simp [htarget]
    · rcases lemma4Trace_terminal_cover
          hpop hquot hk hP z hmass' htarget with hbad | hlow
      · simp [htarget, hbad]
      · simp [htarget, hlow]

/-- The stronger safety exponent fits the deadline's common envelope. -/
theorem lemma4Safety_exp_le_common
    {n k P x₀ : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P) :
    lemma4SafetyBase x₀ P ^ lemma4Buffer P ≤
      ENNReal.ofReal
        (Real.exp
          (-((((k - 2 : ℕ) : ℝ) * (P : ℝ)) /
            (1024 * (k : ℝ))))) := by
  have hnum : (0 : ℝ) ≤ ((k - 2 : ℕ) : ℝ) * (P : ℝ) := by
    positivity
  have hfrac :
      (((k - 2 : ℕ) : ℝ) * (P : ℝ)) /
          (1024 * (k : ℝ)) ≤
        (((k - 2 : ℕ) : ℝ) * (P : ℝ)) /
          (32 * (k : ℝ)) := by
    apply div_le_div_of_nonneg_left hnum
    · positivity
    · nlinarith [show (0 : ℝ) < k by positivity]
  exact
    (lemma4Safety_power_exp hpop hquot hk hP).trans
      (ENNReal.ofReal_le_ofReal <|
        Real.exp_le_exp.mpr (neg_le_neg hfrac))

/-- Counted-trace form of the corrected arbitrary-`k` extinction theorem. -/
theorem lemma4Trace_failure_core
    {n k P x₀ : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P) :
    terminalFailureMass
        (iter (lemma4TraceStep n x₀ P) (lemma4Horizon n k)
          (lemma4Initial x₀))
        (fun z => Lemma4Target n z.x) ≤
      (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-((((k - 2 : ℕ) : ℝ) * (P : ℝ)) /
              (1024 * (k : ℝ))))) := by
  let common :=
    ENNReal.ofReal
      (Real.exp
        (-((((k - 2 : ℕ) : ℝ) * (P : ℝ)) /
          (1024 * (k : ℝ)))))
  calc
    terminalFailureMass
        (iter (lemma4TraceStep n x₀ P) (lemma4Horizon n k)
          (lemma4Initial x₀))
        (fun z => Lemma4Target n z.x) ≤
      (∑' z : Lemma4Trace,
        if Lemma4Bad x₀ P z.x then
          iter (lemma4TraceStep n x₀ P) (lemma4Horizon n k)
            (lemma4Initial x₀) z
        else 0) +
      ∑' z : Lemma4Trace,
        if z.success ≤ lemma4Cutoff n k P then
          iter (lemma4TraceStep n x₀ P) (lemma4Horizon n k)
            (lemma4Initial x₀) z
        else 0 :=
      lemma4Trace_failure_split hpop hquot hk hP
    _ ≤ lemma4SafetyBase x₀ P ^ lemma4Buffer P + common :=
      add_le_add
        (lemma4Trace_bad_mass
          (T := lemma4Horizon n k) hpop hquot hk hP)
        (by
          simpa [common] using
            lemma4Trace_low_success hpop hquot hk hP)
    _ ≤ common + common :=
      add_le_add
        (by
          simpa [common] using
            lemma4Safety_exp_le_common hpop hquot hk hP)
        le_rfl
    _ = (2 : ℝ≥0∞) * common := by ring
    _ = (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-((((k - 2 : ℕ) : ℝ) * (P : ℝ)) /
              (1024 * (k : ℝ))))) := by
      rfl

/-- β/γ-free core of paper Lemma 4.  Starting from exact minority
`P = n/k`, extinction occurs within the literal floor of `2n/(k-2)`
productive events. -/
theorem lemma4_productive_extinction_core
    {n k P x₀ : ℕ}
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hk : 3 ≤ k) (hP : 8 ≤ P) :
    terminalFailureMass
        (iter
          (freeze (Lemma4Target n) (productiveTriChain n))
          (lemma4Horizon n k) x₀)
        (Lemma4Target n) ≤
      (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-((((k - 2 : ℕ) : ℝ) * (P : ℝ)) /
              (1024 * (k : ℝ))))) := by
  have hprojection :=
    targetFreeze_failure_le_lazy_projection
      (Lemma4Target n)
      (productiveTriChain n)
      (lemma4TraceStep n x₀ P)
      Lemma4Trace.toX
      (lemma4TraceStep_isLazyProjection n x₀ P)
      (lemma4Horizon n k) (lemma4Initial x₀)
  have htrace :=
    lemma4Trace_failure_core hpop hquot hk hP
  exact hprojection.trans (by
    simpa [Lemma4Trace.toX, lemma4Initial] using htrace)

/-- **Paper Lemma 4.**  The cross-multiplied premise
`k(γ log₂ n) ≤ n` is the integral form of
`k ≤ n/(γ log₂ n)`.  The explicit large-scale premise is the paper's
standing “sufficiently large `n`” clause. -/
theorem lemma4
    {n γ k P x₀ : ℕ} (β : ℝ)
    (hpop : x₀ + P = n) (hquot : k * P = n)
    (hβ1 : 1 < β) (hβ2 : β ≤ 2)
    (hkβ : 1 + β ≤ (k : ℝ))
    (hscale : k * (γ * Nat.log 2 n) ≤ n)
    (hlarge : 8 ≤ γ * Nat.log 2 n) :
    terminalFailureMass
        (iter
          (freeze (Lemma4Target n) (productiveTriChain n))
          (lemma4Horizon n k) x₀)
        (Lemma4Target n) ≤
      (2 : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp
            (-(((β - 1) *
              ((γ * Nat.log 2 n : ℕ) : ℝ)) / 3072))) := by
  let d := γ * Nat.log 2 n
  have h2kR : (2 : ℝ) < (k : ℝ) := by
    linarith
  have hk : 3 ≤ k := by
    exact_mod_cast h2kR
  have hk0 : 0 < k := by omega
  have hscale' : k * d ≤ k * P := by
    simpa [d, hquot] using hscale
  have hdP : d ≤ P :=
    Nat.le_of_mul_le_mul_left hscale' hk0
  have hP : 8 ≤ P := by
    dsimp only [d] at hdP
    omega
  have hβnonneg : (0 : ℝ) ≤ β - 1 := by linarith
  have hβone : β - 1 ≤ (1 : ℝ) := by linarith
  have hdPR : (d : ℝ) ≤ (P : ℝ) := by
    exact_mod_cast hdP
  have hkthree :
      (k : ℝ) ≤ 3 * (((k - 2 : ℕ) : ℝ)) := by
    rw [Nat.cast_sub (by omega : 2 ≤ k)]
    have hkR : (3 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hk
    norm_num
    linarith
  have hnum :
      (β - 1) * (d : ℝ) * (1024 * (k : ℝ)) ≤
        (((k - 2 : ℕ) : ℝ) * (P : ℝ)) * 3072 := by
    calc
      (β - 1) * (d : ℝ) * (1024 * (k : ℝ)) ≤
          (d : ℝ) * (1024 * (k : ℝ)) := by
        have hmul :=
          mul_le_mul_of_nonneg_right hβone
            (show (0 : ℝ) ≤
              (d : ℝ) * (1024 * (k : ℝ)) by positivity)
        simpa only [one_mul, mul_assoc] using hmul
      _ ≤ (P : ℝ) * (1024 * (k : ℝ)) :=
        mul_le_mul_of_nonneg_right hdPR (by positivity)
      _ ≤ (P : ℝ) *
          (1024 * (3 * (((k - 2 : ℕ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hkthree (by norm_num : (0 : ℝ) ≤ 1024))
          (by positivity)
      _ = (((k - 2 : ℕ) : ℝ) * (P : ℝ)) * 3072 := by ring
  have hexponents :
      ((β - 1) * (d : ℝ)) / 3072 ≤
        (((k - 2 : ℕ) : ℝ) * (P : ℝ)) /
          (1024 * (k : ℝ)) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3072)
      (by positivity : (0 : ℝ) < 1024 * (k : ℝ))]
    exact hnum
  have herr :
      ENNReal.ofReal
          (Real.exp
            (-((((k - 2 : ℕ) : ℝ) * (P : ℝ)) /
              (1024 * (k : ℝ))))) ≤
        ENNReal.ofReal
          (Real.exp
            (-(((β - 1) * (d : ℝ)) / 3072))) :=
    ENNReal.ofReal_le_ofReal <|
      Real.exp_le_exp.mpr (neg_le_neg hexponents)
  exact
    (lemma4_productive_extinction_core hpop hquot hk hP).trans
      (by
        simpa [d, mul_comm] using
          mul_le_mul_right herr (2 : ℝ≥0∞))

end Tri
