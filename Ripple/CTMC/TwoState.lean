/-
  Ripple.CTMC.TwoState — Two-State CTMC Example

  A concrete 2-state birth-death CTMC demonstrating the Q-matrix infrastructure.
  State 0 = "off", State 1 = "on".
  Transitions: 0 →(a) 1 (birth), 1 →(b) 0 (death).
-/

import Ripple.CTMC.CTMC

namespace Ripple.CTMC

/-- A two-state birth-death CTMC with birth rate `a` and death rate `b`.
The Q-matrix is [[-a, a], [b, -b]]. -/
noncomputable def twoStateQ (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    QMatrix (Fin 2) where
  rate s t := if s = 0 then (if t = 0 then -a else a)
    else (if t = 0 then b else -b)
  rate_nonneg := by
    intro s t hne
    fin_cases s <;> fin_cases t <;> simp_all
  rate_diag := by
    intro s
    fin_cases s
    · change -a = -∑ t ∈ Finset.univ.filter (· ≠ (0 : Fin 2)), _
      have : (Finset.univ : Finset (Fin 2)).filter (· ≠ (0 : Fin 2)) =
          {(1 : Fin 2)} := by decide
      rw [this, Finset.sum_singleton]; simp
    · change -b = -∑ t ∈ Finset.univ.filter (· ≠ (1 : Fin 2)), _
      have : (Finset.univ : Finset (Fin 2)).filter (· ≠ (1 : Fin 2)) =
          {(0 : Fin 2)} := by decide
      rw [this, Finset.sum_singleton]; simp

variable {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)

/-- Exit rate from state 0 equals a. -/
theorem twoStateQ_exitRate_zero :
    (twoStateQ a b ha hb).exitRate 0 = a := by
  have hfilt : (Finset.univ : Finset (Fin 2)).filter (· ≠ (0 : Fin 2)) =
      {(1 : Fin 2)} := by ext j; fin_cases j <;> simp
  simp [QMatrix.exitRate, twoStateQ, hfilt]

/-- Exit rate from state 1 equals b. -/
theorem twoStateQ_exitRate_one :
    (twoStateQ a b ha hb).exitRate 1 = b := by
  have hfilt : (Finset.univ : Finset (Fin 2)).filter (· ≠ (1 : Fin 2)) =
      {(0 : Fin 2)} := by ext j; fin_cases j <;> simp
  simp [QMatrix.exitRate, twoStateQ, hfilt]

/-- Row sum is zero (specialization of general theorem). -/
theorem twoStateQ_row_sum_zero (s : Fin 2) :
    ∑ t : Fin 2, (twoStateQ a b ha hb).rate s t = 0 :=
  QMatrix.row_sum_zero _ s

/-- State 0 is absorbing iff a = 0. -/
theorem twoStateQ_absorbing_zero :
    (twoStateQ a b ha hb).IsAbsorbing 0 ↔ a = 0 := by
  simp [QMatrix.IsAbsorbing, twoStateQ_exitRate_zero ha hb]

/-- State 1 is absorbing iff b = 0. -/
theorem twoStateQ_absorbing_one :
    (twoStateQ a b ha hb).IsAbsorbing 1 ↔ b = 0 := by
  simp [QMatrix.IsAbsorbing, twoStateQ_exitRate_one ha hb]

/-- The stationary distribution of the 2-state chain: π(0) = b/(a+b), π(1) = a/(a+b). -/
noncomputable def twoStationary (ha : 0 < a) (hb : 0 < b) :
    Distribution (Fin 2) where
  prob s := if s = 0 then b / (a + b) else a / (a + b)
  nonneg := by
    intro s
    fin_cases s <;> simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.mk_one,
      one_ne_zero] <;> positivity
  sum_one := by
    simp [Fin.sum_univ_two]
    field_simp
    ring

/-- The 2-state stationary distribution satisfies detailed balance. -/
theorem twoState_detailedBalance (ha : 0 < a) (hb : 0 < b) :
    (twoStateQ a b ha.le hb.le).DetailedBalance (twoStationary ha hb) := by
  intro s t hst
  fin_cases s <;> fin_cases t <;> simp_all [twoStationary, twoStateQ] <;> ring

/-- The 2-state stationary distribution is stationary. -/
theorem twoState_isStationary (ha : 0 < a) (hb : 0 < b) :
    (twoStateQ a b ha.le hb.le).IsStationary (twoStationary ha hb) :=
  QMatrix.DetailedBalance.isStationary _ _ (twoState_detailedBalance ha hb)

/-- State 0 is non-absorbing when a > 0. -/
theorem twoStateQ_nonabsorbing_zero (ha : 0 < a) (hb : 0 ≤ b) :
    ¬(twoStateQ a b ha.le hb).IsAbsorbing 0 := by
  rw [twoStateQ_absorbing_zero ha.le hb]
  linarith

/-- State 1 is non-absorbing when b > 0. -/
theorem twoStateQ_nonabsorbing_one (ha : 0 ≤ a) (hb : 0 < b) :
    ¬(twoStateQ a b ha hb.le).IsAbsorbing 1 := by
  rw [twoStateQ_absorbing_one ha hb.le]
  linarith

/-- The 2-state stationary distribution has π(0) > 0. -/
theorem twoStationary_zero_pos (ha : 0 < a) (hb : 0 < b) :
    0 < (twoStationary ha hb).prob 0 := by
  simp only [twoStationary, ↓reduceIte]
  positivity

/-- The 2-state stationary distribution has π(1) > 0. -/
theorem twoStationary_one_pos (ha : 0 < a) (hb : 0 < b) :
    0 < (twoStationary ha hb).prob 1 := by
  simp only [twoStationary, one_ne_zero, ↓reduceIte]
  positivity

/-- All states have positive stationary probability. -/
theorem twoStationary_pos (ha : 0 < a) (hb : 0 < b) (s : Fin 2) :
    0 < (twoStationary ha hb).prob s := by
  fin_cases s
  · exact twoStationary_zero_pos ha hb
  · exact twoStationary_one_pos ha hb

/-- The 2-state chain is reversible (time-reversal equals original). -/
theorem twoState_reversible (ha : 0 < a) (hb : 0 < b) :
    ((twoStateQ a b ha.le hb.le).timeReverse (twoStationary ha hb)
      (twoStationary_pos ha hb)
      ((twoState_detailedBalance ha hb).isStationary _ _)).rate =
    (twoStateQ a b ha.le hb.le).rate :=
  (twoStateQ a b ha.le hb.le).timeReverse_eq_of_detailedBalance _ _
    (twoState_detailedBalance ha hb)

end Ripple.CTMC
