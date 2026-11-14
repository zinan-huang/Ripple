/-
  Ripple.Kurtz.StrongApprox.BinomialRate — the binomial rate function `H(q,p) = D(q‖p)` and the
  monotone ratio `r(p) = |p−q| / ((1−p) √(2H))`

  Mathematics: the Serov–Zubkov signed-root intersection.

  `binRate q p = q (log q − log p) + (1−q)(log(1−q) − log(1−p))`, derivative `(p−q)/(p(1−p))`.
  Two brackets vanish at `p = q`:
  * `binBracketE = H − (p−q)²/(2p(1−q))`, monotone (derivative `(p−q)²(1+p)/(2p²(1−p)(1−q))`);
    it gives the sign of `(r²)' = (p−q)(1−q) E / (H² (1−p)³)` on each side of `q`;
  * `binBracketF = H − (1−q)(p−q)²/(2q(1−p)²)`, antitone (derivative
    `−(p−q)²(1−pq)/(pq(1−p)³)`); it gives `r² ≤ q/(1−q)` left of `q` and `≥` right of `q`.
  Hence `H > 0` off `q`, and `binR q` (value `√(q/(1−q))` at `q`) is monotone on `(0,1)`.
  `H → +∞` at `0⁺` and at `1⁻` (the symmetry `H(1−q, 1−p) = H(q, p)` reduces the second to the
  first).
-/

import Mathlib

namespace Ripple.Kurtz.StrongApprox

open Set Filter Topology

/-- `H(q,p) = D(q‖p) = q (log q − log p) + (1−q)(log(1−q) − log(1−p))`. -/
noncomputable def binRate (q p : ℝ) : ℝ :=
  q * (Real.log q - Real.log p) + (1 - q) * (Real.log (1 - q) - Real.log (1 - p))

theorem binRate_self (q : ℝ) : binRate q q = 0 := by simp [binRate]

/-- `H(1−q, 1−p) = H(q, p)`. -/
theorem binRate_symm (q p : ℝ) : binRate (1 - q) (1 - p) = binRate q p := by
  simp only [binRate, sub_sub_cancel]; ring

theorem hasDerivAt_binRate (q : ℝ) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (binRate q) ((p - q) / (p * (1 - p))) p := by
  have h1p : (1 : ℝ) - p ≠ 0 := by linarith
  have h1 := ((Real.hasDerivAt_log hp0.ne').const_sub (Real.log q)).const_mul q
  have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) p := (hasDerivAt_id p).const_sub 1
  have h3 := ((h2.log h1p).const_sub (Real.log (1 - q))).const_mul (1 - q)
  have h := h1.add h3
  refine h.congr_deriv ?_
  field_simp
  ring

theorem continuousOn_binRate (q : ℝ) : ContinuousOn (binRate q) (Ioo 0 1) := fun p hp =>
  (hasDerivAt_binRate q hp.1 hp.2).continuousAt.continuousWithinAt

/-! ### Bracket `E = H − (p−q)²/(2p(1−q))`, monotone -/

/-- `E(p) = H(p) − (p−q)²/(2p(1−q))`. -/
noncomputable def binBracketE (q p : ℝ) : ℝ := binRate q p - (p - q) ^ 2 / (2 * p * (1 - q))

theorem binBracketE_self (q : ℝ) : binBracketE q q = 0 := by simp [binBracketE, binRate_self]

theorem hasDerivAt_binBracketE {q : ℝ} (hq1 : q < 1) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (binBracketE q)
      ((p - q) ^ 2 * (1 + p) / (2 * p ^ 2 * (1 - p) * (1 - q))) p := by
  have h1p : (1 : ℝ) - p ≠ 0 := by linarith
  have h1q : (1 : ℝ) - q ≠ 0 := by linarith
  have hden : (2 * p * (1 - q)) ≠ 0 := by positivity
  have hnum : HasDerivAt (fun x : ℝ => (x - q) ^ 2) (2 * (p - q)) p := by
    have := ((hasDerivAt_id p).sub_const q).pow 2
    convert this using 1
    simp
  have hd : HasDerivAt (fun x : ℝ => 2 * x * (1 - q)) (2 * (1 - q)) p := by
    have := ((hasDerivAt_id p).const_mul 2).mul_const (1 - q)
    convert this using 1
    simp
  have h := (hasDerivAt_binRate q hp0 hp1).sub (hnum.div hd hden)
  refine h.congr_deriv ?_
  field_simp
  ring

theorem monotoneOn_binBracketE {q : ℝ} (hq1 : q < 1) : MonotoneOn (binBracketE q) (Ioo 0 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 1)
  · intro p hp; exact (hasDerivAt_binBracketE hq1 hp.1 hp.2).continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Ioo] at hp
    exact (hasDerivAt_binBracketE hq1 hp.1 hp.2).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [interior_Ioo] at hp
    rw [(hasDerivAt_binBracketE hq1 hp.1 hp.2).deriv]
    have hp0 : 0 < p := hp.1
    have hp1 : 0 < 1 - p := by linarith [hp.2]
    have hq1' : 0 < 1 - q := by linarith
    positivity

theorem binBracketE_nonpos_of_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {p : ℝ} (hp0 : 0 < p)
    (hpq : p ≤ q) : binBracketE q p ≤ 0 := by
  have := monotoneOn_binBracketE hq1 ⟨hp0, hpq.trans_lt hq1⟩ ⟨hq0, hq1⟩ hpq
  rwa [binBracketE_self] at this

theorem binBracketE_nonneg_of_ge {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {p : ℝ} (hp1 : p < 1)
    (hqp : q ≤ p) : 0 ≤ binBracketE q p := by
  have := monotoneOn_binBracketE hq1 ⟨hq0, hq1⟩ ⟨hq0.trans_le hqp, hp1⟩ hqp
  rwa [binBracketE_self] at this

/-! ### Bracket `F = H − (1−q)(p−q)²/(2q(1−p)²)`, antitone -/

/-- `F(p) = H(p) − (1−q)(p−q)²/(2q(1−p)²)`. -/
noncomputable def binBracketF (q p : ℝ) : ℝ :=
  binRate q p - (1 - q) * (p - q) ^ 2 / (2 * q * (1 - p) ^ 2)

theorem binBracketF_self (q : ℝ) : binBracketF q q = 0 := by simp [binBracketF, binRate_self]

theorem hasDerivAt_binBracketF {q : ℝ} (hq0 : 0 < q) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (binBracketF q)
      (-((p - q) ^ 2 * (1 - p * q) / (p * q * (1 - p) ^ 3))) p := by
  have h1p : (1 : ℝ) - p ≠ 0 := by linarith
  have hden : (2 * q * (1 - p) ^ 2) ≠ 0 := by positivity
  have hnum : HasDerivAt (fun x : ℝ => (1 - q) * (x - q) ^ 2) ((1 - q) * (2 * (p - q))) p := by
    have := (((hasDerivAt_id p).sub_const q).pow 2).const_mul (1 - q)
    convert this using 1
    simp
  have hd : HasDerivAt (fun x : ℝ => 2 * q * (1 - x) ^ 2) (2 * q * (2 * (1 - p) * (-1))) p := by
    have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) p := (hasDerivAt_id p).const_sub 1
    have := (h2.pow 2).const_mul (2 * q)
    convert this using 1
    simp
  have h := (hasDerivAt_binRate q hp0 hp1).sub (hnum.div hd hden)
  refine h.congr_deriv ?_
  field_simp
  ring

theorem antitoneOn_binBracketF {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    AntitoneOn (binBracketF q) (Ioo 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 1)
  · intro p hp; exact (hasDerivAt_binBracketF hq0 hp.1 hp.2).continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Ioo] at hp
    exact (hasDerivAt_binBracketF hq0 hp.1 hp.2).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [interior_Ioo] at hp
    rw [(hasDerivAt_binBracketF hq0 hp.1 hp.2).deriv]
    have hp0 : 0 < p := hp.1
    have hp1 : 0 < 1 - p := by linarith [hp.2]
    have hpq : 0 < 1 - p * q := by nlinarith [hp.2]
    have : 0 ≤ (p - q) ^ 2 * (1 - p * q) / (p * q * (1 - p) ^ 3) := by positivity
    linarith

theorem binBracketF_nonneg_of_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {p : ℝ} (hp0 : 0 < p)
    (hpq : p ≤ q) : 0 ≤ binBracketF q p := by
  have := antitoneOn_binBracketF hq0 hq1 ⟨hp0, hpq.trans_lt hq1⟩ ⟨hq0, hq1⟩ hpq
  rwa [binBracketF_self] at this

theorem binBracketF_nonpos_of_ge {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {p : ℝ} (hp1 : p < 1)
    (hqp : q ≤ p) : binBracketF q p ≤ 0 := by
  have := antitoneOn_binBracketF hq0 hq1 ⟨hq0, hq1⟩ ⟨hq0.trans_le hqp, hp1⟩ hqp
  rwa [binBracketF_self] at this

/-! ### Positivity of `H` -/

theorem binRate_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 ≤ binRate q p := by
  rcases le_or_gt p q with hpq | hqp
  · have hF := binBracketF_nonneg_of_le hq0 hq1 hp0 hpq
    unfold binBracketF at hF
    have : 0 ≤ (1 - q) * (p - q) ^ 2 / (2 * q * (1 - p) ^ 2) := by
      have : 0 < 1 - q := by linarith
      have : 0 < 1 - p := by linarith
      positivity
    linarith
  · have hE := binBracketE_nonneg_of_ge hq0 hq1 hp1 hqp.le
    unfold binBracketE at hE
    have : 0 ≤ (p - q) ^ 2 / (2 * p * (1 - q)) := by
      have : 0 < 1 - q := by linarith
      positivity
    linarith

theorem binRate_pos_of_ne {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hne : p ≠ q) : 0 < binRate q p := by
  have hsq : 0 < (p - q) ^ 2 := by
    have : p - q ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have h1q : 0 < 1 - q := by linarith
  have h1p : 0 < 1 - p := by linarith
  rcases lt_or_gt_of_ne hne with hpq | hqp
  · have hF := binBracketF_nonneg_of_le hq0 hq1 hp0 hpq.le
    unfold binBracketF at hF
    have : 0 < (1 - q) * (p - q) ^ 2 / (2 * q * (1 - p) ^ 2) := by positivity
    linarith
  · have hE := binBracketE_nonneg_of_ge hq0 hq1 hp1 hqp.le
    unfold binBracketE at hE
    have : 0 < (p - q) ^ 2 / (2 * p * (1 - q)) := by positivity
    linarith

/-! ### `r² = (p−q)² / (2H(1−p)²)` -/

/-- `r² = (p−q)² / (2 H (1−p)²)`. -/
noncomputable def binRSq (q p : ℝ) : ℝ := (p - q) ^ 2 / (2 * binRate q p * (1 - p) ^ 2)

theorem hasDerivAt_binRSq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hne : p ≠ q) :
    HasDerivAt (binRSq q)
      ((p - q) * (1 - q) * binBracketE q p / (binRate q p ^ 2 * (1 - p) ^ 3)) p := by
  have hH : 0 < binRate q p := binRate_pos_of_ne hq0 hq1 hp0 hp1 hne
  have h1p : (1 : ℝ) - p ≠ 0 := by linarith
  have h1q : (1 : ℝ) - q ≠ 0 := by linarith
  have hnum : HasDerivAt (fun x : ℝ => (x - q) ^ 2) (2 * (p - q)) p := by
    have := ((hasDerivAt_id p).sub_const q).pow 2
    convert this using 1
    simp
  have hsq : HasDerivAt (fun x : ℝ => (1 - x) ^ 2) (2 * (1 - p) * (-1)) p := by
    have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) p := (hasDerivAt_id p).const_sub 1
    have := h2.pow 2
    convert this using 1
    simp
  have hd := ((hasDerivAt_binRate q hp0 hp1).const_mul 2).mul hsq
  have hden : 2 * binRate q p * (1 - p) ^ 2 ≠ 0 := by positivity
  have h := hnum.div hd hden
  refine h.congr_deriv ?_
  have hH' : binRate q p ≠ 0 := hH.ne'
  have hp0' : p ≠ 0 := hp0.ne'
  unfold binBracketE
  simp only [Pi.mul_apply]
  field_simp
  ring

theorem monotoneOn_binRSq_left {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    MonotoneOn (binRSq q) (Ioo 0 q) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 q)
  · intro p hp
    exact (hasDerivAt_binRSq hq0 hq1 hp.1 (hp.2.trans hq1) hp.2.ne).continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Ioo] at hp
    exact (hasDerivAt_binRSq hq0 hq1 hp.1 (hp.2.trans hq1)
      hp.2.ne).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [interior_Ioo] at hp
    rw [(hasDerivAt_binRSq hq0 hq1 hp.1 (hp.2.trans hq1) hp.2.ne).deriv]
    have hE := binBracketE_nonpos_of_le hq0 hq1 hp.1 hp.2.le
    have hnum : 0 ≤ (p - q) * (1 - q) * binBracketE q p := by
      have : (p - q) * (1 - q) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith [hp.2]) (by linarith)
      exact mul_nonneg_of_nonpos_of_nonpos this hE
    have hH := binRate_pos_of_ne hq0 hq1 hp.1 (hp.2.trans hq1) hp.2.ne
    have h1p : 0 < 1 - p := by linarith [hp.2.trans hq1]
    exact div_nonneg hnum (by positivity)

theorem monotoneOn_binRSq_right {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    MonotoneOn (binRSq q) (Ioo q 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo q 1)
  · intro p hp
    exact (hasDerivAt_binRSq hq0 hq1 (hq0.trans hp.1) hp.2
      (ne_of_gt hp.1)).continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Ioo] at hp
    exact (hasDerivAt_binRSq hq0 hq1 (hq0.trans hp.1) hp.2
      (ne_of_gt hp.1)).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [interior_Ioo] at hp
    rw [(hasDerivAt_binRSq hq0 hq1 (hq0.trans hp.1) hp.2 (ne_of_gt hp.1)).deriv]
    have hE := binBracketE_nonneg_of_ge hq0 hq1 hp.2 hp.1.le
    have hnum : 0 ≤ (p - q) * (1 - q) * binBracketE q p := by
      have : 0 ≤ (p - q) * (1 - q) := mul_nonneg (by linarith [hp.1]) (by linarith)
      exact mul_nonneg this hE
    have hH := binRate_pos_of_ne hq0 hq1 (hq0.trans hp.1) hp.2 (ne_of_gt hp.1)
    have h1p : 0 < 1 - p := by linarith [hp.2]
    exact div_nonneg hnum (by positivity)

theorem binRSq_le_of_lt {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {p : ℝ} (hp0 : 0 < p) (hpq : p < q) :
    binRSq q p ≤ q / (1 - q) := by
  have hH := binRate_pos_of_ne hq0 hq1 hp0 (hpq.trans hq1) hpq.ne
  have hF := binBracketF_nonneg_of_le hq0 hq1 hp0 hpq.le
  unfold binBracketF at hF
  have h1q : 0 < 1 - q := by linarith
  have h1p : 0 < 1 - p := by linarith [hpq.trans hq1]
  unfold binRSq
  rw [div_le_div_iff₀ (by positivity) h1q]
  rw [sub_nonneg, div_le_iff₀ (by positivity)] at hF
  nlinarith

theorem le_binRSq_of_gt {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {p : ℝ} (hp1 : p < 1) (hqp : q < p) :
    q / (1 - q) ≤ binRSq q p := by
  have hH := binRate_pos_of_ne hq0 hq1 (hq0.trans hqp) hp1 (ne_of_gt hqp)
  have hF := binBracketF_nonpos_of_ge hq0 hq1 hp1 hqp.le
  unfold binBracketF at hF
  have h1q : 0 < 1 - q := by linarith
  have h1p : 0 < 1 - p := by linarith
  unfold binRSq
  rw [div_le_div_iff₀ h1q (by positivity)]
  rw [sub_nonpos, le_div_iff₀ (by positivity)] at hF
  nlinarith

/-! ### `r(p) = |p−q| / ((1−p)√(2H))`, monotone on `(0,1)` -/

/-- `r(p) = |p−q| / ((1−p) √(2H(p)))`, with the continuous value `√(q/(1−q))` at `p = q`. -/
noncomputable def binR (q p : ℝ) : ℝ :=
  if p = q then Real.sqrt (q / (1 - q)) else |p - q| / ((1 - p) * Real.sqrt (2 * binRate q p))

theorem binR_of_ne (q : ℝ) {p : ℝ} (hne : p ≠ q) :
    binR q p = |p - q| / ((1 - p) * Real.sqrt (2 * binRate q p)) := by simp [binR, hne]

theorem binR_self (q : ℝ) : binR q q = Real.sqrt (q / (1 - q)) := by simp [binR]

theorem binR_eq_sqrt_binRSq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hne : p ≠ q) : binR q p = Real.sqrt (binRSq q p) := by
  rw [binR_of_ne q hne]
  have h2H : 0 ≤ 2 * binRate q p := by linarith [binRate_nonneg hq0 hq1 hp0 hp1]
  have h1p : 0 ≤ 1 - p := by linarith
  have : binRSq q p = (|p - q| / ((1 - p) * Real.sqrt (2 * binRate q p))) ^ 2 := by
    unfold binRSq; rw [div_pow, mul_pow, Real.sq_sqrt h2H, sq_abs]; ring
  rw [this, Real.sqrt_sq (by positivity)]

theorem binR_nonneg (q : ℝ) {p : ℝ} (hp1 : p < 1) : 0 ≤ binR q p := by
  unfold binR
  split_ifs
  · exact Real.sqrt_nonneg _
  · have : 0 ≤ 1 - p := by linarith
    positivity

/-- `r` is monotone on `(0,1)`. -/
theorem binR_mono {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hy1 : y < 1) : binR q x ≤ binR q y := by
  have hx1 : x < 1 := hxy.trans_lt hy1
  have hy : 0 < y := hx.trans_le hxy
  have hleft : ∀ p, 0 < p → p < q → binR q p ≤ Real.sqrt (q / (1 - q)) := by
    intro p hp hpq
    rw [binR_eq_sqrt_binRSq hq0 hq1 hp (hpq.trans hq1) hpq.ne]
    exact Real.sqrt_le_sqrt (binRSq_le_of_lt hq0 hq1 hp hpq)
  have hright : ∀ p, q < p → p < 1 → Real.sqrt (q / (1 - q)) ≤ binR q p := by
    intro p hqp hp1
    rw [binR_eq_sqrt_binRSq hq0 hq1 (hq0.trans hqp) hp1 (ne_of_gt hqp)]
    exact Real.sqrt_le_sqrt (le_binRSq_of_gt hq0 hq1 hp1 hqp)
  rcases lt_trichotomy x q with hxq | hxq | hxq
  · rcases lt_trichotomy y q with hyq | hyq | hyq
    · rw [binR_eq_sqrt_binRSq hq0 hq1 hx hx1 hxq.ne, binR_eq_sqrt_binRSq hq0 hq1 hy hy1 hyq.ne]
      exact Real.sqrt_le_sqrt (monotoneOn_binRSq_left hq0 hq1 ⟨hx, hxq⟩ ⟨hy, hyq⟩ hxy)
    · rw [hyq, binR_self]; exact hleft x hx hxq
    · exact (hleft x hx hxq).trans (hright y hyq hy1)
  · subst hxq
    rcases eq_or_lt_of_le hxy with hyq | hyq
    · rw [← hyq]
    · rw [binR_self]; exact hright y hyq hy1
  · have hyq : q < y := hxq.trans_le hxy
    rw [binR_eq_sqrt_binRSq hq0 hq1 hx hx1 (ne_of_gt hxq),
      binR_eq_sqrt_binRSq hq0 hq1 hy hy1 (ne_of_gt hyq)]
    exact Real.sqrt_le_sqrt (monotoneOn_binRSq_right hq0 hq1 ⟨hxq, hx1⟩ ⟨hyq, hy1⟩ hxy)

/-! ### Limits of `H` at the ends -/

/-- `H → +∞` as `p → 0⁺` (for `q > 0`). -/
theorem tendsto_binRate_nhdsGT_zero {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (binRate q) (𝓝[>] 0) atTop := by
  have hlog : Tendsto (fun p : ℝ => -q * Real.log p) (𝓝[>] 0) atTop :=
    Tendsto.const_mul_atBot_of_neg (by linarith) Real.tendsto_log_nhdsGT_zero
  have hlin : Tendsto (fun p : ℝ => -q * Real.log p +
      (q * Real.log q + (1 - q) * Real.log (1 - q))) (𝓝[>] 0) atTop :=
    tendsto_atTop_add_const_right _ _ hlog
  refine tendsto_atTop_mono' _ ?_ hlin
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with p hp
  have h1p : Real.log (1 - p) ≤ 0 := Real.log_nonpos (by linarith [hp.2]) (by linarith [hp.1])
  have h1q : 0 ≤ 1 - q := by linarith
  unfold binRate
  nlinarith

theorem tendsto_one_sub_nhdsLT_one : Tendsto (fun p : ℝ => 1 - p) (𝓝[<] 1) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have : Tendsto (fun p : ℝ => 1 - p) (𝓝 1) (𝓝 (1 - 1)) :=
      (continuous_const.sub continuous_id).tendsto 1
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with p hp
    exact sub_pos.mpr (mem_Iio.mp hp)

/-- `H → +∞` as `p → 1⁻` (for `q < 1`). -/
theorem tendsto_binRate_nhdsLT_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (binRate q) (𝓝[<] 1) atTop := by
  have h := (tendsto_binRate_nhdsGT_zero (q := 1 - q) (by linarith) (by linarith)).comp
    tendsto_one_sub_nhdsLT_one
  refine h.congr fun p => ?_
  simp only [Function.comp]
  rw [binRate_symm]

end Ripple.Kurtz.StrongApprox
