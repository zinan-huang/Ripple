/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.HeavyBBand
import Tri.HeavyBBandReturn

/-!
# Heavy-B window-kernel direction tails with ratio guards

This file threads the corrected Heavy-B ratio guard through the stopped
level-window kernel `heavyBandStop`.  The potential is the existing
`heavyPotential w η = w^level * η^(up+down)`, but the one-step guard is
`q*y <= p*x`, so the usable ratio parameter is `p/q < 1` rather than a natural
number `u >= 1`.
-/

namespace Tri

open scoped ENNReal

/-- Ratio scalar step without the unnecessary `p != 0` side condition carried
by `heavy_dir_scalar_ratio`.  The proof is the same instantiation of
`doubleDir_scalar`; the ratio `p/q` is well-formed as soon as `q != 0`. -/
theorem heavy_dir_scalar_ratio_nohp {n p q : ℕ} (s : HeavyState n)
    (h : 2 ≤ heavyEntities s) (w η : ℝ≥0∞)
    (hq : q ≠ 0) (hguard : q * s.1.y ≤ p * s.1.x)
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
  · rw [← heavyResolveDown_eq s h]
    exact PMF.apply_ne_top _ _
  · unfold heavyNeutralMass
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩,
          PMF.apply_ne_top _ _⟩,
        PMF.apply_ne_top _ _⟩
  · rw [← heavyResolveUp_eq s h]
    exact PMF.apply_ne_top _ _

/-- One Heavy-B trace step decreases the ratio potential under a ratio guard. -/
theorem heavyPotential_step_ratio {n p q : ℕ} (s : HeavyTrace n)
    (h : 2 ≤ heavyEntities s.cfg) (a : ℕ)
    (ha : BiCfg.heavyLevel s.cfg.1 = a + 1)
    (w η : ℝ≥0∞) (hq : q ≠ 0)
    (hguard : q * s.cfg.1.y ≤ p * s.cfg.1.x)
    (hrel : η * ((p : ℝ≥0∞) / (q : ℝ≥0∞) + w ^ 2)
      = w * ((p : ℝ≥0∞) / (q : ℝ≥0∞) + 1))
    (hwη : w ≤ η) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤) :
    expect (heavyTraceStep n s) (heavyPotential w η) ≤ heavyPotential w η s := by
  have hexp := heavyTraceStep_expect n s h a ha (fun L u d => w ^ L * η ^ (u + d))
  have hscalar :=
    heavy_dir_scalar_ratio_nohp s.cfg h w η hq hguard hrel hwη hwt hηt
  unfold heavyPotential
  rw [hexp, ha]
  set dn := heavyResolveDown s.cfg
  set up := heavyResolveUp s.cfg
  set neu := heavyNeutralMass h
  set r := s.up + s.down with hr
  have e1 : s.up + (s.down + 1) = r + 1 := by omega
  have e2 : s.up + 1 + s.down = r + 1 := by omega
  rw [e1, e2]
  calc dn * (w ^ a * η ^ (r + 1)) + neu * (w ^ (a + 1) * η ^ r)
        + up * (w ^ (a + 2) * η ^ (r + 1))
      = (w ^ a * η ^ r) * (neu * w + η * (dn + up * w ^ 2)) := by
        rw [pow_succ, pow_succ, pow_succ, pow_succ]
        ring
    _ ≤ (w ^ a * η ^ r) * w := by gcongr
    _ = w ^ (a + 1) * η ^ r := by rw [pow_succ]; ring

/-- Window geometry produces the reciprocal ratio guard used by the one-step
Heavy-B direction inequality. -/
theorem heavyBand_window_guard_geom {n aLo p q : ℕ}
    (hgeomY : aLo + 1 + p = n)
    (hgeomX : q + n = 2 * (aLo + 1))
    (s : HeavyTrace n)
    (hlive : aLo + 1 ≤ BiCfg.heavyLevel s.cfg.1) :
    q * s.cfg.1.y ≤ p * s.cfg.1.x := by
  have hinv : s.cfg.1.x + s.cfg.1.y + 2 * s.cfg.1.b = n := s.cfg.2
  have hy : s.cfg.1.y ≤ p := by
    simp only [BiCfg.heavyLevel] at hlive
    omega
  have hx : q ≤ s.cfg.1.x := by
    simp only [BiCfg.heavyLevel] at hlive
    omega
  calc
    q * s.cfg.1.y ≤ q * p := Nat.mul_le_mul_left q hy
    _ = p * q := by ring
    _ ≤ p * s.cfg.1.x := Nat.mul_le_mul_left p hx

/-- Supermartingale form for any stopped window once the ratio guard is known
on every live state of that window. -/
theorem heavyBandWindowStop_super_of_guard {n : ℕ} (hn : 3 ≤ n)
    (aLo hi p q : ℕ) (hq : q ≠ 0)
    (hguard : ∀ s : HeavyTrace n,
      aLo + 1 ≤ BiCfg.heavyLevel s.cfg.1 →
      BiCfg.heavyLevel s.cfg.1 + 1 ≤ hi →
      q * s.cfg.1.y ≤ p * s.cfg.1.x)
    (w η u : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (q : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hwt : w ≠ ⊤) (hηt : η ≠ ⊤) :
    ∀ s, expect (heavyBandStop n aLo hi s) (heavyPotential w η)
      ≤ 1 * heavyPotential w η s := by
  intro s
  rw [one_mul]
  unfold heavyBandStop
  split_ifs with hlive
  · obtain ⟨a, ha⟩ : ∃ a, BiCfg.heavyLevel s.cfg.1 = a + 1 :=
      ⟨BiCfg.heavyLevel s.cfg.1 - 1, by omega⟩
    have hent : 2 ≤ heavyEntities s.cfg := heavy_two_entities hn s.cfg
    have hrel' : η * ((p : ℝ≥0∞) / (q : ℝ≥0∞) + w ^ 2)
        = w * ((p : ℝ≥0∞) / (q : ℝ≥0∞) + 1) := by
      simpa [hu] using hrel
    exact heavyPotential_step_ratio s hent a ha w η hq
      (hguard s hlive.1 hlive.2) hrel' hwη hwt hηt
  · rw [expect_pure]

/-- The SPEC-shaped window supermartingale: the additive geometry witnesses
derive the ratio guard on-window. -/
theorem heavyBandWindowStop_super {n : ℕ} (hn : 3 ≤ n)
    (aLo hi p q : ℕ) (hq : q ≠ 0)
    (hgeomY : aLo + 1 + p = n)
    (hgeomX : q + n = 2 * (aLo + 1))
    (w η u : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (q : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hwt : w ≠ ⊤) (hηt : η ≠ ⊤) :
    ∀ s, expect (heavyBandStop n aLo hi s) (heavyPotential w η)
      ≤ 1 * heavyPotential w η s := by
  exact heavyBandWindowStop_super_of_guard hn aLo hi p q hq
    (fun s hlive _ => heavyBand_window_guard_geom hgeomY hgeomX s hlive)
    w η u hu hrel hwη hwt hηt

/-- Markov tail for the stopped Heavy-B level window under an on-window ratio
guard. -/
theorem heavyBandWindowStop_tail_of_guard {n : ℕ} (hn : 3 ≤ n)
    (aLo hi p q thr M T : ℕ) (hq : q ≠ 0)
    (hguard : ∀ s : HeavyTrace n,
      aLo + 1 ≤ BiCfg.heavyLevel s.cfg.1 →
      BiCfg.heavyLevel s.cfg.1 + 1 ≤ hi →
      q * s.cfg.1.y ≤ p * s.cfg.1.x)
    (w η u : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (q : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (s₀ : HeavyTrace n) (hr0 : s₀.up + s₀.down = 0) :
    ∑' s, (if BiCfg.heavyLevel s.cfg.1 ≤ thr ∧ M ≤ s.up + s.down then
        iter (heavyBandStop n aLo hi) T s₀ s else 0)
      ≤ w ^ BiCfg.heavyLevel s₀.cfg.1 / (w ^ thr * η ^ M) := by
  have hwt : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  set θ : ℝ≥0∞ := w ^ thr * η ^ M with hθdef
  have hθ0 : θ ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ hw0)
    exact pow_ne_zero _ (by rintro rfl; simp at hη1)
  have hθtop : θ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hwt) (ENNReal.pow_ne_top hηt)
  have hsub : ∀ s : HeavyTrace n,
      (if BiCfg.heavyLevel s.cfg.1 ≤ thr ∧ M ≤ s.up + s.down then
        iter (heavyBandStop n aLo hi) T s₀ s else 0)
      ≤ (if θ ≤ heavyPotential w η s then
        iter (heavyBandStop n aLo hi) T s₀ s else 0) := by
    intro s
    by_cases hs : BiCfg.heavyLevel s.cfg.1 ≤ thr ∧ M ≤ s.up + s.down
    · have hle : θ ≤ heavyPotential w η s := by
        rw [hθdef, heavyPotential]
        exact mul_le_mul' (pow_le_pow_right_of_le_one' hw1 hs.1)
          (pow_le_pow_right₀ hη1 hs.2)
      simp [hs, hle]
    · simp [hs]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans (markov_div (iter (heavyBandStop n aLo hi) T s₀)
    (heavyPotential w η) θ hθ0 hθtop) ?_
  have hiter := expect_iter_le (heavyBandStop n aLo hi) (heavyPotential w η) 1
    (heavyBandWindowStop_super_of_guard hn aLo hi p q hq hguard
      w η u hu hrel hwη hwt hηt) T s₀
  have hΘ0 : heavyPotential w η s₀ = w ^ BiCfg.heavyLevel s₀.cfg.1 := by
    simp [heavyPotential, hr0]
  rw [one_pow, one_mul, hΘ0] at hiter
  exact ENNReal.div_le_div_right hiter θ

/-- The SPEC-shaped Markov tail: the additive geometry witnesses derive the
ratio guard on-window. -/
theorem heavyBandWindowStop_tail {n : ℕ} (hn : 3 ≤ n)
    (aLo hi p q thr M T : ℕ) (hq : q ≠ 0)
    (hgeomY : aLo + 1 + p = n)
    (hgeomX : q + n = 2 * (aLo + 1))
    (w η u : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (q : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (s₀ : HeavyTrace n) (hr0 : s₀.up + s₀.down = 0) :
    ∑' s, (if BiCfg.heavyLevel s.cfg.1 ≤ thr ∧ M ≤ s.up + s.down then
        iter (heavyBandStop n aLo hi) T s₀ s else 0)
      ≤ w ^ BiCfg.heavyLevel s₀.cfg.1 / (w ^ thr * η ^ M) := by
  exact heavyBandWindowStop_tail_of_guard hn aLo hi p q thr M T hq
    (fun s hlive _ => heavyBand_window_guard_geom hgeomY hgeomX s hlive)
    w η u hu hrel hwη hw1 hw0 hη1 hηt s₀ hr0

/-- Backslide specialization of the stopped-window tail. -/
theorem heavyWindow_backslide_tail {n : ℕ} (hn : 3 ≤ n)
    (aLo hi p q thr Bw T : ℕ) (hq : q ≠ 0)
    (hgeomY : aLo + 1 + p = n)
    (hgeomX : q + n = 2 * (aLo + 1))
    (w η u : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (q : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (s₀ : HeavyTrace n) (hr0 : s₀.up + s₀.down = 0)
    (hlev : BiCfg.heavyLevel s₀.cfg.1 = thr + Bw) :
    ∑' s, (if BiCfg.heavyLevel s.cfg.1 ≤ thr then
        iter (heavyBandStop n aLo hi) T s₀ s else 0)
      ≤ w ^ Bw := by
  have hwt : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  have hmain := heavyBandWindowStop_tail hn aLo hi p q thr 0 T hq hgeomY hgeomX
    w η u hu hrel hwη hw1 hw0 hη1 hηt s₀ hr0
  simp only [pow_zero, mul_one, Nat.zero_le, and_true] at hmain
  refine le_trans hmain (le_of_eq ?_)
  rw [hlev, pow_add, div_eq_mul_inv]
  calc w ^ thr * w ^ Bw * (w ^ thr)⁻¹
      = w ^ Bw * (w ^ thr * (w ^ thr)⁻¹) := by ring
    _ = w ^ Bw := by
        rw [ENNReal.mul_inv_cancel (pow_ne_zero _ hw0)
          (ENNReal.pow_ne_top hwt), mul_one]

/-- Deadline specialization of the stopped-window tail. -/
theorem heavyWindow_deadline_tail {n : ℕ} (hn : 3 ≤ n)
    (aLo hi p q Lhi Bw T : ℕ) (hq : q ≠ 0)
    (hgeomY : aLo + 1 + p = n)
    (hgeomX : q + n = 2 * (aLo + 1))
    (w η u : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (q : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hw1 : w ≤ 1) (hw0 : w ≠ 0) (hη1 : 1 ≤ η) (hηt : η ≠ ⊤)
    (s₀ : HeavyTrace n) (hr0 : s₀.up + s₀.down = 0)
    (hLhi : BiCfg.heavyLevel s₀.cfg.1 + 2 * Bw = Lhi) :
    ∑' s, (if BiCfg.heavyLevel s.cfg.1 ≤ Lhi ∧ 2 * n ≤ s.up + s.down then
        iter (heavyBandStop n aLo hi) T s₀ s else 0)
      ≤ 1 / (w ^ (2 * Bw) * η ^ (2 * n)) := by
  have hwt : w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hw1
  refine le_trans (heavyBandWindowStop_tail hn aLo hi p q Lhi (2 * n) T hq
    hgeomY hgeomX w η u hu hrel hwη hw1 hw0 hη1 hηt s₀ hr0) (le_of_eq ?_)
  rw [← hLhi, pow_add, mul_assoc, div_eq_mul_inv, one_div,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ hw0))
      (Or.inl (ENNReal.pow_ne_top hwt)), ← mul_assoc,
    ENNReal.mul_inv_cancel (pow_ne_zero _ hw0) (ENNReal.pow_ne_top hwt),
    one_mul]

/-- The real band parameters satisfy the direction optimum relation. -/
theorem heavyBand_relation_real {a B : ℕ} (ha : 0 < a) (_hB : 0 < B) :
    heavyBandEta a B * (heavyBandU a B + heavyBandW a B ^ 2)
      = heavyBandW a B * (heavyBandU a B + 1) := by
  have hden : heavyBandU a B + heavyBandW a B ^ 2 ≠ 0 := by
    have hu : 0 < heavyBandU a B := heavyBandU_pos ha
    positivity
  unfold heavyBandEta
  field_simp [hden]

/-- The Heavy-B band parameters, transferred to `ℝ≥0∞`, satisfy the complete
hypothesis bundle needed by the stopped-window ratio tail. -/
theorem heavyBand_params_enn {n a B : ℕ} (ha : 0 < a) (hB : 0 < B)
    (_hparam : a + 2 * B = n) :
    let w : ℝ≥0∞ := ENNReal.ofReal (heavyBandW a B)
    let η : ℝ≥0∞ := ENNReal.ofReal (heavyBandEta a B)
    let u : ℝ≥0∞ := (a : ℝ≥0∞) / ((a + 4 * B : ℕ) : ℝ≥0∞)
    η * (u + w ^ 2) = w * (u + 1) ∧
      w ≤ η ∧ w ≤ 1 ∧ w ≠ 0 ∧ 1 ≤ η ∧ η ≠ ⊤ ∧ w ≠ ⊤ := by
  dsimp
  have huRpos : 0 < heavyBandU a B := heavyBandU_pos ha
  have huR0 : 0 ≤ heavyBandU a B := huRpos.le
  have hwRpos : 0 < heavyBandW a B := by
    obtain ⟨hu, huw, -⟩ := heavyBand_tail_regime ha hB
    exact hu.trans huw
  have hwR0 : 0 ≤ heavyBandW a B := hwRpos.le
  have hηRpos : 0 < heavyBandEta a B := heavyBandEta_pos ha hB
  have hηR0 : 0 ≤ heavyBandEta a B := hηRpos.le
  have hdenNatR : 0 < (((a + 4 * B : ℕ) : ℝ)) := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    positivity
  have huenn :
      (a : ℝ≥0∞) / ((a + 4 * B : ℕ) : ℝ≥0∞)
        = ENNReal.ofReal (heavyBandU a B) := by
    rw [← ENNReal.ofReal_natCast a,
      ← ENNReal.ofReal_natCast (a + 4 * B),
      ← ENNReal.ofReal_div_of_pos hdenNatR]
    congr 1
    unfold heavyBandU
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have hrel : ENNReal.ofReal (heavyBandEta a B) *
        ((a : ℝ≥0∞) / ((a + 4 * B : ℕ) : ℝ≥0∞) +
          ENNReal.ofReal (heavyBandW a B) ^ 2)
      = ENNReal.ofReal (heavyBandW a B) *
        ((a : ℝ≥0∞) / ((a + 4 * B : ℕ) : ℝ≥0∞) + 1) := by
    rw [huenn]
    calc
      ENNReal.ofReal (heavyBandEta a B) *
          (ENNReal.ofReal (heavyBandU a B) +
            ENNReal.ofReal (heavyBandW a B) ^ 2)
          = ENNReal.ofReal (heavyBandEta a B) *
              ENNReal.ofReal (heavyBandU a B + heavyBandW a B ^ 2) := by
            rw [← ENNReal.ofReal_pow hwR0,
              ← ENNReal.ofReal_add huR0 (pow_nonneg hwR0 2)]
      _ = ENNReal.ofReal
            (heavyBandEta a B * (heavyBandU a B + heavyBandW a B ^ 2)) := by
            rw [ENNReal.ofReal_mul hηR0]
      _ = ENNReal.ofReal
            (heavyBandW a B * (heavyBandU a B + 1)) := by
            rw [heavyBand_relation_real ha hB]
      _ = ENNReal.ofReal (heavyBandW a B) *
            ENNReal.ofReal (heavyBandU a B + 1) := by
            rw [ENNReal.ofReal_mul hwR0]
      _ = ENNReal.ofReal (heavyBandW a B) *
            (ENNReal.ofReal (heavyBandU a B) + 1) := by
            rw [ENNReal.ofReal_add huR0 zero_le_one, ENNReal.ofReal_one]
  refine ⟨hrel, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ENNReal.ofReal_le_ofReal (heavyBandW_le_eta ha hB)
  · exact ENNReal.ofReal_le_one.mpr (le_of_lt (heavyBandW_lt_one hB))
  · exact ne_of_gt (ENNReal.ofReal_pos.mpr hwRpos)
  · rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (heavyBandEta_ge_one ha hB)
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.ofReal_ne_top

/-- The concrete Heavy-B band window floor implies the ratio guard
`(a+4B) y <= a x` on every live window state. -/
theorem heavyBand_window_guard_params {n a B aLo : ℕ}
    (hparam : a + 2 * B = n)
    (hfloor : n + 2 * B ≤ 2 * (aLo + 1))
    (s : HeavyTrace n)
    (hlive : aLo + 1 ≤ BiCfg.heavyLevel s.cfg.1) :
    (a + 4 * B) * s.cfg.1.y ≤ a * s.cfg.1.x := by
  have hinv : s.cfg.1.x + s.cfg.1.y + 2 * s.cfg.1.b = n := s.cfg.2
  simp only [BiCfg.heavyLevel] at hlive
  nlinarith

/-- End-to-end Heavy-B window band error with the ratio parameters witnessed
internally.  The two masses are the actual stopped trace masses under
`heavyBandStop n aLo hi`; no direction-parameter hypotheses remain. -/
theorem heavy_band_error_exp_witnessed {n a B aLo hi thr Lhi T : ℕ}
    (gamma lgN : ℝ)
    (ha : 0 < a) (hB : 0 < B) (hparam : a + 2 * B = n)
    (hquarter : 4 * B ≤ n)
    (hfloor : n + 2 * B ≤ 2 * (aLo + 1))
    (hstage : gamma * lgN * (n : ℝ) ≤ 16 * (B : ℝ) ^ 2)
    (s₀ : HeavyTrace n) (hr0 : s₀.up + s₀.down = 0)
    (hbackLevel : BiCfg.heavyLevel s₀.cfg.1 = thr + B)
    (hdeadlineLevel : BiCfg.heavyLevel s₀.cfg.1 + 2 * B = Lhi) :
    (∑' s, (if BiCfg.heavyLevel s.cfg.1 ≤ thr then
        iter (heavyBandStop n aLo hi) T s₀ s else 0)) +
      (∑' s, (if BiCfg.heavyLevel s.cfg.1 ≤ Lhi ∧
          2 * n ≤ s.up + s.down then
        iter (heavyBandStop n aLo hi) T s₀ s else 0))
      ≤ ENNReal.ofReal
        (2 * Real.exp
          (-(Real.log ((5 : ℝ) / 4) / 4) * (gamma * lgN))) := by
  let w : ℝ≥0∞ := ENNReal.ofReal (heavyBandW a B)
  let η : ℝ≥0∞ := ENNReal.ofReal (heavyBandEta a B)
  let u : ℝ≥0∞ := (a : ℝ≥0∞) / ((a + 4 * B : ℕ) : ℝ≥0∞)
  have hparams := heavyBand_params_enn ha hB hparam
  dsimp only at hparams
  rcases hparams with ⟨hrel, hwη, hw1, hw0, hη1, hηt, hwt⟩
  have hn3 : 3 ≤ n := by omega
  have hq : a + 4 * B ≠ 0 := by omega
  have hguard : ∀ s : HeavyTrace n,
      aLo + 1 ≤ BiCfg.heavyLevel s.cfg.1 →
      BiCfg.heavyLevel s.cfg.1 + 1 ≤ hi →
      (a + 4 * B) * s.cfg.1.y ≤ a * s.cfg.1.x := by
    intro s hlive _
    exact heavyBand_window_guard_params hparam hfloor s hlive
  have hback :
      (∑' s, (if BiCfg.heavyLevel s.cfg.1 ≤ thr then
          iter (heavyBandStop n aLo hi) T s₀ s else 0))
        ≤ w ^ B := by
    have hmain := heavyBandWindowStop_tail_of_guard (n := n) hn3
      aLo hi a (a + 4 * B) thr 0 T hq hguard
      w η u rfl hrel hwη hw1 hw0 hη1 hηt s₀ hr0
    simp only [pow_zero, mul_one, Nat.zero_le, and_true] at hmain
    refine le_trans hmain (le_of_eq ?_)
    rw [hbackLevel, pow_add, div_eq_mul_inv]
    calc w ^ thr * w ^ B * (w ^ thr)⁻¹
        = w ^ B * (w ^ thr * (w ^ thr)⁻¹) := by ring
      _ = w ^ B := by
          rw [ENNReal.mul_inv_cancel (pow_ne_zero _ hw0)
            (ENNReal.pow_ne_top hwt), mul_one]
  have hdeadline :
      (∑' s, (if BiCfg.heavyLevel s.cfg.1 ≤ Lhi ∧
            2 * n ≤ s.up + s.down then
          iter (heavyBandStop n aLo hi) T s₀ s else 0))
        ≤ 1 / (w ^ (2 * B) * η ^ (2 * n)) := by
    have hmain := heavyBandWindowStop_tail_of_guard (n := n) hn3
      aLo hi a (a + 4 * B) Lhi (2 * n) T hq hguard
      w η u rfl hrel hwη hw1 hw0 hη1 hηt s₀ hr0
    refine le_trans hmain (le_of_eq ?_)
    rw [← hdeadlineLevel, pow_add, mul_assoc, div_eq_mul_inv, one_div,
      ENNReal.mul_inv (Or.inl (pow_ne_zero _ hw0))
        (Or.inl (ENNReal.pow_ne_top hwt)), ← mul_assoc,
      ENNReal.mul_inv_cancel (pow_ne_zero _ hw0) (ENNReal.pow_ne_top hwt),
      one_mul]
  exact heavy_band_error_exp gamma lgN
    (∑' s, (if BiCfg.heavyLevel s.cfg.1 ≤ thr then
        iter (heavyBandStop n aLo hi) T s₀ s else 0))
    (∑' s, (if BiCfg.heavyLevel s.cfg.1 ≤ Lhi ∧
          2 * n ≤ s.up + s.down then
        iter (heavyBandStop n aLo hi) T s₀ s else 0))
    ha hB hparam hquarter hstage hback hdeadline

end Tri

#print axioms Tri.heavy_dir_scalar_ratio_nohp
#print axioms Tri.heavyPotential_step_ratio
#print axioms Tri.heavyBand_window_guard_geom
#print axioms Tri.heavyBandWindowStop_super_of_guard
#print axioms Tri.heavyBandWindowStop_super
#print axioms Tri.heavyBandWindowStop_tail_of_guard
#print axioms Tri.heavyBandWindowStop_tail
#print axioms Tri.heavyWindow_backslide_tail
#print axioms Tri.heavyWindow_deadline_tail
#print axioms Tri.heavyBand_relation_real
#print axioms Tri.heavyBand_params_enn
#print axioms Tri.heavyBand_window_guard_params
#print axioms Tri.heavy_band_error_exp_witnessed
