/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBBandKernel
import Tri.SingleBCreationTail
import Tri.FiveJumpMGF
import Tri.DoubleBAssembly

/-!
# Single-B physical return engine on the co-level

The Single-B physical doubled level `2x+b` is a submartingale wherever
`x ≥ y`, but its noise contains the FAIR creation pair `X+Y → X+B` versus
`X+Y → Y+B`, so no Feller ratio bound is available.  The correct observable
is the doubled co-level `2y+b`, whose one-step exponential moment is
controlled by the *co-level itself*: on states with `2y+b < B ≤ n` the
up-mass of the co-level is at most `B/(n-1)`, because every co-raising
event consumes a `Y`.

This yields the horizon-bounded return estimate: starting `sret+1` co-units
above the failure boundary `B = 2n - Lexit + 1`,

```
P[ level < Lexit at time U ≤ T ] ≤ (1 + ε²·B/(n-1))^T / (1+ε)^(sret+1).
```

The file also provides the horizon-bounded freeze transfer with an
exception event (`failure_le_failure_freeze_add_exc`), which lets the band
transfer charge frozen success states with unpinned physical level (the
creation-imbalance freezes) to their own tail streams; and the Single-B
non-consensus mass equality between the physical chain and the invariant
state chain.
-/

namespace Tri

open scoped ENNReal

variable {α : Type*}

/-! ## Horizon-bounded freeze transfer with an exception stream -/

/-- Horizon-bounded variant of `failure_le_failure_freeze_add`, with an
exception event `E`.  Frozen success states inside `E` are counted as
failures of the frozen chain, so the uniform return bound `δ` is only
demanded on frozen success states outside `E`, and only for horizons up
to `T`. -/
theorem failure_le_failure_freeze_add_exc {B A E : α → Prop}
    [DecidablePred B] [DecidablePred A] [DecidablePred E]
    {K : α → PMF α} {δ : ℝ≥0∞} {T : ℕ}
    (hreturn : ∀ s, B s → A s → ¬ E s → ∀ U, U ≤ T →
      (∑' z, if A z then 0 else iter K U s z) ≤ δ) :
    ∀ U, U ≤ T → ∀ s,
      (∑' z, if A z then 0 else iter K U s z) ≤
        (∑' z, if A z ∧ ¬ E z then 0 else iter (freeze B K) U s z) + δ := by
  let V : α → ℝ≥0∞ := fun z => if A z then 0 else 1
  let V' : α → ℝ≥0∞ := fun z => if A z ∧ ¬ E z then 0 else 1
  have hmass (q : PMF α) :
      (∑' z, if A z then 0 else q z) = expect q V := by
    unfold expect V
    apply tsum_congr
    intro z
    by_cases hz : A z <;> simp [hz]
  have hmass' (q : PMF α) :
      (∑' z, if A z ∧ ¬ E z then 0 else q z) = expect q V' := by
    unfold expect V'
    apply tsum_congr
    intro z
    by_cases hz : A z ∧ ¬ E z <;> simp [hz]
  have hprob (q : PMF α) :
      (∑' z, if A z then 0 else q z) ≤ 1 := by
    calc
      (∑' z, if A z then 0 else q z) ≤ ∑' z, q z :=
        ENNReal.tsum_le_tsum fun z => by
          by_cases hz : A z <;> simp [hz]
      _ = 1 := PMF.tsum_coe q
  intro U
  induction U with
  | zero =>
      intro _hUT s
      rw [hmass, hmass']
      simp only [iter_zero, expect_pure]
      by_cases hsA : A s
      · by_cases hsE : E s
        · simp [V, V', hsA, hsE]
        · simp [V, V', hsA, hsE]
      · simp [V, V', hsA]
  | succ U ih =>
      intro hUT s
      rw [hmass, hmass']
      by_cases hsB : B s
      · rw [iter_freeze_of_mem s hsB (U + 1), expect_pure]
        by_cases hsA : A s
        · by_cases hsE : E s
          · calc
              expect (iter K (U + 1) s) V =
                  ∑' z, (if A z then 0 else iter K (U + 1) s z) :=
                (hmass _).symm
              _ ≤ 1 := hprob _
              _ ≤ V' s + δ := by simp [V', hsA, hsE]
          · have hr := hreturn s hsB hsA hsE (U + 1) hUT
            rw [hmass] at hr
            calc
              expect (iter K (U + 1) s) V ≤ δ := hr
              _ ≤ V' s + δ := le_add_self
        · calc
            expect (iter K (U + 1) s) V =
                ∑' z, (if A z then 0 else iter K (U + 1) s z) :=
              (hmass _).symm
            _ ≤ 1 := hprob _
            _ ≤ V' s + δ := by simp [V', hsA]
      · rw [iter_succ, iter_succ, freeze_of_not_mem s hsB,
          expect_bind, expect_bind]
        calc
          expect (K s) (fun a => expect (iter K U a) V) ≤
              expect (K s) (fun a =>
                expect (iter (freeze B K) U a) V' + δ) := by
            have ihV (a : α) :
                expect (iter K U a) V ≤
                  expect (iter (freeze B K) U a) V' + δ := by
              rw [← hmass, ← hmass']
              exact ih (by omega) a
            unfold expect
            exact ENNReal.tsum_le_tsum fun a =>
              mul_le_mul_left' (ihV a) _
          _ = expect (K s) (fun a =>
                expect (iter (freeze B K) U a) V') + δ := by
            unfold expect
            simp_rw [mul_add]
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe,
              one_mul]

/-! ## The co-level exponential supermartingale -/

/-- The co-level potential on the oriented ledger. -/
noncomputable def singleCoV (lam : ℝ≥0∞) {n : ℕ} (q : SingleLedger n) :
    ℝ≥0∞ :=
  lam ^ q.cfg.1.doubleCoLevel

/-- The co-level return freeze set: the physical doubled co-level has
reached `B`. -/
def SingleCoHigh (B : ℕ) {n : ℕ} (q : SingleLedger n) : Prop :=
  B ≤ q.cfg.1.doubleCoLevel

instance (B n : ℕ) : DecidablePred (SingleCoHigh B (n := n)) := fun _ =>
  inferInstanceAs (Decidable (_ ≤ _))

/-- Scalar core of the co-level step bound: three masses summing to one,
with the up-mass dominated by the down-mass and by `pB`. -/
theorem singleCo_three_mass_core
    (down stay up pB ε : ℝ≥0∞)
    (hsum : down + stay + up = 1)
    (hud : up ≤ down) (hupB : up ≤ pB) (hε1 : ε ≤ 1) :
    down + stay * (1 + ε) + up * (1 + ε) ^ 2 ≤
      (1 + ε) * (1 + ε ^ 2 * pB) := by
  have hexpand :
      down + stay * (1 + ε) + up * (1 + ε) ^ 2 =
        (down + stay + up) + ε * (stay + 2 * up) + ε ^ 2 * up := by
    ring
  have hstay2up : stay + 2 * up ≤ 1 := by
    calc
      stay + 2 * up = stay + up + up := by ring
      _ ≤ stay + up + down := add_le_add le_rfl hud
      _ = down + stay + up := by ring
      _ = 1 := hsum
  have hrhs :
      (1 + ε) * (1 + ε ^ 2 * pB) =
        1 + ε + (ε ^ 2 * pB + ε * (ε ^ 2 * pB)) := by
    ring
  rw [hexpand, hsum, hrhs]
  have h1 : ε * (stay + 2 * up) ≤ ε := by
    calc
      ε * (stay + 2 * up) ≤ ε * 1 := mul_le_mul_left' hstay2up ε
      _ = ε := mul_one ε
  have h2 : ε ^ 2 * up ≤ ε ^ 2 * pB + ε * (ε ^ 2 * pB) :=
    le_add_right (mul_le_mul_left' hupB _)
  calc
    1 + ε * (stay + 2 * up) + ε ^ 2 * up ≤
        1 + ε + ε ^ 2 * up := by
      exact add_le_add (add_le_add le_rfl h1) le_rfl
    _ ≤ 1 + ε + (ε ^ 2 * pB + ε * (ε ^ 2 * pB)) :=
      add_le_add le_rfl h2

/-- One-step bound for the co-level potential below the freeze boundary. -/
theorem singleCoStep_super
    (n : ℕ) (hn : 2 ≤ n) (B : ℕ) (hB : B ≤ n)
    (ε : ℝ≥0∞) (hε1 : ε ≤ 1)
    (q : SingleLedger n) :
    expect (freeze (SingleCoHigh B) (singleLedgerStep n hn) q)
        (singleCoV (1 + ε)) ≤
      (1 + ε ^ 2 * ((B : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) *
        singleCoV (1 + ε) q := by
  set lam : ℝ≥0∞ := 1 + ε with hlamdef
  set pB : ℝ≥0∞ := (B : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞) with hpBdef
  have hone : (1 : ℝ≥0∞) ≤ 1 + ε ^ 2 * pB := le_add_right le_rfl
  have hlam1 : (1 : ℝ≥0∞) ≤ lam := le_add_right le_rfl
  by_cases hfr : SingleCoHigh B q
  · rw [freeze_of_mem q hfr, expect_pure]
    calc
      singleCoV lam q = 1 * singleCoV lam q := (one_mul _).symm
      _ ≤ (1 + ε ^ 2 * pB) * singleCoV lam q :=
        mul_le_mul_right' hone _
  · rw [freeze_of_not_mem q hfr]
    have hco : q.cfg.1.doubleCoLevel + 1 ≤ B := by
      unfold SingleCoHigh at hfr
      omega
    obtain ⟨⟨⟨x, y, b⟩, hinv⟩, cx, cy, rx, ry⟩ := q
    have hpop : x + y + b = n := hinv
    simp only [BiCfg.doubleCoLevel] at hco
    have hyx : y ≤ x := by omega
    have h2 : 2 ≤ x + y + b := by omega
    set q₀ : SingleLedger n :=
      ⟨⟨⟨x, y, b⟩, hinv⟩, cx, cy, rx, ry⟩ with hq₀def
    set c : ℕ := 2 * y + b with hcdef
    have hVq : singleCoV lam q₀ = lam ^ c := rfl
    -- expectation over the seven events
    rw [expect_singleLedgerStep n hn q₀ (singleCoV lam)]
    set pmf : SingleComp → ℝ≥0∞ := fun k =>
      singleCompPMF x y b h2 k with hpmfdef
    have hpmfeq : ∀ k,
        singleCompPMF q₀.cfg.1.x q₀.cfg.1.y q₀.cfg.1.b (by
          have h := q₀.cfg.2
          simp only [BiCfg.DoubleInv] at h
          omega) k = pmf k := by
      intro k
      rfl
    -- pointwise bounds on the seven terms
    have hxx : pmf .xx * singleCoV lam (SingleComp.nextSingleLedger q₀ .xx) ≤
        pmf .xx * lam ^ c := by
      by_cases hw : SingleComp.weight x y b .xx = 0
      · simp only [hpmfdef]
        rw [singleCompPMF_zero_of_weight_zero hw]
        simp
      · unfold SingleComp.nextSingleLedger
        rw [dif_neg hw]
        unfold singleCoV
        simp only [SingleComp.next, BiCfg.doubleCoLevel]
        exact le_rfl
    have hyy : pmf .yy * singleCoV lam (SingleComp.nextSingleLedger q₀ .yy) ≤
        pmf .yy * lam ^ c := by
      by_cases hw : SingleComp.weight x y b .yy = 0
      · simp only [hpmfdef]
        rw [singleCompPMF_zero_of_weight_zero hw]
        simp
      · unfold SingleComp.nextSingleLedger
        rw [dif_neg hw]
        unfold singleCoV
        simp only [SingleComp.next, BiCfg.doubleCoLevel]
        exact le_rfl
    have hbb : pmf .bb * singleCoV lam (SingleComp.nextSingleLedger q₀ .bb) ≤
        pmf .bb * lam ^ c := by
      by_cases hw : SingleComp.weight x y b .bb = 0
      · simp only [hpmfdef]
        rw [singleCompPMF_zero_of_weight_zero hw]
        simp
      · unfold SingleComp.nextSingleLedger
        rw [dif_neg hw]
        unfold singleCoV
        simp only [SingleComp.next, BiCfg.doubleCoLevel]
        exact le_rfl
    have hX : pmf .xyToX *
        singleCoV lam (SingleComp.nextSingleLedger q₀ .xyToX) ≤
        pmf .xyToX * lam ^ (c - 1) := by
      by_cases hw : SingleComp.weight x y b .xyToX = 0
      · simp only [hpmfdef]
        rw [singleCompPMF_zero_of_weight_zero hw]
        simp
      · unfold SingleComp.nextSingleLedger
        rw [dif_neg hw]
        unfold singleCoV
        simp only [SingleComp.next, BiCfg.doubleCoLevel]
        simp only [SingleComp.weight] at hw
        rcases Nat.mul_ne_zero_iff.mp hw with ⟨hx0, hy0⟩
        have hy1 : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hy0
        have hcoeq : 2 * (y - 1) + (b + 1) = c - 1 := by omega
        rw [hcoeq]
    have hxb : pmf .xb *
        singleCoV lam (SingleComp.nextSingleLedger q₀ .xb) ≤
        pmf .xb * lam ^ (c - 1) := by
      by_cases hw : SingleComp.weight x y b .xb = 0
      · simp only [hpmfdef]
        rw [singleCompPMF_zero_of_weight_zero hw]
        simp
      · unfold SingleComp.nextSingleLedger
        rw [dif_neg hw]
        unfold singleCoV
        simp only [SingleComp.next, BiCfg.doubleCoLevel]
        simp only [SingleComp.weight] at hw
        rcases Nat.mul_ne_zero_iff.mp hw with ⟨_h2x, hb0⟩
        have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb0
        have hcoeq : 2 * y + (b - 1) = c - 1 := by omega
        rw [hcoeq]
    have hY : pmf .xyToY *
        singleCoV lam (SingleComp.nextSingleLedger q₀ .xyToY) ≤
        pmf .xyToY * lam ^ (c + 1) := by
      by_cases hw : SingleComp.weight x y b .xyToY = 0
      · simp only [hpmfdef]
        rw [singleCompPMF_zero_of_weight_zero hw]
        simp
      · unfold SingleComp.nextSingleLedger
        rw [dif_neg hw]
        unfold singleCoV
        simp only [SingleComp.next, BiCfg.doubleCoLevel]
        have hcoeq : 2 * y + (b + 1) = c + 1 := by omega
        rw [hcoeq]
    have hyb : pmf .yb *
        singleCoV lam (SingleComp.nextSingleLedger q₀ .yb) ≤
        pmf .yb * lam ^ (c + 1) := by
      by_cases hw : SingleComp.weight x y b .yb = 0
      · simp only [hpmfdef]
        rw [singleCompPMF_zero_of_weight_zero hw]
        simp
      · unfold SingleComp.nextSingleLedger
        rw [dif_neg hw]
        unfold singleCoV
        simp only [SingleComp.next, BiCfg.doubleCoLevel]
        simp only [SingleComp.weight] at hw
        rcases Nat.mul_ne_zero_iff.mp hw with ⟨_h2y, hb0⟩
        have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb0
        have hcoeq : 2 * (y + 1) + (b - 1) = c + 1 := by omega
        rw [hcoeq]
    -- grouped masses
    set down : ℝ≥0∞ := pmf .xyToX + pmf .xb with hdowndef
    set stay : ℝ≥0∞ := pmf .xx + pmf .yy + pmf .bb with hstaydef
    set up : ℝ≥0∞ := pmf .xyToY + pmf .yb with hupdef
    have hsum : down + stay + up = 1 := by
      have h7 := singleCompPMF_sum_seven x y b h2
      simp only [hdowndef, hstaydef, hupdef, hpmfdef]
      calc
        singleCompPMF x y b h2 .xyToX + singleCompPMF x y b h2 .xb +
              (singleCompPMF x y b h2 .xx + singleCompPMF x y b h2 .yy +
                singleCompPMF x y b h2 .bb) +
              (singleCompPMF x y b h2 .xyToY + singleCompPMF x y b h2 .yb)
            = singleCompPMF x y b h2 .xx + singleCompPMF x y b h2 .xyToX +
                singleCompPMF x y b h2 .xyToY + singleCompPMF x y b h2 .yy +
                singleCompPMF x y b h2 .xb + singleCompPMF x y b h2 .yb +
                singleCompPMF x y b h2 .bb := by ring
        _ = 1 := h7
    have hpair : pmf .xyToY = pmf .xyToX := by
      simp only [hpmfdef]
      rfl
    have hybxb : pmf .yb ≤ pmf .xb := by
      simp only [hpmfdef]
      rw [singleCompPMF_apply, singleCompPMF_apply]
      apply ENNReal.div_le_div_right
      have hwle : 2 * y * b ≤ 2 * x * b := by
        exact Nat.mul_le_mul_right b (Nat.mul_le_mul_left 2 hyx)
      exact_mod_cast hwle
    have hud : up ≤ down := by
      rw [hupdef, hdowndef, hpair]
      exact add_le_add le_rfl hybxb
    have hupB : up ≤ pB := by
      have hupeq : up =
          ((x * y + 2 * y * b : ℕ) : ℝ≥0∞) /
            ((2 * Nat.choose (x + y + b) 2 : ℕ) : ℝ≥0∞) := by
        simp only [hupdef, hpmfdef]
        rw [singleCompPMF_apply, singleCompPMF_apply,
          ENNReal.div_add_div_same]
        simp only [SingleComp.weight]
        rw [show ((x * y : ℕ) : ℝ≥0∞) + ((2 * y * b : ℕ) : ℝ≥0∞)
            = ((x * y + 2 * y * b : ℕ) : ℝ≥0∞) by push_cast; ring]
        congr 1
        push_cast
        ring
      rw [hupeq, hpop]
      have hnum : x * y + 2 * y * b ≤ B * n := by
        have hxb2 : x + 2 * b ≤ 2 * n := by omega
        have h2y : 2 * y ≤ B - 1 := by omega
        calc
          x * y + 2 * y * b = y * (x + 2 * b) := by ring
          _ ≤ y * (2 * n) := Nat.mul_le_mul_left y hxb2
          _ = 2 * y * n := by ring
          _ ≤ B * n := Nat.mul_le_mul_right n (by omega)
      have hden : 2 * Nat.choose n 2 = n * (n - 1) := two_mul_choose_two n
      calc
        ((x * y + 2 * y * b : ℕ) : ℝ≥0∞) /
              ((2 * Nat.choose n 2 : ℕ) : ℝ≥0∞)
            ≤ ((B * n : ℕ) : ℝ≥0∞) /
              ((2 * Nat.choose n 2 : ℕ) : ℝ≥0∞) :=
          ENNReal.div_le_div_right (by exact_mod_cast hnum) _
        _ = ((n * B : ℕ) : ℝ≥0∞) / ((n * (n - 1) : ℕ) : ℝ≥0∞) := by
          rw [hden, Nat.mul_comm B n]
        _ = pB := by
          rw [hpBdef, Nat.cast_mul, Nat.cast_mul]
          rw [ENNReal.mul_div_mul_left _ _
            (by
              simp only [ne_eq, Nat.cast_eq_zero]
              omega)
            (ENNReal.natCast_ne_top n)]
    -- assemble
    have hsplit :
        (∑ k : SingleComp, pmf k *
          singleCoV lam (SingleComp.nextSingleLedger q₀ k)) ≤
        down * lam ^ (c - 1) + stay * lam ^ c + up * lam ^ (c + 1) := by
      simp only [hdowndef, hstaydef, hupdef]
      rw [show (Finset.univ : Finset SingleComp) =
        {SingleComp.xx, SingleComp.xyToX, SingleComp.xyToY,
          SingleComp.yy, SingleComp.xb, SingleComp.yb,
          SingleComp.bb} from rfl]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
      refine le_trans
        (add_le_add hxx (add_le_add hX (add_le_add hY (add_le_add hyy
          (add_le_add hxb (add_le_add hyb hbb)))))) (le_of_eq ?_)
      ring
    refine le_trans hsplit ?_
    -- scalar step
    by_cases hc0 : c = 0
    · -- consensus-like corner: no down or up mass
      have hyzero : y = 0 := by omega
      have hbzero : b = 0 := by omega
      have hdown0 : down = 0 := by
        simp only [hdowndef, hpmfdef]
        rw [singleCompPMF_zero_of_weight_zero (by
            simp [SingleComp.weight, hyzero]),
          singleCompPMF_zero_of_weight_zero (by
            simp [SingleComp.weight, hbzero])]
        simp
      have hup0 : up = 0 := by
        simp only [hupdef, hpmfdef]
        rw [singleCompPMF_zero_of_weight_zero (by
            simp [SingleComp.weight, hyzero]),
          singleCompPMF_zero_of_weight_zero (by
            simp [SingleComp.weight, hyzero])]
        simp
      have hstay1 : stay = 1 := by
        have hs' := hsum
        rw [hdown0, hup0] at hs'
        simpa using hs'
      rw [hVq, hc0, hdown0, hup0, hstay1]
      simp only [pow_zero, mul_one, one_mul, zero_mul, add_zero, zero_add]
      exact hone
    · have hcore := singleCo_three_mass_core down stay up pB ε hsum hud hupB hε1
      have hpowc : lam ^ c = lam ^ (c - 1) * lam := by
        rw [← pow_succ]
        congr 1
        omega
      have hpowc1 : lam ^ (c + 1) = lam ^ (c - 1) * lam ^ 2 := by
        rw [← pow_add]
        congr 1
        omega
      have hfac : down * lam ^ (c - 1) + stay * lam ^ c +
          up * lam ^ (c + 1) =
          lam ^ (c - 1) * (down + stay * lam + up * lam ^ 2) := by
        rw [hpowc, hpowc1]
        ring
      rw [hVq, hfac]
      calc
        lam ^ (c - 1) * (down + stay * lam + up * lam ^ 2)
            ≤ lam ^ (c - 1) * (lam * (1 + ε ^ 2 * pB)) := by
          apply mul_le_mul_left'
          rw [hlamdef]
          exact hcore
        _ = (1 + ε ^ 2 * pB) * lam ^ c := by
          rw [hpowc]
          ring

/-! ## The horizon-bounded return bound -/

/-- Failure of a physical level target within a bounded horizon, from a
state comfortably above the target.  `B = 2n - Lexit + 1` is the failure
boundary on the co-level; the start is `sret+1` co-units above it. -/
theorem singleCo_return_raw
    (n : ℕ) (hn : 2 ≤ n) (Lexit sret T U B : ℕ)
    (hUT : U ≤ T) (hLn : n + 1 ≤ Lexit)
    (hBdef : Lexit + B = 2 * n + 1)
    (ε : ℝ≥0∞) (hε1 : ε ≤ 1)
    (s : SingleState n) (hs : Lexit + sret ≤ s.1.doubleLevel) :
    (∑' z : SingleState n, if Lexit ≤ z.1.doubleLevel then 0
        else iter (singleStateStep n hn) U s z) ≤
      (1 + ε ^ 2 * ((B : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T /
        (1 + ε) ^ (sret + 1) := by
  set lam : ℝ≥0∞ := 1 + ε with hlamdef
  set m : ℝ≥0∞ :=
    1 + ε ^ 2 * ((B : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞)) with hmdef
  have hεt : ε ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hε1
  have hlam1 : (1 : ℝ≥0∞) ≤ lam := le_add_right le_rfl
  have hlamne0 : lam ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one hlam1).ne'
  have hlamt : lam ≠ ⊤ := by
    rw [hlamdef]
    finiteness
  have hm1 : (1 : ℝ≥0∞) ≤ m := le_add_right le_rfl
  have hB : B ≤ n := by omega
  let q₀ : SingleLedger n := ⟨s, 0, 0, 0, 0⟩
  let A : SingleState n → Prop := fun z => Lexit ≤ z.1.doubleLevel
  have hAeq :
      (∑' z : SingleState n, if Lexit ≤ z.1.doubleLevel then 0
          else iter (singleStateStep n hn) U s z) =
        ∑' q : SingleLedger n, if A q.cfg then 0
          else iter (singleLedgerStep n hn) U q₀ q := by
    exact singleState_failure_eq_ledger n hn U q₀ A
  have hdisj : ∀ q : SingleLedger n, A q.cfg → ¬ SingleCoHigh B q := by
    intro q hq hhigh
    unfold SingleCoHigh at hhigh
    have hadd := doubleLevel_add_doubleCoLevel q.cfg
    change Lexit ≤ q.cfg.1.doubleLevel at hq
    omega
  have hfreeze :=
    failure_le_failure_freeze
      (B := SingleCoHigh B (n := n))
      (A := fun q : SingleLedger n => A q.cfg)
      (K := singleLedgerStep n hn) hdisj U q₀
  -- Markov on the frozen chain
  set Kf : SingleLedger n → PMF (SingleLedger n) :=
    freeze (SingleCoHigh B) (singleLedgerStep n hn) with hKf
  have hstep : ∀ q : SingleLedger n,
      expect (Kf q) (singleCoV lam) ≤ m * singleCoV lam q := by
    intro q
    exact singleCoStep_super n hn B hB ε hε1 q
  have hiter := expect_iter_le Kf (singleCoV lam) m hstep U q₀
  have hbadmass :
      (∑' q : SingleLedger n, if A q.cfg then 0
          else iter Kf U q₀ q) ≤
        (∑' q : SingleLedger n, if SingleCoHigh B q then
          iter Kf U q₀ q else 0) := by
    refine ENNReal.tsum_le_tsum fun q => ?_
    by_cases hq : A q.cfg
    · simp [hq]
    · have hqco : SingleCoHigh B q := by
        unfold SingleCoHigh
        have hadd := doubleLevel_add_doubleCoLevel q.cfg
        change ¬ Lexit ≤ q.cfg.1.doubleLevel at hq
        omega
      simp [hq, hqco]
  have hθ0 : (lam ^ B : ℝ≥0∞) ≠ 0 := pow_ne_zero _ hlamne0
  have hθt : (lam ^ B : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top hlamt
  have hmarkov :=
    bad_mass_le_expect_div (iter Kf U q₀) (singleCoV lam)
      (SingleCoHigh B) (lam ^ B) hθ0 hθt
      (by
        intro q hq
        unfold SingleCoHigh at hq
        unfold singleCoV
        exact pow_le_pow_right₀ hlam1 hq)
  have hV0 : singleCoV lam q₀ = lam ^ s.1.doubleCoLevel := rfl
  have hcoStart : s.1.doubleCoLevel + (sret + 1) ≤ B := by
    have hadd := doubleLevel_add_doubleCoLevel s
    omega
  have hfinal :
      m ^ U * singleCoV lam q₀ / lam ^ B ≤
        m ^ T / lam ^ (sret + 1) := by
    have hnum : m ^ U * singleCoV lam q₀ ≤
        m ^ T * lam ^ s.1.doubleCoLevel := by
      rw [hV0]
      exact mul_le_mul_right' (pow_le_pow_right₀ hm1 hUT) _
    have hden : lam ^ s.1.doubleCoLevel * lam ^ (sret + 1) ≤ lam ^ B := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hlam1 hcoStart
    calc
      m ^ U * singleCoV lam q₀ / lam ^ B
          ≤ m ^ T * lam ^ s.1.doubleCoLevel / lam ^ B :=
        ENNReal.div_le_div_right hnum _
      _ ≤ m ^ T * lam ^ s.1.doubleCoLevel /
            (lam ^ s.1.doubleCoLevel * lam ^ (sret + 1)) :=
        ENNReal.div_le_div_left hden _
      _ = lam ^ s.1.doubleCoLevel * m ^ T /
            (lam ^ s.1.doubleCoLevel * lam ^ (sret + 1)) := by
        rw [mul_comm (m ^ T)]
      _ = m ^ T / lam ^ (sret + 1) := by
        rw [ENNReal.mul_div_mul_left _ _
          (pow_ne_zero _ hlamne0) (ENNReal.pow_ne_top hlamt)]
  calc
    (∑' z : SingleState n, if Lexit ≤ z.1.doubleLevel then 0
        else iter (singleStateStep n hn) U s z)
        = ∑' q : SingleLedger n, if A q.cfg then 0
            else iter (singleLedgerStep n hn) U q₀ q := hAeq
    _ ≤ ∑' q : SingleLedger n, if A q.cfg then 0
          else iter Kf U q₀ q := hfreeze
    _ ≤ ∑' q : SingleLedger n, if SingleCoHigh B q then
          iter Kf U q₀ q else 0 := hbadmass
    _ ≤ expect (iter Kf U q₀) (singleCoV lam) / lam ^ B := hmarkov
    _ ≤ m ^ U * singleCoV lam q₀ / lam ^ B :=
      ENNReal.div_le_div_right hiter _
    _ ≤ m ^ T / lam ^ (sret + 1) := hfinal

/-! ## Scalar conversion of the return bound -/

/-- Real-exponential form of the co-level return bound. -/
theorem singleCoReturn_exp
    (n T sret B : ℕ) (hn : 2 ≤ n) (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    (1 + (ENNReal.ofReal e) ^ 2 *
          ((B : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T /
        (1 + ENNReal.ofReal e) ^ (sret + 1) ≤
      ENNReal.ofReal
        (Real.exp ((T : ℝ) * (e ^ 2 * (B : ℝ) / ((n - 1 : ℕ) : ℝ)) -
          ((sret + 1 : ℕ) : ℝ) * e / 2)) := by
  have hden0 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    have : 1 ≤ n - 1 := by omega
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  set x : ℝ := e ^ 2 * (B : ℝ) / ((n - 1 : ℕ) : ℝ) with hxdef
  have hx0 : 0 ≤ x := by
    rw [hxdef]
    positivity
  have hnum :
      (1 + (ENNReal.ofReal e) ^ 2 *
          ((B : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞))) ^ T =
        ENNReal.ofReal ((1 + x) ^ T) := by
    have hfrac : (B : ℝ≥0∞) / ((n - 1 : ℕ) : ℝ≥0∞) =
        ENNReal.ofReal ((B : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
      rw [ENNReal.ofReal_div_of_pos hden0]
      rw [ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    rw [hfrac, ← ENNReal.ofReal_pow he0, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by positivity),
      ← ENNReal.ofReal_pow (by positivity)]
    congr 2
    rw [hxdef]
    ring
  have hdenom :
      (1 + ENNReal.ofReal e) ^ (sret + 1) =
        ENNReal.ofReal ((1 + e) ^ (sret + 1)) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) he0,
      ← ENNReal.ofReal_pow (by positivity)]
  rw [hnum, hdenom]
  have hpos : (0 : ℝ) < (1 + e) ^ (sret + 1) := by positivity
  rw [← ENNReal.ofReal_div_of_pos hpos]
  apply ENNReal.ofReal_le_ofReal
  have hup : (1 + x) ^ T ≤ Real.exp ((T : ℝ) * x) := by
    calc
      (1 + x) ^ T ≤ (Real.exp x) ^ T := by
        apply pow_le_pow_left₀ (by positivity)
        have := Real.add_one_le_exp x
        linarith
      _ = Real.exp ((T : ℝ) * x) := by
        rw [← Real.exp_nat_mul]
  have hlow : Real.exp (((sret + 1 : ℕ) : ℝ) * e / 2) ≤ (1 + e) ^ (sret + 1) := by
    have hlog : e / 2 ≤ Real.log (1 + e) := by
      have h1e : (0 : ℝ) < 1 + e := by linarith
      have hinv := Real.log_le_sub_one_of_pos (x := (1 + e)⁻¹)
        (by positivity)
      rw [Real.log_inv] at hinv
      have hlogge : e / (1 + e) ≤ Real.log (1 + e) := by
        have hfld : (1 + e)⁻¹ - 1 = -(e / (1 + e)) := by
          field_simp
          ring
        rw [hfld] at hinv
        linarith
      have hhalf : e / 2 ≤ e / (1 + e) := by
        apply div_le_div_of_nonneg_left he0 (by linarith) (by linarith)
      linarith
    calc
      Real.exp (((sret + 1 : ℕ) : ℝ) * e / 2) =
          (Real.exp (e / 2)) ^ (sret + 1) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ (1 + e) ^ (sret + 1) := by
        apply pow_le_pow_left₀ (by positivity)
        calc
          Real.exp (e / 2) ≤ Real.exp (Real.log (1 + e)) :=
            Real.exp_le_exp.mpr hlog
          _ = 1 + e := Real.exp_log (by linarith)
  calc
    (1 + x) ^ T / (1 + e) ^ (sret + 1)
        ≤ Real.exp ((T : ℝ) * x) /
            Real.exp (((sret + 1 : ℕ) : ℝ) * e / 2) := by
      apply div_le_div₀ (Real.exp_pos _).le hup (Real.exp_pos _) hlow
    _ = Real.exp ((T : ℝ) * x - ((sret + 1 : ℕ) : ℝ) * e / 2) := by
      rw [← Real.exp_sub]

/-! ## Physical-chain mass equalities -/

/-- The physical Single-B chain iterate is the pushforward of the invariant
state-chain iterate. -/
theorem iter_singleBChain_eq_map {n : ℕ} (hn : 2 ≤ n) (T : ℕ)
    (s : SingleState n) :
    iter singleBChain T s.1 =
      (iter (singleStateStep n hn) T s).map Subtype.val :=
  iter_map_equivariant (singleStateStep n hn) singleBChain Subtype.val
    (singleStateStep_map_val n hn) T s

/-- Single-B non-consensus mass is unchanged by passing to the invariant
state chain. -/
theorem singleState_nonconsensus_mass_eq
    (n : ℕ) (hn : 2 ≤ n) (T : ℕ) (s : SingleState n) :
    (∑' z : SingleState n,
        if BiXConsensus n z.1 then 0
        else iter (singleStateStep n hn) T s z) =
      ∑' z : BiCfg,
        if BiXConsensus n z then 0
        else iter singleBChain T s.1 z := by
  rw [masked_eq_expect (fun z : SingleState n => BiXConsensus n z.1),
    masked_eq_expect (BiXConsensus n),
    iter_singleBChain_eq_map hn T s, expect_map]

end Tri

#print axioms Tri.failure_le_failure_freeze_add_exc
#print axioms Tri.singleCoStep_super
#print axioms Tri.singleCo_return_raw
#print axioms Tri.singleCoReturn_exp
#print axioms Tri.singleState_nonconsensus_mass_eq
