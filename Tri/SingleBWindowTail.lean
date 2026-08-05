/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.SingleBBandKernel

/-!
# Single-B stopped-window tails

The direction tail uses the Single-B corrected potential
`singleTheta w v η`.  The key bookkeeping lemma below avoids natural
subtraction: from

`(2x+b)+CY <= thr+CX`

and `w*v=1`, it proves `w^thr * η^M <= singleTheta w v η q` whenever
`M <= RX+RY`.
-/

namespace Tri

open scoped ENNReal

/-- Corrected-level lower-tail containment for `singleTheta`, in additive form.

The proof rewrites `w^thr` as `w^(thr+cx) * v^cx` using `w*v=1`, then uses
`w <= 1` to compare exponents. -/
theorem singleTheta_lower_of_corrected_le {n thr M : ℕ}
    (w v η : ℝ≥0∞) (hwv : w * v = 1) (hw1 : w ≤ 1) (hη1 : 1 ≤ η)
    (q : SingleLedger n)
    (hΛ : q.cfg.1.doubleLevel + q.cy ≤ thr + q.cx)
    (hM : M ≤ q.rx + q.ry) :
    w ^ thr * η ^ M ≤ singleTheta w v η q := by
  unfold singleTheta
  have hwlev :
      w ^ thr ≤ w ^ (q.cfg.1.doubleLevel + q.cy) * v ^ q.cx := by
    have hpow :
        w ^ (thr + q.cx) ≤ w ^ (q.cfg.1.doubleLevel + q.cy) :=
      pow_le_pow_right_of_le_one' hw1 hΛ
    have hrewrite :
        w ^ thr = w ^ (thr + q.cx) * v ^ q.cx := by
      calc
        w ^ thr = w ^ thr * 1 := by rw [mul_one]
        _ = w ^ thr * (w * v) ^ q.cx := by rw [hwv, one_pow]
        _ = w ^ thr * (w ^ q.cx * v ^ q.cx) := by rw [mul_pow]
        _ = w ^ (thr + q.cx) * v ^ q.cx := by
            rw [pow_add]
            ring
    rw [hrewrite]
    exact mul_le_mul' hpow le_rfl
  have hη : η ^ M ≤ η ^ (q.rx + q.ry) :=
    pow_le_pow_right₀ hη1 hM
  calc
    w ^ thr * η ^ M
        ≤ (w ^ (q.cfg.1.doubleLevel + q.cy) * v ^ q.cx) *
            η ^ (q.rx + q.ry) := mul_le_mul' hwlev hη
    _ = w ^ (q.cfg.1.doubleLevel + q.cy) * v ^ q.cx *
            η ^ (q.rx + q.ry) := by ring

/-- Markov tail for a stopped Single-B corrected band.  The live hypothesis is
exactly the hypothesis consumed by `singleTheta_frozen_super`; band geometry
and gap recovery can be used upstream to produce it. -/
theorem singleBandWindow_tail {n : ℕ} (hn : 2 ≤ n)
    (aLoΛ hiΛ D H p qRat thr M T : ℕ) (hq : qRat ≠ 0)
    (w v η u : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (qRat : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hwv : w * v = 1) (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hη1 : 1 ≤ η) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤)
    (hlive : ∀ q, ¬ SingleBandFrozen n aLoΛ hiΛ D H q →
      ∃ a : ℕ, q.CorrectedLevel (a + 1) ∧
        qRat * q.cfg.1.y ≤ p * q.cfg.1.x)
    (s₀ : SingleState n) :
    ∑' q, (if q.cfg.1.doubleLevel + q.cy ≤ thr + q.cx ∧
          M ≤ q.rx + q.ry then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      ≤ w ^ s₀.1.doubleLevel / (w ^ thr * η ^ M) := by
  set θ : ℝ≥0∞ := w ^ thr * η ^ M with hθdef
  have hθ0 : θ ≠ 0 := by
    rw [hθdef]
    apply mul_ne_zero (pow_ne_zero _ hw0)
    exact pow_ne_zero _ (by
      intro hη0
      rw [hη0] at hη1
      simp at hη1)
  have hθtop : θ ≠ ⊤ := by
    rw [hθdef]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top hwt)
      (ENNReal.pow_ne_top hηt)
  have hsub : ∀ q : SingleLedger n,
      (if q.cfg.1.doubleLevel + q.cy ≤ thr + q.cx ∧
            M ≤ q.rx + q.ry then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      ≤ (if θ ≤ singleTheta w v η q then
          iter (singleBandStop n hn aLoΛ hiΛ D H) T
            (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0) := by
    intro q
    by_cases hqev : q.cfg.1.doubleLevel + q.cy ≤ thr + q.cx ∧
        M ≤ q.rx + q.ry
    · have hθle : θ ≤ singleTheta w v η q := by
        rw [hθdef]
        exact singleTheta_lower_of_corrected_le w v η hwv hw1 hη1
          q hqev.1 hqev.2
      simp [hqev, hθle]
    · simp [hqev]
  refine le_trans (ENNReal.tsum_le_tsum hsub) ?_
  refine le_trans (markov_div
    (iter (singleBandStop n hn aLoΛ hiΛ D H) T
      (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n))
    (singleTheta w v η) θ hθ0 hθtop) ?_
  have hiter := singleTheta_frozen_iter_le n hn
    (SingleBandFrozen n aLoΛ hiΛ D H) p qRat T w v η u
    hu hq hrel hwη hwv hwt hηt hlive
    (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n)
  have hΘ0 :
      singleTheta w v η (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n)
        = w ^ s₀.1.doubleLevel := by
    simp [singleTheta]
  refine ENNReal.div_le_div_right ?_ θ
  simpa [singleBandStop, hΘ0] using hiter

/-- Backslide specialization of the stopped Single-B window tail. -/
theorem singleWindow_backslide_tail {n : ℕ} (hn : 2 ≤ n)
    (aLoΛ hiΛ D H p qRat Bw T : ℕ) (hq : qRat ≠ 0)
    (w v η u : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (qRat : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hwv : w * v = 1) (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hη1 : 1 ≤ η) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤)
    (hlive : ∀ q, ¬ SingleBandFrozen n aLoΛ hiΛ D H q →
      ∃ a : ℕ, q.CorrectedLevel (a + 1) ∧
        qRat * q.cfg.1.y ≤ p * q.cfg.1.x)
    (s₀ : SingleState n)
    (hstart : s₀.1.doubleLevel = aLoΛ + Bw) :
    ∑' q, (if q.cfg.1.doubleLevel + q.cy ≤ aLoΛ + q.cx then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      ≤ w ^ Bw := by
  have hmain := singleBandWindow_tail hn aLoΛ hiΛ D H p qRat aLoΛ 0 T hq
    w v η u hu hrel hwη hwv hw1 hw0 hη1 hwt hηt hlive s₀
  simp only [pow_zero, mul_one, Nat.zero_le, and_true] at hmain
  refine le_trans hmain (le_of_eq ?_)
  rw [hstart, pow_add, div_eq_mul_inv]
  calc
    w ^ aLoΛ * w ^ Bw * (w ^ aLoΛ)⁻¹
        = w ^ Bw * (w ^ aLoΛ * (w ^ aLoΛ)⁻¹) := by ring
    _ = w ^ Bw := by
        rw [ENNReal.mul_inv_cancel (pow_ne_zero _ hw0)
          (ENNReal.pow_ne_top hwt), mul_one]

/-- Deadline specialization of the stopped Single-B window tail. -/
theorem singleWindow_deadline_tail {n : ℕ} (hn : 2 ≤ n)
    (aLoΛ hiΛ D H p qRat Lhi width quota T : ℕ) (hq : qRat ≠ 0)
    (w v η u : ℝ≥0∞)
    (hu : u = (p : ℝ≥0∞) / (qRat : ℝ≥0∞))
    (hrel : η * (u + w ^ 2) = w * (u + 1)) (hwη : w ≤ η)
    (hwv : w * v = 1) (hw1 : w ≤ 1) (hw0 : w ≠ 0)
    (hη1 : 1 ≤ η) (hwt : w ≠ ⊤) (hηt : η ≠ ⊤)
    (hlive : ∀ q, ¬ SingleBandFrozen n aLoΛ hiΛ D H q →
      ∃ a : ℕ, q.CorrectedLevel (a + 1) ∧
        qRat * q.cfg.1.y ≤ p * q.cfg.1.x)
    (s₀ : SingleState n)
    (hLhi : s₀.1.doubleLevel + width = Lhi) :
    ∑' q, (if q.cfg.1.doubleLevel + q.cy ≤ Lhi + q.cx ∧
          quota ≤ q.rx + q.ry then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      ≤ 1 / (w ^ width * η ^ quota) := by
  refine le_trans (singleBandWindow_tail hn aLoΛ hiΛ D H p qRat Lhi quota T
    hq w v η u hu hrel hwη hwv hw1 hw0 hη1 hwt hηt hlive s₀) (le_of_eq ?_)
  rw [← hLhi, pow_add, mul_assoc, div_eq_mul_inv, one_div,
    ENNReal.mul_inv (Or.inl (pow_ne_zero _ hw0))
      (Or.inl (ENNReal.pow_ne_top hwt)), ← mul_assoc,
    ENNReal.mul_inv_cancel (pow_ne_zero _ hw0) (ENNReal.pow_ne_top hwt),
    one_mul]

/-- The stopped Single-B band kernel still satisfies the mirror creation tail
on the same `CreationBadY D H` event. -/
theorem singleCreationY_stopped_tail {n : ℕ} (hn : 2 ≤ n)
    (aLoΛ hiΛ D H T : ℕ) (hH : 0 < H) (s₀ : SingleState n) :
    ∑' q, (if CreationBadY D H q then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0)
      ≤ ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ))))) := by
  let K : SingleLedger n → PMF (SingleLedger n) :=
    singleBandStop n hn aLoΛ hiΛ D H
  have hfreeze_eq :
      freeze (CreationBadY D H) K = K := by
    funext q
    unfold K singleBandStop freeze
    by_cases hbad : CreationBadY D H q
    · have hB : SingleBandFrozen n aLoΛ hiΛ D H q :=
        Or.inr (Or.inr (Or.inl hbad))
      rw [if_pos hbad, if_pos hB]
    · rw [if_neg hbad]
  have hhit :
      hitProb (CreationBadY D H) K T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n)
        =
      ∑' q, (if CreationBadY D H q then
          iter K T (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0) := by
    unfold hitProb expect ind
    rw [hfreeze_eq]
    apply tsum_congr
    intro q
    by_cases hq : CreationBadY D H q <;> simp [hq]
  have hlam : (0 : ℝ) ≤ (D : ℝ) / (H : ℝ) := by positivity
  have hville := ville_frozen K (CreationBadY D H)
    (creationG (-((D : ℝ) / (H : ℝ)))) (creationTheta ((D : ℝ) / (H : ℝ)) D H)
    (creationTheta_ne_zero ((D : ℝ) / (H : ℝ)) D H)
    (creationTheta_ne_top ((D : ℝ) / (H : ℝ)) D H)
    (creationY_contain ((D : ℝ) / (H : ℝ)) hlam D H)
    (fun q => by
      dsimp [K]
      simpa [singleBandStop] using
        creationG_freeze_step hn (-((D : ℝ) / (H : ℝ)))
          (SingleBandFrozen n aLoΛ hiΛ D H) q)
    (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n)
  rw [creationYG_fresh ((D : ℝ) / (H : ℝ)) s₀,
    one_div_creationTheta,
    creation_exponent_optimised D H hH] at hville
  calc
    (∑' q, (if CreationBadY D H q then
        iter (singleBandStop n hn aLoΛ hiΛ D H) T
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) q else 0))
        = hitProb (CreationBadY D H) K T
            (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) := by
          simpa [K] using hhit.symm
    _ ≤ ⨆ U : ℕ, hitProb (CreationBadY D H) K U
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n) :=
        le_iSup (fun U : ℕ => hitProb (CreationBadY D H) K U
          (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger n)) T
    _ ≤ ENNReal.ofReal (Real.exp (-((D : ℝ) ^ 2 / (2 * (H : ℝ))))) :=
        hville

section Inhabitation

example :
    let s₀ : SingleState 4 :=
      ⟨⟨2, 1, 1⟩, by norm_num [BiCfg.DoubleInv]⟩
    singleTheta ((1 : ℝ≥0∞) / 2) 2 1
        (⟨s₀, 0, 0, 0, 0⟩ : SingleLedger 4)
      = ((1 : ℝ≥0∞) / 2) ^ s₀.1.doubleLevel := by
  intro s₀
  simp [singleTheta]

end Inhabitation

end Tri

#print axioms Tri.singleTheta_lower_of_corrected_le
#print axioms Tri.singleBandWindow_tail
#print axioms Tri.singleWindow_backslide_tail
#print axioms Tri.singleWindow_deadline_tail
#print axioms Tri.singleCreationY_stopped_tail
