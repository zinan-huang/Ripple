/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantinePhase1Rung
import Tri.PaperLemma6

/-!
# Stochastic order for Byzantine phase I

The productive two-point law is monotone in the effective firing rate.  These
lemmas transfer that order to the paper's worst-case phase-I kernel while
keeping the population interval conditions as additive witnesses.
-/

namespace Tri.Byzantine

open scoped ENNReal NNReal

noncomputable section

variable {n B z : ℕ}

/-- For a fixed down weight `d`, the conditional up probability
`u / (d + u)` is monotone in the raw up weight. -/
private theorem ennreal_up_ratio_mono
    {d u v : ℝ≥0∞}
    (huv : u ≤ v)
    (hdu0 : d + u ≠ 0)
    (hduTop : d + u ≠ ⊤)
    (hdv0 : d + v ≠ 0)
    (hdvTop : d + v ≠ ⊤) :
    u / (d + u) ≤ v / (d + v) := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl hdv0) (Or.inl hdvTop)]
  rw [show
      u / (d + u) * (d + v) =
        (u * (d + v)) / (d + u) by
    simp only [div_eq_mul_inv]
    ring]
  rw [ENNReal.div_le_iff_le_mul (Or.inl hdu0) (Or.inl hduTop)]
  calc
    u * (d + v) = u * d + u * v := by ring
    _ ≤ v * d + u * v := by
      gcongr
    _ = v * (d + u) := by ring

/-- Two probability laws on the same ordered support `{lo, hi}` are ordered
whenever the second has at least as much mass on `hi`. -/
private theorem two_point_expect_le_of_up_le
    {d₀ u₀ d₁ u₁ vlo vhi : ℝ≥0∞}
    (hsum₀ : d₀ + u₀ = 1)
    (hsum₁ : d₁ + u₁ = 1)
    (hup : u₀ ≤ u₁)
    (hval : vlo ≤ vhi) :
    d₀ * vlo + u₀ * vhi ≤
      d₁ * vlo + u₁ * vhi := by
  let e : ℝ≥0∞ := u₁ - u₀
  have huadd : u₀ + e = u₁ :=
    add_tsub_cancel_of_le hup
  have hu₀one : u₀ ≤ 1 := by
    rw [← hsum₀]
    exact le_add_left le_rfl
  have hu₀top : u₀ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hu₀one
  have hbalance : (d₁ + e) + u₀ = d₀ + u₀ := by
    calc
      (d₁ + e) + u₀ = d₁ + (u₀ + e) := by ring
      _ = d₁ + u₁ := by rw [huadd]
      _ = 1 := hsum₁
      _ = d₀ + u₀ := hsum₀.symm
  have hd : d₁ + e = d₀ := by
    -- `hbalance` is stated with `u₀` on the right; cancel it after commuting.
    have hbalance' : u₀ + (d₁ + e) = u₀ + d₀ := by
      rw [add_comm u₀ (d₁ + e), add_comm u₀ d₀]; exact hbalance
    exact (ENNReal.add_right_inj hu₀top).mp hbalance'
  calc
    d₀ * vlo + u₀ * vhi =
        (d₁ + e) * vlo + u₀ * vhi := by rw [hd]
    _ = d₁ * vlo + e * vlo + u₀ * vhi := by ring
    _ ≤ d₁ * vlo + e * vhi + u₀ * vhi := by
      gcongr
    _ = d₁ * vlo + (e + u₀) * vhi := by ring
    _ = d₁ * vlo + u₁ * vhi := by
      rw [add_comm e u₀, huadd]

/-- The conditioned productive two-point law is monotone in the firing rate.
This is the reusable stochastic-order core. -/
theorem relaxedProductiveTriInterior_expect_mono_fire
    (r₀ r₁ : RelaxedRate)
    (a b : ℕ)
    (h : 3 ≤ (a + 1) + (b + 1))
    (hfire : r₀.fire ≤ r₁.fire)
    (hprod₀ :
      relaxedTriStep r₀ (a + 1) (b + 1) h a +
          relaxedTriStep r₀ (a + 1) (b + 1) h (a + 2) ≠ 0)
    (hprod₁ :
      relaxedTriStep r₁ (a + 1) (b + 1) h a +
          relaxedTriStep r₁ (a + 1) (b + 1) h (a + 2) ≠ 0)
    (f : ℕ → ℝ≥0∞)
    (hf : Monotone f) :
    expect (relaxedProductiveTriInterior r₀ a b h hprod₀) f ≤
      expect (relaxedProductiveTriInterior r₁ a b h hprod₁) f := by
  let d₀ : ℝ≥0∞ :=
    relaxedTriStep r₀ (a + 1) (b + 1) h a
  let u₀ : ℝ≥0∞ :=
    relaxedTriStep r₀ (a + 1) (b + 1) h (a + 2)
  let d₁ : ℝ≥0∞ :=
    relaxedTriStep r₁ (a + 1) (b + 1) h a
  let u₁ : ℝ≥0∞ :=
    relaxedTriStep r₁ (a + 1) (b + 1) h (a + 2)

  have hfireE : (r₀.fire : ℝ≥0∞) ≤ (r₁.fire : ℝ≥0∞) := by
    exact_mod_cast hfire

  have hdown : d₀ = d₁ := by
    dsimp only [d₀, d₁]
    rw [relaxedTriStep_down, relaxedTriStep_down]

  have hupRaw : u₀ ≤ u₁ := by
    dsimp only [u₀, u₁]
    rw [relaxedTriStep_up, relaxedTriStep_up]
    -- `mul_le_mul_right` puts the rate on the right; the goal has it on the left.
    have hmul :
        (r₀.fire : ℝ≥0∞) * ((Nat.choose (a + 1) 2 * (b + 1) : ℕ) : ℝ≥0∞) ≤
          (r₁.fire : ℝ≥0∞) * ((Nat.choose (a + 1) 2 * (b + 1) : ℕ) : ℝ≥0∞) := by
      exact mul_le_mul_right' hfireE _
    exact ENNReal.div_le_div_right hmul
      ((Nat.choose ((a + 1) + (b + 1)) 3 : ℕ) : ℝ≥0∞)

  have hden₀0 : d₀ + u₀ ≠ 0 := by
    simpa only [d₀, u₀] using hprod₀
  have hden₁0 : d₁ + u₁ ≠ 0 := by
    simpa only [d₁, u₁] using hprod₁
  have hden₀Top : d₀ + u₀ ≠ ⊤ := by
    dsimp only [d₀, u₀]
    exact ENNReal.add_ne_top.mpr
      ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩
  have hden₁Top : d₁ + u₁ ≠ ⊤ := by
    dsimp only [d₁, u₁]
    exact ENNReal.add_ne_top.mpr
      ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩
  have hdenV0 : d₀ + u₁ ≠ 0 := by
    rw [hdown]
    exact hden₁0
  have hdenVTop : d₀ + u₁ ≠ ⊤ := by
    rw [hdown]
    exact hden₁Top

  have hupCond₀ :
      u₀ / (d₀ + u₀) ≤ u₁ / (d₀ + u₁) :=
    ennreal_up_ratio_mono
      hupRaw hden₀0 hden₀Top hdenV0 hdenVTop
  have hupCond :
      u₀ / (d₀ + u₀) ≤ u₁ / (d₁ + u₁) := by
    calc
      u₀ / (d₀ + u₀) ≤ u₁ / (d₀ + u₁) := hupCond₀
      _ = u₁ / (d₁ + u₁) := by rw [hdown]

  have hmass₀ :
      d₀ / (d₀ + u₀) + u₀ / (d₀ + u₀) = 1 := by
    calc
      d₀ / (d₀ + u₀) + u₀ / (d₀ + u₀) =
          u₀ / (d₀ + u₀) + d₀ / (d₀ + u₀) := by ring
      _ = 1 := by
        simpa only [d₀, u₀] using
          (relaxedProductiveTriInterior_masses
            r₀ a b h hprod₀)
  have hmass₁ :
      d₁ / (d₁ + u₁) + u₁ / (d₁ + u₁) = 1 := by
    calc
      d₁ / (d₁ + u₁) + u₁ / (d₁ + u₁) =
          u₁ / (d₁ + u₁) + d₁ / (d₁ + u₁) := by ring
      _ = 1 := by
        simpa only [d₁, u₁] using
          (relaxedProductiveTriInterior_masses
            r₁ a b h hprod₁)

  rw [expect_relaxedProductiveTriInterior,
    expect_relaxedProductiveTriInterior]
  simpa only [d₀, u₀, d₁, u₁] using
    (two_point_expect_le_of_up_le
      hmass₀ hmass₁ hupCond (hf (by omega)))

/-- If two rates are compared against the same complementary idle allowance,
the rate premise used by Lemma 6 yields the required fire-rate order. -/
theorem fire_le_of_common_idle_allowance
    {r₀ r₁ : RelaxedRate} {c : NNReal}
    (hr₀ : r₀.fire + c = 1)
    (hr₁ : 1 ≤ r₁.fire + c) :
    r₀.fire ≤ r₁.fire := by
  rw [← NNReal.coe_le_coe]
  have hr₀R :
      (r₀.fire : ℝ) + (c : ℝ) = 1 := by
    exact_mod_cast hr₀
  have hr₁R :
      (1 : ℝ) ≤ (r₁.fire : ℝ) + (c : ℝ) := by
    exact_mod_cast hr₁
  linarith

/-- Phase-I band instantiation. The right-hand productive kernel is the
paper-worst Byzantine productive law because `rEff` is certified by
`IsPaperEffectiveRate rEff q.1` and the existing exact raw-step bridge.

All natural-number interval conditions are stated with additive witnesses. -/
theorem phase1_band_floor_productive_expect_le_paperWorst
    (h3 : 3 ≤ n)
    (q : Phase1Level n B z)
    (r₀ rEff : RelaxedRate)
    {Δ₀ Δ A ŷ zSlack anchorSlack lowerSlack upperSlack
      xPred mPred : ℕ}
    (hxPred : State.x q.1 = xPred + 1)
    (hmPred : State.y q.1 + State.z q.1 = mPred + 1)
    (hrate : IsPaperEffectiveRate rEff q.1)
    (hyhat : State.x q.1 + ŷ = n)
    (hbudget : 16 * State.z q.1 + zSlack = Δ₀)
    (hanchor : Δ₀ + anchorSlack = A)
    (hlower : A + lowerSlack = 2 * Δ)
    (hupper : 2 * Δ + upperSlack = n)
    (hgap : n + Δ = 2 * State.x q.1)
    (hr₀ :
      r₀.fire +
          (((A : ℕ) : NNReal) /
            (((2 * n : ℕ) : NNReal))) = 1)
    (f : ℕ → ℝ≥0∞)
    (hf : Monotone f) :
    expect
        (relaxedProductiveTriChain r₀ n (State.x q.1)) f ≤
      expect
        (relaxedProductiveTriChain rEff n (State.x q.1)) f := by
  have hn : 0 < n := by omega

  have hratePremise :
      (1 : NNReal) ≤
        rEff.fire +
          (((A : ℕ) : NNReal) /
            (((2 * n : ℕ) : NNReal))) :=
    interval_lemma6_rate_premise_witness
      (s := q.1) (Δ₀ := Δ₀) (Δ := Δ) (a := A) (ŷ := ŷ)
      (zSlack := zSlack) (anchorSlack := anchorSlack)
      (lowerSlack := lowerSlack) (upperSlack := upperSlack)
      rEff hrate hn hyhat hbudget hanchor hlower hupper hgap

  have hfire : r₀.fire ≤ rEff.fire :=
    fire_le_of_common_idle_allowance hr₀ hratePremise

  let c : NNReal :=
    ((A : ℕ) : NNReal) / (((2 * n : ℕ) : NNReal))
  have hc_lt_one : c < 1 := by
    dsimp only [c]
    rw [div_lt_one]
    · exact_mod_cast (show A < 2 * n by omega)
    · exact_mod_cast (show 0 < 2 * n by omega)
  have hfire₀pos : 0 < r₀.fire := by
    by_contra hnot
    have hzero : r₀.fire = 0 :=
      le_antisymm (not_lt.mp hnot) bot_le
    have hc_eq : c = 1 := by
      simpa only [c, hzero, zero_add] using hr₀
    exact (ne_of_lt hc_lt_one) hc_eq
  have hfireEffPos : 0 < rEff.fire :=
    hfire₀pos.trans_le hfire

  have hpop : xPred + mPred + 2 = n := by
    have htotal := State.total q.1
    omega

  have hprod₀ :
      relaxedTriStep r₀ (xPred + 1) (mPred + 1) (by omega) xPred +
          relaxedTriStep r₀ (xPred + 1) (mPred + 1) (by omega)
            (xPred + 2) ≠ 0 :=
    lemma6_live_productive_nonzero r₀ h3 hpop hfire₀pos
  have hprodEff :
      relaxedTriStep rEff (xPred + 1) (mPred + 1) (by omega) xPred +
          relaxedTriStep rEff (xPred + 1) (mPred + 1) (by omega)
            (xPred + 2) ≠ 0 :=
    lemma6_live_productive_nonzero rEff h3 hpop hfireEffPos

  have hK₀ :
      relaxedProductiveTriChain r₀ n (State.x q.1) =
        relaxedProductiveTriInterior
          r₀ xPred mPred (by omega) hprod₀ := by
    rw [hxPred]
    exact relaxedProductiveTriChain_apply r₀ hpop h3 hprod₀
  have hKEff :
      relaxedProductiveTriChain rEff n (State.x q.1) =
        relaxedProductiveTriInterior
          rEff xPred mPred (by omega) hprodEff := by
    rw [hxPred]
    exact relaxedProductiveTriChain_apply rEff hpop h3 hprodEff

  rw [hK₀, hKEff]
  exact relaxedProductiveTriInterior_expect_mono_fire
    r₀ rEff xPred mPred (by omega)
    hfire hprod₀ hprodEff f hf

end

end Tri.Byzantine
