import Ripple.BoundedUniversality.BGP.SelectorReplicatorFloor
import Ripple.BoundedUniversality.BGP.SelectorReplicatorHStart
import Ripple.BoundedUniversality.BGP.SelectorReplicatorHStartStructural

/-!
# SelectorReplicatorRecovery

ODE comparison bound for winner-lambda recovery at the mid-window anchor.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set MachineInstance
open scoped Topology

/-- **ODE comparison bound** (affine lower envelope).

If `f' ≥ a + b·f` on `[s, t]` with `f(s) ≥ 0`, `a ≥ 0`, `b > 0`, then
`f(u) ≥ (a/b)·(exp(b·(u-s)) - 1)` for all `u ∈ [s, t]`.

Proof: define `G(u) = f(u)·exp(-b(u-s)) - (a/b)(1-exp(-b(u-s)))`.
Then `G' ≥ 0` (from `f' ≥ a + bf`), `G(s) = f(s) ≥ 0`,
so `G(u) ≥ 0`, giving `f(u) ≥ (a/b)(exp(b(u-s))-1)`. -/
theorem linear_ode_lower_bound
    {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 < b)
    {f : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hf_cont : ContinuousOn f (Icc s t))
    (hf_deriv : ∀ u : ℝ, u ∈ Ico s t →
      ∃ fp, HasDerivAt f fp u ∧ a + b * f u ≤ fp)
    (hf_init : 0 ≤ f s) :
    ∀ u : ℝ, u ∈ Icc s t →
      a / b * (Real.exp (b * (u - s)) - 1) ≤ f u := by
  let E : ℝ → ℝ := fun u => Real.exp (-(b * (u - s)))
  let H : ℝ → ℝ := fun u => a / b * (1 - E u)
  let G : ℝ → ℝ := fun u => f u * E u - H u
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have hE_pos : ∀ u, 0 < E u := fun u => Real.exp_pos _
  have hE_deriv : ∀ u : ℝ, HasDerivAt E (-b * E u) u := by
    intro u
    have h1 : HasDerivAt (fun r => -(b * (r - s))) (-b) u := by
      simpa using ((hasDerivAt_id u).sub_const s).const_mul (-b)
    convert h1.exp using 1
    dsimp [E]; ring
  have hH_deriv : ∀ u : ℝ, HasDerivAt H (a * E u) u := by
    intro u
    convert ((hasDerivAt_const u (1 : ℝ)).sub (hE_deriv u)).const_mul (a / b) using 1
    dsimp [H, E]; field_simp; ring
  have hE_cont : Continuous E := by dsimp [E]; fun_prop
  have hG_cont : ContinuousOn G (Icc s t) := by
    dsimp only [G, H]
    exact (hf_cont.mul hE_cont.continuousOn).sub
      (((continuous_const.mul (continuous_const.sub hE_cont))).continuousOn)
  have hG_mono : MonotoneOn G (Icc s t) :=
    monotoneOn_of_hasDerivWithinAt_nonneg
      (D := Icc s t) (f := G) (f' := deriv G)
      (convex_Icc s t) hG_cont
      (fun u hu => by
        rw [interior_Icc] at hu
        obtain ⟨fp, hfp, _⟩ := hf_deriv u (Ioo_subset_Ico_self hu)
        have hG_at : HasDerivAt G (fp * E u + f u * (-b * E u) - a * E u) u :=
          (hfp.mul (hE_deriv u)).sub (hH_deriv u)
        rw [hG_at.deriv]; exact hG_at.hasDerivWithinAt)
      (fun u hu => by
        rw [interior_Icc] at hu
        obtain ⟨fp, hfp, hfp_bound⟩ := hf_deriv u (Ioo_subset_Ico_self hu)
        have hG_at : HasDerivAt G (fp * E u + f u * (-b * E u) - a * E u) u :=
          (hfp.mul (hE_deriv u)).sub (hH_deriv u)
        rw [hG_at.deriv]
        have h : 0 ≤ (fp - b * f u - a) * E u :=
          mul_nonneg (by linarith) (le_of_lt (hE_pos u))
        nlinarith)
  have hG_init : 0 ≤ G s := by
    dsimp [G, H, E]
    simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one, sub_zero]
    exact hf_init
  intro u hu
  have hG_nonneg : 0 ≤ G u :=
    le_trans hG_init (hG_mono (left_mem_Icc.mpr hst) hu hu.1)
  have hfE : a / b * (1 - E u) ≤ f u * E u := by
    have : G u = f u * E u - a / b * (1 - E u) := by dsimp [G, H]
    linarith
  have hexp_prod : Real.exp (b * (u - s)) * E u = 1 := by
    dsimp [E]; rw [← Real.exp_add]; simp
  have hstep : a / b * (Real.exp (b * (u - s)) - 1) * E u ≤ f u * E u := by
    have hrw : a / b * (Real.exp (b * (u - s)) - 1) * E u =
        a / b * (Real.exp (b * (u - s)) * E u) - a / b * E u := by ring
    rw [hrw, hexp_prod]; linarith [hfE]
  exact le_of_mul_le_mul_right hstep (hE_pos u)

/-- Recovery time offset (in radians). -/
def selectorMURecoveryDelta : ℝ := 1 / 100000

theorem selectorMURecoveryDelta_pos : 0 < selectorMURecoveryDelta := by
  norm_num [selectorMURecoveryDelta]

/-- The shifted selection start time: `WriteStart + Δ_rec`. -/
def selectorMUSelectStartTime (j : ℕ) : ℝ :=
  selectorMUWriteStartTime j + selectorMURecoveryDelta

theorem selectorMUSelectStart_lt_hold (j : ℕ) :
    selectorMUSelectStartTime j < selectorMUWriteHoldTime j := by
  simp only [selectorMUSelectStartTime, selectorMUWriteStartTime,
    selectorMUWriteHoldTime, selectorMURecoveryDelta]
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  nlinarith

theorem selectorMUWriteStart_le_selectStart (j : ℕ) :
    selectorMUWriteStartTime j ≤ selectorMUSelectStartTime j := by
  simp only [selectorMUSelectStartTime]
  linarith [selectorMURecoveryDelta_pos]

theorem selectorMUSelectStart_le_read (j : ℕ) :
    selectorMUSelectStartTime j ≤ selectorMUWriteReadTime j :=
  le_trans (le_of_lt (selectorMUSelectStart_lt_hold j))
    (by simp [selectorMUWriteHoldTime, selectorMUWriteReadTime]
        linarith [Real.pi_gt_three])

/-- `exp x` dominates `2^K` once `x ≥ K`.

This is the numerical pattern used by the recovery proof: `2 ≤ exp 1` from
`Real.add_one_le_exp`, then raise to the `K`th power and compare exponents. -/
theorem recovery_exp_ge_two_pow_of_nat_le (K : ℕ) {x : ℝ} (hx : (K : ℝ) ≤ x) :
    (2 : ℝ) ^ K ≤ Real.exp x := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h ⊢
    exact h
  have hpow : (2 : ℝ) ^ K ≤ (Real.exp 1) ^ K :=
    pow_le_pow_left₀ (by norm_num) htwo K
  have hexpK : (Real.exp 1) ^ K = Real.exp (K : ℝ) := by
    rw [← Real.exp_nat_mul]
    simp
  exact hpow.trans (by
    rw [hexpK]
    exact Real.exp_le_exp.mpr hx)

/-- Backwards-compatible specialization at the old exponent. -/
theorem recovery_exp_ge_two_pow_55_of_le {x : ℝ} (hx : (55 : ℝ) ≤ x) :
    (2 : ℝ) ^ 55 ≤ Real.exp x :=
  recovery_exp_ge_two_pow_of_nat_le 55 hx

/-- Algebraic cancellation for the N-free recovery comparison. -/
theorem recovery_factor_ge_one
    {cr b e : ℝ} (hcr : 0 < cr) (hb : 0 < b)
    (hnum : 1 + b / cr ≤ e) :
    1 ≤ cr / b * (e - 1) := by
  have hsub : b / cr ≤ e - 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsub (le_of_lt (div_pos hcr hb))
  have hcancel : cr / b * (b / cr) = 1 := by
    field_simp [ne_of_gt hcr, ne_of_gt hb]
  linarith

/-- Winner recovery at the right endpoint of an arbitrary interval.

This is the interval-parametric form of
`replicator_winner_recovery_at_selectStart`.  The proof first observes that an
already regenerated floor propagates by the floor barrier; otherwise the winner
mass stays below `1 / |V|` throughout the interval, where the affine ODE lower
bound regenerates the floor by the endpoint. -/
theorem replicator_winner_recovery_at_endpoint
    {d B : ℕ} {V : Type} [Fintype V] [Nonempty V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch
      chiReset chiGate kappa gain readoutP)
    (vstar : V) {s t crMin crMax cgMin gap b : ℝ} {K : ℕ}
    (hN2 : 2 ≤ Fintype.card V)
    (hcrMin_pos : 0 < crMin)
    (hcrMin_le_crMax : crMin ≤ crMax)
    (hcgMin_nonneg : 0 ≤ cgMin)
    (hgap_nonneg : 0 ≤ gap)
    (hb_eq : b = cgMin * gap / 2 - crMax)
    (hb_pos : 0 < b)
    (hbDelta : (K : ℝ) ≤ b * (t - s))
    (hpow : 1 + b / crMin ≤ (2 : ℝ) ^ K)
    (hst : s ≤ t)
    (hdom : ∀ u ∈ Icc s t, u ∈ sched.domain)
    (hcr_bounds : ∀ u ∈ Icc s t,
      crMin ≤ chiReset u * kappa u ∧ chiReset u * kappa u ≤ crMax)
    (hcg_min : ∀ u ∈ Icc s t, cgMin ≤ chiGate u * gain u)
    (hgap_floor :
      ∀ v : V, v ≠ vstar → ∀ u ∈ Ico s t,
        readoutP v (sol.u u) - readoutP vstar (sol.u u) ≤ 0)
    (havg_gap :
      ∀ u ∈ Ico s t,
        gap * (1 - sol.lam vstar u) ≤
          readoutP vstar (sol.u u) -
            ∑ w : V, sol.lam w u * readoutP w (sol.u u))
    (hsum : ∀ u ∈ Icc s t, (∑ w : V, sol.lam w u) = 1)
    (hlam_nonneg : ∀ v : V, ∀ u ∈ Icc s t, 0 ≤ sol.lam v u) :
    1 / (Fintype.card V : ℝ) ≤ sol.lam vstar t := by
  classical
  let invCard : ℝ := 1 / (Fintype.card V : ℝ)
  have htIcc : t ∈ Icc s t := right_mem_Icc.mpr hst
  have hsIcc : s ∈ Icc s t := left_mem_Icc.mpr hst
  have hNpos_nat : 0 < Fintype.card V :=
    lt_of_lt_of_le (by decide : 0 < 2) hN2
  have hNpos : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast hNpos_nat
  have hinv_nonneg : 0 ≤ invCard := by
    dsimp [invCard]
    positivity
  have hinv_half : invCard ≤ 1 / 2 := by
    dsimp [invCard]
    have hN2R : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hN2
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hN2R
  by_contra hnot
  have hlt : sol.lam vstar t < invCard :=
    lt_of_not_ge (by simpa [invCard] using hnot)
  have hbelow : ∀ u ∈ Icc s t, sol.lam vstar u < invCard := by
    intro u hu
    by_contra hnotu
    have hinit : invCard ≤ sol.lam vstar u := le_of_not_gt hnotu
    have hdom_sub : ∀ r ∈ Icc u t, r ∈ sched.domain := by
      intro r hr
      exact hdom r ⟨le_trans hu.1 hr.1, hr.2⟩
    have hcr_nonneg_sub : ∀ r ∈ Icc u t, 0 ≤ chiReset r * kappa r := by
      intro r hr
      have hrfull : r ∈ Icc s t := ⟨le_trans hu.1 hr.1, hr.2⟩
      exact le_trans hcrMin_pos.le ((hcr_bounds r hrfull).1)
    have hcg_nonneg_sub : ∀ r ∈ Icc u t, 0 ≤ chiGate r * gain r := by
      intro r hr
      have hrfull : r ∈ Icc s t := ⟨le_trans hu.1 hr.1, hr.2⟩
      exact le_trans hcgMin_nonneg (hcg_min r hrfull)
    have hgap_sub :
        ∀ v : V, v ≠ vstar → ∀ r ∈ Ico u t,
          readoutP v (sol.u r) - readoutP vstar (sol.u r) ≤ 0 := by
      intro v hv r hr
      exact hgap_floor v hv r ⟨le_trans hu.1 hr.1, hr.2⟩
    have hsum_sub : ∀ r ∈ Icc u t, (∑ w : V, sol.lam w r) = 1 := by
      intro r hr
      exact hsum r ⟨le_trans hu.1 hr.1, hr.2⟩
    have hlam_sub : ∀ v : V, ∀ r ∈ Icc u t, 0 ≤ sol.lam v r := by
      intro v r hr
      exact hlam_nonneg v r ⟨le_trans hu.1 hr.1, hr.2⟩
    have hfloor := replicator_winner_floor_on_interval
      (sol := sol) vstar hu.2
      hdom_sub hcr_nonneg_sub hcg_nonneg_sub hgap_sub hsum_sub hlam_sub
      (by simpa [invCard] using hinit)
    have ht_ge := hfloor t (right_mem_Icc.mpr hu.2)
    exact (not_lt_of_ge (by simpa [invCard] using ht_ge)) hlt
  have hlin := linear_ode_lower_bound
    (a := crMin * invCard) (b := b)
    (mul_nonneg hcrMin_pos.le hinv_nonneg) hb_pos hst
    ((sol.cont_lam vstar).continuousOn)
    (fun u hu => by
      let lam : ℝ := sol.lam vstar u
      let cr : ℝ := chiReset u * kappa u
      let cg : ℝ := chiGate u * gain u
      let pdiff : ℝ :=
        readoutP vstar (sol.u u) -
          ∑ w : V, sol.lam w u * readoutP w (sol.u u)
      refine ⟨cr * (invCard - lam) + cg * lam * pdiff, ?_, ?_⟩
      · have huIcc : u ∈ Icc s t := Ico_subset_Icc_self hu
        simpa [cr, cg, pdiff, lam, invCard, mul_assoc] using
          sol.lam_hasDeriv vstar u (hdom u huIcc)
      · have huIcc : u ∈ Icc s t := Ico_subset_Icc_self hu
        have hcrL : crMin ≤ cr := by
          simpa [cr] using (hcr_bounds u huIcc).1
        have hcrU : cr ≤ crMax := by
          simpa [cr] using (hcr_bounds u huIcc).2
        have hcgL : cgMin ≤ cg := by
          simpa [cg] using hcg_min u huIcc
        have hcg_nonneg : 0 ≤ cg := le_trans hcgMin_nonneg hcgL
        have hlam0 : 0 ≤ lam := by
          simpa [lam] using hlam_nonneg vstar u huIcc
        have hlt_inv : lam < invCard := by
          simpa [lam] using hbelow u huIcc
        have hle_inv : lam ≤ invCard := le_of_lt hlt_inv
        have hlam_half : lam ≤ 1 / 2 := le_trans hle_inv hinv_half
        have hhalf : (1 : ℝ) / 2 ≤ 1 - lam := by linarith
        have hone_minus_nonneg : 0 ≤ 1 - lam := by linarith
        have hgap_factor_nonneg : 0 ≤ gap * (1 - lam) :=
          mul_nonneg hgap_nonneg hone_minus_nonneg
        have hpdiff_lb : gap * (1 - lam) ≤ pdiff := by
          simpa [pdiff, lam] using havg_gap u hu
        have hpdiff_nonneg : 0 ≤ pdiff :=
          le_trans hgap_factor_nonneg hpdiff_lb
        have hreset_lower :
            crMin * invCard - crMax * lam ≤ cr * (invCard - lam) := by
          have hleft :
              crMin * invCard - crMax * lam ≤ crMin * invCard - crMin * lam := by
            have hmul : crMin * lam ≤ crMax * lam :=
              mul_le_mul_of_nonneg_right hcrMin_le_crMax hlam0
            linarith
          have hright : crMin * (invCard - lam) ≤ cr * (invCard - lam) :=
            mul_le_mul_of_nonneg_right hcrL (sub_nonneg.mpr hle_inv)
          have hrewrite :
              crMin * invCard - crMin * lam = crMin * (invCard - lam) := by
            ring
          linarith
        have hgrowth_core :
            cgMin * gap / 2 * lam ≤ cgMin * lam * (gap * (1 - lam)) := by
          have hC : 0 ≤ cgMin * gap * lam :=
            mul_nonneg (mul_nonneg hcgMin_nonneg hgap_nonneg) hlam0
          have hmul := mul_le_mul_of_nonneg_left hhalf hC
          nlinarith
        have hgrowth_mid :
            cgMin * lam * (gap * (1 - lam)) ≤ cg * lam * pdiff := by
          have hA : cgMin * lam ≤ cg * lam :=
            mul_le_mul_of_nonneg_right hcgL hlam0
          have h1 := mul_le_mul_of_nonneg_right hA hgap_factor_nonneg
          have hcg_lam_nonneg : 0 ≤ cg * lam := mul_nonneg hcg_nonneg hlam0
          have h2 := mul_le_mul_of_nonneg_left hpdiff_lb hcg_lam_nonneg
          nlinarith
        have hgrowth :
            cgMin * gap / 2 * lam ≤ cg * lam * pdiff :=
          le_trans hgrowth_core hgrowth_mid
        have htarget :
            crMin * invCard + b * lam =
              (crMin * invCard - crMax * lam) + (cgMin * gap / 2 * lam) := by
          rw [hb_eq]
          ring
        calc
          crMin * invCard + b * lam
              = (crMin * invCard - crMax * lam) +
                  (cgMin * gap / 2 * lam) := htarget
          _ ≤ cr * (invCard - lam) + cg * lam * pdiff :=
              add_le_add hreset_lower hgrowth)
    (by exact hlam_nonneg vstar s hsIcc)
  have hlower := hlin t htIcc
  have hexp_big : 1 + b / crMin ≤ Real.exp (b * (t - s)) :=
    hpow.trans (recovery_exp_ge_two_pow_of_nat_le K hbDelta)
  have hfactor :
      1 ≤ crMin / b * (Real.exp (b * (t - s)) - 1) :=
    recovery_factor_ge_one hcrMin_pos hb_pos hexp_big
  have hlower_floor :
      invCard ≤ (crMin * invCard) / b *
          (Real.exp (b * (t - s)) - 1) := by
    have hmul := mul_le_mul_of_nonneg_left hfactor hinv_nonneg
    have hrewrite :
        invCard * (crMin / b * (Real.exp (b * (t - s)) - 1)) =
          (crMin * invCard) / b *
            (Real.exp (b * (t - s)) - 1) := by
      ring
    nlinarith
  exact (not_lt_of_ge (le_trans hlower_floor hlower)) hlt

/-- Subfloor lower envelope for winner recovery.

If the winner mass remains below the `1 / |V|` floor up to an intermediate
time `u`, the affine ODE comparison used in
`replicator_winner_recovery_at_selectStart` gives this explicit lower bound. -/
theorem replicator_winner_recovery_subfloor_lower_bound
    {d B : ℕ} {V : Type} [Fintype V] [Nonempty V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch
      chiReset chiGate kappa gain readoutP)
    (vstar : V) (j : ℕ)
    {crMin crMax cgMin gap b : ℝ}
    (hN2 : 2 ≤ Fintype.card V)
    (hcrMin_pos : 0 < crMin)
    (hcrMin_le_crMax : crMin ≤ crMax)
    (hcgMin_nonneg : 0 ≤ cgMin)
    (hgap_nonneg : 0 ≤ gap)
    (hb_eq : b = cgMin * gap / 2 - crMax)
    (hb_pos : 0 < b)
    (hdom :
      ∀ u ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
        u ∈ sched.domain)
    (hcr_bounds :
      ∀ u ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
        crMin ≤ chiReset u * kappa u ∧ chiReset u * kappa u ≤ crMax)
    (hcg_min :
      ∀ u ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
        cgMin ≤ chiGate u * gain u)
    (havg_gap :
      ∀ u ∈ Ico (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
        gap * (1 - sol.lam vstar u) ≤
          readoutP vstar (sol.u u) -
            ∑ w : V, sol.lam w u * readoutP w (sol.u u))
    (hlam_nonneg :
      ∀ v : V,
        ∀ u ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
          0 ≤ sol.lam v u)
    (u : ℝ)
    (hu : u ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j))
    (hbelow :
      ∀ r ∈ Icc (selectorMUWriteStartTime j) u,
        sol.lam vstar r < 1 / (Fintype.card V : ℝ)) :
    (crMin * (1 / (Fintype.card V : ℝ))) / b *
        (Real.exp (b * (u - selectorMUWriteStartTime j)) - 1) ≤
      sol.lam vstar u := by
  classical
  let s : ℝ := selectorMUWriteStartTime j
  let invCard : ℝ := 1 / (Fintype.card V : ℝ)
  have hsu : s ≤ u := by
    simpa [s] using hu.1
  have hsub_full :
      ∀ r ∈ Icc s u,
        r ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j) := by
    intro r hr
    exact ⟨by simpa [s] using hr.1, le_trans hr.2 hu.2⟩
  have hNpos_nat : 0 < Fintype.card V :=
    lt_of_lt_of_le (by decide : 0 < 2) hN2
  have hNpos : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast hNpos_nat
  have hinv_nonneg : 0 ≤ invCard := by
    dsimp [invCard]
    positivity
  have hinv_half : invCard ≤ 1 / 2 := by
    dsimp [invCard]
    have hN2R : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hN2
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hN2R
  have hlin := linear_ode_lower_bound
    (a := crMin * invCard) (b := b)
    (mul_nonneg hcrMin_pos.le hinv_nonneg) hb_pos hsu
    ((sol.cont_lam vstar).continuousOn)
    (fun r hr => by
      let lam : ℝ := sol.lam vstar r
      let cr : ℝ := chiReset r * kappa r
      let cg : ℝ := chiGate r * gain r
      let pdiff : ℝ :=
        readoutP vstar (sol.u r) -
          ∑ w : V, sol.lam w r * readoutP w (sol.u r)
      refine ⟨cr * (invCard - lam) + cg * lam * pdiff, ?_, ?_⟩
      · have hrIcc : r ∈ Icc s u := Ico_subset_Icc_self hr
        simpa [cr, cg, pdiff, lam, invCard, s, mul_assoc] using
          sol.lam_hasDeriv vstar r (hdom r (hsub_full r hrIcc))
      · have hrIcc : r ∈ Icc s u := Ico_subset_Icc_self hr
        have hrFull : r ∈ Icc
            (selectorMUWriteStartTime j) (selectorMUSelectStartTime j) :=
          hsub_full r hrIcc
        have hrFullIco : r ∈ Ico
            (selectorMUWriteStartTime j) (selectorMUSelectStartTime j) := by
          exact ⟨by simpa [s] using hr.1, lt_of_lt_of_le hr.2 hu.2⟩
        have hcrL : crMin ≤ cr := by
          simpa [cr] using (hcr_bounds r hrFull).1
        have hcrU : cr ≤ crMax := by
          simpa [cr] using (hcr_bounds r hrFull).2
        have hcgL : cgMin ≤ cg := by
          simpa [cg] using hcg_min r hrFull
        have hcg_nonneg : 0 ≤ cg := le_trans hcgMin_nonneg hcgL
        have hlam0 : 0 ≤ lam := by
          simpa [lam] using hlam_nonneg vstar r hrFull
        have hlt_inv : lam < invCard := by
          simpa [lam, invCard, s] using
            hbelow r ⟨by simpa [s] using hrIcc.1, hrIcc.2⟩
        have hle_inv : lam ≤ invCard := le_of_lt hlt_inv
        have hlam_half : lam ≤ 1 / 2 := le_trans hle_inv hinv_half
        have hhalf : (1 : ℝ) / 2 ≤ 1 - lam := by linarith
        have hone_minus_nonneg : 0 ≤ 1 - lam := by linarith
        have hgap_factor_nonneg : 0 ≤ gap * (1 - lam) :=
          mul_nonneg hgap_nonneg hone_minus_nonneg
        have hpdiff_lb : gap * (1 - lam) ≤ pdiff := by
          simpa [pdiff, lam] using havg_gap r hrFullIco
        have hpdiff_nonneg : 0 ≤ pdiff :=
          le_trans hgap_factor_nonneg hpdiff_lb
        have hreset_lower :
            crMin * invCard - crMax * lam ≤ cr * (invCard - lam) := by
          have hleft :
              crMin * invCard - crMax * lam ≤ crMin * invCard - crMin * lam := by
            have hmul : crMin * lam ≤ crMax * lam :=
              mul_le_mul_of_nonneg_right hcrMin_le_crMax hlam0
            linarith
          have hright : crMin * (invCard - lam) ≤ cr * (invCard - lam) :=
            mul_le_mul_of_nonneg_right hcrL (sub_nonneg.mpr hle_inv)
          have hrewrite :
              crMin * invCard - crMin * lam = crMin * (invCard - lam) := by
            ring
          linarith
        have hgrowth_core :
            cgMin * gap / 2 * lam ≤ cgMin * lam * (gap * (1 - lam)) := by
          have hC : 0 ≤ cgMin * gap * lam :=
            mul_nonneg (mul_nonneg hcgMin_nonneg hgap_nonneg) hlam0
          have hmul := mul_le_mul_of_nonneg_left hhalf hC
          nlinarith
        have hgrowth_mid :
            cgMin * lam * (gap * (1 - lam)) ≤ cg * lam * pdiff := by
          have hA : cgMin * lam ≤ cg * lam :=
            mul_le_mul_of_nonneg_right hcgL hlam0
          have h1 := mul_le_mul_of_nonneg_right hA hgap_factor_nonneg
          have hcg_lam_nonneg : 0 ≤ cg * lam := mul_nonneg hcg_nonneg hlam0
          have h2 := mul_le_mul_of_nonneg_left hpdiff_lb hcg_lam_nonneg
          nlinarith
        have hgrowth :
            cgMin * gap / 2 * lam ≤ cg * lam * pdiff :=
          le_trans hgrowth_core hgrowth_mid
        have htarget :
            crMin * invCard + b * lam =
              (crMin * invCard - crMax * lam) + (cgMin * gap / 2 * lam) := by
          rw [hb_eq]
          ring
        calc
          crMin * invCard + b * lam
              = (crMin * invCard - crMax * lam) +
                  (cgMin * gap / 2 * lam) := htarget
          _ ≤ cr * (invCard - lam) + cg * lam * pdiff :=
              add_le_add hreset_lower hgrowth)
    (by
      exact hlam_nonneg vstar s (hsub_full s (left_mem_Icc.mpr hsu)))
  simpa [s, invCard] using hlin u (right_mem_Icc.mpr hsu)

/-- Winner recovery at the shifted select-start time.

The theorem is deliberately N-free in its numerical part.  The cardinality
enters only through `hN2`, which gives `1 / |V| ≤ 1 / 2`; the final exponential
comparison cancels the factor `1 / |V|`.

The analytic inputs are the local rate bounds on
`[WriteStart_j, selectStart_j]`, the weak winner barrier gap used to propagate
an already-recovered floor, and the averaged readout gap lower bound used in
the affine minorization under the contradiction hypothesis. -/
theorem replicator_winner_recovery_at_selectStart
    {d B : ℕ} {V : Type} [Fintype V] [Nonempty V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch
      chiReset chiGate kappa gain readoutP)
    (vstar : V) (j : ℕ)
    {crMin crMax cgMin gap b : ℝ} {K : ℕ}
    (hN2 : 2 ≤ Fintype.card V)
    (hcrMin_pos : 0 < crMin)
    (hcrMin_le_crMax : crMin ≤ crMax)
    (hcgMin_nonneg : 0 ≤ cgMin)
    (hgap_nonneg : 0 ≤ gap)
    (hb_eq : b = cgMin * gap / 2 - crMax)
    (hb_pos : 0 < b)
    (hbDelta : (K : ℝ) ≤ b * selectorMURecoveryDelta)
    (hpow : 1 + b / crMin ≤ (2 : ℝ) ^ K)
    (hdom :
      ∀ u ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
        u ∈ sched.domain)
    (hcr_bounds :
      ∀ u ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
        crMin ≤ chiReset u * kappa u ∧ chiReset u * kappa u ≤ crMax)
    (hcg_min :
      ∀ u ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
        cgMin ≤ chiGate u * gain u)
    (hgap_floor :
      ∀ v : V, v ≠ vstar →
        ∀ u ∈ Ico (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
          readoutP v (sol.u u) - readoutP vstar (sol.u u) ≤ 0)
    (havg_gap :
      ∀ u ∈ Ico (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
        gap * (1 - sol.lam vstar u) ≤
          readoutP vstar (sol.u u) -
            ∑ w : V, sol.lam w u * readoutP w (sol.u u))
    (hsum :
      ∀ u ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
        (∑ w : V, sol.lam w u) = 1)
    (hlam_nonneg :
      ∀ v : V,
        ∀ u ∈ Icc (selectorMUWriteStartTime j) (selectorMUSelectStartTime j),
          0 ≤ sol.lam v u) :
    1 / (Fintype.card V : ℝ) ≤ sol.lam vstar (selectorMUSelectStartTime j) := by
  classical
  let s : ℝ := selectorMUWriteStartTime j
  let t : ℝ := selectorMUSelectStartTime j
  let invCard : ℝ := 1 / (Fintype.card V : ℝ)
  have hst : s ≤ t := by
    simpa [s, t] using selectorMUWriteStart_le_selectStart j
  have htIcc : t ∈ Icc s t := right_mem_Icc.mpr hst
  have hsIcc : s ∈ Icc s t := left_mem_Icc.mpr hst
  have hNpos_nat : 0 < Fintype.card V :=
    lt_of_lt_of_le (by decide : 0 < 2) hN2
  have hNpos : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast hNpos_nat
  have hinv_nonneg : 0 ≤ invCard := by
    dsimp [invCard]
    positivity
  have hinv_half : invCard ≤ 1 / 2 := by
    dsimp [invCard]
    have hN2R : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by
      exact_mod_cast hN2
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hN2R
  by_contra hnot
  have hlt : sol.lam vstar t < invCard :=
    lt_of_not_ge (by simpa [t, invCard] using hnot)
  have hbelow : ∀ u ∈ Icc s t, sol.lam vstar u < invCard := by
    intro u hu
    by_contra hnotu
    have hinit : invCard ≤ sol.lam vstar u := le_of_not_gt hnotu
    have hdom_sub : ∀ r ∈ Icc u t, r ∈ sched.domain := by
      intro r hr
      exact hdom r (by
        simpa [s, t] using
          (show r ∈ Icc s t from ⟨le_trans hu.1 hr.1, hr.2⟩))
    have hcr_nonneg_sub : ∀ r ∈ Icc u t, 0 ≤ chiReset r * kappa r := by
      intro r hr
      have hrfull : r ∈ Icc s t := ⟨le_trans hu.1 hr.1, hr.2⟩
      exact le_trans hcrMin_pos.le
        ((hcr_bounds r (by simpa [s, t] using hrfull)).1)
    have hcg_nonneg_sub : ∀ r ∈ Icc u t, 0 ≤ chiGate r * gain r := by
      intro r hr
      have hrfull : r ∈ Icc s t := ⟨le_trans hu.1 hr.1, hr.2⟩
      exact le_trans hcgMin_nonneg
        (hcg_min r (by simpa [s, t] using hrfull))
    have hgap_sub :
        ∀ v : V, v ≠ vstar → ∀ r ∈ Ico u t,
          readoutP v (sol.u r) - readoutP vstar (sol.u r) ≤ 0 := by
      intro v hv r hr
      exact hgap_floor v hv r (by
        simpa [s, t] using
          (show r ∈ Ico s t from ⟨le_trans hu.1 hr.1, hr.2⟩))
    have hsum_sub : ∀ r ∈ Icc u t, (∑ w : V, sol.lam w r) = 1 := by
      intro r hr
      exact hsum r (by
        simpa [s, t] using
          (show r ∈ Icc s t from ⟨le_trans hu.1 hr.1, hr.2⟩))
    have hlam_sub : ∀ v : V, ∀ r ∈ Icc u t, 0 ≤ sol.lam v r := by
      intro v r hr
      exact hlam_nonneg v r (by
        simpa [s, t] using
          (show r ∈ Icc s t from ⟨le_trans hu.1 hr.1, hr.2⟩))
    have hfloor := replicator_winner_floor_on_interval
      (sol := sol) vstar hu.2
      hdom_sub hcr_nonneg_sub hcg_nonneg_sub hgap_sub hsum_sub hlam_sub
      (by simpa [invCard] using hinit)
    have ht_ge := hfloor t (right_mem_Icc.mpr hu.2)
    exact (not_lt_of_ge (by simpa [invCard, t] using ht_ge)) hlt
  have hlin := linear_ode_lower_bound
    (a := crMin * invCard) (b := b)
    (mul_nonneg hcrMin_pos.le hinv_nonneg) hb_pos hst
    ((sol.cont_lam vstar).continuousOn)
    (fun u hu => by
      let lam : ℝ := sol.lam vstar u
      let cr : ℝ := chiReset u * kappa u
      let cg : ℝ := chiGate u * gain u
      let pdiff : ℝ :=
        readoutP vstar (sol.u u) -
          ∑ w : V, sol.lam w u * readoutP w (sol.u u)
      refine ⟨cr * (invCard - lam) + cg * lam * pdiff, ?_, ?_⟩
      · have huIcc : u ∈ Icc s t := Ico_subset_Icc_self hu
        simpa [cr, cg, pdiff, lam, invCard, s, t, mul_assoc] using
          sol.lam_hasDeriv vstar u
            (hdom u (by simpa [s, t] using huIcc))
      · have huIcc : u ∈ Icc s t := Ico_subset_Icc_self hu
        have hcrL : crMin ≤ cr := by
          simpa [cr, s, t] using
            (hcr_bounds u (by simpa [s, t] using huIcc)).1
        have hcrU : cr ≤ crMax := by
          simpa [cr, s, t] using
            (hcr_bounds u (by simpa [s, t] using huIcc)).2
        have hcgL : cgMin ≤ cg := by
          simpa [cg, s, t] using hcg_min u (by simpa [s, t] using huIcc)
        have hcg_nonneg : 0 ≤ cg := le_trans hcgMin_nonneg hcgL
        have hlam0 : 0 ≤ lam := by
          simpa [lam] using
            hlam_nonneg vstar u (by simpa [s, t] using huIcc)
        have hlt_inv : lam < invCard := by
          simpa [lam] using hbelow u huIcc
        have hle_inv : lam ≤ invCard := le_of_lt hlt_inv
        have hlam_half : lam ≤ 1 / 2 := le_trans hle_inv hinv_half
        have hhalf : (1 : ℝ) / 2 ≤ 1 - lam := by linarith
        have hone_minus_nonneg : 0 ≤ 1 - lam := by linarith
        have hgap_factor_nonneg : 0 ≤ gap * (1 - lam) :=
          mul_nonneg hgap_nonneg hone_minus_nonneg
        have hpdiff_lb : gap * (1 - lam) ≤ pdiff := by
          simpa [pdiff, lam, s, t] using havg_gap u (by simpa [s, t] using hu)
        have hpdiff_nonneg : 0 ≤ pdiff :=
          le_trans hgap_factor_nonneg hpdiff_lb
        have hreset_lower :
            crMin * invCard - crMax * lam ≤ cr * (invCard - lam) := by
          have hleft :
              crMin * invCard - crMax * lam ≤ crMin * invCard - crMin * lam := by
            have hmul : crMin * lam ≤ crMax * lam :=
              mul_le_mul_of_nonneg_right hcrMin_le_crMax hlam0
            linarith
          have hright : crMin * (invCard - lam) ≤ cr * (invCard - lam) :=
            mul_le_mul_of_nonneg_right hcrL (sub_nonneg.mpr hle_inv)
          have hrewrite :
              crMin * invCard - crMin * lam = crMin * (invCard - lam) := by
            ring
          linarith
        have hgrowth_core :
            cgMin * gap / 2 * lam ≤ cgMin * lam * (gap * (1 - lam)) := by
          have hC : 0 ≤ cgMin * gap * lam :=
            mul_nonneg (mul_nonneg hcgMin_nonneg hgap_nonneg) hlam0
          have hmul := mul_le_mul_of_nonneg_left hhalf hC
          nlinarith
        have hgrowth_mid :
            cgMin * lam * (gap * (1 - lam)) ≤ cg * lam * pdiff := by
          have hA : cgMin * lam ≤ cg * lam :=
            mul_le_mul_of_nonneg_right hcgL hlam0
          have h1 := mul_le_mul_of_nonneg_right hA hgap_factor_nonneg
          have hcg_lam_nonneg : 0 ≤ cg * lam := mul_nonneg hcg_nonneg hlam0
          have h2 := mul_le_mul_of_nonneg_left hpdiff_lb hcg_lam_nonneg
          nlinarith
        have hgrowth :
            cgMin * gap / 2 * lam ≤ cg * lam * pdiff :=
          le_trans hgrowth_core hgrowth_mid
        have htarget :
            crMin * invCard + b * lam =
              (crMin * invCard - crMax * lam) + (cgMin * gap / 2 * lam) := by
          rw [hb_eq]
          ring
        calc
          crMin * invCard + b * lam
              = (crMin * invCard - crMax * lam) +
                  (cgMin * gap / 2 * lam) := htarget
          _ ≤ cr * (invCard - lam) + cg * lam * pdiff :=
              add_le_add hreset_lower hgrowth)
    (by
      exact hlam_nonneg vstar s (by simpa [s, t] using hsIcc))
  have hlower := hlin t htIcc
  have hdelta : t - s = selectorMURecoveryDelta := by
    simp [s, t, selectorMUSelectStartTime]
  rw [hdelta] at hlower
  have hexp_big : 1 + b / crMin ≤ Real.exp (b * selectorMURecoveryDelta) :=
    hpow.trans (recovery_exp_ge_two_pow_of_nat_le K hbDelta)
  have hfactor :
      1 ≤ crMin / b * (Real.exp (b * selectorMURecoveryDelta) - 1) :=
    recovery_factor_ge_one hcrMin_pos hb_pos hexp_big
  have hlower_floor :
      invCard ≤ (crMin * invCard) / b *
          (Real.exp (b * selectorMURecoveryDelta) - 1) := by
    have hmul := mul_le_mul_of_nonneg_left hfactor hinv_nonneg
    have hrewrite :
        invCard * (crMin / b * (Real.exp (b * selectorMURecoveryDelta) - 1)) =
          (crMin * invCard) / b *
            (Real.exp (b * selectorMURecoveryDelta) - 1) := by
      ring
    nlinarith
  exact (not_lt_of_ge (le_trans hlower_floor hlower)) hlt

end Ripple.BoundedUniversality.BGP
