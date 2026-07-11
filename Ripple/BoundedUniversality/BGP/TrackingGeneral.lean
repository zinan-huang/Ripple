/-
Ripple.BoundedUniversality.BGP.TrackingGeneral
--------------------------
Fr-GENERALIZED copies of the proven tracking chain (P10' runway step
(i); HANDOFF/p10-blocker.md).  Same proofs as PhaseClock's
perturbation_recurrence / all_time_tracking with the step map
abstracted from `S.evalF` to an arbitrary `Fr` carrying a continuity
hypothesis and the snap property — so they apply to the CLIPPED
continuation of the step polynomial, which is what the global-
existence bootstrap needs (the clipped system is globally dissipative,
giving the crude moving box unconditionally; tracking then shows the
clip is never active, so the solution solves the true system).

Proven-by-copy from PhaseClock (agent A / A-2 proofs, adversarially
reviewed); the originals remain canonical for the S.evalF instance.
-/

import Ripple.BoundedUniversality.BGP.PhaseClock
import Mathlib

namespace Ripple.BoundedUniversality.BGP

open Real intervalIntegral

def MovingBoxF {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ} {E : LatticeEncoding Mch d}
    (Fr : (Fin d → ℝ) → Fin d → ℝ)
    {A : ℝ} {M : ℕ} {w : ℕ}
    (sol : IteratorSol d Fr A M (orbitPoint Mch E w 0))
    (D_K : ℝ) : Prop :=
  ∀ (j : ℕ) (t : ℝ), t ∈ Set.Icc (2*π*j) (2*π*(j+1)) →
    (∀ i, |orbitPoint Mch E w (j+1) i - orbitPoint Mch E w j i| ≤ D_K) ∧
    (∀ i, |sol.z t i - orbitPoint Mch E w j i| ≤ D_K) ∧
    (∀ i, |sol.u t i - orbitPoint Mch E w j i| ≤ D_K) ∧
    (∀ i, |Fr (sol.u t) i - orbitPoint Mch E w j i| ≤ D_K)

/-- **P4, perturbation recurrence** (lem:perturbation-recurrence,
paper constants per main.tex:790): one cycle maps sampling error `e`
to at most `2κ e + 2κ D_K + 2χ D_K + ηstep`, provided the snap input
stays in the snap basin (`e + χ D_K ≤ r₀`). -/
theorem perturbation_recurrence_general
    {Conf : Type} [Primcodable Conf]
    (Mch : DiscreteMachine Conf) (d : ℕ) (E : LatticeEncoding Mch d)
    (S : RobustRealExtension Mch d E)
    (Fr : (Fin d → ℝ) → Fin d → ℝ)
    (hFrc : ∀ k : Fin d, Continuous fun x : Fin d → ℝ => Fr x k)
    (hsnapF : ∀ (c : Conf) (x : Fin d → ℝ),
      (∀ i, |x i - E.enc c i| ≤ (S.r₀ : ℝ)) →
      ∀ i, |Fr x i - E.enc (Mch.step c) i| ≤ (S.ηstep : ℝ))
    (A : ℝ) (hA : 0 < A) (M : ℕ) (w : ℕ)
    (sol : IteratorSol d Fr A M (orbitPoint Mch E w 0))
    (D_K : ℝ) (hD : 0 < D_K) (hbox : MovingBoxF Fr sol D_K)
    (j : ℕ) (e : ℝ) (he0 : 0 ≤ e)
    (he : ∀ i, |sol.z (2*π*j) i - orbitPoint Mch E w j i| ≤ e ∧
               |sol.u (2*π*j) i - orbitPoint Mch E w j i| ≤ e)
    (hsnap : e + trackingChi A M * D_K ≤ (S.r₀ : ℝ)) :
    ∀ i, |sol.z (2*π*(j+1)) i - orbitPoint Mch E w (j+1) i| ≤
          2 * trackingKappa A M * e + 2 * trackingKappa A M * D_K
            + 2 * trackingChi A M * D_K + (S.ηstep : ℝ) ∧
         |sol.u (2*π*(j+1)) i - orbitPoint Mch E w (j+1) i| ≤
          2 * trackingKappa A M * e + 2 * trackingKappa A M * D_K
            + 2 * trackingChi A M * D_K + (S.ηstep : ℝ) := by
  intro i
  let a : ℝ := 2 * π * (j : ℝ)
  let m : ℝ := 2 * π * (j : ℝ) + π
  let b : ℝ := 2 * π * (j : ℝ) + 2 * π
  let xj : Fin d → ℝ := orbitPoint Mch E w j
  let xnext : Fin d → ℝ := orbitPoint Mch E w (j + 1)
  have hπ : 0 < π := Real.pi_pos
  have ha0 : (0:ℝ) ≤ a :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Nat.cast_nonneg j)
  have hamb : a ≤ m := by dsimp [a, m]; linarith
  have hmb : m ≤ b := by dsimp [a, m, b]; linarith [hπ]
  have hab : a ≤ b := le_trans hamb hmb
  have hb_eq : b = 2 * π * ((j : ℝ) + 1) := by dsimp [b]; ring
  have ha_eq : a = 2 * π * j := rfl
  have hm_eq : m = 2 * π * j + π := rfl
  have hcycle_m : m ∈ Set.Icc (2*π*j) (2*π*(j+1)) := by
    constructor
    · simpa [a, m] using hamb
    · simpa [← hb_eq] using hmb
  have hxnext_box : ∀ k, |xnext k - xj k| ≤ D_K := (hbox j m hcycle_m).1
  have hz_cont : ∀ k, Continuous fun t => sol.z t k := fun k => sol.cont_z k
  have hu_cont : ∀ k, Continuous fun t => sol.u t k := fun k => sol.cont_u k
  have hEval_cont : ∀ k, Continuous fun t => Fr (sol.u t) k := fun k => by
    have hsolu : Continuous fun t => sol.u t := continuous_pi fun l => hu_cont l
    exact (hFrc k).comp hsolu
  have hχ_nonneg : 0 ≤ trackingChi A M := by
    unfold trackingChi
    positivity
  have hκ_nonneg : 0 ≤ trackingKappa A M := by
    unfold trackingKappa
    exact (Real.exp_pos _).le
  have hκ_le_one : trackingKappa A M ≤ 1 := by
    unfold trackingKappa
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ (2 * π / 3) * (3 / 4 : ℝ) ^ M := by positivity
    nlinarith
  have hη_nonneg : 0 ≤ (S.ηstep : ℝ) := by exact_mod_cast S.ηstep_pos.le
  have hD_nonneg : 0 ≤ D_K := hD.le
  have hχD_nonneg : 0 ≤ trackingChi A M * D_K := mul_nonneg hχ_nonneg hD_nonneg
  have hold_u_first :
      ∀ t ∈ Set.Icc a m, ∀ k, |sol.u t k - sol.u a k| ≤ trackingChi A M * D_K := by
    intro t ht k
    have hat : a ≤ t := ht.1
    have htm : t ≤ m := ht.2
    have hderiv : ∀ s ∈ Set.Icc a t,
        HasDerivAt (fun τ => sol.u τ k)
          (A * rPulse M s * (sol.z s k - sol.u s k)) s := by
      intro s hs
      exact sol.ode_u s (le_trans ha0 hs.1) k
    have hbound : ∀ s ∈ Set.Icc a t,
        |A * rPulse M s * (sol.z s k - sol.u s k)|
          ≤ A * (1/2) ^ M * (2 * D_K) := by
      intro s hs
      have hs_cycle : s ∈ Set.Icc (2*π*j) (2*π*(j+1)) := by
        simpa [a, ← hb_eq] using
          (⟨hs.1, le_trans hs.2 (le_trans ht.2 hmb)⟩ :
            s ∈ Set.Icc a b)
      have hzD := (hbox j s hs_cycle).2.1 k
      have huD := (hbox j s hs_cycle).2.2.1 k
      have hzu : |sol.z s k - sol.u s k| ≤ 2 * D_K := by
        calc
          |sol.z s k - sol.u s k|
              = |(sol.z s k - xj k) - (sol.u s k - xj k)| := by ring_nf
          _ ≤ |sol.z s k - xj k| + |sol.u s k - xj k| := by
            simpa [abs_sub_comm] using
              abs_sub_le (sol.z s k) (xj k) (sol.u s k)
          _ ≤ D_K + D_K := add_le_add hzD huD
          _ = 2 * D_K := by ring
      have hrle : rPulse M s ≤ (1/2 : ℝ) ^ M := by
        apply rPulse_le_offphase
        apply sin_window_nonneg j
        · simpa [a] using hs_cycle.1
        · have : s ≤ 2 * π * j + π := by
            rw [← hm_eq]
            exact le_trans hs.2 htm
          simpa using this
      have hrnn : 0 ≤ rPulse M s := rPulse_nonneg M s
      calc
        |A * rPulse M s * (sol.z s k - sol.u s k)|
            = A * rPulse M s * |sol.z s k - sol.u s k| := by
              rw [abs_mul, abs_mul, abs_of_pos hA, abs_of_nonneg hrnn]
        _ ≤ A * ((1/2 : ℝ) ^ M) * (2 * D_K) := by
              have htmp := mul_le_mul hrle hzu (abs_nonneg _)
                (pow_nonneg (by norm_num) M)
              convert mul_le_mul_of_nonneg_left htmp hA.le using 1 <;> ring
    have hhold := hold_bound (fun τ => sol.u τ k)
      (fun s => A * rPulse M s * (sol.z s k - sol.u s k))
      (A * (1/2) ^ M * (2 * D_K)) a t hat hderiv hbound
    have hlen : t - a ≤ π := by dsimp [a, m] at ht; linarith
    calc
      |sol.u t k - sol.u a k|
          ≤ (A * (1/2) ^ M * (2 * D_K)) * (t - a) := hhold
      _ ≤ (A * (1/2) ^ M * (2 * D_K)) * π := by
            have hcoef : 0 ≤ A * (1/2 : ℝ) ^ M * (2 * D_K) := by positivity
            exact mul_le_mul_of_nonneg_left hlen hcoef
      _ = trackingChi A M * D_K := by
            unfold trackingChi
            ring
  have hu_first_near : ∀ t ∈ Set.Icc a m, ∀ k, |sol.u t k - xj k| ≤ e + trackingChi A M * D_K := by
    intro t ht k
    have hstart := (he k).2
    rw [← ha_eq] at hstart
    have hhold := hold_u_first t ht k
    calc
      |sol.u t k - xj k|
          = |(sol.u t k - sol.u a k) + (sol.u a k - xj k)| := by ring_nf
      _ ≤ |sol.u t k - sol.u a k| + |sol.u a k - xj k| := abs_add_le _ _
      _ ≤ trackingChi A M * D_K + e := add_le_add hhold hstart
      _ = e + trackingChi A M * D_K := by ring
  have hsnap_first : ∀ t ∈ Set.Icc a m, ∀ k, |Fr (sol.u t) k - xnext k| ≤ (S.ηstep : ℝ) := by
    intro t ht k
    have hnear : ∀ l, |sol.u t l - E.enc (Mch.step^[j] (Mch.init w)) l| ≤ (S.r₀ : ℝ) := by
      intro l
      exact le_trans (hu_first_near t ht l) hsnap
    simpa [RobustRealExtension.evalF, orbitPoint, xnext, Function.iterate_succ_apply'] using
      hsnapF (Mch.step^[j] (Mch.init w)) (sol.u t) hnear k
  have hz_mid :
      |sol.z m i - xnext i| ≤ trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) := by
    have hδ : ∀ t ∈ Set.Icc a m, |Fr (sol.u t) i - xnext i| ≤ (S.ηstep : ℝ) :=
      fun t ht => hsnap_first t ht i
    have hderiv : ∀ t ∈ Set.Icc a m,
        HasDerivAt (fun τ => sol.z τ i)
          (A * qPulse M t * (Fr (sol.u t) i - sol.z t i)) t := by
      intro t ht
      exact sol.ode_z t (le_trans ha0 ht.1) i
    have htarget := targeting_bound A hA (qPulse M)
      (fun t => Fr (sol.u t) i) (fun t => sol.z t i) a m hamb
      (qPulse_continuous M) (fun t ht => qPulse_nonneg M t)
      (hEval_cont i) (xnext i) (S.ηstep : ℝ) hδ hderiv
    have hint := active_integral_lower M j
    have hInt : (2 * π / 3) * (3/4 : ℝ) ^ M ≤ ∫ t in a..m, qPulse M t := by
      simpa [a, m] using hint
    have hcoef :
        Real.exp (-(A * ∫ t in a..m, qPulse M t)) ≤ trackingKappa A M := by
      unfold trackingKappa
      apply Real.exp_le_exp.mpr
      nlinarith [hA, hInt]
    have hstartz := (he i).1
    rw [← ha_eq] at hstartz
    have hxgap := hxnext_box i
    have hza : |sol.z a i - xnext i| ≤ e + D_K := by
      calc
        |sol.z a i - xnext i|
            = |(sol.z a i - xj i) - (xnext i - xj i)| := by ring_nf
        _ ≤ |sol.z a i - xj i| + |xnext i - xj i| := by
          simpa [abs_sub_comm] using
            abs_sub_le (sol.z a i) (xj i) (xnext i)
        _ ≤ e + D_K := add_le_add hstartz hxgap
    have hmul :
        Real.exp (-(A * ∫ t in a..m, qPulse M t)) * |sol.z a i - xnext i|
          ≤ trackingKappa A M * (e + D_K) := by
      exact mul_le_mul hcoef hza (abs_nonneg _) hκ_nonneg
    exact le_trans htarget (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hmul (S.ηstep : ℝ))
  have hold_z_second :
      ∀ t ∈ Set.Icc m b, ∀ k, |sol.z t k - sol.z m k| ≤ trackingChi A M * D_K := by
    intro t ht k
    have hmt : m ≤ t := ht.1
    have htb : t ≤ b := ht.2
    have hderiv : ∀ s ∈ Set.Icc m t,
        HasDerivAt (fun τ => sol.z τ k)
          (A * qPulse M s * (Fr (sol.u s) k - sol.z s k)) s := by
      intro s hs
      exact sol.ode_z s (le_trans (le_trans ha0 hamb) hs.1) k
    have hbound : ∀ s ∈ Set.Icc m t,
        |A * qPulse M s * (Fr (sol.u s) k - sol.z s k)|
          ≤ A * (1/2) ^ M * (2 * D_K) := by
      intro s hs
      have hs_cycle : s ∈ Set.Icc (2*π*j) (2*π*(j+1)) := by
        simpa [a, ← hb_eq] using
          (⟨le_trans hamb hs.1, le_trans hs.2 htb⟩ :
            s ∈ Set.Icc a b)
      have hFD := (hbox j s hs_cycle).2.2.2 k
      have hzD := (hbox j s hs_cycle).2.1 k
      have hFz : |Fr (sol.u s) k - sol.z s k| ≤ 2 * D_K := by
        calc
          |Fr (sol.u s) k - sol.z s k|
              = |(Fr (sol.u s) k - xj k) - (sol.z s k - xj k)| := by ring_nf
          _ ≤ |Fr (sol.u s) k - xj k| + |sol.z s k - xj k| := by
            simpa [abs_sub_comm] using
              abs_sub_le (Fr (sol.u s) k) (xj k) (sol.z s k)
          _ ≤ D_K + D_K := add_le_add hFD hzD
          _ = 2 * D_K := by ring
      have hqle : qPulse M s ≤ (1/2 : ℝ) ^ M := by
        apply qPulse_le_offphase
        apply sin_window_nonpos j
        · have : 2 * π * j + π ≤ s := by
            rw [← hm_eq]
            exact hs.1
          simpa using this
        · simpa [← hb_eq] using hs_cycle.2
      have hqnn : 0 ≤ qPulse M s := qPulse_nonneg M s
      calc
        |A * qPulse M s * (Fr (sol.u s) k - sol.z s k)|
            = A * qPulse M s * |Fr (sol.u s) k - sol.z s k| := by
              rw [abs_mul, abs_mul, abs_of_pos hA, abs_of_nonneg hqnn]
        _ ≤ A * ((1/2 : ℝ) ^ M) * (2 * D_K) := by
              have htmp := mul_le_mul hqle hFz (abs_nonneg _)
                (pow_nonneg (by norm_num) M)
              convert mul_le_mul_of_nonneg_left htmp hA.le using 1 <;> ring
    have hhold := hold_bound (fun τ => sol.z τ k)
      (fun s => A * qPulse M s * (Fr (sol.u s) k - sol.z s k))
      (A * (1/2) ^ M * (2 * D_K)) m t hmt hderiv hbound
    have hlen : t - m ≤ π := by dsimp [m, b] at ht; linarith
    calc
      |sol.z t k - sol.z m k|
          ≤ (A * (1/2) ^ M * (2 * D_K)) * (t - m) := hhold
      _ ≤ (A * (1/2) ^ M * (2 * D_K)) * π := by
            have hcoef : 0 ≤ A * (1/2 : ℝ) ^ M * (2 * D_K) := by positivity
            exact mul_le_mul_of_nonneg_left hlen hcoef
      _ = trackingChi A M * D_K := by
            unfold trackingChi
            ring
  have hz_second_near : ∀ t ∈ Set.Icc m b, ∀ k,
      |sol.z t k - xnext k| ≤
        trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) + trackingChi A M * D_K := by
    intro t ht k
    have hmidk : |sol.z m k - xnext k| ≤
        trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) := by
      -- same first-half targeting estimate as `hz_mid`, for coordinate `k`
      have hδ : ∀ s ∈ Set.Icc a m, |Fr (sol.u s) k - xnext k| ≤ (S.ηstep : ℝ) :=
        fun s hs => hsnap_first s hs k
      have hderiv : ∀ s ∈ Set.Icc a m,
          HasDerivAt (fun τ => sol.z τ k)
            (A * qPulse M s * (Fr (sol.u s) k - sol.z s k)) s := by
        intro s hs
        exact sol.ode_z s (le_trans ha0 hs.1) k
      have htarget := targeting_bound A hA (qPulse M)
        (fun s => Fr (sol.u s) k) (fun s => sol.z s k) a m hamb
        (qPulse_continuous M) (fun s hs => qPulse_nonneg M s)
        (hEval_cont k) (xnext k) (S.ηstep : ℝ) hδ hderiv
      have hInt : (2 * π / 3) * (3/4 : ℝ) ^ M ≤ ∫ s in a..m, qPulse M s := by
        simpa [a, m] using active_integral_lower M j
      have hcoef :
          Real.exp (-(A * ∫ s in a..m, qPulse M s)) ≤ trackingKappa A M := by
        unfold trackingKappa
        apply Real.exp_le_exp.mpr
        nlinarith [hA, hInt]
      have hstartz := (he k).1
      rw [← ha_eq] at hstartz
      have hxgap := hxnext_box k
      have hza : |sol.z a k - xnext k| ≤ e + D_K := by
        calc
          |sol.z a k - xnext k|
              = |(sol.z a k - xj k) - (xnext k - xj k)| := by ring_nf
          _ ≤ |sol.z a k - xj k| + |xnext k - xj k| := by
            simpa [abs_sub_comm] using
              abs_sub_le (sol.z a k) (xj k) (xnext k)
          _ ≤ e + D_K := add_le_add hstartz hxgap
      have hmul :
          Real.exp (-(A * ∫ s in a..m, qPulse M s)) * |sol.z a k - xnext k|
            ≤ trackingKappa A M * (e + D_K) := by
        exact mul_le_mul hcoef hza (abs_nonneg _) hκ_nonneg
      exact le_trans htarget (by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hmul (S.ηstep : ℝ))
    have hhold := hold_z_second t ht k
    calc
      |sol.z t k - xnext k|
          = |(sol.z t k - sol.z m k) + (sol.z m k - xnext k)| := by ring_nf
      _ ≤ |sol.z t k - sol.z m k| + |sol.z m k - xnext k| := abs_add_le _ _
      _ ≤ trackingChi A M * D_K +
          (trackingKappa A M * (e + D_K) + (S.ηstep : ℝ)) := add_le_add hhold hmidk
      _ = trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) + trackingChi A M * D_K := by ring
  have hz_b_pre :
      |sol.z b i - xnext i| ≤
        trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) + trackingChi A M * D_K :=
    hz_second_near b (Set.right_mem_Icc.mpr hmb) i
  have hu_m_xnext : ∀ k, |sol.u m k - xnext k| ≤ e + trackingChi A M * D_K + D_K := by
    intro k
    have hu_near := hu_first_near m (Set.right_mem_Icc.mpr hamb) k
    have hxgap := hxnext_box k
    calc
      |sol.u m k - xnext k|
          = |(sol.u m k - xj k) - (xnext k - xj k)| := by ring_nf
      _ ≤ |sol.u m k - xj k| + |xnext k - xj k| := by
        simpa [abs_sub_comm] using
          abs_sub_le (sol.u m k) (xj k) (xnext k)
      _ ≤ (e + trackingChi A M * D_K) + D_K := add_le_add hu_near hxgap
      _ = e + trackingChi A M * D_K + D_K := by ring
  have hu_b_pre :
      |sol.u b i - xnext i| ≤
        trackingKappa A M * (e + trackingChi A M * D_K + D_K) +
          (trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) + trackingChi A M * D_K) := by
    have hδ : ∀ t ∈ Set.Icc m b,
        |sol.z t i - xnext i| ≤
          trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) + trackingChi A M * D_K :=
      fun t ht => hz_second_near t ht i
    have hderiv : ∀ t ∈ Set.Icc m b,
        HasDerivAt (fun τ => sol.u τ i)
          (A * rPulse M t * (sol.z t i - sol.u t i)) t := by
      intro t ht
      exact sol.ode_u t (le_trans (le_trans ha0 hamb) ht.1) i
    have htarget := targeting_bound A hA (rPulse M)
      (fun t => sol.z t i) (fun t => sol.u t i) m b hmb
      (rPulse_continuous M) (fun t ht => rPulse_nonneg M t)
      (hz_cont i) (xnext i)
      (trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) + trackingChi A M * D_K)
      hδ hderiv
    have hInt : (2 * π / 3) * (3/4 : ℝ) ^ M ≤ ∫ t in m..b, rPulse M t := by
      simpa [m, b] using r_active_integral_lower M j
    have hcoef :
        Real.exp (-(A * ∫ t in m..b, rPulse M t)) ≤ trackingKappa A M := by
      unfold trackingKappa
      apply Real.exp_le_exp.mpr
      nlinarith [hA, hInt]
    have hmul :
        Real.exp (-(A * ∫ t in m..b, rPulse M t)) * |sol.u m i - xnext i|
          ≤ trackingKappa A M * (e + trackingChi A M * D_K + D_K) := by
      exact mul_le_mul hcoef (hu_m_xnext i) (abs_nonneg _) hκ_nonneg
    exact le_trans htarget (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hmul
          (trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) + trackingChi A M * D_K))
  constructor
  · change |sol.z (2 * π * ((j : ℝ) + 1)) i - xnext i| ≤
      2 * trackingKappa A M * e + 2 * trackingKappa A M * D_K
        + 2 * trackingChi A M * D_K + (S.ηstep : ℝ)
    have hb' : 2 * π * ((j : ℝ) + 1) = b := by dsimp [b]; ring
    rw [hb']
    calc
      |sol.z b i - xnext i|
          ≤ trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) + trackingChi A M * D_K := hz_b_pre
      _ ≤ 2 * trackingKappa A M * e + 2 * trackingKappa A M * D_K
          + 2 * trackingChi A M * D_K + (S.ηstep : ℝ) := by
            nlinarith [hκ_nonneg, hχD_nonneg, he0, hD_nonneg]
  · change |sol.u (2 * π * ((j : ℝ) + 1)) i - xnext i| ≤
      2 * trackingKappa A M * e + 2 * trackingKappa A M * D_K
        + 2 * trackingChi A M * D_K + (S.ηstep : ℝ)
    have hb' : 2 * π * ((j : ℝ) + 1) = b := by dsimp [b]; ring
    rw [hb']
    calc
      |sol.u b i - xnext i|
          ≤ trackingKappa A M * (e + trackingChi A M * D_K + D_K) +
            (trackingKappa A M * (e + D_K) + (S.ηstep : ℝ) + trackingChi A M * D_K) := hu_b_pre
      _ ≤ 2 * trackingKappa A M * e + 2 * trackingKappa A M * D_K
          + 2 * trackingChi A M * D_K + (S.ηstep : ℝ) := by
            nlinarith [hκ_le_one, hκ_nonneg, hχD_nonneg, he0, hD_nonneg]

/-- **P5, all-time tracking** (thm:all-time-tracking, cascade per
main.tex:879): under `2κ < 1`, `2κ D_K + 2χ D_K + ηstep ≤ η (1 − 2κ)`,
and `η + χ D_K ≤ r₀`, the iterator tracks the discrete orbit within
`η` at every sampling time, with no time horizon.  Induction over P4:
`e ≤ η ⟹ 2κη + 2κD + 2χD + ηstep ≤ 2κη + η(1−2κ) = η`. -/
theorem all_time_tracking_general
    {Conf : Type} [Primcodable Conf]
    (Mch : DiscreteMachine Conf) (d : ℕ) (E : LatticeEncoding Mch d)
    (S : RobustRealExtension Mch d E)
    (Fr : (Fin d → ℝ) → Fin d → ℝ)
    (hFrc : ∀ k : Fin d, Continuous fun x : Fin d → ℝ => Fr x k)
    (hsnapF : ∀ (c : Conf) (x : Fin d → ℝ),
      (∀ i, |x i - E.enc c i| ≤ (S.r₀ : ℝ)) →
      ∀ i, |Fr x i - E.enc (Mch.step c) i| ≤ (S.ηstep : ℝ))
    (A : ℝ) (hA : 0 < A) (M : ℕ) (w : ℕ)
    (sol : IteratorSol d Fr A M (orbitPoint Mch E w 0))
    (D_K : ℝ) (hD : 0 < D_K) (hbox : MovingBoxF Fr sol D_K)
    (η : ℝ) (hη : 0 < η)
    (hcasc₀ : 2 * trackingKappa A M < 1)
    (hcasc₁ : 2 * trackingKappa A M * D_K + 2 * trackingChi A M * D_K
        + (S.ηstep : ℝ) ≤ η * (1 - 2 * trackingKappa A M))
    (hcasc₂ : η + trackingChi A M * D_K ≤ (S.r₀ : ℝ)) :
    ∀ j : ℕ, ∀ i,
      |sol.z (2*π*j) i - orbitPoint Mch E w j i| ≤ η ∧
      |sol.u (2*π*j) i - orbitPoint Mch E w j i| ≤ η := by
  intro j
  induction j with
  | zero =>
    intro i
    have h0 : 2*π*((0:ℕ):ℝ) = 0 := by norm_num
    rw [h0, sol.init_z, sol.init_u]
    constructor <;> · rw [sub_self, abs_zero]; exact hη.le
  | succ k ih =>
    intro i
    have hrec := perturbation_recurrence_general Mch d E S Fr hFrc hsnapF A hA M w sol D_K hD hbox
      k η hη.le ih hcasc₂
    obtain ⟨hz, hu⟩ := hrec i
    have harith : 2 * trackingKappa A M * η + 2 * trackingKappa A M * D_K
        + 2 * trackingChi A M * D_K + (S.ηstep : ℝ) ≤ η := by
      nlinarith [hcasc₁]
    have hcast : ((k+1:ℕ):ℝ) = (k:ℝ) + 1 := by push_cast; ring
    rw [hcast]
    exact ⟨le_trans hz harith, le_trans hu harith⟩

end Ripple.BoundedUniversality.BGP
