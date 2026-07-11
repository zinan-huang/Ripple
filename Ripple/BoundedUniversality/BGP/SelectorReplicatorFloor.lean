import Mathlib.Analysis.Calculus.MeanValue
import Ripple.BoundedUniversality.BGP.SelectorReplicatorExistence

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorFloor
----------------------------------
Winner-weight floor for the simplex-replicator selector dynamics.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Set
open scoped BigOperators Topology

private theorem scalar_upper_barrier_exterior_on_Icc_from
    {a b wall : ℝ} (_hab : a ≤ b)
    (g gp : ℝ → ℝ)
    (hg0 : g a ≤ wall)
    (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ t : ℝ, t ∈ Ico a b → HasDerivWithinAt g (gp t) (Ici t) t)
    (hbar : ∀ t : ℝ, t ∈ Ico a b → wall ≤ g t → gp t ≤ 0) :
    ∀ t : ℝ, t ∈ Icc a b → g t ≤ wall := by
  intro t ht
  by_contra hnot
  have hgt : wall < g t := lt_of_not_ge hnot
  have ht_shift_one_pos : 0 < t - a + 1 := by linarith [ht.1]
  have hden_pos : 0 < 2 * (t - a + 1) :=
    mul_pos (by norm_num) ht_shift_one_pos
  let ε : ℝ := (g t - wall) / (2 * (t - a + 1))
  have hε : 0 < ε := by
    have hnum : 0 < g t - wall := sub_pos.mpr hgt
    exact div_pos hnum hden_pos
  have hε_bound : g t ≤ wall + ε * (t - a + 1) := by
    have hBcont : ContinuousOn (fun s : ℝ => wall + ε * (s - a + 1)) (Icc a b) := by
      fun_prop
    have hBderiv : ∀ s : ℝ, s ∈ Ico a b →
        HasDerivWithinAt (fun r : ℝ => wall + ε * (r - a + 1)) ε (Ici s) s := by
      intro s _hs
      have hbase : HasDerivAt (fun r : ℝ => r - a + 1) 1 s := by
        simpa using (((hasDerivAt_id s).sub_const a).add_const (1 : ℝ))
      have h : HasDerivAt (fun r : ℝ => wall + ε * (r - a + 1)) ε s := by
        simpa using (hbase.const_mul ε).const_add wall
      exact h.hasDerivWithinAt
    have hstart : g a ≤ wall + ε * (a - a + 1) := by
      have hwall_le : wall ≤ wall + ε := by linarith [le_of_lt hε]
      simpa using le_trans hg0 hwall_le
    have hstrict : ∀ s : ℝ, s ∈ Ico a b →
        g s = wall + ε * (s - a + 1) → gp s < ε := by
      intro s hs hcontact
      have hs_shift_one_pos : 0 < s - a + 1 := by linarith [hs.1]
      have hb_lt_g : wall < g s := by
        rw [hcontact]
        nlinarith [hε, hs_shift_one_pos]
      have hgp_nonpos : gp s ≤ 0 := hbar s hs (le_of_lt hb_lt_g)
      linarith
    exact image_le_of_deriv_right_lt_deriv_boundary'
      (f := g) (f' := gp) (a := a) (b := b)
      (B := fun s : ℝ => wall + ε * (s - a + 1)) (B' := fun _s : ℝ => ε)
      hcont hderiv hstart hBcont hBderiv hstrict ht
  have hmul : ε * (t - a + 1) = (g t - wall) / 2 := by
    have hden_ne : 2 * (t - a + 1) ≠ 0 := ne_of_gt hden_pos
    rw [show ε = (g t - wall) / (2 * (t - a + 1)) from rfl]
    field_simp [hden_ne]
  rw [hmul] at hε_bound
  nlinarith

private theorem scalar_lower_barrier_exterior_on_Icc_from
    {a b floor : ℝ} (hab : a ≤ b)
    (g gp : ℝ → ℝ)
    (hg0 : floor ≤ g a)
    (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ t : ℝ, t ∈ Ico a b → HasDerivWithinAt g (gp t) (Ici t) t)
    (hbar : ∀ t : ℝ, t ∈ Ico a b → g t ≤ floor → 0 ≤ gp t) :
    ∀ t : ℝ, t ∈ Icc a b → floor ≤ g t := by
  have hupper : ∀ t : ℝ, t ∈ Icc a b → -g t ≤ -floor := by
    exact scalar_upper_barrier_exterior_on_Icc_from
      (a := a) (b := b) (wall := -floor) hab
      (fun t : ℝ => -g t) (fun t : ℝ => -gp t)
      (by linarith)
      hcont.neg
      (fun t ht => (hderiv t ht).neg)
      (fun t ht hle => by
        have hg : g t ≤ floor := by linarith
        have hgp : 0 ≤ gp t := hbar t ht hg
        linarith)
  intro t ht
  have h := hupper t ht
  linarith

private theorem weighted_average_le_winner
    {V : Type} [Fintype V] [DecidableEq V]
    (lam P : V → ℝ) (vstar : V)
    (hsum : (∑ v : V, lam v) = 1)
    (hlam_nonneg : ∀ v : V, 0 ≤ lam v)
    (hgap : ∀ v : V, v ≠ vstar → P v - P vstar ≤ 0) :
    (∑ v : V, lam v * P v) ≤ P vstar := by
  classical
  calc
    (∑ v : V, lam v * P v)
        ≤ ∑ v : V, lam v * P vstar := by
          refine Finset.sum_le_sum ?_
          intro v _hv
          have hPv : P v ≤ P vstar := by
            by_cases hv : v = vstar
            · subst v
              rfl
            · linarith [hgap v hv]
          exact mul_le_mul_of_nonneg_left hPv (hlam_nonneg v)
    _ = (∑ v : V, lam v) * P vstar := by
          rw [Finset.sum_mul]
    _ = P vstar := by
          rw [hsum]
          ring

theorem replicator_winner_floor_on_interval
    {d B : ℕ} {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch
      chiReset chiGate kappa gain readoutP)
    (vstar : V) {a b : ℝ} (hab : a ≤ b)
    (hdom : ∀ t ∈ Icc a b, t ∈ sched.domain)
    (hcr_nonneg : ∀ t ∈ Icc a b, 0 ≤ chiReset t * kappa t)
    (hcg_nonneg : ∀ t ∈ Icc a b, 0 ≤ chiGate t * gain t)
    (hgap : ∀ v : V, v ≠ vstar → ∀ t ∈ Ico a b,
      readoutP v (sol.u t) - readoutP vstar (sol.u t) ≤ 0)
    (hsum : ∀ t ∈ Icc a b, (∑ v : V, sol.lam v t) = 1)
    (hlam_nonneg : ∀ v : V, ∀ t ∈ Icc a b, 0 ≤ sol.lam v t)
    (hinit : 1 / (Fintype.card V : ℝ) ≤ sol.lam vstar a) :
    ∀ t ∈ Icc a b,
      1 / (Fintype.card V : ℝ) ≤ sol.lam vstar t := by
  classical
  let floor : ℝ := 1 / (Fintype.card V : ℝ)
  let rhs : ℝ → ℝ := fun t =>
    chiReset t * kappa t * (floor - sol.lam vstar t)
      + chiGate t * gain t * sol.lam vstar t *
          (readoutP vstar (sol.u t) -
            ∑ w : V, sol.lam w t * readoutP w (sol.u t))
  have hcont : ContinuousOn (sol.lam vstar) (Icc a b) :=
    (sol.cont_lam vstar).continuousOn
  have hderiv : ∀ t : ℝ, t ∈ Ico a b →
      HasDerivWithinAt (sol.lam vstar) (rhs t) (Ici t) t := by
    intro t ht
    have htIcc : t ∈ Icc a b := Ico_subset_Icc_self ht
    simpa [rhs, floor, mul_assoc] using
      (sol.lam_hasDeriv vstar t (hdom t htIcc)).hasDerivWithinAt
  have hbar : ∀ t : ℝ, t ∈ Ico a b → sol.lam vstar t ≤ floor → 0 ≤ rhs t := by
    intro t ht hwall
    have htIcc : t ∈ Icc a b := Ico_subset_Icc_self ht
    have havg :
        (∑ w : V, sol.lam w t * readoutP w (sol.u t)) ≤
          readoutP vstar (sol.u t) :=
      weighted_average_le_winner
        (lam := fun w : V => sol.lam w t)
        (P := fun w : V => readoutP w (sol.u t))
        vstar
        (hsum t htIcc)
        (fun w => hlam_nonneg w t htIcc)
        (fun w hw => hgap w hw t ht)
    have hdiff_nonneg :
        0 ≤ readoutP vstar (sol.u t) -
          ∑ w : V, sol.lam w t * readoutP w (sol.u t) := by
      linarith
    have hreset_nonneg :
        0 ≤ chiReset t * kappa t * (floor - sol.lam vstar t) :=
      mul_nonneg (hcr_nonneg t htIcc) (sub_nonneg.mpr hwall)
    have hgate_nonneg :
        0 ≤ chiGate t * gain t * sol.lam vstar t *
          (readoutP vstar (sol.u t) -
            ∑ w : V, sol.lam w t * readoutP w (sol.u t)) :=
      mul_nonneg
        (mul_nonneg (hcg_nonneg t htIcc) (hlam_nonneg vstar t htIcc))
        hdiff_nonneg
    dsimp [rhs]
    exact add_nonneg hreset_nonneg hgate_nonneg
  have hfloor :=
    scalar_lower_barrier_exterior_on_Icc_from
      (a := a) (b := b) (floor := floor) hab
      (sol.lam vstar) rhs
      (by simpa [floor] using hinit)
      hcont hderiv hbar
  intro t ht
  simpa [floor] using hfloor t ht

theorem replicator_winner_floor_on_interval_param
    {d B : ℕ} {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch
      chiReset chiGate kappa gain readoutP)
    (vstar : V) {a b : ℝ} (hab : a ≤ b)
    (Lmin0 : ℝ) (hLmin0_le : Lmin0 ≤ 1 / (Fintype.card V : ℝ))
    (hdom : ∀ t ∈ Icc a b, t ∈ sched.domain)
    (hcr_nonneg : ∀ t ∈ Icc a b, 0 ≤ chiReset t * kappa t)
    (hcg_nonneg : ∀ t ∈ Icc a b, 0 ≤ chiGate t * gain t)
    (hgap : ∀ v : V, v ≠ vstar → ∀ t ∈ Ico a b,
      readoutP v (sol.u t) - readoutP vstar (sol.u t) ≤ 0)
    (hsum : ∀ t ∈ Icc a b, (∑ v : V, sol.lam v t) = 1)
    (hlam_nonneg : ∀ v : V, ∀ t ∈ Icc a b, 0 ≤ sol.lam v t)
    (hinit : Lmin0 ≤ sol.lam vstar a) :
    ∀ t ∈ Icc a b,
      Lmin0 ≤ sol.lam vstar t := by
  classical
  let invCard : ℝ := 1 / (Fintype.card V : ℝ)
  let rhs : ℝ → ℝ := fun t =>
    chiReset t * kappa t * (invCard - sol.lam vstar t)
      + chiGate t * gain t * sol.lam vstar t *
          (readoutP vstar (sol.u t) -
            ∑ w : V, sol.lam w t * readoutP w (sol.u t))
  have hcont : ContinuousOn (sol.lam vstar) (Icc a b) :=
    (sol.cont_lam vstar).continuousOn
  have hderiv : ∀ t : ℝ, t ∈ Ico a b →
      HasDerivWithinAt (sol.lam vstar) (rhs t) (Ici t) t := by
    intro t ht
    have htIcc : t ∈ Icc a b := Ico_subset_Icc_self ht
    simpa [rhs, invCard, mul_assoc] using
      (sol.lam_hasDeriv vstar t (hdom t htIcc)).hasDerivWithinAt
  have hbar : ∀ t : ℝ, t ∈ Ico a b → sol.lam vstar t ≤ Lmin0 → 0 ≤ rhs t := by
    intro t ht hwall
    have htIcc : t ∈ Icc a b := Ico_subset_Icc_self ht
    have havg :
        (∑ w : V, sol.lam w t * readoutP w (sol.u t)) ≤
          readoutP vstar (sol.u t) :=
      weighted_average_le_winner
        (lam := fun w : V => sol.lam w t)
        (P := fun w : V => readoutP w (sol.u t))
        vstar
        (hsum t htIcc)
        (fun w => hlam_nonneg w t htIcc)
        (fun w hw => hgap w hw t ht)
    have hdiff_nonneg :
        0 ≤ readoutP vstar (sol.u t) -
          ∑ w : V, sol.lam w t * readoutP w (sol.u t) := by
      linarith
    have hreset_nonneg :
        0 ≤ chiReset t * kappa t * (invCard - sol.lam vstar t) :=
      mul_nonneg (hcr_nonneg t htIcc)
        (sub_nonneg.mpr (le_trans hwall hLmin0_le))
    have hgate_nonneg :
        0 ≤ chiGate t * gain t * sol.lam vstar t *
          (readoutP vstar (sol.u t) -
            ∑ w : V, sol.lam w t * readoutP w (sol.u t)) :=
      mul_nonneg
        (mul_nonneg (hcg_nonneg t htIcc) (hlam_nonneg vstar t htIcc))
        hdiff_nonneg
    dsimp [rhs]
    exact add_nonneg hreset_nonneg hgate_nonneg
  exact
    scalar_lower_barrier_exterior_on_Icc_from
      (a := a) (b := b) (floor := Lmin0) hab
      (sol.lam vstar) rhs hinit hcont hderiv hbar

end Ripple.BoundedUniversality.BGP
