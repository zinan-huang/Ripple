import Ripple.BoundedUniversality.BGP.SelectorAprioriBound
import Ripple.BoundedUniversality.BGP.SelectorReplicator

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorConc
----------------------------------
Concentration estimates for the simplex-replicator selector weights.

This file is isolated from the assembled selector ODE.  It works with an
abstract family `lam : V → ℝ → ℝ` satisfying the replicator equation

  λ_v' = cr · (1/N - λ_v) + cg · λ_v · (P_v - φ),

where `φ = ∑_w λ_w P_w`.  The gate-window estimates below formalize the
ratio argument for losers against the selected branch `vstar`.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open Set

private theorem off_card_eq_sub_one {V : Type} [Fintype V] [DecidableEq V] (vstar : V) :
    ((Finset.univ.filter (fun v : V => v ≠ vstar)).card : ℝ) =
      (Fintype.card V : ℝ) - 1 := by
  have hset :
      Finset.univ.filter (fun v : V => v ≠ vstar) =
        (Finset.univ : Finset V).erase vstar := by
    ext v
    by_cases h : v = vstar <;> simp [h]
  have hcard :
      (Finset.univ.filter (fun v : V => v ≠ vstar)).card =
        Fintype.card V - 1 := by
    rw [hset, Finset.card_erase_of_mem (by simp : vstar ∈ (Finset.univ : Finset V))]
    rw [Finset.card_univ]
  rw [hcard]
  have hpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨vstar⟩
  norm_num [Nat.cast_sub hpos]

/-- The reset part in the quotient rule reduces to `(q - λ_v)/(N q²)`. -/
theorem replicator_reset_ratio_identity {V : Type} [Fintype V] [Nonempty V]
    {lv q : ℝ} (hq : q ≠ 0) :
    ((1 / (Fintype.card V : ℝ) - lv) * q
        - lv * (1 / (Fintype.card V : ℝ) - q)) / q ^ 2 =
      (q - lv) / ((Fintype.card V : ℝ) * q ^ 2) := by
  have hN : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast
      (ne_of_gt (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card V))
  field_simp [hq, hN]
  ring

/-- Quotient-rule ODE for a loser-to-winner replicator ratio.

For `q = λ_vstar`, `R_v = λ_v/q` satisfies
`R_v' = cg·(P_v - P_vstar)·R_v + cr·(q - λ_v)/(N q²)`.
-/
theorem replicator_ratio_deriv {V : Type} [Fintype V] [Nonempty V]
    (lam P : V → ℝ → ℝ) (cr cg : ℝ → ℝ) (vstar v : V) {t : ℝ}
    (hq : lam vstar t ≠ 0)
    (hode : ∀ w : V,
      HasDerivAt (lam w)
        (cr t * (1 / (Fintype.card V : ℝ) - lam w t)
          + cg t * lam w t *
              (P w t - ∑ u : V, lam u t * P u t)) t) :
    HasDerivAt (fun s : ℝ => lam v s / lam vstar s)
      (cg t * (P v t - P vstar t) * (lam v t / lam vstar t)
        + cr t * (lam vstar t - lam v t) /
            ((Fintype.card V : ℝ) * (lam vstar t) ^ 2)) t := by
  classical
  have hdiv := (hode v).div (hode vstar) hq
  convert hdiv using 1
  · field_simp [hq]
    ring

/-- Pointwise upper bound for the ratio RHS under the gate margin. -/
theorem replicator_ratio_deriv_le {V : Type} [Fintype V] [Nonempty V]
    {Lmin gap : ℝ} {lam P : V → ℝ → ℝ} {cr cg : ℝ → ℝ}
    {vstar v : V} {t : ℝ}
    (hLmin_pos : 0 < Lmin)
    (hqL : Lmin ≤ lam vstar t)
    (hlam_nonneg : 0 ≤ lam v t)
    (hcr_nonneg : 0 ≤ cr t)
    (hcg_nonneg : 0 ≤ cg t)
    (hgap : P v t - P vstar t ≤ -gap) :
    cg t * (P v t - P vstar t) * (lam v t / lam vstar t)
        + cr t * (lam vstar t - lam v t) /
            ((Fintype.card V : ℝ) * (lam vstar t) ^ 2)
      ≤ -gap * cg t * (lam v t / lam vstar t)
        + cr t / ((Fintype.card V : ℝ) * Lmin) := by
  have hq_pos : 0 < lam vstar t := lt_of_lt_of_le hLmin_pos hqL
  have hN_pos_nat : 0 < Fintype.card V :=
    Fintype.card_pos_iff.mpr inferInstance
  have hN_pos : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hN_pos_nat
  have hratio_nonneg : 0 ≤ lam v t / lam vstar t :=
    div_nonneg hlam_nonneg hq_pos.le
  have hgate :
      cg t * (P v t - P vstar t) * (lam v t / lam vstar t)
        ≤ -gap * cg t * (lam v t / lam vstar t) := by
    calc
      cg t * (P v t - P vstar t) * (lam v t / lam vstar t)
          ≤ cg t * (-gap) * (lam v t / lam vstar t) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hgap hcg_nonneg) hratio_nonneg
      _ = -gap * cg t * (lam v t / lam vstar t) := by ring
  have hreset_core :
      (lam vstar t - lam v t) /
          ((Fintype.card V : ℝ) * (lam vstar t) ^ 2)
        ≤ 1 / ((Fintype.card V : ℝ) * Lmin) := by
    have hnum : lam vstar t - lam v t ≤ lam vstar t := by linarith
    have hden_pos : 0 < (Fintype.card V : ℝ) * (lam vstar t) ^ 2 :=
      mul_pos hN_pos (sq_pos_of_ne_zero (ne_of_gt hq_pos))
    calc
      (lam vstar t - lam v t) /
          ((Fintype.card V : ℝ) * (lam vstar t) ^ 2)
          ≤ lam vstar t / ((Fintype.card V : ℝ) * (lam vstar t) ^ 2) := by
            exact div_le_div_of_nonneg_right hnum hden_pos.le
      _ = 1 / ((Fintype.card V : ℝ) * lam vstar t) := by
            field_simp [ne_of_gt hq_pos, ne_of_gt hN_pos]
      _ ≤ 1 / ((Fintype.card V : ℝ) * Lmin) := by
            have hmul : (Fintype.card V : ℝ) * Lmin ≤
                (Fintype.card V : ℝ) * lam vstar t :=
              mul_le_mul_of_nonneg_left hqL hN_pos.le
            exact one_div_le_one_div_of_le
              (mul_pos hN_pos hLmin_pos) hmul
  have hreset :
      cr t * (lam vstar t - lam v t) /
          ((Fintype.card V : ℝ) * (lam vstar t) ^ 2)
        ≤ cr t / ((Fintype.card V : ℝ) * Lmin) := by
    calc
      cr t * (lam vstar t - lam v t) /
          ((Fintype.card V : ℝ) * (lam vstar t) ^ 2)
          = cr t * ((lam vstar t - lam v t) /
              ((Fintype.card V : ℝ) * (lam vstar t) ^ 2)) := by ring
      _ ≤ cr t * (1 / ((Fintype.card V : ℝ) * Lmin)) :=
          mul_le_mul_of_nonneg_left hreset_core hcr_nonneg
      _ = cr t / ((Fintype.card V : ℝ) * Lmin) := by ring
  linarith [hgate, hreset]

/-- Derivative of the aggregate mass on an arbitrary finite bad set. -/
theorem replicator_badMass_deriv {V : Type} [Fintype V] [Nonempty V]
    (lam P : V → ℝ → ℝ) (cr cg : ℝ → ℝ) (bad : Finset V) {t : ℝ}
    (hode : ∀ w : V,
      HasDerivAt (lam w)
        (cr t * (1 / (Fintype.card V : ℝ) - lam w t)
          + cg t * lam w t *
              (P w t - ∑ u : V, lam u t * P u t)) t) :
    HasDerivAt (fun s : ℝ => bad.sum (fun v => lam v s))
      (bad.sum fun v =>
        cr t * (1 / (Fintype.card V : ℝ) - lam v t)
          + cg t * lam v t *
              (P v t - ∑ u : V, lam u t * P u t)) t := by
  simpa using HasDerivAt.fun_sum (u := bad) (fun v _hv => hode v)

/-- Pointwise RHS bound for aggregate bad mass under a direct payoff gap.

This is the algebraic core needed for a two-safe bad-mass Duhamel comparison:
the gate term damps the bad mass, while reset injects at rate at most
`cr * bad.card / |V|`. -/
theorem replicator_badMass_rhs_le {V : Type} [Fintype V] [Nonempty V]
    {lam P : V → ℝ → ℝ} {cr cg : ℝ → ℝ} {bad : Finset V}
    {t gap : ℝ}
    (hlam_nonneg : ∀ v ∈ bad, 0 ≤ lam v t)
    (hcr_nonneg : 0 ≤ cr t)
    (hcg_nonneg : 0 ≤ cg t)
    (hgap : ∀ v ∈ bad,
      P v t - ∑ u : V, lam u t * P u t ≤ -gap) :
    (bad.sum fun v =>
        cr t * (1 / (Fintype.card V : ℝ) - lam v t)
          + cg t * lam v t *
              (P v t - ∑ u : V, lam u t * P u t))
      ≤
        -gap * cg t * bad.sum (fun v => lam v t)
          + cr t * ((bad.card : ℝ) / (Fintype.card V : ℝ)) := by
  classical
  let N : ℝ := Fintype.card V
  let phi : ℝ := ∑ u : V, lam u t * P u t
  have hreset :
      (bad.sum fun v => cr t * (1 / N - lam v t))
        ≤ bad.sum (fun _v => cr t * (1 / N)) := by
    refine Finset.sum_le_sum ?_
    intro v hv
    exact mul_le_mul_of_nonneg_left (by linarith [hlam_nonneg v hv]) hcr_nonneg
  have hgate :
      (bad.sum fun v => cg t * lam v t * (P v t - phi))
        ≤ bad.sum (fun v => -gap * cg t * lam v t) := by
    refine Finset.sum_le_sum ?_
    intro v hv
    have hcoef_nonneg : 0 ≤ cg t * lam v t :=
      mul_nonneg hcg_nonneg (hlam_nonneg v hv)
    have hmul := mul_le_mul_of_nonneg_left (hgap v hv) hcoef_nonneg
    dsimp [phi] at hmul ⊢
    calc
      cg t * lam v t * (P v t - ∑ u : V, lam u t * P u t)
          = (cg t * lam v t) * (P v t - ∑ u : V, lam u t * P u t) := by ring
      _ ≤ (cg t * lam v t) * (-gap) := hmul
      _ = -gap * cg t * lam v t := by ring
  calc
    (bad.sum fun v =>
        cr t * (1 / (Fintype.card V : ℝ) - lam v t)
          + cg t * lam v t *
              (P v t - ∑ u : V, lam u t * P u t))
        =
      (bad.sum fun v => cr t * (1 / N - lam v t)) +
        (bad.sum fun v => cg t * lam v t * (P v t - phi)) := by
          simp [N, phi, Finset.sum_add_distrib]
    _ ≤ bad.sum (fun _v => cr t * (1 / N)) +
        bad.sum (fun v => -gap * cg t * lam v t) :=
          add_le_add hreset hgate
    _ =
        -gap * cg t * bad.sum (fun v => lam v t)
          + cr t * ((bad.card : ℝ) / (Fintype.card V : ℝ)) := by
          have hgate_sum :
              bad.sum (fun v => gap * cg t * lam v t) =
                gap * cg t * bad.sum (fun v => lam v t) := by
            rw [Finset.mul_sum]
          simp [N, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
          rw [hgate_sum]
          ring

private lemma sum_univ_filter_not_mem_add_sum
    {V : Type} [Fintype V] [DecidableEq V]
    (safe : Finset V) (f : V → ℝ) :
    (∑ v : V, f v) =
      (Finset.univ.filter (fun v : V => v ∉ safe)).sum f + safe.sum f := by
  classical
  let bad : Finset V := Finset.univ.filter (fun v : V => v ∉ safe)
  have hdisj : Disjoint bad safe := by
    rw [Finset.disjoint_left]
    intro v hv hsafe
    have hvnot : v ∉ safe := by
      simpa [bad] using hv
    exact hvnot hsafe
  have hcover : bad ∪ safe = (Finset.univ : Finset V) := by
    ext v
    by_cases hv : v ∈ safe
    · simp [bad, hv]
    · simp [bad, hv]
  calc
    (∑ v : V, f v) = (bad ∪ safe).sum f := by rw [hcover]
    _ = bad.sum f + safe.sum f := by rw [Finset.sum_union hdisj]

/-- Gate contribution for mass outside a safe set under pairwise safe dominance. -/
theorem badMass_gate_term_le_pairwise_safe_gap
    {V : Type} [Fintype V] [DecidableEq V]
    (lam P : V → ℝ) (safe : Finset V) {gap : ℝ}
    (hlam_nonneg : ∀ v, 0 ≤ lam v)
    (hsum : (∑ v : V, lam v) = 1)
    (hgap : ∀ v : V, v ∉ safe → ∀ u : V, u ∈ safe → P v - P u ≤ -gap) :
    let bad : Finset V := Finset.univ.filter (fun v : V => v ∉ safe)
    let phi : ℝ := ∑ u : V, lam u * P u
    (bad.sum fun v => lam v * (P v - phi)) ≤
      -gap * (bad.sum fun v => lam v) * (safe.sum fun u => lam u) := by
  classical
  let bad : Finset V := Finset.univ.filter (fun v : V => v ∉ safe)
  let phi : ℝ := ∑ u : V, lam u * P u
  change (bad.sum fun v => lam v * (P v - phi)) ≤
    -gap * (bad.sum fun v => lam v) * (safe.sum fun u => lam u)
  let B : ℝ := bad.sum fun v => lam v
  let S : ℝ := safe.sum fun u => lam u
  let BP : ℝ := bad.sum fun v => lam v * P v
  let SP : ℝ := safe.sum fun u => lam u * P u
  let D : ℝ := bad.sum fun v => safe.sum fun u => lam v * lam u * (P v - P u)
  have hsplit (f : V → ℝ) :
      (∑ v : V, f v) = bad.sum f + safe.sum f := by
    simpa [bad] using (sum_univ_filter_not_mem_add_sum (V := V) safe f)
  have hmass : B + S = 1 := by
    calc
      B + S = (∑ v : V, lam v) := by
        simpa [B, S] using (hsplit lam).symm
      _ = 1 := hsum
  have hphi : phi = BP + SP := by
    simpa [phi, BP, SP] using (hsplit (fun u : V => lam u * P u))
  have hleft_lin :
      (bad.sum fun v => lam v * (P v - phi)) = BP - B * phi := by
    calc
      (bad.sum fun v => lam v * (P v - phi))
          = bad.sum (fun v => lam v * P v - lam v * phi) := by
              refine Finset.sum_congr rfl ?_
              intro v hv
              ring
      _ = bad.sum (fun v => lam v * P v) - bad.sum (fun v => lam v * phi) := by
              rw [Finset.sum_sub_distrib]
      _ = BP - B * phi := by
              rw [← Finset.sum_mul]
  have hleft_eq :
      (bad.sum fun v => lam v * (P v - phi)) = BP * S - B * SP := by
    calc
      (bad.sum fun v => lam v * (P v - phi)) = BP - B * phi := hleft_lin
      _ = BP - B * (BP + SP) := by rw [hphi]
      _ = BP * S - B * SP := by
            have hS : S = 1 - B := by
              rw [← hmass]
              ring
            rw [hS]
            ring
  have hinner (v : V) :
      safe.sum (fun u => lam v * lam u * (P v - P u)) =
        (lam v * P v) * S - lam v * SP := by
    calc
      safe.sum (fun u => lam v * lam u * (P v - P u))
          = safe.sum (fun u => (lam v * P v) * lam u - lam v * (lam u * P u)) := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              ring
      _ = safe.sum (fun u => (lam v * P v) * lam u) -
            safe.sum (fun u => lam v * (lam u * P u)) := by
            rw [Finset.sum_sub_distrib]
      _ = (lam v * P v) * S - lam v * SP := by
              rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hdouble_eq : D = BP * S - B * SP := by
    calc
      D = bad.sum (fun v => safe.sum (fun u => lam v * lam u * (P v - P u))) := by
            rfl
      _ = bad.sum (fun v => (lam v * P v) * S - lam v * SP) := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            exact hinner v
      _ = bad.sum (fun v => (lam v * P v) * S) -
            bad.sum (fun v => lam v * SP) := by
            rw [Finset.sum_sub_distrib]
      _ = BP * S - B * SP := by
            rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hconst :
      (bad.sum fun v => safe.sum fun u => lam v * lam u * (-gap)) = -gap * B * S := by
    calc
      (bad.sum fun v => safe.sum fun u => lam v * lam u * (-gap))
          = bad.sum (fun v => lam v * (safe.sum fun u => lam u * (-gap))) := by
              refine Finset.sum_congr rfl ?_
              intro v hv
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro u hu
              ring
      _ = bad.sum (fun v => lam v * (S * (-gap))) := by
              refine Finset.sum_congr rfl ?_
              intro v hv
              rw [← Finset.sum_mul]
      _ = B * (S * (-gap)) := by
              rw [← Finset.sum_mul]
      _ = -gap * B * S := by ring
  have hD_le : D ≤ -gap * B * S := by
    calc
      D = bad.sum (fun v => safe.sum fun u => lam v * lam u * (P v - P u)) := by
            rfl
      _ ≤ bad.sum (fun v => safe.sum fun u => lam v * lam u * (-gap)) := by
            refine Finset.sum_le_sum ?_
            intro v hv
            refine Finset.sum_le_sum ?_
            intro u hu
            have hvbad : v ∉ safe := by
              simpa [bad] using hv
            have hnonneg : 0 ≤ lam v * lam u :=
              mul_nonneg (hlam_nonneg v) (hlam_nonneg u)
            exact mul_le_mul_of_nonneg_left (hgap v hvbad u hu) hnonneg
      _ = -gap * B * S := hconst
  have hmain : (bad.sum fun v => lam v * (P v - phi)) ≤ -gap * B * S := by
    calc
      (bad.sum fun v => lam v * (P v - phi)) = BP * S - B * SP := hleft_eq
      _ = D := hdouble_eq.symm
      _ ≤ -gap * B * S := hD_le
  simpa [B, S] using hmain

/-- Pointwise RHS bound for bad mass from pairwise safe dominance and a safe
mass floor. -/
theorem replicator_badMass_rhs_le_pairwise_safe_floor
    {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    {lam P : V → ℝ → ℝ} {cr cg : ℝ → ℝ} {safe : Finset V}
    {t gap Lsafe : ℝ}
    (hsum : (∑ v : V, lam v t) = 1)
    (hlam_nonneg : ∀ v : V, 0 ≤ lam v t)
    (hcr_nonneg : 0 ≤ cr t)
    (hcg_nonneg : 0 ≤ cg t)
    (hgap_nonneg : 0 ≤ gap)
    (hsafe_floor : Lsafe ≤ safe.sum (fun u => lam u t))
    (hgap : ∀ v : V, v ∉ safe → ∀ u : V, u ∈ safe →
      P v t - P u t ≤ -gap) :
    let bad : Finset V := Finset.univ.filter (fun v : V => v ∉ safe)
    (bad.sum fun v =>
        cr t * (1 / (Fintype.card V : ℝ) - lam v t)
          + cg t * lam v t *
              (P v t - ∑ u : V, lam u t * P u t))
      ≤
        -(gap * Lsafe) * cg t * bad.sum (fun v => lam v t)
          + cr t * ((bad.card : ℝ) / (Fintype.card V : ℝ)) := by
  classical
  let bad : Finset V := Finset.univ.filter (fun v : V => v ∉ safe)
  let B : ℝ := bad.sum fun v => lam v t
  let S : ℝ := safe.sum fun u => lam u t
  let phi : ℝ := ∑ u : V, lam u t * P u t
  let N : ℝ := Fintype.card V
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg (fun v _hv => hlam_nonneg v)
  have hreset :
      (bad.sum fun v => cr t * (1 / N - lam v t))
        ≤ bad.sum (fun _v => cr t * (1 / N)) := by
    refine Finset.sum_le_sum ?_
    intro v hv
    exact mul_le_mul_of_nonneg_left (by linarith [hlam_nonneg v]) hcr_nonneg
  have hgate_core :
      bad.sum (fun v => lam v t * (P v t - phi)) ≤ -gap * B * S := by
    simpa [bad, B, S, phi] using
      (badMass_gate_term_le_pairwise_safe_gap
        (lam := fun v : V => lam v t) (P := fun v : V => P v t)
        safe hlam_nonneg hsum hgap)
  have hgate :
      (bad.sum fun v => cg t * lam v t * (P v t - phi))
        ≤ -(gap * Lsafe) * cg t * B := by
    have hgate_sum :
        (bad.sum fun v => cg t * lam v t * (P v t - phi))
          = cg t * bad.sum (fun v => lam v t * (P v t - phi)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro v hv
      ring
    have hmul :=
      mul_le_mul_of_nonneg_left hgate_core hcg_nonneg
    have hfloor_mul : gap * B * Lsafe ≤ gap * B * S := by
      exact mul_le_mul_of_nonneg_left hsafe_floor
        (mul_nonneg hgap_nonneg hB_nonneg)
    have hcg_floor : cg t * (gap * B * Lsafe) ≤ cg t * (gap * B * S) :=
      mul_le_mul_of_nonneg_left hfloor_mul hcg_nonneg
    calc
      bad.sum (fun v => cg t * lam v t * (P v t - phi))
          = cg t * bad.sum (fun v => lam v t * (P v t - phi)) := hgate_sum
      _ ≤ cg t * (-gap * B * S) := hmul
      _ = -(cg t * (gap * B * S)) := by ring
      _ ≤ -(cg t * (gap * B * Lsafe)) := neg_le_neg hcg_floor
      _ = -(gap * Lsafe) * cg t * B := by ring
  calc
    (bad.sum fun v =>
        cr t * (1 / (Fintype.card V : ℝ) - lam v t)
          + cg t * lam v t *
              (P v t - ∑ u : V, lam u t * P u t))
        =
      (bad.sum fun v => cr t * (1 / N - lam v t)) +
        (bad.sum fun v => cg t * lam v t * (P v t - phi)) := by
          simp [N, phi, Finset.sum_add_distrib]
    _ ≤ bad.sum (fun _v => cr t * (1 / N)) + (-(gap * Lsafe) * cg t * B) :=
          add_le_add hreset hgate
    _ =
        -(gap * Lsafe) * cg t * bad.sum (fun v => lam v t)
          + cr t * ((bad.card : ℝ) / (Fintype.card V : ℝ)) := by
          simp [N, B, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
          ring

/-- Local derivative inequality for aggregate bad mass outside a safe finite
set, under pairwise safe dominance and a safe-mass floor. -/
theorem replicator_badMass_hasDeriv_le_pairwise_safe_floor
    {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (lam P : V → ℝ → ℝ) (cr cg : ℝ → ℝ) (safe : Finset V)
    {t gap Lsafe : ℝ}
    (hode : ∀ w : V,
      HasDerivAt (lam w)
        (cr t * (1 / (Fintype.card V : ℝ) - lam w t)
          + cg t * lam w t *
              (P w t - ∑ u : V, lam u t * P u t)) t)
    (hsum : (∑ v : V, lam v t) = 1)
    (hlam_nonneg : ∀ v : V, 0 ≤ lam v t)
    (hcr_nonneg : 0 ≤ cr t)
    (hcg_nonneg : 0 ≤ cg t)
    (hgap_nonneg : 0 ≤ gap)
    (hsafe_floor : Lsafe ≤ safe.sum (fun u => lam u t))
    (hgap : ∀ v : V, v ∉ safe → ∀ u : V, u ∈ safe →
      P v t - P u t ≤ -gap) :
    let bad : Finset V := Finset.univ.filter (fun v : V => v ∉ safe)
    ∃ dB : ℝ,
      HasDerivAt (fun s : ℝ => bad.sum (fun v => lam v s)) dB t ∧
        dB ≤
          -(gap * Lsafe) * cg t * bad.sum (fun v => lam v t)
            + cr t * ((bad.card : ℝ) / (Fintype.card V : ℝ)) := by
  classical
  let bad : Finset V := Finset.univ.filter (fun v : V => v ∉ safe)
  let dB : ℝ :=
    bad.sum fun v =>
      cr t * (1 / (Fintype.card V : ℝ) - lam v t)
        + cg t * lam v t *
            (P v t - ∑ u : V, lam u t * P u t)
  refine ⟨dB, ?_, ?_⟩
  · dsimp [dB]
    exact replicator_badMass_deriv (lam := lam) (P := P) (cr := cr) (cg := cg)
      (bad := bad) hode
  · dsimp [dB]
    simpa [bad] using
      (replicator_badMass_rhs_le_pairwise_safe_floor
        (lam := lam) (P := P) (cr := cr) (cg := cg) (safe := safe)
        (t := t) (gap := gap) (Lsafe := Lsafe)
        hsum hlam_nonneg hcr_nonneg hcg_nonneg hgap_nonneg hsafe_floor hgap)

/-- Gate-window ratio bound from the integrating-factor comparison.

The integrating-factor variable is
`Q t = exp(gap·(G t - G a)) · (λ_v t / λ_vstar t)`.  The comparison step uses
Mathlib's `image_le_of_deriv_right_le_deriv_boundary`, the same derivative-boundary
engine used in `SelectorAprioriBound.nonneg_of_linear_inhomogeneous_on_Ico`.
-/
theorem replicator_ratio_bound {V : Type} [Fintype V] [Nonempty V]
    (lam P : V → ℝ → ℝ) (cr cg G : ℝ → ℝ) (vstar v : V)
    {a b Lmin gap R0 Kreset : ℝ}
    (hab : a ≤ b)
    (hLmin_pos : 0 < Lmin)
    (hGcont : Continuous G)
    (hcr_cont : Continuous cr)
    (hlam_cont : ∀ w : V, ContinuousOn (lam w) (Icc a b))
    (hode : ∀ w : V, ∀ t ∈ Ico a b,
      HasDerivAt (lam w)
        (cr t * (1 / (Fintype.card V : ℝ) - lam w t)
          + cg t * lam w t *
              (P w t - ∑ u : V, lam u t * P u t)) t)
    (hGder : ∀ t ∈ Ico a b, HasDerivWithinAt G (cg t) (Ici t) t)
    (hqL : ∀ t ∈ Icc a b, Lmin ≤ lam vstar t)
    (hlam_nonneg : ∀ w : V, ∀ t ∈ Icc a b, 0 ≤ lam w t)
    (hcr_nonneg : ∀ t ∈ Ico a b, 0 ≤ cr t)
    (hcg_nonneg : ∀ t ∈ Ico a b, 0 ≤ cg t)
    (hgap : ∀ t ∈ Ico a b, P v t - P vstar t ≤ -gap)
    (hRa : lam v a / lam vstar a ≤ R0)
    (hKreset : (∫ t in a..b, Real.exp (gap * (G t - G a)) * cr t) ≤ Kreset) :
    lam v b / lam vstar b ≤
      (R0 + Kreset / ((Fintype.card V : ℝ) * Lmin))
        * Real.exp (-gap * (G b - G a)) := by
  classical
  let E : ℝ → ℝ := fun t => Real.exp (gap * (G t - G a))
  let R : ℝ → ℝ := fun t => lam v t / lam vstar t
  let Q : ℝ → ℝ := fun t => R t * E t
  let B : ℝ → ℝ :=
    fun t => R0 + (1 / ((Fintype.card V : ℝ) * Lmin)) *
      ∫ s in a..t, E s * cr s
  have hN_pos_nat : 0 < Fintype.card V :=
    Fintype.card_pos_iff.mpr inferInstance
  have hN_pos : 0 < (Fintype.card V : ℝ) := by exact_mod_cast hN_pos_nat
  have hcoef_nonneg : 0 ≤ 1 / ((Fintype.card V : ℝ) * Lmin) :=
    one_div_nonneg.mpr (mul_pos hN_pos hLmin_pos).le
  have hEcont : Continuous E := by
    dsimp [E]
    fun_prop
  have hEcr_cont : Continuous (fun t => E t * cr t) := hEcont.mul hcr_cont
  have hQcont : ContinuousOn Q (Icc a b) := by
    dsimp [Q, R]
    refine ContinuousOn.mul ?_ hEcont.continuousOn
    exact (hlam_cont v).div (hlam_cont vstar) (fun t ht hzero => by
      have hqpos : 0 < lam vstar t := lt_of_lt_of_le hLmin_pos (hqL t ht)
      exact (ne_of_gt hqpos) hzero)
  have hBcont : ContinuousOn B (Icc a b) := by
    have hprim : Continuous (fun u => ∫ s in a..u, E s * cr s) :=
      continuous_iff_continuousAt.mpr fun t =>
        (intervalIntegral.integral_hasDerivAt_right
          (hEcr_cont.intervalIntegrable a t)
          (hEcr_cont.stronglyMeasurableAtFilter _ _) hEcr_cont.continuousAt).continuousAt
    dsimp [B]
    exact (continuous_const.add (continuous_const.mul hprim)).continuousOn
  have hEder : ∀ t ∈ Ico a b,
      HasDerivWithinAt E (E t * (gap * cg t)) (Ici t) t := by
    intro t ht
    have h := (((hGder t ht).sub_const (G a)).const_mul gap).exp
    simpa [E, mul_comm, mul_left_comm, mul_assoc] using h
  have hRder : ∀ t ∈ Ico a b,
      HasDerivWithinAt R
        (cg t * (P v t - P vstar t) * R t
          + cr t * (lam vstar t - lam v t) /
              ((Fintype.card V : ℝ) * (lam vstar t) ^ 2)) (Ici t) t := by
    intro t ht
    have htc : t ∈ Icc a b := Ico_subset_Icc_self ht
    have hq : lam vstar t ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le hLmin_pos (hqL t htc))
    exact (replicator_ratio_deriv lam P cr cg vstar v hq
      (fun w => hode w t ht)).hasDerivWithinAt
  have hQder : ∀ t ∈ Ico a b,
      HasDerivWithinAt Q
        ((cg t * (P v t - P vstar t) * R t
            + cr t * (lam vstar t - lam v t) /
                ((Fintype.card V : ℝ) * (lam vstar t) ^ 2)) * E t
          + R t * (E t * (gap * cg t))) (Ici t) t := by
    intro t ht
    exact (hRder t ht).mul (hEder t ht)
  have hBder : ∀ t ∈ Ico a b,
      HasDerivWithinAt B ((1 / ((Fintype.card V : ℝ) * Lmin)) * (E t * cr t))
        (Ici t) t := by
    intro t ht
    have hftc : HasDerivAt (fun u => ∫ s in a..u, E s * cr s) (E t * cr t) t :=
      intervalIntegral.integral_hasDerivAt_right
        (hEcr_cont.intervalIntegrable a t)
        (hEcr_cont.stronglyMeasurableAtFilter _ _) hEcr_cont.continuousAt
    exact ((hftc.const_mul (1 / ((Fintype.card V : ℝ) * Lmin))).const_add R0).hasDerivWithinAt
  have hder_le : ∀ t ∈ Ico a b,
      (cg t * (P v t - P vstar t) * R t
            + cr t * (lam vstar t - lam v t) /
                ((Fintype.card V : ℝ) * (lam vstar t) ^ 2)) * E t
          + R t * (E t * (gap * cg t))
        ≤ (1 / ((Fintype.card V : ℝ) * Lmin)) * (E t * cr t) := by
    intro t ht
    have htc : t ∈ Icc a b := Ico_subset_Icc_self ht
    have hRrhs := replicator_ratio_deriv_le (V := V)
      (Lmin := Lmin) (gap := gap) (lam := lam) (P := P) (cr := cr) (cg := cg)
      (vstar := vstar) (v := v) (t := t)
      hLmin_pos (hqL t htc) (hlam_nonneg v t htc) (hcr_nonneg t ht)
      (hcg_nonneg t ht) (hgap t ht)
    have hEpos : 0 < E t := Real.exp_pos _
    have hadd :
        (cg t * (P v t - P vstar t) * (lam v t / lam vstar t)
            + cr t * (lam vstar t - lam v t) /
                ((Fintype.card V : ℝ) * (lam vstar t) ^ 2))
          + gap * cg t * (lam v t / lam vstar t)
        ≤ cr t / ((Fintype.card V : ℝ) * Lmin) := by
      linarith [hRrhs]
    have hmul := mul_le_mul_of_nonneg_right hadd hEpos.le
    dsimp [R] at hmul ⊢
    calc
      (cg t * (P v t - P vstar t) * (lam v t / lam vstar t)
            + cr t * (lam vstar t - lam v t) /
                ((Fintype.card V : ℝ) * (lam vstar t) ^ 2)) * E t
          + (lam v t / lam vstar t) * (E t * (gap * cg t))
          = ((cg t * (P v t - P vstar t) * (lam v t / lam vstar t)
            + cr t * (lam vstar t - lam v t) /
                ((Fintype.card V : ℝ) * (lam vstar t) ^ 2))
              + gap * cg t * (lam v t / lam vstar t)) * E t := by ring
      _ ≤ (cr t / ((Fintype.card V : ℝ) * Lmin)) * E t := by
            exact hmul
      _ = (1 / ((Fintype.card V : ℝ) * Lmin)) * (E t * cr t) := by ring
  have hQa : Q a ≤ B a := by
    dsimp [Q, R, B, E]
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
    simpa using hRa
  have hQB : ∀ x, x ∈ Icc a b → Q x ≤ B x :=
    image_le_of_deriv_right_le_deriv_boundary
      hQcont hQder hQa hBcont hBder hder_le
  have hQb : Q b ≤ B b := hQB b (right_mem_Icc.mpr hab)
  have hB_le :
      B b ≤ R0 + Kreset / ((Fintype.card V : ℝ) * Lmin) := by
    dsimp [B]
    have hmul := mul_le_mul_of_nonneg_left hKreset hcoef_nonneg
    calc
      R0 + (1 / ((Fintype.card V : ℝ) * Lmin)) *
          ∫ s in a..b, E s * cr s
          ≤ R0 + (1 / ((Fintype.card V : ℝ) * Lmin)) * Kreset :=
            by linarith [hmul]
      _ = R0 + Kreset / ((Fintype.card V : ℝ) * Lmin) := by ring
  have hQb_le :
      (lam v b / lam vstar b) * E b
        ≤ R0 + Kreset / ((Fintype.card V : ℝ) * Lmin) := by
    exact le_trans hQb hB_le
  have hEpos_b : 0 < E b := Real.exp_pos _
  have hdiv := (le_div_iff₀ hEpos_b).mpr hQb_le
  dsimp [E] at hdiv ⊢
  rw [show -gap * (G b - G a) = -(gap * (G b - G a)) by ring, Real.exp_neg]
  simpa [div_eq_mul_inv] using hdiv

/-- Sum of loser masses from pointwise loser-ratio bounds. -/
theorem replicator_loser_mass_bound {V : Type} [Fintype V] [DecidableEq V]
    (lam : V → ℝ → ℝ) (vstar : V) {b eps : ℝ}
    (hsum : (∑ w : V, lam w b) = 1)
    (hlam_nonneg : ∀ w : V, 0 ≤ lam w b)
    (hq_pos : 0 < lam vstar b)
    (hratio : ∀ v : V, v ≠ vstar → lam v b / lam vstar b ≤ eps) :
    (Finset.univ.filter (fun v : V => v ≠ vstar)).sum (fun v => lam v b)
      ≤ ((Fintype.card V : ℝ) - 1) * eps := by
  classical
  have hq_le_one : lam vstar b ≤ 1 := by
    have hle_sum : lam vstar b ≤ ∑ w : V, lam w b :=
      Finset.single_le_sum (fun w _ => hlam_nonneg w) (Finset.mem_univ vstar)
    simpa [hsum] using hle_sum
  have hterm : ∀ v ∈ Finset.univ.filter (fun v : V => v ≠ vstar), lam v b ≤ eps := by
    intro v hv
    have hvne : v ≠ vstar := (Finset.mem_filter.mp hv).2
    have hratio_nonneg : 0 ≤ lam v b / lam vstar b :=
      div_nonneg (hlam_nonneg v) hq_pos.le
    have hmul : lam v b ≤ lam v b / lam vstar b := by
      calc
        lam v b = lam vstar b * (lam v b / lam vstar b) := by
          field_simp [ne_of_gt hq_pos]
        _ ≤ 1 * (lam v b / lam vstar b) :=
          mul_le_mul hq_le_one le_rfl hratio_nonneg (by norm_num)
        _ = lam v b / lam vstar b := by ring
    exact hmul.trans (hratio v hvne)
  calc
    (Finset.univ.filter (fun v : V => v ≠ vstar)).sum (fun v => lam v b)
        ≤ (Finset.univ.filter (fun v : V => v ≠ vstar)).sum (fun _ => eps) :=
          Finset.sum_le_sum hterm
    _ = ((Finset.univ.filter (fun v : V => v ≠ vstar)).card : ℝ) * eps := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((Fintype.card V : ℝ) - 1) * eps := by
          rw [off_card_eq_sub_one vstar]

/-- Branch-mixture error from a loser-mass bound and a branch spread bound. -/
theorem replicator_mix_error_of_loser_mass {V : Type} [Fintype V] [DecidableEq V]
    (vstar : V) (lam A : V → ℝ) {Rspread loserBound : ℝ}
    (hRspread_nonneg : 0 ≤ Rspread)
    (hsum : (∑ v : V, lam v) = 1)
    (hlam_nonneg : ∀ v : V, 0 ≤ lam v)
    (hspread : ∀ v : V, v ≠ vstar → |A v - A vstar| ≤ Rspread)
    (hloser :
      (Finset.univ.filter (fun v : V => v ≠ vstar)).sum (fun v => lam v)
        ≤ loserBound) :
    |(∑ v : V, lam v * A v) - A vstar| ≤ Rspread * loserBound := by
  classical
  have hrewrite :
      (∑ v : V, lam v * A v) - A vstar =
        ∑ v : V, lam v * (A v - A vstar) := by
    calc
      (∑ v : V, lam v * A v) - A vstar
          = (∑ v : V, lam v * A v) - (∑ v : V, lam v) * A vstar := by
              rw [hsum]
              ring
      _ = ∑ v : V, lam v * (A v - A vstar) := by
              rw [Finset.sum_mul]
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro v _
              ring
  have hdrop :
      (∑ v : V, lam v * (A v - A vstar)) =
        (Finset.univ.erase vstar).sum (fun v => lam v * (A v - A vstar)) := by
    rw [← Finset.add_sum_erase _ (fun v => lam v * (A v - A vstar))
      (Finset.mem_univ vstar)]
    simp
  have hfilter :
      (Finset.univ.erase vstar).sum (fun v => lam v * (A v - A vstar)) =
        (Finset.univ.filter (fun v : V => v ≠ vstar)).sum
          (fun v => lam v * (A v - A vstar)) := by
    have hset :
        Finset.univ.filter (fun v : V => v ≠ vstar) =
          (Finset.univ : Finset V).erase vstar := by
      ext v
      by_cases h : v = vstar <;> simp [h]
    rw [hset]
  rw [hrewrite, hdrop, hfilter]
  calc
    |(Finset.univ.filter (fun v : V => v ≠ vstar)).sum
        (fun v => lam v * (A v - A vstar))|
        ≤ (Finset.univ.filter (fun v : V => v ≠ vstar)).sum
            (fun v => |lam v * (A v - A vstar)|) :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Finset.univ.filter (fun v : V => v ≠ vstar)).sum
            (fun v => lam v * Rspread) := by
          refine Finset.sum_le_sum ?_
          intro v hv
          have hvne : v ≠ vstar := (Finset.mem_filter.mp hv).2
          rw [abs_mul, abs_of_nonneg (hlam_nonneg v)]
          exact mul_le_mul_of_nonneg_left (hspread v hvne) (hlam_nonneg v)
    _ = ((Finset.univ.filter (fun v : V => v ≠ vstar)).sum (fun v => lam v)) *
            Rspread := by
          rw [Finset.sum_mul]
    _ ≤ loserBound * Rspread := mul_le_mul_of_nonneg_right hloser hRspread_nonneg
    _ = Rspread * loserBound := by ring

/-- The final εmix-shaped concentration estimate for the replicator gate window. -/
theorem replicator_mix_error {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (lam P : V → ℝ → ℝ) (cr cg G : ℝ → ℝ) (vstar : V) (A : V → ℝ)
    {a b Lmin gap R0 Kreset Rspread : ℝ}
    (hab : a ≤ b)
    (hLmin_pos : 0 < Lmin)
    (hGcont : Continuous G)
    (hcr_cont : Continuous cr)
    (hlam_cont : ∀ w : V, ContinuousOn (lam w) (Icc a b))
    (hode : ∀ w : V, ∀ t ∈ Ico a b,
      HasDerivAt (lam w)
        (cr t * (1 / (Fintype.card V : ℝ) - lam w t)
          + cg t * lam w t *
              (P w t - ∑ u : V, lam u t * P u t)) t)
    (hGder : ∀ t ∈ Ico a b, HasDerivWithinAt G (cg t) (Ici t) t)
    (hqL : ∀ t ∈ Icc a b, Lmin ≤ lam vstar t)
    (hlam_nonneg_Icc : ∀ w : V, ∀ t ∈ Icc a b, 0 ≤ lam w t)
    (hsum_b : (∑ w : V, lam w b) = 1)
    (hcr_nonneg : ∀ t ∈ Ico a b, 0 ≤ cr t)
    (hcg_nonneg : ∀ t ∈ Ico a b, 0 ≤ cg t)
    (hgap : ∀ v : V, v ≠ vstar → ∀ t ∈ Ico a b, P v t - P vstar t ≤ -gap)
    (hRa : ∀ v : V, v ≠ vstar → lam v a / lam vstar a ≤ R0)
    (hKreset : (∫ t in a..b, Real.exp (gap * (G t - G a)) * cr t) ≤ Kreset)
    (hRspread_nonneg : 0 ≤ Rspread)
    (hspread : ∀ v : V, v ≠ vstar → |A v - A vstar| ≤ Rspread) :
    |(∑ v : V, lam v b * A v) - A vstar| ≤
      Rspread * ((Fintype.card V : ℝ) - 1) *
        ((R0 + Kreset / ((Fintype.card V : ℝ) * Lmin))
          * Real.exp (-gap * (G b - G a))) := by
  classical
  let eps : ℝ :=
    (R0 + Kreset / ((Fintype.card V : ℝ) * Lmin))
      * Real.exp (-gap * (G b - G a))
  have hq_pos_b : 0 < lam vstar b :=
    lt_of_lt_of_le hLmin_pos (hqL b (right_mem_Icc.mpr hab))
  have hratio : ∀ v : V, v ≠ vstar → lam v b / lam vstar b ≤ eps := by
    intro v hv
    exact replicator_ratio_bound (lam := lam) (P := P) (cr := cr) (cg := cg) (G := G)
      (vstar := vstar) (v := v) hab hLmin_pos hGcont hcr_cont hlam_cont hode
      hGder hqL hlam_nonneg_Icc hcr_nonneg hcg_nonneg (hgap v hv) (hRa v hv) hKreset
  have hloser := replicator_loser_mass_bound (lam := lam) vstar
    (b := b) (eps := eps) hsum_b
    (fun w => hlam_nonneg_Icc w b (right_mem_Icc.mpr hab))
    hq_pos_b hratio
  have hmix := replicator_mix_error_of_loser_mass vstar (fun v => lam v b) A
    hRspread_nonneg hsum_b
    (fun v => hlam_nonneg_Icc v b (right_mem_Icc.mpr hab))
    hspread hloser
  dsimp [eps] at hmix ⊢
  nlinarith [hmix]

#print axioms replicator_reset_ratio_identity
#print axioms replicator_ratio_deriv
#print axioms replicator_ratio_deriv_le
#print axioms replicator_ratio_bound
#print axioms replicator_loser_mass_bound
#print axioms replicator_mix_error_of_loser_mass
#print axioms replicator_mix_error

end Ripple.BoundedUniversality.BGP
