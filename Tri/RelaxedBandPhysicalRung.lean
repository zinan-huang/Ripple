/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.RelaxedBandRung
import Tri.RelaxedBandMonitor
import Tri.LazyHitting

/-!
# Physical dyadic rungs for the unequal-rate chain

The counted band theorem projects exactly to the physical chain frozen at its
two boundaries.  Since the physical chain is nearest-neighbour, the first
upper hit lands at the dyadic target exactly.  This supplies the exact endpoint
needed to concatenate dyadic rungs without resetting a hidden physical state.
-/

namespace Tri

open scoped ENNReal

/-- One relaxed physical step increases the `X` count by at most one. -/
theorem relaxedTriChain_support_le_succ
    (r : RelaxedRate) (n x z : ℕ)
    (hz : relaxedTriChain r n x z ≠ 0) :
    z ≤ x + 1 := by
  unfold relaxedTriChain at hz
  by_cases h : 3 ≤ n ∧ x ≤ n
  · rw [dif_pos h] at hz
    by_cases hx0 : x = 0
    · subst x
      simp only [Nat.sub_zero] at hz
      rw [relaxedTriStep_consensus_Y r n (by simpa using h.1)] at hz
      by_cases hz0 : z = 0
      · omega
      · simp [PMF.pure_apply, hz0] at hz
    · obtain ⟨a, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero hx0
      by_contra hle
      have hza : z ≠ a := by omega
      have hza1 : z ≠ a + 1 := by omega
      have hza2 : z ≠ a + 2 := by omega
      exact hz
        (relaxedTriStep_eq_zero r a (n - (a + 1))
          (by omega) hza hza1 hza2)
  · rw [dif_neg h] at hz
    by_cases hzx : z = x
    · omega
    · simp [PMF.pure_apply, hzx] at hz

/-- Freezing at a lower-or-upper band boundary prevents an overshoot above the
upper target. -/
theorem iter_relaxedBandBoundary_support_le_target
    (r : RelaxedRate) (n lower target T start z : ℕ)
    (hstart : start ≤ target)
    (hz :
      iter
        (freeze (fun x : ℕ => x ≤ lower ∨ target ≤ x)
          (relaxedTriChain r n))
        T start z ≠ 0) :
    z ≤ target := by
  apply iter_support_closed
    (freeze (fun x : ℕ => x ≤ lower ∨ target ≤ x)
      (relaxedTriChain r n))
    (fun x => x ≤ target) _ T start z hstart hz
  intro x hx y hy
  by_cases hboundary : x ≤ lower ∨ target ≤ x
  · rw [freeze_of_mem x hboundary] at hy
    by_cases hyx : y = x
    · omega
    · simp [PMF.pure_apply, hyx] at hy
  · rw [freeze_of_not_mem x hboundary] at hy
    have hxt : x < target := by omega
    exact
      (relaxedTriChain_support_le_succ r n x y hy).trans
        (by omega)

/-- The counted dyadic rung transfers to the physical chain frozen at the
same two boundaries. -/
theorem relaxedDyadicBand_physical_reaches
    (r : RelaxedRate)
    (n P L R H : ℕ)
    (beta slack tau : NNReal)
    (hP : 1 ≤ P) (hL : 1 ≤ L) (hR : 1 ≤ R)
    (hroom : 2 * (P + L) ≤ n)
    (hbeta1 : 1 ≤ beta)
    (hslack : r.fire + slack ≤ beta)
    (htau :
      tau * (relaxedDyadicBHi P L : NNReal) ≤ slack)
    (hmargin :
      (1 : NNReal) + 1 / (R : NNReal) ≤ beta + tau)
    (hcorner :
      beta * (relaxedDyadicBHi P L + 1 : NNReal) ≤
        r.fire * (relaxedDyadicLower n P L + 1 : NNReal)) :
    Reaches
      (freeze
        (fun x : ℕ =>
          x ≤ relaxedDyadicLower n P L ∨
            relaxedDyadicTarget n P ≤ x)
        (relaxedTriChain r n))
      (relaxedDyadicHorizon H n)
      (fun x => x = relaxedDyadicStart n P)
      (fun x => relaxedDyadicTarget n P ≤ x)
      (relaxedDyadicBandError r n P L R H beta tau) := by
  let lower := relaxedDyadicLower n P L
  let start := relaxedDyadicStart n P
  let target := relaxedDyadicTarget n P
  let Kcount := relaxedBandStop r n lower target
  let Kphysical :=
    freeze (fun x : ℕ => x ≤ lower ∨ target ≤ x)
      (relaxedTriChain r n)
  let T := relaxedDyadicHorizon H n
  have hcount :=
    relaxedDyadicBand_reaches
      r n P L R H beta slack tau hP hL hR hroom
      hbeta1 hslack htau hmargin hcorner
  intro x hx
  subst x
  have hmap :
      (iter Kcount T (start, 0)).map Prod.fst =
        iter Kphysical T start := by
    exact iter_map_of_step_map
      Kcount Kphysical Prod.fst
      (relaxedBandStop_map_fst r n lower target)
      T (start, 0)
  change terminalFailureMass
      (iter Kphysical T start) (fun x => target ≤ x) ≤ _
  rw [← hmap, terminalFailureMass_map]
  exact hcount (start, 0) rfl

/-- Nearest-neighbour support strengthens the upper-target postcondition to an
exact landing at the dyadic checkpoint. -/
theorem relaxedDyadicBand_physical_reaches_exact
    (r : RelaxedRate)
    (n P L R H : ℕ)
    (beta slack tau : NNReal)
    (hP : 1 ≤ P) (hL : 1 ≤ L) (hR : 1 ≤ R)
    (hroom : 2 * (P + L) ≤ n)
    (hbeta1 : 1 ≤ beta)
    (hslack : r.fire + slack ≤ beta)
    (htau :
      tau * (relaxedDyadicBHi P L : NNReal) ≤ slack)
    (hmargin :
      (1 : NNReal) + 1 / (R : NNReal) ≤ beta + tau)
    (hcorner :
      beta * (relaxedDyadicBHi P L + 1 : NNReal) ≤
        r.fire * (relaxedDyadicLower n P L + 1 : NNReal)) :
    Reaches
      (freeze
        (fun x : ℕ =>
          x ≤ relaxedDyadicLower n P L ∨
            relaxedDyadicTarget n P ≤ x)
        (relaxedTriChain r n))
      (relaxedDyadicHorizon H n)
      (fun x => x = relaxedDyadicStart n P)
      (fun x => x = relaxedDyadicTarget n P)
      (relaxedDyadicBandError r n P L R H beta tau) := by
  let lower := relaxedDyadicLower n P L
  let start := relaxedDyadicStart n P
  let target := relaxedDyadicTarget n P
  let K :=
    freeze (fun x : ℕ => x ≤ lower ∨ target ≤ x)
      (relaxedTriChain r n)
  let T := relaxedDyadicHorizon H n
  have hupper :=
    relaxedDyadicBand_physical_reaches
      r n P L R H beta slack tau hP hL hR hroom
      hbeta1 hslack htau hmargin hcorner
  intro x hx
  subst x
  have hstartLe : start ≤ target := by
    dsimp only [start, target,
      relaxedDyadicStart, relaxedDyadicTarget]
    omega
  have hsupp :
      ∀ z, iter K T start z ≠ 0 → z ≤ target := by
    intro z hz
    exact iter_relaxedBandBoundary_support_le_target
      r n lower target T start z hstartLe hz
  calc
    terminalFailureMass
        (iter K T start) (fun x => x = target) =
      terminalFailureMass
        (iter K T start) (fun x => target ≤ x) := by
          unfold terminalFailureMass
          apply tsum_congr
          intro z
          by_cases hz : iter K T start z = 0
          · simp [hz]
          · have hzt := hsupp z hz
            by_cases hEq : z = target
            · simp [hEq]
            · have hnot : ¬ target ≤ z := by omega
              simp [hEq, hnot]
    _ ≤ relaxedDyadicBandError r n P L R H beta tau :=
      hupper start rfl

end Tri

#print axioms Tri.relaxedTriChain_support_le_succ
#print axioms Tri.iter_relaxedBandBoundary_support_le_target
#print axioms Tri.relaxedDyadicBand_physical_reaches
#print axioms Tri.relaxedDyadicBand_physical_reaches_exact
