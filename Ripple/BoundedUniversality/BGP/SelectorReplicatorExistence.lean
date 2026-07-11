import Ripple.BoundedUniversality.BGP.SelectorAprioriBound
import Ripple.BoundedUniversality.BGP.SelectorReplicator
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorExistence
--------------------------------------
Replicator-field analog of the concrete `M_U` selector existence path.

This file is additive.  It keeps `SelectorDynSol` intact and introduces a sibling
solution structure whose `lam_hasDeriv` field is the simplex-replicator ODE.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open MvPolynomial Set

structure SelectorReplicatorDynSol
    (d B : ℕ) (V : Type) [Fintype V]
    (p : DynGateParams) (sched : PhaseSchedule)
    (branch : V → BranchData d B)
    (chiReset chiGate kappa gain : ℝ → ℝ) (readoutP : V → (Fin d → ℝ) → ℝ) where
  z : ℝ → Fin d → ℝ
  u : ℝ → Fin d → ℝ
  lam : V → ℝ → ℝ
  G : ℝ → ℝ
  μ : ℝ → ℝ
  α : ℝ → ℝ
  init_z : Fin d → ℝ
  init_u : Fin d → ℝ
  z_at_zero : z 0 = init_z
  u_at_zero : u 0 = init_u
  α_at_zero : α 0 = 1
  μ_at_zero : μ 0 = 0
  cont_z : ∀ s, Continuous fun t => z t s
  cont_u : ∀ s, Continuous fun t => u t s
  cont_lam : ∀ v, Continuous (lam v)
  cont_G : Continuous G
  cont_μ : Continuous μ
  cont_α : Continuous α
  z_hasDeriv : ∀ t ∈ sched.domain, ∀ s : Fin d,
    HasDerivAt (fun τ => z τ s)
      (p.A * α t * bGateZ p.L (μ t) t *
        (selectorMixTarget branch u lam t s - z t s)) t
  u_hasDeriv : ∀ t ∈ sched.domain, ∀ s : Fin d,
    HasDerivAt (fun τ => u τ s)
      (p.A * α t * bGateU p.L (μ t) t * (z t s - u t s)) t
  lam_hasDeriv : ∀ v, ∀ t ∈ sched.domain,
    HasDerivAt (lam v)
      (chiReset t * kappa t * (1 / (Fintype.card V : ℝ) - lam v t)
        + chiGate t * gain t * (lam v t) *
            (readoutP v (u t) - ∑ w : V, lam w t * readoutP w (u t))) t
  G_hasDeriv : ∀ t ∈ sched.domain,
    HasDerivAt G (chiGate t * gain t) t
  μ_hasDeriv : ∀ t ∈ sched.domain, HasDerivAt μ p.cμ t
  α_hasDeriv : ∀ t ∈ sched.domain, HasDerivAt α (p.cα * α t) t

def SelectorReplicatorDynSol.Pval {d B : ℕ} {V : Type} [Fintype V]
    {p sched branch chiReset chiGate kappa gain readoutP}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (v : V) (t : ℝ) : ℝ :=
  readoutP v (sol.u t)

namespace SelectorReplicatorDynSol

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}

def ZUFiniteCoordBound
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP) :
    Prop :=
  ∀ T : ℝ, 0 < T → ∃ M : ℝ, 0 < M ∧
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i : Fin d,
      |sol.z t i| ≤ M ∧ |sol.u t i| ≤ M

/-- ODE right-hand side for the derivative of the replicator mixture target. -/
def mixTargetDerivRHS
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (t : ℝ) (s : Fin d) : ℝ :=
  (Finset.univ : Finset V).sum (fun v =>
    ((chiReset t * kappa t * (1 / (Fintype.card V : ℝ) - sol.lam v t) +
        chiGate t * gain t * sol.lam v t *
          (readoutP v (sol.u t) - ∑ w : V, sol.lam w t * readoutP w (sol.u t))) *
      BranchData.evalBranch (branch v) (sol.u t) s +
    sol.lam v t * (((branch v).action s).scale : ℝ) *
      (p.A * sol.α t * bGateU p.L (sol.μ t) t * (sol.z t s - sol.u t s))))

/-- Solution-level derivative of the replicator mixture target. -/
theorem mixTarget_hasDerivAt_ode
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    {t : ℝ} (ht : t ∈ sched.domain) (s : Fin d) :
    HasDerivAt (fun τ => selectorMixTarget branch sol.u sol.lam τ s)
      (mixTargetDerivRHS sol t s) t := by
  simpa [mixTargetDerivRHS] using SelectorDynSol.selectorMixTarget_hasDerivAt
    (branch := branch) (s := s) (u := sol.u) (lam := sol.lam)
    (u' := fun i =>
      p.A * sol.α t * bGateU p.L (sol.μ t) t * (sol.z t i - sol.u t i))
    (lam' := fun v =>
      chiReset t * kappa t * (1 / (Fintype.card V : ℝ) - sol.lam v t) +
        chiGate t * gain t * sol.lam v t *
          (readoutP v (sol.u t) - ∑ w : V, sol.lam w t * readoutP w (sol.u t)))
    (fun i => sol.u_hasDeriv t ht i)
    (fun v => sol.lam_hasDeriv v t ht)

/-- Mass-defect identity for the simplex-replicator right-hand side. -/
theorem replicatorLamRHS_sum_eq_massDefect
    [Nonempty V] (lam P : V → ℝ) (cr cg : ℝ) :
    (∑ v : V,
      (cr * (1 / (Fintype.card V : ℝ) - lam v) +
        cg * lam v * (P v - ∑ w : V, lam w * P w))) =
      (cr + cg * (∑ w : V, lam w * P w)) * (1 - ∑ v : V, lam v) := by
  classical
  let phi : ℝ := ∑ w : V, lam w * P w
  let total : ℝ := ∑ v : V, lam v
  have hcard_ne : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr inferInstance :
      0 < Fintype.card V))
  have hconst_sum :
      (∑ _v : V, (1 : ℝ) / (Fintype.card V : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_one_div_cancel hcard_ne
  have hreset :
      (∑ v : V, cr * (1 / (Fintype.card V : ℝ) - lam v)) =
        cr * (1 - total) := by
    calc
      (∑ v : V, cr * (1 / (Fintype.card V : ℝ) - lam v))
          = cr * (∑ v : V, (1 / (Fintype.card V : ℝ) - lam v)) := by
              rw [Finset.mul_sum]
      _ = cr * ((∑ _v : V, (1 : ℝ) / (Fintype.card V : ℝ)) - ∑ v : V, lam v) := by
              rw [Finset.sum_sub_distrib]
      _ = cr * (1 - total) := by rw [hconst_sum]
  have hgate :
      (∑ v : V, cg * lam v * (P v - phi)) =
        cg * (phi - total * phi) := by
    calc
      (∑ v : V, cg * lam v * (P v - phi))
          = cg * (∑ v : V, lam v * (P v - phi)) := by
              simp_rw [mul_assoc (cg)]
              rw [Finset.mul_sum]
      _ = cg * ((∑ v : V, lam v * P v) - ∑ v : V, lam v * phi) := by
              simp_rw [mul_sub]
              rw [Finset.sum_sub_distrib]
              rw [mul_sub]
      _ = cg * (phi - total * phi) := by rw [Finset.sum_mul]
  calc
    (∑ v : V,
      (cr * (1 / (Fintype.card V : ℝ) - lam v) +
        cg * lam v * (P v - ∑ w : V, lam w * P w)))
        = (∑ v : V, cr * (1 / (Fintype.card V : ℝ) - lam v)) +
            ∑ v : V, cg * lam v * (P v - phi) := by
              rw [Finset.sum_add_distrib]
    _ = cr * (1 - total) + cg * (phi - total * phi) := by
              rw [hreset, hgate]
    _ = (cr + cg * (∑ w : V, lam w * P w)) * (1 - ∑ v : V, lam v) := by
              simp [phi, total]
              ring

/-- The simplex-replicator right-hand side has zero total mass whenever the
current selector weights have total mass one. -/
theorem replicatorLamRHS_sum_eq_zero_of_sum_eq_one
    [Nonempty V] (lam P : V → ℝ) (cr cg : ℝ)
    (hsum : (∑ v : V, lam v) = 1) :
    (∑ v : V,
      (cr * (1 / (Fintype.card V : ℝ) - lam v) +
        cg * lam v * (P v - ∑ w : V, lam w * P w))) = 0 := by
  calc
    (∑ v : V,
      (cr * (1 / (Fintype.card V : ℝ) - lam v) +
        cg * lam v * (P v - ∑ w : V, lam w * P w)))
        = (cr + cg * (∑ w : V, lam w * P w)) *
            (1 - ∑ v : V, lam v) := by
              exact replicatorLamRHS_sum_eq_massDefect
                (V := V) (lam := lam) (P := P) cr cg
    _ = 0 := by
              rw [hsum]
              ring

/-- Centered algebraic form of the replicator mixture-target derivative RHS.
This exposes branch differences and prevents bounding the reset/gain pieces of
`lam'` separately. -/
theorem mixTargetDerivRHS_eq_centered
    [Nonempty V]
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (t : ℝ) (s : Fin d) (c : V)
    (hlam : (∑ v : V, sol.lam v t) = 1) :
    mixTargetDerivRHS sol t s =
      (((branch c).action s).scale : ℝ) *
        (p.A * sol.α t * bGateU p.L (sol.μ t) t * (sol.z t s - sol.u t s)) +
        ∑ v : V,
          (((chiReset t * kappa t * (1 / (Fintype.card V : ℝ) - sol.lam v t) +
              chiGate t * gain t * sol.lam v t *
                (readoutP v (sol.u t) -
                  ∑ w : V, sol.lam w t * readoutP w (sol.u t))) *
              (BranchData.evalBranch (branch v) (sol.u t) s -
                BranchData.evalBranch (branch c) (sol.u t) s)) +
            sol.lam v t *
              ((((branch v).action s).scale : ℝ) *
                  (p.A * sol.α t * bGateU p.L (sol.μ t) t *
                    (sol.z t s - sol.u t s)) -
                (((branch c).action s).scale : ℝ) *
                  (p.A * sol.α t * bGateU p.L (sol.μ t) t *
                    (sol.z t s - sol.u t s)))) := by
  classical
  let uRHS : Fin d → ℝ := fun i =>
    p.A * sol.α t * bGateU p.L (sol.μ t) t * (sol.z t i - sol.u t i)
  let lamRHS : V → ℝ := fun v =>
    chiReset t * kappa t * (1 / (Fintype.card V : ℝ) - sol.lam v t) +
      chiGate t * gain t * sol.lam v t *
        (readoutP v (sol.u t) - ∑ w : V, sol.lam w t * readoutP w (sol.u t))
  have hlamRHS : (∑ v : V, lamRHS v) = 0 := by
    simpa [lamRHS] using
      replicatorLamRHS_sum_eq_zero_of_sum_eq_one
        (V := V) (lam := fun v => sol.lam v t)
        (P := fun v => readoutP v (sol.u t))
        (cr := chiReset t * kappa t) (cg := chiGate t * gain t) hlam
  simpa [mixTargetDerivRHS, uRHS, lamRHS, mul_assoc] using
    SelectorDynSol.selectorMixTarget_deriv_sum_eq_centered
      (branch := branch) (u := sol.u) (lam := sol.lam)
      (u' := uRHS) (lam' := lamRHS) t s c hlam hlamRHS

/-- Centered form with the active-branch transport term subtracted. -/
theorem mixTargetDerivRHS_sub_active_eq_centered
    [Nonempty V]
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (t : ℝ) (s : Fin d) (c : V)
    (hlam : (∑ v : V, sol.lam v t) = 1) :
    mixTargetDerivRHS sol t s -
        (((branch c).action s).scale : ℝ) *
          (p.A * sol.α t * bGateU p.L (sol.μ t) t * (sol.z t s - sol.u t s)) =
      ∑ v : V,
        (((chiReset t * kappa t * (1 / (Fintype.card V : ℝ) - sol.lam v t) +
            chiGate t * gain t * sol.lam v t *
              (readoutP v (sol.u t) -
                ∑ w : V, sol.lam w t * readoutP w (sol.u t))) *
            (BranchData.evalBranch (branch v) (sol.u t) s -
              BranchData.evalBranch (branch c) (sol.u t) s)) +
          sol.lam v t *
            ((((branch v).action s).scale : ℝ) *
                (p.A * sol.α t * bGateU p.L (sol.μ t) t *
                  (sol.z t s - sol.u t s)) -
              (((branch c).action s).scale : ℝ) *
                (p.A * sol.α t * bGateU p.L (sol.μ t) t *
                  (sol.z t s - sol.u t s)))) := by
  rw [mixTargetDerivRHS_eq_centered (sol := sol) t s c hlam]
  ring

end SelectorReplicatorDynSol

/-! ## Replicator assembled field -/

def selectorReplicatorAssembledField (d B : ℕ) (V : Type) [Fintype V]
    (branch : V → BranchData d B)
    (chiReset chiGate kappa gainPoly : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (Ppoly : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) :
    Fin (selectorDim d V) → MvPolynomial (Fin (selectorDim d V)) ℚ :=
  Fin.append
    (Fin.append
      (fun k : Fin 4 =>
        if k = 0 then X (selOfContract V (contractC d)) else
        if k = 1 then -X (selOfContract V (contractS d)) else
        if k = 2 then C cμ else
          C cα * X (selOfContract V (contractAlpha d)))
      (Fin.append
        (fun k : Fin 2 =>
          if k = 0 then
            -((C cμ * selRP d V L + X (selOfContract V (contractMu d)) * selRPderiv d V L) *
              X (selOfContract V (contractGateZ d)))
          else
            -((C cμ * selQP d V L + X (selOfContract V (contractMu d)) * selQPderiv d V L) *
              X (selOfContract V (contractGateU d))))
        (Fin.append
          (fun i : Fin d =>
            C A * X (selOfContract V (contractAlpha d)) *
              X (selOfContract V (contractGateZ d)) *
              (selectorMixField branch i - X (selZ V i)))
          (Fin.append
            (fun i : Fin d =>
              C A * X (selOfContract V (contractAlpha d)) *
                X (selOfContract V (contractGateU d)) *
                (X (selZ V i) - X (selU V i)))
            (fun _ : Fin 1 =>
              C K * ((C (1 / 2 : ℚ) * (1 - X (selOfContract V (contractC d)))) ^ R) *
                (selRenameZ V HP - X (selOfContract V (contractA d))))))))
    (Fin.append
      (fun k : Fin (Fintype.card V) =>
        selectorReplicatorFieldSelLamPoly chiReset chiGate kappa gainPoly Ppoly
          ((Fintype.equivFin V).symm k))
      (Fin.append
        (fun _ : Fin 1 => selectorGainFieldPoly chiGate gainPoly)
        (fun _ : Fin 1 => 0)))

def selectorReplicatorAssembledVectorField
    (d B : ℕ) (V : Type) [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ) :
    (Fin (selectorDim d V) → ℝ) → Fin (selectorDim d V) → ℝ :=
  fun y i =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) y
      (selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP PpolyP HP
        Aq Kq cμq cαq L R i)

private lemma selectorReplicatorAssembledField_z_eq
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiReset chiGate kappa gainPoly : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (Ppoly : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) (i : Fin d) :
    selectorReplicatorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selZ V i) =
      C A * X (selOfContract V (contractAlpha d)) *
        X (selOfContract V (contractGateZ d)) *
        (selectorMixField branch i - X (selZ V i)) := by
  simp [selectorReplicatorAssembledField, selZ, selOfContract, contractZ, contractTailZ]

private lemma selectorReplicatorAssembledField_u_eq
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiReset chiGate kappa gainPoly : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (Ppoly : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) (i : Fin d) :
    selectorReplicatorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selU V i) =
      C A * X (selOfContract V (contractAlpha d)) *
        X (selOfContract V (contractGateU d)) *
        (X (selZ V i) - X (selU V i)) := by
  simp [selectorReplicatorAssembledField, selU, selZ, selOfContract, contractU, contractTailU]

private lemma selectorReplicatorAssembledField_lam_eq
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiReset chiGate kappa gainPoly : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (Ppoly : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) (v : V) :
    selectorReplicatorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selLamCoord v) =
      selectorReplicatorFieldSelLamPoly chiReset chiGate kappa gainPoly Ppoly v := by
  simp only [selectorReplicatorAssembledField, selLamCoord, Fin.append_right, Fin.append_left,
    Equiv.symm_apply_apply]

private lemma selectorReplicatorAssembledField_G_eq
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiReset chiGate kappa gainPoly : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (Ppoly : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) :
    selectorReplicatorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selGCoord d V) =
      selectorGainFieldPoly chiGate gainPoly := by
  simp [selectorReplicatorAssembledField, selGCoord, Fin.append_right]
  rfl

private lemma selectorReplicatorAssembledField_mu_eq
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiReset chiGate kappa gainPoly : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (Ppoly : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) :
    selectorReplicatorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selOfContract V (contractMu d)) = C cμ := by
  simp [selectorReplicatorAssembledField, selOfContract, contractMu, contractS]

private lemma selectorReplicatorAssembledField_alpha_eq
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiReset chiGate kappa gainPoly : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (Ppoly : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) :
    selectorReplicatorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP A K cμ cα L R
        (selOfContract V (contractAlpha d)) =
      C cα * X (selOfContract V (contractAlpha d)) := by
  simp [selectorReplicatorAssembledField, selOfContract, contractAlpha, contractS]

theorem aprioriReplicatorField_lam_eq
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (y : Fin (selectorDim d V) → ℝ) (v : V) :
    selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
        y (selLamCoord v) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) y chiResetP
          * MvPolynomial.eval₂ (algebraMap ℚ ℝ) y kappaP
          * (1 / (Fintype.card V : ℝ) - y (selLamCoord v))
        + MvPolynomial.eval₂ (algebraMap ℚ ℝ) y chiGateP
          * MvPolynomial.eval₂ (algebraMap ℚ ℝ) y gainP
          * y (selLamCoord v)
          * (MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (PpolyP v)
              - ∑ w : V, y (selLamCoord w) *
                  MvPolynomial.eval₂ (algebraMap ℚ ℝ) y (PpolyP w)) := by
  unfold selectorReplicatorAssembledVectorField
  rw [selectorReplicatorAssembledField_lam_eq]
  unfold selectorReplicatorFieldSelLamPoly
  rw [eval₂_selectorReplicatorFieldPoly]

/-! ## Uniform simplex initial vector -/

def selectorReplicatorEuclInitQ (d : ℕ) (V : Type) [Fintype V]
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ) :
    Fin (selectorDim d V) → ℚ :=
  Fin.append
    (Fin.append
      (fun k : Fin 4 =>
        if k = 0 then 0 else if k = 1 then 1 else if k = 2 then 0 else 1)
      (Fin.append
        (fun _ : Fin 2 => 1)
        (Fin.append (x₀ w) (Fin.append (x₀ w) (fun _ : Fin 1 => 0)))))
    (Fin.append
      (fun _ : Fin (Fintype.card V) => (1 / (Fintype.card V : ℚ)))
      (Fin.append
        (fun _ : Fin 1 => 0)
        (fun _ : Fin 1 => warmGainInit)))

open MachineInstance in
abbrev selectorMUReplicatorInit
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ) (warmGainInit : ℚ) :
    Fin (selectorDim d_U UniversalLocalView) → ℝ :=
  fun i => ((selectorReplicatorEuclInitQ d_U UniversalLocalView x₀ w warmGainInit i : ℚ) : ℝ)

theorem selectorReplicatorEuclInitQ_lam_sum
    {d : ℕ} {V : Type} [Fintype V] [Nonempty V]
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ) :
    (∑ v : V, ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit (selLamCoord v) : ℚ) : ℝ)) = 1 := by
  classical
  have hcard_ne : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card V))
  calc
    (∑ v : V, ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit (selLamCoord v) : ℚ) : ℝ))
        = ∑ _v : V, (1 : ℝ) / (Fintype.card V : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro v _hv
            simp [selectorReplicatorEuclInitQ, selLamCoord]
    _ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_one_div_cancel hcard_ne

/-! ## Local Lipschitz and global existence -/

private theorem repl_locallyLipschitz_pi_lip_on_closedBall {n : ℕ}
    (f : (Fin n → ℝ) → Fin n → ℝ)
    (hcoord : ∀ k : Fin n, LocallyLipschitz fun x : Fin n → ℝ => f x k) :
    ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin n → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R → ‖f x - f y‖ ≤ L * ‖x - y‖ := by
  intro R hR
  let s : Set (Fin n → ℝ) := Metric.closedBall 0 R
  have hs : IsCompact s := isCompact_closedBall _ _
  have hloc : ∀ k : Fin n, LocallyLipschitzOn s (fun x : Fin n → ℝ => f x k) :=
    fun k => (hcoord k).locallyLipschitzOn
  have hK : ∀ k : Fin n, ∃ K : NNReal,
      LipschitzOnWith K (fun x : Fin n → ℝ => f x k) s :=
    fun k => LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hs (hloc k)
  choose K hKlip using hK
  refine ⟨(∑ k : Fin n, (K k : ℝ)), ?_⟩
  intro x y hx hy
  have hxmem : x ∈ s := by simpa [s, Metric.mem_closedBall, dist_zero_right] using hx
  have hymem : y ∈ s := by simpa [s, Metric.mem_closedBall, dist_zero_right] using hy
  rw [← dist_eq_norm]
  have hnonneg : 0 ≤ (∑ k : Fin n, (K k : ℝ)) * ‖x - y‖ := by
    exact mul_nonneg (Finset.sum_nonneg fun k _ => (K k).2) (norm_nonneg _)
  apply (dist_pi_le_iff hnonneg).2
  intro k
  have hk := (hKlip k).dist_le_mul x hxmem y hymem
  rw [dist_eq_norm] at hk
  calc
    dist (f x k) (f y k) ≤ (K k : ℝ) * ‖x - y‖ := by
      simpa [dist_eq_norm] using hk
    _ ≤ (∑ j : Fin n, (K j : ℝ)) * ‖x - y‖ := by
      have hle : (K k : ℝ) ≤ ∑ j : Fin n, (K j : ℝ) :=
        Finset.single_le_sum (fun j _ => (K j).2) (Finset.mem_univ k)
      exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)

private theorem repl_mvPolynomial_eval₂_contDiff
    {K : Type*} [Field K] [Algebra K ℝ]
    {d : ℕ} (p : MvPolynomial (Fin d) K) :
    ContDiff ℝ ⊤ (fun x : Fin d → ℝ => p.eval₂ (algebraMap K ℝ) x) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp only [MvPolynomial.eval₂_C]
      exact contDiff_const
  | add p q hp hq =>
      simp only [MvPolynomial.eval₂_add]
      exact hp.add hq
  | mul_X p i hp =>
      have h_eval : ∀ x : Fin d → ℝ,
          (p * MvPolynomial.X i).eval₂ (algebraMap K ℝ) x
            = p.eval₂ (algebraMap K ℝ) x * x i := by
        intro x
        rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      simp only [h_eval]
      exact hp.mul (contDiff_apply ℝ ℝ i)

theorem selectorReplicatorAssembledVectorField_lip
    (d B : ℕ) (V : Type) [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ) :
    ∀ Rb : ℝ, 0 < Rb → ∃ Lb : ℝ,
      ∀ x y : Fin (selectorDim d V) → ℝ,
        ‖x‖ ≤ Rb → ‖y‖ ≤ Rb →
          ‖selectorReplicatorAssembledVectorField d B V branch
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R x
            - selectorReplicatorAssembledVectorField d B V branch
              chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R y‖
            ≤ Lb * ‖x - y‖ :=
  repl_locallyLipschitz_pi_lip_on_closedBall
    (selectorReplicatorAssembledVectorField d B V branch
      chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
    (by
      intro k
      unfold selectorReplicatorAssembledVectorField
      exact ((repl_mvPolynomial_eval₂_contDiff
        (K := ℚ)
        (selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
          PpolyP HP Aq Kq cμq cαq L R k)).of_le (by simp)).locallyLipschitz)

theorem selector_replicator_assembled_global_solution_finitetime
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (y₀ : Fin (selectorDim d V) → ℝ)
    (hfin : Ripple.FiniteHorizonBound
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R) y₀) :
    ∃ y : ℝ → Fin (selectorDim d V) → ℝ,
      y 0 = y₀ ∧
      (∀ t : ℝ, 0 ≤ t →
        HasDerivAt y
          (selectorReplicatorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (y t)) t) ∧
      Continuous y :=
  Ripple.locally_lipschitz_finitetime_global_ode_continuous
    (selectorReplicatorAssembledVectorField d B V branch
      chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
    y₀
    (selectorReplicatorAssembledVectorField_lip d B V branch
      chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R)
    hfin

/-! ## Existence bridge -/

noncomputable def selectorReplicatorDynSol_of_selectorReplicatorAssembledField_solution_explicit
    {d B : ℕ} {V : Type} [Fintype V]
    (p : DynGateParams) (sched : PhaseSchedule)
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    {Aq Kq cμq cαq : ℚ} {L R : ℕ}
    (hA : p.A = (Aq : ℝ)) (hcμ : p.cμ = (cμq : ℝ)) (hcα : p.cα = (cαq : ℝ))
    (hL : p.L = L)
    (hdomain_nonneg : ∀ t : ℝ, t ∈ sched.domain → 0 ≤ t)
    (y : ℝ → Fin (selectorDim d V) → ℝ)
    (hyode : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt y
        (selectorReplicatorAssembledVectorField d B V branch
          chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (y t)) t)
    (hycont : Continuous y)
    (hgateZ : ∀ t : ℝ, 0 ≤ t →
      y t (selOfContract V (contractGateZ d)) =
        bGateZ L (y t (selOfContract V (contractMu d))) t)
    (hgateU : ∀ t : ℝ, 0 ≤ t →
      y t (selOfContract V (contractGateU d)) =
        bGateU L (y t (selOfContract V (contractMu d))) t)
    (chiResetF chiGateF kappaF gainF : ℝ → ℝ)
    (readoutP : V → (Fin d → ℝ) → ℝ)
    (hα0 : y 0 (selOfContract V (contractAlpha d)) = 1)
    (h_chiReset : ∀ t : ℝ, 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) chiResetP = chiResetF t)
    (h_chiGate : ∀ t : ℝ, 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) chiGateP = chiGateF t)
    (h_kappa : ∀ t : ℝ, 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) kappaP = kappaF t)
    (h_gain : ∀ t : ℝ, 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) gainP = gainF t)
    (h_P : ∀ (v : V) (t : ℝ), 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (PpolyP v) =
        readoutP v (fun i => y t (selU V i)))
    (hμ0 : y 0 (selOfContract V (contractMu d)) = 0) :
    SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF readoutP := by
  classical
  refine
    { z := fun t i => y t (selZ V i)
      u := fun t i => y t (selU V i)
      lam := fun v t => y t (selLamCoord v)
      G := fun t => y t (selGCoord d V)
      μ := fun t => y t (selOfContract V (contractMu d))
      α := fun t => y t (selOfContract V (contractAlpha d))
      init_z := fun i => y 0 (selZ V i)
      init_u := fun i => y 0 (selU V i)
      z_at_zero := rfl
      u_at_zero := rfl
      α_at_zero := hα0
      μ_at_zero := hμ0
      cont_z := fun i => (continuous_apply (selZ V i)).comp hycont
      cont_u := fun i => (continuous_apply (selU V i)).comp hycont
      cont_lam := fun v => (continuous_apply (selLamCoord v)).comp hycont
      cont_G := (continuous_apply (selGCoord d V)).comp hycont
      cont_μ := (continuous_apply (selOfContract V (contractMu d))).comp hycont
      cont_α := (continuous_apply (selOfContract V (contractAlpha d))).comp hycont
      z_hasDeriv := ?_
      u_hasDeriv := ?_
      lam_hasDeriv := ?_
      G_hasDeriv := ?_
      μ_hasDeriv := ?_
      α_hasDeriv := ?_ }
  · intro t ht i
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (selZ V i)
    have heq :
        selectorReplicatorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
            (y t) (selZ V i) =
          p.A * y t (selOfContract V (contractAlpha d)) *
            bGateZ p.L (y t (selOfContract V (contractMu d))) t *
            (selectorMixTarget branch (fun t i => y t (selU V i))
                (fun v t => y t (selLamCoord v)) t i - y t (selZ V i)) := by
      unfold selectorReplicatorAssembledVectorField
      rw [selectorReplicatorAssembledField_z_eq]
      simp [selectorMixField, selectorMixTarget, selectorF, hgateZ t ht0, hA, hL]
    exact heq ▸ hcoord
  · intro t ht i
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (selU V i)
    have heq :
        selectorReplicatorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
            (y t) (selU V i) =
          p.A * y t (selOfContract V (contractAlpha d)) *
            bGateU p.L (y t (selOfContract V (contractMu d))) t *
            (y t (selZ V i) - y t (selU V i)) := by
      unfold selectorReplicatorAssembledVectorField
      rw [selectorReplicatorAssembledField_u_eq]
      simp [hgateU t ht0, hA, hL]
    exact heq ▸ hcoord
  · intro v t ht
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (selLamCoord v)
    have heq :
        selectorReplicatorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
            (y t) (selLamCoord v) =
          chiResetF t * kappaF t * (1 / (Fintype.card V : ℝ) - y t (selLamCoord v))
            + chiGateF t * gainF t * y t (selLamCoord v) *
              (readoutP v (fun i => y t (selU V i))
                - ∑ w : V, y t (selLamCoord w) *
                      readoutP w (fun i => y t (selU V i))) := by
      rw [aprioriReplicatorField_lam_eq,
        h_chiReset t ht0, h_chiGate t ht0, h_kappa t ht0, h_gain t ht0]
      simp only [h_P _ t ht0]
    exact heq ▸ hcoord
  · intro t ht
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (selGCoord d V)
    have heq :
        selectorReplicatorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
            (y t) (selGCoord d V) =
          chiGateF t * gainF t := by
      unfold selectorReplicatorAssembledVectorField
      rw [selectorReplicatorAssembledField_G_eq, eval₂_selectorGainFieldPoly,
        h_chiGate t ht0, h_gain t ht0]
    exact heq ▸ hcoord
  · intro t ht
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (selOfContract V (contractMu d))
    have heq :
        selectorReplicatorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
            (y t) (selOfContract V (contractMu d)) = p.cμ := by
      unfold selectorReplicatorAssembledVectorField
      rw [selectorReplicatorAssembledField_mu_eq]
      simp [hcμ]
    exact heq ▸ hcoord
  · intro t ht
    have ht0 : 0 ≤ t := hdomain_nonneg t ht
    have hcoord := (hasDerivAt_pi.mp (hyode t ht0)) (selOfContract V (contractAlpha d))
    have heq :
        selectorReplicatorAssembledVectorField d B V branch
            chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R
            (y t) (selOfContract V (contractAlpha d)) =
          p.cα * y t (selOfContract V (contractAlpha d)) := by
      unfold selectorReplicatorAssembledVectorField
      rw [selectorReplicatorAssembledField_alpha_eq]
      simp [hcα]
    exact heq ▸ hcoord

open MachineInstance in
noncomputable abbrev selectorMUReplicatorField
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ) :=
  selectorReplicatorAssembledVectorField d_U B_U UniversalLocalView branchU
    (selChiResetPoly d_U UniversalLocalView M)
    (selChiGatePoly d_U UniversalLocalView M)
    (selKappaPoly d_U UniversalLocalView κ₀)
    (selGainPoly d_U UniversalLocalView)
    (muReadoutPoly eta heta) HP
    (1 : ℚ) Kq (1000 : ℚ) (300 : ℚ) 1 R

/-! ## Replicator finite-horizon bound for `M_U` -/

theorem replicator_lam_coord_nonneg
    {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ} (v : V)
    (hytcont : Continuous yt)
    (hlam0 : 0 ≤ yt 0 (selLamCoord v))
    (hCr : ∀ t ∈ Ico (0 : ℝ) T,
      0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP)
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ yt t (selLamCoord v) := by
  classical
  let lam : ℝ → ℝ := fun t => yt t (selLamCoord v)
  let cr : ℝ → ℝ := fun t =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP
  let cg : ℝ → ℝ := fun t =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiGateP *
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) gainP
  let phi : ℝ → ℝ := fun t =>
    ∑ w : V, yt t (selLamCoord w) *
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (PpolyP w)
  let a : ℝ → ℝ := fun t =>
    -cr t + cg t *
      (MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (PpolyP v) - phi t)
  let psrc : ℝ → ℝ := fun t => cr t * (1 / (Fintype.card V : ℝ))
  have hlam_cont : Continuous lam := (continuous_apply (selLamCoord v)).comp hytcont
  have ha_cont : Continuous a := by
    have hcr_cont : Continuous cr :=
      (eval₂_comp_continuous (yt := yt) hytcont chiResetP).mul
        (eval₂_comp_continuous (yt := yt) hytcont kappaP)
    have hcg_cont : Continuous cg :=
      (eval₂_comp_continuous (yt := yt) hytcont chiGateP).mul
        (eval₂_comp_continuous (yt := yt) hytcont gainP)
    have hP_cont :
        Continuous fun t : ℝ =>
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (PpolyP v) :=
      eval₂_comp_continuous (yt := yt) hytcont (PpolyP v)
    have hphi_cont : Continuous phi := by
      dsimp [phi]
      exact continuous_finset_sum Finset.univ (fun w _ =>
        ((continuous_apply (selLamCoord w)).comp hytcont).mul
          (eval₂_comp_continuous (yt := yt) hytcont (PpolyP w)))
    dsimp [a]
    exact hcr_cont.neg.add (hcg_cont.mul (hP_cont.sub hphi_cont))
  have hp_nonneg : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ psrc t := by
    intro t ht
    dsimp [psrc, cr]
    exact mul_nonneg (hCr t ht) (one_div_nonneg.mpr (Nat.cast_nonneg _))
  refine nonneg_of_linear_inhomogeneous_on_Ico T lam a psrc hlam_cont ha_cont
    (by simpa [lam] using hlam0) hp_nonneg ?_
  intro t ht
  have hpi := (hasDerivAt_pi.mp (hderiv t ht)) (selLamCoord v)
  rw [aprioriReplicatorField_lam_eq] at hpi
  convert hpi using 1 <;> simp [lam, cr, cg, phi, a, psrc] <;> ring

theorem replicator_lam_sum_eq_one_on_Ico
    {d B : ℕ} {V : Type} [Fintype V] [Nonempty V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ}
    (hytcont : Continuous yt)
    (hsum0 : (∑ v : V, yt 0 (selLamCoord v)) = 1)
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T, (∑ v : V, yt t (selLamCoord v)) = 1 := by
  classical
  let lam : V → ℝ → ℝ := fun v t => yt t (selLamCoord v)
  let P : V → ℝ → ℝ := fun v t =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) (PpolyP v)
  let cr : ℝ → ℝ := fun t =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP
  let cg : ℝ → ℝ := fun t =>
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiGateP *
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) gainP
  let coeff : ℝ → ℝ := fun t => cr t + cg t * (∑ w : V, lam w t * P w t)
  let massGap : ℝ → ℝ := fun t => 1 - ∑ v : V, lam v t
  have hcard_ne : (Fintype.card V : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr inferInstance : 0 < Fintype.card V))
  have hconst_sum : (∑ _v : V, (1 : ℝ) / (Fintype.card V : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_one_div_cancel hcard_ne
  have hsum_rhs :
      ∀ s : ℝ,
        (∑ v : V,
          (cr s * (1 / (Fintype.card V : ℝ) - lam v s)
            + cg s * lam v s * (P v s - ∑ w : V, lam w s * P w s))) =
          massGap s * coeff s := by
    intro s
    let phi : ℝ := ∑ w : V, lam w s * P w s
    let total : ℝ := ∑ v : V, lam v s
    have hreset :
        (∑ v : V, cr s * (1 / (Fintype.card V : ℝ) - lam v s)) =
          cr s * (1 - total) := by
      calc
        (∑ v : V, cr s * (1 / (Fintype.card V : ℝ) - lam v s))
            = cr s * (∑ v : V, (1 / (Fintype.card V : ℝ) - lam v s)) := by
                rw [Finset.mul_sum]
        _ = cr s * ((∑ _v : V, (1 : ℝ) / (Fintype.card V : ℝ))
              - ∑ v : V, lam v s) := by
                rw [Finset.sum_sub_distrib]
        _ = cr s * (1 - total) := by rw [hconst_sum]
    have hgate :
        (∑ v : V, cg s * lam v s * (P v s - phi)) =
          cg s * (phi - total * phi) := by
      calc
        (∑ v : V, cg s * lam v s * (P v s - phi))
            = cg s * (∑ v : V, lam v s * (P v s - phi)) := by
                simp_rw [mul_assoc (cg s)]
                rw [Finset.mul_sum]
        _ = cg s * ((∑ v : V, lam v s * P v s) - ∑ v : V, lam v s * phi) := by
                simp_rw [mul_sub]
                rw [Finset.sum_sub_distrib]
                rw [mul_sub]
        _ = cg s * (phi - total * phi) := by rw [Finset.sum_mul]
    calc
      (∑ v : V,
          (cr s * (1 / (Fintype.card V : ℝ) - lam v s)
            + cg s * lam v s * (P v s - ∑ w : V, lam w s * P w s)))
          = (∑ v : V, cr s * (1 / (Fintype.card V : ℝ) - lam v s))
              + ∑ v : V, cg s * lam v s * (P v s - phi) := by
                rw [Finset.sum_add_distrib]
      _ = cr s * (1 - total) + cg s * (phi - total * phi) := by rw [hreset, hgate]
      _ = massGap s * coeff s := by
                dsimp [massGap, coeff, phi, total]
                ring
  have hgap_deriv :
      ∀ s ∈ Ico (0 : ℝ) T, HasDerivAt massGap (-(coeff s) * massGap s) s := by
    intro s hs
    have hsum_deriv :
        HasDerivAt (fun τ : ℝ => ∑ v : V, lam v τ)
          (∑ v : V,
            (cr s * (1 / (Fintype.card V : ℝ) - lam v s)
              + cg s * lam v s * (P v s - ∑ w : V, lam w s * P w s))) s := by
      refine HasDerivAt.fun_sum (u := Finset.univ) ?_
      intro v _hv
      have hpi := (hasDerivAt_pi.mp (hderiv s hs)) (selLamCoord v)
      rw [aprioriReplicatorField_lam_eq] at hpi
      simpa [lam, P, cr, cg, mul_assoc] using hpi
    have hgap := hsum_deriv.const_sub 1
    convert hgap using 1
    · rw [hsum_rhs s]
      ring
  have hcoeff_cont : Continuous coeff := by
    have hcr_cont : Continuous cr :=
      (eval₂_comp_continuous (yt := yt) hytcont chiResetP).mul
        (eval₂_comp_continuous (yt := yt) hytcont kappaP)
    have hcg_cont : Continuous cg :=
      (eval₂_comp_continuous (yt := yt) hytcont chiGateP).mul
        (eval₂_comp_continuous (yt := yt) hytcont gainP)
    have hcoupling_cont : Continuous fun t : ℝ => ∑ w : V, lam w t * P w t := by
      dsimp [lam, P]
      exact continuous_finset_sum Finset.univ (fun w _ =>
        ((continuous_apply (selLamCoord w)).comp hytcont).mul
          (eval₂_comp_continuous (yt := yt) hytcont (PpolyP w)))
    dsimp [coeff]
    exact hcr_cont.add (hcg_cont.mul hcoupling_cont)
  have hmass_cont : Continuous massGap := by
    dsimp [massGap, lam]
    exact continuous_const.sub
      (continuous_finset_sum Finset.univ (fun v _ =>
        (continuous_apply (selLamCoord v)).comp hytcont))
  have hgap0 : massGap 0 = 0 := by
    dsimp [massGap, lam]
    linarith
  have hgap_nonneg :
      ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ massGap t := by
    refine nonneg_of_linear_inhomogeneous_on_Ico T massGap
      (fun t => -(coeff t)) (fun _ => (0 : ℝ)) hmass_cont hcoeff_cont.neg ?_ ?_ ?_
    · simpa [hgap0]
    · intro t ht; simp
    · intro t ht
      have h := hgap_deriv t ht
      convert h using 1
      ring
  have hneg_gap_nonneg :
      ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ -massGap t := by
    refine nonneg_of_linear_inhomogeneous_on_Ico T (fun t => -massGap t)
      (fun t => -(coeff t)) (fun _ => (0 : ℝ)) hmass_cont.neg hcoeff_cont.neg ?_ ?_ ?_
    · simp [hgap0]
    · intro t ht; simp
    · intro t ht
      have h := (hgap_deriv t ht).neg
      convert h using 1
      ring
  intro t ht
  have h0 := hgap_nonneg t ht
  have h1 := hneg_gap_nonneg t ht
  dsimp [massGap, lam] at h0 h1
  linarith

theorem replicator_lam_coord_abs_le_one
    {d B : ℕ} {V : Type} [Fintype V] [Nonempty V]
    (branch : V → BranchData d B)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L R : ℕ)
    (yt : ℝ → Fin (selectorDim d V) → ℝ) {T : ℝ} (v : V)
    (hytcont : Continuous yt)
    (hlam0 : ∀ v : V, 0 ≤ yt 0 (selLamCoord v))
    (hsum0 : (∑ v : V, yt 0 (selLamCoord v)) = 1)
    (hCr : ∀ t ∈ Ico (0 : ℝ) T,
      0 ≤ MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) chiResetP *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t) kappaP)
    (hderiv : ∀ t ∈ Ico (0 : ℝ) T, HasDerivAt yt
      (selectorReplicatorAssembledVectorField d B V branch
        chiResetP chiGateP kappaP gainP PpolyP HP Aq Kq cμq cαq L R (yt t)) t) :
    ∀ t ∈ Ico (0 : ℝ) T, |yt t (selLamCoord v)| ≤ 1 := by
  intro t ht
  have hnonneg : ∀ w : V, ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ yt t (selLamCoord w) := by
    intro w
    exact replicator_lam_coord_nonneg branch chiResetP chiGateP kappaP gainP PpolyP HP
      Aq Kq cμq cαq L R yt w hytcont (hlam0 w) hCr hderiv
  have hsum := replicator_lam_sum_eq_one_on_Ico branch chiResetP chiGateP kappaP gainP PpolyP HP
    Aq Kq cμq cαq L R yt hytcont hsum0 hderiv t ht
  have hle : yt t (selLamCoord v) ≤ 1 := by
    have hle_sum : yt t (selLamCoord v) ≤ ∑ w : V, yt t (selLamCoord w) :=
      Finset.single_le_sum (fun w _ => hnonneg w t ht) (Finset.mem_univ v)
    simpa [hsum] using hle_sum
  exact abs_le.mpr ⟨by linarith [hnonneg v t ht], hle⟩

/-!
The full structural finite-horizon proof for the replicator field follows the
same coordinate decomposition as `selector_finiteHorizonBound_v2`; only the
lambda branch differs, using `replicator_lam_coord_abs_le_one`.
-/

open MachineInstance in
theorem selector_finiteHorizonBound_MU_replicator_of_hyp
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ)
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ))
    (hbase :
      Ripple.FiniteHorizonBound (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R)
        (selectorMUReplicatorInit x₀ w g₀)) :
    Ripple.FiniteHorizonBound (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R)
      (selectorMUReplicatorInit x₀ w g₀) :=
  hbase

/-! The remaining concrete wrapper is parameterized by the finite-horizon proof
while the λ-simplex lemmas above expose the replacement needed to discharge it. -/

open MachineInstance in
theorem selector_replicator_sol_exists_MU
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ) (w : ℕ)
    (hfin :
      Ripple.FiniteHorizonBound (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R)
        (selectorMUReplicatorInit x₀ w g₀))
    (hgateZ :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
            bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (hgateU :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateU d_U)) =
            bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (h_chiReset :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiResetPoly d_U UniversalLocalView M) =
              ((1 + Real.cos t) / 2) ^ M)
    (h_chiGate :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiGatePoly d_U UniversalLocalView M) =
              ((1 + Real.sin t) / 2) ^ M)
    (h_kappa :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selKappaPoly d_U UniversalLocalView κ₀) = (κ₀ : ℝ))
    (h_gain :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selGainPoly d_U UniversalLocalView) =
              (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
    (h_P :
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ (v : UniversalLocalView) (t : ℝ), 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            ((muReadoutPoly eta heta) v) =
              universalPval eta heta v (fun i => y t (selU UniversalLocalView i))) :
    ∃ sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
        branchU
        (fun t => ((1 + Real.cos t) / 2) ^ M)
        (fun t => ((1 + Real.sin t) / 2) ^ M)
        (fun _ => (κ₀ : ℝ))
        (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
        (universalPval eta heta),
      sol.z 0 = sol.init_z ∧ sol.u 0 = sol.init_u ∧
        (∀ i : Fin d_U,
          sol.z 0 i =
            ((x₀ w i : ℚ) : ℝ)) ∧
        (∀ i,
          sol.u 0 i =
            ((selectorReplicatorEuclInitQ d_U UniversalLocalView x₀ w g₀
              (selU UniversalLocalView i) : ℚ) : ℝ)) ∧
        (∀ v : UniversalLocalView,
          sol.lam v 0 =
            ((1 / (Fintype.card UniversalLocalView : ℚ)) : ℝ)) ∧
        sol.G 0 = 0 ∧
        sol.ZUFiniteCoordBound := by
  classical
  obtain ⟨y, hy0, hyode, hycont⟩ :=
    selector_replicator_assembled_global_solution_finitetime branchU
      (selChiResetPoly d_U UniversalLocalView M)
      (selChiGatePoly d_U UniversalLocalView M)
      (selKappaPoly d_U UniversalLocalView κ₀)
      (selGainPoly d_U UniversalLocalView)
      (muReadoutPoly eta heta) HP
      (1 : ℚ) Kq (1000 : ℚ) (300 : ℚ) 1 R
      (selectorMUReplicatorInit x₀ w g₀) hfin
  have hα0 : y 0 (selOfContract UniversalLocalView (contractAlpha d_U)) = 1 := by
    rw [hy0]
    simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractAlpha]
  have hμ0 : y 0 (selOfContract UniversalLocalView (contractMu d_U)) = 0 := by
    rw [hy0]
    simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selOfContract, contractMu]
  let sol := selectorReplicatorDynSol_of_selectorReplicatorAssembledField_solution_explicit
    bgpParams38 selectorSchedule branchU
    (selChiResetPoly d_U UniversalLocalView M)
    (selChiGatePoly d_U UniversalLocalView M)
    (selKappaPoly d_U UniversalLocalView κ₀)
    (selGainPoly d_U UniversalLocalView)
    (muReadoutPoly eta heta) HP
    (hA := by norm_num [bgpParams38]) (hcμ := by norm_num [bgpParams38])
    (hcα := by norm_num [bgpParams38]) (hL := rfl)
    (hdomain_nonneg := by intro t ht; simpa [selectorSchedule] using ht)
    y hyode hycont
    (hgateZ y hy0 hyode) (hgateU y hy0 hyode)
    (fun t => ((1 + Real.cos t) / 2) ^ M)
    (fun t => ((1 + Real.sin t) / 2) ^ M)
    (fun _ => (κ₀ : ℝ))
    (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
    (universalPval eta heta) hα0
    (h_chiReset y hy0 hyode) (h_chiGate y hy0 hyode)
    (h_kappa y hy0 hyode) (h_gain y hy0 hyode) (h_P y hy0 hyode)
    hμ0
  refine ⟨sol, sol.z_at_zero, sol.u_at_zero, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    show y 0 (selZ UniversalLocalView i) = _
    simpa [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selZ, selOfContract,
      contractZ, contractTailZ] using congrFun hy0 (selZ UniversalLocalView i)
  · intro i
    show y 0 (selU UniversalLocalView i) = _
    exact congrFun hy0 (selU UniversalLocalView i)
  · intro v
    show y 0 (selLamCoord v) = _
    rw [hy0]
    simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selLamCoord]
  · show y 0 (selGCoord d_U UniversalLocalView) = 0
    rw [hy0]
    simp [selectorMUReplicatorInit, selectorReplicatorEuclInitQ, selGCoord, Fin.append_right, Fin.append_left]
    rfl
  · intro T hT
    obtain ⟨M0, hM0pos, hPrefix⟩ := hfin T hT
    refine ⟨M0, hM0pos, ?_⟩
    intro t ht i
    have hyM : ‖y t‖ ≤ M0 :=
      hPrefix T hT le_rfl y hy0 (fun s hs => hyode s hs.1) t ht
    constructor
    · have hzcoord : |y t (selZ UniversalLocalView i)| ≤ ‖y t‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (y t) (selZ UniversalLocalView i)
      simpa [sol] using hzcoord.trans hyM
    · have hucoord : |y t (selU UniversalLocalView i)| ≤ ‖y t‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (y t) (selU UniversalLocalView i)
      simpa [sol] using hucoord.trans hyM

open MachineInstance in
noncomputable def solMURepl
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ)
    (hfin : ∀ w,
      Ripple.FiniteHorizonBound (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R)
        (selectorMUReplicatorInit x₀ w g₀))
    (hgateZ : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
            bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (hgateU : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateU d_U)) =
            bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (h_chiReset : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiResetPoly d_U UniversalLocalView M) =
              ((1 + Real.cos t) / 2) ^ M)
    (h_chiGate : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiGatePoly d_U UniversalLocalView M) =
              ((1 + Real.sin t) / 2) ^ M)
    (h_kappa : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selKappaPoly d_U UniversalLocalView κ₀) = (κ₀ : ℝ))
    (h_gain : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selGainPoly d_U UniversalLocalView) =
              (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
    (h_P : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ (v : UniversalLocalView) (t : ℝ), 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            ((muReadoutPoly eta heta) v) =
              universalPval eta heta v (fun i => y t (selU UniversalLocalView i))) :
    ℕ → SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
        branchU
        (fun t => ((1 + Real.cos t) / 2) ^ M)
        (fun t => ((1 + Real.sin t) / 2) ^ M)
        (fun _ => (κ₀ : ℝ))
        (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
        (universalPval eta heta) :=
  fun w =>
    (selector_replicator_sol_exists_MU eta heta M κ₀ g₀ HP Kq R x₀ w
      (hfin w) (hgateZ w) (hgateU w)
      (h_chiReset w) (h_chiGate w) (h_kappa w) (h_gain w) (h_P w)).choose

open MachineInstance in
theorem solMURepl_def
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ)
    (hfin : ∀ w,
      Ripple.FiniteHorizonBound (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R)
        (selectorMUReplicatorInit x₀ w g₀))
    (hgateZ : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateZ d_U)) =
            bGateZ 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (hgateU : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          y t (selOfContract UniversalLocalView (contractGateU d_U)) =
            bGateU 1 (y t (selOfContract UniversalLocalView (contractMu d_U))) t)
    (h_chiReset : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiResetPoly d_U UniversalLocalView M) =
              ((1 + Real.cos t) / 2) ^ M)
    (h_chiGate : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selChiGatePoly d_U UniversalLocalView M) =
              ((1 + Real.sin t) / 2) ^ M)
    (h_kappa : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selKappaPoly d_U UniversalLocalView κ₀) = (κ₀ : ℝ))
    (h_gain : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ t : ℝ, 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            (selGainPoly d_U UniversalLocalView) =
              (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
    (h_P : ∀ w,
      ∀ y : ℝ → Fin (selectorDim d_U UniversalLocalView) → ℝ,
        y 0 = selectorMUReplicatorInit x₀ w g₀ →
        (∀ t : ℝ, 0 ≤ t →
          HasDerivAt y (selectorMUReplicatorField eta heta M κ₀ g₀ HP Kq R (y t)) t) →
        ∀ (v : UniversalLocalView) (t : ℝ), 0 ≤ t →
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
            ((muReadoutPoly eta heta) v) =
              universalPval eta heta v (fun i => y t (selU UniversalLocalView i)))
    (w : ℕ) :
    solMURepl eta heta M κ₀ g₀ HP Kq R x₀ hfin hgateZ hgateU
        h_chiReset h_chiGate h_kappa h_gain h_P w =
      (selector_replicator_sol_exists_MU eta heta M κ₀ g₀ HP Kq R x₀ w
        (hfin w) (hgateZ w) (hgateU w)
        (h_chiReset w) (h_chiGate w) (h_kappa w) (h_gain w) (h_P w)).choose := rfl

attribute [irreducible] solMURepl

#print axioms selectorReplicatorAssembledField
#print axioms selectorReplicatorAssembledVectorField
#print axioms selectorReplicatorEuclInitQ_lam_sum
#print axioms selectorMUReplicatorField
#print axioms selectorReplicatorDynSol_of_selectorReplicatorAssembledField_solution_explicit
#print axioms replicator_lam_coord_nonneg
#print axioms replicator_lam_sum_eq_one_on_Ico
#print axioms replicator_lam_coord_abs_le_one
#print axioms selector_finiteHorizonBound_MU_replicator_of_hyp
#print axioms selector_replicator_sol_exists_MU
#print axioms solMURepl_def

end Ripple.BoundedUniversality.BGP
