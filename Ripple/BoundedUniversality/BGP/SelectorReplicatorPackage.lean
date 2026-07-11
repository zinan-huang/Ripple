import Ripple.BoundedUniversality.BGP.SelectorReplicatorExistence
import Ripple.BoundedUniversality.BGP.SelectorFinalAssembly
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorReplicatorPackage
-------------------------------------
Polynomial-field packaging for the selector replicator sibling.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open MvPolynomial Set

structure SelectorReplicatorHaltLatchSol
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    (Hval : (Fin d → ℝ) → ℝ) (K : ℝ) (R : ℕ) where
  a : ℝ → ℝ
  init_a : a 0 = 0
  ode_a : ∀ t : ℝ, HasDerivAt a (K * gPulse R t * (Hval (sol.z t) - a t)) t

section Trajectory

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}

def selectorReplicatorTupleTraj
    (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : SelectorReplicatorHaltLatchSol sol Hval K R)
    (warmGainVal : ℝ) (t : ℝ) :
    Fin (selectorDim d V) → ℝ :=
  Fin.append
    (Fin.append
      (fun k : Fin 4 =>
        if k = 0 then Real.sin t else
        if k = 1 then Real.cos t else
        if k = 2 then sol.μ t else sol.α t)
      (Fin.append
        (fun k : Fin 2 =>
          if k = 0 then bGateZ p.L (sol.μ t) t else bGateU p.L (sol.μ t) t)
        (Fin.append (sol.z t) (Fin.append (sol.u t) (fun _ : Fin 1 => La.a t)))))
    (Fin.append
      (fun k : Fin (Fintype.card V) => sol.lam ((Fintype.equivFin V).symm k) t)
      (Fin.append
        (fun _ : Fin 1 => sol.G t)
        (fun _ : Fin 1 => warmGainVal)))

variable {sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv}
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : SelectorReplicatorHaltLatchSol sol Hval K R)
    (warmGainVal : ℝ) (t : ℝ)

@[simp] lemma selectorReplicatorTupleTraj_s :
    selectorReplicatorTupleTraj sol La warmGainVal t (selOfContract V (contractS d)) = Real.sin t := by
  simp [selectorReplicatorTupleTraj, selOfContract, contractS]

@[simp] lemma selectorReplicatorTupleTraj_c :
    selectorReplicatorTupleTraj sol La warmGainVal t (selOfContract V (contractC d)) = Real.cos t := by
  simp [selectorReplicatorTupleTraj, selOfContract, contractC, contractS]

@[simp] lemma selectorReplicatorTupleTraj_mu :
    selectorReplicatorTupleTraj sol La warmGainVal t (selOfContract V (contractMu d)) = sol.μ t := by
  simp [selectorReplicatorTupleTraj, selOfContract, contractMu]

@[simp] lemma selectorReplicatorTupleTraj_alpha :
    selectorReplicatorTupleTraj sol La warmGainVal t (selOfContract V (contractAlpha d)) = sol.α t := by
  simp [selectorReplicatorTupleTraj, selOfContract, contractAlpha]

@[simp] lemma selectorReplicatorTupleTraj_bz :
    selectorReplicatorTupleTraj sol La warmGainVal t (selOfContract V (contractGateZ d)) =
      bGateZ p.L (sol.μ t) t := by
  simp [selectorReplicatorTupleTraj, selOfContract, contractGateZ]

@[simp] lemma selectorReplicatorTupleTraj_bu :
    selectorReplicatorTupleTraj sol La warmGainVal t (selOfContract V (contractGateU d)) =
      bGateU p.L (sol.μ t) t := by
  simp [selectorReplicatorTupleTraj, selOfContract, contractGateU]

@[simp] lemma selectorReplicatorTupleTraj_z (i : Fin d) :
    selectorReplicatorTupleTraj sol La warmGainVal t (selZ V i) = sol.z t i := by
  simp [selectorReplicatorTupleTraj, selZ, selOfContract, contractZ, contractTailZ]

@[simp] lemma selectorReplicatorTupleTraj_u (i : Fin d) :
    selectorReplicatorTupleTraj sol La warmGainVal t (selU V i) = sol.u t i := by
  simp [selectorReplicatorTupleTraj, selU, selOfContract, contractU, contractTailU]

@[simp] lemma selectorReplicatorTupleTraj_a :
    selectorReplicatorTupleTraj sol La warmGainVal t (selOfContract V (contractA d)) = La.a t := by
  simp [selectorReplicatorTupleTraj, selOfContract, contractA, contractTailA]

@[simp] lemma selectorReplicatorTupleTraj_lam (v : V) :
    selectorReplicatorTupleTraj sol La warmGainVal t (selLamCoord v) = sol.lam v t := by
  simp [selectorReplicatorTupleTraj, selLamCoord, Fin.append_right, Fin.append_left]

@[simp] lemma selectorReplicatorTupleTraj_G :
    selectorReplicatorTupleTraj sol La warmGainVal t (selGCoord d V) = sol.G t := by
  simp [selectorReplicatorTupleTraj, selGCoord, Fin.append_right, Fin.append_left]
  rfl

@[simp] lemma selectorReplicatorTupleTraj_warmGain :
    selectorReplicatorTupleTraj sol La warmGainVal t (selWarmGainCoord d V) = warmGainVal := by
  simp [selectorReplicatorTupleTraj, selWarmGainCoord, Fin.append_right]
  rfl

lemma eval_selRenameZ_tuple_repl (q : MvPolynomial (Fin d) ℚ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t)
        (selRenameZ V q) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) q := by
  rw [selRenameZ, MvPolynomial.eval₂_rename]
  exact MvPolynomial.eval₂_congr
    (f := algebraMap ℚ ℝ) (p := q)
    (g₁ := selectorReplicatorTupleTraj sol La warmGainVal t ∘ selZ V) (g₂ := sol.z t)
    (fun {i} {_c} _hi _hc => selectorReplicatorTupleTraj_z La warmGainVal t i)

lemma eval_selectorMixField_repl (i : Fin d) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t)
        (selectorMixField branch i) =
      selectorMixTarget branch sol.u sol.lam t i := by
  rw [selectorMixField, eval₂_selectorMixFieldPoly]
  simp only [selectorReplicatorTupleTraj_lam, selectorReplicatorTupleTraj_u,
    selectorMixTarget, selectorF]

theorem eval_selChiGatePoly_repl (M : ℕ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t)
        (selChiGatePoly d V M) =
      ((1 + Real.sin t) / 2) ^ M := by
  simp only [selChiGatePoly, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_add, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, MvPolynomial.eval₂_one,
    selectorReplicatorTupleTraj_s, map_div₀, map_one, map_ofNat]
  ring_nf

theorem eval_selChiResetPoly_repl (M : ℕ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t)
        (selChiResetPoly d V M) =
      ((1 + Real.cos t) / 2) ^ M := by
  simp only [selChiResetPoly, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_add, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, MvPolynomial.eval₂_one,
    selectorReplicatorTupleTraj_c, map_div₀, map_one, map_ofNat]
  ring_nf

theorem eval_selKappaPoly_repl (κ₀ : ℚ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t)
        (selKappaPoly d V κ₀) = (κ₀ : ℝ) := by
  simp [selKappaPoly]

theorem eval_selGainPoly_repl :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t)
        (selGainPoly d V) =
      warmGainVal * sol.α t := by
  simp [selGainPoly, selectorReplicatorTupleTraj_warmGain, selectorReplicatorTupleTraj_alpha]

end Trajectory

private lemma repl_hasDerivAt_fin_append {m n : ℕ}
    {f : ℝ → Fin m → ℝ} {g : ℝ → Fin n → ℝ}
    {f' : Fin m → ℝ} {g' : Fin n → ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun τ => Fin.append (f τ) (g τ)) (Fin.append f' g') t := by
  apply hasDerivAt_pi.mpr
  intro i
  refine Fin.addCases (m := m) (n := n) ?_ ?_ i
  · intro k
    simpa [Fin.append_left] using hasDerivAt_pi.mp hf k
  · intro k
    simpa [Fin.append_right] using hasDerivAt_pi.mp hg k

private noncomputable def selRPulseDeriv (L : ℕ) (t : ℝ) : ℝ :=
  (L : ℝ) * ((1 - Real.sin t) / 2) ^ (L - 1) * (-(Real.cos t / 2))

private noncomputable def selQPulseDeriv (L : ℕ) (t : ℝ) : ℝ :=
  (L : ℝ) * ((1 + Real.sin t) / 2) ^ (L - 1) * (Real.cos t / 2)

private lemma sel_hasDerivAt_rPulse (L : ℕ) (t : ℝ) :
    HasDerivAt (fun τ => rPulse L τ) (selRPulseDeriv L t) t := by
  unfold rPulse selRPulseDeriv
  have hbase : HasDerivAt (fun τ : ℝ => (1 - Real.sin τ) / 2) (-(Real.cos t / 2)) t := by
    convert ((hasDerivAt_const (x := t) (c := (1 : ℝ))).sub
      (Real.hasDerivAt_sin t)).div_const 2 using 1 <;> ring
  simpa using hbase.pow L

private lemma sel_hasDerivAt_qPulse (L : ℕ) (t : ℝ) :
    HasDerivAt (fun τ => qPulse L τ) (selQPulseDeriv L t) t := by
  unfold qPulse selQPulseDeriv
  have hbase : HasDerivAt (fun τ : ℝ => (1 + Real.sin τ) / 2) (Real.cos t / 2) t := by
    convert ((hasDerivAt_const (x := t) (c := (1 : ℝ))).add
      (Real.hasDerivAt_sin t)).div_const 2 using 1 <;> ring
  simpa using hbase.pow L

section ODE

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}

private lemma sel_hasDerivAt_bGateZ
    (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {cμ : ℚ} (hcμ : p.cμ = (cμ : ℝ)) (t : ℝ) (ht : t ∈ sched.domain) :
    HasDerivAt (fun τ => bGateZ p.L (sol.μ τ) τ)
      (-( (cμ : ℝ) * rPulse p.L t + sol.μ t * selRPulseDeriv p.L t) *
        bGateZ p.L (sol.μ t) t) t := by
  unfold bGateZ
  have hμ : HasDerivAt sol.μ (cμ : ℝ) t := by
    simpa [hcμ] using sol.μ_hasDeriv t ht
  have hmul := hμ.mul (sel_hasDerivAt_rPulse p.L t)
  have hneg : HasDerivAt (fun τ : ℝ => -(sol.μ τ * rPulse p.L τ))
      (-((cμ : ℝ) * rPulse p.L t + sol.μ t * selRPulseDeriv p.L t)) t := by
    simpa [neg_add_rev] using hmul.neg
  have h := hneg.exp
  convert h using 1 <;> ring

private lemma sel_hasDerivAt_bGateU
    (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {cμ : ℚ} (hcμ : p.cμ = (cμ : ℝ)) (t : ℝ) (ht : t ∈ sched.domain) :
    HasDerivAt (fun τ => bGateU p.L (sol.μ τ) τ)
      (-( (cμ : ℝ) * qPulse p.L t + sol.μ t * selQPulseDeriv p.L t) *
        bGateU p.L (sol.μ t) t) t := by
  unfold bGateU
  have hμ : HasDerivAt sol.μ (cμ : ℝ) t := by
    simpa [hcμ] using sol.μ_hasDeriv t ht
  have hmul := hμ.mul (sel_hasDerivAt_qPulse p.L t)
  have hneg : HasDerivAt (fun τ : ℝ => -(sol.μ τ * qPulse p.L τ))
      (-((cμ : ℝ) * qPulse p.L t + sol.μ t * selQPulseDeriv p.L t)) t := by
    simpa [neg_add_rev] using hmul.neg
  have h := hneg.exp
  convert h using 1 <;> ring

end ODE

section ReplicatorAssembledFieldCoordinates

variable {d B : ℕ} {V : Type} [Fintype V] (branch : V → BranchData d B)
  (chiReset chiGate kappa gainPoly : MvPolynomial (Fin (selectorDim d V)) ℚ)
  (Ppoly : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
  (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ)

private lemma selectorReplicatorAssembledField_s :
    selectorReplicatorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP
        A K cμ cα L R (selOfContract V (contractS d)) =
      X (selOfContract V (contractC d)) := by
  simp [selectorReplicatorAssembledField, selOfContract, contractS]

private lemma selectorReplicatorAssembledField_c :
    selectorReplicatorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP
        A K cμ cα L R (selOfContract V (contractC d)) =
      -X (selOfContract V (contractS d)) := by
  simp [selectorReplicatorAssembledField, selOfContract, contractC, contractS]

private lemma selectorReplicatorAssembledField_mu :
    selectorReplicatorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP
        A K cμ cα L R (selOfContract V (contractMu d)) =
      C cμ := by
  simp [selectorReplicatorAssembledField, selOfContract, contractMu, contractS]

private lemma selectorReplicatorAssembledField_alpha :
    selectorReplicatorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP
        A K cμ cα L R (selOfContract V (contractAlpha d)) =
      C cα * X (selOfContract V (contractAlpha d)) := by
  simp [selectorReplicatorAssembledField, selOfContract, contractAlpha, contractS]

private lemma selectorReplicatorAssembledField_bz :
    selectorReplicatorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP
        A K cμ cα L R (selOfContract V (contractGateZ d)) =
      -((C cμ * selRP d V L + X (selOfContract V (contractMu d)) * selRPderiv d V L) *
        X (selOfContract V (contractGateZ d))) := by
  simp [selectorReplicatorAssembledField, selOfContract, contractGateZ]

private lemma selectorReplicatorAssembledField_bu :
    selectorReplicatorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP
        A K cμ cα L R (selOfContract V (contractGateU d)) =
      -((C cμ * selQP d V L + X (selOfContract V (contractMu d)) * selQPderiv d V L) *
        X (selOfContract V (contractGateU d))) := by
  simp [selectorReplicatorAssembledField, selOfContract, contractGateU]

private lemma selectorReplicatorAssembledField_z (i : Fin d) :
    selectorReplicatorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP
        A K cμ cα L R (selZ V i) =
      C A * X (selOfContract V (contractAlpha d)) *
        X (selOfContract V (contractGateZ d)) *
        (selectorMixField branch i - X (selZ V i)) := by
  simp [selectorReplicatorAssembledField, selZ, selOfContract, contractZ, contractTailZ]

private lemma selectorReplicatorAssembledField_u (i : Fin d) :
    selectorReplicatorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP
        A K cμ cα L R (selU V i) =
      C A * X (selOfContract V (contractAlpha d)) *
        X (selOfContract V (contractGateU d)) *
        (X (selZ V i) - X (selU V i)) := by
  simp [selectorReplicatorAssembledField, selU, selZ, selOfContract, contractU, contractTailU]

private lemma selectorReplicatorAssembledField_a :
    selectorReplicatorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP
        A K cμ cα L R (selOfContract V (contractA d)) =
      C K * ((C (1 / 2 : ℚ) * (1 - X (selOfContract V (contractC d)))) ^ R) *
        (selRenameZ V HP - X (selOfContract V (contractA d))) := by
  simp [selectorReplicatorAssembledField, selOfContract, contractA, contractTailA]

private lemma selectorReplicatorAssembledField_lam (v : V) :
    selectorReplicatorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP
        A K cμ cα L R (selLamCoord v) =
      selectorReplicatorFieldSelLamPoly chiReset chiGate kappa gainPoly Ppoly v := by
  simp only [selectorReplicatorAssembledField, selLamCoord, Fin.append_right, Fin.append_left,
    Equiv.symm_apply_apply]

private lemma selectorReplicatorAssembledField_G :
    selectorReplicatorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP
        A K cμ cα L R (selGCoord d V) =
      selectorGainFieldPoly chiGate gainPoly := by
  simp [selectorReplicatorAssembledField, selGCoord, Fin.append_right]
  rfl

private lemma selectorReplicatorAssembledField_warmGain :
    selectorReplicatorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP
        A K cμ cα L R (selWarmGainCoord d V) = 0 := by
  simp [selectorReplicatorAssembledField, selWarmGainCoord, Fin.append_right, Fin.append_left]
  rfl

end ReplicatorAssembledFieldCoordinates

section ODE

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}

theorem selectorReplicatorTupleTraj_ode
    (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : SelectorReplicatorHaltLatchSol sol Hval K R)
    (warmGainVal : ℝ)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    {Aq Kq cμq cαq : ℚ} {L : ℕ}
    (hA : p.A = (Aq : ℝ)) (hK : K = (Kq : ℝ))
    (hcμ : p.cμ = (cμq : ℝ)) (hcα : p.cα = (cαq : ℝ)) (hL : p.L = L)
    (hdomain : ∀ t : ℝ, 0 ≤ t → t ∈ sched.domain)
    (h_chiReset : ∀ t : ℝ, 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t) chiResetP =
        chiResetF t)
    (h_chiGate : ∀ t : ℝ, 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t) chiGateP =
        chiGateF t)
    (h_kappa : ∀ t : ℝ, 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t) kappaP =
        kappaF t)
    (h_gain : ∀ t : ℝ, 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t) gainP =
        gainF t)
    (h_P : ∀ (v : V) (t : ℝ), 0 ≤ t →
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t) (PpolyP v) =
        Pv v (sol.u t))
    (h_HP : ∀ t : ℝ,
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) HP = Hval (sol.z t)) :
    ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (selectorReplicatorTupleTraj sol La warmGainVal)
        (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
          (selectorReplicatorTupleTraj sol La warmGainVal t)
          (selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
            PpolyP HP Aq Kq cμq cαq L R i)) t := by
  intro t ht
  have htd : t ∈ sched.domain := hdomain t ht
  let core' : Fin 4 → ℝ := fun k =>
    if k = 0 then Real.cos t else
    if k = 1 then -Real.sin t else
    if k = 2 then (cμq : ℝ) else (cαq : ℝ) * sol.α t
  let gate' : Fin 2 → ℝ := fun k =>
    if k = 0 then
      -(((cμq : ℝ) * rPulse L t + sol.μ t * selRPulseDeriv L t) * bGateZ L (sol.μ t) t)
    else
      -(((cμq : ℝ) * qPulse L t + sol.μ t * selQPulseDeriv L t) * bGateU L (sol.μ t) t)
  let z' : Fin d → ℝ := fun i =>
    (Aq : ℝ) * sol.α t * bGateZ L (sol.μ t) t *
      (selectorMixTarget branch sol.u sol.lam t i - sol.z t i)
  let u' : Fin d → ℝ := fun i =>
    (Aq : ℝ) * sol.α t * bGateU L (sol.μ t) t * (sol.z t i - sol.u t i)
  let a' : Fin 1 → ℝ := fun _ =>
    (Kq : ℝ) * gPulse R t * (Hval (sol.z t) - La.a t)
  let lam' : Fin (Fintype.card V) → ℝ := fun k =>
    chiResetF t * kappaF t *
        (1 / (Fintype.card V : ℝ) - sol.lam ((Fintype.equivFin V).symm k) t)
      + chiGateF t * gainF t * sol.lam ((Fintype.equivFin V).symm k) t *
        (Pv ((Fintype.equivFin V).symm k) (sol.u t)
          - ∑ w : V, sol.lam w t * Pv w (sol.u t))
  let G' : Fin 1 → ℝ := fun _ => chiGateF t * gainF t
  let warmGain' : Fin 1 → ℝ := fun _ => 0
  have hcore :
      HasDerivAt
        (fun τ => fun k : Fin 4 =>
          if k = 0 then Real.sin τ else
          if k = 1 then Real.cos τ else
          if k = 2 then sol.μ τ else sol.α τ)
        core' t := by
    apply hasDerivAt_pi.mpr
    intro k
    fin_cases k
    · simpa [core'] using Real.hasDerivAt_sin t
    · simpa [core'] using Real.hasDerivAt_cos t
    · simpa [core', hcμ] using sol.μ_hasDeriv t htd
    · have hα : HasDerivAt sol.α ((cαq : ℝ) * sol.α t) t := by
        simpa [hcα] using sol.α_hasDeriv t htd
      simpa [core'] using hα
  have hgate :
      HasDerivAt
        (fun τ => fun k : Fin 2 =>
          if k = 0 then bGateZ L (sol.μ τ) τ else bGateU L (sol.μ τ) τ)
        gate' t := by
    subst L
    apply hasDerivAt_pi.mpr
    intro k
    fin_cases k
    · convert sel_hasDerivAt_bGateZ sol hcμ t htd using 1
      simp [gate']
      ring_nf
    · convert sel_hasDerivAt_bGateU sol hcμ t htd using 1
      simp [gate']
      ring_nf
  have hz : HasDerivAt (fun τ => sol.z τ) z' t := by
    apply hasDerivAt_pi.mpr
    intro i
    have hz_i := sol.z_hasDeriv t htd i
    convert hz_i using 1
    simp [z', hA, hL]
  have hu : HasDerivAt (fun τ => sol.u τ) u' t := by
    apply hasDerivAt_pi.mpr
    intro i
    have hu_i := sol.u_hasDeriv t htd i
    convert hu_i using 1
    simp [u', hA, hL]
  have ha : HasDerivAt (fun τ => fun _ : Fin 1 => La.a τ) a' t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    have ha0 := La.ode_a t
    convert ha0 using 1
    simp [a', hK]
  have hlam :
      HasDerivAt
        (fun τ => fun k : Fin (Fintype.card V) =>
          sol.lam ((Fintype.equivFin V).symm k) τ)
        lam' t := by
    apply hasDerivAt_pi.mpr
    intro k
    have hd := sol.lam_hasDeriv ((Fintype.equivFin V).symm k) t htd
    simpa [lam'] using hd
  have hG : HasDerivAt (fun τ => fun _ : Fin 1 => sol.G τ) G' t := by
    apply hasDerivAt_pi.mpr
    intro k
    fin_cases k
    have hd := sol.G_hasDeriv t htd
    simpa [G'] using hd
  have hWG : HasDerivAt (fun _ => fun _ : Fin 1 => warmGainVal) warmGain' t := by
    apply hasDerivAt_pi.mpr
    intro k
    fin_cases k
    simpa [warmGain'] using hasDerivAt_const t warmGainVal
  have hraw :
      HasDerivAt (selectorReplicatorTupleTraj sol La warmGainVal)
        (Fin.append
          (Fin.append core' (Fin.append gate' (Fin.append z' (Fin.append u' a'))))
          (Fin.append lam' (Fin.append G' warmGain'))) t := by
    subst L
    simpa [selectorReplicatorTupleTraj, core', gate', z', u', a', lam', G', warmGain'] using
      repl_hasDerivAt_fin_append
        (repl_hasDerivAt_fin_append hcore
          (repl_hasDerivAt_fin_append hgate
            (repl_hasDerivAt_fin_append hz (repl_hasDerivAt_fin_append hu ha))))
        (repl_hasDerivAt_fin_append hlam (repl_hasDerivAt_fin_append hG hWG))
  refine hraw.congr_deriv ?_
  funext j
  refine Fin.addCases (m := contractDim d) (n := selectorTailDim V) ?_ ?_ j
  · intro jc
    simp only [Fin.append_left]
    refine Fin.addCases (m := 4) (n := contractGateTailDim d) ?_ ?_ jc
    · intro k
      fin_cases k
      · change core' 0 =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t)
            (selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
              PpolyP HP Aq Kq cμq cαq L R (selOfContract V (contractS d)))
        simp [core', selectorReplicatorAssembledField_s]
      · change core' 1 =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t)
            (selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
              PpolyP HP Aq Kq cμq cαq L R (selOfContract V (contractC d)))
        simp [core', selectorReplicatorAssembledField_c]
      · change core' 2 =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t)
            (selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
              PpolyP HP Aq Kq cμq cαq L R (selOfContract V (contractMu d)))
        simp [core', selectorReplicatorAssembledField_mu]
      · change core' 3 =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t)
            (selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
              PpolyP HP Aq Kq cμq cαq L R (selOfContract V (contractAlpha d)))
        simp [core', selectorReplicatorAssembledField_alpha]
    · intro tail0
      refine Fin.addCases (m := 2) (n := contractTailDim d) ?_ ?_ tail0
      · intro k
        fin_cases k
        · simp only [Fin.append_left, Fin.append_right]
          change gate' 0 =
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t)
              (selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
                PpolyP HP Aq Kq cμq cαq L R (selOfContract V (contractGateZ d)))
          subst L
          simp [gate', selectorReplicatorAssembledField_bz, selRP, selRPderiv, rPulse,
            selRPulseDeriv]
          left
          ring_nf
        · simp only [Fin.append_left, Fin.append_right]
          change gate' 1 =
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t)
              (selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
                PpolyP HP Aq Kq cμq cαq L R (selOfContract V (contractGateU d)))
          subst L
          simp [gate', selectorReplicatorAssembledField_bu, selQP, selQPderiv, qPulse,
            selQPulseDeriv]
          left
          ring_nf
      · intro tail
        refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
        · intro i
          simp only [Fin.append_left, Fin.append_right]
          change z' i =
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t)
              (selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
                PpolyP HP Aq Kq cμq cαq L R (selZ V i))
          simp [z', selectorReplicatorAssembledField_z, eval_selectorMixField_repl, hL]
        · intro tail2
          refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
          · intro i
            simp only [Fin.append_left, Fin.append_right]
            change u' i =
              MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t)
                (selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
                  PpolyP HP Aq Kq cμq cαq L R (selU V i))
            simp [u', selectorReplicatorAssembledField_u,
              selectorReplicatorTupleTraj_z, selectorReplicatorTupleTraj_u,
              selectorReplicatorTupleTraj_alpha, selectorReplicatorTupleTraj_bu,
              eval₂_mul, eval₂_sub, eval₂_C, eval₂_X, eq_ratCast, hL] <;> ring
          · intro k
            fin_cases k
            simp only [Fin.append_left, Fin.append_right]
            change a' 0 =
              MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t)
                (selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
                  PpolyP HP Aq Kq cμq cαq L R (selOfContract V (contractA d)))
            simp [a', selectorReplicatorAssembledField_a, gPulse, eval_selRenameZ_tuple_repl,
              h_HP]
            exact Or.inl (Or.inl (by ring))
  · intro jt
    simp only [Fin.append_right]
    refine Fin.addCases (m := Fintype.card V) (n := 1 + 1) ?_ ?_ jt
    · intro k
      simp only [Fin.append_left]
      have hfield :
          selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
              PpolyP HP Aq Kq cμq cαq L R
              (Fin.natAdd (contractDim d) (Fin.castAdd 2 k)) =
            selectorReplicatorFieldSelLamPoly chiResetP chiGateP kappaP gainP
              PpolyP ((Fintype.equivFin V).symm k) := by
        simp only [selectorReplicatorAssembledField, Fin.append_right, Fin.append_left]
      rw [hfield]
      simp only [selectorReplicatorFieldSelLamPoly]
      rw [eval₂_selectorReplicatorFieldPoly]
      simp only [selectorReplicatorTupleTraj_lam, h_chiReset t ht, h_chiGate t ht,
        h_kappa t ht, h_gain t ht, h_P _ t ht, lam']
    · intro jGwG
      refine Fin.addCases (m := 1) (n := 1) ?_ ?_ jGwG
      · intro k
        fin_cases k
        simp only [Fin.append_right, Fin.append_left]
        change G' 0 =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t)
            (selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
              PpolyP HP Aq Kq cμq cαq L R (selGCoord d V))
        rw [selectorReplicatorAssembledField_G, eval₂_selectorGainFieldPoly]
        simp only [h_chiGate t ht, h_gain t ht, G']
      · intro k
        fin_cases k
        simp only [Fin.append_right]
        change warmGain' 0 =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t)
            (selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
              PpolyP HP Aq Kq cμq cαq L R (selWarmGainCoord d V))
        rw [selectorReplicatorAssembledField_warmGain]
        simp [warmGain']

end ODE

section Init

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}

theorem selectorReplicatorTupleTraj_zero
    (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : SelectorReplicatorHaltLatchSol sol Hval K R)
    (warmGainVal : ℝ)
    (hμ0 : sol.μ 0 = 0) (hα0 : sol.α 0 = 1) :
    selectorReplicatorTupleTraj sol La warmGainVal 0 =
      Fin.append
        (Fin.append
          (fun k : Fin 4 =>
            if k = 0 then 0 else if k = 1 then 1 else if k = 2 then 0 else 1)
          (Fin.append
            (fun _ : Fin 2 => 1)
            (Fin.append (sol.z 0) (Fin.append (sol.u 0) (fun _ : Fin 1 => La.a 0)))))
        (Fin.append
          (fun k : Fin (Fintype.card V) => sol.lam ((Fintype.equivFin V).symm k) 0)
          (Fin.append
            (fun _ : Fin 1 => sol.G 0)
            (fun _ : Fin 1 => warmGainVal))) := by
  funext j
  refine Fin.addCases (m := contractDim d) (n := selectorTailDim V) ?_ ?_ j
  · intro jc
    simp only [Fin.append_left]
    refine Fin.addCases (m := 4) (n := contractGateTailDim d) ?_ ?_ jc
    · intro k
      fin_cases k <;>
        simp [selectorReplicatorTupleTraj, selOfContract, contractS, contractC, contractMu,
          contractAlpha, hμ0, hα0]
    · intro tail0
      refine Fin.addCases (m := 2) (n := contractTailDim d) ?_ ?_ tail0
      · intro k
        fin_cases k <;>
          simp [selectorReplicatorTupleTraj, selOfContract, contractGateZ, contractGateU,
            bGateZ, bGateU, hμ0]
      · intro tail
        refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
        · intro i
          simp [selectorReplicatorTupleTraj, selOfContract, contractZ, contractTailZ]
        · intro tail2
          refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
          · intro i
            simp [selectorReplicatorTupleTraj, selOfContract, contractU, contractTailU]
          · intro a
            fin_cases a
            simp [selectorReplicatorTupleTraj, selOfContract, contractA, contractTailA]
  · intro jt
    simp only [Fin.append_right]
    refine Fin.addCases (m := Fintype.card V) (n := 1 + 1) ?_ ?_ jt
    · intro k
      simp only [Fin.append_left]
      simp [selectorReplicatorTupleTraj, Fin.append_right, Fin.append_left]
    · intro jGwG
      refine Fin.addCases (m := 1) (n := 1) ?_ ?_ jGwG
      · intro a
        fin_cases a
        simp [selectorReplicatorTupleTraj, Fin.append_right, Fin.append_left]
      · intro a
        fin_cases a
        simp [selectorReplicatorTupleTraj, Fin.append_right]

def selectorReplicatorSphereInitQ (d : ℕ) (V : Type) [Fintype V]
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ) :
    Fin (selectorDim d V + 1) → ℚ :=
  let x := selectorReplicatorEuclInitQ d V x₀ w warmGainInit
  let den : ℚ := (∑ i : Fin (selectorDim d V), x i ^ 2) + 1
  Fin.cases (((∑ i : Fin (selectorDim d V), x i ^ 2) - 1) / den)
    (fun i => 2 * x i / den)

theorem selectorReplicatorTupleTraj_zero_eq_selectorReplicatorEuclInitQ
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit : ℚ)
    (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : SelectorReplicatorHaltLatchSol sol Hval K R)
    (hμ0 : sol.μ 0 = 0) (hα0 : sol.α 0 = 1)
    (hz0 : ∀ i : Fin d, sol.z 0 i = ((x₀ w i : ℚ) : ℝ))
    (hu0 : ∀ i : Fin d, sol.u 0 i = ((x₀ w i : ℚ) : ℝ))
    (hlam0 : ∀ v : V, sol.lam v 0 = ((1 / (Fintype.card V : ℚ)) : ℝ))
    (hG0 : sol.G 0 = 0) (ha0 : La.a 0 = 0) :
    selectorReplicatorTupleTraj sol La (warmGainInit : ℝ) 0 =
      fun i => ((selectorReplicatorEuclInitQ d V x₀ w warmGainInit i : ℚ) : ℝ) := by
  rw [selectorReplicatorTupleTraj_zero sol La (warmGainInit : ℝ) hμ0 hα0]
  funext j
  refine Fin.addCases (m := contractDim d) (n := selectorTailDim V) ?_ ?_ j
  · intro jc
    simp only [Fin.append_left]
    refine Fin.addCases (m := 4) (n := contractGateTailDim d) ?_ ?_ jc
    · intro k
      fin_cases k <;> simp [selectorReplicatorEuclInitQ]
    · intro tail0
      refine Fin.addCases (m := 2) (n := contractTailDim d) ?_ ?_ tail0
      · intro k
        fin_cases k <;> simp [selectorReplicatorEuclInitQ]
      · intro tail
        refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
        · intro i
          simp [selectorReplicatorEuclInitQ, hz0 i]
        · intro tail2
          refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
          · intro i
            simp [selectorReplicatorEuclInitQ, hu0 i]
          · intro a
            fin_cases a
            simp [selectorReplicatorEuclInitQ, ha0]
  · intro jt
    simp only [Fin.append_right]
    refine Fin.addCases (m := Fintype.card V) (n := 1 + 1) ?_ ?_ jt
    · intro k
      simp [selectorReplicatorEuclInitQ, hlam0]
    · intro jGwG
      refine Fin.addCases (m := 1) (n := 1) ?_ ?_ jGwG
      · intro a
        fin_cases a
        simp [Fin.addCases, Fin.append, selectorReplicatorEuclInitQ, hG0]
      · intro a
        fin_cases a
        simp [Fin.addCases, Fin.append, selectorReplicatorEuclInitQ]

end Init

structure SelectorReplicatorPolynomialFieldPackage
    (d B : ℕ) (V : Type) [Fintype V]
    (p : DynGateParams) (sched : PhaseSchedule) (branch : V → BranchData d B)
    (chiResetF chiGateF kappaF gainF : ℝ → ℝ) (Pv : V → (Fin d → ℝ) → ℝ)
    (Hval : (Fin d → ℝ) → ℝ) (K : ℝ) (R : ℕ) where
  nE : ℕ
  field : Fin nE → MvPolynomial (Fin nE) ℚ
  tuple :
    ∀ (_w : ℕ)
      (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv),
      SelectorReplicatorHaltLatchSol sol Hval K R → ℝ → Fin nE → ℝ
  tuple_ode :
    ∀ (w : ℕ)
      (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
      (La : SelectorReplicatorHaltLatchSol sol Hval K R) (t : ℝ), 0 ≤ t →
        HasDerivAt (tuple w sol La)
          (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
            (tuple w sol La t) (field i)) t
  init : ℕ → Fin (nE + 1) → ℚ
  init_presented : ∃ f : ℕ → Fin (nE + 1) → ℤ × ℕ, Computable f ∧
    ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ)
  init_zero :
    ∀ (w : ℕ)
      (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
      (La : SelectorReplicatorHaltLatchSol sol Hval K R),
        ((init w 0 : ℚ) : ℝ) =
          ((∑ i : Fin nE, tuple w sol La 0 i ^ 2) - 1) /
            ((∑ i : Fin nE, tuple w sol La 0 i ^ 2) + 1)
  init_succ :
    ∀ (w : ℕ)
      (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
      (La : SelectorReplicatorHaltLatchSol sol Hval K R) (i : Fin nE),
        ((init w i.succ : ℚ) : ℝ) =
          2 * tuple w sol La 0 i /
            ((∑ k : Fin nE, tuple w sol La 0 k ^ 2) + 1)
  latchCoord : Fin nE
  latch_value :
    ∀ (w : ℕ)
      (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
      (La : SelectorReplicatorHaltLatchSol sol Hval K R) (t : ℝ),
        tuple w sol La t latchCoord = La.a t

section PackageBuild

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}

def selectorReplicatorPolynomialFieldPackage
    (warmGainFn : ℕ → ℝ)
    (chiResetP chiGateP kappaP gainP : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (PpolyP : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L : ℕ)
    (hA : p.A = (Aq : ℝ)) (hK : K = (Kq : ℝ))
    (hcμ : p.cμ = (cμq : ℝ)) (hcα : p.cα = (cαq : ℝ)) (hL : p.L = L)
    (hdomain : ∀ t : ℝ, 0 ≤ t → t ∈ sched.domain)
    (h_chiReset :
      ∀ (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorReplicatorHaltLatchSol sol Hval K R) (wgv : ℝ) (t : ℝ), 0 ≤ t →
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La wgv t) chiResetP =
          chiResetF t)
    (h_chiGate :
      ∀ (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorReplicatorHaltLatchSol sol Hval K R) (wgv : ℝ) (t : ℝ), 0 ≤ t →
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La wgv t) chiGateP =
          chiGateF t)
    (h_kappa :
      ∀ (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorReplicatorHaltLatchSol sol Hval K R) (wgv : ℝ) (t : ℝ), 0 ≤ t →
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La wgv t) kappaP =
          kappaF t)
    (h_gain :
      ∀ (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorReplicatorHaltLatchSol sol Hval K R) (w : ℕ) (t : ℝ), 0 ≤ t →
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La (warmGainFn w) t) gainP =
          gainF t)
    (h_P :
      ∀ (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorReplicatorHaltLatchSol sol Hval K R) (wgv : ℝ) (v : V) (t : ℝ), 0 ≤ t →
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La wgv t) (PpolyP v) =
          Pv v (sol.u t))
    (h_HP :
      ∀ (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorReplicatorHaltLatchSol sol Hval K R) (t : ℝ),
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) HP = Hval (sol.z t))
    (init : ℕ → Fin (selectorDim d V + 1) → ℚ)
    (init_presented : ∃ f : ℕ → Fin (selectorDim d V + 1) → ℤ × ℕ, Computable f ∧
      ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorReplicatorHaltLatchSol sol Hval K R),
          ((init w 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim d V), selectorReplicatorTupleTraj sol La (warmGainFn w) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim d V), selectorReplicatorTupleTraj sol La (warmGainFn w) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorReplicatorHaltLatchSol sol Hval K R) (i : Fin (selectorDim d V)),
          ((init w i.succ : ℚ) : ℝ) =
            2 * selectorReplicatorTupleTraj sol La (warmGainFn w) 0 i /
              ((∑ k : Fin (selectorDim d V), selectorReplicatorTupleTraj sol La (warmGainFn w) 0 k ^ 2) + 1)) :
    SelectorReplicatorPolynomialFieldPackage d B V p sched branch
      chiResetF chiGateF kappaF gainF Pv Hval K R :=
  { nE := selectorDim d V
    field := selectorReplicatorAssembledField d B V branch chiResetP chiGateP kappaP gainP
      PpolyP HP Aq Kq cμq cαq L R
    tuple := fun w sol La => selectorReplicatorTupleTraj sol La (warmGainFn w)
    tuple_ode := by
      intro w sol La t ht
      exact selectorReplicatorTupleTraj_ode sol La (warmGainFn w) chiResetP chiGateP kappaP gainP PpolyP HP
        hA hK hcμ hcα hL hdomain
        (fun t ht => h_chiReset sol La _ t ht) (fun t ht => h_chiGate sol La _ t ht)
        (fun t ht => h_kappa sol La _ t ht) (fun t ht => h_gain sol La w t ht)
        (fun v t ht => h_P sol La _ v t ht) (fun t => h_HP sol La t) t ht
    init := init
    init_presented := init_presented
    init_zero := init_zero
    init_succ := init_succ
    latchCoord := selOfContract V (contractA d)
    latch_value := by
      intro w sol La t
      simp [selectorReplicatorTupleTraj_a] }

end PackageBuild

noncomputable def selector_replicator_zero_latch_solution
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    (R : ℕ) :
    SelectorReplicatorHaltLatchSol sol (fun _ : (Fin d → ℝ) => (0 : ℝ)) 0 R := by
  refine { a := fun _ => 0, init_a := rfl, ode_a := ?_ }
  intro t
  simpa using (hasDerivAt_const (x := t) (c := (0 : ℝ)))

private theorem stereo_sum_sq {nE : ℕ} (x : Fin nE → ℝ) :
    (∑ j : Fin (nE + 1), stereo x j ^ 2) = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [stereo, Fin.cases_zero, Fin.cases_succ]
  set r : ℝ := ∑ i : Fin nE, x i ^ 2 with hr
  have hden : r + 1 ≠ 0 := by
    have hr0 : 0 ≤ r := by
      dsimp [r]
      exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)
    nlinarith
  have htail :
      (∑ i : Fin nE, (2 * x i / (r + 1)) ^ 2) =
        4 * r / (r + 1) ^ 2 := by
    simp only [div_pow, mul_pow]
    calc
      (∑ i : Fin nE, (2 ^ 2 * x i ^ 2) / (r + 1) ^ 2)
          = (∑ i : Fin nE, (4 / (r + 1) ^ 2) * x i ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = (4 / (r + 1) ^ 2) * r := by
            rw [← Finset.mul_sum]
      _ = 4 * r / (r + 1) ^ 2 := by ring
  simp only [stereoDenom, ← hr]
  rw [htail]
  field_simp [hden]
  ring

private theorem stereo_abs_le_one {nE : ℕ} (x : Fin nE → ℝ)
    (j : Fin (nE + 1)) : |stereo x j| ≤ 1 := by
  have hterm :
      stereo x j ^ 2 ≤ ∑ k : Fin (nE + 1), stereo x k ^ 2 :=
    Finset.single_le_sum
      (fun k _hk => sq_nonneg (stereo x k))
      (Finset.mem_univ j)
  have hsq : stereo x j ^ 2 ≤ 1 := by
    simpa [stereo_sum_sq x] using hterm
  exact (sq_le_one_iff_abs_le_one (stereo x j)).mp hsq

theorem main_assembled_dyn_selector_zreadout_nolatch_repl_of_sol_init
    {d B : ℕ} {Conf : Type} [Primcodable Conf]
    (M : UndecidableMachine Conf)
    (p : DynGateParams) (sched : PhaseSchedule)
    {V : Type} [Fintype V] (branch : V → BranchData d B)
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}
    {R nE : ℕ}
    (field : Fin nE → MvPolynomial (Fin nE) ℚ)
    (tuple :
      ∀ (_w : ℕ)
        (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv),
        SelectorReplicatorHaltLatchSol sol (fun _ : (Fin d → ℝ) => (0 : ℝ)) 0 R →
          ℝ → Fin nE → ℝ)
    (tuple_ode :
      ∀ (w : ℕ)
        (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorReplicatorHaltLatchSol sol (fun _ : (Fin d → ℝ) => (0 : ℝ)) 0 R)
        (t : ℝ), 0 ≤ t →
          HasDerivAt (tuple w sol La)
            (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
              (tuple w sol La t) (field i)) t)
    (init : ℕ → Fin (nE + 1) → ℚ)
    (init_presented : ∃ f : ℕ → Fin (nE + 1) → ℤ × ℕ, Computable f ∧
      ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ))
    (sol : ℕ → SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    (init_zero :
      ∀ (w : ℕ),
        let La := selector_replicator_zero_latch_solution (sol w) R
        ((init w 0 : ℚ) : ℝ) =
          ((∑ i : Fin nE, tuple w (sol w) La 0 i ^ 2) - 1) /
            ((∑ i : Fin nE, tuple w (sol w) La 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ) (i : Fin nE),
        let La := selector_replicator_zero_latch_solution (sol w) R
        ((init w i.succ : ℚ) : ℝ) =
          2 * tuple w (sol w) La 0 i /
            ((∑ k : Fin nE, tuple w (sol w) La 0 k ^ 2) + 1))
    (readCoord : Fin d) (readCoordE : Fin nE)
    (hread_value :
      ∀ (w : ℕ)
        (s : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorReplicatorHaltLatchSol s (fun _ : (Fin d → ℝ) => (0 : ℝ)) 0 R) (t : ℝ),
          tuple w s La t readCoordE = s.z t readCoord)
    (correct_halt_z : ∀ w, M.toDiscreteMachine.haltsOn w →
      ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ (sol w).z t readCoord ∧ (sol w).z t readCoord ≤ 1)
    (correct_nonhalt_z : ∀ w, ¬ M.toDiscreteMachine.haltsOn w →
      ∃ T : ℝ, ∀ t ≥ T, 0 ≤ (sol w).z t readCoord ∧ (sol w).z t readCoord ≤ 1 / 4) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P M) := by
  classical
  let La := fun w => selector_replicator_zero_latch_solution (sol w) R
  obtain ⟨Y, _htang, htransfer⟩ := compactification_exists nE field
  let P : Ripple.BoundedUniversality.GPAC.PIVP ℚ :=
    { n := nE + 1
      vf := Y
      init := init }
  have htrans : ∀ w,
      ∃ s : ℝ → ℝ, s 0 = 0 ∧ StrictMonoOn s (Set.Ici 0) ∧
        Filter.Tendsto s Filter.atTop Filter.atTop ∧
        ∀ τ : ℝ, 0 ≤ τ → HasDerivAt
          (fun σ => stereo (tuple w (sol w) (La w) (s σ)))
          (fun j => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
            (stereo (tuple w (sol w) (La w) (s τ))) (Y j)) τ := by
    intro w
    exact htransfer (tuple w (sol w) (La w)) (tuple_ode w (sol w) (La w))
  choose s hs0 _hsmono hstend hsphere using htrans
  refine ⟨P, ⟨{
    traj := fun w τ => stereo (tuple w (sol w) (La w) (s w τ))
    init_at_zero := ?_
    solves_ode := ?_
    bounded := ?_
    encoder_presented := init_presented
    readout := ?_
    correct_halt := ?_
    correct_nonhalt := ?_
  }⟩⟩
  · intro w
    funext j
    rw [hs0 w]
    dsimp [P, Ripple.BoundedUniversality.GPAC.PIVP.realInit]
    refine Fin.cases ?_ ?_ j
    · simp [stereo, stereoDenom, init_zero w, La]
    · intro i
      simp [stereo, stereoDenom, init_succ w i, La]
  · intro w τ hτ
    simpa [P, Ripple.BoundedUniversality.GPAC.PIVP.evalVF] using hsphere w τ hτ
  · refine ⟨1, by norm_num, ?_⟩
    intro w τ i hτ
    exact stereo_abs_le_one _ _
  · exact { hA := readCoordE.succ, h0 := 0, ne := by simp }
  · intro w hw
    obtain ⟨T, hT⟩ := correct_halt_z w hw
    have hev : ∀ᶠ τ in Filter.atTop, max T 0 ≤ s w τ :=
      (hstend w).eventually (Filter.eventually_ge_atTop (max T 0))
    obtain ⟨Θ, hΘ⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max Θ 0, ?_⟩
    intro τ hτ
    have hΘτ : Θ ≤ τ := le_trans (le_max_left Θ 0) hτ
    have hsge : max T 0 ≤ s w τ := hΘ τ hΘτ
    have hTle : T ≤ s w τ := le_trans (le_max_left T 0) hsge
    have hz := hT (s w τ) hTle
    have hcoord :
        3 / 4 ≤ tuple w (sol w) (La w) (s w τ) readCoordE ∧
          tuple w (sol w) (La w) (s w τ) readCoordE ≤ 1 := by
      simpa [hread_value w (sol w) (La w) (s w τ)] using hz
    have hreg :=
      (stereo_readout_transfer (tuple w (sol w) (La w) (s w τ)) readCoordE).1 hcoord
    simpa [ChartThresholdReadout.HaltRegion, P] using hreg
  · intro w hw
    obtain ⟨T, hT⟩ := correct_nonhalt_z w hw
    have hev : ∀ᶠ τ in Filter.atTop, max T 0 ≤ s w τ :=
      (hstend w).eventually (Filter.eventually_ge_atTop (max T 0))
    obtain ⟨Θ, hΘ⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max Θ 0, ?_⟩
    intro τ hτ
    have hΘτ : Θ ≤ τ := le_trans (le_max_left Θ 0) hτ
    have hsge : max T 0 ≤ s w τ := hΘ τ hΘτ
    have hTle : T ≤ s w τ := le_trans (le_max_left T 0) hsge
    have hz := hT (s w τ) hTle
    have hcoord :
        0 ≤ tuple w (sol w) (La w) (s w τ) readCoordE ∧
          tuple w (sol w) (La w) (s w τ) readCoordE ≤ 1 / 4 := by
      simpa [hread_value w (sol w) (La w) (s w τ)] using hz
    have hreg :=
      (stereo_readout_transfer (tuple w (sol w) (La w) (s w τ)) readCoordE).2 hcoord
    simpa [ChartThresholdReadout.NonhaltRegion, P] using hreg

theorem main_assembled_dyn_selector_zreadout_nolatch_repl
    {d B : ℕ} {Conf : Type} [Primcodable Conf]
    (M : UndecidableMachine Conf)
    (p : DynGateParams) (sched : PhaseSchedule)
    {V : Type} [Fintype V] (branch : V → BranchData d B)
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}
    {R : ℕ}
    (fieldPkg :
      SelectorReplicatorPolynomialFieldPackage d B V p sched branch
        chiResetF chiGateF kappaF gainF Pv
        (fun _ : (Fin d → ℝ) => (0 : ℝ)) 0 R)
    (sol : ℕ → SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    (readCoord : Fin d) (readCoordE : Fin fieldPkg.nE)
    (hread_value :
      ∀ (w : ℕ)
        (s : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
        (La : SelectorReplicatorHaltLatchSol s (fun _ : (Fin d → ℝ) => (0 : ℝ)) 0 R) (t : ℝ),
          fieldPkg.tuple w s La t readCoordE = s.z t readCoord)
    (correct_halt_z : ∀ w, M.toDiscreteMachine.haltsOn w →
      ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ (sol w).z t readCoord ∧ (sol w).z t readCoord ≤ 1)
    (correct_nonhalt_z : ∀ w, ¬ M.toDiscreteMachine.haltsOn w →
      ∃ T : ℝ, ∀ t ≥ T, 0 ≤ (sol w).z t readCoord ∧ (sol w).z t readCoord ≤ 1 / 4) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P M) := by
  classical
  let La := fun w => selector_replicator_zero_latch_solution (sol w) R
  obtain ⟨Y, _htang, htransfer⟩ :=
    compactification_exists fieldPkg.nE fieldPkg.field
  let P : Ripple.BoundedUniversality.GPAC.PIVP ℚ :=
    { n := fieldPkg.nE + 1
      vf := Y
      init := fieldPkg.init }
  have htrans : ∀ w,
      ∃ s : ℝ → ℝ, s 0 = 0 ∧ StrictMonoOn s (Set.Ici 0) ∧
        Filter.Tendsto s Filter.atTop Filter.atTop ∧
        ∀ τ : ℝ, 0 ≤ τ → HasDerivAt
          (fun σ => stereo (fieldPkg.tuple w (sol w) (La w) (s σ)))
          (fun j => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
            (stereo (fieldPkg.tuple w (sol w) (La w) (s τ))) (Y j)) τ := by
    intro w
    exact htransfer (fieldPkg.tuple w (sol w) (La w))
      (fieldPkg.tuple_ode w (sol w) (La w))
  choose s hs0 _hsmono hstend hsphere using htrans
  refine ⟨P, ⟨{
    traj := fun w τ => stereo (fieldPkg.tuple w (sol w) (La w) (s w τ))
    init_at_zero := ?_
    solves_ode := ?_
    bounded := ?_
    encoder_presented := fieldPkg.init_presented
    readout := ?_
    correct_halt := ?_
    correct_nonhalt := ?_
  }⟩⟩
  · intro w
    funext j
    rw [hs0 w]
    dsimp [P, Ripple.BoundedUniversality.GPAC.PIVP.realInit]
    refine Fin.cases ?_ ?_ j
    · simp [stereo, stereoDenom, fieldPkg.init_zero w (sol w) (La w)]
    · intro i
      simp [stereo, stereoDenom, fieldPkg.init_succ w (sol w) (La w) i]
  · intro w τ hτ
    simpa [P, Ripple.BoundedUniversality.GPAC.PIVP.evalVF] using hsphere w τ hτ
  · refine ⟨1, by norm_num, ?_⟩
    intro w τ i hτ
    exact stereo_abs_le_one _ _
  · exact { hA := readCoordE.succ, h0 := 0, ne := by simp }
  · intro w hw
    obtain ⟨T, hT⟩ := correct_halt_z w hw
    have hev : ∀ᶠ τ in Filter.atTop, max T 0 ≤ s w τ :=
      (hstend w).eventually (Filter.eventually_ge_atTop (max T 0))
    obtain ⟨Θ, hΘ⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max Θ 0, ?_⟩
    intro τ hτ
    have hΘτ : Θ ≤ τ := le_trans (le_max_left Θ 0) hτ
    have hsge : max T 0 ≤ s w τ := hΘ τ hΘτ
    have hTle : T ≤ s w τ := le_trans (le_max_left T 0) hsge
    have hz := hT (s w τ) hTle
    have hcoord :
        3 / 4 ≤ fieldPkg.tuple w (sol w) (La w) (s w τ) readCoordE ∧
          fieldPkg.tuple w (sol w) (La w) (s w τ) readCoordE ≤ 1 := by
      simpa [hread_value w (sol w) (La w) (s w τ)] using hz
    have hreg :=
      (stereo_readout_transfer
        (fieldPkg.tuple w (sol w) (La w) (s w τ)) readCoordE).1 hcoord
    simpa [ChartThresholdReadout.HaltRegion, P] using hreg
  · intro w hw
    obtain ⟨T, hT⟩ := correct_nonhalt_z w hw
    have hev : ∀ᶠ τ in Filter.atTop, max T 0 ≤ s w τ :=
      (hstend w).eventually (Filter.eventually_ge_atTop (max T 0))
    obtain ⟨Θ, hΘ⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max Θ 0, ?_⟩
    intro τ hτ
    have hΘτ : Θ ≤ τ := le_trans (le_max_left Θ 0) hτ
    have hsge : max T 0 ≤ s w τ := hΘ τ hΘτ
    have hTle : T ≤ s w τ := le_trans (le_max_left T 0) hsge
    have hz := hT (s w τ) hTle
    have hcoord :
        0 ≤ fieldPkg.tuple w (sol w) (La w) (s w τ) readCoordE ∧
          fieldPkg.tuple w (sol w) (La w) (s w τ) readCoordE ≤ 1 / 4 := by
      simpa [hread_value w (sol w) (La w) (s w τ)] using hz
    have hreg :=
      (stereo_readout_transfer
        (fieldPkg.tuple w (sol w) (La w) (s w τ)) readCoordE).2 hcoord
    simpa [ChartThresholdReadout.NonhaltRegion, P] using hreg

section MU

open MachineInstance

private theorem selectorSchedule_domain_nonneg_repl :
    ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain := by
  intro t ht
  simpa [selectorSchedule] using ht

private theorem bgpParams_A_rat_repl : bgpParams38.A = ((1 : ℚ) : ℝ) := by
  norm_num [bgpParams38]

private theorem bgpParams_cμ_rat_repl : bgpParams38.cμ = ((1000 : ℚ) : ℝ) := by
  norm_num [bgpParams38]

private theorem bgpParams_cα_rat_repl : bgpParams38.cα = ((300 : ℚ) : ℝ) := by
  norm_num [bgpParams38]

private theorem zero_eq_rat_zero_repl : (0 : ℝ) = ((0 : ℚ) : ℝ) := by
  norm_num

private theorem bgpParams_L_eq_repl : bgpParams38.L = 1 := by
  rfl

theorem SelectorReplicatorDynSol.alpha_eq_exp
    {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiReset chiGate kappa gain : ℝ → ℝ} {readoutP : V → (Fin d → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d B V p sched branch chiReset chiGate kappa gain readoutP)
    (hdom : ∀ s : ℝ, 0 ≤ s → s ∈ sched.domain) {t : ℝ} (ht : 0 ≤ t) :
    sol.α t = Real.exp (p.cα * t) := by
  rcases eq_or_lt_of_le ht with h0 | h0
  · rw [← h0]; simp [sol.α_at_zero]
  · set g : ℝ → ℝ := fun s => sol.α s * Real.exp (-(p.cα * s)) with hgdef
    have hgder : ∀ s : ℝ, 0 ≤ s → HasDerivAt g 0 s := by
      intro s hs
      have hα := sol.α_hasDeriv s (hdom s hs)
      have hneg : HasDerivAt (fun τ : ℝ => -(p.cα * τ)) (-(p.cα)) s := by
        simpa using (((hasDerivAt_id s).const_mul p.cα).neg)
      have hprod := hα.mul hneg.exp
      rw [hgdef]
      convert hprod using 1
      ring
    have hdiff : DifferentiableOn ℝ g (Set.Icc 0 t) :=
      fun x hx => (hgder x hx.1).differentiableAt.differentiableWithinAt
    have hderivW : ∀ x ∈ Set.Ico 0 t, derivWithin g (Set.Icc 0 t) x = 0 := by
      intro x hx
      have huniq : UniqueDiffWithinAt ℝ (Set.Icc 0 t) x :=
        (uniqueDiffOn_Icc h0) x (Set.Ico_subset_Icc_self hx)
      exact (hgder x hx.1).hasDerivWithinAt.derivWithin huniq
    have hcst := constant_of_derivWithin_zero hdiff hderivW t (Set.right_mem_Icc.mpr ht)
    have hg0 : g 0 = 1 := by simp [hgdef, sol.α_at_zero]
    have hgt : sol.α t * Real.exp (-(p.cα * t)) = 1 := by
      have h := hcst
      rw [hg0] at h
      exact h
    rw [Real.exp_neg, mul_inv_eq_one₀ (Real.exp_ne_zero _)] at hgt
    exact hgt

theorem eval_muReadoutPoly_repl (eta : ℚ) (heta : 0 < eta)
    {p : DynGateParams} {sched : PhaseSchedule}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    {readoutP : UniversalLocalView → (Fin d_U → ℝ) → ℝ}
    (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView p sched branchU
      chiResetF chiGateF kappaF gainF readoutP)
    {Hval : (Fin d_U → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : SelectorReplicatorHaltLatchSol sol Hval K R) (warmGainVal : ℝ) (t : ℝ) (v : UniversalLocalView) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorReplicatorTupleTraj sol La warmGainVal t)
        (muReadoutPoly eta heta v) =
      universalPval eta heta v (sol.u t) := by
  have hu : (fun i => selectorReplicatorTupleTraj sol La warmGainVal t (selU UniversalLocalView i)) =
      sol.u t := by
    funext i
    exact selectorReplicatorTupleTraj_u (sol := sol) La warmGainVal t i
  rw [muReadoutPoly, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_rename]
  rw [show ((selectorReplicatorTupleTraj sol La warmGainVal t) ∘ (selU UniversalLocalView))
        = (fun i => selectorReplicatorTupleTraj sol La warmGainVal t (selU UniversalLocalView i)) from rfl, hu]
  rw [MvPolynomial.eval₂_C]
  rw [universalPval, LambdaN, evalPoly4]
  norm_num

def muReplicatorSelectorFieldPackage
    (eta : ℚ) (heta : 0 < eta)
    (M : ℕ) (κ₀ g₀ : ℚ)
    (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ)
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim d_U UniversalLocalView + 1) → ℤ × ℕ, Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧
          selectorReplicatorSphereInitQ d_U UniversalLocalView x₀ w g₀ i =
            (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
          branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorReplicatorHaltLatchSol sol (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView x₀ w g₀ 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj sol La (g₀ : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj sol La (g₀ : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (sol : SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
          branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorReplicatorHaltLatchSol sol (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R)
        (i : Fin (selectorDim d_U UniversalLocalView)),
          ((selectorReplicatorSphereInitQ d_U UniversalLocalView x₀ w g₀ i.succ : ℚ) : ℝ) =
            2 * selectorReplicatorTupleTraj sol La (g₀ : ℝ) 0 i /
              ((∑ k : Fin (selectorDim d_U UniversalLocalView),
                selectorReplicatorTupleTraj sol La (g₀ : ℝ) 0 k ^ 2) + 1)) :
    SelectorReplicatorPolynomialFieldPackage d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
      (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta) (fun _ : (Fin d_U → ℝ) => (0 : ℝ)) 0 R :=
  selectorReplicatorPolynomialFieldPackage (fun _ => (g₀ : ℝ))
    (selChiResetPoly d_U UniversalLocalView M)
    (selChiGatePoly d_U UniversalLocalView M)
    (selKappaPoly d_U UniversalLocalView κ₀)
    (selGainPoly d_U UniversalLocalView)
    (muReadoutPoly eta heta) (0 : MvPolynomial (Fin d_U) ℚ)
    (Aq := 1) (Kq := 0) (cμq := 1000) (cαq := 300) (L := 1)
    (hA := bgpParams_A_rat_repl) (hK := zero_eq_rat_zero_repl)
    (hcμ := bgpParams_cμ_rat_repl) (hcα := bgpParams_cα_rat_repl) (hL := bgpParams_L_eq_repl)
    (hdomain := selectorSchedule_domain_nonneg_repl)
    (h_chiReset := fun sol La _wgv t _ht =>
      eval_selChiResetPoly_repl (sol := sol) (La := La) (warmGainVal := _wgv) (t := t) M)
    (h_chiGate := fun sol La _wgv t _ht =>
      eval_selChiGatePoly_repl (sol := sol) (La := La) (warmGainVal := _wgv) (t := t) M)
    (h_kappa := fun sol La _wgv t _ht =>
      eval_selKappaPoly_repl (sol := sol) (La := La) (warmGainVal := _wgv) (t := t) κ₀)
    (h_gain := by
      intro sol La _w t ht
      dsimp only
      rw [eval_selGainPoly_repl, sol.alpha_eq_exp selectorSchedule_domain_nonneg_repl ht])
    (h_P := fun sol La _wgv v t _ht => eval_muReadoutPoly_repl eta heta sol La _wgv t v)
    (h_HP := by
      intro sol La t
      simp)
    (init := fun w => selectorReplicatorSphereInitQ d_U UniversalLocalView x₀ w g₀)
    (init_presented := init_presented)
    (init_zero := init_zero) (init_succ := init_succ)

theorem main_assembled_mu_selector_zreadout_nolatch_repl_of_sol_init
    (eta : ℚ) (heta : 0 < eta)
    (M : ℕ) (κ₀ g₀ : ℚ) (R : ℕ)
    (x₀ : ℕ → Fin d_U → ℚ)
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim d_U UniversalLocalView + 1) → ℤ × ℕ, Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧
          selectorReplicatorSphereInitQ d_U UniversalLocalView x₀ w g₀ i =
            (f w i).1 / ((f w i).2 : ℚ))
    (sol : ℕ → SelectorReplicatorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
      (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (init_zero :
      ∀ (w : ℕ),
        let La := selector_replicator_zero_latch_solution (sol w) R
        ((selectorReplicatorSphereInitQ d_U UniversalLocalView x₀ w g₀ 0 : ℚ) : ℝ) =
          ((∑ i : Fin (selectorDim d_U UniversalLocalView),
              selectorReplicatorTupleTraj (sol w) La (g₀ : ℝ) 0 i ^ 2) - 1) /
            ((∑ i : Fin (selectorDim d_U UniversalLocalView),
              selectorReplicatorTupleTraj (sol w) La (g₀ : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ) (i : Fin (selectorDim d_U UniversalLocalView)),
        let La := selector_replicator_zero_latch_solution (sol w) R
        ((selectorReplicatorSphereInitQ d_U UniversalLocalView x₀ w g₀ i.succ : ℚ) : ℝ) =
          2 * selectorReplicatorTupleTraj (sol w) La (g₀ : ℝ) 0 i /
            ((∑ k : Fin (selectorDim d_U UniversalLocalView),
              selectorReplicatorTupleTraj (sol w) La (g₀ : ℝ) 0 k ^ 2) + 1))
    (correct_halt_z : ∀ w, UniversalMachine.undecidableMachine.toDiscreteMachine.haltsOn w →
      ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ (sol w).z t haltCoordU ∧ (sol w).z t haltCoordU ≤ 1)
    (correct_nonhalt_z : ∀ w, ¬ UniversalMachine.undecidableMachine.toDiscreteMachine.haltsOn w →
      ∃ T : ℝ, ∀ t ≥ T, 0 ≤ (sol w).z t haltCoordU ∧ (sol w).z t haltCoordU ≤ 1 / 4) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) := by
  refine main_assembled_dyn_selector_zreadout_nolatch_repl_of_sol_init
    UniversalMachine.undecidableMachine bgpParams38 selectorSchedule branchU
    (selectorReplicatorAssembledField d_U B_U UniversalLocalView branchU
      (selChiResetPoly d_U UniversalLocalView M)
      (selChiGatePoly d_U UniversalLocalView M)
      (selKappaPoly d_U UniversalLocalView κ₀)
      (selGainPoly d_U UniversalLocalView)
      (muReadoutPoly eta heta) (0 : MvPolynomial (Fin d_U) ℚ)
      (1 : ℚ) (0 : ℚ) (1000 : ℚ) (300 : ℚ) 1 R)
    (fun _w sol La => selectorReplicatorTupleTraj sol La (g₀ : ℝ))
    ?_ (fun w => selectorReplicatorSphereInitQ d_U UniversalLocalView x₀ w g₀)
    init_presented sol init_zero init_succ haltCoordU (selZ UniversalLocalView haltCoordU)
    ?_ correct_halt_z correct_nonhalt_z
  · intro w sol La t ht
    exact selectorReplicatorTupleTraj_ode sol La (g₀ : ℝ)
      (selChiResetPoly d_U UniversalLocalView M)
      (selChiGatePoly d_U UniversalLocalView M)
      (selKappaPoly d_U UniversalLocalView κ₀)
      (selGainPoly d_U UniversalLocalView)
      (muReadoutPoly eta heta) (0 : MvPolynomial (Fin d_U) ℚ)
      bgpParams_A_rat_repl zero_eq_rat_zero_repl
      bgpParams_cμ_rat_repl bgpParams_cα_rat_repl bgpParams_L_eq_repl
      selectorSchedule_domain_nonneg_repl
      (fun t _ht => eval_selChiResetPoly_repl (sol := sol) (La := La) (warmGainVal := (g₀ : ℝ)) (t := t) M)
      (fun t _ht => eval_selChiGatePoly_repl (sol := sol) (La := La) (warmGainVal := (g₀ : ℝ)) (t := t) M)
      (fun t _ht => eval_selKappaPoly_repl (sol := sol) (La := La) (warmGainVal := (g₀ : ℝ)) (t := t) κ₀)
      (fun t ht => by
        rw [eval_selGainPoly_repl]
        rw [sol.alpha_eq_exp selectorSchedule_domain_nonneg_repl ht])
      (fun v t _ht => eval_muReadoutPoly_repl eta heta sol La (g₀ : ℝ) t v)
      (fun t => by simp)
      t ht
  · intro w s La t
    show selectorReplicatorTupleTraj s La (g₀ : ℝ) t (selZ UniversalLocalView haltCoordU) =
        s.z t haltCoordU
    exact selectorReplicatorTupleTraj_z (sol := s) (La := La) (warmGainVal := (g₀ : ℝ)) (t := t) haltCoordU

end MU

#print axioms selector_replicator_zero_latch_solution
#print axioms selectorReplicatorTupleTraj_ode
#print axioms selectorReplicatorPolynomialFieldPackage
#print axioms muReplicatorSelectorFieldPackage
#print axioms main_assembled_dyn_selector_zreadout_nolatch_repl_of_sol_init
#print axioms main_assembled_dyn_selector_zreadout_nolatch_repl
#print axioms main_assembled_mu_selector_zreadout_nolatch_repl_of_sol_init

end Ripple.BoundedUniversality.BGP
