import Ripple.BoundedUniversality.BGP.DynamicGate
import Ripple.BoundedUniversality.BGP.MainAssembled

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open Real

private abbrev dynTailDim (d : ℕ) : ℕ := d + (d + 1)
private abbrev dynGateTailDim (d : ℕ) : ℕ := 2 + dynTailDim d
private abbrev dynDim (d : ℕ) : ℕ := 4 + dynGateTailDim d

private noncomputable def dynS (d : ℕ) : Fin (dynDim d) :=
  Fin.castAdd (dynGateTailDim d) (0 : Fin 4)

private noncomputable def dynC (d : ℕ) : Fin (dynDim d) :=
  Fin.castAdd (dynGateTailDim d) (1 : Fin 4)

private noncomputable def dynMu (d : ℕ) : Fin (dynDim d) :=
  Fin.castAdd (dynGateTailDim d) (2 : Fin 4)

private noncomputable def dynAlpha (d : ℕ) : Fin (dynDim d) :=
  Fin.castAdd (dynGateTailDim d) (3 : Fin 4)

private noncomputable def dynGateZ (d : ℕ) : Fin (dynDim d) :=
  Fin.natAdd 4 (Fin.castAdd (dynTailDim d) (0 : Fin 2))

private noncomputable def dynGateU (d : ℕ) : Fin (dynDim d) :=
  Fin.natAdd 4 (Fin.castAdd (dynTailDim d) (1 : Fin 2))

private noncomputable def dynTailZ {d : ℕ} (i : Fin d) : Fin (dynTailDim d) :=
  Fin.castAdd (d + 1) i

private noncomputable def dynTailU {d : ℕ} (i : Fin d) : Fin (dynTailDim d) :=
  Fin.natAdd d (Fin.castAdd 1 i)

private noncomputable def dynTailA (d : ℕ) : Fin (dynTailDim d) :=
  Fin.natAdd d (Fin.natAdd d (0 : Fin 1))

private noncomputable def dynZ {d : ℕ} (i : Fin d) : Fin (dynDim d) :=
  Fin.natAdd 4 (Fin.natAdd 2 (dynTailZ i))

private noncomputable def dynU {d : ℕ} (i : Fin d) : Fin (dynDim d) :=
  Fin.natAdd 4 (Fin.natAdd 2 (dynTailU i))

private noncomputable def dynA (d : ℕ) : Fin (dynDim d) :=
  Fin.natAdd 4 (Fin.natAdd 2 (dynTailA d))

private noncomputable def dynRenameZ {d : ℕ}
    (p : MvPolynomial (Fin d) ℚ) : MvPolynomial (Fin (dynDim d)) ℚ :=
  MvPolynomial.rename (dynZ (d := d)) p

private noncomputable def dynRenameU {d : ℕ}
    (p : MvPolynomial (Fin d) ℚ) : MvPolynomial (Fin (dynDim d)) ℚ :=
  MvPolynomial.rename (dynU (d := d)) p

private noncomputable def dynRP (d L : ℕ) : MvPolynomial (Fin (dynDim d)) ℚ :=
  (MvPolynomial.C (1 / 2 : ℚ) *
    ((1 : MvPolynomial (Fin (dynDim d)) ℚ) - MvPolynomial.X (dynS d))) ^ L

private noncomputable def dynQP (d L : ℕ) : MvPolynomial (Fin (dynDim d)) ℚ :=
  (MvPolynomial.C (1 / 2 : ℚ) *
    ((1 : MvPolynomial (Fin (dynDim d)) ℚ) + MvPolynomial.X (dynS d))) ^ L

private noncomputable def dynRPderiv (d L : ℕ) : MvPolynomial (Fin (dynDim d)) ℚ :=
  MvPolynomial.C (L : ℚ) *
    (MvPolynomial.C (1 / 2 : ℚ) *
      ((1 : MvPolynomial (Fin (dynDim d)) ℚ) - MvPolynomial.X (dynS d))) ^ (L - 1) *
    (-(MvPolynomial.C (1 / 2 : ℚ)) * MvPolynomial.X (dynC d))

private noncomputable def dynQPderiv (d L : ℕ) : MvPolynomial (Fin (dynDim d)) ℚ :=
  MvPolynomial.C (L : ℚ) *
    (MvPolynomial.C (1 / 2 : ℚ) *
      ((1 : MvPolynomial (Fin (dynDim d)) ℚ) + MvPolynomial.X (dynS d))) ^ (L - 1) *
    (MvPolynomial.C (1 / 2 : ℚ) * MvPolynomial.X (dynC d))

/-- Dynamic-gate assembled rational polynomial field with coordinates
`(s, c, μ, α, bZ, bU, z, u, a)`. -/
def dynAssembledField (d : ℕ) (F : Fin d → MvPolynomial (Fin d) ℚ)
    (Hp : MvPolynomial (Fin d) ℚ) (A K c₀ c₁ : ℚ) (L R : ℕ) :
    Fin (dynDim d) → MvPolynomial (Fin (dynDim d)) ℚ :=
  Fin.append
    (fun k : Fin 4 =>
      if k = 0 then MvPolynomial.X (dynC d) else
      if k = 1 then -MvPolynomial.X (dynS d) else
      if k = 2 then MvPolynomial.C c₀ else
        MvPolynomial.C c₁ * MvPolynomial.X (dynAlpha d))
    (Fin.append
      (fun k : Fin 2 =>
        if k = 0 then
          -((MvPolynomial.C c₀ * dynRP d L +
              MvPolynomial.X (dynMu d) * dynRPderiv d L) *
            MvPolynomial.X (dynGateZ d))
        else
          -((MvPolynomial.C c₀ * dynQP d L +
              MvPolynomial.X (dynMu d) * dynQPderiv d L) *
            MvPolynomial.X (dynGateU d)))
      (Fin.append
        (fun i : Fin d =>
          MvPolynomial.C A * MvPolynomial.X (dynAlpha d) * MvPolynomial.X (dynGateZ d) *
            (dynRenameU (F i) - MvPolynomial.X (dynZ i)))
        (Fin.append
          (fun i : Fin d =>
            MvPolynomial.C A * MvPolynomial.X (dynAlpha d) * MvPolynomial.X (dynGateU d) *
              (MvPolynomial.X (dynZ i) - MvPolynomial.X (dynU i)))
          (fun _ : Fin 1 =>
            MvPolynomial.C K *
              ((MvPolynomial.C (1 / 2 : ℚ) *
                  ((1 : MvPolynomial (Fin (dynDim d)) ℚ) -
                    MvPolynomial.X (dynC d))) ^ R) *
              (dynRenameZ Hp - MvPolynomial.X (dynA d))))))

private lemma dynAssembledField_s (d : ℕ) (F : Fin d → MvPolynomial (Fin d) ℚ)
    (Hp : MvPolynomial (Fin d) ℚ) (A K c₀ c₁ : ℚ) (L R : ℕ) :
    dynAssembledField d F Hp A K c₀ c₁ L R (dynS d) = MvPolynomial.X (dynC d) := by
  simp [dynAssembledField, dynS]

private lemma dynAssembledField_c (d : ℕ) (F : Fin d → MvPolynomial (Fin d) ℚ)
    (Hp : MvPolynomial (Fin d) ℚ) (A K c₀ c₁ : ℚ) (L R : ℕ) :
    dynAssembledField d F Hp A K c₀ c₁ L R (dynC d) = -MvPolynomial.X (dynS d) := by
  simp [dynAssembledField, dynC, dynS]

private lemma dynAssembledField_mu (d : ℕ) (F : Fin d → MvPolynomial (Fin d) ℚ)
    (Hp : MvPolynomial (Fin d) ℚ) (A K c₀ c₁ : ℚ) (L R : ℕ) :
    dynAssembledField d F Hp A K c₀ c₁ L R (dynMu d) = MvPolynomial.C c₀ := by
  simp [dynAssembledField, dynMu, dynS]

private lemma dynAssembledField_alpha (d : ℕ) (F : Fin d → MvPolynomial (Fin d) ℚ)
    (Hp : MvPolynomial (Fin d) ℚ) (A K c₀ c₁ : ℚ) (L R : ℕ) :
    dynAssembledField d F Hp A K c₀ c₁ L R (dynAlpha d) =
      MvPolynomial.C c₁ * MvPolynomial.X (dynAlpha d) := by
  simp [dynAssembledField, dynAlpha, dynS]

private lemma dynAssembledField_bz (d : ℕ) (F : Fin d → MvPolynomial (Fin d) ℚ)
    (Hp : MvPolynomial (Fin d) ℚ) (A K c₀ c₁ : ℚ) (L R : ℕ) :
    dynAssembledField d F Hp A K c₀ c₁ L R (dynGateZ d) =
      -((MvPolynomial.C c₀ * dynRP d L +
          MvPolynomial.X (dynMu d) * dynRPderiv d L) *
        MvPolynomial.X (dynGateZ d)) := by
  simp [dynAssembledField, dynGateZ]

private lemma dynAssembledField_bu (d : ℕ) (F : Fin d → MvPolynomial (Fin d) ℚ)
    (Hp : MvPolynomial (Fin d) ℚ) (A K c₀ c₁ : ℚ) (L R : ℕ) :
    dynAssembledField d F Hp A K c₀ c₁ L R (dynGateU d) =
      -((MvPolynomial.C c₀ * dynQP d L +
          MvPolynomial.X (dynMu d) * dynQPderiv d L) *
        MvPolynomial.X (dynGateU d)) := by
  simp [dynAssembledField, dynGateU]

private lemma dynAssembledField_z {d : ℕ} (F : Fin d → MvPolynomial (Fin d) ℚ)
    (Hp : MvPolynomial (Fin d) ℚ) (A K c₀ c₁ : ℚ) (L R : ℕ) (i : Fin d) :
    dynAssembledField d F Hp A K c₀ c₁ L R (dynZ i) =
      MvPolynomial.C A * MvPolynomial.X (dynAlpha d) * MvPolynomial.X (dynGateZ d) *
        (dynRenameU (F i) - MvPolynomial.X (dynZ i)) := by
  simp [dynAssembledField, dynZ, dynTailZ]

private lemma dynAssembledField_u {d : ℕ} (F : Fin d → MvPolynomial (Fin d) ℚ)
    (Hp : MvPolynomial (Fin d) ℚ) (A K c₀ c₁ : ℚ) (L R : ℕ) (i : Fin d) :
    dynAssembledField d F Hp A K c₀ c₁ L R (dynU i) =
      MvPolynomial.C A * MvPolynomial.X (dynAlpha d) * MvPolynomial.X (dynGateU d) *
        (MvPolynomial.X (dynZ i) - MvPolynomial.X (dynU i)) := by
  simp [dynAssembledField, dynU, dynTailU]

private lemma dynAssembledField_a (d : ℕ) (F : Fin d → MvPolynomial (Fin d) ℚ)
    (Hp : MvPolynomial (Fin d) ℚ) (A K c₀ c₁ : ℚ) (L R : ℕ) :
    dynAssembledField d F Hp A K c₀ c₁ L R (dynA d) =
      MvPolynomial.C K *
        ((MvPolynomial.C (1 / 2 : ℚ) *
            ((1 : MvPolynomial (Fin (dynDim d)) ℚ) -
              MvPolynomial.X (dynC d))) ^ R) *
        (dynRenameZ Hp - MvPolynomial.X (dynA d)) := by
  simp [dynAssembledField, dynA, dynTailA]

structure DynLatchSol {d : ℕ} {Fr : (Fin d → ℝ) → Fin d → ℝ}
    {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ} {x₀ : Fin d → ℝ}
    (sol : DynIteratorSol d Fr A L c₀ c₁ x₀)
    (Hval : (Fin d → ℝ) → ℝ) (K : ℝ) (R : ℕ) where
  a : ℝ → ℝ
  init_a : a 0 = 0
  ode_a : ∀ t : ℝ,
    HasDerivAt a (K * gPulse R t * (Hval (sol.z t) - a t)) t

private noncomputable def dynTupleTraj {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ}
    {x₀ : Fin d → ℝ} (sol : DynIteratorSol d Fr A L c₀ c₁ x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : DynLatchSol sol Hval K R) (t : ℝ) : Fin (dynDim d) → ℝ :=
  Fin.append
    (fun k : Fin 4 =>
      if k = 0 then Real.sin t else
      if k = 1 then Real.cos t else
      if k = 2 then sol.μ t else sol.α t)
    (Fin.append
      (fun k : Fin 2 =>
        if k = 0 then bGateZ L (sol.μ t) t else bGateU L (sol.μ t) t)
      (Fin.append (sol.z t) (Fin.append (sol.u t) (fun _ : Fin 1 => La.a t))))

private lemma dynTupleTraj_s {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ}
    {x₀ : Fin d → ℝ} (sol : DynIteratorSol d Fr A L c₀ c₁ x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : DynLatchSol sol Hval K R) (t : ℝ) :
    dynTupleTraj sol La t (dynS d) = Real.sin t := by
  simp [dynTupleTraj, dynS]

private lemma dynTupleTraj_c {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ}
    {x₀ : Fin d → ℝ} (sol : DynIteratorSol d Fr A L c₀ c₁ x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : DynLatchSol sol Hval K R) (t : ℝ) :
    dynTupleTraj sol La t (dynC d) = Real.cos t := by
  simp [dynTupleTraj, dynC, dynS]

private lemma dynTupleTraj_mu {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ}
    {x₀ : Fin d → ℝ} (sol : DynIteratorSol d Fr A L c₀ c₁ x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : DynLatchSol sol Hval K R) (t : ℝ) :
    dynTupleTraj sol La t (dynMu d) = sol.μ t := by
  simp [dynTupleTraj, dynMu, dynS]

private lemma dynTupleTraj_alpha {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ}
    {x₀ : Fin d → ℝ} (sol : DynIteratorSol d Fr A L c₀ c₁ x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : DynLatchSol sol Hval K R) (t : ℝ) :
    dynTupleTraj sol La t (dynAlpha d) = sol.α t := by
  simp [dynTupleTraj, dynAlpha, dynS]

private lemma dynTupleTraj_bz {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ}
    {x₀ : Fin d → ℝ} (sol : DynIteratorSol d Fr A L c₀ c₁ x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : DynLatchSol sol Hval K R) (t : ℝ) :
    dynTupleTraj sol La t (dynGateZ d) = bGateZ L (sol.μ t) t := by
  simp [dynTupleTraj, dynGateZ]

private lemma dynTupleTraj_bu {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ}
    {x₀ : Fin d → ℝ} (sol : DynIteratorSol d Fr A L c₀ c₁ x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : DynLatchSol sol Hval K R) (t : ℝ) :
    dynTupleTraj sol La t (dynGateU d) = bGateU L (sol.μ t) t := by
  simp [dynTupleTraj, dynGateU]

private lemma dynTupleTraj_z {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ}
    {x₀ : Fin d → ℝ} (sol : DynIteratorSol d Fr A L c₀ c₁ x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : DynLatchSol sol Hval K R) (t : ℝ) (i : Fin d) :
    dynTupleTraj sol La t (dynZ i) = sol.z t i := by
  simp [dynTupleTraj, dynZ, dynTailZ]

private lemma dynTupleTraj_u {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ}
    {x₀ : Fin d → ℝ} (sol : DynIteratorSol d Fr A L c₀ c₁ x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : DynLatchSol sol Hval K R) (t : ℝ) (i : Fin d) :
    dynTupleTraj sol La t (dynU i) = sol.u t i := by
  simp [dynTupleTraj, dynU, dynTailU]

private lemma dynTupleTraj_a {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ}
    {x₀ : Fin d → ℝ} (sol : DynIteratorSol d Fr A L c₀ c₁ x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : DynLatchSol sol Hval K R) (t : ℝ) :
    dynTupleTraj sol La t (dynA d) = La.a t := by
  simp [dynTupleTraj, dynA, dynTailA]

private lemma eval_dynRenameU_tuple {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ}
    {x₀ : Fin d → ℝ} (sol : DynIteratorSol d Fr A L c₀ c₁ x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : DynLatchSol sol Hval K R) (t : ℝ)
    (p : MvPolynomial (Fin d) ℚ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (dynTupleTraj sol La t) (dynRenameU p) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.u t) p := by
  rw [dynRenameU, MvPolynomial.eval₂_rename]
  exact MvPolynomial.eval₂_congr
    (f := algebraMap ℚ ℝ) (p := p)
    (g₁ := dynTupleTraj sol La t ∘ dynU) (g₂ := sol.u t)
    (fun {i} {_c} _hi _hc => dynTupleTraj_u sol La t i)

private lemma eval_dynRenameZ_tuple {d : ℕ}
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ}
    {x₀ : Fin d → ℝ} (sol : DynIteratorSol d Fr A L c₀ c₁ x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : DynLatchSol sol Hval K R) (t : ℝ)
    (p : MvPolynomial (Fin d) ℚ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (dynTupleTraj sol La t) (dynRenameZ p) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) p := by
  rw [dynRenameZ, MvPolynomial.eval₂_rename]
  exact MvPolynomial.eval₂_congr
    (f := algebraMap ℚ ℝ) (p := p)
    (g₁ := dynTupleTraj sol La t ∘ dynZ) (g₂ := sol.z t)
    (fun {i} {_c} _hi _hc => dynTupleTraj_z sol La t i)

private lemma hasDerivAt_fin_append {m n : ℕ}
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

private noncomputable def rPulseDeriv (L : ℕ) (t : ℝ) : ℝ :=
  (L : ℝ) * ((1 - Real.sin t) / 2) ^ (L - 1) * (-(Real.cos t / 2))

private noncomputable def qPulseDeriv (L : ℕ) (t : ℝ) : ℝ :=
  (L : ℝ) * ((1 + Real.sin t) / 2) ^ (L - 1) * (Real.cos t / 2)

private lemma hasDerivAt_rPulse (L : ℕ) (t : ℝ) :
    HasDerivAt (fun τ => rPulse L τ) (rPulseDeriv L t) t := by
  unfold rPulse rPulseDeriv
  have hb : HasDerivAt (fun τ : ℝ => (1 - Real.sin τ) / 2) (-(Real.cos t / 2)) t := by
    have hs := Real.hasDerivAt_sin t
    convert ((hasDerivAt_const (x := t) (c := (1 : ℝ))).sub hs).div_const 2 using 1 <;> ring
  simpa [div_eq_mul_inv, mul_assoc] using hb.pow L

private lemma hasDerivAt_qPulse (L : ℕ) (t : ℝ) :
    HasDerivAt (fun τ => qPulse L τ) (qPulseDeriv L t) t := by
  unfold qPulse qPulseDeriv
  have hb : HasDerivAt (fun τ : ℝ => (1 + Real.sin τ) / 2) (Real.cos t / 2) t := by
    have hs := Real.hasDerivAt_sin t
    convert ((hasDerivAt_const (x := t) (c := (1 : ℝ))).add hs).div_const 2 using 1 <;> ring
  simpa [div_eq_mul_inv, mul_assoc] using hb.pow L

lemma hasDerivAt_bGateZ {d : ℕ} {Fr : (Fin d → ℝ) → Fin d → ℝ}
    {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ} {x₀ : Fin d → ℝ}
    (sol : DynIteratorSol d Fr A L c₀ c₁ x₀) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun τ => bGateZ L (sol.μ τ) τ)
      (-( (c₀ : ℝ) * rPulse L t + sol.μ t * rPulseDeriv L t) *
        bGateZ L (sol.μ t) t) t := by
  unfold bGateZ
  have hmul := (sol.ode_μ t ht).mul (hasDerivAt_rPulse L t)
  have hneg : HasDerivAt (fun τ : ℝ => -(sol.μ τ * rPulse L τ))
      (-((c₀ : ℝ) * rPulse L t + sol.μ t * rPulseDeriv L t)) t := by
    simpa [neg_add_rev] using hmul.neg
  have h := hneg.exp
  convert h using 1 <;> ring

lemma hasDerivAt_bGateU {d : ℕ} {Fr : (Fin d → ℝ) → Fin d → ℝ}
    {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ} {x₀ : Fin d → ℝ}
    (sol : DynIteratorSol d Fr A L c₀ c₁ x₀) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun τ => bGateU L (sol.μ τ) τ)
      (-( (c₀ : ℝ) * qPulse L t + sol.μ t * qPulseDeriv L t) *
        bGateU L (sol.μ t) t) t := by
  unfold bGateU
  have hmul := (sol.ode_μ t ht).mul (hasDerivAt_qPulse L t)
  have hneg : HasDerivAt (fun τ : ℝ => -(sol.μ τ * qPulse L τ))
      (-((c₀ : ℝ) * qPulse L t + sol.μ t * qPulseDeriv L t)) t := by
    simpa [neg_add_rev] using hmul.neg
  have h := hneg.exp
  convert h using 1 <;> ring

theorem dynTupleTraj_ode
    {Conf : Type} [Primcodable Conf] {Mch : DiscreteMachine Conf}
    {d : ℕ} {E : LatticeEncoding Mch d}
    (S : RobustRealExtension Mch d E) (I : HaltIndicator Mch d E)
    {A K c₀ c₁ : ℚ} {L R : ℕ} {x₀ : Fin d → ℝ}
    (sol : DynIteratorSol d S.evalF A L c₀ c₁ x₀)
    (La : DynLatchSol sol I.evalH (K : ℝ) R) :
    ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (dynTupleTraj sol La)
        (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (dynTupleTraj sol La t)
          (dynAssembledField d S.F I.H A K c₀ c₁ L R i)) t := by
  intro t ht
  let core' : Fin 4 → ℝ := fun k =>
    if k = 0 then Real.cos t else
    if k = 1 then -Real.sin t else
    if k = 2 then (c₀ : ℝ) else (c₁ : ℝ) * sol.α t
  let gate' : Fin 2 → ℝ := fun k =>
    if k = 0 then
      -(((c₀ : ℝ) * rPulse L t + sol.μ t * rPulseDeriv L t) *
        bGateZ L (sol.μ t) t)
    else
      -(((c₀ : ℝ) * qPulse L t + sol.μ t * qPulseDeriv L t) *
        bGateU L (sol.μ t) t)
  let z' : Fin d → ℝ := fun i =>
    (A : ℝ) * sol.α t * bGateZ L (sol.μ t) t * (S.evalF (sol.u t) i - sol.z t i)
  let u' : Fin d → ℝ := fun i =>
    (A : ℝ) * sol.α t * bGateU L (sol.μ t) t * (sol.z t i - sol.u t i)
  let a' : Fin 1 → ℝ := fun _ =>
    (K : ℝ) * gPulse R t * (I.evalH (sol.z t) - La.a t)
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
    · simpa [core'] using sol.ode_μ t ht
    · simpa [core'] using sol.ode_α t ht
  have hgate :
      HasDerivAt
        (fun τ => fun k : Fin 2 =>
          if k = 0 then bGateZ L (sol.μ τ) τ else bGateU L (sol.μ τ) τ)
        gate' t := by
    apply hasDerivAt_pi.mpr
    intro k
    fin_cases k
    · convert hasDerivAt_bGateZ sol t ht using 1
      simp [gate']
      ring_nf
    · convert hasDerivAt_bGateU sol t ht using 1
      simp [gate']
      ring_nf
  have hz : HasDerivAt (fun τ => sol.z τ) z' t := by
    apply hasDerivAt_pi.mpr
    intro i
    exact sol.ode_z t ht i
  have hu : HasDerivAt (fun τ => sol.u τ) u' t := by
    apply hasDerivAt_pi.mpr
    intro i
    exact sol.ode_u t ht i
  have ha : HasDerivAt (fun τ => fun _ : Fin 1 => La.a τ) a' t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    exact La.ode_a t
  have hraw :
      HasDerivAt (dynTupleTraj sol La)
        (Fin.append core' (Fin.append gate' (Fin.append z' (Fin.append u' a')))) t := by
    simpa [dynTupleTraj, core', gate', z', u', a'] using
      hasDerivAt_fin_append hcore
        (hasDerivAt_fin_append hgate
          (hasDerivAt_fin_append hz (hasDerivAt_fin_append hu ha)))
  refine hraw.congr_deriv ?_
  funext j
  refine Fin.addCases (m := 4) (n := dynGateTailDim d) ?_ ?_ j
  · intro k
    fin_cases k
    · change core' 0 =
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (dynTupleTraj sol La t)
          (dynAssembledField d S.F I.H A K c₀ c₁ L R (dynS d))
      simp [core', dynAssembledField_s, dynTupleTraj_c]
    · change core' 1 =
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (dynTupleTraj sol La t)
          (dynAssembledField d S.F I.H A K c₀ c₁ L R (dynC d))
      simp [core', dynAssembledField_c, dynTupleTraj_s]
    · change core' 2 =
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (dynTupleTraj sol La t)
          (dynAssembledField d S.F I.H A K c₀ c₁ L R (dynMu d))
      simp [core', dynAssembledField_mu]
    · change core' 3 =
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (dynTupleTraj sol La t)
          (dynAssembledField d S.F I.H A K c₀ c₁ L R (dynAlpha d))
      simp [core', dynAssembledField_alpha, dynTupleTraj_alpha]
  · intro tail0
    refine Fin.addCases (m := 2) (n := dynTailDim d) ?_ ?_ tail0
    · intro k
      fin_cases k
      · simp only [Fin.append_left, Fin.append_right]
        change gate' 0 =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (dynTupleTraj sol La t)
            (dynAssembledField d S.F I.H A K c₀ c₁ L R (dynGateZ d))
        simp [gate', dynAssembledField_bz, dynRP, dynRPderiv, rPulse, rPulseDeriv,
          dynTupleTraj_s, dynTupleTraj_c, dynTupleTraj_mu, dynTupleTraj_bz]
        left
        ring_nf
      · simp only [Fin.append_left, Fin.append_right]
        change gate' 1 =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (dynTupleTraj sol La t)
            (dynAssembledField d S.F I.H A K c₀ c₁ L R (dynGateU d))
        simp [gate', dynAssembledField_bu, dynQP, dynQPderiv, qPulse, qPulseDeriv,
          dynTupleTraj_s, dynTupleTraj_c, dynTupleTraj_mu, dynTupleTraj_bu]
        left
        ring_nf
    · intro tail
      refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
      · intro i
        simp only [Fin.append_left, Fin.append_right]
        change z' i =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (dynTupleTraj sol La t)
            (dynAssembledField d S.F I.H A K c₀ c₁ L R (dynZ i))
        simp [z', dynAssembledField_z, RobustRealExtension.evalF,
          eval_dynRenameU_tuple, dynTupleTraj_alpha, dynTupleTraj_bz, dynTupleTraj_z]
      · intro tail2
        refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
        · intro i
          simp only [Fin.append_left, Fin.append_right]
          change u' i =
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (dynTupleTraj sol La t)
              (dynAssembledField d S.F I.H A K c₀ c₁ L R (dynU i))
          simp [u', dynAssembledField_u, dynTupleTraj_alpha, dynTupleTraj_bu,
            dynTupleTraj_z, dynTupleTraj_u]
        · intro k
          fin_cases k
          simp only [Fin.append_left, Fin.append_right]
          change a' 0 =
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (dynTupleTraj sol La t)
              (dynAssembledField d S.F I.H A K c₀ c₁ L R (dynA d))
          simp [a', dynAssembledField_a, HaltIndicator.evalH, gPulse,
            eval_dynRenameZ_tuple, dynTupleTraj_c, dynTupleTraj_a]
          left
          left
          ring_nf

theorem dynTupleTraj_zero
    {d : ℕ} {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ}
    {x₀ : Fin d → ℝ} (sol : DynIteratorSol d Fr A L c₀ c₁ x₀)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : DynLatchSol sol Hval K R) :
    dynTupleTraj sol La 0 =
      Fin.append
        (fun k : Fin 4 =>
          if k = 0 then 0 else if k = 1 then 1 else if k = 2 then 0 else 1)
        (Fin.append
          (fun _ : Fin 2 => 1)
          (Fin.append x₀ (Fin.append x₀ (fun _ : Fin 1 => 0)))) := by
  funext j
  refine Fin.addCases (m := 4) (n := dynGateTailDim d) ?_ ?_ j
  · intro k
    fin_cases k
    · simp [dynTupleTraj, dynS]
    · simp [dynTupleTraj, dynC, dynS]
    · simp [dynTupleTraj, dynMu, dynS, sol.init_μ]
    · simp [dynTupleTraj, dynAlpha, dynS, sol.init_α]
  · intro tail0
    refine Fin.addCases (m := 2) (n := dynTailDim d) ?_ ?_ tail0
    · intro k
      fin_cases k
      · simp [dynTupleTraj, dynGateZ, bGateZ, sol.init_μ]
      · simp [dynTupleTraj, dynGateU, bGateU, sol.init_μ]
    · intro tail
      refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
      · intro i
        simp [dynTupleTraj, dynZ, dynTailZ, sol.init_z]
      · intro tail2
        refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
        · intro i
          simp [dynTupleTraj, dynU, dynTailU, sol.init_u]
        · intro a
          fin_cases a
          simp [dynTupleTraj, dynA, dynTailA, La.init_a]

/-! ## Dynamic latch riding theorems -/

private theorem sqrt_three_le_87_div_50 : Real.sqrt 3 ≤ (87 : ℝ) / 50 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
    Real.sqrt_nonneg (3 : ℝ)]

private theorem sqrt_three_ge_43_div_25 : (43 : ℝ) / 25 ≤ Real.sqrt 3 := by
  rw [Real.le_sqrt' (by norm_num)]
  norm_num

private theorem cos_pi_div_twelve_ge_24_div_25 :
    (24 : ℝ) / 25 ≤ Real.cos (π / 12) := by
  have hhalf := Real.cos_half (x := π / 6)
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hsqrt : (24 : ℝ) / 25 ≤ Real.sqrt (((1 + Real.cos (π / 6)) / 2)) := by
    rw [Real.le_sqrt' (by norm_num)]
    rw [Real.cos_pi_div_six]
    nlinarith [sqrt_three_ge_43_div_25]
  rw [show π / 12 = π / 6 / 2 by ring]
  rw [hhalf]
  exact hsqrt

private theorem cos_shift_eq_neg_cos_center (j : ℕ) (t : ℝ) :
    Real.cos t = -Real.cos (t - 2 * π * (j : ℝ) - π) := by
  have hteq : t =
      ((t - 2 * π * (j : ℝ) - π) + π) + (j : ℕ) * (2 * π) := by
    push_cast
    ring
  conv_lhs => rw [hteq]
  rw [Real.cos_add_nat_mul_two_pi, Real.cos_add_pi]

private theorem cos_stable_inner_le (j : ℕ) {t : ℝ}
    (h1 : 2 * π * j + 11 * π / 12 ≤ t)
    (h2 : t ≤ 2 * π * j + 13 * π / 12) :
    Real.cos t ≤ -(24 : ℝ) / 25 := by
  have hπ := Real.pi_pos
  set x := t - 2 * π * (j : ℝ) - π with hx
  have hxabs : |x| ≤ π / 12 := by
    rw [abs_le]
    constructor <;> simp only [hx] <;> linarith
  have hcosx : (24 : ℝ) / 25 ≤ Real.cos x := by
    rw [← Real.cos_abs x]
    calc
      (24 : ℝ) / 25 ≤ Real.cos (π / 12) := cos_pi_div_twelve_ge_24_div_25
      _ ≤ Real.cos |x| :=
          Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x)
            (by linarith) hxabs
  rw [cos_shift_eq_neg_cos_center j t]
  linarith

private theorem cos_off_left_ge (j : ℕ) {t : ℝ}
    (h1 : 2 * π * j ≤ t)
    (h2 : t ≤ 2 * π * j + 5 * π / 6) :
    -(87 : ℝ) / 100 ≤ Real.cos t := by
  have hπ := Real.pi_pos
  set x := t - 2 * π * (j : ℝ) - π with hx
  have hxlo : π / 6 ≤ |x| := by
    rw [le_abs]
    right
    simp only [hx]
    linarith
  have hxhi : |x| ≤ π := by
    rw [abs_le]
    constructor <;> simp only [hx] <;> linarith
  have hcosx : Real.cos x ≤ (87 : ℝ) / 100 := by
    rw [← Real.cos_abs x]
    calc
      Real.cos |x| ≤ Real.cos (π / 6) :=
          Real.cos_le_cos_of_nonneg_of_le_pi (by linarith)
            hxhi hxlo
      _ = Real.sqrt 3 / 2 := Real.cos_pi_div_six
      _ ≤ (87 : ℝ) / 100 := by
          nlinarith [sqrt_three_le_87_div_50]
  rw [cos_shift_eq_neg_cos_center j t]
  linarith

private theorem cos_off_right_ge (j : ℕ) {t : ℝ}
    (h1 : 2 * π * j + 7 * π / 6 ≤ t)
    (h2 : t ≤ 2 * π * (j + 1)) :
    -(87 : ℝ) / 100 ≤ Real.cos t := by
  have hπ := Real.pi_pos
  set x := t - 2 * π * (j : ℝ) - π with hx
  have hxlo : π / 6 ≤ |x| := by
    rw [le_abs]
    left
    simp only [hx]
    linarith
  have hxhi : |x| ≤ π := by
    rw [abs_le]
    constructor <;> simp only [hx] <;> nlinarith [hπ, h1, h2]
  have hcosx : Real.cos x ≤ (87 : ℝ) / 100 := by
    rw [← Real.cos_abs x]
    calc
      Real.cos |x| ≤ Real.cos (π / 6) :=
          Real.cos_le_cos_of_nonneg_of_le_pi (by linarith)
            hxhi hxlo
      _ = Real.sqrt 3 / 2 := Real.cos_pi_div_six
      _ ≤ (87 : ℝ) / 100 := by
          nlinarith [sqrt_three_le_87_div_50]
  rw [cos_shift_eq_neg_cos_center j t]
  linarith

private theorem gPulse_ge_stable_inner {R j : ℕ} {t : ℝ}
    (h1 : 2 * π * j + 11 * π / 12 ≤ t)
    (h2 : t ≤ 2 * π * j + 13 * π / 12) :
    ((49 : ℝ) / 50) ^ R ≤ gPulse R t := by
  unfold gPulse
  apply pow_le_pow_left₀ (by norm_num)
  have hcos := cos_stable_inner_le j h1 h2
  linarith

private theorem gPulse_le_off_left {R j : ℕ} {t : ℝ}
    (h1 : 2 * π * j ≤ t)
    (h2 : t ≤ 2 * π * j + 5 * π / 6) :
    gPulse R t ≤ ((187 : ℝ) / 200) ^ R := by
  unfold gPulse
  apply pow_le_pow_left₀
  · nlinarith [Real.cos_le_one t]
  · have hcos := cos_off_left_ge j h1 h2
    linarith

private theorem gPulse_le_off_right {R j : ℕ} {t : ℝ}
    (h1 : 2 * π * j + 7 * π / 6 ≤ t)
    (h2 : t ≤ 2 * π * (j + 1)) :
    gPulse R t ≤ ((187 : ℝ) / 200) ^ R := by
  unfold gPulse
  apply pow_le_pow_left₀
  · nlinarith [Real.cos_le_one t]
  · have hcos := cos_off_right_ge j h1 h2
    linarith

private theorem latch_intInt (f : ℝ → ℝ) (hf : Continuous f) (u v : ℝ) :
    IntervalIntegrable f MeasureTheory.volume u v :=
  hf.intervalIntegrable u v

private theorem latch_intConst (c u v : ℝ) :
    IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume u v :=
  _root_.intervalIntegrable_const

private theorem gPulse_stable_inner_integral_lower (R j : ℕ) :
    (π / 6) * ((49 : ℝ) / 50) ^ R ≤
      ∫ t in (2 * π * j + 11 * π / 12)..(2 * π * j + 13 * π / 12),
        gPulse R t := by
  have hπ := Real.pi_pos
  have hab : 2 * π * (j : ℝ) + 11 * π / 12 ≤
      2 * π * (j : ℝ) + 13 * π / 12 := by linarith
  have hint := latch_intInt (gPulse R) (gPulse_continuous R)
  have hconst :
      (∫ _t in (2 * π * (j : ℝ) + 11 * π / 12)..
          (2 * π * (j : ℝ) + 13 * π / 12), ((49 : ℝ) / 50) ^ R)
        = (π / 6) * ((49 : ℝ) / 50) ^ R := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    congr 1
    ring
  rw [← hconst]
  apply intervalIntegral.integral_mono_on hab (latch_intConst _ _ _)
    (hint _ _)
  intro t ht
  exact gPulse_ge_stable_inner ht.1 ht.2

private theorem gPulse_off_left_integral_upper (R j : ℕ) :
    (∫ t in (2 * π * j)..(2 * π * j + 5 * π / 6), gPulse R t)
      ≤ (5 * π / 6) * ((187 : ℝ) / 200) ^ R := by
  have hπ := Real.pi_pos
  have hab : 2 * π * (j : ℝ) ≤ 2 * π * (j : ℝ) + 5 * π / 6 := by
    linarith
  have hint := latch_intInt (gPulse R) (gPulse_continuous R)
  have hconst :
      (∫ _t in (2 * π * (j : ℝ))..(2 * π * (j : ℝ) + 5 * π / 6),
          ((187 : ℝ) / 200) ^ R)
        = (5 * π / 6) * ((187 : ℝ) / 200) ^ R := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    congr 1
    ring
  rw [← hconst]
  apply intervalIntegral.integral_mono_on hab (hint _ _)
    (latch_intConst _ _ _)
  intro t ht
  exact gPulse_le_off_left ht.1 ht.2

private theorem gPulse_off_right_integral_upper (R j : ℕ) :
    (∫ t in (2 * π * j + 7 * π / 6)..(2 * π * ((j : ℝ) + 1)), gPulse R t)
      ≤ (5 * π / 6) * ((187 : ℝ) / 200) ^ R := by
  have hπ := Real.pi_pos
  have hab : 2 * π * (j : ℝ) + 7 * π / 6 ≤ 2 * π * ((j : ℝ) + 1) := by
    linarith
  have hint := latch_intInt (gPulse R) (gPulse_continuous R)
  have hconst :
      (∫ _t in (2 * π * (j : ℝ) + 7 * π / 6)..(2 * π * ((j : ℝ) + 1)),
          ((187 : ℝ) / 200) ^ R)
        = (5 * π / 6) * ((187 : ℝ) / 200) ^ R := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    congr 1
    ring
  rw [← hconst]
  apply intervalIntegral.integral_mono_on hab (hint _ _)
    (latch_intConst _ _ _)
  intro t ht
  apply gPulse_le_off_right ht.1
  simpa [Nat.cast_add, Nat.cast_one] using ht.2

private theorem gPulse_stable_integral_lower (R j : ℕ) :
    (π / 6) * ((49 : ℝ) / 50) ^ R ≤
      ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
        gPulse R t := by
  have hπ := Real.pi_pos
  have hinner :=
    gPulse_stable_inner_integral_lower R j
  have hmono :
      (∫ t in (2 * π * j + 11 * π / 12)..(2 * π * j + 13 * π / 12),
        gPulse R t)
        ≤ ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
          gPulse R t := by
    apply intervalIntegral.integral_mono_interval
    · linarith
    · linarith
    · linarith
    · exact Filter.Eventually.of_forall fun t => gPulse_nonneg R t
    · exact latch_intInt (gPulse R) (gPulse_continuous R) _ _
  exact le_trans hinner hmono

private theorem exp_neg_one_le_half : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
  have h2exp : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    norm_num at h ⊢
    exact h
  rw [Real.exp_neg, one_div]
  exact (inv_le_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr h2exp

private theorem latch_parameter_exists :
    ∃ (K : ℚ) (R : ℕ), 0 < K ∧
      (∀ j : ℕ,
        Real.exp (-((K : ℝ) *
          ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
            gPulse R t)) ≤ (1 / 2 : ℝ)) ∧
      (K : ℝ) * ((187 : ℝ) / 200) ^ R * (5 * π / 6) ≤ (1 / 100 : ℝ) := by
  let q : ℝ := (187 : ℝ) / 196
  have hq0 : 0 < q := by norm_num [q]
  have hq1 : q < 1 := by norm_num [q]
  obtain ⟨R, hR⟩ : ∃ R : ℕ, q ^ R < (3 : ℝ) / 2500 :=
    exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 3 / 2500) hq1
  let Glo : ℝ := (π / 6) * ((49 : ℝ) / 50) ^ R
  have hGlo_pos : 0 < Glo := by
    dsimp [Glo]
    positivity
  let N : ℕ := Nat.ceil (1 / Glo)
  let K : ℚ := (N : ℚ)
  have hNpos : 0 < N := by
    dsimp [N]
    exact Nat.ceil_pos.mpr (by positivity)
  have hKpos : 0 < K := by
    dsimp [K]
    exact_mod_cast hNpos
  refine ⟨K, R, hKpos, ?_, ?_⟩
  · intro j
    have hceil : (1 / Glo : ℝ) ≤ (N : ℝ) := Nat.le_ceil _
    have hKGlo : 1 ≤ (K : ℝ) * Glo := by
      have := mul_le_mul_of_nonneg_right hceil hGlo_pos.le
      have hcast : (K : ℝ) = (N : ℝ) := by norm_num [K]
      rw [hcast] 
      rwa [one_div_mul_cancel hGlo_pos.ne'] at this
    have hint :=
      gPulse_stable_integral_lower R j
    have hKnonneg : 0 ≤ (K : ℝ) := by exact_mod_cast hKpos.le
    have hprod :
        1 ≤ (K : ℝ) *
          ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
            gPulse R t := by
      calc
        1 ≤ (K : ℝ) * Glo := hKGlo
        _ ≤ (K : ℝ) *
          ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
            gPulse R t := by
              apply mul_le_mul_of_nonneg_left
              · simpa [Glo] using hint
              · exact hKnonneg
    calc
      Real.exp (-((K : ℝ) *
          ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
            gPulse R t))
          ≤ Real.exp (-1) := by
            apply Real.exp_le_exp.mpr
            linarith
      _ ≤ (1 / 2 : ℝ) := exp_neg_one_le_half
  · have hceil_lt : (N : ℝ) < 1 / Glo + 1 := by
      dsimp [N]
      exact Nat.ceil_lt_add_one (by positivity)
    have hKle : (K : ℝ) ≤ 1 / Glo + 1 := by
      have hcast : (K : ℝ) = (N : ℝ) := by norm_num [K]
      rw [hcast]
      exact hceil_lt.le
    have hoff_le_q : ((187 : ℝ) / 200) ^ R ≤ q ^ R := by
      apply pow_le_pow_left₀
      · norm_num
      · norm_num [q]
    have hπ4 : π ≤ (4 : ℝ) := Real.pi_le_four
    have hleak_bound :
        (1 / Glo + 1) * ((187 : ℝ) / 200) ^ R * (5 * π / 6)
          ≤ ((25 : ℝ) / 3) * q ^ R := by
      have hstable_pos : 0 < ((49 : ℝ) / 50) ^ R := by positivity
      have hoff_nonneg : 0 ≤ ((187 : ℝ) / 200) ^ R := by positivity
      have hqpow_nonneg : 0 ≤ q ^ R := by positivity
      calc
        (1 / Glo + 1) * ((187 : ℝ) / 200) ^ R * (5 * π / 6)
            = (5 * (((187 : ℝ) / 200) ^ R / (((49 : ℝ) / 50) ^ R)) +
                (5 * π / 6) * ((187 : ℝ) / 200) ^ R) := by
                field_simp [Glo, hGlo_pos.ne', Real.pi_ne_zero, hstable_pos.ne']
                ring
        _ ≤ 5 * q ^ R + (5 * π / 6) * q ^ R := by
              have hratio :
                  ((187 : ℝ) / 200) ^ R / (((49 : ℝ) / 50) ^ R) = q ^ R := by
                rw [← div_pow]
                congr 1
                norm_num [q]
              rw [hratio]
              gcongr
        _ ≤ 5 * q ^ R + (10 / 3 : ℝ) * q ^ R := by
              have hcoef : 5 * π / 6 ≤ (10 / 3 : ℝ) := by
                nlinarith [hπ4]
              have hterm :
                  (5 * π / 6) * q ^ R ≤ (10 / 3 : ℝ) * q ^ R :=
                mul_le_mul_of_nonneg_right hcoef hqpow_nonneg
              linarith
        _ = ((25 : ℝ) / 3) * q ^ R := by ring
    calc
      (K : ℝ) * ((187 : ℝ) / 200) ^ R * (5 * π / 6)
          ≤ (1 / Glo + 1) * ((187 : ℝ) / 200) ^ R * (5 * π / 6) := by
            gcongr
      _ ≤ ((25 : ℝ) / 3) * q ^ R := hleak_bound
      _ ≤ (1 / 100 : ℝ) := by
            nlinarith [hR]

theorem HaltIndicator.dyn_evalH_continuous_along
    {Conf : Type} [Primcodable Conf]
    {Mch : DiscreteMachine Conf} {d : ℕ}
    {E : LatticeEncoding Mch d} (I : HaltIndicator Mch d E)
    {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ}
    {x₀ : Fin d → ℝ} (sol : DynIteratorSol d Fr A L c₀ c₁ x₀) :
    Continuous fun t => I.evalH (sol.z t) := by
  have hz : Continuous fun t => sol.z t :=
    continuous_pi fun i => sol.cont_z i
  unfold HaltIndicator.evalH
  convert
    (MvPolynomial.continuous_eval
      (p := MvPolynomial.map (algebraMap ℚ ℝ) I.H)).comp hz
    using 1
  ext t
  exact MvPolynomial.eval₂_eq_eval_map (algebraMap ℚ ℝ) (sol.z t) I.H

private theorem DiscreteMachine.halted_of_halts_after
    {Conf : Type} [Primcodable Conf] (Mch : DiscreteMachine Conf)
    {w n : ℕ}
    (hn : Mch.halted (Mch.step^[n] (Mch.init w)) = true) :
    ∀ m : ℕ, n ≤ m →
      Mch.halted (Mch.step^[m] (Mch.init w)) = true := by
  intro m hnm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction k with
  | zero =>
      simpa using hn
  | succ k ih =>
      rw [Nat.add_succ, Function.iterate_succ_apply']
      have ih' : Mch.halted (Mch.step^[n + k] (Mch.init w)) = true :=
        ih (Nat.le_add_right n k)
      have hfix :
          Mch.step (Mch.step^[n + k] (Mch.init w)) =
            Mch.step^[n + k] (Mch.init w) :=
        Mch.halted_absorbing _ ih'
      simpa [hfix] using ih'

private theorem DiscreteMachine.running_of_not_haltsOn
    {Conf : Type} [Primcodable Conf] (Mch : DiscreteMachine Conf)
    {w j : ℕ} (h : ¬ Mch.haltsOn w) :
    Mch.halted (Mch.step^[j] (Mch.init w)) = false := by
  cases hj : Mch.halted (Mch.step^[j] (Mch.init w)) with
  | false => rfl
  | true =>
      exact False.elim (h ⟨j, hj⟩)

/-- Monotonicity from pointwise `HasDerivAt` with nonnegative
derivative on `[0, t]`. -/
private theorem nonneg_of_hasDerivAt_nonneg
    (f : ℝ → ℝ) (f' : ℝ → ℝ)
    (hderiv : ∀ s : ℝ, HasDerivAt f (f' s) s)
    (hpos : ∀ s : ℝ, 0 ≤ s → 0 ≤ f' s)
    (h0 : 0 ≤ f 0) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ f t := by
  have hmono : MonotoneOn f (Set.Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
    · exact (fun s _ => (hderiv s).continuousAt.continuousWithinAt)
    · intro s hs
      exact ((hderiv s).differentiableAt).differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hderiv s).deriv]
      exact hpos s hs.1.le
  have := hmono (Set.left_mem_Icc.mpr ht) (Set.right_mem_Icc.mpr ht) ht
  linarith

/-- **P7, forward invariance of `[0, 1]`** for the latch (paper
lem:bounded-working-volume, latch part): the field points inward at
the endpoints whenever `0 ≤ Hval ∘ z ≤ 1` along the trajectory. -/
theorem dyn_latch_mem_unitInterval
    {d : ℕ} {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ}
    {x₀ : Fin d → ℝ} (sol : DynIteratorSol d Fr A L c₀ c₁ x₀)
    (Hval : (Fin d → ℝ) → ℝ) (K : ℝ) (hK : 0 < K) (R : ℕ)
    (L : DynLatchSol sol Hval K R)
    (hH : ∀ t : ℝ, 0 ≤ t → 0 ≤ Hval (sol.z t) ∧ Hval (sol.z t) ≤ 1) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ L.a t ∧ L.a t ≤ 1 := by
  intro t ht
  set φ : ℝ → ℝ := fun s => K * gPulse R s with hφdef
  have hφcont : Continuous φ := by
    have : Continuous (gPulse R) := by
      unfold gPulse
      fun_prop
    fun_prop
  set Φ : ℝ → ℝ := fun s => ∫ τ in (0:ℝ)..s, φ τ with hΦdef
  have hΦderiv : ∀ s : ℝ, HasDerivAt Φ (φ s) s := by
    intro s
    exact intervalIntegral.integral_hasDerivAt_right
      (hφcont.intervalIntegrable 0 s)
      (hφcont.stronglyMeasurableAtFilter _ _)
      hφcont.continuousAt
  set E : ℝ → ℝ := fun s => Real.exp (Φ s) with hEdef
  have hEderiv : ∀ s : ℝ, HasDerivAt E (φ s * E s) s := by
    intro s
    have := (hΦderiv s).exp
    convert this using 1
    simp only [hEdef]
    ring
  have hEpos : ∀ s, 0 < E s := fun s => Real.exp_pos _
  have hE0 : E 0 = 1 := by simp [hEdef, hΦdef]
  constructor
  · have hfderiv : ∀ s : ℝ, HasDerivAt (fun τ => L.a τ * E τ)
        (K * gPulse R s * Hval (sol.z s) * E s) s := by
      intro s
      have h1 := (L.ode_a s).mul (hEderiv s)
      convert h1 using 1
      simp only [hφdef, hEdef]
      ring
    have h := nonneg_of_hasDerivAt_nonneg (fun τ => L.a τ * E τ) _
      hfderiv
      (fun s hs => by
        have hHs := (hH s hs).1
        have := (hEpos s).le
        have := gPulse_nonneg R s
        positivity)
      (by simp [L.init_a]) t ht
    nlinarith [hEpos t, h]
  · have hfderiv : ∀ s : ℝ, HasDerivAt (fun τ => (1 - L.a τ) * E τ)
        (K * gPulse R s * (1 - Hval (sol.z s)) * E s) s := by
      intro s
      have h0 : HasDerivAt (fun τ => 1 - L.a τ)
          (-(K * gPulse R s * (Hval (sol.z s) - L.a s))) s :=
        (L.ode_a s).const_sub 1
      have h1 := h0.mul (hEderiv s)
      convert h1 using 1
      simp only [hφdef, hEdef]
      ring
    have h := nonneg_of_hasDerivAt_nonneg (fun τ => (1 - L.a τ) * E τ) _
      hfderiv
      (fun s hs => by
        have hHs := (hH s hs).2
        have h1 : 0 ≤ 1 - Hval (sol.z s) := by linarith
        have := (hEpos s).le
        have := gPulse_nonneg R s
        positivity)
      (by simp [L.init_a, hE0]) t ht
    nlinarith [hEpos t, h]

private theorem latch_one_sided_target_upper
    (A : ℝ) (hA : 0 < A) (φ w y : ℝ → ℝ)
    (a b η : ℝ) (hab : a ≤ b)
    (hφ_cont : Continuous φ)
    (hφ0 : ∀ t ∈ Set.Icc a b, 0 ≤ φ t)
    (hwη : ∀ t ∈ Set.Icc a b, w t ≤ η)
    (hy : ∀ t ∈ Set.Icc a b, HasDerivAt y (A * φ t * (w t - y t)) t) :
    y b ≤
      Real.exp (-(A * ∫ t in a..b, φ t)) * y a +
        (1 - Real.exp (-(A * ∫ t in a..b, φ t))) * η := by
  set Φ : ℝ → ℝ := fun t => ∫ s in a..t, φ s with hΦdef
  have hΦderiv : ∀ t : ℝ, HasDerivAt Φ (φ t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hφ_cont.intervalIntegrable a t)
      (hφ_cont.stronglyMeasurableAtFilter _ _)
      hφ_cont.continuousAt
  have hΦa : Φ a = 0 := by simp [hΦdef]
  have hΦcont : Continuous Φ := by
    exact continuous_iff_continuousAt.mpr fun t => (hΦderiv t).continuousAt
  set Efun : ℝ → ℝ := fun t => Real.exp (A * Φ t) with hEdef
  have hEderiv : ∀ t : ℝ,
      HasDerivAt Efun (A * φ t * Efun t) t := by
    intro t
    have h1 : HasDerivAt (fun τ => A * Φ τ) (A * φ t) t :=
      (hΦderiv t).const_mul A
    have h2 := h1.exp
    convert h2 using 1
    simp [hEdef]
    ring
  have hEpos : ∀ t, 0 < Efun t := fun t => Real.exp_pos _
  have hEa : Efun a = 1 := by simp [hEdef, hΦa]
  set v : ℝ → ℝ := fun t => (y t - η) * Efun t with hvdef
  have hvderiv : ∀ t ∈ Set.Icc a b,
      HasDerivAt v (A * φ t * (w t - η) * Efun t) t := by
    intro t ht
    have h1 : HasDerivAt (fun τ => y τ - η)
        (A * φ t * (w t - y t)) t := (hy t ht).sub_const η
    have h2 := h1.mul (hEderiv t)
    convert h2 using 1
    simp [hvdef, hEdef]
    ring
  have hvanti : AntitoneOn v (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    · intro t ht
      exact (hvderiv t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact ((hvderiv t (interior_subset ht)).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [(hvderiv t (interior_subset ht)).deriv]
      have hφt := hφ0 t (interior_subset ht)
      have hwt := hwη t (interior_subset ht)
      have hEt : 0 ≤ Efun t := (hEpos t).le
      have hwsub : w t - η ≤ 0 := by linarith
      have hcoef : 0 ≤ A * φ t * Efun t := by positivity
      have hnonpos : A * φ t * (w t - η) * Efun t ≤ 0 := by
        calc
          A * φ t * (w t - η) * Efun t =
              (A * φ t * Efun t) * (w t - η) := by ring
          _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hcoef hwsub
      simpa using hnonpos
  have hvle : v b ≤ v a :=
    hvanti (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab
  have hEbpos := hEpos b
  have hmain : y b - η ≤ (y a - η) / Efun b := by
    have hvle' : (y b - η) * Efun b ≤ (y a - η) * Efun a := by
      simpa [hvdef] using hvle
    rw [hEa] at hvle'
    rw [le_div_iff₀ hEbpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hvle'
  have hEinv :
      (y a - η) / Efun b =
        Real.exp (-(A * ∫ t in a..b, φ t)) * (y a - η) := by
    simp [hEdef, hΦdef, div_eq_mul_inv, Real.exp_neg, mul_comm, mul_left_comm,
      mul_assoc]
  rw [hEinv] at hmain
  have hfinal :
      y b ≤ Real.exp (-(A * ∫ t in a..b, φ t)) * (y a - η) + η := by
    linarith
  calc
    y b ≤ Real.exp (-(A * ∫ t in a..b, φ t)) * (y a - η) + η := hfinal
    _ = Real.exp (-(A * ∫ t in a..b, φ t)) * y a +
        (1 - Real.exp (-(A * ∫ t in a..b, φ t))) * η := by ring

private noncomputable def latchSample (j : ℕ) : ℝ :=
  2 * π * (j : ℝ) + 7 * π / 6

private noncomputable def latchStableStart (j : ℕ) : ℝ :=
  2 * π * (j : ℝ) + 5 * π / 6

private theorem latchSample_add (j n : ℕ) :
    latchSample (j + n) = latchSample j + 2 * π * (n : ℝ) := by
  unfold latchSample
  push_cast
  ring

private theorem latchSample_succ (j : ℕ) :
    latchSample (j + 1) = 2 * π * ((j : ℝ) + 1) + 7 * π / 6 := by
  unfold latchSample
  push_cast
  ring

private theorem latchSample_nonneg (j : ℕ) : 0 ≤ latchSample j := by
  unfold latchSample
  positivity

private theorem latchStableStart_nonneg (j : ℕ) : 0 ≤ latchStableStart j := by
  unfold latchStableStart
  positivity

private theorem latch_cycle_cover {base t : ℝ} (hbase : base ≤ t) :
    ∃ n : ℕ, base + 2 * π * (n : ℝ) ≤ t ∧
      t ≤ base + 2 * π * ((n : ℝ) + 1) := by
  let p : ℝ := 2 * π
  have hp : 0 < p := by
    dsimp [p]
    positivity
  let x : ℝ := (t - base) / p
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (sub_nonneg.mpr hbase) hp.le
  refine ⟨Nat.floor x, ?_, ?_⟩
  · have hfloor : ((Nat.floor x : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
    have hmul := mul_le_mul_of_nonneg_left hfloor hp.le
    have hpx : p * x = t - base := by
      dsimp [x]
      field_simp [hp.ne']
    dsimp [p] at hmul hpx
    nlinarith
  · have hlt : x < ((Nat.floor x : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
    have hmul := mul_lt_mul_of_pos_left hlt hp
    have hpx : p * x = t - base := by
      dsimp [x]
      field_simp [hp.ne']
    dsimp [p] at hmul hpx
    nlinarith

private theorem convex_combo_le_max {θ x η : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ * x + (1 - θ) * η ≤ max x η := by
  by_cases hx : x ≤ η
  · have hmax : max x η = η := max_eq_right hx
    rw [hmax]
    nlinarith
  · have hx' : η ≤ x := le_of_lt (lt_of_not_ge hx)
    have hmax : max x η = x := max_eq_left hx'
    rw [hmax]
    nlinarith

private theorem latch_drift_upper
    (K : ℝ) (hK0 : 0 ≤ K) (R : ℕ)
    (y w : ℝ → ℝ) (a b C ε : ℝ)
    (hab : a ≤ b) (ha0 : 0 ≤ a) (hC0 : 0 ≤ C)
    (hy01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ y t ∧ y t ≤ 1)
    (hw01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ w t ∧ w t ≤ 1)
    (hy : ∀ t ∈ Set.Icc a b,
      HasDerivAt y (K * gPulse R t * (w t - y t)) t)
    (hg : ∀ t ∈ Set.Icc a b, gPulse R t ≤ C)
    (hε : K * C * (b - a) ≤ ε) :
    y b ≤ y a + ε := by
  have hbound : ∀ t ∈ Set.Icc a b,
      |K * gPulse R t * (w t - y t)| ≤ K * C := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans ha0 ht.1
    have hyt := hy01 t ht0
    have hwt := hw01 t ht0
    have hwy : |w t - y t| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hg0 := gPulse_nonneg R t
    have hgC := hg t ht
    calc
      |K * gPulse R t * (w t - y t)|
          = K * gPulse R t * |w t - y t| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hK0, abs_of_nonneg hg0]
      _ ≤ K * C * 1 := by
            gcongr
      _ = K * C := by ring
  have hhold := hold_bound y
    (fun t => K * gPulse R t * (w t - y t)) (K * C) a b hab hy hbound
  have hdiff : y b - y a ≤ ε := by
    calc
      y b - y a ≤ |y b - y a| := le_abs_self _
      _ ≤ K * C * (b - a) := hhold
      _ ≤ ε := hε
  linarith

private theorem latch_stable_max_upper
    (K : ℝ) (hK : 0 < K) (R : ℕ)
    (y w : ℝ → ℝ) (η a b : ℝ)
    (hab : a ≤ b)
    (hwη : ∀ t ∈ Set.Icc a b, w t ≤ η)
    (hy : ∀ t ∈ Set.Icc a b,
      HasDerivAt y (K * gPulse R t * (w t - y t)) t) :
    y b ≤ max (y a) η := by
  have hmain := latch_one_sided_target_upper K hK (gPulse R) w y a b η hab
    (gPulse_continuous R)
    (fun t ht => gPulse_nonneg R t)
    hwη hy
  set θ : ℝ := Real.exp (-(K * ∫ t in a..b, gPulse R t)) with hθ
  have hθ0 : 0 ≤ θ := by
    dsimp [θ]
    exact (Real.exp_pos _).le
  have hint0 : 0 ≤ ∫ t in a..b, gPulse R t :=
    intervalIntegral.integral_nonneg hab (fun t _ => gPulse_nonneg R t)
  have hθ1 : θ ≤ 1 := by
    dsimp [θ]
    apply Real.exp_le_one_iff.mpr
    nlinarith [hK.le, hint0]
  exact le_trans (by simpa [hθ] using hmain) (convex_combo_le_max hθ0 hθ1)

private theorem latch_eventual_upper
    (K : ℝ) (hK : 0 < K) (R : ℕ)
    (hθ : ∀ j : ℕ,
      Real.exp (-(K *
        ∫ t in (2 * π * j + 5 * π / 6)..(2 * π * j + 7 * π / 6),
          gPulse R t)) ≤ (1 / 2 : ℝ))
    (hℓ : K * ((187 : ℝ) / 200) ^ R * (5 * π / 6) ≤ (1 / 100 : ℝ))
    (η : ℝ) (hη0 : 0 ≤ η) (hη : η < 1 / 8)
    (j₀ : ℕ) (y w : ℝ → ℝ)
    (hy01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ y t ∧ y t ≤ 1)
    (hw01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ w t ∧ w t ≤ 1)
    (hy : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt y (K * gPulse R t * (w t - y t)) t)
    (hwStable : ∀ j : ℕ, j₀ ≤ j →
      ∀ t ∈ Set.Icc (2 * π * j + 5 * π / 6) (2 * π * j + 7 * π / 6),
        w t ≤ η) :
    ∃ T : ℝ, ∀ t ≥ T, 0 ≤ y t ∧ y t ≤ 1 / 4 := by
  let C : ℝ := ((187 : ℝ) / 200) ^ R
  let ℓ : ℝ := (1 / 100 : ℝ)
  let B : ℝ := η + 4 * ℓ
  have hK0 : 0 ≤ K := hK.le
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hℓ0 : 0 ≤ ℓ := by norm_num [ℓ]
  have hleak : K * C * (5 * π / 6) ≤ ℓ := by
    simpa [C, ℓ] using hℓ
  have hoff_right :
      ∀ j : ℕ, ∀ t ∈ Set.Icc (latchSample j) (2 * π * ((j : ℝ) + 1)),
        y t ≤ y (latchSample j) + ℓ := by
    intro j t ht
    have hab : latchSample j ≤ t := ht.1
    have ha0 : 0 ≤ latchSample j := latchSample_nonneg j
    apply latch_drift_upper K hK0 R y w (latchSample j) t C ℓ hab ha0 hC0
      hy01 hw01
    · intro s hs
      exact hy s (le_trans ha0 hs.1)
    · intro s hs
      apply gPulse_le_off_right (j := j)
      · simpa [latchSample] using hs.1
      · exact le_trans hs.2 ht.2
    · have hlen : t - latchSample j ≤ 5 * π / 6 := by
        unfold latchSample at ht ⊢
        nlinarith [ht.2]
      calc
        K * C * (t - latchSample j) ≤ K * C * (5 * π / 6) := by
          gcongr
        _ ≤ ℓ := hleak
  have hoff_left :
      ∀ j : ℕ, ∀ t ∈ Set.Icc (2 * π * (j : ℝ)) (latchStableStart j),
        y t ≤ y (2 * π * (j : ℝ)) + ℓ := by
    intro j t ht
    have hab : 2 * π * (j : ℝ) ≤ t := ht.1
    have ha0 : 0 ≤ 2 * π * (j : ℝ) := by positivity
    apply latch_drift_upper K hK0 R y w (2 * π * (j : ℝ)) t C ℓ hab ha0 hC0
      hy01 hw01
    · intro s hs
      exact hy s (le_trans ha0 hs.1)
    · intro s hs
      apply gPulse_le_off_left (j := j)
      · exact hs.1
      · exact le_trans hs.2 ht.2
    · have hlen : t - 2 * π * (j : ℝ) ≤ 5 * π / 6 := by
        unfold latchStableStart at ht
        nlinarith [ht.2]
      calc
        K * C * (t - 2 * π * (j : ℝ)) ≤ K * C * (5 * π / 6) := by
          gcongr
        _ ≤ ℓ := hleak
  have hstable :
      ∀ j : ℕ, j₀ ≤ j → ∀ t ∈ Set.Icc (latchStableStart j) (latchSample j),
        y t ≤ max (y (latchStableStart j)) η := by
    intro j hj t ht
    have hab : latchStableStart j ≤ t := ht.1
    apply latch_stable_max_upper K hK R y w η (latchStableStart j) t hab
    · intro s hs
      apply hwStable j hj s
      constructor
      · simpa [latchStableStart] using hs.1
      · exact le_trans hs.2 ht.2
    · intro s hs
      exact hy s (le_trans (latchStableStart_nonneg j) hs.1)
  have hcycle :
      ∀ j : ℕ, j₀ ≤ j →
        y (latchSample (j + 1)) ≤
          Real.exp (-(K *
            ∫ t in (2 * π * (j + 1) + 5 * π / 6)..
              (2 * π * (j + 1) + 7 * π / 6), gPulse R t)) *
              y (latchSample j) + 2 * ℓ +
            (1 - Real.exp (-(K *
              ∫ t in (2 * π * (j + 1) + 5 * π / 6)..
                (2 * π * (j + 1) + 7 * π / 6), gPulse R t))) * η := by
    intro j hj
    let m : ℝ := 2 * π * ((j : ℝ) + 1)
    let s : ℝ := 2 * π * ((j : ℝ) + 1) + 5 * π / 6
    let e : ℝ := latchSample (j + 1)
    have hsam_m : latchSample j ≤ m := by
      dsimp [m, latchSample]
      nlinarith [Real.pi_pos]
    have hm_s : m ≤ s := by
      dsimp [m, s]
      nlinarith [Real.pi_pos]
    have hs_e : s ≤ e := by
      dsimp [s, e, latchSample]
      push_cast
      nlinarith [Real.pi_pos]
    have hm_bound : y m ≤ y (latchSample j) + ℓ := by
      apply hoff_right j m
      constructor
      · exact hsam_m
      · rfl
    have hs_bound : y s ≤ y (latchSample j) + 2 * ℓ := by
      have hs1 : y s ≤ y m + ℓ := by
        have := hoff_left (j + 1) s
        have hmem : s ∈ Set.Icc (2 * π * ((j + 1 : ℕ) : ℝ)) (latchStableStart (j + 1)) := by
          constructor
          · dsimp [s]
            push_cast
            nlinarith [Real.pi_pos]
          · dsimp [s, latchStableStart]
            push_cast
            exact le_rfl
        have hthis := this hmem
        simpa [m, s, Nat.cast_add, Nat.cast_one] using hthis
      linarith
    have hmain := latch_one_sided_target_upper K hK (gPulse R) w y s e η hs_e
      (gPulse_continuous R)
      (fun t ht => gPulse_nonneg R t)
      (by
        intro t ht
        apply hwStable (j + 1) (le_trans hj (Nat.le_succ j)) t
        constructor
        · simpa [s, latchStableStart, Nat.cast_add, Nat.cast_one] using ht.1
        · simpa [e, latchSample, Nat.cast_add, Nat.cast_one] using ht.2)
      (by
        intro t ht
        exact hy t (le_trans (by dsimp [s]; positivity) ht.1))
    have hθnonneg :
        0 ≤ Real.exp (-(K * ∫ t in s..e, gPulse R t)) :=
      (Real.exp_pos _).le
    calc
      y (latchSample (j + 1)) = y e := rfl
      _ ≤ Real.exp (-(K * ∫ t in s..e, gPulse R t)) * y s +
          (1 - Real.exp (-(K * ∫ t in s..e, gPulse R t))) * η := hmain
      _ ≤ Real.exp (-(K * ∫ t in s..e, gPulse R t)) *
            (y (latchSample j) + 2 * ℓ) +
          (1 - Real.exp (-(K * ∫ t in s..e, gPulse R t))) * η := by
            gcongr
      _ ≤ Real.exp (-(K * ∫ t in s..e, gPulse R t)) * y (latchSample j) +
            2 * ℓ +
          (1 - Real.exp (-(K * ∫ t in s..e, gPulse R t))) * η := by
            have hθle : Real.exp (-(K * ∫ t in s..e, gPulse R t)) ≤ 1 := by
              apply Real.exp_le_one_iff.mpr
              have hint0 : 0 ≤ ∫ t in s..e, gPulse R t :=
                intervalIntegral.integral_nonneg hs_e (fun t _ => gPulse_nonneg R t)
              nlinarith [hK.le, hint0]
            nlinarith [hℓ0, hθnonneg, hθle]
      _ = Real.exp (-(K *
            ∫ t in (2 * π * (j + 1) + 5 * π / 6)..
              (2 * π * (j + 1) + 7 * π / 6), gPulse R t)) *
              y (latchSample j) + 2 * ℓ +
            (1 - Real.exp (-(K *
              ∫ t in (2 * π * (j + 1) + 5 * π / 6)..
                (2 * π * (j + 1) + 7 * π / 6), gPulse R t))) * η := by
            congr 3 <;> simp [s, e, latchSample, Nat.cast_add, Nat.cast_one]
  have hsample :
      ∀ n : ℕ, y (latchSample (j₀ + n)) ≤ B + (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero =>
        have hyb := (hy01 (latchSample j₀) (latchSample_nonneg j₀)).2
        dsimp [B]
        norm_num
        nlinarith [hη0, hℓ0, hyb]
    | succ n ih =>
        have hjle : j₀ ≤ j₀ + n := Nat.le_add_right _ _
        have hrec := hcycle (j₀ + n) hjle
        have htheta := hθ (j₀ + n + 1)
        have htheta0 :
            0 ≤ Real.exp (-(K *
              ∫ t in (2 * π * (j₀ + n + 1) + 5 * π / 6)..
                (2 * π * (j₀ + n + 1) + 7 * π / 6), gPulse R t)) :=
          (Real.exp_pos _).le
        have hstep :
            y (latchSample (j₀ + (n + 1))) ≤
              B + (1 / 2 : ℝ) ^ (n + 1) := by
          have hrec' :
              y (latchSample (j₀ + (n + 1))) ≤
                Real.exp (-(K *
                  ∫ t in (2 * π * (j₀ + n + 1) + 5 * π / 6)..
                    (2 * π * (j₀ + n + 1) + 7 * π / 6), gPulse R t)) *
                    y (latchSample (j₀ + n)) + 2 * ℓ +
                  (1 - Real.exp (-(K *
                    ∫ t in (2 * π * (j₀ + n + 1) + 5 * π / 6)..
                      (2 * π * (j₀ + n + 1) + 7 * π / 6), gPulse R t))) * η := by
            simpa [Nat.add_assoc] using hrec
          calc
            y (latchSample (j₀ + (n + 1))) ≤
                Real.exp (-(K *
                  ∫ t in (2 * π * (j₀ + n + 1) + 5 * π / 6)..
                    (2 * π * (j₀ + n + 1) + 7 * π / 6), gPulse R t)) *
                    y (latchSample (j₀ + n)) + 2 * ℓ +
                  (1 - Real.exp (-(K *
                    ∫ t in (2 * π * (j₀ + n + 1) + 5 * π / 6)..
                      (2 * π * (j₀ + n + 1) + 7 * π / 6), gPulse R t))) * η := hrec'
            _ ≤ B + (1 / 2 : ℝ) ^ (n + 1) := by
              have hpownonneg : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
              have hpowstep : (1 / 2 : ℝ) ^ (n + 1) = (1 / 2 : ℝ) * (1 / 2) ^ n := by
                rw [pow_succ]
                ring
              set θv : ℝ := Real.exp (-(K *
                  ∫ t in (2 * π * (j₀ + n + 1) + 5 * π / 6)..
                    (2 * π * (j₀ + n + 1) + 7 * π / 6), gPulse R t))
              have hθv0 : 0 ≤ θv := by simpa [θv] using htheta0
              have hθv : θv ≤ 1 / 2 := by simpa [θv, Nat.cast_add, Nat.cast_one] using htheta
              have hfirst :
                  θv * y (latchSample (j₀ + n)) + 2 * ℓ + (1 - θv) * η
                    ≤ θv * (B + (1 / 2 : ℝ) ^ n) + 2 * ℓ + (1 - θv) * η := by
                gcongr
              have hsecond :
                  θv * (B + (1 / 2 : ℝ) ^ n) + 2 * ℓ + (1 - θv) * η
                    ≤ B + (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n := by
                dsimp [B]
                nlinarith [hθv, hθv0, hpownonneg, hℓ0]
              dsimp [B]
              rw [hpowstep]
              exact le_trans (by simpa [θv] using hfirst) hsecond
        exact hstep
  refine ⟨latchSample (j₀ + 4), ?_⟩
  intro t htT
  have hy_nonneg := (hy01 t (le_trans (latchSample_nonneg (j₀ + 4)) htT)).1
  refine ⟨hy_nonneg, ?_⟩
  obtain ⟨n, hnlo, hnhi⟩ := latch_cycle_cover htT
  let j : ℕ := j₀ + 4 + n
  have hj_ge : j₀ ≤ j := by
    dsimp [j]
    omega
  have hj4 : ∃ m : ℕ, j = j₀ + m ∧ 4 ≤ m := by
    refine ⟨4 + n, ?_, ?_⟩
    · dsimp [j]
      omega
    · omega
  have hsamp_eq : latchSample j = latchSample (j₀ + 4) + 2 * π * (n : ℝ) := by
    simpa [j, Nat.add_assoc] using latchSample_add (j₀ + 4) n
  have hnext_eq : latchSample (j + 1) =
      latchSample (j₀ + 4) + 2 * π * ((n : ℝ) + 1) := by
    simpa [j, Nat.add_assoc, Nat.cast_add, Nat.cast_one] using
      latchSample_add (j₀ + 4) (n + 1)
  have htcycle : t ∈ Set.Icc (latchSample j) (latchSample (j + 1)) := by
    constructor
    · simpa [hsamp_eq] using hnlo
    · simpa [hnext_eq, Nat.cast_add, Nat.cast_one] using hnhi
  obtain ⟨m, hjm, hm4⟩ := hj4
  have hsample_j : y (latchSample j) ≤ B + (1 / 2 : ℝ) ^ m := by
    simpa [hjm] using hsample m
  have hpow_le : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ (4 : ℕ) := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hm4
  have hsample_j' : y (latchSample j) ≤ B + (1 / 16 : ℝ) := by
    norm_num at hpow_le
    nlinarith
  have hcycle_bound : y t ≤ max (y (latchSample j) + 2 * ℓ) η := by
    let mpt : ℝ := 2 * π * ((j : ℝ) + 1)
    have hmpt_eq : 2 * π * ((j + 1 : ℕ) : ℝ) = mpt := by
      dsimp [mpt]
      rw [Nat.cast_add, Nat.cast_one]
    have hsample_mpt : latchSample j ≤ mpt := by
      change 2 * π * (j : ℝ) + 7 * π / 6 ≤ 2 * π * ((j : ℝ) + 1)
      nlinarith [Real.pi_pos]
    have hm_bound : y mpt ≤ y (latchSample j) + ℓ := by
      apply hoff_right j mpt
      exact ⟨hsample_mpt, le_rfl⟩
    have hstable_left :
        2 * π * ((j + 1 : ℕ) : ℝ) ≤ latchStableStart (j + 1) := by
      change 2 * π * ((j + 1 : ℕ) : ℝ) ≤
        2 * π * ((j + 1 : ℕ) : ℝ) + 5 * π / 6
      exact le_add_of_nonneg_right (by positivity)
    by_cases ht_m : t ≤ mpt
    · have hmem : t ∈ Set.Icc (latchSample j) mpt := ⟨htcycle.1, ht_m⟩
      have h1 := hoff_right j t hmem
      exact le_trans (by nlinarith [hℓ0]) (le_max_left _ _)
    · have hm_t : mpt ≤ t := le_of_lt (lt_of_not_ge ht_m)
      by_cases ht_s : t ≤ latchStableStart (j + 1)
      ·
        have hleft : y t ≤ y mpt + ℓ := by
          have hmem : t ∈ Set.Icc (2 * π * ((j + 1 : ℕ) : ℝ))
              (latchStableStart (j + 1)) := by
            constructor
            · rw [hmpt_eq]
              exact hm_t
            · exact ht_s
          have := hoff_left (j + 1) t hmem
          rw [hmpt_eq] at this
          exact this
        exact le_trans (by nlinarith) (le_max_left _ _)
      · have hs_t : latchStableStart (j + 1) ≤ t := le_of_lt (lt_of_not_ge ht_s)
        have hs_bound :
            y (latchStableStart (j + 1)) ≤ y (latchSample j) + 2 * ℓ := by
          have hleft : y (latchStableStart (j + 1)) ≤ y mpt + ℓ := by
            have hmem :
                latchStableStart (j + 1) ∈ Set.Icc (2 * π * ((j + 1 : ℕ) : ℝ))
                (latchStableStart (j + 1)) := by
              constructor
              · exact hstable_left
              · exact le_rfl
            have := hoff_left (j + 1) (latchStableStart (j + 1)) hmem
            rw [hmpt_eq] at this
            exact this
          linarith [hm_bound]
        have hstab : y t ≤ max (y (latchStableStart (j + 1))) η := by
          have hmem : t ∈ Set.Icc (latchStableStart (j + 1)) (latchSample (j + 1)) := by
            constructor
            · exact hs_t
            · exact htcycle.2
          exact hstable (j + 1) (le_trans hj_ge (Nat.le_succ j)) t hmem
        have hstab_bound :
            max (y (latchStableStart (j + 1))) η ≤ max (y (latchSample j) + 2 * ℓ) η := by
          apply max_le
          · exact le_trans hs_bound (le_max_left _ _)
          · exact le_max_right _ _
        exact le_trans hstab hstab_bound
  have harith : B + (1 / 16 : ℝ) + 2 * ℓ < 1 / 4 := by
    calc
      B + (1 / 16 : ℝ) + 2 * ℓ = η + (49 / 400 : ℝ) := by
        dsimp [B, ℓ]
        ring
      _ < 1 / 8 + (49 / 400 : ℝ) := by
        linarith [hη]
      _ < 1 / 4 := by
        norm_num
  have hmax_bound : max (y (latchSample j) + 2 * ℓ) η ≤ B + (1 / 16 : ℝ) + 2 * ℓ := by
    apply max_le
    · calc
        y (latchSample j) + 2 * ℓ = 2 * ℓ + y (latchSample j) := by ring
        _ ≤ 2 * ℓ + (B + (1 / 16 : ℝ)) := add_le_add_right hsample_j' (2 * ℓ)
        _ = B + (1 / 16 : ℝ) + 2 * ℓ := by ring
    · dsimp [B]
      linarith [hℓ0]
  exact le_of_lt (lt_of_le_of_lt (le_trans hcycle_bound hmax_bound) harith)

/-- **P9, halt-latch eventual readout** (lem:halt-latch).  Run the
latch on an iterator that all-time tracks at radius `≤ I.ρ` and whose
z-channel stays in the working set `W` (R1#8) and, on the mid-cycle
stable window, in the tube of the POST-transition configuration
`step^[j+1]` (R1#9).  If the machine halts the latch eventually stays
in `[3/4, 1]`; if it never halts, in `[0, 1/4]`.  Parameters `K, R`
are chosen uniformly (independent of `w` — they depend only on `ηH`
and the gate integrals; prop:latch-feasibility). -/
theorem dyn_halt_latch_eventual_readout
    {Conf : Type} [Primcodable Conf]
    (Mch : DiscreteMachine Conf) (d : ℕ) (E : LatticeEncoding Mch d)
    (S : RobustRealExtension Mch d E)
    (I : HaltIndicator Mch d E) :
    ∃ (K : ℚ) (R : ℕ), 0 < K ∧
      ∀ (A : ℚ), 0 < A → ∀ (L : ℕ) (c₀ c₁ : ℚ) (w : ℕ)
        (sol : DynIteratorSol d S.evalF A L c₀ c₁ (orbitPoint Mch E w 0)),
        (∀ j : ℕ, ∀ i,
          |sol.z (2*π*j) i - orbitPoint Mch E w j i| ≤ (I.ρ : ℝ) ∧
          |sol.u (2*π*j) i - orbitPoint Mch E w j i| ≤ (I.ρ : ℝ)) →
        (∀ t : ℝ, 0 ≤ t → sol.z t ∈ I.W) →
        (∀ j : ℕ, ∀ t ∈ Set.Icc (2*π*j + 5*π/6) (2*π*j + 7*π/6),
          ∀ i, |sol.z t i - orbitPoint Mch E w (j+1) i| ≤ (I.ρ : ℝ)) →
        ∀ L : DynLatchSol sol I.evalH (K : ℝ) R,
          (Mch.haltsOn w →
            ∃ T : ℝ, ∀ t ≥ T, 3/4 ≤ L.a t ∧ L.a t ≤ 1) ∧
          (¬ Mch.haltsOn w →
            ∃ T : ℝ, ∀ t ≥ T, 0 ≤ L.a t ∧ L.a t ≤ 1/4) := by
  classical
  obtain ⟨K, R, hK, hθ, hℓ⟩ := latch_parameter_exists
  refine ⟨K, R, hK, ?_⟩
  intro A hA L c₀ c₁ w sol _htrack hzW hstable L
  have hKℝ : 0 < (K : ℝ) := by exact_mod_cast hK
  have hη0ℝ : 0 ≤ (I.ηH : ℝ) := by exact_mod_cast I.ηH_pos.le
  have hηltℝ : (I.ηH : ℝ) < 1 / 8 := by
    have h : (I.ηH : ℝ) < ((1 / 8 : ℚ) : ℝ) := by
      exact_mod_cast I.ηH_lt
    norm_num at h
    exact h
  have hHunit : ∀ t : ℝ, 0 ≤ t →
      0 ≤ I.evalH (sol.z t) ∧ I.evalH (sol.z t) ≤ 1 := by
    intro t ht
    exact I.in_unit (sol.z t) (hzW t ht)
  have haUnit : ∀ t : ℝ, 0 ≤ t → 0 ≤ L.a t ∧ L.a t ≤ 1 :=
    dyn_latch_mem_unitInterval sol I.evalH (K : ℝ) hKℝ R L hHunit
  constructor
  · intro hhalt
    obtain ⟨jhalt, hjhalt⟩ := hhalt
    let y : ℝ → ℝ := fun t => 1 - L.a t
    let wtar : ℝ → ℝ := fun t => 1 - I.evalH (sol.z t)
    have hy01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ y t ∧ y t ≤ 1 := by
      intro t ht
      have ht' := haUnit t ht
      dsimp [y]
      constructor <;> linarith
    have hw01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ wtar t ∧ wtar t ≤ 1 := by
      intro t ht
      have ht' := hHunit t ht
      dsimp [wtar]
      constructor <;> linarith
    have hyderiv : ∀ t : ℝ, 0 ≤ t →
        HasDerivAt y ((K : ℝ) * gPulse R t * (wtar t - y t)) t := by
      intro t _ht
      have h0 : HasDerivAt (fun τ => 1 - L.a τ)
          (-((K : ℝ) * gPulse R t * (I.evalH (sol.z t) - L.a t))) t :=
        (L.ode_a t).const_sub 1
      convert h0 using 1 <;> dsimp [y, wtar] <;> ring
    have hwStable : ∀ j : ℕ, jhalt + 1 ≤ j →
        ∀ t ∈ Set.Icc (2 * π * j + 5 * π / 6) (2 * π * j + 7 * π / 6),
          wtar t ≤ (I.ηH : ℝ) := by
      intro j hj t ht
      have hclose := hstable j t ht
      have hhalted :
          Mch.halted (Mch.step^[j + 1] (Mch.init w)) = true := by
        apply DiscreteMachine.halted_of_halts_after Mch hjhalt (j + 1)
        omega
      have hH := I.on_halted (Mch.step^[j + 1] (Mch.init w)) hhalted
        (sol.z t) hclose
      dsimp [wtar, HaltIndicator.evalH]
      linarith
    obtain ⟨T, hT⟩ := latch_eventual_upper (K : ℝ) hKℝ R hθ hℓ
      (I.ηH : ℝ) hη0ℝ hηltℝ (jhalt + 1) y wtar
      hy01 hw01 hyderiv hwStable
    refine ⟨T, ?_⟩
    intro t ht
    have hyT := hT t ht
    dsimp [y] at hyT
    constructor
    · linarith
    · linarith
  · intro hnonhalt
    let y : ℝ → ℝ := L.a
    let wtar : ℝ → ℝ := fun t => I.evalH (sol.z t)
    have hy01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ y t ∧ y t ≤ 1 := by
      intro t ht
      exact haUnit t ht
    have hw01 : ∀ t : ℝ, 0 ≤ t → 0 ≤ wtar t ∧ wtar t ≤ 1 := by
      intro t ht
      exact hHunit t ht
    have hyderiv : ∀ t : ℝ, 0 ≤ t →
        HasDerivAt y ((K : ℝ) * gPulse R t * (wtar t - y t)) t := by
      intro t _ht
      simpa [y, wtar] using L.ode_a t
    have hwStable : ∀ j : ℕ, 0 ≤ j →
        ∀ t ∈ Set.Icc (2 * π * j + 5 * π / 6) (2 * π * j + 7 * π / 6),
          wtar t ≤ (I.ηH : ℝ) := by
      intro j _hj t ht
      have hclose := hstable j t ht
      have hrunning :
          Mch.halted (Mch.step^[j + 1] (Mch.init w)) = false :=
        DiscreteMachine.running_of_not_haltsOn Mch hnonhalt
      exact I.on_running (Mch.step^[j + 1] (Mch.init w)) hrunning
        (sol.z t) hclose
    obtain ⟨T, hT⟩ := latch_eventual_upper (K : ℝ) hKℝ R hθ hℓ
      (I.ηH : ℝ) hη0ℝ hηltℝ 0 y wtar
      hy01 hw01 hyderiv hwStable
    refine ⟨T, ?_⟩
    intro t ht
    exact hT t ht

/-! ## Existence of solutions (Picard–Lindelöf layer) -/

-- old unconditional iterator_solution_exists DELETED (false in general;
-- superseded by Existence.lean's boxed_iterator_exists per R3#8/D-runway).

/-- **P10b (R3#7), latch solution existence**: the scalar latch ODE
has a global solution riding on any iterator solution, provided the
driving term is continuous (the indicator polynomial composed with
the continuous z-channel).  Scalar linear ODE with continuous
time-dependent coefficients; same Picard–Lindelöf layer as P10. -/
theorem dyn_latch_solution_exists
    {d : ℕ} {Fr : (Fin d → ℝ) → Fin d → ℝ} {A : ℚ} {L : ℕ} {c₀ c₁ : ℚ}
    {x₀ : Fin d → ℝ} (sol : DynIteratorSol d Fr A L c₀ c₁ x₀)
    (Hval : (Fin d → ℝ) → ℝ)
    (hHcont : Continuous fun t => Hval (sol.z t))
    (K : ℝ) (R : ℕ) :
    Nonempty (DynLatchSol sol Hval K R) := by
  classical
  set φ : ℝ → ℝ := fun t => K * gPulse R t with hφdef
  have hφcont : Continuous φ := by
    have hg : Continuous (gPulse R) := by
      unfold gPulse
      fun_prop
    fun_prop
  set Φ : ℝ → ℝ := fun t => ∫ s in (0:ℝ)..t, φ s with hΦdef
  have hΦderiv : ∀ t : ℝ, HasDerivAt Φ (φ t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hφcont.intervalIntegrable 0 t)
      (hφcont.stronglyMeasurableAtFilter _ _)
      hφcont.continuousAt
  have hΦcont : Continuous Φ := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hΦderiv t).continuousAt
  set B : ℝ → ℝ :=
    fun t => ∫ s in (0:ℝ)..t, φ s * Hval (sol.z s) * Real.exp (Φ s) with hBdef
  have hBcont_integrand :
      Continuous (fun s : ℝ => φ s * Hval (sol.z s) * Real.exp (Φ s)) := by
    have hE : Continuous fun s : ℝ => Real.exp (Φ s) :=
      Real.continuous_exp.comp hΦcont
    exact (hφcont.mul hHcont).mul hE
  have hBderiv : ∀ t : ℝ,
      HasDerivAt B (φ t * Hval (sol.z t) * Real.exp (Φ t)) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right
      (hBcont_integrand.intervalIntegrable 0 t)
      (hBcont_integrand.stronglyMeasurableAtFilter _ _)
      hBcont_integrand.continuousAt
  set a : ℝ → ℝ := fun t => Real.exp (-(Φ t)) * B t with hadef
  refine ⟨{ a := a, init_a := ?_, ode_a := ?_ }⟩
  · simp [hadef, hBdef]
  · intro t
    have hExpDeriv : HasDerivAt (fun τ : ℝ => Real.exp (-(Φ τ)))
        (-(φ t) * Real.exp (-(Φ t))) t := by
      have hneg : HasDerivAt (fun τ : ℝ => -(Φ τ)) (-(φ t)) t :=
        (hΦderiv t).neg
      have h := hneg.exp
      convert h using 1
      ring
    have hprod := hExpDeriv.mul (hBderiv t)
    convert hprod using 1
    simp only [hadef, hφdef, hBdef]
    have hexp : Real.exp (-(Φ t)) * Real.exp (Φ t) = 1 := by
      rw [← Real.exp_add]
      simp
    have hterm :
        Real.exp (-(Φ t)) *
            (K * gPulse R t * Hval (sol.z t) * Real.exp (Φ t)) =
          K * gPulse R t * Hval (sol.z t) := by
      calc
        Real.exp (-(Φ t)) *
            (K * gPulse R t * Hval (sol.z t) * Real.exp (Φ t)) =
            (Real.exp (-(Φ t)) * Real.exp (Φ t)) *
              (K * gPulse R t * Hval (sol.z t)) := by
              ring
        _ = K * gPulse R t * Hval (sol.z t) := by
              rw [hexp]
              ring
    rw [hterm]
    ring

private theorem dyn_cycle_cover {t : ℝ} (ht : 0 ≤ t) :
    ∃ j : ℕ, 2 * Real.pi * (j : ℝ) ≤ t ∧
      t ≤ 2 * Real.pi * ((j : ℝ) + 1) := by
  let p : ℝ := 2 * Real.pi
  have hp : 0 < p := by
    dsimp [p]
    positivity
  let x : ℝ := t / p
  have hx0 : 0 ≤ x := by exact div_nonneg ht hp.le
  refine ⟨Nat.floor x, ?_, ?_⟩
  · have hfloor : ((Nat.floor x : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
    have hmul := mul_le_mul_of_nonneg_left hfloor hp.le
    have hpx : p * x = t := by dsimp [x]; field_simp [hp.ne']
    dsimp [p] at hmul hpx
    nlinarith
  · have hlt : x < ((Nat.floor x : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one x
    have hmul := mul_lt_mul_of_pos_left hlt hp
    have hpx : p * x = t := by dsimp [x]; field_simp [hp.ne']
    dsimp [p] at hmul hpx
    nlinarith

private theorem dyn_phiZ_continuous_local (L : ℕ) (c₀ c₁ : ℝ) :
    Continuous fun t : ℝ => Real.exp (c₁ * t) * bGateZ L (c₀ * t) t := by
  unfold bGateZ rPulse
  fun_prop

private theorem dyn_phiU_continuous_local (L : ℕ) (c₀ c₁ : ℝ) :
    Continuous fun t : ℝ => Real.exp (c₁ * t) * bGateU L (c₀ * t) t := by
  unfold bGateU qPulse
  fun_prop

private theorem dyn_active_integral_lower_z_to
    (A : ℝ) (L : ℕ) (c₀ c₁ : ℝ) (j : ℕ) {t : ℝ}
    (hA : 0 ≤ A) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlo : 2 * π * j + 5 * π / 6 ≤ t)
    (_hhi : t ≤ 2 * π * j + π) :
    A * Real.exp (c₁ * (2 * π * j))
        * Real.exp (-(c₀ * 2 * π * (j + 1) * (1 / 4) ^ L)) * (2 * π / 3)
      ≤ ∫ s in (2 * π * j)..t,
          A * (Real.exp (c₁ * s) * bGateZ L (c₀ * s) s) := by
  have hπ := Real.pi_pos
  set a : ℝ := 2 * π * (j : ℝ) with ha
  have h1 : a ≤ a + π / 6 := by linarith
  have h2 : a + π / 6 ≤ a + 5 * π / 6 := by linarith
  have h5t : a + 5 * π / 6 ≤ t := by simpa [ha] using hlo
  have h6t : a + π / 6 ≤ t := le_trans h2 h5t
  have hat : a ≤ t := le_trans h1 h6t
  have ha_nonneg : 0 ≤ a := by dsimp [a]; positivity
  let φ : ℝ → ℝ := fun s => A * (Real.exp (c₁ * s) * bGateZ L (c₀ * s) s)
  have hφc : Continuous φ := by
    dsimp [φ]
    exact continuous_const.mul (dyn_phiZ_continuous_local L c₀ c₁)
  have hint : ∀ u v : ℝ, IntervalIntegrable φ MeasureTheory.volume u v :=
    fun u v => hφc.intervalIntegrable u v
  have e1 : (∫ s in a..(a + π / 6), φ s)
      + (∫ s in (a + π / 6)..t, φ s)
      = ∫ s in a..t, φ s :=
    intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have e2 : (∫ s in (a + π / 6)..(a + 5 * π / 6), φ s)
      + (∫ s in (a + 5 * π / 6)..t, φ s)
      = ∫ s in (a + π / 6)..t, φ s :=
    intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
  have hφ_nonneg : ∀ s, 0 ≤ φ s := by
    intro s
    dsimp [φ]
    exact mul_nonneg hA (mul_nonneg (Real.exp_pos _).le (bGateZ_pos L (c₀ * s) s).le)
  have hn1 : 0 ≤ ∫ s in a..(a + π / 6), φ s :=
    intervalIntegral.integral_nonneg h1 (fun s _ => hφ_nonneg s)
  have hn3 : 0 ≤ ∫ s in (a + 5 * π / 6)..t, φ s :=
    intervalIntegral.integral_nonneg h5t (fun s _ => hφ_nonneg s)
  have hmid : A * Real.exp (c₁ * a)
        * Real.exp (-(c₀ * (a + 2 * π) * (1 / 4) ^ L)) * (2 * π / 3)
      ≤ ∫ s in (a + π / 6)..(a + 5 * π / 6), φ s := by
    have hconst : (∫ _s in (a + π / 6)..(a + 5 * π / 6),
        A * Real.exp (c₁ * a)
          * Real.exp (-(c₀ * (a + 2 * π) * (1 / 4) ^ L)))
        = A * Real.exp (c₁ * a)
          * Real.exp (-(c₀ * (a + 2 * π) * (1 / 4) ^ L)) * (2 * π / 3) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [← hconst]
    apply intervalIntegral.integral_mono_on h2 _root_.intervalIntegrable_const (hint _ _)
    intro s hs
    dsimp [φ]
    have has : a ≤ s := le_trans h1 hs.1
    have hsb : s ≤ a + 2 * π := by nlinarith [hπ, hs.2]
    have hα : Real.exp (c₁ * a) ≤ Real.exp (c₁ * s) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hgate : Real.exp (-(c₀ * (a + 2 * π) * (1 / 4) ^ L)) ≤
        bGateZ L (c₀ * s) s := by
      have hmt : c₀ * s ≤ c₀ * (a + 2 * π) := mul_le_mul_of_nonneg_left hsb hc₀
      have hsine : (1 : ℝ) / 2 ≤ Real.sin s :=
        sin_window_ge j (by simpa [ha] using hs.1) (by simpa [ha] using hs.2)
      calc
        Real.exp (-(c₀ * (a + 2 * π) * (1 / 4) ^ L))
            ≤ Real.exp (-(c₀ * s * (1 / 4) ^ L)) := by
              apply Real.exp_le_exp.mpr
              have hp : 0 ≤ ((1 : ℝ) / 4) ^ L := pow_nonneg (by norm_num) L
              nlinarith
        _ ≤ bGateZ L (c₀ * s) s :=
              bGateZ_ge_active L (mul_nonneg hc₀ (le_trans ha_nonneg has)) hsine
    have hmul := mul_le_mul hα hgate (Real.exp_pos _).le (Real.exp_pos _).le
    have hA_mul := mul_le_mul_of_nonneg_left hmul hA
    simpa [mul_assoc] using hA_mul
  have hgoal_mid :
      A * Real.exp (c₁ * (2 * π * j))
        * Real.exp (-(c₀ * 2 * π * (j + 1) * (1 / 4) ^ L)) * (2 * π / 3)
      ≤ ∫ s in (a + π / 6)..(a + 5 * π / 6), φ s := by
    simpa [ha, Nat.cast_add, left_distrib, add_comm, add_left_comm, add_assoc,
      mul_add, add_mul, mul_assoc] using hmid
  have hfull :
      A * Real.exp (c₁ * (2 * π * j))
        * Real.exp (-(c₀ * 2 * π * (j + 1) * (1 / 4) ^ L)) * (2 * π / 3)
      ≤ ∫ s in a..t, φ s := by
    linarith [e1, e2, hn1, hn3, hgoal_mid]
  simpa [φ, ha] using hfull

private theorem dyn_exp_decay_cycle_integral_le
    (A lam a b : ℝ) (hA : 0 ≤ A) (hlam : 0 < lam) (_hab : a ≤ b) :
    ∫ t in a..b, A * Real.exp (-(lam * t)) ≤ A * Real.exp (-(lam * a)) / lam := by
  have hcont : Continuous fun t : ℝ => A * Real.exp (-(lam * t)) := by fun_prop
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => -(A / lam) * Real.exp (-(lam * s)))
        (A * Real.exp (-(lam * t))) t := by
    intro t
    have hin : HasDerivAt (fun s : ℝ => -(lam * s)) (-lam) t := by
      simpa using ((hasDerivAt_id t).const_mul lam).neg
    have h := hin.exp.const_mul (-(A / lam))
    convert h using 1
    field_simp [ne_of_gt hlam]
  have hftc :
      (∫ t in a..b, A * Real.exp (-(lam * t)))
        = (-(A / lam) * Real.exp (-(lam * b)))
          - (-(A / lam) * Real.exp (-(lam * a))) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t _
      exact hderiv t
    · exact hcont.intervalIntegrable a b
  rw [hftc]
  have hterm_nonneg : 0 ≤ (A / lam) * Real.exp (-(lam * b)) := by positivity
  calc
    -(A / lam) * Real.exp (-(lam * b)) - (-(A / lam) * Real.exp (-(lam * a)))
        = A * Real.exp (-(lam * a)) / lam - (A / lam) * Real.exp (-(lam * b)) := by ring
    _ ≤ A * Real.exp (-(lam * a)) / lam := by linarith

set_option maxHeartbeats 800000 in
-- The window proof repeats the dynamic recurrence estimates with an extra
-- split at the stable window, which exceeds the default heartbeat budget.
/-- Dynamic stable-window tracking from the box-only moving hypothesis.

This is the dynamic counterpart of `stable_window_tracking`: sampled
tracking at the left boundary comes from `dyn_all_time_tracking`, the
first half uses the active `z` gate, and the post-`π` tail is paid for by
the dynamic leak envelope `dynChi`. -/
theorem dyn_stable_window_tracking
    {Conf : Type} [Primcodable Conf]
    (Mch : DiscreteMachine Conf) (d : ℕ) (E : LatticeEncoding Mch d)
    (S : RobustRealExtension Mch d E)
    (A : ℚ) (hA : 0 < A)
    (L : ℕ) (c₀ c₁ : ℚ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁)
    (hlam : 0 < (c₀ : ℝ) * (1 / 2) ^ L - (c₁ : ℝ)) (w : ℕ)
    (sol : DynIteratorSol d S.evalF A L c₀ c₁ (orbitPoint Mch E w 0))
    (D_K : ℝ) (hD : 0 < D_K)
    (hbox : ∀ (j : ℕ) (t : ℝ), t ∈ Set.Icc (2 * π * j) (2 * π * (j + 1)) →
      (∀ i, |orbitPoint Mch E w (j + 1) i - orbitPoint Mch E w j i| ≤ D_K) ∧
      (∀ i, |sol.z t i - orbitPoint Mch E w j i| ≤ D_K) ∧
      (∀ i, |sol.u t i - orbitPoint Mch E w j i| ≤ D_K) ∧
      (∀ i, |S.evalF (sol.u t) i - orbitPoint Mch E w j i| ≤ D_K))
    (η : ℝ) (hη : 0 < η)
    (hcasc : ∀ j : ℕ,
      2 * dynKappa (A : ℝ) L (c₀ : ℝ) (c₁ : ℝ) j * (η + D_K) +
          2 * dynChi (A : ℝ) L (c₀ : ℝ) (c₁ : ℝ) j * D_K
        + (S.ηstep : ℝ) ≤ η ∧
      η + 2 * dynChi (A : ℝ) L (c₀ : ℝ) (c₁ : ℝ) j * D_K ≤ (S.r₀ : ℝ)) :
    ∀ j : ℕ, ∀ t ∈ Set.Icc (2 * π * (j : ℝ) + 5 * π / 6)
        (2 * π * (j : ℝ) + 7 * π / 6), ∀ i,
      |sol.z t i - orbitPoint Mch E w (j + 1) i| ≤
        dynKappa (A : ℝ) L (c₀ : ℝ) (c₁ : ℝ) j * (η + D_K) +
          (S.ηstep : ℝ) + 2 * dynChi (A : ℝ) L (c₀ : ℝ) (c₁ : ℝ) j * D_K := by
  intro j t ht i
  let AR : ℝ := (A : ℝ)
  let c0R : ℝ := (c₀ : ℝ)
  let c1R : ℝ := (c₁ : ℝ)
  let lam : ℝ := c0R * (1 / 2) ^ L - c1R
  let a : ℝ := 2 * π * (j : ℝ)
  let m : ℝ := 2 * π * (j : ℝ) + π
  let b : ℝ := 2 * π * (j : ℝ) + 2 * π
  let xj : Fin d → ℝ := orbitPoint Mch E w j
  let xnext : Fin d → ℝ := orbitPoint Mch E w (j + 1)
  let leak : ℝ → ℝ := fun t => AR * Real.exp (-(lam * t))
  let I1 : ℝ := ∫ t in a..m, leak t
  let I2 : ℝ := ∫ t in m..b, leak t
  let H1 : ℝ := 2 * D_K * I1
  let H2 : ℝ := 2 * D_K * I2
  have hπ : 0 < π := Real.pi_pos
  have hAℝ : 0 < AR := by dsimp [AR]; exact_mod_cast hA
  have hA_nonneg : 0 ≤ AR := hAℝ.le
  have hc0ℝ : 0 < c0R := by dsimp [c0R]; exact_mod_cast hc₀
  have hc1ℝ : 0 < c1R := by dsimp [c1R]; exact_mod_cast hc₁
  have hc0_nonneg : 0 ≤ c0R := hc0ℝ.le
  have hc1_nonneg : 0 ≤ c1R := hc1ℝ.le
  have hlamR : 0 < lam := by simpa [lam, c0R, c1R] using hlam
  have ha0 : (0 : ℝ) ≤ a :=
    mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Nat.cast_nonneg j)
  have hamb : a ≤ m := by dsimp [a, m]; linarith
  have hmb : m ≤ b := by dsimp [m, b]; linarith [hπ]
  have hab : a ≤ b := le_trans hamb hmb
  have hb_eq : b = 2 * π * ((j : ℝ) + 1) := by dsimp [b]; ring
  have ha_eq : a = 2 * π * j := rfl
  have hm_eq : m = 2 * π * j + π := rfl
  have ht_low : a + 5 * π / 6 ≤ t := by simpa [a] using ht.1
  have ht_cycle_upper : t ≤ b := by
    have : t ≤ a + 7 * π / 6 := by simpa [a] using ht.2
    dsimp [a, b] at this ⊢
    linarith [hπ, this]
  have hcycle_m : m ∈ Set.Icc (2 * π * j) (2 * π * (j + 1)) := by
    constructor
    · simpa [a, m] using hamb
    · simpa [← hb_eq] using hmb
  have hxnext_box : ∀ k, |xnext k - xj k| ≤ D_K := (hbox j m hcycle_m).1
  have hz_cont : ∀ k, Continuous fun t => sol.z t k := fun k => sol.cont_z k
  have hu_cont : ∀ k, Continuous fun t => sol.u t k := fun k => sol.cont_u k
  have hEval_cont : ∀ k, Continuous fun t => S.evalF (sol.u t) k := fun k => by
    have hsolu : Continuous fun t => sol.u t := continuous_pi fun l => hu_cont l
    unfold RobustRealExtension.evalF
    convert
      (MvPolynomial.continuous_eval (p := MvPolynomial.map (algebraMap ℚ ℝ) (S.F k))).comp hsolu
      using 1
    ext t
    exact MvPolynomial.eval₂_eq_eval_map (algebraMap ℚ ℝ) (sol.u t) (S.F k)
  have hD_nonneg : 0 ≤ D_K := hD.le
  have hκ_nonneg : 0 ≤ dynKappa AR L c0R c1R j := by
    unfold dynKappa
    exact (Real.exp_pos _).le
  have hχ_nonneg : 0 ≤ dynChi AR L c0R c1R j := by
    unfold dynChi
    positivity
  have hχD_nonneg : 0 ≤ 2 * dynChi AR L c0R c1R j * D_K := by positivity
  have hleak_cont : Continuous leak := by
    dsimp [leak]
    fun_prop
  have hleak_nonneg : ∀ t, 0 ≤ leak t := by
    intro t
    dsimp [leak]
    positivity
  have hI1_nonneg : 0 ≤ I1 := by
    dsimp [I1]
    exact intervalIntegral.integral_nonneg hamb (fun t _ => hleak_nonneg t)
  have hI2_nonneg : 0 ≤ I2 := by
    dsimp [I2]
    exact intervalIntegral.integral_nonneg hmb (fun t _ => hleak_nonneg t)
  have hH1_nonneg : 0 ≤ H1 := by dsimp [H1]; positivity
  have hH2_nonneg : 0 ≤ H2 := by dsimp [H2]; positivity
  have hI_sum_le : I1 + I2 ≤ dynChi AR L c0R c1R j := by
    have hadd : I1 + I2 = ∫ t in a..b, leak t := by
      dsimp [I1, I2]
      exact intervalIntegral.integral_add_adjacent_intervals
        (hleak_cont.intervalIntegrable a m) (hleak_cont.intervalIntegrable m b)
    have hcyc : (∫ t in a..b, leak t) ≤ dynChi AR L c0R c1R j := by
      have h := dyn_exp_decay_cycle_integral_le AR lam a b hA_nonneg hlamR hab
      simpa [leak, dynChi, lam, a, AR, c0R, c1R, mul_assoc] using h
    linarith
  have hH_sum_le : H1 + H2 ≤ 2 * dynChi AR L c0R c1R j * D_K := by
    dsimp [H1, H2]
    nlinarith [hI_sum_le, hD_nonneg]
  have hsample := dyn_all_time_tracking Mch d E S A hA L c₀ c₁ hc₀ hc₁
    hlam w sol D_K hD hbox η hη hcasc j
  have hold_u_first :
      ∀ s ∈ Set.Icc a m, ∀ k, |sol.u s k - sol.u a k| ≤ H1 := by
    intro s hs k
    have has : a ≤ s := hs.1
    have hsm : s ≤ m := hs.2
    let g : ℝ → ℝ := fun r =>
      AR * (Real.exp (c1R * r) * bGateU L (c0R * r) r) * (sol.z r k - sol.u r k)
    have hg_cont : Continuous g := by
      dsimp [g]
      have hzu : Continuous fun r => sol.z r k - sol.u r k := (hz_cont k).sub (hu_cont k)
      exact (continuous_const.mul (dyn_phiU_continuous_local L c0R c1R)).mul hzu
    have hderiv : ∀ r ∈ Set.Icc a s, HasDerivAt (fun τ => sol.u τ k) (g r) r := by
      intro r hr
      have hr0 : 0 ≤ r := le_trans ha0 hr.1
      have hα := sol.alpha_eq r hr0
      have hμ := sol.mu_eq r hr0
      have hode := sol.ode_u r hr0 k
      dsimp [g, AR, c0R, c1R]
      convert hode using 1 <;> simp [hα, hμ, mul_assoc]
    have hhold := hold_bound_integral (fun τ => sol.u τ k) g a s has hg_cont hderiv
    have hint_le : (∫ r in a..s, |g r|) ≤ ∫ r in a..s, 2 * D_K * leak r := by
      apply intervalIntegral.integral_mono_on has
      · exact hg_cont.abs.intervalIntegrable a s
      · exact (continuous_const.mul hleak_cont).intervalIntegrable a s
      intro r hr
      have hr0 : 0 ≤ r := le_trans ha0 hr.1
      have hr_cycle : r ∈ Set.Icc (2 * π * j) (2 * π * (j + 1)) := by
        simpa [a, ← hb_eq] using
          (⟨hr.1, le_trans hr.2 (le_trans hsm hmb)⟩ : r ∈ Set.Icc a b)
      have hzD := (hbox j r hr_cycle).2.1 k
      have huD := (hbox j r hr_cycle).2.2.1 k
      have hzu : |sol.z r k - sol.u r k| ≤ 2 * D_K := by
        calc
          |sol.z r k - sol.u r k|
              = |(sol.z r k - xj k) - (sol.u r k - xj k)| := by ring_nf
          _ ≤ |sol.z r k - xj k| + |sol.u r k - xj k| := by
            simpa [abs_sub_comm] using abs_sub_le (sol.z r k) (xj k) (sol.u r k)
          _ ≤ D_K + D_K := add_le_add hzD huD
          _ = 2 * D_K := by ring
      have hgate : bGateU L (c0R * r) r ≤ Real.exp (-(c0R * r * (1 / 2) ^ L)) := by
        have hsin : 0 ≤ Real.sin r := by
          apply sin_window_nonneg j
          · simpa [a] using hr_cycle.1
          · have : r ≤ 2 * π * j + π := by rw [← hm_eq]; exact le_trans hr.2 hsm
            simpa using this
        exact bGateU_le_offphase L (mul_nonneg hc0_nonneg hr0) hsin
      have hprof_le : AR * (Real.exp (c1R * r) * bGateU L (c0R * r) r) ≤ leak r := by
        dsimp [leak]
        have hexp_nonneg : 0 ≤ Real.exp (c1R * r) := (Real.exp_pos _).le
        have hgate_mul :
            Real.exp (c1R * r) * bGateU L (c0R * r) r
              ≤ Real.exp (c1R * r) * Real.exp (-(c0R * r * (1 / 2) ^ L)) :=
          mul_le_mul_of_nonneg_left hgate hexp_nonneg
        have hmul := mul_le_mul_of_nonneg_left hgate_mul hA_nonneg
        calc
          AR * (Real.exp (c1R * r) * bGateU L (c0R * r) r)
              ≤ AR * (Real.exp (c1R * r) * Real.exp (-(c0R * r * (1 / 2) ^ L))) := hmul
          _ = AR * Real.exp (-(lam * r)) := by
                congr 1
                rw [← Real.exp_add]
                congr 1
                dsimp [lam]
                ring
      have hprof_nonneg : 0 ≤ AR * (Real.exp (c1R * r) * bGateU L (c0R * r) r) := by
        exact mul_nonneg hA_nonneg
          (mul_nonneg (Real.exp_pos _).le (bGateU_pos L (c0R * r) r).le)
      calc
        |g r| = AR * (Real.exp (c1R * r) * bGateU L (c0R * r) r) *
            |sol.z r k - sol.u r k| := by
          dsimp [g]
          rw [abs_mul, abs_of_nonneg hprof_nonneg]
        _ ≤ leak r * (2 * D_K) := mul_le_mul hprof_le hzu (abs_nonneg _) (hleak_nonneg r)
        _ = 2 * D_K * leak r := by ring
    have hIt_le : (∫ r in a..s, leak r) ≤ I1 := by
      have htail_nonneg : 0 ≤ ∫ r in s..m, leak r :=
        intervalIntegral.integral_nonneg hsm (fun r _ => hleak_nonneg r)
      have hadd : (∫ r in a..s, leak r) + (∫ r in s..m, leak r) = I1 := by
        dsimp [I1]
        exact intervalIntegral.integral_add_adjacent_intervals
          (hleak_cont.intervalIntegrable a s) (hleak_cont.intervalIntegrable s m)
      linarith
    calc
      |sol.u s k - sol.u a k| ≤ ∫ r in a..s, |g r| := hhold
      _ ≤ ∫ r in a..s, 2 * D_K * leak r := hint_le
      _ = 2 * D_K * (∫ r in a..s, leak r) := by
            rw [intervalIntegral.integral_const_mul]
      _ ≤ H1 := by
            dsimp [H1]
            exact mul_le_mul_of_nonneg_left hIt_le (by positivity)
  have hu_first_near : ∀ s ∈ Set.Icc a m, ∀ k, |sol.u s k - xj k| ≤ η + H1 := by
    intro s hs k
    have hstart := (hsample k).2
    rw [← ha_eq] at hstart
    have hhold := hold_u_first s hs k
    calc
      |sol.u s k - xj k|
          = |(sol.u s k - sol.u a k) + (sol.u a k - xj k)| := by ring_nf
      _ ≤ |sol.u s k - sol.u a k| + |sol.u a k - xj k| := abs_add_le _ _
      _ ≤ H1 + η := add_le_add hhold hstart
      _ = η + H1 := by ring
  have hH1_le : H1 ≤ 2 * dynChi AR L c0R c1R j * D_K := by
    nlinarith [hH_sum_le, hH2_nonneg]
  have hH2_le : H2 ≤ 2 * dynChi AR L c0R c1R j * D_K := by
    nlinarith [hH_sum_le, hH1_nonneg]
  have hsnap_first : ∀ s ∈ Set.Icc a m, ∀ k, |S.evalF (sol.u s) k - xnext k| ≤ (S.ηstep : ℝ) := by
    intro s hs k
    have hnear : ∀ l, |sol.u s l - E.enc (Mch.step^[j] (Mch.init w)) l| ≤ (S.r₀ : ℝ) := by
      intro l
      exact le_trans (hu_first_near s hs l) (by nlinarith [(hcasc j).2, hH1_le])
    simpa [RobustRealExtension.evalF, orbitPoint, xnext, Function.iterate_succ_apply'] using
      S.snap (Mch.step^[j] (Mch.init w)) (sol.u s) hnear k
  have target_to (s : ℝ) (hslo : a + 5 * π / 6 ≤ s) (hsm : s ≤ m) :
      |sol.z s i - xnext i| ≤ dynKappa AR L c0R c1R j * (η + D_K) + (S.ηstep : ℝ) := by
    have has : a ≤ s := by linarith
    let φz : ℝ → ℝ := fun r => Real.exp (c1R * r) * bGateZ L (c0R * r) r
    have hδ : ∀ r ∈ Set.Icc a s, |S.evalF (sol.u r) i - xnext i| ≤ (S.ηstep : ℝ) := by
      intro r hr
      exact hsnap_first r ⟨hr.1, le_trans hr.2 hsm⟩ i
    have hderiv : ∀ r ∈ Set.Icc a s,
        HasDerivAt (fun τ => sol.z τ i) (AR * φz r * (S.evalF (sol.u r) i - sol.z r i)) r := by
      intro r hr
      have hr0 : 0 ≤ r := le_trans ha0 hr.1
      have hα := sol.alpha_eq r hr0
      have hμ := sol.mu_eq r hr0
      have hode := sol.ode_z r hr0 i
      dsimp [φz, AR, c0R, c1R]
      convert hode using 1 <;> simp [hα, hμ, mul_assoc]
    have htarget := targeting_bound AR hAℝ φz
      (fun r => S.evalF (sol.u r) i) (fun r => sol.z r i) a s has
      (dyn_phiZ_continuous_local L c0R c1R)
      (fun r _ => by
        dsimp [φz]
        exact mul_nonneg (Real.exp_pos _).le (bGateZ_pos L (c0R * r) r).le)
      (hEval_cont i) (xnext i) (S.ηstep : ℝ) hδ hderiv
    have hInt : AR * Real.exp (c1R * (2 * π * j))
          * Real.exp (-(c0R * 2 * π * (j + 1) * (1 / 4) ^ L)) * (2 * π / 3)
        ≤ AR * ∫ r in a..s, φz r := by
      simpa [φz, a, AR, c0R, c1R] using
        dyn_active_integral_lower_z_to AR L c0R c1R j hA_nonneg hc0_nonneg hc1_nonneg
          (by simpa [a] using hslo) (by simpa [m] using hsm)
    have hcoef :
        Real.exp (-(AR * ∫ r in a..s, φz r)) ≤ dynKappa AR L c0R c1R j := by
      unfold dynKappa
      have hInt' :
          AR * Real.exp (c1R * 2 * π * j)
              * Real.exp (-(c0R * 2 * π * (j + 1) * (1 / 4) ^ L)) * (2 * π / 3)
            ≤ AR * ∫ r in a..s, φz r := by
        simpa [mul_assoc] using hInt
      exact Real.exp_le_exp.mpr (neg_le_neg hInt')
    have hstartz := (hsample i).1
    rw [← ha_eq] at hstartz
    have hxgap := hxnext_box i
    have hza : |sol.z a i - xnext i| ≤ η + D_K := by
      calc
        |sol.z a i - xnext i|
            = |(sol.z a i - xj i) - (xnext i - xj i)| := by ring_nf
        _ ≤ |sol.z a i - xj i| + |xnext i - xj i| := by
          simpa [abs_sub_comm] using abs_sub_le (sol.z a i) (xj i) (xnext i)
        _ ≤ η + D_K := add_le_add hstartz hxgap
    have hmul :
        Real.exp (-(AR * ∫ r in a..s, φz r)) * |sol.z a i - xnext i|
          ≤ dynKappa AR L c0R c1R j * (η + D_K) := by
      exact mul_le_mul hcoef hza (abs_nonneg _) hκ_nonneg
    exact le_trans htarget (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hmul (S.ηstep : ℝ))
  by_cases htm : t ≤ m
  · have htar := target_to t ht_low htm
    exact le_trans htar (by nlinarith [hχD_nonneg])
  · have hmt : m ≤ t := le_of_not_ge htm
    have hm_low : a + 5 * π / 6 ≤ m := by dsimp [a, m]; linarith
    have hz_m := target_to m hm_low le_rfl
    have hold_z_tail : |sol.z t i - sol.z m i| ≤ H2 := by
      let g : ℝ → ℝ := fun r =>
        AR * (Real.exp (c1R * r) * bGateZ L (c0R * r) r) *
          (S.evalF (sol.u r) i - sol.z r i)
      have hg_cont : Continuous g := by
        dsimp [g]
        have hFz : Continuous fun r => S.evalF (sol.u r) i - sol.z r i :=
          (hEval_cont i).sub (hz_cont i)
        exact (continuous_const.mul (dyn_phiZ_continuous_local L c0R c1R)).mul hFz
      have hderiv : ∀ r ∈ Set.Icc m t, HasDerivAt (fun τ => sol.z τ i) (g r) r := by
        intro r hr
        have hr0 : 0 ≤ r := le_trans (le_trans ha0 hamb) hr.1
        have hα := sol.alpha_eq r hr0
        have hμ := sol.mu_eq r hr0
        have hode := sol.ode_z r hr0 i
        dsimp [g, AR, c0R, c1R]
        convert hode using 1 <;> simp [hα, hμ, mul_assoc]
      have hhold := hold_bound_integral (fun τ => sol.z τ i) g m t hmt hg_cont hderiv
      have hint_le : (∫ r in m..t, |g r|) ≤ ∫ r in m..t, 2 * D_K * leak r := by
        apply intervalIntegral.integral_mono_on hmt
        · exact hg_cont.abs.intervalIntegrable m t
        · exact (continuous_const.mul hleak_cont).intervalIntegrable m t
        intro r hr
        have hr0 : 0 ≤ r := le_trans (le_trans ha0 hamb) hr.1
        have hr_cycle : r ∈ Set.Icc (2 * π * j) (2 * π * (j + 1)) := by
          simpa [a, ← hb_eq] using
            (⟨le_trans hamb hr.1, le_trans hr.2 ht_cycle_upper⟩ : r ∈ Set.Icc a b)
        have hFD := (hbox j r hr_cycle).2.2.2 i
        have hzD := (hbox j r hr_cycle).2.1 i
        have hFz : |S.evalF (sol.u r) i - sol.z r i| ≤ 2 * D_K := by
          calc
            |S.evalF (sol.u r) i - sol.z r i|
                = |(S.evalF (sol.u r) i - xj i) - (sol.z r i - xj i)| := by ring_nf
            _ ≤ |S.evalF (sol.u r) i - xj i| + |sol.z r i - xj i| := by
              simpa [abs_sub_comm] using abs_sub_le (S.evalF (sol.u r) i) (xj i) (sol.z r i)
            _ ≤ D_K + D_K := add_le_add hFD hzD
            _ = 2 * D_K := by ring
        have hgate : bGateZ L (c0R * r) r ≤ Real.exp (-(c0R * r * (1 / 2) ^ L)) := by
          have hsin : Real.sin r ≤ 0 := by
            apply sin_window_nonpos j
            · have : 2 * π * j + π ≤ r := by rw [← hm_eq]; exact hr.1
              simpa using this
            · simpa [← hb_eq] using hr_cycle.2
          exact bGateZ_le_offphase L (mul_nonneg hc0_nonneg hr0) hsin
        have hprof_le : AR * (Real.exp (c1R * r) * bGateZ L (c0R * r) r) ≤ leak r := by
          dsimp [leak]
          have hexp_nonneg : 0 ≤ Real.exp (c1R * r) := (Real.exp_pos _).le
          have hgate_mul :
              Real.exp (c1R * r) * bGateZ L (c0R * r) r
                ≤ Real.exp (c1R * r) * Real.exp (-(c0R * r * (1 / 2) ^ L)) :=
            mul_le_mul_of_nonneg_left hgate hexp_nonneg
          have hmul := mul_le_mul_of_nonneg_left hgate_mul hA_nonneg
          calc
            AR * (Real.exp (c1R * r) * bGateZ L (c0R * r) r)
                ≤ AR * (Real.exp (c1R * r) * Real.exp (-(c0R * r * (1 / 2) ^ L))) := hmul
            _ = AR * Real.exp (-(lam * r)) := by
                  congr 1
                  rw [← Real.exp_add]
                  congr 1
                  dsimp [lam]
                  ring
        have hprof_nonneg : 0 ≤ AR * (Real.exp (c1R * r) * bGateZ L (c0R * r) r) := by
          exact mul_nonneg hA_nonneg
            (mul_nonneg (Real.exp_pos _).le (bGateZ_pos L (c0R * r) r).le)
        calc
          |g r| = AR * (Real.exp (c1R * r) * bGateZ L (c0R * r) r) *
              |S.evalF (sol.u r) i - sol.z r i| := by
            dsimp [g]
            rw [abs_mul, abs_of_nonneg hprof_nonneg]
          _ ≤ leak r * (2 * D_K) := mul_le_mul hprof_le hFz (abs_nonneg _) (hleak_nonneg r)
          _ = 2 * D_K * leak r := by ring
      have hIt_le : (∫ r in m..t, leak r) ≤ I2 := by
        have htail_nonneg : 0 ≤ ∫ r in t..b, leak r :=
          intervalIntegral.integral_nonneg ht_cycle_upper (fun r _ => hleak_nonneg r)
        have hadd : (∫ r in m..t, leak r) + (∫ r in t..b, leak r) = I2 := by
          dsimp [I2]
          exact intervalIntegral.integral_add_adjacent_intervals
            (hleak_cont.intervalIntegrable m t) (hleak_cont.intervalIntegrable t b)
        linarith
      calc
        |sol.z t i - sol.z m i| ≤ ∫ r in m..t, |g r| := hhold
        _ ≤ ∫ r in m..t, 2 * D_K * leak r := hint_le
        _ = 2 * D_K * (∫ r in m..t, leak r) := by
              rw [intervalIntegral.integral_const_mul]
        _ ≤ H2 := by
              dsimp [H2]
              exact mul_le_mul_of_nonneg_left hIt_le (by positivity)
    calc
      |sol.z t i - xnext i|
          = |(sol.z t i - sol.z m i) + (sol.z m i - xnext i)| := by ring_nf
      _ ≤ |sol.z t i - sol.z m i| + |sol.z m i - xnext i| := abs_add_le _ _
      _ ≤ H2 + (dynKappa AR L c0R c1R j * (η + D_K) + (S.ηstep : ℝ)) :=
            add_le_add hold_z_tail hz_m
      _ ≤ dynKappa AR L c0R c1R j * (η + D_K) + (S.ηstep : ℝ)
          + 2 * dynChi AR L c0R c1R j * D_K := by
            nlinarith [hH2_le]

/-- Dynamic analog of `assembled_euclidean_simulation`.

The supplier exposes only the dynamic moving-box hypothesis consumed by
`dyn_all_time_tracking`; post-transition stable-window tracking is
derived internally by `dyn_stable_window_tracking`. -/
theorem dyn_assembled_euclidean_simulation
    {Conf : Type} [Primcodable Conf]
    (Mch : DiscreteMachine Conf) (d : ℕ) (E : LatticeEncoding Mch d)
    (S : RobustRealExtension Mch d E)
    (stateCoord : Fin d) (haltLevels : Finset ℤ)
    (hfin : (Set.range fun c => E.enc c stateCoord).Finite)
    (hlevels : ∀ c : Conf, Mch.halted c = true ↔
      ∃ v ∈ haltLevels, E.enc c stateCoord = (v : ℝ))
    (hmargin : ∀ c : Conf, Mch.halted c = false →
      ∀ v ∈ haltLevels, 1 ≤ |E.enc c stateCoord - (v : ℝ)|)
    (D_K : ℝ) (hD : 0 < D_K)
    (hstepSmall :
      2 * (S.ηstep : ℝ) < min ((S.r₀ : ℝ) / 2) (1 / 4) / 2)
    (hsupply : ∀ (A : ℚ) (L : ℕ) (c₀ c₁ : ℚ) (w : ℕ),
      0 < A → 0 < c₀ → 0 < c₁ →
      (c₀ : ℝ) * (1 / 2) ^ L > (c₁ : ℝ) →
      (c₁ : ℝ) > (c₀ : ℝ) * (1 / 4) ^ L →
      ∃ sol : DynIteratorSol d S.evalF A L c₀ c₁ (orbitPoint Mch E w 0),
        ∀ (j : ℕ) (t : ℝ), t ∈ Set.Icc (2 * π * j) (2 * π * (j + 1)) →
          (∀ i, |orbitPoint Mch E w (j + 1) i - orbitPoint Mch E w j i| ≤ D_K) ∧
          (∀ i, |sol.z t i - orbitPoint Mch E w j i| ≤ D_K) ∧
          (∀ i, |sol.u t i - orbitPoint Mch E w j i| ≤ D_K) ∧
          (∀ i, |S.evalF (sol.u t) i - orbitPoint Mch E w j i| ≤ D_K)) :
    ∃ (I : HaltIndicator Mch d E) (A : ℚ) (L : ℕ) (c₀ c₁ : ℚ)
        (K : ℚ) (R : ℕ),
      0 < A ∧ 0 < c₀ ∧ 0 < c₁ ∧
      (c₀ : ℝ) * (1 / 2) ^ L > (c₁ : ℝ) ∧
      (c₁ : ℝ) > (c₀ : ℝ) * (1 / 4) ^ L ∧
      0 < K ∧
      ∀ w : ℕ,
        ∃ (sol : DynIteratorSol d S.evalF A L c₀ c₁ (orbitPoint Mch E w 0))
          (La : DynLatchSol sol I.evalH (K : ℝ) R),
          (Mch.haltsOn w →
            ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1) ∧
          (¬ Mch.haltsOn w →
            ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4) := by
  classical
  let vals : Finset ℝ := hfin.toFinset
  let maxAbs : ℝ := ∑ v ∈ vals, |v|
  have hmaxAbs_nonneg : 0 ≤ maxAbs := by
    dsimp [maxAbs]
    positivity
  have henc_bound : ∀ c : Conf, |E.enc c stateCoord| ≤ maxAbs := by
    intro c
    have hval : E.enc c stateCoord ∈ vals := by
      rw [Set.Finite.mem_toFinset hfin]
      exact Set.mem_range_self c
    have hterm_nonneg : ∀ v ∈ vals, 0 ≤ |v| := by
      intro v hv
      exact abs_nonneg v
    exact Finset.single_le_sum hterm_nonneg hval
  obtain ⟨Cwidth, hCwidth_gt⟩ : ∃ q : ℚ, maxAbs + D_K < (q : ℝ) :=
    exists_rat_gt (maxAbs + D_K)
  have hCwidth_pos : 0 < Cwidth := by
    have hCwidth_posR : (0 : ℝ) < (Cwidth : ℝ) := by
      nlinarith [hmaxAbs_nonneg, hD, hCwidth_gt]
    exact Rat.cast_pos.mp hCwidth_posR
  obtain ⟨I, _hIη, hIρ_low, _hIρ_high, C, hCwidth_le_C, hIW⟩ :=
    haltIndicator_exists Mch d E S Cwidth hCwidth_pos stateCoord haltLevels
      hfin hlevels hmargin (1 / 16) (by norm_num) (by norm_num)
  let η : ℝ := min ((S.r₀ : ℝ) / 2) (1 / 4) / 2
  have hmin_pos : 0 < min ((S.r₀ : ℝ) / 2) (1 / 4) := by
    have hr0R : 0 < (S.r₀ : ℝ) := by exact_mod_cast S.r₀_pos
    apply lt_min
    · linarith
    · norm_num
  have hη_pos : 0 < η := by
    dsimp [η]
    nlinarith [hmin_pos]
  have hη_le_r0_half : η ≤ (S.r₀ : ℝ) / 2 := by
    dsimp [η]
    have hleft := min_le_left ((S.r₀ : ℝ) / 2) (1 / 4)
    nlinarith [hmin_pos, hleft]
  have hη_le_Iρ : η ≤ (I.ρ : ℝ) := by
    dsimp [η]
    nlinarith [hmin_pos, hIρ_low]
  obtain ⟨A, L, c₀, c₁, hA, hc₀, hc₁, hupper, hlower, hcasc⟩ :=
    dyn_param_feasible S.r₀ S.ηstep S.ηstep_pos S.ηstep_lt_r₀
      D_K hD η hstepSmall hη_le_r0_half
  have hlam : 0 < (c₀ : ℝ) * (1 / 2) ^ L - (c₁ : ℝ) := by
    nlinarith [hupper]
  obtain ⟨K, R, hK, hlatch⟩ := dyn_halt_latch_eventual_readout Mch d E S I
  refine ⟨I, A, L, c₀, c₁, K, R, hA, hc₀, hc₁, hupper, hlower, hK, ?_⟩
  intro w
  obtain ⟨sol, hbox⟩ :=
    hsupply A L c₀ c₁ w hA hc₀ hc₁ hupper hlower
  have hsampleη :=
    dyn_all_time_tracking Mch d E S A hA L c₀ c₁ hc₀ hc₁
      hlam w sol D_K hD hbox η hη_pos hcasc
  have hsampleI : ∀ j : ℕ, ∀ i,
      |sol.z (2 * π * (j : ℝ)) i - orbitPoint Mch E w j i| ≤ (I.ρ : ℝ) ∧
      |sol.u (2 * π * (j : ℝ)) i - orbitPoint Mch E w j i| ≤ (I.ρ : ℝ) := by
    intro j i
    have h := hsampleη j i
    exact ⟨le_trans h.1 hη_le_Iρ, le_trans h.2 hη_le_Iρ⟩
  have hstable_radius : ∀ j : ℕ,
      dynKappa (A : ℝ) L (c₀ : ℝ) (c₁ : ℝ) j * (η + D_K)
          + (S.ηstep : ℝ) + 2 * dynChi (A : ℝ) L (c₀ : ℝ) (c₁ : ℝ) j * D_K
        ≤ η := by
    intro j
    have hκ_nonneg : 0 ≤ dynKappa (A : ℝ) L (c₀ : ℝ) (c₁ : ℝ) j := by
      unfold dynKappa
      exact (Real.exp_pos _).le
    have hηD_nonneg : 0 ≤ η + D_K := by nlinarith [hη_pos, hD]
    nlinarith [(hcasc j).1, hκ_nonneg, hηD_nonneg]
  have hstableI : ∀ j : ℕ,
      ∀ t ∈ Set.Icc (2 * π * (j : ℝ) + 5 * π / 6)
        (2 * π * (j : ℝ) + 7 * π / 6),
        ∀ i, |sol.z t i - orbitPoint Mch E w (j + 1) i| ≤ (I.ρ : ℝ) := by
    intro j t ht i
    have hst :=
      dyn_stable_window_tracking Mch d E S A hA L c₀ c₁ hc₀ hc₁
        hlam w sol D_K hD hbox η hη_pos hcasc j t ht i
    exact le_trans hst (le_trans (hstable_radius j) hη_le_Iρ)
  have hzW : ∀ t : ℝ, 0 ≤ t → sol.z t ∈ I.W := by
    intro t ht
    obtain ⟨j, htcycle⟩ := dyn_cycle_cover ht
    have hzD := (hbox j t htcycle).2.1 stateCoord
    have horbit := henc_bound (Mch.step^[j] (Mch.init w))
    have hz_abs : |sol.z t stateCoord| ≤ maxAbs + D_K := by
      calc
        |sol.z t stateCoord| =
            |(sol.z t stateCoord - orbitPoint Mch E w j stateCoord) +
              orbitPoint Mch E w j stateCoord| := by
              congr 1
              ring
        _ ≤ |sol.z t stateCoord - orbitPoint Mch E w j stateCoord| +
            |orbitPoint Mch E w j stateCoord| := abs_add_le _ _
        _ ≤ D_K + maxAbs := by
            gcongr
            simpa [orbitPoint] using horbit
        _ = maxAbs + D_K := by ring
    rw [hIW]
    have hCwidth_le_Cℝ : (Cwidth : ℝ) ≤ (C : ℝ) := by exact_mod_cast hCwidth_le_C
    change |sol.z t stateCoord| ≤ (C : ℝ)
    linarith
  have hHcont : Continuous fun t => I.evalH (sol.z t) :=
    I.dyn_evalH_continuous_along sol
  obtain ⟨La⟩ := dyn_latch_solution_exists sol I.evalH hHcont (K : ℝ) R
  exact ⟨sol, La, hlatch A hA L c₀ c₁ w sol hsampleI hzW hstableI La⟩


end Ripple.BoundedUniversality.BGP
