import Ripple.BoundedUniversality.BGP.ContractMain
import Ripple.BoundedUniversality.BGP.DynamicAssembly
import Ripple.BoundedUniversality.BGP.MainAssembled

/-!
Ripple.BoundedUniversality.BGP.ContractField
------------------------
Contract dynamic-gate polynomial field package.

This file is intentionally additive.  It mirrors the dynamic assembled layout
`(s, c, μ, α, bZ, bU, z, u, a)` but keeps the contract step target polynomial
as explicit data.  The final machine assembly supplies the selector polynomial
family and the evaluation identities.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open Ripple.BoundedUniversality.Core
open scoped BigOperators
open Real

abbrev contractTailDim (d : ℕ) : ℕ := d + (d + 1)
abbrev contractGateTailDim (d : ℕ) : ℕ := 2 + contractTailDim d
abbrev contractDim (d : ℕ) : ℕ := 4 + contractGateTailDim d

noncomputable def contractS (d : ℕ) : Fin (contractDim d) :=
  Fin.castAdd (contractGateTailDim d) (0 : Fin 4)

noncomputable def contractC (d : ℕ) : Fin (contractDim d) :=
  Fin.castAdd (contractGateTailDim d) (1 : Fin 4)

noncomputable def contractMu (d : ℕ) : Fin (contractDim d) :=
  Fin.castAdd (contractGateTailDim d) (2 : Fin 4)

noncomputable def contractAlpha (d : ℕ) : Fin (contractDim d) :=
  Fin.castAdd (contractGateTailDim d) (3 : Fin 4)

noncomputable def contractGateZ (d : ℕ) : Fin (contractDim d) :=
  Fin.natAdd 4 (Fin.castAdd (contractTailDim d) (0 : Fin 2))

noncomputable def contractGateU (d : ℕ) : Fin (contractDim d) :=
  Fin.natAdd 4 (Fin.castAdd (contractTailDim d) (1 : Fin 2))

noncomputable def contractTailZ {d : ℕ} (i : Fin d) : Fin (contractTailDim d) :=
  Fin.castAdd (d + 1) i

noncomputable def contractTailU {d : ℕ} (i : Fin d) : Fin (contractTailDim d) :=
  Fin.natAdd d (Fin.castAdd 1 i)

noncomputable def contractTailA (d : ℕ) : Fin (contractTailDim d) :=
  Fin.natAdd d (Fin.natAdd d (0 : Fin 1))

noncomputable def contractZ {d : ℕ} (i : Fin d) : Fin (contractDim d) :=
  Fin.natAdd 4 (Fin.natAdd 2 (contractTailZ i))

noncomputable def contractU {d : ℕ} (i : Fin d) : Fin (contractDim d) :=
  Fin.natAdd 4 (Fin.natAdd 2 (contractTailU i))

noncomputable def contractA (d : ℕ) : Fin (contractDim d) :=
  Fin.natAdd 4 (Fin.natAdd 2 (contractTailA d))

noncomputable def contractRenameZ {d : ℕ}
    (p : MvPolynomial (Fin d) ℚ) : MvPolynomial (Fin (contractDim d)) ℚ :=
  MvPolynomial.rename (contractZ (d := d)) p

noncomputable def contractRP (d L : ℕ) : MvPolynomial (Fin (contractDim d)) ℚ :=
  (MvPolynomial.C (1 / 2 : ℚ) *
    ((1 : MvPolynomial (Fin (contractDim d)) ℚ) - MvPolynomial.X (contractS d))) ^ L

noncomputable def contractQP (d L : ℕ) : MvPolynomial (Fin (contractDim d)) ℚ :=
  (MvPolynomial.C (1 / 2 : ℚ) *
    ((1 : MvPolynomial (Fin (contractDim d)) ℚ) + MvPolynomial.X (contractS d))) ^ L

noncomputable def contractRPderiv (d L : ℕ) : MvPolynomial (Fin (contractDim d)) ℚ :=
  MvPolynomial.C (L : ℚ) *
    (MvPolynomial.C (1 / 2 : ℚ) *
      ((1 : MvPolynomial (Fin (contractDim d)) ℚ) - MvPolynomial.X (contractS d))) ^ (L - 1) *
    (-(MvPolynomial.C (1 / 2 : ℚ)) * MvPolynomial.X (contractC d))

noncomputable def contractQPderiv (d L : ℕ) : MvPolynomial (Fin (contractDim d)) ℚ :=
  MvPolynomial.C (L : ℚ) *
    (MvPolynomial.C (1 / 2 : ℚ) *
      ((1 : MvPolynomial (Fin (contractDim d)) ℚ) + MvPolynomial.X (contractS d))) ^ (L - 1) *
    (MvPolynomial.C (1 / 2 : ℚ) * MvPolynomial.X (contractC d))

/--
Contract assembled rational polynomial field.  The `FP` target family is
already over the full extended state, so it may mention `μ`, gate coordinates,
or any other contract coordinate.
-/
def contractAssembledField (d : ℕ)
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) :
    Fin (contractDim d) → MvPolynomial (Fin (contractDim d)) ℚ :=
  Fin.append
    (fun k : Fin 4 =>
      if k = 0 then MvPolynomial.X (contractC d) else
      if k = 1 then -MvPolynomial.X (contractS d) else
      if k = 2 then MvPolynomial.C cμ else
        MvPolynomial.C cα * MvPolynomial.X (contractAlpha d))
    (Fin.append
      (fun k : Fin 2 =>
        if k = 0 then
          -((MvPolynomial.C cμ * contractRP d L +
              MvPolynomial.X (contractMu d) * contractRPderiv d L) *
            MvPolynomial.X (contractGateZ d))
        else
          -((MvPolynomial.C cμ * contractQP d L +
              MvPolynomial.X (contractMu d) * contractQPderiv d L) *
            MvPolynomial.X (contractGateU d)))
      (Fin.append
        (fun i : Fin d =>
          MvPolynomial.C A * MvPolynomial.X (contractAlpha d) *
            MvPolynomial.X (contractGateZ d) *
            (FP i - MvPolynomial.X (contractZ i)))
        (Fin.append
          (fun i : Fin d =>
            MvPolynomial.C A * MvPolynomial.X (contractAlpha d) *
              MvPolynomial.X (contractGateU d) *
              (MvPolynomial.X (contractZ i) - MvPolynomial.X (contractU i)))
          (fun _ : Fin 1 =>
            MvPolynomial.C K *
              ((MvPolynomial.C (1 / 2 : ℚ) *
                  ((1 : MvPolynomial (Fin (contractDim d)) ℚ) -
                    MvPolynomial.X (contractC d))) ^ R) *
              (contractRenameZ HP - MvPolynomial.X (contractA d))))))

private lemma contractAssembledField_s (d : ℕ)
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) :
    contractAssembledField d FP HP A K cμ cα L R (contractS d) =
      MvPolynomial.X (contractC d) := by
  simp [contractAssembledField, contractS]

private lemma contractAssembledField_c (d : ℕ)
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) :
    contractAssembledField d FP HP A K cμ cα L R (contractC d) =
      -MvPolynomial.X (contractS d) := by
  simp [contractAssembledField, contractC, contractS]

private lemma contractAssembledField_mu (d : ℕ)
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) :
    contractAssembledField d FP HP A K cμ cα L R (contractMu d) =
      MvPolynomial.C cμ := by
  simp [contractAssembledField, contractMu, contractS]

private lemma contractAssembledField_alpha (d : ℕ)
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) :
    contractAssembledField d FP HP A K cμ cα L R (contractAlpha d) =
      MvPolynomial.C cα * MvPolynomial.X (contractAlpha d) := by
  simp [contractAssembledField, contractAlpha, contractS]

private lemma contractAssembledField_bz (d : ℕ)
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) :
    contractAssembledField d FP HP A K cμ cα L R (contractGateZ d) =
      -((MvPolynomial.C cμ * contractRP d L +
          MvPolynomial.X (contractMu d) * contractRPderiv d L) *
        MvPolynomial.X (contractGateZ d)) := by
  simp [contractAssembledField, contractGateZ]

private lemma contractAssembledField_bu (d : ℕ)
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) :
    contractAssembledField d FP HP A K cμ cα L R (contractGateU d) =
      -((MvPolynomial.C cμ * contractQP d L +
          MvPolynomial.X (contractMu d) * contractQPderiv d L) *
        MvPolynomial.X (contractGateU d)) := by
  simp [contractAssembledField, contractGateU]

private lemma contractAssembledField_z {d : ℕ}
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) (i : Fin d) :
    contractAssembledField d FP HP A K cμ cα L R (contractZ i) =
      MvPolynomial.C A * MvPolynomial.X (contractAlpha d) *
        MvPolynomial.X (contractGateZ d) *
        (FP i - MvPolynomial.X (contractZ i)) := by
  simp [contractAssembledField, contractZ, contractTailZ]

private lemma contractAssembledField_u {d : ℕ}
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) (i : Fin d) :
    contractAssembledField d FP HP A K cμ cα L R (contractU i) =
      MvPolynomial.C A * MvPolynomial.X (contractAlpha d) *
        MvPolynomial.X (contractGateU d) *
        (MvPolynomial.X (contractZ i) - MvPolynomial.X (contractU i)) := by
  simp [contractAssembledField, contractU, contractTailU]

private lemma contractAssembledField_a (d : ℕ)
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ) :
    contractAssembledField d FP HP A K cμ cα L R (contractA d) =
      MvPolynomial.C K *
        ((MvPolynomial.C (1 / 2 : ℚ) *
            ((1 : MvPolynomial (Fin (contractDim d)) ℚ) -
              MvPolynomial.X (contractC d))) ^ R) *
        (contractRenameZ HP - MvPolynomial.X (contractA d)) := by
  simp [contractAssembledField, contractA, contractTailA]

def contractTupleTraj {d : ℕ}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    {flagCoord : Fin d} {I : ContractFlagIndicatorPackage flagCoord}
    {K : ℝ} {R : ℕ}
    (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ) :
    Fin (contractDim d) → ℝ :=
  Fin.append
    (fun k : Fin 4 =>
      if k = 0 then Real.sin t else
      if k = 1 then Real.cos t else
      if k = 2 then sol.μ t else sol.α t)
    (Fin.append
      (fun k : Fin 2 =>
        if k = 0 then bGateZ p.L (sol.μ t) t else bGateU p.L (sol.μ t) t)
      (Fin.append (sol.z t) (Fin.append (sol.u t) (fun _ : Fin 1 => La.a t))))

@[simp] lemma contractTupleTraj_s {d : ℕ}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    {flagCoord : Fin d} {I : ContractFlagIndicatorPackage flagCoord}
    {K : ℝ} {R : ℕ}
    (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ) :
    contractTupleTraj sol La t (contractS d) = Real.sin t := by
  simp [contractTupleTraj, contractS]

@[simp] lemma contractTupleTraj_c {d : ℕ}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    {flagCoord : Fin d} {I : ContractFlagIndicatorPackage flagCoord}
    {K : ℝ} {R : ℕ}
    (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ) :
    contractTupleTraj sol La t (contractC d) = Real.cos t := by
  simp [contractTupleTraj, contractC, contractS]

@[simp] lemma contractTupleTraj_mu {d : ℕ}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    {flagCoord : Fin d} {I : ContractFlagIndicatorPackage flagCoord}
    {K : ℝ} {R : ℕ}
    (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ) :
    contractTupleTraj sol La t (contractMu d) = sol.μ t := by
  simp [contractTupleTraj, contractMu, contractS]

@[simp] lemma contractTupleTraj_alpha {d : ℕ}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    {flagCoord : Fin d} {I : ContractFlagIndicatorPackage flagCoord}
    {K : ℝ} {R : ℕ}
    (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ) :
    contractTupleTraj sol La t (contractAlpha d) = sol.α t := by
  simp [contractTupleTraj, contractAlpha, contractS]

@[simp] lemma contractTupleTraj_bz {d : ℕ}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    {flagCoord : Fin d} {I : ContractFlagIndicatorPackage flagCoord}
    {K : ℝ} {R : ℕ}
    (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ) :
    contractTupleTraj sol La t (contractGateZ d) = bGateZ p.L (sol.μ t) t := by
  simp [contractTupleTraj, contractGateZ]

@[simp] lemma contractTupleTraj_bu {d : ℕ}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    {flagCoord : Fin d} {I : ContractFlagIndicatorPackage flagCoord}
    {K : ℝ} {R : ℕ}
    (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ) :
    contractTupleTraj sol La t (contractGateU d) = bGateU p.L (sol.μ t) t := by
  simp [contractTupleTraj, contractGateU]

@[simp] lemma contractTupleTraj_z {d : ℕ}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    {flagCoord : Fin d} {I : ContractFlagIndicatorPackage flagCoord}
    {K : ℝ} {R : ℕ}
    (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ) (i : Fin d) :
    contractTupleTraj sol La t (contractZ i) = sol.z t i := by
  simp [contractTupleTraj, contractZ, contractTailZ]

@[simp] lemma contractTupleTraj_u {d : ℕ}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    {flagCoord : Fin d} {I : ContractFlagIndicatorPackage flagCoord}
    {K : ℝ} {R : ℕ}
    (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ) (i : Fin d) :
    contractTupleTraj sol La t (contractU i) = sol.u t i := by
  simp [contractTupleTraj, contractU, contractTailU]

@[simp] lemma contractTupleTraj_a {d : ℕ}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    {flagCoord : Fin d} {I : ContractFlagIndicatorPackage flagCoord}
    {K : ℝ} {R : ℕ}
    (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ) :
    contractTupleTraj sol La t (contractA d) = La.a t := by
  simp [contractTupleTraj, contractA, contractTailA]

private lemma eval_contractRenameZ_tuple {d : ℕ}
    {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    {flagCoord : Fin d} {I : ContractFlagIndicatorPackage flagCoord}
    {K : ℝ} {R : ℕ}
    (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ)
    (q : MvPolynomial (Fin d) ℚ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t)
        (contractRenameZ q) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) q := by
  rw [contractRenameZ, MvPolynomial.eval₂_rename]
  exact MvPolynomial.eval₂_congr
    (f := algebraMap ℚ ℝ) (p := q)
    (g₁ := contractTupleTraj sol La t ∘ contractZ) (g₂ := sol.z t)
    (fun {i} {_c} _hi _hc => contractTupleTraj_z sol La t i)

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

private noncomputable def contractRPulseDeriv (L : ℕ) (t : ℝ) : ℝ :=
  (L : ℝ) * ((1 - Real.sin t) / 2) ^ (L - 1) * (-(Real.cos t / 2))

private noncomputable def contractQPulseDeriv (L : ℕ) (t : ℝ) : ℝ :=
  (L : ℝ) * ((1 + Real.sin t) / 2) ^ (L - 1) * (Real.cos t / 2)

private lemma hasDerivAt_contractRPulse (L : ℕ) (t : ℝ) :
    HasDerivAt (fun τ => rPulse L τ) (contractRPulseDeriv L t) t := by
  unfold rPulse contractRPulseDeriv
  have hbase : HasDerivAt (fun τ : ℝ => (1 - Real.sin τ) / 2) (-(Real.cos t / 2)) t := by
    convert ((hasDerivAt_const (x := t) (c := (1 : ℝ))).sub
      (Real.hasDerivAt_sin t)).div_const 2 using 1 <;> ring
  simpa using hbase.pow L

private lemma hasDerivAt_contractQPulse (L : ℕ) (t : ℝ) :
    HasDerivAt (fun τ => qPulse L τ) (contractQPulseDeriv L t) t := by
  unfold qPulse contractQPulseDeriv
  have hbase : HasDerivAt (fun τ : ℝ => (1 + Real.sin τ) / 2) (Real.cos t / 2) t := by
    convert ((hasDerivAt_const (x := t) (c := (1 : ℝ))).add
      (Real.hasDerivAt_sin t)).div_const 2 using 1 <;> ring
  simpa using hbase.pow L

private lemma hasDerivAt_contract_bGateZ
    {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    {cμ : ℚ} (hcμ : p.cμ = (cμ : ℝ)) (t : ℝ) (ht : t ∈ sched.domain) :
    HasDerivAt (fun τ => bGateZ p.L (sol.μ τ) τ)
      (-( (cμ : ℝ) * rPulse p.L t + sol.μ t * contractRPulseDeriv p.L t) *
        bGateZ p.L (sol.μ t) t) t := by
  unfold bGateZ
  have hμ : HasDerivAt sol.μ (cμ : ℝ) t := by
    simpa [hcμ] using sol.μ_hasDeriv t ht
  have hmul := hμ.mul (hasDerivAt_contractRPulse p.L t)
  have hneg : HasDerivAt (fun τ : ℝ => -(sol.μ τ * rPulse p.L τ))
      (-((cμ : ℝ) * rPulse p.L t + sol.μ t * contractRPulseDeriv p.L t)) t := by
    simpa [neg_add_rev] using hmul.neg
  have h := hneg.exp
  convert h using 1 <;> ring

private lemma hasDerivAt_contract_bGateU
    {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    {cμ : ℚ} (hcμ : p.cμ = (cμ : ℝ)) (t : ℝ) (ht : t ∈ sched.domain) :
    HasDerivAt (fun τ => bGateU p.L (sol.μ τ) τ)
      (-( (cμ : ℝ) * qPulse p.L t + sol.μ t * contractQPulseDeriv p.L t) *
        bGateU p.L (sol.μ t) t) t := by
  unfold bGateU
  have hμ : HasDerivAt sol.μ (cμ : ℝ) t := by
    simpa [hcμ] using sol.μ_hasDeriv t ht
  have hmul := hμ.mul (hasDerivAt_contractQPulse p.L t)
  have hneg : HasDerivAt (fun τ : ℝ => -(sol.μ τ * qPulse p.L τ))
      (-((cμ : ℝ) * qPulse p.L t + sol.μ t * contractQPulseDeriv p.L t)) t := by
    simpa [neg_add_rev] using hmul.neg
  have h := hneg.exp
  convert h using 1 <;> ring

theorem contractTupleTraj_ode_raw
    {d : ℕ}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    {p : DynGateParams} {sched : PhaseSchedule}
    {flagCoord : Fin d} {I : ContractFlagIndicatorPackage flagCoord}
    {K : ℝ} {R : ℕ}
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    {Aq Kq cμq cαq : ℚ} {L : ℕ}
    (hA : p.A = (Aq : ℝ)) (hK : K = (Kq : ℝ))
    (hcμ : p.cμ = (cμq : ℝ)) (hcα : p.cα = (cαq : ℝ))
    (hL : p.L = L)
    (hdomain : ∀ t : ℝ, 0 ≤ t → t ∈ sched.domain)
    (field_eval_identity :
      ∀ (sol : DynContractIteratorSol (Fin d) p sched F)
        (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ), 0 ≤ t →
        ∀ i : Fin d,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t) (FP i) =
            F (sol.μ t) (sol.u t) i)
    (indicator_eval_identity :
      ∀ (sol : DynContractIteratorSol (Fin d) p sched F)
        (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ),
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) HP =
            I.Hval (sol.z t))
    (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched F)
    (La : ContractHaltLatchSol sol I.Hval K R) :
    ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (contractTupleTraj sol La)
        (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
          (contractTupleTraj sol La t)
          (contractAssembledField d FP HP Aq Kq cμq cαq L R i)) t := by
  intro t ht
  have htd : t ∈ sched.domain := hdomain t ht
  let core' : Fin 4 → ℝ := fun k =>
    if k = 0 then Real.cos t else
    if k = 1 then -Real.sin t else
    if k = 2 then (cμq : ℝ) else (cαq : ℝ) * sol.α t
  let gate' : Fin 2 → ℝ := fun k =>
    if k = 0 then
      -(((cμq : ℝ) * rPulse L t + sol.μ t * contractRPulseDeriv L t) *
        bGateZ L (sol.μ t) t)
    else
      -(((cμq : ℝ) * qPulse L t + sol.μ t * contractQPulseDeriv L t) *
        bGateU L (sol.μ t) t)
  let z' : Fin d → ℝ := fun i =>
    (Aq : ℝ) * sol.α t * bGateZ L (sol.μ t) t *
      (F (sol.μ t) (sol.u t) i - sol.z t i)
  let u' : Fin d → ℝ := fun i =>
    (Aq : ℝ) * sol.α t * bGateU L (sol.μ t) t *
      (sol.z t i - sol.u t i)
  let a' : Fin 1 → ℝ := fun _ =>
    (Kq : ℝ) * gPulse R t * (I.Hval (sol.z t) - La.a t)
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
    · convert hasDerivAt_contract_bGateZ sol hcμ t htd using 1
      simp [gate']
      ring_nf
    · convert hasDerivAt_contract_bGateU sol hcμ t htd using 1
      simp [gate']
      ring_nf
  have hz : HasDerivAt (fun τ => sol.z τ) z' t := by
    apply hasDerivAt_pi.mpr
    intro i
    have hz_i := sol.z_hasDeriv t htd i
    convert hz_i using 1
    simp [z', hA, hL, sol.target_eq t htd]
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
  have hraw :
      HasDerivAt (contractTupleTraj sol La)
        (Fin.append core' (Fin.append gate' (Fin.append z' (Fin.append u' a')))) t := by
    subst L
    simpa [core', gate', z', u', a'] using
      hasDerivAt_fin_append hcore
        (hasDerivAt_fin_append hgate
          (hasDerivAt_fin_append hz (hasDerivAt_fin_append hu ha)))
  refine hraw.congr_deriv ?_
  funext j
  refine Fin.addCases (m := 4) (n := contractGateTailDim d) ?_ ?_ j
  · intro k
    fin_cases k
    · change core' 0 =
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t)
          (contractAssembledField d FP HP Aq Kq cμq cαq L R (contractS d))
      simp [core', contractAssembledField_s]
    · change core' 1 =
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t)
          (contractAssembledField d FP HP Aq Kq cμq cαq L R (contractC d))
      simp [core', contractAssembledField_c]
    · change core' 2 =
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t)
          (contractAssembledField d FP HP Aq Kq cμq cαq L R (contractMu d))
      simp [core', contractAssembledField_mu]
    · change core' 3 =
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t)
          (contractAssembledField d FP HP Aq Kq cμq cαq L R (contractAlpha d))
      simp [core', contractAssembledField_alpha]
  · intro tail0
    refine Fin.addCases (m := 2) (n := contractTailDim d) ?_ ?_ tail0
    · intro k
      fin_cases k
      · simp only [Fin.append_left, Fin.append_right]
        change gate' 0 =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t)
            (contractAssembledField d FP HP Aq Kq cμq cαq L R (contractGateZ d))
        subst L
        simp [gate', contractAssembledField_bz, contractRP, contractRPderiv, rPulse,
          contractRPulseDeriv]
        left
        ring_nf
      · simp only [Fin.append_left, Fin.append_right]
        change gate' 1 =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t)
            (contractAssembledField d FP HP Aq Kq cμq cαq L R (contractGateU d))
        subst L
        simp [gate', contractAssembledField_bu, contractQP, contractQPderiv, qPulse,
          contractQPulseDeriv]
        left
        ring_nf
    · intro tail
      refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
      · intro i
        simp only [Fin.append_left, Fin.append_right]
        change z' i =
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t)
            (contractAssembledField d FP HP Aq Kq cμq cαq L R (contractZ i))
        simp [z', contractAssembledField_z, field_eval_identity sol La t ht i, hL]
      · intro tail2
        refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
        · intro i
          simp only [Fin.append_left, Fin.append_right]
          change u' i =
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t)
              (contractAssembledField d FP HP Aq Kq cμq cαq L R (contractU i))
          simp [u', contractAssembledField_u, hL]
        · intro k
          fin_cases k
          simp only [Fin.append_left, Fin.append_right]
          change a' 0 =
            MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t)
              (contractAssembledField d FP HP Aq Kq cμq cαq L R (contractA d))
          simp [a', contractAssembledField_a, gPulse, eval_contractRenameZ_tuple,
            indicator_eval_identity sol La t]
          left
          left
          ring_nf

theorem contractTupleTraj_ode
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    {M : UndecidableMachine Conf}
    {E : StackMachineEncoding d nS M.toDiscreteMachine}
    {S : RobustStepContract M.toDiscreteMachine E}
    {p : DynGateParams} {sched : PhaseSchedule}
    {flagCoord : Fin d} {I : ContractFlagIndicatorPackage flagCoord}
    {K : ℝ} {R : ℕ}
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    {Aq Kq cμq cαq : ℚ} {L : ℕ}
    (hA : p.A = (Aq : ℝ)) (hK : K = (Kq : ℝ))
    (hcμ : p.cμ = (cμq : ℝ)) (hcα : p.cα = (cαq : ℝ))
    (hL : p.L = L)
    (hdomain : ∀ t : ℝ, 0 ≤ t → t ∈ sched.domain)
    (field_eval_identity :
      ∀ (sol : DynContractIteratorSol (Fin d) p sched S.F)
        (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ), 0 ≤ t →
        ∀ i : Fin d,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t) (FP i) =
            S.F (sol.μ t) (sol.u t) i)
    (indicator_eval_identity :
      ∀ (sol : DynContractIteratorSol (Fin d) p sched S.F)
        (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ),
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) HP =
            I.Hval (sol.z t))
    (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F)
    (La : ContractHaltLatchSol sol I.Hval K R) :
    ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (contractTupleTraj sol La)
        (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
          (contractTupleTraj sol La t)
          (contractAssembledField d FP HP Aq Kq cμq cαq L R i)) t :=
  contractTupleTraj_ode_raw FP HP hA hK hcμ hcα hL hdomain
    field_eval_identity indicator_eval_identity w sol La

theorem contractTupleTraj_zero
    {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (sol : DynContractIteratorSol (Fin d) p sched F)
    {flagCoord : Fin d} {I : ContractFlagIndicatorPackage flagCoord}
    {K : ℝ} {R : ℕ}
    (La : ContractHaltLatchSol sol I.Hval K R)
    (hμ0 : sol.init_μ = 0) (hα0 : sol.init_α = 1) :
    contractTupleTraj sol La 0 =
      Fin.append
        (fun k : Fin 4 =>
          if k = 0 then 0 else if k = 1 then 1 else if k = 2 then 0 else 1)
        (Fin.append
          (fun _ : Fin 2 => 1)
          (Fin.append sol.init_z (Fin.append sol.init_u (fun _ : Fin 1 => 0)))) := by
  funext j
  refine Fin.addCases (m := 4) (n := contractGateTailDim d) ?_ ?_ j
  · intro k
    fin_cases k <;> simp [contractTupleTraj, sol.μ_at_zero, sol.α_at_zero, hμ0, hα0]
  · intro tail0
    refine Fin.addCases (m := 2) (n := contractTailDim d) ?_ ?_ tail0
    · intro k
      fin_cases k <;> simp [contractTupleTraj, contractGateZ, contractGateU, bGateZ,
        bGateU, sol.μ_at_zero, hμ0]
    · intro tail
      refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
      · intro i
        simp [contractTupleTraj, contractZ, contractTailZ, sol.z_at_zero]
      · intro tail2
        refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
        · intro i
          simp [contractTupleTraj, contractU, contractTailU, sol.u_at_zero]
        · intro a
          fin_cases a
          simp [contractTupleTraj, contractA, contractTailA, La.init_a]

/-- Rational Euclidean initial vector for the contract layout. -/
def contractEuclInitQ {d : ℕ} (x₀ : ℕ → Fin d → ℚ) (w : ℕ) :
    Fin (contractDim d) → ℚ :=
  Fin.append
    (fun k : Fin 4 =>
      if k = 0 then 0 else if k = 1 then 1 else if k = 2 then 0 else 1)
    (Fin.append
      (fun _ : Fin 2 => 1)
      (Fin.append (x₀ w) (Fin.append (x₀ w) (fun _ : Fin 1 => 0))))

/-- Compactified rational initial vector induced by `contractEuclInitQ`. -/
def contractSphereInitQ {d : ℕ} (x₀ : ℕ → Fin d → ℚ) (w : ℕ) :
    Fin (contractDim d + 1) → ℚ :=
  let x := contractEuclInitQ x₀ w
  let den : ℚ := (∑ i : Fin (contractDim d), x i ^ 2) + 1
  Fin.cases (((∑ i : Fin (contractDim d), x i ^ 2) - 1) / den)
    (fun i => 2 * x i / den)

lemma contractTupleTraj_zero_eq_contractEuclInitQ
    {d : ℕ} {p : DynGateParams} {sched : PhaseSchedule}
    {F : ℝ → (Fin d → ℝ) → Fin d → ℝ}
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ)
    (sol : DynContractIteratorSol (Fin d) p sched F)
    {flagCoord : Fin d} {I : ContractFlagIndicatorPackage flagCoord}
    {K : ℝ} {R : ℕ}
    (La : ContractHaltLatchSol sol I.Hval K R)
    (hμ0 : sol.init_μ = 0) (hα0 : sol.init_α = 1)
    (hz0 : ∀ i : Fin d, sol.init_z i = ((x₀ w i : ℚ) : ℝ))
    (hu0 : ∀ i : Fin d, sol.init_u i = ((x₀ w i : ℚ) : ℝ)) :
    contractTupleTraj sol La 0 =
      fun i => ((contractEuclInitQ x₀ w i : ℚ) : ℝ) := by
  rw [contractTupleTraj_zero sol La hμ0 hα0]
  funext j
  refine Fin.addCases (m := 4) (n := contractGateTailDim d) ?_ ?_ j
  · intro k
    fin_cases k <;> simp [contractEuclInitQ]
  · intro tail0
    refine Fin.addCases (m := 2) (n := contractTailDim d) ?_ ?_ tail0
    · intro k
      fin_cases k <;> simp [contractEuclInitQ]
    · intro tail
      refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
      · intro i
        simp [contractEuclInitQ, hz0 i]
      · intro tail2
        refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
        · intro i
          simp [contractEuclInitQ, hu0 i]
        · intro a
          fin_cases a
          simp [contractEuclInitQ]

lemma contractSphereInitQ_zero
    {d : ℕ} (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (x : Fin (contractDim d) → ℝ)
    (hx : x = fun i => ((contractEuclInitQ x₀ w i : ℚ) : ℝ)) :
    ((contractSphereInitQ x₀ w 0 : ℚ) : ℝ) =
      ((∑ i : Fin (contractDim d), x i ^ 2) - 1) /
        ((∑ i : Fin (contractDim d), x i ^ 2) + 1) := by
  subst x
  simp [contractSphereInitQ, map_sum, map_pow, map_sub, map_add, map_one, map_div₀]

lemma contractSphereInitQ_succ
    {d : ℕ} (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (x : Fin (contractDim d) → ℝ)
    (hx : x = fun i => ((contractEuclInitQ x₀ w i : ℚ) : ℝ))
    (i : Fin (contractDim d)) :
    ((contractSphereInitQ x₀ w i.succ : ℚ) : ℝ) =
      2 * x i / ((∑ k : Fin (contractDim d), x k ^ 2) + 1) := by
  subst x
  simp [contractSphereInitQ, map_sum, map_pow, map_mul, map_add, map_one, map_div₀]

/--
Package constructor for the contract polynomial field layer.

The final machine instance supplies the polynomial target family `FP`, the
indicator polynomial `HP`, their evaluation identities, and a computable
presentation of the rational sphere initial vector.
-/
def contractPolynomialFieldPackage
    {d nS : ℕ} {Conf : Type} [Primcodable Conf]
    (M : UndecidableMachine Conf)
    (E : StackMachineEncoding d nS M.toDiscreteMachine)
    (S : RobustStepContract M.toDiscreteMachine E)
    (p : DynGateParams) (sched : PhaseSchedule)
    (flagCoord : Fin d)
    (I : ContractFlagIndicatorPackage flagCoord)
    {K : ℝ} {R : ℕ}
    (FP : Fin d → MvPolynomial (Fin (contractDim d)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ)
    (Aq Kq cμq cαq : ℚ) (L : ℕ)
    (hA : p.A = (Aq : ℝ)) (hK : K = (Kq : ℝ))
    (hcμ : p.cμ = (cμq : ℝ)) (hcα : p.cα = (cαq : ℝ))
    (hL : p.L = L)
    (hdomain : ∀ t : ℝ, 0 ≤ t → t ∈ sched.domain)
    (field_eval_identity :
      ∀ (sol : DynContractIteratorSol (Fin d) p sched S.F)
        (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ), 0 ≤ t →
        ∀ i : Fin d,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t) (FP i) =
            S.F (sol.μ t) (sol.u t) i)
    (indicator_eval_identity :
      ∀ (sol : DynContractIteratorSol (Fin d) p sched S.F)
        (La : ContractHaltLatchSol sol I.Hval K R) (t : ℝ),
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) HP =
            I.Hval (sol.z t))
    (init : ℕ → Fin (contractDim d + 1) → ℚ)
    (init_presented : ∃ f : ℕ → Fin (contractDim d + 1) → ℤ × ℕ,
      Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F)
        (La : ContractHaltLatchSol sol I.Hval K R),
          ((init w 0 : ℚ) : ℝ) =
            ((∑ i : Fin (contractDim d), contractTupleTraj sol La 0 i ^ 2) - 1) /
              ((∑ i : Fin (contractDim d), contractTupleTraj sol La 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ) (sol : DynContractIteratorSol (Fin d) p sched S.F)
        (La : ContractHaltLatchSol sol I.Hval K R) (i : Fin (contractDim d)),
          ((init w i.succ : ℚ) : ℝ) =
            2 * contractTupleTraj sol La 0 i /
              ((∑ k : Fin (contractDim d), contractTupleTraj sol La 0 k ^ 2) + 1)) :
    ContractPolynomialFieldPackage M E S p sched flagCoord I K R :=
  { nE := contractDim d
    field := contractAssembledField d FP HP Aq Kq cμq cαq L R
    tuple := fun _w sol La => contractTupleTraj sol La
    tuple_ode := by
      intro w sol La t ht
      exact contractTupleTraj_ode
        (M := M) (E := E) (S := S) (p := p) (sched := sched)
        (flagCoord := flagCoord) (I := I) (K := K) (R := R)
        FP HP hA hK hcμ hcα hL hdomain
        field_eval_identity indicator_eval_identity w sol La t ht
    init := init
    init_presented := init_presented
    init_zero := init_zero
    init_succ := init_succ
    latchCoord := contractA d
    latch_value := by
      intro w sol La t
      simp [contractTupleTraj_a] }

end Ripple.BoundedUniversality.BGP
