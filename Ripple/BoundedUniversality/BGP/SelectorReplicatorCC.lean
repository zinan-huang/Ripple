/-
Ripple.BoundedUniversality.BGP.SelectorReplicatorCC
--------------------------------
Constant-coordinate (CC) extension of the assembled replicator field: the two
clock rates `cμ`/`cα` are promoted from baked polynomial constants (`C cμ`,
`C cα`) to STATE COORDINATES with derivative `0` and per-input rational
initial values — exactly the proven `selWarmGainCoord` pattern, applied to the
rates.  This is the realization layer of the word-coupled (`bgpParamsNW`)
consumer flip: the final PIVP field is `w`-independent, `w` enters only
through the (computably presented) initial condition
`cμ-coord ↦ 1000·bgpScaleW w`, `cα-coord ↦ 300·bgpScaleW w`.

Layer 1 (this file's core):
* `selectorDimCC = selectorDim d V + 2`, embedding `selEmbCC = Fin.castAdd 2`,
  the two new coordinates `selCmuCoordCC`/`selCalphaCoordCC`;
* `selectorReplicatorAssembledFieldCC` — textual copy of
  `selectorReplicatorAssembledField` with `X i ↦ X (selEmbCC i)`, composite
  sub-polynomials renamed along `selEmbCC`, `C cμ ↦ X selCmuCoordCC`,
  `C cα ↦ X selCalphaCoordCC`, and two trailing zero slots;
* the eval₂ bridge: at any point whose two CC coordinates carry the rational
  rates, the CC field evaluates on old slots exactly as the old field at
  those rates, and to `0` on the two new slots;
* `selectorReplicatorTupleTrajCC` — the old tuple trajectory extended by the
  two constant coordinates — and its ODE against the CC field, DERIVED from
  `selectorReplicatorTupleTraj_ode` (not re-proved).
-/

import Ripple.BoundedUniversality.BGP.SelectorReplicatorPackage

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open MvPolynomial Set

/-! ## CC coordinate layout -/

/-- CC state dimension: the selector layout plus the two clock-rate constant
coordinates. -/
abbrev selectorDimCC (d : ℕ) (V : Type) [Fintype V] : ℕ := selectorDim d V + 2

/-- Embed an old selector coordinate into the CC state. -/
def selEmbCC {d : ℕ} {V : Type} [Fintype V] :
    Fin (selectorDim d V) → Fin (selectorDimCC d V) := Fin.castAdd 2

/-- The `cμ` constant coordinate. -/
def selCmuCoordCC (d : ℕ) (V : Type) [Fintype V] : Fin (selectorDimCC d V) :=
  Fin.natAdd (selectorDim d V) (0 : Fin 2)

/-- The `cα` constant coordinate. -/
def selCalphaCoordCC (d : ℕ) (V : Type) [Fintype V] : Fin (selectorDimCC d V) :=
  Fin.natAdd (selectorDim d V) (1 : Fin 2)

/-! ## The CC assembled field -/

/-- The CC assembled replicator field: `selectorReplicatorAssembledField` with
the rates read from the two new constant coordinates (whose own slots are `0`).
NOTE: no `cμ cα : ℚ` arguments — the field is rate-free by design. -/
def selectorReplicatorAssembledFieldCC (d B : ℕ) (V : Type) [Fintype V]
    (branch : V → BranchData d B)
    (chiReset chiGate kappa gainPoly : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (Ppoly : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K : ℚ) (L R : ℕ) :
    Fin (selectorDimCC d V) → MvPolynomial (Fin (selectorDimCC d V)) ℚ :=
  Fin.append
    (Fin.append
      (Fin.append
        (fun k : Fin 4 =>
          if k = 0 then X (selEmbCC (selOfContract V (contractC d))) else
          if k = 1 then -X (selEmbCC (selOfContract V (contractS d))) else
          if k = 2 then X (selCmuCoordCC d V) else
            X (selCalphaCoordCC d V) * X (selEmbCC (selOfContract V (contractAlpha d))))
        (Fin.append
          (fun k : Fin 2 =>
            if k = 0 then
              -((X (selCmuCoordCC d V) * rename (selEmbCC (d := d) (V := V)) (selRP d V L) +
                  X (selEmbCC (selOfContract V (contractMu d))) *
                    rename (selEmbCC (d := d) (V := V)) (selRPderiv d V L)) *
                X (selEmbCC (selOfContract V (contractGateZ d))))
            else
              -((X (selCmuCoordCC d V) * rename (selEmbCC (d := d) (V := V)) (selQP d V L) +
                  X (selEmbCC (selOfContract V (contractMu d))) *
                    rename (selEmbCC (d := d) (V := V)) (selQPderiv d V L)) *
                X (selEmbCC (selOfContract V (contractGateU d)))))
          (Fin.append
            (fun i : Fin d =>
              C A * X (selEmbCC (selOfContract V (contractAlpha d))) *
                X (selEmbCC (selOfContract V (contractGateZ d))) *
                (rename (selEmbCC (d := d) (V := V)) (selectorMixField branch i) -
                  X (selEmbCC (selZ V i))))
            (Fin.append
              (fun i : Fin d =>
                C A * X (selEmbCC (selOfContract V (contractAlpha d))) *
                  X (selEmbCC (selOfContract V (contractGateU d))) *
                  (X (selEmbCC (selZ V i)) - X (selEmbCC (selU V i))))
              (fun _ : Fin 1 =>
                C K * ((C (1 / 2 : ℚ) *
                    (1 - X (selEmbCC (selOfContract V (contractC d))))) ^ R) *
                  (rename (selEmbCC (d := d) (V := V)) (selRenameZ V HP) -
                    X (selEmbCC (selOfContract V (contractA d)))))))))
      (Fin.append
        (fun k : Fin (Fintype.card V) =>
          rename (selEmbCC (d := d) (V := V))
            (selectorReplicatorFieldSelLamPoly chiReset chiGate kappa gainPoly Ppoly
              ((Fintype.equivFin V).symm k)))
        (Fin.append
          (fun _ : Fin 1 =>
            rename (selEmbCC (d := d) (V := V)) (selectorGainFieldPoly chiGate gainPoly))
          (fun _ : Fin 1 => 0))))
    (fun _ : Fin 2 => 0)

section Bridge

variable {d B : ℕ} {V : Type} [Fintype V]
    (branch : V → BranchData d B)
    (chiReset chiGate kappa gainPoly : MvPolynomial (Fin (selectorDim d V)) ℚ)
    (Ppoly : V → MvPolynomial (Fin (selectorDim d V)) ℚ)
    (HP : MvPolynomial (Fin d) ℚ) (A K cμ cα : ℚ) (L R : ℕ)

/-- The two new slots of the CC field are `0` (constant coordinates). -/
theorem selectorReplicatorAssembledFieldCC_natAdd (k : Fin 2) :
    selectorReplicatorAssembledFieldCC d B V branch chiReset chiGate kappa gainPoly Ppoly HP
        A K L R (Fin.natAdd (selectorDim d V) k) = 0 := by
  simp [selectorReplicatorAssembledFieldCC]

/-- **The eval₂ bridge**: at any real point `y` whose CC coordinates carry the
rational rates `cμ`/`cα`, the CC field on an embedded old slot evaluates
exactly as the old assembled field at those rates evaluated on the restricted
point `y ∘ selEmbCC`. -/
theorem eval₂_selectorReplicatorAssembledFieldCC_castAdd
    (y : Fin (selectorDimCC d V) → ℝ)
    (hcμ : y (selCmuCoordCC d V) = ((cμ : ℚ) : ℝ))
    (hcα : y (selCalphaCoordCC d V) = ((cα : ℚ) : ℝ))
    (i : Fin (selectorDim d V)) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) y
        (selectorReplicatorAssembledFieldCC d B V branch chiReset chiGate kappa gainPoly Ppoly HP
          A K L R (selEmbCC i)) =
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) (fun j => y (selEmbCC j))
        (selectorReplicatorAssembledField d B V branch chiReset chiGate kappa gainPoly Ppoly HP
          A K cμ cα L R i) := by
  refine Fin.addCases (m := contractDim d) (n := selectorTailDim V) ?_ ?_ i
  · intro jc
    refine Fin.addCases (m := 4) (n := contractGateTailDim d) ?_ ?_ jc
    · intro k
      fin_cases k
      · -- s' = c
        simp [selectorReplicatorAssembledFieldCC, selectorReplicatorAssembledField,
          selEmbCC, selOfContract, contractS, contractC, eval₂_mul, eval₂_add, eval₂_sub, eval₂_pow, eval₂_one, eval₂_C, eval₂_X]
      · -- c' = -s
        simp [selectorReplicatorAssembledFieldCC, selectorReplicatorAssembledField,
          selEmbCC, selOfContract, contractS, contractC, eval₂_mul, eval₂_add, eval₂_sub, eval₂_pow, eval₂_one, eval₂_C, eval₂_X]
      · -- μ' = cμ
        simp [selectorReplicatorAssembledFieldCC, selectorReplicatorAssembledField,
          selEmbCC, selOfContract, contractMu, hcμ, eval₂_mul, eval₂_add, eval₂_sub, eval₂_pow, eval₂_one, eval₂_C, eval₂_X]
      · -- α' = cα·α
        simp [selectorReplicatorAssembledFieldCC, selectorReplicatorAssembledField,
          selEmbCC, selOfContract, contractAlpha, hcα, eval₂_mul, eval₂_add, eval₂_sub, eval₂_pow, eval₂_one, eval₂_C, eval₂_X]
    · intro tail0
      refine Fin.addCases (m := 2) (n := contractTailDim d) ?_ ?_ tail0
      · intro k
        fin_cases k
        · -- gateZ slot
          simp [selectorReplicatorAssembledFieldCC, selectorReplicatorAssembledField,
            selEmbCC, selOfContract, contractGateZ, contractMu, eval₂_rename, Function.comp_def, hcμ, eval₂_mul, eval₂_add, eval₂_sub, eval₂_pow, eval₂_one, eval₂_C, eval₂_X]
        · -- gateU slot
          simp [selectorReplicatorAssembledFieldCC, selectorReplicatorAssembledField,
            selEmbCC, selOfContract, contractGateU, contractMu, eval₂_rename, Function.comp_def, hcμ, eval₂_mul, eval₂_add, eval₂_sub, eval₂_pow, eval₂_one, eval₂_C, eval₂_X]
      · intro tail
        refine Fin.addCases (m := d) (n := d + 1) ?_ ?_ tail
        · intro iz
          -- z slot
          simp [selectorReplicatorAssembledFieldCC, selectorReplicatorAssembledField,
            selEmbCC, selZ, selOfContract, contractZ, contractTailZ, contractAlpha,
            contractGateZ, eval₂_rename, Function.comp_def, eval₂_mul, eval₂_add, eval₂_sub, eval₂_pow, eval₂_one, eval₂_C, eval₂_X]
        · intro tail2
          refine Fin.addCases (m := d) (n := 1) ?_ ?_ tail2
          · intro iu
            -- u slot
            simp [selectorReplicatorAssembledFieldCC, selectorReplicatorAssembledField,
              selEmbCC, selZ, selU, selOfContract, contractZ, contractU, contractTailZ,
              contractTailU, contractAlpha, contractGateU, eval₂_rename, Function.comp_def, eval₂_mul, eval₂_add, eval₂_sub, eval₂_pow, eval₂_one, eval₂_C, eval₂_X]
          · intro k
            fin_cases k
            -- latch slot
            simp [selectorReplicatorAssembledFieldCC, selectorReplicatorAssembledField,
              selEmbCC, selOfContract, contractA, contractTailA, contractC,
              eval₂_rename, Function.comp_def, eval₂_mul, eval₂_add, eval₂_sub, eval₂_pow, eval₂_one, eval₂_C, eval₂_X]
  · intro jt
    refine Fin.addCases (m := Fintype.card V) (n := 1 + 1) ?_ ?_ jt
    · intro k
      -- λ slots
      simp [selectorReplicatorAssembledFieldCC, selectorReplicatorAssembledField,
        selEmbCC, eval₂_rename, Function.comp_def]
    · intro jGwG
      refine Fin.addCases (m := 1) (n := 1) ?_ ?_ jGwG
      · intro k
        fin_cases k
        -- gain slot
        simp [selectorReplicatorAssembledFieldCC, selectorReplicatorAssembledField,
          selEmbCC, eval₂_rename, Function.comp_def, Fin.append_right, Fin.append_left,
          Fin.append, Fin.addCases]
      · intro k
        fin_cases k
        -- warm-gain slot (0 on both sides)
        simp [selectorReplicatorAssembledFieldCC, selectorReplicatorAssembledField,
          selEmbCC, Fin.append_right, Fin.append, Fin.addCases]

end Bridge

/-! ## The CC tuple trajectory and its ODE -/

section Trajectory

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}

/-- The CC tuple trajectory: the old tuple extended by the two constant rate
coordinates. -/
def selectorReplicatorTupleTrajCC
    (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : SelectorReplicatorHaltLatchSol sol Hval K R)
    (warmGainVal cμVal cαVal : ℝ) (t : ℝ) :
    Fin (selectorDimCC d V) → ℝ :=
  Fin.append (selectorReplicatorTupleTraj sol La warmGainVal t)
    (fun k : Fin 2 => if k = 0 then cμVal else cαVal)

variable {sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv}
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : SelectorReplicatorHaltLatchSol sol Hval K R)
    (warmGainVal cμVal cαVal : ℝ) (t : ℝ)

@[simp] lemma selectorReplicatorTupleTrajCC_castAdd (i : Fin (selectorDim d V)) :
    selectorReplicatorTupleTrajCC sol La warmGainVal cμVal cαVal t (selEmbCC i) =
      selectorReplicatorTupleTraj sol La warmGainVal t i := by
  simp [selectorReplicatorTupleTrajCC, selEmbCC]

@[simp] lemma selectorReplicatorTupleTrajCC_cmu :
    selectorReplicatorTupleTrajCC sol La warmGainVal cμVal cαVal t (selCmuCoordCC d V) =
      cμVal := by
  simp [selectorReplicatorTupleTrajCC, selCmuCoordCC]

@[simp] lemma selectorReplicatorTupleTrajCC_calpha :
    selectorReplicatorTupleTrajCC sol La warmGainVal cμVal cαVal t (selCalphaCoordCC d V) =
      cαVal := by
  simp [selectorReplicatorTupleTrajCC, selCalphaCoordCC]

/-- Restriction of the CC tuple along the embedding is the old tuple. -/
lemma selectorReplicatorTupleTrajCC_comp_emb :
    (fun j => selectorReplicatorTupleTrajCC sol La warmGainVal cμVal cαVal t (selEmbCC j)) =
      selectorReplicatorTupleTraj sol La warmGainVal t := by
  funext j
  simp

private lemma replCC_hasDerivAt_fin_append {m n : ℕ}
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

/-- **The CC tuple ODE** — derived from `selectorReplicatorTupleTraj_ode` (the
old realization) plus the eval₂ bridge and the vanishing derivative of the two
constant coordinates.  Hypotheses are identical to the old ODE lemma. -/
theorem selectorReplicatorTupleTrajCC_ode
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
      HasDerivAt (selectorReplicatorTupleTrajCC sol La warmGainVal ((cμq : ℚ) : ℝ) ((cαq : ℚ) : ℝ))
        (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ)
          (selectorReplicatorTupleTrajCC sol La warmGainVal ((cμq : ℚ) : ℝ) ((cαq : ℚ) : ℝ) t)
          (selectorReplicatorAssembledFieldCC d B V branch chiResetP chiGateP kappaP gainP
            PpolyP HP Aq Kq L R i)) t := by
  intro t ht
  have hold := selectorReplicatorTupleTraj_ode sol La warmGainVal
    chiResetP chiGateP kappaP gainP PpolyP HP hA hK hcμ hcα hL hdomain
    h_chiReset h_chiGate h_kappa h_gain h_P h_HP t ht
  have hconst :
      HasDerivAt
        (fun _ : ℝ => (fun k : Fin 2 => if k = 0 then ((cμq : ℚ) : ℝ) else ((cαq : ℚ) : ℝ)))
        (fun _ : Fin 2 => 0) t := by
    apply hasDerivAt_pi.mpr
    intro k
    simpa using hasDerivAt_const t (if k = 0 then ((cμq : ℚ) : ℝ) else ((cαq : ℚ) : ℝ))
  have happ := replCC_hasDerivAt_fin_append hold hconst
  refine happ.congr_deriv ?_
  funext j
  refine Fin.addCases (m := selectorDim d V) (n := 2) ?_ ?_ j
  · intro i
    rw [Fin.append_left]
    have hbridge := eval₂_selectorReplicatorAssembledFieldCC_castAdd
      (d := d) (B := B) (V := V) branch chiResetP chiGateP kappaP gainP PpolyP HP
      Aq Kq cμq cαq L R
      (selectorReplicatorTupleTrajCC sol La warmGainVal ((cμq : ℚ) : ℝ) ((cαq : ℚ) : ℝ) t)
      (by simp) (by simp) i
    rw [show (Fin.castAdd 2 i : Fin (selectorDimCC d V)) = selEmbCC i from rfl, hbridge,
      selectorReplicatorTupleTrajCC_comp_emb]
  · intro k
    rw [Fin.append_right, selectorReplicatorAssembledFieldCC_natAdd]
    simp

end Trajectory

/-! ## CC initial data -/

section InitCC

variable {d B : ℕ} {V : Type} [Fintype V]
    {p : DynGateParams} {sched : PhaseSchedule} {branch : V → BranchData d B}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ} {Pv : V → (Fin d → ℝ) → ℝ}

/-- CC Euclidean initial vector: the old initial vector extended by the two
rational rate values. -/
def selectorReplicatorEuclInitQCC (d : ℕ) (V : Type) [Fintype V]
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit cμInit cαInit : ℚ) :
    Fin (selectorDimCC d V) → ℚ :=
  Fin.append (selectorReplicatorEuclInitQ d V x₀ w warmGainInit)
    (fun k : Fin 2 => if k = 0 then cμInit else cαInit)

/-- CC sphere (stereographic) initial vector. -/
def selectorReplicatorSphereInitQCC (d : ℕ) (V : Type) [Fintype V]
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit cμInit cαInit : ℚ) :
    Fin (selectorDimCC d V + 1) → ℚ :=
  let x := selectorReplicatorEuclInitQCC d V x₀ w warmGainInit cμInit cαInit
  let den : ℚ := (∑ i : Fin (selectorDimCC d V), x i ^ 2) + 1
  Fin.cases (((∑ i : Fin (selectorDimCC d V), x i ^ 2) - 1) / den)
    (fun i => 2 * x i / den)

/-- At `t = 0` the CC tuple is the real cast of the CC Euclidean rational
initial vector (extends the old `_zero_eq_selectorReplicatorEuclInitQ`). -/
theorem selectorReplicatorTupleTrajCC_zero_eq_EuclInitQCC
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (warmGainInit cμInit cαInit : ℚ)
    (sol : SelectorReplicatorDynSol d B V p sched branch chiResetF chiGateF kappaF gainF Pv)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : SelectorReplicatorHaltLatchSol sol Hval K R)
    (hμ0 : sol.μ 0 = 0) (hα0 : sol.α 0 = 1)
    (hz0 : ∀ i : Fin d, sol.z 0 i = ((x₀ w i : ℚ) : ℝ))
    (hu0 : ∀ i : Fin d, sol.u 0 i = ((x₀ w i : ℚ) : ℝ))
    (hlam0 : ∀ v : V, sol.lam v 0 = ((1 / (Fintype.card V : ℚ)) : ℝ))
    (hG0 : sol.G 0 = 0) :
    selectorReplicatorTupleTrajCC sol La (warmGainInit : ℝ) (cμInit : ℝ) (cαInit : ℝ) 0 =
      fun i =>
        ((selectorReplicatorEuclInitQCC d V x₀ w warmGainInit cμInit cαInit i : ℚ) : ℝ) := by
  have hold :=
    selectorReplicatorTupleTraj_zero_eq_selectorReplicatorEuclInitQ
      (d := d) (B := B) (V := V) (p := p) (sched := sched) (branch := branch)
      (chiResetF := chiResetF) (chiGateF := chiGateF) (kappaF := kappaF)
      (gainF := gainF) (Pv := Pv) x₀ w warmGainInit sol La hμ0 hα0
      hz0 hu0 hlam0 hG0 La.init_a
  funext j
  refine Fin.addCases (m := selectorDim d V) (n := 2) ?_ ?_ j
  · intro i
    have := congrFun hold i
    simpa [selectorReplicatorTupleTrajCC, selectorReplicatorEuclInitQCC,
      Fin.append_left] using this
  · intro k
    fin_cases k <;>
      simp [selectorReplicatorTupleTrajCC, selectorReplicatorEuclInitQCC,
        Fin.append_right]

/-- CC init-zero encoder identity (mirrors
`selector_replicator_init_zero_of_initial_values`). -/
theorem selector_replicator_init_zero_of_initial_values_CC
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (g₀ cμInit cαInit : ℚ)
    (s : SelectorReplicatorDynSol d B V p sched branch
      chiResetF chiGateF kappaF gainF Pv)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : SelectorReplicatorHaltLatchSol s Hval K R)
    (hz0 : ∀ i : Fin d, s.z 0 i = ((x₀ w i : ℚ) : ℝ))
    (hu0 : ∀ i : Fin d, s.u 0 i = ((x₀ w i : ℚ) : ℝ))
    (hlam0 : ∀ v : V, s.lam v 0 = ((1 / (Fintype.card V : ℚ)) : ℝ))
    (hG0 : s.G 0 = 0) :
      ((selectorReplicatorSphereInitQCC d V x₀ w g₀ cμInit cαInit 0 : ℚ) : ℝ) =
        ((∑ i : Fin (selectorDimCC d V),
            selectorReplicatorTupleTrajCC s La (g₀ : ℝ) (cμInit : ℝ) (cαInit : ℝ) 0 i ^ 2) - 1) /
          ((∑ i : Fin (selectorDimCC d V),
            selectorReplicatorTupleTrajCC s La (g₀ : ℝ) (cμInit : ℝ) (cαInit : ℝ) 0 i ^ 2) + 1) := by
  have htuple :
      selectorReplicatorTupleTrajCC s La (g₀ : ℝ) (cμInit : ℝ) (cαInit : ℝ) 0 =
        fun i =>
          ((selectorReplicatorEuclInitQCC d V x₀ w g₀ cμInit cαInit i : ℚ) : ℝ) :=
    selectorReplicatorTupleTrajCC_zero_eq_EuclInitQCC x₀ w g₀ cμInit cαInit s La
      s.μ_at_zero s.α_at_zero hz0 hu0 hlam0 hG0
  rw [htuple]
  simp [selectorReplicatorSphereInitQCC, map_sum, map_pow, map_sub, map_add, map_one,
    map_div₀]

/-- CC init-succ encoder identity (mirrors
`selector_replicator_init_succ_of_initial_values`). -/
theorem selector_replicator_init_succ_of_initial_values_CC
    (x₀ : ℕ → Fin d → ℚ) (w : ℕ) (g₀ cμInit cαInit : ℚ)
    (s : SelectorReplicatorDynSol d B V p sched branch
      chiResetF chiGateF kappaF gainF Pv)
    {Hval : (Fin d → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : SelectorReplicatorHaltLatchSol s Hval K R)
    (hz0 : ∀ i : Fin d, s.z 0 i = ((x₀ w i : ℚ) : ℝ))
    (hu0 : ∀ i : Fin d, s.u 0 i = ((x₀ w i : ℚ) : ℝ))
    (hlam0 : ∀ v : V, s.lam v 0 = ((1 / (Fintype.card V : ℚ)) : ℝ))
    (hG0 : s.G 0 = 0) (i : Fin (selectorDimCC d V)) :
      ((selectorReplicatorSphereInitQCC d V x₀ w g₀ cμInit cαInit i.succ : ℚ) : ℝ) =
        2 * selectorReplicatorTupleTrajCC s La (g₀ : ℝ) (cμInit : ℝ) (cαInit : ℝ) 0 i /
          ((∑ k : Fin (selectorDimCC d V),
            selectorReplicatorTupleTrajCC s La (g₀ : ℝ) (cμInit : ℝ) (cαInit : ℝ) 0 k ^ 2) + 1) := by
  have htuple :
      selectorReplicatorTupleTrajCC s La (g₀ : ℝ) (cμInit : ℝ) (cαInit : ℝ) 0 =
        fun i =>
          ((selectorReplicatorEuclInitQCC d V x₀ w g₀ cμInit cαInit i : ℚ) : ℝ) :=
    selectorReplicatorTupleTrajCC_zero_eq_EuclInitQCC x₀ w g₀ cμInit cαInit s La
      s.μ_at_zero s.α_at_zero hz0 hu0 hlam0 hG0
  rw [htuple]
  simp [selectorReplicatorSphereInitQCC, map_sum, map_pow, map_sub, map_add, map_one,
    map_div₀]

end InitCC

end Ripple.BoundedUniversality.BGP
