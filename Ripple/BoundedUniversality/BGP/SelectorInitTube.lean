import Ripple.BoundedUniversality.BGP.SelectorSolWired

/-!
Ripple.BoundedUniversality.BGP.SelectorInitTube
---------------------------
Atomic leaf A1: choose the selector input block to be the rational encoding of
the concrete universal machine's initial configuration.
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open MachineInstance UniversalMachine Turing.PartrecToTM2

local instance : Fintype (SuppLabel c_f) := by
  unfold SuppLabel
  infer_instance

/-- The initial finite-support universal-machine configuration on input `w`. -/
abbrev selectorInitConfig (w : ℕ) : UConf :=
  M_U.init w

theorem selectorInitConfig_eq_undecidable_init (w : ℕ) :
    selectorInitConfig w =
      UniversalMachine.undecidableMachine.toDiscreteMachine.init w := rfl

/-- Concrete rational selector input: exactly the rational encoding of `M_U.init w`. -/
def selectorInitX0 (w : ℕ) (i : Fin d_U) : ℚ :=
  confEncU (selectorInitConfig w) i

theorem selectorInitX0_cast_enc (w : ℕ) (i : Fin d_U) :
    ((selectorInitX0 w i : ℚ) : ℝ) =
      stackMachineEncodingU.enc (selectorInitConfig w) i := rfl

private def selectorInitListDispatch {A B C : Type} [DecidableEq A]
    (xs : List A) (default : B → C) (f : A → B → C) : A → B → C :=
  match xs with
  | [] => fun _ b => default b
  | x :: xs => fun a b =>
      if a = x then f x b else selectorInitListDispatch xs default f a b

private theorem selectorInitPrimrecEqBool {A : Type} [Primcodable A]
    [DecidableEq A] (x : A) :
    Primrec (fun a : A => decide (a = x)) := by
  exact (PrimrecPred.decide
    (PrimrecRel.comp Primrec.eq Primrec.id (Primrec.const x)))

private theorem selectorInitListDispatch_primrec
    {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]
    [DecidableEq A] (xs : List A) (default : B → C) (f : A → B → C)
    (hdefault : Primrec default) (hf : ∀ a, Primrec (f a)) :
    Primrec₂ (selectorInitListDispatch xs default f) := by
  induction xs with
  | nil =>
      exact Primrec₂.mk (hdefault.comp Primrec.snd)
  | cons x xs ih =>
      refine Primrec₂.mk ?_
      have hc : Primrec (fun p : A × B => decide (p.1 = x)) :=
        (selectorInitPrimrecEqBool x).comp Primrec.fst
      have hthen : Primrec (fun p : A × B => f x p.2) :=
        (hf x).comp Primrec.snd
      have helse : Primrec
          (fun p : A × B => selectorInitListDispatch xs default f p.1 p.2) := ih
      exact (Primrec.cond hc hthen helse).of_eq fun p => by
        rcases p with ⟨a, b⟩
        by_cases h : a = x <;> simp [selectorInitListDispatch, h]

private theorem selectorInitListDispatch_eq_of_mem {A B C : Type} [DecidableEq A]
    (xs : List A) (default : B → C) (f : A → B → C)
    {a : A} (ha : a ∈ xs) (b : B) :
    selectorInitListDispatch xs default f a b = f a b := by
  induction xs with
  | nil => cases ha
  | cons x xs ih =>
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · simp [selectorInitListDispatch]
      · by_cases h : a = x
        · simp [selectorInitListDispatch, h]
        · simp [selectorInitListDispatch, h, ih ha]

private def stackCodeUPresenter : List Γ' → ℤ × ℕ
  | [] => (Int.ofNat (bot B_U), B_U)
  | a :: L =>
      let p := stackCodeUPresenter L
      (Int.ofNat (gammaDigit a) * Int.ofNat p.2 + p.1, B_U * p.2)

private theorem stackCodeUPresenter_den_ne_zero (L : List Γ') :
    (stackCodeUPresenter L).2 ≠ 0 := by
  induction L with
  | nil =>
      norm_num [stackCodeUPresenter, B_U]
  | cons a L ih =>
      simp [stackCodeUPresenter, B_U, ih]

private theorem stackCodeUPresenter_spec (L : List Γ') :
    stackCodeU B_U gammaDigit L =
      (stackCodeUPresenter L).1 / ((stackCodeUPresenter L).2 : ℚ) := by
  induction L with
  | nil =>
      norm_num [stackCodeUPresenter, stackCodeU, B_U, bot]
  | cons a L ih =>
      have hd : ((stackCodeUPresenter L).2 : ℚ) ≠ 0 := by
        exact_mod_cast stackCodeUPresenter_den_ne_zero L
      rw [stackCodeU_push, ih]
      simp [stackCodeUPresenter, B_U]
      field_simp [hd]

private def stackCodeUPresenterStep (_ : List Γ')
    (x : Γ' × List Γ' × (ℤ × ℕ)) : ℤ × ℕ :=
  let p := x.2.2
  (Int.ofNat (gammaDigit x.1) * Int.ofNat p.2 + p.1, B_U * p.2)

private theorem primrec_gammaDigit : Primrec gammaDigit :=
  by
    have h₂ : Primrec₂ (fun a (_ : Unit) => gammaDigit a) :=
      let xs := (Finset.univ : Finset Γ').toList
      (selectorInitListDispatch_primrec xs (fun _ : Unit => gammaDigit default)
          (fun a _ => gammaDigit a) (Primrec.const (gammaDigit default))
          (fun a => Primrec.const (gammaDigit a))).of_eq (by
        intro a b
        exact selectorInitListDispatch_eq_of_mem xs (fun _ : Unit => gammaDigit default)
          (fun a _ => gammaDigit a) (by simp [xs]) b)
    simpa using h₂.comp Primrec.id (Primrec.const ())

private theorem primrec_stackCodeUPresenterStep :
    Primrec₂ stackCodeUPresenterStep := by
  unfold stackCodeUPresenterStep
  let den : Γ' × List Γ' × (ℤ × ℕ) → ℕ := fun x => x.2.2.2
  let num : Γ' × List Γ' × (ℤ × ℕ) → ℤ := fun x => x.2.2.1
  have hdig : Primrec fun x : Γ' × List Γ' × (ℤ × ℕ) => gammaDigit x.1 :=
    primrec_gammaDigit.comp Primrec.fst
  have hdigInt : Primrec fun x : Γ' × List Γ' × (ℤ × ℕ) =>
      Int.ofNat (gammaDigit x.1) :=
    primrec_int_ofNat.comp hdig
  have hden : Primrec den :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hdenInt : Primrec fun x : Γ' × List Γ' × (ℤ × ℕ) => Int.ofNat (den x) :=
    primrec_int_ofNat.comp hden
  have hnum : Primrec num :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hmulInt : Primrec fun x : Γ' × List Γ' × (ℤ × ℕ) =>
      Int.ofNat (gammaDigit x.1) * Int.ofNat (den x) :=
    primrec2_int_mul.comp hdigInt hdenInt
  have hnumOut : Primrec fun x : Γ' × List Γ' × (ℤ × ℕ) =>
      Int.ofNat (gammaDigit x.1) * Int.ofNat (den x) + num x :=
    primrec2_int_add.comp hmulInt hnum
  have hdenOut : Primrec fun x : Γ' × List Γ' × (ℤ × ℕ) => B_U * den x :=
    Primrec.nat_mul.comp (Primrec.const B_U) hden
  exact Primrec₂.mk ((Primrec.pair hnumOut hdenOut).comp Primrec.snd)

private theorem computable_stackCodeUPresenter : Computable stackCodeUPresenter := by
  have hprim : Primrec stackCodeUPresenter := by
    refine (Primrec.list_rec (f := fun L : List Γ' => L)
      (g := fun _ : List Γ' => (Int.ofNat (bot B_U), B_U))
      (h := stackCodeUPresenterStep)
      Primrec.id (Primrec.const _) primrec_stackCodeUPresenterStep).of_eq ?_
    intro L
    induction L with
    | nil => rfl
    | cons a L ih =>
        let r : ℤ × ℕ :=
          List.recOn L (Int.ofNat (bot B_U), B_U)
            fun b l IH =>
              (Int.ofNat (gammaDigit b) * Int.ofNat IH.2 + IH.1, B_U * IH.2)
        have hr : r = stackCodeUPresenter L := by
          simpa [stackCodeUPresenterStep] using ih
        change
          (Int.ofNat (gammaDigit a) * Int.ofNat r.2 + r.1, B_U * r.2) =
            (Int.ofNat (gammaDigit a) *
                Int.ofNat (stackCodeUPresenter L).2 + (stackCodeUPresenter L).1,
              B_U * (stackCodeUPresenter L).2)
        rw [hr]
  exact hprim.to_comp

private theorem computable_mainStackU : Computable mainStackU := by
  unfold mainStackU
  exact Computable.fst.comp (Computable.snd.comp Computable.snd)

private theorem computable_revStackU : Computable revStackU := by
  unfold revStackU
  exact Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))

private theorem computable_auxStackU : Computable auxStackU := by
  unfold auxStackU
  exact Computable.fst.comp
    (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))

private theorem computable_dataStackU : Computable dataStackU := by
  unfold dataStackU
  exact Computable.snd.comp
    (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))

private def selectorInitX0Presenter (w : ℕ) (i : Fin d_U) : ℤ × ℕ :=
  if i = mainStackCoordU then
    stackCodeUPresenter (mainStackU (selectorInitConfig w))
  else if i = revStackCoordU then
    stackCodeUPresenter (revStackU (selectorInitConfig w))
  else if i = auxStackCoordU then
    stackCodeUPresenter (auxStackU (selectorInitConfig w))
  else if i = dataStackCoordU then
    stackCodeUPresenter (dataStackU (selectorInitConfig w))
  else if i = ctrlCoordU then
    (ctrlVarCodeU (selectorInitConfig 0).1 (selectorInitConfig 0).2.1, 1)
  else
    (0, 1)

private theorem computable_selectorInitFinLambda {α σ : Type*} [Primcodable α] [Primcodable σ]
    {n : ℕ} {f : α → Fin n → σ}
    (hf : ∀ i, Computable fun a => f a i) : Computable f := by
  have hv : Computable fun a => List.Vector.ofFn fun i => f a i :=
    Computable.vector_ofFn hf
  have he : Computable (Equiv.vectorEquivFin σ n) := Primrec.of_equiv_symm.to_comp
  exact (he.comp hv).of_eq fun a => by
    funext i
    exact List.Vector.get_ofFn (fun i => f a i) i

private theorem computable_selectorInitX0Presenter_apply (i : Fin d_U) :
    Computable fun w => selectorInitX0Presenter w i := by
  have hinit : Computable selectorInitConfig := M_U.init_computable
  have hmain : Computable fun w => stackCodeUPresenter (mainStackU (selectorInitConfig w)) :=
    computable_stackCodeUPresenter.comp (computable_mainStackU.comp hinit)
  have hrev : Computable fun w => stackCodeUPresenter (revStackU (selectorInitConfig w)) :=
    computable_stackCodeUPresenter.comp (computable_revStackU.comp hinit)
  have haux : Computable fun w => stackCodeUPresenter (auxStackU (selectorInitConfig w)) :=
    computable_stackCodeUPresenter.comp (computable_auxStackU.comp hinit)
  have hdata : Computable fun w => stackCodeUPresenter (dataStackU (selectorInitConfig w)) :=
    computable_stackCodeUPresenter.comp (computable_dataStackU.comp hinit)
  fin_cases i
  · simpa [selectorInitX0Presenter, mainStackCoordU] using hmain
  · simpa [selectorInitX0Presenter, mainStackCoordU, revStackCoordU] using hrev
  · simpa [selectorInitX0Presenter, mainStackCoordU, revStackCoordU, auxStackCoordU] using haux
  · simpa [selectorInitX0Presenter, mainStackCoordU, revStackCoordU, auxStackCoordU,
      dataStackCoordU] using hdata
  · exact Computable.const _
  · exact Computable.const _

private theorem computable_selectorInitX0Presenter :
    Computable selectorInitX0Presenter :=
  computable_selectorInitFinLambda computable_selectorInitX0Presenter_apply

private theorem selectorInitX0Presenter_den_ne_zero (w : ℕ) (i : Fin d_U) :
    (selectorInitX0Presenter w i).2 ≠ 0 := by
  fin_cases i <;>
    simp [selectorInitX0Presenter, mainStackCoordU, revStackCoordU, auxStackCoordU,
      dataStackCoordU, ctrlCoordU, stackCodeUPresenter_den_ne_zero]

private theorem selectorInitX0Presenter_ctrl_eq (w : ℕ) :
    ctrlVarCodeU (selectorInitConfig w).1 (selectorInitConfig w).2.1 =
      ctrlVarCodeU (selectorInitConfig 0).1 (selectorInitConfig 0).2.1 := by
  simp [selectorInitConfig, M_U, discreteMachine, finInit]

private theorem selectorInitX0Presenter_halt_zero (w : ℕ) :
    haltFlagU (selectorInitConfig w) = 0 := by
  simp [selectorInitConfig, M_U, discreteMachine, finInit, haltFlagU, finHalted]

private theorem selectorInitX0Presenter_spec (w : ℕ) (i : Fin d_U) :
    selectorInitX0 w i =
      (selectorInitX0Presenter w i).1 / ((selectorInitX0Presenter w i).2 : ℚ) := by
  fin_cases i
  · change confEncU (selectorInitConfig w) mainStackCoordU =
      (stackCodeUPresenter (mainStackU (selectorInitConfig w))).1 /
        ((stackCodeUPresenter (mainStackU (selectorInitConfig w))).2 : ℚ)
    rw [confEncU_main, stackCodeUPresenter_spec]
  · change confEncU (selectorInitConfig w) revStackCoordU =
      (stackCodeUPresenter (revStackU (selectorInitConfig w))).1 /
        ((stackCodeUPresenter (revStackU (selectorInitConfig w))).2 : ℚ)
    rw [confEncU_rev, stackCodeUPresenter_spec]
  · change confEncU (selectorInitConfig w) auxStackCoordU =
      (stackCodeUPresenter (auxStackU (selectorInitConfig w))).1 /
        ((stackCodeUPresenter (auxStackU (selectorInitConfig w))).2 : ℚ)
    rw [confEncU_aux, stackCodeUPresenter_spec]
  · change confEncU (selectorInitConfig w) dataStackCoordU =
      (stackCodeUPresenter (dataStackU (selectorInitConfig w))).1 /
        ((stackCodeUPresenter (dataStackU (selectorInitConfig w))).2 : ℚ)
    rw [confEncU_data, stackCodeUPresenter_spec]
  · change selectorInitX0 w ctrlCoordU =
      (selectorInitX0Presenter w ctrlCoordU).1 /
        ((selectorInitX0Presenter w ctrlCoordU).2 : ℚ)
    rw [show selectorInitX0 w ctrlCoordU =
        (ctrlVarCodeU (selectorInitConfig w).1 (selectorInitConfig w).2.1 : ℚ) by
      simp [selectorInitX0]]
    rw [selectorInitX0Presenter_ctrl_eq w]
    simp [selectorInitX0Presenter, mainStackCoordU, revStackCoordU, auxStackCoordU,
      dataStackCoordU, ctrlCoordU]
  · change selectorInitX0 w haltCoordU =
      (selectorInitX0Presenter w haltCoordU).1 /
        ((selectorInitX0Presenter w haltCoordU).2 : ℚ)
    rw [show selectorInitX0 w haltCoordU = haltFlagU (selectorInitConfig w) by
      simp [selectorInitX0]]
    rw [selectorInitX0Presenter_halt_zero w]
    simp [selectorInitX0Presenter, mainStackCoordU, revStackCoordU, auxStackCoordU,
      dataStackCoordU, ctrlCoordU, haltCoordU]

theorem selectorInitX0_presented :
    ∃ f : ℕ → Fin d_U → ℤ × ℕ, Computable f ∧
      ∀ w i, (f w i).2 ≠ 0 ∧
        selectorInitX0 w i = (f w i).1 / ((f w i).2 : ℚ) := by
  refine ⟨selectorInitX0Presenter, computable_selectorInitX0Presenter, ?_⟩
  intro w i
  exact ⟨selectorInitX0Presenter_den_ne_zero w i, selectorInitX0Presenter_spec w i⟩

theorem selectorEuclInitQ_u_selectorInitX0 (w : ℕ) (g₀ : ℚ) (i : Fin d_U) :
    ((selectorEuclInitQ d_U UniversalLocalView selectorInitX0 w g₀
      (selU UniversalLocalView i) : ℚ) : ℝ) =
      stackMachineEncodingU.enc (selectorInitConfig w) i := by
  simpa [selectorEuclInitQ, selU, selOfContract, contractU, contractTailU] using
    selectorInitX0_cast_enc w i

theorem selectorMUInit_u_selectorInitX0 (w : ℕ) (g₀ : ℚ) (i : Fin d_U) :
    selectorMUInit selectorInitX0 w g₀ (selU UniversalLocalView i) =
      stackMachineEncodingU.enc (selectorInitConfig w) i := by
  simpa [selectorMUInit] using selectorEuclInitQ_u_selectorInitX0 w g₀ i

/-- Zero-radius init tube for any selector solution whose `u 0` is the chosen input block. -/
theorem selector_init_tube_of_u0
    {M : ℕ} {κ₀ g₀ : ℚ}
    {branch : UniversalLocalView → BranchData d_U B_U}
    {readoutP : UniversalLocalView → (Fin d_U → ℝ) → ℝ}
    (sol : SelectorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule branch
      (fun t => ((1 + Real.cos t) / 2) ^ M)
      (fun t => ((1 + Real.sin t) / 2) ^ M)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      readoutP)
    (w : ℕ)
    (hu0 : ∀ i, sol.u 0 i = ((selectorInitX0 w i : ℚ) : ℝ)) :
    ∀ i, |sol.u 0 i - stackMachineEncodingU.enc (selectorInitConfig w) i| = 0 := by
  intro i
  rw [hu0 i, selectorInitX0_cast_enc]
  simp

theorem selector_init_tube_le_zero_of_u0
    {M : ℕ} {κ₀ g₀ : ℚ}
    {branch : UniversalLocalView → BranchData d_U B_U}
    {readoutP : UniversalLocalView → (Fin d_U → ℝ) → ℝ}
    (sol : SelectorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule branch
      (fun t => ((1 + Real.cos t) / 2) ^ M)
      (fun t => ((1 + Real.sin t) / 2) ^ M)
      (fun _ => (κ₀ : ℝ))
      (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      readoutP)
    (w : ℕ)
    (hu0 : ∀ i, sol.u 0 i = ((selectorInitX0 w i : ℚ) : ℝ)) :
    ∀ i, |sol.u 0 i - stackMachineEncodingU.enc (selectorInitConfig w) i| ≤ 0 := by
  intro i
  exact le_of_eq (selector_init_tube_of_u0 sol w hu0 i)

/-! ### A1 closure for the constructed `solMU` family

With the input block fixed to `selectorInitX0` (the rational encoding of the start config), the
constructed `solMU` family's initial `u`-value is EXACTLY `enc(initConfig w)` — so the init tube
holds with radius `0`, unconditionally on any tube hypothesis. Uses the init conjunct now exposed
by `selector_sol_exists_MU38_clean`. -/

/-- `solMU`'s initial u-value at the u-coords equals the encoded start config. -/
theorem solMU_u0_eq_enc
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ) {Rbd : ℝ}
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ)) (hKq0 : 0 ≤ (Kq : ℝ))
    (hytcont : ∀ w, ∀ T, 0 < T → ∀ yt, yt 0 = selectorMUInit selectorInitX0 w g₀ →
        Ripple.DerivOnIco (selectorMUField38 eta heta M κ₀ g₀ HP Kq R) yt T →
        Continuous yt)
    (hRen : ∀ w, ∀ T, 0 < T → ∀ yt, yt 0 = selectorMUInit selectorInitX0 w g₀ →
        Ripple.DerivOnIco (selectorMUField38 eta heta M κ₀ g₀ HP Kq R) yt T →
        ∀ t ∈ Set.Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selRenameZ UniversalLocalView HP)| ≤ Rbd)
    (w : ℕ) :
    ∀ i, (solMU eta heta M κ₀ g₀ HP Kq R selectorInitX0 hκ0 hg0 hKq0 hytcont hRen w).u 0 i
        = stackMachineEncodingU.enc (selectorInitConfig w) i := by
  intro i
  have hspec := (selector_sol_exists_MU38_clean eta heta M κ₀ g₀ HP Kq R selectorInitX0 w
    hκ0 hg0 hKq0 (hytcont w) (hRen w)).choose_spec
  rw [solMU_def eta heta M κ₀ g₀ HP Kq R selectorInitX0
    hκ0 hg0 hKq0 hytcont hRen w]
  rw [hspec.2.2.1 i]
  exact selectorEuclInitQ_u_selectorInitX0 w g₀ i

/-- **A1 (atomic leaf) DISCHARGED.** Init tube of the constructed `solMU` holds with radius 0. -/
theorem solMU_init_tube
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ) {Rbd : ℝ}
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ)) (hKq0 : 0 ≤ (Kq : ℝ))
    (hytcont : ∀ w, ∀ T, 0 < T → ∀ yt, yt 0 = selectorMUInit selectorInitX0 w g₀ →
        Ripple.DerivOnIco (selectorMUField38 eta heta M κ₀ g₀ HP Kq R) yt T →
        Continuous yt)
    (hRen : ∀ w, ∀ T, 0 < T → ∀ yt, yt 0 = selectorMUInit selectorInitX0 w g₀ →
        Ripple.DerivOnIco (selectorMUField38 eta heta M κ₀ g₀ HP Kq R) yt T →
        ∀ t ∈ Set.Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selRenameZ UniversalLocalView HP)| ≤ Rbd)
    (w : ℕ) :
    ∀ i, |(solMU eta heta M κ₀ g₀ HP Kq R selectorInitX0 hκ0 hg0 hKq0 hytcont hRen w).u 0 i
        - stackMachineEncodingU.enc (selectorInitConfig w) i| = 0 := by
  intro i
  rw [solMU_u0_eq_enc eta heta M κ₀ g₀ HP Kq R hκ0 hg0 hKq0 hytcont hRen w i]
  simp

/-- The finite-horizon `z/u` coordinate bound exposed by the constructed `solMU`. -/
theorem solMU_coord_bound
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ) {Rbd : ℝ}
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ)) (hKq0 : 0 ≤ (Kq : ℝ))
    (hytcont : ∀ w, ∀ T, 0 < T → ∀ yt, yt 0 = selectorMUInit selectorInitX0 w g₀ →
        Ripple.DerivOnIco (selectorMUField38 eta heta M κ₀ g₀ HP Kq R) yt T →
        Continuous yt)
    (hRen : ∀ w, ∀ T, 0 < T → ∀ yt, yt 0 = selectorMUInit selectorInitX0 w g₀ →
        Ripple.DerivOnIco (selectorMUField38 eta heta M κ₀ g₀ HP Kq R) yt T →
        ∀ t ∈ Set.Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selRenameZ UniversalLocalView HP)| ≤ Rbd)
    (w : ℕ) :
    (solMU eta heta M κ₀ g₀ HP Kq R selectorInitX0
      hκ0 hg0 hKq0 hytcont hRen w).ZUFiniteCoordBound := by
  have hspec := (selector_sol_exists_MU38_clean eta heta M κ₀ g₀ HP Kq R selectorInitX0 w
    hκ0 hg0 hKq0 (hytcont w) (hRen w)).choose_spec
  rw [solMU_def eta heta M κ₀ g₀ HP Kq R selectorInitX0
    hκ0 hg0 hKq0 hytcont hRen w]
  exact hspec.2.2.2

private theorem selectorSchedule_domain_of_nonneg :
    ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain := by
  intro t ht
  simpa [selectorSchedule] using ht

/-- **A2 (atomic leaf) early drift.**  The witness drift is
`(2 * B * exp(π/16)) * (π/6)`, where `B` is the exposed finite-horizon
coordinate bound for `solMU` on `[0, π/6 + 1)`. -/
theorem solMU_early_drift
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ) (Kq : ℚ) (R : ℕ) {Rbd : ℝ}
    (hκ0 : 0 ≤ (κ₀ : ℝ)) (hg0 : 0 ≤ (g₀ : ℝ)) (hKq0 : 0 ≤ (Kq : ℝ))
    (hytcont : ∀ w, ∀ T, 0 < T → ∀ yt, yt 0 = selectorMUInit selectorInitX0 w g₀ →
        Ripple.DerivOnIco (selectorMUField38 eta heta M κ₀ g₀ HP Kq R) yt T →
        Continuous yt)
    (hRen : ∀ w, ∀ T, 0 < T → ∀ yt, yt 0 = selectorMUInit selectorInitX0 w g₀ →
        Ripple.DerivOnIco (selectorMUField38 eta heta M κ₀ g₀ HP Kq R) yt T →
        ∀ t ∈ Set.Ico (0 : ℝ) T,
          |MvPolynomial.eval₂ (algebraMap ℚ ℝ) (yt t)
            (selRenameZ UniversalLocalView HP)| ≤ Rbd)
    (w : ℕ) :
    ∃ B : ℝ, 0 < B ∧
      ∀ i, |(solMU eta heta M κ₀ g₀ HP Kq R selectorInitX0
          hκ0 hg0 hKq0 hytcont hRen w).u (Real.pi / 6) i
        - (solMU eta heta M κ₀ g₀ HP Kq R selectorInitX0
          hκ0 hg0 hKq0 hytcont hRen w).u 0 i|
        ≤ (2 * B * Real.exp (50 * Real.pi)) * (Real.pi / 6) := by
  let sol := solMU eta heta M κ₀ g₀ HP Kq R selectorInitX0
    hκ0 hg0 hKq0 hytcont hRen w
  have hBsrc := solMU_coord_bound eta heta M κ₀ g₀ HP Kq R
    hκ0 hg0 hKq0 hytcont hRen w
  have hT : 0 < Real.pi / 6 + 1 := by positivity
  obtain ⟨B, hBpos, hB⟩ := hBsrc (Real.pi / 6 + 1) hT
  refine ⟨B, hBpos, ?_⟩
  intro i
  have hpi := Real.pi_pos
  have hab : (0 : ℝ) ≤ Real.pi / 6 := by positivity
  have hfield : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 6),
      |bgpParams38.A * sol.α t * bGateU bgpParams38.L (sol.μ t) t *
        (sol.z t i - sol.u t i)| ≤ 2 * B * Real.exp (50 * Real.pi) := by
    intro t ht
    have htT : t ∈ Set.Ico (0 : ℝ) (Real.pi / 6 + 1) :=
      ⟨ht.1, ht.2.trans_lt (lt_add_of_pos_right _ zero_lt_one)⟩
    have hz := (hB t htT i).1
    have hu := (hB t htT i).2
    have hzu : |sol.z t i - sol.u t i| ≤ 2 * B := by
      calc
        |sol.z t i - sol.u t i| = |sol.z t i + -sol.u t i| := by ring_nf
        _ ≤ |sol.z t i| + |-sol.u t i| := abs_add_le _ _
        _ = |sol.z t i| + |sol.u t i| := by rw [abs_neg]
        _ ≤ B + B := add_le_add hz hu
        _ = 2 * B := by ring
    have hα : sol.α t = Real.exp (bgpParams38.cα * t) :=
      sol.alpha_eq_exp selectorSchedule_domain_of_nonneg ht.1
    have hμ : sol.μ t = bgpParams38.cμ * t := by
      rw [sol.mu_eq_linear selectorSchedule_domain_of_nonneg ht.1, sol.μ_at_zero,
        zero_add]
    have hgate : bGateU bgpParams38.L (sol.μ t) t ≤ 1 := by
      rw [hμ]
      exact bGateU_le_one bgpParams38.L
        (mul_nonneg (by norm_num [bgpParams38]) ht.1) t
    have hcoef :
        Real.exp (bgpParams38.cα * t) * bGateU bgpParams38.L (sol.μ t) t
          ≤ Real.exp (50 * Real.pi) := by
      calc
        Real.exp (bgpParams38.cα * t) * bGateU bgpParams38.L (sol.μ t) t
            ≤ Real.exp (bgpParams38.cα * t) * 1 :=
          mul_le_mul_of_nonneg_left hgate (le_of_lt (Real.exp_pos _))
        _ ≤ Real.exp (50 * Real.pi) := by
          rw [mul_one]
          have htα : bgpParams38.cα * t ≤ 50 * Real.pi := by
            have hmul :=
              mul_le_mul_of_nonneg_left ht.2
                (by norm_num [bgpParams38] : (0 : ℝ) ≤ bgpParams38.cα)
            norm_num [bgpParams38] at hmul ⊢
            nlinarith
          exact Real.exp_le_exp.mpr htα
    rw [show bgpParams38.A = 1 by norm_num [bgpParams38], hα, one_mul]
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (le_of_lt (bGateU_pos bgpParams38.L (sol.μ t) t))]
    have hprod := mul_le_mul hcoef hzu (abs_nonneg _) (le_of_lt (Real.exp_pos _))
    nlinarith [hprod]
  have hhold := hold_bound (fun t => sol.u t i)
    (fun t => bgpParams38.A * sol.α t * bGateU bgpParams38.L (sol.μ t) t *
      (sol.z t i - sol.u t i))
    (2 * B * Real.exp (50 * Real.pi)) 0 (Real.pi / 6) hab
    (fun t ht => sol.u_hasDeriv t (selectorSchedule_domain_of_nonneg t ht.1) i)
    hfield
  simpa [sol] using hhold

end Ripple.BoundedUniversality.BGP
