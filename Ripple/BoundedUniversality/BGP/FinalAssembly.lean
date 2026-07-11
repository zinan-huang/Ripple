import Ripple.BoundedUniversality.BGP.ContractMain
import Ripple.BoundedUniversality.BGP.MachineInstance
import Ripple.BoundedUniversality.BGP.ContractSupply
import Ripple.BoundedUniversality.BGP.ContractSchedules
import Ripple.BoundedUniversality.BGP.ContractLatch
import Ripple.BoundedUniversality.BGP.ContractField
import Ripple.BoundedUniversality.BGP.SelectorAtoms

noncomputable section

namespace Ripple.BoundedUniversality.BGP

def bgpParams : DynGateParams where
  A := 1
  L := 1
  cμ := 1
  cα := (1 : ℝ) / 4

def bgpSchedule : PhaseSchedule where
  domain := Set.Ici 0
  cycleStart := fun j => (j : ℝ)
  cycleMid := fun j => (j : ℝ) + (1 : ℝ) / 2
  cycleEnd := fun j => ((j + 1 : ℕ) : ℝ)
  zActiveWindow := fun _ => Set.univ
  stableWindow_subset_zActiveWindow := by
    intro j x hx
    trivial
  cycleEnd_start_next := by
    intro j
    rfl

private theorem bgpParams_A_rat : bgpParams.A = ((1 : ℚ) : ℝ) := by
  norm_num [bgpParams]

private theorem bgpParams_cμ_rat : bgpParams.cμ = ((1 : ℚ) : ℝ) := by
  norm_num [bgpParams]

private theorem bgpParams_cα_rat : bgpParams.cα = ((1 / 4 : ℚ) : ℝ) := by
  norm_num [bgpParams]

private theorem bgpParams_L_eq : bgpParams.L = 1 := by
  rfl

private theorem bgpSchedule_domain_nonneg :
    ∀ t : ℝ, t ∈ bgpSchedule.domain → 0 ≤ t := by
  intro t ht
  exact ht

private theorem bgpSchedule_domain_of_nonneg :
    ∀ t : ℝ, 0 ≤ t → t ∈ bgpSchedule.domain := by
  intro t ht
  exact ht

private theorem bgpSchedule_domain_cover :
    ∀ t ∈ bgpSchedule.domain, ∃ j, t ∈ bgpSchedule.zActiveWindow j := by
  intro t ht
  exact ⟨0, trivial⟩

private theorem bgpParams_A_nonneg : 0 ≤ bgpParams.A := by
  norm_num [bgpParams]

private theorem bgpParams_gate_regime :
    0 < bgpParams.cμ * (1 / 2 : ℝ) ^ bgpParams.L - bgpParams.cα := by
  norm_num [bgpParams]

private abbrev bgpAtoms
    (control : SlabAtomicSelectorData MachineInstance.d_U ℤ)
    (left right : SlabAtomicSelectorData MachineInstance.d_U (Option (Fin 2))) :
    GateSelectorAtoms MachineInstance.d_U :=
  gateSelectorAtomsBernstein control left right

private abbrev bgpStepContract
    (control : SlabAtomicSelectorData MachineInstance.d_U ℤ)
    (left right : SlabAtomicSelectorData MachineInstance.d_U (Option (Fin 2)))
    (epsF : ℝ → Fin MachineInstance.d_U → ℝ) (D : ℝ)
    (hD : 0 ≤ D)
    (hsharp :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          GateAtomSharpness MachineInstance.universalViewSpec
            (bgpAtoms control left right) x (MachineInstance.localViewU c))
    (hdomain :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          (bgpAtoms control left right).inWorkingDomain x)
    (hspread :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ}
        (i : Fin MachineInstance.d_U),
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          BranchSpread MachineInstance.branchU x (MachineInstance.localViewU c) i (epsF mu i))
    (hselector_budget :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ}
        (i : Fin MachineInstance.d_U),
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          selectorEpsTotal (V := MachineInstance.UniversalLocalView)
              (bgpAtoms control left right).errSel (bgpAtoms control left right).errOff
              ((bgpAtoms control left right).errSum MachineInstance.UniversalLocalView)
              (epsF mu i) ≤ epsF mu i)
    (hdisp :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          ∀ i,
            |MachineInstance.selectorContractF_U MachineInstance.branchU
                (bgpAtoms control left right) mu x i - x i| ≤ D) :
    RobustStepContract UniversalMachine.undecidableMachine.toDiscreteMachine
      MachineInstance.stackMachineEncodingU :=
  MachineInstance.robustStepContractU
    MachineInstance.branchU (bgpAtoms control left right) epsF D hD
    MachineInstance.hlocal_unique hsharp hdomain hspread hselector_budget
    MachineInstance.branchU_contract_clause hdisp

private theorem bgpSelectorBudget
    (control : SlabAtomicSelectorData MachineInstance.d_U ℤ)
    (left right : SlabAtomicSelectorData MachineInstance.d_U (Option (Fin 2)))
    (epsF : ℝ → Fin MachineInstance.d_U → ℝ) (δ : ℝ)
    (hcontrol_err : control.err = δ)
    (hleft_err : left.err = δ) (hright_err : right.err = δ)
    (hδ_nonneg : 0 ≤ δ)
    (hepsF_nonneg : ∀ mu i, 0 ≤ epsF mu i)
    (hselector_budget_numeric :
      ∀ mu i,
        (6 + 2 * offViewCount MachineInstance.UniversalLocalView) * δ * epsF mu i ≤
          epsF mu i) :
    ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ}
      (i : Fin MachineInstance.d_U),
      EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
        selectorEpsTotal (V := MachineInstance.UniversalLocalView)
            (bgpAtoms control left right).errSel (bgpAtoms control left right).errOff
            ((bgpAtoms control left right).errSum MachineInstance.UniversalLocalView)
            (epsF mu i) ≤ epsF mu i := by
  intro mu _c _x i _htube
  exact N4_gateSelectorAtomsBernstein_budget_of_uniform_error
    control left right hcontrol_err hleft_err hright_err hδ_nonneg
    (hepsF_nonneg mu i) (hselector_budget_numeric mu i)

private theorem bgpAtomSharpness
    (control : SlabAtomicSelectorData MachineInstance.d_U ℤ)
    (left right : SlabAtomicSelectorData MachineInstance.d_U (Option (Fin 2)))
    (hctrl_on :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x control.coord -
            control.code (MachineInstance.universalViewSpec.q (MachineInstance.localViewU c))| ≤
              (control.rho : ℝ))
    (hleft_on :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x left.coord -
            left.code (MachineInstance.universalViewSpec.leftTop (MachineInstance.localViewU c))| ≤
              (left.rho : ℝ))
    (hright_on :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x right.coord -
            right.code
              (MachineInstance.universalViewSpec.rightTop (MachineInstance.localViewU c))| ≤
              (right.rho : ℝ)) :
    ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
      EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
        GateAtomSharpness MachineInstance.universalViewSpec
          (bgpAtoms control left right) x (MachineInstance.localViewU c) := by
  intro c x htube
  exact N4_gateSelectorAtomsBernstein_sharpness
    MachineInstance.universalViewSpec control left right
    (hctrl_on htube) (hleft_on htube) (hright_on htube)

private theorem bgpWorkingDomain
    (control : SlabAtomicSelectorData MachineInstance.d_U ℤ)
    (left right : SlabAtomicSelectorData MachineInstance.d_U (Option (Fin 2)))
    (hcontrol_domain :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x control.coord| ≤ (control.C : ℝ))
    (hleft_domain :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x left.coord| ≤ (left.C : ℝ))
    (hright_domain :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x right.coord| ≤ (right.C : ℝ)) :
    ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
      EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
        (bgpAtoms control left right).inWorkingDomain x := by
  intro c x htube
  exact N4_gateSelectorAtomsBernstein_inWorkingDomain control left right
    (hcontrol_domain htube) (hleft_domain htube) (hright_domain htube)

private abbrev bgpStepContractN4
    (control : SlabAtomicSelectorData MachineInstance.d_U ℤ)
    (left right : SlabAtomicSelectorData MachineInstance.d_U (Option (Fin 2)))
    (epsF : ℝ → Fin MachineInstance.d_U → ℝ) (δ : ℝ)
    (hcontrol_err : control.err = δ)
    (hleft_err : left.err = δ) (hright_err : right.err = δ)
    (hδ_nonneg : 0 ≤ δ)
    (hepsF_nonneg : ∀ mu i, 0 ≤ epsF mu i)
    (hselector_budget_numeric :
      ∀ mu i,
        (6 + 2 * offViewCount MachineInstance.UniversalLocalView) * δ * epsF mu i ≤
          epsF mu i)
    (hctrl_on :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x control.coord -
            control.code (MachineInstance.universalViewSpec.q (MachineInstance.localViewU c))| ≤
              (control.rho : ℝ))
    (hleft_on :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x left.coord -
            left.code (MachineInstance.universalViewSpec.leftTop (MachineInstance.localViewU c))| ≤
              (left.rho : ℝ))
    (hright_on :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x right.coord -
            right.code
              (MachineInstance.universalViewSpec.rightTop (MachineInstance.localViewU c))| ≤
              (right.rho : ℝ))
    (hcontrol_domain :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x control.coord| ≤ (control.C : ℝ))
    (hleft_domain :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x left.coord| ≤ (left.C : ℝ))
    (hright_domain :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x right.coord| ≤ (right.C : ℝ))
    (hspread :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ}
        (i : Fin MachineInstance.d_U),
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          BranchSpread MachineInstance.branchU x (MachineInstance.localViewU c) i (epsF mu i))
    (hdisp :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          ∀ i,
            |MachineInstance.selectorContractF_U MachineInstance.branchU
                (bgpAtoms control left right) mu x i - x i| ≤ MachineInstance.D_U) :
    RobustStepContract UniversalMachine.undecidableMachine.toDiscreteMachine
      MachineInstance.stackMachineEncodingU :=
  bgpStepContract control left right epsF MachineInstance.D_U MachineInstance.D_U_nonneg
    (bgpAtomSharpness control left right hctrl_on hleft_on hright_on)
    (bgpWorkingDomain control left right hcontrol_domain hleft_domain hright_domain)
    hspread
    (bgpSelectorBudget control left right epsF δ hcontrol_err hleft_err hright_err
      hδ_nonneg hepsF_nonneg hselector_budget_numeric)
    hdisp

private def bgpEpsSchedule : ℝ → Fin MachineInstance.d_U → ℝ :=
  fun mu _ => Real.exp (-mu)

/-- Public alias for the exponential eps schedule `fun mu _ => exp (-mu)` used by
the assembled warmed step `bgpStepContractExp_N_assembled`.  Exposed so the
downstream warmed-headline instantiation can state the `hspread`/`hdisp`
hypotheses (which mention this schedule) outside this file. -/
@[reducible] def bgpEpsScheduleU : ℝ → Fin MachineInstance.d_U → ℝ :=
  fun mu _ => Real.exp (-mu)

theorem bgpEpsScheduleU_eq : bgpEpsScheduleU = bgpEpsSchedule := rfl

private theorem bgpEpsSchedule_pos :
    ∀ mu i, 0 < bgpEpsSchedule mu i := by
  intro mu i
  exact Real.exp_pos _

private theorem bgpEpsSchedule_nonneg :
    ∀ mu i, 0 ≤ bgpEpsSchedule mu i := by
  intro mu i
  exact (bgpEpsSchedule_pos mu i).le

private theorem bgpEpsSchedule_selectorBudget (δ : ℝ)
    (hδ_budget :
      (6 + 2 * offViewCount MachineInstance.UniversalLocalView) * δ ≤ 1) :
    ∀ mu i,
      (6 + 2 * offViewCount MachineInstance.UniversalLocalView) * δ *
          bgpEpsSchedule mu i ≤
        bgpEpsSchedule mu i := by
  intro mu i
  have hmul :=
    mul_le_mul_of_nonneg_right hδ_budget (bgpEpsSchedule_nonneg mu i)
  calc
    (6 + 2 * offViewCount MachineInstance.UniversalLocalView) * δ *
        bgpEpsSchedule mu i
        = ((6 + 2 * offViewCount MachineInstance.UniversalLocalView) * δ) *
            bgpEpsSchedule mu i := by ring
    _ ≤ 1 * bgpEpsSchedule mu i := hmul
    _ = bgpEpsSchedule mu i := by ring

private def bgpSelectorScale : ℝ :=
  (6 : ℝ) + 2 * (offViewCount MachineInstance.UniversalLocalView : ℝ)

private def bgpSelectorDelta : ℝ :=
  1 / (bgpSelectorScale + 1)

private theorem bgpSelectorDelta_budget :
    ((6 : ℝ) + 2 * (offViewCount MachineInstance.UniversalLocalView : ℝ)) *
        bgpSelectorDelta ≤ 1 := by
  have hscale_nonneg : 0 ≤ bgpSelectorScale := by
    have hoff : 0 ≤ offViewCount MachineInstance.UniversalLocalView := by
      simp [offViewCount]
    unfold bgpSelectorScale
    nlinarith
  have hdenpos : 0 < bgpSelectorScale + 1 := by
    linarith
  have hle : bgpSelectorScale ≤ bgpSelectorScale + 1 := by
    linarith
  change bgpSelectorScale * (1 / (bgpSelectorScale + 1)) ≤ 1
  rw [mul_one_div]
  exact (div_le_one hdenpos).mpr hle

private theorem bgpSelectorDelta_budget_of_control_err
    (control : SlabAtomicSelectorData MachineInstance.d_U ℤ)
    (hcontrol_err : control.err = bgpSelectorDelta) :
    (6 + 2 * offViewCount MachineInstance.UniversalLocalView) *
        control.err ≤ 1 := by
  rw [hcontrol_err]
  exact bgpSelectorDelta_budget

private abbrev bgpStepContractExp
    (control : SlabAtomicSelectorData MachineInstance.d_U ℤ)
    (left right : SlabAtomicSelectorData MachineInstance.d_U (Option (Fin 2)))
    (hδ_budget :
      (6 + 2 * offViewCount MachineInstance.UniversalLocalView) * control.err ≤ 1)
    (hleft_err : left.err = control.err) (hright_err : right.err = control.err)
    (hctrl_on :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x control.coord -
            control.code (MachineInstance.universalViewSpec.q (MachineInstance.localViewU c))| ≤
              (control.rho : ℝ))
    (hleft_on :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x left.coord -
            left.code (MachineInstance.universalViewSpec.leftTop (MachineInstance.localViewU c))| ≤
              (left.rho : ℝ))
    (hright_on :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x right.coord -
            right.code
              (MachineInstance.universalViewSpec.rightTop (MachineInstance.localViewU c))| ≤
              (right.rho : ℝ))
    (hcontrol_domain :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x control.coord| ≤ (control.C : ℝ))
    (hleft_domain :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x left.coord| ≤ (left.C : ℝ))
    (hright_domain :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x right.coord| ≤ (right.C : ℝ))
    (hspread :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ}
        (i : Fin MachineInstance.d_U),
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          BranchSpread MachineInstance.branchU x (MachineInstance.localViewU c) i
            (bgpEpsSchedule mu i))
    (hdisp :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          ∀ i,
            |MachineInstance.selectorContractF_U MachineInstance.branchU
                (bgpAtoms control left right) mu x i - x i| ≤ MachineInstance.D_U) :
    RobustStepContract UniversalMachine.undecidableMachine.toDiscreteMachine
      MachineInstance.stackMachineEncodingU :=
  bgpStepContractN4 control left right bgpEpsSchedule control.err rfl hleft_err hright_err
    control.err_nonneg bgpEpsSchedule_nonneg (bgpEpsSchedule_selectorBudget control.err hδ_budget)
    hctrl_on hleft_on hright_on hcontrol_domain hleft_domain hright_domain
    hspread hdisp

private theorem bgpSupply
    (S : RobustStepContract UniversalMachine.undecidableMachine.toDiscreteMachine
      MachineInstance.stackMachineEncodingU)
    (R : ℕ)
    (FP : Fin MachineInstance.d_U → MvPolynomial (Fin (contractDim MachineInstance.d_U)) ℚ)
    (HP : MvPolynomial (Fin MachineInstance.d_U) ℚ)
    (y₀ : ℕ → Fin (contractDim MachineInstance.d_U) → ℝ)
    (Mbound : ℝ) (hMbound : 0 < Mbound)
    (h_invariant :
      ∀ w : ℕ, ∀ T : ℝ, 0 < T →
        ∀ y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ,
          y 0 = y₀ w →
          (∀ t ∈ Set.Ico (0 : ℝ) T,
            HasDerivAt y
              (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
                (contractAssembledField MachineInstance.d_U FP HP
                  (1 : ℚ) (1 : ℚ) (1 : ℚ) (1 / 4 : ℚ) 1 R i)) t) →
          ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t‖ ≤ Mbound)
    (hgateZ :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ),
        ∀ t : ℝ, 0 ≤ t →
          y t (contractGateZ MachineInstance.d_U) =
            bGateZ 1 (y t (contractMu MachineInstance.d_U)) t)
    (hgateU :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ),
        ∀ t : ℝ, 0 ≤ t →
          y t (contractGateU MachineInstance.d_U) =
            bGateU 1 (y t (contractMu MachineInstance.d_U)) t)
    (field_eval_identity :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ),
        ∀ t : ℝ, 0 ≤ t → ∀ i : Fin MachineInstance.d_U,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (FP i) =
            S.F (y t (contractMu MachineInstance.d_U)) (fun k => y t (contractU k)) i)
    (hbox :
      ∀ (w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ)
        (hyode : ∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
              (contractAssembledField MachineInstance.d_U FP HP
                (1 : ℚ) (1 : ℚ) (1 : ℚ) (1 / 4 : ℚ) 1 R i)) t)
        (hycont : Continuous y),
        ContractPerCycleBoxBounds MachineInstance.stackMachineEncodingU
          (dynContractIteratorSol_of_contractAssembledField_solution
            (E := MachineInstance.stackMachineEncodingU) (S := S)
            (p := bgpParams) (sched := bgpSchedule)
            FP HP bgpParams_A_rat bgpParams_cμ_rat bgpParams_cα_rat
            bgpParams_L_eq bgpSchedule_domain_nonneg y hyode hycont
            (hgateZ w y) (hgateU w y) (field_eval_identity w y))
          w MachineInstance.D_U) :
    ∀ w : ℕ,
      ∃ sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule S.F,
        ContractPerCycleBox MachineInstance.stackMachineEncodingU sol w MachineInstance.D_U :=
  contract_supply_of_polynomial_field
    MachineInstance.stackMachineEncodingU S bgpParams bgpSchedule FP HP
    (Aq := (1 : ℚ)) (Kq := (1 : ℚ)) (cμq := (1 : ℚ)) (cαq := (1 / 4 : ℚ))
    (L := 1) (R := R)
    bgpParams_A_rat bgpParams_cμ_rat bgpParams_cα_rat bgpParams_L_eq
    bgpSchedule_domain_nonneg y₀ Mbound hMbound MachineInstance.D_U
    h_invariant hgateZ hgateU field_eval_identity hbox

private theorem bgpLatch
    (S : RobustStepContract UniversalMachine.undecidableMachine.toDiscreteMachine
      MachineInstance.stackMachineEncodingU)
    (R : ℕ)
    (hHcont :
      ∀ sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule S.F,
        Continuous fun t => MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t))
    (hhigh :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule S.F)
        (La : ContractHaltLatchSol (p := bgpParams) (sched := bgpSchedule) (F := S.F)
          sol MachineInstance.contractFlagIndicatorPackageU.Hval MachineInstance.K_U R),
        (∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ bgpSchedule.zActiveWindow j,
          1 - MachineInstance.contractFlagIndicatorPackageU.eta ≤
            MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t)) →
          ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1)
    (hlow :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule S.F)
        (La : ContractHaltLatchSol (p := bgpParams) (sched := bgpSchedule) (F := S.F)
          sol MachineInstance.contractFlagIndicatorPackageU.Hval MachineInstance.K_U R),
        (∀ j : ℕ, ∀ t ∈ bgpSchedule.zActiveWindow j,
          MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t) ≤
            MachineInstance.contractFlagIndicatorPackageU.eta) →
          ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4) :
    ∀ sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule S.F,
      ∃ La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R,
        ContractLatchConvergenceKernel sol MachineInstance.haltCoordU
          MachineInstance.contractFlagIndicatorPackageU La :=
  hlatch_adapter MachineInstance.contractFlagIndicatorPackageU
    MachineInstance.K_U_pos hHcont hhigh hlow

private def bgpFieldPkg
    (S : RobustStepContract UniversalMachine.undecidableMachine.toDiscreteMachine
      MachineInstance.stackMachineEncodingU)
    (R : ℕ)
    (FP : Fin MachineInstance.d_U → MvPolynomial (Fin (contractDim MachineInstance.d_U)) ℚ)
    (HP : MvPolynomial (Fin MachineInstance.d_U) ℚ)
    (field_eval_identity :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule S.F)
        (La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (t : ℝ), 0 ≤ t → ∀ i : Fin MachineInstance.d_U,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t) (FP i) =
            S.F (sol.μ t) (sol.u t) i)
    (indicator_eval_identity :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule S.F)
        (_La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (t : ℝ),
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) HP =
            MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t))
    (init : ℕ → Fin (contractDim MachineInstance.d_U + 1) → ℚ)
    (init_presented : ∃ f : ℕ → Fin (contractDim MachineInstance.d_U + 1) → ℤ × ℕ,
      Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule S.F)
        (La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R),
          ((init w 0 : ℚ) : ℝ) =
            ((∑ i : Fin (contractDim MachineInstance.d_U), contractTupleTraj sol La 0 i ^ 2) - 1) /
              ((∑ i : Fin (contractDim MachineInstance.d_U), contractTupleTraj sol La 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule S.F)
        (La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (i : Fin (contractDim MachineInstance.d_U)),
          ((init w i.succ : ℚ) : ℝ) =
            2 * contractTupleTraj sol La 0 i /
              ((∑ k : Fin (contractDim MachineInstance.d_U),
                contractTupleTraj sol La 0 k ^ 2) + 1)) :
    ContractPolynomialFieldPackage UniversalMachine.undecidableMachine
      MachineInstance.stackMachineEncodingU S bgpParams bgpSchedule MachineInstance.haltCoordU
      MachineInstance.contractFlagIndicatorPackageU MachineInstance.K_U R :=
  contractPolynomialFieldPackage
    UniversalMachine.undecidableMachine MachineInstance.stackMachineEncodingU S
    bgpParams bgpSchedule MachineInstance.haltCoordU
    MachineInstance.contractFlagIndicatorPackageU
    FP HP (1 : ℚ) (1 : ℚ) (1 : ℚ) (1 / 4 : ℚ) 1
    bgpParams_A_rat (by norm_num [MachineInstance.K_U])
    bgpParams_cμ_rat bgpParams_cα_rat bgpParams_L_eq
    bgpSchedule_domain_of_nonneg field_eval_identity indicator_eval_identity
    init init_presented init_zero init_succ

/--
Correct-shape BGP headline assembly.

This is the public entry point that should be used instead of trying to
discharge the older `bgp_unconditional_*` wrappers.  It deliberately does not
construct the selector `RobustStepContract`, does not use a uniform all-time
`Mbound` supply hypothesis, and does not fix the hard-step indicator.  Those
facts must be supplied in the shape in which the later contract machinery
actually consumes them:

* `S` is an already valid step contract.
* `I` is the indicator package used by the latch and polynomial field package
  (for Paper 3 this should be the ramp indicator).
* `hsupply` supplies the actual ODE solution and its per-cycle box witness.
* `htracking_inputs` is restricted to those supplied solutions and boxes.
-/
theorem bgp_headline_of_contract_data
    (S : RobustStepContract UniversalMachine.undecidableMachine.toDiscreteMachine
      MachineInstance.stackMachineEncodingU)
    (I : ContractFlagIndicatorPackage MachineInstance.haltCoordU)
    {K : ℝ} {R : ℕ} (hK : 0 < K)
    (η :
      DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule S.F →
        ℕ → Fin MachineInstance.d_U → ℝ)
    (W : ℕ → ℕ → Fin MachineInstance.d_U → ℝ)
    (depth : ℕ → ℕ → Fin MachineInstance.d_U → ℤ)
    (hsupply :
      ∀ w : ℕ,
        ∃ sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule S.F,
          ContractPerCycleBox MachineInstance.stackMachineEncodingU sol w MachineInstance.D_U)
    (htracking_inputs :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule S.F),
        ContractPerCycleBox MachineInstance.stackMachineEncodingU sol w MachineInstance.D_U →
          ContractTrackingInputs S bgpParams bgpSchedule sol
            (fun j =>
              UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
                (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
            (kappaSchedule bgpParams) (chiSchedule bgpParams)
            MachineInstance.rLE_constU
            (MachineInstance.ampU fun j =>
              UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
                (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
            (η sol) (W w) (depth w)
            (contractMovingBox
              (contractOrbit MachineInstance.stackMachineEncodingU w)
              MachineInstance.D_U bgpSchedule)
            MachineInstance.haltCoordU)
    (hlatch :
      ∀ sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule S.F,
        ∃ La : ContractHaltLatchSol sol I.Hval K R,
          ContractLatchConvergenceKernel sol MachineInstance.haltCoordU I La)
    (hflag_margin_all :
      ∀ sol j, η sol j MachineInstance.haltCoordU ≤
        MachineInstance.haltFlagPackageU.flagMargin)
    (hflag_domain :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule S.F)
        (_box : ContractPerCycleBox MachineInstance.stackMachineEncodingU sol w
          MachineInstance.D_U),
        ∀ j t, t ∈ bgpSchedule.zActiveWindow j →
          sol.z t MachineInstance.haltCoordU ∈ Set.Icc (0 : ℝ) 1)
    (fieldPkg :
      ContractPolynomialFieldPackage UniversalMachine.undecidableMachine
        MachineInstance.stackMachineEncodingU S bgpParams bgpSchedule
        MachineInstance.haltCoordU I K R) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  main_assembled_dyn_contract
    UniversalMachine.undecidableMachine
    MachineInstance.stackMachineEncodingU
    S bgpParams bgpSchedule
    MachineInstance.haltCoordU
    MachineInstance.haltFlagPackageU
    I hK
    (kappaSchedule bgpParams) (chiSchedule bgpParams)
    MachineInstance.rLE_constU
    (fun w => MachineInstance.ampU fun j =>
      UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
        (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
    η W depth
    (fun w =>
      contractMovingBox (contractOrbit MachineInstance.stackMachineEncodingU w)
        MachineInstance.D_U bgpSchedule)
    MachineInstance.D_U
    hsupply
    htracking_inputs
    hlatch
    hflag_margin_all
    MachineInstance.haltFlagPackageU.margin_le_quarter
    hflag_domain
    fieldPkg

/--
Correct-shape BGP headline with solution-specific producer data.

This is the hypothesis-shape-correct variant for the contract route: for each
input word, the same supplied ODE solution carries its box witness, tracking
inputs, latch kernel, flag-margin bound, and flag-domain invariant.  In
particular, none of these downstream facts is quantified over arbitrary
solutions of the assembled ODE.
-/
theorem bgp_headline_of_rich_contract_data
    (S : RobustStepContract UniversalMachine.undecidableMachine.toDiscreteMachine
      MachineInstance.stackMachineEncodingU)
    (I : ContractFlagIndicatorPackage MachineInstance.haltCoordU)
    {K : ℝ} {R : ℕ} (hK : 0 < K)
    (η :
      DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule S.F →
        ℕ → Fin MachineInstance.d_U → ℝ)
    (W : ℕ → ℕ → Fin MachineInstance.d_U → ℝ)
    (depth : ℕ → ℕ → Fin MachineInstance.d_U → ℤ)
    (hsupply_rich :
      ∀ w : ℕ,
        ∃ sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule S.F,
        ∃ _box : ContractPerCycleBox MachineInstance.stackMachineEncodingU sol w
          MachineInstance.D_U,
          ContractTrackingInputs S bgpParams bgpSchedule sol
            (fun j =>
              UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
                (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
            (kappaSchedule bgpParams) (chiSchedule bgpParams)
            MachineInstance.rLE_constU
            (MachineInstance.ampU fun j =>
              UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
                (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
            (η sol) (W w) (depth w)
            (contractMovingBox
              (contractOrbit MachineInstance.stackMachineEncodingU w)
              MachineInstance.D_U bgpSchedule)
            MachineInstance.haltCoordU ∧
          (∃ La : ContractHaltLatchSol sol I.Hval K R,
            ContractLatchConvergenceKernel sol MachineInstance.haltCoordU I La) ∧
          (∀ j, η sol j MachineInstance.haltCoordU ≤
            MachineInstance.haltFlagPackageU.flagMargin) ∧
          (∀ j t, t ∈ bgpSchedule.zActiveWindow j →
            sol.z t MachineInstance.haltCoordU ∈ Set.Icc (0 : ℝ) 1))
    (fieldPkg :
      ContractPolynomialFieldPackage UniversalMachine.undecidableMachine
        MachineInstance.stackMachineEncodingU S bgpParams bgpSchedule
        MachineInstance.haltCoordU I K R) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  main_assembled_dyn_contract_rich_supply
    UniversalMachine.undecidableMachine
    MachineInstance.stackMachineEncodingU
    S bgpParams bgpSchedule
    MachineInstance.haltCoordU
    MachineInstance.haltFlagPackageU
    I hK
    (kappaSchedule bgpParams) (chiSchedule bgpParams)
    MachineInstance.rLE_constU
    (fun w => MachineInstance.ampU fun j =>
      UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
        (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
    η W depth
    (fun w =>
      contractMovingBox (contractOrbit MachineInstance.stackMachineEncodingU w)
        MachineInstance.D_U bgpSchedule)
    MachineInstance.D_U
    hsupply_rich
    MachineInstance.haltFlagPackageU.margin_le_quarter
    fieldPkg

#print axioms bgp_headline_of_rich_contract_data

private theorem bgpTrackingInputs
    (S : RobustStepContract UniversalMachine.undecidableMachine.toDiscreteMachine
      MachineInstance.stackMachineEncodingU)
    (w : ℕ)
    (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule S.F)
    (box : ContractPerCycleBox MachineInstance.stackMachineEncodingU sol w MachineInstance.D_U)
    (amp W : ℕ → Fin MachineInstance.d_U → ℝ)
    (depth : ℕ → Fin MachineInstance.d_U → ℤ)
    (hamp_stack :
      ∀ j s, amp j (MachineInstance.stackMachineEncodingU.stackCoord s) =
        (MachineInstance.stackMachineEncodingU.k : ℝ) ^
          MachineInstance.stackMachineEncodingU.stackDelta
            ((fun j =>
              UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
                (UniversalMachine.undecidableMachine.toDiscreteMachine.init w)) j) s)
    (hamp_reset :
      ∀ j i, MachineInstance.stackMachineEncodingU.coordStackIndex i = none →
        amp j i = 0)
    (hmu_large :
      ∀ j t, t ∈ bgpSchedule.zActiveWindow j → S.mu_min ≤ sol.μ t)
    (heps_mono :
      ∀ i {mu0 mu1 : ℝ}, mu0 ≤ mu1 → S.epsF mu1 i ≤ S.epsF mu0 i)
    (hinit_weighted :
      ContractWeightedBound (E := MachineInstance.stackMachineEncodingU) sol
        (fun j =>
          UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
            (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
        depth W 0)
    (hhold_slack :
      ∀ j,
        ContractWeightedBound (E := MachineInstance.stackMachineEncodingU) sol
          (fun j =>
            UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
              (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
          depth W j →
          ∀ i,
            contractBoundaryError (E := MachineInstance.stackMachineEncodingU) sol
                (fun j =>
                  UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
                    (UniversalMachine.undecidableMachine.toDiscreteMachine.init w)) j i +
              chiSchedule bgpParams j * S.D ≤ MachineInstance.rLE_constU i)
    (hwindow_hold :
      ∀ j t, t ∈ bgpSchedule.zActiveWindow j → ∀ i,
        |sol.u t i -
            MachineInstance.stackMachineEncodingU.enc
              ((fun j =>
                UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
                  (UniversalMachine.undecidableMachine.toDiscreteMachine.init w)) j) i| ≤
          contractBoundaryError (E := MachineInstance.stackMachineEncodingU) sol
              (fun j =>
                UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
                  (UniversalMachine.undecidableMachine.toDiscreteMachine.init w)) j i +
            chiSchedule bgpParams j * S.D)
    (hz_window_hold :
      ∀ j t, t ∈ bgpSchedule.zActiveWindow j → ∀ i,
        |sol.z t i -
            MachineInstance.stackMachineEncodingU.enc
              ((fun j =>
                UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
                  (UniversalMachine.undecidableMachine.toDiscreteMachine.init w)) j) i| ≤
          contractBoundaryError (E := MachineInstance.stackMachineEncodingU) sol
              (fun j =>
                UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
                  (UniversalMachine.undecidableMachine.toDiscreteMachine.init w)) j i +
            chiSchedule bgpParams j * S.D)
    (hflag_z_read_window_bridge :
      ∀ j t, t ∈ bgpSchedule.zActiveWindow j →
        |sol.z t MachineInstance.haltCoordU -
            MachineInstance.stackMachineEncodingU.enc
              ((fun j =>
                UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
                  (UniversalMachine.undecidableMachine.toDiscreteMachine.init w)) j)
              MachineInstance.haltCoordU| ≤
          contractBoundaryError (E := MachineInstance.stackMachineEncodingU) sol
            (fun j =>
              UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
                (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
            (j + 1) MachineInstance.haltCoordU)
    (hrLE_radius :
      ∀ j t, t ∈ bgpSchedule.zActiveWindow j → ∀ i,
        MachineInstance.rLE_constU i ≤ S.radius (sol.μ t))
    (hrecurrence_of_branch :
      ∀ j,
        ContractWeightedBound (E := MachineInstance.stackMachineEncodingU) sol
          (fun j =>
            UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
              (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
          depth W j →
        ContractWindowTube (E := MachineInstance.stackMachineEncodingU) sol
          (fun j =>
            UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
              (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
          MachineInstance.rLE_constU j →
        ContractBranchLocked (E := MachineInstance.stackMachineEncodingU) S sol
          (fun j =>
            UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
              (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
          j →
        ContractRecurrenceAt (E := MachineInstance.stackMachineEncodingU) sol
          (fun j =>
            UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
              (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
          amp (contractEtaSchedule S bgpParams bgpSchedule sol) j)
    (hweighted_step :
      ∀ j,
        ContractWeightedBound (E := MachineInstance.stackMachineEncodingU) sol
          (fun j =>
            UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
              (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
          depth W j →
        ContractRecurrenceAt (E := MachineInstance.stackMachineEncodingU) sol
          (fun j =>
            UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
              (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
          amp (contractEtaSchedule S bgpParams bgpSchedule sol) j →
        ContractWeightedBound (E := MachineInstance.stackMachineEncodingU) sol
          (fun j =>
            UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
              (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
          depth W (j + 1)) :
    ContractTrackingInputs S bgpParams bgpSchedule sol
      (fun j =>
        UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
          (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
      (kappaSchedule bgpParams) (chiSchedule bgpParams) MachineInstance.rLE_constU
      amp (contractEtaSchedule S bgpParams bgpSchedule sol) W depth
      (contractMovingBox (contractOrbit MachineInstance.stackMachineEncodingU w)
        MachineInstance.D_U bgpSchedule)
      MachineInstance.haltCoordU :=
  contract_tracking_inputs_assemble
    MachineInstance.stackMachineEncodingU S bgpParams bgpSchedule w sol
    MachineInstance.D_U box MachineInstance.rLE_constU amp W depth
    MachineInstance.haltCoordU bgpParams_A_nonneg bgpParams_gate_regime
    hamp_stack hamp_reset hmu_large heps_mono hinit_weighted hhold_slack
    hwindow_hold hz_window_hold hflag_z_read_window_bridge hrLE_radius
    hrecurrence_of_branch hweighted_step bgpSchedule_domain_cover

/-! ### N-atom assembled contract (selector premises discharged) -/

private theorem selectorEpsTotalN_budget {V : Type} [Fintype V] {d n : ℕ}
    (A : GateSelectorAtomsN d n) {spread theta : ℝ}
    (hb : (2 + 2 * offViewCount V) * A.errSel * spread ≤ theta) :
    selectorEpsTotal (V := V) A.errSel A.errSel (A.errSum V) spread ≤ theta := by
  unfold selectorEpsTotal selectorReassemblyCoeff GateSelectorAtomsN.errSum
  nlinarith [hb]

/--
Fully assembled N-atom robust-step contract for the universal machine.  The
selector sharpness and working-domain obligations are discharged internally by
`universalGateAtoms_sharpness` / `universalGateAtoms_inWorkingDomain`; only the
genuine analytic obligations (branch spread, selector budget, displacement)
remain.
-/
def bgpStepContractN_assembled
    (eta : ℚ) (heta : 0 < eta)
    (epsF : ℝ → Fin MachineInstance.d_U → ℝ)
    (hselector_budget_numeric :
      ∀ mu i,
        (2 + 2 * offViewCount MachineInstance.UniversalLocalView) *
            (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel *
            epsF mu i ≤ epsF mu i)
    (hspread :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ}
        (i : Fin MachineInstance.d_U),
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          BranchSpread MachineInstance.branchU x (MachineInstance.localViewU c) i (epsF mu i))
    (hdisp :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x → ∀ i,
          |MachineInstance.selectorContractF_N_U MachineInstance.branchU
              (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta))
              mu x i - x i| ≤ MachineInstance.D_U) :
    RobustStepContract MachineInstance.M_U MachineInstance.stackMachineEncodingU :=
  MachineInstance.robustStepContractN_U MachineInstance.branchU
    (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta))
    epsF MachineInstance.D_U MachineInstance.D_U_nonneg
    MachineInstance.hlocal_unique
    (fun {_c _x} htube =>
      MachineInstance.universalGateAtoms_sharpness eta heta
        (by simpa [EncodingTube, MachineInstance.stackMachineEncodingU] using htube))
    (fun {_c _x} htube =>
      MachineInstance.universalGateAtoms_inWorkingDomain eta heta
        (by simpa [EncodingTube, MachineInstance.stackMachineEncodingU] using htube))
    hspread
    (fun {_mu _c _x} i _htube =>
      selectorEpsTotalN_budget _ (hselector_budget_numeric _ i))
    MachineInstance.branchU_contract_clause
    hdisp

/--
Shape-correct N-atom robust-step contract for the universal machine.  The
branch-spread radius is independent from the target diagonal error `epsF`.
-/
def bgpStepContractN_assembled_withSpread
    (eta : ℚ) (heta : 0 < eta)
    (epsF spread : ℝ → Fin MachineInstance.d_U → ℝ)
    (hselector_budget_numeric :
      ∀ mu i,
        (2 + 2 * offViewCount MachineInstance.UniversalLocalView) *
            (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel *
            spread mu i ≤ epsF mu i)
    (hspread :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ}
        (i : Fin MachineInstance.d_U),
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          BranchSpread MachineInstance.branchU x (MachineInstance.localViewU c) i
            (spread mu i))
    (hdisp :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x → ∀ i,
          |MachineInstance.selectorContractF_N_U MachineInstance.branchU
              (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta))
              mu x i - x i| ≤ MachineInstance.D_U) :
    RobustStepContract MachineInstance.M_U MachineInstance.stackMachineEncodingU :=
  MachineInstance.robustStepContractN_U_withSpread MachineInstance.branchU
    (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta))
    epsF spread MachineInstance.D_U MachineInstance.D_U_nonneg
    MachineInstance.hlocal_unique
    (fun {_c _x} htube =>
      MachineInstance.universalGateAtoms_sharpness eta heta
        (by simpa [EncodingTube, MachineInstance.stackMachineEncodingU] using htube))
    (fun {_c _x} htube =>
      MachineInstance.universalGateAtoms_inWorkingDomain eta heta
        (by simpa [EncodingTube, MachineInstance.stackMachineEncodingU] using htube))
    hspread
    (fun {_mu _c _x} i _htube =>
      selectorEpsTotalN_budget _ (hselector_budget_numeric _ i))
    MachineInstance.branchU_contract_clause
    hdisp

/--
Exponential-schedule N-atom assembled contract: `bgpStepContractN_assembled`
specialized to `epsF = bgpEpsSchedule`, with the clean budget
`(2 + 2·off)·errSel ≤ 1`.  Selector sharpness/domain discharged internally.
-/
def bgpStepContractExp_N_assembled
    (eta : ℚ) (heta : 0 < eta)
    (hδ_budget :
      (2 + 2 * offViewCount MachineInstance.UniversalLocalView) *
          (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel ≤ 1)
    (hspread :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ}
        (i : Fin MachineInstance.d_U),
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          BranchSpread MachineInstance.branchU x (MachineInstance.localViewU c) i
            (bgpEpsSchedule mu i))
    (hdisp :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x → ∀ i,
          |MachineInstance.selectorContractF_N_U MachineInstance.branchU
              (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta))
              mu x i - x i| ≤ MachineInstance.D_U) :
    RobustStepContract MachineInstance.M_U MachineInstance.stackMachineEncodingU :=
  bgpStepContractN_assembled eta heta bgpEpsSchedule
    (fun mu i => mul_le_of_le_one_left (bgpEpsSchedule_nonneg mu i) hδ_budget)
    hspread hdisp

/-- Constant selector-error envelope used by the shape-correct deep headline. -/
@[reducible] def bgpConstEpsF4DU : ℝ → Fin MachineInstance.d_U → ℝ :=
  fun _ _ => 4 * MachineInstance.D_U

theorem bgpConstEpsF4DU_nonneg :
    ∀ mu i, 0 ≤ bgpConstEpsF4DU mu i := by
  intro mu i
  have hD := MachineInstance.D_U_nonneg
  simp [bgpConstEpsF4DU]
  nlinarith

theorem bgpConstEpsF4DU_selectorBudget
    (eta : ℚ) (heta : 0 < eta)
    (hδ_budget :
      (2 + 2 * offViewCount MachineInstance.UniversalLocalView) *
          (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel ≤ 1) :
    ∀ mu i,
      (2 + 2 * offViewCount MachineInstance.UniversalLocalView) *
          (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel *
          bgpConstEpsF4DU mu i ≤
        bgpConstEpsF4DU mu i := by
  intro mu i
  have hmul :=
    mul_le_mul_of_nonneg_right hδ_budget (bgpConstEpsF4DU_nonneg mu i)
  calc
    (2 + 2 * offViewCount MachineInstance.UniversalLocalView) *
          (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel *
          bgpConstEpsF4DU mu i
        =
          ((2 + 2 * offViewCount MachineInstance.UniversalLocalView) *
            (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel) *
            bgpConstEpsF4DU mu i := by ring
    _ ≤ 1 * bgpConstEpsF4DU mu i := hmul
    _ = bgpConstEpsF4DU mu i := by ring

theorem bgpConstEpsF4DU_spread :
    ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ}
      (i : Fin MachineInstance.d_U),
      EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
        BranchSpread MachineInstance.branchU x (MachineInstance.localViewU c) i
          (bgpConstEpsF4DU mu i) := by
  intro mu c x i htube
  simpa [bgpConstEpsF4DU] using
    MachineInstance.branchU_BranchSpread_four_D_U htube i

theorem bgpConstEpsF4DU_selectorBudget_one
    (eta : ℚ) (heta : 0 < eta)
    (hδ_budget :
      (2 + 2 * offViewCount MachineInstance.UniversalLocalView) *
          (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel *
          (4 * MachineInstance.D_U) ≤ 1) :
    ∀ mu i,
      (2 + 2 * offViewCount MachineInstance.UniversalLocalView) *
          (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel *
          bgpConstEpsF4DU mu i ≤ (1 : ℝ) := by
  intro mu i
  simpa [bgpConstEpsF4DU] using hδ_budget

theorem bgpConstEpsF4DU_displacementBound
    (eta : ℚ) (heta : 0 < eta)
    (hδ_budget :
      (2 + 2 * offViewCount MachineInstance.UniversalLocalView) *
          (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel *
          (4 * MachineInstance.D_U) ≤ 1) :
    ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
      EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x → ∀ i,
        |MachineInstance.selectorContractF_N_U MachineInstance.branchU
            (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta))
            mu x i - x i| ≤ MachineInstance.D_U := by
  intro mu c x htube i
  have hutube :
      MachineInstance.UTube MachineInstance.r_LE_U c x := by
    simpa [EncodingTube, MachineInstance.stackMachineEncodingU] using htube
  have hselector_one :
      selectorEpsTotal (V := MachineInstance.UniversalLocalView)
          (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel
          (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel
          ((gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSum
            MachineInstance.UniversalLocalView)
          (bgpConstEpsF4DU mu i) ≤ (1 : ℝ) :=
    selectorEpsTotalN_budget _
      ((bgpConstEpsF4DU_selectorBudget_one eta heta hδ_budget) mu i)
  have hcoord := MachineInstance.gate_selector_robust_coord_clause_N_U
    (branch := MachineInstance.branchU)
    (atoms := gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta))
    (Z := x) (c := c) (i := i)
    (spread := bgpConstEpsF4DU mu i) (theta := (1 : ℝ))
    (MachineInstance.universalGateAtoms_inWorkingDomain eta heta hutube)
    (MachineInstance.universalGateAtoms_sharpness eta heta hutube)
    hselector_one
    (bgpConstEpsF4DU_spread (mu := mu) (c := c) (x := x) i htube)
    (MachineInstance.branchU_contract_clause c)
  have hnext :
      |MachineInstance.selectorContractF_N_U MachineInstance.branchU
          (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta))
          mu x i -
          MachineInstance.stackMachineEncodingU.enc (MachineInstance.M_U.step c) i| ≤
        MachineInstance.stackMachineEncodingU.coordMultiplier c i *
            |x i - MachineInstance.stackMachineEncodingU.enc c i| + 1 := by
    simpa [MachineInstance.selectorContractF_N_U, MachineInstance.selectorTotalPolyN_U,
      MachineInstance.M_U] using hcoord
  have htube_i :
      |x i - MachineInstance.stackMachineEncodingU.enc c i| ≤ MachineInstance.r_LE_U :=
    htube i
  have hfirst :
      |MachineInstance.selectorContractF_N_U MachineInstance.branchU
          (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta))
          mu x i -
          MachineInstance.stackMachineEncodingU.enc (MachineInstance.M_U.step c) i| ≤
        MachineInstance.stackMachineEncodingU.coordMultiplier c i * MachineInstance.r_LE_U + 1 := by
    exact hnext.trans
      (by
        simpa [add_comm] using
          (add_le_add_right
            (mul_le_mul_of_nonneg_left htube_i
              (MachineInstance.coordMultiplierU_nonneg c i)) 1))
  have hsecond :
      |MachineInstance.stackMachineEncodingU.enc (MachineInstance.M_U.step c) i - x i| ≤
        MachineInstance.D_U - 2 + MachineInstance.r_LE_U := by
    have hcur :
        |MachineInstance.stackMachineEncodingU.enc c i - x i| ≤ MachineInstance.r_LE_U := by
      simpa [abs_sub_comm] using htube_i
    have htri :
        |MachineInstance.stackMachineEncodingU.enc (MachineInstance.M_U.step c) i - x i| ≤
          |MachineInstance.stackMachineEncodingU.enc (MachineInstance.M_U.step c) i -
              MachineInstance.stackMachineEncodingU.enc c i| +
            |MachineInstance.stackMachineEncodingU.enc c i - x i| := by
      have hsum :
          MachineInstance.stackMachineEncodingU.enc (MachineInstance.M_U.step c) i - x i =
            (MachineInstance.stackMachineEncodingU.enc (MachineInstance.M_U.step c) i -
              MachineInstance.stackMachineEncodingU.enc c i) +
            (MachineInstance.stackMachineEncodingU.enc c i - x i) := by
        ring
      rw [hsum]
      exact abs_add_le _ _
    exact htri.trans
      (add_le_add (MachineInstance.enc_step_abs_diff_le_D_U_sub_two c i) hcur)
  have htri :
      |MachineInstance.selectorContractF_N_U MachineInstance.branchU
          (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta))
          mu x i - x i| ≤
        |MachineInstance.selectorContractF_N_U MachineInstance.branchU
            (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta))
            mu x i -
            MachineInstance.stackMachineEncodingU.enc (MachineInstance.M_U.step c) i| +
          |MachineInstance.stackMachineEncodingU.enc (MachineInstance.M_U.step c) i - x i| := by
    have hsum :
        MachineInstance.selectorContractF_N_U MachineInstance.branchU
            (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta))
            mu x i - x i =
          (MachineInstance.selectorContractF_N_U MachineInstance.branchU
              (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta))
              mu x i -
              MachineInstance.stackMachineEncodingU.enc (MachineInstance.M_U.step c) i) +
            (MachineInstance.stackMachineEncodingU.enc (MachineInstance.M_U.step c) i - x i) := by
      ring
    rw [hsum]
    exact abs_add_le _ _
  have hpre :
      |MachineInstance.selectorContractF_N_U MachineInstance.branchU
          (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta))
          mu x i - x i| ≤
        (MachineInstance.stackMachineEncodingU.coordMultiplier c i * MachineInstance.r_LE_U + 1) +
          (MachineInstance.D_U - 2 + MachineInstance.r_LE_U) :=
    htri.trans (add_le_add hfirst hsecond)
  have hmult := MachineInstance.coordMultiplierU_le_six c i
  have hr : (0 : ℝ) ≤ MachineInstance.r_LE_U := le_of_lt MachineInstance.r_LE_U_pos
  have hmul :
      MachineInstance.stackMachineEncodingU.coordMultiplier c i * MachineInstance.r_LE_U ≤
        6 * MachineInstance.r_LE_U :=
    mul_le_mul_of_nonneg_right hmult hr
  have hbound :
      (MachineInstance.stackMachineEncodingU.coordMultiplier c i * MachineInstance.r_LE_U + 1) +
          (MachineInstance.D_U - 2 + MachineInstance.r_LE_U) ≤ MachineInstance.D_U := by
    norm_num [MachineInstance.r_LE_U] at hmul ⊢
    linarith
  exact hpre.trans hbound

def bgpStepContractN_constSpread_one
    (eta : ℚ) (heta : 0 < eta)
    (hδ_budget :
      (2 + 2 * offViewCount MachineInstance.UniversalLocalView) *
          (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel *
          (4 * MachineInstance.D_U) ≤ 1) :
    RobustStepContract MachineInstance.M_U MachineInstance.stackMachineEncodingU :=
  bgpStepContractN_assembled_withSpread eta heta (fun _ _ => (1 : ℝ))
    bgpConstEpsF4DU
    (bgpConstEpsF4DU_selectorBudget_one eta heta hδ_budget)
    bgpConstEpsF4DU_spread
    (bgpConstEpsF4DU_displacementBound eta heta hδ_budget)

private structure BgpTrackingPremises
    (S : RobustStepContract UniversalMachine.undecidableMachine.toDiscreteMachine
      MachineInstance.stackMachineEncodingU)
    (w : ℕ)
    (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule S.F)
    (amp W : ℕ → Fin MachineInstance.d_U → ℝ)
    (depth : ℕ → Fin MachineInstance.d_U → ℤ) where
  hmu_large :
    ∀ j t, t ∈ bgpSchedule.zActiveWindow j → S.mu_min ≤ sol.μ t
  heps_mono :
    ∀ i {mu0 mu1 : ℝ}, mu0 ≤ mu1 → S.epsF mu1 i ≤ S.epsF mu0 i
  hinit_weighted :
    ContractWeightedBound (E := MachineInstance.stackMachineEncodingU) sol
      (fun j =>
        UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
          (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
      depth W 0
  hhold_slack :
    ∀ j,
      ContractWeightedBound (E := MachineInstance.stackMachineEncodingU) sol
        (fun j =>
          UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
            (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
        depth W j →
        ∀ i,
          contractBoundaryError (E := MachineInstance.stackMachineEncodingU) sol
              (fun j =>
                UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
                  (UniversalMachine.undecidableMachine.toDiscreteMachine.init w)) j i +
            chiSchedule bgpParams j * S.D ≤ MachineInstance.rLE_constU i
  hwindow_hold :
    ∀ j t, t ∈ bgpSchedule.zActiveWindow j → ∀ i,
      |sol.u t i -
          MachineInstance.stackMachineEncodingU.enc
            ((fun j =>
              UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
                (UniversalMachine.undecidableMachine.toDiscreteMachine.init w)) j) i| ≤
        contractBoundaryError (E := MachineInstance.stackMachineEncodingU) sol
            (fun j =>
              UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
                (UniversalMachine.undecidableMachine.toDiscreteMachine.init w)) j i +
          chiSchedule bgpParams j * S.D
  hz_window_hold :
    ∀ j t, t ∈ bgpSchedule.zActiveWindow j → ∀ i,
      |sol.z t i -
          MachineInstance.stackMachineEncodingU.enc
            ((fun j =>
              UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
                (UniversalMachine.undecidableMachine.toDiscreteMachine.init w)) j) i| ≤
        contractBoundaryError (E := MachineInstance.stackMachineEncodingU) sol
            (fun j =>
              UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
                (UniversalMachine.undecidableMachine.toDiscreteMachine.init w)) j i +
          chiSchedule bgpParams j * S.D
  hflag_z_read_window_bridge :
    ∀ j t, t ∈ bgpSchedule.zActiveWindow j →
      |sol.z t MachineInstance.haltCoordU -
          MachineInstance.stackMachineEncodingU.enc
            ((fun j =>
              UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
                (UniversalMachine.undecidableMachine.toDiscreteMachine.init w)) j)
            MachineInstance.haltCoordU| ≤
        contractBoundaryError (E := MachineInstance.stackMachineEncodingU) sol
          (fun j =>
            UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
              (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
          (j + 1) MachineInstance.haltCoordU
  hrLE_radius :
    ∀ j t, t ∈ bgpSchedule.zActiveWindow j → ∀ i,
      MachineInstance.rLE_constU i ≤ S.radius (sol.μ t)
  hrecurrence_of_branch :
    ∀ j,
      ContractWeightedBound (E := MachineInstance.stackMachineEncodingU) sol
        (fun j =>
          UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
            (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
        depth W j →
      ContractWindowTube (E := MachineInstance.stackMachineEncodingU) sol
        (fun j =>
          UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
            (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
        MachineInstance.rLE_constU j →
      ContractBranchLocked (E := MachineInstance.stackMachineEncodingU) S sol
        (fun j =>
          UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
            (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
        j →
      ContractRecurrenceAt (E := MachineInstance.stackMachineEncodingU) sol
        (fun j =>
          UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
            (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
        amp (contractEtaSchedule S bgpParams bgpSchedule sol) j
  hweighted_step :
    ∀ j,
      ContractWeightedBound (E := MachineInstance.stackMachineEncodingU) sol
        (fun j =>
          UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
            (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
        depth W j →
      ContractRecurrenceAt (E := MachineInstance.stackMachineEncodingU) sol
        (fun j =>
          UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
            (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
        amp (contractEtaSchedule S bgpParams bgpSchedule sol) j →
      ContractWeightedBound (E := MachineInstance.stackMachineEncodingU) sol
        (fun j =>
          UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
            (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
        depth W (j + 1)

theorem bgp_unconditional
    (control : SlabAtomicSelectorData MachineInstance.d_U ℤ)
    (left right : SlabAtomicSelectorData MachineInstance.d_U (Option (Fin 2)))
    (epsF : ℝ → Fin MachineInstance.d_U → ℝ)
    (δ : ℝ)
    (R : ℕ)
    (W : ℕ → ℕ → Fin MachineInstance.d_U → ℝ)
    (depth : ℕ → ℕ → Fin MachineInstance.d_U → ℤ)
    (FP : Fin MachineInstance.d_U → MvPolynomial (Fin (contractDim MachineInstance.d_U)) ℚ)
    (HP : MvPolynomial (Fin MachineInstance.d_U) ℚ)
    (hcontrol_err : control.err = δ)
    (hleft_err : left.err = δ) (hright_err : right.err = δ)
    (hδ_nonneg : 0 ≤ δ)
    (hepsF_nonneg : ∀ mu i, 0 ≤ epsF mu i)
    (hselector_budget_numeric :
      ∀ mu i,
        (6 + 2 * offViewCount MachineInstance.UniversalLocalView) * δ * epsF mu i ≤
          epsF mu i)
    (hctrl_on :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x control.coord -
            control.code (MachineInstance.universalViewSpec.q (MachineInstance.localViewU c))| ≤
              (control.rho : ℝ))
    (hleft_on :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x left.coord -
            left.code (MachineInstance.universalViewSpec.leftTop (MachineInstance.localViewU c))| ≤
              (left.rho : ℝ))
    (hright_on :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x right.coord -
            right.code
              (MachineInstance.universalViewSpec.rightTop (MachineInstance.localViewU c))| ≤
              (right.rho : ℝ))
    (hcontrol_domain :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x control.coord| ≤ (control.C : ℝ))
    (hleft_domain :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x left.coord| ≤ (left.C : ℝ))
    (hright_domain :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x right.coord| ≤ (right.C : ℝ))
    (hspread :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ}
        (i : Fin MachineInstance.d_U),
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          BranchSpread MachineInstance.branchU x (MachineInstance.localViewU c) i (epsF mu i))
    (hdisp :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          ∀ i,
            |MachineInstance.selectorContractF_U MachineInstance.branchU
                (bgpAtoms control left right) mu x i - x i| ≤ MachineInstance.D_U)
    (y₀ : ℕ → Fin (contractDim MachineInstance.d_U) → ℝ)
    (Mbound : ℝ) (hMbound : 0 < Mbound)
    (hSupplyInvariant :
      ∀ w : ℕ, ∀ T : ℝ, 0 < T →
        ∀ y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ,
          y 0 = y₀ w →
          (∀ t ∈ Set.Ico (0 : ℝ) T,
            HasDerivAt y
              (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
                (contractAssembledField MachineInstance.d_U FP HP
                  (1 : ℚ) (1 : ℚ) (1 : ℚ) (1 / 4 : ℚ) 1 R i)) t) →
          ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t‖ ≤ Mbound)
    (hSupplyGateZ :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ),
        ∀ t : ℝ, 0 ≤ t →
          y t (contractGateZ MachineInstance.d_U) =
            bGateZ 1 (y t (contractMu MachineInstance.d_U)) t)
    (hSupplyGateU :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ),
        ∀ t : ℝ, 0 ≤ t →
          y t (contractGateU MachineInstance.d_U) =
            bGateU 1 (y t (contractMu MachineInstance.d_U)) t)
    (hSupplyFieldEval :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ),
        ∀ t : ℝ, 0 ≤ t → ∀ i : Fin MachineInstance.d_U,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (FP i) =
            (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err hright_err
              hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on hright_on
              hcontrol_domain hleft_domain hright_domain hspread hdisp).F
              (y t (contractMu MachineInstance.d_U)) (fun k => y t (contractU k)) i)
    (hSupplyBox :
      ∀ (w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ)
        (hyode : ∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
              (contractAssembledField MachineInstance.d_U FP HP
                (1 : ℚ) (1 : ℚ) (1 : ℚ) (1 / 4 : ℚ) 1 R i)) t)
        (hycont : Continuous y),
        ContractPerCycleBoxBounds MachineInstance.stackMachineEncodingU
          (dynContractIteratorSol_of_contractAssembledField_solution
            (E := MachineInstance.stackMachineEncodingU)
            (S := (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err
              hright_err hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on
              hright_on hcontrol_domain hleft_domain hright_domain
              hspread hdisp))
            (p := bgpParams) (sched := bgpSchedule)
            FP HP bgpParams_A_rat bgpParams_cμ_rat bgpParams_cα_rat
            bgpParams_L_eq bgpSchedule_domain_nonneg y hyode hycont
            (hSupplyGateZ w y) (hSupplyGateU w y) (hSupplyFieldEval w y))
          w MachineInstance.D_U)
    (htracking_inputs :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err
            hright_err hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain
            hspread hdisp).F),
        ContractPerCycleBox MachineInstance.stackMachineEncodingU sol w MachineInstance.D_U →
          BgpTrackingPremises
            (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err
              hright_err hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on
              hright_on hcontrol_domain hleft_domain hright_domain
              hspread hdisp)
            w sol (MachineInstance.ampU (fun j => UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j] (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))) (W w) (depth w))
    (hLatchHcont :
      ∀ sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err
            hright_err hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain
            hspread hdisp).F,
        Continuous fun t => MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t))
    (hLatchHigh :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err
            hright_err hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain
            hspread hdisp).F)
        (La : ContractHaltLatchSol (p := bgpParams) (sched := bgpSchedule)
          (F := (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err
            hright_err hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain
            hspread hdisp).F)
          sol MachineInstance.contractFlagIndicatorPackageU.Hval MachineInstance.K_U R),
        (∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ bgpSchedule.zActiveWindow j,
          1 - MachineInstance.contractFlagIndicatorPackageU.eta ≤
            MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t)) →
          ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1)
    (hLatchLow :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err
            hright_err hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain
            hspread hdisp).F)
        (La : ContractHaltLatchSol (p := bgpParams) (sched := bgpSchedule)
          (F := (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err
            hright_err hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain
            hspread hdisp).F)
          sol MachineInstance.contractFlagIndicatorPackageU.Hval MachineInstance.K_U R),
        (∀ j : ℕ, ∀ t ∈ bgpSchedule.zActiveWindow j,
          MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t) ≤
            MachineInstance.contractFlagIndicatorPackageU.eta) →
          ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4)
    (hflag_margin_all :
      ∀ sol j, contractEtaSchedule
        (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err hright_err
        hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on hright_on
        hcontrol_domain hleft_domain hright_domain hspread hdisp)
        bgpParams bgpSchedule sol j MachineInstance.haltCoordU ≤
          MachineInstance.haltFlagPackageU.flagMargin)
    (hflag_domain :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err
            hright_err hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain
            hspread hdisp).F)
        (_box : ContractPerCycleBox MachineInstance.stackMachineEncodingU sol w
          MachineInstance.D_U),
        ∀ j t, t ∈ bgpSchedule.zActiveWindow j →
          sol.z t MachineInstance.haltCoordU ∈ Set.Icc (0 : ℝ) 1)
    (hFieldEval :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err
            hright_err hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain
            hspread hdisp).F)
        (La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (t : ℝ), 0 ≤ t → ∀ i : Fin MachineInstance.d_U,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t) (FP i) =
            (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err hright_err
              hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on hright_on
              hcontrol_domain hleft_domain hright_domain hspread hdisp).F
              (sol.μ t) (sol.u t) i)
    (hIndicatorEval :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err
            hright_err hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain
            hspread hdisp).F)
        (_La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (t : ℝ),
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) HP =
            MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t))
    (init : ℕ → Fin (contractDim MachineInstance.d_U + 1) → ℚ)
    (init_presented : ∃ f : ℕ → Fin (contractDim MachineInstance.d_U + 1) → ℤ × ℕ,
      Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err
            hright_err hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain
            hspread hdisp).F)
        (La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R),
          ((init w 0 : ℚ) : ℝ) =
            ((∑ i : Fin (contractDim MachineInstance.d_U),
                contractTupleTraj sol La 0 i ^ 2) - 1) /
              ((∑ i : Fin (contractDim MachineInstance.d_U),
                contractTupleTraj sol La 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err
            hright_err hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain
            hspread hdisp).F)
        (La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (i : Fin (contractDim MachineInstance.d_U)),
          ((init w i.succ : ℚ) : ℝ) =
            2 * contractTupleTraj sol La 0 i /
              ((∑ k : Fin (contractDim MachineInstance.d_U),
                contractTupleTraj sol La 0 k ^ 2) + 1)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  main_assembled_dyn_contract
    UniversalMachine.undecidableMachine
    MachineInstance.stackMachineEncodingU
    (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err hright_err
      hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on hright_on
      hcontrol_domain hleft_domain hright_domain hspread hdisp)
    bgpParams bgpSchedule
    MachineInstance.haltCoordU
    MachineInstance.haltFlagPackageU
    MachineInstance.contractFlagIndicatorPackageU
    MachineInstance.K_U_pos
    (kappaSchedule bgpParams) (chiSchedule bgpParams) MachineInstance.rLE_constU
    (fun w => (MachineInstance.ampU (fun j => UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j] (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))))
    (contractEtaSchedule
      (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err hright_err
        hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on hright_on
        hcontrol_domain hleft_domain hright_domain hspread hdisp)
      bgpParams bgpSchedule)
    W depth
    (fun w => contractMovingBox (contractOrbit MachineInstance.stackMachineEncodingU w)
      MachineInstance.D_U bgpSchedule)
    MachineInstance.D_U
    (bgpSupply
      (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err hright_err
        hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on hright_on
        hcontrol_domain hleft_domain hright_domain hspread hdisp)
      R FP HP y₀ Mbound hMbound hSupplyInvariant hSupplyGateZ hSupplyGateU
      hSupplyFieldEval hSupplyBox)
    (fun w sol box =>
      let hp := htracking_inputs w sol box
      bgpTrackingInputs
        (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err hright_err
          hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on hright_on
          hcontrol_domain hleft_domain hright_domain hspread hdisp)
        w sol box (MachineInstance.ampU (fun j => UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j] (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))) (W w) (depth w)
        (MachineInstance.ampU_stack (fun j => UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j] (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))) (fun j i hi => MachineInstance.ampU_reset (fun j => UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j] (UniversalMachine.undecidableMachine.toDiscreteMachine.init w)) j i hi) hp.hmu_large hp.heps_mono
        hp.hinit_weighted hp.hhold_slack hp.hwindow_hold hp.hz_window_hold
        hp.hflag_z_read_window_bridge hp.hrLE_radius hp.hrecurrence_of_branch
        hp.hweighted_step)
    (bgpLatch
      (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err hright_err
        hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on hright_on
        hcontrol_domain hleft_domain hright_domain hspread hdisp)
      R hLatchHcont hLatchHigh hLatchLow)
    hflag_margin_all
    MachineInstance.haltFlagPackageU.margin_le_quarter
    hflag_domain
    (bgpFieldPkg
      (bgpStepContractN4 control left right epsF δ hcontrol_err hleft_err hright_err
        hδ_nonneg hepsF_nonneg hselector_budget_numeric hctrl_on hleft_on hright_on
        hcontrol_domain hleft_domain hright_domain hspread hdisp)
      R FP HP hFieldEval hIndicatorEval init init_presented init_zero init_succ)

theorem bgp_unconditional_N
    (eta : ℚ)
    (heta : 0 < eta)
    (epsF : ℝ → Fin MachineInstance.d_U → ℝ)
    (R : ℕ)
    (W : ℕ → ℕ → Fin MachineInstance.d_U → ℝ)
    (depth : ℕ → ℕ → Fin MachineInstance.d_U → ℤ)
    (FP : Fin MachineInstance.d_U → MvPolynomial (Fin (contractDim MachineInstance.d_U)) ℚ)
    (HP : MvPolynomial (Fin MachineInstance.d_U) ℚ)
    (hepsF_nonneg : ∀ mu i, 0 ≤ epsF mu i)
    (hselector_budget_numeric :
      ∀ mu i,
        (2 + 2 * offViewCount MachineInstance.UniversalLocalView) *
            (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel * epsF mu i ≤
          epsF mu i)
    (hspread :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ}
        (i : Fin MachineInstance.d_U),
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          BranchSpread MachineInstance.branchU x (MachineInstance.localViewU c) i (epsF mu i))
    (hdisp :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          ∀ i,
            |MachineInstance.selectorContractF_N_U MachineInstance.branchU
                (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)) mu x i - x i| ≤ MachineInstance.D_U)
    (y₀ : ℕ → Fin (contractDim MachineInstance.d_U) → ℝ)
    (Mbound : ℝ)
    (hMbound : 0 < Mbound)
    (hSupplyInvariant :
      ∀ w : ℕ, ∀ T : ℝ, 0 < T →
        ∀ y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ,
          y 0 = y₀ w →
          (∀ t ∈ Set.Ico (0 : ℝ) T,
            HasDerivAt y
              (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
                (contractAssembledField MachineInstance.d_U FP HP
                  (1 : ℚ) (1 : ℚ) (1 : ℚ) (1 / 4 : ℚ) 1 R i)) t) →
          ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t‖ ≤ Mbound)
    (hSupplyGateZ :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ),
        ∀ t : ℝ, 0 ≤ t →
          y t (contractGateZ MachineInstance.d_U) =
            bGateZ 1 (y t (contractMu MachineInstance.d_U)) t)
    (hSupplyGateU :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ),
        ∀ t : ℝ, 0 ≤ t →
          y t (contractGateU MachineInstance.d_U) =
            bGateU 1 (y t (contractMu MachineInstance.d_U)) t)
    (hSupplyFieldEval :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ),
        ∀ t : ℝ, 0 ≤ t → ∀ i : Fin MachineInstance.d_U,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (FP i) =
            (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp).F
              (y t (contractMu MachineInstance.d_U)) (fun k => y t (contractU k)) i)
    (hSupplyBox :
      ∀ (w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ)
        (hyode : ∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
              (contractAssembledField MachineInstance.d_U FP HP
                (1 : ℚ) (1 : ℚ) (1 : ℚ) (1 / 4 : ℚ) 1 R i)) t)
        (hycont : Continuous y),
        ContractPerCycleBoxBounds MachineInstance.stackMachineEncodingU
          (dynContractIteratorSol_of_contractAssembledField_solution
            (E := MachineInstance.stackMachineEncodingU)
            (S := (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp))
            (p := bgpParams) (sched := bgpSchedule)
            FP HP bgpParams_A_rat bgpParams_cμ_rat bgpParams_cα_rat
            bgpParams_L_eq bgpSchedule_domain_nonneg y hyode hycont
            (hSupplyGateZ w y) (hSupplyGateU w y) (hSupplyFieldEval w y))
          w MachineInstance.D_U)
    (htracking_inputs :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp).F),
        ContractPerCycleBox MachineInstance.stackMachineEncodingU sol w MachineInstance.D_U →
          BgpTrackingPremises
            (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp)
            w sol (MachineInstance.ampU (fun j => UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j] (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))) (W w) (depth w))
    (hLatchHcont :
      ∀ sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp).F,
        Continuous fun t => MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t))
    (hLatchHigh :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp).F)
        (La : ContractHaltLatchSol (p := bgpParams) (sched := bgpSchedule)
          (F := (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp).F)
          sol MachineInstance.contractFlagIndicatorPackageU.Hval MachineInstance.K_U R),
        (∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ bgpSchedule.zActiveWindow j,
          1 - MachineInstance.contractFlagIndicatorPackageU.eta ≤
            MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t)) →
          ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1)
    (hLatchLow :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp).F)
        (La : ContractHaltLatchSol (p := bgpParams) (sched := bgpSchedule)
          (F := (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp).F)
          sol MachineInstance.contractFlagIndicatorPackageU.Hval MachineInstance.K_U R),
        (∀ j : ℕ, ∀ t ∈ bgpSchedule.zActiveWindow j,
          MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t) ≤
            MachineInstance.contractFlagIndicatorPackageU.eta) →
          ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4)
    (hflag_margin_all :
      ∀ sol j, contractEtaSchedule
        (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp)
        bgpParams bgpSchedule sol j MachineInstance.haltCoordU ≤
          MachineInstance.haltFlagPackageU.flagMargin)
    (hflag_domain :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp).F)
        (_box : ContractPerCycleBox MachineInstance.stackMachineEncodingU sol w
          MachineInstance.D_U),
        ∀ j t, t ∈ bgpSchedule.zActiveWindow j →
          sol.z t MachineInstance.haltCoordU ∈ Set.Icc (0 : ℝ) 1)
    (hFieldEval :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp).F)
        (La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (t : ℝ), 0 ≤ t → ∀ i : Fin MachineInstance.d_U,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t) (FP i) =
            (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp).F
              (sol.μ t) (sol.u t) i)
    (hIndicatorEval :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp).F)
        (_La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (t : ℝ),
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) HP =
            MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t))
    (init : ℕ → Fin (contractDim MachineInstance.d_U + 1) → ℚ)
    (init_presented : ∃ f : ℕ → Fin (contractDim MachineInstance.d_U + 1) → ℤ × ℕ,
      Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp).F)
        (La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R),
          ((init w 0 : ℚ) : ℝ) =
            ((∑ i : Fin (contractDim MachineInstance.d_U),
                contractTupleTraj sol La 0 i ^ 2) - 1) /
              ((∑ i : Fin (contractDim MachineInstance.d_U),
                contractTupleTraj sol La 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp).F)
        (La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (i : Fin (contractDim MachineInstance.d_U)),
          ((init w i.succ : ℚ) : ℝ) =
            2 * contractTupleTraj sol La 0 i /
              ((∑ k : Fin (contractDim MachineInstance.d_U),
                contractTupleTraj sol La 0 k ^ 2) + 1))
    :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  main_assembled_dyn_contract
    UniversalMachine.undecidableMachine
    MachineInstance.stackMachineEncodingU
    (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp)
    bgpParams bgpSchedule
    MachineInstance.haltCoordU
    MachineInstance.haltFlagPackageU
    MachineInstance.contractFlagIndicatorPackageU
    MachineInstance.K_U_pos
    (kappaSchedule bgpParams) (chiSchedule bgpParams) MachineInstance.rLE_constU
    (fun w => (MachineInstance.ampU (fun j => UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j] (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))))
    (contractEtaSchedule
      (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp)
      bgpParams bgpSchedule)
    W depth
    (fun w => contractMovingBox (contractOrbit MachineInstance.stackMachineEncodingU w)
      MachineInstance.D_U bgpSchedule)
    MachineInstance.D_U
    (bgpSupply
      (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp)
      R FP HP y₀ Mbound hMbound hSupplyInvariant hSupplyGateZ hSupplyGateU
      hSupplyFieldEval hSupplyBox)
    (fun w sol box =>
      let hp := htracking_inputs w sol box
      bgpTrackingInputs
        (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp)
        w sol box (MachineInstance.ampU (fun j => UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j] (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))) (W w) (depth w)
        (MachineInstance.ampU_stack (fun j => UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j] (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))) (fun j i hi => MachineInstance.ampU_reset (fun j => UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j] (UniversalMachine.undecidableMachine.toDiscreteMachine.init w)) j i hi) hp.hmu_large hp.heps_mono
        hp.hinit_weighted hp.hhold_slack hp.hwindow_hold hp.hz_window_hold
        hp.hflag_z_read_window_bridge hp.hrLE_radius hp.hrecurrence_of_branch
        hp.hweighted_step)
    (bgpLatch
      (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp)
      R hLatchHcont hLatchHigh hLatchLow)
    hflag_margin_all
    MachineInstance.haltFlagPackageU.margin_le_quarter
    hflag_domain
    (bgpFieldPkg
      (bgpStepContractN_assembled eta heta epsF hselector_budget_numeric hspread hdisp)
      R FP HP hFieldEval hIndicatorEval init init_presented init_zero init_succ)

theorem bgp_unconditional_expEps
    (control : SlabAtomicSelectorData MachineInstance.d_U ℤ)
    (left right : SlabAtomicSelectorData MachineInstance.d_U (Option (Fin 2)))
    (R : ℕ)
    (W : ℕ → ℕ → Fin MachineInstance.d_U → ℝ)
    (depth : ℕ → ℕ → Fin MachineInstance.d_U → ℤ)
    (FP : Fin MachineInstance.d_U → MvPolynomial (Fin (contractDim MachineInstance.d_U)) ℚ)
    (HP : MvPolynomial (Fin MachineInstance.d_U) ℚ)
    (hδ_budget :
      (6 + 2 * offViewCount MachineInstance.UniversalLocalView) * control.err ≤ 1)
    (hleft_err : left.err = control.err) (hright_err : right.err = control.err)
    (hctrl_on :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x control.coord -
            control.code (MachineInstance.universalViewSpec.q (MachineInstance.localViewU c))| ≤
              (control.rho : ℝ))
    (hleft_on :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x left.coord -
            left.code (MachineInstance.universalViewSpec.leftTop (MachineInstance.localViewU c))| ≤
              (left.rho : ℝ))
    (hright_on :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x right.coord -
            right.code
              (MachineInstance.universalViewSpec.rightTop (MachineInstance.localViewU c))| ≤
              (right.rho : ℝ))
    (hcontrol_domain :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x control.coord| ≤ (control.C : ℝ))
    (hleft_domain :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x left.coord| ≤ (left.C : ℝ))
    (hright_domain :
      ∀ {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          |x right.coord| ≤ (right.C : ℝ))
    (hspread :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ}
        (i : Fin MachineInstance.d_U),
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          BranchSpread MachineInstance.branchU x (MachineInstance.localViewU c) i
            (bgpEpsSchedule mu i))
    (hdisp :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          ∀ i,
            |MachineInstance.selectorContractF_U MachineInstance.branchU
                (bgpAtoms control left right) mu x i - x i| ≤ MachineInstance.D_U)
    (y₀ : ℕ → Fin (contractDim MachineInstance.d_U) → ℝ)
    (Mbound : ℝ) (hMbound : 0 < Mbound)
    (hSupplyInvariant :
      ∀ w : ℕ, ∀ T : ℝ, 0 < T →
        ∀ y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ,
          y 0 = y₀ w →
          (∀ t ∈ Set.Ico (0 : ℝ) T,
            HasDerivAt y
              (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
                (contractAssembledField MachineInstance.d_U FP HP
                  (1 : ℚ) (1 : ℚ) (1 : ℚ) (1 / 4 : ℚ) 1 R i)) t) →
          ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t‖ ≤ Mbound)
    (hSupplyGateZ :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ),
        ∀ t : ℝ, 0 ≤ t →
          y t (contractGateZ MachineInstance.d_U) =
            bGateZ 1 (y t (contractMu MachineInstance.d_U)) t)
    (hSupplyGateU :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ),
        ∀ t : ℝ, 0 ≤ t →
          y t (contractGateU MachineInstance.d_U) =
            bGateU 1 (y t (contractMu MachineInstance.d_U)) t)
    (hSupplyFieldEval :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ),
        ∀ t : ℝ, 0 ≤ t → ∀ i : Fin MachineInstance.d_U,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (FP i) =
            (bgpStepContractExp control left right hδ_budget hleft_err hright_err hctrl_on hleft_on
              hright_on hcontrol_domain hleft_domain hright_domain hspread hdisp).F
              (y t (contractMu MachineInstance.d_U)) (fun k => y t (contractU k)) i)
    (hSupplyBox :
      ∀ (w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ)
        (hyode : ∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
              (contractAssembledField MachineInstance.d_U FP HP
                (1 : ℚ) (1 : ℚ) (1 : ℚ) (1 / 4 : ℚ) 1 R i)) t)
        (hycont : Continuous y),
        ContractPerCycleBoxBounds MachineInstance.stackMachineEncodingU
          (dynContractIteratorSol_of_contractAssembledField_solution
            (E := MachineInstance.stackMachineEncodingU)
            (S := (bgpStepContractExp control left right hδ_budget hleft_err hright_err hctrl_on
              hleft_on hright_on hcontrol_domain hleft_domain hright_domain
              hspread hdisp))
            (p := bgpParams) (sched := bgpSchedule)
            FP HP bgpParams_A_rat bgpParams_cμ_rat bgpParams_cα_rat
            bgpParams_L_eq bgpSchedule_domain_nonneg y hyode hycont
            (hSupplyGateZ w y) (hSupplyGateU w y) (hSupplyFieldEval w y))
          w MachineInstance.D_U)
    (htracking_inputs :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractExp control left right hδ_budget hleft_err hright_err hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain hspread hdisp).F),
        ContractPerCycleBox MachineInstance.stackMachineEncodingU sol w MachineInstance.D_U →
          BgpTrackingPremises
            (bgpStepContractExp control left right hδ_budget hleft_err hright_err hctrl_on hleft_on
              hright_on hcontrol_domain hleft_domain hright_domain hspread hdisp)
            w sol (MachineInstance.ampU (fun j => UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j] (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))) (W w) (depth w))
    (hLatchHcont :
      ∀ sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractExp control left right hδ_budget hleft_err hright_err hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain hspread hdisp).F,
        Continuous fun t => MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t))
    (hLatchHigh :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractExp control left right hδ_budget hleft_err hright_err hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain hspread hdisp).F)
        (La : ContractHaltLatchSol (p := bgpParams) (sched := bgpSchedule)
          (F := (bgpStepContractExp control left right hδ_budget hleft_err hright_err hctrl_on
            hleft_on hright_on hcontrol_domain hleft_domain hright_domain
            hspread hdisp).F)
          sol MachineInstance.contractFlagIndicatorPackageU.Hval MachineInstance.K_U R),
        (∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ bgpSchedule.zActiveWindow j,
          1 - MachineInstance.contractFlagIndicatorPackageU.eta ≤
            MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t)) →
          ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1)
    (hLatchLow :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractExp control left right hδ_budget hleft_err hright_err hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain hspread hdisp).F)
        (La : ContractHaltLatchSol (p := bgpParams) (sched := bgpSchedule)
          (F := (bgpStepContractExp control left right hδ_budget hleft_err hright_err hctrl_on
            hleft_on hright_on hcontrol_domain hleft_domain hright_domain
            hspread hdisp).F)
          sol MachineInstance.contractFlagIndicatorPackageU.Hval MachineInstance.K_U R),
        (∀ j : ℕ, ∀ t ∈ bgpSchedule.zActiveWindow j,
          MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t) ≤
            MachineInstance.contractFlagIndicatorPackageU.eta) →
          ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4)
    (hflag_margin_all :
      ∀ sol j, contractEtaSchedule
        (bgpStepContractExp control left right hδ_budget hleft_err hright_err hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain hspread hdisp)
        bgpParams bgpSchedule sol j MachineInstance.haltCoordU ≤
          MachineInstance.haltFlagPackageU.flagMargin)
    (hflag_domain :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractExp control left right hδ_budget hleft_err hright_err hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain hspread hdisp).F)
        (_box : ContractPerCycleBox MachineInstance.stackMachineEncodingU sol w
          MachineInstance.D_U),
        ∀ j t, t ∈ bgpSchedule.zActiveWindow j →
          sol.z t MachineInstance.haltCoordU ∈ Set.Icc (0 : ℝ) 1)
    (hFieldEval :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractExp control left right hδ_budget hleft_err hright_err hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain hspread hdisp).F)
        (La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (t : ℝ), 0 ≤ t → ∀ i : Fin MachineInstance.d_U,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t) (FP i) =
            (bgpStepContractExp control left right hδ_budget hleft_err hright_err hctrl_on hleft_on
              hright_on hcontrol_domain hleft_domain hright_domain hspread hdisp).F
              (sol.μ t) (sol.u t) i)
    (hIndicatorEval :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractExp control left right hδ_budget hleft_err hright_err hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain hspread hdisp).F)
        (_La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (t : ℝ),
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) HP =
            MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t))
    (init : ℕ → Fin (contractDim MachineInstance.d_U + 1) → ℚ)
    (init_presented : ∃ f : ℕ → Fin (contractDim MachineInstance.d_U + 1) → ℤ × ℕ,
      Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractExp control left right hδ_budget hleft_err hright_err hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain hspread hdisp).F)
        (La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R),
          ((init w 0 : ℚ) : ℝ) =
            ((∑ i : Fin (contractDim MachineInstance.d_U),
                contractTupleTraj sol La 0 i ^ 2) - 1) /
              ((∑ i : Fin (contractDim MachineInstance.d_U),
                contractTupleTraj sol La 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractExp control left right hδ_budget hleft_err hright_err hctrl_on hleft_on
            hright_on hcontrol_domain hleft_domain hright_domain hspread hdisp).F)
        (La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (i : Fin (contractDim MachineInstance.d_U)),
          ((init w i.succ : ℚ) : ℝ) =
            2 * contractTupleTraj sol La 0 i /
              ((∑ k : Fin (contractDim MachineInstance.d_U),
                contractTupleTraj sol La 0 k ^ 2) + 1)) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_unconditional control left right bgpEpsSchedule control.err R W depth
    FP HP rfl hleft_err hright_err control.err_nonneg bgpEpsSchedule_nonneg
    (bgpEpsSchedule_selectorBudget control.err hδ_budget)
    hctrl_on hleft_on hright_on hcontrol_domain hleft_domain hright_domain hspread hdisp
    y₀ Mbound hMbound hSupplyInvariant hSupplyGateZ hSupplyGateU hSupplyFieldEval
    hSupplyBox htracking_inputs hLatchHcont hLatchHigh hLatchLow hflag_margin_all
    hflag_domain hFieldEval hIndicatorEval init init_presented init_zero init_succ

theorem bgp_unconditional_expEps_N
    (eta : ℚ)
    (heta : 0 < eta)
    (R : ℕ)
    (W : ℕ → ℕ → Fin MachineInstance.d_U → ℝ)
    (depth : ℕ → ℕ → Fin MachineInstance.d_U → ℤ)
    (FP : Fin MachineInstance.d_U → MvPolynomial (Fin (contractDim MachineInstance.d_U)) ℚ)
    (HP : MvPolynomial (Fin MachineInstance.d_U) ℚ)
    (hδ_budget :
      (2 + 2 * offViewCount MachineInstance.UniversalLocalView) *
          (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel ≤ 1)
    (hspread :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ}
        (i : Fin MachineInstance.d_U),
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          BranchSpread MachineInstance.branchU x (MachineInstance.localViewU c) i
            (bgpEpsSchedule mu i))
    (hdisp :
      ∀ {mu : ℝ} {c : MachineInstance.UConf} {x : Fin MachineInstance.d_U → ℝ},
        EncodingTube MachineInstance.stackMachineEncodingU MachineInstance.r_LE_U c x →
          ∀ i,
            |MachineInstance.selectorContractF_N_U MachineInstance.branchU
                (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)) mu x i - x i| ≤ MachineInstance.D_U)
    (y₀ : ℕ → Fin (contractDim MachineInstance.d_U) → ℝ)
    (Mbound : ℝ)
    (hMbound : 0 < Mbound)
    (hSupplyInvariant :
      ∀ w : ℕ, ∀ T : ℝ, 0 < T →
        ∀ y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ,
          y 0 = y₀ w →
          (∀ t ∈ Set.Ico (0 : ℝ) T,
            HasDerivAt y
              (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
                (contractAssembledField MachineInstance.d_U FP HP
                  (1 : ℚ) (1 : ℚ) (1 : ℚ) (1 / 4 : ℚ) 1 R i)) t) →
          ∀ t ∈ Set.Ico (0 : ℝ) T, ‖y t‖ ≤ Mbound)
    (hSupplyGateZ :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ),
        ∀ t : ℝ, 0 ≤ t →
          y t (contractGateZ MachineInstance.d_U) =
            bGateZ 1 (y t (contractMu MachineInstance.d_U)) t)
    (hSupplyGateU :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ),
        ∀ t : ℝ, 0 ≤ t →
          y t (contractGateU MachineInstance.d_U) =
            bGateU 1 (y t (contractMu MachineInstance.d_U)) t)
    (hSupplyFieldEval :
      ∀ (_w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ),
        ∀ t : ℝ, 0 ≤ t → ∀ i : Fin MachineInstance.d_U,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t) (FP i) =
            (bgpStepContractExp_N_assembled eta heta hδ_budget hspread hdisp).F
              (y t (contractMu MachineInstance.d_U)) (fun k => y t (contractU k)) i)
    (hSupplyBox :
      ∀ (w : ℕ) (y : ℝ → Fin (contractDim MachineInstance.d_U) → ℝ)
        (hyode : ∀ t : ℝ, 0 ≤ t →
          HasDerivAt y
            (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) (y t)
              (contractAssembledField MachineInstance.d_U FP HP
                (1 : ℚ) (1 : ℚ) (1 : ℚ) (1 / 4 : ℚ) 1 R i)) t)
        (hycont : Continuous y),
        ContractPerCycleBoxBounds MachineInstance.stackMachineEncodingU
          (dynContractIteratorSol_of_contractAssembledField_solution
            (E := MachineInstance.stackMachineEncodingU)
            (S := (bgpStepContractExp_N_assembled eta heta hδ_budget hspread hdisp))
            (p := bgpParams) (sched := bgpSchedule)
            FP HP bgpParams_A_rat bgpParams_cμ_rat bgpParams_cα_rat
            bgpParams_L_eq bgpSchedule_domain_nonneg y hyode hycont
            (hSupplyGateZ w y) (hSupplyGateU w y) (hSupplyFieldEval w y))
          w MachineInstance.D_U)
    (htracking_inputs :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractExp_N_assembled eta heta hδ_budget hspread hdisp).F),
        ContractPerCycleBox MachineInstance.stackMachineEncodingU sol w MachineInstance.D_U →
          BgpTrackingPremises
            (bgpStepContractExp_N_assembled eta heta hδ_budget hspread hdisp)
            w sol (MachineInstance.ampU (fun j => UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j] (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))) (W w) (depth w))
    (hLatchHcont :
      ∀ sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractExp_N_assembled eta heta hδ_budget hspread hdisp).F,
        Continuous fun t => MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t))
    (hLatchHigh :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractExp_N_assembled eta heta hδ_budget hspread hdisp).F)
        (La : ContractHaltLatchSol (p := bgpParams) (sched := bgpSchedule)
          (F := (bgpStepContractExp_N_assembled eta heta hδ_budget hspread hdisp).F)
          sol MachineInstance.contractFlagIndicatorPackageU.Hval MachineInstance.K_U R),
        (∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ bgpSchedule.zActiveWindow j,
          1 - MachineInstance.contractFlagIndicatorPackageU.eta ≤
            MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t)) →
          ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1)
    (hLatchLow :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractExp_N_assembled eta heta hδ_budget hspread hdisp).F)
        (La : ContractHaltLatchSol (p := bgpParams) (sched := bgpSchedule)
          (F := (bgpStepContractExp_N_assembled eta heta hδ_budget hspread hdisp).F)
          sol MachineInstance.contractFlagIndicatorPackageU.Hval MachineInstance.K_U R),
        (∀ j : ℕ, ∀ t ∈ bgpSchedule.zActiveWindow j,
          MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t) ≤
            MachineInstance.contractFlagIndicatorPackageU.eta) →
          ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4)
    (hflag_margin_all :
      ∀ sol j, contractEtaSchedule
        (bgpStepContractExp_N_assembled eta heta hδ_budget hspread hdisp)
        bgpParams bgpSchedule sol j MachineInstance.haltCoordU ≤
          MachineInstance.haltFlagPackageU.flagMargin)
    (hflag_domain :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractExp_N_assembled eta heta hδ_budget hspread hdisp).F)
        (_box : ContractPerCycleBox MachineInstance.stackMachineEncodingU sol w
          MachineInstance.D_U),
        ∀ j t, t ∈ bgpSchedule.zActiveWindow j →
          sol.z t MachineInstance.haltCoordU ∈ Set.Icc (0 : ℝ) 1)
    (hFieldEval :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractExp_N_assembled eta heta hδ_budget hspread hdisp).F)
        (La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (t : ℝ), 0 ≤ t → ∀ i : Fin MachineInstance.d_U,
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (contractTupleTraj sol La t) (FP i) =
            (bgpStepContractExp_N_assembled eta heta hδ_budget hspread hdisp).F
              (sol.μ t) (sol.u t) i)
    (hIndicatorEval :
      ∀ (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractExp_N_assembled eta heta hδ_budget hspread hdisp).F)
        (_La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (t : ℝ),
          MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) HP =
            MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t))
    (init : ℕ → Fin (contractDim MachineInstance.d_U + 1) → ℚ)
    (init_presented : ∃ f : ℕ → Fin (contractDim MachineInstance.d_U + 1) → ℤ × ℕ,
      Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractExp_N_assembled eta heta hδ_budget hspread hdisp).F)
        (La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R),
          ((init w 0 : ℚ) : ℝ) =
            ((∑ i : Fin (contractDim MachineInstance.d_U),
                contractTupleTraj sol La 0 i ^ 2) - 1) /
              ((∑ i : Fin (contractDim MachineInstance.d_U),
                contractTupleTraj sol La 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (sol : DynContractIteratorSol (Fin MachineInstance.d_U) bgpParams bgpSchedule
          (bgpStepContractExp_N_assembled eta heta hδ_budget hspread hdisp).F)
        (La : ContractHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (i : Fin (contractDim MachineInstance.d_U)),
          ((init w i.succ : ℚ) : ℝ) =
            2 * contractTupleTraj sol La 0 i /
              ((∑ k : Fin (contractDim MachineInstance.d_U),
                contractTupleTraj sol La 0 k ^ 2) + 1))
    :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_unconditional_N eta heta bgpEpsSchedule R W depth
    FP HP bgpEpsSchedule_nonneg
    (fun mu i => mul_le_of_le_one_left (bgpEpsSchedule_nonneg mu i) hδ_budget)
    hspread hdisp
    y₀ Mbound hMbound hSupplyInvariant hSupplyGateZ hSupplyGateU hSupplyFieldEval
    hSupplyBox htracking_inputs hLatchHcont hLatchHigh hLatchLow hflag_margin_all
    hflag_domain hFieldEval hIndicatorEval init init_presented init_zero init_succ

/-- The five universal gate atoms carry total error `9·eta`. -/
theorem universalGateAtoms_errSel (eta : ℚ) (heta : 0 < eta) :
    (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel =
      9 * (eta : ℝ) := by
  rw [GateSelectorAtomsN.errSel, Fin.sum_univ_five]
  simp [gateSelectorAtomsCoordN, CoordAtomData.toAtomicSelectorData,
    MachineInstance.universalGateAtoms, MachineInstance.controlAtom,
    MachineInstance.mainPairAtom, MachineInstance.stackTopAtom, CoordAtomData.relabel,
    IntervalAtomSpec.toCoordAtomData, SlabAtomicSelectorData.toCoordAtomData,
    MachineInstance.controlAtomSlab, finiteCoordinateAtoms,
    MachineInstance.stackTopAtomSpec, MachineInstance.mainPairAtomSpec]
  ring

/-- The selector budget `(2 + 2·off)·errSel ≤ 1` is satisfiable: a small enough
positive `eta` makes it hold (equality at `eta = 1/(18·card)`). -/
theorem universalGateAtoms_budget_satisfiable :
    ∃ (eta : ℚ) (heta : 0 < eta),
      (2 + 2 * offViewCount MachineInstance.UniversalLocalView) *
          (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel ≤ 1 := by
  have hN : 0 < Fintype.card MachineInstance.UniversalLocalView :=
    Fintype.card_pos_iff.mpr ⟨MachineInstance.defaultLocalViewU⟩
  have hNq : (0 : ℚ) < (Fintype.card MachineInstance.UniversalLocalView : ℚ) := by
    exact_mod_cast hN
  have hNr : (0 : ℝ) < (Fintype.card MachineInstance.UniversalLocalView : ℝ) := by
    exact_mod_cast hN
  refine ⟨1 / (18 * Fintype.card MachineInstance.UniversalLocalView), by positivity, ?_⟩
  rw [universalGateAtoms_errSel]
  unfold offViewCount
  rw [Nat.cast_sub hN]
  push_cast
  apply le_of_eq
  field_simp
  ring

theorem bgpConstEpsF4DU_selectorBudget_satisfiable :
    ∃ (eta : ℚ) (heta : 0 < eta),
      ∀ mu i,
        (2 + 2 * offViewCount MachineInstance.UniversalLocalView) *
            (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel *
            bgpConstEpsF4DU mu i ≤
          bgpConstEpsF4DU mu i := by
  rcases universalGateAtoms_budget_satisfiable with ⟨eta, heta, hδ_budget⟩
  exact ⟨eta, heta, bgpConstEpsF4DU_selectorBudget eta heta hδ_budget⟩

end Ripple.BoundedUniversality.BGP
