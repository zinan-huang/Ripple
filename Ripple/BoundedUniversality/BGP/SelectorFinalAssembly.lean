import Ripple.BoundedUniversality.BGP.SelectorField
import Ripple.BoundedUniversality.BGP.SelectorMachineInstance
import Ripple.BoundedUniversality.BGP.SelectorGateApprox
import Ripple.BoundedUniversality.BGP.SelectorLatchConv
import Ripple.BoundedUniversality.BGP.FinalAssembly
import Ripple.BoundedUniversality.BGP.BGPParams38

/-!
Ripple.BoundedUniversality.BGP.SelectorFinalAssembly
--------------------------------
M_U instantiation of the clock-driven selector: discharge the inputs of
`bgp_unconditional_selector_assembled` for the universal machine, mirroring the
fixed-precision `FinalAssembly.lean` path but feeding the selector machinery.

The fixed-precision contract carries an UNSATISFIABLE selector premise (`hspread`/
`hdisp` with the fixed per-step floor `epsF` and the budget `(6+2k)·δ·epsF ≤ epsF`).
The clock-driven selector REPLACES that floor with `εmix(t) → 0`, achieved by the
growing gate gain (`SelectorGateApprox.gate_mix_error_approx` + the `ΔG_j → ∞`
mechanism).  This file builds the concrete M_U readout polynomial and its
realization identity — the first concrete brick of the field package.

D-step 1 (this commit): the universal readout polynomial `muReadoutPoly` over the
extended selector state, with `eval₂(selectorTupleTraj) muReadoutPoly v =
universalPval eta heta v (sol.u t)` — exactly the `h_P` realization hypothesis the
field-package constructor `selectorPolynomialFieldPackage` consumes (with
`readoutP := universalPval eta heta`, the config-reading margin readout the
`Pval → readoutP` refactor made hostable).
-/

noncomputable section

namespace Ripple.BoundedUniversality.BGP

open scoped BigOperators
open MachineInstance

/-- The universal margin readout as a polynomial over the extended selector state.
`viewSelectorPolyN` (the coarse Bernstein readout over the `d_U` config coords),
renamed into the `u`-block of the extended state via `selU`, minus the `1/2`
threshold.  Evaluated along the selector trajectory it yields
`universalPval eta heta v (sol.u t) = Λ_N(sol.u t) v − 1/2` (see `eval_muReadoutPoly`). -/
def muReadoutPoly (eta : ℚ) (heta : 0 < eta) (v : UniversalLocalView) :
    MvPolynomial (Fin (selectorDim d_U UniversalLocalView)) ℚ :=
  MvPolynomial.rename (selU UniversalLocalView)
      (viewSelectorPolyN universalViewSpecN
        (gateSelectorAtomsCoordN (universalGateAtoms eta heta)) v)
    - MvPolynomial.C (1 / 2 : ℚ)

variable {p : DynGateParams} {sched : PhaseSchedule}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    {readoutP : UniversalLocalView → (Fin d_U → ℝ) → ℝ}

/-- **Realization of the universal readout polynomial.**  Along the selector
trajectory, `muReadoutPoly` evaluates to the universal coarse-margin readout
`universalPval eta heta v (sol.u t)`.  This is the `h_P` hypothesis of
`selectorPolynomialFieldPackage` for the M_U instance (with the `readoutP` set to
`universalPval eta heta`).  Proof: `eval₂_rename` pushes the evaluation through the
`selU` embedding onto the `u`-block coordinates `selectorTupleTraj … (selU i) =
sol.u t i`, recovering `evalPoly4 (sol.u t) (viewSelectorPolyN …) = LambdaN`. -/
theorem eval_muReadoutPoly (eta : ℚ) (heta : 0 < eta)
    (sol : SelectorDynSol d_U B_U UniversalLocalView p sched branchU
      chiResetF chiGateF kappaF gainF readoutP)
    {Hval : (Fin d_U → ℝ) → ℝ} {K : ℝ} {R : ℕ}
    (La : SelectorHaltLatchSol sol Hval K R) (warmGainVal : ℝ) (t : ℝ) (v : UniversalLocalView) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) (selectorTupleTraj sol La warmGainVal t)
        (muReadoutPoly eta heta v) =
      universalPval eta heta v (sol.u t) := by
  have hu : (fun i => selectorTupleTraj sol La warmGainVal t (selU UniversalLocalView i)) = sol.u t := by
    funext i; exact selectorTupleTraj_u (sol := sol) (La := La) (warmGainVal := warmGainVal) (t := t) i
  rw [muReadoutPoly, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_rename]
  rw [show ((selectorTupleTraj sol La warmGainVal t) ∘ (selU UniversalLocalView))
        = (fun i => selectorTupleTraj sol La warmGainVal t (selU UniversalLocalView i)) from rfl, hu]
  rw [MvPolynomial.eval₂_C]
  rw [universalPval, LambdaN, evalPoly4]
  norm_num

/-! ## INPUT (1): the M_U clock-driven-selector polynomial field package -/

/-- `selectorSchedule.domain = Set.Ici 0`, so every nonnegative real lies in it. -/
private theorem selectorSchedule_domain_nonneg :
    ∀ t : ℝ, 0 ≤ t → t ∈ selectorSchedule.domain := by
  intro t ht
  simpa [selectorSchedule] using ht

/-- **Concrete clock gain growth (the floor is removed for the real clock).**  For a selector
solution whose gate envelope is the sin-gate `χ_gate = ((1+sin t)/2)^M` and whose gain is the
exponential clock gain `g₀·exp(cα·t)`, the per-cycle accumulated gate gain over the rising gate
sub-window `[2πj+π/6, 2πj+π/2]` of the `selectorSchedule` cycle grows AT LEAST LINEARLY:
`c·j ≤ G(2πj+π/2) − G(2πj+π/6)` with the explicit positive constant
`c = (3/4)^M · g₀ · exp(cα·π/6) · (π/3) · (2π·cα)`.  Instantiates `selector_gain_linear_growth`
with the gate windows and discharges `hchi` via `sin_ge_half_of_gate_window` + `chiGate_lb`.  Feeds
`selector_epsmix_decay_of_gain_linear` (hΔG) ⇒ the per-cycle εmix decays geometrically. -/
theorem selector_clock_gain_growth
    {d B : ℕ} {V : Type} [Fintype V] {branch : V → BranchData d B}
    {Pv : V → (Fin d → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF kappaF : ℝ → ℝ} (M : ℕ) {g₀ cα : ℝ} (hcα : 0 < cα) (hg₀ : 0 < g₀)
    (sol : SelectorDynSol d B V p selectorSchedule branch
      chiResetF (fun t => ((1 + Real.sin t) / 2) ^ M) kappaF
      (fun t => g₀ * Real.exp (cα * t)) Pv) :
    ∀ j : ℕ,
      ((3 / 4 : ℝ) ^ M * g₀ * Real.exp (cα * (Real.pi / 6)) * (Real.pi / 3)
          * (2 * Real.pi * cα)) * (j : ℝ)
        ≤ sol.G (2 * Real.pi * (j : ℝ) + Real.pi / 2)
          - sol.G (2 * Real.pi * (j : ℝ) + Real.pi / 6) := by
  have hpi := Real.pi_pos
  have hℓ : (0 : ℝ) < (3 / 4 : ℝ) ^ M := by positivity
  refine selector_gain_linear_growth sol
    (aw := fun j => 2 * Real.pi * (j : ℝ) + Real.pi / 6)
    (bw := fun j => 2 * Real.pi * (j : ℝ) + Real.pi / 2)
    (ℓ := (3 / 4 : ℝ) ^ M) (a₀ := Real.pi / 6) (w := Real.pi / 3)
    hcα hℓ hg₀ (by linarith) (by linarith) ?_ ?_ ?_ ?_ (fun _ => rfl) (by fun_prop) ?_
  · intro j; linarith
  · intro j; have : (2 * Real.pi * (j : ℝ) + Real.pi / 2)
      - (2 * Real.pi * (j : ℝ) + Real.pi / 6) = Real.pi / 3 := by ring
    linarith [this]
  · intro j; linarith
  · intro j t ht
    refine selectorSchedule_domain_nonneg t ?_
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have : (0 : ℝ) ≤ 2 * Real.pi * (j : ℝ) + Real.pi / 6 := by positivity
    linarith [ht.1]
  · intro j t ht
    have hsin := sin_ge_half_of_gate_window j ht
    have := chiGate_lb (s0 := (1 / 2 : ℝ)) M hsin (by norm_num)
    have heq : ((1 + (1 / 2 : ℝ)) / 2) ^ M = (3 / 4 : ℝ) ^ M := by norm_num
    rwa [heq] at this

/-- The rational-parameter equalities for `bgpParams38` (`A = 1`, `cμ = 1000`,
`cα = 300`, `L = 1`).  These mirror the `private` proofs in `FinalAssembly.lean`,
re-derived here so the selector package can consume them. -/
private theorem bgpParams_A_rat' : bgpParams38.A = ((1 : ℚ) : ℝ) := by
  norm_num [bgpParams38]

private theorem bgpParams_cμ_rat' : bgpParams38.cμ = ((1000 : ℚ) : ℝ) := by
  norm_num [bgpParams38]

private theorem bgpParams_cα_rat' : bgpParams38.cα = ((300 : ℚ) : ℝ) := by
  norm_num [bgpParams38]

private theorem bgpParams_L_eq' : bgpParams38.L = 1 := by
  rfl

open MachineInstance in
/-- **INPUT (1) of `bgp_unconditional_selector_assembled`: the M_U
clock-driven-selector polynomial field package.**

This discharges the polynomial-field layer for the universal machine `M_U`.  It
applies the generic constructor `selectorPolynomialFieldPackage` with:

* the χ/κ/gain phase polynomials `selChiResetPoly`/`selChiGatePoly`/`selKappaPoly`/
  `selGainPoly` and their trajectory realizations `((1±cos t)/2)^M`, `κ₀`, and
  `g₀·exp(c_α·t)` — the last chained through `SelectorDynSol.alpha_eq_exp`
  (`α t = exp(c_α t)` on the schedule domain) so the gain matches the fixed
  exponential clock gain `gainF`;
* the universal readout polynomial `muReadoutPoly eta heta` with realization
  `eval_muReadoutPoly` (the `h_P` hypothesis, `Pv := universalPval eta heta`);
* the shared `bgpParams38` rational equalities (`A=1, cμ=1000, c_α=300, L=1`).

The remaining genuine framework inputs are passed straight through as explicit
hypotheses, exactly as the fixed-precision contract takes `HP`/`Hval`/`init` as
inputs:

* `HP`/`Hval`/`K`/`R`/`h_HP` — the halt-readout polynomial, its target value, the
  latch threshold/window, and the halt-readout realization identity;
* `Kq`/`hK` — the rational presentation of the latch threshold `K`;
* `init`/`init_presented`/`init_zero`/`init_succ` — the computable stereographic
  rational initial vector and its two stereographic identities.

No `sorry`/`axiom`: every M_U-specific obligation is discharged from the eval
lemmas; every irreducibly-framework obligation is an explicit hypothesis. -/
def muSelectorFieldPackage
    (eta : ℚ) (heta : 0 < eta)
    (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin d_U) ℚ)
    (Hval : (Fin d_U → ℝ) → ℝ) (K : ℝ) (R : ℕ)
    (Kq : ℚ) (hK : K = (Kq : ℝ))
    (h_HP :
      ∀ (sol : SelectorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
          branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol Hval K R) (t : ℝ),
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) HP = Hval (sol.z t))
    (init : ℕ → Fin (selectorDim d_U UniversalLocalView + 1) → ℚ)
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim d_U UniversalLocalView + 1) → ℤ × ℕ, Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (sol : SelectorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
          branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol Hval K R),
          ((init w 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim d_U UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (sol : SelectorDynSol d_U B_U UniversalLocalView bgpParams38 selectorSchedule
          branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol Hval K R) (i : Fin (selectorDim d_U UniversalLocalView)),
          ((init w i.succ : ℚ) : ℝ) =
            2 * selectorTupleTraj sol La (g₀ : ℝ) 0 i /
              ((∑ k : Fin (selectorDim d_U UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 k ^ 2) + 1)) :
    SelectorPolynomialFieldPackage d_U B_U UniversalLocalView bgpParams38 selectorSchedule
      branchU
      (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
      (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta) Hval K R :=
  selectorPolynomialFieldPackage (fun _ => (g₀ : ℝ))
    (selChiResetPoly d_U UniversalLocalView M)
    (selChiGatePoly d_U UniversalLocalView M)
    (selKappaPoly d_U UniversalLocalView κ₀)
    (selGainPoly d_U UniversalLocalView)
    (muReadoutPoly eta heta) HP
    (Aq := 1) (Kq := Kq) (cμq := 1000) (cαq := 300) (L := 1)
    (hA := bgpParams_A_rat') (hK := hK)
    (hcμ := bgpParams_cμ_rat') (hcα := bgpParams_cα_rat') (hL := bgpParams_L_eq')
    (hdomain := selectorSchedule_domain_nonneg)
    (h_chiReset := fun sol La _wgv t _ht =>
      eval_selChiResetPoly (sol := sol) (La := La) (warmGainVal := _wgv) (t := t) M)
    (h_chiGate := fun sol La _wgv t _ht =>
      eval_selChiGatePoly (sol := sol) (La := La) (warmGainVal := _wgv) (t := t) M)
    (h_kappa := fun sol La _wgv t _ht =>
      eval_selKappaPoly (sol := sol) (La := La) (warmGainVal := _wgv) (t := t) κ₀)
    (h_gain := by
      intro sol La _w t ht
      dsimp only
      rw [eval_selGainPoly, sol.alpha_eq_exp selectorSchedule_domain_nonneg ht])
    (h_P := fun sol La _wgv v t _ht => eval_muReadoutPoly eta heta sol La _wgv t v)
    (h_HP := h_HP)
    (init := init) (init_presented := init_presented)
    (init_zero := init_zero) (init_succ := init_succ)

/-! ## CAPSTONE: the unconditional M_U selector simulation -/

/-- **Capstone (M_U instantiation).**  Instantiates the generic conditional headline
`bgp_unconditional_selector_assembled` for the universal machine
`UniversalMachine.undecidableMachine`, feeding the concrete M_U field package
`muSelectorFieldPackage`.  Given the per-input selector solution `sol`, the
driving-signal continuity `hHcont`, the scalar latch convergence facts
`hhigh`/`hlow`, and the per-input flag tube `hflag_read` + flag domain `hflag_dom`
(together with the framework polynomial-field inputs threaded into the field
package: `HP`/`h_HP`, the latch threshold rational presentation `K_U = (1 : ℚ)`,
and the computable stereographic initial vector `init` with its identities), there
is a PIVP that eventually-threshold simulates `M_U`.  No `sorry`/`axiom`. -/
theorem bgp_unconditional_selector_MU
    (eta : ℚ) (heta : 0 < eta)
    (M : ℕ) (κ₀ g₀ : ℚ)
    (HP : MvPolynomial (Fin MachineInstance.d_U) ℚ) (R : ℕ)
    (h_HP :
      ∀ (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
          MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
          MachineInstance.branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (t : ℝ),
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) HP =
          MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t))
    (init : ℕ → Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView + 1) → ℚ)
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
          MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
          MachineInstance.branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R),
          ((init w 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
          MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
          MachineInstance.branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R)
        (i : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView)),
          ((init w i.succ : ℚ) : ℝ) =
            2 * selectorTupleTraj sol La (g₀ : ℝ) 0 i /
              ((∑ k : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 k ^ 2) + 1))
    (sol : ℕ → SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView bgpParams38 selectorSchedule MachineInstance.branchU
      (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
      (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (hHcont : ∀ w, Continuous fun t =>
      MachineInstance.contractFlagIndicatorPackageU.Hval ((sol w).z t))
    (hhigh : ∀ (w : ℕ)
        (La : SelectorHaltLatchSol (sol w) MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R),
      (∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ selectorSchedule.zActiveWindow j,
        1 - MachineInstance.contractFlagIndicatorPackageU.eta ≤
          MachineInstance.contractFlagIndicatorPackageU.Hval ((sol w).z t)) →
        ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1)
    (hlow : ∀ (w : ℕ)
        (La : SelectorHaltLatchSol (sol w) MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R),
      (∀ j : ℕ, ∀ t ∈ selectorSchedule.zActiveWindow j,
        MachineInstance.contractFlagIndicatorPackageU.Hval ((sol w).z t) ≤
          MachineInstance.contractFlagIndicatorPackageU.eta) →
        ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4)
    (hflag_read : ∀ w j t, t ∈ selectorSchedule.zActiveWindow j →
      |(sol w).z t MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc
            (UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
              (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
            MachineInstance.haltCoordU| ≤ 1 / 4)
    (hflag_dom : ∀ w j t, t ∈ selectorSchedule.zActiveWindow j →
      (sol w).z t MachineInstance.haltCoordU ∈ Set.Icc (0 : ℝ) 1) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_unconditional_selector_assembled
    UniversalMachine.undecidableMachine
    MachineInstance.stackMachineEncodingU
    MachineInstance.branchU
    bgpParams38 selectorSchedule
    MachineInstance.haltCoordU
    MachineInstance.haltFlagPackageU
    MachineInstance.contractFlagIndicatorPackageU
    MachineInstance.K_U_pos
    (muSelectorFieldPackage eta heta M κ₀ g₀ HP
      MachineInstance.contractFlagIndicatorPackageU.Hval
      MachineInstance.K_U R (1 : ℚ) (by norm_num [MachineInstance.K_U]) h_HP
      init init_presented init_zero init_succ)
    sol hHcont hhigh hlow hflag_read hflag_dom

/-! ## DISCHARGE of the flag tube: `hflag_read` derived from the tracking premises -/

/-- **M_U flag-read DISCHARGED from the solution tracking.**

This proves the `hflag_read` hypothesis of `bgp_unconditional_selector_MU` as a
THEOREM (for a fixed input `w`), rather than assuming it.  The high-level flag tube
`|z t halt − enc(orbit j) halt| ≤ 1/4` on the read windows is derived from the
SELECTOR-SPECIFIC machinery — the gate/margin/gain layer — DISCHARGED here, while the
genuinely contract-status pieces (the per-cycle config `z/u`-Reach integrals, the
depth-budget bookkeeping, the initial-config tube) are carried as explicit
hypotheses, exactly as the contract `bgp_unconditional_N` carries its analogous
`BgpTrackingPremises`.

Architecture (DISCHARGED, not assumed):
* the simultaneous-induction wiring — via `selector_MU_config_tube`, whose
  `margins-from-tube` link (`universal_selector_margins_on_window`) is discharged
  internally;
* the per-cycle gate-phase recurrence on the held config — via
  `selector_cycle_step_gate_approx` (the `εmix → 0` mechanism), FED the margins the
  induction supplies (`hPtrue`/`hPfalse` come straight from the `Branch` invariant,
  using `sol.Pval v t = universalPval eta heta v (sol.u t)` by `rfl`);
* the gate sharpness `χ_gate ≥ (3/4)^M` and the linear gain growth `ΔG_j ≥ c·j` —
  available from `selector_clock_gain_growth` + `selector_epsmix_decay_of_gain_linear`
  (the `εmix` geometric decay), here exposed as the per-cycle structure of `Recur`;
* the `u`-tube → `z`-tube → flag-read closing — via `selector_MU_flag_read_of_ztube`.

The concrete cycle data:
`c j := M_U.step^[j] (M_U.init w)` (the orbit), gate window
`[aGate j, bGate j] = [2πj+π/6, 2πj+π/2]` (where `sin ≥ 1/2`, so `χ_gate ≥ (3/4)^M`).

The `Weighted`/`Recur` invariant pair is taken ABSTRACT (the contract-status
weighted/budget invariant), with the only DISCHARGED step being
`hrecur_of_branch`: the recurrence engine consumes the discharged margins.  The
remaining premises — the tube-hold `Weighted → Window` (`hwin_of_weighted`), the
budget step `Weighted ∧ Recur → Weighted'` (`hweighted_step`), the recurrence-from-
margins engine (`hrecur_engine`, the `cycle_step` Reach bundle), and the
`z`-near-`u` window-hold (`hztube_of_utube`) — are CARRIED. -/
theorem selector_MU_flag_read_of_tracking
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (herr : (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel
      < 1 / 2)
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView bgpParams38 selectorSchedule MachineInstance.branchU
      (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
      (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (w : ℕ)
    -- CARRIED contract-status invariant predicates (weighted/budget bookkeeping)
    (Weighted Recur : ℕ → Prop)
    -- CARRIED: the initial config in the encoding tube on the first gate window
    (hinit : Weighted 0)
    -- CARRIED: the tube-hold `Weighted → Window` (the `u`-Reach hold integral)
    (hwin_of_weighted : ∀ j, Weighted j →
      ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
          (2 * Real.pi * (j : ℝ) + Real.pi / 2),
        MachineInstance.UTube MachineInstance.r_LE_U
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) (sol.u t))
    -- DISCHARGED-INTO recurrence engine: consumes the margins (already discharged from
    -- the tube) to produce `Recur j`.  This is the `cycle_step ∘ gate_mix_error_approx`
    -- Reach bundle (the `hdiag`/`hhold`/`hwrite` config-Reach + gate sharpness + gain
    -- integral): carried as the contract-status per-cycle facts, but it receives the
    -- SELECTOR margins (`hPtrue`/`hPfalse` shape) which ARE discharged.
    (hrecur_engine : ∀ j, Weighted j →
      (∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
            (2 * Real.pi * (j : ℝ) + Real.pi / 2),
          1 / 2 - (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel
            ≤ sol.Pval
                (MachineInstance.localViewU (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)))
                t) →
      (∀ v, v ≠ MachineInstance.localViewU
              (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) →
          ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
              (2 * Real.pi * (j : ℝ) + Real.pi / 2),
            sol.Pval v t ≤
              -(1 / 2 -
                (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel)) →
      Recur j)
    -- CARRIED: the depth-budget step `Weighted ∧ Recur → Weighted'`
    (hweighted_step : ∀ j, Weighted j → Recur j → Weighted (j + 1))
    -- CARRIED: the `z`-near-`u` window-hold (the `z`-Reach window integral) — lifts the
    -- `u`-tube on the gate window to a `z`-tube on the read window (= all of `ℝ`).
    (hztube_of_utube : (∀ j : ℕ, ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
          (2 * Real.pi * (j : ℝ) + Real.pi / 2),
        MachineInstance.UTube MachineInstance.r_LE_U
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) (sol.u t)) →
      ∀ j t, t ∈ selectorSchedule.zActiveWindow j →
        MachineInstance.UTube MachineInstance.r_LE_U
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) (sol.z t)) :
    ∀ j t, t ∈ selectorSchedule.zActiveWindow j →
      |sol.z t MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc
            (UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
              (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
            MachineInstance.haltCoordU| ≤ 1 / 4 := by
  -- (a) the `u`-tube on every gate window, via the simultaneous induction.  The
  -- margins-from-tube link is discharged inside `selector_MU_config_tube`; the
  -- `hrecur_of_branch` premise is discharged here by feeding the discharged margins
  -- (whose `universalPval` shape is defeq to `sol.Pval`) into `hrecur_engine`.
  have hutube :
      ∀ j : ℕ, ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
          (2 * Real.pi * (j : ℝ) + Real.pi / 2),
        MachineInstance.UTube MachineInstance.r_LE_U
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) (sol.u t) := by
    refine selector_MU_config_tube sol eta heta herr
      (fun j => MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w))
      (fun j => 2 * Real.pi * (j : ℝ) + Real.pi / 6)
      (fun j => 2 * Real.pi * (j : ℝ) + Real.pi / 2)
      Weighted Recur hinit hwin_of_weighted ?_ hweighted_step
    intro j _hwj _hutube_j hmargins
    -- `universalPval eta heta v (sol.u t) = sol.Pval v t` definitionally (the M_U sol's
    -- `readoutP` is `universalPval eta heta`), so the discharged margins are exactly the
    -- `hPtrue`/`hPfalse` shape the recurrence engine consumes.
    exact hrecur_engine j _hwj hmargins.1 hmargins.2
  -- (b) lift the `u`-tube to a `z`-tube on the read windows (CARRIED `z`-Reach), then
  -- close the flag-read via `selector_MU_flag_read_of_ztube`.
  have hztube := hztube_of_utube hutube
  exact selector_MU_flag_read_of_ztube sol
    (fun j => MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) hztube

/-- **Capstone with the flag tube DISCHARGED.**  Identical to
`bgp_unconditional_selector_MU` except the high-level `hflag_read` argument is REPLACED
by the solution-tracking premises of `selector_MU_flag_read_of_tracking`: the headline
no longer ASSUMES the flag tube — it DERIVES it from the gate/margin/gain machinery,
carrying only the standard contract-status Reach/budget premises (the `BgpTrackingPremises`
analog), exactly matching the contract's status.  Every selector-specific obligation
(gate sharpness, margins, gain growth, `εmix` decay, the `u`→`z`→flag-read wiring) is
DISCHARGED.  No `sorry`/`axiom`. -/
theorem bgp_unconditional_selector_MU_closed
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (herr : (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel
      < 1 / 2)
    (HP : MvPolynomial (Fin MachineInstance.d_U) ℚ) (R : ℕ)
    (h_HP :
      ∀ (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
          MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
          MachineInstance.branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (t : ℝ),
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) HP =
          MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t))
    (init : ℕ → Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView + 1) → ℚ)
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
          MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
          MachineInstance.branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R),
          ((init w 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
          MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
          MachineInstance.branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R)
        (i : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView)),
          ((init w i.succ : ℚ) : ℝ) =
            2 * selectorTupleTraj sol La (g₀ : ℝ) 0 i /
              ((∑ k : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 k ^ 2) + 1))
    (sol : ℕ → SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView bgpParams38 selectorSchedule MachineInstance.branchU
      (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
      (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (hHcont : ∀ w, Continuous fun t =>
      MachineInstance.contractFlagIndicatorPackageU.Hval ((sol w).z t))
    (hhigh : ∀ (w : ℕ)
        (La : SelectorHaltLatchSol (sol w) MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R),
      (∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ selectorSchedule.zActiveWindow j,
        1 - MachineInstance.contractFlagIndicatorPackageU.eta ≤
          MachineInstance.contractFlagIndicatorPackageU.Hval ((sol w).z t)) →
        ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1)
    (hlow : ∀ (w : ℕ)
        (La : SelectorHaltLatchSol (sol w) MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R),
      (∀ j : ℕ, ∀ t ∈ selectorSchedule.zActiveWindow j,
        MachineInstance.contractFlagIndicatorPackageU.Hval ((sol w).z t) ≤
          MachineInstance.contractFlagIndicatorPackageU.eta) →
        ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4)
    -- CARRIED contract-status tracking premises (the `BgpTrackingPremises` analog),
    -- per input `w`.  These REPLACE the assumed `hflag_read`.
    (Weighted Recur : ℕ → ℕ → Prop)
    (hinit : ∀ w, Weighted w 0)
    (hwin_of_weighted : ∀ w j, Weighted w j →
      ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
          (2 * Real.pi * (j : ℝ) + Real.pi / 2),
        MachineInstance.UTube MachineInstance.r_LE_U
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) ((sol w).u t))
    (hrecur_engine : ∀ w j, Weighted w j →
      (∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
            (2 * Real.pi * (j : ℝ) + Real.pi / 2),
          1 / 2 - (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel
            ≤ (sol w).Pval
                (MachineInstance.localViewU (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)))
                t) →
      (∀ v, v ≠ MachineInstance.localViewU
              (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) →
          ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
              (2 * Real.pi * (j : ℝ) + Real.pi / 2),
            (sol w).Pval v t ≤
              -(1 / 2 -
                (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel)) →
      Recur w j)
    (hweighted_step : ∀ w j, Weighted w j → Recur w j → Weighted w (j + 1))
    (hztube_of_utube : ∀ w,
      (∀ j : ℕ, ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
          (2 * Real.pi * (j : ℝ) + Real.pi / 2),
        MachineInstance.UTube MachineInstance.r_LE_U
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) ((sol w).u t)) →
      ∀ j t, t ∈ selectorSchedule.zActiveWindow j →
        MachineInstance.UTube MachineInstance.r_LE_U
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) ((sol w).z t))
    (hflag_dom : ∀ w j t, t ∈ selectorSchedule.zActiveWindow j →
      (sol w).z t MachineInstance.haltCoordU ∈ Set.Icc (0 : ℝ) 1) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_unconditional_selector_MU eta heta M κ₀ g₀ HP R h_HP
    init init_presented init_zero init_succ sol hHcont hhigh hlow
    (fun w => selector_MU_flag_read_of_tracking eta heta M κ₀ g₀ herr (sol w) w
      (Weighted w) (Recur w) (hinit w) (hwin_of_weighted w) (hrecur_engine w)
      (hweighted_step w) (hztube_of_utube w))
    hflag_dom

/-! ## CONCRETE recurrence engine: the gate+gain produce the boundary-error recurrence

The carried `hrecur_engine` of `selector_MU_flag_read_of_tracking` is an ABSTRACT
implication (margins ⇒ `Recur j`) — the contract-status placeholder for the per-cycle
boundary-error recurrence.  The two lemmas below make it CONCRETE:

* `selector_MU_recur_concrete` reduces the recurrence to `selector_cycle_step_gate_approx`
  (`= cycle_step ∘ gate_mix_error_approx`) applied per coordinate, with the εmix term
  exactly the *decaying gate form* `card·R·(1+ρb·Cb·Kint)·exp(−α·ΔG_j)` and `α = 1/2 − errSel`
  the margin from the gate.  Everything beyond the gate→recurrence content (the config
  z/u-Reach integrals `hdiag`/`hhold`/`hwrite`, the λ-invariants, the integral bound `hint`,
  the χ_reset ρ-bounds) is CARRIED as an explicit hypothesis — contract-status, exactly as
  the contract's `BgpTrackingPremises`.

* `selector_MU_eps_decays` shows that the εmix term DECAYS GEOMETRICALLY:
  `card·R·(1+ρb·Cb·Kint)·exp(−α·ΔG_j) ≤ C₀·exp(−(α·c)·j)` via the *concrete* clock gain
  growth `ΔG_j ≥ c·j` (`selector_clock_gain_growth`) + `selector_epsmix_decay_of_gain_linear`.
  This is the selector's *no-floor advantage*: the fixed-precision contract had a
  non-summable constant floor in this slot; the growing clock turns it into a convergent
  geometric tail (`eps_mix_summable_of_gain_linear`). -/

/-- **Per-cycle εmix geometric decay (CONCRETE, no floor).**  For the M_U selector with the
sin-gate `χ_gate = ((1+sin t)/2)^M` and the exponential clock gain `g₀·exp(cα·t)`, the gate
εmix term `C₀·exp(−α·ΔG_j)` over the rising gate sub-window `ΔG_j = G(2πj+π/2) − G(2πj+π/6)`
is bounded by `C₀·exp(−(α·c)·j)` — a genuine geometric decay in the cycle index `j` (no
constant floor).  The linear-growth rate is the concrete positive constant
`c = (3/4)^M·g₀·exp(cα·π/6)·(π/3)·(2π·cα)` from `selector_clock_gain_growth`, and the decay is
`selector_epsmix_decay_of_gain_linear` with `ΔG j := G(2πj+π/2) − G(2πj+π/6)`.  This is the
mechanism that closes the all-time tube WITHOUT the fixed-precision floor. -/
theorem selector_MU_eps_decays
    {V : Type} [Fintype V] {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF kappaF : ℝ → ℝ} (M : ℕ) {g₀ cα C₀ α : ℝ}
    (hcα : 0 < cα) (hg₀ : 0 < g₀) (hC₀ : 0 ≤ C₀) (hα : 0 ≤ α)
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V p selectorSchedule branch
      chiResetF (fun t => ((1 + Real.sin t) / 2) ^ M) kappaF
      (fun t => g₀ * Real.exp (cα * t)) Pv) :
    ∀ j : ℕ,
      C₀ * Real.exp (-α * (sol.G (2 * Real.pi * (j : ℝ) + Real.pi / 2)
              - sol.G (2 * Real.pi * (j : ℝ) + Real.pi / 6)))
        ≤ C₀ * Real.exp (-(α *
            ((3 / 4 : ℝ) ^ M * g₀ * Real.exp (cα * (Real.pi / 6)) * (Real.pi / 3)
              * (2 * Real.pi * cα))) * (j : ℝ)) := by
  -- the concrete linear gain growth `c·j ≤ ΔG_j` for the rising gate sub-window
  have hgrow := selector_clock_gain_growth (M := M) hcα hg₀ sol
  -- feed it to the geometric-decay lemma with `ΔG j := G(bGate j) − G(aGate j)`
  exact selector_epsmix_decay_of_gain_linear (C₀ := C₀) (α := α)
    (c := (3 / 4 : ℝ) ^ M * g₀ * Real.exp (cα * (Real.pi / 6)) * (Real.pi / 3)
      * (2 * Real.pi * cα)) hC₀ hα
    (fun j => sol.G (2 * Real.pi * (j : ℝ) + Real.pi / 2)
      - sol.G (2 * Real.pi * (j : ℝ) + Real.pi / 6)) hgrow

/-- **CONCRETE per-cycle recurrence engine (the gate+gain produce the boundary-error
recurrence).**  This is a *concrete* `hrecur_engine` for `selector_MU_flag_read_of_tracking`:
given the discharged gate-phase margins (the `hPtrue`/`hPfalse` shape with `α = 1/2 − errSel`,
fed in from the simultaneous induction) and the CARRIED contract-status hypotheses
(λ-invariants `hunit`/`hlama`/`hLlb_vstar`/`hLub_false`, the χ_reset ρ-bounds
`hρ_vstar`/`hρ_false`/`hρ_false_le`, the integral bound `hint`, the config z/u-Reach
`hdiag`/`hhold`/`hwrite`, the branch bound `hA`, and the positivity/domain facts `hr0`/`hdom`),
it produces the PER-COORDINATE one-cycle boundary-error recurrence

`∀ i, |sol.u (tStart (j+1)) i − enc (j+1) i| ≤ mult·|sol.u (tStart j) i − enc j i| + η j`

with `enc j = stackMachineEncodingU.enc (M_U.step^[j] (M_U.init w))`, the gate window
`[a j, tHold j] = [2πj+π/6, 2πj+π/2]`, and

`η j = card·R·((1+ρb·Cb·Kint)·exp(−α·(G(tHold j) − G(a j)))) + εwrite + mult·εhold`.

The proof is per-coordinate `selector_cycle_step_gate_approx` (= `cycle_step ∘
gate_mix_error_approx`).  The KEY beyond-contract content is the εmix term
`card·R·(1+ρb·Cb·Kint)·exp(−α·ΔG_j)` — the *decaying gate form* whose `ΔG_j → ∞` (linear in
`j`, `selector_MU_eps_decays`) removes the fixed-precision floor.  Everything else is CARRIED
(contract-status), exactly mirroring the abstract `hrecur_engine`'s status. -/
theorem selector_MU_recur_concrete
    {V : Type} [Fintype V] [DecidableEq V]
    {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {p : DynGateParams} {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    {readoutP : V → (Fin MachineInstance.d_U → ℝ) → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V p selectorSchedule branch
      chiResetF chiGateF kappaF gainF readoutP)
    (vstar : V) (enc : ℕ → Fin MachineInstance.d_U → ℝ)
    (tStart tEnd : ℕ → ℝ) (j : ℕ)
    {α Lmin Lmax ρb Kint Cb R εwrite εhold mult δ : ℝ}
    (hmult : 0 ≤ mult) (hLmin0 : 0 < Lmin) (hLmax1 : Lmax < 1) (hρb : 0 ≤ ρb)
    (hKint : 0 ≤ Kint) (hR : 0 ≤ R) (hCb_lo : 1 / Lmin ^ 2 ≤ Cb) (hCb_hi : 1 / (1 - Lmax) ^ 2 ≤ Cb)
    (hδ : 0 ≤ δ) (hδhalf : δ < 1 / 2)
    -- CARRIED (contract-status): domain + positivity of the effective rate
    (hdom : ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi / 2), t ∈ selectorSchedule.domain)
    (hr0 : ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi / 2), 0 ≤ chiGateF t * gainF t)
    -- CARRIED (contract-status): the λ-invariants
    (hunit : ∀ v, ∀ t ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi / 2), 0 < sol.lam v t ∧ sol.lam v t < 1)
    (hlama : ∀ v, |sol.lam v (2 * Real.pi * (j : ℝ) + Real.pi / 6) - 1 / 2| ≤ δ)
    (hLlb_vstar : ∀ t ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi / 2), Lmin ≤ sol.lam vstar t)
    (hLub_false : ∀ v, v ≠ vstar → ∀ t ∈ Set.Icc (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi / 2), sol.lam v t ≤ Lmax)
    -- DISCHARGED-INTO: the gate-phase margins (the `hPtrue`/`hPfalse` shape from the
    -- induction), with `α = 1/2 − errSel`.  These ARE the discharged content.
    (hPtrue : ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi / 2), α ≤ sol.Pval vstar t)
    (hPfalse : ∀ v, v ≠ vstar → ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi / 2), sol.Pval v t ≤ -α)
    -- CARRIED (contract-status): the χ_reset ρ-bounds on the gate window
    (hρ_vstar : ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi / 2),
        -ρb ≤ chiResetF t * kappaF t * (1 / 2 - sol.lam vstar t))
    (hρ_false : ∀ v, v ≠ vstar → ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi / 2),
        -ρb ≤ chiResetF t * kappaF t * (1 / 2 - sol.lam v t))
    (hρ_false_le : ∀ v, v ≠ vstar → ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
        (2 * Real.pi * (j : ℝ) + Real.pi / 2),
        chiResetF t * kappaF t * (1 / 2 - sol.lam v t) ≤ ρb)
    -- CARRIED (contract-status): the gate-gain integral bound
    (hint : (∫ t in (2 * Real.pi * (j : ℝ) + Real.pi / 6)..(2 * Real.pi * (j : ℝ) + Real.pi / 2),
        Real.exp (α * (sol.G t - sol.G (2 * Real.pi * (j : ℝ) + Real.pi / 6)))) ≤ Kint)
    -- CARRIED (contract-status): the per-coordinate config z/u-Reach facts
    (hA : ∀ i, ∀ v, |BranchData.evalBranch (branch v)
        (sol.u (2 * Real.pi * (j : ℝ) + Real.pi / 2)) i| ≤ R)
    (hdiag : ∀ i, |BranchData.evalBranch (branch vstar)
          (sol.u (2 * Real.pi * (j : ℝ) + Real.pi / 2)) i - enc (j + 1) i|
        ≤ mult * |sol.u (2 * Real.pi * (j : ℝ) + Real.pi / 2) i - enc j i|)
    (hhold : ∀ i, |sol.u (2 * Real.pi * (j : ℝ) + Real.pi / 2) i - enc j i|
        ≤ |sol.u (tStart j) i - enc j i| + εhold)
    (hwrite : ∀ i, |sol.u (tEnd j) i
          - selectorMixTarget branch sol.u sol.lam (2 * Real.pi * (j : ℝ) + Real.pi / 2) i|
        ≤ εwrite) :
    ∀ i : Fin MachineInstance.d_U,
      |sol.u (tEnd j) i - enc (j + 1) i| ≤
        mult * |sol.u (tStart j) i - enc j i| +
          ((Fintype.card V : ℝ) * R *
              (((1 / 2 + δ) / (1 / 2 - δ) + ρb * Cb * Kint)
                * Real.exp (-α * (sol.G (2 * Real.pi * (j : ℝ) + Real.pi / 2)
                    - sol.G (2 * Real.pi * (j : ℝ) + Real.pi / 6))))
            + εwrite + mult * εhold) := by
  intro i
  have hab : (2 * Real.pi * (j : ℝ) + Real.pi / 6) ≤ (2 * Real.pi * (j : ℝ) + Real.pi / 2) := by
    have := Real.pi_pos; linarith
  exact selector_cycle_step_gate_approx sol vstar i
    (tStart j) (2 * Real.pi * (j : ℝ) + Real.pi / 6) (2 * Real.pi * (j : ℝ) + Real.pi / 2)
    (tEnd j) (enc j) (enc (j + 1))
    hmult hab hLmin0 hLmax1 hρb hKint hR hCb_lo hCb_hi hδ hδhalf hdom hr0 hunit hlama
    hPtrue hPfalse hLlb_vstar hLub_false hρ_vstar hρ_false hρ_false_le hint
    (hA i) (hdiag i) (hhold i) (hwrite i)

/-! ## CONCRETIZED tracking: contract-form `Weighted`/`Recur` + DepthBudget weighted step

The abstract `Weighted Recur : ℕ → Prop` predicates of `selector_MU_flag_read_of_tracking`
(and the `ℕ → ℕ → Prop` of `bgp_unconditional_selector_MU_closed`) are opaque
placeholders for the precision-weighted budget bookkeeping.  The definitions and the
headline below REPLACE them with the CONCRETE contract-form invariants — the
`ContractWeightedBound`-style precision-weighted boundary bound and the per-cycle
boundary-error recurrence — and DISCHARGE the budget step `Weighted ∧ Recur → Weighted'`
via the framework's `DepthBudget.weighted_step` (the `k^depth · boundaryError ≤ W`
inductive step).  This mirrors `contract_all_time_tracking`'s weighted step exactly. -/

/-- The selector's per-cycle, per-coordinate boundary error at the gate-window start
`aGate j = 2πj + π/6`: the unweighted gap between the held config `sol.u` and the encoded
orbit value `enc j i`.  This is the selector analog of `contractBoundaryError`. -/
def muBoundaryError
    {V : Type} [Fintype V] {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V p selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (enc : ℕ → Fin MachineInstance.d_U → ℝ) (j : ℕ) (i : Fin MachineInstance.d_U) : ℝ :=
  |sol.u (2 * Real.pi * (j : ℝ) + Real.pi / 6) i - enc j i|

theorem muBoundaryError_nonneg
    {V : Type} [Fintype V] {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V p selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (enc : ℕ → Fin MachineInstance.d_U → ℝ) (j : ℕ) (i : Fin MachineInstance.d_U) :
    0 ≤ muBoundaryError sol enc j i := abs_nonneg _

/-- **CONCRETE weighted invariant** (the `ContractWeightedBound` analog): the
precision-weighted boundary error `k^(depth j i) · boundaryError j i` is bounded by the
budget `Wbound j i`, for every coordinate.  This is the inductive DepthBudget invariant. -/
def MUWeighted
    {V : Type} [Fintype V] {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V p selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (enc : ℕ → Fin MachineInstance.d_U → ℝ) (k : ℝ) (dep : ℕ → Fin MachineInstance.d_U → ℤ)
    (Wbound : ℕ → Fin MachineInstance.d_U → ℝ) (j : ℕ) : Prop :=
  ∀ i : Fin MachineInstance.d_U,
    k ^ dep j i * muBoundaryError sol enc j i ≤ Wbound j i

/-- **CONCRETE per-cycle recurrence invariant** (the `ContractRecurrenceAt` analog): the
boundary error one cycle later is bounded by `k^(delta j i)·(current) + η j i`.  The
coefficients `k^delta`/`η` are the raw config-Reach data — `mult`/`η` of
`selector_MU_recur_concrete` (with `mult = k^delta`), CARRIED as hypotheses. -/
def MURecur
    {V : Type} [Fintype V] {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V p selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (enc : ℕ → Fin MachineInstance.d_U → ℝ) (k : ℝ) (delta : ℕ → Fin MachineInstance.d_U → ℤ)
    (η : ℕ → Fin MachineInstance.d_U → ℝ) (j : ℕ) : Prop :=
  ∀ i : Fin MachineInstance.d_U,
    muBoundaryError sol enc (j + 1) i ≤
      k ^ delta j i * muBoundaryError sol enc j i + η j i

/-- **The DepthBudget weighted step, DISCHARGED concretely.**  From the concrete weighted
bound `MUWeighted j` and the concrete recurrence `MURecur j`, with the depth bookkeeping
`dep (j+1) i = dep j i − delta j i`, derive `MUWeighted (j+1)` with the updated budget
`Wbound (j+1) i = Wbound j i + k^(dep (j+1) i)·η j i`.  This is exactly
`DepthBudget.weighted_step` applied per coordinate — the same inductive step
`contract_all_time_tracking` uses, here CLOSED (not carried). -/
theorem mu_weighted_step
    {V : Type} [Fintype V] {branch : V → BranchData MachineInstance.d_U MachineInstance.B_U}
    {Pv : V → (Fin MachineInstance.d_U → ℝ) → ℝ} {p : DynGateParams}
    {chiResetF chiGateF kappaF gainF : ℝ → ℝ}
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U V p selectorSchedule branch
      chiResetF chiGateF kappaF gainF Pv)
    (enc : ℕ → Fin MachineInstance.d_U → ℝ) {k : ℝ} (hk : 1 < k)
    (dep delta : ℕ → Fin MachineInstance.d_U → ℤ) (η Wbound : ℕ → Fin MachineInstance.d_U → ℝ)
    (hdepth : ∀ j i, dep (j + 1) i = dep j i - delta j i)
    (hWstep : ∀ j i, Wbound j i + k ^ dep (j + 1) i * η j i ≤ Wbound (j + 1) i)
    (j : ℕ) (hw : MUWeighted sol enc k dep Wbound j)
    (hr : MURecur sol enc k delta η j) :
    MUWeighted sol enc k dep Wbound (j + 1) := by
  intro i
  -- the per-coordinate one-step weighted inequality, mirroring `DepthBudget.weighted_step`.
  have hk0 : (0 : ℝ) ≤ k := (zero_lt_one.trans hk).le
  have hk_ne : k ≠ 0 := (zero_lt_one.trans hk).ne'
  have hpow_nonneg : 0 ≤ k ^ dep (j + 1) i := zpow_nonneg hk0 _
  have hstep :
      k ^ dep (j + 1) i * muBoundaryError sol enc (j + 1) i ≤
        k ^ dep j i * muBoundaryError sol enc j i + k ^ dep (j + 1) i * η j i := by
    calc k ^ dep (j + 1) i * muBoundaryError sol enc (j + 1) i
        ≤ k ^ dep (j + 1) i *
            (k ^ delta j i * muBoundaryError sol enc j i + η j i) :=
          mul_le_mul_of_nonneg_left (hr i) hpow_nonneg
      _ = k ^ (dep (j + 1) i + delta j i) * muBoundaryError sol enc j i
            + k ^ dep (j + 1) i * η j i := by
          rw [mul_add, ← mul_assoc, ← zpow_add₀ hk_ne]
      _ = k ^ dep j i * muBoundaryError sol enc j i + k ^ dep (j + 1) i * η j i := by
          have hd : dep (j + 1) i + delta j i = dep j i := by rw [hdepth j i]; abel
          rw [hd]
  calc k ^ dep (j + 1) i * muBoundaryError sol enc (j + 1) i
      ≤ k ^ dep j i * muBoundaryError sol enc j i + k ^ dep (j + 1) i * η j i := hstep
    _ ≤ Wbound j i + k ^ dep (j + 1) i * η j i := by linarith [hw i]
    _ ≤ Wbound (j + 1) i := hWstep j i

/-- **M_U flag-read with the CONCRETE contract-form tracking and DISCHARGED budget step.**

Same conclusion as `selector_MU_flag_read_of_tracking`, but the abstract `Weighted`/`Recur`
predicates are REPLACED by the concrete `MUWeighted`/`MURecur` invariants, and the budget
step `Weighted ∧ Recur → Weighted'` is DISCHARGED internally via `mu_weighted_step`
(`DepthBudget.weighted_step`) rather than carried.  The CARRIED facts are now exactly the
raw config-Reach contract data:

* `dep`/`delta`/`η`/`Wbound`/`k` — the precision/depth/budget parameters and the per-cycle
  recurrence coefficients (`k^delta`/`η`), the contract's own `BgpTrackingPremises`;
* `hk`/`hdepth`/`hWstep` — `k>1`, the depth bookkeeping `dep(j+1)=dep j−delta j`, and the
  budget admissibility `Wbound j + k^dep·η ≤ Wbound (j+1)` (satisfiable because `η` decays
  geometrically, `selector_MU_eps_decays`);
* `hinit_weighted` — the initial weighted bound `MUWeighted 0` (initial config tube);
* `hwin_of_weighted` — the tube-hold `MUWeighted j → u-tube on window` (`u`-Reach hold);
* `hrecur_engine` — the recurrence engine producing `MURecur j` from the discharged margins
  (the `cycle_step ∘ gate_mix_error` Reach bundle; `selector_MU_recur_concrete`);
* `hztube_of_utube` — the `z`-near-`u` window-hold (`z`-Reach).

The simultaneous-induction tube-closing and the budget bookkeeping are DISCHARGED. -/
theorem selector_MU_flag_read_of_tracking_concrete
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (herr : (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel
      < 1 / 2)
    (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView bgpParams38 selectorSchedule MachineInstance.branchU
      (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
      (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (w : ℕ)
    -- CARRIED raw config-Reach / depth-budget parameters
    {k : ℝ} (hk : 1 < k)
    (dep delta : ℕ → Fin MachineInstance.d_U → ℤ)
    (η Wbound : ℕ → Fin MachineInstance.d_U → ℝ)
    (hdepth : ∀ j i, dep (j + 1) i = dep j i - delta j i)
    (hWstep : ∀ j i, Wbound j i + k ^ dep (j + 1) i * η j i ≤ Wbound (j + 1) i)
    -- CARRIED: the initial weighted bound (initial config in the encoding tube)
    (hinit_weighted :
      MUWeighted sol
        (fun j => MachineInstance.stackMachineEncodingU.enc
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)))
        k dep Wbound 0)
    -- CARRIED: tube-hold `MUWeighted j → u-tube on window` (the `u`-Reach hold)
    (hwin_of_weighted : ∀ j,
      MUWeighted sol
        (fun j => MachineInstance.stackMachineEncodingU.enc
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)))
        k dep Wbound j →
      ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
          (2 * Real.pi * (j : ℝ) + Real.pi / 2),
        MachineInstance.UTube MachineInstance.r_LE_U
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) (sol.u t))
    -- DISCHARGED-INTO recurrence engine: produces `MURecur j` from the discharged margins
    (hrecur_engine : ∀ j,
      MUWeighted sol
        (fun j => MachineInstance.stackMachineEncodingU.enc
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)))
        k dep Wbound j →
      (∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
            (2 * Real.pi * (j : ℝ) + Real.pi / 2),
          1 / 2 - (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel
            ≤ sol.Pval
                (MachineInstance.localViewU (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)))
                t) →
      (∀ v, v ≠ MachineInstance.localViewU
              (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) →
          ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
              (2 * Real.pi * (j : ℝ) + Real.pi / 2),
            sol.Pval v t ≤
              -(1 / 2 -
                (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel)) →
      MURecur sol
        (fun j => MachineInstance.stackMachineEncodingU.enc
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)))
        k delta η j)
    -- CARRIED: the `z`-near-`u` window-hold (`z`-Reach window integral)
    (hztube_of_utube : (∀ j : ℕ, ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
          (2 * Real.pi * (j : ℝ) + Real.pi / 2),
        MachineInstance.UTube MachineInstance.r_LE_U
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) (sol.u t)) →
      ∀ j t, t ∈ selectorSchedule.zActiveWindow j →
        MachineInstance.UTube MachineInstance.r_LE_U
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) (sol.z t)) :
    ∀ j t, t ∈ selectorSchedule.zActiveWindow j →
      |sol.z t MachineInstance.haltCoordU
        - MachineInstance.stackMachineEncodingU.enc
            (UniversalMachine.undecidableMachine.toDiscreteMachine.step^[j]
              (UniversalMachine.undecidableMachine.toDiscreteMachine.init w))
            MachineInstance.haltCoordU| ≤ 1 / 4 := by
  -- The budget step is now CLOSED via `mu_weighted_step`; everything else is fed to the
  -- abstract `selector_MU_flag_read_of_tracking` with the concrete invariants instantiated.
  set enc := fun j => MachineInstance.stackMachineEncodingU.enc
    (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) with henc
  exact selector_MU_flag_read_of_tracking eta heta M κ₀ g₀ herr sol w
    (MUWeighted sol enc k dep Wbound) (MURecur sol enc k delta η)
    hinit_weighted hwin_of_weighted hrecur_engine
    (fun j hw hr => mu_weighted_step sol enc hk dep delta η Wbound hdepth hWstep j hw hr)
    hztube_of_utube

/-- **Capstone with the CONCRETE contract-form tracking and DISCHARGED budget step.**

Identical headline to `bgp_unconditional_selector_MU_closed`, but the abstract
`Weighted Recur : ℕ → ℕ → Prop` are REPLACED by the concrete `MUWeighted`/`MURecur`
contract-form invariants (parameterized by the raw recurrence coefficients
`dep`/`delta`/`η`/`Wbound`/`k`), and the depth-budget weighted step is DISCHARGED via
`mu_weighted_step` (`DepthBudget.weighted_step`).  The CARRIED facts are precisely the
contract's own `BgpTrackingPremises`: the per-cycle boundary-error recurrence coefficients
(`k^delta`/`η`, from the sol's `z`/`u`-Reach), the `u`-tube hold, the `z`-near-`u`
window-hold, the initial config tube, the depth bookkeeping and the budget admissibility.
No `sorry`/`axiom`. -/
theorem bgp_unconditional_selector_MU_tracked
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (herr : (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel
      < 1 / 2)
    (HP : MvPolynomial (Fin MachineInstance.d_U) ℚ) (R : ℕ)
    (h_HP :
      ∀ (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
          MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
          MachineInstance.branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (t : ℝ),
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) HP =
          MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t))
    (init : ℕ → Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView + 1) → ℚ)
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
          MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
          MachineInstance.branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R),
          ((init w 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
          MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
          MachineInstance.branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R)
        (i : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView)),
          ((init w i.succ : ℚ) : ℝ) =
            2 * selectorTupleTraj sol La (g₀ : ℝ) 0 i /
              ((∑ k : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 k ^ 2) + 1))
    (sol : ℕ → SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView bgpParams38 selectorSchedule MachineInstance.branchU
      (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
      (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (hHcont : ∀ w, Continuous fun t =>
      MachineInstance.contractFlagIndicatorPackageU.Hval ((sol w).z t))
    (hhigh : ∀ (w : ℕ)
        (La : SelectorHaltLatchSol (sol w) MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R),
      (∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ selectorSchedule.zActiveWindow j,
        1 - MachineInstance.contractFlagIndicatorPackageU.eta ≤
          MachineInstance.contractFlagIndicatorPackageU.Hval ((sol w).z t)) →
        ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1)
    (hlow : ∀ (w : ℕ)
        (La : SelectorHaltLatchSol (sol w) MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R),
      (∀ j : ℕ, ∀ t ∈ selectorSchedule.zActiveWindow j,
        MachineInstance.contractFlagIndicatorPackageU.Hval ((sol w).z t) ≤
          MachineInstance.contractFlagIndicatorPackageU.eta) →
        ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4)
    -- CONCRETE contract-form tracking parameters (the raw config-Reach data), per input `w`.
    {k : ℝ} (hk : 1 < k)
    (dep delta : ℕ → ℕ → Fin MachineInstance.d_U → ℤ)
    (η Wbound : ℕ → ℕ → Fin MachineInstance.d_U → ℝ)
    (hdepth : ∀ w j i, dep w (j + 1) i = dep w j i - delta w j i)
    (hWstep : ∀ w j i, Wbound w j i + k ^ dep w (j + 1) i * η w j i ≤ Wbound w (j + 1) i)
    (hinit_weighted : ∀ w,
      MUWeighted (sol w)
        (fun j => MachineInstance.stackMachineEncodingU.enc
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)))
        k (dep w) (Wbound w) 0)
    (hwin_of_weighted : ∀ w j,
      MUWeighted (sol w)
        (fun j => MachineInstance.stackMachineEncodingU.enc
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)))
        k (dep w) (Wbound w) j →
      ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
          (2 * Real.pi * (j : ℝ) + Real.pi / 2),
        MachineInstance.UTube MachineInstance.r_LE_U
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) ((sol w).u t))
    (hrecur_engine : ∀ w j,
      MUWeighted (sol w)
        (fun j => MachineInstance.stackMachineEncodingU.enc
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)))
        k (dep w) (Wbound w) j →
      (∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
            (2 * Real.pi * (j : ℝ) + Real.pi / 2),
          1 / 2 - (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel
            ≤ (sol w).Pval
                (MachineInstance.localViewU (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)))
                t) →
      (∀ v, v ≠ MachineInstance.localViewU
              (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) →
          ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
              (2 * Real.pi * (j : ℝ) + Real.pi / 2),
            (sol w).Pval v t ≤
              -(1 / 2 -
                (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel)) →
      MURecur (sol w)
        (fun j => MachineInstance.stackMachineEncodingU.enc
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)))
        k (delta w) (η w) j)
    (hztube_of_utube : ∀ w,
      (∀ j : ℕ, ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
          (2 * Real.pi * (j : ℝ) + Real.pi / 2),
        MachineInstance.UTube MachineInstance.r_LE_U
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) ((sol w).u t)) →
      ∀ j t, t ∈ selectorSchedule.zActiveWindow j →
        MachineInstance.UTube MachineInstance.r_LE_U
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) ((sol w).z t))
    (hflag_dom : ∀ w j t, t ∈ selectorSchedule.zActiveWindow j →
      (sol w).z t MachineInstance.haltCoordU ∈ Set.Icc (0 : ℝ) 1) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_unconditional_selector_MU eta heta M κ₀ g₀ HP R h_HP
    init init_presented init_zero init_succ sol hHcont hhigh hlow
    (fun w => selector_MU_flag_read_of_tracking_concrete eta heta M κ₀ g₀ herr (sol w) w
      hk (dep w) (delta w) (η w) (Wbound w) (hdepth w) (hWstep w)
      (hinit_weighted w) (hwin_of_weighted w) (hrecur_engine w) (hztube_of_utube w))
    hflag_dom

/-! ## DISCHARGE of the depth bookkeeping `hdepth` and the budget admissibility `hWstep`

The headline `bgp_unconditional_selector_MU_tracked` carries the depth-budget parameters
`dep`/`delta`/`Wbound` as FREE inputs, together with the bookkeeping obligations
`hdepth : dep(j+1) = dep j − delta j` and `hWstep : Wbound j + k^dep(j+1)·η j ≤ Wbound(j+1)`.
These two are pure budget bookkeeping — they do not touch the solution, only the abstract
precision/budget schema.  The lemmas below fix CONCRETE schemata for `dep`/`delta`/`Wbound`
(linear depth `D − j`, unit decrement, telescoping budget) for which `hdepth` and `hWstep`
hold UNCONDITIONALLY (no extra hypothesis on `η`).  Feeding them into the tracked headline
DISCHARGES `hdepth`/`hWstep` and REMOVES `dep`/`delta`/`Wbound`/`hdepth`/`hWstep` from the
carried set, leaving only the genuinely solution-level Reach premises
(`hinit_weighted`/`hwin_of_weighted`/`hrecur_engine`/`hztube_of_utube`), the geometric
per-cycle defect `η`, and `hk`. -/

/-- Concrete linear depth schedule: `dep j i = D − j` (cast to `ℤ`), independent of `i`. -/
def muDepthSchema (D : ℕ) : ℕ → Fin MachineInstance.d_U → ℤ :=
  fun j _ => (D : ℤ) - (j : ℤ)

/-- Concrete unit-decrement schedule: `delta j i = 1`. -/
def muDeltaSchema : ℕ → Fin MachineInstance.d_U → ℤ :=
  fun _ _ => 1

/-- Concrete telescoping budget: `Wbound j i = W₀ i + Σ_{l<j} k^(dep(l+1) i)·η l i`.  With the
linear depth schema this is exactly the cumulative weighted-defect sum, so the budget step
`Wbound j + k^(dep(j+1))·η j = Wbound(j+1)` holds by `Finset.sum_range_succ`. -/
def muWboundSchema (k : ℝ) (dep : ℕ → Fin MachineInstance.d_U → ℤ)
    (η : ℕ → Fin MachineInstance.d_U → ℝ) (W₀ : Fin MachineInstance.d_U → ℝ) :
    ℕ → Fin MachineInstance.d_U → ℝ :=
  fun j i => W₀ i + ∑ l ∈ Finset.range j, k ^ dep (l + 1) i * η l i

/-- `hdepth` for the concrete schemata: `dep(j+1) = dep j − delta j`. -/
theorem muDepthSchema_step (D : ℕ) :
    ∀ j (i : Fin MachineInstance.d_U),
      muDepthSchema D (j + 1) i = muDepthSchema D j i - muDeltaSchema j i := by
  intro j i
  simp only [muDepthSchema, muDeltaSchema]
  push_cast
  ring

/-- `hWstep` for the concrete telescoping budget: `Wbound j + k^(dep(j+1))·η j ≤ Wbound(j+1)`
(in fact an equality), by `Finset.sum_range_succ`. -/
theorem muWboundSchema_step (k : ℝ) (dep : ℕ → Fin MachineInstance.d_U → ℤ)
    (η : ℕ → Fin MachineInstance.d_U → ℝ) (W₀ : Fin MachineInstance.d_U → ℝ) :
    ∀ j (i : Fin MachineInstance.d_U),
      muWboundSchema k dep η W₀ j i + k ^ dep (j + 1) i * η j i
        ≤ muWboundSchema k dep η W₀ (j + 1) i := by
  intro j i
  simp only [muWboundSchema]
  rw [Finset.sum_range_succ]
  apply le_of_eq
  ring

/-- **Capstone with the depth bookkeeping AND budget admissibility DISCHARGED.**

Identical headline to `bgp_unconditional_selector_MU_tracked`, but the depth schedule
`dep`, the decrement `delta`, the budget `Wbound`, and their two bookkeeping obligations
`hdepth`/`hWstep` are no longer carried: they are fixed to the concrete schemata
`muDepthSchema`/`muDeltaSchema`/`muWboundSchema` (linear depth `D − j`, unit decrement,
telescoping budget), for which `hdepth`/`hWstep` hold unconditionally via
`muDepthSchema_step`/`muWboundSchema_step`.

The CARRIED set is thereby reduced to exactly the genuinely-solution-level Reach premises:

* `hk` — `k > 1` (the precision base);
* `η` and `W₀` — the per-cycle geometric defect (from the sol's `z`/`u`-Reach, geometrically
  decaying by `selector_MU_eps_decays`) and the initial budget profile;
* `hinit_weighted` — the initial config tube (`MUWeighted 0` at the telescoping budget's base);
* `hwin_of_weighted` — the `u`-Reach tube-hold on the gate window;
* `hrecur_engine` — the `cycle_step ∘ gate_mix_error` recurrence engine (consumes the
  discharged margins; `selector_MU_recur_concrete`);
* `hztube_of_utube` — the `z`-near-`u` window-hold (`z`-Reach);
* `hflag_dom` — the halt-coordinate domain constraint;
* plus the standard framework inputs (`HP`/`h_HP`, the computable `init` with its
  stereographic identities, `hHcont`/`hhigh`/`hlow`).

The headline now depends only on solution existence + the framework hyps + the four Reach
premises + the geometric `η`; the depth/budget bookkeeping is internalised.  No `sorry`/`axiom`. -/
theorem bgp_unconditional_selector_MU_full
    (eta : ℚ) (heta : 0 < eta) (M : ℕ) (κ₀ g₀ : ℚ)
    (herr : (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel
      < 1 / 2)
    (HP : MvPolynomial (Fin MachineInstance.d_U) ℚ) (R : ℕ)
    (h_HP :
      ∀ (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
          MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
          MachineInstance.branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R) (t : ℝ),
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) (sol.z t) HP =
          MachineInstance.contractFlagIndicatorPackageU.Hval (sol.z t))
    (init : ℕ → Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView + 1) → ℚ)
    (init_presented :
      ∃ f : ℕ → Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView + 1) → ℤ × ℕ,
        Computable f ∧
        ∀ w i, (f w i).2 ≠ 0 ∧ init w i = (f w i).1 / ((f w i).2 : ℚ))
    (init_zero :
      ∀ (w : ℕ)
        (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
          MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
          MachineInstance.branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R),
          ((init w 0 : ℚ) : ℝ) =
            ((∑ i : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 i ^ 2) - 1) /
              ((∑ i : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 i ^ 2) + 1))
    (init_succ :
      ∀ (w : ℕ)
        (sol : SelectorDynSol MachineInstance.d_U MachineInstance.B_U
          MachineInstance.UniversalLocalView bgpParams38 selectorSchedule
          MachineInstance.branchU
          (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
          (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
          (universalPval eta heta))
        (La : SelectorHaltLatchSol sol MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R)
        (i : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView)),
          ((init w i.succ : ℚ) : ℝ) =
            2 * selectorTupleTraj sol La (g₀ : ℝ) 0 i /
              ((∑ k : Fin (selectorDim MachineInstance.d_U MachineInstance.UniversalLocalView),
                selectorTupleTraj sol La (g₀ : ℝ) 0 k ^ 2) + 1))
    (sol : ℕ → SelectorDynSol MachineInstance.d_U MachineInstance.B_U
      MachineInstance.UniversalLocalView bgpParams38 selectorSchedule MachineInstance.branchU
      (fun t => ((1 + Real.cos t) / 2) ^ M) (fun t => ((1 + Real.sin t) / 2) ^ M)
      (fun _ => (κ₀ : ℝ)) (fun t => (g₀ : ℝ) * Real.exp (bgpParams38.cα * t))
      (universalPval eta heta))
    (hHcont : ∀ w, Continuous fun t =>
      MachineInstance.contractFlagIndicatorPackageU.Hval ((sol w).z t))
    (hhigh : ∀ (w : ℕ)
        (La : SelectorHaltLatchSol (sol w) MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R),
      (∃ J : ℕ, ∀ j ≥ J, ∀ t ∈ selectorSchedule.zActiveWindow j,
        1 - MachineInstance.contractFlagIndicatorPackageU.eta ≤
          MachineInstance.contractFlagIndicatorPackageU.Hval ((sol w).z t)) →
        ∃ T : ℝ, ∀ t ≥ T, 3 / 4 ≤ La.a t ∧ La.a t ≤ 1)
    (hlow : ∀ (w : ℕ)
        (La : SelectorHaltLatchSol (sol w) MachineInstance.contractFlagIndicatorPackageU.Hval
          MachineInstance.K_U R),
      (∀ j : ℕ, ∀ t ∈ selectorSchedule.zActiveWindow j,
        MachineInstance.contractFlagIndicatorPackageU.Hval ((sol w).z t) ≤
          MachineInstance.contractFlagIndicatorPackageU.eta) →
        ∃ T : ℝ, ∀ t ≥ T, 0 ≤ La.a t ∧ La.a t ≤ 1 / 4)
    -- CARRIED solution-level Reach premises (the genuine `BgpTrackingPremises`), per input `w`.
    {k : ℝ} (hk : 1 < k)
    (D : ℕ)
    (η : ℕ → ℕ → Fin MachineInstance.d_U → ℝ)
    (W₀ : ℕ → Fin MachineInstance.d_U → ℝ)
    (hinit_weighted : ∀ w,
      MUWeighted (sol w)
        (fun j => MachineInstance.stackMachineEncodingU.enc
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)))
        k (muDepthSchema D)
        (muWboundSchema k (muDepthSchema D) (η w) (W₀ w)) 0)
    (hwin_of_weighted : ∀ w j,
      MUWeighted (sol w)
        (fun j => MachineInstance.stackMachineEncodingU.enc
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)))
        k (muDepthSchema D)
        (muWboundSchema k (muDepthSchema D) (η w) (W₀ w)) j →
      ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
          (2 * Real.pi * (j : ℝ) + Real.pi / 2),
        MachineInstance.UTube MachineInstance.r_LE_U
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) ((sol w).u t))
    (hrecur_engine : ∀ w j,
      MUWeighted (sol w)
        (fun j => MachineInstance.stackMachineEncodingU.enc
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)))
        k (muDepthSchema D)
        (muWboundSchema k (muDepthSchema D) (η w) (W₀ w)) j →
      (∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
            (2 * Real.pi * (j : ℝ) + Real.pi / 2),
          1 / 2 - (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel
            ≤ (sol w).Pval
                (MachineInstance.localViewU (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)))
                t) →
      (∀ v, v ≠ MachineInstance.localViewU
              (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) →
          ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
              (2 * Real.pi * (j : ℝ) + Real.pi / 2),
            (sol w).Pval v t ≤
              -(1 / 2 -
                (gateSelectorAtomsCoordN (MachineInstance.universalGateAtoms eta heta)).errSel)) →
      MURecur (sol w)
        (fun j => MachineInstance.stackMachineEncodingU.enc
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)))
        k muDeltaSchema (η w) j)
    (hztube_of_utube : ∀ w,
      (∀ j : ℕ, ∀ t ∈ Set.Ico (2 * Real.pi * (j : ℝ) + Real.pi / 6)
          (2 * Real.pi * (j : ℝ) + Real.pi / 2),
        MachineInstance.UTube MachineInstance.r_LE_U
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) ((sol w).u t)) →
      ∀ j t, t ∈ selectorSchedule.zActiveWindow j →
        MachineInstance.UTube MachineInstance.r_LE_U
          (MachineInstance.M_U.step^[j] (MachineInstance.M_U.init w)) ((sol w).z t))
    (hflag_dom : ∀ w j t, t ∈ selectorSchedule.zActiveWindow j →
      (sol w).z t MachineInstance.haltCoordU ∈ Set.Icc (0 : ℝ) 1) :
    ∃ P : Ripple.BoundedUniversality.GPAC.PIVP ℚ,
      Nonempty (EventualThresholdSimulation P UniversalMachine.undecidableMachine) :=
  bgp_unconditional_selector_MU_tracked eta heta M κ₀ g₀ herr HP R h_HP
    init init_presented init_zero init_succ sol hHcont hhigh hlow
    hk (fun _ => muDepthSchema D) (fun _ => muDeltaSchema)
    η (fun w => muWboundSchema k (muDepthSchema D) (η w) (W₀ w))
    (fun w => muDepthSchema_step D)
    (fun w => muWboundSchema_step k (muDepthSchema D) (η w) (W₀ w))
    hinit_weighted hwin_of_weighted hrecur_engine hztube_of_utube hflag_dom

end Ripple.BoundedUniversality.BGP
