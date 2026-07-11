/-
  Ionescu-Tulcea trajectory construction for mass-action CRN kinetics.
-/
import Ripple.sCRNUniversality.Stochastic.MassAction.Weights
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Basic

namespace Ripple.sCRNUniversality.Stochastic.MassAction

open MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators ENNReal

universe u v

variable {S : Type u} [Fintype S] [DecidableEq S]
variable (N : Network.{u, v} S) [DecidableEq N.I]

noncomputable instance instMS : MeasurableSpace (Option N.I) := ⊤
noncomputable instance instMSC : MeasurableSingletonClass (Option N.I) := ⟨fun _ => trivial⟩

open Classical in
private noncomputable def chooseEnabled (z : State S) (hNT : ¬ N.Terminal z) : N.I := by
  have : ∃ i, N.EnabledAt z i := by
    by_contra h; push_neg at h; exact hNT h
  exact this.choose

open Classical in
private theorem chooseEnabled_enabled (z : State S) (hNT : ¬ N.Terminal z) :
    N.EnabledAt z (chooseEnabled N z hNT) := by
  unfold chooseEnabled
  exact Exists.choose_spec _

open Classical in
noncomputable def fireOptionSanitized (z : State S) (o : Option N.I)
    (hNT : ¬ N.Terminal z) : N.I :=
  match o with
  | some i => if N.EnabledAt z i then i else chooseEnabled N z hNT
  | none => chooseEnabled N z hNT

theorem fireOptionSanitized_enabled (z : State S) (o : Option N.I)
    (hNT : ¬ N.Terminal z) :
    N.EnabledAt z (fireOptionSanitized N z o hNT) := by
  unfold fireOptionSanitized
  cases o with
  | none => exact chooseEnabled_enabled N z hNT
  | some i =>
    simp only
    split
    · assumption
    · exact chooseEnabled_enabled N z hNT

theorem fireOptionSanitized_of_enabled (z : State S) (i : N.I)
    (hNT : ¬ N.Terminal z) (hE : N.EnabledAt z i) :
    fireOptionSanitized N z (some i) hNT = i := by
  simp [fireOptionSanitized, hE]

open Classical in
noncomputable def stateStep (z : State S) (o : Option N.I) : State S :=
  if hT : N.Terminal z then z
  else (N.rxn (fireOptionSanitized N z o hT)).fire z

open Classical in
noncomputable def prefixToState (z0 : State S) :
    (n : Nat) → ((i : Finset.Iic n) → Option N.I) → State S
  | 0, _ => z0
  | n + 1, p =>
    let prev := prefixToState z0 n (fun k => p ⟨k.val,
      Finset.mem_Iic.mpr (le_trans (Finset.mem_Iic.mp k.property) (Nat.le_succ n))⟩)
    stateStep N prev (p ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)

noncomputable def stepKernel
    (hPos : N.hasPositiveRates) (z0 : State S) (n : Nat) :
    Kernel ((i : Finset.Iic n) → Option N.I) (Option N.I) :=
  Kernel.ofFunOfCountable
    (fun p => (massActionPMF N hPos (prefixToState N z0 n p)).toMeasure)

instance instIsMarkovKernelStepKernel
    (hPos : N.hasPositiveRates) (z0 : State S) (n : Nat) :
    IsMarkovKernel (stepKernel N hPos z0 n) where
  isProbabilityMeasure p := by
    change IsProbabilityMeasure ((massActionPMF N hPos _).toMeasure)
    infer_instance

noncomputable def rawLaw
    (hPos : N.hasPositiveRates) (z0 : State S) :
    Measure ((n : Nat) → Option N.I) :=
  Kernel.trajFun
    (X := fun _ => Option N.I)
    (fun n => stepKernel N hPos z0 n) 0 (fun _ => none)

theorem rawLaw_isProbabilityMeasure
    (hPos : N.hasPositiveRates) (z0 : State S) :
    IsProbabilityMeasure (rawLaw N hPos z0) :=
  Kernel.isProbabilityMeasure_trajFun
    (X := fun _ => Option N.I)
    (fun n => stepKernel N hPos z0 n) 0 (fun _ => none)

set_option maxHeartbeats 4000000 in
theorem rawLaw_map_eval_succ
    (hPos : N.hasPositiveRates) (z0 : State S) (t : Nat) :
    (rawLaw N hPos z0).map (fun ω => ω (t + 1)) =
      (stepKernel N hPos z0 t ∘ₖ
        Kernel.partialTraj (X := fun _ => Option N.I)
          (fun n => stepKernel N hPos z0 n) 0 t) (fun _ => none) := by
  set κ := fun n => stepKernel N hPos z0 n
  set x₀ : (j : Finset.Iic 0) → Option N.I := fun _ => none
  -- rawLaw = traj κ 0 x₀
  show (Kernel.traj (X := fun _ => Option N.I) κ 0 x₀).map (fun ω => ω (t + 1)) = _
  rw [← Kernel.map_apply _ (measurable_pi_apply (t + 1)) x₀]
  congr 1
  -- (traj κ 0).map (eval(t+1)) = κ t ∘ₖ partialTraj κ 0 t
  rw [← Kernel.traj_comp_partialTraj (X := fun _ => Option N.I) (Nat.zero_le t),
    Kernel.map_comp]
  congr 1
  exact Kernel.map_traj_succ_self (X := fun _ => Option N.I)

end Ripple.sCRNUniversality.Stochastic.MassAction
