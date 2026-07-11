import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase3Assembly
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# The protocol trace law `μ` via Ionescu–Tulcea.

`Phase3Assembly.TraceLawAt entry T μ` is the property that `μ : Measure (Trace)`
has the protocol's endpoint law (`Measure.map (·T) μ = kernel^T entry`) and starts
at `entry`.  This file *constructs* such a `μ` from the protocol's transition
kernel using Mathlib's homogeneous Ionescu–Tulcea trajectory `traj`.

`Config` carries `DiscreteMeasurableSpace`, and `(NonuniformMajority L K).transitionKernel`
is a Markov kernel — exactly the two hypotheses `traj` needs (no StandardBorel).

This file constructs `μ` and proves `TraceLawAt`: the endpoint law comes from
`traj_map_frestrictLe` plus the finite `partialTraj ↔ kernel^T` identity, and
`starts_at` comes from the `Iic 0` coordinate.
-/

namespace ExactMajority
namespace ProtocolTraceLaw

open ProbabilityTheory MeasureTheory
open Finset Preorder
open scoped ENNReal

variable {L K : ℕ}

/-- The constant state space: `Config` at every time. -/
abbrev St (L K : ℕ) : ℕ → Type := fun _ => Config (AgentState L K)

/-- The Ionescu–Tulcea kernel family for a time-homogeneous chain: at step `n`,
ignore all but the current (index-`n`) coordinate and apply the protocol kernel. -/
noncomputable def kfamily (n : ℕ) :
    Kernel (Π i : Finset.Iic n, St L K i) (St L K (n + 1)) :=
  Kernel.comap (NonuniformMajority L K).transitionKernel
    (fun x => x ⟨n, Finset.mem_Iic.2 le_rfl⟩)
    (measurable_pi_apply _)

instance instMarkov (n : ℕ) : IsMarkovKernel (kfamily (L := L) (K := K) n) := by
  unfold kfamily
  infer_instance

/-- The trajectory kernel from the time-`0` slice. -/
noncomputable def traj0 :
    Kernel (Π i : Finset.Iic 0, St L K i) (Π n, St L K n) :=
  Kernel.traj (kfamily (L := L) (K := K)) 0

/-- The protocol trace law from an entry configuration. -/
noncomputable def μ (entry : Config (AgentState L K)) :
    Measure (Π n, St L K n) :=
  traj0 (L := L) (K := K) (fun _ => entry)

instance (entry : Config (AgentState L K)) :
    IsProbabilityMeasure (μ (L := L) (K := K) entry) := by
  unfold μ traj0
  infer_instance

/-- The endpoint marginal of the finite Ionescu-Tulcea trajectory is the
homogeneous kernel power, read from the time-`0` coordinate. -/
private lemma partialTraj_endpoint_kernel (T : ℕ) :
    (Kernel.partialTraj (kfamily (L := L) (K := K)) 0 T).map
        (fun x : Π i : Finset.Iic T, St L K i =>
          x ⟨T, Finset.mem_Iic.2 le_rfl⟩) =
      (((NonuniformMajority L K).transitionKernel ^ T).comap
        (fun x : Π i : Finset.Iic 0, St L K i =>
          x ⟨0, Finset.mem_Iic.2 le_rfl⟩)
        (measurable_pi_apply _)) := by
  induction T with
  | zero =>
      ext x s hs
      rw [Kernel.map_apply _ (measurable_pi_apply _) x, Kernel.partialTraj_self,
        Kernel.id_apply, Measure.map_dirac' (measurable_pi_apply _) x,
        Kernel.comap_apply, pow_zero]
      change (Measure.dirac (x ⟨0, Finset.mem_Iic.2 le_rfl⟩)) s =
        (Kernel.id (x ⟨0, Finset.mem_Iic.2 le_rfl⟩)) s
      rw [Kernel.id_apply]
  | succ T ih =>
      let P : Kernel (Config (AgentState L K)) (Config (AgentState L K)) :=
        (NonuniformMajority L K).transitionKernel
      let coord0 : (Π i : Finset.Iic 0, St L K i) → Config (AgentState L K) :=
        fun x => x ⟨0, Finset.mem_Iic.2 le_rfl⟩
      let coordT : (Π i : Finset.Iic T, St L K i) → Config (AgentState L K) :=
        fun x => x ⟨T, Finset.mem_Iic.2 le_rfl⟩
      let coordTs : (Π i : Finset.Iic (T + 1), St L K i) → Config (AgentState L K) :=
        fun x => x ⟨T + 1, Finset.mem_Iic.2 le_rfl⟩
      calc
        (Kernel.partialTraj (kfamily (L := L) (K := K)) 0 (T + 1)).map coordTs
            = ((Kernel.partialTraj (kfamily (L := L) (K := K)) T (T + 1) ∘ₖ
                Kernel.partialTraj (kfamily (L := L) (K := K)) 0 T)).map coordTs := by
                rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le T)]
        _ = ((Kernel.partialTraj (kfamily (L := L) (K := K)) T (T + 1)).map coordTs) ∘ₖ
                Kernel.partialTraj (kfamily (L := L) (K := K)) 0 T := by
                rw [Kernel.map_comp]
        _ = kfamily (L := L) (K := K) T ∘ₖ
                Kernel.partialTraj (kfamily (L := L) (K := K)) 0 T := by
                rw [Kernel.map_partialTraj_succ_self]
        _ = (P.comap coordT (measurable_pi_apply _)) ∘ₖ
                Kernel.partialTraj (kfamily (L := L) (K := K)) 0 T := by
                rfl
        _ = P ∘ₖ ((Kernel.partialTraj (kfamily (L := L) (K := K)) 0 T).map coordT) := by
                rw [← Kernel.comp_map (Kernel.partialTraj (kfamily (L := L) (K := K)) 0 T) P
                  (measurable_pi_apply _)]
        _ = P ∘ₖ ((P ^ T).comap coord0 (measurable_pi_apply _)) := by
                simpa [P, coord0, coordT] using congrArg (fun η => P ∘ₖ η) ih
        _ = ((NonuniformMajority L K).transitionKernel ^ (T + 1)).comap coord0
                (measurable_pi_apply _) := by
                ext x s hs
                rw [Kernel.comap_apply,
                  Kernel.pow_succ_apply_eq_lintegral P T (coord0 x) hs,
                  Kernel.comp_apply' _ _ _ hs, Kernel.comap_apply]

/-- Endpoint projection of the infinite trajectory has the `T`-step protocol law. -/
private lemma endpoint_law (entry : Config (AgentState L K)) (T : ℕ) :
    Measure.map (fun tr : Phase3GoodClock.Trace L K => tr T)
        (μ (L := L) (K := K) entry) =
      ((NonuniformMajority L K).transitionKernel ^ T) entry := by
  let x0 : Π i : Finset.Iic 0, St L K i := fun _ => entry
  let coordT : (Π i : Finset.Iic T, St L K i) → Config (AgentState L K) :=
    fun x => x ⟨T, Finset.mem_Iic.2 le_rfl⟩
  let restrictT : (Π n, St L K n) → (Π i : Finset.Iic T, St L K i) :=
    frestrictLe (π := St L K) T
  unfold μ traj0
  change Measure.map (fun tr : Π n, St L K n => tr T)
      ((Kernel.traj (kfamily (L := L) (K := K)) 0) x0) =
    ((NonuniformMajority L K).transitionKernel ^ T) entry
  calc
    Measure.map (fun tr : Π n, St L K n => tr T)
        ((Kernel.traj (kfamily (L := L) (K := K)) 0) x0)
        = Measure.map (coordT ∘ restrictT)
            ((Kernel.traj (kfamily (L := L) (K := K)) 0) x0) := by
            rfl
    _ = Measure.map coordT
            (Measure.map restrictT
              ((Kernel.traj (kfamily (L := L) (K := K)) 0) x0)) := by
            rw [← Measure.map_map (measurable_pi_apply _) (measurable_frestrictLe T)]
    _ = Measure.map coordT
            (Kernel.partialTraj (kfamily (L := L) (K := K)) 0 T x0) := by
            dsimp [restrictT]
            rw [Kernel.traj_map_frestrictLe_apply]
    _ = ((NonuniformMajority L K).transitionKernel ^ T) entry := by
            rw [← Kernel.map_apply _ (measurable_pi_apply _) x0]
            rw [partialTraj_endpoint_kernel]
            rw [Kernel.comap_apply]

/-- The Ionescu-Tulcea trajectory measure is a `TraceLawAt` for the protocol. -/
theorem traceLawAt (entry : Config (AgentState L K)) (T : ℕ) :
    Phase3Assembly.TraceLawAt (L := L) (K := K) entry T
      (μ (L := L) (K := K) entry) where
  endpoint_law := endpoint_law (L := L) (K := K) entry T
  starts_at := by
    have hsingle :
        MeasurableSet ({entry} : Set (Config (AgentState L K))) :=
      measurableSet_singleton entry
    calc
      μ (L := L) (K := K) entry {tr | tr 0 = entry}
          = Measure.map (fun tr : Phase3GoodClock.Trace L K => tr 0)
              (μ (L := L) (K := K) entry) {entry} := by
              rw [Measure.map_apply (measurable_pi_apply 0) hsingle]
              rfl
      _ = ((NonuniformMajority L K).transitionKernel ^ 0) entry {entry} := by
              rw [endpoint_law (L := L) (K := K) entry 0]
      _ = 1 := by
              rw [pow_zero]
              change (Kernel.id entry) ({entry} : Set (Config (AgentState L K))) = 1
              rw [Kernel.id_apply, Measure.dirac_apply' entry hsingle]
              simp

end ProtocolTraceLaw
end ExactMajority

#print axioms ExactMajority.ProtocolTraceLaw.μ
#print axioms ExactMajority.ProtocolTraceLaw.kfamily
#print axioms ExactMajority.ProtocolTraceLaw.traceLawAt
