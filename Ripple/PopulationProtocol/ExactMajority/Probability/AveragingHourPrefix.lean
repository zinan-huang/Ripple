-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingHourPrefix.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingSeededDelay
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Ripple.PopulationProtocol.ExactMajority.AveragingHourPrefix
open TimeTheorem PairLog PhaseOneDrain AveragingSeededDelay
variable {L K:ℕ}
def observedCheckpoint (init:Cfg L K)
  (seed checkpoint:Ω L K→WithTop ℕ)
  (P:Cfg L K→Cfg L K→Prop):Set (Ω L K) :=
 {ω | ∃ S u:ℕ,S≤u∧seed ω=(S:WithTop ℕ) ∧
  checkpoint ω=(u:WithTop ℕ) ∧
  P (trace init ω S) (trace init ω u)}
def observedCheckpointBy (init:Cfg L K)
  (seed checkpoint:Ω L K→WithTop ℕ)
  (P:Cfg L K→Cfg L K→Prop) (t:ℕ):Set (Ω L K) :=
 {ω | ∃ S u:ℕ,S≤u∧u≤t∧seed ω=(S:WithTop ℕ) ∧
  checkpoint ω=(u:WithTop ℕ) ∧
  P (trace init ω S) (trace init ω u)}
theorem observedCheckpointBy_measurable (init:Cfg L K)
  (seed checkpoint:Ω L K→WithTop ℕ)
  (hseed:PairLogPastTime seed) (hcheckpoint:PairLogPastTime checkpoint)
  (P:Cfg L K→Cfg L K→Prop) (t:ℕ) :
  MeasurableSet[pairLogFiltration L K t]
   (observedCheckpointBy init seed checkpoint P t):=by
 have heq:observedCheckpointBy init seed checkpoint P t =
   ⋃ S:ℕ,⋃ u:ℕ,
    {ω | S≤u∧u≤t∧seed ω=(S:WithTop ℕ) ∧
     checkpoint ω=(u:WithTop ℕ) ∧
     P (trace init ω S) (trace init ω u)}:=by
  ext ω
  simp only [observedCheckpointBy,Set.mem_setOf_eq,Set.mem_iUnion]
 rw [heq]
 refine MeasurableSet.iUnion fun S=>MeasurableSet.iUnion fun u=>?_
 by_cases hSu:S≤u
 ·
  by_cases hut:u≤t
  ·
   have hSt:=hSu.trans hut
   have hs:=(pairLogFiltration L K).mono hSt _ (hseed S)
   have hu:=(pairLogFiltration L K).mono hut _ (hcheckpoint u)
   have hp:MeasurableSet[pairLogFiltration L K t]
     {ω | P (trace init ω S) (trace init ω u)} :=
    (show MeasurableSet {p:Cfg L K×Cfg L K | P p.1 p.2} from
     (Set.to_countable _).measurableSet).preimage
      ((measurable_trace_at_of_le init hSt).prodMk
       (measurable_trace_at_of_le init hut))
   simpa only [hSu,hut,true_and] using hs.inter (hu.inter hp)
  · simp only [hut,false_and,and_false,Set.setOf_false,MeasurableSet.empty]
 · simp only [hSu,false_and,Set.setOf_false,MeasurableSet.empty]
theorem observedCheckpointBy_subset (init:Cfg L K)
  (seed checkpoint:Ω L K→WithTop ℕ)
  (P:Cfg L K→Cfg L K→Prop) (t:ℕ) :
  observedCheckpointBy init seed checkpoint P t ⊆
   observedCheckpoint init seed checkpoint P:=by
 rintro ω ⟨S,u,hSu,_,hs,hu,hp⟩
 exact ⟨S,u,hSu,hs,hu,hp⟩
theorem observedCheckpointBy_iff_of_completed (init:Cfg L K)
  (seed checkpoint:Ω L K→WithTop ℕ)
  (P:Cfg L K→Cfg L K→Prop) (ω:Ω L K) (u t:ℕ)
  (hu:checkpoint ω=(u:WithTop ℕ)) (hut:u≤t) :
  ω∈observedCheckpointBy init seed checkpoint P t ↔
   ω∈observedCheckpoint init seed checkpoint P:=by
 constructor
 · exact fun h => observedCheckpointBy_subset init seed checkpoint P t h
 ·
  rintro ⟨S,v,hSv,hs,hv,hp⟩
  have hvu:v=u:=WithTop.coe_injective (hv.symm.trans hu)
  subst v
  exact ⟨S,u,hSv,hut,hs,hu,hp⟩
def checkpointHourSuccess (init:Cfg L K) (seed:Ω L K→WithTop ℕ)
  (checkpoint:ℕ→Fin 5→Ω L K→WithTop ℕ)
  (test:ℕ→Fin 5→Cfg L K→Cfg L K→Prop)
  (h:ℕ) (ω:Ω L K):Prop :=
 ∀ i,ω∈observedCheckpoint init seed (checkpoint h i) (test h i)
def previousHoursBy (init:Cfg L K) (seed:Ω L K→WithTop ℕ)
  (checkpoint:ℕ→Fin 5→Ω L K→WithTop ℕ)
  (test:ℕ→Fin 5→Cfg L K→Cfg L K→Prop)
  (k t:ℕ):Set (Ω L K) :=
 {ω | ∀ j,j < k→∀ i,
  ω∈observedCheckpointBy init seed (checkpoint (j+1) i)
   (test (j+1) i) t}
theorem previousHoursBy_measurable (init:Cfg L K)
  (seed:Ω L K→WithTop ℕ) (hseed:PairLogPastTime seed)
  (checkpoint:ℕ→Fin 5→Ω L K→WithTop ℕ)
  (hcheckpoint:∀ h i,PairLogPastTime (checkpoint h i))
  (test:ℕ→Fin 5→Cfg L K→Cfg L K→Prop) (k t:ℕ) :
  MeasurableSet[pairLogFiltration L K t]
   (previousHoursBy init seed checkpoint test k t):=by
 simp only [previousHoursBy,Set.setOf_forall]
 refine MeasurableSet.iInter fun j=>MeasurableSet.iInter fun hj =>
  MeasurableSet.iInter fun i=>?_
 exact observedCheckpointBy_measurable init seed (checkpoint (j+1) i)
  hseed (hcheckpoint (j+1) i) (test (j+1) i) t
theorem previousHoursBy_iff_of_completed (init:Cfg L K)
  (seed:Ω L K→WithTop ℕ)
  (checkpoint:ℕ→Fin 5→Ω L K→WithTop ℕ)
  (test:ℕ→Fin 5→Cfg L K→Cfg L K→Prop)
  (ω:Ω L K) (k t:ℕ)
  (hcompleted:∀ j,j < k→∀ i,∃ u:ℕ,
   checkpoint (j+1) i ω=(u:WithTop ℕ)∧u≤t) :
  ω∈previousHoursBy init seed checkpoint test k t ↔
   ∀ j,j < k→checkpointHourSuccess init seed checkpoint test (j+1) ω:=by
 constructor
 ·
  intro h j hj i
  exact observedCheckpointBy_subset init seed _ _ t (h j hj i)
 ·
  intro h j hj i
  obtain ⟨u,hu,hut⟩:=hcompleted j hj i
  exact (observedCheckpointBy_iff_of_completed init seed _ _ ω u t hu hut).2
   (h j hj i)
section FirstFailure
variable {Ξ:Type*}
def firstFailedHour (good:ℕ→Ξ→Prop) (k:ℕ):Set Ξ :=
 {ω | (∀ j,j < k→good (j+1) ω)∧¬ good (k+1) ω}
def hourFailure (good:ℕ→Ξ→Prop) (H:ℕ):Set Ξ :=
 {ω | ∃ k,k < H∧¬ good (k+1) ω}
theorem hourFailure_eq_firstFailed (good:ℕ→Ξ→Prop) (H:ℕ) :
  hourFailure good H=⋃ k:Fin H,firstFailedHour good k.val:=by
 classical
 ext ω
 constructor
 ·
  intro h
  let k:=Nat.find h
  have hk:k < H∧¬ good (k+1) ω:=Nat.find_spec h
  apply Set.mem_iUnion.mpr
  refine ⟨⟨k,hk.1⟩,?_⟩
  refine ⟨?_,hk.2⟩
  intro j hj
  by_contra hbad
  exact (Nat.find_min h hj) ⟨by omega,hbad⟩
 ·
  intro h
  obtain ⟨k,hk⟩:=Set.mem_iUnion.mp h
  exact ⟨k.val,k.isLt,hk.2⟩
variable [MeasurableSpace Ξ]
theorem restricted_hourFailure_measure_le (μ:Measure Ξ) (G:Set Ξ)
  (good:ℕ→Ξ→Prop) (H:ℕ) :
  μ (G∩hourFailure good H) ≤
   ∑ k:Fin H,μ (G∩firstFailedHour good k.val):=by
 have heq:G∩hourFailure good H =
   ⋃ k:Fin H,G∩firstFailedHour good k.val:=by
  rw [hourFailure_eq_firstFailed,Set.inter_iUnion]
 rw [heq]
 exact (measure_iUnion_le _).trans_eq (tsum_fintype _)
end FirstFailure
end Ripple.PopulationProtocol.ExactMajority.AveragingHourPrefix
end
