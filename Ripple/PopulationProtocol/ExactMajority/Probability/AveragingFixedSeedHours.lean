-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingFixedSeedHours.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingHourEvents
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingHourFailureCover
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Ripple.PopulationProtocol.ExactMajority.AveragingFixedSeedHours

open PhaseThreeClockProducer
open TimeTheorem PairLog PhaseOneDrain StageEventSpec AveragingSparseEntry
open AveragingHourEvents AveragingHourPrefix AveragingHourFailureCover
open AveragingHourGateAssembly AveragingHourSchedule AveragingHourStops
open AveragingSeededDelay AveragingCanonicalBlocks AveragingRandomOldBlocks
open AveragingObservedHourTails AveragingNumerics AveragingTerminalDebtDeadlines
variable {n:ℕ}
private theorem success_of_checks {init:InputCfg n} {ω:InputLog n}
  {S T ρ ell h:ℕ} {w:ClockTimes init}
  (H:ClockHistory init ω S T ρ w) (seed:InputLog n→WithTop ℕ)
  (hs:seed ω=(S:WithTop ℕ)) (σ:Sign) (hh:1≤h)
  (hle:h≤ell) (hL:h≤PhaseThreeModel.Numeric.hourIndex n)
  (hc:CurrentHourChecks σ init ω S w ell h) :
  hourSuccess init seed ell σ h ω:=by
 let C:=clockCount (trace init ω S)
 let M:=timeMainCount (trace init ω S)
 let W:=warmCheckpoint w C h
 let P:=potentialCheckpoint w C M h
 let V:=workCheckpoint w C M h
 have hS:=(H.start_positive h hh hL).1
 have hSW:S≤W:=by dsimp only [W,warmCheckpoint]; omega
 have hSP:S≤P:=by dsimp only [P,potentialCheckpoint]; omega
 have hSV:S≤V:=by dsimp only [V,workCheckpoint]; omega
 have hw:=hourWarmStart_clockHistory H seed h hs hL
 have hp:=hourPotentialEnd_clockHistory H seed h hs hL
 have hv:=hourWorkEnd_clock H seed hs h hL
 rcases hc with ⟨hf,ho,hphi,ht,hm⟩
 intro i
 fin_cases i
 · exact ⟨S,W,hSW,hs,by simpa [checkTime] using hw,by simpa [checkTest] using hf⟩
 · exact ⟨S,W,hSW,hs,by simpa [checkTime] using hw,by simpa [checkTest] using ho⟩
 · exact ⟨S,P,hSP,hs,by simpa [checkTime] using hp,by simpa [checkTest] using hphi⟩
 · exact ⟨S,V,hSV,hs,by simpa [checkTime] using hv,by simpa [checkTest] using ht⟩
 · exact ⟨S,V,hSV,hs,by simpa [checkTime] using hv,by simpa [checkTest,hle] using hm⟩
private theorem weighted_fibres {Ω:Type*} [MeasurableSpace Ω]
  (μ:Measure Ω) (E:Set Ω) (τ:Ω→WithTop ℕ)
  (P B:ℕ→Set Ω) (ε:ℝ≥0∞)
  (hP:∀ s,MeasurableSet (P s))
  (hsub:∀ s,P s⊆E∩{ω | τ ω=(s:WithTop ℕ)})
  (ht:∀ s,μ (P s∩B s)≤ε*μ (P s)) :
  μ (⋃ s,P s∩B s)≤ε*μ E:=by
 have hd:Pairwise (fun s t=>Disjoint (P s) (P t)):=by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro ω hs ht
  exact hst (WithTop.coe_injective ((hsub s hs).2.symm.trans (hsub t ht).2))
 have hu:(⋃ s,P s)⊆E:=by
  intro ω hω
  obtain ⟨s,hs⟩:=Set.mem_iUnion.mp hω
  exact (hsub s hs).1
 calc
  _≤∑' s,μ (P s∩B s):=measure_iUnion_le _
  _≤∑' s,ε*μ (P s):=ENNReal.tsum_le_tsum ht
  _=ε*μ (⋃ s,P s):=by rw [ENNReal.tsum_mul_left,←measure_iUnion hd hP]
  _≤ε*μ E:=mul_le_mul_left' (measure_mono hu) ε
def ClockScope (init:InputCfg n) (S ell N:ℕ) (σ:Sign):Set (InputLog n) :=
 {ω | ∃ T ρ,∃ w:ClockTimes init,ClockHistory init ω S T ρ w ∧
  5*2^ell*gapMagnitude init < 4*timeMainCount (trace init ω S) ∧
  (ell≤N+4→winningSign init σ ∧
   2*timeMainCount (trace init ω S)≤5*2^ell*gapMagnitude init)}
theorem fixed_seed_hour_failure_tail (init:InputCfg n)
  (hvalid:validInitial init) (hcard:init.card=n)
  (hn:timePopulationThreshold≤n) (S ell N:ℕ) (σ:Sign)
  (hell:5≤ell) (hNell:N≤ell)
  (hNL:N≤PhaseThreeModel.Numeric.hourIndex n)
  (E:Set (InputLog n))
  (hE:MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 S] E)
  (hseed:∀ ω∈E,SafeSparseSeed init ω S) :
  law init ((E∩ClockScope init S ell N σ) ∩
   hourFailure (hourSuccess init (seedTime init 3) ell σ) N) ≤
   5*(N:ℝ≥0∞)*hourError n*law init E:=by
 let seed:=seedTime init 3
 have hsPast:=seedTime_pastTime init 3
 have hnpos:0 < n:=by have h:=(time_population_bounds hn).2; omega
 have seed_eq (ω:InputLog n) (hω:ω∈E):seed ω=(S:WithTop ℕ) :=
  (seedTime_eq_iff init 3 ω S).2 (hseed ω hω).1
 have piece (k:Fin N) :
   law init ((E∩ClockScope init S ell N σ) ∩
    firstFailedHour (hourSuccess init seed ell σ) k.val) ≤
   5*hourError n*law init E:=by
  let h:=k.val+1
  let r:=h - oldCutoff n
  have hh:1≤h:=by dsimp [h]; omega
  have hN:h≤N:=by have hk:=k.isLt; dsimp [h]; omega
  have hle:h≤ell:=hN.trans hNell
  have hL:h≤PhaseThreeModel.Numeric.hourIndex n:=hN.trans hNL
  let start:=hourStart init seed h
  let earlier:=hourPotentialEnd init seed r
  let finish:=hourWarmStart init seed h
  let blocks:=oldBlockStarts init seed r (oldCutoff n)
  let Pc:ℕ→Set (InputLog n):=fun s =>
   {ω | S≤s∧ω∈E∧start ω=(s:WithTop ℕ) ∧
    ω∈earlierSuccessBy init seed ell σ k.val s}
  let Po:ℕ→Set (InputLog n):=fun s =>
   {ω | oldCutoff n < h∧S≤s∧ω∈E∧earlier ω=(s:WithTop ℕ)}
  let Bc:ℕ→Set (InputLog n):=fun s =>
   observedSimultaneousFailure init S s ⟨h,by omega⟩
    (fun M=>2*totalPrevious ell h*M) σ (totalRegime ell h) (minorityRegime ell h)
  let Bo:ℕ→Set (InputLog n):=fun s =>
   observedOldFailure init S s r blocks finish
  have hc (s:ℕ):MeasurableSet (Pc s) ∧
    law init (Pc s∩Bc s)≤(4*hourError n)*law init (Pc s):=by
   by_cases hs:S≤s
   ·
    have hm:MeasurableSet[pairLogFiltration _ 256 s] (Pc s):=by
     have heq:Pc s=E∩({ω | hourStart init seed h ω=(s:WithTop ℕ)}∩
       earlierSuccessBy init seed ell σ k.val s):=by
      ext ω
      simp only [Pc,start,hs,true_and,Set.mem_setOf_eq,Set.mem_inter_iff]
     rw [heq]
     exact ((pairLogFiltration _ _).mono hs _ hE).inter
       ((hourStart_pastTime init seed hsPast h s).inter
        (earlierSuccessBy_past init seed hsPast ell σ k.val s))
    refine ⟨(pairLogFiltration _ _).le s _ hm,?_⟩
    exact observed_simultaneous_prefix_tail init hvalid hcard hn S s hs
     ⟨h,by omega⟩ hh _ σ _ _ (Pc s) hm
     (fun ω hω=>(hseed ω hω.2.1).2.1)
   · simp [Pc,hs]
  have ho (s:ℕ):MeasurableSet (Po s) ∧
    law init (Po s∩Bo s)≤hourError n*law init (Po s):=by
   by_cases hr:oldCutoff n < h
   ·
    by_cases hs:S≤s
    ·
     have hm:MeasurableSet[pairLogFiltration _ 256 s] (Po s):=by
      have heq:Po s=E∩{ω | hourPotentialEnd init seed r ω=(s:WithTop ℕ)}:=by
       ext ω
       simp only [Po,earlier,hr,hs,true_and,Set.mem_setOf_eq,Set.mem_inter_iff]
      rw [heq]
      exact ((pairLogFiltration _ _).mono hs _ hE).inter
        (hourPotentialEnd_pastTime init seed hsPast r s)
     refine ⟨(pairLogFiltration _ _).le s _ hm,?_⟩
     exact observed_old_prefix_tail init hn S s hs r (by dsimp [r]; omega)
      blocks (fun j=>oldBlockStarts_pastTime init seed hsPast r (oldCutoff n) j)
      finish (hourWarmStart_pastTime init seed hsPast h) (Po s) hm
      (fun ω hω=>(hseed ω hω.2.2.1).2.1)
    · simp [Po,hs]
   · simp [Po,hr]
  have tc:=weighted_fibres (law init) E start Pc Bc (4*hourError n)
   (fun s=>(hc s).1) (fun s ω hω=>⟨hω.2.1,hω.2.2.1⟩)
   (fun s=>(hc s).2)
  have old:=weighted_fibres (law init) E earlier Po Bo (hourError n)
   (fun s=>(ho s).1) (fun s ω hω=>⟨hω.2.2.1,hω.2.2.2⟩)
   (fun s=>(ho s).2)
  have cover:((E∩ClockScope init S ell N σ) ∩
    firstFailedHour (hourSuccess init seed ell σ) k.val) ⊆
    (⋃ s,Pc s∩Bc s)∪(⋃ s,Po s∩Bo s):=by
   rintro ω ⟨⟨he,T,ρ,w,H,hu,hside⟩,hf⟩
   have hs:=seed_eq ω he
   have past:=preceding_of_success H seed hs hL hle σ (fun j hj hjh=>by
    have hjk:j - 1 < k.val:=by dsimp [h] at hjh; omega
    have heq:j - 1+1=j:=by omega
    simpa only [heq] using hf.1 (j - 1) hjk)
   have hb:¬ CurrentHourChecks σ init ω S w ell h :=
    fun checks=>hf.2 (success_of_checks H seed hs σ hh hle hL checks)
   have hit:=current_failure_cover σ hvalid (hseed ω he) H hn hell hh hle hL
    seed hs hu (fun hlast=>(hside (by omega)).1)
    (fun hlast=>(hside (by omega)).2) past.1 past.2 hb
   rcases hit with ⟨hr,hit⟩ | hit
   ·
    obtain ⟨s,u,hsval,hfval,hlive,hcomplete,hpositive⟩:=hit
    have hrpos:1≤r:=by dsimp [r]; omega
    have hrL:r≤PhaseThreeModel.Numeric.hourIndex n:=by dsimp [r]; omega
    have hp:=hourPotentialEnd_clockHistory H seed r hs hrL
    have htime:=(H.start_positive r hrpos hrL).1
    have heq:s=w.start r+clockWarmup n (clockCount (trace init ω S))+
      potentialTrials n (timeMainCount (trace init ω S)):=
     WithTop.coe_injective (hsval.symm.trans hp)
    have hSs:S≤s:=by omega
    apply Or.inr
    apply Set.mem_iUnion.mpr
    exact ⟨s,⟨hr,hSs,he,hsval⟩,u,hfval,hlive,hcomplete,hpositive⟩
   ·
    apply Or.inl
    apply Set.mem_iUnion.mpr
    refine ⟨w.start h,?_,?_⟩
    · exact ⟨(H.start_positive h hh hL).1,he,
        hourStart_clockHistory H seed h hs hL,
        (earlierSuccessBy_iff H hnpos seed hs σ k.val hL).2 hf.1⟩
    · simpa only [Bc,observedSimultaneousFailure,Set.mem_setOf_eq,seedCounts,
        warmCheckpoint,potentialCheckpoint,hcard] using hit
  calc
   _≤law init (⋃ s,Pc s∩Bc s)+law init (⋃ s,Po s∩Bo s) :=
    (measure_mono cover).trans (measure_union_le _ _)
   _≤(4*hourError n)*law init E+hourError n*law init E:=add_le_add tc old
   _=5*hourError n*law init E:=by ring
 calc
  _≤∑ k:Fin N,law init ((E∩ClockScope init S ell N σ) ∩
    firstFailedHour (hourSuccess init seed ell σ) k.val) :=
   restricted_hourFailure_measure_le (law init) _ _ N
  _≤∑ _:Fin N,5*hourError n*law init E :=
   Finset.sum_le_sum (fun k _=>piece k)
  _=5*(N:ℝ≥0∞)*hourError n*law init E:=by
   simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
   ring
end Ripple.PopulationProtocol.ExactMajority.AveragingFixedSeedHours
end
