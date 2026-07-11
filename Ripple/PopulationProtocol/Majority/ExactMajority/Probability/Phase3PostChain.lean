import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase3Assembly

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Real

namespace Phase3Post3

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

theorem lemma612_h13_killed_tail_to_good
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {h dt : ℕ}
    {GoodNow GoodNext : Option (Config (AgentState L K)) → Prop}
    {η : ℝ≥0∞}
    (d : Phase3Core.Lemma612 (L := L) (K := K) D T h)
    (hstart :
      ∀ o, GoodNow o →
        ∃ c, o = some c ∧ c ∈ T.surface.checkpoint .afterO h)
    (hnext :
      ∀ c,
        Phase3Core.OFuelFloor (L := L) (K := K) D h c →
          GoodNext (some c))
    (hdt :
      dt ≤
        Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterO (L := L) (K := K) (T.clockInput h))
    (hη : T.surface.eps13 h ≤ η) :
    ∀ o, GoodNow o →
      (GatedDrift.killK_now
          (NonuniformMajority L K).transitionKernel
          (T.surface.hourGate h) ^ dt) o
        {x | ¬ GoodNext x} ≤ η := by
  intro o ho
  rcases hstart o ho with ⟨c, rfl, hc⟩
  have ht :=
    d.1.tail c hc dt hdt
  have hsub :
      {x : Option (Config (AgentState L K)) | ¬ GoodNext x} ⊆
        Phase3Core.killedBad
          (fun y : Config (AgentState L K) =>
            ¬ Phase3Core.OFuelFloor (L := L) (K := K) D h y) := by
    intro x hx
    cases x with
    | none =>
        exact Or.inl rfl
    | some y =>
        exact Or.inr ⟨y, rfl, fun hy => hx (hnext y hy)⟩
  calc
    (GatedDrift.killK_now
        (NonuniformMajority L K).transitionKernel
        (T.surface.hourGate h) ^ dt) (some c)
      {x | ¬ GoodNext x}
        ≤
      (GatedDrift.killK_now
        (NonuniformMajority L K).transitionKernel
        (T.surface.hourGate h) ^ dt) (some c)
      (Phase3Core.killedBad
        (fun y : Config (AgentState L K) =>
          ¬ Phase3Core.OFuelFloor (L := L) (K := K) D h y)) :=
        measure_mono hsub
    _ ≤ T.surface.eps13 h := by
        simpa [Phase3Core.stoppedTail, Phase3Core.phase3Kernel] using ht
    _ ≤ η := hη

theorem lemma612_h15_killed_tail_to_good
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {h dt : ℕ}
    {GoodNow GoodNext : Option (Config (AgentState L K)) → Prop}
    {η : ℝ≥0∞}
    (d : Phase3Core.Lemma612 (L := L) (K := K) D T h)
    (hstart :
      ∀ o, GoodNow o →
        ∃ c, o = some c ∧ c ∈ T.surface.checkpoint .afterO h)
    (hnext :
      ∀ c,
        Phase3Core.PhiPotentialDrop (L := L) (K := K) D h c →
          GoodNext (some c))
    (hdt :
      dt =
        Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterO (L := L) (K := K) (T.clockInput h))
    (hη : T.surface.eps15 h ≤ η) :
    ∀ o, GoodNow o →
      (GatedDrift.killK_now
          (NonuniformMajority L K).transitionKernel
          (T.surface.hourGate h) ^ dt) o
        {x | ¬ GoodNext x} ≤ η := by
  intro o ho
  rcases hstart o ho with ⟨c, rfl, hc⟩
  have ht :=
    d.2.1.tail c hc
  have hsub :
      {x : Option (Config (AgentState L K)) | ¬ GoodNext x} ⊆
        Phase3Core.killedBad
          (fun y : Config (AgentState L K) =>
            ¬ Phase3Core.PhiPotentialDrop (L := L) (K := K) D h y) := by
    intro x hx
    cases x with
    | none =>
        exact Or.inl rfl
    | some y =>
        exact Or.inr ⟨y, rfl, fun hy => hx (hnext y hy)⟩
  calc
    (GatedDrift.killK_now
        (NonuniformMajority L K).transitionKernel
        (T.surface.hourGate h) ^ dt) (some c)
      {x | ¬ GoodNext x}
        ≤
      (GatedDrift.killK_now
        (NonuniformMajority L K).transitionKernel
        (T.surface.hourGate h) ^ dt) (some c)
      (Phase3Core.killedBad
        (fun y : Config (AgentState L K) =>
          ¬ Phase3Core.PhiPotentialDrop (L := L) (K := K) D h y)) :=
        measure_mono hsub
    _ ≤ T.surface.eps15 h := by
        simpa [Phase3Core.stoppedTail, Phase3Core.phase3Kernel, hdt] using ht
    _ ≤ η := hη

theorem lemma612_h16_killed_tail_to_good
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {h dt : ℕ}
    {GoodNow GoodNext : Option (Config (AgentState L K)) → Prop}
    {η : ℝ≥0∞}
    (d : Phase3Core.Lemma612 (L := L) (K := K) D T h)
    (hstart :
      ∀ o, GoodNow o →
        ∃ c, o = some c ∧ c ∈ T.surface.checkpoint .afterPhi h)
    (hnext :
      ∀ c,
        Phase3Core.TotalMassBound (L := L) (K := K) D h c →
          GoodNext (some c))
    (hdt_lo :
      Phase3Core.ClockCut.afterMass (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h)
        ≤ dt)
    (hdt_hi :
      dt ≤
        Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h))
    (hη : T.surface.eps16 h ≤ η) :
    ∀ o, GoodNow o →
      (GatedDrift.killK_now
          (NonuniformMajority L K).transitionKernel
          (T.surface.hourGate h) ^ dt) o
        {x | ¬ GoodNext x} ≤ η := by
  intro o ho
  rcases hstart o ho with ⟨c, rfl, hc⟩
  have ht :=
    d.2.2.tail c hc dt hdt_lo hdt_hi
  have hsub :
      {x : Option (Config (AgentState L K)) | ¬ GoodNext x} ⊆
        Phase3Core.killedBad
          (fun y : Config (AgentState L K) =>
            ¬ Phase3Core.TotalMassBound (L := L) (K := K) D h y) := by
    intro x hx
    cases x with
    | none =>
        exact Or.inl rfl
    | some y =>
        exact Or.inr ⟨y, rfl, fun hy => hx (hnext y hy)⟩
  calc
    (GatedDrift.killK_now
        (NonuniformMajority L K).transitionKernel
        (T.surface.hourGate h) ^ dt) (some c)
      {x | ¬ GoodNext x}
        ≤
      (GatedDrift.killK_now
        (NonuniformMajority L K).transitionKernel
        (T.surface.hourGate h) ^ dt) (some c)
      (Phase3Core.killedBad
        (fun y : Config (AgentState L K) =>
          ¬ Phase3Core.TotalMassBound (L := L) (K := K) D h y)) :=
        measure_mono hsub
    _ ≤ T.surface.eps16 h := by
        simpa [Phase3Core.stoppedTail, Phase3Core.phase3Kernel] using ht
    _ ≤ η := hη

noncomputable def coreRowError
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (h : ℕ) : ℝ≥0∞ :=
  T.surface.eps13 h + T.surface.eps15 h + T.surface.eps16 h

theorem lemma612_h131516_killed_tail_to_good
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {h dt : ℕ}
    {GoodNow GoodNext : Option (Config (AgentState L K)) → Prop}
    (d : Phase3Core.Lemma612 (L := L) (K := K) D T h)
    (hstartAfterO :
      ∀ o, GoodNow o →
        ∃ c, o = some c ∧ c ∈ T.surface.checkpoint .afterO h)
    (hstartAfterPhi :
      ∀ o, GoodNow o →
        ∃ c, o = some c ∧ c ∈ T.surface.checkpoint .afterPhi h)
    (hnext :
      ∀ c,
        Phase3Core.OFuelFloor (L := L) (K := K) D h c →
        Phase3Core.PhiPotentialDrop (L := L) (K := K) D h c →
        Phase3Core.TotalMassBound (L := L) (K := K) D h c →
          GoodNext (some c))
    (hdt13 :
      dt ≤
        Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterO (L := L) (K := K) (T.clockInput h))
    (hdt15 :
      dt =
        Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterO (L := L) (K := K) (T.clockInput h))
    (hdt16_lo :
      Phase3Core.ClockCut.afterMass (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h)
        ≤ dt)
    (hdt16_hi :
      dt ≤
        Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput h) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput h)) :
    ∀ o, GoodNow o →
      (GatedDrift.killK_now
          (NonuniformMajority L K).transitionKernel
          (T.surface.hourGate h) ^ dt) o
        {x | ¬ GoodNext x} ≤
          T.surface.eps13 h + T.surface.eps15 h + T.surface.eps16 h := by
  intro o ho
  let OFGood : Option (Config (AgentState L K)) → Prop :=
    fun x =>
      match x with
      | some c => Phase3Core.OFuelFloor (L := L) (K := K) D h c
      | none => False
  let PhiGood : Option (Config (AgentState L K)) → Prop :=
    fun x =>
      match x with
      | some c => Phase3Core.PhiPotentialDrop (L := L) (K := K) D h c
      | none => False
  let MassGood : Option (Config (AgentState L K)) → Prop :=
    fun x =>
      match x with
      | some c => Phase3Core.TotalMassBound (L := L) (K := K) D h c
      | none => False
  let A13 : Set (Option (Config (AgentState L K))) := {x | ¬ OFGood x}
  let A15 : Set (Option (Config (AgentState L K))) := {x | ¬ PhiGood x}
  let A16 : Set (Option (Config (AgentState L K))) := {x | ¬ MassGood x}
  have h13 :
      (GatedDrift.killK_now
          (NonuniformMajority L K).transitionKernel
          (T.surface.hourGate h) ^ dt) o A13 ≤ T.surface.eps13 h := by
    dsimp [A13]
    exact
      lemma612_h13_killed_tail_to_good
        (L := L) (K := K) (θ := θ) (tr := tr)
        (D := D) (T := T) (h := h) (dt := dt)
        (GoodNow := GoodNow) (GoodNext := OFGood)
        (η := T.surface.eps13 h)
        d hstartAfterO
        (by
          intro c hc
          simpa [OFGood] using hc)
        hdt13 le_rfl
        o ho
  have h15 :
      (GatedDrift.killK_now
          (NonuniformMajority L K).transitionKernel
          (T.surface.hourGate h) ^ dt) o A15 ≤ T.surface.eps15 h := by
    dsimp [A15]
    exact
      lemma612_h15_killed_tail_to_good
        (L := L) (K := K) (θ := θ) (tr := tr)
        (D := D) (T := T) (h := h) (dt := dt)
        (GoodNow := GoodNow) (GoodNext := PhiGood)
        (η := T.surface.eps15 h)
        d hstartAfterO
        (by
          intro c hc
          simpa [PhiGood] using hc)
        hdt15 le_rfl
        o ho
  have h16 :
      (GatedDrift.killK_now
          (NonuniformMajority L K).transitionKernel
          (T.surface.hourGate h) ^ dt) o A16 ≤ T.surface.eps16 h := by
    dsimp [A16]
    exact
      lemma612_h16_killed_tail_to_good
        (L := L) (K := K) (θ := θ) (tr := tr)
        (D := D) (T := T) (h := h) (dt := dt)
        (GoodNow := GoodNow) (GoodNext := MassGood)
        (η := T.surface.eps16 h)
        d hstartAfterPhi
        (by
          intro c hc
          simpa [MassGood] using hc)
        hdt16_lo hdt16_hi le_rfl
        o ho
  have hsub :
      {x : Option (Config (AgentState L K)) | ¬ GoodNext x} ⊆
        A13 ∪ (A15 ∪ A16) := by
    intro x hx
    cases x with
    | none =>
        left
        simp [A13, OFGood]
    | some y =>
        by_cases hOF :
          Phase3Core.OFuelFloor (L := L) (K := K) D h y
        · by_cases hPhi :
            Phase3Core.PhiPotentialDrop (L := L) (K := K) D h y
          · by_cases hMass :
              Phase3Core.TotalMassBound (L := L) (K := K) D h y
            · exact False.elim (hx (hnext y hOF hPhi hMass))
            · right
              right
              simpa [A16, MassGood] using hMass
          · right
            left
            simpa [A15, PhiGood] using hPhi
        · left
          simpa [A13, OFGood] using hOF
  have hunion :
      (GatedDrift.killK_now
          (NonuniformMajority L K).transitionKernel
          (T.surface.hourGate h) ^ dt) o (A13 ∪ (A15 ∪ A16)) ≤
        (GatedDrift.killK_now
          (NonuniformMajority L K).transitionKernel
          (T.surface.hourGate h) ^ dt) o A13 +
        ((GatedDrift.killK_now
          (NonuniformMajority L K).transitionKernel
          (T.surface.hourGate h) ^ dt) o A15 +
        (GatedDrift.killK_now
          (NonuniformMajority L K).transitionKernel
          (T.surface.hourGate h) ^ dt) o A16) := by
    calc
      (GatedDrift.killK_now
          (NonuniformMajority L K).transitionKernel
          (T.surface.hourGate h) ^ dt) o (A13 ∪ (A15 ∪ A16))
          ≤
        (GatedDrift.killK_now
          (NonuniformMajority L K).transitionKernel
          (T.surface.hourGate h) ^ dt) o A13 +
        (GatedDrift.killK_now
          (NonuniformMajority L K).transitionKernel
          (T.surface.hourGate h) ^ dt) o (A15 ∪ A16) :=
            measure_union_le A13 (A15 ∪ A16)
      _ ≤
        (GatedDrift.killK_now
          (NonuniformMajority L K).transitionKernel
          (T.surface.hourGate h) ^ dt) o A13 +
        ((GatedDrift.killK_now
          (NonuniformMajority L K).transitionKernel
          (T.surface.hourGate h) ^ dt) o A15 +
        (GatedDrift.killK_now
          (NonuniformMajority L K).transitionKernel
          (T.surface.hourGate h) ^ dt) o A16) :=
            by gcongr; exact measure_union_le _ _
  calc
    (GatedDrift.killK_now
        (NonuniformMajority L K).transitionKernel
        (T.surface.hourGate h) ^ dt) o {x | ¬ GoodNext x}
        ≤
      (GatedDrift.killK_now
        (NonuniformMajority L K).transitionKernel
        (T.surface.hourGate h) ^ dt) o (A13 ∪ (A15 ∪ A16)) :=
          measure_mono hsub
    _ ≤
      (GatedDrift.killK_now
        (NonuniformMajority L K).transitionKernel
        (T.surface.hourGate h) ^ dt) o A13 +
      ((GatedDrift.killK_now
        (NonuniformMajority L K).transitionKernel
        (T.surface.hourGate h) ^ dt) o A15 +
      (GatedDrift.killK_now
        (NonuniformMajority L K).transitionKernel
        (T.surface.hourGate h) ^ dt) o A16) :=
          hunion
    _ ≤ T.surface.eps13 h + (T.surface.eps15 h + T.surface.eps16 h) :=
          add_le_add h13 (add_le_add h15 h16)
    _ ≤ T.surface.eps13 h + T.surface.eps15 h + T.surface.eps16 h := by
          simp [add_assoc]

structure CoreRowsSnapshot617Readout
    (n ell : ℕ) (M g₀ : ℝ) (σ : Sign)
    (H : ℕ)
    (Good : ℕ → Option (Config (AgentState L K)) → Prop) : Prop where
  phase3 :
    ∀ c,
      Good H (some c) →
        AllPhase3 (L := L) (K := K) n c
  gap_eq :
    ∀ c,
      Good H (some c) →
        signedGap (L := L) (K := K) c = g₀
  total_mass_bound :
    ∀ c,
      Good H (some c) →
        weightedMass (L := L) (K := K) c ≤
          Lemma616TotalMass.Constants.rho_l * M * (2 : ℝ) ^ (-(ell : ℤ))
  muAbove_bound :
    ∀ c,
      Good H (some c) →
        Lemma615MassAbove.muAbove (L := L) (K := K) ell c ≤
          (1 / 500 : ℝ) * M * (2 : ℝ) ^ (-(ell : ℤ))
  minority_bound :
    ∀ c,
      Good H (some c) →
        minorityMass (L := L) (K := K) σ c ≤
          (1 / 250 : ℝ) * M * (2 : ℝ) ^ (-(ell : ℤ))
  main_confined :
    ∀ c,
      Good H (some c) →
        MainExponentConfinement.MainProfileConfinedToUseful
          (L := L) (K := K) c

namespace CoreRowsSnapshot617Readout

def toSnapshot617
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    {H : ℕ}
    {Good : ℕ → Option (Config (AgentState L K)) → Prop}
    (R : CoreRowsSnapshot617Readout
      (L := L) (K := K) n ell M g₀ σ H Good) :
    ∀ c,
      Good H (some c) →
        Snapshot617 (L := L) (K := K) n ell M g₀ σ c := by
  intro c hc
  exact
    Snapshot617.ofCapBound
      (L := L) (K := K)
      (R.phase3 c hc)
      (R.gap_eq c hc)
      (R.total_mass_bound c hc)
      (R.muAbove_bound c hc)
      (R.minority_bound c hc)
      (R.main_confined c hc)

end CoreRowsSnapshot617Readout

structure CoreRowsSnapshot617Adapter
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    (D : Phase3Core.Phase3ModeDomain L)
    (T : Phase3Core.CoreThread (L := L) (K := K) D θ tr)
    (n ell : ℕ) (M g₀ : ℝ) (σ : Sign) where
  horizon : Snapshot617Horizon (L := L) (K := K) n ell
  gate : Set (Config (AgentState L K))
  H : ℕ
  hourLen : ℕ → ℕ
  Good : ℕ → Option (Config (AgentState L K)) → Prop
  hCore : ∀ i, i < H → i ≤ D.lastCoreHour
  gate_eq :
    ∀ i, i < H → gate = T.surface.hourGate i
  good0 :
    ∀ c₀,
      Slot3Entry (L := L) (K := K) n g₀ c₀ →
        Good 0 (some c₀)
  none_bad :
    ¬ Good H none
  start_afterO :
    ∀ i, i < H → ∀ o,
      Good i o →
        ∃ c, o = some c ∧ c ∈ T.surface.checkpoint .afterO i
  start_afterPhi :
    ∀ i, i < H → ∀ o,
      Good i o →
        ∃ c, o = some c ∧ c ∈ T.surface.checkpoint .afterPhi i
  next_of_rows :
    ∀ i, i < H → ∀ c,
      Phase3Core.OFuelFloor (L := L) (K := K) D i c →
      Phase3Core.PhiPotentialDrop (L := L) (K := K) D i c →
      Phase3Core.TotalMassBound (L := L) (K := K) D i c →
        Good (i + 1) (some c)
  hourLen_h13_le :
    ∀ i, i < H →
      hourLen i ≤
        Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput i) -
          Phase3Core.ClockCut.afterO (L := L) (K := K) (T.clockInput i)
  hourLen_h15_eq :
    ∀ i, i < H →
      hourLen i =
        Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput i) -
          Phase3Core.ClockCut.afterO (L := L) (K := K) (T.clockInput i)
  hourLen_h16_lo :
    ∀ i, i < H →
      Phase3Core.ClockCut.afterMass (L := L) (K := K) (T.clockInput i) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput i)
        ≤ hourLen i
  hourLen_h16_hi :
    ∀ i, i < H →
      hourLen i ≤
        Phase3Core.ClockCut.finish (L := L) (K := K) (T.clockInput i) -
          Phase3Core.ClockCut.afterPhi (L := L) (K := K) (T.clockInput i)
  readout :
    CoreRowsSnapshot617Readout
      (L := L) (K := K) n ell M g₀ σ H Good
  horizon_eq :
    horizon.T_end_l2 = ChapmanKolmogorovChain.hourPrefix hourLen H
  ε : ℝ≥0
  budget :
    (∑ i ∈ Finset.range H, coreRowError (L := L) (K := K) T i) ≤
      (ε : ℝ≥0∞)

noncomputable def snapshot617HourChain_of_core_rows
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (P : Phase3Core.CoreProducers (L := L) (K := K) D T)
    (A :
      CoreRowsSnapshot617Adapter
        (L := L) (K := K) D T n ell M g₀ σ) :
    Snapshot617HourChain (L := L) (K := K) n ell M g₀ σ where
  horizon := A.horizon
  gate := A.gate
  H := A.H
  hourLen := A.hourLen
  Good := A.Good
  ηhour := fun i => coreRowError (L := L) (K := K) T i
  good0 := A.good0
  none_bad := A.none_bad
  tail := by
    intro i hi o ho
    simpa [A.gate_eq i hi, coreRowError] using
      (lemma612_h131516_killed_tail_to_good
        (L := L) (K := K) (θ := θ) (tr := tr)
        (D := D) (T := T)
        (h := i) (dt := A.hourLen i)
        (GoodNow := A.Good i)
        (GoodNext := A.Good (i + 1))
        (Phase3Core.lemma612_all
          (L := L) (K := K) P i (A.hCore i hi))
        (A.start_afterO i hi)
        (A.start_afterPhi i hi)
        (A.next_of_rows i hi)
        (A.hourLen_h13_le i hi)
        (A.hourLen_h15_eq i hi)
        (A.hourLen_h16_lo i hi)
        (A.hourLen_h16_hi i hi)
        o ho)
  readout :=
    CoreRowsSnapshot617Readout.toSnapshot617
      (L := L) (K := K) A.readout
  horizon_eq := A.horizon_eq
  ε := A.ε
  budget := A.budget

noncomputable def snapshot617Tail_of_core_rows
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (P : Phase3Core.CoreProducers (L := L) (K := K) D T)
    (A :
      CoreRowsSnapshot617Adapter
        (L := L) (K := K) D T n ell M g₀ σ) :
    Snapshot617Tail (L := L) (K := K) n ell M g₀ σ :=
  Snapshot617HourChain.toSnapshot617Tail
    (L := L) (K := K)
    (snapshot617HourChain_of_core_rows
      (L := L) (K := K) P A)

end Phase3Post3

namespace Phase3Assembly

variable {L K : ℕ}

attribute [local instance] Classical.propDecidable

noncomputable def snapshot617HourChain_of_dischargedCore
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (P : DischargedCoreEngineProducers (L := L) (K := K) D T)
    (A :
      Phase3Post3.CoreRowsSnapshot617Adapter
        (L := L) (K := K) D T n ell M g₀ σ) :
    Phase3Post3.Snapshot617HourChain
      (L := L) (K := K) n ell M g₀ σ :=
  Phase3Post3.snapshot617HourChain_of_core_rows
    (L := L) (K := K)
    (DischargedCoreEngineProducers.toCoreProducers
      (L := L) (K := K) P)
    A

noncomputable def snapshot617Tail_of_dischargedCore
    {θ : Phase3GoodClock.ClockTimingParams}
    {tr : Phase3GoodClock.Trace L K}
    {D : Phase3Core.Phase3ModeDomain L}
    {T : Phase3Core.CoreThread (L := L) (K := K) D θ tr}
    {n ell : ℕ} {M g₀ : ℝ} {σ : Sign}
    (P : DischargedCoreEngineProducers (L := L) (K := K) D T)
    (A :
      Phase3Post3.CoreRowsSnapshot617Adapter
        (L := L) (K := K) D T n ell M g₀ σ) :
    Phase3Post3.Snapshot617Tail
      (L := L) (K := K) n ell M g₀ σ :=
  Phase3Post3.snapshot617Tail_of_core_rows
    (L := L) (K := K)
    (DischargedCoreEngineProducers.toCoreProducers
      (L := L) (K := K) P)
    A

end Phase3Assembly

end ExactMajority
