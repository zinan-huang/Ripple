-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingDebtService.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingDebtTransitions

/-!
# Unit service by the actual sampled interaction

Clock service includes the initializer and the same interaction's hour drag.
Splitting service is proved for both ordered orientations of an already active
zero/biased Main pair. These are deterministic service certificates; scheduler
rectangles are supplied separately.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingDebtService

open TimeTheorem P3DeterministicAlgebra AveragingMixedAlgebra AveragingMixedLedgers
open AveragingDebtAlgebra AveragingDebtTransitions PhaseTwoActivationLocal

variable {L : ℕ}

def ClockServiceTarget (h : ℕ) (s : AgentState L 256) : Prop :=
  s.role = .main ∧
    (s.phase.val < 3 ∨ (s.bias = .zero ∧ s.hour.val < h))

def ClockServiceSource (h : ℕ) (t : AgentState L 256) : Prop :=
  t.phase.val = 3 ∧ t.role = .clock ∧ h ≤ t.minute.val / 256

theorem p3_main_clock_nonzero (a t : AgentState L 256) (har : a.role = .main)
    (htc : t.role = .clock) (hb : a.bias ≠ .zero) :
    Phase3Transition L 256 a t = (a, t) := by
  simp [Phase3Transition, har, htc, hb]

theorem p3_main_clock_zero (a t : AgentState L 256) (har : a.role = .main)
    (htc : t.role = .clock) (hb : a.bias = .zero) :
    (Phase3Transition L 256 a t).2 = t ∧
      (Phase3Transition L 256 a t).1.role = .main ∧
      (Phase3Transition L 256 a t).1.phase = a.phase ∧
      (Phase3Transition L 256 a t).1.bias = .zero ∧
      (Phase3Transition L 256 a t).1.smallBias = a.smallBias ∧
      (Phase3Transition L 256 a t).1.hour.val = max a.hour.val (min L (t.minute.val / 256)) := by
  simp [Phase3Transition, har, htc, hb]

theorem enterThree_main_fields (s : AgentState L 256)
    (hp : 1 ≤ s.phase.val ∧ s.phase.val ≤ 2)
    (hsafe : 2 ≤ s.smallBias.val ∧ s.smallBias.val ≤ 4)
    (hsm : s.role = .main) :
    (enterThree s).phase.val = 3 ∧ (enterThree s).role = .main ∧
      (enterThree s).smallBias = s.smallBias ∧
      (enterThree s).hour.val = 0 ∧
      (enterThree s).bias =
        (if s.smallBias.val < 3 then Bias.dyadic .neg ⟨0, by omega⟩
          else if s.smallBias.val > 3 then Bias.dyadic .pos ⟨0, by omega⟩
          else Bias.zero) := by
  have hn1 : ¬ s.smallBias.val ≤ 1 := by omega
  have hn5 : ¬ 5 ≤ s.smallBias.val := by omega
  have hcases : s.phase.val = 1 ∨ s.phase.val = 2 := by omega
  rcases hcases with hone | htwo
  · have hlist : (List.range 11).filter
        (fun k => decide (1 < k) && decide (k ≤ 3)) = [2, 3] := by decide
    simp [enterThree, hone, runInitsBetween, hlist, phaseInit, hsm, hn1, hn5]
  · have hlist : (List.range 11).filter
        (fun k => decide (2 < k) && decide (k ≤ 3)) = [3] := by decide
    simp [enterThree, htwo, runInitsBetween, hlist, phaseInit, hsm]


theorem epi_left_pending (s t : AgentState L 256)
    (hp : 1 ≤ s.phase.val ∧ s.phase.val ≤ 2)
    (hsafe : 2 ≤ s.smallBias.val ∧ s.smallBias.val ≤ 4)
    (hsm : s.role = .main) (htp : t.phase.val = 3) :
    Transition L 256 s t =
      (finishPhase10Entry L 256 (enterThree s) (Phase3Transition L 256 (enterThree s) t).1,
       finishPhase10Entry L 256 t (Phase3Transition L 256 (enterThree s) t).2) := by
  have hf := enterThree_main_fields s hp hsafe hsm
  have htf : t.phase = ⟨3, by decide⟩ := Fin.ext htp
  have hmax : max s.phase t.phase = ⟨3, by decide⟩ := by
    apply Fin.ext
    change max s.phase.val t.phase.val = 3
    omega
  have hts : runInitsBetween L 256 t.phase.val 3 { t with phase := ⟨3, by decide⟩ } = t := by
    rw [htp, runInitsBetween_self]
    cases t
    simp_all
  have hepi : phaseEpidemicUpdate L 256 s t = (enterThree s, t) := by
    unfold phaseEpidemicUpdate
    simp only [hmax]
    change (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        ((enterThree s).phase.val = 10 ∨
          (runInitsBetween L 256 t.phase.val 3 { t with phase := ⟨3, by decide⟩ }).phase.val = 10) then
      (phase10EpidemicEntry L 256 s (enterThree s),
        phase10EpidemicEntry L 256 t (runInitsBetween L 256 t.phase.val 3 { t with phase := ⟨3, by decide⟩ }))
      else (enterThree s, runInitsBetween L 256 t.phase.val 3 { t with phase := ⟨3, by decide⟩ })) = _
    rw [hts, if_neg]
    rintro ⟨-, h10 | h10⟩
    · omega
    · omega
  have hph : (enterThree s).phase = ⟨3, by decide⟩ := Fin.ext hf.1
  unfold Transition
  rw [hepi]
  simp only [hph]


theorem left_pending (α β : ℚ) (h : ℕ) (hh : h ≤ L)
    (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 2)
    (hsafe : 2 ≤ s.smallBias.val ∧ s.smallBias.val ≤ 4)
    (hsm : s.role = .main) (htp : t.phase.val = 3) (htc : t.role = .clock)
    (hfl : h ≤ t.minute.val / 256) :
    agentDebt α β h (Transition L 256 s t).1 +
        agentDebt α β h (Transition L 256 s t).2 + 1 =
      agentDebt α β h s + agentDebt α β h t := by
  have hnotold : ¬ max 0 (min L (t.minute.val / 256)) < h := by omega
  rw [epi_left_pending s t hs hsafe hsm htp]
  obtain ⟨hap, har, hasb, hahr, habias⟩ := enterThree_main_fields s hs hsafe hsm
  generalize enterThree s = a at *
  rw [agentDebt_eq_pending α β h s (by omega)]
  have hv : s.smallBias.val = 2 ∨ s.smallBias.val = 3 ∨ s.smallBias.val = 4 := by omega
  have ha10 : a.phase.val ≠ 10 := by omega
  have ht10 : t.phase.val ≠ 10 := by omega
  rcases hv with hv | hv | hv
  · have hb : a.bias = .dyadic .neg ⟨0, by omega⟩ := by rw [habias]; simp [hv]
    have hbne : a.bias ≠ .zero := by rw [hb]; simp
    rw [p3_main_clock_nonzero a t har htc hbne,
      finishPhase10Entry_eq_self_of_after_ne_10 L 256 a a ha10,
      finishPhase10Entry_eq_self_of_after_ne_10 L 256 t t ht10]
    dsimp only
    rw [agentDebt_eq_active α β h a har (by omega)]
    norm_num [activeDebt, hb, hsm, hv, PhaseTwoSparse.smallValue, Bias.toRat, massBlend]
    simp
    ring
  · have hb : a.bias = .zero := by rw [habias]; simp [hv]
    obtain ⟨h2, hrole, hphase, hbias, hsb, hhour⟩ := p3_main_clock_zero a t har htc hb
    have hX10 : (Phase3Transition L 256 a t).1.phase.val ≠ 10 := by rw [hphase]; exact ha10
    rw [h2, finishPhase10Entry_eq_self_of_after_ne_10 L 256 a _ hX10,
      finishPhase10Entry_eq_self_of_after_ne_10 L 256 t t ht10,
      agentDebt_eq_active α β h _ hrole (by rw [hphase]; omega)]
    have hlz : ¬ (Phase3Transition L 256 a t).1.hour.val < h := by
      rw [hhour, hahr]; exact hnotold
    simp only [activeDebt, hbias, hlz, and_false, if_false, Bias.toRat, massBlend, hv,
      PhaseTwoSparse.smallValue, agentDebt_eq_pending]
    norm_num [hsm, hv]
    ring
  · have hb : a.bias = .dyadic .pos ⟨0, by omega⟩ := by rw [habias]; simp [hv]
    have hbne : a.bias ≠ .zero := by rw [hb]; simp
    rw [p3_main_clock_nonzero a t har htc hbne,
      finishPhase10Entry_eq_self_of_after_ne_10 L 256 a a ha10,
      finishPhase10Entry_eq_self_of_after_ne_10 L 256 t t ht10]
    dsimp only
    rw [agentDebt_eq_active α β h a har (by omega)]
    norm_num [activeDebt, hb, hsm, hv, PhaseTwoSparse.smallValue, Bias.toRat, massBlend]
    simp
    ring

theorem p3_clock_main_nonzero (s a : AgentState L 256) (hsc : s.role = .clock)
    (har : a.role = .main) (hb : a.bias ≠ .zero) :
    Phase3Transition L 256 s a = (s, a) := by
  simp [Phase3Transition, har, hsc, hb]

theorem p3_clock_main_zero (s a : AgentState L 256) (hsc : s.role = .clock)
    (har : a.role = .main) (hb : a.bias = .zero) :
    (Phase3Transition L 256 s a).1 = s ∧
      (Phase3Transition L 256 s a).2.role = .main ∧
      (Phase3Transition L 256 s a).2.phase = a.phase ∧
      (Phase3Transition L 256 s a).2.bias = .zero ∧
      (Phase3Transition L 256 s a).2.smallBias = a.smallBias ∧
      (Phase3Transition L 256 s a).2.hour.val = max a.hour.val (min L (s.minute.val / 256)) := by
  simp [Phase3Transition, har, hsc, hb]

theorem epi_right_pending (s t : AgentState L 256)
    (hp : 1 ≤ t.phase.val ∧ t.phase.val ≤ 2)
    (hsafe : 2 ≤ t.smallBias.val ∧ t.smallBias.val ≤ 4)
    (htm : t.role = .main) (hsp : s.phase.val = 3) :
    Transition L 256 s t =
      (finishPhase10Entry L 256 s (Phase3Transition L 256 s (enterThree t)).1,
       finishPhase10Entry L 256 (enterThree t) (Phase3Transition L 256 s (enterThree t)).2) := by
  have hf := enterThree_main_fields t hp hsafe htm
  have hsf : s.phase = ⟨3, by decide⟩ := Fin.ext hsp
  have hmax : max s.phase t.phase = ⟨3, by decide⟩ := by
    apply Fin.ext
    change max s.phase.val t.phase.val = 3
    omega
  have hss : runInitsBetween L 256 s.phase.val 3 { s with phase := ⟨3, by decide⟩ } = s := by
    rw [hsp, runInitsBetween_self]
    cases s
    simp_all
  have hepi : phaseEpidemicUpdate L 256 s t = (s, enterThree t) := by
    unfold phaseEpidemicUpdate
    simp only [hmax]
    change (if (s.phase.val < 10 ∨ t.phase.val < 10) ∧
        ((runInitsBetween L 256 s.phase.val 3 { s with phase := ⟨3, by decide⟩ }).phase.val = 10 ∨
          (enterThree t).phase.val = 10) then
      (phase10EpidemicEntry L 256 s (runInitsBetween L 256 s.phase.val 3 { s with phase := ⟨3, by decide⟩ }),
        phase10EpidemicEntry L 256 t (enterThree t))
      else (runInitsBetween L 256 s.phase.val 3 { s with phase := ⟨3, by decide⟩ }, enterThree t)) = _
    rw [hss, if_neg]
    rintro ⟨-, h10 | h10⟩
    · omega
    · omega
  have hph : s.phase = ⟨3, by decide⟩ := hsf
  unfold Transition
  rw [hepi]
  simp only [hph]

theorem right_pending (α β : ℚ) (h : ℕ) (hh : h ≤ L)
    (s t : AgentState L 256)
    (hs : 1 ≤ t.phase.val ∧ t.phase.val ≤ 2)
    (hsafe : 2 ≤ t.smallBias.val ∧ t.smallBias.val ≤ 4)
    (htm : t.role = .main) (hsp : s.phase.val = 3) (hsc : s.role = .clock)
    (hfl : h ≤ s.minute.val / 256) :
    agentDebt α β h (Transition L 256 s t).1 +
        agentDebt α β h (Transition L 256 s t).2 + 1 =
      agentDebt α β h s + agentDebt α β h t := by
  have hnotold : ¬ max 0 (min L (s.minute.val / 256)) < h := by omega
  rw [epi_right_pending s t hs hsafe htm hsp]
  obtain ⟨hap, har, hasb, hahr, habias⟩ := enterThree_main_fields t hs hsafe htm
  generalize enterThree t = a at *
  rw [agentDebt_eq_pending α β h t (by omega)]
  have hv : t.smallBias.val = 2 ∨ t.smallBias.val = 3 ∨ t.smallBias.val = 4 := by omega
  have ha10 : a.phase.val ≠ 10 := by omega
  have hs10 : s.phase.val ≠ 10 := by omega
  rcases hv with hv | hv | hv
  · have hb : a.bias = .dyadic .neg ⟨0, by omega⟩ := by rw [habias]; simp [hv]
    have hbne : a.bias ≠ .zero := by rw [hb]; simp
    rw [p3_clock_main_nonzero s a hsc har hbne,
      finishPhase10Entry_eq_self_of_after_ne_10 L 256 s s hs10,
      finishPhase10Entry_eq_self_of_after_ne_10 L 256 a a ha10]
    dsimp only
    rw [agentDebt_eq_active α β h a har (by omega)]
    norm_num [activeDebt, hb, htm, hv, PhaseTwoSparse.smallValue, Bias.toRat, massBlend]
    simp
    ring
  · have hb : a.bias = .zero := by rw [habias]; simp [hv]
    obtain ⟨h1, hrole, hphase, hbias, hsb, hhour⟩ := p3_clock_main_zero s a hsc har hb
    have hX10 : (Phase3Transition L 256 s a).2.phase.val ≠ 10 := by rw [hphase]; exact ha10
    rw [h1, finishPhase10Entry_eq_self_of_after_ne_10 L 256 s s hs10,
      finishPhase10Entry_eq_self_of_after_ne_10 L 256 a _ hX10,
      agentDebt_eq_active α β h _ hrole (by rw [hphase]; omega)]
    have hlz : ¬ (Phase3Transition L 256 s a).2.hour.val < h := by
      rw [hhour, hahr]; exact hnotold
    simp only [activeDebt, hbias, hlz, and_false, if_false, Bias.toRat, massBlend, hv,
      PhaseTwoSparse.smallValue]
    norm_num [htm, hv] <;> ring
  · have hb : a.bias = .dyadic .pos ⟨0, by omega⟩ := by rw [habias]; simp [hv]
    have hbne : a.bias ≠ .zero := by rw [hb]; simp
    rw [p3_clock_main_nonzero s a hsc har hbne,
      finishPhase10Entry_eq_self_of_after_ne_10 L 256 s s hs10,
      finishPhase10Entry_eq_self_of_after_ne_10 L 256 a a ha10]
    dsimp only
    rw [agentDebt_eq_active α β h a har (by omega)]
    norm_num [activeDebt, hb, htm, hv, PhaseTwoSparse.smallValue, Bias.toRat, massBlend]
    simp
    ring


/-- A pending Main is initialized and serviced in the sampled interaction.
For an already active target, the same statement is the actual hour drag. -/
theorem transition_clock_service_left (α β : ℚ) (h : ℕ) (hh : h ≤ L)
    (s t : AgentState L 256)
    (hs : 1 ≤ s.phase.val ∧ s.phase.val ≤ 3)
    (hsafe : s.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hmain : ClockServiceTarget h s) (hclock : ClockServiceSource h t) :
    agentDebt α β h (Transition L 256 s t).1 +
        agentDebt α β h (Transition L 256 s t).2 + 1 =
      agentDebt α β h s + agentDebt α β h t := by
  have hsm := hmain.1
  have htp := hclock.1
  have htc := hclock.2.1
  have htf : t.phase = ⟨3, by decide⟩ := Fin.ext htp
  have hfloor : h ≤ min L (t.minute.val / 256) := le_min hh hclock.2.2
  have hnotold : ¬ max s.hour.val (min L (t.minute.val / 256)) < h := by omega
  have hmax : max s.phase t.phase = ⟨3, by decide⟩ := by
    apply Fin.ext
    change max s.phase.val t.phase.val = 3
    omega
  have hempty : (List.range 11).filter
      (fun k => decide (3 < k) && decide (k ≤ 3)) = [] := by decide
  by_cases hpend : s.phase.val < 3
  · have hsafe' : 2 ≤ s.smallBias.val ∧ s.smallBias.val ≤ 4 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsafe
      omega
    exact left_pending α β h hh s t ⟨hs.1, by omega⟩ hsafe' hsm htp htc hclock.2.2
  · have hthree : s.phase.val = 3 := by omega
    have hsf : s.phase = ⟨3, by decide⟩ := Fin.ext hthree
    have hz : s.bias = .zero := (hmain.2.resolve_left (by omega)).1
    have hlo : s.hour.val < h := (hmain.2.resolve_left (by omega)).2
    simp [Transition, phaseEpidemicUpdate, hmax, hsf, htf, runInitsBetween,
      hempty, Phase3Transition, hsm, htc, hz, hlo, hnotold, agentDebt,
      inactiveMainWeight, lowHourZeroWeight, prePhase4Mass, Bias.toRat, massBlend] <;> ring

theorem transition_clock_service_right (α β : ℚ) (h : ℕ) (hh : h ≤ L)
    (s t : AgentState L 256)
    (ht : 1 ≤ t.phase.val ∧ t.phase.val ≤ 3)
    (htsafe : t.smallBias.val ∈ ({2, 3, 4} : Finset ℕ))
    (hclock : ClockServiceSource h s) (hmain : ClockServiceTarget h t) :
    agentDebt α β h (Transition L 256 s t).1 +
        agentDebt α β h (Transition L 256 s t).2 + 1 =
      agentDebt α β h s + agentDebt α β h t := by
  have htm := hmain.1
  have hsp := hclock.1
  have hsc := hclock.2.1
  have hsf : s.phase = ⟨3, by decide⟩ := Fin.ext hsp
  have hfloor : h ≤ min L (s.minute.val / 256) := le_min hh hclock.2.2
  have hnotold : ¬ max t.hour.val (min L (s.minute.val / 256)) < h := by omega
  have hmax : max s.phase t.phase = ⟨3, by decide⟩ := by
    apply Fin.ext
    change max s.phase.val t.phase.val = 3
    omega
  have hempty : (List.range 11).filter
      (fun k => decide (3 < k) && decide (k ≤ 3)) = [] := by decide
  by_cases hpend : t.phase.val < 3
  · have hsafe' : 2 ≤ t.smallBias.val ∧ t.smallBias.val ≤ 4 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at htsafe
      omega
    exact right_pending α β h hh s t ⟨ht.1, by omega⟩ hsafe' htm hsp hsc hclock.2.2
  · have hthree : t.phase.val = 3 := by omega
    have htf : t.phase = ⟨3, by decide⟩ := Fin.ext hthree
    have hz : t.bias = .zero := (hmain.2.resolve_left (by omega)).1
    have hlo : t.hour.val < h := (hmain.2.resolve_left (by omega)).2
    simp [Transition, phaseEpidemicUpdate, hmax, hsf, htf, runInitsBetween,
      hempty, Phase3Transition, htm, hsc, hz, hlo, hnotold, agentDebt,
      inactiveMainWeight, lowHourZeroWeight, prePhase4Mass, Bias.toRat, massBlend] <;> ring

theorem transition_split_service_left (α β : ℚ) (h : ℕ)
    (s t : AgentState L 256) (sgn : Sign) (i : Fin (L + 1))
    (hs : s.phase.val = 3) (ht : t.phase.val = 3)
    (hsm : s.role = .main) (htm : t.role = .main)
    (hsb : s.bias = .zero) (htb : t.bias = .dyadic sgn i)
    (hgt : i.val < s.hour.val) (hcount : s.hour.val < h) :
    agentDebt α β h (Transition L 256 s t).1 +
        agentDebt α β h (Transition L 256 s t).2 + 1 =
      agentDebt α β h s + agentDebt α β h t := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
  have hsf : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have hr := Phase5To6FuelProducer.phase3CancelSplit_roles s t
  have hp := phase3CancelSplit_phase_preserved L 256 s t
  have hl := agentDebt_eq_active α β h (phase3CancelSplit L 256 s t).1
    (hr.1.trans hsm) (by rw [hp.1, hs])
  have hh := agentDebt_eq_active α β h (phase3CancelSplit L 256 s t).2
    (hr.2.trans htm) (by rw [hp.2, ht])
  have hsl := agentDebt_eq_active α β h s hsm (by omega)
  have htl := agentDebt_eq_active α β h t htm (by omega)
  have hservice := activeDebt_split_left α β h s t sgn i hsb htb hgt
  rw [if_pos hcount, ← hl, ← hh, ← hsl, ← htl] at hservice
  unfold Transition
  rw [hepi]
  simpa [hsf, Phase3Transition, hsm, htm, agentDebt, inactiveMainWeight,
    lowHourZeroWeight, prePhase4Mass] using hservice

theorem transition_split_service_right (α β : ℚ) (h : ℕ)
    (s t : AgentState L 256) (sgn : Sign) (i : Fin (L + 1))
    (hs : s.phase.val = 3) (ht : t.phase.val = 3)
    (hsm : s.role = .main) (htm : t.role = .main)
    (hsb : s.bias = .dyadic sgn i) (htb : t.bias = .zero)
    (hgt : i.val < t.hour.val) (hcount : t.hour.val < h) :
    agentDebt α β h (Transition L 256 s t).1 +
        agentDebt α β h (Transition L 256 s t).2 + 1 =
      agentDebt α β h s + agentDebt α β h t := by
  have hepi := ClockRealKernel.phaseEpidemicUpdate_eq_self_p3 s t hs ht
  have hsf : s.phase = ⟨3, by decide⟩ := Fin.ext hs
  have hr := Phase5To6FuelProducer.phase3CancelSplit_roles s t
  have hp := phase3CancelSplit_phase_preserved L 256 s t
  have hl := agentDebt_eq_active α β h (phase3CancelSplit L 256 s t).1
    (hr.1.trans hsm) (by rw [hp.1, hs])
  have hh := agentDebt_eq_active α β h (phase3CancelSplit L 256 s t).2
    (hr.2.trans htm) (by rw [hp.2, ht])
  have hsl := agentDebt_eq_active α β h s hsm (by omega)
  have htl := agentDebt_eq_active α β h t htm (by omega)
  have hservice := activeDebt_split_right α β h s t sgn i hsb htb hgt
  rw [if_pos hcount, ← hl, ← hh, ← hsl, ← htl] at hservice
  unfold Transition
  rw [hepi]
  simpa [hsf, Phase3Transition, hsm, htm, agentDebt, inactiveMainWeight,
    lowHourZeroWeight, prePhase4Mass] using hservice

theorem totalDebt_step_service (α β : ℚ) (h : ℕ)
    (c : Cfg L 256) (s t : AgentState L 256)
    (happ : Protocol.Applicable c s t)
    (hservice : agentDebt α β h (Transition L 256 s t).1 +
        agentDebt α β h (Transition L 256 s t).2 + 1 =
      agentDebt α β h s + agentDebt α β h t) :
    totalDebt α β h (Protocol.stepOrSelf (NonuniformMajority L 256) c s t) + 1 =
      totalDebt α β h c := by
  have hstep : Protocol.stepOrSelf (NonuniformMajority L 256) c s t =
      c - {s, t} + {(Transition L 256 s t).1, (Transition L 256 s t).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ] <;> rfl
  have hsplit : c = c - {s, t} + ({s, t} : Multiset (AgentState L 256)) := by
    rw [Multiset.sub_add_cancel (show ({s, t} : Multiset (AgentState L 256)) ≤ c from happ)]
  rw [hstep, totalDebt_add_pair]
  conv_rhs => rw [hsplit]
  rw [totalDebt_add_pair]
  linarith only [hservice]

end Ripple.PopulationProtocol.ExactMajority.AveragingDebtService

end
