/-
Non-vacuity probe for SCWB Theorem 3.2 (repaired network).
CTM level: instantiates `scwb_theorem_3_2_ctm` on a concrete one-state CTM that rewrites the
read bit, clock length `L + 1 = 2`, tapes of length `3`, `δ = 1/2`, input tape `011`, one CTM
step.
TM level: instantiates `scwb_theorem_3_2` on a one-state TM that keeps the read bit and moves
right, cycle length `2`, one TM step from the tape `[1]`; its space premise is discharged, the
CTM run is computed (6 CTM steps, cycle word `10 ↦ 01`), and the success event `TmOK` is
nonempty (it has probability at least `1/2`); the paper-form time bound
`3168 (3/2)^L (v/k) s³ t²/(3^s δ)` is instantiated at `s = 4`.
-/
import Ripple.sCRNUniversality.ClockedCTM.TMtoCTM

namespace ProbeSCWB32

open MeasureTheory Ripple.sCRNUniversality Ripple.sCRNUniversality.ClockedCTM
open Ripple.sCRNUniversality.Stochastic.MassAction

/-- A one-state CTM: read `b`, write `b` (the tape rotates). -/
def rot : CTM Unit := ⟨fun q b => (q, b)⟩

def c0 : Unit × List Bool := ((), [false, true, true])

theorem c0_len : c0.2.length = 0 + 3 := rfl

/-- The headline on the concrete machine: `#A* = f` and `#A = a f` with error `≤ 1/2` and
expected time `≤ 8 (3/2) · 1² · Θsum 0 / (1/2)` (units `v/k`). -/
theorem probe :
    ∃ f : ℕ, 1 ≤ f ∧ ∃ a : ℕ, 2 ≤ a ∧
      rawLaw (net rot 1) (net_hasPositiveRates rot 1) (initState 0 c0 a f)
          {ω | ¬ SimOK (ctmSched rot 0 c0 c0_len) (4 * 1) (initState 0 c0 a f) ω} ≤
        ENNReal.ofReal (1 / 2) ∧
      ENNReal.ofReal (1 / 1) * expTime rot (initState (L := 1) 0 c0 a f) (4 * 1) ≤
        ENNReal.ofReal (8 * (3 / 2) ^ 1 * 1 * ((1 : ℕ) : ℝ) ^ 2 * Θsum 0 / (1 * (1 / 2))) := by
  obtain ⟨f, hf, h⟩ := scwb_theorem_3_2_ctm rot 1 le_rfl 0
  obtain ⟨a, ha, herr, htime⟩ := h (1 / 2) (by norm_num) (by norm_num) c0 c0_len 1 le_rfl
  exact ⟨f, hf, a, ha, herr, htime 1 1 one_pos one_pos⟩

/-- The initial state is in the class `𝒦_1(c0)` and has the clock at the top. -/
theorem probe_init (a f : ℕ) :
    K1 (9 * 3 ^ 0) (20 * 3 ^ 0) c0.1 (tval c0.2) (rest (initState (L := 1) 0 c0 a f)) ∧
      ClockAt (a * f) f (Fin.last 1) (initState (Q := Unit) (L := 1) 0 c0 a f) :=
  ⟨initState_K1 0 c0 a f, initState_clockAt 0 c0 a f⟩

/-- `tval 011 = 1·9 + 2·3 + 2 = 17`, and one CTM step gives the tape `110`, value
`2·9 + 2·3 + 1 = 25 = 3 (17 - 9) + 1`. -/
example : tval c0.2 = 17 ∧ (rot.runT c0 1).2 = [true, true, false] ∧
    tval (rot.runT c0 1).2 = 25 := by decide

/-- The target class just before tick 4 is the class `𝒦_4` that encodes the configuration
after one step, and it is nonempty. -/
def k4State : State (Sp Unit 1) := fun s =>
  match s with
  | .u _ false => 9
  | .mem .md => 25
  | .mem .td => 20
  | .mem .ds => 9
  | .mem .bs => 1
  | _ => 0

theorem probe_target :
    schCl rot 0 c0 (4 * 0 + 3) k4State := by
  rw [schCl_three]
  refine ⟨fun s hs hn => ?_, rfl, ?_⟩
  · rcases s with q | q | q | q | ⟨q, b⟩ | _ | c | _ | _ | x
    all_goals first | rfl | (simp [Sp.IsState] at hs)
    cases b
    · simp [CTM.runT, c0] at hn
    · rfl
  · simp [Mem4, memv, k4State, CTM.runT, CTM.stepT, c0, rot, tval, bw]

/-! ### TM level -/

/-- A one-state TM: keep the read bit and move right. -/
def mv : TM.Machine Unit Bool := ⟨(), false, fun _ a => some (a, .R, ())⟩

def c1 : TM.Cfg Unit Bool := ⟨(), ⟨[], true, []⟩⟩

/-- The space premise of the headline: at most `2` cells within `1` step. -/
theorem mv_space : ∀ t' ≤ 1, tlen (tmRun mv c1 t').tape ≤ 2 := by
  intro t' ht'
  interval_cases t' <;> decide

/-- One TM step is `2 · 2 + 2 = 6` CTM steps; the cycle word goes from `10` to `01`, and the
CTM run lands on its canonical encoding (Lemma 6.3 on this instance). -/
example : ctmTime mv 2 c1 1 = 6 ∧ cyc 2 c1.tape = [true, false] ∧
    cyc 2 (tmRun mv c1 1).tape = [false, true] ∧
    (ctmOf mv).runT (encC c1.state (cyc 2 c1.tape)) 6 = encC () [false, true] := by
  decide

/-- The headline on the concrete TM, with `δ = 1/2`. -/
theorem probe_tm :
    ∃ f : ℕ, 1 ≤ f ∧ ∃ a : ℕ, 2 ≤ a ∧
      rawLaw (net (ctmOf mv) 1) (net_hasPositiveRates (ctmOf mv) 1)
          (initState (2 * 2 - 3) (encC c1.state (cyc 2 c1.tape)) a f)
          {ω | ¬ TmOK mv 2 c1 1 (initState (2 * 2 - 3) (encC c1.state (cyc 2 c1.tape)) a f) ω} ≤
        ENNReal.ofReal (1 / 2) := by
  obtain ⟨f, hf, h⟩ := scwb_theorem_3_2 mv rfl 1 le_rfl 2 le_rfl
  obtain ⟨a, ha, herr, -⟩ := h (1 / 2) (by norm_num) (by norm_num) c1 1 le_rfl mv_space
  exact ⟨f, hf, a, ha, herr⟩

/-- The paper-form time bound on the concrete TM: tape length `s = 4`, `δ = 1/2`, `v = k = 1`. -/
theorem probe_tm_time :
    ∃ f : ℕ, 1 ≤ f ∧ ∃ a : ℕ, 2 ≤ a ∧
      ENNReal.ofReal (1 / 1) * expTime (ctmOf mv)
          (initState (L := 1) (2 * 2 - 3) (encC c1.state (cyc 2 c1.tape)) a f)
          (4 * ctmTime mv 2 c1 1) ≤
        ENNReal.ofReal (3168 * (3 / 2) ^ 1 * 1 * ((2 * 2 : ℕ) : ℝ) ^ 3 * ((1 : ℕ) : ℝ) ^ 2 /
          (1 * 3 ^ (2 * 2) * (1 / 2))) := by
  obtain ⟨f, hf, h⟩ := scwb_theorem_3_2 mv rfl 1 le_rfl 2 le_rfl
  obtain ⟨a, ha, -, htime⟩ := h (1 / 2) (by norm_num) (by norm_num) c1 1 le_rfl mv_space
  exact ⟨f, hf, a, ha, (htime 1 1 one_pos one_pos).2⟩

/-- The TM-level success event is nonempty: some jump sequence simulates the TM step. -/
theorem probe_tm_nonempty :
    ∃ f a : ℕ, ∃ ω, TmOK mv 2 c1 1 (initState (L := 1) (2 * 2 - 3)
      (encC c1.state (cyc 2 c1.tape)) a f) ω := by
  obtain ⟨f, -, a, -, herr⟩ := probe_tm
  refine ⟨f, a, ?_⟩
  by_contra hne
  simp only [not_exists] at hne
  haveI := rawLaw_isProbabilityMeasure (net (ctmOf mv) 1) (net_hasPositiveRates (ctmOf mv) 1)
    (initState (2 * 2 - 3) (encC c1.state (cyc 2 c1.tape)) a f)
  have h1 : (1 : ENNReal) ≤ ENNReal.ofReal (1 / 2) := by
    refine le_trans ?_ herr
    rw [← measure_univ (μ := rawLaw (net (ctmOf mv) 1) (net_hasPositiveRates (ctmOf mv) 1)
      (initState (2 * 2 - 3) (encC c1.state (cyc 2 c1.tape)) a f))]
    exact measure_mono fun ω _ => hne ω
  have hlt : ENNReal.ofReal (1 / 2) < 1 := by
    rw [ENNReal.ofReal_lt_one]; norm_num
  exact absurd h1 (not_le.mpr hlt)

end ProbeSCWB32

#print axioms ProbeSCWB32.probe
#print axioms ProbeSCWB32.probe_init
#print axioms ProbeSCWB32.probe_target
#print axioms ProbeSCWB32.mv_space
#print axioms ProbeSCWB32.probe_tm
#print axioms ProbeSCWB32.probe_tm_time
#print axioms ProbeSCWB32.probe_tm_nonempty
