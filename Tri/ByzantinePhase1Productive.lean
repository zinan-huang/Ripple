/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantinePhase1StochOrder
import Tri.MultiProductiveTimeChange
import Tri.RelaxedProductiveTimeChange

/-!
# Productive fixed-fibre bridge for Byzantine Phase I

The paper-worst raw fixed-fibre step is a state-dependent mixture of an inert
self-loop and one step of a conditioned two-point productive kernel.  A
countdown records how many productive events remain and transfers productive-
time estimates to a raw-interaction deadline.
-/

namespace Tri.Byzantine

open scoped BigOperators ENNReal NNReal

noncomputable section

variable {n B z : ℕ}

/-! ## Conditioned paper-worst kernel on a fixed Byzantine fibre -/

noncomputable def phase1DownMass
    (h3 : 3 ≤ n) (q : Phase1Level n B z) : ℝ≥0∞ :=
  movePMF Control.worst q.1 h3 .down

noncomputable def phase1UpMass
    (h3 : 3 ≤ n) (q : Phase1Level n B z) : ℝ≥0∞ :=
  movePMF Control.worst q.1 h3 .up

noncomputable def phase1NonproductiveMass
    (h3 : 3 ≤ n) (q : Phase1Level n B z) : ℝ≥0∞ :=
  movePMF Control.worst q.1 h3 .stay

noncomputable def phase1ProductiveMass
    (h3 : 3 ≤ n) (q : Phase1Level n B z) : ℝ≥0∞ :=
  phase1DownMass h3 q + phase1UpMass h3 q

theorem phase1NonproductiveMass_add_productiveMass
    (h3 : 3 ≤ n) (q : Phase1Level n B z) :
    phase1NonproductiveMass h3 q + phase1ProductiveMass h3 q = 1 := by
  unfold phase1NonproductiveMass phase1ProductiveMass
    phase1DownMass phase1UpMass
  simpa [add_assoc, add_comm, add_left_comm] using
    movePMF_masses_sum Control.worst q.1 h3

/-- Total fixed-fibre update for a productive direction.  Zero-mass impossible
branches are sent to the current state. -/
noncomputable def phase1DirectionNext
    (q : Phase1Level n B z) (up : Bool) : Phase1Level n B z :=
  if up then
    if hy : 0 < State.y q.1 then
      ⟨State.up q.1 hy, by simp [q.2]⟩
    else q
  else
    if hx : 0 < State.x q.1 then
      ⟨State.down q.1 hx, by simp [q.2]⟩
    else q

/-- Boolean direction law obtained by conditioning the paper-worst raw law on
one of its two state-changing atoms. -/
noncomputable def phase1ProductiveDirectionPMF
    (h3 : 3 ≤ n) (q : Phase1Level n B z) : PMF Bool := by
  classical
  let P := phase1ProductiveMass h3 q
  if hP : P ≠ 0 then
    have hPle : P ≤ 1 := by
      rw [← phase1NonproductiveMass_add_productiveMass h3 q]
      exact le_add_left le_rfl
    have hPtop : P ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top hPle
    exact PMF.ofFintype
      (fun up =>
        if up then phase1UpMass h3 q / P
        else phase1DownMass h3 q / P)
      (by
        rw [show (Finset.univ : Finset Bool) = {false, true} by
          ext u
          cases u <;> simp]
        simp only [Finset.sum_insert, Finset.mem_singleton,
          Bool.false_eq_true, not_false_eq_true,
          Finset.sum_singleton, if_false, if_true]
        rw [ENNReal.div_add_div_same]
        exact ENNReal.div_self hP hPtop)
  else
    exact PMF.pure false

@[simp] theorem phase1ProductiveDirectionPMF_false
    (h3 : 3 ≤ n) (q : Phase1Level n B z)
    (hP : phase1ProductiveMass h3 q ≠ 0) :
    phase1ProductiveDirectionPMF h3 q false =
      phase1DownMass h3 q / phase1ProductiveMass h3 q := by
  classical
  unfold phase1ProductiveDirectionPMF
  dsimp only
  rw [dif_pos hP]
  rfl

@[simp] theorem phase1ProductiveDirectionPMF_true
    (h3 : 3 ≤ n) (q : Phase1Level n B z)
    (hP : phase1ProductiveMass h3 q ≠ 0) :
    phase1ProductiveDirectionPMF h3 q true =
      phase1UpMass h3 q / phase1ProductiveMass h3 q := by
  classical
  unfold phase1ProductiveDirectionPMF
  dsimp only
  rw [dif_pos hP]
  rfl

/-- The paper-worst fixed-fibre chain conditioned on one productive event.
When productive mass is zero it is a self-loop, exactly as in
`relaxedProductiveTriChain`. -/
noncomputable def phase1ProductiveReferenceStep
    (h3 : 3 ≤ n) (q : Phase1Level n B z) :
    PMF (Phase1Level n B z) :=
  if hP : phase1ProductiveMass h3 q ≠ 0 then
    (phase1ProductiveDirectionPMF h3 q).map
      (phase1DirectionNext q)
  else
    PMF.pure q

theorem phase1ProductiveReferenceStep_of_ne_zero
    (h3 : 3 ≤ n) (q : Phase1Level n B z)
    (hP : phase1ProductiveMass h3 q ≠ 0) :
    phase1ProductiveReferenceStep h3 q =
      (phase1ProductiveDirectionPMF h3 q).map
        (phase1DirectionNext q) := by
  simp [phase1ProductiveReferenceStep, hP]

theorem phase1ProductiveReferenceStep_of_eq_zero
    (h3 : 3 ≤ n) (q : Phase1Level n B z)
    (hP : phase1ProductiveMass h3 q = 0) :
    phase1ProductiveReferenceStep h3 q = PMF.pure q := by
  simp [phase1ProductiveReferenceStep, hP]

/-! ## Exact identification with the state-dependent relaxed productive law -/

theorem phase1DownMass_eq_relaxed
    (h3 : 3 ≤ n) (q : Phase1Level n B z)
    (rEff : RelaxedRate)
    {xPred mPred : ℕ}
    (hxPred : State.x q.1 = xPred + 1)
    (hmPred : State.y q.1 + State.z q.1 = mPred + 1)
    (hrate : IsPaperEffectiveRate rEff q.1) :
    phase1DownMass h3 q =
      relaxedTriStep rEff (xPred + 1) (mPred + 1) (by
        have ht := State.total q.1
        omega) xPred := by
  have hraw :=
    paperWorst_step_map_x_eq_relaxedTriStep
      rEff q.1 h3 hrate
  have hat := congrArg (fun p : PMF ℕ => p xPred) hraw
  calc
    phase1DownMass h3 q =
        (downWeight Control.worst q.1 : ℝ≥0∞) /
          (Nat.choose n 3 : ℝ≥0∞) := by
      unfold phase1DownMass
      exact movePMF_down Control.worst q.1 h3
    _ = ((step Control.worst q.1 h3).map State.x)
          (State.x q.1 - 1) :=
      (step_x_down_mass Control.worst q.1 h3 (by omega)).symm
    _ = ((step Control.worst q.1 h3).map State.x) xPred := by
      congr 1
      omega
    _ = relaxedTriStep rEff (xPred + 1) (mPred + 1) (by
          have ht := State.total q.1
          omega) xPred := by
      simpa only [hxPred, hmPred] using hat

theorem phase1UpMass_eq_relaxed
    (h3 : 3 ≤ n) (q : Phase1Level n B z)
    (rEff : RelaxedRate)
    {xPred mPred : ℕ}
    (hxPred : State.x q.1 = xPred + 1)
    (hmPred : State.y q.1 + State.z q.1 = mPred + 1)
    (hrate : IsPaperEffectiveRate rEff q.1) :
    phase1UpMass h3 q =
      relaxedTriStep rEff (xPred + 1) (mPred + 1) (by
        have ht := State.total q.1
        omega) (xPred + 2) := by
  have hraw :=
    paperWorst_step_map_x_eq_relaxedTriStep
      rEff q.1 h3 hrate
  have hat := congrArg (fun p : PMF ℕ => p (xPred + 2)) hraw
  calc
    phase1UpMass h3 q =
        (upWeight Control.worst q.1 : ℝ≥0∞) /
          (Nat.choose n 3 : ℝ≥0∞) := by
      unfold phase1UpMass
      exact movePMF_up Control.worst q.1 h3
    _ = ((step Control.worst q.1 h3).map State.x)
          (State.x q.1 + 1) :=
      (step_x_up_mass Control.worst q.1 h3).symm
    _ = ((step Control.worst q.1 h3).map State.x) (xPred + 2) := by
      congr 1
      omega
    _ = relaxedTriStep rEff (xPred + 1) (mPred + 1) (by
          have ht := State.total q.1
          omega) (xPred + 2) := by
      simpa only [hxPred, hmPred] using hat

theorem phase1ProductiveMass_eq_relaxed
    (h3 : 3 ≤ n) (q : Phase1Level n B z)
    (rEff : RelaxedRate)
    {xPred mPred : ℕ}
    (hxPred : State.x q.1 = xPred + 1)
    (hmPred : State.y q.1 + State.z q.1 = mPred + 1)
    (hrate : IsPaperEffectiveRate rEff q.1) :
    phase1ProductiveMass h3 q =
      relaxedTriStep rEff (xPred + 1) (mPred + 1) (by
          have ht := State.total q.1
          omega) xPred +
        relaxedTriStep rEff (xPred + 1) (mPred + 1) (by
          have ht := State.total q.1
          omega) (xPred + 2) := by
  unfold phase1ProductiveMass
  rw [phase1DownMass_eq_relaxed h3 q rEff hxPred hmPred hrate,
    phase1UpMass_eq_relaxed h3 q rEff hxPred hmPred hrate]

/-- Exact expectation of the conditioned fixed-fibre law at its two support
points. -/
theorem expect_phase1ProductiveReferenceStep
    (h3 : 3 ≤ n) (q : Phase1Level n B z)
    (hP : phase1ProductiveMass h3 q ≠ 0)
    (F : Phase1Level n B z → ℝ≥0∞) :
    expect (phase1ProductiveReferenceStep h3 q) F =
      phase1DownMass h3 q / phase1ProductiveMass h3 q *
          F (phase1DirectionNext q false) +
        phase1UpMass h3 q / phase1ProductiveMass h3 q *
          F (phase1DirectionNext q true) := by
  rw [phase1ProductiveReferenceStep_of_ne_zero h3 q hP, expect_map]
  unfold expect
  rw [tsum_fintype]
  rw [show (Finset.univ : Finset Bool) = {false, true} by
    ext up
    cases up <;> simp]
  simp [phase1ProductiveDirectionPMF_false h3 q hP,
    phase1ProductiveDirectionPMF_true h3 q hP]

/-- The fixed-fibre conditioned law has exactly the state-dependent effective
relaxed productive `X` law. -/
theorem phase1ProductiveReferenceStep_map_x_eq_relaxed
    (h3 : 3 ≤ n) (q : Phase1Level n B z)
    (rEff : RelaxedRate)
    {xPred mPred : ℕ}
    (hxPred : State.x q.1 = xPred + 1)
    (hmPred : State.y q.1 + State.z q.1 = mPred + 1)
    (hy : 0 < State.y q.1)
    (hrate : IsPaperEffectiveRate rEff q.1)
    (hP : phase1ProductiveMass h3 q ≠ 0) :
    (phase1ProductiveReferenceStep h3 q).map
        (fun r => State.x r.1) =
      relaxedProductiveTriChain rEff n (State.x q.1) := by
  have hpop : xPred + mPred + 2 = n := by
    have ht := State.total q.1
    omega
  have hmass :=
    phase1ProductiveMass_eq_relaxed
      h3 q rEff hxPred hmPred hrate
  have hprod :
      relaxedTriStep rEff (xPred + 1) (mPred + 1) (by omega) xPred +
          relaxedTriStep rEff (xPred + 1) (mPred + 1) (by omega)
            (xPred + 2) ≠ 0 := by
    intro hz0
    apply hP
    exact hmass.trans hz0
  have hdown :=
    phase1DownMass_eq_relaxed
      h3 q rEff hxPred hmPred hrate
  have hup :=
    phase1UpMass_eq_relaxed
      h3 q rEff hxPred hmPred hrate
  have hdir :
      phase1ProductiveDirectionPMF h3 q =
        relaxedProductiveDirectionPMF
          rEff xPred mPred (by omega) hprod := by
    apply PMF.ext
    intro up
    cases up with
    | false =>
        rw [phase1ProductiveDirectionPMF_false h3 q hP,
          relaxedProductiveDirectionPMF_false,
          hdown, hmass]
    | true =>
        rw [phase1ProductiveDirectionPMF_true h3 q hP,
          relaxedProductiveDirectionPMF_true,
          hup, hmass]
  have hxpos : 0 < State.x q.1 := by omega
  calc
    (phase1ProductiveReferenceStep h3 q).map
          (fun r => State.x r.1) =
        ((phase1ProductiveDirectionPMF h3 q).map
          (phase1DirectionNext q)).map
          (fun r => State.x r.1) := by
      rw [phase1ProductiveReferenceStep_of_ne_zero h3 q hP]
    _ = (phase1ProductiveDirectionPMF h3 q).map
          (fun up => State.x (phase1DirectionNext q up).1) := by
      rw [PMF.map_comp]
      rfl
    _ = (relaxedProductiveDirectionPMF
          rEff xPred mPred (by omega) hprod).map
          (fun up => if up then xPred + 2 else xPred) := by
      rw [hdir]
      apply congrArg
        (fun g : Bool → ℕ =>
          (relaxedProductiveDirectionPMF
            rEff xPred mPred (by omega) hprod).map g)
      funext up
      cases up <;>
        simp [phase1DirectionNext, hxpos, hy, hxPred]
    _ = relaxedProductiveTriInterior
          rEff xPred mPred (by omega) hprod := by
      rfl
    _ = relaxedProductiveTriChain rEff n (State.x q.1) := by
      rw [hxPred]
      exact (relaxedProductiveTriChain_apply rEff hpop h3 hprod).symm

/-! ## Exact raw/productive mixture -/

private theorem phase1_three_mass_mixture
    {down stay up gd gs gu : ℝ≥0∞}
    (hprod : down + up ≠ 0)
    (hprodTop : down + up ≠ ⊤) :
    down * gd + stay * gs + up * gu =
      stay * gs +
        (down + up) *
          (down / (down + up) * gd +
            up / (down + up) * gu) := by
  have hdown :
      (down + up) * (down / (down + up)) = down :=
    ENNReal.mul_div_cancel hprod hprodTop
  have hup :
      (down + up) * (up / (down + up)) = up :=
    ENNReal.mul_div_cancel hprod hprodTop
  calc
    down * gd + stay * gs + up * gu =
        stay * gs +
          ((down + up) * (down / (down + up))) * gd +
          ((down + up) * (up / (down + up))) * gu := by
      rw [hdown, hup]
      ring
    _ = _ := by ring

/-- One paper-worst raw step is its inert self-loop contribution plus its
productive mass times the conditioned productive expectation. -/
theorem expect_phase1ReferenceStep_eq_nonproductive_add_productive
    (h3 : 3 ≤ n) (q : Phase1Level n B z)
    (hx : 0 < State.x q.1) (hy : 0 < State.y q.1)
    (F : Phase1Level n B z → ℝ≥0∞) :
    expect (phase1ReferenceStep h3 q) F =
      phase1NonproductiveMass h3 q * F q +
        phase1ProductiveMass h3 q *
          expect (phase1ProductiveReferenceStep h3 q) F := by
  classical
  have hraw :
      expect (phase1ReferenceStep h3 q) F =
        movePMF Control.worst q.1 h3 .down *
            phase1FiberValue q F (State.x q.1 - 1) +
          movePMF Control.worst q.1 h3 .stay *
            phase1FiberValue q F (State.x q.1) +
          movePMF Control.worst q.1 h3 .up *
            phase1FiberValue q F (State.x q.1 + 1) := by
    calc
      expect (phase1ReferenceStep h3 q) F =
          expect ((step Control.worst q.1 h3).map State.x)
            (phase1FiberValue q F) :=
        phase1ReferenceStep_expect_eq_x q h3 q F
      _ = expect (step Control.worst q.1 h3)
            (fun s => phase1FiberValue q F (State.x s)) := by
        rw [expect_map]
      _ = _ :=
        expect_step_x_actions Control.worst q.1 h3
          (phase1FiberValue q F)
  have hcenter :
      phase1FiberValue q F (State.x q.1) = F q :=
    phase1FiberValue_eq_of_level q F q
  have hdownState :
      State.x (phase1DirectionNext q false).1 =
        State.x q.1 - 1 := by
    simp [phase1DirectionNext, hx]
  have hupState :
      State.x (phase1DirectionNext q true).1 =
        State.x q.1 + 1 := by
    simp [phase1DirectionNext, hy]
  have hdownValue :
      phase1FiberValue q F (State.x q.1 - 1) =
        F (phase1DirectionNext q false) := by
    rw [← hdownState]
    exact phase1FiberValue_eq_of_level
      q F (phase1DirectionNext q false)
  have hupValue :
      phase1FiberValue q F (State.x q.1 + 1) =
        F (phase1DirectionNext q true) := by
    rw [← hupState]
    exact phase1FiberValue_eq_of_level
      q F (phase1DirectionNext q true)
  rw [hraw, hdownValue, hcenter, hupValue]
  change
    phase1DownMass h3 q * F (phase1DirectionNext q false) +
          phase1NonproductiveMass h3 q * F q +
        phase1UpMass h3 q * F (phase1DirectionNext q true) =
      phase1NonproductiveMass h3 q * F q +
        phase1ProductiveMass h3 q *
          expect (phase1ProductiveReferenceStep h3 q) F
  by_cases hP : phase1ProductiveMass h3 q = 0
  · have hdu :
        phase1DownMass h3 q = 0 ∧ phase1UpMass h3 q = 0 := by
      apply add_eq_zero.mp
      simpa only [phase1ProductiveMass] using hP
    rw [hdu.1, hdu.2, hP]
    simp
  · have hPle : phase1ProductiveMass h3 q ≤ 1 := by
      rw [← phase1NonproductiveMass_add_productiveMass h3 q]
      exact le_add_left le_rfl
    have hPtop : phase1ProductiveMass h3 q ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top hPle
    rw [expect_phase1ProductiveReferenceStep h3 q hP F]
    exact phase1_three_mass_mixture hP hPtop

/-! ## Productive countdown and raw-clock bridge -/

/-- Raw paper-worst chain with a decreasing remaining-productive-events
counter. -/
noncomputable def phase1ProductiveCountdown
    (h3 : 3 ≤ n) :
    Phase1Level n B z × ℕ → PMF (Phase1Level n B z × ℕ)
  | q@(_, 0) => PMF.pure q
  | (s, k + 1) =>
      (phase1ReferenceStep h3 s).map fun t =>
        if t = s then (s, k + 1) else (t, k)

@[simp] theorem phase1ProductiveCountdown_zero
    (h3 : 3 ≤ n) (q : Phase1Level n B z) :
    phase1ProductiveCountdown h3 (q, 0) = PMF.pure (q, 0) :=
  rfl

theorem phase1ProductiveCountdown_succ_map_fst
    (h3 : 3 ≤ n) (q : Phase1Level n B z) (k : ℕ) :
    (phase1ProductiveCountdown h3 (q, k + 1)).map Prod.fst =
      phase1ReferenceStep h3 q := by
  unfold phase1ProductiveCountdown
  rw [PMF.map_comp]
  have hf :
      (Prod.fst ∘ fun t : Phase1Level n B z =>
        if t = q then (q, k + 1) else (t, k)) = id := by
    funext t
    by_cases ht : t = q <;> simp [ht]
  rw [hf, PMF.map_id]

/-- Exact one-step inert/productive mixture for the countdown. -/
theorem expect_phase1ProductiveCountdown_succ
    (h3 : 3 ≤ n) (q : Phase1Level n B z) (k : ℕ)
    (hx : 0 < State.x q.1) (hy : 0 < State.y q.1)
    (G : Phase1Level n B z × ℕ → ℝ≥0∞) :
    expect (phase1ProductiveCountdown h3 (q, k + 1)) G =
      phase1NonproductiveMass h3 q * G (q, k + 1) +
        phase1ProductiveMass h3 q *
          expect (phase1ProductiveReferenceStep h3 q)
            (fun t => G (t, k)) := by
  classical
  unfold phase1ProductiveCountdown
  rw [expect_map]
  let H : Phase1Level n B z → ℝ≥0∞ := fun t =>
    G (if t = q then (q, k + 1) else (t, k))
  change expect (phase1ReferenceStep h3 q) H = _
  rw [expect_phase1ReferenceStep_eq_nonproductive_add_productive
    h3 q hx hy H]
  have hHq : H q = G (q, k + 1) := by
    simp [H]
  rw [hHq]
  by_cases hP : phase1ProductiveMass h3 q = 0
  · rw [hP]
    simp
  · have hdownNe : phase1DirectionNext q false ≠ q := by
      intro hEq
      have hxEq := congrArg
        (fun s : Phase1Level n B z => State.x s.1) hEq
      have : State.x q.1 - 1 = State.x q.1 := by
        simpa [phase1DirectionNext, hx] using hxEq
      omega
    have hupNe : phase1DirectionNext q true ≠ q := by
      intro hEq
      have hxEq := congrArg
        (fun s : Phase1Level n B z => State.x s.1) hEq
      have : State.x q.1 + 1 = State.x q.1 := by
        simpa [phase1DirectionNext, hy] using hxEq
      omega
    have hproductive :
        expect (phase1ProductiveReferenceStep h3 q) H =
          expect (phase1ProductiveReferenceStep h3 q)
            (fun t => G (t, k)) := by
      rw [expect_phase1ProductiveReferenceStep h3 q hP H,
        expect_phase1ProductiveReferenceStep h3 q hP
          (fun t => G (t, k))]
      simp [H, hdownNe, hupNe]
    rw [hproductive]

/-- Countdown frozen when a physical fixed-fibre boundary is reached. -/
noncomputable def phase1ProductiveCountdownStop
    (Stop : Phase1Level n B z → Prop) [DecidablePred Stop]
    (h3 : 3 ≤ n) :
    Phase1Level n B z × ℕ → PMF (Phase1Level n B z × ℕ) :=
  freeze (fun q => Stop q.1) (phase1ProductiveCountdown h3)

theorem phase1ProductiveCountdownStop_isLazyProjection
    (Stop : Phase1Level n B z → Prop) [DecidablePred Stop]
    (h3 : 3 ≤ n) :
    IsLazyProjection (phase1ReferenceStep h3)
      (phase1ProductiveCountdownStop Stop h3) Prod.fst := by
  classical
  intro qr
  rcases qr with ⟨q, r⟩
  by_cases hStop : Stop q
  · right
    have hPair :
        (fun p : Phase1Level n B z × ℕ => Stop p.1) (q, r) := hStop
    rw [phase1ProductiveCountdownStop,
      freeze_of_mem (q, r) hPair]
    exact PMF.pure_map Prod.fst (q, r)
  · have hPair :
        ¬ (fun p : Phase1Level n B z × ℕ => Stop p.1) (q, r) := hStop
    rw [phase1ProductiveCountdownStop,
      freeze_of_not_mem (q, r) hPair]
    cases r with
    | zero =>
        right
        rw [phase1ProductiveCountdown_zero]
        exact PMF.pure_map Prod.fst (q, 0)
    | succ r =>
        left
        exact phase1ProductiveCountdown_succ_map_fst h3 q r

theorem phase1ReferenceStep_targetFailure_le_productiveCountdownStop
    (Target Stop : Phase1Level n B z → Prop)
    [DecidablePred Target] [DecidablePred Stop]
    (h3 : 3 ≤ n) (T K : ℕ) (q0 : Phase1Level n B z) :
    terminalFailureMass
        (iter (freeze Target (phase1ReferenceStep h3)) T q0)
        Target ≤
      terminalFailureMass
        (iter (phase1ProductiveCountdownStop Stop h3) T (q0, K))
        (fun q => Target q.1) := by
  exact targetFreeze_failure_le_lazy_projection
    Target (phase1ReferenceStep h3)
    (phase1ProductiveCountdownStop Stop h3) Prod.fst
    (phase1ProductiveCountdownStop_isLazyProjection Stop h3)
    T (q0, K)

@[simp] theorem phase1ProductiveCountdownStop_zero
    (Stop : Phase1Level n B z → Prop) [DecidablePred Stop]
    (h3 : 3 ≤ n) (q : Phase1Level n B z) :
    phase1ProductiveCountdownStop Stop h3 (q, 0) =
      PMF.pure (q, 0) := by
  by_cases hStop : Stop q
  · have hPair :
        (fun p : Phase1Level n B z × ℕ => Stop p.1) (q, 0) := hStop
    rw [phase1ProductiveCountdownStop,
      freeze_of_mem (q, 0) hPair]
  · have hPair :
        ¬ (fun p : Phase1Level n B z × ℕ => Stop p.1) (q, 0) := hStop
    rw [phase1ProductiveCountdownStop,
      freeze_of_not_mem (q, 0) hPair,
      phase1ProductiveCountdown_zero]

theorem iter_phase1ProductiveCountdownStop_of_boundary
    (Stop : Phase1Level n B z → Prop) [DecidablePred Stop]
    (h3 : 3 ≤ n) (q : Phase1Level n B z) (r : ℕ)
    (hStop : Stop q) :
    ∀ T,
      iter (phase1ProductiveCountdownStop Stop h3) T (q, r) =
        PMF.pure (q, r) := by
  intro T
  have hPair :
      (fun p : Phase1Level n B z × ℕ => Stop p.1) (q, r) := hStop
  simpa only [phase1ProductiveCountdownStop] using
    iter_targetFreeze_of_mem
      (fun p : Phase1Level n B z × ℕ => Stop p.1)
      (phase1ProductiveCountdown h3) (q, r) hPair T

/-- A stopped raw countdown resolved either by its boundary or by completing
its quota is bounded by the boundary-stopped productive chain. -/
theorem phase1ProductiveCountdownStop_resolved_le
    (Stop : Phase1Level n B z → Prop) [DecidablePred Stop]
    (h3 : 3 ≤ n)
    (hlive : ∀ q, ¬ Stop q →
      0 < State.x q.1 ∧ 0 < State.y q.1)
    (F : Phase1Level n B z → ℝ≥0∞) :
    ∀ T r (q : Phase1Level n B z),
      expect (iter (phase1ProductiveCountdownStop Stop h3) T (q, r))
          (fun u => if u.2 = 0 ∨ Stop u.1 then F u.1 else 0) ≤
        expect (iter (freeze Stop (phase1ProductiveReferenceStep h3)) r q) F := by
  intro T
  induction T with
  | zero =>
      intro r q
      cases r with
      | zero => simp [iter]
      | succ r =>
          by_cases hStop : Stop q
          · rw [iter_targetFreeze_of_mem Stop
                (phase1ProductiveReferenceStep h3) q hStop (r + 1)]
            simp [iter, hStop]
          · simp [iter, hStop]
  | succ T ih =>
      intro r q
      cases r with
      | zero =>
          rw [iter_succ, phase1ProductiveCountdownStop_zero,
            PMF.pure_bind]
          simpa [iter] using ih 0 q
      | succ r =>
          by_cases hStop : Stop q
          · rw [iter_phase1ProductiveCountdownStop_of_boundary
                Stop h3 q (r + 1) hStop,
              iter_targetFreeze_of_mem Stop
                (phase1ProductiveReferenceStep h3) q hStop (r + 1)]
            simp [hStop]
          · rw [iter_succ, expect_bind]
            change
              expect (phase1ProductiveCountdownStop Stop h3 (q, r + 1))
                  (fun a =>
                    expect
                      (iter (phase1ProductiveCountdownStop Stop h3) T a)
                      (fun u =>
                        if u.2 = 0 ∨ Stop u.1 then F u.1 else 0)) ≤
                expect
                  (iter (freeze Stop (phase1ProductiveReferenceStep h3))
                    (r + 1) q) F
            have hPair :
                ¬ (fun p : Phase1Level n B z × ℕ => Stop p.1)
                  (q, r + 1) := hStop
            rw [phase1ProductiveCountdownStop,
              freeze_of_not_mem (q, r + 1) hPair,
              expect_phase1ProductiveCountdown_succ
                h3 q r (hlive q hStop).1 (hlive q hStop).2]
            let V : Phase1Level n B z → ℝ≥0∞ := fun d =>
              expect
                (iter (freeze Stop (phase1ProductiveReferenceStep h3)) r d) F
            have hsmall :
                expect (phase1ProductiveReferenceStep h3 q)
                    (fun d =>
                      expect
                        (iter (phase1ProductiveCountdownStop Stop h3) T (d, r))
                        (fun u =>
                          if u.2 = 0 ∨ Stop u.1 then F u.1 else 0)) ≤
                  expect (phase1ProductiveReferenceStep h3 q) V := by
              unfold expect
              exact ENNReal.tsum_le_tsum fun d =>
                mul_le_mul_right (ih r d) _
            have htarget :
                expect
                    (iter (freeze Stop (phase1ProductiveReferenceStep h3))
                      (r + 1) q) F =
                  expect (phase1ProductiveReferenceStep h3 q) V := by
              rw [iter_succ, freeze_of_not_mem q hStop, expect_bind]
              rfl
            calc
              phase1NonproductiveMass h3 q *
                    expect
                      (iter (phase1ProductiveCountdownStop Stop h3) T
                        (q, r + 1))
                      (fun u =>
                        if u.2 = 0 ∨ Stop u.1 then F u.1 else 0) +
                  phase1ProductiveMass h3 q *
                    expect (phase1ProductiveReferenceStep h3 q)
                      (fun d =>
                        expect
                          (iter (phase1ProductiveCountdownStop Stop h3) T
                            (d, r))
                          (fun u =>
                            if u.2 = 0 ∨ Stop u.1 then F u.1 else 0)) ≤
                phase1NonproductiveMass h3 q *
                    expect
                      (iter (freeze Stop (phase1ProductiveReferenceStep h3))
                        (r + 1) q) F +
                  phase1ProductiveMass h3 q *
                    expect (phase1ProductiveReferenceStep h3 q) V := by
                exact add_le_add
                  (mul_le_mul_left' (ih (r + 1) q) _)
                  (mul_le_mul_left' hsmall _)
              _ = phase1NonproductiveMass h3 q *
                    expect
                      (iter (freeze Stop (phase1ProductiveReferenceStep h3))
                        (r + 1) q) F +
                  phase1ProductiveMass h3 q *
                    expect
                      (iter (freeze Stop (phase1ProductiveReferenceStep h3))
                        (r + 1) q) F := by
                rw [htarget]
              _ = expect
                    (iter (freeze Stop (phase1ProductiveReferenceStep h3))
                      (r + 1) q) F := by
                rw [← add_mul,
                  phase1NonproductiveMass_add_productiveMass, one_mul]

noncomputable def phase1ProductiveCountdownLivePotential
    (Stop : Phase1Level n B z → Prop) [DecidablePred Stop] :
    Phase1Level n B z × ℕ → ℝ≥0∞ := fun q =>
  if Stop q.1 ∨ q.2 = 0 then 0 else (2 : ℝ≥0∞) ^ q.2

theorem phase1ProductiveCountdownStop_livePotential_super
    (Stop : Phase1Level n B z → Prop) [DecidablePred Stop]
    (h3 : 3 ≤ n)
    (p p' : ℝ≥0∞) (hp : p + p' = 1)
    (hlive : ∀ q, ¬ Stop q →
      0 < State.x q.1 ∧ 0 < State.y q.1)
    (hpFloor : ∀ q, ¬ Stop q →
      p ≤ phase1ProductiveMass h3 q) :
    ∀ qr,
      expect (phase1ProductiveCountdownStop Stop h3 qr)
          (phase1ProductiveCountdownLivePotential Stop) ≤
        (p' + p * ((1 : ℝ≥0∞) / 2)) *
          phase1ProductiveCountdownLivePotential Stop qr := by
  intro qr
  rcases qr with ⟨q, r⟩
  by_cases hStop : Stop q
  · have hPair :
        (fun u : Phase1Level n B z × ℕ => Stop u.1) (q, r) := hStop
    rw [phase1ProductiveCountdownStop,
      freeze_of_mem (q, r) hPair, expect_pure]
    simp [phase1ProductiveCountdownLivePotential, hStop]
  · cases r with
    | zero =>
        rw [phase1ProductiveCountdownStop_zero, expect_pure]
        simp [phase1ProductiveCountdownLivePotential, hStop]
    | succ r =>
        have hPair :
            ¬ (fun u : Phase1Level n B z × ℕ => Stop u.1)
              (q, r + 1) := hStop
        rw [phase1ProductiveCountdownStop,
          freeze_of_not_mem (q, r + 1) hPair,
          expect_phase1ProductiveCountdown_succ
            h3 q r (hlive q hStop).1 (hlive q hStop).2]
        have hproductive :
            expect (phase1ProductiveReferenceStep h3 q)
                (fun d =>
                  phase1ProductiveCountdownLivePotential Stop (d, r)) ≤
              (2 : ℝ≥0∞) ^ r := by
          unfold expect
          calc
            (∑' d,
              phase1ProductiveReferenceStep h3 q d *
                phase1ProductiveCountdownLivePotential Stop (d, r)) ≤
                ∑' d,
                  phase1ProductiveReferenceStep h3 q d *
                    (2 : ℝ≥0∞) ^ r := by
              exact ENNReal.tsum_le_tsum fun d =>
                mul_le_mul_right
                  (by
                    unfold phase1ProductiveCountdownLivePotential
                    split_ifs <;> simp) _
            _ = (∑' d, phase1ProductiveReferenceStep h3 q d) *
                (2 : ℝ≥0∞) ^ r := by
              rw [ENNReal.tsum_mul_right]
            _ = (2 : ℝ≥0∞) ^ r := by
              rw [PMF.tsum_coe, one_mul]
        have hqsum :
            phase1ProductiveMass h3 q +
                phase1NonproductiveMass h3 q = 1 := by
          simpa [add_comm] using
            phase1NonproductiveMass_add_productiveMass h3 q
        have hfactor :=
          step_factor_antitone_ennreal hp hqsum
            (by norm_num : ((1 : ℝ≥0∞) / 2) ≤ 1)
            (hpFloor q hStop)
        have hpow :
            (2 : ℝ≥0∞) ^ r =
              ((1 : ℝ≥0∞) / 2) * (2 : ℝ≥0∞) ^ (r + 1) := by
          have hhalfTwo :
              ((1 : ℝ≥0∞) / 2) * 2 = 1 := by
            calc
              ((1 : ℝ≥0∞) / 2) * 2 =
                  2 * ((1 : ℝ≥0∞) / 2) := by ring
              _ = 1 := by
                rw [one_div,
                  ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
          symm
          calc
            ((1 : ℝ≥0∞) / 2) * (2 : ℝ≥0∞) ^ (r + 1) =
                ((1 : ℝ≥0∞) / 2) *
                  ((2 : ℝ≥0∞) ^ r * 2) := by rw [pow_succ]
            _ = (2 : ℝ≥0∞) ^ r *
                  (((1 : ℝ≥0∞) / 2) * 2) := by ring
            _ = (2 : ℝ≥0∞) ^ r := by rw [hhalfTwo, mul_one]
        simp only [phase1ProductiveCountdownLivePotential, hStop,
          false_or, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
        calc
          phase1NonproductiveMass h3 q * (2 : ℝ≥0∞) ^ (r + 1) +
                phase1ProductiveMass h3 q *
                  expect (phase1ProductiveReferenceStep h3 q)
                    (fun d =>
                      phase1ProductiveCountdownLivePotential Stop (d, r)) ≤
              phase1NonproductiveMass h3 q * (2 : ℝ≥0∞) ^ (r + 1) +
                phase1ProductiveMass h3 q * (2 : ℝ≥0∞) ^ r := by
            exact add_le_add le_rfl
              (mul_le_mul_left' hproductive _)
          _ = (phase1NonproductiveMass h3 q +
                  phase1ProductiveMass h3 q * ((1 : ℝ≥0∞) / 2)) *
                (2 : ℝ≥0∞) ^ (r + 1) := by
            rw [hpow]
            ring
          _ ≤ (p' + p * ((1 : ℝ≥0∞) / 2)) *
                (2 : ℝ≥0∞) ^ (r + 1) :=
            mul_le_mul_left hfactor _

theorem phase1ProductiveCountdownStop_live_tail
    (Stop : Phase1Level n B z → Prop) [DecidablePred Stop]
    (h3 : 3 ≤ n)
    (p p' : ℝ≥0∞) (hp : p + p' = 1)
    (hlive : ∀ q, ¬ Stop q →
      0 < State.x q.1 ∧ 0 < State.y q.1)
    (hpFloor : ∀ q, ¬ Stop q →
      p ≤ phase1ProductiveMass h3 q)
    (T K : ℕ) (q0 : Phase1Level n B z) :
    (∑' qr, if ¬ Stop qr.1 ∧ qr.2 ≠ 0 then
        iter (phase1ProductiveCountdownStop Stop h3) T (q0, K) qr
      else 0) ≤
      (p' + p * ((1 : ℝ≥0∞) / 2)) ^ T *
        (2 : ℝ≥0∞) ^ K := by
  let V : Phase1Level n B z × ℕ → ℝ≥0∞ :=
    phase1ProductiveCountdownLivePotential Stop
  have hpoint : ∀ qr,
      (if ¬ Stop qr.1 ∧ qr.2 ≠ 0 then
          iter (phase1ProductiveCountdownStop Stop h3) T (q0, K) qr
        else 0) ≤
        iter (phase1ProductiveCountdownStop Stop h3) T (q0, K) qr *
          V qr := by
    intro qr
    by_cases hqr : ¬ Stop qr.1 ∧ qr.2 ≠ 0
    · have hr : 1 ≤ qr.2 := Nat.one_le_iff_ne_zero.mpr hqr.2
      have hpow : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ qr.2 :=
        one_le_pow₀ (by norm_num)
      rw [if_pos hqr]
      change
        iter (phase1ProductiveCountdownStop Stop h3) T (q0, K) qr ≤
          iter (phase1ProductiveCountdownStop Stop h3) T (q0, K) qr *
            phase1ProductiveCountdownLivePotential Stop qr
      rw [phase1ProductiveCountdownLivePotential,
        if_neg (by simp [hqr.1, hqr.2])]
      simpa only [mul_one] using
        mul_le_mul_right hpow
          (iter (phase1ProductiveCountdownStop Stop h3) T (q0, K) qr)
    · simp [hqr]
  calc
    (∑' qr, if ¬ Stop qr.1 ∧ qr.2 ≠ 0 then
        iter (phase1ProductiveCountdownStop Stop h3) T (q0, K) qr
      else 0) ≤
      expect (iter (phase1ProductiveCountdownStop Stop h3) T (q0, K)) V := by
        unfold expect
        exact ENNReal.tsum_le_tsum hpoint
    _ ≤ (p' + p * ((1 : ℝ≥0∞) / 2)) ^ T * V (q0, K) :=
      expect_iter_le
        (phase1ProductiveCountdownStop Stop h3) V
        (p' + p * ((1 : ℝ≥0∞) / 2))
        (by
          simpa only [V] using
            phase1ProductiveCountdownStop_livePotential_super
              Stop h3 p p' hp hlive hpFloor)
        T (q0, K)
    _ ≤ (p' + p * ((1 : ℝ≥0∞) / 2)) ^ T *
          (2 : ℝ≥0∞) ^ K := by
      apply mul_le_mul_left'
      unfold V phase1ProductiveCountdownLivePotential
      split_ifs <;> simp

theorem phase1ProductiveCountdownStop_failure_le
    (Target Stop : Phase1Level n B z → Prop)
    [DecidablePred Target] [DecidablePred Stop]
    (h3 : 3 ≤ n)
    (hlive : ∀ q, ¬ Stop q →
      0 < State.x q.1 ∧ 0 < State.y q.1)
    (T K : ℕ) (q0 : Phase1Level n B z) :
    terminalFailureMass
        (iter (phase1ProductiveCountdownStop Stop h3) T (q0, K))
        (fun qr => Target qr.1) ≤
      terminalFailureMass
          (iter (freeze Stop (phase1ProductiveReferenceStep h3)) K q0)
          Target +
        ∑' qr, if ¬ Stop qr.1 ∧ qr.2 ≠ 0 then
          iter (phase1ProductiveCountdownStop Stop h3) T (q0, K) qr
        else 0 := by
  let law :=
    iter (phase1ProductiveCountdownStop Stop h3) T (q0, K)
  let F : Phase1Level n B z → ℝ≥0∞ := fun q =>
    if Target q then 0 else 1
  let Resolved : Phase1Level n B z × ℕ → Prop := fun qr =>
    qr.2 = 0 ∨ Stop qr.1
  have hpoint : ∀ qr,
      law qr * (if Target qr.1 then 0 else 1) ≤
        law qr * (if Resolved qr then F qr.1 else 0) +
          (if ¬ Stop qr.1 ∧ qr.2 ≠ 0 then law qr else 0) := by
    intro qr
    by_cases hTarget : Target qr.1
    · simp [hTarget]
    · by_cases hResolved : Resolved qr
      · simp [hTarget, hResolved, Resolved, F]
      · have hLive : ¬ Stop qr.1 ∧ qr.2 ≠ 0 :=
          ⟨(fun hStop => hResolved (Or.inr hStop)),
            (fun hzero => hResolved (Or.inl hzero))⟩
        simp [hTarget, hResolved, hLive, F]
  have hresolved :=
    phase1ProductiveCountdownStop_resolved_le
      Stop h3 hlive F T K q0
  rw [terminalFailureMass_eq_expect,
    terminalFailureMass_eq_expect]
  calc
    expect law
          (fun qr => (if Target qr.1 then 0 else 1 : ℝ≥0∞)) ≤
        expect law
            (fun qr => if Resolved qr then F qr.1 else 0) +
          ∑' qr, if ¬ Stop qr.1 ∧ qr.2 ≠ 0 then law qr else 0 := by
      unfold expect
      rw [← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum hpoint
    _ ≤ expect
          (iter (freeze Stop (phase1ProductiveReferenceStep h3)) K q0) F +
        ∑' qr, if ¬ Stop qr.1 ∧ qr.2 ≠ 0 then law qr else 0 :=
      add_le_add
        (by simpa only [law, Resolved] using hresolved) le_rfl
    _ = expect
          (iter (freeze Stop (phase1ProductiveReferenceStep h3)) K q0)
            (fun q => (if Target q then 0 else 1 : ℝ≥0∞)) +
        ∑' qr, if ¬ Stop qr.1 ∧ qr.2 ≠ 0 then law qr else 0 := rfl

theorem phase1ProductiveCountdownStop_failure_le_clock
    (Target Stop : Phase1Level n B z → Prop)
    [DecidablePred Target] [DecidablePred Stop]
    (h3 : 3 ≤ n)
    (p p' : ℝ≥0∞) (hp : p + p' = 1)
    (hlive : ∀ q, ¬ Stop q →
      0 < State.x q.1 ∧ 0 < State.y q.1)
    (hpFloor : ∀ q, ¬ Stop q →
      p ≤ phase1ProductiveMass h3 q)
    (T K : ℕ) (q0 : Phase1Level n B z) :
    terminalFailureMass
        (iter (phase1ProductiveCountdownStop Stop h3) T (q0, K))
        (fun qr => Target qr.1) ≤
      terminalFailureMass
          (iter (freeze Stop (phase1ProductiveReferenceStep h3)) K q0)
          Target +
        (p' + p * ((1 : ℝ≥0∞) / 2)) ^ T *
          (2 : ℝ≥0∞) ^ K := by
  exact
    (phase1ProductiveCountdownStop_failure_le
      Target Stop h3 hlive T K q0).trans
      (add_le_add le_rfl
        (phase1ProductiveCountdownStop_live_tail
          Stop h3 p p' hp hlive hpFloor T K q0))

theorem phase1ReferenceStep_failure_le_productive_add_clock
    (Target Stop : Phase1Level n B z → Prop)
    [DecidablePred Target] [DecidablePred Stop]
    (h3 : 3 ≤ n)
    (p p' : ℝ≥0∞) (hp : p + p' = 1)
    (hlive : ∀ q, ¬ Stop q →
      0 < State.x q.1 ∧ 0 < State.y q.1)
    (hpFloor : ∀ q, ¬ Stop q →
      p ≤ phase1ProductiveMass h3 q)
    (T K : ℕ) (q0 : Phase1Level n B z) :
    terminalFailureMass
        (iter (freeze Target (phase1ReferenceStep h3)) T q0)
        Target ≤
      terminalFailureMass
          (iter (freeze Stop (phase1ProductiveReferenceStep h3)) K q0)
          Target +
        (p' + p * ((1 : ℝ≥0∞) / 2)) ^ T *
          (2 : ℝ≥0∞) ^ K := by
  calc
    terminalFailureMass
        (iter (freeze Target (phase1ReferenceStep h3)) T q0)
        Target ≤
      terminalFailureMass
        (iter (phase1ProductiveCountdownStop Stop h3) T (q0, K))
        (fun qr => Target qr.1) :=
      phase1ReferenceStep_targetFailure_le_productiveCountdownStop
        Target Stop h3 T K q0
    _ ≤ _ :=
      phase1ProductiveCountdownStop_failure_le_clock
        Target Stop h3 p p' hp hlive hpFloor T K q0

/-! ## Uniform `27/64` live-band clock floor -/

noncomputable def phase1ClockP : NNReal := 27 / 64
noncomputable def phase1ClockP' : NNReal := 37 / 64

theorem phase1ClockP_add_complement :
    (phase1ClockP : ℝ≥0∞) + (phase1ClockP' : ℝ≥0∞) = 1 := by
  rw [← ENNReal.coe_add, ← ENNReal.coe_one]
  congr 1
  apply NNReal.eq
  norm_num [phase1ClockP, phase1ClockP',
    NNReal.coe_add, NNReal.coe_div]

theorem phase1ProductiveMass_ge_clockP
    (h3 : 3 ≤ n) (q : Phase1Level n B z)
    (rEff : RelaxedRate)
    {xPred mPred : ℕ}
    (hxPred : State.x q.1 = xPred + 1)
    (hmPred : State.y q.1 + State.z q.1 = mPred + 1)
    (hrate : IsPaperEffectiveRate rEff q.1)
    (hfire : (3 / 4 : NNReal) ≤ rEff.fire)
    (hxLo : n < 2 * State.x q.1)
    (hxHi : 4 * State.x q.1 < 3 * n) :
    (phase1ClockP : ℝ≥0∞) ≤ phase1ProductiveMass h3 q := by
  have hpop : xPred + mPred + 2 = n := by
    have ht := State.total q.1
    omega
  have hxmReal :
      (3 : ℝ) * (n : ℝ) ^ 2 ≤
        16 * (xPred + 1 : ℝ) * (mPred + 1 : ℝ) := by
    have hsum :
        (xPred + 1 : ℝ) + (mPred + 1 : ℝ) = (n : ℝ) := by
      -- `hpop : xPred + mPred + 2 = n`; reassociate in ℕ before casting.
      have hpop' : xPred + 1 + (mPred + 1) = n := by omega
      exact_mod_cast hpop'
    have hlo : (n : ℝ) < 2 * (xPred + 1 : ℝ) := by
      exact_mod_cast (by simpa [hxPred] using hxLo)
    have hhi : 4 * (xPred + 1 : ℝ) < 3 * (n : ℝ) := by
      exact_mod_cast (by simpa [hxPred] using hxHi)
    have h1 : 0 ≤ 4 * (xPred + 1 : ℝ) - (n : ℝ) := by
      linarith
    have h2 : 0 ≤ 3 * (n : ℝ) - 4 * (xPred + 1 : ℝ) := by
      linarith
    nlinarith [mul_nonneg h1 h2]
  have hxmNat :
      3 * n * n ≤ 16 * (xPred + 1) * (mPred + 1) := by
    -- `hxmReal` is phrased with `n ^ 2`; normalise the power first.
    have hxmReal' :
        (3 : ℝ) * (n : ℝ) * (n : ℝ) ≤
          16 * (xPred + 1 : ℝ) * (mPred + 1 : ℝ) := by
      have := hxmReal; nlinarith [this]
    exact_mod_cast hxmReal'
  have hordinary :
      ((9 / 16 : NNReal) : ℝ≥0∞) ≤
        triStep (xPred + 1) (mPred + 1) (by omega) xPred +
          triStep (xPred + 1) (mPred + 1) (by omega)
            (xPred + 2) := by
    rw [productive_mass_closed xPred mPred n h3 hpop]
    have hpred : xPred + mPred + 1 ≤ n := by omega
    have hcross :
        9 * (n * (xPred + mPred + 1)) ≤
          (3 * ((xPred + 1) * (mPred + 1))) * 16 := by
      nlinarith [Nat.mul_le_mul_left n hpred]
    have hnum :
        (((9 / 16 : NNReal) : ℝ≥0∞) *
          ((n * (xPred + mPred + 1) : ℕ) : ℝ≥0∞)) ≤
          ((3 * ((xPred + 1) * (mPred + 1)) : ℕ) : ℝ≥0∞) := by
      -- Keep the division intact: `ENNReal.div_le_iff` turns `9/16 * D ≤ N`
      -- into the cross-multiplied natural inequality directly, whereas
      -- unfolding to `mul_inv` first leaves a shape `div_le_of_le_mul` cannot see.
      rw [ENNReal.coe_div (by norm_num : (16 : NNReal) ≠ 0)]
      -- reshape `9/16 * D` into `(9 * D)/16` by hand: ENNReal is not a
      -- DivisionRing, so div_mul_eq_mul_div does not apply.
      rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv,
        ENNReal.div_le_iff (by simp) (by simp)]
      exact_mod_cast hcross
    have hden0 :
        ((n * (xPred + mPred + 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero, Nat.mul_eq_zero]
      omega
    have hdenTop :
        ((n * (xPred + mPred + 1) : ℕ) : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.natCast_ne_top _
    exact (ENNReal.le_div_iff_mul_le
      (Or.inl hden0) (Or.inl hdenTop)).2 hnum
  have hfireE :
      (((3 / 4 : NNReal) : ℝ≥0∞)) ≤ (rEff.fire : ℝ≥0∞) := by
    exact_mod_cast hfire
  have hrelaxed :=
    relaxed_productive_mass_ge_fire_mul
      rEff xPred mPred (by omega)
  have hnumNN :
      (phase1ClockP : NNReal) =
        (3 / 4 : NNReal) * (9 / 16 : NNReal) := by
    apply NNReal.eq
    norm_num [phase1ClockP, NNReal.coe_mul, NNReal.coe_div]
  have hnumE :
      (phase1ClockP : ℝ≥0∞) =
        ((3 / 4 : NNReal) : ℝ≥0∞) *
          ((9 / 16 : NNReal) : ℝ≥0∞) := by
    exact_mod_cast hnumNN
  rw [hnumE]
  calc
    ((3 / 4 : NNReal) : ℝ≥0∞) *
          ((9 / 16 : NNReal) : ℝ≥0∞) ≤
        (rEff.fire : ℝ≥0∞) *
          (triStep (xPred + 1) (mPred + 1) (by omega) xPred +
            triStep (xPred + 1) (mPred + 1) (by omega)
              (xPred + 2)) :=
      mul_le_mul hfireE hordinary bot_le bot_le
    _ ≤ relaxedTriStep rEff (xPred + 1) (mPred + 1) (by omega) xPred +
          relaxedTriStep rEff (xPred + 1) (mPred + 1) (by omega)
            (xPred + 2) := hrelaxed
    _ = phase1ProductiveMass h3 q :=
      (phase1ProductiveMass_eq_relaxed
        h3 q rEff hxPred hmPred hrate).symm

/-! ## Explicit `40n` raw clock -/

theorem phase1ClockError_40n_5n_le
    (n : ℕ) :
    ((phase1ClockP' : ℝ≥0∞) +
          (phase1ClockP : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2)) ^ (40 * n) *
        (2 : ℝ≥0∞) ^ (5 * n) ≤
      ((1 : ℝ≥0∞) / 2) ^ n := by
  have hfactorNN :
      phase1ClockP' + phase1ClockP * (1 / 2 : NNReal) ≤
        (4 / 5 : NNReal) := by
    rw [← NNReal.coe_le_coe]
    norm_num [phase1ClockP, phase1ClockP',
      NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div]
  have hfactorE :
      (phase1ClockP' : ℝ≥0∞) +
          (phase1ClockP : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2) ≤
        ((4 / 5 : NNReal) : ℝ≥0∞) := by
    -- `exact_mod_cast` will not push the coercion through the literal division;
    -- do it explicitly.
    have h := hfactorNN
    rw [← ENNReal.coe_le_coe] at h
    -- distribute the coercion over the sum and product before matching
    push_cast at h
    exact h
  have hblockNN :
      (4 / 5 : NNReal) ^ 8 * 2 ≤ (1 / 2 : NNReal) := by
    rw [← NNReal.coe_le_coe]
    norm_num [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div]
  have hblockE :
      ((4 / 5 : NNReal) : ℝ≥0∞) ^ 8 * 2 ≤
        ((1 / 2 : NNReal) : ℝ≥0∞) := by
    exact_mod_cast hblockNN
  have hhalfE :
      (((1 / 2 : NNReal) : ℝ≥0∞)) =
        ((1 : ℝ≥0∞) / 2) := by
    rw [ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0)]
    norm_num
  calc
    ((phase1ClockP' : ℝ≥0∞) +
          (phase1ClockP : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2)) ^ (40 * n) *
        (2 : ℝ≥0∞) ^ (5 * n) =
      ((((phase1ClockP' : ℝ≥0∞) +
          (phase1ClockP : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2)) ^ 8) * 2) ^
        (5 * n) := by
      rw [show 40 * n = 8 * (5 * n) by ring, pow_mul, ← mul_pow]
    _ ≤ ((((4 / 5 : NNReal) : ℝ≥0∞) ^ 8) * 2) ^ (5 * n) := by
      gcongr
    _ ≤ (((1 / 2 : NNReal) : ℝ≥0∞)) ^ (5 * n) := by
      gcongr
    _ ≤ (((1 / 2 : NNReal) : ℝ≥0∞)) ^ n := by
      apply pow_le_pow_right_of_le_one'
      · exact_mod_cast (by
          rw [div_le_one]
          · norm_num
          · norm_num : (1 / 2 : NNReal) ≤ 1)
      · omega
    _ = ((1 : ℝ≥0∞) / 2) ^ n := by
      rw [hhalfE]

theorem phase1ReferenceStep_failure_le_productive_add_clock_40n
    (Target Stop : Phase1Level n B z → Prop)
    [DecidablePred Target] [DecidablePred Stop]
    (h3 : 3 ≤ n)
    (hlive : ∀ q, ¬ Stop q →
      0 < State.x q.1 ∧ 0 < State.y q.1)
    (hpFloor : ∀ q, ¬ Stop q →
      (phase1ClockP : ℝ≥0∞) ≤ phase1ProductiveMass h3 q)
    (q0 : Phase1Level n B z) :
    terminalFailureMass
        (iter (freeze Target (phase1ReferenceStep h3)) (40 * n) q0)
        Target ≤
      terminalFailureMass
          (iter (freeze Stop (phase1ProductiveReferenceStep h3))
            (5 * n) q0)
          Target +
        ((1 : ℝ≥0∞) / 2) ^ n := by
  exact
    (phase1ReferenceStep_failure_le_productive_add_clock
      Target Stop h3
      (phase1ClockP : ℝ≥0∞) (phase1ClockP' : ℝ≥0∞)
      phase1ClockP_add_complement
      hlive hpFloor (40 * n) (5 * n) q0).trans
      (add_le_add le_rfl (phase1ClockError_40n_5n_le n))

end

end Tri.Byzantine
