-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockMainProcess.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainTerminal
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMainAlgebra

/-!
# The concrete killed Main-credit process

The process is defined first on a finite pair-log pfx.  Consequently its value at
raw time `t` is literally a function of `frestrictLe t`; adaptation does not require a
separate recursion theorem through full paths.

The state machine has five modes.

* `dormant`: no admissible first Phase-3 seed has yet been observed;
* `waiting`: an admissible seed has been recorded, but the level
  `256 * (h + 1)` front is still zero;
* `live`: age, Main credit, front count, and discounted potential are stored;
* `stopped`: a credit/front/time barrier was accepted and its endpoint retained;
* `killed`: a sampled step failed a current-pfx guard.  Its value is
  `min (q⁻¹ y, y)`, written without `min` to expose its two drift cases.

Every `waiting` or `live` payload carries its current virtual labelling and the exact
local invariants used by the next step.  A failed candidate is killed before its
Main-credit atom is installed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainProcess

open TimeTheorem PairLog PairLogAuxiliary StageEventSpec TraceDrain
  PhaseThreeClockVirtual PhaseThreeClockCore PhaseThreeClockGatedLaw
  PhaseThreeClockGatedLevelOne PhaseThreeClockEmbeddingBridge
  PhaseThreeClockMainLedger PhaseThreeClockMainPath
  PhaseThreeClockMainAlgebra PhaseThreeClockMainTerminal
open PhaseThreeModel.Numeric

variable {n : ℕ} (init : InputCfg n)

/-! ## Seed data and scalar definitions -/

/-- The information frozen when the first exact Phase-3 state is accepted. -/
structure MainSeedData where
  time : ℕ
  labels : Lab init
  cfg : InputCfg n

/-- Prefix-checkable seed data used by the global process.

The density fields are deliberately stored.  Later, the guarded-path bridge should
construct this predicate from `SeedProfile`, `timePopulationThreshold ≤ n`, and
`labelCfg labels = cfg`.  Keeping them in the payload makes every later scalar bound
local and prevents the process from relying on a future `AsyncEntry` proof. -/
structure MainSeedAdmissible (data : MainSeedData init) : Prop where
  cfg_eq : labelCfg data.labels = data.cfg
  profile : SeedProfile n init data.cfg
  card_eq : init.card = n
  main_lower : 12 * n ≤ 25 * timeMainCount data.cfg
  main_upper : 25 * timeMainCount data.cfg ≤ 13 * n
  clock_lower : 6 * n ≤ 25 * StageEventSpec.clockCount data.cfg
  clock_upper : 25 * StageEventSpec.clockCount data.cfg ≤ 7 * n
  clock_large : 2000 ≤ StageEventSpec.clockCount data.cfg

abbrev MainSeed := {data : MainSeedData init // MainSeedAdmissible init data}

def mainSeedM (seed : MainSeed init) : ℕ := timeMainCount seed.1.cfg

def mainSeedC (seed : MainSeed init) : ℕ := StageEventSpec.clockCount seed.1.cfg

def mainLevel (h : ℕ) : ℕ := 256 * (h + 1)

def mainPairDenominator (n : ℕ) : ℝ :=
  (n : ℝ) * ((n : ℝ) - 1)

/-- `κ = 4 b_* M/P`, with `b_* = 3/2500`. -/
def mainKappa (seed : MainSeed init) : ℝ :=
  12 * (mainSeedM init seed : ℝ) /
    (2500 * mainPairDenominator n)

def mainQ (seed : MainSeed init) : ℝ := 1 + mainKappa init seed

def mainDiscount (seed : MainSeed init) (age : ℕ) : ℝ :=
  (mainQ init seed)⁻¹ ^ age

def mainPotential (seed : MainSeed init) (credit front : ℕ) : ℝ :=
  (credit : ℝ) / (mainSeedM init seed : ℝ) -
    (11 / 10 : ℝ) * ((front : ℝ) / (mainSeedC init seed : ℝ))

def mainLiveValue (seed : MainSeed init) (age credit front : ℕ) : ℝ :=
  mainDiscount init seed age * mainPotential init seed credit front

/-! ## Current-state guards -/

/-- The zero-ledger state between the seed and the first high Clock. -/
structure MainWaitingCondition (h : ℕ) (seed : MainSeed init)
    (lab : Lab init) : Prop where
  environment : ClockEnvironment lab
  roles : ∀ i, (lab i).role = (seed.1.labels i).role
  front_zero : PhaseThreeClockGatedLaw.frontCount lab (mainLevel h) = 0
  vertical_zero : vSum init h lab = 0
  hour_zero : hSum init h lab = 0

/-- The pfx invariants installed after an accepted sampled step. -/
structure MainAcceptedCondition (h : ℕ) (seed : MainSeed init)
    (lab : Lab init) (credit front : ℕ) : Prop where
  environment : ClockEnvironment lab
  roles : ∀ i, (lab i).role = (seed.1.labels i).role
  front_eq : PhaseThreeClockGatedLaw.frontCount lab (mainLevel h) = front
  vertical_le : vSum init h lab ≤ 2 * credit
  hour_le : hSum init h lab ≤ credit

/-- Strict interior of the stopped window. -/
structure MainLiveCondition (h : ℕ) (seed : MainSeed init)
    (lab : Lab init) (age credit front : ℕ) (value : ℝ) : Prop where
  accepted : MainAcceptedCondition init h seed lab credit front
  credit_small : 2500 * credit < 3 * mainSeedM init seed
  front_small : front < smallThreshold (mainSeedC init seed)
  age_small : age < logWindow n 30
  value_eq : value = mainLiveValue init seed age credit front

/-- The waiting-to-live gate.  `front_one` is needed globally for the `10/n`
increment bound; on the guarded path it follows from unit front increments. -/
structure MainStartCondition (h : ℕ) (seed : MainSeed init)
    (lab : Lab init) (front : ℕ) (value : ℝ) : Prop where
  front_one : front = 1
  live : MainLiveCondition init h seed lab 0 0 front value

/-! ## State space -/

structure MainWaiting (h : ℕ) where
  seed : MainSeed init
  lab : Lab init
  valid : MainWaitingCondition init h seed lab

structure MainLive (h : ℕ) where
  seed : MainSeed init
  lab : Lab init
  age : ℕ
  credit : ℕ
  front : ℕ
  value : ℝ
  valid : MainLiveCondition init h seed lab age credit front value

inductive MainProcessFlag
  | dormant
  | waiting
  | live
  | stopped
  | killed

deriving DecidableEq

inductive MainProcessState (h : ℕ)
  | dormant
  | waiting (data : MainWaiting init h)
  | live (data : MainLive init h)
  | stopped (value : ℝ)
  | killed (value : ℝ)

def mainStateFlag {init : InputCfg n} {h : ℕ} : MainProcessState init h → MainProcessFlag
  | .dormant => .dormant
  | .waiting _ => .waiting
  | .live _ => .live
  | .stopped _ => .stopped
  | .killed _ => .killed

def mainStateValue {init : InputCfg n} {h : ℕ} : MainProcessState init h → ℝ
  | .dormant => 0
  | .waiting _ => 0
  | .live data => data.value
  | .stopped value => value
  | .killed value => value

def MainStateLabAgrees {h : ℕ} (state : MainProcessState init h)
    (lab : Lab init) : Prop :=
  match state with
  | .waiting data => data.lab = lab
  | .live data => data.lab = lab
  | _ => True

/-! ## One-step atoms -/

/-- Some agent is in exact Phase 3 in the current physical configuration. -/
def HasExactPhaseThree (cfg : InputCfg n) : Prop :=
  ∃ agent ∈ cfg, agent.phase.val = 3

/-- `contact + 2 * deep-cancellation` for the sampled ordered pair. -/
def mainPairCredit (h : ℕ) (lab : Lab init) :
    Option (Fin init.card × Fin init.card) → ℕ
  | none => 0
  | some (i, j) =>
      contactInd h (lab i) (lab j) + 2 * deepCancelInd h (lab i) (lab j)

open Classical in
/-- The level-`256(h+1)` gated front increment of the sampled pair. -/
def mainPairRaising (h : ℕ) (lab : Lab init) :
    Option (Fin init.card × Fin init.card) → ℕ
  | none => 0
  | some (i, j) =>
      if GatedTick (mainLevel h) lab i j then 1 else 0

open Classical in
/-- Rejected sampled steps are killed before their candidate credit is installed.
At the current discount scale this is `min (q⁻¹ y, y)`. -/
def mainKillValue (seed : MainSeed init) (value : ℝ) : ℝ :=
  if 0 ≤ value then (mainQ init seed)⁻¹ * value else value

/-- The three accepted endpoint barriers. -/
def mainStop (seed : MainSeed init) (age credit front : ℕ) : Prop :=
  3 * mainSeedM init seed ≤ 2500 * credit ∨
    smallThreshold (mainSeedC init seed) ≤ front ∨
    logWindow n 30 ≤ age

/-! ## Candidate fields of a live step -/

def mainNextCredit {h : ℕ} (data : MainLive init h)
    (draw : Option (Fin init.card × Fin init.card)) : ℕ :=
  data.credit + mainPairCredit init h data.lab draw

def mainNextFront {h : ℕ} (data : MainLive init h)
    (draw : Option (Fin init.card × Fin init.card)) : ℕ :=
  data.front + mainPairRaising init h data.lab draw

def mainNextAge {h : ℕ} (data : MainLive init h) : ℕ := data.age + 1

def mainNextValue {h : ℕ} (data : MainLive init h)
    (draw : Option (Fin init.card × Fin init.card)) : ℝ :=
  mainLiveValue init data.seed (mainNextAge init data)
    (mainNextCredit init data draw) (mainNextFront init data draw)

def mainWaitingFront (h : ℕ) (lab : Lab init) : ℕ :=
  PhaseThreeClockGatedLaw.frontCount lab (mainLevel h)

def mainStartValue (seed : MainSeed init) (front : ℕ) : ℝ :=
  mainLiveValue init seed 0 0 front

/-! ## State transitions -/

open Classical in
/-- Inspect a candidate first exact-Phase-3 state.  A malformed seed is terminally
killed at value zero; a non-seed state remains dormant. -/
def mainMakeSeedState (h time : ℕ) (lab : Lab init) (cfg : InputCfg n) :
    MainProcessState init h :=
  if HasExactPhaseThree cfg then
    let raw : MainSeedData init := { time := time, labels := lab, cfg := cfg }
    if admissible : MainSeedAdmissible init raw then
      let seed : MainSeed init := ⟨raw, admissible⟩
      if waiting : MainWaitingCondition init h seed lab then
        .waiting { seed := seed, lab := lab, valid := waiting }
      else .killed 0
    else .killed 0
  else .dormant

open Classical in
/-- Waiting either stays at the zero front, enters live at the unit first hit, or
kills at zero. -/
def mainWaitingStep (h : ℕ) (data : MainWaiting init h) (nextLab : Lab init) :
    MainProcessState init h :=
  let front := mainWaitingFront init h nextLab
  if front = 0 then
    if waiting : MainWaitingCondition init h data.seed nextLab then
      .waiting { seed := data.seed, lab := nextLab, valid := waiting }
    else .killed 0
  else
    let value := mainStartValue init data.seed front
    if start : MainStartCondition init h data.seed nextLab front value then
      .live
        { seed := data.seed
          lab := nextLab
          age := 0
          credit := 0
          front := front
          value := value
          valid := start.live }
    else .killed 0

open Classical in
/-- Accepted candidates install their credit/front atom and retain a stopping
endpoint.  Rejected candidates are killed from the old value, before installing the
candidate atom. -/
def mainLiveStep (h : ℕ) (data : MainLive init h)
    (draw : Option (Fin init.card × Fin init.card)) (nextLab : Lab init) :
    MainProcessState init h :=
  let age := mainNextAge init data
  let credit := mainNextCredit init data draw
  let front := mainNextFront init data draw
  let value := mainNextValue init data draw
  if accepted : MainAcceptedCondition init h data.seed nextLab credit front then
    if hstop : mainStop init data.seed age credit front then .stopped value
    else
      .live
        { seed := data.seed
          lab := nextLab
          age := age
          credit := credit
          front := front
          value := value
          valid :=
            { accepted := accepted
              credit_small := by
                have hnot : ¬ 3 * mainSeedM init data.seed ≤ 2500 * credit := by
                  intro hbad
                  apply ‹¬ mainStop init data.seed age credit front›
                  exact Or.inl hbad
                omega
              front_small := by
                have hnot : ¬ smallThreshold (mainSeedC init data.seed) ≤ front := by
                  intro hbad
                  apply ‹¬ mainStop init data.seed age credit front›
                  exact Or.inr (Or.inl hbad)
                omega
              age_small := by
                have hnot : ¬ logWindow n 30 ≤ age := by
                  intro hbad
                  apply ‹¬ mainStop init data.seed age credit front›
                  exact Or.inr (Or.inr hbad)
                omega
              value_eq := rfl } }
  else .killed (mainKillValue init data.seed data.value)

/-- The global raw-time transition. -/
def mainProcessStep (h nextTime : ℕ) (state : MainProcessState init h)
    (draw : Option (Fin init.card × Fin init.card))
    (nextLab : Lab init) (nextCfg : InputCfg n) : MainProcessState init h :=
  match state with
  | .dormant => mainMakeSeedState init h nextTime nextLab nextCfg
  | .waiting data => mainWaitingStep init h data nextLab
  | .live data => mainLiveStep init h data draw nextLab
  | .stopped value => .stopped value
  | .killed value => .killed value

/-! ## Finite-pfx recursion -/

abbrev MainDraw := Draw (hourIndex n) 256

def mainPrefixRestrict {t : ℕ}
    (pfx : (k : Finset.Iic (t + 1)) → MainDraw (n := n)) :
    (k : Finset.Iic t) → MainDraw (n := n) :=
  restrictPrefix (Nat.le_succ t) pfx

/-- The selected physical labels at the last coordinate of a finite pfx. -/
def mainPrefixDraw (t : ℕ)
    (pfx : (k : Finset.Iic (t + 1)) → MainDraw (n := n)) :
    Option (Fin init.card × Fin init.card) :=
  selectLabels (prefixLabels init t (mainPrefixRestrict pfx))
    (pfx ⟨t + 1, Finset.mem_Iic.mpr le_rfl⟩)

open Classical in
/-- The complete state after reading exactly the pfx through time `t`. -/
def mainPrefixState (h : ℕ) :
    (t : ℕ) → ((k : Finset.Iic t) → MainDraw (n := n)) → MainProcessState init h
  | 0, pfx =>
      mainMakeSeedState init h 0
        (auxPrefix init virtualRule 0 pfx) (prefixCfg init 0 pfx)
  | t + 1, pfx =>
      mainProcessStep init h (t + 1)
        (mainPrefixState h t (mainPrefixRestrict pfx))
        (mainPrefixDraw init t pfx)
        (auxPrefix init virtualRule (t + 1) pfx)
        (prefixCfg init (t + 1) pfx)

/-- The state and real process on a full recorded path. -/
def mainProcessState (h t : ℕ) (ω : InputLog n) : MainProcessState init h :=
  mainPrefixState init h t (frestrictLe t ω)

def mainProcessY (h t : ℕ) (ω : InputLog n) : ℝ :=
  mainStateValue (mainProcessState init h t ω)

/-! ## Exact transition observations -/

theorem mainMakeSeedState_value_zero (h time : ℕ) (lab : Lab init)
    (cfg : InputCfg n) :
    mainStateValue (mainMakeSeedState init h time lab cfg) = 0 := by
  classical
  dsimp only [mainMakeSeedState]
  split_ifs <;> rfl

/-- A waiting transition either has value zero or is exactly its certified unit-front
start value. -/
theorem mainWaitingStep_value_cases (h : ℕ) (data : MainWaiting init h)
    (nextLab : Lab init) :
    mainStateValue (mainWaitingStep init h data nextLab) = 0 ∨
      ∃ start : MainStartCondition init h data.seed nextLab
          (mainWaitingFront init h nextLab)
          (mainStartValue init data.seed (mainWaitingFront init h nextLab)),
        mainStateValue (mainWaitingStep init h data nextLab) =
          mainStartValue init data.seed (mainWaitingFront init h nextLab) := by
  classical
  dsimp only [mainWaitingStep]
  split_ifs <;> simp_all [mainStateValue]

/-- A live transition stores either the accepted candidate value or the corrected
killed value. -/
theorem mainLiveStep_value_cases (h : ℕ) (data : MainLive init h)
    (draw : Option (Fin init.card × Fin init.card)) (nextLab : Lab init) :
    mainStateValue (mainLiveStep init h data draw nextLab) =
        mainNextValue init data draw ∨
      mainStateValue (mainLiveStep init h data draw nextLab) =
        mainKillValue init data.seed data.value := by
  classical
  dsimp only [mainLiveStep]
  split_ifs <;> simp_all [mainStateValue]

/-! ## The stored labelling is the current pfx labelling -/

theorem mainMakeSeedState_lab (h time : ℕ) (lab : Lab init) (cfg : InputCfg n) :
    MainStateLabAgrees init (mainMakeSeedState init h time lab cfg) lab := by
  classical
  dsimp only [mainMakeSeedState]
  split_ifs <;> simp_all [MainStateLabAgrees]

theorem mainWaitingStep_lab (h : ℕ) (data : MainWaiting init h)
    (nextLab : Lab init) :
    MainStateLabAgrees init (mainWaitingStep init h data nextLab) nextLab := by
  classical
  dsimp only [mainWaitingStep]
  split_ifs <;> simp_all [MainStateLabAgrees]

theorem mainLiveStep_lab (h : ℕ) (data : MainLive init h)
    (draw : Option (Fin init.card × Fin init.card)) (nextLab : Lab init) :
    MainStateLabAgrees init (mainLiveStep init h data draw nextLab) nextLab := by
  classical
  dsimp only [mainLiveStep]
  split_ifs <;> simp_all [MainStateLabAgrees]

theorem mainProcessStep_lab (h nextTime : ℕ) (state : MainProcessState init h)
    (draw : Option (Fin init.card × Fin init.card))
    (nextLab : Lab init) (nextCfg : InputCfg n) :
    MainStateLabAgrees init
      (mainProcessStep init h nextTime state draw nextLab nextCfg) nextLab := by
  cases state with
  | dormant =>
      simpa only [mainProcessStep] using
        mainMakeSeedState_lab init h nextTime nextLab nextCfg
  | waiting data =>
      simpa only [mainProcessStep] using mainWaitingStep_lab init h data nextLab
  | live data =>
      simpa only [mainProcessStep] using mainLiveStep_lab init h data draw nextLab
  | stopped value => simp [mainProcessStep, MainStateLabAgrees]
  | killed value => simp [mainProcessStep, MainStateLabAgrees]

theorem mainPrefixState_lab (h t : ℕ)
    (pfx : (k : Finset.Iic t) → MainDraw (n := n)) :
    MainStateLabAgrees init (mainPrefixState init h t pfx)
      (auxPrefix init virtualRule t pfx) := by
  cases t with
  | zero =>
      simpa only [mainPrefixState] using
        mainMakeSeedState_lab init h 0
          (auxPrefix init virtualRule 0 pfx) (prefixCfg init 0 pfx)
  | succ t =>
      simp only [mainPrefixState]
      exact mainProcessStep_lab init h (t + 1)
        (mainPrefixState init h t (mainPrefixRestrict pfx))
        (mainPrefixDraw init t pfx)
        (auxPrefix init virtualRule (t + 1) pfx)
        (prefixCfg init (t + 1) pfx)

theorem mainProcessState_lab (h t : ℕ) (ω : InputLog n) :
    MainStateLabAgrees init (mainProcessState init h t ω)
      (virtualLabels init ω t) := by
  change MainStateLabAgrees init
    (mainPrefixState init h t (frestrictLe t ω))
    (auxPrefix init virtualRule t (frestrictLe t ω))
  exact mainPrefixState_lab init h t (frestrictLe t ω)

/-! ## Adaptedness -/

/-- Item 1: the concrete process is adapted to the original, unshifted pair-log
filtration. -/
theorem mainProcessY_adapted (h t : ℕ) :
    StronglyMeasurable[pairLogFiltration (hourIndex n) 256 t]
      (mainProcessY init h t) := by
  have hprefix : Measurable
      (fun pfx : (k : Finset.Iic t) → MainDraw (n := n) =>
        mainStateValue (mainPrefixState init h t pfx)) :=
    measurable_of_countable _
  exact (hprefix.comp
    (measurable_pairLog_prefix (hourIndex n) 256 t)).stronglyMeasurable

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockMainProcess

end
