-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSamplingCompletion.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateCompletionDeathTail
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase5Convergence
import Ripple.PopulationProtocol.ExactMajority.Probability.LateF6OriginalLaw
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingSplice
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingServiceProbability

/-!
# N18 row 3: actual Phase-5 sampling completion

The process starts at the genuine first homogeneous Phase-5 state.  Its gate
requires the actual trace to remain homogeneous Phase 5 and to retain the
`296/3125 n` useful-Main floor.  A gate failure kills the debt; hence the law
statement is a joint prefix event and never conditions on future timer survival.

Both ordered-pair orientations are proved.  Sixteen work units then give the
exact exponent `-6347/3125`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder Set
open scoped ENNReal MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.LateSamplingCompletion

open TimeTheorem PairLog TraceDrain PhaseOneDrain PhaseOneDrainStopping
open AveragingRecordedExpectation AveragingServiceProbability
open AveragingStoppedDebt
open ReserveSampling Phase5Convergence
open LateCompletionDeathTail LateSamplingSplice

variable {L K n : ℕ}

/-- Number of currently useful sampling partners. -/
def usefulMainCount (c : Cfg L K) : ℕ :=
  c.countP (fun a => biasedMainLtL a)

/-- Rational form of the number of unset Reserves. -/
def completionDebt (c : Cfg L K) : ℚ :=
  (unsampledReserveU c : ℚ)

/-- Exact current-state gate for the sixteen-work-unit death process. -/
structure CompletionGate (n : ℕ) (c : Cfg L K) : Prop where
  population : c.card = n
  phase_five : ∀ a ∈ c, a.phase.val = 5
  useful_floor : 296 * n ≤ 3125 * usefulMainCount c

theorem CompletionGate.phase5AllWin
    {c : Cfg L K} (h : CompletionGate n c) : Phase5AllWin n c :=
  ⟨h.population, h.phase_five⟩

theorem completionDebt_ceil (c : Cfg L K) :
    Nat.ceil (completionDebt c - 0) = unsampledReserveU c := by
  simp only [completionDebt, sub_zero, Nat.ceil_natCast]

/-- Reverse ordered-pair version of the compiled Phase-5 strict drop. -/
theorem Phase5Transition_unsampled_pair_drop_reverse
    (m r : AgentState L K)
    (hm : biasedMainLtL m) (hr : unsampled r) :
    Multiset.countP (fun a => unsampled a)
        ({(Phase5Transition L K m r).1, (Phase5Transition L K m r).2}
          : Multiset (AgentState L K)) + 1
      ≤ Multiset.countP (fun a => unsampled a)
          ({m, r} : Multiset (AgentState L K)) := by
  classical
  obtain ⟨hmrole, σ, i, hiL, hmb⟩ := hm
  obtain ⟨hrrole, hrhour⟩ := hr
  have hm_not : ¬ unsampled m := by
    intro hu
    rw [hu.1] at hmrole
    exact absurd hmrole (by decide)
  have hrhs :
      Multiset.countP (fun a => unsampled a)
        ({m, r} : Multiset (AgentState L K)) = 1 := by
    rw [countP_unsampled_pair, if_neg hm_not,
      if_pos ⟨hrrole, hrhour⟩]
  have hbias_ne : m.bias ≠ Bias.zero := by
    rw [hmb]
    exact fun h => by simp at h
  have hforward :
      ¬ (m.role = Role.reserve ∧ r.role = Role.main ∧ r.bias ≠ Bias.zero) := by
    intro h
    rw [hmrole] at h
    exact absurd h.1 (by decide)
  have hreverse :
      r.role = Role.reserve ∧ m.role = Role.main ∧ m.bias ≠ Bias.zero :=
    ⟨hrrole, hmrole, hbias_ne⟩
  have hm_not_clock : ¬ m.role = Role.clock := by
    rw [hmrole]
    decide
  have hr_not_clock :
      ¬ ({r with hour := exponentOf L m.bias} : AgentState L K).role =
        Role.clock := by
    show r.role ≠ Role.clock
    rw [hrrole]
    decide
  have hfire :
      Phase5Transition L K m r =
        (m, {r with hour := exponentOf L m.bias}) := by
    unfold Phase5Transition
    simp only [if_neg hforward, if_pos hreverse, if_pos hrhour]
    rw [if_neg hm_not_clock, if_neg hr_not_clock]
  have hexp : exponentOf L m.bias = i := by
    rw [hmb]
    rfl
  have hout_not :
      ¬ unsampled ({r with hour := exponentOf L m.bias} : AgentState L K) := by
    intro hu
    have heq : (exponentOf L m.bias).val = L := hu.2
    rw [hexp] at heq
    omega
  rw [hfire, countP_unsampled_pair, if_neg hm_not,
    if_neg hout_not, hrhs]

/-- Config-level reverse-orientation strict drop. -/
theorem unsampledReserveU_stepOrSelf_drop_reverse
    (n : ℕ) (c : Cfg L K) (m r : AgentState L K)
    (hwin : Phase5AllWin n c)
    (happ : Protocol.Applicable c m r)
    (hm : biasedMainLtL m) (hr : unsampled r) :
    unsampledReserveU
        (Protocol.stepOrSelf (NonuniformMajority L K) c m r) + 1
      ≤ unsampledReserveU c := by
  have hmmem : m ∈ c := Multiset.mem_of_le happ (by simp)
  have hrmem : r ∈ c := Multiset.mem_of_le happ (by simp)
  have hmfive : m.phase.val = 5 := hwin.2 m hmmem
  have hrfive : r.phase.val = 5 := hwin.2 r hrmem
  have hsub : ({m, r} : Multiset (AgentState L K)) ≤ c := happ
  have hstep :
      Protocol.stepOrSelf (NonuniformMajority L K) c m r =
        c - {m, r} + {(Transition L K m r).1, (Transition L K m r).2} := by
    unfold Protocol.stepOrSelf
    rw [if_pos happ]
    rfl
  unfold unsampledReserveU
  rw [hstep, Multiset.countP_add, Multiset.countP_sub hsub]
  rw [Transition_eq_Phase5Transition_of_phase5
    (L := L) (K := K) m r hmfive hrfive]
  have hdrop := Phase5Transition_unsampled_pair_drop_reverse
    (L := L) (K := K) m r hm hr
  have hpair_le :
      Multiset.countP (fun a => unsampled a)
          ({m, r} : Multiset (AgentState L K)) ≤
        Multiset.countP (fun a => unsampled a) c :=
    Multiset.countP_le_of_le _ hsub
  omega

/-- Strict drop for either scheduler orientation. -/
theorem unsampledReserveU_stepOrSelf_drop_both
    (n : ℕ) (c : Cfg L K) (s t : AgentState L K)
    (hwin : Phase5AllWin n c)
    (happ : Protocol.Applicable c s t)
    (hpair : (unsampled s ∧ biasedMainLtL t) ∨
      (biasedMainLtL s ∧ unsampled t)) :
    unsampledReserveU
        (Protocol.stepOrSelf (NonuniformMajority L K) c s t) + 1
      ≤ unsampledReserveU c := by
  rcases hpair with hforward | hreverse
  · exact unsampledReserveU_stepOrSelf_drop n c hwin s t happ
      hforward.1 hforward.2
  · exact unsampledReserveU_stepOrSelf_drop_reverse n c s t hwin happ
      hreverse.1 hreverse.2

/-- The unset count is nonincreasing while the source configuration is in the
homogeneous Phase-5 gate. -/
theorem completionDebt_draw_le
    (n : ℕ) (c : Cfg L K) (hc : CompletionGate n c)
    (d : Draw L K) :
    completionDebt (applyDraw c d) ≤ completionDebt c := by
  cases d with
  | none => exact le_rfl
  | some pair =>
      change (unsampledReserveU
          (Protocol.stepOrSelf (NonuniformMajority L K) c
            pair.1.1 pair.2.1) : ℚ) ≤
        (unsampledReserveU c : ℚ)
      exact_mod_cast unsampledReserveU_stepOrSelf_le n c
        hc.phase5AllWin pair.1.1 pair.2.1

/-- Per-item death rate obtained from both ordered-pair orientations and the
`296/3125 n` useful-partner floor. -/
def completionDeathRate (n : ℕ) : ℝ :=
  592 / (3125 * (n : ℝ))

theorem completionDeathRate_nonneg (n : ℕ) :
    0 ≤ completionDeathRate n := by
  unfold completionDeathRate
  positivity

theorem completionDeathRate_le_one (hn : 1 ≤ n) :
    completionDeathRate n ≤ 1 := by
  unfold completionDeathRate
  apply (div_le_iff₀ (show (0 : ℝ) < 3125 * n by positivity)).2
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

open Classical in
/-- Actual draw-integral service inequality.  It invokes the compiled strict
pair drop and proves the reverse orientation rather than discarding the factor
of two. -/
theorem completion_service_probability
    (n : ℕ) (hn : 2 ≤ n) (c : Cfg L K)
    (hc : CompletionGate n c) :
    completionDeathRate n *
        (Nat.ceil (completionDebt c - 0) : ℝ) ≤
      ∫ d, (if ¬ CompletionGate n (applyDraw c d) ∨
          completionDebt (applyDraw c d) + 1 ≤ completionDebt c
        then (1 : ℝ) else 0) ∂(drawLaw c).toMeasure := by
  have hrectangle := service_rectangle_real c
    (by rw [hc.population]; exact hn)
    unsampled biasedMainLtL
    (fun c' => ¬ CompletionGate n c' ∨
      completionDebt c' + 1 ≤ completionDebt c)
    (by
      intro a hu hm
      have hm1 := hm.1
      rw [hu.1] at hm1
      exact absurd hm1 (by decide))
    (by
      intro s t happ hpair
      by_cases hnext : CompletionGate n
          (Protocol.stepOrSelf (NonuniformMajority L K) c s t)
      · apply Or.inr
        simp only [completionDebt]
        exact_mod_cast unsampledReserveU_stepOrSelf_drop_both
          n c s t hc.phase5AllWin happ hpair
      · exact Or.inl hnext)
  have huseful :
      (296 : ℝ) * n ≤
        3125 * (c.countP (fun a => biasedMainLtL a) : ℝ) := by
    exact_mod_cast hc.useful_floor
  have hkey :
      (592 : ℝ) * ((n : ℝ) - 1) ≤
        6250 * (c.countP (fun a => biasedMainLtL a) : ℝ) := by
    nlinarith only [huseful]
  have hcross :
      ((592 : ℝ) * (c.countP (fun a => unsampled a) : ℝ)) *
          ((n : ℝ) * ((n : ℝ) - 1)) ≤
        (2 * (c.countP (fun a => unsampled a) : ℝ) *
          (c.countP (fun a => biasedMainLtL a) : ℝ)) *
            (3125 * (n : ℝ)) := by
    calc
      ((592 : ℝ) * (c.countP (fun a => unsampled a) : ℝ)) *
          ((n : ℝ) * ((n : ℝ) - 1)) =
          ((c.countP (fun a => unsampled a) : ℝ) * n) *
            (592 * ((n : ℝ) - 1)) := by ring
      _ ≤ ((c.countP (fun a => unsampled a) : ℝ) * n) *
            (6250 * (c.countP (fun a => biasedMainLtL a) : ℝ)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = (2 * (c.countP (fun a => unsampled a) : ℝ) *
          (c.countP (fun a => biasedMainLtL a) : ℝ)) *
            (3125 * (n : ℝ)) := by ring
  have hleft : (0 : ℝ) < 3125 * n := by positivity
  have hright : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hprob :
      completionDeathRate n *
          (Nat.ceil (completionDebt c - 0) : ℝ) ≤
        (2 * (c.countP (fun a => unsampled a) : ℝ) *
          (c.countP (fun a => biasedMainLtL a) : ℝ)) /
            (c.totalPairs : ℝ) := by
    rw [completionDebt_ceil]
    unfold completionDeathRate unsampledReserveU
    rw [Config.totalPairs, hc.population, Nat.cast_mul,
      Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one,
      div_mul_eq_mul_div]
    exact (div_le_div_iff₀ hleft hright).2 hcross
  refine hprob.trans ?_
  convert hrectangle using 8

/-- Six raw work units would not suffice; the paper's completion row uses
sixteen. -/
def completionHorizon (n : ℕ) : ℕ :=
  logWindow n 16

/-- Genuine first homogeneous Phase-5 state. -/
def allPhaseFive (c : Cfg L K) : Prop :=
  ∀ a ∈ c, a.phase.val = 5

def homogeneousFiveStart (init : Cfg L K) : Ω L K → WithTop ℕ :=
  TraceDrain.exitTime init allPhaseFive

theorem homogeneousFiveStart_isStoppingTime (init : Cfg L K) :
    IsStoppingTime (pairLogFiltration L K) (homogeneousFiveStart init) :=
  TraceDrain.exitTime_isStoppingTime init allPhaseFive

theorem homogeneousFiveStart_past (init : Cfg L K) :
    PairLogPastTime (homogeneousFiveStart init) :=
  exitTime_pairLogPastTime init allPhaseFive

/-- State predicate whose first hit is the actual sampling-completion time. -/
structure SamplingComplete (n : ℕ) (c : Cfg L K) : Prop where
  population : c.card = n
  phase_five : allPhaseFive c
  sampled : ReserveSampled c

def completionTime (init : Cfg L K) (n : ℕ) : Ω L K → WithTop ℕ :=
  TraceDrain.exitTime init (SamplingComplete n)

theorem completionTime_isStoppingTime (init : Cfg L K) (n : ℕ) :
    IsStoppingTime (pairLogFiltration L K) (completionTime init n) :=
  TraceDrain.exitTime_isStoppingTime init (SamplingComplete n)

theorem completionTime_past (init : Cfg L K) (n : ℕ) :
    PairLogPastTime (completionTime init n) :=
  exitTime_pairLogPastTime init (SamplingComplete n)

/-- Local killed-prefix failure from one observed homogeneous-five start. -/
def completionFailureFrom (init : Cfg L K) (s n : ℕ) : Set (Ω L K) :=
  extinctionFailure init s completionDebt 0 (CompletionGate n) n
    (completionHorizon n)

/-- Original-law failure at the genuine homogeneous-five stopping time. -/
def completionFailure (init : Cfg L K) (n : ℕ) : Set (Ω L K) :=
  {ω | ∃ s : ℕ, homogeneousFiveStart init ω = (s : WithTop ℕ) ∧
    ω ∈ completionFailureFrom init s n}

/-- Optional observed-start prefix event.  This is an intersection, not a
conditional law, and therefore costs no union over selected prefix data. -/
abbrev InputRecordedPrefix (n s : ℕ) :=
  RecordedPrefix (PhaseThreeModel.Numeric.hourIndex n) 256 s

def completionFailureWithPrefix (init : InputCfg n)
    (A : (s : ℕ) → Set (InputRecordedPrefix n s)) : Set (InputLog n) :=
  {ω | ∃ s : ℕ, homogeneousFiveStart init ω = (s : WithTop ℕ) ∧
    frestrictLe (π := fun _ : ℕ => Draw
      (PhaseThreeModel.Numeric.hourIndex n) 256) s ω ∈ A s ∧
    ω ∈ completionFailureFrom init s n}

/-- Local recorded-continuation tail before numerical simplification. -/
theorem recorded_completion_tail
    (init : Cfg L K) (s n : ℕ)
    (p : (i : Finset.Iic s) → Draw L K) (hn : 2 ≤ n) :
    recordedFuture init s p (completionFailureFrom init s n) ≤
      ENNReal.ofReal
        ((n : ℝ) * Real.exp
          (-completionDeathRate n * completionHorizon n)) := by
  apply recorded_extinction_tail init s p completionDebt 0
    (CompletionGate n) n (completionDeathRate n)
    (completionDeathRate_nonneg n)
    (completionDeathRate_le_one (by omega))
  · intro c hc d _
    exact completionDebt_draw_le n c hc d
  · exact completion_service_probability n hn

/-- Exact numerical conversion of sixteen work units. -/
theorem completion_sixteen_work_units
    (hn : timePopulationThreshold ≤ n) :
    (n : ℝ) * Real.exp
        (-completionDeathRate n * completionHorizon n) ≤
      Real.rpow (n : ℝ) (-(6347 / 3125 : ℝ)) := by
  obtain ⟨hnpos, hnlog⟩ :=
    ScalarTails.time_population_scalar_bounds hn
  have hceil :
      16 * (n : ℝ) * Real.log (n : ℝ) ≤
        (completionHorizon n : ℝ) := by
    unfold completionHorizon logWindow
    exact Nat.le_ceil _
  have hrate :
      (9472 / 3125 : ℝ) * Real.log (n : ℝ) ≤
        completionDeathRate n * (completionHorizon n : ℝ) := by
    calc
      (9472 / 3125 : ℝ) * Real.log (n : ℝ) =
          completionDeathRate n *
            (16 * (n : ℝ) * Real.log (n : ℝ)) := by
        unfold completionDeathRate
        field_simp [ne_of_gt hnpos]
        ring
      _ ≤ completionDeathRate n * (completionHorizon n : ℝ) :=
        mul_le_mul_of_nonneg_left hceil
          (completionDeathRate_nonneg n)
  have hpow : Real.rpow (n : ℝ) (-(6347 / 3125 : ℝ)) =
      Real.exp (Real.log (n : ℝ) * (-(6347 / 3125 : ℝ))) :=
    Real.rpow_def_of_pos hnpos _
  rw [hpow]
  calc
    (n : ℝ) * Real.exp
        (-completionDeathRate n * completionHorizon n) =
      Real.exp
        (Real.log (n : ℝ) +
          -completionDeathRate n * completionHorizon n) := by
        rw [Real.exp_add, Real.exp_log hnpos]
    _ ≤ Real.exp
        (Real.log (n : ℝ) * (-(6347 / 3125 : ℝ))) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hrate]

/-- Row-3 original-law headline.  The event is the joint event that the
homogeneous-five/useful-floor gate survives for all sixteen work units while
at least one Reserve remains unset. -/
theorem law_completion_failure_tail
    (init : InputCfg n) (hn : timePopulationThreshold ≤ n) :
    law init (completionFailure init n) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(6347 / 3125 : ℝ))) := by
  have hnsmall : 2 ≤ n := by
    have hlarge := (time_population_bounds hn).2
    omega
  have htail := extinction_tail_at_pastTime init
    (homogeneousFiveStart init) (homogeneousFiveStart_past init)
    completionDebt 0 (CompletionGate n) n (completionDeathRate n)
    (completionDeathRate_nonneg n)
    (completionDeathRate_le_one (by omega))
    (fun c hc d _ => completionDebt_draw_le n c hc d)
    (completion_service_probability n hnsmall)
    (completionHorizon n)
  have hnumeric := completion_sixteen_work_units hn
  have h1 : law init (completionFailure init n) ≤
      ENNReal.ofReal ((n : ℝ) * Real.exp
        (-completionDeathRate n * completionHorizon n)) := by
    simpa only [completionFailure, completionFailureFrom] using htail
  exact h1.trans (ENNReal.ofReal_le_ofReal hnumeric)

/-- Same headline with an arbitrary observed prefix selector attached to the
start fibre.  No conditioning and no extra factor are introduced. -/
theorem law_completion_failure_with_prefix_tail
    (init : InputCfg n) (hn : timePopulationThreshold ≤ n)
    (A : (s : ℕ) → Set (InputRecordedPrefix n s)) :
    law init (completionFailureWithPrefix init A) ≤
      ENNReal.ofReal (Real.rpow (n : ℝ) (-(6347 / 3125 : ℝ))) := by
  apply (measure_mono ?_).trans (law_completion_failure_tail init hn)
  rintro ω ⟨s, hs, hA, hfail⟩
  exact ⟨s, hs, hfail⟩

/-- Construct the killed-prefix live condition from deterministic actual-trace
facts.  This is the input supplied by the protected timer and the useful-class
receipt, not a probabilistic conditioning assumption. -/
theorem completionDebtLive_of_gates
    (init : Cfg L K) (ω : Ω L K) (s n : ℕ)
    (hgates : ∀ u, u ≤ completionHorizon n →
      CompletionGate n (trace init ω (s + u))) :
    DebtLive init s completionDebt 0 (CompletionGate n) n
      (completionHorizon n) ω := by
  have hstart := hgates 0 (Nat.zero_le _)
  have hcount : unsampledReserveU (trace init ω s) ≤ n := by
    have hle : unsampledReserveU (trace init ω s) ≤
        (trace init ω s).card := by
      unfold unsampledReserveU
      exact Multiset.countP_le_card _ _
    have hp : (trace init ω s).card = n := hstart.population
    exact hle.trans hp.le
  refine ⟨?_, hgates⟩
  simpa only [completionDebt, sub_zero, Nat.ceil_natCast] using hcount

/-- On the complement of the killed failure event, gate survival forces every
Reserve to have an actual sample at the sixteen-unit endpoint. -/
theorem sampled_endpoint_of_not_failure
    (init : Cfg L K) (ω : Ω L K) (s n : ℕ)
    (hlive : DebtLive init s completionDebt 0 (CompletionGate n) n
      (completionHorizon n) ω)
    (hnot : ω ∉ completionFailureFrom init s n) :
    ReserveSampled
      (trace init ω (s + completionHorizon n)) := by
  unfold ReserveSampled
  by_contra hne
  apply hnot
  change ω ∈ extinctionFailure init s completionDebt 0
    (CompletionGate n) n (completionHorizon n)
  refine ⟨hlive, ?_⟩
  rw [completionDebt_ceil]
  exact Nat.one_le_iff_ne_zero.mpr hne

/-- The genuine completion stopping time is finite and lies in the actual
sixteen-work-unit interval. -/
theorem completion_before_horizon
    (init : Cfg L K) (ω : Ω L K) (s n : ℕ)
    (hstart : homogeneousFiveStart init ω = (s : WithTop ℕ))
    (hlive : DebtLive init s completionDebt 0 (CompletionGate n) n
      (completionHorizon n) ω)
    (hnot : ω ∉ completionFailureFrom init s n) :
    ∃ u, s ≤ u ∧ u ≤ s + completionHorizon n ∧
      completionTime init n ω = (u : WithTop ℕ) ∧
      SamplingComplete n (trace init ω u) := by
  have hgate := hlive.2 (completionHorizon n) le_rfl
  have hsampled := sampled_endpoint_of_not_failure
    init ω s n hlive hnot
  have hend : SamplingComplete n
      (trace init ω (s + completionHorizon n)) :=
    ⟨hgate.population, hgate.phase_five, hsampled⟩
  have hle : completionTime init n ω ≤
      ((s + completionHorizon n : ℕ) : WithTop ℕ) :=
    (TraceDrain.exitTime_le_iff init (SamplingComplete n) ω _).2
      ⟨s + completionHorizon n, le_rfl, hend⟩
  have hfinite : completionTime init n ω ≠ ⊤ :=
    ne_top_of_le_ne_top
      (show ((s + completionHorizon n : ℕ) : WithTop ℕ) ≠ ⊤ from
        WithTop.coe_ne_top) hle
  obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have htime : completionTime init n ω = (u : WithTop ℕ) := hu.symm
  have huend : u ≤ s + completionHorizon n := by
    rw [htime] at hle
    exact WithTop.coe_le_coe.mp hle
  have hucomplete :=
    (exitTime_eq_iff_firstHit init (SamplingComplete n) ω u).mp
      (by simpa only [completionTime] using htime)
  have hsfirst :=
    (exitTime_eq_iff_firstHit init allPhaseFive ω s).mp
      (by simpa only [homogeneousFiveStart] using hstart)
  have hsu : s ≤ u := by
    by_contra h
    have hus : u < s := by omega
    exact hsfirst.2 u hus hucomplete.1.phase_five
  exact ⟨u, hsu, huend, htime, hucomplete.1⟩

/-- Row-4-facing receipt.  `Snapshot` is the separate row-2 headline and is
therefore an explicit hypothesis rather than duplicated here. -/
structure CompletionReceipt
    (init : InputCfg n) (ω : InputLog n)
    (a four five u : ℕ) (Snapshot : InputCfg n → Prop) : Prop where
  observed_path : LateF6OriginalLaw.Prefix init ω a four u
  five_start : homogeneousFiveStart init ω = (five : WithTop ℕ)
  completed_at : completionTime init n ω = (u : WithTop ℕ)
  start_le : five ≤ u
  within_sixteen : u ≤ five + completionHorizon n
  complete : SamplingComplete n (trace init ω u)
  snapshot : Snapshot (trace init ω u)

/-- Deterministic receipt constructor on every actual trace.  The only input
from row 2 is the named `hrowTwo` predicate at the actual completion hit. -/
theorem completionReceipt_of_no_failure
    (init : InputCfg n) (ω : InputLog n)
    (a four five : ℕ) (Snapshot : InputCfg n → Prop)
    (hstart : homogeneousFiveStart init ω = (five : WithTop ℕ))
    (hgates : ∀ v, v ≤ completionHorizon n →
      CompletionGate n (trace init ω (five + v)))
    (hnot : ω ∉ completionFailureFrom init five n)
    (hpath : ∀ u, five ≤ u → u ≤ five + completionHorizon n →
      LateF6OriginalLaw.Prefix init ω a four u)
    (hrowTwo : ∀ u, five ≤ u → u ≤ five + completionHorizon n →
      completionTime init n ω = (u : WithTop ℕ) →
      Snapshot (trace init ω u)) :
    ∃ u, CompletionReceipt init ω a four five u Snapshot := by
  have hlive := completionDebtLive_of_gates init ω five n hgates
  obtain ⟨u, hfu, huend, htime, hcomplete⟩ :=
    completion_before_horizon init ω five n hstart hlive hnot
  exact ⟨u,
    { observed_path := hpath u hfu huend
      five_start := hstart
      completed_at := htime
      start_le := hfu
      within_sixteen := huend
      complete := hcomplete
      snapshot := hrowTwo u hfu huend htime }⟩

end Ripple.PopulationProtocol.ExactMajority.LateSamplingCompletion

end
