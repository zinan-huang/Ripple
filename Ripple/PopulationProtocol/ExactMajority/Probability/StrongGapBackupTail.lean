import Ripple.PopulationProtocol.ExactMajority.Probability.StrongGapBackupDrift
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseTwoThresholds

/-!
# Strong-gap backup tails on the original recorded law

Every stage retains the mass of the original prefix event. The decay estimate
uses truncated ENNReal subtraction and makes no assertion that sourceRate ≤ 1.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.StrongGapBackup

open TimeTheorem PairLog TraceDrain

variable {L K : ℕ}

theorem useful_gap_of_main_floor {n M d : ℕ}
    (hM : 99 * n ≤ 200 * M) (hstrong : M < 40 * d) :
    n ≤ 120 * d := by
  omega

def stageBudget (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1 / (n : ℝ) ^ 3)

def threeStageHorizon (n : ℕ) : ℕ := 3 * logWindow n 240

def backupHorizon (n : ℕ) : ℕ :=
  StageEventSpec.activationHorizon n + threeStageHorizon n

theorem sourceRate_eq_ofReal {n d : ℕ} (hn : 2 ≤ n) :
    sourceRate n d =
      ENNReal.ofReal ((2 * (d : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hden : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  calc sourceRate n d =
      ENNReal.ofReal ((2 * d : ℕ) : ℝ) /
        ENNReal.ofReal ((n * (n - 1) : ℕ) : ℝ) := by
        simp only [sourceRate, ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal
        (((2 * d : ℕ) : ℝ) / ((n * (n - 1) : ℕ) : ℝ)) :=
      (ENNReal.ofReal_div_of_pos (by exact_mod_cast hden)).symm
    _ = _ := by
      simp only [Nat.cast_mul, Nat.cast_sub (show 1 ≤ n by omega),
        Nat.cast_ofNat, Nat.cast_one]

theorem sourceRate_floor {n d : ℕ} (hn : 2 ≤ n) (hstrong : n ≤ 120 * d) :
    ENNReal.ofReal (1 / (60 * (n : ℝ))) ≤ sourceRate n d := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hnminus : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hstrongR : (n : ℝ) ≤ 120 * (d : ℝ) := by exact_mod_cast hstrong
  rw [sourceRate_eq_ofReal hn]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hm := mul_le_mul_of_nonneg_right hstrongR hnpos.le
  nlinarith

theorem stage_scalar {n d : ℕ} (hn : 2 ≤ n) (hstrong : n ≤ 120 * d) :
    (1 - sourceRate n d) ^ logWindow n 240 * (n : ℝ≥0∞) ≤ stageBudget n := by
  let N := logWindow n 240
  let r : ℝ := 1 / (60 * (n : ℝ))
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hrzero : 0 ≤ r := by dsimp [r]; positivity
  have hrone : r ≤ 1 := by
    dsimp [r]
    rw [div_le_one (by positivity)]
    linarith
  have hrate : ENNReal.ofReal r ≤ sourceRate n d := sourceRate_floor hn hstrong
  have hbase : 1 - sourceRate n d ≤ ENNReal.ofReal (1 - r) := by
    calc 1 - sourceRate n d ≤ 1 - ENNReal.ofReal r :=
        tsub_le_tsub_left hrate 1
      _ = ENNReal.ofReal (1 - r) := by
        rw [ENNReal.ofReal_sub _ hrzero, ENNReal.ofReal_one]
  have hpow : (1 - sourceRate n d) ^ N ≤ ENNReal.ofReal ((1 - r) ^ N) := by
    rw [ENNReal.ofReal_pow (by linarith)]
    gcongr
  have hceil : (240 : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤ (N : ℝ) := by
    dsimp [N, logWindow]
    exact Nat.le_ceil _
  have hcal : 4 * Real.log (n : ℝ) ≤ r * (N : ℝ) := by
    calc 4 * Real.log (n : ℝ) =
        r * ((240 : ℝ) * (n : ℝ) * Real.log (n : ℝ)) := by
          dsimp [r]
          field_simp [ne_of_gt hnpos]
          <;> ring
      _ ≤ r * (N : ℝ) := mul_le_mul_of_nonneg_left hceil hrzero
  have hcube : Real.exp ((3 : ℝ) * Real.log (n : ℝ)) = (n : ℝ) ^ 3 := by
    simpa only [Real.exp_log hnpos] using (Real.exp_nat_mul (Real.log (n : ℝ)) 3)
  have hdecay : Real.exp (-4 * Real.log (n : ℝ)) * (n : ℝ) =
      1 / (n : ℝ) ^ 3 := by
    calc Real.exp (-4 * Real.log (n : ℝ)) * (n : ℝ) =
        Real.exp (-4 * Real.log (n : ℝ)) * Real.exp (Real.log (n : ℝ)) := by
          rw [Real.exp_log hnpos]
      _ = Real.exp (-4 * Real.log (n : ℝ) + Real.log (n : ℝ)) :=
        (Real.exp_add _ _).symm
      _ = Real.exp (-((3 : ℝ) * Real.log (n : ℝ))) := by congr 1; ring
      _ = 1 / (n : ℝ) ^ 3 := by rw [Real.exp_neg, hcube, one_div]
  have hreal : (1 - r) ^ N * (n : ℝ) ≤ 1 / (n : ℝ) ^ 3 := by
    have he : (1 - r) ^ N ≤ Real.exp (-r * (N : ℝ)) := by
      calc (1 - r) ^ N ≤ Real.exp (-r) ^ N :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-r)]) N
        _ = Real.exp (-r * (N : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    calc (1 - r) ^ N * (n : ℝ) ≤
        Real.exp (-r * (N : ℝ)) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right he hnpos.le
      _ ≤ Real.exp (-4 * Real.log (n : ℝ)) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [hcal])) hnpos.le
      _ = 1 / (n : ℝ) ^ 3 := hdecay
  calc (1 - sourceRate n d) ^ logWindow n 240 * (n : ℝ≥0∞) ≤
      ENNReal.ofReal ((1 - r) ^ N) * ENNReal.ofReal (n : ℝ) := by
        rw [ENNReal.ofReal_natCast]
        exact mul_le_mul_right' hpow _
    _ = ENNReal.ofReal ((1 - r) ^ N * (n : ℝ)) :=
      (ENNReal.ofReal_mul (pow_nonneg (by linarith) N)).symm
    _ ≤ stageBudget n := ENNReal.ofReal_le_ofReal hreal

theorem stage_tail_from_prefix_calibrated (init : Cfg L K)
    (σ : Sign) (stage : Stage) (n d : ℕ)
    (hn : 2 ≤ n) (hstrong : n ≤ 120 * d)
    (s : ℕ) (A : Set ((k : Finset.Iic s) → Draw L K))
    (hA : ∀ p ∈ A, Domain σ stage n d (prefixCfg init s p)) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        1 ≤ targetCount σ stage (trace init ω (s + logWindow n 240))} ≤
      stageBudget n *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} :=
  (stage_tail_from_prefix init σ stage n d hn s (logWindow n 240) A hA).trans
    (mul_le_mul_right' (stage_scalar hn hstrong) _)

/-- Three concrete target-count stages on the original recorded trajectory.
Only a finite-prefix event is conditioned on, and its probability is retained. -/
theorem three_stage_tail_from_prefix (init : Cfg L K)
    (hinit : validInitial init) (σ : Sign) (n d : ℕ)
    (hn : 2 ≤ n) (hstrong : n ≤ 120 * d)
    (s : ℕ) (A : Set ((k : Finset.Iic s) → Draw L K))
    (hA : ∀ p ∈ A, Domain σ .cancel n d (prefixCfg init s p)) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        trace init ω (s + threeStageHorizon n) ∉ StableDone L K init} ≤
      3 * stageBudget n *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  let N := logWindow n 240
  let tFirst := s + N
  let tSecond := tFirst + N
  have hsFirst : s ≤ tFirst := by dsimp [tFirst]; omega
  have hsSecond : s ≤ tSecond := by dsimp [tSecond, tFirst]; omega
  have hfirstSecond : tFirst ≤ tSecond := by dsimp [tSecond]; omega
  have hfinal : tSecond + N = s + threeStageHorizon n := by
    dsimp [tSecond, tFirst, N, threeStageHorizon]
    omega
  let AFirst : Set ((k : Finset.Iic tFirst) → Draw L K) :=
    {p | restrictPrefix hsFirst p ∈ A ∧
      Domain σ .absorb n d (prefixCfg init tFirst p)}
  let ASecond : Set ((k : Finset.Iic tSecond) → Draw L K) :=
    {p | restrictPrefix hsSecond p ∈ A ∧
      Domain σ .broadcast n d (prefixCfg init tSecond p)}
  let PA := law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A}
  let ECancel : Set (Ω L K) :=
    {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
      1 ≤ targetCount σ .cancel (trace init ω tFirst)}
  let EAbsorb : Set (Ω L K) :=
    {ω | frestrictLe (π := fun _ : ℕ => Draw L K) tFirst ω ∈ AFirst ∧
      1 ≤ targetCount σ .absorb (trace init ω tSecond)}
  let EBroadcast : Set (Ω L K) :=
    {ω | frestrictLe (π := fun _ : ℕ => Draw L K) tSecond ω ∈ ASecond ∧
      1 ≤ targetCount σ .broadcast (trace init ω (tSecond + N))}
  have hFirstMass :
      law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) tFirst ω ∈ AFirst} ≤ PA :=
    measure_mono fun ω hω => hω.1
  have hSecondMass :
      law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) tSecond ω ∈ ASecond} ≤ PA :=
    measure_mono fun ω hω => hω.1
  have hCancel : law init ECancel ≤ stageBudget n * PA :=
    stage_tail_from_prefix_calibrated init σ .cancel n d hn hstrong s A hA
  have hAbsorb : law init EAbsorb ≤ stageBudget n * PA :=
    (stage_tail_from_prefix_calibrated init σ .absorb n d hn hstrong tFirst AFirst
      (fun p hp => hp.2)).trans (mul_le_mul_left' hFirstMass _)
  have hBroadcast : law init EBroadcast ≤ stageBudget n * PA :=
    (stage_tail_from_prefix_calibrated init σ .broadcast n d hn hstrong tSecond ASecond
      (fun p hp => hp.2)).trans (mul_le_mul_left' hSecondMass _)
  have hcover :
      {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        trace init ω (s + threeStageHorizon n) ∉ StableDone L K init} ⊆
      ECancel ∪ (EAbsorb ∪ EBroadcast) := by
    rintro ω ⟨hp, hbad⟩
    by_cases hcancel : 1 ≤ targetCount σ .cancel (trace init ω tFirst)
    · exact Or.inl ⟨hp, hcancel⟩
    have hcancelZero : targetCount σ .cancel (trace init ω tFirst) = 0 := by omega
    have hcancelDomain : Domain σ .cancel n d (trace init ω tFirst) :=
      domain_preserved_by_reachable σ .cancel n d _ _ (hA _ hp)
        (trace_reachable init ω hsFirst)
    have hFirst : frestrictLe (π := fun _ : ℕ => Draw L K) tFirst ω ∈ AFirst :=
      ⟨hp, absorb_domain_of_cancel_drained σ n d _ hcancelDomain hcancelZero⟩
    by_cases habsorb : 1 ≤ targetCount σ .absorb (trace init ω tSecond)
    · exact Or.inr (Or.inl ⟨hFirst, habsorb⟩)
    have habsorbZero : targetCount σ .absorb (trace init ω tSecond) = 0 := by omega
    have habsorbDomain : Domain σ .absorb n d (trace init ω tSecond) :=
      domain_preserved_by_reachable σ .absorb n d _ _ hFirst.2
        (trace_reachable init ω hfirstSecond)
    have hSecond : frestrictLe (π := fun _ : ℕ => Draw L K) tSecond ω ∈ ASecond :=
      ⟨hp, broadcast_domain_of_absorb_drained σ n d _ habsorbDomain habsorbZero⟩
    by_cases hbroadcast : 1 ≤ targetCount σ .broadcast (trace init ω (tSecond + N))
    · exact Or.inr (Or.inr ⟨hSecond, hbroadcast⟩)
    have hbroadcastZero :
        targetCount σ .broadcast (trace init ω (tSecond + N)) = 0 := by omega
    have hbroadcastDomain : Domain σ .broadcast n d (trace init ω (tSecond + N)) :=
      domain_preserved_by_reachable σ .broadcast n d _ _ hSecond.2
        (trace_reachable init ω (Nat.le_add_right _ _))
    have hreach :
        (NonuniformMajority L K).Reachable init (trace init ω (tSecond + N)) := by
      simpa only [TimeTheorem.trace_zero] using
        (trace_reachable init ω (s := 0) (t := tSecond + N) (Nat.zero_le _))
    have hdone := broadcast_drained_mem_stableDone σ n d (by omega) init _
      hinit hreach hbroadcastDomain hbroadcastZero
    exact False.elim (hbad (by simpa only [hfinal] using hdone))
  calc
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        trace init ω (s + threeStageHorizon n) ∉ StableDone L K init} ≤
        law init (ECancel ∪ (EAbsorb ∪ EBroadcast)) := measure_mono hcover
    _ ≤ law init ECancel + law init (EAbsorb ∪ EBroadcast) := measure_union_le _ _
    _ ≤ law init ECancel + (law init EAbsorb + law init EBroadcast) :=
      by gcongr; exact measure_union_le _ _
    _ ≤ stageBudget n * PA + (stageBudget n * PA + stageBudget n * PA) :=
      add_le_add hCancel (add_le_add hAbsorb hBroadcast)
    _ = 3 * stageBudget n * PA := by ring


/-- A sign selected from the conserved input gap. -/
def majoritySign (init : Cfg L K) : Sign :=
  if 0 ≤ initialGap init then .pos else .neg

theorem signedGap_eq_gapMagnitude_of_reachable (init c : Cfg L K)
    (hinit : validInitial init)
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hphase : ∀ a ∈ c, a.phase.val = 10) :
    signedGap (majoritySign init) c = (gapMagnitude init : ℤ) := by
  have hsum := phase10ActiveSignedSum_eq_initialGap_of_reachable
    init c hinit hreach hphase
  unfold majoritySign
  split_ifs with h
  · change phase10ActiveSignedSum c = (gapMagnitude init : ℤ)
    rw [hsum, gapMagnitude, Int.natCast_natAbs, abs_of_nonneg h]
  · change -phase10ActiveSignedSum c = (gapMagnitude init : ℤ)
    rw [hsum, gapMagnitude, Int.natCast_natAbs, abs_of_neg (lt_of_not_ge h)]

def BackupSeed (n : ℕ) (c : Cfg L K) : Prop :=
  c.card = n ∧ ∃ a ∈ c, a.phase.val = 10

theorem activation_budget_le_two_stages {n : ℕ} (hn : 2 ≤ n) :
    PhaseTwoThresholds.thresholdBudget n (StageEventSpec.activationHorizon n) ≤
      2 * stageBudget n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hpow : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 5 := by
    have h := mul_le_mul_of_nonneg_right hsq (pow_nonneg hnpos.le 3)
    nlinarith only [h]
  have hratio : 2 / (n : ℝ) ^ 5 ≤ 2 / (n : ℝ) ^ 3 := by
    apply (div_le_div_iff₀ (pow_pos hnpos 5) (pow_pos hnpos 3)).2
    nlinarith only [hpow]
  calc PhaseTwoThresholds.thresholdBudget n (StageEventSpec.activationHorizon n) ≤
      ENNReal.ofReal (2 / (n : ℝ) ^ 5) :=
        PhaseTwoThresholds.activation_thresholdBudget_le hn
    _ ≤ ENNReal.ofReal (2 / (n : ℝ) ^ 3) := ENNReal.ofReal_le_ofReal hratio
    _ = 2 * stageBudget n := by
      unfold stageBudget
      rw [show (2 : ℝ) / (n : ℝ) ^ 3 = 2 * (1 / (n : ℝ) ^ 3) by ring,
        ENNReal.ofReal_mul (by norm_num)]
      norm_num

theorem five_stage_budget_eq (n : ℕ) :
    (5 : ℝ≥0∞) * stageBudget n = ENNReal.ofReal (5 / (n : ℝ) ^ 3) := by
  unfold stageBudget
  rw [show (5 : ℝ) / (n : ℝ) ^ 3 = 5 * (1 / (n : ℝ) ^ 3) by ring,
    ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- From an observed phase-10 seed, spread the threshold at a fixed offset and
run the three stages there. Every term retains the original prefix mass.
The sign and source supply come from the reachable initial configuration. -/
theorem backup_seed_tail_from_prefix (init : Cfg L K) (hinit : validInitial init)
    {n : ℕ} (hn : 2 ≤ n) (hstrong : n ≤ 120 * gapMagnitude init)
    (s : ℕ) (A : Set ((k : Finset.Iic s) → Draw L K))
    (hA : ∀ p ∈ A, BackupSeed n (prefixCfg init s p)) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        trace init ω (s + backupHorizon n) ∉ StableDone L K init} ≤
      ENNReal.ofReal (5 / (n : ℝ) ^ 3) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := by
  let t := s + StageEventSpec.activationHorizon n
  have hst : s ≤ t := by dsimp [t]; omega
  have hfinal : t + threeStageHorizon n = s + backupHorizon n := by
    dsimp [t, backupHorizon]
    omega
  let Ready : Set ((k : Finset.Iic t) → Draw L K) :=
    {p | restrictPrefix hst p ∈ A ∧
      Domain (majoritySign init) .cancel n (gapMagnitude init) (prefixCfg init t p)}
  let PA := law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A}
  let EFlood : Set (Ω L K) :=
    {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
      ¬ ∀ a ∈ trace init ω t, 10 ≤ a.phase.val}
  let EStages : Set (Ω L K) :=
    {ω | frestrictLe (π := fun _ : ℕ => Draw L K) t ω ∈ Ready ∧
      trace init ω (t + threeStageHorizon n) ∉ StableDone L K init}
  have hseed : ∀ p ∈ A,
      (prefixCfg init s p).card = n ∧
        ∃ a ∈ prefixCfg init s p, 10 ≤ a.phase.val := by
    intro p hp
    obtain ⟨hcard, a, ha, hphase⟩ := hA p hp
    exact ⟨hcard, a, ha, hphase.ge⟩
  have hFlood : law init EFlood ≤ 2 * stageBudget n * PA :=
    (PhaseTwoThresholds.threshold_spread_from_prefix init hn 10 (by decide)
      s (StageEventSpec.activationHorizon n) A hseed).trans
        (mul_le_mul_right' (activation_budget_le_two_stages hn) _)
  have hReadyMass :
      law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) t ω ∈ Ready} ≤ PA :=
    measure_mono fun ω hω => hω.1
  have hStages : law init EStages ≤ 3 * stageBudget n * PA :=
    (three_stage_tail_from_prefix init hinit (majoritySign init) n (gapMagnitude init)
      hn hstrong t Ready (fun p hp => hp.2)).trans
        (mul_le_mul_left' hReadyMass _)
  have hcover :
      {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        trace init ω (s + backupHorizon n) ∉ StableDone L K init} ⊆
      EFlood ∪ EStages := by
    rintro ω ⟨hp, hbad⟩
    by_cases hphase : ∀ a ∈ trace init ω t, 10 ≤ a.phase.val
    · have hexact : ∀ a ∈ trace init ω t, a.phase.val = 10 := by
        intro a ha
        have hlow := hphase a ha
        have hhigh := a.phase.isLt
        omega
      have hreach : (NonuniformMajority L K).Reachable init (trace init ω t) := by
        simpa only [TimeTheorem.trace_zero] using
          (trace_reachable init ω (s := 0) (t := t) (Nat.zero_le _))
      have hcard : (trace init ω t).card = n :=
        (Protocol.reachable_card_eq (trace_reachable init ω hst)).trans (hA _ hp).1
      have hgap := signedGap_eq_gapMagnitude_of_reachable init _
        hinit hreach hexact
      have hdomain :
          Domain (majoritySign init) .cancel n (gapMagnitude init) (trace init ω t) :=
        ⟨hcard, hexact, le_of_eq hgap.symm, fun _ _ => trivial⟩
      refine Or.inr ⟨⟨hp, hdomain⟩, ?_⟩
      simpa only [hfinal] using hbad
    · exact Or.inl ⟨hp, hphase⟩
  calc law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
        trace init ω (s + backupHorizon n) ∉ StableDone L K init} ≤
        law init (EFlood ∪ EStages) := measure_mono hcover
    _ ≤ law init EFlood + law init EStages := measure_union_le _ _
    _ ≤ 2 * stageBudget n * PA + 3 * stageBudget n * PA :=
      add_le_add hFlood hStages
    _ = (5 * stageBudget n) * PA := by ring
    _ = ENNReal.ofReal (5 / (n : ℝ) ^ 3) * PA := by rw [five_stage_budget_eq]

def backupFailureAt (init : Cfg L K) (n : ℕ)
    (τ : Ω L K → WithTop ℕ) : Set (Ω L K) :=
  {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
    BackupSeed n (trace init ω s) ∧
    trace init ω (s + backupHorizon n) ∉ StableDone L K init}

theorem backupFailureAt_measurable (init : Cfg L K) (n : ℕ)
    (τ : Ω L K → WithTop ℕ) (hτ : PhaseOneDrain.PairLogPastTime τ) :
    MeasurableSet (backupFailureAt init n τ) := by
  have heq : backupFailureAt init n τ =
      ⋃ s : ℕ, {ω | τ ω = (s : WithTop ℕ)} ∩
        {ω | BackupSeed n (trace init ω s)} ∩
        {ω | trace init ω (s + backupHorizon n) ∉ StableDone L K init} := by
    ext ω
    simp only [backupFailureAt, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨s, hs, hseed, hbad⟩
      exact ⟨s, ⟨⟨hs, hseed⟩, hbad⟩⟩
    · rintro ⟨s, ⟨⟨hs, hseed⟩, hbad⟩⟩
      exact ⟨s, hs, hseed, hbad⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro s
  have htime : MeasurableSet {ω | τ ω = (s : WithTop ℕ)} :=
    (pairLogFiltration L K).le s _ (hτ s)
  have hseed : MeasurableSet {ω | BackupSeed n (trace init ω s)} :=
    (Set.to_countable {c : Cfg L K | BackupSeed n c}).measurableSet.preimage
      ((measurable_pi_apply s).comp (measurable_trace init))
  have hbad : MeasurableSet
      {ω | trace init ω (s + backupHorizon n) ∉ StableDone L K init} :=
    (Set.to_countable {c : Cfg L K | c ∉ StableDone L K init}).measurableSet.preimage
      ((measurable_pi_apply (s + backupHorizon n)).comp (measurable_trace init))
  exact (htime.inter hseed).inter hbad

/-- The concrete strong-gap backup tail at a genuine observed pair-log time.
No independence from the observed prefix is asserted or assumed. -/
theorem backup_seed_tail_at_past_time (init : Cfg L K) (hinit : validInitial init)
    {n : ℕ} (hn : 2 ≤ n) (hstrong : n ≤ 120 * gapMagnitude init)
    (τ : Ω L K → WithTop ℕ) (hτ : PhaseOneDrain.PairLogPastTime τ) :
    law init (backupFailureAt init n τ) ≤ ENNReal.ofReal (5 / (n : ℝ) ^ 3) := by
  refine genuine_seed_splice (law init) τ (backupFailureAt init n τ)
    (ENNReal.ofReal (5 / (n : ℝ) ^ 3))
    (backupFailureAt_measurable init n τ hτ)
    (fun s => (pairLogFiltration L K).le s _ (hτ s)) ?_ ?_
  · rintro ω ⟨s, hs, _⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    have hτs := hτ s
    rw [pairLogFiltration_eq_comap] at hτs
    obtain ⟨Aτ, _, hAτ⟩ := hτs
    let A : Set ((k : Finset.Iic s) → Draw L K) :=
      {p | p ∈ Aτ ∧ BackupSeed n (prefixCfg init s p)}
    have hmem (ω : Ω L K) :
        frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ Aτ ↔
          τ ω = (s : WithTop ℕ) := by
      change ω ∈ (frestrictLe (π := fun _ : ℕ => Draw L K) s) ⁻¹' Aτ ↔
        ω ∈ {ω | τ ω = (s : WithTop ℕ)}
      rw [hAτ]
    have htail := backup_seed_tail_from_prefix init hinit hn hstrong s A
      (fun p hp => hp.2)
    calc
      law init (backupFailureAt init n τ ∩ {ω | τ ω = (s : WithTop ℕ)}) ≤
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A ∧
            trace init ω (s + backupHorizon n) ∉ StableDone L K init} := by
        apply measure_mono
        rintro ω ⟨⟨r, hr, hseed, hbad⟩, hs⟩
        have hrs : r = s := WithTop.coe_injective (hr.symm.trans hs)
        subst r
        exact ⟨⟨(hmem ω).mpr hs, hseed⟩, hbad⟩
      _ ≤ ENNReal.ofReal (5 / (n : ℝ) ^ 3) *
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw L K) s ω ∈ A} := htail
      _ ≤ ENNReal.ofReal (5 / (n : ℝ) ^ 3) *
          law init {ω | τ ω = (s : WithTop ℕ)} :=
        mul_le_mul_left' (measure_mono fun ω hω => (hmem ω).mp hω.1) _

/-- Historical no-hit form, with the same original-law deadline. -/
theorem backup_no_stable_hit_tail (init : Cfg L K) (hinit : validInitial init)
    {n : ℕ} (hn : 2 ≤ n) (hstrong : n ≤ 120 * gapMagnitude init)
    (τ : Ω L K → WithTop ℕ) (hτ : PhaseOneDrain.PairLogPastTime τ) :
    law init {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
        BackupSeed n (trace init ω s) ∧
        ∀ k ≤ backupHorizon n, trace init ω (s + k) ∉ StableDone L K init} ≤
      ENNReal.ofReal (5 / (n : ℝ) ^ 3) := by
  refine (measure_mono ?_).trans
    (backup_seed_tail_at_past_time init hinit hn hstrong τ hτ)
  rintro ω ⟨s, hs, hseed, hbad⟩
  exact ⟨s, hs, hseed, hbad (backupHorizon n) le_rfl⟩


end Ripple.PopulationProtocol.ExactMajority.StrongGapBackup

end
