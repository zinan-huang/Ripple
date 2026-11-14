-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingTerminalDebtDeadlines.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingTerminalDebtTails
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCreditClockBridge
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingNumerics

/-!
# Calibrated actual F/X/Y drain deadlines

The service counts are ceilings of the real count floors. This retains the
full .899 C and .19 M rates without a finite-population loss. The raw lengths
are the literal ceilings of 5 n^2/C and 30 n^2/M. Their bounds are joint with
the observed prefix gates under the original law.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.AveragingTerminalDebtDeadlines

open TimeTheorem PairLog StageEventSpec AveragingLiveProduct
open AveragingMixedAlgebra AveragingMixedLedgers
open AveragingDebtService AveragingPotentialService
open AveragingTerminalDebt AveragingMajorityPartners AveragingTerminalDebtTails
open AveragingChangingZeroTail AveragingStoppedDebt AveragingStoppedDebtLaw
open AveragingNumerics

variable {L : ℕ}

def warmClockCount (C : ℕ) : ℕ :=
  Nat.ceil ((899 / 1000 : ℚ) * C)

def majorityPartnerCount (M : ℕ) : ℕ :=
  Nat.ceil ((19 / 100 : ℚ) * M)

def clockWarmup (n C : ℕ) : ℕ :=
  Nat.ceil ((5 : ℝ) * (n : ℝ) ^ 2 / C)

def majorityWork (n M : ℕ) : ℕ :=
  Nat.ceil ((30 : ℝ) * (n : ℝ) ^ 2 / M)

theorem warmClockCount_ge (C : ℕ) :
    (899 / 1000 : ℝ) * C ≤ (warmClockCount C : ℝ) := by
  unfold warmClockCount
  have h := (Rat.cast_le (K := ℝ)).2 (Nat.le_ceil ((899 / 1000 : ℚ) * C))
  push_cast at h
  exact h

theorem majorityPartnerCount_ge (M : ℕ) :
    (19 / 100 : ℝ) * M ≤ (majorityPartnerCount M : ℝ) := by
  unfold majorityPartnerCount
  have h := (Rat.cast_le (K := ℝ)).2 (Nat.le_ceil ((19 / 100 : ℚ) * M))
  push_cast at h
  exact h

theorem warmClockCount_le (C : ℕ) : warmClockCount C ≤ C := by
  apply Nat.ceil_le.mpr
  have hC : (0 : ℚ) ≤ C := by positivity
  nlinarith

theorem majorityPartnerCount_le (M : ℕ) : majorityPartnerCount M ≤ M := by
  apply Nat.ceil_le.mpr
  have hM : (0 : ℚ) ≤ M := by positivity
  nlinarith

theorem two_service_size_bound (n R M : ℕ) (hn : 2 ≤ n) (hroles : R + M ≤ n) :
    2 * R * M ≤ n * (n - 1) := by
  have hnz : (2 : ℤ) ≤ n := by exact_mod_cast hn
  have hrolesz : (R : ℤ) + M ≤ n := by exact_mod_cast hroles
  have hsq := pow_le_pow_left₀
    (by positivity : (0 : ℤ) ≤ (R : ℤ) + M) hrolesz 2
  have hdiff := sq_nonneg ((R : ℤ) - M)
  have hpred : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have hnprod := mul_nonneg (show (0 : ℤ) ≤ n by omega)
    (show (0 : ℤ) ≤ (n : ℤ) - 2 by omega)
  have hbound : (2 : ℤ) * R * M ≤ (n : ℤ) * ((n - 1 : ℕ) : ℤ) := by
    rw [hpred]
    nlinarith only [hnprod, hsq, hdiff]
  exact_mod_cast hbound

theorem clockWarmup_size_bound (n C M : ℕ) (hn : 2 ≤ n) (hroles : C + M ≤ n) :
    2 * warmClockCount C * M ≤ n * (n - 1) :=
  two_service_size_bound n (warmClockCount C) M hn
    ((Nat.add_le_add_right (warmClockCount_le C) M).trans hroles)

theorem majorityWork_size_bound (n M : ℕ) (hn : 3 ≤ n)
    (hmain : 25 * M ≤ 13 * n) :
    2 * majorityPartnerCount M * M ≤ n * (n - 1) := by
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hmainreal : (25 : ℝ) * M ≤ 13 * n := by exact_mod_cast hmain
  have hceil : (majorityPartnerCount M : ℝ) < (19 / 100 : ℝ) * M + 1 := by
    unfold majorityPartnerCount
    have hq := (Rat.cast_lt (K := ℝ)).2 (Nat.ceil_lt_add_one
      (show (0 : ℚ) ≤ (19 / 100 : ℚ) * M by positivity))
    push_cast at hq
    exact hq
  have hsum : (majorityPartnerCount M : ℝ) + M ≤ n := by
    nlinarith only [hnreal, hmainreal, hceil]
  exact two_service_size_bound n (majorityPartnerCount M) M (by omega)
    (by exact_mod_cast hsum)

theorem clockWarmup_rate (n C : ℕ) (hn : 2 ≤ n) (hC : 0 < C) :
    (899 / 100 : ℝ) ≤
      clockDeathRate n (warmClockCount C) * clockWarmup n C := by
  have hCp : (0 : ℝ) < C := by exact_mod_cast hC
  have hden : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n - 1)
  have hdenle : ((n * (n - 1) : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hp : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    simpa only [Nat.cast_mul, pow_two] using
      mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg n)
  have htime : (5 : ℝ) * (n : ℝ) ^ 2 / C ≤ (clockWarmup n C : ℝ) :=
    Nat.le_ceil _
  have hprod :
      (899 / 200 : ℝ) * (n : ℝ) ^ 2 ≤
        (warmClockCount C : ℝ) * (clockWarmup n C : ℝ) := by
    calc
      (899 / 200 : ℝ) * (n : ℝ) ^ 2 =
          ((899 / 1000 : ℝ) * C) * ((5 : ℝ) * (n : ℝ) ^ 2 / C) := by
        field_simp [hCp.ne'] <;> ring
      _ ≤ _ := mul_le_mul (warmClockCount_ge C) htime (by positivity) (by positivity)
  unfold clockDeathRate
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).2
  have hscaled := mul_le_mul_of_nonneg_left hdenle
    (by norm_num : (0 : ℝ) ≤ 899 / 100)
  nlinarith only [hprod, hscaled]

theorem majorityWork_rate (n M : ℕ) (hn : 2 ≤ n) (hM : 0 < M) :
    (57 / 5 : ℝ) ≤
      clockDeathRate n (majorityPartnerCount M) * majorityWork n M := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hden : (0 : ℝ) < ((n * (n - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (by omega : 0 < n) (by omega : 0 < n - 1)
  have hdenle : ((n * (n - 1) : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hp : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
    simpa only [Nat.cast_mul, pow_two] using
      mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg n)
  have htime : (30 : ℝ) * (n : ℝ) ^ 2 / M ≤ (majorityWork n M : ℝ) :=
    Nat.le_ceil _
  have hprod :
      (57 / 10 : ℝ) * (n : ℝ) ^ 2 ≤
        (majorityPartnerCount M : ℝ) * (majorityWork n M : ℝ) := by
    calc
      (57 / 10 : ℝ) * (n : ℝ) ^ 2 =
          ((19 / 100 : ℝ) * M) * ((30 : ℝ) * (n : ℝ) ^ 2 / M) := by
        field_simp [hMp.ne'] <;> ring
      _ ≤ _ := mul_le_mul (majorityPartnerCount_ge M) htime (by positivity) (by positivity)
  unfold clockDeathRate
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).2
  have hscaled := mul_le_mul_of_nonneg_left hdenle
    (by norm_num : (0 : ℝ) ≤ 57 / 5)
  nlinarith only [hprod, hscaled]

/-- Helper: `labelCount` is monotone in its predicate. -/
theorem labelCount_mono_aux {n : ℕ} (init : InputCfg n)
    {P Q : Fin init.card → Prop} (h : ∀ i, P i → Q i) :
    labelCount init P ≤ labelCount init Q := by
  classical
  unfold labelCount
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, h i hi.2⟩

open Classical in
theorem clockFloor_of_clockHistory {n : ℕ}
    {init : InputCfg n} {ω : InputLog n} {S T ρ v : ℕ}
    {w : ClockTimes init} (h : ClockHistory init ω S T ρ w)
    (hSv : S ≤ v) (hvρ : v < ρ) (k : ℕ)
    (hk : k ≤ PhaseThreeModel.Numeric.hourIndex n)
    (hstart : w.start k ≤ v) (hfinish : v ≤ w.finish k) :
    warmClockCount (clockCount (trace init ω S)) ≤
      (trace init ω v).countP (ClockServiceSource k) := by
  have hcount : exactHourClocks init ω S v k ≤
      (trace init ω v).countP (ClockServiceSource k) := by
    rw [countP_trace_eq_labelCount]
    unfold exactHourClocks
    apply labelCount_mono_aux
    intro i hi
    obtain ⟨hrole, hactive, hhour⟩ := hi
    have himem : labelsAt init ω v i ∈ trace init ω v := by
      rw [← labelsAt_config init ω v]
      exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
    have hphase := (h.phase_range v hSv hvρ _ himem).2
    have hr := h.roles_fixed v hSv hvρ i
    refine ⟨?_, ?_, hhour.ge⟩
    · change 3 ≤ (labelsAt init ω v i).phase.val at hactive
      omega
    · change (labelsAt init ω S i).role = .clock at hrole
      exact hr.trans hrole
  have hoccupancy := h.exact_hour k hk v hstart hfinish
  have hnat := hoccupancy.trans (Nat.mul_le_mul_left 1000 hcount)
  apply Nat.ceil_le.mpr
  have hrat :
      (899 : ℚ) * clockCount (trace init ω S) ≤
        1000 * ((trace init ω v).countP (ClockServiceSource k) : ℚ) := by
    exact_mod_cast hnat
  nlinarith only [hrat]

open Classical in
theorem yGate_with_canonical_partners (σ : Sign) (ell : ℕ) (xstar gap : ℚ)
    (n M : ℕ) (c : Cfg L 256)
    (hpop : c.card = n) (hc : PotentialDomain c)
    (hX : debtX σ (ell + 2) c ≤ xstar)
    (hell : 1 ≤ ell) (hM : RoleSplitConcentration.mainCount c = M)
    (hsigned : prePhase4MassSum c = if σ = .pos then gap else -gap)
    (hscale : (2 / 5 : ℚ) * M ≤ (2 : ℚ) ^ ell * gap)
    (hphi : augmentedPhi ell c ≤ (1 / 1000 : ℚ) * M) :
    YGate σ ell xstar n (majorityPartnerCount M) c := by
  have hcarrier : ∀ a ∈ c, ¬ a.phase.val < 3 → a.role ≠ .main → a.bias = .zero := by
    intro a ha hp hm
    have hphase : a.phase.val = 3 := by
      have hr := (hc a ha).range
      omega
    exact (hc a ha).active_carrier hphase hm
  have hfloor := majority_partner_floor_of_gap_and_phi σ ell M c gap
    hell hM hcarrier hsigned hscale hphi
  rw [nearMajorityCount_eq_count σ ell c (fun a ha => (hc a ha).range.2)] at hfloor
  refine ⟨hpop, hc, hX, ?_⟩
  apply Nat.ceil_le.mpr
  have hq : (19 : ℚ) * M ≤ 100 * (c.countP (NearMajority σ ell) : ℚ) := by
    exact_mod_cast hfloor
  nlinarith only [hq]

def thresholdFailure (init : Cfg L 256) (s : ℕ) (F : Cfg L 256 → ℚ)
    (A : ℚ) (W : Cfg L 256 → Prop) (M : ℕ) (a : ℚ) (T : ℕ) : Set (Ω L 256) :=
  {ω | DebtLive init s F A W M T ω ∧ A + a * M < F (trace init ω (s + T))}

theorem thresholdFailure_subset (init : Cfg L 256) (s : ℕ)
    (F : Cfg L 256 → ℚ) (A : ℚ) (W : Cfg L 256 → Prop)
    (M : ℕ) (a : ℚ) (T : ℕ) :
    thresholdFailure init s F A W M a T ⊆ debtFailure init s F A W M (a : ℝ) T := by
  rintro ω ⟨hlive, hlarge⟩
  refine ⟨hlive, ?_⟩
  have hle : a * (M : ℚ) ≤ (Nat.ceil (F (trace init ω (s + T)) - A) : ℚ) :=
    (show a * (M : ℚ) ≤ F (trace init ω (s + T)) - A by linarith).trans (Nat.le_ceil _)
  exact_mod_cast hle

/-- Actual changing-zero warmup, with its .002 M threshold and e^(-M/500) error. -/
theorem changingZeroFuel_warmup_tail_from (init : Cfg L 256) (s : ℕ)
    (B : Set ((i : Finset.Iic s) → Draw L 256))
    (k : ℕ) (hk : k ≤ L) (A : ℚ)
    (n C M : ℕ) (hn : 2 ≤ n) (hC : 0 < C) (hroles : C + M ≤ n) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ thresholdFailure init s (changingZeroFuel k) A
          (FuelGate k A n (warmClockCount C)) M (1 / 500) (clockWarmup n C)} ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) / 500)) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B} := by
  have hsize := clockWarmup_size_bound n C M hn hroles
  have htail := stoppedDebt_tail_from init s B (changingZeroFuel k) A
    (FuelGate k A n (warmClockCount C)) M (clockDeathRate n (warmClockCount C))
    (1 / 500) (clockDeathRate_nonneg n (warmClockCount C))
    (clockDeathRate_size_bound n (warmClockCount C) M hn hsize)
    (fun c hc d hd => changingZeroFuel_draw_le k c hc.domain d hd.domain)
    (changingZeroFuel_service_probability k hk A n (warmClockCount C) hn)
    (clockWarmup n C)
  have hsubset :
      {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ thresholdFailure init s (changingZeroFuel k) A
          (FuelGate k A n (warmClockCount C)) M (1 / 500) (clockWarmup n C)} ⊆
      {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ debtFailure init s (changingZeroFuel k) A
          (FuelGate k A n (warmClockCount C)) M (1 / 500) (clockWarmup n C)} := by
    rintro ω ⟨hp, hf⟩
    refine ⟨hp, ?_⟩
    simpa using thresholdFailure_subset init s _ _ _ M (1 / 500) _ hf
  refine (measure_mono hsubset).trans (htail.trans ?_)
  simpa only [neg_mul] using mul_le_mul_right'
    (ENNReal.ofReal_le_ofReal
      (warmup_death_exponent (clockWarmup_rate n C hn hC) (Nat.cast_nonneg M)))
    (law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B})

/-- The actual X warmup retains the same two-orientation Clock rate. -/
theorem debtX_warmup_tail_from (init : Cfg L 256) (s : ℕ)
    (B : Set ((i : Finset.Iic s) → Draw L 256))
    (σ : Sign) (k : ℕ) (hk : k ≤ L) (Dstar : ℚ)
    (n C M : ℕ) (hn : 2 ≤ n) (hC : 0 < C) (hroles : C + M ≤ n) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ thresholdFailure init s (debtX σ k) (2 * Dstar)
          (XGate σ k Dstar n (warmClockCount C)) M (1 / 500) (clockWarmup n C)} ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) / 500)) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B} := by
  have htail := debtX_tail_from init s B σ k hk Dstar n (warmClockCount C) M hn
    (clockWarmup_size_bound n C M hn hroles) (1 / 500) (clockWarmup n C)
  have hsubset :
      {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ thresholdFailure init s (debtX σ k) (2 * Dstar)
          (XGate σ k Dstar n (warmClockCount C)) M (1 / 500) (clockWarmup n C)} ⊆
      {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ debtFailure init s (debtX σ k) (2 * Dstar)
          (XGate σ k Dstar n (warmClockCount C)) M (1 / 500) (clockWarmup n C)} := by
    rintro ω ⟨hp, hf⟩
    refine ⟨hp, ?_⟩
    simpa using thresholdFailure_subset init s _ _ _ M (1 / 500) _ hf
  refine (measure_mono hsubset).trans (htail.trans ?_)
  simpa only [neg_mul] using mul_le_mul_right'
    (ENNReal.ofReal_le_ofReal
      (warmup_death_exponent (clockWarmup_rate n C hn hC) (Nat.cast_nonneg M)))
    (law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B})

/-- The actual Y service work uses ceil(.19 M) partners for ceil(30 n^2/M) draws. -/
theorem debtY_service_tail_from (init : Cfg L 256) (s : ℕ)
    (B : Set ((i : Finset.Iic s) → Draw L 256))
    (σ : Sign) (ell : ℕ) (xstar : ℚ)
    (n M : ℕ) (hn : 3 ≤ n) (hM : 0 < M) (hmain : 25 * M ≤ 13 * n) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ thresholdFailure init s (debtY σ (ell + 2)) xstar
          (YGate σ ell xstar n (majorityPartnerCount M)) M
          (1 / 1000) (majorityWork n M)} ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) / 600)) *
        law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B} := by
  have htail := debtY_tail_from init s B σ ell xstar n (majorityPartnerCount M) M
    (by omega) (majorityWork_size_bound n M hn hmain) (1 / 1000) (majorityWork n M)
  have hsubset :
      {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ thresholdFailure init s (debtY σ (ell + 2)) xstar
          (YGate σ ell xstar n (majorityPartnerCount M)) M
          (1 / 1000) (majorityWork n M)} ⊆
      {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ debtFailure init s (debtY σ (ell + 2)) xstar
          (YGate σ ell xstar n (majorityPartnerCount M)) M
          (1 / 1000) (majorityWork n M)} := by
    rintro ω ⟨hp, hf⟩
    refine ⟨hp, ?_⟩
    simpa using thresholdFailure_subset init s _ _ _ M (1 / 1000) _ hf
  refine (measure_mono hsubset).trans (htail.trans ?_)
  simpa only [neg_mul] using mul_le_mul_right'
    (ENNReal.ofReal_le_ofReal
      (terminal_death_exponent (majorityWork_rate n M (by omega) hM) (Nat.cast_nonneg M)))
    (law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B})

theorem debtX_target_of_warmup {M : ℕ} {Dstar x : ℚ}
    (hD : Dstar ≤ (2 / 125 : ℚ) * M)
    (hX : x ≤ 2 * Dstar + (1 / 500 : ℚ) * M) :
    x ≤ (17 / 500 : ℚ) * M := by linarith

theorem debtY_target_of_service {M : ℕ} {xstar y : ℚ}
    (hX : xstar ≤ (17 / 500 : ℚ) * M)
    (hY : y ≤ xstar + (1 / 1000 : ℚ) * M) :
    y ≤ (7 / 200 : ℚ) * M := by linarith

theorem terminal_work_below_hour (n C M : ℕ)
    (hn : 2 ≤ n) (hC : 0 < C) (hM : 0 < M)
    (hCcard : C ≤ n) (hratio : 12 * C ≤ 7 * M) :
    ((clockWarmup n C + majorityWork n M : ℕ) : ℝ) <
      (70 : ℝ) * (n : ℝ) ^ 2 / C := by
  have hCp : (0 : ℝ) < C := by exact_mod_cast hC
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hCr : (C : ℝ) ≤ n := by exact_mod_cast hCcard
  have hratioR : (12 : ℝ) * C ≤ 7 * M := by exact_mod_cast hratio
  have hw : (clockWarmup n C : ℝ) < (5 : ℝ) * (n : ℝ) ^ 2 / C + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hm : (majorityWork n M : ℝ) < (30 : ℝ) * (n : ℝ) ^ 2 / M + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hquot : (30 : ℝ) / M ≤ (35 / 2 : ℝ) / C := by
    apply (div_le_div_iff₀ hMp hCp).2
    nlinarith only [hratioR]
  have hwork : (30 : ℝ) * (n : ℝ) ^ 2 / M ≤
      (35 / 2 : ℝ) * (n : ℝ) ^ 2 / C := by
    have hs := mul_le_mul_of_nonneg_left hquot (sq_nonneg (n : ℝ))
    convert hs using 1 <;> ring
  have hunit : (2 : ℝ) ≤ (n : ℝ) ^ 2 / C := by
    apply (le_div_iff₀ hCp).2
    have hnprod := mul_nonneg (show (0 : ℝ) ≤ n by positivity)
      (show (0 : ℝ) ≤ (n : ℝ) - 2 by linarith only [hnreal])
    nlinarith only [hnprod, hCr]
  push_cast
  have e1 : (5 : ℝ) * (n : ℝ) ^ 2 / C = 5 * ((n : ℝ) ^ 2 / C) := mul_div_assoc _ _ _
  have e2 : (70 : ℝ) * (n : ℝ) ^ 2 / C = 70 * ((n : ℝ) ^ 2 / C) := mul_div_assoc _ _ _
  have e3 : (35 / 2 : ℝ) * (n : ℝ) ^ 2 / C = 35 / 2 * ((n : ℝ) ^ 2 / C) := mul_div_assoc _ _ _
  linarith only [hw, hm, hwork, hunit, e1, e2, e3]

theorem terminal_work_fits_window (n C M width : ℕ)
    (hn : 2 ≤ n) (hC : 0 < C) (hM : 0 < M)
    (hCcard : C ≤ n) (hratio : 12 * C ≤ 7 * M)
    (hwidth : 70 * n ^ 2 < C * width) :
    clockWarmup n C + majorityWork n M < width := by
  have hCp : (0 : ℝ) < C := by exact_mod_cast hC
  have hw : (70 : ℝ) * (n : ℝ) ^ 2 < (C : ℝ) * width := by exact_mod_cast hwidth
  have hdiv : (70 : ℝ) * (n : ℝ) ^ 2 / C < width :=
    (div_lt_iff₀ hCp).2 (by simpa only [mul_comm] using hw)
  have h := (terminal_work_below_hour n C M hn hC hM hCcard hratio).trans hdiv
  exact_mod_cast h

theorem exactZeroCount_le_mainCount (k : ℕ) (c : Cfg L 256) :
    exactZeroCount k c ≤ RoleSplitConcentration.mainCount c := by
  have hcount := clock_targets_le_mainCount (k + 1) c
  have hsplit := lowHourZeroCount_succ k c
  omega

theorem fuel_initial_ceiling_le_mainCount (k : ℕ) (A : ℚ)
    (n C : ℕ) (c : Cfg L 256) (hc : FuelGate k A n C c) :
    Nat.ceil (changingZeroFuel k c - A) ≤ RoleSplitConcentration.mainCount c := by
  classical
  exact (fuel_excess_le_targets k A n C c hc).trans
    (by rw [clockTarget_count]; exact clock_targets_le_mainCount k c)

theorem x_initial_ceiling_le_mainCount (σ : Sign) (k : ℕ)
    (Dstar : ℚ) (c : Cfg L 256) (hD : minorityDebt σ k c ≤ Dstar) :
    Nat.ceil (debtX σ k c - 2 * Dstar) ≤ RoleSplitConcentration.mainCount c := by
  apply Nat.ceil_le.mpr
  exact (le_max_left _ _).trans (debtX_excess_le_mainCount σ k c Dstar hD)

theorem y_initial_ceiling_le_mainCount (σ : Sign) (k : ℕ)
    (xstar : ℚ) (c : Cfg L 256) (hX : debtX σ k c ≤ xstar) :
    Nat.ceil (debtY σ k c - xstar) ≤ RoleSplitConcentration.mainCount c := by
  apply Nat.ceil_le.mpr
  have hfloor := debtY_service_floor σ k c xstar hX
  have hcount : (exactZeroCount k c : ℚ) ≤
      (RoleSplitConcentration.mainCount c : ℚ) := by
    exact_mod_cast exactZeroCount_le_mainCount k c
  exact (le_max_left _ _).trans (hfloor.trans hcount)

theorem changingZeroFuel_warmup_tail_at_pastTime (init : Cfg L 256)
    (τ : Ω L 256 → WithTop ℕ) (hτ : PhaseOneDrain.PairLogPastTime τ)
    (k : ℕ) (hk : k ≤ L) (A : ℚ)
    (n C M : ℕ) (hn : 2 ≤ n) (hC : 0 < C) (hroles : C + M ≤ n) :
    law init {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
        ω ∈ thresholdFailure init s (changingZeroFuel k) A
          (FuelGate k A n (warmClockCount C)) M (1 / 500) (clockWarmup n C)} ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) / 500)) := by
  have hsize := clockWarmup_size_bound n C M hn hroles
  have htail := stoppedDebt_tail_at_pastTime init τ hτ (changingZeroFuel k) A
    (FuelGate k A n (warmClockCount C)) M (clockDeathRate n (warmClockCount C))
    (1 / 500) (clockDeathRate_nonneg n (warmClockCount C))
    (clockDeathRate_size_bound n (warmClockCount C) M hn hsize)
    (fun c hc d hd => changingZeroFuel_draw_le k c hc.domain d hd.domain)
    (changingZeroFuel_service_probability k hk A n (warmClockCount C) hn)
    (clockWarmup n C)
  refine (measure_mono ?_).trans (htail.trans ?_)
  · rintro ω ⟨s, hs, hf⟩
    refine ⟨s, hs, ?_⟩
    simpa using thresholdFailure_subset init s _ _ _ M (1 / 500) _ hf
  · simpa only [neg_mul] using ENNReal.ofReal_le_ofReal
      (warmup_death_exponent (clockWarmup_rate n C hn hC) (Nat.cast_nonneg M))

theorem debtX_warmup_tail_at_pastTime (init : Cfg L 256)
    (τ : Ω L 256 → WithTop ℕ) (hτ : PhaseOneDrain.PairLogPastTime τ)
    (σ : Sign) (k : ℕ) (hk : k ≤ L) (Dstar : ℚ)
    (n C M : ℕ) (hn : 2 ≤ n) (hC : 0 < C) (hroles : C + M ≤ n) :
    law init {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
        ω ∈ thresholdFailure init s (debtX σ k) (2 * Dstar)
          (XGate σ k Dstar n (warmClockCount C)) M (1 / 500) (clockWarmup n C)} ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) / 500)) := by
  have htail := debtX_tail_at_pastTime init τ hτ σ k hk Dstar n (warmClockCount C) M hn
    (clockWarmup_size_bound n C M hn hroles) (1 / 500) (clockWarmup n C)
  refine (measure_mono ?_).trans (htail.trans ?_)
  · rintro ω ⟨s, hs, hf⟩
    refine ⟨s, hs, ?_⟩
    simpa using thresholdFailure_subset init s _ _ _ M (1 / 500) _ hf
  · simpa only [neg_mul] using ENNReal.ofReal_le_ofReal
      (warmup_death_exponent (clockWarmup_rate n C hn hC) (Nat.cast_nonneg M))

theorem debtY_service_tail_at_pastTime (init : Cfg L 256)
    (τ : Ω L 256 → WithTop ℕ) (hτ : PhaseOneDrain.PairLogPastTime τ)
    (σ : Sign) (ell : ℕ) (xstar : ℚ)
    (n M : ℕ) (hn : 3 ≤ n) (hM : 0 < M) (hmain : 25 * M ≤ 13 * n) :
    law init {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
        ω ∈ thresholdFailure init s (debtY σ (ell + 2)) xstar
          (YGate σ ell xstar n (majorityPartnerCount M)) M
          (1 / 1000) (majorityWork n M)} ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) / 600)) := by
  have htail := debtY_tail_at_pastTime init τ hτ σ ell xstar
    n (majorityPartnerCount M) M (by omega)
    (majorityWork_size_bound n M hn hmain) (1 / 1000) (majorityWork n M)
  refine (measure_mono ?_).trans (htail.trans ?_)
  · rintro ω ⟨s, hs, hf⟩
    refine ⟨s, hs, ?_⟩
    simpa using thresholdFailure_subset init s _ _ _ M (1 / 1000) _ hf
  · simpa only [neg_mul] using ENNReal.ofReal_le_ofReal
      (terminal_death_exponent (majorityWork_rate n M (by omega) hM) (Nat.cast_nonneg M))

open Classical in
/-- Every field is a current-configuration fact. The two-stage estimate below
intersects the event that these facts persist with the actual failure event. -/
structure TerminalGate (σ : Sign) (ell : ℕ) (Dstar : ℚ)
    (n C M : ℕ) (c : Cfg L 256) : Prop where
  population : c.card = n
  domain : PotentialDomain c
  main_count : RoleSplitConcentration.mainCount c = M
  minority : minorityDebt σ (ell + 2) c ≤ Dstar
  clocks : warmClockCount C ≤ c.countP (ClockServiceSource (ell + 2))
  partners : majorityPartnerCount M ≤ c.countP (NearMajority σ ell)

theorem TerminalGate.xGate {σ : Sign} {ell : ℕ} {Dstar : ℚ}
    {n C M : ℕ} {c : Cfg L 256} (hc : TerminalGate σ ell Dstar n C M c) :
    XGate σ (ell + 2) Dstar n (warmClockCount C) c :=
  ⟨hc.population, hc.domain, hc.minority, hc.clocks⟩

theorem TerminalGate.yGate {σ : Sign} {ell : ℕ} {Dstar xstar : ℚ}
    {n C M : ℕ} {c : Cfg L 256} (hc : TerminalGate σ ell Dstar n C M c)
    (hX : debtX σ (ell + 2) c ≤ xstar) :
    YGate σ ell xstar n (majorityPartnerCount M) c :=
  ⟨hc.population, hc.domain, hX, hc.partners⟩

def terminalFailure (init : Cfg L 256) (s : ℕ) (σ : Sign) (ell : ℕ)
    (Dstar : ℚ) (n C M : ℕ) : Set (Ω L 256) :=
  {ω | (∀ u, u ≤ clockWarmup n C + majorityWork n M →
      TerminalGate σ ell Dstar n C M (trace init ω (s + u))) ∧
    (7 / 200 : ℚ) * M <
      debtY σ (ell + 2) (trace init ω (s + (clockWarmup n C + majorityWork n M)))}

/-- The X and Y drains are composed at the real fixed offset. There is one
original-law prefix event, retained as a multiplicative factor throughout. -/
theorem terminal_two_drains_from (init : Cfg L 256) (s : ℕ)
    (B : Set ((i : Finset.Iic s) → Draw L 256))
    (σ : Sign) (ell : ℕ) (hk : ell + 2 ≤ L) (Dstar : ℚ)
    (n C M : ℕ) (hn : 3 ≤ n) (hC : 0 < C) (hM : 0 < M)
    (hroles : C + M ≤ n) (hmain : 25 * M ≤ 13 * n)
    (hD : Dstar ≤ (2 / 125 : ℚ) * M) :
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ terminalFailure init s σ ell Dstar n C M} ≤
      (ENNReal.ofReal (Real.exp (-(M : ℝ) / 500)) +
        ENNReal.ofReal (Real.exp (-(M : ℝ) / 600))) *
      law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B} := by
  let u := s + clockWarmup n C
  let Bnext : Set ((i : Finset.Iic u) → Draw L 256) :=
    {p | TraceDrain.restrictPrefix (by dsimp [u]; omega : s ≤ u) p ∈ B}
  let Efirst : Set (Ω L 256) :=
    {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
      ω ∈ thresholdFailure init s (debtX σ (ell + 2)) (2 * Dstar)
        (XGate σ (ell + 2) Dstar n (warmClockCount C)) M
        (1 / 500) (clockWarmup n C)}
  let Esecond : Set (Ω L 256) :=
    {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) u ω ∈ Bnext ∧
      ω ∈ thresholdFailure init u (debtY σ (ell + 2)) ((17 / 500 : ℚ) * M)
        (YGate σ ell ((17 / 500 : ℚ) * M) n (majorityPartnerCount M)) M
        (1 / 1000) (majorityWork n M)}
  have hprefix :
      {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) u ω ∈ Bnext} =
      {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B} := by
    ext ω
    rfl
  have hfirst := debtX_warmup_tail_from init s B σ (ell + 2) hk Dstar n C M
    (by omega) hC hroles
  have hsecond := debtY_service_tail_from init u Bnext σ ell ((17 / 500 : ℚ) * M)
    n M hn hM hmain
  rw [hprefix] at hsecond
  have hsubset :
      {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ terminalFailure init s σ ell Dstar n C M} ⊆ Efirst ∪ Esecond := by
    rintro ω ⟨hp, hwindow, hbad⟩
    have hgate (v : ℕ) (hsv : s ≤ v)
        (hv : v ≤ s + (clockWarmup n C + majorityWork n M)) :
        TerminalGate σ ell Dstar n C M (trace init ω v) := by
      have h := hwindow (v - s) (by omega)
      have he : s + (v - s) = v := by omega
      simpa only [he] using h
    have hstart := hgate s le_rfl (by omega)
    have hmid := hgate u (by dsimp [u]; omega) (by dsimp [u]; omega)
    have hXlive :
        DebtLive init s (debtX σ (ell + 2)) (2 * Dstar)
          (XGate σ (ell + 2) Dstar n (warmClockCount C)) M (clockWarmup n C) ω := by
      refine ⟨?_, fun v hv => (hwindow v (by omega)).xGate⟩
      simpa only [hstart.main_count] using
        x_initial_ceiling_le_mainCount σ (ell + 2) Dstar _ hstart.minority
    by_cases hXbad :
        2 * Dstar + (1 / 500 : ℚ) * M < debtX σ (ell + 2) (trace init ω u)
    · apply Or.inl
      exact ⟨hp, hXlive, hXbad⟩
    · have hXmid : debtX σ (ell + 2) (trace init ω u) ≤ (17 / 500 : ℚ) * M :=
        debtX_target_of_warmup hD (le_of_not_gt hXbad)
      have hXlater (v : ℕ) (hv : v ≤ majorityWork n M) :
          debtX σ (ell + 2) (trace init ω (u + v)) ≤ (17 / 500 : ℚ) * M := by
        apply (debtX_trace_le σ (ell + 2) init ω u (u + v) (by omega) ?_ ?_ ?_).trans hXmid
        · intro q huq hq a ha
          exact ((hgate q (by dsimp [u] at huq; omega) (by dsimp [u] at hq; omega)).domain a ha).range
        · intro q huq hq a ha
          exact ((hgate q (by dsimp [u] at huq; omega) (by dsimp [u] at hq; omega)).domain a ha).safe
        · intro q huq hq a ha
          exact ((hgate q (by dsimp [u] at huq; omega) (by dsimp [u] at hq; omega)).domain a ha).small_carrier
      have hYlive :
          DebtLive init u (debtY σ (ell + 2)) ((17 / 500 : ℚ) * M)
            (YGate σ ell ((17 / 500 : ℚ) * M) n (majorityPartnerCount M)) M
            (majorityWork n M) ω := by
        refine ⟨?_, ?_⟩
        · simpa only [hmid.main_count] using
            y_initial_ceiling_le_mainCount σ (ell + 2) ((17 / 500 : ℚ) * M) _ hXmid
        · intro v hv
          exact (hgate (u + v) (by dsimp [u]; omega) (by dsimp [u]; omega)).yGate
            (hXlater v hv)
      apply Or.inr
      refine ⟨?_, hYlive, ?_⟩
      · change TraceDrain.restrictPrefix _ (frestrictLe (π := fun _ : ℕ => Draw L 256) u ω) ∈ B
        rw [TraceDrain.restrictPrefix_frestrictLe]
        exact hp
      · have he : u + majorityWork n M =
            s + (clockWarmup n C + majorityWork n M) := by dsimp [u]; omega
        rw [he]
        linarith only [hbad]
  calc
    law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B ∧
        ω ∈ terminalFailure init s σ ell Dstar n C M} ≤
        law init Efirst + law init Esecond :=
      (measure_mono hsubset).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal (Real.exp (-(M : ℝ) / 500)) *
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B} +
        ENNReal.ofReal (Real.exp (-(M : ℝ) / 600)) *
          law init {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ B} :=
      add_le_add hfirst hsecond
    _ = _ := by rw [add_mul]


/-- The composed two-drain estimate at an arbitrary pair-log past time.
The disjoint genuine-time splice introduces no factor for the possible starts. -/
theorem terminal_two_drains_at_pastTime (init : Cfg L 256)
    (τ : Ω L 256 → WithTop ℕ) (hτ : PhaseOneDrain.PairLogPastTime τ)
    (σ : Sign) (ell : ℕ) (hk : ell + 2 ≤ L) (Dstar : ℚ)
    (n C M : ℕ) (hn : 3 ≤ n) (hC : 0 < C) (hM : 0 < M)
    (hroles : C + M ≤ n) (hmain : 25 * M ≤ 13 * n)
    (hD : Dstar ≤ (2 / 125 : ℚ) * M) :
    law init {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
        ω ∈ terminalFailure init s σ ell Dstar n C M} ≤
      ENNReal.ofReal (Real.exp (-(M : ℝ) / 500)) +
        ENNReal.ofReal (Real.exp (-(M : ℝ) / 600)) := by
  let E : Set (Ω L 256) := {ω | ∃ s : ℕ, τ ω = (s : WithTop ℕ) ∧
    ω ∈ terminalFailure init s σ ell Dstar n C M}
  apply PhaseThreeClockProducer.splice_of_local (law init) τ E _
    (fun s => (pairLogFiltration L 256).le s _ (hτ s))
  · rintro ω ⟨s, hs, _⟩
    rw [hs]
    exact WithTop.coe_ne_top
  · intro s
    have hτs := hτ s
    rw [pairLogFiltration_eq_comap] at hτs
    obtain ⟨A, hA, hEq⟩ := hτs
    have hmem (ω : Ω L 256) :
        frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A ↔
          τ ω = (s : WithTop ℕ) := by
      change ω ∈ (frestrictLe (π := fun _ : ℕ => Draw L 256) s) ⁻¹' A ↔
        ω ∈ {ω | τ ω = (s : WithTop ℕ)}
      rw [hEq]
    have hevent :
        E ∩ {ω | τ ω = (s : WithTop ℕ)} =
          {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A ∧
            ω ∈ terminalFailure init s σ ell Dstar n C M} := by
      ext ω
      constructor
      · rintro ⟨⟨r, hr, hb⟩, hs⟩
        have hrs : r = s := WithTop.coe_injective (hr.symm.trans hs)
        subst r
        exact ⟨(hmem ω).mpr hs, hb⟩
      · rintro ⟨ha, hb⟩
        have hs := (hmem ω).mp ha
        exact ⟨⟨s, hs, hb⟩, hs⟩
    rw [hevent]
    have hbound := terminal_two_drains_from init s A σ ell hk Dstar n C M
      hn hC hM hroles hmain hD
    simpa only [show {ω | frestrictLe (π := fun _ : ℕ => Draw L 256) s ω ∈ A} =
      {ω | τ ω = (s : WithTop ℕ)} from Set.ext hmem] using hbound

end Ripple.PopulationProtocol.ExactMajority.AveragingTerminalDebtDeadlines

end
