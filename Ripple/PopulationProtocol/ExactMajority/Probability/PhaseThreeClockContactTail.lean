import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockContactBridge
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockSeedTails

/-!
# The guarded contact-row tail (N12, step 4, PHASE3 P14 rows of §11)

The contact row of `PhaseThreeClockRows` (every seed Clock has fewer than `40 (H + 1)`
eligible contacts from its initialization to `cap + T_set`) is charged in §11 only on
the activation-good prefix intersected with front success: the local cap window must be
short (`tick_local`) and the cap must be reached (`capRow`). This file proves the
guarded tail

`law {∃ S T, seed at S, entry (S, T), activation/passage/shape/cap rows, ¬ contact row}
   ≤ 1 / n ^ 6 + 1 / n ^ 21`,

by the fibre decomposition over the seed time `s` and the seed Clock set `C`
(`seedClockPrefix`), the two passages of `PhaseThreeClockCapPassages` (the `n^{-6}`
row: P1 is negligible and P2 costs `C e^{-7.2 ln n}`) and the MGF bound of
`PhaseThreeClockContactMGF` for each of the `C ≤ n` Clocks (the `n^{-21}` row:
`2^{-40 H} e^{18 ln n}` per Clock), with the deterministic bridge
`PhaseThreeClockContactBridge.tagBad_of_guard`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators MeasureTheory ProbabilityTheory

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockContactTail

open TimeTheorem PairLog PairLogAuxiliary PhaseThreeClockVirtual
  PhaseThreeClockGatedLaw PhaseThreeClockGatedLevelOne PhaseThreeClockEmbedding
  PhaseThreeClockEmbeddingBridge PhaseThreeClockCore PhaseThreeClockRows
  PhaseThreeClockProductTails PhaseThreeScalar PhaseThreeClockPrefixTails
  PhaseThreeClockProbabilityFloors PhaseThreeClockRegime PhaseThreeClockCapSpread
  PhaseThreeClockCapPassages PhaseThreeClockContactMGF PhaseThreeClockContactBridge
  PhaseThreeClockProducer PhaseThreeClockSeedTails
open StageEventSpec hiding frontCount clockCount
open Classical

variable {n : ℕ} (init : InputCfg n)

/-! ## Numerics at the population threshold -/

section Numerics

/-- `ln n ≥ 2^29` and `n ≥ (ln n)^2 / 2` at the population threshold. -/
theorem log_facts (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) :
    (536870912 : ℝ) ≤ Real.log (n : ℝ) ∧ Real.exp (Real.log (n : ℝ)) = n ∧
      (Real.log (n : ℝ)) ^ 2 / 2 ≤ n := by
  have hpos : 0 < n := pos_of_threshold hn
  have hposR : (0 : ℝ) < n := by exact_mod_cast hpos
  obtain ⟨-, hx, -, -, -⟩ := PhaseThreeModel.Numeric.logarithmic_inputs hn
    (show (6 / 25 : ℝ) * n ≤ n by linarith) le_rfl
  clear hn
  refine ⟨hx, Real.exp_log hposR, ?_⟩
  have hq := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ Real.log n by linarith)
  rw [Real.exp_log hposR] at hq
  linarith [Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hpos)]

theorem log_le_hourIndex_mul (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) :
    Real.log (n : ℝ) ≤ (PhaseThreeModel.Numeric.hourIndex n : ℝ) * Real.log 2 := by
  clear hn
  rw [PhaseThreeModel.Numeric.hourIndex_eq_real_ceiling]
  have hl2 := PhaseThreeModel.Numeric.log_two_bounds
  have hpos : 0 < Real.log 2 := by linarith
  have h := Nat.le_ceil (Real.log (n : ℝ) / Real.log 2)
  have h2 := mul_le_mul_of_nonneg_right h hpos.le
  rwa [div_mul_cancel₀ _ hpos.ne'] at h2

/-- `(1/2)^{40 (H + 1)} ≤ e^{-40 ln n}`. -/
theorem half_pow_le (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) :
    ((1 / 2 : ℝ)) ^ (40 * (PhaseThreeModel.Numeric.hourIndex n + 1)) ≤
      Real.exp (-(40 * Real.log (n : ℝ))) := by
  have hH := log_le_hourIndex_mul hn
  clear hn
  have hl2 := PhaseThreeModel.Numeric.log_two_bounds
  rw [show ((1 / 2 : ℝ)) = Real.exp (Real.log (1 / 2)) by
    rw [Real.exp_log (by norm_num)], ← Real.exp_nat_mul, Real.exp_le_exp,
    Real.log_div (by norm_num) (by norm_num), Real.log_one]
  push_cast
  nlinarith

/-- `frontWidth C ≤ ln n / 2^20` for the seed Clock count. -/
theorem frontWidth_le_log (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) {C : ℕ}
    (hlo : 6 * n ≤ 25 * C) (hCn : C ≤ n) :
    (frontWidth C : ℝ) ≤ Real.log (n : ℝ) / 1048576 := by
  have hlo' : (6 / 25 : ℝ) * n ≤ C := by
    have : (6 : ℝ) * n ≤ 25 * C := by exact_mod_cast hlo
    linarith
  obtain ⟨-, hx, hCn', -, -⟩ := PhaseThreeModel.Numeric.logarithmic_inputs hn hlo'
    (by exact_mod_cast hCn)
  obtain ⟨-, hw1, hw2⟩ := PhaseThreeModel.Numeric.frontWidth_bounds hx
  have := hw1.trans hw2
  calc (frontWidth C : ℝ) ≤ Real.log (C : ℝ) / 1048576 := this
    _ ≤ Real.log (n : ℝ) / 1048576 := by
        apply div_le_div_of_nonneg_right hCn' (by norm_num)

/-- The P1 term: `e^{-0.47 C} ≤ (1/2) n^{-6}`. -/
theorem p1_term_le (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) {C : ℕ}
    (hlo : 6 * n ≤ 25 * C) :
    Real.exp (-(47 / 100) * C) ≤ 1 / 2 * Real.exp (-(6 * Real.log (n : ℝ))) := by
  obtain ⟨hL, hexp, hquad⟩ := log_facts hn
  clear hn
  set L := Real.log (n : ℝ) with hLdef
  have hlo' : (6 : ℝ) * n ≤ 25 * C := by exact_mod_cast hlo
  have hl2 := PhaseThreeModel.Numeric.log_two_bounds
  rw [show (1 / 2 : ℝ) = Real.exp (-Real.log 2) by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num, ← Real.exp_add, Real.exp_le_exp]
  nlinarith

/-- The P2 term: `C e^{-p · finWindow} ≤ (1/2) n^{-6}` with `p` the hit rate. -/
theorem p2_term_le (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (hcard : init.card = n) (C : Finset (Fin init.card))
    (hlo : 6 * n ≤ 25 * C.card) (hCn : C.card ≤ n) :
    (C.card : ℝ) * Real.exp (-(hitRate init (highThreshold C.card) * finWindow n C.card)) ≤
      1 / 2 * Real.exp (-(6 * Real.log (n : ℝ))) := by
  obtain ⟨hL, hexp, hquad⟩ := log_facts hn
  clear hn
  have hcardR : (init.card : ℝ) = n := by exact_mod_cast hcard
  set L := Real.log (n : ℝ) with hLdef
  have hlo' : (6 : ℝ) * n ≤ 25 * C.card := by exact_mod_cast hlo
  have hCn' : (C.card : ℝ) ≤ n := by exact_mod_cast hCn
  have hnR : (2 : ℝ) ^ 57 ≤ n := by nlinarith
  have hCpos : (0 : ℝ) < C.card := by nlinarith
  have hl2 := PhaseThreeModel.Numeric.log_two_bounds
  -- the exponent is at least `7.2 L`
  have hrate : (72 / 10 : ℝ) * L ≤ hitRate init (highThreshold C.card) * finWindow n C.card := by
    unfold hitRate finWindow
    rw [hcardR]
    have hh : (9 * (C.card : ℝ) / 10) ≤ (highThreshold C.card : ℝ) := by
      unfold highThreshold
      exact Nat.le_ceil _
    have hf : 4 * (n : ℝ) ^ 2 * L / C.card ≤
        (Nat.ceil (4 * (n : ℝ) ^ 2 * Real.log (n : ℝ) / (C.card : ℝ)) : ℝ) := Nat.le_ceil _
    have hP : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    have h1 : 2 * (9 * (C.card : ℝ) / 10) / ((n : ℝ) * ((n : ℝ) - 1)) ≤
        2 * (highThreshold C.card : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) :=
      div_le_div_of_nonneg_right (by linarith) hP.le
    have hkey : 2 * (9 * (C.card : ℝ) / 10) / ((n : ℝ) * ((n : ℝ) - 1)) *
        (4 * (n : ℝ) ^ 2 * L / C.card) = (72 / 10) * L * ((n : ℝ) / ((n : ℝ) - 1)) := by
      field_simp
      ring
    have hfrac : (1 : ℝ) ≤ (n : ℝ) / ((n : ℝ) - 1) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    calc (72 / 10 : ℝ) * L ≤ (72 / 10) * L * ((n : ℝ) / ((n : ℝ) - 1)) := by
          have : (0 : ℝ) ≤ (72 / 10) * L := by positivity
          nlinarith
      _ = _ := hkey.symm
      _ ≤ _ := mul_le_mul h1 hf (by positivity) (by positivity)
  calc (C.card : ℝ) * Real.exp (-(hitRate init (highThreshold C.card) * finWindow n C.card))
      ≤ Real.exp L * Real.exp (-((72 / 10) * L)) := by
        apply mul_le_mul
        · rw [hexp]; exact_mod_cast hCn
        · rw [Real.exp_le_exp]; linarith
        · exact Real.exp_nonneg _
        · exact Real.exp_nonneg _
    _ = Real.exp (-(6 * L)) * Real.exp (-((2 / 10) * L)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
    _ ≤ 1 / 2 * Real.exp (-(6 * L)) := by
        rw [mul_comm]
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        rw [show (1 / 2 : ℝ) = Real.exp (-Real.log 2) by
          rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num, Real.exp_le_exp]
        nlinarith

/-- The MGF term for one Clock, times the number of Clocks: at most `n^{-21}`. -/
theorem mgf_term_le (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (hcard : init.card = n) (C : Finset (Fin init.card))
    (hlo : 6 * n ≤ 25 * C.card) (hhi : 25 * C.card ≤ 7 * n) (hCn : C.card ≤ n) :
    (C.card : ℝ) * ((1 / 2 : ℝ) ^ (40 * (PhaseThreeModel.Numeric.hourIndex n + 1)) *
      ((C.card : ℝ) + 2) ^ (localTickBudget C.card + 13 * C.card) /
        (C.card : ℝ) ^ (localTickBudget C.card + 13 * C.card) *
      Real.exp (tagRate init C * (finWindow n C.card + logWindow n 16))) ≤
      Real.exp (-(21 * Real.log (n : ℝ))) := by
  obtain ⟨hL, hexp, hquad⟩ := log_facts hn
  have hw := frontWidth_le_log hn hlo hCn
  have hhalf := half_pow_le hn
  have hcardR : (init.card : ℝ) = n := by exact_mod_cast hcard
  clear hn
  set L := Real.log (n : ℝ) with hLdef
  have hlo' : (6 : ℝ) * n ≤ 25 * C.card := by exact_mod_cast hlo
  have hhi' : 25 * (C.card : ℝ) ≤ 7 * n := by exact_mod_cast hhi
  have hCn' : (C.card : ℝ) ≤ n := by exact_mod_cast hCn
  have hnR : (2 : ℝ) ^ 57 ≤ n := by nlinarith
  have hCpos : (0 : ℝ) < C.card := by nlinarith
  set c : ℝ := (C.card : ℝ) with hc
  set R₁ : ℕ := localTickBudget C.card + 13 * C.card with hR₁
  -- the Clock-pair compensation
  have hR₁R : (R₁ : ℝ) = 200 * (frontWidth C.card : ℝ) * c + 13 * c := by
    rw [hR₁]
    unfold localTickBudget
    push_cast
    ring
  have hdisc : ((c + 2) ^ R₁ / c ^ R₁ : ℝ) ≤ Real.exp (L / 1000) := by
    rw [← div_pow, show (c + 2) / c = Real.exp (Real.log ((c + 2) / c)) by
      rw [Real.exp_log (by positivity)], ← Real.exp_nat_mul, Real.exp_le_exp]
    have hlog : Real.log ((c + 2) / c) ≤ 2 / c := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (c + 2) / c by positivity)
      have e : (c + 2) / c - 1 = 2 / c := by field_simp; ring
      linarith
    have hR₁pos : (0 : ℝ) ≤ R₁ := Nat.cast_nonneg _
    calc (R₁ : ℝ) * Real.log ((c + 2) / c) ≤ (R₁ : ℝ) * (2 / c) :=
          mul_le_mul_of_nonneg_left hlog hR₁pos
      _ = 400 * (frontWidth C.card : ℝ) + 26 := by
          rw [hR₁R]
          field_simp
          ring
      _ ≤ L / 1000 := by nlinarith
  -- the time compensation
  have hq : tagRate init C * (finWindow n C.card + logWindow n 16) ≤ 17 * L := by
    unfold tagRate
    rw [hcardR]
    have hP : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    have hrate : 2 * (c - 1) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 2 * c / ((n : ℝ) * ((n : ℝ) - 1)) :=
      div_le_div_of_nonneg_right (by linarith) hP.le
    have hfin : (finWindow n C.card : ℝ) ≤ 4 * (n : ℝ) ^ 2 * L / c + 1 := by
      unfold finWindow
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have hlw : (logWindow n 16 : ℝ) ≤ 16 * (n : ℝ) * L + 1 := by
      unfold logWindow
      push_cast
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have hD : (finWindow n C.card : ℝ) + logWindow n 16 ≤ 4 * (n : ℝ) ^ 2 * L / c + 16 * n * L + 2 := by
      linarith
    have hrate0 : (0 : ℝ) ≤ 2 * (c - 1) / ((n : ℝ) * ((n : ℝ) - 1)) := by
      apply div_nonneg (by linarith) hP.le
    have hD0 : (0 : ℝ) ≤ (finWindow n C.card : ℝ) + logWindow n 16 := by positivity
    have hkey : 2 * c / ((n : ℝ) * ((n : ℝ) - 1)) * (4 * (n : ℝ) ^ 2 * L / c + 16 * n * L + 2) =
        (8 * n * L + 32 * c * L + 4 * c / n) / ((n : ℝ) - 1) := by
      field_simp
      ring
    have hbound : (8 * n * L + 32 * c * L + 4 * c / n) / ((n : ℝ) - 1) ≤ 17 * L := by
      rw [div_le_iff₀ (by linarith)]
      have h4 : 4 * c / (n : ℝ) ≤ 4 := by
        rw [div_le_iff₀ (by linarith)]
        linarith
      have hcL : 32 * c * L ≤ (224 / 25) * n * L := by
        have : (0 : ℝ) ≤ L := by linarith
        nlinarith
      have hnL : (2 : ℝ) ^ 57 * L ≤ n * L := mul_le_mul_of_nonneg_right hnR (by linarith)
      nlinarith
    calc 2 * (c - 1) / ((n : ℝ) * ((n : ℝ) - 1)) * ((finWindow n C.card : ℝ) + logWindow n 16)
        ≤ 2 * c / ((n : ℝ) * ((n : ℝ) - 1)) * (4 * (n : ℝ) ^ 2 * L / c + 16 * n * L + 2) :=
          mul_le_mul hrate hD hD0 (by positivity)
      _ = _ := hkey
      _ ≤ 17 * L := hbound
  calc c * ((1 / 2 : ℝ) ^ (40 * (PhaseThreeModel.Numeric.hourIndex n + 1)) *
        (c + 2) ^ R₁ / c ^ R₁ *
        Real.exp (tagRate init C * (finWindow n C.card + logWindow n 16)))
      = c * ((1 / 2 : ℝ) ^ (40 * (PhaseThreeModel.Numeric.hourIndex n + 1)) *
        ((c + 2) ^ R₁ / c ^ R₁) *
        Real.exp (tagRate init C * (finWindow n C.card + logWindow n 16))) := by ring
    _ ≤ Real.exp L * (Real.exp (-(40 * L)) * Real.exp (L / 1000) * Real.exp (17 * L)) := by
        apply mul_le_mul
        · rw [hexp]; exact hCn'
        · apply mul_le_mul (mul_le_mul hhalf hdisc (by positivity) (Real.exp_nonneg _))
            (Real.exp_le_exp.mpr hq) (Real.exp_nonneg _) (by positivity)
        · positivity
        · exact Real.exp_nonneg _
    _ = Real.exp (L + (-(40 * L) + L / 1000 + 17 * L)) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_add]
    _ ≤ Real.exp (-(21 * L)) := by
        rw [Real.exp_le_exp]
        nlinarith

/-- `e^{-6 ln n} = 1 / n^6` and `e^{-21 ln n} = 1 / n^21`. -/
theorem exp_neg_mul_log (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n) (k : ℕ) :
    Real.exp (-((k : ℝ) * Real.log (n : ℝ))) = 1 / (n : ℝ) ^ k := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast pos_of_threshold hn
  rw [show -((k : ℝ) * Real.log (n : ℝ)) = (k : ℕ) * (-Real.log (n : ℝ)) by ring,
    Real.exp_nat_mul, Real.exp_neg, Real.exp_log hpos, inv_pow, one_div]

/-- The three fibre terms sum to the P14 budget. -/
theorem contact_fibre_budget (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (hcard : init.card = n) (C : Finset (Fin init.card))
    (hlo : 6 * n ≤ 25 * C.card) (hhi : 25 * C.card ≤ 7 * n) (hCn : C.card ≤ n) :
    Real.exp (-(47 / 100) * C.card) +
      (C.card : ℝ) * Real.exp (-(hitRate init (highThreshold C.card) * finWindow n C.card)) +
      (C.card : ℝ) * ((1 / 2 : ℝ) ^ (40 * (PhaseThreeModel.Numeric.hourIndex n + 1)) *
        ((C.card : ℝ) + 2) ^ (localTickBudget C.card + 13 * C.card) /
          (C.card : ℝ) ^ (localTickBudget C.card + 13 * C.card) *
        Real.exp (tagRate init C * (finWindow n C.card + logWindow n 16))) ≤
      1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21 := by
  have h1 := p1_term_le hn hlo
  have h2 := p2_term_le init hn hcard C hlo hCn
  have h3 := mgf_term_le init hn hcard C hlo hhi hCn
  have e6 := exp_neg_mul_log hn 6
  have e21 := exp_neg_mul_log hn 21
  clear hn
  push_cast at e6 e21
  rw [e6] at h1 h2
  rw [e21] at h3
  linarith

end Numerics

/-! ## The fibres -/

/-- The fibre: the genuine first Phase-3 seed at `s` with its profile, and the seed Clock
label set `C`, which then has the seed density. -/
def seedClockPrefix (s : ℕ) (C : Finset (Fin init.card)) : Set (InputLog n) :=
  {ω | seedTime init 3 ω = (s : WithTop ℕ) ∧ SeedProfile n init (trace init ω s) ∧
    clockSet (virtualLabels init ω s) = C ∧ 6 * n ≤ 25 * C.card ∧ 25 * C.card ≤ 7 * n ∧
    C.card ≤ n}

theorem seedClockPrefix_measurableSet (s : ℕ) (C : Finset (Fin init.card)) :
    MeasurableSet[pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 s]
      (seedClockPrefix init s C) := by
  by_cases hdens : 6 * n ≤ 25 * C.card ∧ 25 * C.card ≤ 7 * n ∧ C.card ≤ n
  · have hset : seedClockPrefix init s C =
        seedPrefix init s ∩ {ω | clockSet (virtualLabels init ω s) = C} := by
      ext ω
      simp only [seedClockPrefix, seedPrefix, Set.mem_setOf_eq, Set.mem_inter_iff, hdens.1,
        hdens.2.1, hdens.2.2, and_true, and_assoc]
    rw [hset]
    exact (seedPrefix_measurable init s).inter
      (measurableSet_virtual_single init le_rfl (fun f => clockSet f = C))
  · have hset : seedClockPrefix init s C = ∅ := by
      ext ω
      simp only [seedClockPrefix, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, -, -, h1, h2, h3⟩
      exact hdens ⟨h1, h2, h3⟩
    rw [hset]
    exact @MeasurableSet.empty _ (pairLogFiltration (PhaseThreeModel.Numeric.hourIndex n) 256 s)

theorem seedClockPrefix_disjoint {a b : ℕ × Finset (Fin init.card)} (hab : a ≠ b) :
    Disjoint (seedClockPrefix init a.1 a.2) (seedClockPrefix init b.1 b.2) := by
  rw [Set.disjoint_left]
  rintro ω ⟨ha1, -, ha3, -, -, -⟩ ⟨hb1, -, hb3, -, -, -⟩
  have hs : a.1 = b.1 := by
    have := ha1.symm.trans hb1
    exact_mod_cast this
  apply hab
  apply Prod.ext hs
  rw [← ha3, ← hb3, hs]

/-- The guarded failure of the contact row. -/
def guardedContactFailure : Set (InputLog n) :=
  {ω | ∃ S T : ℕ, seedTime init 3 ω = (S : WithTop ℕ) ∧ T ≤ earlyHorizon n ∧
    AsyncEntry init ω S T ∧ activationRow init ω S T ∧ passageRow init ω S T ∧
    shapeRow init ω S T ∧ capRow init ω S T ∧ ¬ contactRow init ω S T}

/-- The horizon of the fibre `C`. -/
def fibreHorizon (C : Finset (Fin init.card)) : ℕ :=
  logWindow n 20000 + finWindow n C.card + logWindow n 16

/-- The bad event of the fibre `(s, C)`: the two passages or some Clock's MGF event. -/
def fibreBad (s : ℕ) (C : Finset (Fin init.card)) : Set (InputLog n) :=
  bulkHighBad init C s (fibreHorizon init C) ∪
    ((⋃ j ∈ C, highAllBad init (highThreshold C.card) s s (finWindow n C.card) j (fibreHorizon init C)) ∪
      ⋃ i₀ ∈ C, tagBad init C s i₀ (logWindow n 16) (fibreHorizon init C)
        (40 * (PhaseThreeModel.Numeric.hourIndex n + 1))
        (localTickBudget C.card + 13 * C.card) (finWindow n C.card + logWindow n 16))

/-- The guarded failure lies in the union of the fibre bad events. -/
theorem guardedContactFailure_subset (hn : PhaseThreeModel.Numeric.populationThreshold ≤ n)
    (hcard : init.card = n) :
    guardedContactFailure init ⊆
      ⋃ sC : ℕ × Finset (Fin init.card), seedClockPrefix init sC.1 sC.2 ∩ fibreBad init sC.1 sC.2 := by
  rintro ω ⟨s, T, hs, -, hentry, hact, hpass, hshape, hcap, hnot⟩
  set C := clockSet (virtualLabels init ω s) with hC
  have hdens := seed_clock_density init ω hentry
  have hupper : 25 * clockCount (virtualLabels init ω s) ≤ 7 * n := by
    have h := (seed_density init ω hentry).2.2.2.1
    rw [← virtualCfg_clockCount_eq_seed init ω hentry s le_rfl, clockCount_virtualCfg_eq] at h
    exact h
  have hle : C.card ≤ n := by
    have h : C.card ≤ init.card := seed_clock_le init ω (s := s)
    omega
  have hmem : ω ∈ seedClockPrefix init s C :=
    ⟨hs, hentry.seed_profile, rfl, hdens, hupper, hle⟩
  refine Set.mem_iUnion.mpr ⟨(s, C), hmem, ?_⟩
  by_cases hP1 : ω ∈ bulkHighBad init C s (fibreHorizon init C)
  · exact Or.inl hP1
  by_cases hP2 : ∃ j ∈ C, ω ∈ highAllBad init (highThreshold C.card) s s (finWindow n C.card) j (fibreHorizon init C)
  · obtain ⟨j, hj, hjbad⟩ := hP2
    exact Or.inr (Or.inl (Set.mem_iUnion₂.mpr ⟨j, hj, hjbad⟩))
  push_neg at hP2
  obtain ⟨i₀, hi₀, hbad⟩ := tagBad_of_guard init ω hentry C hC (fibreHorizon init C) hn hcard
    hact hpass hshape hcap hnot le_rfl hP1 hP2
  exact Or.inr (Or.inr (Set.mem_iUnion₂.mpr ⟨i₀, hi₀, hbad⟩))

/-- The fibre estimate. -/
theorem fibre_tail (hinput : ThresholdEpidemic.GoodInput n init) (s : ℕ)
    (C : Finset (Fin init.card)) :
    law init (seedClockPrefix init s C ∩ fibreBad init s C) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21) * law init (seedClockPrefix init s C) := by
  have hn : PhaseThreeModel.Numeric.populationThreshold ≤ n :=
    (time_population_bounds hinput.1).1
  have h40 : 40 ≤ n := (time_population_bounds hinput.1).2
  have hcard : init.card = n := hinput.2.2
  have hc : 2 ≤ init.card := by omega
  by_cases hdens : 6 * n ≤ 25 * C.card ∧ 25 * C.card ≤ 7 * n ∧ C.card ≤ n
  · obtain ⟨hlo, hhi, hCn⟩ := hdens
    have hC1 : 1 ≤ C.card := by omega
    have hE := seedClockPrefix_measurableSet init s C
    set E := seedClockPrefix init s C with hEdef
    set N := fibreHorizon init C with hN
    -- the hit rate is below one
    have hbudget := contact_fibre_budget init hn hcard C hlo hhi hCn
    have hcardR : (init.card : ℝ) = n := by exact_mod_cast hcard
    clear hn
    have hp : hitRate init (highThreshold C.card) < 1 := by
      unfold hitRate
      rw [hcardR]
      have hnR : (40 : ℝ) ≤ n := by exact_mod_cast h40
      have hh : (highThreshold C.card : ℝ) ≤ n := by
        have := (highThreshold_le_card C.card).trans hCn
        exact_mod_cast this
      rw [div_lt_one (by nlinarith)]
      nlinarith
    have h1 := bulk_high_tail init C s hc N E hE
    have h2 : ∀ j ∈ C, law init (E ∩ highAllBad init (highThreshold C.card) s s (finWindow n C.card) j N) ≤
        ENNReal.ofReal (Real.exp (-(hitRate init (highThreshold C.card) * finWindow n C.card))) * law init E :=
      fun j _ => high_all_tail init (highThreshold C.card) s s (finWindow n C.card) j hc hp N E hE
    have h3 : ∀ i₀ ∈ C, law init (E ∩ tagBad init C s i₀ (logWindow n 16) N
        (40 * (PhaseThreeModel.Numeric.hourIndex n + 1))
        (localTickBudget C.card + 13 * C.card) (finWindow n C.card + logWindow n 16)) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (40 * (PhaseThreeModel.Numeric.hourIndex n + 1)) *
          ((C.card : ℝ) + 2) ^ (localTickBudget C.card + 13 * C.card) /
            (C.card : ℝ) ^ (localTickBudget C.card + 13 * C.card) *
          Real.exp (tagRate init C * ((finWindow n C.card + logWindow n 16 : ℕ) : ℝ))) *
          law init E :=
      fun i₀ _ => tag_budget_tail init C s i₀ hc hC1 (logWindow n 16) N _ _ _ E hE
    -- the union bound in the fibre
    have hunion : law init (E ∩ fibreBad init s C) ≤
        law init (E ∩ bulkHighBad init C s N) +
          (∑ j ∈ C, law init (E ∩ highAllBad init (highThreshold C.card) s s (finWindow n C.card) j N) +
            ∑ i₀ ∈ C, law init (E ∩ tagBad init C s i₀ (logWindow n 16) N
              (40 * (PhaseThreeModel.Numeric.hourIndex n + 1))
              (localTickBudget C.card + 13 * C.card) (finWindow n C.card + logWindow n 16))) := by
      unfold fibreBad
      rw [Set.inter_union_distrib_left, Set.inter_union_distrib_left]
      refine (measure_union_le _ _).trans (add_le_add le_rfl ?_)
      refine (measure_union_le _ _).trans (add_le_add ?_ ?_)
      · rw [Set.inter_iUnion₂]
        exact measure_biUnion_finset_le _ _
      · rw [Set.inter_iUnion₂]
        exact measure_biUnion_finset_le _ _
    have hsum2 : ∑ j ∈ C, law init (E ∩ highAllBad init (highThreshold C.card) s s (finWindow n C.card) j N) ≤
        ENNReal.ofReal ((C.card : ℝ) * Real.exp (-(hitRate init (highThreshold C.card) * finWindow n C.card))) *
          law init E := by
      calc ∑ j ∈ C, law init (E ∩ highAllBad init (highThreshold C.card) s s (finWindow n C.card) j N)
          ≤ ∑ _j ∈ C, ENNReal.ofReal (Real.exp (-(hitRate init (highThreshold C.card) * finWindow n C.card))) *
              law init E := Finset.sum_le_sum h2
        _ = (C.card : ℝ≥0∞) * (ENNReal.ofReal (Real.exp (-(hitRate init (highThreshold C.card) * finWindow n C.card))) *
              law init E) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = _ := by
            rw [← mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    have hsum3 : ∑ i₀ ∈ C, law init (E ∩ tagBad init C s i₀ (logWindow n 16) N
        (40 * (PhaseThreeModel.Numeric.hourIndex n + 1))
        (localTickBudget C.card + 13 * C.card) (finWindow n C.card + logWindow n 16)) ≤
        ENNReal.ofReal ((C.card : ℝ) * ((1 / 2 : ℝ) ^ (40 * (PhaseThreeModel.Numeric.hourIndex n + 1)) *
          ((C.card : ℝ) + 2) ^ (localTickBudget C.card + 13 * C.card) /
            (C.card : ℝ) ^ (localTickBudget C.card + 13 * C.card) *
          Real.exp (tagRate init C * ((finWindow n C.card + logWindow n 16 : ℕ) : ℝ)))) *
          law init E := by
      calc ∑ i₀ ∈ C, law init (E ∩ tagBad init C s i₀ (logWindow n 16) N
            (40 * (PhaseThreeModel.Numeric.hourIndex n + 1))
            (localTickBudget C.card + 13 * C.card) (finWindow n C.card + logWindow n 16))
          ≤ ∑ _i₀ ∈ C, ENNReal.ofReal ((1 / 2 : ℝ) ^ (40 * (PhaseThreeModel.Numeric.hourIndex n + 1)) *
              ((C.card : ℝ) + 2) ^ (localTickBudget C.card + 13 * C.card) /
                (C.card : ℝ) ^ (localTickBudget C.card + 13 * C.card) *
              Real.exp (tagRate init C * ((finWindow n C.card + logWindow n 16 : ℕ) : ℝ))) *
              law init E := Finset.sum_le_sum h3
        _ = (C.card : ℝ≥0∞) * (ENNReal.ofReal ((1 / 2 : ℝ) ^ (40 * (PhaseThreeModel.Numeric.hourIndex n + 1)) *
              ((C.card : ℝ) + 2) ^ (localTickBudget C.card + 13 * C.card) /
                (C.card : ℝ) ^ (localTickBudget C.card + 13 * C.card) *
              Real.exp (tagRate init C * ((finWindow n C.card + logWindow n 16 : ℕ) : ℝ))) *
              law init E) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = _ := by
            rw [← mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    have hcastD : ((finWindow n C.card + logWindow n 16 : ℕ) : ℝ) =
        (finWindow n C.card : ℝ) + logWindow n 16 := by push_cast; ring
    rw [hcastD] at hsum3
    have ha : (0 : ℝ) ≤ Real.exp (-(47 / 100) * C.card) := Real.exp_nonneg _
    have hb : (0 : ℝ) ≤ (C.card : ℝ) * Real.exp (-(hitRate init (highThreshold C.card) * finWindow n C.card)) := by
      positivity
    have hc' : (0 : ℝ) ≤ (C.card : ℝ) * ((1 / 2 : ℝ) ^ (40 * (PhaseThreeModel.Numeric.hourIndex n + 1)) *
        ((C.card : ℝ) + 2) ^ (localTickBudget C.card + 13 * C.card) /
          (C.card : ℝ) ^ (localTickBudget C.card + 13 * C.card) *
        Real.exp (tagRate init C * (finWindow n C.card + logWindow n 16))) := by positivity
    calc law init (E ∩ fibreBad init s C)
        ≤ _ := hunion
      _ ≤ ENNReal.ofReal (Real.exp (-(47 / 100) * C.card)) * law init E +
          (ENNReal.ofReal ((C.card : ℝ) * Real.exp (-(hitRate init (highThreshold C.card) * finWindow n C.card))) *
            law init E +
          ENNReal.ofReal ((C.card : ℝ) *
            ((1 / 2 : ℝ) ^ (40 * (PhaseThreeModel.Numeric.hourIndex n + 1)) *
            ((C.card : ℝ) + 2) ^ (localTickBudget C.card + 13 * C.card) /
              (C.card : ℝ) ^ (localTickBudget C.card + 13 * C.card) *
            Real.exp (tagRate init C * (finWindow n C.card + logWindow n 16)))) * law init E) :=
          add_le_add h1 (add_le_add hsum2 hsum3)
      _ = ENNReal.ofReal (Real.exp (-(47 / 100) * C.card) +
          ((C.card : ℝ) * Real.exp (-(hitRate init (highThreshold C.card) * finWindow n C.card)) +
          (C.card : ℝ) * ((1 / 2 : ℝ) ^ (40 * (PhaseThreeModel.Numeric.hourIndex n + 1)) *
            ((C.card : ℝ) + 2) ^ (localTickBudget C.card + 13 * C.card) /
              (C.card : ℝ) ^ (localTickBudget C.card + 13 * C.card) *
            Real.exp (tagRate init C * (finWindow n C.card + logWindow n 16))))) * law init E := by
          rw [ENNReal.ofReal_add ha (add_nonneg hb hc'), ENNReal.ofReal_add hb hc']
          ring
      _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21) * law init E := by
          apply mul_le_mul_right'
          apply ENNReal.ofReal_le_ofReal
          linarith
  · have hempty : seedClockPrefix init s C = ∅ := by
      ext ω
      simp only [seedClockPrefix, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨-, -, -, h1, h2, h3⟩
      exact hdens ⟨h1, h2, h3⟩
    rw [hempty]
    simp

/-- The guarded contact-row tail: the P14 rows of PHASE3 §11, `n^{-6} + n^{-21}`. -/
theorem guarded_contact_tail (hinput : ThresholdEpidemic.GoodInput n init) :
    law init (guardedContactFailure init) ≤
      ENNReal.ofReal (1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21) := by
  have hn : PhaseThreeModel.Numeric.populationThreshold ≤ n :=
    (time_population_bounds hinput.1).1
  have hcard : init.card = n := hinput.2.2
  have hdisj : Pairwise (Function.onFun Disjoint
      fun sC : ℕ × Finset (Fin init.card) => seedClockPrefix init sC.1 sC.2) :=
    fun a b hab => seedClockPrefix_disjoint init hab
  have hmeas : ∀ sC : ℕ × Finset (Fin init.card), MeasurableSet (seedClockPrefix init sC.1 sC.2) :=
    fun sC => (pairLogFiltration _ _).le _ _ (seedClockPrefix_measurableSet init sC.1 sC.2)
  have hsum : ∑' sC : ℕ × Finset (Fin init.card), law init (seedClockPrefix init sC.1 sC.2) ≤ 1 := by
    rw [← measure_iUnion hdisj hmeas]
    exact prob_le_one
  calc law init (guardedContactFailure init)
      ≤ law init (⋃ sC : ℕ × Finset (Fin init.card),
          seedClockPrefix init sC.1 sC.2 ∩ fibreBad init sC.1 sC.2) :=
        measure_mono (guardedContactFailure_subset init hn hcard)
    _ ≤ ∑' sC : ℕ × Finset (Fin init.card),
          law init (seedClockPrefix init sC.1 sC.2 ∩ fibreBad init sC.1 sC.2) :=
        measure_iUnion_le _
    _ ≤ ∑' sC : ℕ × Finset (Fin init.card),
          ENNReal.ofReal (1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21) *
            law init (seedClockPrefix init sC.1 sC.2) :=
        ENNReal.tsum_le_tsum (fun sC => fibre_tail init hinput sC.1 sC.2)
    _ = ENNReal.ofReal (1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21) *
          ∑' sC : ℕ × Finset (Fin init.card), law init (seedClockPrefix init sC.1 sC.2) :=
        ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21) * 1 := mul_le_mul_right hsum _
    _ = ENNReal.ofReal (1 / (n : ℝ) ^ 6 + 1 / (n : ℝ) ^ 21) := mul_one _

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockContactTail

end
