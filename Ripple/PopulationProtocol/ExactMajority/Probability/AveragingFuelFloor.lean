-- Ripple/PopulationProtocol/ExactMajority/Probability/AveragingFuelFloor.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.AveragingCreditClockBridge

/-!
# The current exact-hour zero floor after the changing-zero warmup

Every Main is charged either by F_h, by the exact-hour-h zero count, or by
the actual high-zero/deep-bias exception count. Pending Mains are included
in F_h, so no completion-of-activation premise is needed.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.AveragingFuelFloor

open TimeTheorem StageEventSpec P3DeterministicAlgebra
open AveragingMixedAlgebra AveragingMixedLedgers
open AveragingTerminalDebt AveragingCreditCount AveragingCreditClockBridge

variable {L K : ℕ}

theorem mainUnit_le_fuel_zero_exception (h : ℕ) (a : AgentState L K) :
    mainUnit a ≤ mainFuel h a +
      (exactZeroWeight h a : ℚ) + (exceptionWeight h a : ℚ) := by
  by_cases hm : a.role = .main
  · by_cases hp : a.phase.val < 3
    · have hn : (0 : ℚ) ≤ (2 : ℚ) ^ h * |prePhase4Mass a| := by positivity
      simp [mainUnit, mainFuel, hm, hp, exactZeroWeight, exceptionWeight] <;>
        linarith only [hn]
    · cases hb : a.bias with
      | zero =>
          by_cases hlo : a.hour.val < h
          · have hne : a.hour.val ≠ h := by omega
            have hhi : ¬ h < a.hour.val := by omega
            simp [mainUnit, mainFuel, hm, hp, hb, prePhase4Mass, Bias.toRat,
              exactZeroWeight, exceptionWeight, hlo, hne, hhi]
          · by_cases he : a.hour.val = h
            · simp [mainUnit, mainFuel, hm, hp, hb, prePhase4Mass, Bias.toRat,
                exactZeroWeight, exceptionWeight, hlo, he]
            · have hhi : h < a.hour.val := by omega
              simp [mainUnit, mainFuel, hm, hp, hb, prePhase4Mass, Bias.toRat,
                exactZeroWeight, exceptionWeight, hlo, he, hhi]
      | dyadic σ i =>
          have habs : |prePhase4Mass a| = weightQ i := by
            cases σ <;> simp [prePhase4Mass, hp, hb, Bias.toRat, weightQ, abs_div]
          by_cases hdeep : h < i.val
          · have hn : (0 : ℚ) ≤ (2 : ℚ) ^ h * weightQ i :=
              mul_nonneg (by positivity) (weightQ_nonneg i)
            simp [mainUnit, mainFuel, hm, hp, hb, exactZeroWeight,
              exceptionWeight, habs, hdeep] <;> linarith only [hn, weightQ_nonneg i]
          · have hone := scaled_weight_ge_one h i (by omega)
            simpa [mainUnit, mainFuel, hm, hp, hb, exactZeroWeight,
              exceptionWeight, habs, hdeep] using hone
  · simp [mainUnit, mainFuel, hm, exactZeroWeight, exceptionWeight]

theorem mainCount_le_fuel_zero_exception (h : ℕ) (c : Cfg L K) :
    (RoleSplitConcentration.mainCount c : ℚ) ≤ changingZeroFuel h c +
      (exactZeroCount h c : ℚ) + (exceptionCount h c : ℚ) := by
  induction c using Multiset.induction_on with
  | empty =>
      simp [RoleSplitConcentration.mainCount, changingZeroFuel,
        exactZeroCount, exceptionCount]
  | cons a c ih =>
      have ha := mainUnit_le_fuel_zero_exception h a
      rw [mainCount_cons_cast]
      simp only [changingZeroFuel, exactZeroCount, exceptionCount,
        Multiset.map_cons, Multiset.sum_cons, Nat.cast_add] at ih ⊢
      linarith only [ha, ih]

/-- .9956 is the exact remainder after .002 warmup loss and .0024 exceptions. -/
theorem exact_zero_floor (h M : ℕ) (c : Cfg L K) (r : ℚ)
    (hM : RoleSplitConcentration.mainCount c = M)
    (hfuel : changingZeroFuel h c ≤ (2 * r + 1 / 500) * M)
    (hexception : (exceptionCount h c : ℚ) ≤ (3 / 1250 : ℚ) * M) :
    (2489 / 2500 - 2 * r : ℚ) * M ≤ (exactZeroCount h c : ℚ) := by
  have hcount := mainCount_le_fuel_zero_exception h c
  rw [hM] at hcount
  nlinarith only [hcount, hfuel, hexception]

theorem exact_zero_floor_general (h M : ℕ) (c : Cfg L K) (r : ℚ)
    (hM : RoleSplitConcentration.mainCount c = M)
    (hfuel : changingZeroFuel h c ≤ (2 * r + 1 / 500) * M)
    (hexception : (exceptionCount h c : ℚ) ≤ (3 / 1250 : ℚ) * M)
    (hr : r ≤ (51 / 125 : ℚ)) :
    (17 / 100 : ℚ) * M ≤ (exactZeroCount h c : ℚ) := by
  have hfloor := exact_zero_floor h M c r hM hfuel hexception
  have hscaled := mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg M : (0 : ℚ) ≤ M)
  have hnonneg : (0 : ℚ) ≤ M := by positivity
  nlinarith only [hfloor, hscaled, hnonneg]

theorem exact_zero_floor_early (h M : ℕ) (c : Cfg L K)
    (hM : RoleSplitConcentration.mainCount c = M)
    (hfuel : changingZeroFuel h c ≤ (101 / 500 : ℚ) * M)
    (hexception : (exceptionCount h c : ℚ) ≤ (3 / 1250 : ℚ) * M) :
    (77 / 100 : ℚ) * M ≤ (exactZeroCount h c : ℚ) := by
  have hfloor := exact_zero_floor h M c (1 / 10) hM
    (by norm_num <;> exact hfuel) hexception
  have hnonneg : (0 : ℚ) ≤ M := by positivity
  nlinarith only [hfloor, hnonneg]

theorem clockHistory_exact_zero_floor {n : ℕ}
    {init : InputCfg n} {ω : InputLog n} {S T ρ v : ℕ}
    {w : ClockTimes init} (h : ClockHistory init ω S T ρ w)
    (hSv : S ≤ v) (hvρ : v < ρ) (k : ℕ)
    (hk : k ≤ PhaseThreeModel.Numeric.hourIndex n) (hv : v ≤ w.finish k)
    (r : ℚ)
    (hfuel : changingZeroFuel k (trace init ω v) ≤
      (2 * r + 1 / 500) * timeMainCount (trace init ω S)) :
    (2489 / 2500 - 2 * r : ℚ) * timeMainCount (trace init ω S) ≤
      (exactZeroCount k (trace init ω v) : ℚ) := by
  have hM : RoleSplitConcentration.mainCount (trace init ω v) =
      timeMainCount (trace init ω S) := by
    convert h.main_count v hSv hvρ using 1 <;>
      simp only [RoleSplitConcentration.mainCount, timeMainCount] <;> congr!
  exact exact_zero_floor k _ _ r hM hfuel
    (exceptionCount_bound_clockHistory h hSv hvρ k hk hv)

end Ripple.PopulationProtocol.ExactMajority.AveragingFuelFloor

end
