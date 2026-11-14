-- Ripple/PopulationProtocol/ExactMajority/Probability/LateBiasedResourceCredit.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingCorrectedFuelProducer
import Ripple.PopulationProtocol.ExactMajority.Probability.LateMixedFuelLedger
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6BlockSnapshot

/-!
# The Lemma-11 biased-population credit: definitions and entry arithmetic

The excluded sign `sigma` is the minority sign.  Thus
`majorityBlockCount sigma ell` counts majority Mains in
`ell, ell+1, ell+2`, while `minorityDebt sigma ell` is `Dminus` through
`p = ell+4`.

Theorem list:
* `four_mul_minoritySplitDebt_le_minorityDebt`
* `biasedMainCount_le_mainCount`
* `lateBiasedResourceCredit_initialFloor`
* `phaseSixEntry_preserves_credit_fields`
* `lateBiasedResourceAtom_phaseSixEntry_eq`

Covers the initial floor and the Init-6 part of the Phase-6 dispatch.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateBiasedResourceCredit

open Phase7BandDefs
open Phase7MajorityBlockLedger
open Phase6BlockSnapshot
open scoped BigOperators

variable {L K : ℕ}

/-- `k = ell + 2`. -/
def middleIndex (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L) : Fin (L + 1) :=
  ⟨ell.val + 2, by omega⟩

@[simp] theorem middleIndex_val
    (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L) :
    (middleIndex ell hell).val = ell.val + 2 := rfl

/-- One unit for every current biased Main, including a converted Reserve. -/
def biasedMainUnit (a : AgentState L K) : ℕ :=
  if a.role = Role.main ∧ a.bias ≠ Bias.zero then 1 else 0

/-- The sign-restricted split debt `Eminus` of (49). -/
def minoritySplitDebtUnit (sigma : Sign) (i : Fin (L + 1))
    (a : AgentState L K) : ℕ :=
  match a.bias with
  | Bias.zero => 0
  | Bias.dyadic s _ =>
      if s = sigma then
        Phase6FuelLedger.agentDebt (L := L) (K := K) i a
      else 0

/-- Configuration form of `Eminus`. -/
def minoritySplitDebt (sigma : Sign) (i : Fin (L + 1))
    (c : Config (AgentState L K)) : ℕ :=
  (c.map (minoritySplitDebtUnit (L := L) (K := K) sigma i)).sum

/-- The non-`Dminus` penalty in (49): `V + Eminus + Dhigh + 3 Sbad`. -/
def phaseSixChargeUnit (sigma : Sign) (ell : Fin (L + 1))
    (hell : ell.val + 2 ≤ L) (a : AgentState L K) : ℕ :=
  biasedMainUnit a +
    minoritySplitDebtUnit sigma (middleIndex ell hell) a +
    Phase6FuelLedger.agentDebt (L := L) (K := K) ell a +
    3 * dangerousReserveUnit (L := L) (K := K) ell.val a

/-- Configuration form of the Phase-6 penalty. -/
def phaseSixCharge (sigma : Sign) (ell : Fin (L + 1))
    (hell : ell.val + 2 ≤ L) (c : Config (AgentState L K)) : ℕ :=
  Lemma613OFloor.phase3BiasedMainCount (L := L) (K := K) c +
    minoritySplitDebt (L := L) (K := K) sigma (middleIndex ell hell) c +
    Phase6FuelLedger.splitDebt (L := L) (K := K) ell c +
    3 * dangerousReserveCount (L := L) (K := K) ell.val c

/-- Per-agent summand for the integer credit. -/
def lateBiasedResourceAtom (sigma : Sign) (ell : Fin (L + 1))
    (hell : ell.val + 2 ≤ L) (a : AgentState L K) : ℤ :=
  2 * (majorityBlockUnit (L := L) (K := K) sigma ell.val a : ℤ) -
    (phaseSixChargeUnit sigma ell hell a : ℤ) -
    2 * (minorityDebtUnit (L := L) (K := K) sigma ell.val a : ℤ)

/-- Equation (49):
`2 Q - V - Eminus - 2 Dminus - Dhigh - 3 Sbad`. -/
def lateBiasedResourceCredit (sigma : Sign) (ell : Fin (L + 1))
    (hell : ell.val + 2 ≤ L) (c : Config (AgentState L K)) : ℤ :=
  2 * (majorityBlockCount (L := L) (K := K) sigma ell.val c : ℤ) -
    (phaseSixCharge sigma ell hell c : ℤ) -
    2 * (minorityDebt (L := L) (K := K) sigma ell.val c : ℤ)

@[simp] theorem biasedMainCount_add
    (a b : Config (AgentState L K)) :
    Lemma613OFloor.phase3BiasedMainCount (L := L) (K := K) (a + b) =
      Lemma613OFloor.phase3BiasedMainCount (L := L) (K := K) a +
        Lemma613OFloor.phase3BiasedMainCount (L := L) (K := K) b := by
  simp [Lemma613OFloor.phase3BiasedMainCount, Multiset.countP_add]

@[simp] theorem biasedMainCount_pair (a b : AgentState L K) :
    Lemma613OFloor.phase3BiasedMainCount (L := L) (K := K)
        ({a, b} : Config (AgentState L K)) =
      biasedMainUnit a + biasedMainUnit b := by
  change Multiset.countP
      (fun x : AgentState L K => x.role = Role.main ∧ x.bias ≠ Bias.zero)
      (a ::ₘ b ::ₘ 0) = _
  rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_zero]
  simp [biasedMainUnit, add_comm]

@[simp] theorem minoritySplitDebt_add
    (sigma : Sign) (i : Fin (L + 1))
    (a b : Config (AgentState L K)) :
    minoritySplitDebt (L := L) (K := K) sigma i (a + b) =
      minoritySplitDebt (L := L) (K := K) sigma i a +
        minoritySplitDebt (L := L) (K := K) sigma i b := by
  simp [minoritySplitDebt]

@[simp] theorem minoritySplitDebt_pair
    (sigma : Sign) (i : Fin (L + 1)) (a b : AgentState L K) :
    minoritySplitDebt (L := L) (K := K) sigma i
        ({a, b} : Config (AgentState L K)) =
      minoritySplitDebtUnit sigma i a + minoritySplitDebtUnit sigma i b := by
  simp [minoritySplitDebt]

@[simp] theorem splitDebt_pair
    (i : Fin (L + 1)) (a b : AgentState L K) :
    Phase6FuelLedger.splitDebt (L := L) (K := K) i
        ({a, b} : Config (AgentState L K)) =
      Phase6FuelLedger.agentDebt (L := L) (K := K) i a +
        Phase6FuelLedger.agentDebt (L := L) (K := K) i b := by
  simp [Phase6FuelLedger.splitDebt]

@[simp] theorem phaseSixCharge_add
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (a b : Config (AgentState L K)) :
    phaseSixCharge sigma ell hell (a + b) =
      phaseSixCharge sigma ell hell a + phaseSixCharge sigma ell hell b := by
  unfold phaseSixCharge
  rw [biasedMainCount_add, minoritySplitDebt_add,
    Phase6FuelLedger.splitDebt_add, dangerousReserveCount_add]
  omega

@[simp] theorem phaseSixCharge_pair
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (a b : AgentState L K) :
    phaseSixCharge sigma ell hell ({a, b} : Config (AgentState L K)) =
      phaseSixChargeUnit sigma ell hell a +
        phaseSixChargeUnit sigma ell hell b := by
  unfold phaseSixCharge phaseSixChargeUnit
  rw [biasedMainCount_pair, minoritySplitDebt_pair, splitDebt_pair,
    dangerousReserveCount_pair]
  omega

@[simp] theorem lateBiasedResourceCredit_add
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (a b : Config (AgentState L K)) :
    lateBiasedResourceCredit sigma ell hell (a + b) =
      lateBiasedResourceCredit sigma ell hell a +
        lateBiasedResourceCredit sigma ell hell b := by
  unfold lateBiasedResourceCredit
  rw [majorityBlockCount_add, phaseSixCharge_add, minorityDebt_add]
  push_cast
  ring

@[simp] theorem lateBiasedResourceCredit_pair
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (a b : AgentState L K) :
    lateBiasedResourceCredit sigma ell hell
        ({a, b} : Config (AgentState L K)) =
      lateBiasedResourceAtom sigma ell hell a +
        lateBiasedResourceAtom sigma ell hell b := by
  unfold lateBiasedResourceCredit lateBiasedResourceAtom
  rw [majorityBlockCount_pair, phaseSixCharge_pair, minorityDebt_pair]
  push_cast
  ring

/-- A unit of `Eminus` is at most one quarter of the `Dminus` unit. -/
theorem four_mul_minoritySplitDebtUnit_le_minorityDebtUnit
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (a : AgentState L K) :
    4 * minoritySplitDebtUnit sigma (middleIndex ell hell) a ≤
      minorityDebtUnit (L := L) (K := K) sigma ell.val a := by
  classical
  cases hb : a.bias with
  | zero =>
      simp [minoritySplitDebtUnit, minorityDebtUnit, hb]
  | dyadic s j =>
      by_cases hs : s = sigma
      · subst s
        by_cases hm : a.role = Role.main
        · by_cases hj : j.val < ell.val + 2
          · have hjp : j.val ≤ ell.val + 4 := by omega
            have hexp :
                ell.val + 4 - j.val =
                  (ell.val + 2 - j.val) + 2 := by omega
            simp [minoritySplitDebtUnit, Phase6FuelLedger.agentDebt,
              minorityDebtUnit, hb, hm, hj, hjp, middleIndex,
              hexp, pow_add]
            omega
          · simp [minoritySplitDebtUnit, Phase6FuelLedger.agentDebt,
              minorityDebtUnit, hb, hm, hj, middleIndex]
        · simp [minoritySplitDebtUnit, Phase6FuelLedger.agentDebt,
            minorityDebtUnit, hb, hm]
      · simp [minoritySplitDebtUnit, minorityDebtUnit, hb, hs]

/-- Configuration form: `4 Eminus <= Dminus`. -/
theorem four_mul_minoritySplitDebt_le_minorityDebt
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (c : Config (AgentState L K)) :
    4 * minoritySplitDebt sigma (middleIndex ell hell) c ≤
      minorityDebt (L := L) (K := K) sigma ell.val c := by
  induction c using Multiset.induction_on with
  | empty => simp [minoritySplitDebt, minorityDebt]
  | cons a c ih =>
      simp only [minoritySplitDebt, minorityDebt, Multiset.map_cons,
        Multiset.sum_cons] at ih ⊢
      have ha := four_mul_minoritySplitDebtUnit_le_minorityDebtUnit
        (L := L) (K := K) sigma ell hell a
      omega

/-- Every biased Main is a Main; this remains true after Reserve conversion. -/
theorem biasedMainCount_le_mainCount
    (c : Config (AgentState L K)) :
    Lemma613OFloor.phase3BiasedMainCount (L := L) (K := K) c ≤
      RoleSplitConcentration.mainCount (L := L) (K := K) c := by
  classical
  induction c using Multiset.induction_on with
  | empty =>
      simp [Lemma613OFloor.phase3BiasedMainCount,
        RoleSplitConcentration.mainCount]
  | cons a c ih =>
      simp only [Lemma613OFloor.phase3BiasedMainCount,
        RoleSplitConcentration.mainCount, Multiset.countP_cons] at ih ⊢
      simp only [ne_eq] at ih
      by_cases hm : a.role = Role.main
      · by_cases hb : a.bias = Bias.zero
        · simp [hm, hb] <;> omega
        · simp [hm, hb] <;> omega
      · simp [hm] <;> omega

/-- Equation (50), using the exact integer-scaled floors. -/
theorem lateBiasedResourceCredit_initialFloor
    {n M R : ℕ}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma tau : Sign)
    (c : Config
      (AgentState (PhaseThreeModel.Numeric.hourIndex n) 256))
    (hsnapshot :
      LateSamplingCorrectedFuelProducer.CompletedRowTwoFuelSnapshot
        (n := n) ell tau M R c)
    (hblock :
      920 * M ≤ 1000 *
        majorityBlockCount sigma ell.val c)
    (hmain :
      RoleSplitConcentration.mainCount c = M)
    (hminor :
      1000 * minorityDebt sigma ell.val c ≤ 64 * M)
    (hdanger :
      1000 * dangerousReserveCount ell.val c ≤ 50 * M) :
    (544 : ℤ) * (M : ℤ) ≤
      1000 * lateBiasedResourceCredit sigma ell hell c := by
  let Q := majorityBlockCount sigma ell.val c
  let V := Lemma613OFloor.phase3BiasedMainCount c
  let E := minoritySplitDebt sigma (middleIndex ell hell) c
  let D := minorityDebt sigma ell.val c
  let H := Phase6FuelLedger.splitDebt ell c
  let S := dangerousReserveCount ell.val c
  have hQ : 920 * M ≤ 1000 * Q := by simpa [Q] using hblock
  have hVraw := biasedMainCount_le_mainCount c
  have hV : V ≤ M := by simpa [V, hmain] using hVraw
  have hED := four_mul_minoritySplitDebt_le_minorityDebt
    sigma ell hell c
  have hE : 1000 * E ≤ 16 * M := by
    change 1000 * E ≤ 16 * M
    change 4 * E ≤ D at hED
    change 1000 * D ≤ 64 * M at hminor
    omega
  have hD : 1000 * D ≤ 64 * M := by simpa [D] using hminor
  have hHtail := Phase6FuelEntry.splitDebt_le_massAboveScaled ell c
  have hH : 1000 * H ≤ 2 * M := by
    change H ≤ Lemma615MassAbove.massAboveScaled ell.val c at hHtail
    have hup : 500 * Lemma615MassAbove.massAboveScaled ell.val c ≤ M :=
      hsnapshot.upper_tail_scaled
    omega
  have hS : 1000 * S ≤ 50 * M := by simpa [S] using hdanger
  have hnat :
      544 * M + 1000 * V + 1000 * E + 2000 * D +
          1000 * H + 3000 * S ≤
        2000 * Q := by
    omega
  have hint :
      (544 : ℤ) * (M : ℤ) + 1000 * (V : ℤ) + 1000 * (E : ℤ) +
          2000 * (D : ℤ) + 1000 * (H : ℤ) + 3000 * (S : ℤ) ≤
        2000 * (Q : ℤ) := by
    exact_mod_cast hnat
  change (544 : ℤ) * (M : ℤ) ≤
    1000 *
      (2 * (Q : ℤ) - ((V + E + H + 3 * S : ℕ) : ℤ) -
        2 * (D : ℤ))
  push_cast at hint ⊢
  omega

/-! ## Static-field lemmas for Init 6 -/

private theorem biasedMainUnit_eq_of_role_bias
    (x y : AgentState L K)
    (hrole : x.role = y.role) (hbias : x.bias = y.bias) :
    biasedMainUnit x = biasedMainUnit y := by
  unfold biasedMainUnit
  rw [hrole, hbias]

private theorem agentDebt_eq_of_role_bias
    (i : Fin (L + 1)) (x y : AgentState L K)
    (hrole : x.role = y.role) (hbias : x.bias = y.bias) :
    Phase6FuelLedger.agentDebt i x = Phase6FuelLedger.agentDebt i y := by
  unfold Phase6FuelLedger.agentDebt
  rw [hrole, hbias]

private theorem minoritySplitDebtUnit_eq_of_role_bias
    (sigma : Sign) (i : Fin (L + 1)) (x y : AgentState L K)
    (hrole : x.role = y.role) (hbias : x.bias = y.bias) :
    minoritySplitDebtUnit sigma i x = minoritySplitDebtUnit sigma i y := by
  unfold minoritySplitDebtUnit
  rw [hbias]
  cases hy : y.bias with
  | zero => simp [hy]
  | dyadic s j =>
      by_cases hs : s = sigma
      · simp [hy, hs, agentDebt_eq_of_role_bias i x y hrole hbias]
      · simp [hy, hs]

private theorem majorityBlockUnit_eq_of_role_bias
    (sigma : Sign) (l : ℕ) (x y : AgentState L K)
    (hrole : x.role = y.role) (hbias : x.bias = y.bias) :
    majorityBlockUnit sigma l x = majorityBlockUnit sigma l y := by
  have hmem :
      x ∈ majorityBand3 (L := L) (K := K) sigma l ↔
        y ∈ majorityBand3 (L := L) (K := K) sigma l := by
    rw [majorityBand3, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rw [hrole, hbias]
  unfold majorityBlockUnit
  by_cases hx : x ∈ majorityBand3 (L := L) (K := K) sigma l
  · rw [if_pos hx, if_pos (hmem.mp hx)]
  · rw [if_neg hx, if_neg]
    exact fun hy => hx (hmem.mpr hy)

private theorem minorityDebtUnit_eq_of_role_bias
    (sigma : Sign) (l : ℕ) (x y : AgentState L K)
    (hrole : x.role = y.role) (hbias : x.bias = y.bias) :
    minorityDebtUnit sigma l x = minorityDebtUnit sigma l y := by
  unfold minorityDebtUnit
  rw [hrole, hbias]

private theorem dangerousReserveUnit_eq_of_role_hour
    (l : ℕ) (x y : AgentState L K)
    (hrole : x.role = y.role) (hhour : x.hour = y.hour) :
    dangerousReserveUnit l x = dangerousReserveUnit l y := by
  unfold dangerousReserveUnit
  rw [hrole, hhour]

private theorem phaseSixChargeUnit_eq_of_static
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (x y : AgentState L K)
    (hrole : x.role = y.role) (hbias : x.bias = y.bias)
    (hhour : x.hour = y.hour) :
    phaseSixChargeUnit sigma ell hell x =
      phaseSixChargeUnit sigma ell hell y := by
  unfold phaseSixChargeUnit
  rw [biasedMainUnit_eq_of_role_bias x y hrole hbias,
    minoritySplitDebtUnit_eq_of_role_bias sigma (middleIndex ell hell)
      x y hrole hbias,
    agentDebt_eq_of_role_bias ell x y hrole hbias,
    dangerousReserveUnit_eq_of_role_hour ell.val x y hrole hhour]

private theorem lateBiasedResourceAtom_eq_of_static
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (x y : AgentState L K)
    (hrole : x.role = y.role) (hbias : x.bias = y.bias)
    (hhour : x.hour = y.hour) :
    lateBiasedResourceAtom sigma ell hell x =
      lateBiasedResourceAtom sigma ell hell y := by
  unfold lateBiasedResourceAtom
  rw [majorityBlockUnit_eq_of_role_bias sigma ell.val x y hrole hbias,
    phaseSixChargeUnit_eq_of_static sigma ell hell x y hrole hbias hhour,
    minorityDebtUnit_eq_of_role_bias sigma ell.val x y hrole hbias]

@[simp] theorem lateBiasedResourceAtom_set_phase_eq
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (a : AgentState L K) (p : Fin 11) :
    lateBiasedResourceAtom sigma ell hell {a with phase := p} =
      lateBiasedResourceAtom sigma ell hell a := by
  exact lateBiasedResourceAtom_eq_of_static sigma ell hell _ a rfl rfl rfl

@[simp] theorem lateBiasedResourceAtom_phaseSixEntry_eq
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (a : AgentState L K) :
    lateBiasedResourceAtom sigma ell hell
        (LateMixedFuelLedger.phaseSixEntry a) =
      lateBiasedResourceAtom sigma ell hell a := by
  apply lateBiasedResourceAtom_eq_of_static sigma ell hell
  · exact LateMixedFuelLedger.phaseSixEntry_role a
  · exact LateMixedFuelLedger.phaseSixEntry_bias a
  · exact LateMixedFuelLedger.phaseSixEntry_hour a

/-- Init 6 preserves every field entering (49), not only their aggregate. -/
theorem phaseSixEntry_preserves_credit_fields
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (a : AgentState L K) :
    majorityBlockUnit sigma ell.val (LateMixedFuelLedger.phaseSixEntry a) =
        majorityBlockUnit sigma ell.val a ∧
      biasedMainUnit (LateMixedFuelLedger.phaseSixEntry a) =
        biasedMainUnit a ∧
      minoritySplitDebtUnit sigma (middleIndex ell hell)
          (LateMixedFuelLedger.phaseSixEntry a) =
        minoritySplitDebtUnit sigma (middleIndex ell hell) a ∧
      minorityDebtUnit sigma ell.val (LateMixedFuelLedger.phaseSixEntry a) =
        minorityDebtUnit sigma ell.val a ∧
      Phase6FuelLedger.agentDebt ell (LateMixedFuelLedger.phaseSixEntry a) =
        Phase6FuelLedger.agentDebt ell a ∧
      dangerousReserveUnit ell.val (LateMixedFuelLedger.phaseSixEntry a) =
        dangerousReserveUnit ell.val a := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact majorityBlockUnit_eq_of_role_bias sigma ell.val _ a
      (LateMixedFuelLedger.phaseSixEntry_role a)
      (LateMixedFuelLedger.phaseSixEntry_bias a)
  · exact biasedMainUnit_eq_of_role_bias _ a
      (LateMixedFuelLedger.phaseSixEntry_role a)
      (LateMixedFuelLedger.phaseSixEntry_bias a)
  · exact minoritySplitDebtUnit_eq_of_role_bias sigma
      (middleIndex ell hell) _ a
      (LateMixedFuelLedger.phaseSixEntry_role a)
      (LateMixedFuelLedger.phaseSixEntry_bias a)
  · exact minorityDebtUnit_eq_of_role_bias sigma ell.val _ a
      (LateMixedFuelLedger.phaseSixEntry_role a)
      (LateMixedFuelLedger.phaseSixEntry_bias a)
  · exact agentDebt_eq_of_role_bias ell _ a
      (LateMixedFuelLedger.phaseSixEntry_role a)
      (LateMixedFuelLedger.phaseSixEntry_bias a)
  · exact dangerousReserveUnit_eq_of_role_hour ell.val _ a
      (LateMixedFuelLedger.phaseSixEntry_role a)
      (LateMixedFuelLedger.phaseSixEntry_hour a)

/-- Clocks and other non-Main/non-Reserve roles contribute zero. -/
theorem lateBiasedResourceAtom_eq_zero_of_nonmain_nonreserve
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (a : AgentState L K)
    (hm : a.role ≠ Role.main) (hr : a.role ≠ Role.reserve) :
    lateBiasedResourceAtom sigma ell hell a = 0 := by
  cases hb : a.bias <;>
    simp [lateBiasedResourceAtom, phaseSixChargeUnit, biasedMainUnit,
      minoritySplitDebtUnit, Phase6FuelLedger.agentDebt,
      dangerousReserveUnit, hm, hr, hb]

end Ripple.PopulationProtocol.ExactMajority.LateBiasedResourceCredit
