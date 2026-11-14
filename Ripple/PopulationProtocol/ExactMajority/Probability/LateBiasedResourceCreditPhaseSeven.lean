-- Ripple/PopulationProtocol/ExactMajority/Probability/LateBiasedResourceCreditPhaseSeven.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateBiasedResourceCreditPhaseSix
import Ripple.PopulationProtocol.ExactMajority.Probability.LatePhaseSixDrainSelectedLevel

/-!
# Lemma 11: Phase-7 and mixed 6/7 transport of the biased resource credit

Expected surface of `LateBiasedResourceCredit`:
* `LateBiasedResourceCredit.lateBiasedResourceAtom`
* `LateBiasedResourceCredit.lateBiasedResourceCredit`
* `LateBiasedResourceCredit.lateBiasedResourceCredit_add`
* `LateBiasedResourceCredit.lateBiasedResourceCredit_pair`
* `LateBiasedResourceCredit.lateBiasedResourceAtom_eq_zero_of_nonmain_nonreserve`
* `LateBiasedResourceCredit.middleIndex`
* `LateBiasedResourceCredit.biasedMainUnit`
* `LateBiasedResourceCredit.minoritySplitDebtUnit`
* `LateBiasedResourceCredit.phaseSixChargeUnit`
* `LateBiasedResourceCreditPhaseSix.PhaseSixDispatchPair`
* `LateBiasedResourceCreditPhaseSix.Transition_atom_pair_mono_of_phaseSixDispatch`
* `LateBiasedResourceCreditPhaseSix.ReachablePhaseSixWindow`

Theorem list:
* `NoShallowMain`
* `phaseSevenEntry_preserves_credit_fields`
* `cancelSplit_atom_pair_mono_of_noShallow`
* `cancelSplit_noShallow_pair`
* `Transition_atom_pair_mono_of_phaseSixOrSeven`
* `Transition_noShallow_pair_of_phaseSixOrSeven`
* `PhaseSixSevenCreditStep`, `PhaseSixSevenCreditReachable`
* `phaseSixSevenCreditStep_preserves`
* `phaseSixSevenCreditReachable_preserves`
* `phaseSixSevenCreditReachable_to_phaseSixToSevenReachable`
* `reachablePhaseSixWindow_after_step_of_beforeEight`

Closes task item 1.  The five `split_ifs` branches below are exactly equal,
gap one in both orientations, and corrected gap two in both orientations.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateBiasedResourceCreditPhaseSeven

open LateBiasedResourceCredit
open LateBiasedResourceCreditPhaseSix
open Phase7BandDefs
open Phase7MajorityBlockLedger
open Phase6BlockSnapshot

variable {L K : ℕ}

/-- Lemma 10's deterministic configuration conclusion. -/
def NoShallowMain (ell : Fin (L + 1))
    (c : Config (AgentState L K)) : Prop :=
  ∀ a ∈ c,
    ¬ Phase6Convergence.highSt (L := L) (K := K) ell.val a

private theorem majorityBlockUnit_eq_of_staticFields
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

private theorem minorityDebtUnit_eq_of_staticFields
    (sigma : Sign) (l : ℕ) (x y : AgentState L K)
    (hrole : x.role = y.role) (hbias : x.bias = y.bias) :
    minorityDebtUnit sigma l x = minorityDebtUnit sigma l y := by
  unfold minorityDebtUnit
  rw [hrole, hbias]

private theorem agentDebt_eq_of_staticFields
    (i : Fin (L + 1)) (x y : AgentState L K)
    (hrole : x.role = y.role) (hbias : x.bias = y.bias) :
    Phase6FuelLedger.agentDebt i x = Phase6FuelLedger.agentDebt i y := by
  unfold Phase6FuelLedger.agentDebt
  rw [hrole, hbias]

private theorem biasedMainUnit_eq_of_staticFields
    (x y : AgentState L K)
    (hrole : x.role = y.role) (hbias : x.bias = y.bias) :
    biasedMainUnit x = biasedMainUnit y := by
  unfold biasedMainUnit
  rw [hrole, hbias]

private theorem minoritySplitDebtUnit_eq_of_staticFields
    (sigma : Sign) (i : Fin (L + 1)) (x y : AgentState L K)
    (hrole : x.role = y.role) (hbias : x.bias = y.bias) :
    minoritySplitDebtUnit sigma i x = minoritySplitDebtUnit sigma i y := by
  unfold minoritySplitDebtUnit
  rw [hbias]
  cases hy : y.bias with
  | zero => simp [hy]
  | dyadic s j =>
      by_cases hs : s = sigma
      · simp [hy, hs, agentDebt_eq_of_staticFields i x y hrole hbias]
      · simp [hy, hs]

private theorem dangerousReserveUnit_eq_of_staticFields
    (l : ℕ) (x y : AgentState L K)
    (hrole : x.role = y.role)
    (hhour : y.role = Role.reserve → x.hour = y.hour) :
    dangerousReserveUnit l x = dangerousReserveUnit l y := by
  unfold dangerousReserveUnit
  by_cases hy : y.role = Role.reserve
  · have hx : x.role = Role.reserve := by simpa [hrole] using hy
    rw [hhour hy]
    simp [hx, hy]
  · have hx : x.role ≠ Role.reserve := by simpa [hrole] using hy
    simp [hx, hy]

/-- Public static-field bridge used by the pathwise file for locked Phase 5.
Only a Reserve's hour is observable in `J`. -/
theorem lateBiasedResourceAtom_eq_of_staticFields
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (x y : AgentState L K)
    (hrole : x.role = y.role) (hbias : x.bias = y.bias)
    (hhour : y.role = Role.reserve → x.hour = y.hour) :
    lateBiasedResourceAtom sigma ell hell x =
      lateBiasedResourceAtom sigma ell hell y := by
  have hQ := majorityBlockUnit_eq_of_staticFields
    (L := L) (K := K) sigma ell.val x y hrole hbias
  have hV := biasedMainUnit_eq_of_staticFields x y hrole hbias
  have hE := minoritySplitDebtUnit_eq_of_staticFields
    (L := L) (K := K) sigma (middleIndex ell hell) x y hrole hbias
  have hD := minorityDebtUnit_eq_of_staticFields
    (L := L) (K := K) sigma ell.val x y hrole hbias
  have hH := agentDebt_eq_of_staticFields
    (L := L) (K := K) ell x y hrole hbias
  have hS := dangerousReserveUnit_eq_of_staticFields
    (L := L) (K := K) ell.val x y hrole hhour
  unfold lateBiasedResourceAtom phaseSixChargeUnit
  rw [hQ, hV, hE, hD, hH, hS]

private theorem noShallowAgent_of_staticFields
    (ell : Fin (L + 1)) (x y : AgentState L K)
    (hrole : x.role = y.role) (hbias : x.bias = y.bias)
    (hy : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val y) :
    ¬ Phase6Convergence.highSt (L := L) (K := K) ell.val x := by
  rintro ⟨hxmain, s, i, hxbias, hi⟩
  apply hy
  exact ⟨by simpa [hrole] using hxmain, s, i,
    by simpa [hbias] using hxbias, hi⟩

/-- The exact state produced by Init 7. -/
def phaseSevenEntry (a : AgentState L K) : AgentState L K :=
  phaseInit L K ⟨7, by decide⟩ {a with phase := ⟨7, by decide⟩}

theorem phaseSevenEntry_role (a : AgentState L K) :
    (phaseSevenEntry (L := L) (K := K) a).role = a.role := by
  simpa [phaseSevenEntry] using
    Phase5Convergence.phaseInit_role_ge_five
      (L := L) (K := K) (⟨7, by decide⟩ : Fin 11)
      ({a with phase := ⟨7, by decide⟩} : AgentState L K) (by decide)

theorem phaseSevenEntry_bias (a : AgentState L K) :
    (phaseSevenEntry (L := L) (K := K) a).bias = a.bias := by
  simpa [phaseSevenEntry] using
    Phase5Convergence.phaseInit_bias_ge_five
      (L := L) (K := K) (⟨7, by decide⟩ : Fin 11)
      ({a with phase := ⟨7, by decide⟩} : AgentState L K) (by decide)

theorem phaseSevenEntry_hour (a : AgentState L K) :
    (phaseSevenEntry (L := L) (K := K) a).hour = a.hour := by
  simpa [phaseSevenEntry] using
    ReserveSampling.phaseInit_hour_ge_six
      (L := L) (K := K) (⟨7, by decide⟩ : Fin 11)
      ({a with phase := ⟨7, by decide⟩} : AgentState L K) (by decide)

theorem phaseSevenEntry_phase (a : AgentState L K) :
    (phaseSevenEntry (L := L) (K := K) a).phase.val = 7 := by
  unfold phaseSevenEntry
  exact Phase6Convergence.phaseInit_phase_eq_of_seven
    (L := L) (K := K)
    ({a with phase := ⟨7, by decide⟩} : AgentState L K)
    ⟨7, by decide⟩ (by decide) (by simp)

/-- Init 7 preserves every field occurring in (49). -/
theorem phaseSevenEntry_preserves_credit_fields
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (a : AgentState L K) :
    lateBiasedResourceAtom sigma ell hell (phaseSevenEntry a) =
      lateBiasedResourceAtom sigma ell hell a ∧
    (¬ Phase6Convergence.highSt (L := L) (K := K) ell.val a →
      ¬ Phase6Convergence.highSt
        (L := L) (K := K) ell.val (phaseSevenEntry a)) := by
  constructor
  · exact lateBiasedResourceAtom_eq_of_staticFields sigma ell hell _ a
      (phaseSevenEntry_role a) (phaseSevenEntry_bias a)
      (fun _ => phaseSevenEntry_hour a)
  · exact noShallowAgent_of_staticFields ell _ a
      (phaseSevenEntry_role a) (phaseSevenEntry_bias a)

/-- Value table of a Main agent with a biased exponent at distance `d` above
`ell`, for the minority sign. -/
def minVal : ℕ → ℤ
  | 0 => -36
  | 1 => -18
  | 2 => -9
  | 3 => -5
  | 4 => -3
  | _ => -1

/-- Value table of a Main agent with a biased exponent at distance `d` above
`ell`, for the majority sign. -/
def majVal : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | _ => -1

private theorem atom_main_zero
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (a : AgentState L K) (hm : a.role = Role.main)
    (hb : a.bias = Bias.zero) :
    lateBiasedResourceAtom sigma ell hell a = 0 := by
  have hr : a.role ≠ Role.reserve := by rw [hm]; decide
  simp [lateBiasedResourceAtom, phaseSixChargeUnit, biasedMainUnit,
    minoritySplitDebtUnit, Phase6FuelLedger.agentDebt, majorityBlockUnit_main_zero
      sigma ell.val a hm hb, minorityDebtUnit_main_zero sigma ell.val a hm hb,
    hm, hb, hr]

private theorem atom_main_dyadic
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (a : AgentState L K) (sg : Sign) (j : Fin (L + 1))
    (hm : a.role = Role.main) (hb : a.bias = Bias.dyadic sg j)
    (hj : ell.val ≤ j.val) :
    lateBiasedResourceAtom sigma ell hell a =
      if sg = sigma then minVal (j.val - ell.val)
      else majVal (j.val - ell.val) := by
  obtain ⟨e, he⟩ : ∃ e, j.val = ell.val + e := ⟨j.val - ell.val, by omega⟩
  have hr : a.role ≠ Role.reserve := by rw [hm]; decide
  have hQ := majorityBlockUnit_main_dyadic (L := L) (K := K) sigma sg ell.val
    j a hm hb
  have hD := minorityDebtUnit_main_dyadic (L := L) (K := K) sigma sg ell.val
    j a hm hb
  have hV : biasedMainUnit a = 1 := by
    unfold biasedMainUnit
    rw [if_pos]
    exact ⟨hm, by rw [hb]; simp⟩
  have hE : minoritySplitDebtUnit sigma (middleIndex ell hell) a =
      if sg = sigma then
        (if j.val < ell.val + 2 then 2 ^ (ell.val + 2 - j.val) - 1 else 0)
      else 0 := by
    unfold minoritySplitDebtUnit
    rw [hb]
    simp only
    split_ifs with h1 h2
    · simp [Phase6FuelLedger.agentDebt, hm, hb, h2]
    · simp [Phase6FuelLedger.agentDebt, hm, hb, h2]
    · rfl
  have hH : Phase6FuelLedger.agentDebt ell a = 0 := by
    have : ¬ j.val < ell.val := by omega
    simp [Phase6FuelLedger.agentDebt, hm, hb, this]
  have hS : dangerousReserveUnit ell.val a = 0 :=
    dangerousReserveUnit_of_role_ne_reserve ell.val a hr
  unfold lateBiasedResourceAtom phaseSixChargeUnit
  rw [hQ, hV, hE, hH, hS, hD]
  rw [he]
  rcases e with _ | _ | _ | _ | _ | e
  · by_cases h : sg = sigma <;> simp [h, minVal, majVal]
  · by_cases h : sg = sigma <;> simp [h, minVal, majVal]
  · by_cases h : sg = sigma <;> simp [h, minVal, majVal]
  · by_cases h : sg = sigma <;> simp [h, minVal, majVal]
  · by_cases h : sg = sigma <;> simp [h, minVal, majVal]
  · by_cases h : sg = sigma <;> simp [h, minVal, majVal]

private theorem atom_main_dyadic_pair_table
    (sigma sa sb : Sign) (hab : sa ≠ sb) (e : ℕ) :
    (-- equal exponents annihilate
      ((if sa = sigma then minVal e else majVal e) +
        (if sb = sigma then minVal e else majVal e) ≤ 0)) ∧
    (-- gap one, `s` smaller index
      ((if sa = sigma then minVal e else majVal e) +
        (if sb = sigma then minVal (e + 1) else majVal (e + 1)) ≤
        (if sa = sigma then minVal (e + 1) else majVal (e + 1)))) ∧
    (-- gap one, `t` smaller index
      ((if sa = sigma then minVal (e + 1) else majVal (e + 1)) +
        (if sb = sigma then minVal e else majVal e) ≤
        (if sb = sigma then minVal (e + 1) else majVal (e + 1)))) ∧
    (-- corrected gap two, `s` smaller index
      ((if sa = sigma then minVal e else majVal e) +
        (if sb = sigma then minVal (e + 2) else majVal (e + 2)) ≤
        (if sa = sigma then minVal (e + 1) else majVal (e + 1)) +
          (if sa = sigma then minVal (e + 2) else majVal (e + 2)))) ∧
    (-- corrected gap two, `t` smaller index
      ((if sa = sigma then minVal (e + 2) else majVal (e + 2)) +
        (if sb = sigma then minVal e else majVal e) ≤
        (if sb = sigma then minVal (e + 2) else majVal (e + 2)) +
          (if sb = sigma then minVal (e + 1) else majVal (e + 1)))) := by
  rcases e with _ | _ | _ | _ | _ | _ | e
  all_goals
    cases sa <;> cases sb <;> cases sigma <;>
      simp_all [minVal, majVal]

/-- The finite branch normalization is the literal five-row `cancelSplit`
table. -/
theorem cancelSplit_atom_pair_mono_of_noShallow
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (hsNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val s)
    (htNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val t) :
    lateBiasedResourceAtom sigma ell hell s +
        lateBiasedResourceAtom sigma ell hell t ≤
      lateBiasedResourceAtom sigma ell hell (cancelSplit L K s t).1 +
        lateBiasedResourceAtom sigma ell hell (cancelSplit L K s t).2 := by
  classical
  cases hsb : s.bias with
  | zero => simp [cancelSplit, hsb]
  | dyadic ss i =>
      have hi : ell.val ≤ i.val := by
        by_contra hlt
        exact hsNo ⟨hsM, ss, i, hsb, by omega⟩
      cases htb : t.bias with
      | zero => simp [cancelSplit, hsb, htb]
      | dyadic st j =>
          have hj : ell.val ≤ j.val := by
            by_contra hlt
            exact htNo ⟨htM, st, j, htb, by omega⟩
          have hiL : i.val < L + 1 := i.2
          have hjL : j.val < L + 1 := j.2
          have hs0 := atom_main_dyadic sigma ell hell s ss i hsM hsb hi
          have ht0 := atom_main_dyadic sigma ell hell t st j htM htb hj
          by_cases hsg : ss = st
          · have : cancelSplit L K s t = (s, t) := by
              simp [cancelSplit, hsb, htb, hsg]
            rw [this]
          · simp only [cancelSplit, hsb, htb]
            rw [if_pos hsg]
            by_cases h0 : i.val = j.val
            · rw [dif_pos h0]
              have h1 := (atom_main_dyadic_pair_table sigma ss st hsg
                (i.val - ell.val)).1
              have z1 := atom_main_zero sigma ell hell
                ({ s with bias := Bias.zero } : AgentState L K) hsM rfl
              have z2 := atom_main_zero sigma ell hell
                ({ t with bias := Bias.zero } : AgentState L K) htM rfl
              have hjj : j.val - ell.val = i.val - ell.val := by omega
              rw [hs0, ht0, hjj, z1, z2]
              simpa using h1
            · rw [dif_neg h0]
              by_cases h1 : i.val + 1 = j.val
              · rw [dif_pos h1]
                have tab := (atom_main_dyadic_pair_table sigma ss st hsg
                  (i.val - ell.val)).2.1
                have z2 := atom_main_zero sigma ell hell
                  ({ t with bias := Bias.zero } : AgentState L K) htM rfl
                have n1 := atom_main_dyadic sigma ell hell
                  ({ s with bias := Bias.dyadic ss ⟨i.val + 1, by omega⟩ } :
                    AgentState L K) ss ⟨i.val + 1, by omega⟩ hsM rfl
                  (by simp; omega)
                have hjj : j.val - ell.val = i.val - ell.val + 1 := by omega
                simp only at n1
                rw [hs0, ht0, hjj, z2, n1]
                have : i.val + 1 - ell.val = i.val - ell.val + 1 := by omega
                rw [this]
                simpa using tab
              · rw [dif_neg h1]
                by_cases h2 : j.val + 1 = i.val
                · rw [dif_pos h2]
                  have tab := (atom_main_dyadic_pair_table sigma ss st hsg
                    (j.val - ell.val)).2.2.1
                  have z1 := atom_main_zero sigma ell hell
                    ({ s with bias := Bias.zero } : AgentState L K) hsM rfl
                  have n2 := atom_main_dyadic sigma ell hell
                    ({ t with bias := Bias.dyadic st ⟨j.val + 1, by omega⟩ } :
                      AgentState L K) st ⟨j.val + 1, by omega⟩ htM rfl
                    (by simp; omega)
                  have hii : i.val - ell.val = j.val - ell.val + 1 := by omega
                  simp only at n2
                  rw [hs0, ht0, hii, z1, n2]
                  have : j.val + 1 - ell.val = j.val - ell.val + 1 := by omega
                  rw [this]
                  simpa using tab
                · rw [dif_neg h2]
                  by_cases h3 : i.val + 2 = j.val
                  · rw [dif_pos h3]
                    have tab := (atom_main_dyadic_pair_table sigma ss st hsg
                      (i.val - ell.val)).2.2.2.1
                    have n1 := atom_main_dyadic sigma ell hell
                      ({ s with bias := Bias.dyadic ss ⟨i.val + 1, by omega⟩ } :
                        AgentState L K) ss ⟨i.val + 1, by omega⟩ hsM rfl
                      (by simp; omega)
                    have n2 := atom_main_dyadic sigma ell hell
                      ({ t with bias := Bias.dyadic ss ⟨i.val + 2, by omega⟩ } :
                        AgentState L K) ss ⟨i.val + 2, by omega⟩ htM rfl
                      (by simp; omega)
                    have hjj : j.val - ell.val = i.val - ell.val + 2 := by omega
                    simp only at n1 n2
                    rw [hs0, ht0, hjj, n1, n2]
                    have e1 : i.val + 1 - ell.val = i.val - ell.val + 1 := by omega
                    have e2 : i.val + 2 - ell.val = i.val - ell.val + 2 := by omega
                    rw [e1, e2]
                    simpa using tab
                  · rw [dif_neg h3]
                    by_cases h4 : j.val + 2 = i.val
                    · rw [dif_pos h4]
                      have tab := (atom_main_dyadic_pair_table sigma ss st hsg
                        (j.val - ell.val)).2.2.2.2
                      have n1 := atom_main_dyadic sigma ell hell
                        ({ s with bias := Bias.dyadic st ⟨j.val + 2, by omega⟩ } :
                          AgentState L K) st ⟨j.val + 2, by omega⟩ hsM rfl
                        (by simp; omega)
                      have n2 := atom_main_dyadic sigma ell hell
                        ({ t with bias := Bias.dyadic st ⟨j.val + 1, by omega⟩ } :
                          AgentState L K) st ⟨j.val + 1, by omega⟩ htM rfl
                        (by simp; omega)
                      have hii : i.val - ell.val = j.val - ell.val + 2 := by omega
                      simp only at n1 n2
                      rw [hs0, ht0, hii, n1, n2]
                      have e1 : j.val + 2 - ell.val = j.val - ell.val + 2 := by omega
                      have e2 : j.val + 1 - ell.val = j.val - ell.val + 1 := by omega
                      rw [e1, e2]
                      simpa using tab
                    · rw [dif_neg h4]

/-- `cancelSplit` never moves a biased Main to a smaller Lean index. -/
theorem cancelSplit_noShallow_pair
    (ell : Fin (L + 1)) (s t : AgentState L K)
    (hsM : s.role = Role.main) (htM : t.role = Role.main)
    (hsNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val s)
    (htNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val t) :
    (¬ Phase6Convergence.highSt
        (L := L) (K := K) ell.val (cancelSplit L K s t).1) ∧
      (¬ Phase6Convergence.highSt
        (L := L) (K := K) ell.val (cancelSplit L K s t).2) := by
  classical
  cases hsb : s.bias with
  | zero => simpa [cancelSplit, hsb] using And.intro hsNo htNo
  | dyadic ss i =>
      have hi : ell.val ≤ i.val := by
        by_contra hlt
        exact hsNo ⟨hsM, ss, i, hsb, by omega⟩
      cases htb : t.bias with
      | zero => simpa [cancelSplit, hsb, htb] using And.intro hsNo htNo
      | dyadic st j =>
          have hj : ell.val ≤ j.val := by
            by_contra hlt
            exact htNo ⟨htM, st, j, htb, by omega⟩
          have hiL : i.val < L + 1 := i.2
          have hjL : j.val < L + 1 := j.2
          simp only [cancelSplit, hsb, htb]
          split_ifs <;>
            simp_all [Phase6Convergence.highSt] <;>
            first | omega | (simp only [Fin.le_def, Fin.val_mk] at *; omega)

private theorem clockBranch_atom_eq
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (a : AgentState L K) (ha : 5 ≤ a.phase.val) :
    lateBiasedResourceAtom sigma ell hell
        (if a.role = Role.clock then stdCounterSubroutine L K a else a) =
      lateBiasedResourceAtom sigma ell hell a := by
  by_cases hc : a.role = Role.clock
  · rw [if_pos hc]
    have hout : (stdCounterSubroutine L K a).role = Role.clock := by
      rw [Phase6Convergence.stdCounterSubroutine_role_ge_five6
        (L := L) (K := K) a ha, hc]
    rw [lateBiasedResourceAtom_eq_zero_of_nonmain_nonreserve
          sigma ell hell (stdCounterSubroutine L K a)
          (by rw [hout]; decide) (by rw [hout]; decide),
      lateBiasedResourceAtom_eq_zero_of_nonmain_nonreserve
          sigma ell hell a (by rw [hc]; decide) (by rw [hc]; decide)]
  · rw [if_neg hc]

private theorem clockBranch_noShallow
    (ell : Fin (L + 1)) (a : AgentState L K) (ha : 5 ≤ a.phase.val)
    (hNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val a) :
    ¬ Phase6Convergence.highSt (L := L) (K := K) ell.val
      (if a.role = Role.clock then stdCounterSubroutine L K a else a) := by
  by_cases hc : a.role = Role.clock
  · rw [if_pos hc]
    intro hhigh
    have hrole := Phase6Convergence.stdCounterSubroutine_role_ge_five6
      (L := L) (K := K) a ha
    have hm := hhigh.1
    rw [hrole, hc] at hm
    exact (by decide : Role.clock ≠ Role.main) hm
  · simpa [hc] using hNo

private theorem Transition_fst_eq_self_of_phaseSeven_notClock
    (s t : AgentState L K)
    (hs : s.phase.val = 7) (ht : t.phase.val = 7)
    (hboth : ¬ (s.role = Role.main ∧ t.role = Role.main))
    (hclock : s.role ≠ Role.clock) :
    (Transition L K s t).1 = s := by
  have hepi := Phase7Convergence.phaseEpidemicUpdate_eq_self_of_phase7
    (L := L) (K := K) s t hs ht
  have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs
  have hp : (Phase7Transition L K s t).1 = s := by
    unfold Phase7Transition
    simp [hboth, hclock]
  unfold Transition
  rw [hepi]
  simp only [hsp]
  rw [finishPhase10Entry_eq_self_of_after_ne_10
    (L := L) (K := K) s _ (by rw [hp, hs]; decide)]
  exact hp

private theorem Transition_snd_eq_self_of_phaseSeven_notClock
    (s t : AgentState L K)
    (hs : s.phase.val = 7) (ht : t.phase.val = 7)
    (hboth : ¬ (s.role = Role.main ∧ t.role = Role.main))
    (hclock : t.role ≠ Role.clock) :
    (Transition L K s t).2 = t := by
  have hepi := Phase7Convergence.phaseEpidemicUpdate_eq_self_of_phase7
    (L := L) (K := K) s t hs ht
  have hsp : s.phase = ⟨7, by decide⟩ := Fin.ext hs
  have hp : (Phase7Transition L K s t).2 = t := by
    unfold Phase7Transition
    simp [hboth, hclock]
  unfold Transition
  rw [hepi]
  simp only [hsp]
  rw [finishPhase10Entry_eq_self_of_after_ne_10
    (L := L) (K := K) t _ (by rw [hp, ht]; decide)]
  exact hp

private theorem Transition_atom_pair_mono_of_phaseSeven
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K)
    (hs : s.phase.val = 7) (ht : t.phase.val = 7)
    (hsNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val s)
    (htNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val t) :
    lateBiasedResourceAtom sigma ell hell s +
        lateBiasedResourceAtom sigma ell hell t ≤
      lateBiasedResourceAtom sigma ell hell (Transition L K s t).1 +
        lateBiasedResourceAtom sigma ell hell (Transition L K s t).2 := by
  by_cases hboth : s.role = Role.main ∧ t.role = Role.main
  · rw [Phase7Convergence.Transition_eq_cancelSplit_of_phase7_main
      (L := L) (K := K) s t hs ht hboth.1 hboth.2]
    exact cancelSplit_atom_pair_mono_of_noShallow
      sigma ell hell s t hboth.1 hboth.2 hsNo htNo
  · obtain ⟨hroleLeft, hroleRight⟩ :=
      PhaseOnlyWindows.Transition_role_phase7
        (L := L) (K := K) s t hs ht
    have hleft :
        lateBiasedResourceAtom sigma ell hell (Transition L K s t).1 =
          lateBiasedResourceAtom sigma ell hell s := by
      by_cases hc : s.role = Role.clock
      · rw [lateBiasedResourceAtom_eq_zero_of_nonmain_nonreserve
            sigma ell hell (Transition L K s t).1
            (by rw [hroleLeft, hc]; decide)
            (by rw [hroleLeft, hc]; decide),
          lateBiasedResourceAtom_eq_zero_of_nonmain_nonreserve
            sigma ell hell s (by rw [hc]; decide) (by rw [hc]; decide)]
      · rw [Transition_fst_eq_self_of_phaseSeven_notClock s t hs ht hboth hc]
    have hright :
        lateBiasedResourceAtom sigma ell hell (Transition L K s t).2 =
          lateBiasedResourceAtom sigma ell hell t := by
      by_cases hc : t.role = Role.clock
      · rw [lateBiasedResourceAtom_eq_zero_of_nonmain_nonreserve
            sigma ell hell (Transition L K s t).2
            (by rw [hroleRight, hc]; decide)
            (by rw [hroleRight, hc]; decide),
          lateBiasedResourceAtom_eq_zero_of_nonmain_nonreserve
            sigma ell hell t (by rw [hc]; decide) (by rw [hc]; decide)]
      · rw [Transition_snd_eq_self_of_phaseSeven_notClock s t hs ht hboth hc]
    rw [hleft, hright]

private theorem Transition_noShallow_pair_of_phaseSeven
    (ell : Fin (L + 1)) (s t : AgentState L K)
    (hs : s.phase.val = 7) (ht : t.phase.val = 7)
    (hsNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val s)
    (htNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val t) :
    (¬ Phase6Convergence.highSt
        (L := L) (K := K) ell.val (Transition L K s t).1) ∧
      (¬ Phase6Convergence.highSt
        (L := L) (K := K) ell.val (Transition L K s t).2) := by
  by_cases hboth : s.role = Role.main ∧ t.role = Role.main
  · rw [Phase7Convergence.Transition_eq_cancelSplit_of_phase7_main
      (L := L) (K := K) s t hs ht hboth.1 hboth.2]
    exact cancelSplit_noShallow_pair ell s t hboth.1 hboth.2 hsNo htNo
  · obtain ⟨hroleLeft, hroleRight⟩ :=
      PhaseOnlyWindows.Transition_role_phase7
        (L := L) (K := K) s t hs ht
    constructor
    · by_cases hc : s.role = Role.clock
      · intro hhigh
        have hm := hhigh.1
        rw [hroleLeft, hc] at hm
        exact (by decide : Role.clock ≠ Role.main) hm
      · simpa [Transition_fst_eq_self_of_phaseSeven_notClock
          s t hs ht hboth hc] using hsNo
    · by_cases hc : t.role = Role.clock
      · intro hhigh
        have hm := hhigh.1
        rw [hroleRight, hc] at hm
        exact (by decide : Role.clock ≠ Role.main) hm
      · simpa [Transition_snd_eq_self_of_phaseSeven_notClock
          s t hs ht hboth hc] using htNo

private theorem Phase6Transition_noShallow_pair
    (ell : Fin (L + 1)) (s t : AgentState L K)
    (hs : 6 ≤ s.phase.val) (ht : 6 ≤ t.phase.val)
    (hsNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val s)
    (htNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val t) :
    (¬ Phase6Convergence.highSt
        (L := L) (K := K) ell.val (Phase6Transition L K s t).1) ∧
      (¬ Phase6Convergence.highSt
        (L := L) (K := K) ell.val (Phase6Transition L K s t).2) := by
  have hsZero := Phase6Convergence.agentMassW_eq_zero_of_not_high
    (L := L) (K := K) ell.val s hsNo
  have htZero := Phase6Convergence.agentMassW_eq_zero_of_not_high
    (L := L) (K := K) ell.val t htNo
  have hpair := Phase6Convergence.Phase6Transition_highMass_pair_le
    (L := L) (K := K) ell.val s t hs ht
  have hleft : Phase6Convergence.agentMassW
      (L := L) (K := K) ell.val (Phase6Transition L K s t).1 = 0 := by
    omega
  have hright : Phase6Convergence.agentMassW
      (L := L) (K := K) ell.val (Phase6Transition L K s t).2 = 0 := by
    omega
  constructor
  · intro hhigh
    have hpos := Phase6Convergence.agentMassW_pos_of_high
      (L := L) (K := K) ell.val _ hhigh
    omega
  · intro hhigh
    have hpos := Phase6Convergence.agentMassW_pos_of_high
      (L := L) (K := K) ell.val _ hhigh
    omega

private theorem runInitsBetween_six_seven_phase
    (a : AgentState L K) (ha : a.phase.val = 7) :
    (runInitsBetween L K 6 7 a).phase.val = 7 := by
  unfold runInitsBetween
  have hlist :
      (List.range 11).filter (fun k => 6 < k ∧ k ≤ 7) = [7] := by decide
  rw [hlist]
  by_cases hc : a.role = Role.clock <;> simp [phaseInit, hc, ha]

private theorem phaseEpidemicUpdate_phases_seven_of_six_seven
    (s t : AgentState L K) (hs : s.phase.val = 6) (ht : t.phase.val = 7) :
    (phaseEpidemicUpdate L K s t).1.phase.val = 7 ∧
      (phaseEpidemicUpdate L K s t).2.phase.val = 7 := by
  have hpval : (max s.phase t.phase).val = 7 := by simp [hs, ht]
  have hs' :
      (runInitsBetween L K s.phase.val (max s.phase t.phase).val
        ({s with phase := max s.phase t.phase} : AgentState L K)).phase.val
        = 7 := by
    rw [hs, hpval]
    exact runInitsBetween_six_seven_phase _ (by simp [hpval])
  have ht' :
      (runInitsBetween L K t.phase.val (max s.phase t.phase).val
        ({t with phase := max s.phase t.phase} : AgentState L K)).phase.val
        = 7 := by
    rw [ht, hpval, runInitsBetween_self]
    simp [hpval]
  unfold phaseEpidemicUpdate
  dsimp only
  rw [if_neg (by omega)]
  exact ⟨hs', ht'⟩

private theorem phaseEpidemicUpdate_phases_seven_of_seven_six
    (s t : AgentState L K) (hs : s.phase.val = 7) (ht : t.phase.val = 6) :
    (phaseEpidemicUpdate L K s t).1.phase.val = 7 ∧
      (phaseEpidemicUpdate L K s t).2.phase.val = 7 := by
  have hpval : (max s.phase t.phase).val = 7 := by simp [hs, ht]
  have hs' :
      (runInitsBetween L K s.phase.val (max s.phase t.phase).val
        ({s with phase := max s.phase t.phase} : AgentState L K)).phase.val
        = 7 := by
    rw [hs, hpval, runInitsBetween_self]
    simp [hpval]
  have ht' :
      (runInitsBetween L K t.phase.val (max s.phase t.phase).val
        ({t with phase := max s.phase t.phase} : AgentState L K)).phase.val
        = 7 := by
    rw [ht, hpval]
    exact runInitsBetween_six_seven_phase _ (by simp [hpval])
  unfold phaseEpidemicUpdate
  dsimp only
  rw [if_neg (by omega)]
  exact ⟨hs', ht'⟩

private theorem Transition_eq_Transition_epidemic_of_phaseSeven
    (s t : AgentState L K)
    (hleft : (phaseEpidemicUpdate L K s t).1.phase.val = 7)
    (hright : (phaseEpidemicUpdate L K s t).2.phase.val = 7) :
    Transition L K s t =
      Transition L K (phaseEpidemicUpdate L K s t).1
        (phaseEpidemicUpdate L K s t).2 := by
  let ep := phaseEpidemicUpdate L K s t
  have hepid : phaseEpidemicUpdate L K ep.1 ep.2 = ep :=
    Phase7Convergence.phaseEpidemicUpdate_eq_self_of_phase7
      ep.1 ep.2 hleft hright
  unfold Transition
  rw [hepid]

private theorem Transition_atom_pair_mono_of_epidemic_seven
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K)
    (hs5 : 5 ≤ s.phase.val) (ht5 : 5 ≤ t.phase.val)
    (hep : (phaseEpidemicUpdate L K s t).1.phase.val = 7 ∧
      (phaseEpidemicUpdate L K s t).2.phase.val = 7)
    (hsNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val s)
    (htNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val t) :
    lateBiasedResourceAtom sigma ell hell s +
        lateBiasedResourceAtom sigma ell hell t ≤
      lateBiasedResourceAtom sigma ell hell (Transition L K s t).1 +
        lateBiasedResourceAtom sigma ell hell (Transition L K s t).2 := by
  have hbias := Phase6Convergence.phaseEpidemicUpdate_bias_ge_five
    (L := L) (K := K) s t hs5 ht5
  have hfields := ReserveSampling.phaseEpidemicUpdate_role_hour_ge5
    (L := L) (K := K) s t hs5 ht5
  have hAtomLeft : lateBiasedResourceAtom sigma ell hell
      (phaseEpidemicUpdate L K s t).1 =
      lateBiasedResourceAtom sigma ell hell s :=
    lateBiasedResourceAtom_eq_of_staticFields sigma ell hell _ s
      hfields.1 hbias.1 (fun _ => hfields.2.1)
  have hAtomRight : lateBiasedResourceAtom sigma ell hell
      (phaseEpidemicUpdate L K s t).2 =
      lateBiasedResourceAtom sigma ell hell t :=
    lateBiasedResourceAtom_eq_of_staticFields sigma ell hell _ t
      hfields.2.2.1 hbias.2 (fun _ => hfields.2.2.2)
  have hNoLeft := noShallowAgent_of_staticFields ell
    (phaseEpidemicUpdate L K s t).1 s hfields.1 hbias.1 hsNo
  have hNoRight := noShallowAgent_of_staticFields ell
    (phaseEpidemicUpdate L K s t).2 t hfields.2.2.1 hbias.2 htNo
  have hmono := Transition_atom_pair_mono_of_phaseSeven
    sigma ell hell (phaseEpidemicUpdate L K s t).1
    (phaseEpidemicUpdate L K s t).2 hep.1 hep.2 hNoLeft hNoRight
  rw [Transition_eq_Transition_epidemic_of_phaseSeven s t hep.1 hep.2]
  linarith

private theorem Transition_noShallow_pair_of_epidemic_seven
    (ell : Fin (L + 1)) (s t : AgentState L K)
    (hs5 : 5 ≤ s.phase.val) (ht5 : 5 ≤ t.phase.val)
    (hep : (phaseEpidemicUpdate L K s t).1.phase.val = 7 ∧
      (phaseEpidemicUpdate L K s t).2.phase.val = 7)
    (hsNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val s)
    (htNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val t) :
    (¬ Phase6Convergence.highSt
        (L := L) (K := K) ell.val (Transition L K s t).1) ∧
      (¬ Phase6Convergence.highSt
        (L := L) (K := K) ell.val (Transition L K s t).2) := by
  have hbias := Phase6Convergence.phaseEpidemicUpdate_bias_ge_five
    (L := L) (K := K) s t hs5 ht5
  have hfields := ReserveSampling.phaseEpidemicUpdate_role_hour_ge5
    (L := L) (K := K) s t hs5 ht5
  have hNoLeft := noShallowAgent_of_staticFields ell
    (phaseEpidemicUpdate L K s t).1 s hfields.1 hbias.1 hsNo
  have hNoRight := noShallowAgent_of_staticFields ell
    (phaseEpidemicUpdate L K s t).2 t hfields.2.2.1 hbias.2 htNo
  rw [Transition_eq_Transition_epidemic_of_phaseSeven s t hep.1 hep.2]
  exact Transition_noShallow_pair_of_phaseSeven
    ell _ _ hep.1 hep.2 hNoLeft hNoRight

/-- Full actual dispatch on a `6/7` source pair.  The `6/6` branch reuses
the Phase-6 dispatch; every branch containing a `7` performs Init 7 and then the literal
Phase-7 table. -/
theorem Transition_atom_pair_mono_of_phaseSixOrSeven
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K)
    (hs : s.phase.val = 6 ∨ s.phase.val = 7)
    (ht : t.phase.val = 6 ∨ t.phase.val = 7)
    (hsNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val s)
    (htNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val t) :
    lateBiasedResourceAtom sigma ell hell s +
        lateBiasedResourceAtom sigma ell hell t ≤
      lateBiasedResourceAtom sigma ell hell (Transition L K s t).1 +
        lateBiasedResourceAtom sigma ell hell (Transition L K s t).2 := by
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · exact Transition_atom_pair_mono_of_phaseSixDispatch
      sigma ell hell s t (.six_six hs ht)
  · exact Transition_atom_pair_mono_of_epidemic_seven
      sigma ell hell s t (by omega) (by omega)
      (phaseEpidemicUpdate_phases_seven_of_six_seven s t hs ht) hsNo htNo
  · exact Transition_atom_pair_mono_of_epidemic_seven
      sigma ell hell s t (by omega) (by omega)
      (phaseEpidemicUpdate_phases_seven_of_seven_six s t hs ht) hsNo htNo
  · exact Transition_atom_pair_mono_of_phaseSeven
      sigma ell hell s t hs ht hsNo htNo

/-- The same actual dispatch preserves Lemma 10's no-shallow predicate. -/
theorem Transition_noShallow_pair_of_phaseSixOrSeven
    (ell : Fin (L + 1)) (s t : AgentState L K)
    (hs : s.phase.val = 6 ∨ s.phase.val = 7)
    (ht : t.phase.val = 6 ∨ t.phase.val = 7)
    (hsNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val s)
    (htNo : ¬ Phase6Convergence.highSt
      (L := L) (K := K) ell.val t) :
    (¬ Phase6Convergence.highSt
        (L := L) (K := K) ell.val (Transition L K s t).1) ∧
      (¬ Phase6Convergence.highSt
        (L := L) (K := K) ell.val (Transition L K s t).2) := by
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · rw [Phase6Convergence.Transition_eq_Phase6Transition_of_phase6
      (L := L) (K := K) s t hs ht]
    exact Phase6Transition_noShallow_pair ell s t
      (by omega) (by omega) hsNo htNo
  · exact Transition_noShallow_pair_of_epidemic_seven
      ell s t (by omega) (by omega)
      (phaseEpidemicUpdate_phases_seven_of_six_seven s t hs ht) hsNo htNo
  · exact Transition_noShallow_pair_of_epidemic_seven
      ell s t (by omega) (by omega)
      (phaseEpidemicUpdate_phases_seven_of_seven_six s t hs ht) hsNo htNo
  · exact Transition_noShallow_pair_of_phaseSeven
      ell s t hs ht hsNo htNo

/-- One source-guarded actual step.  The source is reachable and lies in the
common `5..7` envelope; the final target is allowed to be the first Phase-8
configuration. -/
structure PhaseSixSevenCreditStep
    (init c d : Config (AgentState L K)) : Prop where
  source_reachable : ReachablePhaseSixWindow init c
  source_window : Phase6To7Window (L := L) (K := K) c
  step : (NonuniformMajority L K).StepRel c d

def PhaseSixSevenCreditReachable
    (init c d : Config (AgentState L K)) : Prop :=
  Relation.ReflTransGen (PhaseSixSevenCreditStep init) c d

/-- One reachable source step preserves both the no-shallow invariant and J. -/
theorem phaseSixSevenCreditStep_preserves
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    {init c d : Config (AgentState L K)}
    (hNo : NoShallowMain ell c)
    (hstep : PhaseSixSevenCreditStep init c d) :
    NoShallowMain ell d ∧
      lateBiasedResourceCredit sigma ell hell c ≤
        lateBiasedResourceCredit sigma ell hell d := by
  rcases hstep.step with ⟨s, t, happ, hd0⟩
  have hd : d = c - ({s, t} : Config (AgentState L K)) +
      ({(Transition L K s t).1, (Transition L K s t).2} :
        Config (AgentState L K)) := hd0
  have hsmem : s ∈ c := Multiset.mem_of_le happ (by simp)
  have htmem : t ∈ c := Multiset.mem_of_le happ (by simp)
  have hsphase := hstep.source_window s hsmem
  have htphase := hstep.source_window t htmem
  have hsNo := hNo s hsmem
  have htNo := hNo t htmem
  have hpairCredit := Transition_atom_pair_mono_of_phaseSixOrSeven
    sigma ell hell s t hsphase htphase hsNo htNo
  have hpairNo := Transition_noShallow_pair_of_phaseSixOrSeven
    ell s t hsphase htphase hsNo htNo
  have hsub : ({s, t} : Config (AgentState L K)) ≤ c := happ
  constructor
  · rw [hd]
    intro a ha
    rw [Multiset.mem_add] at ha
    rcases ha with hold | hnew
    · exact hNo a (Multiset.mem_of_le (Multiset.sub_le_self c {s, t}) hold)
    · have hnew' : a = (Transition L K s t).1 ∨ a = (Transition L K s t).2 := by
        simpa using hnew
      rcases hnew' with hleft | hright
      · rw [hleft]; exact hpairNo.1
      · rw [hright]; exact hpairNo.2
  · rw [hd]
    have hadd1 := lateBiasedResourceCredit_add sigma ell hell
      (c - {s, t}) ({s, t} : Config (AgentState L K))
    have hadd2 := lateBiasedResourceCredit_add sigma ell hell
      (c - {s, t})
      ({(Transition L K s t).1, (Transition L K s t).2} :
        Config (AgentState L K))
    have hc : c - {s, t} + ({s, t} : Config (AgentState L K)) = c :=
      tsub_add_cancel_of_le hsub
    rw [hc] at hadd1
    rw [hadd2]
    have hp1 := lateBiasedResourceCredit_pair sigma ell hell s t
    have hp2 := lateBiasedResourceCredit_pair sigma ell hell
      (Transition L K s t).1 (Transition L K s t).2
    linarith

/-- Iteration through the whole source-guarded mixed 6/7 route. -/
theorem phaseSixSevenCreditReachable_preserves
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    {init c d : Config (AgentState L K)}
    (hreach : PhaseSixSevenCreditReachable init c d)
    (hNo : NoShallowMain ell c) :
    NoShallowMain ell d ∧
      lateBiasedResourceCredit sigma ell hell c ≤
        lateBiasedResourceCredit sigma ell hell d := by
  induction hreach with
  | refl => exact ⟨hNo, le_rfl⟩
  | tail _ hlast ih =>
      have hnext := phaseSixSevenCreditStep_preserves
        sigma ell hell ih.1 hlast
      exact ⟨hnext.1, ih.2.trans hnext.2⟩

/-- Forgetting reachability metadata recovers the seam relation used by
`phase6To7FuelLedger_of_reachable`. -/
theorem phaseSixSevenCreditReachable_to_phaseSixToSevenReachable
    {init c d : Config (AgentState L K)}
    (hreach : PhaseSixSevenCreditReachable init c d) :
    Phase6To7Reachable (L := L) (K := K) c d := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlast ih =>
      exact ih.tail ⟨hlast.source_window, hlast.step⟩

/-- The `5..7` envelope is preserved only before the first Phase-8
escape.  Without `hbelow`, a Phase-7 Clock with zero counter is the literal
counterexample: its trailing update advances it to Phase 8. -/
theorem reachablePhaseSixWindow_after_step_of_beforeEight
    {init c d : Config (AgentState L K)}
    (hstep : PhaseSixSevenCreditStep init c d)
    (hbelow : ∀ a ∈ d, a.phase.val < 8) :
    ReachablePhaseSixWindow init d := by
  rcases hstep.step with ⟨s, t, happ, hd0⟩
  have hd : d = c - ({s, t} : Config (AgentState L K)) +
      ({(Transition L K s t).1, (Transition L K s t).2} :
        Config (AgentState L K)) := hd0
  have hsmem : s ∈ c := Multiset.mem_of_le happ (by simp)
  have htmem : t ∈ c := Multiset.mem_of_le happ (by simp)
  have hslo := (hstep.source_reachable.phase_range s hsmem).1
  have htlo := (hstep.source_reachable.phase_range t htmem).1
  have hmono := Transition_phase_monotone (L := L) (K := K) s t
  refine ⟨hstep.source_reachable.reachable.tail hstep.step, ?_⟩
  rw [hd]
  intro a ha
  have hupper := hbelow a (by rw [hd]; exact ha)
  rw [Multiset.mem_add] at ha
  rcases ha with hold | hnew
  · have holdMem := Multiset.mem_of_le (Multiset.sub_le_self c {s, t}) hold
    exact ⟨(hstep.source_reachable.phase_range a holdMem).1, by omega⟩
  · have hnew' : a = (Transition L K s t).1 ∨ a = (Transition L K s t).2 := by
      simpa using hnew
    rcases hnew' with hleft | hright
    · rw [hleft] at hupper ⊢
      exact ⟨hslo.trans hmono.1, by omega⟩
    · rw [hright] at hupper ⊢
      exact ⟨htlo.trans hmono.2, by omega⟩

/-!
CLOSES
* All five `cancelSplit` rows, including corrected gap two.
* Exact Phase-7 dispatch, Init 7, and trailing Clock updates.
* Actual `6/7`, `7/6`, `7/7`, and residual `6/6` pairs.
* Preservation of `NoShallowMain` by Phase 6 and Phase 7.
* Reachability-scoped configuration transport of J.
* The genuine non-closure diagnosis at the first Phase-8 seed.

UNFINISHED
* The original-law constructor of a finite first-Phase-8 route is not in the
  selected-level failure set in the library; the next file exposes that producer.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateBiasedResourceCreditPhaseSeven

end
