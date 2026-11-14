-- Ripple/PopulationProtocol/ExactMajority/Probability/LateBiasedResourceCreditPath.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateBiasedResourceCreditPhaseSeven

/-!
# Lemma 11 path receipt, the .806 ledger, and deterministic consumers

Theorem list:
* `simpleResourceCredit`, `simpleResourceCredit_initialFloor`
* `PhaseFiveSixCreditStep`, `PhaseFiveSixCreditReachable`
* `phaseFiveSixCreditReachable_credit_mono`
* `phaseFiveSixCreditReachable_simple_mono`
* `phaseSixSevenCreditReachable_simple_mono`
* `LemmaElevenEntry`
* `LemmaElevenPathReceipt`
* `LemmaElevenPathReceipt.credit_at`
* `LemmaElevenPathReceipt.noShallow_at`
* `LemmaElevenPathReceipt.simple_at`
* `LemmaElevenPathReceipt.fuelLedger_at`
* `PhaseSevenBandConsumer`, `phaseSeven_band_hazard_floor`
* `PhaseEightCreditConsumer`

This file closes the deterministic pathwise instance and both consumer forms.
Its final comment identifies the two producer fields not yet packaged in the library.
-/

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority.LateBiasedResourceCreditPath

open TimeTheorem
open LateBiasedResourceCredit
open LateBiasedResourceCreditPhaseSix
open LateBiasedResourceCreditPhaseSeven
open Phase7BandDefs
open Phase7MajorityBlockLedger
open Phase6BlockSnapshot
open LateMixedFuelLedger

variable {L K : ℕ}

/-- A pair step increases any additive credit whose pair atoms increase. -/
private theorem credit_step_mono_of_pair
    (cred : Config (AgentState L K) → ℤ) (atom : AgentState L K → ℤ)
    (hadd : ∀ a b, cred (a + b) = cred a + cred b)
    (hpairEq : ∀ a b : AgentState L K, cred {a, b} = atom a + atom b)
    {c d : Config (AgentState L K)} {s t : AgentState L K}
    (hsub : ({s, t} : Config (AgentState L K)) ≤ c)
    (hd : d = c - {s, t} +
      ({(Transition L K s t).1, (Transition L K s t).2} :
        Config (AgentState L K)))
    (hmono : atom s + atom t ≤
      atom (Transition L K s t).1 + atom (Transition L K s t).2) :
    cred c ≤ cred d := by
  have hadd1 := hadd (c - {s, t}) ({s, t} : Config (AgentState L K))
  have hadd2 := hadd (c - {s, t})
    ({(Transition L K s t).1, (Transition L K s t).2} :
      Config (AgentState L K))
  have hc : c - {s, t} + ({s, t} : Config (AgentState L K)) = c :=
    tsub_add_cancel_of_le hsub
  rw [hc] at hadd1
  rw [hd, hadd2]
  have hp1 := hpairEq s t
  have hp2 := hpairEq (Transition L K s t).1 (Transition L K s t).2
  linarith

/-- Equation (51) as an integer-valued margin. -/
def simpleResourceCredit (sigma : Sign) (ell : Fin (L + 1))
    (c : Config (AgentState L K)) : ℤ :=
  (majorityBlockCount (L := L) (K := K) sigma ell.val c : ℤ) -
    (minorityDebt (L := L) (K := K) sigma ell.val c : ℤ) -
    (dangerousReserveCount (L := L) (K := K) ell.val c : ℤ)

/-- Per-agent version used by pair steps. -/
def simpleResourceAtom (sigma : Sign) (ell : Fin (L + 1))
    (a : AgentState L K) : ℤ :=
  (majorityBlockUnit (L := L) (K := K) sigma ell.val a : ℤ) -
    (minorityDebtUnit (L := L) (K := K) sigma ell.val a : ℤ) -
    (dangerousReserveUnit (L := L) (K := K) ell.val a : ℤ)

@[simp] theorem simpleResourceCredit_add
    (sigma : Sign) (ell : Fin (L + 1))
    (a b : Config (AgentState L K)) :
    simpleResourceCredit sigma ell (a + b) =
      simpleResourceCredit sigma ell a + simpleResourceCredit sigma ell b := by
  unfold simpleResourceCredit
  rw [majorityBlockCount_add, minorityDebt_add, dangerousReserveCount_add]
  push_cast
  ring

@[simp] theorem simpleResourceCredit_pair
    (sigma : Sign) (ell : Fin (L + 1)) (a b : AgentState L K) :
    simpleResourceCredit sigma ell ({a, b} : Config (AgentState L K)) =
      simpleResourceAtom sigma ell a + simpleResourceAtom sigma ell b := by
  unfold simpleResourceCredit simpleResourceAtom
  rw [majorityBlockCount_pair, minorityDebt_pair, dangerousReserveCount_pair]
  push_cast
  ring

private theorem simple_majorityBlockUnit_eq
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

private theorem simpleResourceAtom_eq_of_staticFields
    (sigma : Sign) (ell : Fin (L + 1)) (x y : AgentState L K)
    (hrole : x.role = y.role) (hbias : x.bias = y.bias)
    (hhour : y.role = Role.reserve → x.hour = y.hour) :
    simpleResourceAtom sigma ell x = simpleResourceAtom sigma ell y := by
  have hQ := simple_majorityBlockUnit_eq (L := L) (K := K)
    sigma ell.val x y hrole hbias
  have hD : minorityDebtUnit sigma ell.val x =
      minorityDebtUnit sigma ell.val y := by
    unfold minorityDebtUnit
    rw [hrole, hbias]
  have hS : dangerousReserveUnit ell.val x = dangerousReserveUnit ell.val y := by
    unfold dangerousReserveUnit
    by_cases hy : y.role = Role.reserve
    · have hx : x.role = Role.reserve := by simpa [hrole] using hy
      rw [hhour hy]
      simp [hx, hy]
    · have hx : x.role ≠ Role.reserve := by simpa [hrole] using hy
      simp [hx, hy]
  unfold simpleResourceAtom
  rw [hQ, hD, hS]

/-- Exact .806 entry margin: `.92 - .064 - .05`. -/
theorem simpleResourceCredit_initialFloor
    (sigma : Sign) (ell : Fin (L + 1)) (M : ℕ)
    (c : Config (AgentState L K))
    (hblock : 920 * M ≤ 1000 * majorityBlockCount sigma ell.val c)
    (hminor : 1000 * minorityDebt sigma ell.val c ≤ 64 * M)
    (hdanger : 1000 * dangerousReserveCount ell.val c ≤ 50 * M) :
    (806 : ℤ) * (M : ℤ) ≤
      1000 * simpleResourceCredit sigma ell c := by
  have hnat :
      806 * M + 1000 * minorityDebt sigma ell.val c +
          1000 * dangerousReserveCount ell.val c ≤
        1000 * majorityBlockCount sigma ell.val c := by
    omega
  have hint :
      (806 : ℤ) * (M : ℤ) +
          1000 * (minorityDebt sigma ell.val c : ℤ) +
          1000 * (dangerousReserveCount ell.val c : ℤ) ≤
        1000 * (majorityBlockCount sigma ell.val c : ℤ) := by
    exact_mod_cast hnat
  unfold simpleResourceCredit
  push_cast at hint ⊢
  omega

private theorem not_unsampled_of_reserveSampled
    (c : Config (AgentState L K))
    (hsampled : ReserveSampling.ReserveSampled (L := L) (K := K) c)
    (a : AgentState L K) (ha : a ∈ c) :
    ¬ ReserveSampling.unsampled (L := L) (K := K) a := by
  unfold ReserveSampling.ReserveSampled
    ReserveSampling.unsampledReserveU at hsampled
  rw [Multiset.countP_eq_zero] at hsampled
  exact hsampled a ha

private theorem Transition_atom_pair_eq_of_locked_five_five
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 5)
    (hslocked : ¬ ReserveSampling.unsampled (L := L) (K := K) s)
    (htlocked : ¬ ReserveSampling.unsampled (L := L) (K := K) t) :
    lateBiasedResourceAtom sigma ell hell (Transition L K s t).1 +
        lateBiasedResourceAtom sigma ell hell (Transition L K s t).2 =
      lateBiasedResourceAtom sigma ell hell s +
        lateBiasedResourceAtom sigma ell hell t := by
  rw [ReserveSampling.Transition_eq_Phase5Transition_of_phase5
    (L := L) (K := K) s t hs ht]
  apply congrArg₂ (· + ·)
  · apply lateBiasedResourceAtom_eq_of_staticFields sigma ell hell _ s
    · exact Phase5Convergence.Phase5Transition_fst_role_eq
        (L := L) (K := K) s t hs
    · exact Phase5Convergence.Phase5Transition_fst_bias_eq
        (L := L) (K := K) s t hs
    · intro hreserve
      apply Phase5Convergence.Phase5Transition_fst_hour_eq_of_reserve_ne_L
        (L := L) (K := K) s t hreserve
      exact fun heq => hslocked ⟨hreserve, heq⟩
  · apply lateBiasedResourceAtom_eq_of_staticFields sigma ell hell _ t
    · exact Phase5Convergence.Phase5Transition_snd_role_eq
        (L := L) (K := K) s t ht
    · exact Phase5Convergence.Phase5Transition_snd_bias_eq
        (L := L) (K := K) s t ht
    · intro hreserve
      apply Phase5Convergence.Phase5Transition_snd_hour_eq_of_reserve_ne_L
        (L := L) (K := K) s t hreserve
      exact fun heq => htlocked ⟨hreserve, heq⟩

private theorem Transition_simple_pair_eq_of_locked_five_five
    (sigma : Sign) (ell : Fin (L + 1))
    (s t : AgentState L K)
    (hs : s.phase.val = 5) (ht : t.phase.val = 5)
    (hslocked : ¬ ReserveSampling.unsampled (L := L) (K := K) s)
    (htlocked : ¬ ReserveSampling.unsampled (L := L) (K := K) t) :
    simpleResourceAtom sigma ell (Transition L K s t).1 +
        simpleResourceAtom sigma ell (Transition L K s t).2 =
      simpleResourceAtom sigma ell s + simpleResourceAtom sigma ell t := by
  rw [ReserveSampling.Transition_eq_Phase5Transition_of_phase5
    (L := L) (K := K) s t hs ht]
  apply congrArg₂ (· + ·)
  · apply simpleResourceAtom_eq_of_staticFields sigma ell _ s
    · exact Phase5Convergence.Phase5Transition_fst_role_eq
        (L := L) (K := K) s t hs
    · exact Phase5Convergence.Phase5Transition_fst_bias_eq
        (L := L) (K := K) s t hs
    · intro hreserve
      apply Phase5Convergence.Phase5Transition_fst_hour_eq_of_reserve_ne_L
        (L := L) (K := K) s t hreserve
      exact fun heq => hslocked ⟨hreserve, heq⟩
  · apply simpleResourceAtom_eq_of_staticFields sigma ell _ t
    · exact Phase5Convergence.Phase5Transition_snd_role_eq
        (L := L) (K := K) s t ht
    · exact Phase5Convergence.Phase5Transition_snd_bias_eq
        (L := L) (K := K) s t ht
    · intro hreserve
      apply Phase5Convergence.Phase5Transition_snd_hour_eq_of_reserve_ne_L
        (L := L) (K := K) s t hreserve
      exact fun heq => htlocked ⟨hreserve, heq⟩

private theorem Phase6Transition_simple_pair_mono
    (sigma : Sign) (ell : Fin (L + 1)) (s t : AgentState L K)
    (hs : 6 ≤ s.phase.val) (ht : 6 ≤ t.phase.val) :
    simpleResourceAtom sigma ell s + simpleResourceAtom sigma ell t ≤
      simpleResourceAtom sigma ell (Phase6Transition L K s t).1 +
        simpleResourceAtom sigma ell (Phase6Transition L K s t).2 := by
  have hblock := Phase6Transition_block_danger_pair
    (L := L) (K := K) sigma ell.val s t hs ht
  have hdebt := Phase6Transition_minorityDebt_pair_le
    (L := L) (K := K) sigma ell.val s t hs ht
  have hblockInt := (Nat.cast_le (α := ℤ)).mpr hblock
  have hdebtInt := (Nat.cast_le (α := ℤ)).mpr hdebt
  unfold simpleResourceAtom
  push_cast at hblockInt hdebtInt ⊢
  omega

private theorem Transition_simple_pair_mono_of_phaseSixDispatch
    (sigma : Sign) (ell : Fin (L + 1)) (s t : AgentState L K)
    (hpair : PhaseSixDispatchPair s t) :
    simpleResourceAtom sigma ell s + simpleResourceAtom sigma ell t ≤
      simpleResourceAtom sigma ell (Transition L K s t).1 +
        simpleResourceAtom sigma ell (Transition L K s t).2 := by
  cases hpair with
  | five_six hs ht =>
      rw [Transition_eq_Phase6Transition_of_five_six s t hs ht]
      let sSix := phaseSixEntry (L := L) (K := K) s
      let tSix : AgentState L K := {t with phase := ⟨6, by decide⟩}
      have hmono := Phase6Transition_simple_pair_mono
        sigma ell sSix tSix (by simp [sSix, phaseSixEntry_phase]) (by simp [tSix])
      have hsEq : simpleResourceAtom sigma ell sSix =
          simpleResourceAtom sigma ell s :=
        simpleResourceAtom_eq_of_staticFields sigma ell sSix s
          (phaseSixEntry_role s) (phaseSixEntry_bias s)
          (fun _ => phaseSixEntry_hour s)
      have htEq : simpleResourceAtom sigma ell tSix =
          simpleResourceAtom sigma ell t :=
        simpleResourceAtom_eq_of_staticFields sigma ell tSix t rfl rfl
          (fun _ => rfl)
      linarith
  | six_five hs ht =>
      rw [Transition_eq_Phase6Transition_of_six_five s t hs ht]
      let sSix : AgentState L K := {s with phase := ⟨6, by decide⟩}
      let tSix := phaseSixEntry (L := L) (K := K) t
      have hmono := Phase6Transition_simple_pair_mono
        sigma ell sSix tSix (by simp [sSix]) (by simp [tSix, phaseSixEntry_phase])
      have htEq : simpleResourceAtom sigma ell tSix =
          simpleResourceAtom sigma ell t :=
        simpleResourceAtom_eq_of_staticFields sigma ell tSix t
          (phaseSixEntry_role t) (phaseSixEntry_bias t)
          (fun _ => phaseSixEntry_hour t)
      have hsEq : simpleResourceAtom sigma ell sSix =
          simpleResourceAtom sigma ell s :=
        simpleResourceAtom_eq_of_staticFields sigma ell sSix s rfl rfl
          (fun _ => rfl)
      linarith
  | six_six hs ht =>
      rw [Phase6Convergence.Transition_eq_Phase6Transition_of_phase6
        (L := L) (K := K) s t hs ht]
      exact Phase6Transition_simple_pair_mono
        sigma ell s t (by omega) (by omega)

/-- Existing block/debt/danger accounting gives monotonicity of (51) on every
actual `6/7` source pair. -/
theorem Transition_simple_pair_mono_of_phaseSixOrSeven
    (sigma : Sign) (ell : Fin (L + 1)) (s t : AgentState L K)
    (hs : s.phase.val = 6 ∨ s.phase.val = 7)
    (ht : t.phase.val = 6 ∨ t.phase.val = 7) :
    simpleResourceAtom sigma ell s + simpleResourceAtom sigma ell t ≤
      simpleResourceAtom sigma ell (Transition L K s t).1 +
        simpleResourceAtom sigma ell (Transition L K s t).2 := by
  have hledger := Transition_block_debt_danger_pair_of_phase_six_or_seven
    (L := L) (K := K) sigma ell.val s t hs ht
  have hint := (Nat.cast_le (α := ℤ)).mpr hledger
  unfold simpleResourceAtom
  push_cast at hint ⊢
  omega

/-- Reachability-scoped Phase-5/6 source step, including locked `(5,5)` pairs. -/
structure PhaseFiveSixCreditStep
    (init : Config (AgentState L K)) (n : ℕ)
    (c d : Config (AgentState L K)) : Prop where
  source_reachable : ReachablePhaseSixWindow init c
  source_window : MixedFiveSixWin (L := L) (K := K) n c
  sampled : ReserveSampling.ReserveSampled (L := L) (K := K) c
  step : (NonuniformMajority L K).StepRel c d

def PhaseFiveSixCreditReachable
    (init : Config (AgentState L K)) (n : ℕ)
    (c d : Config (AgentState L K)) : Prop :=
  Relation.ReflTransGen (PhaseFiveSixCreditStep init n) c d

private theorem phaseFiveSixCreditStep_pair_data
    {init c d : Config (AgentState L K)} {n : ℕ}
    (hstep : PhaseFiveSixCreditStep init n c d) :
    ∃ s t, Protocol.Applicable c s t ∧
      (s.phase.val = 5 ∨ s.phase.val = 6) ∧
      (t.phase.val = 5 ∨ t.phase.val = 6) ∧
      ¬ ReserveSampling.unsampled (L := L) (K := K) s ∧
      ¬ ReserveSampling.unsampled (L := L) (K := K) t ∧
      d = c - {s, t} + {(Transition L K s t).1, (Transition L K s t).2} := by
  rcases hstep.step with ⟨s, t, happ, hd⟩
  have hsmem : s ∈ c := Multiset.mem_of_le happ (by simp)
  have htmem : t ∈ c := Multiset.mem_of_le happ (by simp)
  exact ⟨s, t, happ, hstep.source_window.2 s hsmem,
    hstep.source_window.2 t htmem,
    not_unsampled_of_reserveSampled c hstep.sampled s hsmem,
    not_unsampled_of_reserveSampled c hstep.sampled t htmem, hd⟩

/-- One actual locked Phase-5/6 source step preserves J. -/
theorem phaseFiveSixCreditStep_credit_mono
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    {init c d : Config (AgentState L K)} {n : ℕ}
    (hstep : PhaseFiveSixCreditStep init n c d) :
    lateBiasedResourceCredit sigma ell hell c ≤
      lateBiasedResourceCredit sigma ell hell d := by
  obtain ⟨s, t, happ, hs, ht, hslocked, htlocked, hd⟩ :=
    phaseFiveSixCreditStep_pair_data hstep
  have hpair :
      lateBiasedResourceAtom sigma ell hell s +
          lateBiasedResourceAtom sigma ell hell t ≤
        lateBiasedResourceAtom sigma ell hell (Transition L K s t).1 +
          lateBiasedResourceAtom sigma ell hell (Transition L K s t).2 := by
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact (Transition_atom_pair_eq_of_locked_five_five
        sigma ell hell s t hs ht hslocked htlocked).ge
    · exact Transition_atom_pair_mono_of_phaseSixDispatch
        sigma ell hell s t (.five_six hs ht)
    · exact Transition_atom_pair_mono_of_phaseSixDispatch
        sigma ell hell s t (.six_five hs ht)
    · exact Transition_atom_pair_mono_of_phaseSixDispatch
        sigma ell hell s t (.six_six hs ht)
  have hsub : ({s, t} : Config (AgentState L K)) ≤ c := happ
  exact credit_step_mono_of_pair (lateBiasedResourceCredit sigma ell hell) (lateBiasedResourceAtom sigma ell hell)
    (lateBiasedResourceCredit_add sigma ell hell )
    (lateBiasedResourceCredit_pair sigma ell hell )
    hsub hd hpair

/-- The same source step preserves the exact .806 simple margin. -/
theorem phaseFiveSixCreditStep_simple_mono
    (sigma : Sign) (ell : Fin (L + 1))
    {init c d : Config (AgentState L K)} {n : ℕ}
    (hstep : PhaseFiveSixCreditStep init n c d) :
    simpleResourceCredit sigma ell c ≤ simpleResourceCredit sigma ell d := by
  obtain ⟨s, t, happ, hs, ht, hslocked, htlocked, hd⟩ :=
    phaseFiveSixCreditStep_pair_data hstep
  have hpair :
      simpleResourceAtom sigma ell s + simpleResourceAtom sigma ell t ≤
        simpleResourceAtom sigma ell (Transition L K s t).1 +
          simpleResourceAtom sigma ell (Transition L K s t).2 := by
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact (Transition_simple_pair_eq_of_locked_five_five
        sigma ell s t hs ht hslocked htlocked).ge
    · exact Transition_simple_pair_mono_of_phaseSixDispatch
        sigma ell s t (.five_six hs ht)
    · exact Transition_simple_pair_mono_of_phaseSixDispatch
        sigma ell s t (.six_five hs ht)
    · exact Transition_simple_pair_mono_of_phaseSixDispatch
        sigma ell s t (.six_six hs ht)
  have hsub : ({s, t} : Config (AgentState L K)) ≤ c := happ
  exact credit_step_mono_of_pair (simpleResourceCredit sigma ell) (simpleResourceAtom sigma ell)
    (simpleResourceCredit_add sigma ell )
    (simpleResourceCredit_pair sigma ell )
    hsub hd hpair

theorem phaseFiveSixCreditReachable_credit_mono
    (sigma : Sign) (ell : Fin (L + 1)) (hell : ell.val + 2 ≤ L)
    {init c d : Config (AgentState L K)} {n : ℕ}
    (hreach : PhaseFiveSixCreditReachable init n c d) :
    lateBiasedResourceCredit sigma ell hell c ≤
      lateBiasedResourceCredit sigma ell hell d := by
  induction hreach with
  | refl => exact le_rfl
  | tail _ hlast ih =>
      exact ih.trans (phaseFiveSixCreditStep_credit_mono
        sigma ell hell hlast)

theorem phaseFiveSixCreditReachable_simple_mono
    (sigma : Sign) (ell : Fin (L + 1))
    {init c d : Config (AgentState L K)} {n : ℕ}
    (hreach : PhaseFiveSixCreditReachable init n c d) :
    simpleResourceCredit sigma ell c ≤ simpleResourceCredit sigma ell d := by
  induction hreach with
  | refl => exact le_rfl
  | tail _ hlast ih =>
      exact ih.trans (phaseFiveSixCreditStep_simple_mono sigma ell hlast)

/-- Simple-margin transport on the source-guarded mixed 6/7 relation. -/
theorem phaseSixSevenCreditStep_simple_mono
    (sigma : Sign) (ell : Fin (L + 1))
    {init c d : Config (AgentState L K)}
    (hstep : PhaseSixSevenCreditStep init c d) :
    simpleResourceCredit sigma ell c ≤ simpleResourceCredit sigma ell d := by
  rcases hstep.step with ⟨s, t, happ, hd⟩
  have hsmem : s ∈ c := Multiset.mem_of_le happ (by simp)
  have htmem : t ∈ c := Multiset.mem_of_le happ (by simp)
  have hpair := Transition_simple_pair_mono_of_phaseSixOrSeven
    sigma ell s t (hstep.source_window s hsmem)
      (hstep.source_window t htmem)
  have hsub : ({s, t} : Config (AgentState L K)) ≤ c := happ
  exact credit_step_mono_of_pair (simpleResourceCredit sigma ell) (simpleResourceAtom sigma ell)
    (simpleResourceCredit_add sigma ell )
    (simpleResourceCredit_pair sigma ell )
    hsub hd hpair

theorem phaseSixSevenCreditReachable_simple_mono
    (sigma : Sign) (ell : Fin (L + 1))
    {init c d : Config (AgentState L K)}
    (hreach : PhaseSixSevenCreditReachable init c d) :
    simpleResourceCredit sigma ell c ≤ simpleResourceCredit sigma ell d := by
  induction hreach with
  | refl => exact le_rfl
  | tail _ hlast ih =>
      exact ih.trans (phaseSixSevenCreditStep_simple_mono sigma ell hlast)

/-- The actual completed-snapshot inputs consumed by the credit transport. -/
structure LemmaElevenEntry {n M R : ℕ}
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma tau : Sign) (c : InputCfg n) : Prop where
  snapshot : LateSamplingCorrectedFuelProducer.CompletedRowTwoFuelSnapshot
    (n := n) ell tau M R c
  block : 920 * M ≤ 1000 * majorityBlockCount sigma ell.val c
  main_count : RoleSplitConcentration.mainCount c = M
  minority : 1000 * minorityDebt sigma ell.val c ≤ 64 * M
  dangerous : 1000 * dangerousReserveCount ell.val c ≤ 50 * M

namespace LemmaElevenEntry

 theorem creditFloor {n M R : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign} {c : InputCfg n}
    (h : LemmaElevenEntry (M := M) (R := R) ell hell sigma tau c) :
    (544 : ℤ) * (M : ℤ) ≤
      1000 * lateBiasedResourceCredit sigma ell hell c :=
  lateBiasedResourceCredit_initialFloor
    ell hell sigma tau c h.snapshot h.block h.main_count h.minority h.dangerous

 theorem simpleFloor {n M R : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign} {c : InputCfg n}
    (h : LemmaElevenEntry (M := M) (R := R) ell hell sigma tau c) :
    (806 : ℤ) * (M : ℤ) ≤ 1000 * simpleResourceCredit sigma ell c :=
  simpleResourceCredit_initialFloor sigma ell M c
    h.block h.minority h.dangerous

 theorem fuelLedgerFloor {n M R : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign} {c : InputCfg n}
    (h : LemmaElevenEntry (M := M) (R := R) ell hell sigma tau c) :
    Phase6To7FuelLedger sigma ell.val (806 * M / 1000) c := by
  have hfloor := Nat.div_mul_le_self (806 * M) 1000
  have h1 := h.minority
  have h2 := h.dangerous
  have h3 := h.block
  unfold Phase6To7FuelLedger
  omega

end LemmaElevenEntry

/-- Monotonicity of the integer margin transports any existing
`Phase6To7FuelLedger` without redoing pair arithmetic. -/
theorem phase6To7FuelLedger_of_simpleResourceCredit_le
    (sigma : Sign) (ell : Fin (L + 1)) (G : ℕ)
    (c d : Config (AgentState L K))
    (hledger : Phase6To7FuelLedger sigma ell.val G c)
    (hmono : simpleResourceCredit sigma ell c ≤
      simpleResourceCredit sigma ell d) :
    Phase6To7FuelLedger sigma ell.val G d := by
  have hledgerZ :
      (G : ℤ) + (minorityDebt sigma ell.val c : ℤ) +
          (dangerousReserveCount ell.val c : ℤ) ≤
        (majorityBlockCount sigma ell.val c : ℤ) := by
    exact_mod_cast hledger
  have hgoalZ :
      (G : ℤ) + (minorityDebt sigma ell.val d : ℤ) +
          (dangerousReserveCount ell.val d : ℤ) ≤
        (majorityBlockCount sigma ell.val d : ℤ) := by
    unfold simpleResourceCredit at hmono
    omega
  exact_mod_cast hgoalZ

/-- Concrete per-log receipt.  It contains no all-log premise.  The two route
fields contain only actual reachable source steps. -/
structure LemmaElevenPathReceipt {n M R : ℕ}
    (init : InputCfg n) (omega : InputLog n)
    (completed seven eight : ℕ)
    (ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1))
    (hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n)
    (sigma tau : Sign) : Prop where
  good_input : ThresholdEpidemic.GoodInput n init
  small_history : omega ∈ LateStrengthening.smallHistory init
  selected_good :
    omega ∉ LatePhaseSixDrainSelectedLevel.smallGapPhaseSixDrainFailure init
  order : completed ≤ seven ∧ seven ≤ eight
  seven_time : LateMixedFiveSixWindow.firstPhaseSevenStart init omega =
    (seven : WithTop ℕ)
  eight_seed : firstPhaseSeed init 8 eight omega
  entry : LemmaElevenEntry (M := M) (R := R) ell hell sigma tau (trace init omega completed)
  before_seven :
    ∀ t, completed ≤ t → t ≤ seven →
      PhaseFiveSixCreditReachable init n
        (trace init omega completed) (trace init omega t)
  no_shallow_seven : NoShallowMain ell (trace init omega seven)
  after_seven :
    ∀ t, seven ≤ t → t ≤ eight →
      PhaseSixSevenCreditReachable init
        (trace init omega seven) (trace init omega t)

namespace LemmaElevenPathReceipt

/-- J is at least `.544 M` at every requested time. -/
theorem credit_at {n M R : ℕ}
    {init : InputCfg n} {omega : InputLog n}
    {completed seven eight t : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (h : LemmaElevenPathReceipt (M := M) (R := R) init omega completed seven eight
      ell hell sigma tau)
    (hct : completed ≤ t) (hte : t ≤ eight) :
    (544 : ℤ) * (M : ℤ) ≤
      1000 * lateBiasedResourceCredit sigma ell hell (trace init omega t) := by
  by_cases hts : t ≤ seven
  · have hmono := phaseFiveSixCreditReachable_credit_mono
      sigma ell hell (h.before_seven t hct hts)
    exact h.entry.creditFloor.trans (mul_le_mul_of_nonneg_left hmono (by norm_num))
  · have hcreditSeven :
        (544 : ℤ) * (M : ℤ) ≤
          1000 * lateBiasedResourceCredit sigma ell hell
            (trace init omega seven) := by
      have hmono := phaseFiveSixCreditReachable_credit_mono
        sigma ell hell (h.before_seven seven h.order.1 le_rfl)
      exact h.entry.creditFloor.trans
        (mul_le_mul_of_nonneg_left hmono (by norm_num))
    have hst : seven ≤ t := by omega
    have hroute := h.after_seven t hst hte
    have hmono :=
      (phaseSixSevenCreditReachable_preserves
        sigma ell hell hroute h.no_shallow_seven).2
    exact hcreditSeven.trans
      (mul_le_mul_of_nonneg_left hmono (by norm_num))

/-- Lemma 10's conclusion persists from the first Phase-7 configuration
through the first Phase-8 seed configuration. -/
theorem noShallow_at {n M R : ℕ}
    {init : InputCfg n} {omega : InputLog n}
    {completed seven eight t : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (h : LemmaElevenPathReceipt (M := M) (R := R) init omega completed seven eight
      ell hell sigma tau)
    (hst : seven ≤ t) (hte : t ≤ eight) :
    NoShallowMain ell (trace init omega t) :=
  (phaseSixSevenCreditReachable_preserves sigma ell hell
    (h.after_seven t hst hte) h.no_shallow_seven).1

/-- Exact scaled form of equation (52), without a natural-number floor. -/
theorem simple_at {n M R : ℕ}
    {init : InputCfg n} {omega : InputLog n}
    {completed seven eight t : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (h : LemmaElevenPathReceipt (M := M) (R := R) init omega completed seven eight
      ell hell sigma tau)
    (hct : completed ≤ t) (hte : t ≤ eight) :
    (806 : ℤ) * (M : ℤ) ≤
      1000 * simpleResourceCredit sigma ell (trace init omega t) := by
  by_cases hts : t ≤ seven
  · have hmono := phaseFiveSixCreditReachable_simple_mono
      sigma ell (h.before_seven t hct hts)
    exact h.entry.simpleFloor.trans
      (mul_le_mul_of_nonneg_left hmono (by norm_num))
  · have hsimpleSeven :
        (806 : ℤ) * (M : ℤ) ≤
          1000 * simpleResourceCredit sigma ell
            (trace init omega seven) := by
      have hmono := phaseFiveSixCreditReachable_simple_mono
        sigma ell (h.before_seven seven h.order.1 le_rfl)
      exact h.entry.simpleFloor.trans
        (mul_le_mul_of_nonneg_left hmono (by norm_num))
    have hst : seven ≤ t := by omega
    have hmono := phaseSixSevenCreditReachable_simple_mono
      sigma ell (h.after_seven t hst hte)
    exact hsimpleSeven.trans
      (mul_le_mul_of_nonneg_left hmono (by norm_num))

/-- The existing `Phase6To7FuelLedger` is retained through Phase 7 with the
integer-safe permanent floor `floor(.806 M)`. -/
theorem fuelLedger_at {n M R : ℕ}
    {init : InputCfg n} {omega : InputLog n}
    {completed seven eight t : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (h : LemmaElevenPathReceipt (M := M) (R := R) init omega completed seven eight
      ell hell sigma tau)
    (hst : seven ≤ t) (hte : t ≤ eight) :
    Phase6To7FuelLedger sigma ell.val (806 * M / 1000)
      (trace init omega t) := by
  have hmonoToSeven := phaseFiveSixCreditReachable_simple_mono
    sigma ell (h.before_seven seven h.order.1 le_rfl)
  have hledgerSeven := phase6To7FuelLedger_of_simpleResourceCredit_le
    sigma ell (806 * M / 1000)
    (trace init omega completed) (trace init omega seven)
    h.entry.fuelLedgerFloor hmonoToSeven
  have hmainRoute :=
    phaseSixSevenCreditReachable_to_phaseSixToSevenReachable
      (h.after_seven t hst hte)
  exact phase6To7FuelLedger_of_reachable
    sigma ell.val (806 * M / 1000) hmainRoute hledgerSeven

end LemmaElevenPathReceipt

/-- The exact scaled simple margin implies the literal count form of (52). -/
theorem majorityBlock_scaled_806_of_simple
    (sigma : Sign) (ell : Fin (L + 1)) (M : ℕ)
    (c : Config (AgentState L K))
    (h : (806 : ℤ) * (M : ℤ) ≤
      1000 * simpleResourceCredit sigma ell c) :
    806 * M ≤ 1000 * majorityBlockCount sigma ell.val c := by
  have hsimple : simpleResourceCredit sigma ell c ≤
      (majorityBlockCount sigma ell.val c : ℤ) := by
    unfold simpleResourceCredit
    omega
  have hz : (806 : ℤ) * (M : ℤ) ≤
      1000 * (majorityBlockCount sigma ell.val c : ℤ) :=
    h.trans (mul_le_mul_of_nonneg_left hsimple (by norm_num))
  exact_mod_cast hz

/-- Deterministic Phase-7 handoff: genuine Phase 7, the permanent
ledger, and the exact scaled `.806 M` block count. -/
structure PhaseSevenBandConsumer
    (N M : ℕ) (sigma : Sign) (ell : Fin (L + 1))
    (c : Config (AgentState L K)) : Prop where
  honest : PhaseOnlyWindows.Phase7Win (L := L) (K := K) N c
  simple_scaled : (806 : ℤ) * (M : ℤ) ≤
    1000 * simpleResourceCredit sigma ell c
  ledger : Phase6To7FuelLedger sigma ell.val (806 * M / 1000) c

namespace PhaseSevenBandConsumer

 theorem block_scaled {N M : ℕ} {sigma : Sign} {ell : Fin (L + 1)}
    {c : Config (AgentState L K)}
    (h : PhaseSevenBandConsumer N M sigma ell c) :
    806 * M ≤ 1000 * majorityBlockCount sigma ell.val c :=
  majorityBlock_scaled_806_of_simple sigma ell M c h.simple_scaled

 theorem majorityLedger {N M : ℕ} {sigma : Sign}
    {ell : Fin (L + 1)} {c : Config (AgentState L K)}
    (h : PhaseSevenBandConsumer N M sigma ell c) :
    MajorityBlockLedger sigma ell.val (806 * M / 1000) c :=
  majorityBlockLedger_of_phase6To7FuelLedger
    sigma ell.val (806 * M / 1000) c h.ledger

end PhaseSevenBandConsumer

/-- Lemma 12's two-orientation hazard floor `2(.806 M)/N`.  This is the
real-valued form consumed before replacing the denominator by `n-1`. -/
theorem phaseSeven_band_hazard_floor
    (N M : ℕ) (hN : 0 < N) (sigma : Sign) (ell : Fin (L + 1))
    (c : Config (AgentState L K))
    (h : 806 * M ≤ 1000 * majorityBlockCount sigma ell.val c) :
    (403 / 250 : ℝ) * (M : ℝ) / (N : ℝ) ≤
      2 * (majorityBlockCount sigma ell.val c : ℝ) / (N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hR : (806 : ℝ) * (M : ℝ) ≤
      1000 * (majorityBlockCount sigma ell.val c : ℝ) := by
    exact_mod_cast h
  rw [div_le_div_iff₀ hNR hNR]
  nlinarith

/-- Deterministic Phase-8 handoff.  No Phase-8 transition is claimed here;
`F8` is added in a later file. -/
structure PhaseEightCreditConsumer
    (M : ℕ) (sigma : Sign) (ell : Fin (L + 1))
    (hell : ell.val + 2 ≤ L) (c : Config (AgentState L K)) : Prop where
  credit_scaled : (544 : ℤ) * (M : ℤ) ≤
    1000 * lateBiasedResourceCredit sigma ell hell c
  no_shallow : NoShallowMain ell c
  block_scaled : 806 * M ≤ 1000 * majorityBlockCount sigma ell.val c

/-- The path receipt supplies exactly the first-Phase-8 deterministic input. -/
theorem phaseEightCreditConsumer_of_path {n M R : ℕ}
    {init : InputCfg n} {omega : InputLog n}
    {completed seven eight : ℕ}
    {ell : Fin (PhaseThreeModel.Numeric.hourIndex n + 1)}
    {hell : ell.val + 2 ≤ PhaseThreeModel.Numeric.hourIndex n}
    {sigma tau : Sign}
    (h : LemmaElevenPathReceipt (M := M) (R := R) init omega completed seven eight
      ell hell sigma tau) :
    PhaseEightCreditConsumer M sigma ell hell (trace init omega eight) := by
  refine ⟨h.credit_at (h.order.1.trans h.order.2) le_rfl,
    h.noShallow_at h.order.2 le_rfl, ?_⟩
  exact majorityBlock_scaled_806_of_simple sigma ell M
    (trace init omega eight)
    (h.simple_at (h.order.1.trans h.order.2) le_rfl)

/-!
CLOSES
* Locked `(5,5)` steps omitted from the dispatcher table.
* Exact `.806 M` simple credit and its transport through all `5/6/7` steps.
* Integer-safe `Phase6To7FuelLedger` with floor `806 M / 1000`.
* Deterministic all-times path consumer from the completed snapshot through
  the first Phase-8 seed.
* Lemma-12 block/hazard and Lemma-13 first-Phase-8 consumer forms.

CARRIED PREMISES AND PRODUCERS
* `entry.snapshot`: `StrongSeedReceipt.completion.snapshot` in the library.
* `entry.block`: `LateSamplingSeedReceipt.protectedBand_at`, plus the elementary
  majority-sign/excluded-sign count bridge; this adapter is not packaged.
* `entry.main_count`: `StrongSeedReceipt.completed_main` and
  `labelMainCount_eq_trace` in the library.
* `entry.minority`: low-level producer
  `Phase6BlockSnapshot.minorityDebt_64_of_minorityMass_bound_after_phase34`;
  the fixed N16-to-completed adapter is not packaged.
* `entry.dangerous`: `LateSamplingSentinelBoundary.protectedDangerousRow_of_completion`
  plus `StrongSeedDensity`; the final `.05 M` arithmetic adapter is not packaged.
* `no_shallow_seven`: produced in the library by
  `no_shallow_main_at_firstPhaseSeven_of_smallHistory`, for the selected level.
* `before_seven`: deterministic from `MixedFiveSixPrefix`, sample-lock
  preservation, homogeneous Phase 6, and first-7 minimality; not packaged as
  the relation above.
* `after_seven` and `eight_seed`: OPEN.  The selected-level named failure union
  stops at the first Phase-7 configuration and has no first-8 producer.

UNFINISHED
* A constructor of `LemmaElevenPathReceipt` from only `small_history` and the
  complement of `smallGapPhaseSixDrainFailure`.  It requires the three small
  entry adapters just listed and a named Phase-7/first-8 timer-spread route.
* Phase-7 probability/drift and every Phase-8 transition belong to later rows.
END
-/

end Ripple.PopulationProtocol.ExactMajority.LateBiasedResourceCreditPath

end
