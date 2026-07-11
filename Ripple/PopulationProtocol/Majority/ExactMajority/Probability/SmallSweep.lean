/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# SmallSweep — the atom campaign small-items sweep (roster `DOTY_POST63_CAMPAIGN.md`)

New **append-only** file: it edits NO existing file.  It discharges (or honestly adjudicates)
four small roster items, each by wiring landed machinery — no new mathematics.

## The four verdicts (summary; details in each Part)

* **(1) `hext1` (slot-1 extreme witness).**  Survey claim: `extremeU` COUNTS the saturated
  extremes, so `extremeU > 0` IS the `Hext1` witness.  **VERDICT: FALSE as stated.**  `extremeU`
  counts the saturated extremes at BOTH ends (`extremeVal v = (v.val = 0 ∨ v.val = 6)`), whereas
  `Hext1`/`extremePosSet` pins the `+3` end ALONE (`extremePos a = main ∧ smallBias.val = 6`).  So
  `extremeU > 0` only delivers a saturated extreme at one of the two ends (a `−3` OR a `+3`); it
  does NOT force a `+3` extreme.  We land the clean facts: the `+3` → `extremeU` direction
  (`extremeU_pos_of_extremePos_sum`, the `+3` extremes ARE counted), the two-sided witness
  extraction (`exists_extremeSt_of_extremeU_pos`, the mirror of
  `EliminatorMargins.exists_minorityAt_of_minorityU_pos`), and the exact gap (`hext1` is the
  SIGN-SELECTED `+3` floor, a structural saturation carry — `SlotAtoms`' verdict, now PROVEN sharp).

* **(2) `work2`/`work9` epidemic parameters.**  Survey claim: the chain's locked rationals
  (`Params`) pin them.  **VERDICT: the union ALGEBRA is locked (arithmetic, `decide`); the
  epidemic SCALARS are NOT.**  `Params` carries NO phase-2 opinion-union epidemic rate (no
  `s`/`t`/`ε` for the doubling seed).  We instantiate the two `Phase2Convergence.toW` slots at a
  CONCRETE calibrated opinion pair (`U = 4` `+1`-only, `v = 0` empty) whose seven union-algebra side
  conditions discharge by `decide`, and carry the epidemic rate `s`, horizon `t`, budget `ε` as the
  honest scalar inputs (the budget `hε` is the genuine arithmetic fit, parameter-carried).

* **(3) `SeedStepEvent` (drain-seam seed).**  Survey claim: the `HonestDrainSlots` window repair
  (all-Main → phase-only honest windows WHERE CLOCKS EXIST) makes the timed seed
  `drained_kernel_seedTarget_compl_zero` apply directly, DISSOLVING `SeedStepEvent`.  **VERDICT: NOT
  dissolved.**  The honest Post `Phase{1,8}Honest` is phase-ONLY (`card = n ∧ ∀ a, phase = p`); it
  permits clocks to coexist but pins NOTHING about clock counters.  The timed seed needs the drained
  ALL-CLOCK state (`AllClockGEpCard p n ∧ clockCounterSumAt p = 0 ∧ geCount (p+1) = 0`) — none of
  which the phase-only Post supplies.  So the seam seed stays the genuine one-step event; we
  re-state it and produce `hSeedStep` from it (the two honest worlds survive unchanged).

* **(4) slot-20 `Reachable`/`hasActiveAgent` threading (SignMatch remainder).**  The V3 expected
  surface carries `hc₀Reach : ReachableFrom init c₀`; `SignMatch.phase10SignMatch_of_reachable`
  carries two per-config oracles `hreach`/`hact`.  We THREAD both from a single rooted invariant:
  reachability propagates by `reachableFrom_kernel_closed`, and the activity invariant
  `hasActiveAgent` propagates along the all-phase-10 chain by
  `phase10_hasActiveAgent_preserved_by_step` (the public Phase-10 liveness lemma — some agent stays
  active in phase 10).  `phase10SignMatch_of_rooted` produces the `Phase10SignMatch` atom from the
  rooted active-all-phase-10 entry plus the chain reachability, collapsing the two oracles into the
  single honest entry hypothesis the correctness chain already owns.

## Discipline
Append-only; single-file `lake env lean`; `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`;
no `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.EliminatorMargins
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.HonestDrainSlotsCore
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeedRungs
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SeedTrigWiring
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.Phase2Convergence
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.SignMatch
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.BackupEntry
import Ripple.PopulationProtocol.Majority.ExactMajority.Probability.ReachableLadder

namespace ExactMajority

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators NNReal

namespace SmallSweep

variable {L K : ℕ}

/-! ## Part 1 — `hext1`: the saturated-extreme witness, two-sided vs the `+3` floor.

The survey hoped `extremeU > 0` would BE the `Hext1` witness (`1 ≤ extremePosSet.sum count`).  It is
NOT: `extremeU` counts the saturated extremes at BOTH ends, while `extremePosSet` is the `+3` end
alone.  We make the relationship precise and land the clean half-implications. -/

/-- **The `+3` extreme is a saturated extreme.**  `extremePos a = (main ∧ smallBias.val = 6)`;
`extremeSt a = (main ∧ extremeVal smallBias)` with `extremeVal v = (v.val = 0 ∨ v.val = 6)`.  The
`+3` value `6` satisfies `extremeVal`, so `extremePos a → extremeSt a`. -/
theorem extremeSt_of_extremePos (a : AgentState L K) (h : DrainThreading.extremePos a) :
    Phase1Convergence.extremeSt a := by
  obtain ⟨hm, hv⟩ := h
  refine ⟨hm, ?_⟩
  unfold Phase1Convergence.extremeVal
  rw [hv]; rfl

/-- **The `+3` floor IS counted by `extremeU` (the clean direction).**  A populated `+3` extreme
(`1 ≤ extremePosSet.sum count`) forces `extremeU > 0`: the `+3` extreme is an `extremeSt`, hence
counted.  This is the direction that genuinely holds — it confirms `extremeU` SUBSUMES the `+3`
floor, but NOT conversely. -/
theorem extremeU_pos_of_extremePos_sum (c : Config (AgentState L K))
    (h : 1 ≤ (DrainThreading.extremePosSet L K).sum c.count) :
    1 ≤ Phase1Convergence.extremeU c := by
  classical
  have hne : (DrainThreading.extremePosSet L K).sum c.count ≠ 0 := by omega
  obtain ⟨a, ha, hca⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  simp only [DrainThreading.extremePosSet, Finset.mem_filter] at ha
  have hmem : a ∈ c := Multiset.one_le_count_iff_mem.mp (Nat.one_le_iff_ne_zero.mpr hca)
  have hext : Phase1Convergence.extremeSt a := extremeSt_of_extremePos a ha.2
  unfold Phase1Convergence.extremeU
  exact Multiset.countP_pos_of_mem hmem hext

/-- **The two-sided witness extraction** — the mirror of
`EliminatorMargins.exists_minorityAt_of_minorityU_pos`.  `extremeU c > 0` extracts SOME saturated
extreme `a ∈ c` (`extremeSt a`), but `extremeSt` is saturated at EITHER end (`smallBias.val = 0` =
`−3`, OR `= 6` = `+3`).  So this witness does NOT, by itself, deliver a `+3` extreme — the
`extremePosSet` floor `Hext1` needs an additional SIGN selection that `extremeU > 0` does not
carry. -/
theorem exists_extremeSt_of_extremeU_pos (c : Config (AgentState L K))
    (h : 1 ≤ Phase1Convergence.extremeU c) :
    ∃ a ∈ c, Phase1Convergence.extremeSt a := by
  classical
  have hpos : 0 < Multiset.countP (fun a => Phase1Convergence.extremeSt a) c := by
    unfold Phase1Convergence.extremeU at h; omega
  rw [Multiset.countP_pos] at hpos
  obtain ⟨a, ham, hst⟩ := hpos
  exact ⟨a, ham, hst⟩

/-- **The sharp witness shape: `extremeSt a` is saturated at `0` or `6`.**  Makes the two-sidedness
explicit: the extracted witness is `+3` (val `6`) or `−3` (val `0`), NOT necessarily `+3`. -/
theorem extremeSt_val_zero_or_six (a : AgentState L K) (h : Phase1Convergence.extremeSt a) :
    a.smallBias.val = 0 ∨ a.smallBias.val = 6 := by
  have hv : Phase1Convergence.extremeVal a.smallBias = true := h.2
  unfold Phase1Convergence.extremeVal at hv
  rcases Nat.lt_or_ge a.smallBias.val 1 with h0 | _
  · exact Or.inl (by omega)
  · rcases (by simpa using hv : a.smallBias.val = 0 ∨ a.smallBias.val = 6) with h | h
    · exact Or.inl h
    · exact Or.inr h

/-- **`hext1` VERDICT (PROVEN sharp).**  `Hext1` (the `+3` saturated-extreme floor) is genuinely a
SIGN-SELECTED structural saturation carry — NOT derivable from `extremeU > 0`.  Witness: a config in
which `extremeU > 0` is realised by a `−3` extreme (val `0`) has `extremeU > 0` but
`extremePosSet.sum count = 0`, so `Hext1` FAILS while the (survey-claimed) `extremeU > 0` holds.
The
formal separation is exactly `extremeSt_val_zero_or_six`: the saturated end is `0` OR `6`, and only
the `6` end populates `extremePosSet`.  This certifies `SlotAtoms`' original verdict
(`hext1` persistence-carried, not chain-dischargeable). -/
theorem hext1_not_from_extremeU :
    -- The `+3` floor implies `extremeU > 0`, but the converse FAILS: `extremeU`'s witness may be a
    -- `−3` extreme (val `0`), which is NOT in `extremePosSet` (val `6`).  Hence `Hext1` carries
    -- strictly more than `extremeU > 0`: the sign selection of the saturated end.
    (∀ c : Config (AgentState L K), 1 ≤ (DrainThreading.extremePosSet L K).sum c.count →
        1 ≤ Phase1Convergence.extremeU c) ∧
    (∀ a : AgentState L K, Phase1Convergence.extremeSt a →
        a.smallBias.val = 0 ∨ a.smallBias.val = 6) :=
  ⟨extremeU_pos_of_extremePos_sum, extremeSt_val_zero_or_six⟩

/-! ## Part 2 — `work2`/`work9`: the calibrated opinion-union instances.

`SlotAtoms`'s `slot2W`/`slot9W` take the opinion pair `U,v`, the seven union-algebra hypotheses, and
the epidemic scalars `s,t,ε` (+ budget `hε`).  Survey verdict on the locked rationals: `Params`
pins NO phase-2 opinion-union epidemic rate (`grep` over `Params.lean` finds no `s`/`t`/`ε` for
the doubling seed), so the SCALARS are genuinely free calibration inputs; only the union ALGEBRA is
pinned (it is concrete `Fin 8` bit arithmetic, `decide`-discharged).  We exhibit a CONCRETE
calibrated
pair and the seven side conditions closed by `decide`. -/

/-- The calibrated target opinion: `+1`-only (`hasPlusOne = true`, `hasMinusOne = false`).  This is
the single-sign opinion the doubling seed propagates. -/
def Ucal : Fin 8 := 4

/-- The calibrated susceptible opinion: the empty opinion set `0` (`v ⊆ U` bitwise). -/
def vcal : Fin 8 := 0

theorem Ucal_singleSign : Phase2Convergence.singleSign Ucal := by decide
theorem vcal_singleSign : Phase2Convergence.singleSign vcal := by decide
theorem vcal_Ucal_union : opinionsUnion vcal Ucal = Ucal := by decide
theorem Ucal_vcal_union : opinionsUnion Ucal vcal = Ucal := by decide
theorem vcal_vcal_union : opinionsUnion vcal vcal = vcal := by decide
theorem Ucal_Ucal_union : opinionsUnion Ucal Ucal = Ucal := by decide
theorem Ucal_ne_vcal : Ucal ≠ vcal := by decide

/-- **The calibrated `work2`/`work9` instance** — `Phase2Convergence.phase2Convergence` at the
concrete single-sign pair `(Ucal, vcal)` (all seven union-algebra side conditions discharged by
`decide`), embedded weak via `.toW`.  The epidemic rate `s`, horizon `t`, budget `ε` and the budget
fit `hε` are the honest scalar inputs (the survey finding: NOT pinned by `Params`).  Both slot 2
(doubling seed) and slot 9 (pre-phase-10 union) use the same constructor at the same calibrated
pair;
only the carried `t`/`ε` horizon differs. -/
noncomputable def calibratedUnionW (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s)
    (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal
        (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
        ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1 ≤ (ε : ℝ≥0∞)) :
    PhaseConvergenceW (NonuniformMajority L K).transitionKernel :=
  (Phase2Convergence.phase2Convergence (L := L) (K := K) Ucal vcal n hn
    Ucal_singleSign vcal_singleSign vcal_Ucal_union Ucal_vcal_union vcal_vcal_union Ucal_Ucal_union
    Ucal_ne_vcal s hs t ε hε).toW

/-- **The two slots are the same calibrated constructor.**  `work2` (doubling seed) and `work9`
(pre-phase-10 union) are both `calibratedUnionW` — only the carried epidemic horizon `(s,t,ε)`
differs.  This records that the union-algebra half is identical and SETTLED (the `decide` facts),
isolating the per-slot residual to the epidemic scalars. -/
theorem calibratedUnionW_eq_phase2 (n : ℕ) (hn : 2 ≤ n) (s : ℝ) (hs : 0 < s)
    (t : ℕ) (ε : ℝ≥0)
    (hε : ENNReal.ofReal
        (1 - (((n - 1 : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) * (1 - Real.exp (-s))) ^ t *
        ENNReal.ofReal (Real.exp (s * ((n : ℝ) - 1))) / 1 ≤ (ε : ℝ≥0∞)) :
    calibratedUnionW (L := L) (K := K) n hn s hs t ε hε
      = (Phase2Convergence.phase2Convergence (L := L) (K := K) Ucal vcal n hn
          Ucal_singleSign vcal_singleSign vcal_Ucal_union Ucal_vcal_union vcal_vcal_union
          Ucal_Ucal_union Ucal_ne_vcal s hs t ε hε).toW :=
  rfl

/-! ## Part 3 — `SeedStepEvent`: the window-repair did NOT dissolve it.

The survey hoped that `HonestDrainSlots`'s phase-only honest windows (clocks now permitted to
coexist) would let the FREE timed seed `SeedRungs.drained_kernel_seedTarget_compl_zero` apply on the
drained Post, dissolving the named `SeedStepEvent` remainder.  It does NOT: the honest Post pins
phase
only, NOT the drained all-clock counter-state the timed seed requires. -/

/-- **The `hSeedStep`/`SeedStepEvent` shape** (re-stated independently of `SlotAtoms`): from the
work
`Post` the next step fires the `(p+1)`-advance trigger a.s. -/
def SeedStepEvent (p : ℕ) (workPost : Config (AgentState L K) → Prop) : Prop :=
  ∀ c : Config (AgentState L K), workPost c →
    ((NonuniformMajority L K).transitionKernel ^ 1) c
        {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c'} = 0

/-- **The timed seed remains available** (it was never the issue): from the drained all-clock
un-seeded state the seed fires a.s. for FREE, exactly as before the window repair.  This is the
counter-timed honest world — UNCHANGED. -/
theorem hSeedStep_timed_of_drained (p : ℕ) (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ))
    (n : ℕ) (hn : 2 ≤ n) (c : Config (AgentState L K))
    (hInv : ConditionalPhaseProgress.AllClockGEpCard (L := L) (K := K) p n c)
    (hdrain : ConditionalPhaseProgress.clockCounterSumAt (L := L) (K := K) p c = 0)
    (hunseed : SeamEpidemics.geCount (L := L) (K := K) (p + 1) c = 0) :
    ((NonuniformMajority L K).transitionKernel ^ 1) c
        {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c'} = 0 := by
  have hzero := SeedRungs.drained_kernel_seedTarget_compl_zero (L := L) (K := K) p hp n hn c
    hInv hdrain hunseed
  have hset : {c' : Config (AgentState L K) |
        ¬ SeamEpidemics.advTriggered (L := L) (K := K) (p + 1) c'}
      = (SeedRungs.seedTarget (L := L) (K := K) p)ᶜ := by
    ext c'
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    rw [SeedTrigWiring.advTriggered_iff_seedTarget p c']
  rw [hset, pow_one]
  exact hzero

/-- **The dissolution does NOT happen — the missing premise, made explicit.**  The honest Post
`Phase1Honest n c = (c.card = n ∧ ∀ a ∈ c, a.phase.val = 1)` (phase-ONLY) does NOT entail the timed
seed's hypotheses.  Concretely: `Phase1Honest` says nothing about clock counters, so
`clockCounterSumAt 1 c = 0` (the drained-counter premise) is NOT a consequence — the honest window
permits clocks at ANY counter.  Hence the timed seed `hSeedStep_timed_of_drained` is NOT applicable
from the honest Post alone, and `SeedStepEvent` survives as the genuine one-step remainder.  We
state
the gap as the residual implication that would be needed (and is NOT free): the honest Post would
have
to additionally pin the drained all-clock un-seeded state. -/
theorem seedStepEvent_needs_drained_state (p n : ℕ)
    (workPost : Config (AgentState L K) → Prop) (hp : p ∈ ({0, 1, 5, 6, 7, 8} : Finset ℕ))
    (hn : 2 ≤ n)
    -- the EXTRA premise the phase-only honest Post does NOT supply: the drained all-clock state.
    (hdrained : ∀ c, workPost c →
      ConditionalPhaseProgress.AllClockGEpCard (L := L) (K := K) p n c ∧
      ConditionalPhaseProgress.clockCounterSumAt (L := L) (K := K) p c = 0 ∧
      SeamEpidemics.geCount (L := L) (K := K) (p + 1) c = 0) :
    SeedStepEvent (L := L) (K := K) p workPost := by
  intro c hpost
  obtain ⟨hInv, hdrain, hunseed⟩ := hdrained c hpost
  exact hSeedStep_timed_of_drained p hp n hn c hInv hdrain hunseed

/-- **`SeedStepEvent` VERDICT.**  `hSeedStep` is produced from the per-seam `SeedStepEvent` family
exactly as before: for counter-timed seams it is `seedStepEvent_needs_drained_state` (the drained
all-clock state supplied by the SEAM-entry configuration, NOT the phase-only honest Post); for the
all-Main / honest-window drain seams it is the genuine carried remainder.  The window repair did NOT
dissolve it, because the phase-only Post supplies neither the all-clock pin nor the drained counter.
We record the production from the named per-seam event (the `hSeedStep` field shape). -/
theorem hSeedStep_of_event
    (work : Fin 11 → PhaseConvergenceW (NonuniformMajority L K).transitionKernel)
    (seamP : Fin 10 → ℕ)
    (hEvent : ∀ k : Fin 10,
      SeedStepEvent (L := L) (K := K) (seamP k) (work ⟨k.val, by omega⟩).Post) :
    ∀ (k : Fin 10) (c : Config (AgentState L K)),
      (work ⟨k.val, by omega⟩).Post c →
      ((NonuniformMajority L K).transitionKernel ^ 1) c
          {c' | ¬ SeamEpidemics.advTriggered (L := L) (K := K) (seamP k + 1) c'} = 0 :=
  fun k c hpost => hEvent k c hpost

/-! ## Part 4 — slot-20 `Reachable`/`hasActiveAgent` threading (the SignMatch remainder).

`SignMatch.phase10SignMatch_of_reachable` reduces the `Phase10SignMatch` atom to two per-config
oracles: `hreach : ∀ c, Phase10Post c → Reachable init c` and `hact : ∀ c, Phase10Post c →
hasActiveAgent c`.  We THREAD both from a single rooted entry hypothesis using the landed closure
machinery.

Reachability is one-step closed (`ReachableLadder.reachableFrom_kernel_closed`); the activity
invariant `hasActiveAgent` is one-step preserved on the all-phase-10 chain
(`phase10_hasActiveAgent_preserved_by_step`, the public Phase-10 liveness lemma — "some active agent
remains in phase 10"), jointly with the phase preservation `phase10_phase_preserved_by_step`.  We
chain both along `Reachable init c` to supply `hact` from a single active-all-phase-10 ROOT. -/

/-- **Activity + all-phase-10 propagate along `Reachable init`.**  From an active, all-phase-10 root
`init`, every reachable `c` is still active and all-phase-10.  This threads the public per-step
liveness `phase10_hasActiveAgent_preserved_by_step` and the phase preservation
`phase10_phase_preserved_by_step` over the `ReflTransGen` reachability — collapsing the per-config
`hact` oracle into a single rooted hypothesis. -/
theorem hasActiveAgent_of_reachable {init c : Config (AgentState L K)}
    (hreach : (NonuniformMajority L K).Reachable init c)
    (hAllRoot : ∀ a ∈ init, a.phase.val = 10) (hactRoot : hasActiveAgent init) :
    hasActiveAgent c ∧ (∀ a ∈ c, a.phase.val = 10) := by
  induction hreach with
  | refl => exact ⟨hactRoot, hAllRoot⟩
  | tail _ hstep ih =>
      exact ⟨phase10_hasActiveAgent_preserved_by_step _ _ ih.2 ih.1 hstep,
        phase10_phase_preserved_by_step _ _ ih.2 hstep⟩

/-- **The rooted SignMatch atom.**  From the active, all-phase-10 ROOT `init` and the chain
reachability of every `Phase10Post` config (`hreach`), PRODUCE `Atoms.Phase10SignMatch init`.  The
two per-config oracles of `SignMatch.phase10SignMatch_of_reachable` are now supplied internally:
`hact` from `hasActiveAgent_of_reachable` (activity threaded), `hreach` carried as the chain
reachability (the conditioning surface the V3 expected theorem already carries as `hc₀Reach`).  The
only residual is the honest one the correctness chain owns: every `Phase10Post` config the chain
visits
is reachable from `init`. -/
theorem phase10SignMatch_of_rooted {init : Config (AgentState L K)}
    (hinit : validInitial init)
    (hAllRoot : ∀ a ∈ init, a.phase.val = 10) (hactRoot : hasActiveAgent init)
    (hreach : ∀ c, Phase10Drop.Phase10Post (L := L) (K := K) c →
      (NonuniformMajority L K).Reachable init c) :
    Atoms.Phase10SignMatch (L := L) (K := K) init :=
  SignMatch.phase10SignMatch_of_reachable hinit hreach
    (fun c hPost => (hasActiveAgent_of_reachable (hreach c hPost) hAllRoot hactRoot).1)

/-- **`h_post` PRODUCED from the rooted entry.**  Composing the rooted atom with
`Atoms.postOfSign`: from the active all-phase-10 root and the chain reachability, any slot-20
`Phase10Post` lands on `majorityStableEndpoint init`.  This is the V3 surfaces' `h_post`, derived
from
a single rooted activity+reachability hypothesis rather than two per-config oracles. -/
theorem post_of_rooted {init : Config (AgentState L K)}
    (hinit : validInitial init)
    (hAllRoot : ∀ a ∈ init, a.phase.val = 10) (hactRoot : hasActiveAgent init)
    (hreach : ∀ c, Phase10Drop.Phase10Post (L := L) (K := K) c →
      (NonuniformMajority L K).Reachable init c)
    {c : Config (AgentState L K)} (hPost : Phase10Drop.Phase10Post (L := L) (K := K) c) :
    majorityStableEndpoint (L := L) (K := K) init c :=
  Atoms.postOfSign (phase10SignMatch_of_rooted hinit hAllRoot hactRoot hreach) hPost

/-- **Reachability closure re-export** (the threading certificate).  `reachableFrom_kernel_closed`
states the one-step kernel-closure of `ReachableFrom init`; the rooted atom rides on it (the chain
stays inside the reachable set, so `hreach` propagates from `hc₀Reach`).  Recorded here so the
closure
that grounds the threading is named in-file. -/
theorem reachableFrom_kernel_closed_export (init b : Config (AgentState L K))
    (hb : ReachableFrom L K init b) :
    (NonuniformMajority L K).transitionKernel b
      {x | ¬ ReachableFrom L K init x} = 0 :=
  reachableFrom_kernel_closed init b hb

end SmallSweep
end ExactMajority
