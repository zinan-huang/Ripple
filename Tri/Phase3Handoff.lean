/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.EscapeFromExit

/-!
# The buffered phase-2 to phase-3 handoff

The phase-3 live region has minority coordinate `1 <= y <= n / 6`.  Entering
only under `y <= n / 12` leaves a genuine buffer: one interaction either stays
in the live region or reaches all-`X` consensus.  Over longer horizons, escape
is possible but requires crossing the lower `X` boundary against the majority
drift.  This file bounds that escaped mass by `Tri.tri_feller` rather than
incorrectly asserting that it is zero.

The Feller boundary is described by subtraction-free arithmetic certificates.
Its last bad state is `aLo`, its complementary population parameter is `bHi`,
and `k` is the distance from the buffered start to `aLo`.  The buffered size
guard implies `n <= 12 * k`, making the exponential escape distance explicit.
-/

namespace Tri

open scoped ENNReal

/-- A phase-2 exit with enough room before the phase-3 upper minority boundary.
The first two conjuncts are the subtraction-free statement
`y <= gamma * log_2 n`; the last conjunct puts that threshold below `n / 12`. -/
def Phase2ExitBuffered (n gamma x : ℕ) : Prop :=
  x ≤ n ∧ n ≤ x + gamma * Nat.log 2 n ∧
    12 * gamma * Nat.log 2 n ≤ n

/-- Membership in the buffered phase-2 exit region is decidable. -/
instance (n gamma : ℕ) : DecidablePred (Phase2ExitBuffered n gamma) := by
  intro x
  unfold Phase2ExitBuffered
  infer_instance

/-- A buffered exit is, in particular, an ordinary phase-2 exit. -/
theorem Phase2ExitBuffered.phase2Exit {n gamma x : ℕ}
    (hx : Phase2ExitBuffered n gamma x) : Phase2Exit n gamma x := by
  exact ⟨hx.1, hx.2.1⟩

/-- The strengthened size guard carried by a buffered phase-2 exit. -/
theorem Phase2ExitBuffered.size {n gamma x : ℕ}
    (hx : Phase2ExitBuffered n gamma x) :
    12 * gamma * Nat.log 2 n ≤ n := by
  exact hx.2.2

/-- Exact subtraction-free parameters for applying `tri_feller` at the lower
boundary of `Phase3Region`.

`aLo` is the last state below the phase-3 region, `bHi` is its complementary
population parameter, and the start is exactly `k` states above `aLo`. -/
structure Phase3FellerParameters (n x : ℕ) where
  /-- Last `X`-count below the phase-3 live region. -/
  aLo : ℕ
  /-- Complementary Feller population parameter at `aLo`. -/
  bHi : ℕ
  /-- Distance from `aLo` to the initial state. -/
  k : ℕ
  /-- The initial state is physical. -/
  hphysical : x ≤ n
  /-- The initial state is exactly `k` above the lower boundary. -/
  hstart : aLo + k = x
  /-- The population decomposition required by `tri_feller`. -/
  hpop : aLo + bHi + 2 = n
  /-- The lower boundary parameter is positive. -/
  haLo : 0 < aLo
  /-- The complementary parameter is positive. -/
  hbHi : 0 < bHi
  /-- The whole Feller region lies on the `X`-majority side. -/
  hmajority : bHi ≤ aLo
  /-- `aLo` itself is strictly below the phase-3 region. -/
  hlastBad : 6 * aLo < 5 * n
  /-- The successor of `aLo` is inside the phase-3 lower boundary. -/
  hfirstLive : 5 * n ≤ 6 * (aLo + 1)

/-- The corrected escape-slack statement: the stopped escape mass is bounded
by a Feller term whose exponent is at least the buffered distance `n / 12`.
All arithmetic is packaged without natural subtraction. -/
def Phase3FellerEscapeSlack (n T x : ℕ) : Prop :=
  ∃ F : Phase3FellerParameters n x,
    n ≤ 12 * F.k ∧
      phase3EscapeMass n T x ≤
        ((F.bHi : ℝ≥0∞) / (F.aLo : ℝ≥0∞)) ^ F.k

/-- The exact Feller boundary characterizes the phase-3 live interval. -/
theorem phase3Region_iff_fellerBand {n x : ℕ}
    (F : Phase3FellerParameters n x) (z : ℕ) :
    Phase3Region n z ↔ F.aLo < z ∧ z < n := by
  unfold Phase3Region
  constructor
  · rintro ⟨hzn, hlive⟩
    constructor
    · by_contra hlo
      have hzle : z ≤ F.aLo := Nat.le_of_not_gt hlo
      have hscaled : 6 * z ≤ 6 * F.aLo :=
        Nat.mul_le_mul_left 6 hzle
      have hlastBad := F.hlastBad
      omega
    · exact hzn
  · rintro ⟨hlo, hzn⟩
    constructor
    · exact hzn
    · exact F.hfirstLive.trans
        (Nat.mul_le_mul_left 6 (by omega : F.aLo + 1 ≤ z))

/-- At or above the population count, `triChain` is already the pure chain. -/
theorem triChain_pure_of_population_le {n z : ℕ} (h3 : 3 ≤ n)
    (hnz : n ≤ z) : triChain n z = PMF.pure z := by
  rcases eq_or_lt_of_le hnz with hzn | hzn
  · subst z
    exact triChain_consensus h3
  · unfold triChain
    rw [dif_neg]
    omega

/-- With exact boundary parameters, the stopped phase-3 chain is the Feller
chain frozen at `z <= aLo`.  The extra phase-3 freeze at consensus is harmless
because consensus is already pure. -/
theorem phase3Stop_eq_fellerFreeze {n x : ℕ}
    (F : Phase3FellerParameters n x) :
    phase3Stop n = freeze (fun z : ℕ => z ≤ F.aLo) (triChain n) := by
  have h3 : 3 ≤ n := by
    have hpop := F.hpop
    have haLo := F.haLo
    have hbHi := F.hbHi
    omega
  funext z
  unfold phase3Stop
  by_cases hzlo : z ≤ F.aLo
  · have hnregion : ¬ Phase3Region n z := by
      intro hregion
      have := (phase3Region_iff_fellerBand F z).mp hregion
      omega
    rw [freeze_of_mem z hnregion, freeze_of_mem z hzlo]
  · have halo : F.aLo < z := by omega
    by_cases hzn : z < n
    · have hregion : Phase3Region n z :=
        (phase3Region_iff_fellerBand F z).2 ⟨halo, hzn⟩
      rw [freeze_of_not_mem z (by simpa using hregion),
        freeze_of_not_mem z hzlo]
    · have hnregion : ¬ Phase3Region n z := by
        intro hregion
        exact hzn ((phase3Region_iff_fellerBand F z).mp hregion).2
      rw [freeze_of_mem z hnregion, freeze_of_not_mem z hzlo,
        triChain_pure_of_population_le h3 (by omega)]

/-- One stopped phase-3 step from a physical state has no mass above the fixed
population. -/
theorem phase3Stop_eq_zero_above (n x z : ℕ) (h3 : 3 ≤ n)
    (hx : x ≤ n) (hz : n < z) : phase3Stop n x z = 0 := by
  by_cases hregion : Phase3Region n x
  · rw [phase3Stop, freeze_of_not_mem x (by simpa using hregion)]
    exact triChain_eq_zero_above n x z h3 hx hz
  · rw [phase3Stop, freeze_of_mem x hregion]
    simp [PMF.pure_apply]
    omega

/-- Every iterate of the stopped phase-3 chain preserves the physical range. -/
theorem iter_phase3Stop_eq_zero_above (n T x z : ℕ) (h3 : 3 ≤ n)
    (hx : x ≤ n) (hz : n < z) :
    iter (phase3Stop n) T x z = 0 := by
  induction T generalizing x with
  | zero =>
      simp [iter, PMF.pure_apply]
      omega
  | succ T ih =>
      rw [iter_succ, PMF.bind_apply, ENNReal.tsum_eq_zero]
      intro y
      by_cases hy : y ≤ n
      · rw [ih y hy, mul_zero]
      · rw [phase3Stop_eq_zero_above n x y h3 hx (by omega), zero_mul]

/-- From a buffered phase-2 exit, every state with nonzero one-step mass is
either still in `Phase3Region` or is all-`X` consensus, where the killed
phase-3 potential is zero. -/
theorem buffered_entry_no_single_escape (n gamma x z : ℕ)
    (hx : Phase2ExitBuffered n gamma x)
    (hz : triChain n x z ≠ 0) :
    z = n ∨ Phase3Region n z := by
  rcases hx with ⟨hxphysical, hxentry, hxsize⟩
  let m := gamma * Nat.log 2 n
  have hentry : n ≤ x + m := by simpa [m] using hxentry
  have hsize : 12 * m ≤ n := by
    simpa [m, Nat.mul_assoc] using hxsize
  by_cases hxn : x = n
  · subst x
    have hpure : triChain n n = PMF.pure n := by
      by_cases h3 : 3 ≤ n
      · exact triChain_consensus h3
      · unfold triChain
        rw [dif_neg]
        omega
    rw [hpure] at hz
    left
    by_contra hzn
    exact hz (by simp [PMF.pure_apply, hzn])
  · have hxlt : x < n := lt_of_le_of_ne hxphysical hxn
    have hmpos : 0 < m := by omega
    have hn12 : 12 ≤ n := by omega
    have hxpos : 0 < x := by omega
    obtain ⟨a, rfl⟩ : ∃ a, x = a + 1 := ⟨x - 1, by omega⟩
    obtain ⟨b, hpop⟩ : ∃ b, a + b + 2 = n :=
      ⟨n - a - 2, by omega⟩
    have hbentry : b + 1 ≤ m := by omega
    have h3 : 3 ≤ n := by omega
    rw [triChain_apply hpop h3] at hz
    by_cases hdown : z = a
    · subst z
      right
      unfold Phase3Region
      constructor <;> omega
    · by_cases hstay : z = a + 1
      · subst z
        right
        unfold Phase3Region
        constructor <;> omega
      · by_cases hup : z = a + 2
        · subst z
          by_cases hconsensus : a + 2 = n
          · exact Or.inl hconsensus
          · right
            unfold Phase3Region
            constructor <;> omega
        · exact False.elim (hz
            (triStep_eq_zero a (b + 1) (by omega) hdown hstay hup))

/-- The stopped non-consensus escape mass is at most the corresponding Feller
hitting probability at the exact lower boundary. -/
theorem phase3EscapeMass_le_hitProb {n x : ℕ}
    (F : Phase3FellerParameters n x) (T : ℕ) :
    phase3EscapeMass n T x ≤
      hitProb (fun z : ℕ => z ≤ F.aLo) (triChain n) T x := by
  have h3 : 3 ≤ n := by
    have hpop := F.hpop
    have haLo := F.haLo
    have hbHi := F.hbHi
    omega
  have hstop := phase3Stop_eq_fellerFreeze F
  have hhit :
      hitProb (fun z : ℕ => z ≤ F.aLo) (triChain n) T x =
        ∑' z, if z ≤ F.aLo then iter (phase3Stop n) T x z else 0 := by
    unfold hitProb expect ind
    rw [← hstop]
    apply tsum_congr
    intro z
    by_cases hz : z ≤ F.aLo <;> simp [hz]
  rw [hhit]
  unfold phase3EscapeMass
  refine ENNReal.tsum_le_tsum fun z => ?_
  by_cases hescape : ¬ Phase3Region n z ∧ z ≠ n
  · by_cases hzphysical : z ≤ n
    · have hzlo : z ≤ F.aLo := by
        by_contra hzlo
        have hregion := (phase3Region_iff_fellerBand F z).2
          ⟨by omega, lt_of_le_of_ne hzphysical hescape.2⟩
        exact hescape.1 hregion
      simp [hescape, hzlo]
    · have hzero := iter_phase3Stop_eq_zero_above n T x z h3
        F.hphysical (by omega)
      have haLon : F.aLo < n := by
        have hpop := F.hpop
        have hbHi := F.hbHi
        omega
      have hzlo : ¬ z ≤ F.aLo := by omega
      simp [hescape, hzlo, hzero]
  · simp [hescape]

/-- The phase-3 stopped escape mass obeys the exponential Feller bound for
every finite horizon. -/
theorem phase3_escape_le_feller {n x : ℕ}
    (F : Phase3FellerParameters n x) (T : ℕ) :
    phase3EscapeMass n T x ≤
      ((F.bHi : ℝ≥0∞) / (F.aLo : ℝ≥0∞)) ^ F.k := by
  have h3 : 3 ≤ n := by
    have hpop := F.hpop
    have haLo := F.haLo
    have hbHi := F.hbHi
    omega
  calc
    phase3EscapeMass n T x ≤
        hitProb (fun z : ℕ => z ≤ F.aLo) (triChain n) T x :=
      phase3EscapeMass_le_hitProb F T
    _ = hitProb (fun z : ℕ => z ≤ F.aLo) (triChain n) T
        (F.aLo + F.k) := by rw [F.hstart]
    _ ≤ ⨆ U : ℕ,
        hitProb (fun z : ℕ => z ≤ F.aLo) (triChain n) U
          (F.aLo + F.k) := le_iSup (fun U : ℕ =>
            hitProb (fun z : ℕ => z ≤ F.aLo) (triChain n) U
              (F.aLo + F.k)) T
    _ ≤ ((F.bHi : ℝ≥0∞) / (F.aLo : ℝ≥0∞)) ^ F.k :=
      tri_feller n F.aLo F.bHi F.k h3 F.hpop F.haLo F.hbHi
        F.hmajority

/-- The stronger `12 * gamma * log_2 n <= n` guard constructs exact Feller
parameters, and the resulting exponent satisfies `n <= 12 * k`. -/
theorem phase2ExitBuffered_feller_parameters (n gamma x : ℕ)
    (hn12 : 12 ≤ n) (hx : Phase2ExitBuffered n gamma x) :
    ∃ F : Phase3FellerParameters n x, n ≤ 12 * F.k := by
  rcases hx with ⟨hxphysical, hxentry, hxsize⟩
  let m := gamma * Nat.log 2 n
  let q := n / 6
  let r := n % 6
  have hentry : n ≤ x + m := by simpa [m] using hxentry
  have hsize : 12 * m ≤ n := by
    simpa [m, Nat.mul_assoc] using hxsize
  have hdecomp : r + 6 * q = n := by
    simpa [q, r] using Nat.mod_add_div n 6
  have hr : r < 6 := by
    exact Nat.mod_lt n (by norm_num)
  have hq : 2 ≤ q := by omega
  obtain ⟨bHi, hqeq⟩ : ∃ bHi : ℕ, q = bHi + 1 :=
    ⟨q - 1, by omega⟩
  let aLo := 5 * bHi + 4 + r
  have hpop : aLo + bHi + 2 = n := by
    dsimp [aLo]
    omega
  have haLo : 0 < aLo := by
    dsimp [aLo]
    omega
  have hbHi : 0 < bHi := by omega
  have hmajority : bHi ≤ aLo := by
    dsimp [aLo]
    omega
  have hlastBad : 6 * aLo < 5 * n := by
    dsimp [aLo]
    omega
  have hfirstLive : 5 * n ≤ 6 * (aLo + 1) := by
    dsimp [aLo]
    omega
  have hmle : m ≤ bHi + 2 := by omega
  have haLox : aLo ≤ x := by omega
  let k := x - aLo
  have hstart : aLo + k = x := by
    dsimp [k]
    omega
  have hgap : n ≤ 12 * k := by omega
  let F : Phase3FellerParameters n x :=
    { aLo := aLo
      bHi := bHi
      k := k
      hphysical := hxphysical
      hstart := hstart
      hpop := hpop
      haLo := haLo
      hbHi := hbHi
      hmajority := hmajority
      hlastBad := hlastBad
      hfirstLive := hfirstLive }
  exact ⟨F, hgap⟩

/-- The correctly restated escape handoff is fully discharged for every
buffered phase-2 exit at populations at least twelve.  No zero-escape premise
is assumed: the conclusion carries the proved Feller term. -/
theorem hescape_buffered_proved (n gamma T x : ℕ) (hn12 : 12 ≤ n)
    (hx : Phase2ExitBuffered n gamma x) :
    Phase3FellerEscapeSlack n T x := by
  rcases phase2ExitBuffered_feller_parameters n gamma x hn12 hx with
    ⟨F, hgap⟩
  exact ⟨F, hgap, phase3_escape_le_feller F T⟩

/-- The operational handoff: actual terminal failure is bounded by the killed
phase-3 expectation plus the Feller escape term. -/
theorem phase3_failure_le_expect_add_feller {n x : ℕ}
    (F : Phase3FellerParameters n x) (T : ℕ) :
    (∑' z, if IsXMajority n z then 0 else iter (triChain n) T x z) ≤
      expect (iter (phase3Stop n) T x) (phase3StoppedPotential n) +
        ((F.bHi : ℝ≥0∞) / (F.aLo : ℝ≥0∞)) ^ F.k := by
  have h3 : 3 ≤ n := by
    have hpop := F.hpop
    have haLo := F.haLo
    have hbHi := F.hbHi
    omega
  exact (phase3_failure_le_expect_add_escape n T x h3).trans
    (add_le_add_right (phase3_escape_le_feller F T) _)

#print axioms Phase2ExitBuffered.phase2Exit
#print axioms Phase2ExitBuffered.size
#print axioms phase3Region_iff_fellerBand
#print axioms triChain_pure_of_population_le
#print axioms phase3Stop_eq_fellerFreeze
#print axioms phase3Stop_eq_zero_above
#print axioms iter_phase3Stop_eq_zero_above
#print axioms buffered_entry_no_single_escape
#print axioms phase3EscapeMass_le_hitProb
#print axioms phase3_escape_le_feller
#print axioms phase2ExitBuffered_feller_parameters
#print axioms hescape_buffered_proved
#print axioms phase3_failure_le_expect_add_feller

end Tri
