/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.ByzantineAdaptive
import Tri.Drift

/-!
# Entry no-backsliding monitor for adaptive Byzantine Tri

The paper's initial Byzantine condition is used in the integer-safe form
`16 * z ≤ d`, where `d` is the initial signed gap `2x - n`. While the current
signed gap remains at least `d/2` and at most `n/2`, the adverse fixed response
has a uniform strict bias toward increasing honest `X`.

The monitor is genuinely joint in `(x,z)`: its geometric part depends on `x`,
but it is set to `⊤` when the Byzantine budget fails. Since `z` is conserved,
this is the minimal state monitor needed to turn the existing adverse envelope
for antitone `X`-potentials into a theorem for every adaptive history.
-/

namespace Tri.Byzantine

open scoped ENNReal

variable {n B : ℕ}

/-- The paper's Byzantine budget relative to an initial gap parameter `d`. -/
def EntryBudget (d : ℕ) (s : State n B) : Prop :=
  16 * State.z s ≤ d

instance entryBudgetDecidable (d : ℕ) (s : State n B) :
    Decidable (EntryBudget d s) := by
  unfold EntryBudget
  infer_instance

/-- Lower failure: the signed gap `2x-n` has fallen below `d/2`. -/
def EntryBad (d : ℕ) (s : State n B) : Prop :=
  4 * State.x s < 2 * n + d

instance entryBadDecidable (d : ℕ) (s : State n B) :
    Decidable (EntryBad d s) := by
  unfold EntryBad
  infer_instance

/-- Upper entry checkpoint: the signed gap is at least `n/2`. -/
def EntryTarget (s : State n B) : Prop :=
  3 * n ≤ 4 * State.x s

instance entryTargetDecidable (s : State n B) :
    Decidable (EntryTarget s) := by
  unfold EntryTarget
  infer_instance

/-- The arithmetic band in which the strict adverse bias is proved. -/
def EntryLive (d : ℕ) (s : State n B) : Prop :=
  2 * n + d ≤ 4 * State.x s ∧
    4 * State.x s ≤ 3 * n ∧
    EntryBudget d s

/-- Geometric base used in the entry monitor. -/
noncomputable def entryBase (n d : ℕ) : ℝ≥0∞ :=
  ((128 * n : ℕ) : ℝ≥0∞) /
    ((128 * n + d : ℕ) : ℝ≥0∞)

/-- Integer lower threshold used by the terminal Markov bound. -/
def entryLower (n d : ℕ) : ℕ :=
  (2 * n + d) / 4

/-- Minimal joint monitor. The transition part is geometric in `x`; a violated
Byzantine budget is assigned infinite badness. -/
noncomputable def entryPotential (n d : ℕ) (s : State n B) : ℝ≥0∞ :=
  if EntryBudget d s then entryBase n d ^ State.x s else ⊤

/-- The geometric base is at most one. -/
theorem entryBase_le_one (n d : ℕ) (hn : 0 < n) :
    entryBase n d ≤ 1 := by
  unfold entryBase
  have hden0 : (((128 * n + d : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast (by omega : 128 * n + d ≠ 0)
  have hdenTop : (((128 * n + d : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  calc
    ((128 * n : ℕ) : ℝ≥0∞) /
          ((128 * n + d : ℕ) : ℝ≥0∞) ≤
        ((128 * n + d : ℕ) : ℝ≥0∞) /
          ((128 * n + d : ℕ) : ℝ≥0∞) := by
      exact ENNReal.div_le_div_right
        (by exact_mod_cast (by omega : 128 * n ≤ 128 * n + d)) _
    _ = 1 := ENNReal.div_self hden0 hdenTop

/-- The geometric base is nonzero. -/
theorem entryBase_ne_zero (n d : ℕ) (hn : 0 < n) :
    entryBase n d ≠ 0 := by
  unfold entryBase
  simp only [ne_eq, ENNReal.div_eq_zero_iff, not_or]
  exact ⟨by
    simp only [Nat.cast_eq_zero]
    omega, ENNReal.natCast_ne_top _⟩

/-- Powers of a subunit base are antitone in the exponent. -/
theorem entryBase_pow_antitone (n d : ℕ) (hn : 0 < n) :
    Antitone (fun k : ℕ => entryBase n d ^ k) := by
  have hu := entryBase_le_one n d hn
  intro a b hab
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  change entryBase n d ^ (a + k) ≤ entryBase n d ^ a
  rw [pow_add]
  have hk : entryBase n d ^ k ≤ 1 :=
    pow_le_one₀ bot_le hu
  calc
    entryBase n d ^ a * entryBase n d ^ k ≤
        entryBase n d ^ a * 1 := by
      gcongr
    _ = entryBase n d ^ a := by simp

/-- Exact count inequality in the paper's entry band. -/
theorem entryBand_worst_weight_cross
    (d : ℕ) (s : State n B) (hs : EntryLive d s) :
    (128 * n + d) * worstDownWeight s ≤
      (128 * n) * worstUpWeight s := by
  let x := State.x s
  let y := State.y s
  let z := State.z s
  let m := y + z
  rcases hs with ⟨hlo, hhi, hz⟩
  change 2 * n + d ≤ 4 * x at hlo
  change 4 * x ≤ 3 * n at hhi
  change 16 * z ≤ d at hz
  have htotal : x + m = n := by
    dsimp only [x, y, z, m]
    have ht := State.total s
    omega
  have hmle : m ≤ n := by omega
  have hnlem4 : n ≤ 4 * m := by omega
  have hdle : d ≤ n := by omega
  have h4z : 4 * z ≤ m := by omega
  have hzley : z ≤ y := by
    dsimp only [m] at h4z
    omega
  have hm2y : m ≤ 2 * y := by
    dsimp only [m]
    omega
  have hshift : d + 2 * (m - 1) ≤ 2 * (x - 1) := by
    omega
  have hsmall : (m - 1) * (8 * n + m) ≤ 18 * n * y := by
    calc
      (m - 1) * (8 * n + m) ≤ m * (8 * n + m) := by
        exact Nat.mul_le_mul (Nat.sub_le m 1) le_rfl
      _ ≤ (2 * y) * (9 * n) := by
        exact Nat.mul_le_mul hm2y (by omega)
      _ = 18 * n * y := by ring
  have hzpart :
      128 * n * (m - 1) * z ≤ 8 * n * d * (m - 1) := by
    have hmul := Nat.mul_le_mul_left (8 * n * (m - 1)) hz
    calc
      128 * n * (m - 1) * z =
          (8 * n * (m - 1)) * (16 * z) := by ring
      _ ≤ (8 * n * (m - 1)) * d := hmul
      _ = 8 * n * d * (m - 1) := by ring
  have htail :
      128 * n * (m - 1) * z + d * m * (m - 1) ≤
        64 * n * d * y := by
    calc
      128 * n * (m - 1) * z + d * m * (m - 1) ≤
          8 * n * d * (m - 1) + d * m * (m - 1) := by
        exact add_le_add hzpart le_rfl
      _ = d * ((m - 1) * (8 * n + m)) := by ring
      _ ≤ d * (18 * n * y) := Nat.mul_le_mul_left d hsmall
      _ = 18 * n * d * y := by ring
      _ ≤ 64 * n * d * y := by
        gcongr
        norm_num
  have hfront :
      128 * n * (m - 1) * y + 64 * n * d * y ≤
        128 * n * (x - 1) * y := by
    have hmul := Nat.mul_le_mul_left (64 * n * y) hshift
    calc
      128 * n * (m - 1) * y + 64 * n * d * y =
          (64 * n * y) * (d + 2 * (m - 1)) := by ring
      _ ≤ (64 * n * y) * (2 * (x - 1)) := hmul
      _ = 128 * n * (x - 1) * y := by ring
  have hcore :
      (128 * n + d) * m * (m - 1) ≤
        128 * n * (x - 1) * y := by
    calc
      (128 * n + d) * m * (m - 1) =
          128 * n * (m - 1) * y +
            (128 * n * (m - 1) * z + d * m * (m - 1)) := by
        dsimp only [m]
        ring
      _ ≤ 128 * n * (m - 1) * y + 64 * n * d * y := by
        exact add_le_add le_rfl htail
      _ ≤ 128 * n * (x - 1) * y := hfront
  have htwoM : 2 * Nat.choose m 2 = m * (m - 1) :=
    two_mul_choose_two m
  have htwoX : 2 * Nat.choose x 2 = x * (x - 1) :=
    two_mul_choose_two x
  have hscaled :
      2 * ((128 * n + d) * worstDownWeight s) ≤
        2 * ((128 * n) * worstUpWeight s) := by
    unfold worstDownWeight worstUpWeight
    change
      2 * ((128 * n + d) * (x * Nat.choose m 2)) ≤
        2 * ((128 * n) * (Nat.choose x 2 * y))
    calc
      2 * ((128 * n + d) * (x * Nat.choose m 2)) =
          x * ((128 * n + d) * (2 * Nat.choose m 2)) := by ring
      _ = x * ((128 * n + d) * (m * (m - 1))) := by rw [htwoM]
      _ ≤ x * (128 * n * (x - 1) * y) := by
        exact Nat.mul_le_mul_left x (by
          simpa only [Nat.mul_assoc] using hcore)
      _ = (128 * n) * ((2 * Nat.choose x 2) * y) := by
        rw [htwoX]
        ring
      _ = 2 * ((128 * n) * (Nat.choose x 2 * y)) := by ring
  omega

/-- Exact mass bias supplied by the entry-band arithmetic. -/
theorem entryBand_worst_mass_bias
    (h3 : 3 ≤ n) (d : ℕ) (s : State n B) (hs : EntryLive d s) :
    movePMF Control.worst s h3 .down ≤
      movePMF Control.worst s h3 .up * entryBase n d := by
  rw [movePMF_down, movePMF_up, downWeight_worst, upWeight_worst]
  apply div_le_div_mul_right
  unfold entryBase
  have hden0 : (((128 * n + d : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast (by omega : 128 * n + d ≠ 0)
  have hdenTop : (((128 * n + d : ℕ) : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [← mul_div_assoc,
    ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdenTop)]
  exact_mod_cast (by
    simpa [mul_comm] using entryBand_worst_weight_cross d s hs)

/-- The three action masses sum to one. -/
theorem movePMF_masses_sum
    (u : Control) (s : State n B) (h3 : 3 ≤ n) :
    movePMF u s h3 .down + movePMF u s h3 .stay +
      movePMF u s h3 .up = 1 := by
  have hsum := PMF.tsum_coe (movePMF u s h3)
  rw [tsum_fintype] at hsum
  rw [show (Finset.univ : Finset Action) =
    {Action.down, Action.stay, Action.up} from rfl] at hsum
  simpa [add_assoc, add_left_comm, add_comm] using hsum

/-- One physical step expanded over the three possible selected actions. -/
theorem expect_step_x_actions
    (u : Control) (s : State n B) (h3 : 3 ≤ n)
    (V : ℕ → ℝ≥0∞) :
    expect (step u s h3) (fun t => V (State.x t)) =
      movePMF u s h3 .down * V (State.x s - 1) +
      movePMF u s h3 .stay * V (State.x s) +
      movePMF u s h3 .up * V (State.x s + 1) := by
  calc
    expect (step u s h3) (fun t => V (State.x t)) =
        expect ((step u s h3).map State.x) V :=
      (expect_map (step u s h3) State.x V).symm
    _ = expect ((movePMF u s h3).map
          (Action.nextX (State.x s))) V := by rw [step_map_x]
    _ = expect (movePMF u s h3)
          (fun a => V (Action.nextX (State.x s) a)) :=
      expect_map (movePMF u s h3) (Action.nextX (State.x s)) V
    _ = movePMF u s h3 .down * V (State.x s - 1) +
          movePMF u s h3 .stay * V (State.x s) +
          movePMF u s h3 .up * V (State.x s + 1) := by
      unfold expect
      rw [tsum_fintype]
      rw [show (Finset.univ : Finset Action) =
        {Action.down, Action.stay, Action.up} from rfl]
      simp [Action.nextX]
      ring

/-- Exact one-step geometric conservation under the adverse response. -/
theorem entryBand_worst_conserve
    (h3 : 3 ≤ n) (d : ℕ) (s : State n B) (hs : EntryLive d s) :
    expect (step Control.worst s h3)
        (fun t => entryBase n d ^ State.x t) ≤
      entryBase n d ^ State.x s := by
  have hu1 := entryBase_le_one n d (by omega)
  have hx : 0 < State.x s := by
    have hlo := hs.1
    omega
  rw [expect_step_x_actions]
  have hkey := three_term_drift_ennreal
    (movePMF_masses_sum Control.worst s h3) hu1
    (entryBand_worst_mass_bias h3 d s hs)
  have hpowx :
      entryBase n d ^ State.x s =
        entryBase n d ^ (State.x s - 1) * entryBase n d := by
    rw [show State.x s = (State.x s - 1) + 1 by omega, pow_add]
    simp
  have hpowx1 :
      entryBase n d ^ (State.x s + 1) =
        entryBase n d ^ (State.x s - 1) * entryBase n d ^ 2 := by
    rw [show State.x s + 1 = (State.x s - 1) + 2 by omega, pow_add]
  calc
    movePMF Control.worst s h3 .down *
          entryBase n d ^ (State.x s - 1) +
        movePMF Control.worst s h3 .stay *
          entryBase n d ^ State.x s +
        movePMF Control.worst s h3 .up *
          entryBase n d ^ (State.x s + 1) =
      entryBase n d ^ (State.x s - 1) *
        (movePMF Control.worst s h3 .down +
          movePMF Control.worst s h3 .stay * entryBase n d +
          movePMF Control.worst s h3 .up * entryBase n d ^ 2) := by
      rw [hpowx, hpowx1]
      ring
    _ ≤ entryBase n d ^ (State.x s - 1) * entryBase n d :=
      mul_le_mul_right hkey _
    _ = entryBase n d ^ State.x s := by
      rw [show State.x s = (State.x s - 1) + 1 by omega, pow_add]
      simp

/-- On a budget-valid state the joint potential reduces to its geometric part
under every fixed-control step. -/
theorem expect_step_entryPotential_eq
    (u : Control) (s : State n B) (h3 : 3 ≤ n)
    (d : ℕ) (hb : EntryBudget d s) :
    expect (step u s h3) (entryPotential n d) =
      expect (step u s h3)
        (fun t => entryBase n d ^ State.x t) := by
  unfold step
  rw [expect_map, expect_map]
  congr 1
  funext k
  have hbudget : EntryBudget d (nextState u s k) := by
    unfold EntryBudget at hb ⊢
    rw [nextState_z]
    exact hb
  rw [entryPotential, if_pos hbudget]

/-- Exact one-step bound at every adaptive history before a monitor boundary. -/
theorem adaptiveStep_entryPotential_conserve
    (σ : Strategy n B) (hist : History n B)
    (s : State n B) (h3 : 3 ≤ n) (d : ℕ)
    (hbad : ¬ EntryBad d s) (htarget : ¬ EntryTarget s) :
    expect (adaptiveStep σ hist s h3) (entryPotential n d) ≤
      entryPotential n d s := by
  by_cases hb : EntryBudget d s
  · have hlive : EntryLive d s := by
      refine ⟨?_, ?_, hb⟩
      · unfold EntryBad at hbad
        omega
      · unfold EntryTarget at htarget
        omega
    calc
      expect (adaptiveStep σ hist s h3) (entryPotential n d) =
          expect (adaptiveStep σ hist s h3)
            (fun t => entryBase n d ^ State.x t) := by
        unfold adaptiveStep
        exact expect_step_entryPotential_eq
          (σ.choose hist s) s h3 d hb
      _ ≤ expect (step Control.worst s h3)
            (fun t => entryBase n d ^ State.x t) :=
        adaptiveStep_expect_x_le_worst σ hist s h3
          (fun k => entryBase n d ^ k)
          (entryBase_pow_antitone n d (by omega))
      _ ≤ entryBase n d ^ State.x s :=
        entryBand_worst_conserve h3 d s hlive
      _ = entryPotential n d s := by
        simp [entryPotential, hb]
  · rw [entryPotential, if_neg hb]
    exact le_top

/-- Stop on lower failure or the upper entry checkpoint. -/
def EntryStop (d : ℕ) (s : State n B) : Prop :=
  EntryBad d s ∨ EntryTarget s

instance entryStopDecidable (d : ℕ) (s : State n B) :
    Decidable (EntryStop d s) := by
  unfold EntryStop
  infer_instance

/-- History-dependent physical law stopped on the entry monitor boundaries. -/
noncomputable def entryLaw
    (σ : Strategy n B) (h3 : 3 ≤ n) (d : ℕ) :
    ℕ → History n B → State n B → PMF (State n B)
  | 0, _, s => PMF.pure s
  | T + 1, hist, s =>
      if EntryStop d s then
        PMF.pure s
      else
        (adaptiveEventStep σ hist s h3).bind
          (fun e => entryLaw σ h3 d T (e :: hist) e.after)

/-- The joint potential is a supermartingale for the stopped finite law. -/
theorem entryLaw_expect_le
    (σ : Strategy n B) (h3 : 3 ≤ n) (d : ℕ) :
    ∀ T hist s,
      expect (entryLaw σ h3 d T hist s) (entryPotential n d) ≤
        entryPotential n d s := by
  intro T
  induction T with
  | zero =>
      intro hist s
      simp [entryLaw]
  | succ T ih =>
      intro hist s
      by_cases hstop : EntryStop d s
      · rw [entryLaw, if_pos hstop, expect_pure]
      · rw [entryLaw, if_neg hstop, expect_bind']
        have hbad : ¬ EntryBad d s := by
          intro h
          exact hstop (Or.inl h)
        have htarget : ¬ EntryTarget s := by
          intro h
          exact hstop (Or.inr h)
        calc
          (∑' e, adaptiveEventStep σ hist s h3 e *
              expect (entryLaw σ h3 d T (e :: hist) e.after)
                (entryPotential n d)) ≤
              ∑' e, adaptiveEventStep σ hist s h3 e *
                entryPotential n d e.after := by
            exact ENNReal.tsum_le_tsum fun e =>
              mul_le_mul_right (ih (e :: hist) e.after) _
          _ = expect (adaptiveEventStep σ hist s h3)
                (fun e => entryPotential n d e.after) := by
            rfl
          _ = expect (adaptiveStep σ hist s h3)
                (entryPotential n d) :=
            expect_adaptiveEventStep_after σ hist s h3
              (entryPotential n d)
          _ ≤ entryPotential n d s :=
            adaptiveStep_entryPotential_conserve
              σ hist s h3 d hbad htarget

/-- Terminal lower-failure mass of the stopped entry monitor. -/
noncomputable def entryFailureMass
    (σ : Strategy n B) (h3 : 3 ≤ n) (d T : ℕ)
    (hist : History n B) (s : State n B) : ℝ≥0∞ :=
  ∑' t, if EntryBad d t then entryLaw σ h3 d T hist s t else 0

/-- Every lower-failure state has at least the threshold potential. -/
theorem entryPotential_bad_floor
    (h3 : 3 ≤ n) (d : ℕ) (s : State n B) (hs : EntryBad d s) :
    entryBase n d ^ entryLower n d ≤ entryPotential n d s := by
  by_cases hb : EntryBudget d s
  · rw [entryPotential, if_pos hb]
    apply entryBase_pow_antitone n d (by omega)
    unfold entryLower EntryBad at *
    omega
  · rw [entryPotential, if_neg hb]
    exact le_top

/-- Exact finite-horizon no-backsliding bound for every adaptive strategy. -/
theorem adaptive_entry_failure_le
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (d T : ℕ) (s₀ : State n B)
    (hbudget : EntryBudget d s₀) :
    entryFailureMass σ h3 d T [] s₀ ≤
      entryBase n d ^ State.x s₀ /
        entryBase n d ^ entryLower n d := by
  have hu0 := entryBase_ne_zero n d (by omega)
  have hutop : entryBase n d ≠ ⊤ := by
    unfold entryBase
    finiteness
  have hpow0 : entryBase n d ^ entryLower n d ≠ 0 :=
    pow_ne_zero _ hu0
  have hpowtop : entryBase n d ^ entryLower n d ≠ ⊤ :=
    ENNReal.pow_ne_top hutop
  unfold entryFailureMass
  calc
    (∑' t, if EntryBad d t then entryLaw σ h3 d T [] s₀ t else 0) ≤
        ∑' t, if entryBase n d ^ entryLower n d ≤
            entryPotential n d t then
          entryLaw σ h3 d T [] s₀ t else 0 := by
      refine ENNReal.tsum_le_tsum fun t => ?_
      by_cases ht : EntryBad d t
      · have hf := entryPotential_bad_floor h3 d t ht
        simp [ht, hf]
      · simp [ht]
    _ ≤ expect (entryLaw σ h3 d T [] s₀) (entryPotential n d) /
          entryBase n d ^ entryLower n d :=
      markov_div _ _ _ hpow0 hpowtop
    _ ≤ entryPotential n d s₀ /
          entryBase n d ^ entryLower n d :=
      ENNReal.div_le_div_right
        (entryLaw_expect_le σ h3 d T [] s₀) _
    _ = entryBase n d ^ State.x s₀ /
          entryBase n d ^ entryLower n d := by
      rw [entryPotential, if_pos hbudget]

/-- The paper's initial gap and budget imply a valid monitor start. -/
theorem paper_initial_implies_entry_start
    (d : ℕ) (s₀ : State n B)
    (hgap : n + d ≤ 2 * State.x s₀)
    (hbudget : 16 * State.z s₀ ≤ d) :
    EntryBudget d s₀ ∧ ¬ EntryBad d s₀ := by
  constructor
  · exact hbudget
  · unfold EntryBad
    omega

/-- Paper-facing finite-horizon corollary. -/
theorem adaptive_entry_failure_le_of_paper_initial
    (σ : Strategy n B) (h3 : 3 ≤ n)
    (d T : ℕ) (s₀ : State n B)
    (hgap : n + d ≤ 2 * State.x s₀)
    (hbudget : 16 * State.z s₀ ≤ d) :
    entryFailureMass σ h3 d T [] s₀ ≤
      entryBase n d ^ State.x s₀ /
        entryBase n d ^ entryLower n d := by
  have hstart :=
    paper_initial_implies_entry_start d s₀ hgap hbudget
  exact adaptive_entry_failure_le σ h3 d T s₀ hstart.1

end Tri.Byzantine

#print axioms Tri.Byzantine.entryBand_worst_weight_cross
#print axioms Tri.Byzantine.entryBand_worst_mass_bias
#print axioms Tri.Byzantine.entryBand_worst_conserve
#print axioms Tri.Byzantine.adaptiveStep_entryPotential_conserve
#print axioms Tri.Byzantine.entryLaw_expect_le
#print axioms Tri.Byzantine.adaptive_entry_failure_le
