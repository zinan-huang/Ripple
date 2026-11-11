/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.sCRNUniversality.ClockedCTM.Run
import Ripple.sCRNUniversality.Stochastic.MassAction.Completion

/-!
# Completion of the clocked CTM simulation

`SimOK S N z0 ω` (`Assembly.lean`) is a safety predicate: no tick before the `N`-th is drawn
outside its target class.  This file adds the liveness half.

* `Reaches N ω`: tick `N` is drawn along `ω`; `Simulates S N z0 ω := SimOK ∧ Reaches`.
* `good_path`: on a correct run without null labels, after `n` jumps with fewer than `N` ticks
  the clock invariant holds, the non-clock state lies in the window of the current tick count,
  and (after the first tick) the potential is below the start bound of that window.
* `law_simOK_not_reaches`: if the window sets (with the potential below its start bound) have
  bounded populations, the correct runs that never reach tick `N` form a null set: the total
  propensity is bounded on them, so every jump costs at least a fixed expected holding time,
  while `expTime` is finite (`MassAction.measure_tsum_eq_top`).
* `schW_bounded`: the windows of `ctmSched` are bounded (the memory classes bound the memory
  directly; in stage (c) of `Win34` the potential bound `V34 ≤ Θ34` bounds `Φ₁` and `Φ₂`
  through its logarithmic terms).
* `ctm_simulates_error_time`: the CTM-level error and time bounds for `Simulates`.

Under `rawLaw` (the embedded jump chain) and with `expTime` (the expected holding-time
functional before tick `N`), "the simulation completes" is the event `Reaches N`; explosion
(infinitely many jumps in finite expected time) cannot occur on a correct run before tick `N`,
because the populations are bounded there.
-/

namespace Ripple.sCRNUniversality.ClockedCTM

open MeasureTheory Preorder Stochastic Stochastic.MassAction
open scoped ENNReal

variable {Q : Type} [Fintype Q] [DecidableEq Q] {L : ℕ} {C : CTM Q}

/-! ### Ticks -/

/-- Tick `N` is drawn along `ω`. -/
def Reaches (N : ℕ) (ω : ℕ → Option (Rx Q L)) : Prop := ∃ n, ticks n ω = N

/-- **Correct and complete simulation up to tick `N`**: every tick before the `N`-th is drawn
from its target class (`SimOK`), and tick `N` is drawn (`Reaches`). -/
def Simulates (S : Sched C L) (N : ℕ) (z0 : State (Sp Q L)) (ω : ℕ → Option (Rx Q L)) : Prop :=
  SimOK S N z0 ω ∧ Reaches N ω

omit [Fintype Q] in
theorem ticks_succ (n : ℕ) (ω : ℕ → Option (Rx Q L)) :
    ticks (n + 1) ω = ticks n ω + if ω (n + 1) = some .tick then 1 else 0 := rfl

omit [Fintype Q] in
theorem ticks_le_succ (n : ℕ) (ω : ℕ → Option (Rx Q L)) : ticks (n + 1) ω ≤ ticks n ω + 1 := by
  rw [ticks_succ]; split_ifs <;> omega

omit [Fintype Q] in
theorem ticks_mono (ω : ℕ → Option (Rx Q L)) {m n : ℕ} (h : m ≤ n) : ticks m ω ≤ ticks n ω := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (Nat.le_add_right _ _)

omit [Fintype Q] in
theorem ticks_det : ∀ (n : ℕ) {ω ω' : ℕ → Option (Rx Q L)},
    frestrictLe n ω = frestrictLe n ω' → ticks n ω = ticks n ω'
  | 0, _, _, _ => rfl
  | n + 1, ω, ω', h => by
    have h1 : frestrictLe n ω = frestrictLe n ω' := by
      funext k
      have := congrFun h ⟨k.1, Finset.mem_Iic.mpr
        (le_trans (Finset.mem_Iic.mp k.2) (Nat.le_succ n))⟩
      simpa using this
    have h2 : ω (n + 1) = ω' (n + 1) := by
      have := congrFun h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩
      simpa using this
    rw [ticks_succ, ticks_succ, ticks_det n h1, h2]

omit [Fintype Q] in
/-- If the tick count reaches `N`, it equals `N` after some jump. -/
theorem exists_ticks_eq_of_le (ω : ℕ → Option (Rx Q L)) {N n : ℕ} (h : N ≤ ticks n ω) :
    ∃ m, ticks m ω = N := by
  induction n with
  | zero => exact ⟨0, by simp only [ticks] at h ⊢; omega⟩
  | succ n ih =>
    by_cases hn : N ≤ ticks n ω
    · exact ih hn
    · exact ⟨n + 1, by have := ticks_le_succ n ω; omega⟩

omit [Fintype Q] in
theorem Reaches.mono (ω : ℕ → Option (Rx Q L)) {N N' : ℕ} (h : N ≤ N') (hr : Reaches N' ω) :
    Reaches N ω := by
  obtain ⟨n, hn⟩ := hr
  exact exists_ticks_eq_of_le ω (hn ▸ h)

omit [Fintype Q] in
/-- The jump that draws tick `N ≥ 1`. -/
theorem exists_tick_of_ticks_eq (ω : ℕ → Option (Rx Q L)) {N n : ℕ} (hN : 1 ≤ N)
    (h : ticks n ω = N) : ∃ k < n, ω (k + 1) = some .tick ∧ ticks k ω + 1 = N := by
  induction n with
  | zero => simp only [ticks] at h; omega
  | succ n ih =>
    rw [ticks_succ] at h
    split_ifs at h with ht
    · exact ⟨n, Nat.lt_succ_self n, ht, h⟩
    · obtain ⟨k, hk, hkt, hkN⟩ := ih (by omega)
      exact ⟨k, by omega, hkt, hkN⟩

/-! ### Paths -/

theorem traj_zero (C : CTM Q) (z0 : State (Sp Q L)) (ω : ℕ → Option (Rx Q L)) :
    traj C z0 0 ω = z0 := rfl

theorem traj_succ (C : CTM Q) (z0 : State (Sp Q L)) (n : ℕ) (ω : ℕ → Option (Rx Q L)) :
    traj C z0 (n + 1) ω = stateStep (net C L) (traj C z0 n ω) (ω (n + 1)) := rfl

/-- Some label of mass-action probability zero is drawn. -/
def NullLabel (C : CTM Q) (z0 : State (Sp Q L)) (ω : ℕ → Option (Rx Q L)) : Prop :=
  ∃ n, massActionPMF (net C L) (net_hasPositiveRates C L) (traj C z0 n ω) (ω (n + 1)) = 0

theorem law_nullLabel (C : CTM Q) (z0 : State (Sp Q L)) :
    rawLaw (net C L) (net_hasPositiveRates C L) z0 {ω | NullLabel C z0 ω} = 0 :=
  rawLaw_null_label (net C L) (net_hasPositiveRates C L) z0

/-- **Window invariant along a correct run.** On a run without null labels in which every tick
before the `N`-th is correct, after `n` jumps with fewer than `N` ticks the clock invariant
holds, the non-clock state lies in the window of the current tick count, and after the first
tick the potential is below the start bound of that window. -/
theorem good_path (S : Sched C L) (N : ℕ) {a f : ℕ} (ha : 1 ≤ a) (hf : 1 ≤ f)
    {z0 : State (Sp Q L)} (hz0 : ClockAt (a * f) f (Fin.last L) z0) (hW0 : S.W 0 (rest z0))
    {ω : ℕ → Option (Rx Q L)} (hok : SimOK S N z0 ω) (hnull : ¬ NullLabel C z0 ω) :
    ∀ n, ticks n ω < N →
      (∃ c, ClockAt (a * f) f c (traj C z0 n ω)) ∧ S.W (ticks n ω) (rest (traj C z0 n ω)) ∧
        (1 ≤ ticks n ω → S.V (ticks n ω) (rest (traj C z0 n ω)) ≤ S.Θ (ticks n ω)) := by
  have haf : 1 ≤ a * f := Nat.one_le_iff_ne_zero.mpr (by positivity)
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨⟨_, hz0⟩, hW0, fun h => by simp [ticks] at h⟩
  | succ n ih =>
    intro hlt
    have hle : ticks n ω ≤ ticks (n + 1) ω := ticks_mono ω (Nat.le_succ n)
    obtain ⟨⟨c, hc⟩, hW, hV⟩ := ih (lt_of_le_of_lt hle hlt)
    have hT := not_terminal_of_clockAt (C := C) haf hf hc
    have hpmf : massActionPMF (net C L) (net_hasPositiveRates C L) (traj C z0 n ω)
        (ω (n + 1)) ≠ 0 := fun h0 => hnull ⟨n, h0⟩
    cases ho : ω (n + 1) with
    | none =>
      have h0 : massActionPMF (net C L) (net_hasPositiveRates C L) (traj C z0 n ω)
          (none : Option (Rx Q L)) = 0 := pmf_none C hT
      rw [ho, h0] at hpmf
      exact absurd rfl hpmf
    | some i =>
      have hs : massActionPMF (net C L) (net_hasPositiveRates C L) (traj C z0 n ω)
          (some i : Option (Rx Q L)) =
            (rate C i (traj C z0 n ω) : ℝ≥0∞) / (btot C (traj C z0 n ω) : ℝ≥0∞) :=
        pmf_some C hT i
      rw [ho, hs] at hpmf
      have hr : rate C i (traj C z0 n ω) ≠ 0 := by
        intro h; apply hpmf; simp [h]
      have hstep : traj C z0 (n + 1) ω = (rxn C i).fire (traj C z0 n ω) := by
        rw [traj_succ, ho]
        exact stateStep_of_rate C hr
      by_cases hi : i.IsClock
      · cases i <;> simp only [Rx.IsClock] at hi
        · -- tick
          have hc0 : c.val = 0 := by
            by_contra hne
            rw [rate_tick_of C hc, if_neg hne] at hr
            exact hr rfl
          have hc' := ClockAt.tick (C := C) hf (show ClockAt (a * f) f 0 (traj C z0 n ω) by
            rwa [show (0 : Fin (L + 1)) = c from Fin.ext (by simp [hc0])])
          have hk : ticks (n + 1) ω = ticks n ω + 1 := by
            rw [ticks_succ, ho, if_pos rfl]
          have hCl : S.Cl (ticks n ω) (rest (traj C z0 n ω)) :=
            hok n ho (lt_of_le_of_lt hle hlt)
          obtain ⟨hW', hV'⟩ := S.start (ticks n ω) _ hW hCl
          rw [hstep, rest_fire_tick, hk]
          exact ⟨⟨_, hc'⟩, hW', fun _ => hV'⟩
        · -- up
          rename_i c'
          have hcc : c'.castSucc = c := by
            by_contra hne
            rw [rate_up_of C hc, if_neg hne] at hr
            exact hr rfl
          have hc' := ClockAt.up (C := C) haf (hcc ▸ hc)
          have hk : ticks (n + 1) ω = ticks n ω := by
            rw [ticks_succ, ho,
              if_neg (show (some (Rx.up c') : Option (Rx Q L)) ≠ some .tick by simp), add_zero]
          rw [hstep, rest_fire_up, hk]
          exact ⟨⟨_, hc'⟩, hW, hV⟩
        · -- down
          rename_i c'
          have hcc : c'.succ = c := by
            by_contra hne
            rw [rate_down_of C hc, if_neg hne] at hr
            exact hr rfl
          have hc' := ClockAt.down (C := C) hf (hcc ▸ hc)
          have hk : ticks (n + 1) ω = ticks n ω := by
            rw [ticks_succ, ho,
              if_neg (show (some (Rx.down c') : Option (Rx Q L)) ≠ some .tick by simp), add_zero]
          rw [hstep, rest_fire_down, hk]
          exact ⟨⟨_, hc'⟩, hW, hV⟩
      · have hc' := hc.fire_nonclock (C := C) hi
        have hne : (some i : Option (Rx Q L)) ≠ some .tick := fun e => hi (by
          simp only [Option.some.injEq] at e; subst e; simp [Rx.IsClock])
        have hk : ticks (n + 1) ω = ticks n ω := by
          rw [ticks_succ, ho, if_neg hne, add_zero]
        have hr' : rate C i (rest (traj C z0 n ω)) ≠ 0 := by rw [rate_rest C hi]; exact hr
        obtain ⟨hW', hV'⟩ := S.fire (ticks n ω) _ hW i hi hr'
        rw [hstep, rest_fire C hi, hk]
        exact ⟨⟨_, hc'⟩, hW', fun h1 => hV'.trans (hV h1)⟩

/-! ### Bounded populations -/

omit [DecidableEq Q] in
theorem btot_le_of_le (C : CTM Q) {z : State (Sp Q L)} {B : ℕ} (h : ∀ s, z s ≤ B) :
    btot C z ≤ Fintype.card (Rx Q L) * (B * B) := by
  unfold btot
  calc ∑ i : Rx Q L, rate C i z ≤ ∑ _i : Rx Q L, B * B :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul (h _) (h _)
    _ = Fintype.card (Rx Q L) * (B * B) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

omit [Fintype Q] [DecidableEq Q] in
/-- A state with the clock invariant and bounded non-clock part is bounded. -/
theorem state_le_of_clockAt {r f : ℕ} {c : Fin (L + 1)} {z : State (Sp Q L)}
    (hc : ClockAt r f c z) {B : ℕ} (hB : ∀ s : Sp Q L, ¬ s.IsClock → rest z s ≤ B)
    (s : Sp Q L) : z s ≤ B + r + f + 1 := by
  by_cases hs : s.IsClock
  · obtain ⟨ha, hf, hclk⟩ := hc
    cases s <;> simp only [Sp.IsClock] at hs
    · rw [hclk]; split_ifs <;> omega
    · rw [ha]; omega
    · rw [hf]; omega
  · have := hB s hs
    simp only [rest, if_neg hs] at this
    omega

/-- **Correct runs reach tick `N` almost surely** when the window sets are bounded. -/
theorem law_simOK_not_reaches (S : Sched C L) (N : ℕ) {a f : ℕ} (ha : 2 ≤ a) (hf : 1 ≤ f)
    (hL : 1 ≤ L) {z0 : State (Sp Q L)} (hz0 : ClockAt (a * f) f (Fin.last L) z0)
    (hW0 : S.W 0 (rest z0)) (B : ℕ)
    (hB : ∀ k < N, ∀ w : State (Sp Q L), S.W k w → (1 ≤ k → S.V k w ≤ S.Θ k) →
      ∀ s : Sp Q L, ¬ s.IsClock → w s ≤ B) :
    rawLaw (net C L) (net_hasPositiveRates C L) z0 {ω | SimOK S N z0 ω ∧ ¬ Reaches N ω} = 0 := by
  classical
  have ha1 : 1 ≤ a := by omega
  let g : ℕ → ((k : ℕ) → Option (net C L).I) → ℝ≥0∞ := fun n ω =>
    if ticks n ω < N then (((net C L).totalPropensity (traj C z0 n ω) : ℝ≥0∞))⁻¹ else 0
  have hg : ∀ n, Measurable (g n) := fun n =>
    measurable_of_frestrictLe (net C L) n (g n) fun ω ω' h => by
      have h' : frestrictLe (π := fun _ => Option (Rx Q L)) n ω = frestrictLe n ω' := h
      simp only [g, ticks_det n h', traj, h']
      rfl
  have hfin : ∫⁻ ω, ∑' n, g n ω ∂(rawLaw (net C L) (net_hasPositiveRates C L) z0) ≠ ⊤ := by
    have h := expTime_le (C := C) N ha hf hL hz0
    unfold expTime at h
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hcast : ∀ m : ℕ, (((m : ℚ≥0)) : ℝ≥0∞) = (m : ℝ≥0∞) := fun m => by
    rw [← ENNReal.coe_nnratCast, NNRat.cast_natCast, ENNReal.coe_natCast]
  refine measure_mono_null ?_
    (measure_union_null (law_nullLabel C z0) (measure_tsum_eq_top g hg hfin))
  rintro ω ⟨hok, hnr⟩
  by_cases hnull : NullLabel C z0 ω
  · exact Or.inl hnull
  refine Or.inr ?_
  have hlt : ∀ n, ticks n ω < N := fun n =>
    lt_of_not_ge fun h => hnr (exists_ticks_eq_of_le ω h)
  change ∑' n, g n ω = ⊤
  refine tsum_eq_top_of_le
    (ε := (((Fintype.card (Rx Q L) * ((B + a * f + f + 1) * (B + a * f + f + 1)) : ℕ) :
      ℝ≥0∞))⁻¹)
    (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)) fun n => ?_
  obtain ⟨⟨c, hc⟩, hW, hV⟩ := good_path S N ha1 hf hz0 hW0 hok hnull n (hlt n)
  have hbnd : ∀ s, traj C z0 n ω s ≤ B + a * f + f + 1 :=
    state_le_of_clockAt hc (hB _ (hlt n) _ hW hV)
  simp only [g, if_pos (hlt n), totalPropensity_eq, hcast]
  exact ENNReal.inv_le_inv.mpr (by exact_mod_cast btot_le_of_le C hbnd)

/-- **Error bound for a schedule, with completion.** -/
theorem sched_simulates_error_le (S : Sched C L) (N : ℕ) {a f : ℕ} (ha : 2 ≤ a) (hf : 1 ≤ f)
    (hL : 1 ≤ L) {z0 : State (Sp Q L)} (hz0 : ClockAt (a * f) f (Fin.last L) z0)
    (hW0 : S.W 0 (rest z0)) (hC0 : S.Cl 0 (rest z0)) (B : ℕ)
    (hB : ∀ k < N, ∀ w : State (Sp Q L), S.W k w → (1 ≤ k → S.V k w ≤ S.Θ k) →
      ∀ s : Sp Q L, ¬ s.IsClock → w s ≤ B) :
    rawLaw (net C L) (net_hasPositiveRates C L) z0 {ω | ¬ Simulates S N z0 ω} ≤
      ENNReal.ofReal ((f : ℝ) / gs a L * ∑ j ∈ Finset.Ioo 0 N, S.Θ j) := by
  have hsub : {ω | ¬ Simulates S N z0 ω} ⊆
      {ω | ¬ SimOK S N z0 ω} ∪ {ω | SimOK S N z0 ω ∧ ¬ Reaches N ω} := by
    intro ω hω
    by_cases h : SimOK S N z0 ω
    · exact Or.inr ⟨h, fun hr => hω ⟨h, hr⟩⟩
    · exact Or.inl h
  calc _ ≤ _ := measure_mono hsub
    _ ≤ rawLaw (net C L) (net_hasPositiveRates C L) z0 {ω | ¬ SimOK S N z0 ω} +
        rawLaw (net C L) (net_hasPositiveRates C L) z0 {ω | SimOK S N z0 ω ∧ ¬ Reaches N ω} :=
        measure_union_le _ _
    _ = rawLaw (net C L) (net_hasPositiveRates C L) z0 {ω | ¬ SimOK S N z0 ω} := by
        rw [law_simOK_not_reaches S N ha hf hL hz0 hW0 B hB, add_zero]
    _ ≤ _ := sched_error_le S N (by omega) hf hL hz0 hW0 hC0

/-! ### The windows of `ctmSched` are bounded -/

theorem memA_le {m T0 x : ℕ} {v : Mem → ℕ} (h : MemA m T0 x v) (y : Mem) :
    v y ≤ m + T0 + x + 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  cases y <;> omega

theorem mem4_le {m T0 x' : ℕ} {v : Mem → ℕ} (h : Mem4 m T0 x' v) (y : Mem) :
    v y ≤ m + T0 + x' + 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  cases y <;> omega

omit [Fintype Q] [DecidableEq Q] in
theorem memC_le {m T0 x' : ℕ} {b z : Bool} {w : State (Sp Q L)}
    (h : MemC m T0 b z x' (memv w)) {P1 P2 : ℕ} (h1 : phi1 w ≤ P1) (h2 : phi2 w ≤ P2) (y : Mem) :
    w (.mem y) ≤ m + T0 + x' + 1 + P1 + P2 := by
  obtain ⟨e1, e2, e3, e4⟩ := h
  simp only [memv_apply] at e1 e2 e3 e4
  unfold phi1 at h1
  unfold phi2 at h2
  cases b <;> cases z <;>
    simp only [show bw true = 2 from rfl, show bw false = 1 from rfl] at e1 <;>
    cases y <;> omega

omit [Fintype Q] [DecidableEq Q] in
/-- The logarithmic terms of `V34` bound `Φ₁` and `Φ₂`. -/
theorem phi_le_of_V34_le {m g x' : ℕ} (hm : 1 ≤ m) (hx' : 1 ≤ x') {q : Q} {b : Bool}
    {w : State (Sp Q L)} {Θ : ℝ} (hΘ : 0 ≤ Θ) (hV : V34 m g x' q b w ≤ Θ) {X : ℕ} (hX : x' ≤ X) :
    phi1 w ≤ ⌈Real.exp ((m : ℝ) * Θ / 4)⌉₊ ∧ phi2 w ≤ ⌈Real.exp ((X : ℝ) * Θ / 4)⌉₊ := by
  unfold V34 at hV
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hx0 : (0 : ℝ) < x' := by exact_mod_cast hx'
  have hXr : (x' : ℝ) ≤ X := by exact_mod_cast hX
  have t1 : 0 ≤ (if w .i = 1 then 1 / (m : ℝ) else 0) := by split_ifs <;> positivity
  have t2 : 0 ≤ (if w .i = 1 ∨ w (.rq q) = 1 then 1 / (g : ℝ) else 0) := by
    split_ifs <;> positivity
  have t3 := aut_nonneg m (max (w (.u q b)) 1)
  have p1 : (0 : ℝ) ≤ phi1 w := Nat.cast_nonneg _
  have p2 : (0 : ℝ) ≤ phi2 w := Nat.cast_nonneg _
  have l1 : 0 ≤ Real.log (1 + (phi1 w : ℝ)) := Real.log_nonneg (by linarith)
  have l2 : 0 ≤ Real.log (1 + (phi2 w : ℝ)) := Real.log_nonneg (by linarith)
  have t4 : 0 ≤ 4 / (m : ℝ) * Real.log (1 + phi1 w) := by positivity
  have t5 : 0 ≤ 4 / (x' : ℝ) * Real.log (1 + phi2 w) := by positivity
  constructor
  · have h : 4 / (m : ℝ) * Real.log (1 + phi1 w) ≤ Θ := by linarith
    have h' : Real.log (1 + (phi1 w : ℝ)) ≤ (m : ℝ) * Θ / 4 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hm0] at h
      linarith
    have he := Real.exp_le_exp.mpr h'
    rw [Real.exp_log (by positivity)] at he
    have hc := he.trans (Nat.le_ceil _)
    exact_mod_cast (by linarith : (phi1 w : ℝ) ≤ (⌈Real.exp ((m : ℝ) * Θ / 4)⌉₊ : ℝ))
  · have h : 4 / (x' : ℝ) * Real.log (1 + phi2 w) ≤ Θ := by linarith
    have h' : Real.log (1 + (phi2 w : ℝ)) ≤ (X : ℝ) * Θ / 4 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hx0] at h
      have := mul_le_mul_of_nonneg_right hXr hΘ
      linarith
    have he := Real.exp_le_exp.mpr h'
    rw [Real.exp_log (by positivity)] at he
    have hc := he.trans (Nat.le_ceil _)
    exact_mod_cast (by linarith : (phi2 w : ℝ) ≤ (⌈Real.exp ((X : ℝ) * Θ / 4)⌉₊ : ℝ))

omit [Fintype Q] [DecidableEq Q] in
theorem state_le_of_onlyState {l : List (Sp Q L)} {w : State (Sp Q L)} (h : OnlyState l w)
    {B : ℕ} (hl : ∀ s ∈ l, w s ≤ B) {s : Sp Q L} (hs : s.IsState) : w s ≤ B := by
  by_cases hsl : s ∈ l
  · exact hl s hsl
  · rw [h s hs hsl]; exact Nat.zero_le _

omit [Fintype Q] [DecidableEq Q] in
theorem le_of_state_mem {w : State (Sp Q L)} {B : ℕ} (hA : ∀ s : Sp Q L, s.IsState → w s ≤ B)
    (hB : ∀ y, w (.mem y) ≤ B) {s : Sp Q L} (hs : ¬ s.IsClock) : w s ≤ B := by
  cases s <;> first | exact hB _ | exact absurd trivial hs | exact hA _ trivial

/-- **The windows of `ctmSched` are bounded.** -/
theorem schW_bounded (C : CTM Q) {n : ℕ} {c0 : Q × List Bool} (hc0 : c0.2.length = n + 3) :
    ∃ B : ℕ, ∀ k, ∀ w : State (Sp Q L), schW C n c0 k w →
      (1 ≤ k → schV C n c0 k w ≤ schΘ n k) → ∀ s : Sp Q L, ¬ s.IsClock → w s ≤ B := by
  refine ⟨9 * 3 ^ n + 20 * 3 ^ n + 3 * (9 * 3 ^ n) + 1 +
    ⌈Real.exp (((9 * 3 ^ n : ℕ) : ℝ) * Θ34 n / 4)⌉₊ +
    ⌈Real.exp (((3 * (9 * 3 ^ n) : ℕ) : ℝ) * Θ34 n / 4)⌉₊, ?_⟩
  intro k w hW hV s hs
  have hm1 : 1 ≤ 9 * 3 ^ n := by have := Nat.one_le_pow n 3 (by norm_num); omega
  obtain ⟨-, -, -, hx'ge, hx'lt, hxlt⟩ := tape_facts (cfg_length C hc0 k)
    (C.next (cfg C c0 k).1 ((cfg C c0 k).2.headD false)).2
  have hx'ge' : 9 * 3 ^ n ≤ tval (C.stepT (cfg C c0 k)).2 := hx'ge
  have hx'lt' : tval (C.stepT (cfg C c0 k)).2 < 3 * (9 * 3 ^ n) := hx'lt
  unfold schW at hW
  by_cases hk0 : k = 0
  · -- `K1`
    simp only [if_pos hk0] at hW
    obtain ⟨hO, hs1, hM⟩ := hW
    refine le_of_state_mem (fun s₁ hs₁ => ?_) (fun y => (memA_le hM y).trans (by omega)) hs
    refine state_le_of_onlyState hO (fun s' hs' => ?_) hs₁
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
    subst hs'; omega
  by_cases hk1 : k % 4 = 1
  · -- `Win12`
    simp only [if_neg hk0, if_pos hk1] at hW
    obtain ⟨⟨hO, hs12, hi, hM⟩, -⟩ := hW
    refine le_of_state_mem (fun s₁ hs₁ => ?_) (fun y => (memA_le hM y).trans (by omega)) hs
    refine state_le_of_onlyState hO (fun s' hs' => ?_) hs₁
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
    rcases hs' with rfl | rfl | rfl <;> omega
  by_cases hk2 : k % 4 = 2
  · -- `Win23`
    simp only [if_neg hk0, if_neg hk1, if_pos hk2] at hW
    obtain ⟨hO, hs23, hi, hM, -⟩ := hW
    refine le_of_state_mem (fun s₁ hs₁ => ?_) (fun y => (memA_le hM y).trans (by omega)) hs
    refine state_le_of_onlyState hO (fun s' hs' => ?_) hs₁
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
    rcases hs' with rfl | rfl | rfl <;> omega
  by_cases hk3 : k % 4 = 3
  · -- `Win34`
    simp only [if_neg hk0, if_neg hk1, if_neg hk2, if_pos hk3] at hW
    have hV' : V34 (9 * 3 ^ n) (2 * 3 ^ n) (tval (C.stepT (cfg C c0 k)).2) (cfg C c0 k).1
        ((cfg C c0 k).2.headD false) w ≤ Θ34 n := by
      have := hV (by omega)
      unfold schV schΘ at this
      simpa only [if_neg hk0, if_neg hk1, if_neg hk2, if_pos hk3] using this
    rcases hW with ⟨hO, hi, hs3, hM⟩ | ⟨hO, hr, hs3, hM⟩ | ⟨hO, hsu, hu, hM⟩
    · refine le_of_state_mem (fun s₁ hs₁ => ?_) (fun y => (memA_le hM.1 y).trans (by omega)) hs
      refine state_le_of_onlyState hO (fun s' hs' => ?_) hs₁
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
      rcases hs' with rfl | rfl <;> omega
    · refine le_of_state_mem (fun s₁ hs₁ => ?_) (fun y => (memA_le hM.1 y).trans (by omega)) hs
      refine state_le_of_onlyState hO (fun s' hs' => ?_) hs₁
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
      rcases hs' with rfl | rfl <;> omega
    · obtain ⟨hp1, hp2⟩ := phi_le_of_V34_le hm1 (by omega) (Θ34_nonneg n) hV' hx'lt'.le
      refine le_of_state_mem (fun s₁ hs₁ => ?_)
        (fun y => (memC_le hM hp1 hp2 y).trans (by omega)) hs
      refine state_le_of_onlyState hO (fun s' hs' => ?_) hs₁
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
      rcases hs' with rfl | rfl <;> omega
  · -- `Win41`
    simp only [if_neg hk0, if_neg hk1, if_neg hk2, if_neg hk3] at hW
    obtain ⟨hO, hsu, hi, hM⟩ := hW
    refine le_of_state_mem (fun s₁ hs₁ => ?_) (fun y => (mem4_le hM y).trans (by omega)) hs
    refine state_le_of_onlyState hO (fun s' hs' => ?_) hs₁
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
    rcases hs' with rfl | rfl | rfl <;> omega

/-- **CTM-level error and time bounds with completion** for clock parameters `a ≥ 2`,
`f ≥ 1`: from `initState n c0 a f`, the probability that the simulation is not correct and
complete up to tick `4 t` is at most `(f / G) t Θsum n`, and the expected time before tick
`4 t` is at most `8 t G / f`, `G = 1 + a + ⋯ + a^L`. -/
theorem ctm_simulates_error_time (C : CTM Q) (hL : 1 ≤ L) {n : ℕ} {c0 : Q × List Bool}
    (hc0 : c0.2.length = n + 3) (t : ℕ) {a f : ℕ} (ha : 2 ≤ a) (hf : 1 ≤ f) :
    rawLaw (net C L) (net_hasPositiveRates C L) (initState n c0 a f)
        {ω | ¬ Simulates (ctmSched C n c0 hc0) (4 * t) (initState n c0 a f) ω} ≤
      ENNReal.ofReal ((f : ℝ) / gs a L * (t * Θsum n)) ∧
    expTime C (initState (L := L) n c0 a f) (4 * t) ≤
      ENNReal.ofReal (2 * (4 * t : ℕ) * gs a L / f) := by
  obtain ⟨B, hB⟩ := schW_bounded (L := L) C hc0
  refine ⟨(sched_simulates_error_le (ctmSched C n c0 hc0) (4 * t) ha hf hL
    (initState_clockAt n c0 a f) ?_ ?_ B fun k _ w hW hV => hB k w hW hV).trans ?_,
    expTime_le (4 * t) ha hf hL (initState_clockAt n c0 a f)⟩
  · change schW C n c0 0 _
    unfold schW
    rw [if_pos rfl]
    exact initState_K1 n c0 a f
  · change schCl C n c0 0 _
    unfold schCl
    rw [if_pos rfl]
    exact initState_K1 n c0 a f
  · apply ENNReal.ofReal_le_ofReal
    have hG : (0 : ℝ) < gs a L := by linarith [one_le_gs (Nat.cast_nonneg (α := ℝ) a) L]
    exact mul_le_mul_of_nonneg_left (sum_schΘ_le n t) (by positivity)

end Ripple.sCRNUniversality.ClockedCTM
