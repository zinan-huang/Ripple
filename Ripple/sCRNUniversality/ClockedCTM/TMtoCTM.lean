/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.sCRNUniversality.ClockedCTM.Theorem
import Ripple.sCRNUniversality.TM.Basic

/-!
# Lemma A.9 and SCWB Theorem 3.2 for Turing machines (FIX3-SCWB-T32 §6, §7)

For a binary Turing machine `M : TM.Machine QM Bool` with blank `false` (it halts when `delta`
returns `none`; a halted machine stays put):

* **Cycle view (Lemma 6.1).**  `cyc Lc T` is the tape `T` read clockwise from the head on a
  cycle of length `Lc` (head, cells to the right, blanks, cells to the left, nearest last).
  `cyc_move`: a TM step that writes `z` and moves `d` acts on the cycle word as `cycStep`
  (`R`: `u₂ ⋯ u_L z`; `L`: `u_L z u₂ ⋯ u_{L-1}`), provided the new tape uses at most `Lc` cells.
* **The CTM `ctmOf M` (§6 table).**  States `F_m, F_s, Hd, Mk, Ms, C_m, C_s, Cs, Sh_m, Sh_s,
  Se`; the cycle configuration `(q, u)` is encoded by `encC q u = (F_m q, 1u₁ 0u₂ ⋯ 0u_L)`.
  Halting is read off `delta = none` at `Hd` (the paper reads it at `F_m` from a halting set;
  both return to the same canonical configuration after `2L` steps).
* **Lemma 6.2** (`ctm_step_R`, `ctm_step_L`, `ctm_step_halt`): from `encC q u` the CTM reaches
  `encC q' (cycStep u z d)` after exactly `2L + 2` (`R`) or `4L` (`L`) steps, and `encC q u`
  again after `2L` steps if `M` halts.
* **Lemma 6.3** (`ctm_tracks`): after `ctmTime M Lc c t ≤ 4 Lc t` CTM steps the CTM is in the
  encoding of the TM configuration after `t` steps, as long as the TM uses at most `Lc` cells.
* **Theorem 3.2′** (`scwb_theorem_3_2_of_Θsum`): the network `net (ctmOf M) L` is fixed by `M`
  and the clock length; for a cycle length `Lc ≥ 2` the count `#A* = f` is fixed; then for every
  `δ ∈ (0, 1]`, every TM configuration `c` and every `t ≥ 1` such that `M` uses at most `Lc`
  cells within `t` steps there is `a ≥ 2` such that with probability at least `1 - δ` the
  network simulates the CTM correctly up to tick `4 N`, `N = ctmTime M Lc c t`, and just before
  tick `4 N` encodes the TM configuration after `t` steps (`TmOK`); the expected time before
  tick `4 N` is at most `128 (3/2)^L Lc² t² Θsum (2 Lc - 3) / δ` (units `v/k`).
* **Paper form** (`scwb_theorem_3_2`): with `Θsum_le_pow`, for CTM tape length `s = 2 Lc` the
  expected time is at most `2880 (3/2)^L (v/k) s² t² (1 + (s-1) ln 3)/(3^s δ)
  ≤ 3168 (3/2)^L (v/k) s³ t²/(3^s δ)`.
-/

namespace Ripple.sCRNUniversality.ClockedCTM

open MeasureTheory Stochastic Stochastic.MassAction
open scoped ENNReal

/-! ### Cycle view of a tape -/

/-- Number of cells of a tape. -/
def tlen (T : TM.Tape Bool) : ℕ := T.left.length + 1 + T.right.length

/-- The tape read clockwise from the head on a cycle of length `Lc`. -/
def cyc (Lc : ℕ) (T : TM.Tape Bool) : List Bool :=
  T.head :: (T.right ++ List.replicate (Lc - tlen T) false ++ T.left.reverse)

theorem cyc_length {Lc : ℕ} {T : TM.Tape Bool} (h : tlen T ≤ Lc) : (cyc Lc T).length = Lc := by
  simp only [cyc, tlen, List.length_cons, List.length_append, List.length_replicate,
    List.length_reverse] at h ⊢
  omega

/-- One step on a cycle word: write `z` at the head and move. -/
def cycStep (u : List Bool) (z : Bool) : TM.Move → List Bool
  | .R => u.tail ++ [z]
  | .L => u.tail.getLastD false :: z :: u.tail.dropLast

theorem getLastD_snoc (l : List Bool) (a d : Bool) : (l ++ [a]).getLastD d = a := by
  induction l generalizing d with
  | nil => rfl
  | cons b l ih =>
    simp only [List.cons_append, List.getLastD_cons]
    exact ih b

/-- **Lemma 6.1 (cycle view).**  One TM step acts on the cycle word as `cycStep`, as long as
the new tape has at most `Lc` cells. -/
theorem cyc_move (Lc : ℕ) (T : TM.Tape Bool) (z : Bool) (d : TM.Move)
    (h : tlen ((T.write z).move false d) ≤ Lc) :
    cyc Lc ((T.write z).move false d) = cycStep (cyc Lc T) z d := by
  obtain ⟨l, hd, r⟩ := T
  cases d with
  | L =>
    cases l with
    | nil =>
      have hN : TM.Tape.move false .L (TM.Tape.write z ⟨[], hd, r⟩) = ⟨[], false, z :: r⟩ := rfl
      rw [hN] at h ⊢
      obtain ⟨k, hk1, hk2⟩ : ∃ k, Lc - tlen ⟨[], false, z :: r⟩ = k ∧
          Lc - tlen ⟨[], hd, r⟩ = k + 1 :=
        ⟨_, rfl, by simp only [tlen, List.length_cons, List.length_nil] at h ⊢ <;> omega⟩
      simp only [cyc, cycStep, hk1, hk2, List.reverse_nil, List.append_nil, List.tail_cons,
        List.replicate_succ', ← List.append_assoc, getLastD_snoc, List.dropLast_concat,
        List.cons_append]
    | cons a l =>
      have hN : TM.Tape.move false .L (TM.Tape.write z ⟨a :: l, hd, r⟩) = ⟨l, a, z :: r⟩ := rfl
      rw [hN] at h ⊢
      obtain ⟨k, hk1, hk2⟩ : ∃ k, Lc - tlen ⟨l, a, z :: r⟩ = k ∧
          Lc - tlen ⟨a :: l, hd, r⟩ = k :=
        ⟨_, rfl, by simp only [tlen, List.length_cons] <;> omega⟩
      simp only [cyc, cycStep, hk1, hk2, List.reverse_cons, List.tail_cons,
        ← List.append_assoc, getLastD_snoc, List.dropLast_concat, List.cons_append]
  | R =>
    cases r with
    | nil =>
      have hN : TM.Tape.move false .R (TM.Tape.write z ⟨l, hd, []⟩) = ⟨z :: l, false, []⟩ := rfl
      rw [hN] at h ⊢
      obtain ⟨k, hk1, hk2⟩ : ∃ k, Lc - tlen ⟨z :: l, false, []⟩ = k ∧
          Lc - tlen ⟨l, hd, []⟩ = k + 1 :=
        ⟨_, rfl, by simp only [tlen, List.length_cons, List.length_nil] at h ⊢ <;> omega⟩
      simp only [cyc, cycStep, hk1, hk2, List.replicate_succ, List.reverse_cons,
        List.tail_cons, List.nil_append, List.cons_append, List.append_assoc]
    | cons a r =>
      have hN : TM.Tape.move false .R (TM.Tape.write z ⟨l, hd, a :: r⟩) = ⟨z :: l, a, r⟩ := rfl
      rw [hN] at h ⊢
      obtain ⟨k, hk1, hk2⟩ : ∃ k, Lc - tlen ⟨z :: l, a, r⟩ = k ∧
          Lc - tlen ⟨l, hd, a :: r⟩ = k :=
        ⟨_, rfl, by simp only [tlen, List.length_cons] <;> omega⟩
      simp only [cyc, cycStep, hk1, hk2, List.reverse_cons, List.tail_cons, List.cons_append,
        List.append_assoc]

/-! ### The CTM of a TM -/

/-- States of the CTM `𝒞(M)`. -/
inductive CS (QM : Type)
  | fm (q : QM)
  | fs (q : QM)
  | hd (q : QM)
  | mk (q : QM)
  | ms (q : QM)
  | cm (q : QM)
  | cs0 (q : QM)
  | cs1 (q : QM)
  | shm (q : QM) (c : Bool)
  | shs (q : QM) (c : Bool)
  | se (q : QM) (c : Bool)
  deriving DecidableEq, Fintype

variable {QM : Type}

/-- **The CTM `𝒞(M)`** (FIX3-SCWB-T32 §6 table; halting is read off `delta = none` at `hd`). -/
def ctmOf (M : TM.Machine QM Bool) : CTM (CS QM) where
  next s a := match s, a with
    | .fm q, false => (.fs q, false)
    | .fm q, true => (.hd q, true)
    | .fs q, a => (.fm q, a)
    | .hd q, a =>
      match M.delta q a with
      | none => (.fm q, a)
      | some (z, .R, q') => (.mk q', z)
      | some (z, .L, q') => (.shm q' z, z)
    | .mk q, _ => (.ms q, true)
    | .ms q, a => (.cm q, a)
    | .cm q, false => (.cs0 q, false)
    | .cm q, true => (.cs1 q, false)
    | .cs0 q, a => (.cm q, a)
    | .cs1 q, a => (.fm q, a)
    | .shm q c, false => (.shs q c, false)
    | .shm q c, true => (.se q c, true)
    | .shs q c, a => (.shm q a, c)
    | .se q c, _ => (.fm q, c)

/-- Cells with marker `0`. -/
def pairs0 (v : List Bool) : List Bool := v.flatMap fun a => [false, a]

theorem pairs0_nil : pairs0 [] = [] := rfl

theorem pairs0_cons (a : Bool) (v : List Bool) : pairs0 (a :: v) = false :: a :: pairs0 v := rfl

theorem pairs0_append (v w : List Bool) : pairs0 (v ++ w) = pairs0 v ++ pairs0 w := by
  simp [pairs0, List.flatMap_append]

theorem pairs0_length (v : List Bool) : (pairs0 v).length = 2 * v.length := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    simp only [pairs0_cons, List.length_cons, ih]
    ring

/-- Canonical encoding of a cycle word: `1u₁ 0u₂ ⋯ 0u_L`. -/
def encT : List Bool → List Bool
  | [] => []
  | a :: v => true :: a :: pairs0 v

theorem encT_length (u : List Bool) : (encT u).length = 2 * u.length := by
  cases u with
  | nil => rfl
  | cons a v =>
    simp only [encT, List.length_cons, pairs0_length]
    ring

/-- Canonical CTM configuration of the cycle configuration `(q, u)`. -/
def encC (q : QM) (u : List Bool) : CS QM × List Bool := (.fm q, encT u)

theorem runT_add {Q : Type} (C : CTM Q) (c : Q × List Bool) (m n : ℕ) :
    C.runT c (m + n) = C.runT (C.runT c m) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← Nat.add_assoc, CTM.runT, ih, CTM.runT]

theorem runT_two {Q : Type} (C : CTM Q) (c : Q × List Bool) :
    C.runT c 2 = C.stepT (C.stepT c) := rfl

theorem runT_four {Q : Type} (C : CTM Q) (c : Q × List Bool) :
    C.runT c 4 = C.stepT (C.stepT (C.stepT (C.stepT c))) := rfl

variable (M : TM.Machine QM Bool)

/-- The copy loop `C_m / C_s`: `|v|` cells with marker `0` move to the back. -/
theorem run_cm (q : QM) (v rest : List Bool) :
    (ctmOf M).runT (.cm q, pairs0 v ++ rest) (2 * v.length) = (.cm q, rest ++ pairs0 v) := by
  induction v generalizing rest with
  | nil => simp [pairs0_nil, CTM.runT]
  | cons a v ih =>
    have h2 : (ctmOf M).runT (.cm q, pairs0 (a :: v) ++ rest) 2 =
        (.cm q, pairs0 v ++ (rest ++ [false, a])) := by
      rw [runT_two]
      simp [CTM.stepT, ctmOf, pairs0_cons]
    rw [show 2 * (a :: v).length = 2 + 2 * v.length by simp only [List.length_cons]; ring,
      runT_add, h2, ih]
    simp [pairs0_cons]

/-- The copy loop `F_m / F_s`. -/
theorem run_fm (q : QM) (v rest : List Bool) :
    (ctmOf M).runT (.fm q, pairs0 v ++ rest) (2 * v.length) = (.fm q, rest ++ pairs0 v) := by
  induction v generalizing rest with
  | nil => simp [pairs0_nil, CTM.runT]
  | cons a v ih =>
    have h2 : (ctmOf M).runT (.fm q, pairs0 (a :: v) ++ rest) 2 =
        (.fm q, pairs0 v ++ (rest ++ [false, a])) := by
      rw [runT_two]
      simp [CTM.stepT, ctmOf, pairs0_cons]
    rw [show 2 * (a :: v).length = 2 + 2 * v.length by simp only [List.length_cons]; ring,
      runT_add, h2, ih]
    simp [pairs0_cons]

/-- The shift loop `Sh_m / Sh_s` with carry `c`: symbols move back by one cell. -/
theorem run_shm (q : QM) (v : List Bool) (c : Bool) (rest : List Bool) :
    (ctmOf M).runT (.shm q c, pairs0 v ++ rest) (2 * v.length) =
      (.shm q (v.getLastD c), rest ++ pairs0 (c :: v).dropLast) := by
  induction v generalizing c rest with
  | nil => simp [pairs0_nil, CTM.runT]
  | cons a v ih =>
    have h2 : (ctmOf M).runT (.shm q c, pairs0 (a :: v) ++ rest) 2 =
        (.shm q a, pairs0 v ++ (rest ++ [false, c])) := by
      rw [runT_two]
      simp [CTM.stepT, ctmOf, pairs0_cons]
    rw [show 2 * (a :: v).length = 2 + 2 * v.length by simp only [List.length_cons]; ring,
      runT_add, h2, ih, List.getLastD_cons, List.dropLast_cons₂, pairs0_cons]
    simp

/-! ### Lemma 6.2 -/

/-- **Lemma 6.2, move right**: `2L + 2` CTM steps. -/
theorem ctm_step_R {q q' : QM} {u1 u2 : Bool} {rest : List Bool} {z : Bool}
    (hδ : M.delta q u1 = some (z, .R, q')) :
    (ctmOf M).runT (encC q (u1 :: u2 :: rest)) (2 * (u1 :: u2 :: rest).length + 2) =
      encC q' (cycStep (u1 :: u2 :: rest) z .R) := by
  have h4 : (ctmOf M).runT (encC q (u1 :: u2 :: rest)) 4 =
      (.cm q', pairs0 rest ++ [true, z, true, u2]) := by
    rw [runT_four]
    simp [encC, encT, pairs0_cons, CTM.stepT, ctmOf, hδ]
  have h6 : (ctmOf M).runT (encC q (u1 :: u2 :: rest)) (4 + 2 * rest.length) =
      (.cm q', [true, z, true, u2] ++ pairs0 rest) := by
    rw [runT_add, h4, run_cm]
  rw [show 2 * (u1 :: u2 :: rest).length + 2 = 4 + 2 * rest.length + 2 by
      simp only [List.length_cons]; ring,
    runT_add _ _ (4 + 2 * rest.length) 2, h6, runT_two]
  simp [CTM.stepT, ctmOf, encC, encT, cycStep, pairs0_cons, pairs0_append, pairs0_nil]

/-- **Lemma 6.2, move left**: `4L` CTM steps. -/
theorem ctm_step_L {q q' : QM} {u1 u2 : Bool} {rest : List Bool} {z : Bool}
    (hδ : M.delta q u1 = some (z, .L, q')) :
    (ctmOf M).runT (encC q (u1 :: u2 :: rest)) (4 * (u1 :: u2 :: rest).length) =
      encC q' (cycStep (u1 :: u2 :: rest) z .L) := by
  have h2 : (ctmOf M).runT (encC q (u1 :: u2 :: rest)) 2 =
      (.shm q' z, pairs0 (u2 :: rest) ++ [true, z]) := by
    rw [runT_two]
    simp [encC, encT, pairs0_cons, CTM.stepT, ctmOf, hδ]
  have h3 : (ctmOf M).runT (encC q (u1 :: u2 :: rest)) (2 + 2 * (u2 :: rest).length) =
      (.shm q' ((u2 :: rest).getLastD z), [true, z] ++ pairs0 (z :: u2 :: rest).dropLast) := by
    rw [runT_add, h2, run_shm]
  have h4 : (ctmOf M).runT (encC q (u1 :: u2 :: rest)) (2 + 2 * (u2 :: rest).length + 2) =
      (.fm q', pairs0 (z :: u2 :: rest).dropLast ++ [true, (u2 :: rest).getLastD z]) := by
    rw [runT_add, h3, runT_two]
    simp [CTM.stepT, ctmOf]
  rw [show 4 * (u1 :: u2 :: rest).length =
      2 + 2 * (u2 :: rest).length + 2 + 2 * ((z :: u2 :: rest).dropLast).length by
    simp only [List.length_cons, List.length_dropLast]; omega, runT_add, h4, run_fm]
  simp only [encC, encT, cycStep, List.tail_cons, List.getLastD_cons, List.dropLast_cons₂,
    pairs0_cons] <;> simp

/-- **Lemma 6.2, halted**: `2L` CTM steps back to the same canonical configuration. -/
theorem ctm_step_halt {q : QM} {u1 u2 : Bool} {rest : List Bool}
    (hδ : M.delta q u1 = none) :
    (ctmOf M).runT (encC q (u1 :: u2 :: rest)) (2 * (u1 :: u2 :: rest).length) =
      encC q (u1 :: u2 :: rest) := by
  have h2 : (ctmOf M).runT (encC q (u1 :: u2 :: rest)) 2 =
      (.fm q, pairs0 (u2 :: rest) ++ [true, u1]) := by
    rw [runT_two]
    simp [encC, encT, pairs0_cons, CTM.stepT, ctmOf, hδ]
  rw [show 2 * (u1 :: u2 :: rest).length = 2 + 2 * (u2 :: rest).length by
      simp only [List.length_cons]; ring, runT_add, h2, run_fm]
  simp [encC, encT]

/-! ### Lemma 6.3 -/

/-- The TM configuration after `t` steps (constant after halting). -/
def tmRun (c : TM.Cfg QM Bool) : ℕ → TM.Cfg QM Bool
  | 0 => c
  | t + 1 => (M.step? (tmRun c t)).getD (tmRun c t)

/-- CTM steps for one TM step on a cycle of length `Lc`. -/
def stepCost (Lc : ℕ) (c : TM.Cfg QM Bool) : ℕ :=
  match M.delta c.state c.tape.head with
  | none => 2 * Lc
  | some (_, .R, _) => 2 * Lc + 2
  | some (_, .L, _) => 4 * Lc

/-- CTM steps for `t` TM steps. -/
def ctmTime (Lc : ℕ) (c : TM.Cfg QM Bool) : ℕ → ℕ
  | 0 => 0
  | t + 1 => ctmTime Lc c t + stepCost M Lc (tmRun M c t)

theorem stepCost_le {Lc : ℕ} (hLc : 2 ≤ Lc) (c : TM.Cfg QM Bool) :
    stepCost M Lc c ≤ 4 * Lc := by
  unfold stepCost
  split <;> omega

theorem four_le_stepCost {Lc : ℕ} (hLc : 2 ≤ Lc) (c : TM.Cfg QM Bool) :
    4 ≤ stepCost M Lc c := by
  unfold stepCost
  split <;> omega

theorem ctmTime_le {Lc : ℕ} (hLc : 2 ≤ Lc) (c : TM.Cfg QM Bool) (t : ℕ) :
    ctmTime M Lc c t ≤ 4 * Lc * t := by
  induction t with
  | zero => simp [ctmTime]
  | succ t ih =>
    have h1 := stepCost_le M hLc (tmRun M c t)
    have h2 : 4 * Lc * (t + 1) = 4 * Lc * t + 4 * Lc := by ring
    simp only [ctmTime]
    omega

theorem four_mul_le_ctmTime {Lc : ℕ} (hLc : 2 ≤ Lc) (c : TM.Cfg QM Bool) (t : ℕ) :
    4 * t ≤ ctmTime M Lc c t := by
  induction t with
  | zero => simp [ctmTime]
  | succ t ih =>
    have h1 := four_le_stepCost M hLc (tmRun M c t)
    simp only [ctmTime]
    omega

/-- **Lemma 6.3.**  While the TM uses at most `Lc` cells, the CTM run from the canonical
encoding tracks the TM run: after `ctmTime M Lc c t` CTM steps it is in the canonical encoding
of the TM configuration after `t` steps. -/
theorem ctm_tracks (hb : M.blank = false) {Lc : ℕ} (hLc : 2 ≤ Lc) (c : TM.Cfg QM Bool)
    (t : ℕ) (hsp : ∀ t' ≤ t, tlen (tmRun M c t').tape ≤ Lc) :
    (ctmOf M).runT (encC c.state (cyc Lc c.tape)) (ctmTime M Lc c t) =
      encC (tmRun M c t).state (cyc Lc (tmRun M c t).tape) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [ctmTime, runT_add, ih (fun t' ht' => hsp t' (by omega))]
    have hlen := cyc_length (hsp t (by omega))
    have hsp1 := hsp (t + 1) le_rfl
    rw [show tmRun M c (t + 1) = (M.step? (tmRun M c t)).getD (tmRun M c t) from rfl] at hsp1 ⊢
    generalize tmRun M c t = ct at hlen hsp1 ⊢
    obtain ⟨q, T⟩ := ct
    change (cyc Lc T).length = Lc at hlen
    obtain ⟨u2, rest, hu⟩ : ∃ u2 rest, cyc Lc T = T.head :: u2 :: rest := by
      have hlen' := hlen
      unfold cyc at hlen' ⊢
      generalize T.right ++ List.replicate (Lc - tlen T) false ++ T.left.reverse = X at hlen' ⊢
      cases X with
      | nil => simp only [List.length_cons, List.length_nil] at hlen'; omega
      | cons u2 rest => exact ⟨u2, rest, rfl⟩
    have hL2 : Lc = (T.head :: u2 :: rest).length := by rw [← hu, hlen]
    simp only [stepCost, TM.Machine.step?, TM.Tape.read] at hsp1 ⊢
    rcases hδ : M.delta q T.head with _ | ⟨z, _ | _, q'⟩
    · simp only [Option.getD_none] at hsp1 ⊢
      rw [hu, hL2]
      exact ctm_step_halt M hδ
    · simp only [hδ, Option.getD_some] at hsp1 ⊢
      rw [hb] at hsp1 ⊢
      rw [cyc_move Lc T z .L hsp1, hu, hL2]
      exact ctm_step_L M hδ
    · simp only [hδ, Option.getD_some] at hsp1 ⊢
      rw [hb] at hsp1 ⊢
      rw [cyc_move Lc T z .R hsp1, hu, hL2]
      exact ctm_step_R M hδ

/-! ### Theorem 3.2 for Turing machines -/

section Network

variable {Q : Type} [Fintype Q] [DecidableEq Q] {L : ℕ}

/-- Correct simulation of the CTM run from `c0` up to tick `N`: `SimOK` without the length
proof (`simOK_iff`). -/
def CtmOK (C : CTM Q) (n : ℕ) (c0 : Q × List Bool) (N : ℕ) (z0 : State (Sp Q L))
    (ω : ℕ → Option (Rx Q L)) : Prop :=
  ∀ k, ω (k + 1) = some .tick → ticks k ω < N →
    schCl C n c0 (ticks k ω) (rest (traj C z0 k ω))

theorem simOK_iff (C : CTM Q) {n : ℕ} {c0 : Q × List Bool} (hc0 : c0.2.length = n + 3)
    (N : ℕ) (z0 : State (Sp Q L)) (ω : ℕ → Option (Rx Q L)) :
    SimOK (ctmSched C n c0 hc0) N z0 ω ↔ CtmOK C n c0 N z0 ω := Iff.rfl

theorem expTime_mono (C : CTM Q) (z0 : State (Sp Q L)) {N N' : ℕ} (h : N ≤ N') :
    expTime C z0 N ≤ expTime C z0 N' := by
  unfold expTime
  refine lintegral_mono fun ω => ENNReal.tsum_le_tsum fun n => ?_
  by_cases h1 : ticks n ω < N
  · rw [if_pos h1, if_pos (lt_of_lt_of_le h1 h)]
  · rw [if_neg h1]
    simp

end Network

variable [Fintype QM] [DecidableEq QM] {L : ℕ}

/-- **Success at the TM level.**  The network simulates the CTM `ctmOf M` from the canonical
encoding of `c` correctly up to tick `4 N`, `N = ctmTime M Lc c t`, and just before tick `4 N`
it is in the class `𝒦_4(p, b; w)` with `w` the canonical encoding of the TM tape after `t`
steps and `p, b` such that the CTM state after the step is `F_m` of the TM state after `t`
steps. -/
def TmOK (Lc : ℕ) (c : TM.Cfg QM Bool) (t : ℕ) (z0 : State (Sp (CS QM) L))
    (ω : ℕ → Option (Rx (CS QM) L)) : Prop :=
  CtmOK (ctmOf M) (2 * Lc - 3) (encC c.state (cyc Lc c.tape)) (4 * ctmTime M Lc c t) z0 ω ∧
    ∀ k, ω (k + 1) = some .tick → ticks k ω + 1 = 4 * ctmTime M Lc c t →
      ∃ (p : CS QM) (b : Bool), ((ctmOf M).next p b).1 = .fm (tmRun M c t).state ∧
        K4 (9 * 3 ^ (2 * Lc - 3)) (20 * 3 ^ (2 * Lc - 3)) p b
          (tval (encT (cyc Lc (tmRun M c t).tape))) (rest (traj (ctmOf M) z0 k ω))

/-- Correct CTM simulation up to tick `4 T`, `T ≥ ctmTime M Lc c t`, gives `TmOK`. -/
theorem tmOK_of_simOK (hb : M.blank = false) {Lc : ℕ} (hLc : 2 ≤ Lc) (c : TM.Cfg QM Bool)
    {t : ℕ} (ht : 1 ≤ t) (hsp : ∀ t' ≤ t, tlen (tmRun M c t').tape ≤ Lc) {T : ℕ}
    (hT : ctmTime M Lc c t ≤ T) (z0 : State (Sp (CS QM) L)) (ω : ℕ → Option (Rx (CS QM) L))
    (hc0 : (encC c.state (cyc Lc c.tape)).2.length = 2 * Lc - 3 + 3)
    (h : SimOK (ctmSched (ctmOf M) (2 * Lc - 3) (encC c.state (cyc Lc c.tape)) hc0) (4 * T) z0
      ω) :
    TmOK M Lc c t z0 ω := by
  unfold SimOK at h
  unfold TmOK CtmOK
  refine ⟨fun k hk hlt => h k hk (by omega), fun k hk hkN => ?_⟩
  have h1 : schCl (ctmOf M) (2 * Lc - 3) (encC c.state (cyc Lc c.tape)) (ticks k ω)
      (rest (traj (ctmOf M) z0 k ω)) := h k hk (by omega)
  obtain ⟨N', hN'⟩ : ∃ N', ctmTime M Lc c t = N' + 1 :=
    ⟨ctmTime M Lc c t - 1, by have := four_mul_le_ctmTime M hLc c t; omega⟩
  have htk : ticks k ω = 4 * N' + 3 := by omega
  rw [htk, schCl_three] at h1
  have htr := ctm_tracks M hb hLc c t hsp
  rw [hN'] at htr
  refine ⟨((ctmOf M).runT (encC c.state (cyc Lc c.tape)) N').1,
    ((ctmOf M).runT (encC c.state (cyc Lc c.tape)) N').2.headD false,
    congrArg Prod.fst htr, ?_⟩
  rw [htr] at h1
  exact h1

/-- **SCWB Theorem 3.2 for Turing machines, `Θsum` form** (the lemma `scwb_theorem_3_2` is
derived from).

The network `net (ctmOf M) L` depends only on the TM `M` and the clock length; for a cycle
length `Lc ≥ 2` the count `#A* = f` is fixed; then for every `δ ∈ (0, 1]`, every TM
configuration `c` and every `t ≥ 1` such that `M` uses at most `Lc` cells within `t` steps,
there is `a ≥ 2` (`#A = a f`) such that, from the initial state with memory `tval` of the
canonical encoding of `c`:

* with probability at least `1 - δ`, the CTM simulation is correct up to tick `4 N`,
  `N = ctmTime M Lc c t ≤ 4 Lc t`, and just before tick `4 N` the state encodes the TM
  configuration after `t` steps (`TmOK`);
* the expected time before tick `4 N` is at most `128 (3/2)^L Lc² t² Θsum (2 Lc - 3) / δ`
  (units `v/k`). -/
theorem scwb_theorem_3_2_of_Θsum (hb : M.blank = false) (L : ℕ) (hL : 1 ≤ L) (Lc : ℕ)
    (hLc : 2 ≤ Lc) :
    ∃ f : ℕ, 1 ≤ f ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ (c : TM.Cfg QM Bool) (t : ℕ), 1 ≤ t →
      (∀ t' ≤ t, tlen (tmRun M c t').tape ≤ Lc) → ∃ a : ℕ, 2 ≤ a ∧
        rawLaw (net (ctmOf M) L) (net_hasPositiveRates (ctmOf M) L)
            (initState (2 * Lc - 3) (encC c.state (cyc Lc c.tape)) a f)
            {ω | ¬ TmOK M Lc c t (initState (2 * Lc - 3) (encC c.state (cyc Lc c.tape)) a f) ω} ≤
          ENNReal.ofReal δ ∧
        ∀ v k : ℝ, 0 < v → 0 < k →
          ENNReal.ofReal (v / k) * expTime (ctmOf M)
              (initState (L := L) (2 * Lc - 3) (encC c.state (cyc Lc c.tape)) a f)
              (4 * ctmTime M Lc c t) ≤
            ENNReal.ofReal
              (128 * (3 / 2) ^ L * v * Lc ^ 2 * t ^ 2 * Θsum (2 * Lc - 3) / (k * δ)) := by
  obtain ⟨f, hf, hmain⟩ := scwb_theorem_3_2_ctm (ctmOf M) L hL (2 * Lc - 3)
  refine ⟨f, hf, fun δ hδ hδ1 c t ht hsp => ?_⟩
  have hc0 : (encC c.state (cyc Lc c.tape)).2.length = 2 * Lc - 3 + 3 := by
    show (encT (cyc Lc c.tape)).length = _
    rw [encT_length, cyc_length (T := c.tape) (hsp 0 (Nat.zero_le _))]
    omega
  have hT : 1 ≤ 4 * Lc * t := Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
  obtain ⟨a, ha, herr, htime⟩ := hmain δ hδ hδ1 _ hc0 (4 * Lc * t) hT
  refine ⟨a, ha, ?_, fun v k hv hk => ?_⟩
  · refine le_trans (measure_mono ?_) herr
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    intro hs
    exact hω <| tmOK_of_simOK M hb hLc c ht hsp (ctmTime_le M hLc c t) _ ω hc0 hs
  · refine (mul_le_mul_left' (expTime_mono (ctmOf M) _
      (Nat.mul_le_mul_left 4 (ctmTime_le M hLc c t))) _).trans ((htime v k hv hk).trans_eq ?_)
    congr 1
    push_cast
    ring

/-- **SCWB Theorem 3.2 for Turing machines** (repaired network, FIX3-SCWB-T32 Theorem 3.2′,
paper form with explicit constants).

The network `net (ctmOf M) L` (the repaired network `N♯(𝒞(M), L + 1)`) depends only on the TM
`M` and the clock length; for a cycle length `Lc ≥ 2`, i.e. CTM tape length `s = 2 Lc`, the
count `#A* = f` is fixed; then for every `δ ∈ (0, 1]`, every TM configuration `c` and every
`t ≥ 1` such that `M` uses at most `Lc` cells within `t` steps, there is `a ≥ 2` (`#A = a f`)
such that, from the initial state with memory `tval` of the canonical encoding of `c`:

* with probability at least `1 - δ`, the CTM simulation is correct up to tick `4 N`,
  `N = ctmTime M Lc c t ≤ 2 s t`, and just before tick `4 N` the state encodes the TM
  configuration after `t` steps (`TmOK`);
* the expected time before tick `4 N` is at most
  `2880 (3/2)^L (v/k) s² t² (1 + (s - 1) ln 3) / (3^s δ)`, hence at most
  `3168 (3/2)^L (v/k) s³ t² / (3^s δ)` (the constant `3168 = 2880 · 1.1` comes from
  `Θsum_le_log`, `K = 30`). For comparison: the repaired paper analysis
  `docs/audit/FIX3-SCWB-T32.md` obtains `2746 (3/2)^{l-1} (v/k) s³ t_tm²/(3^s δ)` with `l = L + 1`
  (`K = 26`); SCWB's printed Theorem 3.2 states only
  `O(v (s_tm+Δ)^{7/2} t_tm^{5/2}/(k 3^{2 s_tm+Δ} δ^{3/2}))`.

`TmOK` is a safety predicate (no wrong observed tick before tick `4 N`); it does not assert that
tick `4 N` is reached. -/
theorem scwb_theorem_3_2 (hb : M.blank = false) (L : ℕ) (hL : 1 ≤ L) (Lc : ℕ) (hLc : 2 ≤ Lc) :
    ∃ f : ℕ, 1 ≤ f ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ (c : TM.Cfg QM Bool) (t : ℕ), 1 ≤ t →
      (∀ t' ≤ t, tlen (tmRun M c t').tape ≤ Lc) → ∃ a : ℕ, 2 ≤ a ∧
        rawLaw (net (ctmOf M) L) (net_hasPositiveRates (ctmOf M) L)
            (initState (2 * Lc - 3) (encC c.state (cyc Lc c.tape)) a f)
            {ω | ¬ TmOK M Lc c t (initState (2 * Lc - 3) (encC c.state (cyc Lc c.tape)) a f) ω} ≤
          ENNReal.ofReal δ ∧
        ∀ v k : ℝ, 0 < v → 0 < k →
          ENNReal.ofReal (v / k) * expTime (ctmOf M)
              (initState (L := L) (2 * Lc - 3) (encC c.state (cyc Lc c.tape)) a f)
              (4 * ctmTime M Lc c t) ≤
            ENNReal.ofReal (2880 * (3 / 2) ^ L * v * ((2 * Lc : ℕ) : ℝ) ^ 2 * (t : ℝ) ^ 2 *
              (1 + (((2 * Lc : ℕ) : ℝ) - 1) * Real.log 3) / (k * 3 ^ (2 * Lc) * δ)) ∧
          ENNReal.ofReal (v / k) * expTime (ctmOf M)
              (initState (L := L) (2 * Lc - 3) (encC c.state (cyc Lc c.tape)) a f)
              (4 * ctmTime M Lc c t) ≤
            ENNReal.ofReal (3168 * (3 / 2) ^ L * v * ((2 * Lc : ℕ) : ℝ) ^ 3 * (t : ℝ) ^ 2 /
              (k * 3 ^ (2 * Lc) * δ)) := by
  obtain ⟨f, hf, hmain⟩ := scwb_theorem_3_2_of_Θsum M hb L hL Lc hLc
  refine ⟨f, hf, fun δ hδ hδ1 c t ht hsp => ?_⟩
  obtain ⟨a, ha, herr, htime⟩ := hmain δ hδ hδ1 c t ht hsp
  refine ⟨a, ha, herr, fun v k hv hk => ?_⟩
  have hk0 : k ≠ 0 := hk.ne'
  have hδ0 : δ ≠ 0 := hδ.ne'
  have key : 128 * (3 / 2) ^ L * v * (Lc : ℝ) ^ 2 * (t : ℝ) ^ 2 * Θsum (2 * Lc - 3) / (k * δ) ≤
      2880 * (3 / 2) ^ L * v * ((2 * Lc : ℕ) : ℝ) ^ 2 * (t : ℝ) ^ 2 *
        (1 + (((2 * Lc : ℕ) : ℝ) - 1) * Real.log 3) / (k * 3 ^ (2 * Lc) * δ) := by
    have hP : 0 ≤ 128 * (3 / 2) ^ L * v * (Lc : ℝ) ^ 2 * (t : ℝ) ^ 2 / (k * δ) := by positivity
    calc 128 * (3 / 2) ^ L * v * (Lc : ℝ) ^ 2 * (t : ℝ) ^ 2 * Θsum (2 * Lc - 3) / (k * δ)
        = (128 * (3 / 2) ^ L * v * (Lc : ℝ) ^ 2 * (t : ℝ) ^ 2 / (k * δ)) *
            Θsum (2 * Lc - 3) := by ring
      _ ≤ (128 * (3 / 2) ^ L * v * (Lc : ℝ) ^ 2 * (t : ℝ) ^ 2 / (k * δ)) *
            (90 * (1 + (((2 * Lc - 3 : ℕ) : ℝ) + 2) * Real.log 3) / 3 ^ (2 * Lc - 3 + 3)) :=
          mul_le_mul_of_nonneg_left (Θsum_le_pow _) hP
      _ = 2880 * (3 / 2) ^ L * v * ((2 * Lc : ℕ) : ℝ) ^ 2 * (t : ℝ) ^ 2 *
            (1 + (((2 * Lc : ℕ) : ℝ) - 1) * Real.log 3) / (k * 3 ^ (2 * Lc) * δ) := by
          rw [show 2 * Lc - 3 + 3 = 2 * Lc by omega, Nat.cast_sub (show 3 ≤ 2 * Lc by omega)]
          push_cast
          field_simp
          ring
  have hRb : 2880 * (3 / 2) ^ L * v * ((2 * Lc : ℕ) : ℝ) ^ 2 * (t : ℝ) ^ 2 *
        (1 + (((2 * Lc : ℕ) : ℝ) - 1) * Real.log 3) / (k * 3 ^ (2 * Lc) * δ) ≤
      3168 * (3 / 2) ^ L * v * ((2 * Lc : ℕ) : ℝ) ^ 3 * (t : ℝ) ^ 2 / (k * 3 ^ (2 * Lc) * δ) := by
    have hl3 := log_three_le
    have hs : (4 : ℝ) ≤ ((2 * Lc : ℕ) : ℝ) := by
      have : (2 : ℝ) ≤ Lc := by exact_mod_cast hLc
      push_cast
      linarith
    have hQ : 0 ≤ 2880 * (3 / 2) ^ L * v * (t : ℝ) ^ 2 / (k * 3 ^ (2 * Lc) * δ) := by positivity
    generalize ((2 * Lc : ℕ) : ℝ) = s at hs ⊢
    have hm : (s - 1) * Real.log 3 ≤ (s - 1) * 1.0989 :=
      mul_le_mul_of_nonneg_left hl3 (by linarith)
    have hin : 1 + (s - 1) * Real.log 3 ≤ 11 / 10 * s := by linarith
    calc 2880 * (3 / 2) ^ L * v * s ^ 2 * (t : ℝ) ^ 2 * (1 + (s - 1) * Real.log 3) /
          (k * 3 ^ (2 * Lc) * δ)
        = (2880 * (3 / 2) ^ L * v * (t : ℝ) ^ 2 / (k * 3 ^ (2 * Lc) * δ)) *
            (s ^ 2 * (1 + (s - 1) * Real.log 3)) := by ring
      _ ≤ (2880 * (3 / 2) ^ L * v * (t : ℝ) ^ 2 / (k * 3 ^ (2 * Lc) * δ)) *
            (s ^ 2 * (11 / 10 * s)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hin (sq_nonneg s)) hQ
      _ = 3168 * (3 / 2) ^ L * v * s ^ 3 * (t : ℝ) ^ 2 / (k * 3 ^ (2 * Lc) * δ) := by ring
  have hA := (htime v k hv hk).trans (ENNReal.ofReal_le_ofReal key)
  exact ⟨hA, hA.trans (ENNReal.ofReal_le_ofReal hRb)⟩

end Ripple.sCRNUniversality.ClockedCTM
