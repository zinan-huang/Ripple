/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Ripple.sCRNUniversality.ClockedCTM.Window41

/-!
# Window `𝒦_3 + I → 𝒦_4` (FIX3-SCWB-T32 Lemma 4.4, Lemma 5.4)

From `𝒦_3(q, w) + I`, with `b = w_1` and `(q', z) = next q b`:
(a) `I + S_{q,3} → R_q`; (b) `R_q + T → U_{q,0} + T` if `b = 0`, `R_q + M → U_{q,1} + M` if
`b = 1`; (c) `S_{q,3} + U_{q,b} → 2 U_{q,b}` together with the `U_{q,b}`-catalysed memory
reactions, `T + M → T* + M*` and the `K`-reactions.  During (c) the quantity
`Ψ = 3(#M + #M*) + #M† - (#K_1 + 2#K_2) - 3(b+1)#D + (z+1)#B` is conserved (`MemC`), and the
window ends in `𝒦_4(q, b; w')` with `#M† = x' = val w'`.

Potential (replaces the per-molecule maxima of Lemma 5.4 by a logarithmic Lyapunov function):
`V34 w = [I = 1]/m + [I = 1 ∨ R_q = 1]/g + aut m (max #U_{q,b} 1)
  + (4/m) log(1 + Φ₁) + (4/x') log(1 + Φ₂)`,
`Φ₁ = #D + #B + 2#T + #T* + #M + 2#M*`, `Φ₂ = #K_1 + 2#K_2 + 6#D`.  Every memory reaction
weakly decreases `Φ₁` and `Φ₂`; once `U_{q,b} = m`, `Φ₁` decreases at rate `≥ (m/2) Φ₁`, and
when `Φ₁ = 0`, `Φ₂` decreases at rate `≥ (x'/2) Φ₂` (then `#M† ≥ x'`).  Since
`log(1+a') - log(1+a) ≤ (a'-a)/(1+a)`, the drift of `V34` is at most `-1` off the target.
-/

namespace Ripple.sCRNUniversality.ClockedCTM

open Stochastic Stochastic.MassAction

variable {Q : Type} [Fintype Q] [DecidableEq Q] {L : ℕ} (C : CTM Q)

/-- Digit of a bit: `1` for `false`, `2` for `true`. -/
def bw (b : Bool) : ℕ := if b then 2 else 1

/-- Memory of `𝒦_3` for the read bit `b`, with threshold margin `g`. -/
def K3mem (m T0 g : ℕ) (b : Bool) (x : ℕ) (v : Mem → ℕ) : Prop :=
  MemA m T0 x v ∧ MemReset v ∧ (b = false → v .m = 0 ∧ g ≤ v .t) ∧ (b = true → v .t = 0 ∧ g ≤ v .m)

/-- Memory during stage (c): conservation of `Ψ` and of the `T`, `D`, `B` totals. -/
def MemC (m T0 : ℕ) (b z : Bool) (x' : ℕ) (v : Mem → ℕ) : Prop :=
  3 * (v .m + v .ms) + v .md + bw z * v .b = x' + v .k1 + 2 * v .k2 + 3 * bw b * v .d ∧
    v .t + v .ts + v .td = T0 ∧ v .d + v .ds = m ∧ v .b + v .bs = 1

/-- States of the window `𝒦_3(q, w) + I → 𝒦_4(q, b; w')`: stages (a), (b), (c). -/
def Win34 (m T0 g : ℕ) (q : Q) (b : Bool) (x x' : ℕ) (w : State (Sp Q L)) : Prop :=
  (OnlyState [.s3 q, .i] w ∧ w .i = 1 ∧ w (.s3 q) = m ∧ K3mem m T0 g b x (memv w)) ∨
  (OnlyState [.s3 q, .rq q] w ∧ w (.rq q) = 1 ∧ w (.s3 q) + 1 = m ∧ K3mem m T0 g b x (memv w)) ∨
  (OnlyState [.s3 q, .u q b] w ∧ w (.s3 q) + w (.u q b) = m ∧ 1 ≤ w (.u q b) ∧
    MemC m T0 b (C.next q b).2 x' (memv w))

/-- `Φ₁ = #D + #B + 2#T + #T* + #M + 2#M*`. -/
def phi1 (w : State (Sp Q L)) : ℕ :=
  w (.mem .d) + w (.mem .b) + 2 * w (.mem .t) + w (.mem .ts) + w (.mem .m) + 2 * w (.mem .ms)

/-- `Φ₂ = #K_1 + 2#K_2 + 6#D`. -/
def phi2 (w : State (Sp Q L)) : ℕ := w (.mem .k1) + 2 * w (.mem .k2) + 6 * w (.mem .d)

/-- Potential of the window `𝒦_3 + I → 𝒦_4`. -/
noncomputable def V34 (m g x' : ℕ) (q : Q) (b : Bool) (w : State (Sp Q L)) : ℝ :=
  (if w .i = 1 then 1 / (m : ℝ) else 0) + (if w .i = 1 ∨ w (.rq q) = 1 then 1 / (g : ℝ) else 0) +
    aut m (max (w (.u q b)) 1) + 4 / (m : ℝ) * Real.log (1 + phi1 w) +
    4 / (x' : ℝ) * Real.log (1 + phi2 w)

theorem log_one_add_sub_le {a a' : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a') :
    Real.log (1 + a') - Real.log (1 + a) ≤ (a' - a) / (1 + a) := by
  rw [← Real.log_div (by linarith) (by linarith)]
  have h := Real.log_le_sub_one_of_pos (show 0 < (1 + a') / (1 + a) by positivity)
  have : (1 + a') / (1 + a) - 1 = (a' - a) / (1 + a) := by field_simp; ring
  linarith

/-- Comparison of `V34` at two states that agree on `I`, `R_q`, `U_{q,b}`. -/
theorem V34_sub_le {m g x' : ℕ} (hm : 0 < m) (hx' : 0 < x') {q : Q} {b : Bool}
    {w w' : State (Sp Q L)} (hi : w' .i = w .i) (hr : w' (.rq q) = w (.rq q))
    (hu : w' (.u q b) = w (.u q b)) (h1 : phi1 w' ≤ phi1 w) (h2 : phi2 w' ≤ phi2 w) :
    V34 m g x' q b w' - V34 m g x' q b w ≤
        4 / (m : ℝ) * (((phi1 w' : ℝ) - phi1 w) / (1 + phi1 w)) ∧
      V34 m g x' q b w' - V34 m g x' q b w ≤
        4 / (x' : ℝ) * (((phi2 w' : ℝ) - phi2 w) / (1 + phi2 w)) ∧
      V34 m g x' q b w' ≤ V34 m g x' q b w := by
  have l1 := log_one_add_sub_le (Nat.cast_nonneg (phi1 w)) (Nat.cast_nonneg (phi1 w'))
  have l2 := log_one_add_sub_le (Nat.cast_nonneg (phi2 w)) (Nat.cast_nonneg (phi2 w'))
  have m1 : Real.log (1 + phi1 w') ≤ Real.log (1 + phi1 w) :=
    Real.log_le_log (by positivity) (by have : (phi1 w' : ℝ) ≤ phi1 w := by exact_mod_cast h1
                                        linarith)
  have m2 : Real.log (1 + phi2 w') ≤ Real.log (1 + phi2 w) :=
    Real.log_le_log (by positivity) (by have : (phi2 w' : ℝ) ≤ phi2 w := by exact_mod_cast h2
                                        linarith)
  have e : V34 m g x' q b w' - V34 m g x' q b w =
      4 / (m : ℝ) * (Real.log (1 + phi1 w') - Real.log (1 + phi1 w)) +
        4 / (x' : ℝ) * (Real.log (1 + phi2 w') - Real.log (1 + phi2 w)) := by
    simp only [V34, hi, hr, hu]; ring
  have hm' : (0 : ℝ) ≤ 4 / (m : ℝ) := by positivity
  have hx'' : (0 : ℝ) ≤ 4 / (x' : ℝ) := by positivity
  have p1 : 4 / (m : ℝ) * (Real.log (1 + phi1 w') - Real.log (1 + phi1 w)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hm' (by linarith)
  have p2 : 4 / (x' : ℝ) * (Real.log (1 + phi2 w') - Real.log (1 + phi2 w)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hx'' (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · rw [e]
    have := mul_le_mul_of_nonneg_left l1 hm'
    linarith
  · rw [e]
    have := mul_le_mul_of_nonneg_left l2 hx''
    linarith
  · linarith

/-- `OnlyState` of the fired state from a pointwise description. -/
theorem OnlyState.fire' {l : List (Sp Q L)} {w' : State (Sp Q L)}
    (h : ∀ s : Sp Q L, s.IsState → s ∉ l → w' s = 0) : OnlyState l w' := h

set_option hygiene false in
/-- Close a case in which some reactant is a state species that the window keeps at `0`. -/
local macro "kill_state" : tactic => `(tactic| first
  | exact absurd trivial hi
  | (exfalso; simp only [src1, src2] at hr; simp_all [Sp.IsState])
  | (exfalso; simp only [src1, src2] at hr; omega))

/-- Stage (a): only `I + S_{q,3} → R_q` is enabled. -/
theorem win34a_enabled {m T0 g x : ℕ} {q : Q} {b : Bool} {w : State (Sp Q L)}
    (hO : OnlyState [.s3 q, .i] w) (hM : K3mem m T0 g b x (memv w))
    (i : Rx Q L) (hi : ¬ i.IsClock) (hr : rate C i w ≠ 0) : i = .adv3 q := by
  rw [rate_ne_zero_iff] at hr
  unfold OnlyState at hO
  obtain ⟨⟨-, -, -, -, -, hk1, hk2⟩, ⟨hmd, htd, hds, hbs⟩, hb0, hb1⟩ := hM
  simp only [memv_apply] at hk1 hk2 hmd htd hds hbs hb0 hb1
  have hTM : w (.mem .t) = 0 ∨ w (.mem .m) = 0 := by
    cases b
    · exact Or.inr (hb0 rfl).1
    · exact Or.inl (hb1 rfl).1
  cases i with
  | adv3 q' =>
    by_cases hq : q' = q
    · rw [hq]
    · exfalso; simp only [src1, src2] at hr; exact hr.2 (hO _ trivial (by simp [hq]))
  | auto34 q' b' =>
    exfalso; simp only [src1, src2] at hr; exact hr.2 (hO _ trivial (by simp))
  | pair => exfalso; simp only [src1, src2] at hr; omega
  | _ => kill_state

/-- Stage (b): only `R_q + T → U_{q,0} + T` (if `b = 0`) or `R_q + M → U_{q,1} + M` (if
`b = 1`) is enabled. -/
theorem win34b_enabled {m T0 g x : ℕ} {q : Q} {b : Bool} {w : State (Sp Q L)}
    (hO : OnlyState [.s3 q, .rq q] w) (hM : K3mem m T0 g b x (memv w))
    (i : Rx Q L) (hi : ¬ i.IsClock) (hr : rate C i w ≠ 0) :
    (i = .rt q ∧ b = false) ∨ (i = .rm q ∧ b = true) := by
  rw [rate_ne_zero_iff] at hr
  unfold OnlyState at hO
  obtain ⟨⟨-, -, -, -, -, hk1, hk2⟩, ⟨hmd, htd, hds, hbs⟩, hb0, hb1⟩ := hM
  simp only [memv_apply] at hk1 hk2 hmd htd hds hbs hb0 hb1
  have hTM : w (.mem .t) = 0 ∨ w (.mem .m) = 0 := by
    cases b
    · exact Or.inr (hb0 rfl).1
    · exact Or.inl (hb1 rfl).1
  cases i with
  | rt q' =>
    by_cases hq : q' = q
    · subst hq
      left; refine ⟨rfl, ?_⟩
      cases b
      · rfl
      · exfalso; simp only [src1, src2] at hr; exact hr.2 (hb1 rfl).1
    · exfalso; simp only [src1, src2] at hr; exact hr.1 (hO _ trivial (by simp [hq]))
  | rm q' =>
    by_cases hq : q' = q
    · subst hq
      right; refine ⟨rfl, ?_⟩
      cases b
      · exfalso; simp only [src1, src2] at hr; exact hr.2 (hb0 rfl).1
      · rfl
    · exfalso; simp only [src1, src2] at hr; exact hr.1 (hO _ trivial (by simp [hq]))
  | adv3 q' => exfalso; simp only [src1, src2] at hr; exact hr.1 (hO _ trivial (by simp))
  | auto34 q' b' =>
    exfalso; simp only [src1, src2] at hr; exact hr.2 (hO _ trivial (by simp))
  | pair => exfalso; simp only [src1, src2] at hr; omega
  | _ => kill_state

/-- Stage (c): only the autocatalysis, the `U_{q,b}`-catalysed reactions, the comparison and
the `K`-reactions are enabled. -/
theorem win34c_enabled {q : Q} {b : Bool} {w : State (Sp Q L)}
    (hO : OnlyState [.s3 q, .u q b] w) (i : Rx Q L) (hi : ¬ i.IsClock)
    (hr : rate C i w ≠ 0) :
    i ∈ [.auto34 q b, .cMs q b, .cTs q b, .cT q b, .cM q b, .cD q b, .cB q b, .pair, .k1, .k2] := by
  rw [rate_ne_zero_iff] at hr
  unfold OnlyState at hO
  have hu : ∀ q' b', ¬ (q' = q ∧ b' = b) → w (.u q' b') = 0 := fun q' b' h =>
    hO _ trivial (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or, Sp.u.injEq]
      exact ⟨by simp, h⟩)
  have h3 : ∀ q', q' ≠ q → w (.s3 q') = 0 := fun q' h => hO _ trivial (by simp [h])
  cases i with
  | auto34 q' b' =>
    by_cases h : q' = q ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := h; simp
    · exfalso; simp only [src1, src2] at hr; exact hr.2 (hu q' b' h)
  | cMs q' b' | cTs q' b' | cT q' b' | cM q' b' | cD q' b' | cB q' b' =>
    by_cases h : q' = q ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := h; simp
    · exfalso; simp only [src1, src2] at hr; exact hr.1 (hu q' b' h)
  | eps q' b' =>
    exfalso; simp only [src1, src2] at hr; exact hr.1 (hO _ trivial (by simp))
  | auto41 q' b' =>
    exfalso; simp only [src1, src2] at hr; exact hr.2 (hO _ trivial (by simp))
  | adv3 q' => exfalso; simp only [src1, src2] at hr; exact hr.1 (hO _ trivial (by simp))
  | auto23 q' => exfalso; simp only [src1, src2] at hr; exact hr.1 (hO _ trivial (by simp))
  | pair => simp
  | k1 => simp
  | k2 => simp
  | _ => kill_state


set_option hygiene false in
/-- One memory reaction of stage (c) of Lemma 4.4: the window set is kept and `V34` does not
increase (the step shared by `win34c_fire_cMs` … `win34c_fire_k2`). -/
local macro "win34c_mem_tac" : tactic => `(tactic| (
    have hr' := hr
    rw [rate_ne_zero_iff] at hr'
    simp only [src1, src2] at hr'
    refine ⟨Or.inr (Or.inr ⟨hO.fire C _ fun s hs hn => ?_, ?_, ?_, ?_⟩), ?_⟩
    · cases s <;> simp_all [out, Sp.IsState]
    · simp [src1, src2, out] <;> omega
    · simp [src1, src2, out] <;> omega
    · simp only [MemC, memv_apply] at hMC ⊢
      cases b <;> cases hz : (C.next q _).2 <;> simp [src1, src2, out, bw, hz] at hMC ⊢ <;> omega
    · refine (V34_sub_le hm hx'pos (by simp [src1, src2, out]) (by simp [src1, src2, out])
        (by simp [src1, src2, out] <;> omega) ?_ ?_).2.2
      · simp only [phi1]; cases b <;> simp [src1, src2, out] <;> omega
      · simp only [phi2]; cases b <;> simp [src1, src2, out] <;> omega))

/-- Lemma 4.4 (closure), stage (c), autocatalysis `U + S₃ → 2U`. -/
theorem win34c_fire_auto {m T0 g x x' : ℕ} (hm : 0 < m) (hx'pos : 0 < x') {q : Q} {b : Bool}
    {w : State (Sp Q L)} (hO : OnlyState [.s3 q, .u q b] w) (h3 : w (.s3 q) + w (.u q b) = m)
    (hu : 1 ≤ w (.u q b)) (hMC : MemC m T0 b (C.next q b).2 x' (memv w))
    (hr : rate C (.auto34 q b) w ≠ 0) :
    Win34 C m T0 g q b x x' ((rxn C (.auto34 q b)).fire w) ∧
      V34 m g x' q b ((rxn C (.auto34 q b)).fire w) ≤ V34 m g x' q b w := by
  have hr' := hr
  rw [rate_ne_zero_iff] at hr'
  simp only [src1, src2] at hr'
  have hmm : memv ((rxn C (.auto34 q b)).fire w) = memv w :=
    memv_fire_of_state (by simp [src1]) (by simp [src2]) (by simp [out])
  refine ⟨Or.inr (Or.inr ⟨hO.fire C _ fun s hs hn => ?_, ?_, ?_, hmm ▸ hMC⟩), ?_⟩
  · cases s <;> simp_all [out, Sp.IsState]
  · simp [src1, src2, out] <;> omega
  · simp [src1, src2, out]
  · have e1 : ((rxn C (.auto34 q b)).fire w) .i = w .i := by simp [src1, src2, out]
    have e2 : ((rxn C (.auto34 q b)).fire w) (.rq q) = w (.rq q) := by simp [src1, src2, out]
    have e3 : ((rxn C (.auto34 q b)).fire w) (.u q b) = w (.u q b) + 1 := by
      simp [src1, src2, out]; omega
    have p1 : phi1 ((rxn C (.auto34 q b)).fire w) = phi1 w := by simp [phi1, src1, src2, out]
    have p2 : phi2 ((rxn C (.auto34 q b)).fire w) = phi2 w := by simp [phi2, src1, src2, out]
    simp only [V34, e1, e2, e3, p1, p2]
    have := aut_anti (m := m) (show max (w (.u q b)) 1 ≤ max (w (.u q b) + 1) 1 by omega)
    linarith

/-- Lemma 4.4 (closure), stage (c), reaction `cMs`. -/
theorem win34c_fire_cMs {m T0 g x x' : ℕ} (hm : 0 < m) (hx'pos : 0 < x') {q : Q} {b : Bool}
    {w : State (Sp Q L)} (hO : OnlyState [.s3 q, .u q b] w) (h3 : w (.s3 q) + w (.u q b) = m)
    (hu : 1 ≤ w (.u q b)) (hMC : MemC m T0 b (C.next q b).2 x' (memv w))
    (hr : rate C (.cMs q b) w ≠ 0) :
    Win34 C m T0 g q b x x' ((rxn C (.cMs q b)).fire w) ∧
      V34 m g x' q b ((rxn C (.cMs q b)).fire w) ≤ V34 m g x' q b w := by
  win34c_mem_tac

/-- Lemma 4.4 (closure), stage (c), reaction `cTs`. -/
theorem win34c_fire_cTs {m T0 g x x' : ℕ} (hm : 0 < m) (hx'pos : 0 < x') {q : Q} {b : Bool}
    {w : State (Sp Q L)} (hO : OnlyState [.s3 q, .u q b] w) (h3 : w (.s3 q) + w (.u q b) = m)
    (hu : 1 ≤ w (.u q b)) (hMC : MemC m T0 b (C.next q b).2 x' (memv w))
    (hr : rate C (.cTs q b) w ≠ 0) :
    Win34 C m T0 g q b x x' ((rxn C (.cTs q b)).fire w) ∧
      V34 m g x' q b ((rxn C (.cTs q b)).fire w) ≤ V34 m g x' q b w := by
  win34c_mem_tac

/-- Lemma 4.4 (closure), stage (c), reaction `cT`. -/
theorem win34c_fire_cT {m T0 g x x' : ℕ} (hm : 0 < m) (hx'pos : 0 < x') {q : Q} {b : Bool}
    {w : State (Sp Q L)} (hO : OnlyState [.s3 q, .u q b] w) (h3 : w (.s3 q) + w (.u q b) = m)
    (hu : 1 ≤ w (.u q b)) (hMC : MemC m T0 b (C.next q b).2 x' (memv w))
    (hr : rate C (.cT q b) w ≠ 0) :
    Win34 C m T0 g q b x x' ((rxn C (.cT q b)).fire w) ∧
      V34 m g x' q b ((rxn C (.cT q b)).fire w) ≤ V34 m g x' q b w := by
  win34c_mem_tac

/-- Lemma 4.4 (closure), stage (c), reaction `cM`. -/
theorem win34c_fire_cM {m T0 g x x' : ℕ} (hm : 0 < m) (hx'pos : 0 < x') {q : Q} {b : Bool}
    {w : State (Sp Q L)} (hO : OnlyState [.s3 q, .u q b] w) (h3 : w (.s3 q) + w (.u q b) = m)
    (hu : 1 ≤ w (.u q b)) (hMC : MemC m T0 b (C.next q b).2 x' (memv w))
    (hr : rate C (.cM q b) w ≠ 0) :
    Win34 C m T0 g q b x x' ((rxn C (.cM q b)).fire w) ∧
      V34 m g x' q b ((rxn C (.cM q b)).fire w) ≤ V34 m g x' q b w := by
  win34c_mem_tac

/-- Lemma 4.4 (closure), stage (c), reaction `cD`. -/
theorem win34c_fire_cD {m T0 g x x' : ℕ} (hm : 0 < m) (hx'pos : 0 < x') {q : Q} {b : Bool}
    {w : State (Sp Q L)} (hO : OnlyState [.s3 q, .u q b] w) (h3 : w (.s3 q) + w (.u q b) = m)
    (hu : 1 ≤ w (.u q b)) (hMC : MemC m T0 b (C.next q b).2 x' (memv w))
    (hr : rate C (.cD q b) w ≠ 0) :
    Win34 C m T0 g q b x x' ((rxn C (.cD q b)).fire w) ∧
      V34 m g x' q b ((rxn C (.cD q b)).fire w) ≤ V34 m g x' q b w := by
  win34c_mem_tac

/-- Lemma 4.4 (closure), stage (c), reaction `cB`. -/
theorem win34c_fire_cB {m T0 g x x' : ℕ} (hm : 0 < m) (hx'pos : 0 < x') {q : Q} {b : Bool}
    {w : State (Sp Q L)} (hO : OnlyState [.s3 q, .u q b] w) (h3 : w (.s3 q) + w (.u q b) = m)
    (hu : 1 ≤ w (.u q b)) (hMC : MemC m T0 b (C.next q b).2 x' (memv w))
    (hr : rate C (.cB q b) w ≠ 0) :
    Win34 C m T0 g q b x x' ((rxn C (.cB q b)).fire w) ∧
      V34 m g x' q b ((rxn C (.cB q b)).fire w) ≤ V34 m g x' q b w := by
  win34c_mem_tac

/-- Lemma 4.4 (closure), stage (c), reaction `pair`. -/
theorem win34c_fire_pair {m T0 g x x' : ℕ} (hm : 0 < m) (hx'pos : 0 < x') {q : Q} {b : Bool}
    {w : State (Sp Q L)} (hO : OnlyState [.s3 q, .u q b] w) (h3 : w (.s3 q) + w (.u q b) = m)
    (hu : 1 ≤ w (.u q b)) (hMC : MemC m T0 b (C.next q b).2 x' (memv w))
    (hr : rate C .pair w ≠ 0) :
    Win34 C m T0 g q b x x' ((rxn C .pair).fire w) ∧
      V34 m g x' q b ((rxn C .pair).fire w) ≤ V34 m g x' q b w := by
  win34c_mem_tac

/-- Lemma 4.4 (closure), stage (c), reaction `k1`. -/
theorem win34c_fire_k1 {m T0 g x x' : ℕ} (hm : 0 < m) (hx'pos : 0 < x') {q : Q} {b : Bool}
    {w : State (Sp Q L)} (hO : OnlyState [.s3 q, .u q b] w) (h3 : w (.s3 q) + w (.u q b) = m)
    (hu : 1 ≤ w (.u q b)) (hMC : MemC m T0 b (C.next q b).2 x' (memv w))
    (hr : rate C .k1 w ≠ 0) :
    Win34 C m T0 g q b x x' ((rxn C .k1).fire w) ∧
      V34 m g x' q b ((rxn C .k1).fire w) ≤ V34 m g x' q b w := by
  win34c_mem_tac

/-- Lemma 4.4 (closure), stage (c), reaction `k2`. -/
theorem win34c_fire_k2 {m T0 g x x' : ℕ} (hm : 0 < m) (hx'pos : 0 < x') {q : Q} {b : Bool}
    {w : State (Sp Q L)} (hO : OnlyState [.s3 q, .u q b] w) (h3 : w (.s3 q) + w (.u q b) = m)
    (hu : 1 ≤ w (.u q b)) (hMC : MemC m T0 b (C.next q b).2 x' (memv w))
    (hr : rate C .k2 w ≠ 0) :
    Win34 C m T0 g q b x x' ((rxn C .k2).fire w) ∧
      V34 m g x' q b ((rxn C .k2).fire w) ≤ V34 m g x' q b w := by
  win34c_mem_tac

/-- **Lemma 4.4 (closure), stage (c).** -/
theorem win34c_fire {m T0 g x x' : ℕ} (hm : 0 < m) (hx'pos : 0 < x') {q : Q} {b : Bool}
    {w : State (Sp Q L)} (hO : OnlyState [.s3 q, .u q b] w) (h3 : w (.s3 q) + w (.u q b) = m)
    (hu : 1 ≤ w (.u q b)) (hMC : MemC m T0 b (C.next q b).2 x' (memv w))
    (i : Rx Q L) (hi : ¬ i.IsClock) (hr : rate C i w ≠ 0) :
    Win34 C m T0 g q b x x' ((rxn C i).fire w) ∧
      V34 m g x' q b ((rxn C i).fire w) ≤ V34 m g x' q b w := by
  have hmem := win34c_enabled C hO i hi hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact win34c_fire_auto C hm hx'pos hO h3 hu hMC hr
  · exact win34c_fire_cMs C hm hx'pos hO h3 hu hMC hr
  · exact win34c_fire_cTs C hm hx'pos hO h3 hu hMC hr
  · exact win34c_fire_cT C hm hx'pos hO h3 hu hMC hr
  · exact win34c_fire_cM C hm hx'pos hO h3 hu hMC hr
  · exact win34c_fire_cD C hm hx'pos hO h3 hu hMC hr
  · exact win34c_fire_cB C hm hx'pos hO h3 hu hMC hr
  · exact win34c_fire_pair C hm hx'pos hO h3 hu hMC hr
  · exact win34c_fire_k1 C hm hx'pos hO h3 hu hMC hr
  · exact win34c_fire_k2 C hm hx'pos hO h3 hu hMC hr

/-- **Lemma 4.4 (closure).** -/
theorem win34_fire {m T0 g x x' : ℕ} (hm : 0 < m) (hx'pos : 0 < x') {q : Q} {b : Bool}
    (hx' : x' + 3 * bw b * m = 3 * x + bw (C.next q b).2) {w : State (Sp Q L)}
    (h : Win34 C m T0 g q b x x' w) (i : Rx Q L) (hi : ¬ i.IsClock) (hr : rate C i w ≠ 0) :
    Win34 C m T0 g q b x x' ((rxn C i).fire w) ∧
      V34 m g x' q b ((rxn C i).fire w) ≤ V34 m g x' q b w := by
  rcases h with ⟨hO, hI, h3, hM⟩ | ⟨hO, hR, h3, hM⟩ | ⟨hO, h3, hu, hMC⟩
  · -- stage (a)
    obtain rfl := win34a_enabled C hO hM i hi hr
    have hr' := hr
    rw [rate_ne_zero_iff] at hr'
    simp only [src1, src2] at hr'
    have hRq : w (.rq q) = 0 := hO _ trivial (by simp)
    have hmem : memv ((rxn C (.adv3 q)).fire w) = memv w :=
      memv_fire_of_state (by simp [src1]) (by simp [src2]) (by simp [out])
    refine ⟨Or.inr (Or.inl ⟨OnlyState.fire' ?_, ?_, ?_, hmem ▸ hM⟩), ?_⟩
    · intro s hs hn
      rw [fire_apply]
      by_cases e : s = .i
      · subst e; simp [src1, src2, out, hI]
      · have hz := hO s hs (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn ⊢
          exact ⟨hn.1, e⟩)
        have hn' : s ≠ .rq q := fun h' => hn (by simp [h'])
        simp [src1, src2, out, hz, hn', e]
    · simp [src1, src2, out, hRq]
    · simp [src1, src2, out] <;> omega
    · have hu : w (.u q b) = 0 := hO _ trivial (by simp)
      have e1 : ((rxn C (.adv3 q)).fire w) .i = 0 := by simp [src1, src2, out, hI]
      have e2 : ((rxn C (.adv3 q)).fire w) (.rq q) = 1 := by simp [src1, src2, out, hRq]
      have e3 : ((rxn C (.adv3 q)).fire w) (.u q b) = 0 := by simp [src1, src2, out, hu]
      have p1 : phi1 ((rxn C (.adv3 q)).fire w) = phi1 w := by simp [phi1, src1, src2, out]
      have p2 : phi2 ((rxn C (.adv3 q)).fire w) = phi2 w := by simp [phi2, src1, src2, out]
      simp only [V34, e1, e2, e3, p1, p2, hI, hu]
      simp
  · -- stage (b)
    have hr' := hr
    rw [rate_ne_zero_iff] at hr'
    have hI : w .i = 0 := hO _ trivial (by simp)
    have hu0 : w (.u q b) = 0 := hO _ trivial (by simp)
    obtain ⟨⟨hA1, hA2, hA3, hA4, hA5, hA6, hA7⟩, ⟨hmd, htd, hds, hbs⟩, hb0, hb1⟩ := hM
    simp only [memv_apply] at hA1 hA2 hA3 hA4 hA5 hA6 hA7 hmd htd hds hbs hb0 hb1
    rcases win34b_enabled C hO ⟨⟨hA1, hA2, hA3, hA4, hA5, hA6, hA7⟩, ⟨hmd, htd, hds, hbs⟩, hb0,
      hb1⟩ i hi hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- `rt`
        simp only [src1, src2] at hr'
        refine ⟨Or.inr (Or.inr ⟨OnlyState.fire' ?_, ?_, ?_, ?_⟩), ?_⟩
        · intro s hs hn
          rw [fire_apply]
          by_cases e : s = .rq q
          · subst e; simp [src1, src2, out, hR]
          · have hz := hO s hs (by
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn ⊢
              exact ⟨hn.1, e⟩)
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
            have hm' : ∀ y, s ≠ .mem y := by rintro y rfl; exact hs
            simp [src1, src2, out, hz, hn.2, e, hm']
        · simp [src1, src2, out, hu0] <;> omega
        · simp [src1, src2, out, hu0]
        · simp only [MemC, memv_apply]
          cases hz : (C.next q false).2 <;> simp [src1, src2, out, bw, hz] at hx' ⊢ <;> omega
        · have e1 : ((rxn C (.rt q)).fire w) .i = 0 := by simp [src1, src2, out, hI]
          have p1 : phi1 ((rxn C (.rt q)).fire w) = phi1 w := by
            simp [phi1, src1, src2, out] <;> omega
          have p2 : phi2 ((rxn C (.rt q)).fire w) = phi2 w := by
            simp [phi2, src1, src2, out] <;> omega
          simp only [V34, e1, p1, p2, hI, hR, hu0]
          simp [src1, src2, out, hu0]
          split_ifs <;> first | exact le_refl _ | positivity

    · -- `rm`
        simp only [src1, src2] at hr'
        refine ⟨Or.inr (Or.inr ⟨OnlyState.fire' ?_, ?_, ?_, ?_⟩), ?_⟩
        · intro s hs hn
          rw [fire_apply]
          by_cases e : s = .rq q
          · subst e; simp [src1, src2, out, hR]
          · have hz := hO s hs (by
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn ⊢
              exact ⟨hn.1, e⟩)
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
            have hm' : ∀ y, s ≠ .mem y := by rintro y rfl; exact hs
            simp [src1, src2, out, hz, hn.2, e, hm']
        · simp [src1, src2, out, hu0] <;> omega
        · simp [src1, src2, out, hu0]
        · simp only [MemC, memv_apply]
          cases hz : (C.next q true).2 <;> simp [src1, src2, out, bw, hz] at hx' ⊢ <;> omega
        · have e1 : ((rxn C (.rm q)).fire w) .i = 0 := by simp [src1, src2, out, hI]
          have p1 : phi1 ((rxn C (.rm q)).fire w) = phi1 w := by
            simp [phi1, src1, src2, out] <;> omega
          have p2 : phi2 ((rxn C (.rm q)).fire w) = phi2 w := by
            simp [phi2, src1, src2, out] <;> omega
          simp only [V34, e1, p1, p2, hI, hR, hu0]
          simp [src1, src2, out, hu0]
          split_ifs <;> first | exact le_refl _ | positivity
  · -- stage (c)
    exact win34c_fire C hm hx'pos hO h3 hu hMC i hi hr

/-! ### Target, drift and start -/

theorem V34_nonneg (m g x' : ℕ) (q : Q) (b : Bool) (w : State (Sp Q L)) :
    0 ≤ V34 m g x' q b w := by
  unfold V34
  have := aut_nonneg m (max (w (.u q b)) 1)
  have : 0 ≤ Real.log (1 + phi1 w) := Real.log_nonneg (by linarith [(Nat.cast_nonneg (phi1 w) : (0 : ℝ) ≤ phi1 w)])
  have : 0 ≤ Real.log (1 + phi2 w) := Real.log_nonneg (by linarith [(Nat.cast_nonneg (phi2 w) : (0 : ℝ) ≤ phi2 w)])
  have : (0 : ℝ) ≤ if w .i = 1 then 1 / (m : ℝ) else 0 := by split_ifs <;> positivity
  have : (0 : ℝ) ≤ if w .i = 1 ∨ w (.rq q) = 1 then 1 / (g : ℝ) else 0 := by
    split_ifs <;> positivity
  positivity

theorem log_one_add_eq_zero {a : ℕ} (h : Real.log (1 + (a : ℝ)) = 0) : a = 0 := by
  rcases Real.log_eq_zero.mp h with h' | h' | h'
  · have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  · exact_mod_cast (show (a : ℝ) = 0 by linarith)
  · have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith

/-- The target `𝒦_4(q, b; w')` is the zero set of `V34` in the window. -/
theorem k4_iff_V34 {m T0 g x x' : ℕ} (hm : 2 ≤ m) (hg : 1 ≤ g) (hx'pos : 1 ≤ x') {q : Q}
    {b : Bool} {w : State (Sp Q L)} (h : Win34 C m T0 g q b x x' w) :
    K4 m T0 q b x' w ↔ V34 m g x' q b w = 0 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hg' : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hx' : (0 : ℝ) < x' := by exact_mod_cast (show 0 < x' by omega)
  constructor
  · rintro ⟨hO4, hu, hM4⟩
    have hi : w .i = 0 := hO4 .i trivial (by simp)
    have hR : w (.rq q) = 0 := hO4 _ trivial (by simp)
    obtain ⟨-, -, -, -, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hM4
    simp only [memv_apply] at h5 h6 h7 h8 h9 h10 h11 h12
    have p1 : phi1 w = 0 := by simp [phi1, h5, h6, h7, h8, h9, h10]
    have p2 : phi2 w = 0 := by simp [phi2, h9, h11, h12]
    simp [V34, hi, hR, hu, p1, p2, aut_eq_zero_of (le_max_left m 1)]
  · intro hV
    have a1 := aut_nonneg m (max (w (.u q b)) 1)
    have l1 : 0 ≤ Real.log (1 + phi1 w) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg (phi1 w) : (0 : ℝ) ≤ phi1 w)])
    have l2 : 0 ≤ Real.log (1 + phi2 w) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg (phi2 w) : (0 : ℝ) ≤ phi2 w)])
    have i1 : (0 : ℝ) ≤ if w .i = 1 then 1 / (m : ℝ) else 0 := by split_ifs <;> positivity
    have i2 : (0 : ℝ) ≤ if w .i = 1 ∨ w (.rq q) = 1 then 1 / (g : ℝ) else 0 := by
      split_ifs <;> positivity
    have t4 : 0 ≤ 4 / (m : ℝ) * Real.log (1 + phi1 w) := by positivity
    have t5 : 0 ≤ 4 / (x' : ℝ) * Real.log (1 + phi2 w) := by positivity
    unfold V34 at hV
    have e2 : (if w .i = 1 ∨ w (.rq q) = 1 then 1 / (g : ℝ) else 0) = 0 := by linarith
    have e3 : aut m (max (w (.u q b)) 1) = 0 := by linarith
    have e4 : 4 / (m : ℝ) * Real.log (1 + phi1 w) = 0 := by linarith
    have e5 : 4 / (x' : ℝ) * Real.log (1 + phi2 w) = 0 := by linarith
    have hnot : ¬ (w .i = 1 ∨ w (.rq q) = 1) := by
      intro hc; rw [if_pos hc] at e2; exact absurd e2 (by positivity)
    have p1 : phi1 w = 0 :=
      log_one_add_eq_zero ((mul_eq_zero.mp e4).resolve_left (by positivity))
    have p2 : phi2 w = 0 :=
      log_one_add_eq_zero ((mul_eq_zero.mp e5).resolve_left (by positivity))
    rcases h with ⟨_, hI, _⟩ | ⟨_, hR, _⟩ | ⟨hO, h3, hu, hMC⟩
    · exact absurd (Or.inl hI) hnot
    · exact absurd (Or.inr hR) hnot
    · have hum : m ≤ w (.u q b) := by
        by_contra hlt
        exact absurd e3 (aut_pos (le_max_right _ _) (by omega)).ne'
      simp only [phi1, phi2] at p1 p2
      obtain ⟨c1, c2, c3, c4⟩ := hMC
      simp only [memv_apply] at c1 c2 c3 c4
      have hD : w (.mem .d) = 0 := by omega
      have hB : w (.mem .b) = 0 := by omega
      have hk1 : w (.mem .k1) = 0 := by omega
      have hk2 : w (.mem .k2) = 0 := by omega
      rw [hB, hD, hk1, hk2] at c1
      simp only [mul_zero, add_zero] at c1
      refine ⟨fun s hs hn => ?_, by omega, ?_⟩
      · by_cases e : s = .s3 q
        · rw [e]; omega
        · exact hO s hs (by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn ⊢
            exact ⟨e, hn⟩)
      · simp only [Mem4, memv_apply]; omega

/-- A non-clock term with nonnegative rate is bounded by the rate times a bound on the
increment, provided the bound holds whenever the rate is positive. -/
theorem term_le {r : ℕ} {d c : ℝ} (h : r ≠ 0 → d ≤ c) : (r : ℝ) * d ≤ r * c := by
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · simp [h0]
  · exact mul_le_mul_of_nonneg_left (h hpos.ne') (Nat.cast_nonneg _)

/-- A `U`-catalysed reaction at `U = m` lowers `Φ₁` by `k` per molecule of its reactant. -/
theorem term_phi1_le {m g x' : ℕ} (hm : 0 < m) (hx'pos : 0 < x') {q : Q} {b : Bool}
    {w : State (Sp Q L)} {ℓ : Rx Q L} (hc : ¬ ℓ.IsClock) {X : Sp Q L} {k : ℕ}
    (hrate : rate C ℓ w = m * w X)
    (hfire : w X ≠ 0 → ((rxn C ℓ).fire w) .i = w .i ∧
      ((rxn C ℓ).fire w) (.rq q) = w (.rq q) ∧ ((rxn C ℓ).fire w) (.u q b) = w (.u q b) ∧
      phi1 ((rxn C ℓ).fire w) + k = phi1 w ∧ phi2 ((rxn C ℓ).fire w) ≤ phi2 w) :
    (if ℓ.IsClock then 0 else (rate C ℓ w : ℝ) *
      (V34 m g x' q b ((rxn C ℓ).fire w) - V34 m g x' q b w)) ≤
        -(4 * k * (w X : ℝ)) / (1 + phi1 w) := by
  rw [if_neg hc, hrate]
  rcases Nat.eq_zero_or_pos (w X) with h0 | hpos
  · simp [h0]
  · obtain ⟨e1, e2, e3, e4, e5⟩ := hfire hpos.ne'
    have hV := (V34_sub_le (g := g) hm hx'pos e1 e2 e3 (by omega) e5).1
    have e4' : (phi1 ((rxn C ℓ).fire w) : ℝ) - phi1 w = -(k : ℝ) := by
      have : ((phi1 ((rxn C ℓ).fire w) + k : ℕ) : ℝ) = phi1 w := by exact_mod_cast e4
      push_cast at this; linarith
    rw [e4'] at hV
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hp : (0 : ℝ) < 1 + phi1 w := by positivity
    calc ((m * w X : ℕ) : ℝ) * (V34 m g x' q b ((rxn C ℓ).fire w) - V34 m g x' q b w)
        ≤ ((m * w X : ℕ) : ℝ) * (4 / (m : ℝ) * (-(k : ℝ) / (1 + phi1 w))) :=
          mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg _)
      _ = -(4 * k * (w X : ℝ)) / (1 + phi1 w) := by
          push_cast; field_simp

/-- A `K`-reaction lowers `Φ₂` by one; its rate is `#K · #M†` with `#M† ≥ x'`. -/
theorem term_phi2_le {m g x' : ℕ} (hm : 0 < m) (hx'pos : 0 < x') {q : Q} {b : Bool}
    {w : State (Sp Q L)} {ℓ : Rx Q L} (hc : ¬ ℓ.IsClock) {K : Sp Q L}
    (hrate : rate C ℓ w = w K * w (.mem .md)) (hmd : x' ≤ w (.mem .md))
    (hfire : w K ≠ 0 → ((rxn C ℓ).fire w) .i = w .i ∧
      ((rxn C ℓ).fire w) (.rq q) = w (.rq q) ∧ ((rxn C ℓ).fire w) (.u q b) = w (.u q b) ∧
      phi1 ((rxn C ℓ).fire w) ≤ phi1 w ∧ phi2 ((rxn C ℓ).fire w) + 1 = phi2 w) :
    (if ℓ.IsClock then 0 else (rate C ℓ w : ℝ) *
      (V34 m g x' q b ((rxn C ℓ).fire w) - V34 m g x' q b w)) ≤
        -(4 * (w K : ℝ)) / (1 + phi2 w) := by
  rw [if_neg hc, hrate]
  rcases Nat.eq_zero_or_pos (w K) with h0 | hpos
  · simp [h0]
  · obtain ⟨e1, e2, e3, e4, e5⟩ := hfire hpos.ne'
    have hV := (V34_sub_le (g := g) hm hx'pos e1 e2 e3 e4 (by omega)).2.1
    have e5' : (phi2 ((rxn C ℓ).fire w) : ℝ) - phi2 w = -1 := by
      have : ((phi2 ((rxn C ℓ).fire w) + 1 : ℕ) : ℝ) = phi2 w := by exact_mod_cast e5
      push_cast at this; linarith
    rw [e5'] at hV
    have hx' : (0 : ℝ) < x' := by exact_mod_cast hx'pos
    have hp : (0 : ℝ) < 1 + phi2 w := by positivity
    have hmd' : (x' : ℝ) ≤ w (.mem .md) := by exact_mod_cast hmd
    have hneg : 4 / (x' : ℝ) * (-1 / (1 + phi2 w)) ≤ 0 := by
      have : -1 / (1 + (phi2 w : ℝ)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hp.le
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) this
    calc ((w K * w (.mem .md) : ℕ) : ℝ) * (V34 m g x' q b ((rxn C ℓ).fire w) - V34 m g x' q b w)
        ≤ ((w K * w (.mem .md) : ℕ) : ℝ) * (4 / (x' : ℝ) * (-1 / (1 + phi2 w))) :=
          mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg _)
      _ ≤ ((w K : ℝ) * x') * (4 / (x' : ℝ) * (-1 / (1 + phi2 w))) := by
          push_cast
          exact mul_le_mul_of_nonpos_right
            (mul_le_mul_of_nonneg_left hmd' (Nat.cast_nonneg _)) hneg
      _ = -(4 * (w K : ℝ)) / (1 + phi2 w) := by field_simp

/-- **Lemma 5.4 (drift).**  Off the target the non-clock drift of `V34` is at most `-1`. -/
theorem win34_drift {m T0 g x x' : ℕ} (hm : 2 ≤ m) (hg : 1 ≤ g) (hx'pos : 1 ≤ x') {q : Q}
    {b : Bool} (hx' : x' + 3 * bw b * m = 3 * x + bw (C.next q b).2) {w : State (Sp Q L)}
    (h : Win34 C m T0 g q b x x' w) (hK : ¬ K4 m T0 q b x' w) :
    drift C (V34 m g x' q b) w ≤ -1 := by
  have hm0 : 0 < m := by omega
  have hmono : ∀ i : Rx Q L, ¬ i.IsClock → rate C i w ≠ 0 →
      V34 m g x' q b ((rxn C i).fire w) ≤ V34 m g x' q b w :=
    fun i hi hr => (win34_fire C hm0 (by omega) hx' h i hi hr).2
  have hW := h
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hg' : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  rcases h with ⟨hO, hI, h3, hM⟩ | ⟨hO, hR, h3, hM⟩ | ⟨hO, h3, hu, hMC⟩
  · -- stage (a)
    have hRq : w (.rq q) = 0 := hO _ trivial (by simp)
    have hu0 : w (.u q b) = 0 := hO _ trivial (by simp)
    refine (drift_le_sum C _ w hmono {.adv3 q}).trans (le_of_eq ?_)
    rw [Finset.sum_singleton, if_neg (by simp [Rx.IsClock])]
    have p1 : phi1 ((rxn C (.adv3 q)).fire w) = phi1 w := by simp [phi1, src1, src2, out]
    have p2 : phi2 ((rxn C (.adv3 q)).fire w) = phi2 w := by simp [phi2, src1, src2, out]
    have e : V34 m g x' q b ((rxn C (.adv3 q)).fire w) = V34 m g x' q b w - 1 / m := by
      simp only [V34, p1, p2]
      simp [src1, src2, out, hI, hRq, hu0]
      try ring
    rw [e, rate_eq]
    simp only [src1, src2, hI, h3]
    rw [show V34 m g x' q b w - 1 / (m : ℝ) - V34 m g x' q b w = -(1 / (m : ℝ)) by ring]
    push_cast
    rw [one_mul, mul_neg, mul_one_div_cancel hm'.ne']
  · -- stage (b)
    have hI : w .i = 0 := hO _ trivial (by simp)
    have hu0 : w (.u q b) = 0 := hO _ trivial (by simp)
    obtain ⟨hA, hRs, hb0, hb1⟩ := hM
    simp only [memv_apply] at hb0 hb1
    cases b
    · obtain ⟨hM0, hT⟩ := hb0 rfl
      refine (drift_le_sum C _ w hmono {.rt q}).trans ?_
      rw [Finset.sum_singleton, if_neg (by simp [Rx.IsClock])]
      have p1 : phi1 ((rxn C (.rt q)).fire w) = phi1 w := by
        simp [phi1, src1, src2, out] <;> omega
      have p2 : phi2 ((rxn C (.rt q)).fire w) = phi2 w := by simp [phi2, src1, src2, out]
      have e : V34 m g x' q false ((rxn C (.rt q)).fire w) = V34 m g x' q false w - 1 / g := by
        simp only [V34, p1, p2]
        simp [src1, src2, out, hI, hR, hu0]
        try ring
      rw [e, rate_eq]
      simp only [src1, src2, hR]
      rw [show V34 m g x' q false w - 1 / (g : ℝ) - V34 m g x' q false w = -(1 / (g : ℝ)) by ring]
      have hT' : (g : ℝ) ≤ w (.mem .t) := by exact_mod_cast hT
      push_cast
      rw [one_mul, mul_neg, ← le_neg, neg_neg, mul_one_div, le_div_iff₀ hg', one_mul]
      exact hT'
    · obtain ⟨hT0, hM⟩ := hb1 rfl
      refine (drift_le_sum C _ w hmono {.rm q}).trans ?_
      rw [Finset.sum_singleton, if_neg (by simp [Rx.IsClock])]
      have p1 : phi1 ((rxn C (.rm q)).fire w) = phi1 w := by
        simp [phi1, src1, src2, out] <;> omega
      have p2 : phi2 ((rxn C (.rm q)).fire w) = phi2 w := by simp [phi2, src1, src2, out]
      have e : V34 m g x' q true ((rxn C (.rm q)).fire w) = V34 m g x' q true w - 1 / g := by
        simp only [V34, p1, p2]
        simp [src1, src2, out, hI, hR, hu0]
        try ring
      rw [e, rate_eq]
      simp only [src1, src2, hR]
      rw [show V34 m g x' q true w - 1 / (g : ℝ) - V34 m g x' q true w = -(1 / (g : ℝ)) by ring]
      have hM' : (g : ℝ) ≤ w (.mem .m) := by exact_mod_cast hM
      push_cast
      rw [one_mul, mul_neg, ← le_neg, neg_neg, mul_one_div, le_div_iff₀ hg', one_mul]
      exact hM'
  · -- stage (c)
    rcases Nat.lt_or_ge (w (.u q b)) m with hlt | hge
    · refine (drift_le_sum C _ w hmono {.auto34 q b}).trans (le_of_eq ?_)
      rw [Finset.sum_singleton, if_neg (by simp [Rx.IsClock])]
      have p1 : phi1 ((rxn C (.auto34 q b)).fire w) = phi1 w := by simp [phi1, src1, src2, out]
      have p2 : phi2 ((rxn C (.auto34 q b)).fire w) = phi2 w := by simp [phi2, src1, src2, out]
      have e : V34 m g x' q b ((rxn C (.auto34 q b)).fire w) - V34 m g x' q b w =
          aut m (w (.u q b) + 1) - aut m (w (.u q b)) := by
        simp only [V34, p1, p2]
        simp [src1, src2, out]
        try rw [max_eq_left (by omega : 1 ≤ w (.u q b) - 1 + 2)]
        rw [max_eq_left hu, show w (.u q b) - 1 + 2 = w (.u q b) + 1 by omega]
      rw [e, rate_eq]
      simp only [src1, src2]
      have := aut_drift (m := m) hu hlt
      rw [show w (.s3 q) = m - w (.u q b) by omega]
      push_cast at this ⊢
      linear_combination this
    · have hum : w (.u q b) = m := by omega
      have hph : 1 ≤ phi1 w ∨ (phi1 w = 0 ∧ 1 ≤ phi2 w) := by
        by_contra hc
        apply hK
        rw [k4_iff_V34 C hm hg hx'pos hW]
        have p1 : phi1 w = 0 := by omega
        have p2 : phi2 w = 0 := by omega
        have hi : w .i = 0 := hO _ trivial (by simp)
        have hR : w (.rq q) = 0 := hO _ trivial (by simp)
        simp [V34, hi, hR, hum, p1, p2, aut_eq_zero_of (le_max_left m 1)]
      obtain ⟨c1, c2, c3, c4⟩ := hMC
      simp only [memv_apply] at c1 c2 c3 c4
      have hR : w (.rq q) = 0 := hO _ trivial (by simp)
      have hi : w .i = 0 := hO _ trivial (by simp)
      have hx'r : (0 : ℝ) < x' := by exact_mod_cast hx'pos
      rcases hph with hp1 | ⟨hp1, hp2⟩
      · -- `Φ₁ ≥ 1`: the six `U`-catalysed reactions
        refine (drift_le_sum C _ w hmono
          {.cMs q b, .cTs q b, .cT q b, .cM q b, .cD q b, .cB q b}).trans ?_
        rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp),
          Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
        have t1 := term_phi1_le C (g := g) (x' := x') hm0 (by omega) (q := q) (b := b) (w := w) (ℓ := .cMs q b)
          (by simp [Rx.IsClock]) (X := .mem .ms) (k := 1) (by simp [rate_eq, src1, src2, hum])
          (fun h0 => ⟨by simp [src1, src2, out], by simp [src1, src2, out],
            by simp [src1, src2, out] <;> omega, by simp [phi1, src1, src2, out]; omega,
            by simp [phi2, src1, src2, out]⟩)
        have t2 := term_phi1_le C (g := g) (x' := x') hm0 (by omega) (q := q) (b := b) (w := w) (ℓ := .cTs q b)
          (by simp [Rx.IsClock]) (X := .mem .ts) (k := 1) (by simp [rate_eq, src1, src2, hum])
          (fun h0 => ⟨by simp [src1, src2, out], by simp [src1, src2, out],
            by simp [src1, src2, out] <;> omega, by simp [phi1, src1, src2, out]; omega,
            by simp [phi2, src1, src2, out]⟩)
        have t3 := term_phi1_le C (g := g) (x' := x') hm0 (by omega) (q := q) (b := b) (w := w) (ℓ := .cT q b)
          (by simp [Rx.IsClock]) (X := .mem .t) (k := 2) (by simp [rate_eq, src1, src2, hum])
          (fun h0 => ⟨by simp [src1, src2, out], by simp [src1, src2, out],
            by simp [src1, src2, out] <;> omega, by simp [phi1, src1, src2, out]; omega,
            by simp [phi2, src1, src2, out]⟩)
        have t4 := term_phi1_le C (g := g) (x' := x') hm0 (by omega) (q := q) (b := b) (w := w) (ℓ := .cM q b)
          (by simp [Rx.IsClock]) (X := .mem .m) (k := 1) (by simp [rate_eq, src1, src2, hum])
          (fun h0 => ⟨by simp [src1, src2, out], by simp [src1, src2, out],
            by simp [src1, src2, out] <;> omega, by simp [phi1, src1, src2, out]; omega,
            by simp [phi2, src1, src2, out]⟩)
        have t5 := term_phi1_le C (g := g) (x' := x') hm0 (by omega) (q := q) (b := b) (w := w) (ℓ := .cD q b)
          (by simp [Rx.IsClock]) (X := .mem .d) (k := 1) (by simp [rate_eq, src1, src2, hum])
          (fun h0 => ⟨by simp [src1, src2, out], by simp [src1, src2, out],
            by simp [src1, src2, out] <;> omega, by cases b <;> simp [phi1, src1, src2, out] <;> omega,
            by cases b <;> simp [phi2, src1, src2, out] <;> omega⟩)
        have t6 := term_phi1_le C (g := g) (x' := x') hm0 (by omega) (q := q) (b := b) (w := w) (ℓ := .cB q b)
          (by simp [Rx.IsClock]) (X := .mem .b) (k := 1) (by simp [rate_eq, src1, src2, hum])
          (fun h0 => ⟨by simp [src1, src2, out], by simp [src1, src2, out],
            by simp [src1, src2, out] <;> omega, by simp [phi1, src1, src2, out]; omega,
            by simp [phi2, src1, src2, out]⟩)
        have hp : (0 : ℝ) < 1 + phi1 w := by positivity
        have hsum : (1 + (phi1 w : ℝ)) ≤ 4 * ((w (.mem .ms) : ℝ) + w (.mem .ts) + 2 * w (.mem .t) +
            w (.mem .m) + w (.mem .d) + w (.mem .b)) := by
          have h1 : (1 : ℝ) ≤ phi1 w := by exact_mod_cast hp1
          have : (phi1 w : ℝ) = w (.mem .d) + w (.mem .b) + 2 * w (.mem .t) + w (.mem .ts) +
              w (.mem .m) + 2 * w (.mem .ms) := by simp [phi1]
          have hms : (0 : ℝ) ≤ w (.mem .ms) := Nat.cast_nonneg _
          linarith
        have : -(4 * (1 : ℕ) * (w (.mem .ms) : ℝ)) / (1 + phi1 w) +
            (-(4 * (1 : ℕ) * (w (.mem .ts) : ℝ)) / (1 + phi1 w) +
            (-(4 * (2 : ℕ) * (w (.mem .t) : ℝ)) / (1 + phi1 w) +
            (-(4 * (1 : ℕ) * (w (.mem .m) : ℝ)) / (1 + phi1 w) +
            (-(4 * (1 : ℕ) * (w (.mem .d) : ℝ)) / (1 + phi1 w) +
            -(4 * (1 : ℕ) * (w (.mem .b) : ℝ)) / (1 + phi1 w))))) ≤ -1 := by
          rw [← add_div, ← add_div, ← add_div, ← add_div, ← add_div, div_le_iff₀ hp]
          push_cast
          linarith
        exact (add_le_add t1 (add_le_add t2 (add_le_add t3 (add_le_add t4
          (add_le_add t5 t6))))).trans this
      · -- `Φ₁ = 0`, `Φ₂ ≥ 1`: the two `K`-reactions, with `#M† ≥ x'`
        simp only [phi1] at hp1
        have hmd : x' ≤ w (.mem .md) := by
          have hB : w (.mem .b) = 0 := by omega
          have hD : w (.mem .d) = 0 := by omega
          rw [hB, hD] at c1
          simp only [mul_zero, add_zero] at c1
          omega
        refine (drift_le_sum C _ w hmono {.k1, .k2}).trans ?_
        rw [Finset.sum_insert (by simp), Finset.sum_singleton]
        have t1 := term_phi2_le C (g := g) hm0 (by omega) (q := q) (b := b) (w := w) (ℓ := .k1)
          (by simp [Rx.IsClock]) (K := .mem .k1) (by simp [rate_eq, src1, src2]) hmd
          (fun h0 => ⟨by simp [src1, src2, out], by simp [src1, src2, out],
            by simp [src1, src2, out] <;> omega, by simp [phi1, src1, src2, out],
            by simp [phi2, src1, src2, out]; omega⟩)
        have t2 := term_phi2_le C (g := g) hm0 (by omega) (q := q) (b := b) (w := w) (ℓ := .k2)
          (by simp [Rx.IsClock]) (K := .mem .k2) (by simp [rate_eq, src1, src2]) hmd
          (fun h0 => ⟨by simp [src1, src2, out], by simp [src1, src2, out],
            by simp [src1, src2, out] <;> omega, by simp [phi1, src1, src2, out],
            by simp [phi2, src1, src2, out]; omega⟩)
        have hp : (0 : ℝ) < 1 + phi2 w := by positivity
        have hsum : (1 + (phi2 w : ℝ)) ≤ 4 * ((w (.mem .k1) : ℝ) + w (.mem .k2)) := by
          have h2 : (1 : ℝ) ≤ phi2 w := by exact_mod_cast hp2
          have hD : w (.mem .d) = 0 := by omega
          have : (phi2 w : ℝ) = w (.mem .k1) + 2 * w (.mem .k2) := by simp [phi2, hD]
          have : (0 : ℝ) ≤ w (.mem .k1) := Nat.cast_nonneg _
          linarith
        have : -(4 * (w (.mem .k1) : ℝ)) / (1 + phi2 w) + -(4 * (w (.mem .k2) : ℝ)) / (1 + phi2 w)
            ≤ -1 := by
          rw [← add_div, div_le_iff₀ hp]
          linarith
        linarith

omit [Fintype Q] in
/-- **Start of the window** (tick from `𝒦_3`), with the bound of Lemma 5.4. -/
theorem win34_start {m T0 g x x' : ℕ} (hg : 1 ≤ g) {q : Q} {b : Bool}
    (hb0 : b = false → x + g ≤ T0) (hb1 : b = true → T0 + g ≤ x) {w : State (Sp Q L)}
    (h : K3 m T0 q x w) :
    Win34 C m T0 g q b x x' (w + one .i) ∧
      V34 m g x' q b (w + one .i) ≤ 1 / m + 1 / g + aut m 1 +
        4 / (m : ℝ) * Real.log (1 + (m + 1 + 2 * T0 + 2 * x : ℕ)) +
        4 / (x' : ℝ) * Real.log (1 + (6 * m : ℕ)) := by
  obtain ⟨hO, hs, hM, hR, hTM⟩ := h
  have hi : w .i = 0 := hO .i trivial (by simp)
  have hRq : w (.rq q) = 0 := hO _ trivial (by simp)
  have hu : w (.u q b) = 0 := hO _ trivial (by simp)
  have hmem : memv (w + one .i) = memv w := by funext y; simp
  have hMT := m_add_T0 hM hR
  simp only [memv_apply] at hMT
  have hK3 : K3mem m T0 g b x (memv w) := by
    refine ⟨hM, hR, fun hb => ?_, fun hb => ?_⟩
    · have := hb0 hb
      simp only [memv_apply]
      rcases hTM with h0 | h0 <;> omega
    · have := hb1 hb
      simp only [memv_apply]
      rcases hTM with h0 | h0 <;> omega
  refine ⟨Or.inl ⟨fun s hs' hn => ?_, by simp [hi], by simp; omega, hmem ▸ hK3⟩, ?_⟩
  · have : s ≠ .i := fun e => hn (by simp [e])
    simp [this, hO s hs' (by simp_all)]
  · have ei : (w + one .i : State (Sp Q L)) .i = 1 := by simp [hi]
    have er : (w + one .i : State (Sp Q L)) (.rq q) = 0 := by simp [hRq]
    have eu : (w + one .i : State (Sp Q L)) (.u q b) = 0 := by simp [hu]
    have p1 : phi1 (w + one .i : State (Sp Q L)) = phi1 w := by simp [phi1]
    have p2 : phi2 (w + one .i : State (Sp Q L)) = phi2 w := by simp [phi2]
    simp only [V34, ei, er, eu, p1, p2, if_true, true_or, max_eq_right (zero_le_one' ℕ)]
    simp only [MemA, MemReset, memv_apply] at hM hR
    have b1 : phi1 w ≤ m + 1 + 2 * T0 + 2 * x := by simp only [phi1]; omega
    have b2 : phi2 w ≤ 6 * m := by simp only [phi2]; omega
    have l1 : Real.log (1 + phi1 w) ≤ Real.log (1 + (m + 1 + 2 * T0 + 2 * x : ℕ)) :=
      Real.log_le_log (by positivity) (by have := (Nat.cast_le (α := ℝ)).mpr b1; linarith)
    have l2 : Real.log (1 + phi2 w) ≤ Real.log (1 + (6 * m : ℕ)) :=
      Real.log_le_log (by positivity) (by have := (Nat.cast_le (α := ℝ)).mpr b2; linarith)
    have c1 : (0 : ℝ) ≤ 4 / (m : ℝ) := by positivity
    have c2 : (0 : ℝ) ≤ 4 / (x' : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left l1 c1
    have := mul_le_mul_of_nonneg_left l2 c2
    linarith

end Ripple.sCRNUniversality.ClockedCTM
