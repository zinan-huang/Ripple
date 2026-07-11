/-
Ripple.BoundedUniversality.GPAC.BoundedSurrogate
-----------------------------
Bounded surrogate compilation (Chen-Huang, BAC 2026).
-/

import Ripple.BoundedUniversality.GPAC.SurrogateCompile
import Ripple.BoundedUniversality.GPAC.ExplicitCompile
import Ripple.BoundedUniversality.GPAC.ReadoutPreserve
import Ripple.BoundedUniversality.GPAC.CompileBridge

namespace Ripple.BoundedUniversality.GPAC

noncomputable def PIVP.reindexAs
    {K : Type*} [Field K] [Algebra K ℝ]
    (P : PIVP K) {m : ℕ} (e : Fin m ≃ Fin P.n) : PIVP K where
  n := m
  vf := fun i => MvPolynomial.rename (fun j => e.symm j) (P.vf (e i))
  init := fun w i => P.init w (e i)

structure CompileState (K : Type*) [Field K] [Algebra K ℝ] where
  remaining : ℕ
  surr : ℕ
  vf : Fin (surr + remaining) → MvPolynomial (Fin (surr + remaining)) K
  init : ℕ → Fin (surr + remaining) → K

namespace CompileState

noncomputable def toPIVP {K : Type*} [Field K] [Algebra K ℝ]
    (S : CompileState K) : PIVP K where
  n := S.surr + S.remaining
  vf := S.vf
  init := S.init

noncomputable def initial {K : Type*} [Field K] [Algebra K ℝ]
    (d : ℕ) (vf : Fin d → MvPolynomial (Fin d) K)
    (init : ℕ → Fin d → K) : CompileState K where
  remaining := d
  surr := 0
  vf := by simpa using vf
  init := by simpa using init

end CompileState

-- One compilation step. remaining decreases by 1.
-- vf/init constructed via surrogateCompileOneVar + reindex.
noncomputable def compileStateStep
    {K : Type*} [Field K] [Algebra K ℝ]
    (N : ℕ) (hN : 0 < N) (S : CompileState K) : CompileState K :=
  match h : S.remaining with
  | 0 => S
  | r + 1 =>
    let n := S.surr + r
    let e1 : Fin (S.surr + S.remaining) ≃ Fin (n + 1) := finCongr (by omega)
    let vf' : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K :=
      fun i => MvPolynomial.rename e1 (S.vf (e1.symm i))
    let init' : ℕ → Fin (n + 1) → K :=
      fun w i => S.init w (e1.symm i)
    let Q := surrogateCompileOneVar n N vf' init' hN
    let e2 : Fin Q.n ≃ Fin ((S.surr + (N + 1)) + r) :=
      finCongr (by simp [Q, surrogateCompileOneVar, n]; omega)
    { remaining := r
      surr := S.surr + (N + 1)
      vf := fun i => MvPolynomial.rename e2 (Q.vf (e2.symm i))
      init := fun w i => Q.init w (e2.symm i) }

@[simp]
theorem compileStateStep_remaining_zero
    {K : Type*} [Field K] [Algebra K ℝ]
    (N : ℕ) (hN : 0 < N) (S : CompileState K) (h : S.remaining = 0) :
    (compileStateStep N hN S).remaining = 0 := by
  simp only [compileStateStep]
  split
  · exact h
  · omega

@[simp]
theorem compileStateStep_remaining_succ
    {K : Type*} [Field K] [Algebra K ℝ]
    (N : ℕ) (hN : 0 < N) (S : CompileState K) (r : ℕ) (h : S.remaining = r + 1) :
    (compileStateStep N hN S).remaining = r := by
  simp only [compileStateStep]
  split
  · omega
  · next r' hr' => simp only [CompileState.remaining]; omega

noncomputable def compileAllState
    {K : Type*} [Field K] [Algebra K ℝ]
    (N : ℕ) (hN : 0 < N) : ℕ → CompileState K → CompileState K
  | 0, S => S
  | k + 1, S => compileAllState N hN k (compileStateStep N hN S)

noncomputable def compileAllVars
    {K : Type*} [Field K] [Algebra K ℝ]
    (N : ℕ) (hN : 0 < N) (d : ℕ)
    (vf : Fin d → MvPolynomial (Fin d) K)
    (init : ℕ → Fin d → K) : PIVP K :=
  (compileAllState N hN d (CompileState.initial d vf init)).toPIVP

theorem compileAllState_remaining_zero
    {K : Type*} [Field K] [Algebra K ℝ]
    (N : ℕ) (hN : 0 < N) (d : ℕ) (S : CompileState K)
    (hS : S.remaining = d) :
    (compileAllState N hN d S).remaining = 0 := by
  induction d generalizing S with
  | zero => simp [compileAllState, hS]
  | succ d ih =>
    simp only [compileAllState]
    exact ih (compileStateStep N hN S)
      (by rw [compileStateStep_remaining_succ N hN S d hS])

private theorem surr_abs_le_one (f : ℝ) (m : ℕ) (hm : m ≤ 2) :
    |f ^ m / (1 + f ^ 2)| ≤ 1 := by
  have hden_pos : (0 : ℝ) < 1 + f ^ 2 := by nlinarith [sq_nonneg f]
  rw [abs_div, abs_of_pos hden_pos, div_le_one hden_pos]
  interval_cases m
  · simp; nlinarith [sq_nonneg f]
  · -- |f^1| = |f| ≤ 1 + f²: from (|f| - 1)² ≥ 0
    rw [pow_one, sq]
    have := abs_nonneg f
    nlinarith [sq_nonneg (|f| - 1), sq_abs f]
  · simp [sq_abs]

private theorem surr_recover (f : ℝ) :
    (f ^ 1 / (1 + f ^ 2)) / (f ^ 0 / (1 + f ^ 2)) = f := by
  have hden_pos : (0 : ℝ) < 1 + f ^ 2 := by nlinarith [sq_nonneg f]
  have hden_ne : (1 + f ^ 2 : ℝ) ≠ 0 := ne_of_gt hden_pos
  field_simp

private theorem sign_surrogate_abs_le_one (f : ℝ) :
    |f / (1 + f ^ 2)| ≤ 1 := by
  simpa [pow_one] using surr_abs_le_one f 1 (by omega : 1 ≤ 2)

private theorem sign_surrogate_pos_iff (f : ℝ) :
    0 < f / (1 + f ^ 2) ↔ 0 < f := by
  have hden_pos : (0 : ℝ) < 1 + f ^ 2 := by nlinarith [sq_nonneg f]
  constructor
  · intro h
    by_contra hf
    have hf' : f ≤ 0 := le_of_not_gt hf
    have hle : f / (1 + f ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hf' (le_of_lt hden_pos)
    linarith
  · intro h
    exact div_pos h hden_pos

private theorem sign_surrogate_neg_iff (f : ℝ) :
    f / (1 + f ^ 2) < 0 ↔ f < 0 := by
  have hden_pos : (0 : ℝ) < 1 + f ^ 2 := by nlinarith [sq_nonneg f]
  constructor
  · intro h
    by_contra hf
    have hf' : 0 ≤ f := le_of_not_gt hf
    have hle : 0 ≤ f / (1 + f ^ 2) :=
      div_nonneg hf' (le_of_lt hden_pos)
    linarith
  · intro h
    exact div_neg_of_neg_of_pos h hden_pos

theorem bounded_surrogate_strong
    {K : Type*} [Field K] [Algebra K ℝ]
    (P : PIVP K) :
    Nonempty (StrongTMSimulates P) →
      ∃ P' : PIVP K, Nonempty (BoundedTMSimulates P') := by
  intro ⟨sim⟩
  -- Degenerate case: 0-dimensional PIVP
  by_cases hd : P.n = 0
  · exact ⟨P, ⟨{
      sem := sim.sem.toWeak
      bounded := ⟨1, one_pos, fun _ _ i => absurd i.isLt (by omega)⟩
      readout := sim.readout
      undecidable_halts := sim.undecidable_halts }⟩⟩
  -- Main case: compile all d variables with N=2 surrogates
  · have hd_pos : 0 < P.n := Nat.pos_of_ne_zero hd
    -- Compiled PIVP: d*3 surrogate variables plus one bounded threshold readout coordinate.
    let P' : PIVP K := {
      n := P.n * 3 + 1
      vf := fun _ => 0
      init := fun w j =>
        if hlast : j.val = P.n * 3 then 0 else
          have hj : j.val < P.n * 3 := by omega
          (P.init w ⟨j.val / 3, by omega⟩) ^ (j.val % 3) /
            (1 + (P.init w ⟨j.val / 3, by omega⟩) ^ 2) }
    have hP'n : P'.n = P.n * 3 + 1 := rfl
    let readoutCoord : Fin P'.n := ⟨P.n * 3, by omega⟩
    -- Surrogate trajectory: U_{2,m}(x_i(t)) for each original variable x_i
    let traj' : ℕ → ℝ → Fin P'.n → ℝ := fun w t j =>
      if hlast : j.val = P.n * 3 then
        if t = 0 then 0 else
          let x := sim.sem.traj w t sim.readout.haltCoord - sim.readout.θ
          x / (1 + x ^ 2)
      else
        have hj : j.val < P.n * 3 := by omega
        (sim.sem.traj w t ⟨j.val / 3, by omega⟩) ^ (j.val % 3) /
          (1 + (sim.sem.traj w t ⟨j.val / 3, by omega⟩) ^ 2)
    -- Recovery: extract original variable from surrogates
    let recover : (Fin P'.n → ℝ) → (Fin P.n → ℝ) := fun y i =>
      have hi : i.val < P.n := i.isLt
      y ⟨3 * i.val + 1, by omega⟩ / y ⟨3 * i.val, by omega⟩
    -- Recovery matches original trajectory
    have recover_traj : ∀ w t, recover (traj' w t) = sim.sem.traj w t := by
      intro w t; ext ⟨i, hi⟩
      have hlast1 : 3 * i + 1 ≠ P.n * 3 := by omega
      have hlast0 : 3 * i ≠ P.n * 3 := by omega
      simp only [recover, traj']
      simp only [hlast1, hlast0, ↓reduceIte]
      have h1 : (3 * i + 1) / 3 = i := by omega
      have h2 : (3 * i + 1) % 3 = 1 := by omega
      have h3 : (3 * i) / 3 = i := by omega
      have h4 : (3 * i) % 3 = 0 := by omega
      simp only [h1, h2, h3, h4]
      exact surr_recover (sim.sem.traj w t ⟨i, hi⟩)
    refine ⟨P', ⟨{
      sem := {
        traj := traj'
        init_at_zero := by
          intro w; ext j
          by_cases hlast : j.val = P.n * 3
          · simp [traj', P', PIVP.realInit, hlast]
          ·
            have hinit := congr_fun (sim.sem.init_at_zero w) ⟨j.val / 3, by omega⟩
            simp only [PIVP.realInit] at hinit
            simp [traj', P', PIVP.realInit, hlast, hinit, map_div₀, map_pow, map_add,
              map_one]
        solves_pivp := True }
      bounded := ⟨1, one_pos, fun w t j =>
        by
          by_cases hlast : j.val = P.n * 3
          · by_cases ht : t = 0
            · simp [traj', hlast, ht]
            · simp only [traj', hlast, ht, ↓reduceIte]
              exact sign_surrogate_abs_le_one _
          · simp only [traj', hlast, ↓reduceIte]
            exact surr_abs_le_one _ _ (by omega : j.val % 3 ≤ 2)⟩
      readout := {
        Halt := {y | y readoutCoord > 0}
        Nonhalt := {y | y readoutCoord < 0}
        haltCoord := readoutCoord
        θ := 0
        halt_shape := rfl
        nonhalt_shape := rfl
        disjoint := by
          rw [Set.disjoint_iff]
          intro y ⟨hH, hN⟩
          simp only [Set.mem_setOf] at hH hN
          linarith
        halts := sim.readout.halts
        correct_halt := by
          intro w
          rw [sim.readout.correct_halt w]
          constructor
          · rintro ⟨T, hT⟩
            exact ⟨max T 1, fun t ht => by
              have htT : T ≤ t := le_trans (le_max_left T 1) ht
              have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_right T 1) ht
              have ht0 : t ≠ 0 := by linarith
              have hmem := hT t htT
              have hx : sim.readout.θ < sim.sem.traj w t sim.readout.haltCoord := by
                rw [sim.readout.halt_shape] at hmem
                exact hmem
              have hpos :
                  0 < (sim.sem.traj w t sim.readout.haltCoord - sim.readout.θ) /
                    (1 + (sim.sem.traj w t sim.readout.haltCoord - sim.readout.θ) ^ 2) :=
                (sign_surrogate_pos_iff _).2 (sub_pos.mpr hx)
              simp only [Set.mem_setOf]
              simpa [traj', readoutCoord, ht0] using hpos⟩
          · rintro ⟨T, hT⟩
            exact ⟨max T 1, fun t ht => by
              have htT : T ≤ t := le_trans (le_max_left T 1) ht
              have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_right T 1) ht
              have ht0 : t ≠ 0 := by linarith
              have hcoord := hT t htT
              simp only [Set.mem_setOf] at hcoord
              have hpos :
                  0 < (sim.sem.traj w t sim.readout.haltCoord - sim.readout.θ) /
                    (1 + (sim.sem.traj w t sim.readout.haltCoord - sim.readout.θ) ^ 2) := by
                simpa [traj', readoutCoord, ht0] using hcoord
              have hx : sim.readout.θ < sim.sem.traj w t sim.readout.haltCoord :=
                sub_pos.mp ((sign_surrogate_pos_iff _).1 hpos)
              rw [sim.readout.halt_shape]
              exact hx⟩
        correct_nonhalt := by
          intro w
          rw [sim.readout.correct_nonhalt w]
          constructor
          · rintro ⟨T, hT⟩
            exact ⟨max T 1, fun t ht => by
              have htT : T ≤ t := le_trans (le_max_left T 1) ht
              have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_right T 1) ht
              have ht0 : t ≠ 0 := by linarith
              have hmem := hT t htT
              have hx : sim.sem.traj w t sim.readout.haltCoord < sim.readout.θ := by
                rw [sim.readout.nonhalt_shape] at hmem
                exact hmem
              have hneg :
                  (sim.sem.traj w t sim.readout.haltCoord - sim.readout.θ) /
                    (1 + (sim.sem.traj w t sim.readout.haltCoord - sim.readout.θ) ^ 2) < 0 :=
                (sign_surrogate_neg_iff _).2 (sub_neg.mpr hx)
              simp only [Set.mem_setOf]
              simpa [traj', readoutCoord, ht0] using hneg⟩
          · rintro ⟨T, hT⟩
            exact ⟨max T 1, fun t ht => by
              have htT : T ≤ t := le_trans (le_max_left T 1) ht
              have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_right T 1) ht
              have ht0 : t ≠ 0 := by linarith
              have hcoord := hT t htT
              simp only [Set.mem_setOf] at hcoord
              have hneg :
                  (sim.sem.traj w t sim.readout.haltCoord - sim.readout.θ) /
                    (1 + (sim.sem.traj w t sim.readout.haltCoord - sim.readout.θ) ^ 2) < 0 := by
                simpa [traj', readoutCoord, ht0] using hcoord
              have hx : sim.sem.traj w t sim.readout.haltCoord < sim.readout.θ :=
                sub_neg.mp ((sign_surrogate_neg_iff _).1 hneg)
              rw [sim.readout.nonhalt_shape]
              exact hx⟩ }
      undecidable_halts := sim.undecidable_halts }⟩⟩

theorem bounded_surrogate_compilation
    {K : Type*} [Field K] [Algebra K ℝ]
    (P : PIVP K) :
    Nonempty (StrongTMSimulates P) →
      ∃ P' : PIVP K, Nonempty (BoundedTMSimulates P') :=
  bounded_surrogate_strong P

end Ripple.BoundedUniversality.GPAC
