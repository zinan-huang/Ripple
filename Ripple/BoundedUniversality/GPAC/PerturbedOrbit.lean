/-
Ripple.BoundedUniversality.GPAC.PerturbedOrbit
--------------------------
T3, the perturbed-orbit impossibility theorem (paper §dichotomy,
thm:pseudo-orbit): δ-pseudo-orbit robustness of an eventual-threshold
verdict implies decidability of the decided predicate — so no
δ-robust simulation of the halting problem exists, even with EXACT
initial data.

Proof note: the PAPER proves this constructively (deterministic
min-successor on a rational mesh, eventual periodicity, cycle
inspection).  The Lean proof is shorter and classical: the rounded
grid orbit from input `w` is a δ-pseudo-orbit whose tail is a
function of the starting CELL alone, the cell grid is finite, and any
function on a finite primcodable type is computable
(`Primrec.dom_finite`) — so the verdict factors through the
finite-advice mechanism of `Ripple.BoundedUniversality.GPAC.Impossibility` and decides
`sourceHalts`.  Same theorem, cheaper proof; the constructive
algorithm remains the right PROSE proof (it exhibits the decider).

Hypotheses are stated for an abstract step map with a Lipschitz
modulus and box invariance on a rational box; the polynomial instance
discharges them.  As in T1, the computability of the input-cell map
is the single honesty hypothesis (`hcell`), discharged by any
explicitly-given encoder.
-/

import Ripple.BoundedUniversality.GPAC.Impossibility

namespace Ripple.BoundedUniversality.GPAC.PerturbedOrbit

open Ripple.BoundedUniversality.Core Ripple.BoundedUniversality.GPAC.Impossibility

/-- Coordinatewise rounding to the `η`-grid (nearest grid point;
real-valued, noncomputable — computability is never needed on the
mathematical side). -/
noncomputable def gridify (η : ℝ) {d : ℕ} (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (⌊v i / η + 1/2⌋ : ℤ) * η

theorem gridify_close (η : ℝ) (hη : 0 < η) {d : ℕ} (v : Fin d → ℝ) :
    ∀ i, |gridify η v i - v i| ≤ η / 2 := by
  intro i
  unfold gridify
  set u := v i / η + 1/2 with hu
  have h1 : (⌊u⌋ : ℝ) ≤ u := Int.floor_le u
  have h2 : u < ⌊u⌋ + 1 := Int.lt_floor_add_one u
  have hvi : v i = (u - 1/2) * η := by
    rw [hu]
    have hcancel : (v i / η + 1/2 - 1/2) = v i / η := by ring
    rw [hcancel, div_mul_cancel₀ _ hη.ne']
  rw [hvi, abs_le]
  constructor
  · have : (⌊u⌋ : ℝ) * η - (u - 1/2) * η = (⌊u⌋ - u + 1/2) * η := by ring
    rw [this]
    nlinarith
  · have : (⌊u⌋ : ℝ) * η - (u - 1/2) * η = (⌊u⌋ - u + 1/2) * η := by ring
    rw [this]
    nlinarith

/-- Two points with equal rounding floors gridify identically. -/
theorem gridify_eq_of_floor_eq (η : ℝ) {d : ℕ} (v w : Fin d → ℝ)
    (h : ∀ i, ⌊v i / η + 1/2⌋ = ⌊w i / η + 1/2⌋) :
    gridify η v = gridify η w := by
  funext i
  unfold gridify
  rw [h i]

/-- **T3 (no δ-robust perturbed simulation).**  Let `Step` be a map of
the box `[-B-1, B+1]^d` into `[-B, B]^d` with Lipschitz modulus `L`,
and suppose the eventual-threshold verdict at coordinate `h` is
δ-robust: for EVERY δ-pseudo-orbit `X` from the (exact, rational,
bounded) encoded input `x₀ w`, the alternative
`∃ N, ∀ n ≥ N, 1/2 + γ < X n h` holds iff `sourceHalts w`.  If the
input-cell map (the rounding floors of the encoder, refined by any
computable `cell` into a finite type) is computable, this contradicts
the undecidability of `sourceHalts`.

Grid mesh: `η` with `(L + 1) * η ≤ δ` and `η ≤ 1`. -/
theorem no_perturbed_robust_simulation
    {F : Type*} [Primcodable F] [Finite F]
    (d : ℕ) (Bb L δ γ η : ℚ)
    (hL : 1 ≤ L) (hδ : 0 < δ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hηδ : (L + 1) * η ≤ δ)
    (Step : (Fin d → ℝ) → Fin d → ℝ)
    (hbox : ∀ x : Fin d → ℝ, (∀ i, |x i| ≤ (Bb : ℝ) + 1) →
      ∀ i, |Step x i| ≤ (Bb : ℝ))
    (hLip : ∀ x y : Fin d → ℝ, (∀ i, |x i| ≤ (Bb : ℝ) + 1) →
      (∀ i, |y i| ≤ (Bb : ℝ) + 1) →
      ∀ r : ℝ, 0 ≤ r → (∀ i, |x i - y i| ≤ r) →
      ∀ i, |Step x i - Step y i| ≤ (L : ℝ) * r)
    (x₀ : ℕ → Fin d → ℚ) (hx₀ : ∀ w i, |x₀ w i| ≤ Bb)
    (h : Fin d)
    (cell : ℕ → F) (hcell : Computable cell)
    (hrefine : ∀ a b, cell a = cell b →
      ∀ i, ⌊x₀ a i / η + 1/2⌋ = ⌊x₀ b i / η + 1/2⌋)
    (hrob : ∀ (w : ℕ) (X : ℕ → Fin d → ℝ),
      X 0 = (fun i => (x₀ w i : ℝ)) →
      (∀ n i, |X (n+1) i - Step (X n) i| ≤ (δ : ℝ)) →
      ((∃ N, ∀ n ≥ N, (1:ℝ)/2 + (γ : ℝ) < X n h) ↔ sourceHalts w)) :
    False := by
  have hηR : (0:ℝ) < (η:ℝ) := by exact_mod_cast hη
  have hη1R : (η:ℝ) ≤ 1 := by exact_mod_cast hη1
  have hLR : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
  have hηδR : ((L:ℝ) + 1) * (η:ℝ) ≤ (δ:ℝ) := by exact_mod_cast hηδ
  have hδR : (0:ℝ) < (δ:ℝ) := by exact_mod_cast hδ
  -- the deterministic grid evolution and the per-input grid orbit
  set G : (Fin d → ℝ) → Fin d → ℝ :=
    fun v => gridify (η:ℝ) (Step v) with hG
  -- starting grid point of input w
  set start : ℕ → Fin d → ℝ :=
    fun w => gridify (η:ℝ) (fun i => (x₀ w i : ℝ)) with hstart
  -- box bounds
  have hhalf : (η:ℝ)/2 ≤ 1 := by linarith
  have hstart_box : ∀ w i, |start w i| ≤ (Bb:ℝ) + 1 := by
    intro w i
    have hc := gridify_close (η:ℝ) hηR (fun i => (x₀ w i : ℝ)) i
    have hx : |(x₀ w i : ℝ)| ≤ (Bb:ℝ) := by exact_mod_cast hx₀ w i
    calc |start w i|
        = |(start w i - (x₀ w i : ℝ)) + (x₀ w i : ℝ)| := by congr 1; ring
      _ ≤ |start w i - (x₀ w i : ℝ)| + |(x₀ w i : ℝ)| := abs_add_le _ _
      _ ≤ (η:ℝ)/2 + (Bb:ℝ) := by
          have : |start w i - (x₀ w i : ℝ)| ≤ (η:ℝ)/2 := hc
          linarith [hx]
      _ ≤ (Bb:ℝ) + 1 := by linarith
  have hG_box : ∀ v : Fin d → ℝ, (∀ i, |v i| ≤ (Bb:ℝ) + 1) →
      ∀ i, |G v i| ≤ (Bb:ℝ) + 1 := by
    intro v hv i
    have hSv := hbox v hv i
    have hc := gridify_close (η:ℝ) hηR (Step v) i
    calc |G v i|
        = |(G v i - Step v i) + Step v i| := by congr 1; ring
      _ ≤ |G v i - Step v i| + |Step v i| := abs_add_le _ _
      _ ≤ (η:ℝ)/2 + (Bb:ℝ) := by
          have : |G v i - Step v i| ≤ (η:ℝ)/2 := hc
          linarith [hSv]
      _ ≤ (Bb:ℝ) + 1 := by linarith
  have horbit_box : ∀ (w : ℕ) (n : ℕ) (i : Fin d),
      |G^[n] (start w) i| ≤ (Bb:ℝ) + 1 := by
    intro w n
    induction n with
    | zero => exact fun i => hstart_box w i
    | succ k ih =>
      intro i
      rw [Function.iterate_succ_apply']
      exact hG_box _ ih i
  -- the pseudo-orbit for input w: exact start, then the grid orbit
  -- shifted by one application of G
  set X : ℕ → ℕ → Fin d → ℝ :=
    fun w n => if n = 0 then (fun i => (x₀ w i : ℝ))
               else G^[n] (start w) with hX
  have hX0 : ∀ w, X w 0 = fun i => (x₀ w i : ℝ) := by
    intro w; simp [hX]
  have hXpseudo : ∀ w n i, |X w (n+1) i - Step (X w n) i| ≤ (δ:ℝ) := by
    intro w n i
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- first step: |G(start) - Step(x₀)| ≤ η/2 + L·(η/2) ≤ δ
      subst hn
      simp only [hX, if_pos rfl, if_neg (Nat.one_ne_zero)]
      have h1 : |G (start w) i - Step (start w) i| ≤ (η:ℝ)/2 :=
        gridify_close (η:ℝ) hηR (Step (start w)) i
      have hclose : ∀ j, |start w j - (x₀ w j : ℝ)| ≤ (η:ℝ)/2 :=
        fun j => gridify_close (η:ℝ) hηR (fun i => (x₀ w i : ℝ)) j
      have hx0box : ∀ j, |(x₀ w j : ℝ)| ≤ (Bb:ℝ) + 1 := by
        intro j
        have : |(x₀ w j : ℝ)| ≤ (Bb:ℝ) := by exact_mod_cast hx₀ w j
        linarith
      have h2 : |Step (start w) i - Step (fun j => (x₀ w j : ℝ)) i|
          ≤ (L:ℝ) * ((η:ℝ)/2) :=
        hLip (start w) (fun j => (x₀ w j : ℝ))
          (hstart_box w) hx0box ((η:ℝ)/2) (by linarith) hclose i
      calc |G (start w) i - Step (fun j => (x₀ w j : ℝ)) i|
          = |(G (start w) i - Step (start w) i)
              + (Step (start w) i - Step (fun j => (x₀ w j : ℝ)) i)| := by
            congr 1; ring
        _ ≤ |G (start w) i - Step (start w) i|
              + |Step (start w) i - Step (fun j => (x₀ w j : ℝ)) i| :=
            abs_add_le _ _
        _ ≤ (η:ℝ)/2 + (L:ℝ) * ((η:ℝ)/2) := by linarith
        _ = ((L:ℝ) + 1) * (η:ℝ) / 2 := by ring
        _ ≤ (δ:ℝ) := by linarith
    · -- later steps: |G^[n+1](start) - Step(G^[n](start))| ≤ η/2 ≤ δ
      have hne : n ≠ 0 := by omega
      simp only [hX, if_neg (Nat.succ_ne_zero n), if_neg hne]
      rw [Function.iterate_succ_apply']
      have := gridify_close (η:ℝ) hηR (Step (G^[n] (start w))) i
      calc |G (G^[n] (start w)) i - Step (G^[n] (start w)) i| ≤ (η:ℝ)/2 :=
            this
        _ ≤ (δ:ℝ) := by nlinarith
  -- the verdict factors through the starting grid point, hence
  -- through the input cell
  have hfac : ∀ a b, cell a = cell b → (sourceHalts a ↔ sourceHalts b) := by
    intro a b hab
    have hstarteq : start a = start b := by
      apply gridify_eq_of_floor_eq
      intro i
      have := hrefine a b hab i
      -- transfer the ℚ-floor equality to ℝ
      have hcast : ∀ (w : ℕ),
          ⌊(x₀ w i : ℝ) / (η:ℝ) + 1/2⌋ = ⌊x₀ w i / η + 1/2⌋ := by
        intro w
        rw [show (x₀ w i : ℝ) / (η:ℝ) + 1/2
              = ((x₀ w i / η + 1/2 : ℚ) : ℝ) by push_cast; ring]
        exact Rat.floor_cast _
      rw [hcast a, hcast b, this]
    have htail : (∃ N, ∀ n ≥ N, (1:ℝ)/2 + (γ:ℝ) < X a n h) ↔
        (∃ N, ∀ n ≥ N, (1:ℝ)/2 + (γ:ℝ) < X b n h) := by
      constructor
      all_goals
        rintro ⟨N, hN⟩
        refine ⟨max N 1, fun n hn => ?_⟩
        have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
        have hnN : N ≤ n := le_trans (le_max_left N 1) hn
        have hne : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn1
        have := hN n hnN
      · -- a → b direction: rewrite the orbit through hstarteq
        simp only [hX, if_neg hne] at this ⊢
        rwa [← hstarteq]
      · simp only [hX, if_neg hne] at this ⊢
        rwa [hstarteq]
    rw [← hrob a (X a) (hX0 a) (hXpseudo a),
        ← hrob b (X b) (hX0 b) (hXpseudo b)]
    exact htail
  -- finite advice closes it
  exact sourceHalts_noBoolDecider
    (hasDecider_of_factors_through_finite sourceHalts cell hcell hfac)

end Ripple.BoundedUniversality.GPAC.PerturbedOrbit
