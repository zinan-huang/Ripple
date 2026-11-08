/-
  Ripple.LPP.Computation — the computability predicates of [LPP] Definition 9

  [LPP] = Huang, Huls, "Computing real numbers with large-population protocols having a
  continuum of equilibria", DNA 28 (2022); PDF `Huang-Huls.pdf` in the Bounded `ref/` folder.

  Definition 9 (p. 11) has two clauses that matter here:

  * the PLPP clause: a probabilistic large-population protocol (Definition 6, p. 9) with
    rational transition probabilities `α i j k l`, its balance equation (5) and ODE (6),
    rational initial fractions on the simplex, and a marked set whose fraction tends to `ν`;
  * the LPP clause: the same with a deterministic protocol, whose balance equation is
    Definition 5, Equation (4), with `δ q₁ q₂ q₃ q₄ ∈ {0, 1}`.

  The PLPP clause is `IsPLPPComputable`, built on the existing `PLPPTransitions` and
  `PLPPContinuumComputation`. The deterministic clause is `IsLPPComputable`, built on
  `LPPTransitions` (a transition function `Q × Q → Q × Q`). [LPP] Theorem 17 (= [BFK] Lemma 4)
  says the two predicates agree; it is proved in `Ripple.LPP.Determinization`.

  Reading notes (also in `docs/refactor/S1.md` §1.3):
  * Definition 6 literally asks `α i j k l > 0` for every output pair; Construction 1 and
    Theorem 16 (pp. 21-22) produce zero entries and idle rules, so the intended condition is
    `0 ≤ α`, which `PLPPTransitions.nonneg` encodes.
  * Definition 9 asks for initial values `rᵢ ∈ ℚ ∩ [0, 1]` ("positive" in the text, but the
    discussion right after it initializes species to zero), and `x(t) ∈ [0, 1]ⁿ`; both follow
    from the fields `init_rational`, `init_nonneg`, `init_simplex`, `simplex`, `nonneg` of
    `PLPPContinuumComputation`.
-/

import Ripple.LPP.Stochastic

namespace Ripple

/-! ## The PLPP clause of [LPP] Definition 9 -/

/-- A PLPP computation of `ν` ([LPP] Definition 6 and Definition 9, PLPP clause): a number of
states `n`, a rational transition table `tr` (Definition 6, with `0 ≤ α`), a marked set of
states, and a trajectory of the balance-equation ODE (Equations (5), (6)) from a rational
initial point of the simplex whose marked fraction tends to `ν`. -/
structure PLPPComputation (ν : ℝ) where
  /-- Number of states. -/
  n : ℕ
  /-- The rational transition probabilities (Definition 6). -/
  tr : PLPPTransitions n
  /-- The marked states `M` of Definition 9. -/
  marked : Finset (Fin n)
  /-- The trajectory of the balance equation and its convergence (Definition 9). -/
  comp : PLPPContinuumComputation tr marked ν

/-- `ν` is computable by a PLPP ([LPP] Definition 9, PLPP clause). -/
def IsPLPPComputable (ν : ℝ) : Prop := Nonempty (PLPPComputation ν)

/-! ## The deterministic clause: [LPP] Definition 5 -/

/-- A deterministic large-population protocol on `n` states ([LPP] Definition 5): every ordered
pair of states `(q₁, q₂)` reacts to exactly one ordered pair `step q₁ q₂ = (q₃, q₄)`. A pair
without a rule in the paper's rule set is the null reaction `step q₁ q₂ = (q₁, q₂)` ("we interpret
`(q₁, q₂)` as a null reaction and the agents remain unchanged", p. 9). The ordered pairs
`(q₁, q₂)` and `(q₂, q₁)` may react differently (the paper's asymmetric convention). -/
structure LPPTransitions (n : ℕ) where
  /-- The transition function `(q₁, q₂) ↦ (q₃, q₄)`. -/
  step : Fin n → Fin n → Fin n × Fin n

namespace LPPTransitions

variable {n : ℕ} (T : LPPTransitions n)

/-- The coefficient `δ q₁ q₂ q₃ q₄` of [LPP] Definition 5: `1` if `(q₁, q₂) → (q₃, q₄)` is the
rule of the protocol, `0` otherwise. -/
def δ (q₁ q₂ q₃ q₄ : Fin n) : ℕ := if T.step q₁ q₂ = (q₃, q₄) then 1 else 0

/-- `δ ∈ {0, 1}`, as Definition 5 requires. -/
theorem δ_eq_zero_or_one (q₁ q₂ q₃ q₄ : Fin n) :
    T.δ q₁ q₂ q₃ q₄ = 0 ∨ T.δ q₁ q₂ q₃ q₄ = 1 := by
  unfold δ
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The balance equation of a deterministic LPP, [LPP] Definition 5, Equation (4), written
coordinatewise:
`b(x)_r = Σ_{q₁,q₂} x_{q₁} x_{q₂} (-[q₁ = r] - [q₂ = r] + Σ_{q₃,q₄} δ q₁ q₂ q₃ q₄ ([q₃ = r] + [q₄ = r]))`. -/
def balanceField (x : Fin n → ℝ) (r : Fin n) : ℝ :=
  ∑ q₁, ∑ q₂, x q₁ * x q₂ *
    (-(if q₁ = r then 1 else 0) - (if q₂ = r then 1 else 0) +
      ∑ q₃, ∑ q₄, (T.δ q₁ q₂ q₃ q₄ : ℝ) *
        ((if q₃ = r then 1 else 0) + (if q₄ = r then 1 else 0)))

/-- A deterministic LPP viewed as a PLPP whose probabilities are the `δ ∈ {0, 1}` of
Definition 5. -/
def toPLPP : PLPPTransitions n where
  α i j k l := (T.δ i j k l : ℚ)
  nonneg i j k l := Nat.cast_nonneg _
  sum_one i j := by
    rw [← Fintype.sum_prod_type' (f := fun k l => ((T.δ i j k l : ℕ) : ℚ))]
    simp only [δ, Prod.mk.eta, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_ite_eq]
    simp

theorem toPLPP_α (i j k l : Fin n) : T.toPLPP.α i j k l = (T.δ i j k l : ℚ) := rfl

/-- The PLPP balance field of `T.toPLPP` (Equation (5)) is the deterministic balance equation
of Definition 5 (Equation (4)). So a `PLPPContinuumComputation T.toPLPP` is a trajectory of
Equation (4). -/
theorem toPLPP_balanceField : T.toPLPP.balanceField = T.balanceField := by
  funext x r
  unfold PLPPTransitions.balanceField balanceField
  have hδ : ∀ q₁ q₂ : Fin n,
      (∑ q₃, ∑ q₄, (T.δ q₁ q₂ q₃ q₄ : ℝ) *
          ((if q₃ = r then 1 else 0) + (if q₄ = r then 1 else 0))) =
        ∑ k, (T.toPLPP.α q₁ q₂ r k : ℝ) + ∑ k, (T.toPLPP.α q₁ q₂ k r : ℝ) := by
    intro q₁ q₂
    simp only [toPLPP_α, Rat.cast_natCast, mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single r (fun b _ hb => by simp [hb]) (by simp)]
      simp
    · apply Finset.sum_congr rfl
      intro q₃ _
      rw [Finset.sum_eq_single r (fun b _ hb => by simp [hb]) (by simp)]
      simp
  simp_rw [hδ]
  have h1 : (∑ q₁ : Fin n, ∑ q₂ : Fin n, x q₁ * x q₂ * (if q₁ = r then (1 : ℝ) else 0)) =
      x r * ∑ k, x k := by
    rw [Finset.sum_eq_single r (fun b _ hb => by simp [hb]) (by simp), Finset.mul_sum]
    simp
  have h2 : (∑ q₁ : Fin n, ∑ q₂ : Fin n, x q₁ * x q₂ * (if q₂ = r then (1 : ℝ) else 0)) =
      x r * ∑ k, x k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q₁ _
    rw [Finset.sum_eq_single r (fun b _ hb => by simp [hb]) (by simp)]
    simp only [if_true, mul_one]
    ring
  have hsplit : ∀ q₁ q₂ : Fin n,
      x q₁ * x q₂ * (-(if q₁ = r then (1 : ℝ) else 0) - (if q₂ = r then 1 else 0) +
          (∑ k, (T.toPLPP.α q₁ q₂ r k : ℝ) + ∑ k, (T.toPLPP.α q₁ q₂ k r : ℝ))) =
        x q₁ * x q₂ * (∑ k, (T.toPLPP.α q₁ q₂ r k : ℝ) + ∑ k, (T.toPLPP.α q₁ q₂ k r : ℝ)) -
          (x q₁ * x q₂ * (if q₁ = r then (1 : ℝ) else 0) +
            x q₁ * x q₂ * (if q₂ = r then (1 : ℝ) else 0)) := by
    intro q₁ q₂
    ring
  simp_rw [hsplit, Finset.sum_sub_distrib, Finset.sum_add_distrib, h1, h2]
  ring

end LPPTransitions

/-- A deterministic LPP computation of `ν` ([LPP] Definition 5 and Definition 9, LPP clause):
a deterministic transition table, a marked set, and a trajectory of the balance equation (4)
from a rational initial point of the simplex whose marked fraction tends to `ν`. The trajectory
is recorded as a `PLPPContinuumComputation` of `tr.toPLPP`, whose balance field is Equation (4)
by `LPPTransitions.toPLPP_balanceField`. -/
structure LPPComputation (ν : ℝ) where
  /-- Number of states. -/
  n : ℕ
  /-- The deterministic transition function (Definition 5). -/
  tr : LPPTransitions n
  /-- The marked states `M` of Definition 9. -/
  marked : Finset (Fin n)
  /-- The trajectory of the balance equation (4) and its convergence (Definition 9). -/
  comp : PLPPContinuumComputation tr.toPLPP marked ν

/-- `ν` is computable by a (deterministic) LPP ([LPP] Definition 9, LPP clause). -/
def IsLPPComputable (ν : ℝ) : Prop := Nonempty (LPPComputation ν)

/-- A deterministic LPP computation is a PLPP computation (`δ ∈ {0,1}` are probabilities). -/
def LPPComputation.toPLPPComputation {ν : ℝ} (c : LPPComputation ν) : PLPPComputation ν :=
  ⟨c.n, c.tr.toPLPP, c.marked, c.comp⟩

theorem IsLPPComputable.isPLPPComputable {ν : ℝ} (h : IsLPPComputable ν) :
    IsPLPPComputable ν :=
  h.elim fun c => ⟨c.toPLPPComputation⟩

namespace LPPTransitions

/-- The idle protocol: every ordered pair reacts to itself (only null reactions). -/
def idle (n : ℕ) : LPPTransitions n := ⟨fun i j => (i, j)⟩

/-- The balance field of the idle protocol vanishes. -/
theorem idle_balanceField (n : ℕ) : (idle n).balanceField = 0 := by
  funext x r
  unfold balanceField
  simp only [Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro q₁ _
  apply Finset.sum_eq_zero
  intro q₂ _
  have hinner : (∑ q₃, ∑ q₄, ((idle n).δ q₁ q₂ q₃ q₄ : ℝ) *
      ((if q₃ = r then 1 else 0) + (if q₄ = r then 1 else 0))) =
        (if q₁ = r then 1 else 0) + (if q₂ = r then 1 else 0) := by
    rw [Finset.sum_eq_single q₁]
    · rw [Finset.sum_eq_single q₂]
      · simp [δ, idle]
      · intro b _ hb
        simp [δ, idle, Ne.symm hb]
      · simp
    · intro b _ hb
      apply Finset.sum_eq_zero
      intro c _
      simp [δ, idle, Ne.symm hb]
    · simp
  rw [hinner]
  ring

end LPPTransitions

/-- Every rational `q ∈ [0, 1]` is computed by a deterministic LPP: the idle protocol on two
states started at `(q, 1 - q)`, marking the first state. -/
theorem isLPPComputable_rat (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    IsLPPComputable (q : ℝ) := by
  let v : Fin 2 → ℝ := fun i => if i = 0 then (q : ℝ) else 1 - q
  have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast h0
  have hq1 : (q : ℝ) ≤ 1 := by exact_mod_cast h1
  have hsum : ∑ i, v i = 1 := by simp [v, Fin.sum_univ_two]
  have hnn : ∀ i, 0 ≤ v i := by
    intro i
    simp only [v]
    split_ifs <;> linarith
  refine ⟨⟨2, LPPTransitions.idle 2, {0}, ?_⟩⟩
  exact
    { sol := fun _ => v
      init_rational := by
        intro i
        by_cases hi : i = 0
        · exact ⟨q, by simp [v, hi]⟩
        · exact ⟨1 - q, by simp [v, hi]⟩
      init_simplex := hsum
      init_nonneg := hnn
      simplex := fun _ _ => hsum
      nonneg := fun _ _ => hnn
      ode := by
        intro t _
        rw [LPPTransitions.toPLPP_balanceField, LPPTransitions.idle_balanceField]
        simpa using hasDerivAt_const t v
      readout_tendsto := by
        simp only [Finset.sum_singleton]
        simpa [v] using tendsto_const_nhds }

/-- The value of a PLPP computation lies in `[0, 1]` (the marked fraction of a point of the
simplex). -/
theorem IsPLPPComputable.mem_Icc {ν : ℝ} (h : IsPLPPComputable ν) : ν ∈ Set.Icc 0 1 := by
  obtain ⟨⟨n, tr, M, C⟩⟩ := h
  have hlo : ∀ t, 0 ≤ t → 0 ≤ ∑ i ∈ M, C.sol t i := fun t ht =>
    Finset.sum_nonneg fun i _ => C.nonneg t ht i
  have hhi : ∀ t, 0 ≤ t → ∑ i ∈ M, C.sol t i ≤ 1 := fun t ht => by
    rw [← C.simplex t ht]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ M)
      fun i _ _ => C.nonneg t ht i
  have hev : ∀ᶠ t in Filter.atTop, (∑ i ∈ M, C.sol t i) ∈ Set.Icc (0 : ℝ) 1 :=
    Filter.eventually_atTop.mpr ⟨0, fun t ht => ⟨hlo t ht, hhi t ht⟩⟩
  exact isClosed_Icc.mem_of_tendsto C.readout_tendsto hev

end Ripple
