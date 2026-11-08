/-
  Ripple.LPP.R2Trick — Protocol-level PP → NAP bridge via the r²-trick,
  parameterized over `QuadField`.

  This file assembles the protocol-level PP→NAP connection at both the
  QuadField and SynPPBalance layers:

  • Primary layer (`QuadField`): any slack-structured QuadField on `Fin n`
    induces an r²-lifted field on `Fin (n+1)` with slack slot 0. The
    per-pair NAP split wrappers consume the newer
    `quad_r2_nap_split_of_slackStructured` theorem, so the per-pair
    hypothesis is simply positivity of the target coefficient, with NSS
    yielding the disjunctive off-self condition automatically.

  • Compatibility layer (`SynPPBalance`): the original PP-level r²-lifted
    field factors through `eq.toQuadField`. The PP-specific prod/loss
    decomposition (`r2Prod`, `r2Loss`, `r2ChainRuleSum_eq_raw_sub_loss`)
    and the ODE-chain-rule content (`HasDerivAt`) live in this layer.

  References: BD Theorem 11.2, Note 14. The monomial-level primitive is
  `Ripple.pp_r2_nap_split`; the reconstruction identity is
  `Ripple.splitRate_reconstructs`.
-/

import Ripple.LPP.NAP

namespace Ripple

/-! ## Projection helpers

The n+1-variable r²-system indexes slack at slot 0 and the original n
species at slots 1 … n. The map `Fin n → Fin (n+1)` is `Fin.succ`;
projecting back drops the slack slot. -/

/-- Project an (n+1)-state down to the n original species by dropping slot 0. -/
noncomputable def origProj {n : ℕ} (x : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i => x i.succ

/-! ## Raw chain-rule monomial (QuadField layer)

A positive coefficient `F.coeff source a b` in the original `QuadField F`
contributes, after the `x_0²` lift and chain rule for `v̇_α = d/dt (x^α)`,
a degree-6 monomial weighted by `(α source.succ) · F.coeff source a b`.
For non-source slack slots the `r2PPMonomial` exponent lives in `Fin (n+1)`
with slack at slot 0. -/

/-- Chain-rule exponent vector for a non-slack-source `(source, a, b)`
triple, with slack `0 : Fin (n+1)` and the original species lifted via
`Fin.succ`. -/
def r2ChainDelta {n : ℕ} (α : Fin (n + 1) → ℕ)
    (source a b : Fin n) : Fin (n + 1) → ℕ :=
  fun k => (α k - if k = source.succ then 1 else 0) +
    r2PPMonomial (0 : Fin (n + 1)) a.succ b.succ k

/-- Chain-rule coefficient at the QuadField level. Can be negative
whenever `F.coeff source a b < 0`; we tag splits only at positive
entries. -/
def QuadField.r2ChainCoeff {n : ℕ} (F : QuadField n) (α : Fin (n + 1) → ℕ)
    (source a b : Fin n) : ℚ :=
  (α source.succ : ℚ) * F.coeff source a b

/-- Chain-rule coefficient at the SynPPBalance level (always nonneg). -/
def SynPPBalance.r2ChainCoeff {n : ℕ} (eq : SynPPBalance n)
    (α : Fin (n + 1) → ℕ) (source a b : Fin n) : ℚ :=
  (α source.succ : ℚ) * eq.coeff source a b

theorem SynPPBalance.r2ChainCoeff_nonneg {n : ℕ} (eq : SynPPBalance n)
    (α : Fin (n + 1) → ℕ) (source a b : Fin n) :
    0 ≤ eq.r2ChainCoeff α source a b := by
  unfold SynPPBalance.r2ChainCoeff
  exact mul_nonneg (by exact_mod_cast Nat.zero_le _) (eq.coeff_nonneg _ _ _)

/-! ## Per-pair NAP split (QuadField layer)

Given a slack-structured `QuadField F` on `Fin n` and a positive entry
`F.coeff source a b > 0`, we lift to `Fin (n+1)` (slack at slot 0) and
invoke `quad_r2_nap_split_of_slackStructured` on the r²-lifted QuadField
`F.lambdaLift j₀ lam`. The per-pair hypothesis collapses to positivity;
NSS handles the disjunctive off-self condition automatically. -/

/-- Chain-rule target for positive entries in a non-slack-source `(source, a, b)`
triple: after lifting to `Fin (n+1)` with slack slot `0`, the r²-lifted
chain-rule monomial has exponent `r2ChainDelta α source a b`. -/
theorem QuadField.r2ChainDelta_shape {n : ℕ}
    (α : Fin (n + 1) → ℕ) (source a b : Fin n) :
    r2ChainDelta α source a b =
      fun k => (α k - if k = source.succ then 1 else 0) +
        r2PPMonomial (0 : Fin (n + 1)) a.succ b.succ k := by
  funext k; rfl

/-- Per-pair NAP split for a non-slack-source chain-rule monomial at the
SynPPBalance level: the disjunctive off-self hypothesis `a ≠ source ∨
b ≠ source` is the weakest condition the underlying `pp_r2_nap_split`
theorem needs (once a, b ≠ slack, which is automatic for `.succ`). -/
noncomputable def r2MonomialSplit {n : ℕ}
    (α : Fin (n + 1) → ℕ) (hα : IsCubedIndex α)
    (source a b : Fin n) (hsrc : 0 < α source.succ)
    (hab : a ≠ source ∨ b ≠ source) :
    MonomialSplit (r2ChainDelta α source a b) := by
  -- Apply `pp_r2_nap_split` at n+1 species, slack zero = 0.
  have hza : a.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero _
  have hzb : b.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero _
  have hnoself : source.succ ≠ (0 : Fin (n + 1)) →
      a.succ ≠ source.succ ∨ b.succ ≠ source.succ := by
    intro _
    rcases hab with ha | hb
    · exact Or.inl (fun h => ha (Fin.succ_injective _ h))
    · exact Or.inr (fun h => hb (Fin.succ_injective _ h))
  have hexists :=
    pp_r2_nap_split α hα (0 : Fin (n + 1)) source.succ a.succ b.succ
      hsrc hza hzb hnoself
  -- Transport across `r2ChainDelta` = the δ produced by pp_r2_nap_split.
  exact Classical.choose hexists

theorem r2MonomialSplit_balanced {n : ℕ}
    (α : Fin (n + 1) → ℕ) (hα : IsCubedIndex α)
    (source a b : Fin n) (hsrc : 0 < α source.succ)
    (hab : a ≠ source ∨ b ≠ source) :
    (r2MonomialSplit α hα source a b hsrc hab).balanced := by
  unfold r2MonomialSplit
  have hza : a.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero _
  have hzb : b.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero _
  have hnoself : source.succ ≠ (0 : Fin (n + 1)) →
      a.succ ≠ source.succ ∨ b.succ ≠ source.succ := by
    intro _
    rcases hab with ha | hb
    · exact Or.inl (fun h => ha (Fin.succ_injective _ h))
    · exact Or.inr (fun h => hb (Fin.succ_injective _ h))
  exact (Classical.choose_spec
    (pp_r2_nap_split α hα (0 : Fin (n + 1)) source.succ a.succ b.succ
      hsrc hza hzb hnoself)).1

theorem r2MonomialSplit_nonAutocatalytic {n : ℕ}
    (α : Fin (n + 1) → ℕ) (hα : IsCubedIndex α)
    (source a b : Fin n) (hsrc : 0 < α source.succ)
    (hab : a ≠ source ∨ b ≠ source) :
    (r2MonomialSplit α hα source a b hsrc hab).nonAutocatalytic α := by
  unfold r2MonomialSplit
  have hza : a.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero _
  have hzb : b.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero _
  have hnoself : source.succ ≠ (0 : Fin (n + 1)) →
      a.succ ≠ source.succ ∨ b.succ ≠ source.succ := by
    intro _
    rcases hab with ha | hb
    · exact Or.inl (fun h => ha (Fin.succ_injective _ h))
    · exact Or.inr (fun h => hb (Fin.succ_injective _ h))
  exact (Classical.choose_spec
    (pp_r2_nap_split α hα (0 : Fin (n + 1)) source.succ a.succ b.succ
      hsrc hza hzb hnoself)).2

/-! ## Slack-source chain-rule contribution

When `source = 0` (slack), the `r2PPMonomial` exponent `μ_{0, source.succ, k.succ}`
has two slack factors automatically, and `pp_r2_nap_split` dispatches via
the `source = zero` case with no off-self hypothesis needed. -/

/-- Chain-rule exponent vector for a slack-source `(source, k)` pair. -/
def r2SlackChainDelta {n : ℕ} (α : Fin (n + 1) → ℕ)
    (source k : Fin n) : Fin (n + 1) → ℕ :=
  fun i => (α i - if i = 0 then 1 else 0) +
    r2PPMonomial (0 : Fin (n + 1)) source.succ k.succ i

/-- Slack-source chain-rule coefficient (derived from `SynPPBalance.toField`'s
`-2 x_r (Σ x)` degradation: the `2` is the degradation rate). -/
def r2SlackChainCoeff {n : ℕ} (α : Fin (n + 1) → ℕ) : ℚ :=
  2 * (α 0 : ℚ)

theorem r2SlackChainCoeff_nonneg {n : ℕ} (α : Fin (n + 1) → ℕ) :
    0 ≤ r2SlackChainCoeff α := by
  unfold r2SlackChainCoeff; positivity

noncomputable def r2SlackMonomialSplit {n : ℕ}
    (α : Fin (n + 1) → ℕ) (hα : IsCubedIndex α)
    (source k : Fin n) (hsrc : 0 < α 0) :
    MonomialSplit (r2SlackChainDelta α source k) := by
  -- Slack source: apply `pp_r2_nap_split` with source = 0, which dispatches
  -- via the `source = zero` case (no off-self disjunction needed).
  have hza : source.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero _
  have hzb : k.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero _
  have hnoself : (0 : Fin (n + 1)) ≠ 0 →
      source.succ ≠ 0 ∨ k.succ ≠ 0 :=
    fun h => (h rfl).elim
  have hexists :=
    pp_r2_nap_split α hα (0 : Fin (n + 1)) 0 source.succ k.succ
      hsrc hza hzb hnoself
  exact Classical.choose hexists

theorem r2SlackMonomialSplit_balanced {n : ℕ}
    (α : Fin (n + 1) → ℕ) (hα : IsCubedIndex α)
    (source k : Fin n) (hsrc : 0 < α 0) :
    (r2SlackMonomialSplit α hα source k hsrc).balanced := by
  unfold r2SlackMonomialSplit
  have hza : source.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero _
  have hzb : k.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero _
  have hnoself : (0 : Fin (n + 1)) ≠ 0 →
      source.succ ≠ 0 ∨ k.succ ≠ 0 :=
    fun h => (h rfl).elim
  exact (Classical.choose_spec
    (pp_r2_nap_split α hα (0 : Fin (n + 1)) 0 source.succ k.succ
      hsrc hza hzb hnoself)).1

theorem r2SlackMonomialSplit_nonAutocatalytic {n : ℕ}
    (α : Fin (n + 1) → ℕ) (hα : IsCubedIndex α)
    (source k : Fin n) (hsrc : 0 < α 0) :
    (r2SlackMonomialSplit α hα source k hsrc).nonAutocatalytic α := by
  unfold r2SlackMonomialSplit
  have hza : source.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero _
  have hzb : k.succ ≠ (0 : Fin (n + 1)) := Fin.succ_ne_zero _
  have hnoself : (0 : Fin (n + 1)) ≠ 0 →
      source.succ ≠ 0 ∨ k.succ ≠ 0 :=
    fun h => (h rfl).elim
  exact (Classical.choose_spec
    (pp_r2_nap_split α hα (0 : Fin (n + 1)) 0 source.succ k.succ
      hsrc hza hzb hnoself)).2

/-- Per-pair NAP reconstruction identity for slack-source chain terms. -/
theorem r2SlackPair_reconstructs {n : ℕ}
    (α : Fin (n + 1) → ℕ) (hα : IsCubedIndex α)
    (source k : Fin n) (hsrc : 0 < α 0) (x : Fin (n + 1) → ℝ) :
    (splitRate (r2SlackChainCoeff α)
        (r2SlackMonomialSplit α hα source k hsrc) : ℝ) *
      cubedLift (r2SlackMonomialSplit α hα source k hsrc).β x *
      cubedLift (r2SlackMonomialSplit α hα source k hsrc).γ x =
    (r2SlackChainCoeff α : ℝ) *
      rawMonomial (r2SlackChainDelta α source k) x :=
  splitRate_reconstructs _ _ x

/-- Aggregated slack-source NAP identity over all `(source, k)` pairs. -/
theorem r2_slack_chain_nap_eq_raw {n : ℕ}
    (α : Fin (n + 1) → ℕ) (hα : IsCubedIndex α)
    (hsrc : 0 < α 0) (x : Fin (n + 1) → ℝ) :
    (∑ sk : Fin n × Fin n,
        (splitRate (r2SlackChainCoeff α)
            (r2SlackMonomialSplit α hα sk.1 sk.2 hsrc) : ℝ) *
          cubedLift (r2SlackMonomialSplit α hα sk.1 sk.2 hsrc).β x *
          cubedLift (r2SlackMonomialSplit α hα sk.1 sk.2 hsrc).γ x)
      =
    (∑ sk : Fin n × Fin n,
        (r2SlackChainCoeff α : ℝ) *
          rawMonomial (r2SlackChainDelta α sk.1 sk.2) x) := by
  refine Finset.sum_congr rfl ?_
  intro sk _
  exact r2SlackPair_reconstructs α hα sk.1 sk.2 hsrc x

theorem r2SlackMonomialSplit_splitRate_nonneg {n : ℕ}
    (α : Fin (n + 1) → ℕ) (hα : IsCubedIndex α)
    (source k : Fin n) (hsrc : 0 < α 0) :
    0 ≤ splitRate (r2SlackChainCoeff α)
      (r2SlackMonomialSplit α hα source k hsrc) :=
  splitRate_nonneg (r2SlackChainCoeff_nonneg α) _

/-! ## Support filter for non-slack sources -/

abbrev NonSlackSourceSupp {n : ℕ} (α : Fin (n + 1) → ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun source : Fin n => 0 < α source.succ)

/-! ## r²-lifted ODE field (QuadField layer)

Given a `QuadField F` on `Fin n`, the r²-lifted field on `Fin (n+1)`
scales every production monomial by `x_0²` and enforces conservation
by setting the slack slot to the negated sum of all other slots. This
is the universal algebraic form; it specializes to the PP-specific
prod/loss decomposition only via `SynPPBalance.toField`. -/

noncomputable def QuadField.r2Field {n : ℕ} (F : QuadField n) :
    (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ :=
  fun x => Fin.cases
    (-∑ i : Fin n, (x 0) ^ 2 * F.toField (origProj x) i)
    (fun i => (x 0) ^ 2 * F.toField (origProj x) i)

theorem QuadField.r2Field_zero {n : ℕ} (F : QuadField n)
    (x : Fin (n + 1) → ℝ) :
    F.r2Field x 0 = -∑ i : Fin n, (x 0) ^ 2 * F.toField (origProj x) i := by
  simp [QuadField.r2Field]

theorem QuadField.r2Field_succ {n : ℕ} (F : QuadField n)
    (x : Fin (n + 1) → ℝ) (i : Fin n) :
    F.r2Field x i.succ = (x 0) ^ 2 * F.toField (origProj x) i := by
  simp [QuadField.r2Field]

theorem QuadField.r2Field_conservative {n : ℕ} (F : QuadField n)
    (x : Fin (n + 1) → ℝ) :
    ∑ j : Fin (n + 1), F.r2Field x j = 0 := by
  rw [Fin.sum_univ_succ, F.r2Field_zero]
  have hsucc :
      (∑ i : Fin n, F.r2Field x i.succ)
        = ∑ i : Fin n, (x 0) ^ 2 * F.toField (origProj x) i :=
    Finset.sum_congr rfl (fun i _ => F.r2Field_succ x i)
  rw [hsucc]; ring

/-! ## SynPPBalance r²-lifted field

For `eq : SynPPBalance n`, the r²-lifted field coincides with
`eq.toQuadField.r2Field`. Pointwise this is immediate from
`toQuadField_toField`. The PP view has an additional prod/loss
decomposition that QuadField doesn't: `r2Field = r2Prod - r2Loss`
on non-slack slots. -/

noncomputable def SynPPBalance.r2Field {n : ℕ} (eq : SynPPBalance n) :
    (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ :=
  eq.toQuadField.r2Field

theorem SynPPBalance.r2Field_eq_quadField {n : ℕ} (eq : SynPPBalance n) :
    eq.r2Field = eq.toQuadField.r2Field := rfl

theorem SynPPBalance.r2Field_zero {n : ℕ} (eq : SynPPBalance n)
    (x : Fin (n + 1) → ℝ) :
    eq.r2Field x 0 = -∑ i : Fin n, (x 0) ^ 2 * eq.toField (origProj x) i := by
  unfold SynPPBalance.r2Field
  rw [eq.toQuadField.r2Field_zero]
  congr 1; refine Finset.sum_congr rfl ?_
  intro i _
  rw [show eq.toQuadField.toField (origProj x) i = eq.toField (origProj x) i by
    rw [eq.toQuadField_toField]]

theorem SynPPBalance.r2Field_succ {n : ℕ} (eq : SynPPBalance n)
    (x : Fin (n + 1) → ℝ) (i : Fin n) :
    eq.r2Field x i.succ = (x 0) ^ 2 * eq.toField (origProj x) i := by
  unfold SynPPBalance.r2Field
  rw [eq.toQuadField.r2Field_succ x i]
  rw [show eq.toQuadField.toField (origProj x) i = eq.toField (origProj x) i by
    rw [eq.toQuadField_toField]]

theorem SynPPBalance.r2Field_conservative {n : ℕ} (eq : SynPPBalance n)
    (x : Fin (n + 1) → ℝ) :
    ∑ j : Fin (n + 1), eq.r2Field x j = 0 :=
  eq.toQuadField.r2Field_conservative x

/-! ## Production/loss decomposition (SynPPBalance-specific) -/

noncomputable def SynPPBalance.r2Prod {n : ℕ} (eq : SynPPBalance n)
    (x : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  (x 0) ^ 2 * eq.evalProd i (origProj x)

noncomputable def SynPPBalance.r2Loss {n : ℕ} (_eq : SynPPBalance n)
    (x : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  2 * (x 0) ^ 2 * x i.succ * (∑ k : Fin n, x k.succ)

theorem SynPPBalance.r2Field_succ_eq {n : ℕ} (eq : SynPPBalance n)
    (x : Fin (n + 1) → ℝ) (i : Fin n) :
    eq.r2Field x i.succ = eq.r2Prod x i - eq.r2Loss x i := by
  rw [eq.r2Field_succ]
  simp only [SynPPBalance.r2Prod, SynPPBalance.r2Loss, SynPPBalance.toField,
    origProj]
  ring

theorem SynPPBalance.r2Prod_nonneg {n : ℕ} (eq : SynPPBalance n)
    (x : Fin (n + 1) → ℝ) (hx : ∀ j, 0 ≤ x j) (i : Fin n) :
    0 ≤ eq.r2Prod x i := by
  unfold SynPPBalance.r2Prod
  exact mul_nonneg (sq_nonneg _)
    (eq.evalProd_nonneg i (origProj x) (fun j => hx j.succ))

theorem SynPPBalance.r2Loss_nonneg {n : ℕ} (eq : SynPPBalance n)
    (x : Fin (n + 1) → ℝ) (hx : ∀ j, 0 ≤ x j) (i : Fin n) :
    0 ≤ eq.r2Loss x i := by
  unfold SynPPBalance.r2Loss
  have h1 : (0 : ℝ) ≤ 2 := by norm_num
  have h2 : 0 ≤ (x 0) ^ 2 := sq_nonneg _
  have h3 : 0 ≤ x i.succ := hx _
  have h4 : 0 ≤ ∑ k : Fin n, x k.succ := Finset.sum_nonneg (fun k _ => hx _)
  exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4

/-! ## Chain-rule algebra (SynPPBalance layer)

We preserve the full algebraic chain-rule identity
`r2ChainRuleSum eq α = (r2NonSlackChainRaw + r2SlackChainRaw) - r2LossSum`
from the SynPPBalance prod/loss decomposition. -/

noncomputable def SynPPBalance.r2NonSlackChainRaw {n : ℕ}
    (eq : SynPPBalance n) (α : Fin (n + 1) → ℕ) (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ src ∈ (NonSlackSourceSupp α).attach,
    ∑ ab : Fin n × Fin n,
      (eq.r2ChainCoeff α src.1 ab.1 ab.2 : ℝ) *
        rawMonomial (r2ChainDelta α src.1 ab.1 ab.2) x

noncomputable def SynPPBalance.r2SlackChainRaw {n : ℕ}
    (_eq : SynPPBalance n) (α : Fin (n + 1) → ℕ)
    (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ sk : Fin n × Fin n,
    (r2SlackChainCoeff α : ℝ) *
      rawMonomial (r2SlackChainDelta α sk.1 sk.2) x

noncomputable def SynPPBalance.r2SlackChainNAP {n : ℕ}
    (_eq : SynPPBalance n) (α : Fin (n + 1) → ℕ) (hα : IsCubedIndex α)
    (x : Fin (n + 1) → ℝ) : ℝ :=
  if hsrc : 0 < α 0 then
    ∑ sk : Fin n × Fin n,
      (splitRate (r2SlackChainCoeff α)
          (r2SlackMonomialSplit α hα sk.1 sk.2 hsrc) : ℝ) *
        cubedLift (r2SlackMonomialSplit α hα sk.1 sk.2 hsrc).β x *
        cubedLift (r2SlackMonomialSplit α hα sk.1 sk.2 hsrc).γ x
  else 0

theorem SynPPBalance.r2SlackChainRaw_zero_of_α0_zero {n : ℕ}
    (eq : SynPPBalance n)
    (α : Fin (n + 1) → ℕ) (hα0 : α 0 = 0) (x : Fin (n + 1) → ℝ) :
    eq.r2SlackChainRaw α x = 0 := by
  unfold SynPPBalance.r2SlackChainRaw r2SlackChainCoeff
  simp [hα0]

theorem SynPPBalance.r2SlackChainNAP_eq_raw {n : ℕ} (eq : SynPPBalance n)
    (α : Fin (n + 1) → ℕ) (hα : IsCubedIndex α) (x : Fin (n + 1) → ℝ) :
    eq.r2SlackChainNAP α hα x = eq.r2SlackChainRaw α x := by
  unfold SynPPBalance.r2SlackChainNAP
  by_cases hsrc : 0 < α 0
  · rw [dif_pos hsrc]
    exact r2_slack_chain_nap_eq_raw α hα hsrc x
  · rw [dif_neg hsrc]
    have hα0 : α 0 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (by omega))
    rw [eq.r2SlackChainRaw_zero_of_α0_zero α hα0 x]

/-! ## Non-slack NAP aggregation

The non-slack chain sum admits a NAP-split reconstruction identity at the
purely algebraic level: for every `(src, a, b)` triple we pick a
`MonomialSplit` (a real NAP-split from `r2MonomialSplit` when available,
a trivial `(β = δ, γ = 0)` split on the degenerate `a = b = src` diagonal),
and `splitRate_reconstructs` gives the per-triple identity regardless.

NAP validity (balanced + nonAutocatalytic) of the chosen splits is a
separate statement that additionally needs `eq.NoSelfSelf`: under NSS the
diagonal triples have `eq.coeff src src src = 0` so their contribution
vanishes, and for positive-coefficient triples the disjunctive off-self
hypothesis `a ≠ src ∨ b ≠ src` is automatic — giving a real NAP split. -/

/-- Trivial `MonomialSplit` witness with `β = δ, γ = 0`. Used as a fallback
on the forbidden diagonal `(a = src ∧ b = src)` where no NAP split exists.
The reconstruction identity `splitRate · cubed · cubed = coeff · raw` still
holds algebraically for any split; NAP validity is a separate predicate. -/
def trivialSplit {n : ℕ} (δ : Fin n → ℕ) : MonomialSplit δ where
  β := δ
  γ := fun _ => 0
  sum_eq := fun _ => by ring

/-- Canonical split choice for a non-slack chain-rule triple: `r2MonomialSplit`
when `a ≠ src ∨ b ≠ src` (disjunctive off-self hypothesis), else `trivialSplit`. -/
noncomputable def r2NonSlackMonomialSplit {n : ℕ}
    (α : Fin (n + 1) → ℕ) (hα : IsCubedIndex α)
    (src a b : Fin n) (hsrc : 0 < α src.succ) :
    MonomialSplit (r2ChainDelta α src a b) := by
  classical
  by_cases hab : a ≠ src ∨ b ≠ src
  · exact r2MonomialSplit α hα src a b hsrc hab
  · exact trivialSplit _

/-- Per-triple NAP reconstruction identity at the non-slack level. Purely
algebraic — holds for any `MonomialSplit`, so no NSS hypothesis needed. -/
theorem r2NonSlackPair_reconstructs {n : ℕ}
    (eq : SynPPBalance n) (α : Fin (n + 1) → ℕ) (hα : IsCubedIndex α)
    (src a b : Fin n) (hsrc : 0 < α src.succ) (x : Fin (n + 1) → ℝ) :
    (splitRate (eq.r2ChainCoeff α src a b)
        (r2NonSlackMonomialSplit α hα src a b hsrc) : ℝ) *
      cubedLift (r2NonSlackMonomialSplit α hα src a b hsrc).β x *
      cubedLift (r2NonSlackMonomialSplit α hα src a b hsrc).γ x =
    (eq.r2ChainCoeff α src a b : ℝ) *
      rawMonomial (r2ChainDelta α src a b) x :=
  splitRate_reconstructs _ _ x

/-- NAP-split form of the non-slack chain sum. -/
noncomputable def SynPPBalance.r2NonSlackChainNAP {n : ℕ}
    (eq : SynPPBalance n) (α : Fin (n + 1) → ℕ) (hα : IsCubedIndex α)
    (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ src ∈ (NonSlackSourceSupp α).attach,
    ∑ ab : Fin n × Fin n,
      (splitRate (eq.r2ChainCoeff α src.1 ab.1 ab.2)
          (r2NonSlackMonomialSplit α hα src.1 ab.1 ab.2
            (by simpa [NonSlackSourceSupp] using (Finset.mem_filter.mp src.2).2)) : ℝ) *
        cubedLift (r2NonSlackMonomialSplit α hα src.1 ab.1 ab.2
          (by simpa [NonSlackSourceSupp] using (Finset.mem_filter.mp src.2).2)).β x *
        cubedLift (r2NonSlackMonomialSplit α hα src.1 ab.1 ab.2
          (by simpa [NonSlackSourceSupp] using (Finset.mem_filter.mp src.2).2)).γ x

/-- **Non-slack chain NAP reconstruction**: the aggregated NAP-split form of
the non-slack chain sum equals the raw sum. Pure algebra via
`splitRate_reconstructs`, no NSS required. -/
theorem SynPPBalance.r2NonSlackChainNAP_eq_raw {n : ℕ} (eq : SynPPBalance n)
    (α : Fin (n + 1) → ℕ) (hα : IsCubedIndex α) (x : Fin (n + 1) → ℝ) :
    eq.r2NonSlackChainNAP α hα x = eq.r2NonSlackChainRaw α x := by
  unfold SynPPBalance.r2NonSlackChainNAP SynPPBalance.r2NonSlackChainRaw
  refine Finset.sum_congr rfl ?_
  intro src _
  refine Finset.sum_congr rfl ?_
  intro ab _
  have hsrc : 0 < α src.1.succ := by
    simpa [NonSlackSourceSupp] using (Finset.mem_filter.mp src.2).2
  exact r2NonSlackPair_reconstructs eq α hα src.1 ab.1 ab.2 hsrc x

/-! ## Monomial algebra

Raw polynomial identities that hold for any QuadField's r²-lifted
chain-rule computation. -/

def shiftDown {m : ℕ} (α : Fin m → ℕ) (j : Fin m) : Fin m → ℕ :=
  fun k => α k - if k = j then 1 else 0

theorem rawMonomial_r2PPMonomial_succ {n : ℕ}
    (a b : Fin n) (x : Fin (n + 1) → ℝ) :
    rawMonomial (r2PPMonomial (0 : Fin (n + 1)) a.succ b.succ) x =
      (x 0) ^ 2 * x a.succ * x b.succ := by
  classical
  have hsplit :
      (fun k : Fin (n + 1) =>
          (if k = (0 : Fin (n + 1)) then 2 else 0) +
            ((if k = a.succ then 1 else 0) + (if k = b.succ then 1 else 0)))
        = fun k : Fin (n + 1) =>
            r2PPMonomial (0 : Fin (n + 1)) a.succ b.succ k := by
    funext k
    unfold r2PPMonomial
    ring
  have hadd1 :
      rawMonomial
          (fun k : Fin (n + 1) =>
            (if k = (0 : Fin (n + 1)) then 2 else 0) +
              ((if k = a.succ then 1 else 0) + (if k = b.succ then 1 else 0))) x
        = rawMonomial (fun k : Fin (n + 1) => if k = (0 : Fin (n + 1)) then 2 else 0) x *
            rawMonomial
              (fun k : Fin (n + 1) =>
                (if k = a.succ then 1 else 0) + (if k = b.succ then 1 else 0)) x :=
    rawMonomial_add _ _ x
  have hadd2 :
      rawMonomial
          (fun k : Fin (n + 1) =>
            (if k = a.succ then 1 else 0) + (if k = b.succ then 1 else 0)) x
        = rawMonomial (fun k : Fin (n + 1) => if k = a.succ then 1 else 0) x *
            rawMonomial (fun k : Fin (n + 1) => if k = b.succ then 1 else 0) x :=
    rawMonomial_add _ _ x
  have h0 :
      rawMonomial (fun k : Fin (n + 1) => if k = (0 : Fin (n + 1)) then 2 else 0) x
        = (x 0) ^ 2 := by
    unfold rawMonomial
    rw [Finset.prod_eq_single (0 : Fin (n + 1))]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact (h (Finset.mem_univ _)).elim
  have ha :
      rawMonomial (fun k : Fin (n + 1) => if k = a.succ then 1 else 0) x
        = x a.succ := by
    unfold rawMonomial
    rw [Finset.prod_eq_single a.succ]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact (h (Finset.mem_univ _)).elim
  have hb :
      rawMonomial (fun k : Fin (n + 1) => if k = b.succ then 1 else 0) x
        = x b.succ := by
    unfold rawMonomial
    rw [Finset.prod_eq_single b.succ]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; exact (h (Finset.mem_univ _)).elim
  have key :
      rawMonomial
          (fun k : Fin (n + 1) =>
            (if k = (0 : Fin (n + 1)) then 2 else 0) +
              ((if k = a.succ then 1 else 0) + (if k = b.succ then 1 else 0))) x
        = (x 0) ^ 2 * x a.succ * x b.succ := by
    rw [hadd1, hadd2, h0, ha, hb]; ring
  have hrw :
      rawMonomial
          (fun k : Fin (n + 1) =>
            (if k = (0 : Fin (n + 1)) then 2 else 0) +
              ((if k = a.succ then 1 else 0) + (if k = b.succ then 1 else 0))) x
        = rawMonomial (r2PPMonomial (0 : Fin (n + 1)) a.succ b.succ) x := by
    have hfun : (fun k : Fin (n + 1) =>
              (if k = (0 : Fin (n + 1)) then 2 else 0) +
                ((if k = a.succ then 1 else 0) + (if k = b.succ then 1 else 0)))
            = r2PPMonomial (0 : Fin (n + 1)) a.succ b.succ := by
      funext k
      unfold r2PPMonomial
      ring
    rw [hfun]
  rw [← hrw]; exact key

theorem r2ChainDelta_eq_add {n : ℕ}
    (α : Fin (n + 1) → ℕ) (source a b : Fin n) :
    r2ChainDelta α source a b =
      fun k => shiftDown α source.succ k +
        r2PPMonomial (0 : Fin (n + 1)) a.succ b.succ k := by
  funext k; rfl

theorem rawMonomial_r2ChainDelta {n : ℕ}
    (α : Fin (n + 1) → ℕ) (source a b : Fin n) (x : Fin (n + 1) → ℝ) :
    rawMonomial (r2ChainDelta α source a b) x =
      rawMonomial (shiftDown α source.succ) x *
        ((x 0) ^ 2 * x a.succ * x b.succ) := by
  rw [r2ChainDelta_eq_add, rawMonomial_add, rawMonomial_r2PPMonomial_succ]

theorem SynPPBalance.r2NonSlackChainRaw_prodForm {n : ℕ}
    (eq : SynPPBalance n) (α : Fin (n + 1) → ℕ) (x : Fin (n + 1) → ℝ) :
    eq.r2NonSlackChainRaw α x =
      ∑ i : Fin n,
        (α i.succ : ℝ) * rawMonomial (shiftDown α i.succ) x *
          eq.r2Prod x i := by
  classical
  have hFilter :
      ∑ src ∈ (NonSlackSourceSupp α).attach,
          ∑ ab : Fin n × Fin n,
            (eq.r2ChainCoeff α src.1 ab.1 ab.2 : ℝ) *
              rawMonomial (r2ChainDelta α src.1 ab.1 ab.2) x
        = ∑ src : Fin n,
            ∑ ab : Fin n × Fin n,
              (eq.r2ChainCoeff α src ab.1 ab.2 : ℝ) *
                rawMonomial (r2ChainDelta α src ab.1 ab.2) x := by
    rw [Finset.sum_attach (NonSlackSourceSupp α)
        (fun src => ∑ ab : Fin n × Fin n,
          (eq.r2ChainCoeff α src ab.1 ab.2 : ℝ) *
            rawMonomial (r2ChainDelta α src ab.1 ab.2) x)]
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro src _ hsrc
    have hα0 : α src.succ = 0 := by
      by_contra h
      exact hsrc (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, Nat.pos_of_ne_zero h⟩)
    refine Finset.sum_eq_zero ?_
    intro ab _
    unfold SynPPBalance.r2ChainCoeff
    simp [hα0]
  have hInner : ∀ src : Fin n,
      ∑ ab : Fin n × Fin n,
          (eq.r2ChainCoeff α src ab.1 ab.2 : ℝ) *
            rawMonomial (r2ChainDelta α src ab.1 ab.2) x
        = (α src.succ : ℝ) * rawMonomial (shiftDown α src.succ) x *
            eq.r2Prod x src := by
    intro src
    have hEach : ∀ ab : Fin n × Fin n,
        (eq.r2ChainCoeff α src ab.1 ab.2 : ℝ) *
            rawMonomial (r2ChainDelta α src ab.1 ab.2) x
          = (α src.succ : ℝ) * rawMonomial (shiftDown α src.succ) x *
              ((x 0) ^ 2 * ((eq.coeff src ab.1 ab.2 : ℝ) *
                x ab.1.succ * x ab.2.succ)) := by
      intro ab
      rw [rawMonomial_r2ChainDelta]
      unfold SynPPBalance.r2ChainCoeff
      push_cast
      ring
    rw [show (∑ ab : Fin n × Fin n,
          (eq.r2ChainCoeff α src ab.1 ab.2 : ℝ) *
            rawMonomial (r2ChainDelta α src ab.1 ab.2) x)
        = ∑ ab : Fin n × Fin n,
          (α src.succ : ℝ) * rawMonomial (shiftDown α src.succ) x *
            ((x 0) ^ 2 * ((eq.coeff src ab.1 ab.2 : ℝ) *
              x ab.1.succ * x ab.2.succ)) from
        Finset.sum_congr rfl (fun ab _ => hEach ab)]
    rw [← Finset.mul_sum]
    have hProd :
        ∑ ab : Fin n × Fin n,
          (x 0) ^ 2 * ((eq.coeff src ab.1 ab.2 : ℝ) *
            x ab.1.succ * x ab.2.succ)
          = eq.r2Prod x src := by
      unfold SynPPBalance.r2Prod SynPPBalance.evalProd origProj
      rw [← Finset.mul_sum]
      congr 1
      rw [← Finset.sum_product']
      refine Finset.sum_congr rfl ?_
      intro ab _
      ring
    rw [hProd]
  unfold SynPPBalance.r2NonSlackChainRaw
  rw [hFilter]
  exact Finset.sum_congr rfl (fun src _ => hInner src)

theorem r2SlackChainDelta_eq_add {n : ℕ}
    (α : Fin (n + 1) → ℕ) (source k : Fin n) :
    r2SlackChainDelta α source k =
      fun i => shiftDown α 0 i +
        r2PPMonomial (0 : Fin (n + 1)) source.succ k.succ i := by
  funext i; rfl

theorem rawMonomial_r2SlackChainDelta {n : ℕ}
    (α : Fin (n + 1) → ℕ) (source k : Fin n) (x : Fin (n + 1) → ℝ) :
    rawMonomial (r2SlackChainDelta α source k) x =
      rawMonomial (shiftDown α 0) x *
        ((x 0) ^ 2 * x source.succ * x k.succ) := by
  rw [r2SlackChainDelta_eq_add, rawMonomial_add,
      rawMonomial_r2PPMonomial_succ]

theorem SynPPBalance.r2SlackChainRaw_lossForm {n : ℕ}
    (eq : SynPPBalance n) (α : Fin (n + 1) → ℕ) (x : Fin (n + 1) → ℝ) :
    eq.r2SlackChainRaw α x =
      (α 0 : ℝ) * rawMonomial (shiftDown α 0) x *
        (∑ i : Fin n, eq.r2Loss x i) := by
  unfold SynPPBalance.r2SlackChainRaw r2SlackChainCoeff
  have hEach : ∀ sk : Fin n × Fin n,
      ((2 * (α 0 : ℚ) : ℚ) : ℝ) *
          rawMonomial (r2SlackChainDelta α sk.1 sk.2) x
        = (α 0 : ℝ) * rawMonomial (shiftDown α 0) x *
            (2 * (x 0) ^ 2 * x sk.1.succ * x sk.2.succ) := by
    intro sk
    rw [rawMonomial_r2SlackChainDelta]
    push_cast; ring
  rw [show (∑ sk : Fin n × Fin n,
        ((2 * (α 0 : ℚ) : ℚ) : ℝ) *
          rawMonomial (r2SlackChainDelta α sk.1 sk.2) x)
      = ∑ sk : Fin n × Fin n,
        (α 0 : ℝ) * rawMonomial (shiftDown α 0) x *
          (2 * (x 0) ^ 2 * x sk.1.succ * x sk.2.succ) from
      Finset.sum_congr rfl (fun sk _ => hEach sk)]
  rw [← Finset.mul_sum]
  have hLoss :
      ∑ sk : Fin n × Fin n,
          (2 * (x 0) ^ 2 * x sk.1.succ * x sk.2.succ)
        = ∑ i : Fin n, eq.r2Loss x i := by
    rw [Fintype.sum_prod_type]
    unfold SynPPBalance.r2Loss
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
  rw [hLoss]

/-! ## Full algebraic chain-rule identity -/

noncomputable def SynPPBalance.r2ChainRuleSum {n : ℕ} (eq : SynPPBalance n)
    (α : Fin (n + 1) → ℕ) (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ j : Fin (n + 1), (α j : ℝ) * rawMonomial (shiftDown α j) x *
    eq.r2Field x j

noncomputable def SynPPBalance.r2LossSum {n : ℕ} (eq : SynPPBalance n)
    (α : Fin (n + 1) → ℕ) (x : Fin (n + 1) → ℝ) : ℝ :=
  (∑ i : Fin n, (α i.succ : ℝ) * rawMonomial (shiftDown α i.succ) x *
      eq.r2Loss x i)
  + (α 0 : ℝ) * rawMonomial (shiftDown α 0) x *
      (∑ i : Fin n, eq.r2Prod x i)

theorem SynPPBalance.r2ChainRuleSum_eq_raw_sub_loss {n : ℕ}
    (eq : SynPPBalance n) (α : Fin (n + 1) → ℕ) (x : Fin (n + 1) → ℝ) :
    eq.r2ChainRuleSum α x =
      (eq.r2NonSlackChainRaw α x + eq.r2SlackChainRaw α x) -
        eq.r2LossSum α x := by
  unfold SynPPBalance.r2ChainRuleSum
  rw [Fin.sum_univ_succ]
  rw [eq.r2Field_zero]
  have hSucc : ∀ i : Fin n,
      (α i.succ : ℝ) * rawMonomial (shiftDown α i.succ) x *
          eq.r2Field x i.succ
        = (α i.succ : ℝ) * rawMonomial (shiftDown α i.succ) x *
            eq.r2Prod x i -
          (α i.succ : ℝ) * rawMonomial (shiftDown α i.succ) x *
            eq.r2Loss x i := by
    intro i
    rw [eq.r2Field_succ_eq]; ring
  rw [show (∑ i : Fin n, (α i.succ : ℝ) * rawMonomial (shiftDown α i.succ) x *
            eq.r2Field x i.succ)
        = ∑ i : Fin n,
            ((α i.succ : ℝ) * rawMonomial (shiftDown α i.succ) x *
              eq.r2Prod x i -
            (α i.succ : ℝ) * rawMonomial (shiftDown α i.succ) x *
              eq.r2Loss x i) from
      Finset.sum_congr rfl (fun i _ => hSucc i)]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ i : Fin n, (α i.succ : ℝ) * rawMonomial (shiftDown α i.succ) x *
              eq.r2Prod x i)
          = eq.r2NonSlackChainRaw α x from
      (eq.r2NonSlackChainRaw_prodForm α x).symm]
  have hSlackSimp :
      (α 0 : ℝ) * rawMonomial (shiftDown α 0) x *
          (-∑ i : Fin n, (x 0) ^ 2 * eq.toField (origProj x) i)
        = -(α 0 : ℝ) * rawMonomial (shiftDown α 0) x *
            (∑ i : Fin n, eq.r2Prod x i) +
          (α 0 : ℝ) * rawMonomial (shiftDown α 0) x *
            (∑ i : Fin n, eq.r2Loss x i) := by
    have hToField : ∀ i : Fin n,
        (x 0) ^ 2 * eq.toField (origProj x) i
          = eq.r2Prod x i - eq.r2Loss x i := by
      intro i
      unfold SynPPBalance.r2Prod SynPPBalance.r2Loss SynPPBalance.toField origProj
      ring
    rw [show (∑ i : Fin n, (x 0) ^ 2 * eq.toField (origProj x) i)
            = ∑ i : Fin n, (eq.r2Prod x i - eq.r2Loss x i) from
        Finset.sum_congr rfl (fun i _ => hToField i)]
    rw [Finset.sum_sub_distrib]
    ring
  rw [hSlackSimp]
  rw [show ((α 0 : ℝ) * rawMonomial (shiftDown α 0) x *
              (∑ i : Fin n, eq.r2Loss x i))
          = eq.r2SlackChainRaw α x from
      (eq.r2SlackChainRaw_lossForm α x).symm]
  unfold SynPPBalance.r2LossSum
  ring

/-- **Whole-PIVP chain-rule NAP identity.** Combines the non-slack and slack
NAP aggregations with `r2ChainRuleSum_eq_raw_sub_loss` to give the clean
"whole-PIVP" form: the total chain-rule sum equals the aggregated NAP-split
contributions (non-slack + slack) minus the degradation loss.

This is the target statement of the PP → NAP pipeline at the aggregated
level: every cubed-index ODE derivative for the r²-lifted SynPPBalance field
decomposes as a sum of routed NAP interactions plus degradation. -/
theorem SynPPBalance.r2ChainRuleSum_eq_nap_sub_loss {n : ℕ}
    (eq : SynPPBalance n) (α : Fin (n + 1) → ℕ) (hα : IsCubedIndex α)
    (x : Fin (n + 1) → ℝ) :
    eq.r2ChainRuleSum α x =
      (eq.r2NonSlackChainNAP α hα x + eq.r2SlackChainNAP α hα x) -
        eq.r2LossSum α x := by
  rw [eq.r2ChainRuleSum_eq_raw_sub_loss α x]
  rw [eq.r2NonSlackChainNAP_eq_raw α hα x]
  rw [eq.r2SlackChainNAP_eq_raw α hα x]

/-! ## ODE chain rule for `rawMonomial` and `cubedLift` -/

theorem hasDerivAt_rawMonomial {m : ℕ} (α : Fin m → ℕ)
    (g : Fin m → ℝ → ℝ) (g' : Fin m → ℝ) (t : ℝ)
    (h : ∀ i : Fin m, HasDerivAt (g i) (g' i) t) :
    HasDerivAt (fun t' => rawMonomial α (fun j => g j t'))
      (∑ i : Fin m,
        (α i : ℝ) * rawMonomial (shiftDown α i) (fun j => g j t) * g' i) t := by
  classical
  have hexpand :
      (fun t' : ℝ => rawMonomial α (fun j => g j t')) =
        fun t' : ℝ => ∏ j : Fin m, (g j t') ^ α j := by
    funext t'; unfold rawMonomial; rfl
  rw [hexpand]
  have hpow : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      HasDerivAt (fun t' : ℝ => (g i t') ^ α i)
        ((α i : ℝ) * (g i t) ^ (α i - 1) * g' i) t := by
    intro i _
    have := (h i).pow (α i)
    simpa using this
  have hprod :=
    HasDerivAt.fun_finset_prod (𝔸' := ℝ)
      (u := (Finset.univ : Finset (Fin m)))
      (f := fun i t' => (g i t') ^ α i)
      (f' := fun i => (α i : ℝ) * (g i t) ^ (α i - 1) * g' i) hpow
  convert hprod using 1
  refine Finset.sum_congr rfl ?_
  intro i _
  have hprodErase :
      (∏ j ∈ (Finset.univ : Finset (Fin m)).erase i, (g j t) ^ α j)
          * (g i t) ^ (α i - 1)
        = rawMonomial (shiftDown α i) (fun j => g j t) := by
    unfold rawMonomial shiftDown
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin m))
        (fun j => (g j t) ^ (α j - if j = i then 1 else 0))
        (Finset.mem_univ i)]
    have hprodCongr :
        (∏ x ∈ Finset.univ.erase i, (g x t) ^ α x)
          = ∏ x ∈ Finset.univ.erase i,
              (g x t) ^ (α x - (if x = i then 1 else 0)) := by
      refine Finset.prod_congr rfl ?_
      intro x hx
      have hxi : x ≠ i := Finset.ne_of_mem_erase hx
      simp [hxi]
    rw [hprodCongr]
    have hpowi :
        (g i t) ^ (α i - (if i = i then 1 else 0)) = (g i t) ^ (α i - 1) := by
      simp
    rw [hpowi]
    ring
  rw [smul_eq_mul]
  rw [← hprodErase]
  ring

theorem hasDerivAt_cubedLift_along_r2Field {n : ℕ}
    (eq : SynPPBalance n) (α : Fin (n + 1) → ℕ)
    (xpath : ℝ → Fin (n + 1) → ℝ) (t : ℝ)
    (hx : ∀ i : Fin (n + 1),
      HasDerivAt (fun t' => xpath t' i) (eq.r2Field (xpath t) i) t) :
    HasDerivAt (fun t' => cubedLift α (xpath t'))
      ((cubedCoeff α : ℝ) * eq.r2ChainRuleSum α (xpath t)) t := by
  have hraw :
      HasDerivAt (fun t' => rawMonomial α (xpath t'))
        (eq.r2ChainRuleSum α (xpath t)) t := by
    have hraw' :
        HasDerivAt (fun t' => rawMonomial α (fun j => xpath t' j))
          (∑ i : Fin (n + 1),
            (α i : ℝ) * rawMonomial (shiftDown α i)
              (fun j => xpath t j) * eq.r2Field (xpath t) i) t :=
      hasDerivAt_rawMonomial α (fun i => fun t' => xpath t' i)
        (fun i => eq.r2Field (xpath t) i) t (fun i => hx i)
    have hcong :
        (fun t' => rawMonomial α (fun j => xpath t' j))
          = fun t' => rawMonomial α (xpath t') := by
      funext t'; rfl
    have hsum :
        (∑ i : Fin (n + 1),
            (α i : ℝ) * rawMonomial (shiftDown α i)
              (fun j => xpath t j) * eq.r2Field (xpath t) i)
          = eq.r2ChainRuleSum α (xpath t) := rfl
    rw [hcong] at hraw'
    rw [hsum] at hraw'
    exact hraw'
  have hcubed :
      HasDerivAt (fun t' => cubedLift α (xpath t'))
        ((cubedCoeff α : ℝ) * eq.r2ChainRuleSum α (xpath t)) t := by
    have := hraw.const_mul ((cubedCoeff α : ℝ))
    simpa [cubedLift] using this
  exact hcubed

/-! ## Nonnegativity -/

theorem rawMonomial_nonneg {m : ℕ} (α : Fin m → ℕ) {x : Fin m → ℝ}
    (hx : ∀ j, 0 ≤ x j) : 0 ≤ rawMonomial α x := by
  unfold rawMonomial
  exact Finset.prod_nonneg (fun j _ => pow_nonneg (hx j) _)

theorem SynPPBalance.r2NonSlackChainRaw_nonneg {n : ℕ}
    (eq : SynPPBalance n) (α : Fin (n + 1) → ℕ)
    (x : Fin (n + 1) → ℝ) (hx : ∀ j, 0 ≤ x j) :
    0 ≤ eq.r2NonSlackChainRaw α x := by
  rw [eq.r2NonSlackChainRaw_prodForm]
  refine Finset.sum_nonneg ?_
  intro i _
  have h1 : (0 : ℝ) ≤ (α i.succ : ℝ) := by exact_mod_cast Nat.zero_le _
  have h2 : 0 ≤ rawMonomial (shiftDown α i.succ) x := rawMonomial_nonneg _ hx
  have h3 : 0 ≤ eq.r2Prod x i := eq.r2Prod_nonneg x hx i
  exact mul_nonneg (mul_nonneg h1 h2) h3

theorem SynPPBalance.r2SlackChainRaw_nonneg {n : ℕ}
    (eq : SynPPBalance n) (α : Fin (n + 1) → ℕ)
    (x : Fin (n + 1) → ℝ) (hx : ∀ j, 0 ≤ x j) :
    0 ≤ eq.r2SlackChainRaw α x := by
  rw [eq.r2SlackChainRaw_lossForm]
  have h1 : (0 : ℝ) ≤ (α 0 : ℝ) := by exact_mod_cast Nat.zero_le _
  have h2 : 0 ≤ rawMonomial (shiftDown α 0) x := rawMonomial_nonneg _ hx
  have h3 : 0 ≤ ∑ i : Fin n, eq.r2Loss x i :=
    Finset.sum_nonneg (fun i _ => eq.r2Loss_nonneg x hx i)
  exact mul_nonneg (mul_nonneg h1 h2) h3

theorem SynPPBalance.r2LossSum_nonneg {n : ℕ}
    (eq : SynPPBalance n) (α : Fin (n + 1) → ℕ)
    (x : Fin (n + 1) → ℝ) (hx : ∀ j, 0 ≤ x j) :
    0 ≤ eq.r2LossSum α x := by
  unfold SynPPBalance.r2LossSum
  have hLoss :
      0 ≤ ∑ i : Fin n, (α i.succ : ℝ) * rawMonomial (shiftDown α i.succ) x *
            eq.r2Loss x i := by
    refine Finset.sum_nonneg ?_
    intro i _
    have h1 : (0 : ℝ) ≤ (α i.succ : ℝ) := by exact_mod_cast Nat.zero_le _
    have h2 : 0 ≤ rawMonomial (shiftDown α i.succ) x :=
      rawMonomial_nonneg _ hx
    have h3 : 0 ≤ eq.r2Loss x i := eq.r2Loss_nonneg x hx i
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hSlack :
      0 ≤ (α 0 : ℝ) * rawMonomial (shiftDown α 0) x *
            (∑ i : Fin n, eq.r2Prod x i) := by
    have h1 : (0 : ℝ) ≤ (α 0 : ℝ) := by exact_mod_cast Nat.zero_le _
    have h2 : 0 ≤ rawMonomial (shiftDown α 0) x := rawMonomial_nonneg _ hx
    have h3 : 0 ≤ ∑ i : Fin n, eq.r2Prod x i :=
      Finset.sum_nonneg (fun i _ => eq.r2Prod_nonneg x hx i)
    exact mul_nonneg (mul_nonneg h1 h2) h3
  linarith

end Ripple
