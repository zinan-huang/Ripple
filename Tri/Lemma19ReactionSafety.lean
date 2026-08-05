/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.InfectionReactionSafety
import Tri.Lemma19FullPoolJoint

/-!
# Positive-gap reaction safety on the Lemma 19 joint path

The adverse productive-reaction count is stopped before either its budget is
spent or a genuine immutable-label prefix exceeds its budget.  Until one of
those events occurs, the exact gap ledger keeps the active gap positive, so
the harmonic reaction potential is a supermartingale.
-/

namespace Tri

open scoped ENNReal

noncomputable section

variable {α : Type*}

/-- Freezing a kernel on its hitting target before forming `hitProb` changes
nothing. -/
theorem hitProb_freeze_same
    (B : α → Prop) [DecidablePred B]
    (K : α → PMF α) (T : ℕ) (s : α) :
    hitProb B (freeze B K) T s =
      hitProb B K T s := by
  have hidem :
      freeze B (freeze B K) = freeze B K := by
    funext x
    by_cases hx : B x
    · rw [freeze_of_mem x hx, freeze_of_mem x hx]
    · rw [freeze_of_not_mem x hx, freeze_of_not_mem x hx]
  unfold hitProb
  rw [hidem]

/-- A hit of `Bad` either occurs after first hitting `Guard`, or occurs in the
chain stopped at `Guard`. -/
theorem hitProb_le_guard_add_guarded
    (K : α → PMF α)
    (Bad Guard : α → Prop)
    [DecidablePred Bad] [DecidablePred Guard] :
    ∀ (T : ℕ) (s : α),
      hitProb Bad K T s ≤
        hitProb Guard K T s +
          hitProb Bad (freeze Guard K) T s := by
  intro T
  induction T with
  | zero =>
      intro s
      by_cases hGuard : Guard s
      · rw [hitProb_eq_one_of_mem Guard K 0 s hGuard]
        exact
          (hitProb_le_one Bad K 0 s).trans
            le_self_add
      · by_cases hBad : Bad s
        · rw [hitProb_eq_one_of_mem Bad K 0 s hBad,
            hitProb_eq_one_of_mem Bad
              (freeze Guard K) 0 s hBad]
          calc
            (1 : ℝ≥0∞) ≤
                1 + hitProb Guard K 0 s :=
              le_self_add
            _ =
                hitProb Guard K 0 s + 1 := by
              rw [add_comm]
        · unfold hitProb
          simp [iter, ind, hGuard, hBad]
  | succ T ih =>
      intro s
      by_cases hGuard : Guard s
      · rw [
          hitProb_eq_one_of_mem Guard K (T + 1) s
            hGuard]
        exact
          (hitProb_le_one Bad K (T + 1) s).trans
            le_self_add
      · by_cases hBad : Bad s
        · rw [
            hitProb_eq_one_of_mem Bad K (T + 1) s
              hBad,
            hitProb_eq_one_of_mem Bad
              (freeze Guard K) (T + 1) s hBad]
          calc
            (1 : ℝ≥0∞) ≤
                1 + hitProb Guard K (T + 1) s :=
              le_self_add
            _ =
                hitProb Guard K (T + 1) s + 1 := by
              rw [add_comm]
        · rw [
            hitProb_succ_of_not Bad K T s hBad,
            hitProb_succ_of_not Guard K T s hGuard,
            hitProb_succ_of_not Bad
              (freeze Guard K) T s hBad]
          rw [freeze_of_not_mem s hGuard,
            ← ENNReal.tsum_add]
          refine ENNReal.tsum_le_tsum fun z => ?_
          rw [← mul_add]
          exact mul_le_mul_right (ih z) _

/-- The probability of hitting either competing event is bounded by hitting
the guard first plus hitting the bad event in the guard-stopped chain. -/
theorem hitProb_union_le_guard_add_guarded
    (K : α → PMF α)
    (Bad Guard : α → Prop)
    [DecidablePred Bad] [DecidablePred Guard] :
    ∀ (T : ℕ) (s : α),
      hitProb (fun z => Guard z ∨ Bad z) K T s ≤
        hitProb Guard K T s +
          hitProb Bad (freeze Guard K) T s := by
  intro T
  induction T with
  | zero =>
      intro s
      by_cases hGuard : Guard s
      · rw [
          hitProb_eq_one_of_mem
            (fun z => Guard z ∨ Bad z) K 0 s
            (Or.inl hGuard),
          hitProb_eq_one_of_mem Guard K 0 s hGuard]
        exact le_self_add
      · by_cases hBad : Bad s
        · rw [
            hitProb_eq_one_of_mem
              (fun z => Guard z ∨ Bad z) K 0 s
              (Or.inr hBad),
            hitProb_eq_one_of_mem Bad
              (freeze Guard K) 0 s hBad]
          calc
            (1 : ℝ≥0∞) ≤
                1 + hitProb Guard K 0 s :=
              le_self_add
            _ =
                hitProb Guard K 0 s + 1 := by
              rw [add_comm]
        · unfold hitProb
          simp [iter, ind, hGuard, hBad]
  | succ T ih =>
      intro s
      by_cases hGuard : Guard s
      · rw [
          hitProb_eq_one_of_mem
            (fun z => Guard z ∨ Bad z) K (T + 1) s
            (Or.inl hGuard),
          hitProb_eq_one_of_mem Guard K (T + 1) s
            hGuard]
        exact le_self_add
      · by_cases hBad : Bad s
        · rw [
            hitProb_eq_one_of_mem
              (fun z => Guard z ∨ Bad z) K (T + 1) s
              (Or.inr hBad),
            hitProb_eq_one_of_mem Bad
              (freeze Guard K) (T + 1) s hBad]
          calc
            (1 : ℝ≥0∞) ≤
                1 + hitProb Guard K (T + 1) s :=
              le_self_add
            _ =
                hitProb Guard K (T + 1) s + 1 := by
              rw [add_comm]
        · have hUnion :
              ¬ (Guard s ∨ Bad s) := by tauto
          rw [
            hitProb_succ_of_not
              (fun z => Guard z ∨ Bad z) K T s
              hUnion,
            hitProb_succ_of_not Guard K T s hGuard,
            hitProb_succ_of_not Bad
              (freeze Guard K) T s hBad]
          rw [freeze_of_not_mem s hGuard,
            ← ENNReal.tsum_add]
          refine ENNReal.tsum_le_tsum fun z => ?_
          rw [← mul_add]
          exact mul_le_mul_right (ih z) _

variable {n : ℕ}

/-- The productive type-(2) count has exceeded the type-(1) count by `M`. -/
def Lemma19ReactionAdverseBad
    (M : ℕ) (q : Lemma17CountedPathState n) : Prop :=
  q.reaction.typeOneCount + M ≤
    q.reaction.typeTwoCount

noncomputable instance lemma19ReactionAdverseBadDecidable
    (M : ℕ) :
    DecidablePred (@Lemma19ReactionAdverseBad n M) :=
  Classical.decPred _

/-- The reaction safety potential crosses the reciprocal harmonic threshold
when the adverse directional excess reaches `M`. -/
theorem infectionReactionSafetyPotential_threshold
    (N D M : ℕ)
    (hDn : D < N)
    (q : InfectionReactionTraceState N)
    (hbad :
      q.typeOneCount + M ≤ q.typeTwoCount) :
    (lemma3SafetyBase N D)⁻¹ ^ M ≤
      infectionReactionSafetyPotential D q := by
  let u := lemma3SafetyBase N D
  have hu1 : u ≤ 1 :=
    lemma3SafetyBase_le_one hDn
  have hinv1 : 1 ≤ u⁻¹ :=
    ENNReal.one_le_inv.mpr hu1
  have hpow :
      u⁻¹ ^ (q.typeOneCount + M) ≤
        u⁻¹ ^ q.typeTwoCount :=
    pow_le_pow_right₀ hinv1 hbad
  have hu0 : u ≠ 0 :=
    lemma3SafetyBase_ne_zero hDn
  have hutop : u ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hu1
  have hcancel :
      u ^ q.typeOneCount *
          u⁻¹ ^ (q.typeOneCount + M) =
        u⁻¹ ^ M := by
    rw [pow_add, ← mul_assoc, ← mul_pow,
      ENNReal.mul_inv_cancel hu0 hutop,
      one_pow, one_mul]
  unfold infectionReactionSafetyPotential
  calc
    (lemma3SafetyBase N D)⁻¹ ^ M =
        u ^ q.typeOneCount *
          u⁻¹ ^ (q.typeOneCount + M) := by
      rw [hcancel]
    _ ≤
        u ^ q.typeOneCount *
          u⁻¹ ^ q.typeTwoCount :=
      mul_le_mul_left' hpow _
    _ =
        lemma3SafetyBase N D ^ q.typeOneCount *
          (lemma3SafetyBase N D)⁻¹ ^
            q.typeTwoCount := rfl

/-- Before the genuine label-prefix budget is crossed, the probability that
productive type-(2) reactions exceed type-(1) reactions by `M` is bounded by
the harmonic positive-gap power. -/
theorem lemma19CountedPath_guarded_reaction_hitProb
    (n : ℕ) (h3 : 3 ≤ n)
    (r Dstart Dlabel M targetGap T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + r = n)
    (hstart :
      s.coarse.1.ay + Dstart ≤ s.coarse.1.ax)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ Dstart)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n) :
    hitProb (Lemma19ReactionAdverseBad M)
        (freeze (Lemma17PhysicalLabelBad Dlabel)
          (lemma17CountedPathStep n h3 r n 0))
        T (lemma17CountedPathInitial s)
      ≤
    lemma3SafetyBase n targetGap ^ M := by
  let K := lemma17CountedPathStep n h3 r n 0
  let Guard : Lemma17CountedPathState n → Prop :=
    Lemma17PhysicalLabelBad Dlabel
  let Bad : Lemma17CountedPathState n → Prop :=
    Lemma19ReactionAdverseBad M
  let V : Lemma17CountedPathState n → ℝ≥0∞ :=
    fun z =>
      infectionReactionSafetyPotential targetGap
        z.reaction
  let θ : ℝ≥0∞ :=
    (lemma3SafetyBase n targetGap)⁻¹ ^ M
  let P : Lemma17CountedPathState n → Prop :=
    fun z =>
      Lemma17CountedPathInv s r n 0 z ∧
        Lemma17ReactionGapLedger z ∧
        Lemma17ReactionLabelInv n 0 z
  let q₀ := lemma17CountedPathInitial s
  have hclosedK :
      ∀ x, P x → ∀ y, K x y ≠ 0 → P y := by
    intro x hx y hy
    exact
      ⟨lemma17CountedPathStep_inv_closed
          n h3 r n 0 s hanchorActive
          x y hx.1 hy,
        lemma17CountedPathStep_gapLedger_closed
          n h3 r n 0 s x y hx.1 hx.2.1 hy,
        lemma17CountedPathStep_labelInv_closed
          n h3 r n 0 x y hx.2.2 hy⟩
  have hclosedGuard :
      ∀ x, P x → ∀ y,
        freeze Guard K x y ≠ 0 → P y := by
    intro x hx y hy
    by_cases hguard : Guard x
    · rw [freeze_of_mem x hguard] at hy
      have hyx : y = x := by
        by_contra hne
        simp [PMF.pure_apply, hne] at hy
      simpa [hyx] using hx
    · rw [freeze_of_not_mem x hguard] at hy
      exact hclosedK x hx y hy
  have hclosed :
      ∀ x, P x → ∀ y,
        freeze Bad (freeze Guard K) x y ≠ 0 →
          P y := by
    intro x hx y hy
    by_cases hbad : Bad x
    · rw [freeze_of_mem x hbad] at hy
      have hyx : y = x := by
        by_contra hne
        simp [PMF.pure_apply, hne] at hy
      simpa [hyx] using hx
    · rw [freeze_of_not_mem x hbad] at hy
      exact hclosedGuard x hx y hy
  have hsuper :
      ∀ x, P x →
        expect
            (freeze Bad (freeze Guard K) x) V ≤
          V x := by
    intro x hx
    by_cases hbad : Bad x
    · rw [freeze_of_mem x hbad, expect_pure]
    · rw [freeze_of_not_mem x hbad]
      by_cases hguard : Guard x
      · rw [freeze_of_mem x hguard, expect_pure]
      · rw [freeze_of_not_mem x hguard]
        have hlabelBad :
            ¬ Lemma17LabelBad Dlabel x := by
          intro hcached
          exact hguard
            (lemma17LabelBad_implies_physical
              n 0 Dlabel x hx.2.2 hcached)
        have hlabel :
            x.reactionYCount ≤
              x.reactionXCount + Dlabel := by
          unfold Lemma17LabelBad at hlabelBad
          omega
        have hdirection :
            x.reaction.typeTwoCount ≤
              x.reaction.typeOneCount + M := by
          unfold Bad Lemma19ReactionAdverseBad at hbad
          omega
        have hgap :
            x.reaction.current.1.ay + targetGap ≤
              x.reaction.current.1.ax :=
          lemma19Reaction_gap_ge
            s r n Dstart Dlabel M targetGap x
            hx.1 hx.2.1 hstart hlabel hdirection
            hbudget
        have hmap :
            (K x).map lemma17CountedPathToReaction =
              infectionReactionTraceStep
                n h3 n 0 x.reaction := by
          exact
            lemma17CountedPathStep_map_reaction_on_inv
              n h3 r n 0 s hanchorActive x hx.1
        calc
          expect (K x) V =
              expect
                ((K x).map
                  lemma17CountedPathToReaction)
                (infectionReactionSafetyPotential
                  targetGap) := by
                    rw [expect_map]
                    rfl
          _ =
              expect
                (infectionReactionTraceStep
                  n h3 n 0 x.reaction)
                (infectionReactionSafetyPotential
                  targetGap) := by
                    rw [hmap]
          _ ≤
              infectionReactionSafetyPotential
                targetGap x.reaction :=
            expect_infectionReactionTraceStep_reactionSafetyPotential
              n targetGap h3 hgap0 hgapn n 0
              x.reaction hgap
          _ = V x := rfl
  have hinitial : P q₀ :=
    ⟨lemma17CountedPathInitial_inv s r n 0,
      lemma17CountedPathInitial_gapLedger s,
      lemma17CountedPathInitial_labelInv n 0 s⟩
  have hθ0 : θ ≠ 0 := by
    exact
      pow_ne_zero _
        (ENNReal.inv_ne_zero.mpr
          (ne_top_of_le_ne_top ENNReal.one_ne_top
            (lemma3SafetyBase_le_one hgapn)))
  have hθtop : θ ≠ ⊤ := by
    exact
      ENNReal.pow_ne_top
        (ENNReal.inv_ne_top.mpr
          (lemma3SafetyBase_ne_zero hgapn))
  have hcontain :
      ∀ z, P z → Bad z → θ ≤ V z := by
    intro z _ hz
    exact
      infectionReactionSafetyPotential_threshold
        n targetGap M hgapn z.reaction
        (by
          simpa [Bad, Lemma19ReactionAdverseBad]
            using hz)
  have hville :
      ⨆ U : ℕ,
          hitProb Bad
            (freeze Bad (freeze Guard K))
            U q₀ ≤
        V q₀ / θ :=
    ville_frozen_of_support_invariant
      (freeze Bad (freeze Guard K))
      Bad P V θ hθ0 hθtop hcontain hclosed
      hsuper q₀ hinitial
  calc
    hitProb (Lemma19ReactionAdverseBad M)
        (freeze (Lemma17PhysicalLabelBad Dlabel)
          (lemma17CountedPathStep n h3 r n 0))
        T (lemma17CountedPathInitial s) =
      hitProb Bad (freeze Guard K) T q₀ := rfl
    _ =
      hitProb Bad
        (freeze Bad (freeze Guard K)) T q₀ := by
      symm
      exact hitProb_freeze_same
        Bad (freeze Guard K) T q₀
    _ ≤
      ⨆ U : ℕ,
        hitProb Bad
          (freeze Bad (freeze Guard K)) U q₀ :=
      le_iSup
        (fun U =>
          hitProb Bad
            (freeze Bad (freeze Guard K)) U q₀) T
    _ ≤ V q₀ / θ := hville
    _ =
      lemma3SafetyBase n targetGap ^ M := by
        simp only [V, q₀, θ,
          infectionReactionSafetyPotential,
          lemma17CountedPathInitial, pow_zero,
          mul_one, one_div]
        rw [← ENNReal.inv_pow, inv_inv]

/-- The full-pool label estimate and the guarded reaction potential give an
unconditional positive-gap reaction tail on the joint path. -/
theorem lemma19CountedPath_full_reaction_hitProb
    (n : ℕ) (h3 : 3 ≤ n)
    (L : ℝ)
    (Dstart Dlabel M targetGap k r B R T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + r = n)
    (hstart :
      s.coarse.1.ay + Dstart ≤ s.coarse.1.ax)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ Dstart)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hDlabel : 0 < Dlabel)
    (hk : 0 < k)
    (hpool : k + 2 = B + R)
    (hmajor : R ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hscale :
      L * ((B + R : ℕ) : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2) :
    hitProb (Lemma19ReactionAdverseBad M)
        (lemma17CountedPathStep n h3 r n 0)
        T (lemma17CountedPathInitial s)
      ≤
    (k + 2 : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-L))) +
      lemma3SafetyBase n targetGap ^ M := by
  let K := lemma17CountedPathStep n h3 r n 0
  let q₀ := lemma17CountedPathInitial s
  let Bad : Lemma17CountedPathState n → Prop :=
    Lemma19ReactionAdverseBad M
  let Guard : Lemma17CountedPathState n → Prop :=
    Lemma17PhysicalLabelBad Dlabel
  have hsplit :
      hitProb Bad K T q₀ ≤
        hitProb Guard K T q₀ +
          hitProb Bad (freeze Guard K) T q₀ :=
    hitProb_le_guard_add_guarded K Bad Guard T q₀
  have hlabel :
      hitProb Guard K T q₀ ≤
        (k + 2 : ℝ≥0∞) *
          (2 * ENNReal.ofReal (Real.exp (-L))) := by
    simpa [Guard, K, q₀] using
      lemma19CountedPath_full_physical_label_hitProb
        n h3 L Dlabel k r B R T s hanchorActive
        hDlabel hk hpool hmajor hx0 hy0 hscale
  have hreaction :
      hitProb Bad (freeze Guard K) T q₀ ≤
        lemma3SafetyBase n targetGap ^ M := by
    simpa [Bad, Guard, K, q₀] using
      lemma19CountedPath_guarded_reaction_hitProb
        n h3 r Dstart Dlabel M targetGap T s
        hanchorActive hstart hbudget hgap0 hgapn
  exact hsplit.trans (add_le_add hlabel hreaction)

/-- Fixed-time terminal form of the full positive-gap reaction tail. -/
theorem lemma19CountedPath_full_reaction_tail
    (n : ℕ) (h3 : 3 ≤ n)
    (L : ℝ)
    (Dstart Dlabel M targetGap k r B R T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + r = n)
    (hstart :
      s.coarse.1.ay + Dstart ≤ s.coarse.1.ax)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ Dstart)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hDlabel : 0 < Dlabel)
    (hk : 0 < k)
    (hpool : k + 2 = B + R)
    (hmajor : R ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hscale :
      L * ((B + R : ℕ) : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2) :
    terminalFailureMass
        (iter (lemma17CountedPathStep n h3 r n 0)
          T (lemma17CountedPathInitial s))
        (fun z => ¬ Lemma19ReactionAdverseBad M z)
      ≤
    (k + 2 : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-L))) +
      lemma3SafetyBase n targetGap ^ M := by
  calc
    terminalFailureMass
        (iter (lemma17CountedPathStep n h3 r n 0)
          T (lemma17CountedPathInitial s))
        (fun z => ¬ Lemma19ReactionAdverseBad M z)
      ≤
        hitProb (Lemma19ReactionAdverseBad M)
          (lemma17CountedPathStep n h3 r n 0)
          T (lemma17CountedPathInitial s) :=
      terminalEventMass_iter_le_hitProb
        (Lemma19ReactionAdverseBad M)
        (lemma17CountedPathStep n h3 r n 0)
        T (lemma17CountedPathInitial s)
    _ ≤
      (k + 2 : ℝ≥0∞) *
          (2 * ENNReal.ofReal (Real.exp (-L))) +
        lemma3SafetyBase n targetGap ^ M :=
      lemma19CountedPath_full_reaction_hitProb
        n h3 L Dstart Dlabel M targetGap
        k r B R T s hanchorActive hstart hbudget
        hgap0 hgapn hDlabel hk hpool hmajor
        hx0 hy0 hscale

/-- The joint terminal label/reaction certificate costs one label tail and
one guarded harmonic reaction tail. -/
theorem lemma19CountedPath_full_positive_gap_safety_tail
    (n : ℕ) (h3 : 3 ≤ n)
    (L : ℝ)
    (Dstart Dlabel M targetGap k r B R T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + r = n)
    (hstart :
      s.coarse.1.ay + Dstart ≤ s.coarse.1.ax)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ Dstart)
    (hgap0 : 0 < targetGap)
    (hgapn : targetGap < n)
    (hDlabel : 0 < Dlabel)
    (hk : 0 < k)
    (hpool : k + 2 = B + R)
    (hmajor : R ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hscale :
      L * ((B + R : ℕ) : ℝ) ≤
        ((Dlabel : ℝ) / 2) ^ 2) :
    terminalFailureMass
        (iter (lemma17CountedPathStep n h3 r n 0)
          T (lemma17CountedPathInitial s))
        (fun z =>
          ¬ Lemma17PhysicalLabelBad Dlabel z ∧
            ¬ Lemma19ReactionAdverseBad M z)
      ≤
    (k + 2 : ℝ≥0∞) *
        (2 * ENNReal.ofReal (Real.exp (-L))) +
      lemma3SafetyBase n targetGap ^ M := by
  let K := lemma17CountedPathStep n h3 r n 0
  let q₀ := lemma17CountedPathInitial s
  let Guard : Lemma17CountedPathState n → Prop :=
    Lemma17PhysicalLabelBad Dlabel
  let Bad : Lemma17CountedPathState n → Prop :=
    Lemma19ReactionAdverseBad M
  have hterminal :
      terminalFailureMass (iter K T q₀)
          (fun z => ¬ Guard z ∧ ¬ Bad z) ≤
        hitProb (fun z => Guard z ∨ Bad z) K T q₀ := by
    simpa only [not_or] using
      terminalEventMass_iter_le_hitProb
        (fun z => Guard z ∨ Bad z) K T q₀
  have hsplit :
      hitProb (fun z => Guard z ∨ Bad z) K T q₀ ≤
        hitProb Guard K T q₀ +
          hitProb Bad (freeze Guard K) T q₀ :=
    hitProb_union_le_guard_add_guarded
      K Bad Guard T q₀
  have hlabel :
      hitProb Guard K T q₀ ≤
        (k + 2 : ℝ≥0∞) *
          (2 * ENNReal.ofReal (Real.exp (-L))) := by
    simpa [Guard, K, q₀] using
      lemma19CountedPath_full_physical_label_hitProb
        n h3 L Dlabel k r B R T s hanchorActive
        hDlabel hk hpool hmajor hx0 hy0 hscale
  have hreaction :
      hitProb Bad (freeze Guard K) T q₀ ≤
        lemma3SafetyBase n targetGap ^ M := by
    simpa [Bad, Guard, K, q₀] using
      lemma19CountedPath_guarded_reaction_hitProb
        n h3 r Dstart Dlabel M targetGap T s
        hanchorActive hstart hbudget hgap0 hgapn
  exact
    hterminal.trans
      (hsplit.trans (add_le_add hlabel hreaction))

/-- Label and adverse-reaction budgets alone preserve the positive physical
gap; no all-active exposure cap is needed. -/
theorem lemma19CountedPath_gap_good_of_no_label_or_adverse
    {n : ℕ}
    (s : InfectionRevealPhysicalState n)
    (k A Dstart Dlabel M targetGap : ℕ)
    (q : Lemma17CountedPathState n)
    (hinv : Lemma17CountedPathInv s k A 0 q)
    (hledger : Lemma17ReactionGapLedger q)
    (hstart :
      s.coarse.1.ay + Dstart ≤ s.coarse.1.ax)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ Dstart)
    (hlabelBad : ¬ Lemma17LabelBad Dlabel q)
    (hreactionBad :
      ¬ Lemma19ReactionAdverseBad M q) :
    q.counted.path.current.coarse.1.ay + targetGap ≤
        q.counted.path.current.coarse.1.ax ∧
      q.reaction.current =
        q.counted.path.current.coarse := by
  have hlabel :
      q.reactionYCount ≤
        q.reactionXCount + Dlabel := by
    unfold Lemma17LabelBad at hlabelBad
    omega
  have hdirection :
      q.reaction.typeTwoCount ≤
        q.reaction.typeOneCount + M := by
    unfold Lemma19ReactionAdverseBad at hreactionBad
    omega
  have hnotGap :=
    lemma19Reaction_not_majorityStopped
      s k A Dstart Dlabel M targetGap q
      hinv hledger hstart hlabel hdirection hbudget
  have halign :=
    lemma17Reaction_align_of_not_gapStopped
      s k A 0 q hinv (by simpa using hnotGap)
  constructor
  · rw [← halign]
    exact
      lemma19Reaction_gap_ge
        s k A Dstart Dlabel M targetGap q
        hinv hledger hstart hlabel hdirection hbudget
  · exact halign

/-- Same-horizon Lemma 19 assembly using the positive-gap harmonic reaction
tail instead of a finite-exposure Hoeffding event. -/
theorem lemma19CountedPath_positive_gap_stage
    (n : ℕ) (h3 : 3 ≤ n)
    (k A T Dstart Dlabel M targetGap : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = A)
    (hstart :
      s.coarse.1.ay + Dstart ≤ s.coarse.1.ax)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ Dstart)
    (εClock εLabel εReaction : ℝ≥0∞)
    (hclock :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A 0) T
            (lemma17CountedPathInitial s))
          (fun z =>
            A ≤ z.counted.path.current.coarse.1.active)
        ≤ εClock)
    (hlabel :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A 0) T
            (lemma17CountedPathInitial s))
          (fun z => ¬ Lemma17LabelBad Dlabel z)
        ≤ εLabel)
    (hreaction :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A 0) T
            (lemma17CountedPathInitial s))
          (fun z =>
            ¬ Lemma19ReactionAdverseBad M z)
        ≤ εReaction) :
    terminalFailureMass
        (iter (lemma17CountedPathStep n h3 k A 0) T
          (lemma17CountedPathInitial s))
        (Lemma19StageGood A targetGap)
      ≤
    (εClock + εLabel) + εReaction := by
  let K := lemma17CountedPathStep n h3 k A 0
  let q₀ := lemma17CountedPathInitial s
  let μ := iter K T q₀
  let Reached : Lemma17CountedPathState n → Prop :=
    fun z => A ≤ z.counted.path.current.coarse.1.active
  let LabelGood : Lemma17CountedPathState n → Prop :=
    fun z => ¬ Lemma17LabelBad Dlabel z
  let ReactionGood : Lemma17CountedPathState n → Prop :=
    fun z => ¬ Lemma19ReactionAdverseBad M z
  let Certificate : Lemma17CountedPathState n → Prop :=
    fun z =>
      (Reached z ∧ LabelGood z) ∧ ReactionGood z
  have hcertificate :
      ∀ z, μ z ≠ 0 → Certificate z →
        Lemma19StageGood A targetGap z := by
    intro z hzμ hzcert
    rcases hzcert with
      ⟨⟨hzReached, hzLabel⟩, hzReaction⟩
    have hinv :
        Lemma17CountedPathInv s k A 0 z :=
      lemma17CountedPath_iter_inv
        n h3 k A 0 T s hanchorActive z
        (by simpa [μ, K, q₀] using hzμ)
    have hledger :
        Lemma17ReactionGapLedger z :=
      lemma17CountedPath_iter_gapLedger
        n h3 k A 0 T s hanchorActive z
        (by simpa [μ, K, q₀] using hzμ)
    have hgap :=
      lemma19CountedPath_gap_good_of_no_label_or_adverse
        s k A Dstart Dlabel M targetGap z
        hinv hledger hstart hbudget
        (by simpa [LabelGood] using hzLabel)
        (by simpa [ReactionGood] using hzReaction)
    exact ⟨hzReached, hgap.1⟩
  have htarget :
      terminalFailureMass μ
          (Lemma19StageGood A targetGap) ≤
        terminalFailureMass μ Certificate := by
    unfold terminalFailureMass
    exact ENNReal.tsum_le_tsum fun z => by
      by_cases hzμ : μ z = 0
      · simp [hzμ]
      · by_cases hzCert : Certificate z
        · have hzTarget :=
            hcertificate z hzμ hzCert
          simp [hzCert, hzTarget]
        · by_cases hzTarget :
              Lemma19StageGood A targetGap z
          · simp [hzCert, hzTarget]
          · simp [hzCert, hzTarget]
  have hcertBound :
      terminalFailureMass μ Certificate ≤
        (εClock + εLabel) + εReaction := by
    calc
      terminalFailureMass μ Certificate
          ≤ terminalFailureMass μ
                (fun z => Reached z ∧ LabelGood z) +
              terminalFailureMass μ ReactionGood :=
        terminalFailureMass_inter_le
          μ (fun z => Reached z ∧ LabelGood z)
          ReactionGood
      _ ≤
          (terminalFailureMass μ Reached +
              terminalFailureMass μ LabelGood) +
            terminalFailureMass μ ReactionGood := by
        exact add_le_add
          (terminalFailureMass_inter_le
            μ Reached LabelGood)
          le_rfl
      _ ≤
          (εClock + εLabel) + εReaction := by
        exact add_le_add
          (add_le_add
            (by simpa [μ, K, q₀, Reached] using hclock)
            (by simpa [μ, K, q₀, LabelGood] using hlabel))
          (by
            simpa [μ, K, q₀, ReactionGood]
              using hreaction)
  exact htarget.trans hcertBound

/-- Same-horizon assembly consuming the genuine physical-prefix/reaction
certificate produced by the guarded potential argument. -/
theorem lemma19CountedPath_positive_gap_physical_stage
    (n : ℕ) (h3 : 3 ≤ n)
    (k A T Dstart Dlabel M targetGap : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = A)
    (hstart :
      s.coarse.1.ay + Dstart ≤ s.coarse.1.ax)
    (hbudget :
      targetGap + Dlabel + 2 * M ≤ Dstart)
    (εClock εSafety : ℝ≥0∞)
    (hclock :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A 0) T
            (lemma17CountedPathInitial s))
          (fun z =>
            A ≤ z.counted.path.current.coarse.1.active)
        ≤ εClock)
    (hsafety :
      terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A 0) T
            (lemma17CountedPathInitial s))
          (fun z =>
            ¬ Lemma17PhysicalLabelBad Dlabel z ∧
              ¬ Lemma19ReactionAdverseBad M z)
        ≤ εSafety) :
    terminalFailureMass
        (iter (lemma17CountedPathStep n h3 k A 0) T
          (lemma17CountedPathInitial s))
        (Lemma19StageGood A targetGap)
      ≤ εClock + εSafety := by
  let K := lemma17CountedPathStep n h3 k A 0
  let q₀ := lemma17CountedPathInitial s
  let μ := iter K T q₀
  let Reached : Lemma17CountedPathState n → Prop :=
    fun z => A ≤ z.counted.path.current.coarse.1.active
  let SafetyGood : Lemma17CountedPathState n → Prop :=
    fun z =>
      ¬ Lemma17PhysicalLabelBad Dlabel z ∧
        ¬ Lemma19ReactionAdverseBad M z
  let Certificate : Lemma17CountedPathState n → Prop :=
    fun z => Reached z ∧ SafetyGood z
  have hcertificate :
      ∀ z, μ z ≠ 0 → Certificate z →
        Lemma19StageGood A targetGap z := by
    intro z hzμ hzcert
    rcases hzcert with
      ⟨hzReached, hzPhysical, hzReaction⟩
    have hinv :
        Lemma17CountedPathInv s k A 0 z :=
      lemma17CountedPath_iter_inv
        n h3 k A 0 T s hanchorActive z
        (by simpa [μ, K, q₀] using hzμ)
    have hledger :
        Lemma17ReactionGapLedger z :=
      lemma17CountedPath_iter_gapLedger
        n h3 k A 0 T s hanchorActive z
        (by simpa [μ, K, q₀] using hzμ)
    have hlabelInv :
        Lemma17ReactionLabelInv A 0 z :=
      lemma17CountedPath_iter_labelInv
        n h3 k A 0 T s z
        (by simpa [μ, K, q₀] using hzμ)
    have hcached :
        ¬ Lemma17LabelBad Dlabel z := by
      intro hbad
      exact hzPhysical
        (lemma17LabelBad_implies_physical
          A 0 Dlabel z hlabelInv hbad)
    have hgap :=
      lemma19CountedPath_gap_good_of_no_label_or_adverse
        s k A Dstart Dlabel M targetGap z
        hinv hledger hstart hbudget
        hcached hzReaction
    exact ⟨hzReached, hgap.1⟩
  have htarget :
      terminalFailureMass μ
          (Lemma19StageGood A targetGap) ≤
        terminalFailureMass μ Certificate := by
    unfold terminalFailureMass
    exact ENNReal.tsum_le_tsum fun z => by
      by_cases hzμ : μ z = 0
      · simp [hzμ]
      · by_cases hzCert : Certificate z
        · have hzTarget :=
            hcertificate z hzμ hzCert
          simp [hzCert, hzTarget]
        · by_cases hzTarget :
              Lemma19StageGood A targetGap z
          · simp [hzCert, hzTarget]
          · simp [hzCert, hzTarget]
  have hcertBound :
      terminalFailureMass μ Certificate ≤
        εClock + εSafety := by
    calc
      terminalFailureMass μ Certificate
          ≤ terminalFailureMass μ Reached +
              terminalFailureMass μ SafetyGood :=
        terminalFailureMass_inter_le
          μ Reached SafetyGood
      _ ≤ εClock + εSafety :=
        add_le_add
          (by simpa [μ, K, q₀, Reached] using hclock)
          (by simpa [μ, K, q₀, SafetyGood] using hsafety)
  exact htarget.trans hcertBound

end

end Tri

#print axioms Tri.hitProb_freeze_same
#print axioms Tri.hitProb_le_guard_add_guarded
#print axioms Tri.hitProb_union_le_guard_add_guarded
#print axioms Tri.infectionReactionSafetyPotential_threshold
#print axioms Tri.lemma19CountedPath_guarded_reaction_hitProb
#print axioms Tri.lemma19CountedPath_full_reaction_hitProb
#print axioms Tri.lemma19CountedPath_full_reaction_tail
#print axioms Tri.lemma19CountedPath_full_positive_gap_safety_tail
#print axioms Tri.lemma19CountedPath_gap_good_of_no_label_or_adverse
#print axioms Tri.lemma19CountedPath_positive_gap_stage
#print axioms Tri.lemma19CountedPath_positive_gap_physical_stage
