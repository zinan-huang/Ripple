/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.Lemma17JointLabelTail

/-!
# Lemma 17 label tails for an arbitrary remaining pool

Later activation stages do not start with one active molecule.  The relevant
urn size is therefore the current inactive pool `nu`, not `n - 1`.  This file
restates the exponent calculation at that general pool size and transfers it
to the physical maximal-prefix process.
-/

namespace Tri

open scoped ENNReal

noncomputable section

/-- The Lemma 16 exponent calculation only needs the current urn-pool size,
not the initial one-active identity relation. -/
theorem lemma17_pool_exponent_floor
    (qq rho : ℝ) (a k u nu : ℕ)
    (hq : 0 ≤ qq)
    (hrho : qq * (a : ℝ) ≤ rho ^ 2)
    (hk : k + 1 = a)
    (huk : u + k + 1 = nu)
    (hquarter : 4 * a ≤ nu + 1)
    (hk0 : 0 < k) :
    3 / 16 * qq
      ≤ (rho / (2 * (nu : ℝ))) ^ 2 *
          (nu : ℝ) * ((u : ℝ) + 1) / (k : ℝ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast hk0
  have hnuR : (0 : ℝ) < (nu : ℝ) := by
    have : 0 < nu := by omega
    exact_mod_cast this
  have haR : (a : ℝ) = (k : ℝ) + 1 := by
    exact_mod_cast hk.symm
  have hu1 :
      (u : ℝ) + 1 = (nu : ℝ) - (k : ℝ) := by
    have h :
        ((u + k + 1 : ℕ) : ℝ) = (nu : ℝ) := by
      exact_mod_cast huk
    push_cast at h
    linarith
  have hqu :
      4 * ((k : ℝ) + 1) ≤ (nu : ℝ) + 1 := by
    have h :
        ((4 * a : ℕ) : ℝ) ≤ ((nu + 1 : ℕ) : ℝ) := by
      exact_mod_cast hquarter
    push_cast at h
    linarith [haR]
  have hexp :
      (rho / (2 * (nu : ℝ))) ^ 2 *
          (nu : ℝ) * ((u : ℝ) + 1) / (k : ℝ) =
        rho ^ 2 * ((nu : ℝ) - (k : ℝ)) /
          (4 * (nu : ℝ) * (k : ℝ)) := by
    rw [hu1]
    field_simp
    ring
  rw [hexp]
  rw [le_div_iff₀ (by positivity)]
  have hpoly :
      (3 : ℝ) / 4 * (nu : ℝ) * (k : ℝ) ≤
        ((k : ℝ) + 1) *
          ((nu : ℝ) - (k : ℝ)) := by
    nlinarith [hqu, hkR, hnuR]
  have hnuk : (0 : ℝ) ≤ (nu : ℝ) - (k : ℝ) := by
    linarith
  have hkey :
      (3 : ℝ) / 4 * qq * (nu : ℝ) * (k : ℝ) ≤
        qq * (((k : ℝ) + 1) *
          ((nu : ℝ) - (k : ℝ))) := by
    nlinarith [hpoly, hq]
  have hrho' :
      qq * ((k : ℝ) + 1) ≤ rho ^ 2 := by
    rw [← haR]
    exact hrho
  nlinarith [hkey, hrho', hnuk, hq]

/-- Negative-tilt urn tail for an arbitrary current inactive pool. -/
theorem lemma17_urn_window_tail_Y_pool
    (q rho a k u nu R B : ℕ)
    (hqa : q * a ≤ rho ^ 2)
    (hk : k + 1 = a)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hquarter : 4 * a ≤ nu + 1)
    (hk0 : 0 < k) :
    ⨆ T : ℕ,
        hitProb (Lemma16UrnWindowBadY rho u k R B)
          urnStopped T (B, R)
      ≤ lemma16UrnError q := by
  have hsum : u + k + 1 = B + R := by omega
  have htail :=
    urn_window_tail_telescope_neg
      ((rho : ℝ) / (2 * ((B : ℝ) + (R : ℝ))))
      u k B R (by positivity) hsum hk0
  refine htail.trans ?_
  unfold lemma16UrnError
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hBRReal :
      (B : ℝ) + (R : ℝ) = (nu : ℝ) := by
    have h : B + R = nu := by omega
    exact_mod_cast h
  have hexp :
      2 * ((rho : ℝ) /
            (2 * ((B : ℝ) + (R : ℝ)))) ^ 2 /
          (2 * (k : ℝ) /
            (((u : ℝ) + 1) *
              ((B : ℝ) + (R : ℝ)))) =
        ((rho : ℝ) / (2 * (nu : ℝ))) ^ 2 *
          (nu : ℝ) * ((u : ℝ) + 1) / (k : ℝ) := by
    rw [hBRReal]
    field_simp
  rw [hexp]
  have hfloor :=
    lemma17_pool_exponent_floor
      (q : ℝ) (rho : ℝ) a k u nu
      (by positivity)
      (by exact_mod_cast hqa)
      hk huk hquarter hk0
  linarith

/-- Physical maximal-prefix label tail from any current inactive pool. -/
theorem infectionRevealPhysical_lemma17_max_prefix_tail_pool
    (n : ℕ) (h3 : 3 ≤ n)
    (q rho a k u nu R B : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hqa : q * a ≤ rho ^ 2)
    (hk : k + 1 = a)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hquarter : 4 * a ≤ nu + 1)
    (hmajor : R ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    everHit
        (fun z =>
          Lemma17LogicalMaxLabelBad
            s.inactive.initialLabel rho
            (InfectionRevealPrefixCheckpoint.ofPhysical
              (InfectionRevealFirstKQuotient.ofPath k z)))
        (infectionRevealPhysicalFirstKStep n h3 k)
        (infectionRevealPhysicalPathInitial s)
      ≤ lemma16UrnError q := by
  have hsum : R + B = u + k + 1 := by omega
  have hidscard :
      s.inactive.ids.card = R + B := by
    calc
      s.inactive.ids.card =
          s.inactive.xIds.card +
            s.inactive.yIds.card := by
        rw [
          InfectionInactiveView.xIds_card_add_yIds_card]
      _ = R + B := by omega
  have hroom : k + 2 ≤ s.inactive.ids.card := by
    omega
  calc
    everHit
        (fun z =>
          Lemma17LogicalMaxLabelBad
            s.inactive.initialLabel rho
            (InfectionRevealPrefixCheckpoint.ofPhysical
              (InfectionRevealFirstKQuotient.ofPath k z)))
        (infectionRevealPhysicalFirstKStep n h3 k)
        (infectionRevealPhysicalPathInitial s)
        ≤
      everHit
        (Lemma17LogicalMaxLabelBad
          s.inactive.initialLabel rho)
        (InfectionRevealPrefixCheckpoint.oneStep n k)
        (.live s.inactive []) :=
      infectionRevealPhysicalFirstK_initial_everHit_le_logical
        n h3 k s hk0 hroom
          (Lemma17LogicalMaxLabelBad
            s.inactive.initialLabel rho)
    _ ≤
      everHit
        (Lemma16UrnWindowBadY rho u k R B)
        urnStopped (B, R) :=
      lemma17_logical_max_prefix_everHit_le_urn
        s.inactive rho u k R B hsum hmajor
        hx0 hy0 hk0 hroom
    _ ≤ lemma16UrnError q := by
      unfold everHit
      exact
        lemma17_urn_window_tail_Y_pool
          q rho a k u nu R B
          hqa hk huk hRB hquarter hk0

/-- The arbitrary-pool physical tail transfers to the stopped joint path. -/
theorem lemma17CountedPath_label_tail_pool
    (n : ℕ) (h3 : 3 ≤ n)
    (qpar rho sampleSize k u nu R B A G T : ℕ)
    (s : InfectionRevealPhysicalState n)
    (hanchorActive : s.coarse.1.active + k = A)
    (hqa : qpar * sampleSize ≤ rho ^ 2)
    (hk : k + 1 = sampleSize)
    (huk : u + k + 1 = nu)
    (hRB : R + B = nu)
    (hquarter : 4 * sampleSize ≤ nu + 1)
    (hmajor : R ≤ B)
    (hx0 : s.inactive.xIds.card = B)
    (hy0 : s.inactive.yIds.card = R)
    (hk0 : 0 < k) :
    terminalFailureMass
        (iter (lemma17CountedPathStep n h3 k A G) T
          (lemma17CountedPathInitial s))
        (fun z => ¬ Lemma17LabelBad (rho + 1) z)
      ≤ lemma16UrnError qpar := by
  let K := lemma17CountedPathStep n h3 k A G
  let q₀ := lemma17CountedPathInitial s
  let μ := iter K T q₀
  let LabelBad : Lemma17CountedPathState n → Prop :=
    Lemma17LabelBad (rho + 1)
  let PathBad : InfectionRevealPhysicalPathState n → Prop :=
    fun z =>
      Lemma17LogicalMaxLabelBad
        s.inactive.initialLabel rho
        (InfectionRevealPrefixCheckpoint.ofPhysical
          (InfectionRevealFirstKQuotient.ofPath k z))
  let P : Lemma17CountedPathState n → Prop :=
    fun z =>
      Lemma17CountedPathInv s k A G z ∧
        Lemma17ReactionLabelInv A G z
  have hclosed :
      ∀ x, P x → ∀ y, K x y ≠ 0 → P y := by
    intro x hx y hy
    exact
      ⟨lemma17CountedPathStep_inv_closed
          n h3 k A G s hanchorActive x y hx.1 hy,
        lemma17CountedPathStep_labelInv_closed
          n h3 k A G x y hx.2 hy⟩
  have hcontain :
      ∀ z, P z → LabelBad z →
        PathBad (lemma17CountedPathToPath z) := by
    intro z hz hbad
    exact
      lemma17LabelBad_succ_implies_logicalMax
        s k A G rho z hz.1 hz.2 hbad
  have hinitial : P q₀ :=
    ⟨lemma17CountedPathInitial_inv s k A G,
      lemma17CountedPathInitial_labelInv A G s⟩
  have hterminal :
      terminalFailureMass μ (fun z => ¬ LabelBad z) ≤
        hitProb LabelBad K T q₀ :=
    terminalEventMass_iter_le_hitProb
      LabelBad K T q₀
  have hmono :
      hitProb LabelBad K T q₀ ≤
        hitProb
          (fun z =>
            PathBad (lemma17CountedPathToPath z))
          K T q₀ :=
    hitProb_mono_target_of_support_invariant
      K LabelBad
      (fun z =>
        PathBad (lemma17CountedPathToPath z))
      P hclosed hcontain T q₀ hinitial
  have hintertwines :
      Intertwines lemma17CountedPathToPath K
        (infectionRevealPhysicalFirstKStep n h3 k) :=
    lemma17CountedPathStep_map_path n h3 k A G
  have htransfer :
      hitProb
          (fun z =>
            PathBad (lemma17CountedPathToPath z))
          K T q₀ =
        hitProb PathBad
          (infectionRevealPhysicalFirstKStep n h3 k)
          T (infectionRevealPhysicalPathInitial s) := by
    simpa [q₀, lemma17CountedPathInitial,
      lemma17CountedPathToPath,
      lemma16CountedPathInitial] using
      hitProb_transfer hintertwines PathBad T q₀
  have hfinite :
      hitProb PathBad
          (infectionRevealPhysicalFirstKStep n h3 k)
          T (infectionRevealPhysicalPathInitial s) ≤
        everHit PathBad
          (infectionRevealPhysicalFirstKStep n h3 k)
          (infectionRevealPhysicalPathInitial s) := by
    exact le_iSup
      (fun U =>
        hitProb PathBad
          (infectionRevealPhysicalFirstKStep n h3 k)
          U (infectionRevealPhysicalPathInitial s)) T
  have hphysical :
      everHit PathBad
          (infectionRevealPhysicalFirstKStep n h3 k)
          (infectionRevealPhysicalPathInitial s) ≤
        lemma16UrnError qpar := by
    simpa [PathBad] using
      infectionRevealPhysical_lemma17_max_prefix_tail_pool
        n h3 qpar rho sampleSize k u nu R B s
        hqa hk huk hRB hquarter hmajor hx0 hy0 hk0
  calc
    terminalFailureMass
          (iter (lemma17CountedPathStep n h3 k A G) T
            (lemma17CountedPathInitial s))
          (fun z => ¬ Lemma17LabelBad (rho + 1) z) ≤
        hitProb LabelBad K T q₀ := by
          simpa [μ, K, q₀, LabelBad] using hterminal
    _ ≤
        hitProb
          (fun z =>
            PathBad (lemma17CountedPathToPath z))
          K T q₀ := hmono
    _ =
        hitProb PathBad
          (infectionRevealPhysicalFirstKStep n h3 k)
          T (infectionRevealPhysicalPathInitial s) :=
      htransfer
    _ ≤
        everHit PathBad
          (infectionRevealPhysicalFirstKStep n h3 k)
          (infectionRevealPhysicalPathInitial s) :=
      hfinite
    _ ≤ lemma16UrnError qpar := hphysical

end

end Tri

#print axioms Tri.lemma17_pool_exponent_floor
#print axioms Tri.lemma17_urn_window_tail_Y_pool
#print axioms Tri.infectionRevealPhysical_lemma17_max_prefix_tail_pool
#print axioms Tri.lemma17CountedPath_label_tail_pool
