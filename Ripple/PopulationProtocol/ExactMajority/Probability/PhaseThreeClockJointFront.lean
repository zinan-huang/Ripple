-- Ripple/PopulationProtocol/ExactMajority/Probability/PhaseThreeClockJointFront.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockMarkCoverage
import Ripple.PopulationProtocol.ExactMajority.Probability.PhaseThreeClockSquaringCollapse

/-!
The deterministic P6 induction on the actual virtual labelled path.
The hypotheses are the separately charged local events, not a restarted
conditional law on their intersection. No F_Q assertion is made.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockJointFront

open TimeTheorem PairLog PhaseThreeClockVirtual PhaseThreeClockGatedLaw
  PhaseThreeClockSeedTails PhaseThreeClockThinning PhaseThreeClockShapeFreeze
  PhaseThreeClockRareDrips PhaseThreeClockRareDripCharging
  PhaseThreeClockMarkedShape PhaseThreeClockSharpActivationSeed
  PhaseThreeClockMacroscopicActivation PhaseThreeClockMarkCoverage
  PhaseThreeClockSquaringCollapse
open PhaseThreeModel.Numeric

variable {L K n : ℕ}

theorem coarse_contact_chain (init : Cfg L K) (C : Finset (Fin init.card))
    (tau : ℕ → ℕ) (Q : ℕ) (ω : Ω L K)
    (hstep : ∀ ell, 1 ≤ ell → ell < Q →
      maskContacts init C (tau ell) (tau (ell + 1)) ω ≤ 100 * C.card) :
    ∀ j r, 1 ≤ j → j + r ≤ Q →
      maskContacts init C (tau j) (tau (j + r)) ω ≤ 100 * r * C.card := by
  classical
  intro j r hj
  induction r with
  | zero =>
      intro _
      simp [maskContacts]
  | succ r ih =>
      intro htop
      have hi := ih (by omega)
      have hs := hstep (j + r) (by omega) (by omega)
      calc
        maskContacts init C (tau j) (tau (j + (r + 1))) ω ≤
            maskContacts init C (tau j) (tau (j + r)) ω +
            maskContacts init C (tau (j + r)) (tau (j + (r + 1))) ω :=
          maskContacts_triangle init C _ _ _ ω
        _ ≤ 100 * r * C.card + 100 * C.card := by
          apply add_le_add hi
          simpa only [Nat.add_assoc] using hs
        _ = 100 * (r + 1) * C.card := by ring

theorem activation_coarse_chain (init : Cfg L K) (C : Finset (Fin init.card))
    (tau : ℕ → ℕ) (alpha Q : ℕ) (ω : Ω L K)
    (hbase : maskContacts init C alpha (tau 1) ω ≤ 100 * C.card)
    (hstep : ∀ ell, 1 ≤ ell → ell < Q →
      maskContacts init C (tau ell) (tau (ell + 1)) ω ≤ 100 * C.card)
    (i : ℕ) (hi : 1 ≤ i) (hiQ : i ≤ Q) :
    maskContacts init C alpha (tau i) ω ≤ 100 * i * C.card := by
  have he : 1 + (i - 1) = i := by omega
  have hchain := coarse_contact_chain init C tau Q ω hstep 1 (i - 1)
    (by omega) (by omega)
  rw [he] at hchain
  calc
    maskContacts init C alpha (tau i) ω ≤
        maskContacts init C alpha (tau 1) ω +
        maskContacts init C (tau 1) (tau i) ω :=
      maskContacts_triangle init C _ _ _ ω
    _ ≤ 100 * C.card + 100 * (i - 1) * C.card := add_le_add hbase hchain
    _ = 100 * (1 + (i - 1)) * C.card := by ring
    _ = 100 * i * C.card := by rw [he]

def ThroughBulkShape (init : InputCfg n) (C : Finset (Fin init.card))
    (s : ℕ) (tau : ℕ → ℕ) (ell : ℕ) (ω : InputLog n) : Prop :=
  ∀ v, s ≤ v → v ≤ tau ell →
    shapeCutoff C.card ≤ frontCount (virtualLabels init ω v) ell →
    frontCount (virtualLabels init ω v) ell ≤ StageEventSpec.bulkThreshold C.card →
    C.card * frontCount (virtualLabels init ω v) (ell + 1) ≤
      frontCount (virtualLabels init ω v) ell ^ 2

/-- Joint A_i/F_i induction. The last component records the nontrivial
first-hit width fact needed to pass from first hits to all raw times. -/
theorem joint_front_induction (init : InputCfg n)
    (hn : populationThreshold ≤ n) (C : Finset (Fin init.card))
    (s alpha : ℕ) (f tau : ℕ → ℕ) (ω : InputLog n)
    (hseed : ω ∈ seedPrefix init s)
    (hmask : C = clockSet (labelsAt init ω s))
    (hsafe : ∀ v, s ≤ v → shapeSafeAt init C s v ω)
    (ha : macroscopicTime init s ω = (alpha : WithTop ℕ))
    (hfirst : ∀ ell, 1 ≤ ell → ell ≤ clockCap n →
      StageEventSpec.firstAfter
        (fun t => 1 ≤ frontCount (virtualLabels init ω t) ell) s (f ell))
    (hbulk : ∀ ell, 1 ≤ ell → ell ≤ clockCap n →
      StageEventSpec.firstAfter
        (fun t => StageEventSpec.bulkThreshold C.card ≤
          frontCount (virtualLabels init ω t) ell) s (tau ell))
    (hsharp : ω ∉ sharpActivationFailure init s C.card)
    (hmarked : ∀ ell, 1 ≤ ell → ell < clockCap n →
      ω ∉ markedShapeFailure init C ell s)
    (hraw : ∀ ell, 1 ≤ ell → ell ≤ clockCap n →
      tau ell ≤ f ell + firstHitHorizon n)
    (hbase : maskContacts init C alpha (tau 1) ω ≤ 100 * C.card)
    (hcoarse : ∀ ell, 1 ≤ ell → ell < clockCap n →
      maskContacts init C (tau ell) (tau (ell + 1)) ω ≤ 100 * C.card)
    (hrare : ∀ k, 1 ≤ k → k + frontWidth C.card ≤ clockCap n →
      rareDripCount init k (shapeCutoff C.card)
        (shapeCutoff C.card ^ 2 / C.card) (f k) (firstHitHorizon n) ω <
          ((frontWidth C.card - 1 : ℕ) : ℝ)) :
    ∀ i, 1 ≤ i → i ≤ clockCap n →
      maskContacts init C (max (f i) alpha) (tau i) ω ≤ fineTicks C.card ∧
      (i < clockCap n → ThroughBulkShape init C s tau i ω) ∧
      (2 * frontWidth C.card < i → tau (i - 2 * frontWidth C.card) ≤ f i) := by
  have hcount : clockCount (labelsAt init ω s) = C.card := by
    change (clockSet (labelsAt init ω s)).card = C.card
    rw [← hmask]
  obtain ⟨hm, hlo, hCn⟩ := seed_clock_calibration_inputs init hn ω s C.card hseed hcount
  obtain ⟨hC, hx, -⟩ := logarithmic_inputs hm hlo hCn
  have hCnpos : 0 < C.card := by exact_mod_cast hC
  have hd : 38 ≤ frontWidth C.card := (frontWidth_bounds hx).1
  have hw : 1 ≤ shapeCutoff C.card := by
    have hp := Real.rpow_pos_of_pos hC (17 / 25 : ℝ)
    have hc : (C.card : ℝ) ^ (17 / 25 : ℝ) ≤ (shapeCutoff C.card : ℝ) :=
      Nat.le_ceil _
    have hp' : (0 : ℝ) < (shapeCutoff C.card : ℝ) := hp.trans_le hc
    have : 0 < shapeCutoff C.card := by exact_mod_cast hp'
    omega
  have hwb : shapeCutoff C.card ≤ StageEventSpec.bulkThreshold C.card :=
    (cutoff_calibration hC hx (le_refl C.card)).2.2.2.1.le
  have hshape_of_budget (i : ℕ) (hi : 1 ≤ i) (hiQ : i < clockCap n)
      (hA : maskContacts init C (max (f i) alpha) (tau i) ω ≤ fineTicks C.card) :
      ThroughBulkShape init C s tau i ω := by
    intro v hsv hvtau hlow hupp
    exact shape_through_bulk_of_tick_budget init hn C s i alpha (f i) (tau i) ω
      hseed hmask ha (hfirst i hi hiQ.le) hsharp (hmarked i hi hiQ) hA
      v hsv hvtau (hsafe v hsv).2 hlow hupp
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hi hiQ
      by_cases hshort : i ≤ 2 * frontWidth C.card
      · have hA : maskContacts init C (max (f i) alpha) (tau i) ω ≤ fineTicks C.card := by
          calc
            _ ≤ maskContacts init C alpha (tau i) ω :=
              maskContacts_antitone_left init C alpha (max (f i) alpha)
                (tau i) (le_max_right _ _) ω
            _ ≤ 100 * i * C.card :=
              activation_coarse_chain init C tau alpha (clockCap n) ω
                hbase hcoarse i hi hiQ
            _ ≤ 100 * (2 * frontWidth C.card) * C.card :=
              Nat.mul_le_mul_right C.card (Nat.mul_le_mul_left 100 hshort)
            _ = fineTicks C.card := by unfold fineTicks; ring
        exact ⟨hA, fun hiQ' => hshape_of_budget i hi hiQ' hA, by intro hlong; omega⟩
      · let d := frontWidth C.card
        let k := i - d
        let j := i - 2 * d
        have hdpos : 2 ≤ d := by dsimp only [d]; omega
        have hlong : 2 * d < i := by dsimp only [d]; omega
        have hk : 1 ≤ k := by dsimp only [k]; omega
        have hj : 1 ≤ j := by dsimp only [j]; omega
        have hki : k < i := by dsimp only [k]; omega
        have hji : j < i := by dsimp only [j]; omega
        have hkd : k + d = i := by dsimp only [k]; omega
        have hjd : j + d = k := by dsimp only [j, k]; omega
        have hjtwo : j + 2 * d = i := by dsimp only [j]; omega
        have hFk : ThroughBulkShape init C s tau k ω :=
          (ih k hki hk (by omega)).2.1 (by omega)
        have hhigh : shapeCutoff C.card ≤
            frontCount (virtualLabels init ω (f i)) k := by
          by_contra hsmall
          have hsafeMax : shapeSafeAt init C s (max (f (k + d)) (tau k)) ω :=
            hsafe _ ((hbulk k hk (by omega)).1.trans (le_max_right _ _))
          have hcharged := sparse_chain_implies_rare_count init C s k d
            (shapeCutoff C.card) (StageEventSpec.bulkThreshold C.card) (firstHitHorizon n)
            hCnpos hk hdpos hw hwb
            (by simpa only [clockCap, clockHours, hkd] using hiQ)
            f (tau k) ω
            (fun ell hkel hle => hfirst ell (by omega) (by omega))
            hsafeMax (hbulk k hk (by omega)) hFk
            (hraw k hk (by omega))
            (by simpa only [hkd] using (show
              frontCount (virtualLabels init ω (f i)) k < shapeCutoff C.card by omega))
          exact (not_lt_of_ge hcharged) (hrare k hk (by dsimp only [d] at hkd; omega))
        have hbulkJ : StageEventSpec.bulkThreshold C.card ≤
            frontCount (virtualLabels init ω (f i)) j := by
          by_contra hnot
          have hbelow : frontCount (virtualLabels init ω (f i)) j <
              StageEventSpec.bulkThreshold C.card := by omega
          have hanti : Antitone (fun ell => frontCount (virtualLabels init ω (f i)) ell) :=
            fun a b hab => frontCount_antitone_level _ a b hab
          have hshapes : ∀ ell, j ≤ ell → ell < j + frontWidth C.card →
              shapeCutoff C.card ≤ frontCount (virtualLabels init ω (f i)) ell →
              frontCount (virtualLabels init ω (f i)) ell ≤ StageEventSpec.bulkThreshold C.card →
              C.card * frontCount (virtualLabels init ω (f i)) (ell + 1) ≤
                frontCount (virtualLabels init ω (f i)) ell ^ 2 := by
            intro ell hjell hell hlow hupp
            have helli : ell < i := by
              change ell < j + d at hell
              omega
            have hellpos : 1 ≤ ell := by omega
            have hbelowEll : frontCount (virtualLabels init ω (f i)) ell <
                StageEventSpec.bulkThreshold C.card :=
              (hanti hjell).trans_lt hbelow
            have hbefore : f i ≤ tau ell := by
              by_contra hnotBefore
              have hmono := frontCount_mono_safe init C s (tau ell) (f i) ell
                (hbulk ell hellpos (by omega)).1 (by omega) hellpos
                (by simpa only [clockCap, clockHours] using (show ell ≤ clockCap n by omega))
                ω (hsafe _ (hfirst i hi hiQ).1)
              have hhit := (hbulk ell hellpos (by omega)).2.1
              omega
            exact (ih ell helli hellpos (by omega)).2.1 (by omega)
              (f i) (hfirst i hi hiQ).1 hbefore hlow hupp
          have hc := bulk_of_sublinear_front_and_shapes C.card j
            (fun ell => frontCount (virtualLabels init ω (f i)) ell)
            hC hx hanti
            (by simpa only [show j + frontWidth C.card = k from hjd] using hhigh)
            hshapes
          exact hnot hc
        have htj : tau j ≤ f i :=
          firstAfter_le_of_hit (hbulk j hj (by omega)) (hfirst i hi hiQ).1 hbulkJ
        have hchain := coarse_contact_chain init C tau (clockCap n) ω hcoarse
          j (2 * d) hj (by omega)
        rw [hjtwo] at hchain
        have hA : maskContacts init C (max (f i) alpha) (tau i) ω ≤ fineTicks C.card := by
          calc
            _ ≤ maskContacts init C (f i) (tau i) ω :=
              maskContacts_antitone_left init C (f i) (max (f i) alpha)
                (tau i) (le_max_left _ _) ω
            _ ≤ maskContacts init C (tau j) (tau i) ω :=
              maskContacts_antitone_left init C (tau j) (f i) (tau i) htj ω
            _ ≤ 100 * (2 * d) * C.card := hchain
            _ = fineTicks C.card := by dsimp only [fineTicks, d]; ring
        refine ⟨hA, fun hiQ' => hshape_of_budget i hi hiQ' hA, ?_⟩
        intro _
        exact htj

end Ripple.PopulationProtocol.ExactMajority.PhaseThreeClockJointFront

end
