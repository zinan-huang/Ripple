/-
Copyright (c) 2026 Xiang Huang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiang Huang
-/
import Tri.PhaseGlue

/-!
# Inhabiting the phase-2 bridge from two-sided bands

This module turns the local phase-2 contraction into every field of
`Phase2Bridge`.  Each nonconsensus initial state supplies either a direct
`triChain_upper_target_failure` certificate when it is already sufficiently
far above the next checkpoint, or a two-sided-band certificate.  In the latter
case `DirectionProgress.phase1_direction_progress` controls lower ruin and the
live-band tail, and `Reaches.of_bandCount_upper` uses the Feller return estimate
to transfer an upper stopped hit back to the original exact-time chain.

Two genuinely unproved inputs remain, both exposed stage by stage:

* `Phase2BandBridge.hcontract` is a strengthened one-step base-two contraction
  on the selected band.  The non-strengthened contraction on `Phase2Live` is
  proved below from `phase2_halving_step`; absorbing both Feller terms into the
  fixed `phase2StageError` additionally needs quantitative slack and control of
  the two fringe regions.
* `Phase2BandBridge.herror` and `Phase2ReturnBridge.herror` are the explicit
  scalar checks that the lower-ruin, live-tail, and upper-return terms (or the
  direct return term) fit inside `phase2StageError`.

Thus no field of `Phase2Bridge` is left as a hypothesis.  The remaining work is
the concrete choice of band boundaries and verification of precisely the
fringe and scalar inequalities above.
-/

namespace Tri

open scoped ENNReal

/-- The upper arithmetic half of `Phase2Stage`, without its physical-range
conjunct.  Removing that conjunct lets upper-return lemmas quantify over all
natural states; support of `triChain` restores the conjunct afterwards. -/
def Phase2Upper (n s x : ℕ) : Prop :=
  2 ^ s * n ≤ 2 ^ s * x + n

/-- Membership in the upper arithmetic half of a phase-2 checkpoint is
decidable. -/
instance (n s : ℕ) : DecidablePred (Phase2Upper n s) := by
  intro x
  unfold Phase2Upper
  infer_instance

/-- The ENNReal form of the phase-2 contraction factor. -/
noncomputable def phase2DecayENN (s : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (phase2Decay s)

/-- The phase-2 contraction factor is nonnegative. -/
theorem phase2Decay_nonneg (s : ℕ) : 0 ≤ phase2Decay s := by
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ s := one_le_pow₀ (by norm_num)
  unfold phase2Decay
  apply sub_nonneg.mpr
  apply (div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ (s + 5))).2
  rw [pow_add]
  norm_num
  nlinarith

/-- The real one-step phase-2 estimate is exactly the ENNReal base-`1/2`
directional contraction required by the doubly stopped progress theorem. -/
theorem phase2_direction_step (a b n s : ℕ) (h3 : 3 ≤ n)
    (hpop : a + b + 2 = n) (hlive : Phase2Live n s (a + 1)) :
    triStep (a + 1) (b + 1) (by omega) a +
          triStep (a + 1) (b + 1) (by omega) (a + 1) *
            ((1 : ℝ≥0∞) / 2) +
          triStep (a + 1) (b + 1) (by omega) (a + 2) *
            ((1 : ℝ≥0∞) / 2) ^ 2 ≤
        phase2DecayENN s * ((1 : ℝ≥0∞) / 2) := by
  have f0 : triStep (a + 1) (b + 1) (by omega) a ≠ ⊤ :=
    PMF.apply_ne_top _ _
  have f1 : triStep (a + 1) (b + 1) (by omega) (a + 1) ≠ ⊤ :=
    PMF.apply_ne_top _ _
  have f2 : triStep (a + 1) (b + 1) (by omega) (a + 2) ≠ ⊤ :=
    PMF.apply_ne_top _ _
  have fhalf : ((1 : ℝ≥0∞) / 2) ≠ ⊤ := by norm_num
  have f1half : triStep (a + 1) (b + 1) (by omega) (a + 1) *
      ((1 : ℝ≥0∞) / 2) ≠ ⊤ := ENNReal.mul_ne_top f1 fhalf
  have f2half : triStep (a + 1) (b + 1) (by omega) (a + 2) *
      ((1 : ℝ≥0∞) / 2) ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top f2 (ENNReal.pow_ne_top fhalf)
  have fleft : triStep (a + 1) (b + 1) (by omega) a +
        triStep (a + 1) (b + 1) (by omega) (a + 1) *
          ((1 : ℝ≥0∞) / 2) +
        triStep (a + 1) (b + 1) (by omega) (a + 2) *
          ((1 : ℝ≥0∞) / 2) ^ 2 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨f0, f1half⟩, f2half⟩
  have fright : phase2DecayENN s * ((1 : ℝ≥0∞) / 2) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top fhalf
  rw [← ENNReal.toReal_le_toReal fleft fright,
    ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨f0, f1half⟩) f2half,
    ENNReal.toReal_add f0 f1half]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_one, phase2DecayENN,
    ENNReal.toReal_ofReal (phase2Decay_nonneg s)]
  norm_num only [ENNReal.toReal_ofNat]
  have hstep := phase2_halving_step a b n s h3 hpop hlive
  calc
    ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) a) +
          ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) (a + 1)) *
            (1 / 2 : ℝ) +
          ENNReal.toReal (triStep (a + 1) (b + 1) (by omega) (a + 2)) *
            (1 / 4 : ℝ) =
        phase2Moment a b (by omega) / (2 : ℝ) ^ (b + 2) := by
      unfold phase2Moment
      rw [show b + 2 = b + 1 + 1 by omega, pow_succ, pow_succ]
      field_simp
      ring
    _ ≤ ((2 : ℝ) ^ (b + 1) * phase2Decay s) /
          (2 : ℝ) ^ (b + 2) :=
      div_le_div_of_nonneg_right hstep (by positivity)
    _ = phase2Decay s * (1 / 2 : ℝ) := by
      rw [show b + 2 = b + 1 + 1 by omega, pow_succ]
      field_simp
      ring

/-- A reachability estimate for the upper arithmetic half of a checkpoint
becomes a `Phase2Stage` estimate when all initial states are physical. -/
theorem Reaches.phase2Stage_of_upper {n s T : ℕ} {P : ℕ → Prop}
    [DecidablePred P] {ε : ℝ≥0∞} (h3 : 3 ≤ n)
    (hphysical : ∀ x, P x → x ≤ n)
    (hupper : Reaches (triChain n) T P (Phase2Upper n s) ε) :
    Reaches (triChain n) T P (Phase2Stage n s) ε := by
  intro x hx
  calc
    ∑' z, (if Phase2Stage n s z then 0 else iter (triChain n) T x z) ≤
        ∑' z, (if Phase2Upper n s z then 0 else
          iter (triChain n) T x z) := by
      refine ENNReal.tsum_le_tsum fun z => ?_
      by_cases hupperZ : Phase2Upper n s z
      · by_cases hphysicalZ : z ≤ n
        · have hstageZ : Phase2Stage n s z := ⟨hphysicalZ, hupperZ⟩
          simp [hstageZ, hupperZ]
        · have hzero := iter_triChain_eq_zero_above n T x z h3
            (hphysical x hx) (by omega)
          simp [Phase2Stage, Phase2Upper, hphysicalZ, hzero]
      · by_cases hstageZ : Phase2Stage n s z <;>
          simp [hstageZ, hupperZ]
    _ ≤ ε := hupper x hx

/-- A first-coordinate reachability estimate for `bandChain` lifts to
`bandCount`; the artificial productive counter does not change its projected
law. -/
theorem Reaches.bandCount_of_bandChain
    (n bandLo aHi T x₀ c₀ : ℕ) (A : ℕ → Prop) [DecidablePred A]
    (ε : ℝ≥0∞)
    (h : Reaches (bandChain n bandLo aHi) T
      (fun x => x = x₀) A ε) :
    Reaches (bandCount n bandLo aHi) T
      (fun s => s = (x₀, c₀)) (fun s => A s.1) ε := by
  intro s hs
  subst s
  let V : ℕ → ℝ≥0∞ := fun x => if A x then 0 else 1
  have hmap :
      (iter (bandCount n bandLo aHi) T (x₀, c₀)).map Prod.fst =
        iter (bandChain n bandLo aHi) T x₀ :=
    iter_map_of_step_map _ _ _ (bandCount_map_fst n bandLo aHi) T _
  have hmassNat (q : PMF ℕ) :
      (∑' z, if A z then 0 else q z) = expect q V := by
    unfold expect V
    apply tsum_congr
    intro z
    by_cases hz : A z <;> simp [hz]
  have hmassPair (q : PMF (ℕ × ℕ)) :
      (∑' z, if A z.1 then 0 else q z) =
        expect q (fun z => V z.1) := by
    unfold expect V
    apply tsum_congr
    intro z
    by_cases hz : A z.1 <;> simp [hz]
  calc
    ∑' z, (if A z.1 then 0 else
        iter (bandCount n bandLo aHi) T (x₀, c₀) z) =
        expect (iter (bandCount n bandLo aHi) T (x₀, c₀))
          (fun z => V z.1) := hmassPair _
    _ = expect ((iter (bandCount n bandLo aHi) T
          (x₀, c₀)).map Prod.fst) V := (expect_map _ _ _).symm
    _ = expect (iter (bandChain n bandLo aHi) T x₀) V := by rw [hmap]
    _ = ∑' z, (if A z then 0 else
        iter (bandChain n bandLo aHi) T x₀ z) := (hmassNat _).symm
    _ ≤ ε := h x₀ rfl

/-- Direct Feller-return data for an initial state sufficiently far above the
next dyadic checkpoint.  The sole analytic residual is `herror`. -/
structure Phase2ReturnBridge (n s x : ℕ) where
  /-- Threshold below which return counts as failure. -/
  returnLo : ℕ
  /-- Complementary population parameter at the return threshold. -/
  bHi : ℕ
  /-- Distance of the initial state above the return threshold. -/
  k : ℕ
  /-- Population decomposition at the return threshold. -/
  hpop : returnLo + bHi + 2 = n
  /-- Positivity of the return threshold. -/
  hreturnLo : 0 < returnLo
  /-- Positivity of the complementary population parameter. -/
  hbHi : 0 < bHi
  /-- The return threshold is on the majority side. -/
  hmaj : bHi ≤ returnLo
  /-- The initial state lies at least `k` states above the return threshold. -/
  hgap : returnLo + k ≤ x
  /-- Every failure of the next upper checkpoint lies below `returnLo`. -/
  hfailure : ∀ z, ¬ Phase2Upper n (s + 1) z → z ≤ returnLo
  /-- The direct Feller return term fits the advertised stage error. -/
  herror : ((bHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ k ≤
    phase2StageError n s

/-- The exact two-sided-band data for an initial state below its next dyadic
checkpoint.  `hcontract` is the strengthened band contraction needed to leave
room for both Feller terms; `herror` is the remaining scalar check. -/
structure Phase2BandBridge (n s x : ℕ) where
  /-- Lower freeze boundary. -/
  bandLo : ℕ
  /-- Complementary population parameter at the lower boundary. -/
  bandBHi : ℕ
  /-- Distance of the initial state above the lower boundary. -/
  bandGap : ℕ
  /-- Distance from the initial state to the upper freeze boundary. -/
  upperGap : ℕ
  /-- Threshold below which a return from the upper boundary is failure. -/
  returnLo : ℕ
  /-- Complementary population parameter at `returnLo`. -/
  returnBHi : ℕ
  /-- Distance used in the upper Feller-return estimate. -/
  returnGap : ℕ
  /-- Strict contraction factor used for the selected extended band. -/
  φ : ℝ≥0∞
  /-- The initial state is exactly `bandGap` above the lower boundary. -/
  hstart : bandLo + bandGap = x
  /-- Population decomposition at the lower boundary. -/
  hbandPop : bandLo + bandBHi + 2 = n
  /-- Positivity of the lower boundary. -/
  hbandLo : 0 < bandLo
  /-- Positivity of its complementary population parameter. -/
  hbandBHi : 0 < bandBHi
  /-- The lower boundary is on the majority side. -/
  hbandMaj : bandBHi ≤ bandLo
  /-- The initial state lies strictly above the lower boundary. -/
  hbandGap : 0 < bandGap
  /-- The upper boundary lies strictly above the initial state. -/
  hupperGap : 0 < upperGap
  /-- The upper boundary remains in the physical range. -/
  hupperPhysical : x + upperGap ≤ n
  /-- Population decomposition at the return threshold. -/
  hreturnPop : returnLo + returnBHi + 2 = n
  /-- Positivity of the return threshold. -/
  hreturnLo : 0 < returnLo
  /-- Positivity of its complementary population parameter. -/
  hreturnBHi : 0 < returnBHi
  /-- The return threshold is on the majority side. -/
  hreturnMaj : returnBHi ≤ returnLo
  /-- The upper boundary has the required return gap. -/
  hreturnGap : returnLo + returnGap ≤ x + upperGap
  /-- A next-stage success lies above the lower freeze boundary. -/
  hlower : ∀ z, Phase2Upper n (s + 1) z → bandLo < z
  /-- Reaching the upper freeze boundary implies the next checkpoint. -/
  hupper : ∀ z, x + upperGap ≤ z → Phase2Upper n (s + 1) z
  /-- Every failure of the next checkpoint lies below `returnLo`. -/
  hfailure : ∀ z, ¬ Phase2Upper n (s + 1) z → z ≤ returnLo
  /-- Strengthened base-two contraction throughout the selected open band. -/
  hcontract : ∀ (a b : ℕ) (_hlocal : 3 ≤ (a + 1) + (b + 1)),
    a + b + 2 = n →
    bandLo < a + 1 → a + 1 < x + upperGap →
    triStep (a + 1) (b + 1) _hlocal a +
          triStep (a + 1) (b + 1) _hlocal (a + 1) *
            ((1 : ℝ≥0∞) / 2) +
          triStep (a + 1) (b + 1) _hlocal (a + 2) *
            ((1 : ℝ≥0∞) / 2) ^ 2 ≤
        φ * ((1 : ℝ≥0∞) / 2)
  /-- Lower ruin, the live-band tail, and upper return together fit the
  advertised phase-2 stage error. -/
  herror :
    (((bandBHi : ℝ≥0∞) / (bandLo : ℝ≥0∞)) ^ bandGap +
        φ ^ (4 * n) * ((1 : ℝ≥0∞) / 2) ^ x /
          ((1 : ℝ≥0∞) / 2) ^ (x + upperGap)) +
      ((returnBHi : ℝ≥0∞) / (returnLo : ℝ≥0∞)) ^ returnGap ≤
        phase2StageError n s

/-- A state sufficiently far above the next checkpoint satisfies the
advertised exact-time stage bound by the direct Feller-return certificate. -/
theorem phase2_stage_of_return (n s x : ℕ) (h3 : 3 ≤ n)
    (hx : Phase2Stage n s x) (B : Phase2ReturnBridge n s x) :
    ∑' z, (if Phase2Stage n (s + 1) z then 0
      else iter (triChain n) (4 * n) x z) ≤ phase2StageError n s := by
  have hupper : Reaches (triChain n) (4 * n) (fun y => y = x)
      (Phase2Upper n (s + 1))
      (((B.bHi : ℝ≥0∞) / (B.returnLo : ℝ≥0∞)) ^ B.k) := by
    intro y hy
    subst y
    exact triChain_upper_target_failure n B.returnLo B.bHi B.k x (4 * n)
      h3 B.hpop B.hreturnLo B.hbHi B.hmaj B.hgap
      (Phase2Upper n (s + 1)) B.hfailure
  have hstage := hupper.phase2Stage_of_upper h3 (fun y hy => by
    subst y
    exact hx.1)
  exact (hstage.mono_error B.herror) x rfl

/-- A state below the next checkpoint satisfies the advertised exact-time
stage bound from the two-sided direction band and upper-return transfer. -/
theorem phase2_stage_of_band (n s x : ℕ) (h3 : 3 ≤ n)
    (hx : Phase2Stage n s x) (B : Phase2BandBridge n s x) :
    ∑' z, (if Phase2Stage n (s + 1) z then 0
      else iter (triChain n) (4 * n) x z) ≤ phase2StageError n s := by
  have hdir : ∀ (a b : ℕ) (hab : a + b + 2 = n),
      B.bandLo < a + 1 → a + 1 < x + B.upperGap →
      triStep (a + 1) (b + 1) (by omega) a +
            triStep (a + 1) (b + 1) (by omega) (a + 1) *
              ((1 : ℝ≥0∞) / 2) +
            triStep (a + 1) (b + 1) (by omega) (a + 2) *
              ((1 : ℝ≥0∞) / 2) ^ 2 ≤
          B.φ * ((1 : ℝ≥0∞) / 2) := by
    intro a b hab hlo hhi
    exact B.hcontract a b (by omega) hab hlo hhi
  have hdir' : ∀ (a b : ℕ) (hab : a + b + 2 = n),
      B.bandLo < a + 1 →
      a + 1 < B.bandLo + B.bandGap + B.upperGap →
      triStep (a + 1) (b + 1) (by omega) a +
            triStep (a + 1) (b + 1) (by omega) (a + 1) *
              ((1 : ℝ≥0∞) / 2) +
            triStep (a + 1) (b + 1) (by omega) (a + 2) *
              ((1 : ℝ≥0∞) / 2) ^ 2 ≤
          B.φ * ((1 : ℝ≥0∞) / 2) := by
    intro a b hab hlo hhi
    exact hdir a b hab hlo (by simpa [B.hstart] using hhi)
  have hstopped0 := DirectionProgress.phase1_direction_progress
    n B.bandLo B.bandBHi B.bandGap B.upperGap (4 * n) h3
    B.hbandPop B.hbandLo B.hbandBHi B.hbandMaj B.hbandGap B.hupperGap
    (by simpa [B.hstart] using B.hupperPhysical)
    ((1 : ℝ≥0∞) / 2) B.φ
    (by norm_num) (by norm_num) hdir'
  rw [B.hstart] at hstopped0
  have hstopped : Reaches (bandChain n B.bandLo (x + B.upperGap)) (4 * n)
      (fun y => y = x) (fun z => x + B.upperGap ≤ z)
      (((B.bandBHi : ℝ≥0∞) / (B.bandLo : ℝ≥0∞)) ^ B.bandGap +
        B.φ ^ (4 * n) * ((1 : ℝ≥0∞) / 2) ^ x /
          ((1 : ℝ≥0∞) / 2) ^ (x + B.upperGap)) := by
    intro y hy
    subst y
    simpa only [directionStop, bandChain] using hstopped0
  have hupperBand := hstopped.mono_post B.hupper
  have hcount := Reaches.bandCount_of_bandChain n B.bandLo
    (x + B.upperGap) (4 * n) x 0 (Phase2Upper n (s + 1)) _ hupperBand
  have horiginal := Reaches.of_bandCount_upper
    n B.bandLo (x + B.upperGap) B.returnLo B.returnBHi B.returnGap
      (4 * n) x 0 h3 B.hreturnPop B.hreturnLo B.hreturnBHi B.hreturnMaj
      B.hreturnGap (Phase2Upper n (s + 1)) _ B.hlower B.hfailure hcount
  have hstage := horiginal.phase2Stage_of_upper h3 (fun y hy => by
    subst y
    exact hx.1)
  exact (hstage.mono_error B.herror) x rfl

/-- The deterministic corrected moment used to inhabit `Phase2Bridge` once
the exact-time stage bound has been proved by the band certificates. -/
noncomputable def phase2BridgePotential (n s t : ℕ) : ℝ :=
  (2 : ℝ) ^ (n / 2 ^ s) * phase2Decay s ^ t

/-- Construct every field of the complete phase-2 ladder bridge.  The two
certificate alternatives let each nonconsensus state use either a direct
return estimate or a two-sided band; consensus is discharged directly. -/
noncomputable def phase2_bridge (n : ℕ) (h3 : 3 ≤ n)
    (hcertificates : ∀ i < Nat.log 2 n, ∀ x,
      Phase2Stage n (2 + i) x → x < n →
      Phase2ReturnBridge n (2 + i) x ⊕ Phase2BandBridge n (2 + i) x) :
    Phase2Bridge n (Nat.log 2 n) := by
  refine
    { V := fun i _x t => phase2BridgePotential n (2 + i) t
      hV0 := ?_
      hVstep := ?_
      hfail := ?_ }
  · intro i hi x hx
    simp [phase2BridgePotential]
  · intro i hi x hx hguard t
    simp only [phase2BridgePotential, pow_succ]
    ring_nf
    exact le_rfl
  · intro i hi x hx
    by_cases hxn : x = n
    · subst x
      have htarget : Phase2Stage n (2 + i + 1) n := by
        constructor
        · exact le_rfl
        · omega
      have hiter : iter (triChain n) (4 * n) n = PMF.pure n := by
        generalize 4 * n = T
        induction T with
        | zero => rfl
        | succ T ih =>
            rw [iter_succ, triChain_consensus h3, PMF.pure_bind, ih]
      rw [hiter]
      have hzero :
          (∑' z, (if Phase2Stage n (2 + i + 1) z then 0
            else PMF.pure n z)) = 0 := by
        apply ENNReal.tsum_eq_zero.mpr
        intro z
        by_cases hz : z = n
        · subst z
          simp [htarget]
        · simp [PMF.pure_apply, hz]
      rw [hzero]
      exact bot_le
    · have hxlt : x < n := lt_of_le_of_ne hx.1 hxn
      have hbound :
          ∑' z, (if Phase2Stage n (2 + i + 1) z then 0
            else iter (triChain n) (4 * n) x z) ≤
              phase2StageError n (2 + i) := by
        rcases hcertificates i hi x hx hxlt with B | B
        · exact phase2_stage_of_return n (2 + i) x h3 hx B
        · exact phase2_stage_of_band n (2 + i) x h3 hx B
      simpa [phase2BridgePotential, phase2StageError] using hbound

#print axioms phase2Decay_nonneg
#print axioms phase2_direction_step
#print axioms Reaches.phase2Stage_of_upper
#print axioms Reaches.bandCount_of_bandChain
#print axioms phase2_stage_of_return
#print axioms phase2_stage_of_band
#print axioms phase2_bridge

end Tri
