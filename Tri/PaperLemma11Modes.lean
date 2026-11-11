import Tri.MultiProductiveLinear
import Tri.Rung

/-!
# Cumulative direct and third-party backsliding modes

Partial formalization of the genuine events in Section 7.2, Lemma 11 of
Condon--Hajiaghayi--Kirkpatrick--Manuch.

The module defines path counters and their unrestricted hitting probabilities,
proves deterministic reconstruction/support facts, and separates the two
one-step geometric moments using existing reaction-mass estimates.

The final probability bounds are proposition specifications only. Their
stopped-process proofs remain unfinished.
-/

namespace Tri

open scoped ENNReal

/-- Ignore the ±1 jumps and retain the direct ±2 contribution. -/
theorem direct_only_five_jump_mgf_core
    {down2 down1 stay up1 up2 u : ℝ≥0∞}
    (hsum : down2 + down1 + stay + up1 + up2 = 1)
    (hu1 : u ≤ 1)
    (h2 : down2 ≤ up2 * u ^ 2) :
    down2 + (down1 + stay + up1) * u ^ 2 +
      up2 * u ^ 4 ≤ u ^ 2 := by
  have hs :
      down2 + 0 + (down1 + stay + up1) + 0 + up2 = 1 := by
    simpa only [add_zero, add_assoc] using hsum
  have h := five_jump_mgf_core
    (down2 := down2) (down1 := 0)
    (stay := down1 + stay + up1)
    (up1 := 0) (up2 := up2) (u := u)
    hs hu1 (by simp) h2
  simpa only [zero_mul, add_zero] using h

/-- Ignore the ±2 jumps and retain the third-party ±1 contribution. -/
theorem third_only_five_jump_mgf_core
    {down2 down1 stay up1 up2 u : ℝ≥0∞}
    (hsum : down2 + down1 + stay + up1 + up2 = 1)
    (hu1 : u ≤ 1)
    (h1 : down1 ≤ up1 * u) :
    down1 * u + (down2 + stay + up2) * u ^ 2 +
      up1 * u ^ 3 ≤ u ^ 2 := by
  have hs :
      0 + down1 + (down2 + stay + up2) + up1 + 0 = 1 := by
    simpa only [zero_add, add_zero, add_assoc, add_comm, add_left_comm]
      using hsum
  have h := five_jump_mgf_core
    (down2 := 0) (down1 := down1)
    (stay := down2 + stay + up2)
    (up1 := up1) (up2 := 0) (u := u)
    hs hu1 h1 (by simp)
  simpa only [zero_mul, zero_add, add_zero] using h

/-- Geometric moment for the cumulative direct contribution. -/
theorem direct_only_geometric_of_core
    {down2 down1 stay up1 up2 u : ℝ≥0∞} {g : ℕ}
    (hg : 2 ≤ g)
    (hcore :
      down2 + (down1 + stay + up1) * u ^ 2 +
        up2 * u ^ 4 ≤ u ^ 2) :
    down2 * u ^ (g - 2) +
      (down1 + stay + up1) * u ^ g +
      up2 * u ^ (g + 2) ≤ u ^ g := by
  have h := five_jump_geometric_of_core
    (down2 := down2) (down1 := 0)
    (stay := down1 + stay + up1)
    (up1 := 0) (up2 := up2) (u := u) hg
    (by simpa only [zero_mul, add_zero] using hcore)
  simpa only [zero_mul, add_zero] using h

/-- Geometric moment for the cumulative third-party contribution. -/
theorem third_only_geometric_of_core
    {down2 down1 stay up1 up2 u : ℝ≥0∞} {g : ℕ}
    (hg : 2 ≤ g)
    (hcore :
      down1 * u + (down2 + stay + up2) * u ^ 2 +
        up1 * u ^ 3 ≤ u ^ 2) :
    down1 * u ^ (g - 1) +
      (down2 + stay + up2) * u ^ g +
      up1 * u ^ (g + 1) ≤ u ^ g := by
  have h := five_jump_geometric_of_core
    (down2 := 0) (down1 := down1)
    (stay := down2 + stay + up2)
    (up1 := up1) (up2 := 0) (u := u) hg
    (by simpa only [zero_mul, zero_add, add_zero] using hcore)
  simpa only [zero_mul, zero_add, add_zero] using h

namespace Multi

variable {m n : ℕ}

/-- Raw physical reaction masses satisfy the direct-mode MGF inequality.
Only the local X-versus-Y gap is needed. The ±1 reactions contribute zero
to the direct counter. -/
theorem pairDeltaMass_direct_mgf
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (d : ℕ)
    (hgap : count c Y + d ≤ count c X) :
    pairDeltaMass c h3 X Y (-2) +
      (pairDeltaMass c h3 X Y (-1) +
        pairDeltaMass c h3 X Y 0 +
        pairDeltaMass c h3 X Y 1) * pairGapLinearBase n d ^ 2 +
      pairDeltaMass c h3 X Y 2 * pairGapLinearBase n d ^ 4 ≤
      pairGapLinearBase n d ^ 2 := by
  apply direct_only_five_jump_mgf_core
    (pairDeltaMass_five_sum c h3 X Y)
    (pairGapLinearBase_le_one n d (by omega))
  rw [pairDeltaMass_neg_two_eq_directedFireMass c h3 X Y hXY,
    pairDeltaMass_two_eq_directedFireMass c h3 X Y hXY]
  exact reverse_directedFireMass_le_linearBase_sq
    c h3 X Y hXY d hgap

/-- Raw physical reaction masses satisfy the third-party-mode MGF inequality.
This needs the global plurality-gap hypothesis. Direct ±2 reactions
contribute zero to the third-party counter. -/
theorem pairDeltaMass_third_mgf
    (c : Config m n) (h3 : 3 ≤ n)
    (X Y : Species m) (hXY : X ≠ Y)
    (d : ℕ)
    (hgap : HasPairwiseGap c X d) :
    pairDeltaMass c h3 X Y (-1) * pairGapLinearBase n d +
      (pairDeltaMass c h3 X Y (-2) +
        pairDeltaMass c h3 X Y 0 +
        pairDeltaMass c h3 X Y 2) * pairGapLinearBase n d ^ 2 +
      pairDeltaMass c h3 X Y 1 * pairGapLinearBase n d ^ 3 ≤
      pairGapLinearBase n d ^ 2 := by
  apply third_only_five_jump_mgf_core
    (pairDeltaMass_five_sum c h3 X Y)
    (pairGapLinearBase_le_one n d (by omega))
  rw [pairDeltaMass_neg_one_eq_thirdPartyDownMass_sum c h3 X Y hXY,
    pairDeltaMass_one_eq_thirdPartyUpMass_sum c h3 X Y hXY]
  exact thirdPartyDownMass_sum_le_up_mul_linearBase
    c h3 X Y hXY d hgap

end Multi
end Tri

namespace Tri.Multi

open scoped BigOperators ENNReal

variable {m n : ℕ}

/-- The actual signed change in a fixed pair gap along a configuration edge. -/
def pairTransitionDelta
    (c c' : Config m n) (X Y : Species m) : ℤ :=
  pairGap c' X Y - pairGap c X Y

/-- The contribution from direct X/Y reactions.
On supported transitions these are precisely the jumps of size two. -/
def directGapIncrement
    (c c' : Config m n) (X Y : Species m) : ℤ :=
  if pairTransitionDelta c c' X Y = 2 ∨
      pairTransitionDelta c c' X Y = -2 then
    pairTransitionDelta c c' X Y
  else 0

/-- The contribution from reactions involving one tracked species and a
third species. On supported transitions these are the jumps of size one. -/
def thirdPartyGapIncrement
    (c c' : Config m n) (X Y : Species m) : ℤ :=
  if pairTransitionDelta c c' X Y = 1 ∨
      pairTransitionDelta c c' X Y = -1 then
    pairTransitionDelta c c' X Y
  else 0

theorem pairTransitionDelta_sampleNext
    (c : Config m n) (t : TripleSample c) (X Y : Species m) :
    pairTransitionDelta c (sampleNext c t) X Y =
      samplePairDelta t X Y := by
  unfold pairTransitionDelta
  rw [pairGap_sampleNext]
  omega

theorem directGapIncrement_ne_zero_iff
    (c c' : Config m n) (X Y : Species m) :
    directGapIncrement c c' X Y ≠ 0 ↔
      pairTransitionDelta c c' X Y = 2 ∨
        pairTransitionDelta c c' X Y = -2 := by
  unfold directGapIncrement
  split_ifs <;> omega

theorem thirdPartyGapIncrement_ne_zero_iff
    (c c' : Config m n) (X Y : Species m) :
    thirdPartyGapIncrement c c' X Y ≠ 0 ↔
      pairTransitionDelta c c' X Y = 1 ∨
        pairTransitionDelta c c' X Y = -1 := by
  unfold thirdPartyGapIncrement
  split_ifs <;> omega

theorem directGapIncrement_cases
    (c c' : Config m n) (X Y : Species m) :
    directGapIncrement c c' X Y = -2 ∨
      directGapIncrement c c' X Y = 0 ∨
      directGapIncrement c c' X Y = 2 := by
  unfold directGapIncrement
  split_ifs <;> omega

theorem thirdPartyGapIncrement_cases
    (c c' : Config m n) (X Y : Species m) :
    thirdPartyGapIncrement c c' X Y = -1 ∨
      thirdPartyGapIncrement c c' X Y = 0 ∨
      thirdPartyGapIncrement c c' X Y = 1 := by
  unfold thirdPartyGapIncrement
  split_ifs <;> omega

/-- Direct contributions occur exactly on the two direct firing fibers. -/
theorem directGapIncrement_sampleNext_ne_zero_iff
    (c : Config m n) (t : TripleSample c)
    (X Y : Species m) (hXY : X ≠ Y) :
    directGapIncrement c (sampleNext c t) X Y ≠ 0 ↔
      IsFirePair t (X, Y) ∨ IsFirePair t (Y, X) := by
  simp only [
    directGapIncrement_ne_zero_iff,
    pairTransitionDelta_sampleNext,
    samplePairDelta_eq_two_iff_fire t X Y hXY,
    samplePairDelta_eq_neg_two_iff_fire t X Y hXY]

/-- Third-party contributions occur exactly on the four relevant
third-species firing fibers. The first disjunct is favorable and the second
is adverse for the X-Y gap. -/
theorem thirdPartyGapIncrement_sampleNext_ne_zero_iff
    (c : Config m n) (t : TripleSample c)
    (X Y : Species m) (hXY : X ≠ Y) :
    thirdPartyGapIncrement c (sampleNext c t) X Y ≠ 0 ↔
      (∃ Z ∈ thirdSpecies X Y,
        IsFirePair t (X, Z) ∨ IsFirePair t (Z, Y)) ∨
      (∃ Z ∈ thirdSpecies X Y,
        IsFirePair t (Z, X) ∨ IsFirePair t (Y, Z)) := by
  simp only [
    thirdPartyGapIncrement_ne_zero_iff,
    pairTransitionDelta_sampleNext,
    samplePairDelta_eq_one_iff_third t X Y hXY,
    samplePairDelta_eq_neg_one_iff_third t X Y hXY]

theorem modeGapIncrement_decomposition
    (c c' : Config m n) (X Y : Species m)
    (hlo : (-2 : ℤ) ≤ pairTransitionDelta c c' X Y)
    (hhi : pairTransitionDelta c c' X Y ≤ (2 : ℤ)) :
    directGapIncrement c c' X Y +
        thirdPartyGapIncrement c c' X Y =
      pairTransitionDelta c c' X Y := by
  unfold directGapIncrement thirdPartyGapIncrement
  split_ifs <;> omega

/-- Every supported productive step is either the total kernel's absorbing
self-loop or the image of a physical sample. -/
theorem productiveStep_eq_self_or_sample_of_ne_zero
    (h3 : 3 ≤ n) (c c' : Config m n)
    (hstep : productiveStep h3 c c' ≠ 0) :
    c' = c ∨ ∃ t : TripleSample c, c' = sampleNext c t := by
  classical
  by_cases hprod : productiveMass c h3 ≠ 0
  · rw [productiveStep_of_mass_ne_zero h3 c hprod,
      PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at hstep
    push Not at hstep
    obtain ⟨t, ht⟩ := hstep
    right
    refine ⟨t, ?_⟩
    by_contra hnext
    simp [hnext] at ht
  · rw [show productiveStep h3 c = PMF.pure c by
      unfold productiveStep
      simp [hprod]] at hstep
    simp only [PMF.pure_apply] at hstep
    by_cases heq : c' = c
    · exact Or.inl heq
    · simp [heq] at hstep

theorem pairTransitionDelta_bounds_of_productiveStep
    (h3 : 3 ≤ n) (c c' : Config m n)
    (X Y : Species m)
    (hstep : productiveStep h3 c c' ≠ 0) :
    (-2 : ℤ) ≤ pairTransitionDelta c c' X Y ∧
      pairTransitionDelta c c' X Y ≤ (2 : ℤ) := by
  rcases productiveStep_eq_self_or_sample_of_ne_zero
      h3 c c' hstep with rfl | ⟨t, rfl⟩
  · simp [pairTransitionDelta]
  · rw [pairTransitionDelta_sampleNext]
    exact ⟨samplePairDelta_lower t X Y, samplePairDelta_upper t X Y⟩

theorem modeGapIncrement_decomposition_of_productiveStep
    (h3 : 3 ≤ n) (c c' : Config m n)
    (X Y : Species m)
    (hstep : productiveStep h3 c c' ≠ 0) :
    directGapIncrement c c' X Y +
        thirdPartyGapIncrement c c' X Y =
      pairTransitionDelta c c' X Y := by
  have hb :=
    pairTransitionDelta_bounds_of_productiveStep h3 c c' X Y hstep
  exact modeGapIncrement_decomposition c c' X Y hb.1 hb.2

/-- Support condition for an infinite productive-configuration path. -/
def ProductivePathSupported
    (h3 : 3 ≤ n) (ω : ℕ → Config m n) : Prop :=
  ∀ t, productiveStep h3 (ω t) (ω (t + 1)) ≠ 0

/-- Cumulative direct-mode contribution through T productive transitions. -/
def directGapContribution
    (ω : ℕ → Config m n) (X Y : Species m) (T : ℕ) : ℤ :=
  ∑ t ∈ Finset.range T,
    directGapIncrement (ω t) (ω (t + 1)) X Y

/-- Cumulative third-party-mode contribution through T productive transitions. -/
def thirdPartyGapContribution
    (ω : ℕ → Config m n) (X Y : Species m) (T : ℕ) : ℤ :=
  ∑ t ∈ Finset.range T,
    thirdPartyGapIncrement (ω t) (ω (t + 1)) X Y

@[simp] theorem directGapContribution_succ
    (ω : ℕ → Config m n) (X Y : Species m) (T : ℕ) :
    directGapContribution ω X Y (T + 1) =
      directGapContribution ω X Y T +
        directGapIncrement (ω T) (ω (T + 1)) X Y := by
  simp only [directGapContribution, Finset.sum_range_succ]

@[simp] theorem thirdPartyGapContribution_succ
    (ω : ℕ → Config m n) (X Y : Species m) (T : ℕ) :
    thirdPartyGapContribution ω X Y (T + 1) =
      thirdPartyGapContribution ω X Y T +
        thirdPartyGapIncrement (ω T) (ω (T + 1)) X Y := by
  simp only [thirdPartyGapContribution, Finset.sum_range_succ]

/-- Exact pathwise reconstruction of the physical pair gap. -/
theorem pairGap_eq_initial_add_modeContributions
    (h3 : 3 ≤ n) (ω : ℕ → Config m n)
    (hpath : ProductivePathSupported h3 ω)
    (X Y : Species m) (T : ℕ) :
    pairGap (ω T) X Y =
      pairGap (ω 0) X Y +
        directGapContribution ω X Y T +
        thirdPartyGapContribution ω X Y T := by
  induction T with
  | zero =>
      simp [directGapContribution, thirdPartyGapContribution]
  | succ T ih =>
      have hsplit :=
        modeGapIncrement_decomposition_of_productiveStep
          h3 (ω T) (ω (T + 1)) X Y (hpath T)
      rw [directGapContribution_succ, thirdPartyGapContribution_succ]
      unfold pairTransitionDelta at hsplit
      omega

/-- Full configuration, all direct counters, and all third-party counters.
The designated species X is a parameter of the transition kernel. -/
abbrev PairModeState (m n : ℕ) :=
  Config m n × (Species m → ℤ) × (Species m → ℤ)

def pairModeInitial (c0 : Config m n) : PairModeState m n :=
  (c0, fun _ => 0, fun _ => 0)

def pairModeNext
    (X : Species m) (q : PairModeState m n) (c' : Config m n) :
    PairModeState m n :=
  (c',
    fun Y => q.2.1 Y + directGapIncrement q.1 c' X Y,
    fun Y => q.2.2 Y + thirdPartyGapIncrement q.1 c' X Y)

@[simp] theorem pairModeNext_self
    (X : Species m) (q : PairModeState m n) :
    pairModeNext X q q.1 = q := by
  rcases q with ⟨c, a, b⟩
  simp [pairModeNext, directGapIncrement, thirdPartyGapIncrement,
    pairTransitionDelta]

/-- The unrestricted productive chain carrying both families of counters. -/
noncomputable def productivePairModeStep
    (h3 : 3 ≤ n) (X : Species m)
    (q : PairModeState m n) : PMF (PairModeState m n) :=
  (productiveStep h3 q.1).map (pairModeNext X q)

theorem productivePairModeStep_map_fst
    (h3 : 3 ≤ n) (X : Species m) (q : PairModeState m n) :
    (productivePairModeStep h3 X q).map Prod.fst =
      productiveStep h3 q.1 := by
  unfold productivePairModeStep
  rw [PMF.map_comp]
  change (productiveStep h3 q.1).map id = productiveStep h3 q.1
  exact PMF.map_id _

/-- Every finite configuration marginal is exactly the original productive
chain marginal. -/
theorem productivePairModeStep_iter_map_fst
    (h3 : 3 ≤ n) (X : Species m)
    (T : ℕ) (q : PairModeState m n) :
    (iter (productivePairModeStep h3 X) T q).map Prod.fst =
      iter (productiveStep h3) T q.1 := by
  exact iter_map_of_step_map
    (productivePairModeStep h3 X) (productiveStep h3)
    Prod.fst (productivePairModeStep_map_fst h3 X) T q

/-- Support of the lifted kernel consists exactly of supported productive
configuration transitions with the prescribed counter update. -/
theorem productivePairModeStep_support_iff
    (h3 : 3 ≤ n) (X : Species m) (q z : PairModeState m n) :
    productivePairModeStep h3 X q z ≠ 0 ↔
      productiveStep h3 q.1 z.1 ≠ 0 ∧
        z = pairModeNext X q z.1 := by
  classical
  constructor
  · intro h
    unfold productivePairModeStep at h
    rw [PMF.map_apply, Ne, ENNReal.tsum_eq_zero] at h
    push Not at h
    obtain ⟨c', hc'⟩ := h
    have hz : z = pairModeNext X q c' := by
      by_contra hne
      simp [hne] at hc'
    have hc : productiveStep h3 q.1 c' ≠ 0 := by
      intro hzero
      simp [hzero] at hc'
    have hfst : z.1 = c' := congrArg Prod.fst hz
    constructor
    · simpa only [hfst] using hc
    · simpa only [hfst] using hz
  · rintro ⟨hbase, hnext⟩ hzero
    unfold productivePairModeStep at hzero
    rw [PMF.map_apply, ENNReal.tsum_eq_zero] at hzero
    have hterm := hzero z.1
    apply hbase
    simpa only [if_pos hnext] using hterm

/-- Lift an actual configuration path using its cumulative mode sums. -/
def pairModePath
    (ω : ℕ → Config m n) (X : Species m) (T : ℕ) :
    PairModeState m n :=
  (ω T,
    fun Y => directGapContribution ω X Y T,
    fun Y => thirdPartyGapContribution ω X Y T)

@[simp] theorem pairModePath_zero
    (ω : ℕ → Config m n) (X : Species m) :
    pairModePath ω X 0 = pairModeInitial (ω 0) := by
  simp [pairModePath, pairModeInitial,
    directGapContribution, thirdPartyGapContribution]

theorem pairModePath_succ
    (ω : ℕ → Config m n) (X : Species m) (T : ℕ) :
    pairModePath ω X (T + 1) =
      pairModeNext X (pairModePath ω X T) (ω (T + 1)) := by
  unfold pairModePath pairModeNext
  simp only [directGapContribution_succ, thirdPartyGapContribution_succ]

theorem pairModePath_supported
    (h3 : 3 ≤ n) (ω : ℕ → Config m n)
    (hpath : ProductivePathSupported h3 ω)
    (X : Species m) (T : ℕ) :
    productivePairModeStep h3 X
        (pairModePath ω X T) (pairModePath ω X (T + 1)) ≠ 0 := by
  apply (productivePairModeStep_support_iff h3 X
    (pairModePath ω X T) (pairModePath ω X (T + 1))).2
  exact ⟨hpath T, pairModePath_succ ω X T⟩

/-- Reconstruction invariant relative to the initial configuration. -/
def PairModeInvariant
    (c0 : Config m n) (X : Species m) (q : PairModeState m n) : Prop :=
  ∀ Y, pairGap q.1 X Y =
    pairGap c0 X Y + q.2.1 Y + q.2.2 Y

theorem pairModeInvariant_initial
    (c0 : Config m n) (X : Species m) :
    PairModeInvariant c0 X (pairModeInitial c0) := by
  simp [PairModeInvariant, pairModeInitial]

theorem pairModeInvariant_next
    (h3 : 3 ≤ n) (c0 : Config m n) (X : Species m)
    (q : PairModeState m n) (c' : Config m n)
    (hq : PairModeInvariant c0 X q)
    (hstep : productiveStep h3 q.1 c' ≠ 0) :
    PairModeInvariant c0 X (pairModeNext X q c') := by
  intro Y
  have hqY := hq Y
  have hsplit :=
    modeGapIncrement_decomposition_of_productiveStep h3 q.1 c' X Y hstep
  change pairGap c' X Y =
    pairGap c0 X Y +
      (q.2.1 Y + directGapIncrement q.1 c' X Y) +
      (q.2.2 Y + thirdPartyGapIncrement q.1 c' X Y)
  unfold pairTransitionDelta at hsplit
  omega

theorem productivePairModeStep_inv
    (h3 : 3 ≤ n) (c0 : Config m n) (X : Species m)
    (q z : PairModeState m n)
    (hq : PairModeInvariant c0 X q)
    (hqz : productivePairModeStep h3 X q z ≠ 0) :
    PairModeInvariant c0 X z := by
  obtain ⟨hbase, hnext⟩ :=
    (productivePairModeStep_support_iff h3 X q z).1 hqz
  rw [hnext]
  exact pairModeInvariant_next h3 c0 X q z.1 hq hbase

theorem productivePairModeStep_iter_inv
    (h3 : 3 ≤ n) (c0 : Config m n) (X : Species m)
    (T : ℕ) (q z : PairModeState m n)
    (hq : PairModeInvariant c0 X q)
    (hqz : iter (productivePairModeStep h3 X) T q z ≠ 0) :
    PairModeInvariant c0 X z := by
  classical
  induction T generalizing q with
  | zero =>
      simp only [iter, PMF.pure_apply] at hqz
      by_cases hzq : z = q
      · simpa [hzq] using hq
      · simp [hzq] at hqz
  | succ T ih =>
      rw [iter_succ, PMF.bind_apply] at hqz
      by_contra hzInv
      apply hqz
      rw [ENNReal.tsum_eq_zero]
      intro a
      by_cases hqa : productivePairModeStep h3 X q a = 0
      · simp [hqa]
      · have haInv :=
          productivePairModeStep_inv h3 c0 X q a hq hqa
        have hiaz :
            iter (productivePairModeStep h3 X) T a z = 0 := by
          by_contra hne
          exact hzInv (ih a haInv hne)
        simp [hiaz]

/-- Current direct counter threshold, unioned over genuine competitors. -/
def DirectModeBad
    (X : Species m) (D : ℕ) (q : PairModeState m n) : Prop :=
  ∃ Y, Y ≠ X ∧ 4 * q.2.1 Y ≤ -(D : ℤ)

/-- Current third-party counter threshold, unioned over competitors. -/
def ThirdPartyModeBad
    (X : Species m) (D : ℕ) (q : PairModeState m n) : Prop :=
  ∃ Y, Y ≠ X ∧ 4 * q.2.2 Y ≤ -(D : ℤ)

/-- The common boundary needed for a first-crossing argument. -/
def PairModeBad
    (X : Species m) (D : ℕ) (q : PairModeState m n) : Prop :=
  DirectModeBad X D q ∨ ThirdPartyModeBad X D q

/-- Before any mode counter reaches its quarter-gap threshold, the
reconstruction invariant guarantees the protected physical half-gap. -/
theorem pairModeInvariant_gap_of_not_bad
    (c0 : Config m n) (X : Species m) (D : ℕ)
    (q : PairModeState m n)
    (hinit : HasPairwiseGap c0 X D)
    (hinv : PairModeInvariant c0 X q)
    (hsafe : ¬ PairModeBad X D q) :
    HasPairwiseGap q.1 X (D / 2) := by
  intro Y hYX
  have h0 := hinit Y hYX
  have hrec := hinv Y
  have hd : ¬ 4 * q.2.1 Y ≤ -(D : ℤ) := by
    intro h
    exact hsafe (Or.inl ⟨Y, hYX, h⟩)
  have ht : ¬ 4 * q.2.2 Y ≤ -(D : ℤ) := by
    intro h
    exact hsafe (Or.inr ⟨Y, hYX, h⟩)
  unfold pairGap at hrec
  omega

/-- Finite-horizon direct-mode backsliding on the unrestricted path. -/
def DirectModeBackslideBy
    (ω : ℕ → Config m n) (X : Species m) (D T : ℕ) : Prop :=
  ∃ Y, Y ≠ X ∧ ∃ t, t ≤ T ∧
    4 * directGapContribution ω X Y t ≤ -(D : ℤ)

/-- Finite-horizon third-party-mode backsliding on the unrestricted path. -/
def ThirdPartyModeBackslideBy
    (ω : ℕ → Config m n) (X : Species m) (D T : ℕ) : Prop :=
  ∃ Y, Y ≠ X ∧ ∃ t, t ≤ T ∧
    4 * thirdPartyGapContribution ω X Y t ≤ -(D : ℤ)

def DirectModeBackslide
    (ω : ℕ → Config m n) (X : Species m) (D : ℕ) : Prop :=
  ∃ T, DirectModeBackslideBy ω X D T

def ThirdPartyModeBackslide
    (ω : ℕ → Config m n) (X : Species m) (D : ℕ) : Prop :=
  ∃ T, ThirdPartyModeBackslideBy ω X D T

theorem directModeBackslideBy_iff_lifted_hit
    (ω : ℕ → Config m n) (X : Species m) (D T : ℕ) :
    DirectModeBackslideBy ω X D T ↔
      ∃ t, t ≤ T ∧ DirectModeBad X D (pairModePath ω X t) := by
  constructor
  · rintro ⟨Y, hY, t, ht, hbad⟩
    exact ⟨t, ht, Y, hY, hbad⟩
  · rintro ⟨t, ht, Y, hY, hbad⟩
    exact ⟨Y, hY, t, ht, hbad⟩

theorem thirdPartyModeBackslideBy_iff_lifted_hit
    (ω : ℕ → Config m n) (X : Species m) (D T : ℕ) :
    ThirdPartyModeBackslideBy ω X D T ↔
      ∃ t, t ≤ T ∧ ThirdPartyModeBad X D (pairModePath ω X t) := by
  constructor
  · rintro ⟨Y, hY, t, ht, hbad⟩
    exact ⟨t, ht, Y, hY, hbad⟩
  · rintro ⟨t, ht, Y, hY, hbad⟩
    exact ⟨Y, hY, t, ht, hbad⟩

/-- Finite-horizon probability for the direct event under the unrestricted
productive chain with its exact accumulated counters. -/
noncomputable def productiveDirectModeHitMass
    (h3 : 3 ≤ n) (X : Species m) (D T : ℕ)
    (c0 : Config m n) : ℝ≥0∞ := by
  classical
  exact hitProb (DirectModeBad X D)
    (productivePairModeStep h3 X) T (pairModeInitial c0)

/-- Finite-horizon probability for the third-party event. -/
noncomputable def productiveThirdPartyModeHitMass
    (h3 : 3 ≤ n) (X : Species m) (D T : ℕ)
    (c0 : Config m n) : ℝ≥0∞ := by
  classical
  exact hitProb (ThirdPartyModeBad X D)
    (productivePairModeStep h3 X) T (pairModeInitial c0)

noncomputable def productiveDirectModeEverMass
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (c0 : Config m n) : ℝ≥0∞ :=
  ⨆ T : ℕ, productiveDirectModeHitMass h3 X D T c0

noncomputable def productiveThirdPartyModeEverMass
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (c0 : Config m n) : ℝ≥0∞ :=
  ⨆ T : ℕ, productiveThirdPartyModeHitMass h3 X D T c0

/-- The unrestricted union event; useful for dominating either individual
unrestricted event after a common first-crossing analysis. -/
noncomputable def productivePairModeEverMass
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (c0 : Config m n) : ℝ≥0∞ := by
  classical
  exact ⨆ T : ℕ,
    hitProb (PairModeBad X D)
      (productivePairModeStep h3 X) T (pairModeInitial c0)

/-- Unproved specification for the requested direct-mode result.
This declaration is a proposition definition, not a proof of the bound. -/
def Lemma11DirectModeStatement
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (c0 : Config m n) : Prop :=
  4 ≤ D → D ≤ n → HasPairwiseGap c0 X D →
    productiveDirectModeEverMass h3 X D c0 ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ)))))

/-- Unproved specification for the requested third-party-mode result. -/
def Lemma11ThirdPartyModeStatement
    (h3 : 3 ≤ n) (X : Species m) (D : ℕ)
    (c0 : Config m n) : Prop :=
  4 ≤ D → D ≤ n → HasPairwiseGap c0 X D →
    productiveThirdPartyModeEverMass h3 X D c0 ≤
      (m : ℝ≥0∞) *
        ENNReal.ofReal
          (Real.exp (-((D : ℝ) ^ 2 / (18 * (n : ℝ)))))

end Tri.Multi
