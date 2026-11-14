-- Ripple/Kurtz/StrongApprox/FiniteClockFirstHit.lean
import Ripple.Kurtz.StrongApprox.FiniteBatchTimeChange

/-!
# First hits in a finite family of continuous clocks

The main lemma selects the earliest threshold reached by a finite family of
continuous monotone clocks.  Before that time every threshold remains strict.
It is the deterministic substitute for an informal “take the first jump”.
-/

noncomputable section

namespace Ripple.Kurtz.StrongApprox

open MeasureTheory Set Finset Filter Topology

/-- A finite labelled counting path is locally constant to the right at every
clock value.  Repeated thresholds are allowed and are crossed as one batch. -/
theorem finiteArrivalCount_eventually_right
    {κ : Type*} [Fintype κ] (arrival : κ → ℝ) (u : ℝ) :
    ∀ᶠ w in 𝓝[≥] u,
      finiteArrivalCount arrival w = finiteArrivalCount arrival u := by
  classical
  have hlabel : ∀ a ∈ (Finset.univ : Finset κ),
      ∀ᶠ w in 𝓝[≥] u,
        (arrival a ≤ w) ↔ (arrival a ≤ u) := by
    intro a _
    by_cases ha : arrival a ≤ u
    · filter_upwards [self_mem_nhdsWithin] with w huw
      exact ⟨fun _ => ha, fun _ => ha.trans huw⟩
    · have hua : u < arrival a := lt_of_not_ge ha
      filter_upwards
        [(eventually_lt_nhds hua).filter_mono nhdsWithin_le_nhds]
        with w hwa
      exact ⟨fun haw => absurd haw (not_le.mpr hwa), fun hau => absurd hau ha⟩
  filter_upwards [(Filter.eventually_all_finset _).2 hlabel] with w hw
  unfold finiteArrivalCount
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hw a (Finset.mem_univ a)

/-- A continuous clock that starts strictly below a threshold and reaches it
by `t` has a first hitting time.  The threshold is not reached anywhere in
the preceding half-open interval. -/
theorem exists_first_hit_of_continuous
    (q : ℝ → ℝ) (hq : Continuous q)
    {s t a : ℝ} (hst : s ≤ t)
    (hs : q s < a) (ht : a ≤ q t) :
    ∃ u ∈ Ioc s t,
      q u = a ∧
        ∀ r ∈ Ico s u, q r < a := by
  let H : Set ℝ := Icc s t ∩ q ⁻¹' Ici a
  have hHclosed : IsClosed H :=
    isClosed_Icc.inter (isClosed_Ici.preimage hq)
  have hHnonempty : H.Nonempty := by
    refine ⟨t, ?_⟩
    exact ⟨right_mem_Icc.mpr hst, ht⟩
  have hHbdd : BddBelow H := by
    refine ⟨s, ?_⟩
    intro z hz
    exact hz.1.1
  let u : ℝ := sInf H
  have huH : u ∈ H := hHclosed.csInf_mem hHnonempty hHbdd
  have hsu : s < u := by
    have hsuWeak : s ≤ u := huH.1.1
    apply lt_of_le_of_ne hsuWeak
    intro hsuEq
    have hau : a ≤ q s := by
      simpa [hsuEq] using huH.2
    exact (not_le_of_gt hs) hau
  have haRange : a ∈ Icc (q s) (q u) :=
    ⟨le_of_lt hs, huH.2⟩
  obtain ⟨v, hv, hqv⟩ :=
    (intermediate_value_Icc hsu.le hq.continuousOn) haRange
  have hvH : v ∈ H := by
    refine ⟨⟨hv.1, hv.2.trans huH.1.2⟩, ?_⟩
    simpa [hqv]
  have huv : u ≤ v := csInf_le hHbdd hvH
  have hvu : v ≤ u := hv.2
  have hvEq : v = u := le_antisymm hvu huv
  have hqu : q u = a := by
    simpa [hvEq] using hqv
  refine ⟨u, ⟨hsu, huH.1.2⟩, hqu, ?_⟩
  intro r hr
  by_contra hra
  have har : a ≤ q r := not_lt.mp hra
  have hrH : r ∈ H := by
    refine ⟨⟨hr.1, hr.2.le.trans huH.1.2⟩, har⟩
  have hur : u ≤ r := csInf_le hHbdd hrH
  exact (not_lt_of_ge hur) hr.2

/-- **First hit from a finite clock-hitting family.** If at least one
threshold is reached by `t`, there is a channel/token whose first hitting time
is minimal.  Before that time no threshold in the family is reached. -/
theorem exists_first_hit_from_finite_family
    {κ : Type*} [Fintype κ]
    (q : κ → ℝ → ℝ) (level : κ → ℝ)
    (hcontinuous : ∀ a, Continuous (q a))
    (hmonotone : ∀ a, Monotone (q a))
    {s t : ℝ} (hst : s ≤ t)
    (hstart : ∀ a, q a s < level a)
    (hcross : ∃ a, level a ≤ q a t) :
    ∃ a u,
      u ∈ Ioc s t ∧
        q a u = level a ∧
          ∀ b r, r ∈ Ico s u → q b r < level b := by
  classical
  let Cross := {a : κ // level a ≤ q a t}
  have hCross : Nonempty Cross := by
    obtain ⟨a, ha⟩ := hcross
    exact ⟨⟨a, ha⟩⟩
  have hfirst (a : Cross) :
      ∃ u ∈ Ioc s t,
        q a.1 u = level a.1 ∧
          ∀ r ∈ Ico s u, q a.1 r < level a.1 :=
    exists_first_hit_of_continuous (q a.1) (hcontinuous a.1)
      hst (hstart a.1) a.2
  let hit : Cross → ℝ := fun a => Classical.choose (hfirst a)
  have hit_spec (a : Cross) :
      hit a ∈ Ioc s t ∧
        q a.1 (hit a) = level a.1 ∧
          ∀ r ∈ Ico s (hit a), q a.1 r < level a.1 := by
    dsimp [hit]
    exact Classical.choose_spec (hfirst a)
  let S : Finset ℝ := (Finset.univ : Finset Cross).image hit
  let a₀ : Cross := Classical.choice hCross
  have hSne : S.Nonempty := by
    refine ⟨hit a₀, ?_⟩
    simp [S]
  let u : ℝ := S.min' hSne
  have huMem : u ∈ S := S.min'_mem hSne
  obtain ⟨a, _, hau⟩ := Finset.mem_image.mp huMem
  have huIoc : u ∈ Ioc s t := by
    rw [← hau]
    exact (hit_spec a).1
  have hhit : q a.1 u = level a.1 := by
    rw [← hau]
    exact (hit_spec a).2.1
  refine ⟨a.1, u, huIoc, hhit, ?_⟩
  intro b r hr
  by_cases hb : level b ≤ q b t
  · let bCross : Cross := ⟨b, hb⟩
    have huLe : u ≤ hit bCross := by
      dsimp [u]
      exact Finset.min'_le S (hit bCross) (by simp [S])
    exact (hit_spec bCross).2.2 r
      ⟨hr.1, hr.2.trans_le huLe⟩
  · have hrt : r ≤ t := hr.2.le.trans huIoc.2
    have hqr : q b r ≤ q b t := hmonotone b hrt
    exact hqr.trans_lt (lt_of_not_ge hb)

end Ripple.Kurtz.StrongApprox

end
