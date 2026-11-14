import Ripple.Core.SurrogateCompilationBlowup
import Ripple.Core.ODEGlobal
import Ripple.Core.ZeroInitPositivity

/-!
# Maximal forward solutions and the BAC journal finite-lifespan interface

Maximality means non-extendability. Neither boundedness nor blow-up is a
field of the maximal-solution structure.

Existence takes the supremum of the lifetimes of forward solutions and
glues their common values using ODE uniqueness. A uniform local Picard
step proves continuation from a bounded point. Consequently a finite
maximal endpoint forces the norm to tend to infinity.

The time-change and certificate exports retain the actual rational
polynomial compilers. Negative-time representatives are not identified by
uniqueness: all uniqueness statements concern the forward domain.
-/

noncomputable section

namespace Ripple.MaximalPIVP

open Filter Set Topology MeasureTheory
open scoped ENNReal

variable {d : ℕ} {P : PolyPIVP d}

/-- The half-open forward interval, including the infinite-endpoint case. -/
def forwardInterval (T : ℝ≥0∞) : Set ℝ :=
  {t | 0 ≤ t ∧ ENNReal.ofReal t < T}

@[simp] theorem forwardInterval_top :
    forwardInterval ⊤ = Set.Ici (0 : ℝ) := by
  ext t
  simp [forwardInterval]

theorem forwardInterval_finite {T : ℝ≥0∞}
    (hpos : 0 < T) (hfin : T ≠ ⊤) :
    forwardInterval T = Set.Ico (0 : ℝ) T.toReal := by
  have hp : 0 < T.toReal := ENNReal.toReal_pos hpos.ne' hfin
  ext t
  have hlt : ENNReal.ofReal t < T ↔ t < T.toReal := by
    have h := ENNReal.ofReal_lt_ofReal_iff (p := t) (q := T.toReal) hp
    simpa only [ENNReal.ofReal_toReal hfin] using h
  simp only [forwardInterval, Set.mem_setOf_eq, Set.mem_Ico, hlt]

private theorem real_time_above {T : ℝ≥0∞} {t : ℝ}
    (hpos : 0 < T) (ht : ENNReal.ofReal t < T) :
    ∃ b : ℝ, t < b ∧ ENNReal.ofReal b < T := by
  by_cases htop : T = ⊤
  · exact ⟨t + 1, by linarith, by simp [htop]⟩
  · have hp : 0 < T.toReal := ENNReal.toReal_pos hpos.ne' htop
    have ht' : t < T.toReal := by
      apply (ENNReal.ofReal_lt_ofReal_iff hp).mp
      simpa only [ENNReal.ofReal_toReal htop] using ht
    obtain ⟨b, htb, hb⟩ := exists_between ht'
    refine ⟨b, htb, ?_⟩
    calc
      ENNReal.ofReal b < ENNReal.ofReal T.toReal :=
        (ENNReal.ofReal_lt_ofReal_iff hp).mpr hb
      _ = T := ENNReal.ofReal_toReal htop

/-- A forward solution, with no assertion of maximality. -/
structure ForwardSolution (P : PolyPIVP d) where
  lifetime : ℝ≥0∞
  positive : 0 < lifetime
  trajectory : ℝ → Fin d → ℝ
  initial : trajectory 0 = fun i => (P.init i : ℝ)
  ode : ∀ t ∈ forwardInterval lifetime,
    HasDerivAt trajectory (P.evalField (trajectory t)) t

/-- An extension agrees on the entire old forward interval. -/
def ForwardSolution.Extends (v u : ForwardSolution P) : Prop :=
  u.lifetime ≤ v.lifetime ∧
    Set.EqOn v.trajectory u.trajectory (forwardInterval u.lifetime)

/-- Non-extendability, not a reformulation using unboundedness. -/
def ForwardSolution.IsMaximal (u : ForwardSolution P) : Prop :=
  ∀ v : ForwardSolution P, v.Extends u → v.lifetime ≤ u.lifetime

structure MaximalSolution (P : PolyPIVP d) extends ForwardSolution P where
  maximal : toForwardSolution.IsMaximal

private theorem field_lipschitz (P : PolyPIVP d) :
    ∀ R : ℝ, 0 < R → ∃ L : ℝ, ∀ x y : Fin d → ℝ,
      ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖P.evalField x - P.evalField y‖ ≤ L * ‖x - y‖ :=
  polyPIVP_field_locally_lipschitz P

/-- A finite half-open solution is a forward solution. -/
def ForwardSolution.ofIco (P : PolyPIVP d) (T : ℝ) (hT : 0 < T)
    (y : ℝ → Fin d → ℝ)
    (hy : y 0 = fun i => (P.init i : ℝ))
    (hd : ∀ t ∈ Set.Ico 0 T, HasDerivAt y (P.evalField (y t)) t) :
    ForwardSolution P where
  lifetime := ENNReal.ofReal T
  positive := ENNReal.ofReal_pos.mpr hT
  trajectory := y
  initial := hy
  ode := by
    intro t ht
    exact hd t ⟨ht.1, (ENNReal.ofReal_lt_ofReal_iff hT).mp ht.2⟩

def ForwardSolution.ofGlobal (s : PIVP.Solution P.toPIVP) :
    ForwardSolution P where
  lifetime := ⊤
  positive := by simp
  trajectory := s.trajectory
  initial := s.init_cond
  ode := fun t ht => s.is_solution t ht.1

def ForwardSolution.toGlobal (u : ForwardSolution P) (htop : u.lifetime = ⊤) :
    PIVP.Solution P.toPIVP where
  trajectory := u.trajectory
  init_cond := u.initial
  is_solution := by
    intro t ht
    apply u.ode t
    exact ⟨ht, by simp [htop]⟩

private theorem agree_at (P : PolyPIVP d)
    {y z : ℝ → Fin d → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hy : y 0 = fun i => (P.init i : ℝ))
    (hz : z 0 = fun i => (P.init i : ℝ))
    (hdy : ∀ s ∈ Set.Icc 0 t, HasDerivAt y (P.evalField (y s)) s)
    (hdz : ∀ s ∈ Set.Icc 0 t, HasDerivAt z (P.evalField (z s)) s) :
    y t = z t := by
  by_cases hzero : t = 0
  · subst t
    exact hy.trans hz.symm
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzero)
  have hcy : ContinuousOn y (Set.Icc 0 t) :=
    fun s hs => (hdy s hs).continuousAt.continuousWithinAt
  have hcz : ContinuousOn z (Set.Icc 0 t) :=
    fun s hs => (hdz s hs).continuousAt.continuousWithinAt
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hcy
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcz
  have heq := solutions_agree_on_Icc
    (f := P.evalField) (y₀ := fun i => (P.init i : ℝ))
    (M := max (max A B) 0) htpos (le_max_right _ _)
    (field_lipschitz P) hy hz
    (fun s hs => (hdy s hs).hasDerivWithinAt)
    (fun s hs => (hdz s hs).hasDerivWithinAt)
    (fun s hs => (hA s hs).trans
      ((le_max_left A B).trans (le_max_left _ 0)))
    (fun s hs => (hB s hs).trans
      ((le_max_right A B).trans (le_max_left _ 0)))
  exact heq ⟨ht, le_rfl⟩

/-- Uniqueness on the common interval; no bound is an input premise. -/
theorem ForwardSolution.agree (u v : ForwardSolution P) {t : ℝ}
    (hu : t ∈ forwardInterval u.lifetime)
    (hv : t ∈ forwardInterval v.lifetime) :
    u.trajectory t = v.trajectory t := by
  apply agree_at P hu.1 u.initial v.initial
  · intro s hs
    exact u.ode s ⟨hs.1,
      (ENNReal.ofReal_le_ofReal hs.2).trans_lt hu.2⟩
  · intro s hs
    exact v.ode s ⟨hs.1,
      (ENNReal.ofReal_le_ofReal hs.2).trans_lt hv.2⟩

/-- The polynomial global solution is unique on nonnegative time. -/
theorem global_solution_unique (P : PolyPIVP d)
    (s t : PIVP.Solution P.toPIVP) :
    Set.EqOn s.trajectory t.trajectory (Set.Ici 0) := by
  intro a ha
  exact agree_at P ha s.init_cond t.init_cond
    (fun b hb => s.is_solution b hb.1)
    (fun b hb => t.is_solution b hb.1)

private theorem local_solution (P : PolyPIVP d) :
    ∃ T : ℝ, 0 < T ∧ ∃ y : ℝ → Fin d → ℝ,
      y 0 = (fun i => (P.init i : ℝ)) ∧
      ∀ t ∈ Set.Ico 0 T, HasDerivAt y (P.evalField (y t)) t := by
  let x : Fin d → ℝ := fun i => (P.init i : ℝ)
  obtain ⟨ε, K, B, hε, hB, hside, hlip, hbound⟩ :=
    picard_uniform_step (field_lipschitz P) (‖x‖ + 1) (by positivity)
  obtain ⟨a, ha, had⟩ := single_step_solution
    (M := ‖x‖ + 1) hε hB hside hlip hbound x (by linarith) (0 : ℝ)
  have had' : ∀ t ∈ Set.Icc (0 : ℝ) ε,
      HasDerivWithinAt a (P.evalField (a t)) (Set.Icc 0 ε) t := by
    simpa only [zero_add] using had
  obtain ⟨y, hy, _, hyd⟩ := extend_left_linear_hasDerivAt hε ha had'
  exact ⟨ε, hε, y, hy, hyd⟩

/-- Uniform continuation from any bounded endpoint of any forward solution. -/
theorem uniform_forward_extension (P : PolyPIVP d) (M : ℝ) (hM : 0 ≤ M) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u : ForwardSolution P, ∀ t : ℝ,
      t ∈ forwardInterval u.lifetime → ‖u.trajectory t‖ ≤ M →
      ∃ v : ForwardSolution P,
        v.lifetime = ENNReal.ofReal (t + ε) ∧
        Set.EqOn v.trajectory u.trajectory (Set.Icc 0 t) := by
  obtain ⟨ε, K, B, hε, hB, hside, hlip, hbound⟩ :=
    picard_uniform_step (field_lipschitz P) M hM
  refine ⟨ε, hε, ?_⟩
  intro u t ht hb
  have hd : ∀ s ∈ Set.Icc 0 t,
      HasDerivWithinAt u.trajectory (P.evalField (u.trajectory s))
        (Set.Icc 0 t) s := by
    intro s hs
    exact (u.ode s ⟨hs.1,
      (ENNReal.ofReal_le_ofReal hs.2).trans_lt ht.2⟩).hasDerivWithinAt
  obtain ⟨β, hβ, hagree, hβd⟩ := iterate_one_step
    (M := M) hε hB hside hlip hbound t ht.1 u.trajectory hd hb
    (fun i => (P.init i : ℝ)) u.initial
  have hT : 0 < t + ε := by linarith [ht.1]
  obtain ⟨γ, hγ, hγβ, hγd⟩ := extend_left_linear_hasDerivAt hT hβ hβd
  refine ⟨ForwardSolution.ofIco P (t + ε) hT γ hγ hγd, rfl, ?_⟩
  intro s hs
  exact (hγβ s hs.1).trans (hagree s hs)

/-- Existence by the supremum of all forward existence intervals. -/
theorem exists_maximal (P : PolyPIVP d) : Nonempty (MaximalSolution P) := by
  classical
  obtain ⟨T, hT, b, hb, hbd⟩ := local_solution P
  let base : ForwardSolution P := ForwardSolution.ofIco P T hT b hb hbd
  let E : ℝ≥0∞ := ⨆ v : ForwardSolution P, v.lifetime
  let y : ℝ → Fin d → ℝ := fun t =>
    if h : ∃ v : ForwardSolution P, t ∈ forwardInterval v.lifetime then
      (Classical.choose h).trajectory t
    else base.trajectory t
  have hagree : ∀ v : ForwardSolution P, ∀ t ∈ forwardInterval v.lifetime,
      y t = v.trajectory t := by
    intro v t ht
    have h : ∃ w : ForwardSolution P, t ∈ forwardInterval w.lifetime := ⟨v, ht⟩
    dsimp only [y]
    rw [dif_pos h]
    exact (Classical.choose h).agree v (Classical.choose_spec h) ht
  have hbase : (0 : ℝ) ∈ forwardInterval base.lifetime :=
    ⟨le_rfl, by simpa using base.positive⟩
  have hyzero : y 0 = fun i => (P.init i : ℝ) :=
    (hagree base 0 hbase).trans base.initial
  have hE : 0 < E := base.positive.trans_le
    (le_iSup (fun v : ForwardSolution P => v.lifetime) base)
  have hyd : ∀ t ∈ forwardInterval E,
      HasDerivAt y (P.evalField (y t)) t := by
    intro t ht
    by_cases htzero : t = 0
    · subst t
      have hev : y =ᶠ[𝓝 (0 : ℝ)] base.trajectory := by
        filter_upwards [Iio_mem_nhds hT] with s hs
        by_cases hsnonneg : 0 ≤ s
        · apply hagree base s
          exact ⟨hsnonneg, (ENNReal.ofReal_lt_ofReal_iff hT).mpr hs⟩
        · have hn : ¬ ∃ v : ForwardSolution P,
              s ∈ forwardInterval v.lifetime := by
            rintro ⟨v, hv⟩
            exact hsnonneg hv.1
          simp only [y, dif_neg hn]
      rw [hagree base 0 hbase]
      exact (base.ode 0 hbase).congr_of_eventuallyEq hev
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
      have hsup : ENNReal.ofReal t < ⨆ v : ForwardSolution P, v.lifetime := ht.2
      obtain ⟨v, hv⟩ := lt_iSup_iff.mp hsup
      obtain ⟨R, htR, hR⟩ := real_time_above v.positive hv
      have hvt : t ∈ forwardInterval v.lifetime := ⟨ht.1, hv⟩
      have hev : y =ᶠ[𝓝 t] v.trajectory := by
        filter_upwards [Ioo_mem_nhds htpos htR] with s hs
        exact hagree v s ⟨hs.1.le,
          (ENNReal.ofReal_le_ofReal hs.2.le).trans_lt hR⟩
      rw [hagree v t hvt]
      exact (v.ode t hvt).congr_of_eventuallyEq hev
  refine ⟨{
    toForwardSolution := {
      lifetime := E
      positive := hE
      trajectory := y
      initial := hyzero
      ode := hyd }
    maximal := ?_ }⟩
  intro v _
  exact le_iSup (fun w : ForwardSolution P => w.lifetime) v

/-- Every forward solution has lifetime at most that of a maximal solution. -/
theorem MaximalSolution.lifetime_le (u : MaximalSolution P)
    (v : ForwardSolution P) : v.lifetime ≤ u.lifetime := by
  rcases le_total v.lifetime u.lifetime with h | h
  · exact h
  · apply u.maximal v
    refine ⟨h, ?_⟩
    intro t ht
    exact v.agree u.toForwardSolution
      ⟨ht.1, ht.2.trans_le h⟩ ht

/-- Uniqueness includes the endpoint and all forward values, not arbitrary
values of the chosen total functions outside their forward intervals. -/
theorem MaximalSolution.unique (u v : MaximalSolution P) :
    u.lifetime = v.lifetime ∧
      Set.EqOn u.trajectory v.trajectory (forwardInterval u.lifetime) := by
  have he : u.lifetime = v.lifetime :=
    le_antisymm (v.lifetime_le u.toForwardSolution)
      (u.lifetime_le v.toForwardSolution)
  refine ⟨he, ?_⟩
  intro t ht
  apply u.toForwardSolution.agree v.toForwardSolution ht
  simpa only [he] using ht

theorem MaximalSolution.finite_time_pos (u : MaximalSolution P)
    (hfin : u.lifetime ≠ ⊤) : 0 < u.lifetime.toReal :=
  ENNReal.toReal_pos u.positive.ne' hfin

theorem MaximalSolution.ode_finite (u : MaximalSolution P)
    (hfin : u.lifetime ≠ ⊤) :
    ∀ t ∈ Set.Ico 0 u.lifetime.toReal,
      HasDerivAt u.trajectory (P.evalField (u.trajectory t)) t := by
  intro t ht
  apply u.ode t
  rw [forwardInterval_finite u.positive hfin]
  exact ht

/-- The strong finite-endpoint blow-up alternative. -/
theorem MaximalSolution.norm_tendsto_at_finite (u : MaximalSolution P)
    (hfin : u.lifetime ≠ ⊤) :
    Tendsto (fun t => ‖u.trajectory t‖)
      (nhdsWithin u.lifetime.toReal (Set.Iio u.lifetime.toReal)) atTop := by
  rw [Filter.tendsto_atTop]
  intro K
  obtain ⟨ε, hε, hext⟩ :=
    uniform_forward_extension P (max K 0) (le_max_right _ _)
  let T := u.lifetime.toReal
  let a : ℝ := max 0 (T - ε / 2)
  have hT : 0 < T := u.finite_time_pos hfin
  have ha : a < T := max_lt hT (by linarith)
  have ha_nonneg : 0 ≤ a := le_max_left _ _
  have ha_lower : T - ε / 2 ≤ a := le_max_right _ _
  refine mem_nhdsLT_iff_exists_Ioo_subset.mpr ⟨a, ha, ?_⟩
  intro t ht
  change K ≤ ‖u.trajectory t‖
  by_contra hsmall
  have htzero : 0 ≤ t := ha_nonneg.trans ht.1.le
  have hdom : t ∈ forwardInterval u.lifetime := by
    rw [forwardInterval_finite u.positive hfin]
    exact ⟨htzero, ht.2⟩
  have hb : ‖u.trajectory t‖ ≤ max K 0 :=
    (lt_of_not_ge hsmall).le.trans (le_max_left _ _)
  obtain ⟨v, hv, _⟩ := hext u.toForwardSolution t hdom hb
  have hTR : T < t + ε := by linarith [ht.1]
  have hR : 0 < t + ε := by linarith
  have hlt : u.lifetime < v.lifetime := by
    calc
      u.lifetime = ENNReal.ofReal T := (ENNReal.ofReal_toReal hfin).symm
      _ < ENNReal.ofReal (t + ε) :=
        (ENNReal.ofReal_lt_ofReal_iff hR).mpr hTR
      _ = v.lifetime := hv.symm
  exact (not_lt_of_ge (u.lifetime_le v)) hlt

/-- The exact unboundedness premise used by the existing blow-up compilers. -/
theorem MaximalSolution.not_bddAbove_of_finite (u : MaximalSolution P)
    (hfin : u.lifetime ≠ ⊤) :
    ¬ BddAbove ((fun t => ‖u.trajectory t‖) '' Set.Ico 0 u.lifetime.toReal) := by
  rintro ⟨K, hK⟩
  have hhigh : ∀ᶠ t in nhdsWithin u.lifetime.toReal (Set.Iio u.lifetime.toReal),
      K + 1 ≤ ‖u.trajectory t‖ :=
    (Filter.tendsto_atTop.mp (u.norm_tendsto_at_finite hfin)) (K + 1)
  obtain ⟨a, ha, hab⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hhigh
  have hm : max a 0 < u.lifetime.toReal :=
    max_lt ha (u.finite_time_pos hfin)
  obtain ⟨t, htl, htr⟩ := exists_between hm
  have hn : 0 ≤ t := (le_max_right a 0).trans htl.le
  have hlo : ‖u.trajectory t‖ ≤ K := hK ⟨t, ⟨hn, htr⟩, rfl⟩
  have hhi : K + 1 ≤ ‖u.trajectory t‖ := hab ⟨(le_max_left a 0).trans_lt htl, htr⟩
  linarith

/-- A global forward solution exists exactly when the maximal lifespan is infinite. -/
theorem MaximalSolution.lifetime_eq_top_iff (u : MaximalSolution P) :
    u.lifetime = ⊤ ↔ Nonempty (PIVP.Solution P.toPIVP) := by
  constructor
  · intro h
    exact ⟨u.toForwardSolution.toGlobal h⟩
  · rintro ⟨s⟩
    exact top_le_iff.mp (u.lifetime_le (ForwardSolution.ofGlobal s))

/-! ## The complete time change, for finite and infinite maximal lifespans -/

/-- The source endpoint filter: infinity, or approach to a finite endpoint from below. -/
def endpointFilter (T : ℝ≥0∞) : Filter ℝ := by
  classical
  exact if T = ⊤ then atTop else nhdsWithin T.toReal (Set.Iio T.toReal)

def jointTime (u : MaximalSolution P) (N : ℕ) (t : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..t, jointClock N (u.trajectory v)

theorem jointTime_nonneg (u : MaximalSolution P) {N : ℕ}
    (hN : Even N) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ jointTime u N t :=
  intervalIntegral.integral_nonneg ht
    (fun v _ => zero_le_one.trans (jointClock_ge_one hN _))

/-- Complete inverse-clock data. `curve` is a continuous total representative
of the reparametrized source and agrees with the actual source for τ ≥ 0. -/
structure TimeChange (u : MaximalSolution P) (N : ℕ) where
  inverse : ℝ → ℝ
  inverse_zero : inverse 0 = 0
  inverse_continuous : Continuous inverse
  inverse_strictMono : StrictMono inverse
  inverse_mem : ∀ τ, 0 ≤ τ → inverse τ ∈ forwardInterval u.lifetime
  left_inverse : ∀ t ∈ forwardInterval u.lifetime,
    inverse (jointTime u N t) = t
  right_inverse : ∀ τ, 0 ≤ τ → jointTime u N (inverse τ) = τ
  inverse_deriv : ∀ τ, 0 ≤ τ →
    HasDerivAt inverse (jointClock N (u.trajectory (inverse τ)))⁻¹ τ
  inverse_limit : Tendsto inverse atTop (endpointFilter u.lifetime)
  curve : ℝ → Fin d → ℝ
  curve_continuous : Continuous curve
  curve_eq : ∀ τ, 0 ≤ τ → curve τ = u.trajectory (inverse τ)
  curve_initial : curve 0 = fun i => (P.init i : ℝ)
  curve_deriv : ∀ τ, 0 ≤ τ → ∀ i,
    HasDerivAt (fun σ => curve σ i)
      (P.evalField (curve τ) i / jointClock N (curve τ)) τ

/-- The displacement-versus-clock argument, separated from maximality.
This is the estimate used in `SurrogateCompilationBlowup.lean`. -/
private theorem clock_unbounded (P : PolyPIVP d) {N : ℕ}
    (hN : Even N) (hdeg : ∀ i, (P.field i).totalDegree ≤ N)
    {T : ℝ} (y : ℝ → Fin d → ℝ)
    (hc : ContinuousOn y (Set.Iio T))
    (hd : ∀ t ∈ Set.Ico 0 T, HasDerivAt y (P.evalField (y t)) t)
    (hunb : ¬ BddAbove ((fun t => ‖y t‖) '' Set.Ico 0 T)) :
    ¬ BddAbove (clockIntegral (fun t => jointClock N (y t)) '' Set.Ico 0 T) := by
  rintro ⟨K, hK⟩
  apply hunb
  let CF : ℝ := ∑ i, ∑ b : MIndex d N, |(((P.field i).coeff b.toFinsupp : ℚ) : ℝ)|
  have hCF : 0 ≤ CF :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun b _ => abs_nonneg _
  refine ⟨∑ i, |y 0 i| + CF * max K 0, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have hθt : clockIntegral (fun v => jointClock N (y v)) t ≤ max K 0 :=
    (hK ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  have hci : ∀ i, ContinuousOn (fun v => P.evalField (y v) i) (Set.Icc 0 t) :=
    fun i => ((continuous_apply i).comp P.continuous_evalField).comp_continuousOn
      (hc.mono fun v hv => hv.2.trans_lt ht.2)
  have hcoord : ∀ i, |y t i| ≤ |y 0 i| + CF * max K 0 := by
    intro i
    have hderiv : ∀ v ∈ Set.uIcc 0 t,
        HasDerivAt (fun v => y v i) (P.evalField (y v) i) v := by
      intro v hv
      rw [Set.uIcc_of_le ht.1] at hv
      exact hasDerivAt_pi.mp (hd v ⟨hv.1, hv.2.trans_lt ht.2⟩) i
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((hci i).intervalIntegrable_of_Icc ht.1)
    have hF : ∀ v ∈ Set.Icc 0 t,
        |P.evalField (y v) i| ≤ CF * jointClock N (y v) := by
      intro v _
      refine (abs_eval₂_le_jointClock hN (P.field i) (hdeg i) (y v)).trans ?_
      apply mul_le_mul_of_nonneg_right _
        (zero_le_one.trans (jointClock_ge_one hN _))
      exact Finset.single_le_sum
        (f := fun i => ∑ b : MIndex d N, |(((P.field i).coeff b.toFinsupp : ℚ) : ℝ)|)
        (fun i _ => Finset.sum_nonneg fun b _ => abs_nonneg _)
        (Finset.mem_univ i)
    have hint : |∫ v in (0 : ℝ)..t, P.evalField (y v) i| ≤
        CF * clockIntegral (fun v => jointClock N (y v)) t := by
      calc
        |∫ v in (0 : ℝ)..t, P.evalField (y v) i|
            ≤ ∫ v in (0 : ℝ)..t, |P.evalField (y v) i| :=
          intervalIntegral.abs_integral_le_integral_abs ht.1
        _ ≤ ∫ v in (0 : ℝ)..t, CF * jointClock N (y v) :=
          intervalIntegral.integral_mono_on ht.1
            (((hci i).abs).intervalIntegrable_of_Icc ht.1)
            (ContinuousOn.intervalIntegrable_of_Icc ht.1
              (continuousOn_const.mul ((continuous_jointClock N).comp_continuousOn
                (hc.mono fun v (hv : v ∈ Set.Icc 0 t) => hv.2.trans_lt ht.2)))) hF
        _ = CF * clockIntegral (fun v => jointClock N (y v)) t := by
          unfold clockIntegral
          exact intervalIntegral.integral_const_mul _ _
    rw [hftc] at hint
    have ha := abs_sub_abs_le_abs_sub (y t i) (y 0 i)
    have hb := mul_le_mul_of_nonneg_left hθt hCF
    linarith
  refine (pi_norm_le_iff_of_nonneg ?_).mpr fun i => ?_
  · exact add_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)
      (mul_nonneg hCF (le_max_right _ _))
  · rw [Real.norm_eq_abs]
    have hi : |y 0 i| ≤ ∑ j, |y 0 j| :=
      Finset.single_le_sum (f := fun j => |y 0 j|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    exact (hcoord i).trans (by linarith)

/-- B3, including both lifespans. There is no independent blow-up premise. -/
theorem exists_timeChange (u : MaximalSolution P) {N : ℕ}
    (hN : Even N) (hdeg : ∀ i, (P.field i).totalDegree ≤ N) :
    Nonempty (TimeChange u N) := by
  classical
  by_cases htop : u.lifetime = ⊤
  · let sol := u.toForwardSolution.toGlobal htop
    obtain ⟨solc, hcont, heq⟩ := sol.exists_continuous
    have hagree : ∀ t, 0 ≤ t → solc.trajectory t = u.trajectory t :=
      fun t ht => heq t ht
    have hρc : Continuous (fun t => jointClock N (solc.trajectory t)) :=
      (continuous_jointClock N).comp hcont
    have hρ : ∀ t, 1 ≤ jointClock N (solc.trajectory t) :=
      fun t => jointClock_ge_one hN _
    obtain ⟨s, hs, hsd, hsc, hsm, hst, hsθ, hθs⟩ :=
      exists_inverse_timeChange hρc hρ
    have hnonneg : ∀ τ, 0 ≤ τ → 0 ≤ s τ :=
      fun τ hτ => hs ▸ hsm.monotone hτ
    have hclock : ∀ t, 0 ≤ t → jointTime u N t =
        clockIntegral (fun v => jointClock N (solc.trajectory v)) t := by
      intro t ht
      unfold jointTime clockIntegral
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [Set.uIcc_of_le ht] at hv
      rw [hagree v hv.1]
    refine ⟨{
      inverse := s
      inverse_zero := hs
      inverse_continuous := hsc
      inverse_strictMono := hsm
      inverse_mem := fun τ hτ => ⟨hnonneg τ hτ, by simp [htop]⟩
      left_inverse := ?_
      right_inverse := ?_
      inverse_deriv := ?_
      inverse_limit := by simpa only [endpointFilter, if_pos htop] using hst
      curve := fun τ => solc.trajectory (s τ)
      curve_continuous := hcont.comp hsc
      curve_eq := fun τ hτ => hagree (s τ) (hnonneg τ hτ)
      curve_initial := by rw [hs, solc.init_cond]; rfl
      curve_deriv := ?_ }⟩
    · intro t ht
      rw [hclock t ht.1]
      exact hsθ t
    · intro τ hτ
      rw [hclock (s τ) (hnonneg τ hτ)]
      exact hθs τ
    · intro τ hτ
      simpa only [hagree (s τ) (hnonneg τ hτ)] using hsd τ
    · intro τ hτ i
      have h := (solc.is_solution (s τ) (hnonneg τ hτ)).scomp τ (hsd τ)
      refine (hasDerivAt_pi.mp h i).congr_deriv ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_eq_inv_mul]; rfl
  · have hT := u.finite_time_pos htop
    have hy := u.ode_finite htop
    obtain ⟨y, hc, hagree, hd⟩ := exists_extension_Iio hT u.trajectory hy
    have hunb : ¬ BddAbove ((fun t => ‖y t‖) '' Set.Ico 0 u.lifetime.toReal) := by
      rintro ⟨K, hK⟩
      apply u.not_bddAbove_of_finite htop
      refine ⟨K, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      have h : ‖y t‖ ≤ K := hK ⟨t, ht, rfl⟩
      rwa [hagree t ht.1] at h
    have hρc : ContinuousOn (fun t => jointClock N (y t))
        (Set.Iio u.lifetime.toReal) :=
      (continuous_jointClock N).comp_continuousOn hc
    have hρ : ∀ t, 1 ≤ jointClock N (y t) :=
      fun t => jointClock_ge_one hN _
    have hθunb := clock_unbounded P hN hdeg y hc hd hunb
    obtain ⟨s, hs, hsT, hsd, hsc, hsm, hst, hsθ⟩ :=
      exists_inverse_timeChange_Iio hT hρc hρ hθunb
    have hnonneg : ∀ τ, 0 ≤ τ → 0 ≤ s τ :=
      fun τ hτ => hs ▸ hsm.monotone hτ
    have hmem : ∀ τ, 0 ≤ τ → s τ ∈ forwardInterval u.lifetime := by
      intro τ hτ
      rw [forwardInterval_finite u.positive htop]
      exact ⟨hnonneg τ hτ, hsT τ⟩
    have hclock : ∀ t, 0 ≤ t → jointTime u N t =
        clockIntegral (fun v => jointClock N (y v)) t := by
      intro t ht
      unfold jointTime clockIntegral
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [Set.uIcc_of_le ht] at hv
      rw [hagree v hv.1]
    have hθs : ∀ τ, clockIntegral (fun v => jointClock N (y v)) (s τ) = τ :=
      fun τ => hsm.injective (hsθ (s τ) (hsT τ))
    refine ⟨{
      inverse := s
      inverse_zero := hs
      inverse_continuous := hsc
      inverse_strictMono := hsm
      inverse_mem := hmem
      left_inverse := ?_
      right_inverse := ?_
      inverse_deriv := ?_
      inverse_limit := by simpa only [endpointFilter, if_neg htop] using hst
      curve := fun τ => y (s τ)
      curve_continuous := hc.comp_continuous hsc (fun τ => hsT τ)
      curve_eq := fun τ hτ => hagree (s τ) (hnonneg τ hτ)
      curve_initial := by rw [hs, hagree 0 le_rfl, u.initial]
      curve_deriv := ?_ }⟩
    · intro t ht
      have ht' : t ∈ Set.Ico 0 u.lifetime.toReal := by
        rwa [forwardInterval_finite u.positive htop] at ht
      rw [hclock t ht'.1]
      exact hsθ t ht'.2
    · intro τ hτ
      rw [hclock (s τ) (hnonneg τ hτ)]
      exact hθs τ
    · intro τ hτ
      simpa only [hagree (s τ) (hnonneg τ hτ)] using hsd τ
    · intro τ hτ i
      have h := (hd (s τ) ⟨hnonneg τ hτ, hsT τ⟩).scomp τ (hsd τ)
      refine (hasDerivAt_pi.mp h i).congr_deriv ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [div_eq_inv_mul]

/-- The clock has exactly the paper's source and target intervals. -/
theorem TimeChange.clock_bijOn {u : MaximalSolution P} {N : ℕ}
    (tc : TimeChange u N) (hN : Even N) :
    Set.BijOn (jointTime u N) (forwardInterval u.lifetime) (Set.Ici 0) := by
  refine ⟨fun t ht => jointTime_nonneg u hN ht.1, ?_, ?_⟩
  · intro a ha b hb hab
    have h := congrArg tc.inverse hab
    simpa only [tc.left_inverse a ha, tc.left_inverse b hb] using h
  · intro τ hτ
    exact ⟨tc.inverse τ, tc.inverse_mem τ hτ, tc.right_inverse τ hτ⟩

theorem TimeChange.inverse_image {u : MaximalSolution P} {N : ℕ}
    (tc : TimeChange u N) (hN : Even N) :
    tc.inverse '' Set.Ici 0 = forwardInterval u.lifetime := by
  ext t
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact tc.inverse_mem τ hτ
  · intro ht
    exact ⟨jointTime u N t, jointTime_nonneg u hN ht.1, tc.left_inverse t ht⟩

theorem TimeChange.clock_strictMonoOn {u : MaximalSolution P} {N : ℕ}
    (tc : TimeChange u N) :
    StrictMonoOn (jointTime u N) (forwardInterval u.lifetime) := by
  intro a ha b hb hab
  by_contra h
  have hm := tc.inverse_strictMono.monotone (not_lt.mp h)
  rw [tc.left_inverse b hb, tc.left_inverse a ha] at hm
  exact (not_le_of_gt hab) hm

/-- The inverse derivative has precisely the range (0,1]. -/
theorem TimeChange.inverse_derivative_bounds {u : MaximalSolution P} {N : ℕ}
    (tc : TimeChange u N) (hN : Even N) (τ : ℝ) :
    0 < (jointClock N (u.trajectory (tc.inverse τ)))⁻¹ ∧
      (jointClock N (u.trajectory (tc.inverse τ)))⁻¹ ≤ 1 := by
  have hp := jointClock_pos hN (u.trajectory (tc.inverse τ))
  refine ⟨inv_pos.mpr hp, ?_⟩
  simpa only [one_div] using
    (div_le_one hp).mpr (jointClock_ge_one hN (u.trajectory (tc.inverse τ)))

/-- The exact source-coordinate limit, for any coordinate, not just the output. -/
theorem TimeChange.coordinate_limit {u : MaximalSolution P} {N : ℕ}
    (tc : TimeChange u N) (i : Fin d) {L : ℝ}
    (hlim : Tendsto (fun t => u.trajectory t i) (endpointFilter u.lifetime) (𝓝 L)) :
    Tendsto (fun τ => u.trajectory (tc.inverse τ) i) atTop (𝓝 L) :=
  hlim.comp tc.inverse_limit

/-- B3's full compiled solution formula and forward uniqueness. -/
theorem TimeChange.compiled_solution {u : MaximalSolution P} {N : ℕ}
    (tc : TimeChange u N) (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N) :
    ∃ sol : PIVP.Solution (P.jointSurrogateCompile N).toPIVP,
      Continuous sol.trajectory ∧
      (∀ τ, 0 ≤ τ → sol.trajectory τ (P.jointSurrogateCompile N).output =
        u.trajectory (tc.inverse τ) P.output) ∧
      (∀ τ, 0 ≤ τ → ∀ a : SurrogateIndex d N,
        sol.trajectory τ (surrogateCoord a) =
          jointSurrogate N a (u.trajectory (tc.inverse τ))) ∧
      (∀ other : PIVP.Solution (P.jointSurrogateCompile N).toPIVP,
        Set.EqOn other.trajectory sol.trajectory (Set.Ici 0)) := by
  obtain ⟨sol, hout, hsur, hc⟩ :=
    P.jointSurrogateCompile_solution_of_curve hN hdeg
      tc.curve tc.curve_initial tc.curve_deriv
  refine ⟨sol, hc tc.curve_continuous, ?_, ?_, ?_⟩
  · intro τ hτ
    rw [hout τ, tc.curve_eq τ hτ]
  · intro τ hτ a
    rw [hsur τ a, tc.curve_eq τ hτ]
  · intro other
    exact global_solution_unique _ other sol

/-! ## B4: endpoint limits, the source supremum, and bounded certificates -/

def coordinateValues (u : MaximalSolution P) (i : Fin d) : Set ℝ :=
  (fun t => |u.trajectory t i|) '' forwardInterval u.lifetime

def coordinateSup (u : MaximalSolution P) (i : Fin d) : ℝ :=
  sSup (coordinateValues u i)

/-- A finite coordinate limit bounds that coordinate on the entire forward lifespan. -/
theorem coordinateValues_bddAbove (u : MaximalSolution P) (i : Fin d) {L : ℝ}
    (hlim : Tendsto (fun t => u.trajectory t i) (endpointFilter u.lifetime) (𝓝 L)) :
    BddAbove (coordinateValues u i) := by
  classical
  by_cases htop : u.lifetime = ⊤
  · have hlim' : Tendsto (fun t => u.trajectory t i) atTop (𝓝 L) := by
      simpa only [endpointFilter, if_pos htop] using hlim
    obtain ⟨M, _, hM⟩ := exists_abs_le_of_tendsto
      (fun t ht => (continuous_apply i).continuousAt.comp
        (u.ode t ⟨ht, by simp [htop]⟩).continuousAt) hlim'
    refine ⟨M, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hM t ht.1
  · have hlim' : Tendsto (fun t => u.trajectory t i)
        (nhdsWithin u.lifetime.toReal (Set.Iio u.lifetime.toReal)) (𝓝 L) := by
      simpa only [endpointFilter, if_neg htop] using hlim
    obtain ⟨M, _, hM⟩ := exists_abs_le_of_tendsto_Iio (u.finite_time_pos htop)
      (fun t ht => (continuous_apply i).continuousAt.comp
        (u.ode_finite htop t ht).continuousAt) hlim'
    refine ⟨M, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    apply hM t
    rwa [forwardInterval_finite u.positive htop] at ht

theorem coordinate_le_sup (u : MaximalSolution P) (i : Fin d)
    (hb : BddAbove (coordinateValues u i)) {t : ℝ}
    (ht : t ∈ forwardInterval u.lifetime) :
    |u.trajectory t i| ≤ coordinateSup u i :=
  le_csSup hb ⟨t, ht, rfl⟩

theorem coordinateSup_nonneg (u : MaximalSolution P) (i : Fin d)
    (hb : BddAbove (coordinateValues u i)) : 0 ≤ coordinateSup u i := by
  have hz : (0 : ℝ) ∈ forwardInterval u.lifetime :=
    ⟨le_rfl, by simpa using u.positive⟩
  exact (abs_nonneg _).trans (coordinate_le_sup u i hb hz)

/-- B4 in a single exported package, for either maximal lifespan.
The certificate has the original-time output identity, every surrogate
identity, the actual source supremum bound, and an explicit all-state bound. -/
theorem bounded_compilation_of_maximal_certified
    (u : MaximalSolution P) {N : ℕ} (hN : Even N)
    (hdeg : ∀ i, (P.field i).totalDegree ≤ N) {L : ℝ}
    (hlim : Tendsto (fun t => u.trajectory t P.output)
      (endpointFilter u.lifetime) (𝓝 L)) :
    ∃ (tc : TimeChange u N)
      (btc : CertifiedBoundedTimeComputable (jointDim d N) L),
      btc.pivp = P.jointSurrogateCompile N ∧
      BddAbove (coordinateValues u P.output) ∧
      (∀ τ, 0 ≤ τ → btc.sol.trajectory τ btc.pivp.output =
        u.trajectory (tc.inverse τ) P.output) ∧
      (∀ τ, 0 ≤ τ → ∀ a : SurrogateIndex d N,
        btc.sol.trajectory τ (surrogateCoord a) =
          jointSurrogate N a (u.trajectory (tc.inverse τ))) ∧
      (∀ τ, 0 ≤ τ → |btc.sol.trajectory τ btc.pivp.output| ≤
        coordinateSup u P.output) ∧
      (∀ τ, 0 ≤ τ → ‖btc.sol.trajectory τ‖ ≤
        max (coordinateSup u P.output) 1) ∧
      Tendsto (fun τ => btc.sol.trajectory τ btc.pivp.output) atTop (𝓝 L) := by
  obtain ⟨tc⟩ := exists_timeChange u hN hdeg
  obtain ⟨sol, hc, hout, hsur, _⟩ := tc.compiled_solution hN hdeg
  have hsup := coordinateValues_bddAbove u P.output hlim
  have hsource : ∀ τ, 0 ≤ τ →
      |u.trajectory (tc.inverse τ) P.output| ≤ coordinateSup u P.output :=
    fun τ hτ => coordinate_le_sup u P.output hsup (tc.inverse_mem τ hτ)
  have hbd := jointSurrogateCompile_isBounded P hN sol
    (fun τ => u.trajectory (tc.inverse τ)) hout hsur hsource
  have hlimit : Tendsto (fun τ => sol.trajectory τ (P.jointSurrogateCompile N).output)
      atTop (𝓝 L) := by
    refine (tc.coordinate_limit P.output hlim).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with τ hτ
    exact (hout τ hτ).symm
  have hnorm : ∀ τ, 0 ≤ τ →
      ‖sol.trajectory τ‖ ≤ max (coordinateSup u P.output) 1 := by
    intro τ hτ
    refine (pi_norm_le_iff_of_nonneg
      (zero_le_one.trans (le_max_right _ _))).mpr fun j => ?_
    rw [Real.norm_eq_abs]
    rcases jointCoord_cases j with rfl | ⟨a, rfl⟩
    · rw [← jointSurrogateCompile_output, hout τ hτ]
      exact (hsource τ hτ).trans (le_max_left _ _)
    · rw [hsur τ hτ a]
      exact (jointSurrogate_abs_le_one hN a _).trans (le_max_right _ _)
  obtain ⟨btc, hpin, htraj⟩ :=
    CertifiedBoundedTimeComputable.exists_of_tendsto _ sol hbd hc hlimit
  refine ⟨tc, btc, hpin, hsup, ?_, ?_, ?_, ?_, btc.to_tendsto⟩
  · intro τ hτ
    rw [htraj, hpin]
    exact hout τ hτ
  · intro τ hτ a
    rw [htraj]
    exact hsur τ hτ a
  · intro τ hτ
    rw [htraj, hpin, hout τ hτ]
    exact hsource τ hτ
  · intro τ hτ
    rw [htraj]
    exact hnorm τ hτ

/-- Direct finite-lifespan bridge to the existing B4 compiler. -/
theorem bounded_compilation_of_finite_maximal_certified
    (u : MaximalSolution P) (hfin : u.lifetime ≠ ⊤)
    {N : ℕ} (hN : Even N) (hdeg : ∀ i, (P.field i).totalDegree ≤ N) {L : ℝ}
    (hlim : Tendsto (fun t => u.trajectory t P.output)
      (nhdsWithin u.lifetime.toReal (Set.Iio u.lifetime.toReal)) (𝓝 L)) :
    ∃ btc : CertifiedBoundedTimeComputable (jointDim d N) L,
      btc.pivp = P.jointSurrogateCompile N :=
  Ripple.bounded_compilation_of_blowup_certified P hN hdeg
    u.trajectory u.initial (u.ode_finite hfin)
    (u.not_bddAbove_of_finite hfin) hlim

/-- The original time-change interface now requires finite maximality,
not an independent norm-unboundedness assumption. The stronger all-lifespan
interface is `exists_timeChange` together with the `TimeChange` projections. -/
theorem exists_timeChange_of_finite_maximal
    (u : MaximalSolution P) (hfin : u.lifetime ≠ ⊤)
    {N : ℕ} (hN : Even N) (hdeg : ∀ i, (P.field i).totalDegree ≤ N) :
    ∃ (y : ℝ → Fin d → ℝ) (s : ℝ → ℝ),
      (∀ t, 0 ≤ t → y t = u.trajectory t) ∧ s 0 = 0 ∧
      (∀ τ, 0 ≤ τ → 0 ≤ s τ ∧ s τ < u.lifetime.toReal) ∧
      Continuous (fun τ => y (s τ)) ∧ Continuous s ∧
      Tendsto s atTop (nhdsWithin u.lifetime.toReal (Set.Iio u.lifetime.toReal)) ∧
      (∀ τ, HasDerivAt s (jointClock N (y (s τ)))⁻¹ τ) ∧
      (∀ τ, 0 ≤ τ → ∀ i, HasDerivAt (fun σ => y (s σ) i)
        (P.evalField (y (s τ)) i / jointClock N (y (s τ))) τ) :=
  Ripple.exists_timeChange_of_blowup P hN hdeg (u.finite_time_pos hfin)
    u.trajectory (u.ode_finite hfin) (u.not_bddAbove_of_finite hfin)

/-! ## B5: a finite maximal endpoint is bounded-PIVP computable -/

/-- Every admissible exponent gives the specified clock compiler. No output
limit and no independently assumed blow-up property are required. -/
theorem isCRNComputable_maximalTime_certified
    (u : MaximalSolution P) (hfin : u.lifetime ≠ ⊤)
    {N : ℕ} (hN : Even N) (hdeg : ∀ i, (P.field i).totalDegree ≤ N) :
    ∃ btc : CertifiedBoundedTimeComputable (jointDim d N) u.lifetime.toReal,
      btc.pivp = P.jointClockCompile N :=
  Ripple.isCRNComputable_blowupTime_certified P hN hdeg
    u.trajectory u.initial (u.ode_finite hfin) (u.not_bddAbove_of_finite hfin)

theorem isCRNComputable_maximalTime
    (u : MaximalSolution P) (hfin : u.lifetime ≠ ⊤) :
    IsCRNComputable u.lifetime.toReal :=
  Ripple.isCRNComputable_blowupTime P u.trajectory u.initial
    (u.ode_finite hfin) (u.not_bddAbove_of_finite hfin)

end Ripple.MaximalPIVP
