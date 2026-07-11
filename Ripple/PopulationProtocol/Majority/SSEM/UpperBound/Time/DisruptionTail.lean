import Ripple.PopulationProtocol.Majority.SSEM.Probability.RandomScheduler
import Ripple.PopulationProtocol.Majority.SSEM.Protocol.RankDelta
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.PowersetCard
import Mathlib.Data.Nat.Choose.Bounds

namespace SSEM

open scoped BigOperators ENNReal

variable {n : ℕ}

/-!
# Disruption tail certificates

This file isolates the scheduler-load certificate used for the disruption
tail.  The protocol-specific datum is `ErrorLoadCertificateAt`: while an
agent is still `Unsettled`, its current counter plus the number of times it
has been selected in the prefix is at least the fresh reset value `Emax`.
-/

/-- Agent `a` is one of the two endpoints selected by deterministic scheduler
`γ` at time `t`. -/
def selectedAt (γ : DetScheduler n) (a : Fin n) (t : ℕ) : Prop :=
  a = (γ t).1 ∨ a = (γ t).2

instance selectedAt_decidable (γ : DetScheduler n) (a : Fin n) (t : ℕ) :
    Decidable (selectedAt γ a t) := by
  unfold selectedAt
  infer_instance

/-- Number of steps `t < K` in which `a` is selected as an endpoint. -/
def selectionCount (γ : DetScheduler n) (a : Fin n) (K : ℕ) : ℕ :=
  ((Finset.range K).filter fun t => selectedAt γ a t).card

theorem selectionCount_mono
    (γ : DetScheduler n) (a : Fin n) {K L : ℕ} (hKL : K ≤ L) :
    selectionCount γ a K ≤ selectionCount γ a L := by
  classical
  unfold selectionCount
  apply Finset.card_le_card
  intro t ht
  rw [Finset.mem_filter] at ht ⊢
  have htK : t < K := by simpa using ht.1
  have htL : t < L := lt_of_lt_of_le htK hKL
  exact ⟨by simpa using htL, ht.2⟩

theorem selectionCount_succ
    (γ : DetScheduler n) (a : Fin n) (t : ℕ) :
    selectionCount γ a (t + 1) =
      selectionCount γ a t + if selectedAt γ a t then 1 else 0 := by
  classical
  unfold selectionCount
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases hsel : selectedAt γ a t
  · rw [if_pos hsel]
    simp [hsel]
  · rw [if_neg hsel]
    simp [hsel]

theorem selectionCount_succ_of_selected
    (γ : DetScheduler n) (a : Fin n) {t : ℕ}
    (hsel : selectedAt γ a t) :
    selectionCount γ a (t + 1) = selectionCount γ a t + 1 := by
  rw [selectionCount_succ, if_pos hsel]

/-- The error-load certificate at a concrete configuration/time. -/
def ErrorLoadCertificateAt
    (Emax : ℕ) (γ : DetScheduler n) (t : ℕ)
    (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ a : Fin n,
    (C a).1.role = .Unsettled →
      Emax ≤ (C a).1.errorcount + selectionCount γ a t

/-- A one-step abstract condition sufficient to propagate the load
certificate.  Each post-step `Unsettled` endpoint is either freshly created
with counter at least `Emax`, or came from a pre-step `Unsettled` endpoint
whose counter dropped by at most one if that endpoint was selected. -/
def ErrorCounterStepOK
    (Emax : ℕ) (γ : DetScheduler n) (t : ℕ)
    (C C' : Config (AgentState n) Opinion n) : Prop :=
  ∀ a : Fin n,
    (C' a).1.role = .Unsettled →
      Emax ≤ (C' a).1.errorcount ∨
        ((C a).1.role = .Unsettled ∧
          (C a).1.errorcount ≤
            (C' a).1.errorcount +
              (if selectedAt γ a t then 1 else 0))

theorem ErrorLoadCertificateAt.step
    {Emax : ℕ} {γ : DetScheduler n} {t : ℕ}
    {C C' : Config (AgentState n) Opinion n}
    (hcert : ErrorLoadCertificateAt Emax γ t C)
    (hstep : ErrorCounterStepOK Emax γ t C C') :
    ErrorLoadCertificateAt Emax γ (t + 1) C' := by
  classical
  intro a haUn
  have hsucc := selectionCount_succ γ a t
  rcases hstep a haUn with hfresh | hprev
  · rw [hsucc]
    omega
  · rcases hprev with ⟨haUnOld, hdrop⟩
    have hold := hcert a haUnOld
    rw [hsucc]
    by_cases hsel : selectedAt γ a t <;> simp [hsel] at hdrop ⊢ <;> omega

/-- Initial configurations whose existing `Unsettled` agents already have a
fresh enough counter satisfy the time-0 load certificate. -/
theorem initial_error_load_certificate
    {Emax : ℕ} {γ : DetScheduler n}
    {C : Config (AgentState n) Opinion n}
    (hinit : ∀ a : Fin n,
      (C a).1.role = .Unsettled → Emax ≤ (C a).1.errorcount) :
    ErrorLoadCertificateAt Emax γ 0 C := by
  intro a ha
  simpa [selectionCount] using hinit a ha

/-- Structural disruption predicate used by the load certificate: before step
`t`, a selected `Unsettled` endpoint has counter at most `1`, so that the
error-monitoring decrement can drain it to zero during this interaction. -/
def ErrorTimeoutSelectedAt
    (γ : DetScheduler n) (t : ℕ)
    (C : Config (AgentState n) Opinion n) (a : Fin n) : Prop :=
  selectedAt γ a t ∧
    (C a).1.role = .Unsettled ∧
      (C a).1.errorcount ≤ 1

/-- Disruption before `K`, packaged with the load certificate at the
pre-disruption time.  This is the exact certificate needed for the tail bound;
the separate `ErrorLoadCertificateAt.step` lemma is the reusable invariant
propagation hook for protocol-specific one-step proofs. -/
def DisruptionBeforeK
    (P : Protocol (AgentState n) Opinion Output)
    (Emax : ℕ) (C₀ : Config (AgentState n) Opinion n)
    (γ : DetScheduler n) (K : ℕ) : Prop :=
  ∃ t : ℕ, t < K ∧
    ∃ a : Fin n,
      ErrorLoadCertificateAt Emax γ t (execution P C₀ γ t) ∧
        ErrorTimeoutSelectedAt γ t (execution P C₀ γ t) a

/-- Load certificate: if an error timeout drains an `Unsettled` endpoint before
`K`, then some agent was selected at least `Emax` times in the first `K`
steps. -/
theorem disruption_before_K_implies_high_load
    {P : Protocol (AgentState n) Opinion Output}
    {Emax : ℕ} {C₀ : Config (AgentState n) Opinion n}
    {γ : DetScheduler n} {K : ℕ}
    (hD : DisruptionBeforeK P Emax C₀ γ K) :
    ∃ a : Fin n, Emax ≤ selectionCount γ a K := by
  rcases hD with ⟨t, htK, a, hcert, htimeout⟩
  rcases htimeout with ⟨hsel, haUn, haErr⟩
  refine ⟨a, ?_⟩
  have hcertA := hcert a haUn
  have hsucc :
      selectionCount γ a (t + 1) = selectionCount γ a t + 1 :=
    selectionCount_succ_of_selected γ a hsel
  have htoSucc :
      (execution P C₀ γ t a).1.errorcount + selectionCount γ a t ≤
        selectionCount γ a (t + 1) := by
    rw [hsucc]
    omega
  have hmono :
      selectionCount γ a (t + 1) ≤ selectionCount γ a K :=
    selectionCount_mono γ a (by omega)
  exact hcertA.trans (htoSucc.trans hmono)

/-! ## Union and crude binomial tail, as scheduler-prefix events -/

/-- A scheduler prefix of length `K`. -/
abbrev SchedulerPrefix (n K : ℕ) := Fin K → Fin n × Fin n

def prefixSelectedAt {K : ℕ}
    (σ : SchedulerPrefix n K) (a : Fin n) (t : Fin K) : Prop :=
  a = (σ t).1 ∨ a = (σ t).2

instance prefixSelectedAt_decidable {K : ℕ}
    (σ : SchedulerPrefix n K) (a : Fin n) (t : Fin K) :
    Decidable (prefixSelectedAt σ a t) := by
  unfold prefixSelectedAt
  infer_instance

def prefixSelectionCount {K : ℕ}
    (σ : SchedulerPrefix n K) (a : Fin n) : ℕ :=
  (Finset.univ.filter fun t : Fin K => prefixSelectedAt σ a t).card

def PrefixHighLoad {K : ℕ}
    (σ : SchedulerPrefix n K) (r : ℕ) : Prop :=
  ∃ a : Fin n, r ≤ prefixSelectionCount σ a

def PrefixAgentHighLoad {K : ℕ}
    (σ : SchedulerPrefix n K) (a : Fin n) (r : ℕ) : Prop :=
  r ≤ prefixSelectionCount σ a

def PrefixAgentSelectedOn {K : ℕ}
    (σ : SchedulerPrefix n K) (a : Fin n) (T : Finset (Fin K)) : Prop :=
  ∀ t ∈ T, prefixSelectedAt σ a t

theorem prefix_agent_high_load_has_selected_subset
    {K r : ℕ} {σ : SchedulerPrefix n K} {a : Fin n}
    (hload : PrefixAgentHighLoad σ a r) :
    ∃ T : Finset (Fin K),
      T.card = r ∧ PrefixAgentSelectedOn σ a T := by
  classical
  let S : Finset (Fin K) :=
    Finset.univ.filter fun t : Fin K => prefixSelectedAt σ a t
  have hrS : r ≤ S.card := by
    simpa [PrefixAgentHighLoad, prefixSelectionCount, S] using hload
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hrS
  refine ⟨T, hTcard, ?_⟩
  intro t ht
  have htS : t ∈ S := hTS ht
  exact (Finset.mem_filter.mp htS).2

/-- A fixed-agent high-load event is contained in the union over all `r`-sets
of times on which that agent is selected. -/
theorem prefix_agent_high_load_subset_selected_on_union
    {K r : ℕ} (a : Fin n) :
    {σ : SchedulerPrefix n K | PrefixAgentHighLoad σ a r} ⊆
      {σ : SchedulerPrefix n K |
        ∃ T : Finset (Fin K),
          T.card = r ∧ PrefixAgentSelectedOn σ a T} := by
  intro σ hσ
  exact prefix_agent_high_load_has_selected_subset hσ

/-- Crude binomial-tail union bound for a fixed agent, stated for any finite
prefix probability functional that has the expected independent-cylinder
bound. -/
theorem prefix_agent_high_load_mass_le_choose
    {K r : ℕ} {Ω : Type*} (mass : Set Ω → ENNReal)
    (A : Ω → SchedulerPrefix n K) (a : Fin n)
    (hmono : ∀ X Y : Set Ω, X ⊆ Y → mass X ≤ mass Y)
    (hUnion :
      ∀ B : {T : Finset (Fin K) // T.card = r} → Set Ω,
        mass {ω | ∃ T : {T : Finset (Fin K) // T.card = r}, ω ∈ B T} ≤
          ∑ T : {T : Finset (Fin K) // T.card = r}, mass (B T))
    (hcylinder :
      ∀ T : Finset (Fin K), T.card = r →
        mass {ω | PrefixAgentSelectedOn (A ω) a T} ≤
          ((2 : ENNReal) * (n : ENNReal)⁻¹) ^ r) :
    mass {ω | PrefixAgentHighLoad (A ω) a r} ≤
      (Nat.choose K r : ENNReal) *
        (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ r) := by
  classical
  let ι := {T : Finset (Fin K) // T.card = r}
  have hsub :
      {ω | PrefixAgentHighLoad (A ω) a r} ⊆
        {ω | ∃ T : ι, PrefixAgentSelectedOn (A ω) a T.1} := by
    intro ω hω
    obtain ⟨T, hTcard, hsel⟩ :=
      prefix_agent_high_load_has_selected_subset (σ := A ω) (a := a) hω
    exact ⟨⟨T, hTcard⟩, hsel⟩
  calc
    mass {ω | PrefixAgentHighLoad (A ω) a r}
        ≤ mass {ω | ∃ T : ι, PrefixAgentSelectedOn (A ω) a T.1} :=
          hmono _ _ hsub
    _ ≤ ∑ T : ι, mass {ω | PrefixAgentSelectedOn (A ω) a T.1} :=
          hUnion (fun T : ι => {ω | PrefixAgentSelectedOn (A ω) a T.1})
    _ ≤ ∑ _T : ι, ((2 : ENNReal) * (n : ENNReal)⁻¹) ^ r := by
          apply Finset.sum_le_sum
          intro T _hT
          exact hcylinder T.1 T.2
    _ = (Fintype.card ι : ENNReal) *
          (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ r) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = (Nat.choose K r : ENNReal) *
          (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ r) := by
          congr
          dsimp [ι]
          rw [← Nat.card_eq_fintype_card]
          change Nat.card (Set.powersetCard (Fin K) r) = Nat.choose K r
          simpa [Nat.card_eq_fintype_card, Fintype.card_fin] using
            (Set.powersetCard.card (α := Fin K) (n := r))

/-- Union over agents plus the fixed-agent crude binomial tail. -/
theorem prefix_high_load_mass_le_union_choose
    {K r : ℕ} {Ω : Type*} (mass : Set Ω → ENNReal)
    (A : Ω → SchedulerPrefix n K)
    (hmono : ∀ X Y : Set Ω, X ⊆ Y → mass X ≤ mass Y)
    (hUnionAgents :
      ∀ B : Fin n → Set Ω,
        mass {ω | ∃ a : Fin n, ω ∈ B a} ≤ ∑ a : Fin n, mass (B a))
    (hUnionTimes :
      ∀ _a : Fin n,
        ∀ B : {T : Finset (Fin K) // T.card = r} → Set Ω,
          mass {ω | ∃ T : {T : Finset (Fin K) // T.card = r}, ω ∈ B T} ≤
            ∑ T : {T : Finset (Fin K) // T.card = r}, mass (B T))
    (hcylinder :
      ∀ (a : Fin n) (T : Finset (Fin K)), T.card = r →
        mass {ω | PrefixAgentSelectedOn (A ω) a T} ≤
          ((2 : ENNReal) * (n : ENNReal)⁻¹) ^ r) :
    mass {ω | PrefixHighLoad (A ω) r} ≤
      (n : ENNReal) * (Nat.choose K r : ENNReal) *
        (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ r) := by
  classical
  have hsub :
      {ω | PrefixHighLoad (A ω) r} ⊆
        {ω | ∃ a : Fin n, PrefixAgentHighLoad (A ω) a r} := by
    intro ω hω
    exact hω
  calc
    mass {ω | PrefixHighLoad (A ω) r}
        ≤ mass {ω | ∃ a : Fin n, PrefixAgentHighLoad (A ω) a r} :=
          hmono _ _ hsub
    _ ≤ ∑ a : Fin n, mass {ω | PrefixAgentHighLoad (A ω) a r} :=
          hUnionAgents
            (fun a : Fin n => {ω | PrefixAgentHighLoad (A ω) a r})
    _ ≤ ∑ _a : Fin n,
          (Nat.choose K r : ENNReal) *
            (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ r) := by
          apply Finset.sum_le_sum
          intro a _ha
          exact prefix_agent_high_load_mass_le_choose
            (n := n) (K := K) (r := r) mass A a hmono (hUnionTimes a)
            (hcylinder a)
    _ = (n : ENNReal) * (Nat.choose K r : ENNReal) *
          (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ r) := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- Final union-tail wrapper: any disruption event already certified to imply
prefix high load inherits the crude binomial union bound. -/
theorem disruption_event_mass_le_union_choose
    {K r : ℕ} {Ω : Type*} (mass : Set Ω → ENNReal)
    (A : Ω → SchedulerPrefix n K) (D : Ω → Prop)
    (hD_high : ∀ ω : Ω, D ω → PrefixHighLoad (A ω) r)
    (hmono : ∀ X Y : Set Ω, X ⊆ Y → mass X ≤ mass Y)
    (hUnionAgents :
      ∀ B : Fin n → Set Ω,
        mass {ω | ∃ a : Fin n, ω ∈ B a} ≤ ∑ a : Fin n, mass (B a))
    (hUnionTimes :
      ∀ _a : Fin n,
        ∀ B : {T : Finset (Fin K) // T.card = r} → Set Ω,
          mass {ω | ∃ T : {T : Finset (Fin K) // T.card = r}, ω ∈ B T} ≤
            ∑ T : {T : Finset (Fin K) // T.card = r}, mass (B T))
    (hcylinder :
      ∀ (a : Fin n) (T : Finset (Fin K)), T.card = r →
        mass {ω | PrefixAgentSelectedOn (A ω) a T} ≤
          ((2 : ENNReal) * (n : ENNReal)⁻¹) ^ r) :
    mass {ω | D ω} ≤
      (n : ENNReal) * (Nat.choose K r : ENNReal) *
        (((2 : ENNReal) * (n : ENNReal)⁻¹) ^ r) := by
  have hsub : {ω | D ω} ⊆ {ω | PrefixHighLoad (A ω) r} := by
    intro ω hω
    exact hD_high ω hω
  exact (hmono _ _ hsub).trans
    (prefix_high_load_mass_le_union_choose
      (n := n) (K := K) (r := r) mass A hmono hUnionAgents hUnionTimes
      hcylinder)

end SSEM
