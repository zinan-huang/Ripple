import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.DisruptionTail
import Ripple.PopulationProtocol.Majority.SSEM.Protocol.RankDelta

namespace SSEM

open scoped BigOperators ENNReal

variable {n : ℕ}

/-!
# No-wake delay-drain certificates

This is the delay-timer analogue of `DisruptionTail.lean`.

The invariant is:

  for every dormant agent still in role `Resetting` with `resetcount = 0`,
    d ≤ delaytimer + selectionCount γ a t.

When a selected dormant resetting agent decrements its delaytimer by one,
the selected-count term increases by one, so the sum is preserved.  When
a resetting agent wakes, the pre-wake timer must be at most `1`, and the
certificate then forces high scheduler load on that agent.

Protocol-specific boundary:

To instantiate `SomeAgentAwakeStepWitness` for the concrete `rankDeltaOSSR`
step along an all-resetting prefix, prove separately that the first awake
agent must be one of the selected endpoints and that its pre-step delaytimer
is at most `1`.  This is exactly where the `processAgent` side conditions
belong:

* the endpoint is in the dormant `rc = 0` branch;
* along an all-resetting prefix, its partner is resetting, so
  `partnerResetting = true`;
* hence the `!partnerResetting` wake branch cannot fire, and leaving
  `Resetting` is caused by `delaytimer - 1 = 0`, i.e. pre-delaytimer ≤ 1.
-/

/-- Some agent has left the `Resetting` role. -/
def SomeAgentAwake
    (C : Config (AgentState n) Opinion n) : Prop :=
  ∃ a : Fin n, (C a).1.role ≠ .Resetting

/-- All agents are still in the `Resetting` role. -/
def AllAgentsResetting
    (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ a : Fin n, (C a).1.role = .Resetting

theorem not_someAgentAwake_iff_allAgentsResetting
    (C : Config (AgentState n) Opinion n) :
    ¬ SomeAgentAwake C ↔ AllAgentsResetting C := by
  constructor
  · intro h a
    by_cases ha : (C a).1.role = .Resetting
    · exact ha
    · exact False.elim (h ⟨a, ha⟩)
  · intro h hAwake
    rcases hAwake with ⟨a, ha⟩
    exact ha (h a)

/-- Dormant resetting agents are exactly the agents whose delay timer can be
decremented by `processAgent`. -/
def DormantResetting
    (C : Config (AgentState n) Opinion n) (a : Fin n) : Prop :=
  (C a).1.role = .Resetting ∧ (C a).1.resetcount = 0

/-- The wake-load certificate at a concrete configuration/time.

For every dormant resetting agent, the residual delaytimer plus the number of
scheduler selections already charged to that agent is at least the budget `d`.
Positive-resetcount resetting agents are not charged: `processAgent` does not
decrement their delaytimer, and when they become dormant they are refreshed to
`Dmax`. -/
def WakeLoadCertificateAt
    (d : ℕ) (γ : DetScheduler n) (t : ℕ)
    (C : Config (AgentState n) Opinion n) : Prop :=
  ∀ a : Fin n,
    DormantResetting C a →
      d ≤ (C a).1.delaytimer + selectionCount γ a t

/-- A one-step abstract condition sufficient to propagate the wake-load
certificate.

Each post-step dormant resetting agent is either assigned enough fresh delay
budget, or came from a pre-step dormant resetting agent whose delaytimer dropped
by at most one if that agent was selected at this step.

This is the exact place where the concrete `processAgent` proof should feed
in the `rc = 0` and partner-resetting facts. -/
def WakeDelaytimerStepOK
    (d : ℕ) (γ : DetScheduler n) (t : ℕ)
    (C C' : Config (AgentState n) Opinion n) : Prop :=
  ∀ a : Fin n,
    DormantResetting C' a →
      d ≤ (C' a).1.delaytimer ∨
        (DormantResetting C a ∧
          (C a).1.delaytimer ≤
            (C' a).1.delaytimer +
              (if selectedAt γ a t then 1 else 0))

/-- One-step propagation of the wake-load certificate.

This is the delaytimer analogue of `ErrorLoadCertificateAt.step`. -/
theorem WakeLoadCertificateAt.step
    {d : ℕ} {γ : DetScheduler n} {t : ℕ}
    {C C' : Config (AgentState n) Opinion n}
    (hcert : WakeLoadCertificateAt d γ t C)
    (hstep : WakeDelaytimerStepOK d γ t C C') :
    WakeLoadCertificateAt d γ (t + 1) C' := by
  classical
  intro a haDorm
  have hsucc := selectionCount_succ γ a t
  rcases hstep a haDorm with hfresh | hprev
  · rw [hsucc]
    omega
  · rcases hprev with ⟨haResOld, hdrop⟩
    have hold := hcert a haResOld
    rw [hsucc]
    by_cases hsel : selectedAt γ a t <;>
      simp [hsel] at hdrop ⊢ <;>
      omega

/-- Initial configurations whose existing `Resetting` agents already have a
fresh enough delaytimer satisfy the time-0 wake-load certificate. -/
theorem initial_wake_load_certificate
    {d : ℕ} {γ : DetScheduler n}
    {C : Config (AgentState n) Opinion n}
    (hinit : ∀ a : Fin n,
      DormantResetting C a → d ≤ (C a).1.delaytimer) :
    WakeLoadCertificateAt d γ 0 C := by
  intro a ha
  simpa [selectionCount] using hinit a ha

/-- Common fresh-start specialization for dormant resetting agents. -/
theorem initial_wake_load_certificate_eq
    {d : ℕ} {γ : DetScheduler n}
    {C : Config (AgentState n) Opinion n}
    (hinit : ∀ a : Fin n,
      DormantResetting C a → (C a).1.delaytimer = d) :
    WakeLoadCertificateAt d γ 0 C := by
  apply initial_wake_load_certificate
  intro a ha
  rw [hinit a ha]

/-- Structural wake predicate used by the load certificate: before step `t`,
a selected `Resetting` endpoint has delaytimer at most `1`, so the dormant
delay decrement can wake it during this interaction. -/
def WakeTimeoutSelectedAt
    (γ : DetScheduler n) (t : ℕ)
    (C : Config (AgentState n) Opinion n) (a : Fin n) : Prop :=
  selectedAt γ a t ∧
    DormantResetting C a ∧
      (C a).1.delaytimer ≤ 1

/-- Certified wake before `K`, packaged with the load certificate at the
pre-wake time.  This is the direct analogue of `DisruptionBeforeK`. -/
def CertifiedWakeBeforeK
    (P : Protocol (AgentState n) Opinion Output)
    (d : ℕ) (C₀ : Config (AgentState n) Opinion n)
    (γ : DetScheduler n) (K : ℕ) : Prop :=
  ∃ t : ℕ, t < K ∧
    ∃ a : Fin n,
      WakeLoadCertificateAt d γ t (execution P C₀ γ t) ∧
        WakeTimeoutSelectedAt γ t (execution P C₀ γ t) a

/-- Certified load extraction: if a wake timeout happens before `K`, then
some agent was selected at least `d` times in the first `K` steps. -/
theorem certified_wake_before_K_implies_high_load
    {P : Protocol (AgentState n) Opinion Output}
    {d : ℕ} {C₀ : Config (AgentState n) Opinion n}
    {γ : DetScheduler n} {K : ℕ}
    (hW : CertifiedWakeBeforeK P d C₀ γ K) :
    ∃ a : Fin n, d ≤ selectionCount γ a K := by
  rcases hW with ⟨t, htK, a, hcert, htimeout⟩
  rcases htimeout with ⟨hsel, haRes, haDelay⟩
  refine ⟨a, ?_⟩
  have hcertA := hcert a haRes
  have hsucc :
      selectionCount γ a (t + 1) = selectionCount γ a t + 1 :=
    selectionCount_succ_of_selected γ a hsel
  have htoSucc :
      (execution P C₀ γ t a).1.delaytimer + selectionCount γ a t ≤
        selectionCount γ a (t + 1) := by
    rw [hsucc]
    omega
  have hmono :
      selectionCount γ a (t + 1) ≤ selectionCount γ a K :=
    selectionCount_mono γ a (by omega)
  exact hcertA.trans (htoSucc.trans hmono)

/-- The raw event that `SomeAgentAwake` first becomes true during one of the
first `K` interactions.  The wake is observed at time `t+1`, with pre-state
time `t`. -/
def SomeAgentAwakeBeforeK
    (P : Protocol (AgentState n) Opinion Output)
    (C₀ : Config (AgentState n) Opinion n)
    (γ : DetScheduler n) (K : ℕ) : Prop :=
  ∃ t : ℕ, t < K ∧
    ¬ SomeAgentAwake (execution P C₀ γ t) ∧
      SomeAgentAwake (execution P C₀ γ (t + 1))

/-- Protocol-specific witness obligation for turning a first `SomeAgentAwake`
transition into the selected-endpoint timeout fact needed by the certificate.

For the concrete wake/drain proof, instantiate this using `rankDeltaOSSR` /
`processAgent` plus the all-resetting-prefix fact. -/
def SomeAgentAwakeStepWitness
    (γ : DetScheduler n) (t : ℕ)
    (C C' : Config (AgentState n) Opinion n) : Prop :=
  ¬ SomeAgentAwake C →
    SomeAgentAwake C' →
      ∃ a : Fin n, WakeTimeoutSelectedAt γ t C a

/-- Main no-wake certificate lemma in raw `SomeAgentAwake` form.

Assumptions:
* `hWake` says `SomeAgentAwake` is hit within the first `K` interactions;
* `hcert` supplies the wake-load certificate at every pre-wake time;
* `hwitness` is the protocol-specific fact that a first wake from an
  all-resetting prefix must come from a selected endpoint with delaytimer ≤ 1.

Conclusion: some agent has scheduler load at least `Dmax` in the length-`K`
prefix. -/
theorem wake_before_K_implies_high_load
    {P : Protocol (AgentState n) Opinion Output}
    {d : ℕ} {C₀ : Config (AgentState n) Opinion n}
    {γ : DetScheduler n} {K : ℕ}
    (hWake : SomeAgentAwakeBeforeK P C₀ γ K)
    (hcert :
      ∀ t : ℕ, t < K →
        WakeLoadCertificateAt d γ t (execution P C₀ γ t))
    (hwitness :
      ∀ t : ℕ, t < K →
        SomeAgentAwakeStepWitness γ t
          (execution P C₀ γ t) (execution P C₀ γ (t + 1))) :
    ∃ a : Fin n, d ≤ selectionCount γ a K := by
  rcases hWake with ⟨t, htK, hnotAwake, hAwakeNext⟩
  rcases hwitness t htK hnotAwake hAwakeNext with ⟨a, htimeout⟩
  rcases htimeout with ⟨hsel, haRes, haDelay⟩
  refine ⟨a, ?_⟩
  have hcertA := hcert t htK a haRes
  have hsucc :
      selectionCount γ a (t + 1) = selectionCount γ a t + 1 :=
    selectionCount_succ_of_selected γ a hsel
  have htoSucc :
      (execution P C₀ γ t a).1.delaytimer + selectionCount γ a t ≤
        selectionCount γ a (t + 1) := by
    rw [hsucc]
    omega
  have hmono :
      selectionCount γ a (t + 1) ≤ selectionCount γ a K :=
    selectionCount_mono γ a (by omega)
  exact hcertA.trans (htoSucc.trans hmono)

end SSEM
