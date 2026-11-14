-- Ripple/PopulationProtocol/ExactMajority/Probability/LateSharpInitialPotential.lean
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSeedPotential
import Ripple.PopulationProtocol.ExactMajority.Probability.Phase6PhiPotential
import Ripple.PopulationProtocol.ExactMajority.Probability.LateSamplingStrongSeedReceipt

noncomputable section

namespace Ripple.PopulationProtocol.ExactMajority
namespace LateSharpInitialPotential

open TimeTheorem StageEventSpec
open LateStrengthening LateSamplingStrongSeedReceipt

variable {n : ℕ}

private def largeAtom {L K : ℕ}
    (ell : ℕ) (a : AgentState L K) : ℕ :=
  if a.role = .main then
    match a.bias with
    | .zero => 0
    | .dyadic _ j =>
        if j.val < ell then 128 ^ (ell - j.val - 1) else 0
  else 0

private def shallowAtom {L K : ℕ}
    (ell : ℕ) (a : AgentState L K) : ℕ :=
  if a.role = .main then
    match a.bias with
    | .zero => 0
    | .dyadic _ j =>
        if j.val < ell then 4 ^ (ell - j.val - 1) else 0
  else 0

private theorem largeAtom_le_pow_mul_phiAtom
    (ell q : ℕ) (c : InputCfg n)
    (hcut : noIndexBelow (ell - q) c)
    (a : AgentState (PhaseThreeModel.Numeric.hourIndex n) 256)
    (ha : a ∈ c) :
    largeAtom ell a ≤
      32 ^ q * Phase6PhiPotential.agentPhiW ell a := by
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero =>
        simp [largeAtom, Phase6PhiPotential.agentPhiW,
          Phase6PhiPotential.biasPhiW, hm, hb]
    | dyadic tau j =>
        by_cases hj : j.val < ell
        · have hlo : ell - q ≤ j.val := hcut a ha hm tau j hb
          have hexp : ell - j.val - 1 ≤ q := by omega
          have hreorder : ell - 1 - j.val = ell - j.val - 1 := by omega
          have hpow : 32 ^ (ell - j.val - 1) ≤ 32 ^ q :=
            pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 32) hexp
          simp only [largeAtom, Phase6PhiPotential.agentPhiW,
            Phase6PhiPotential.biasPhiW, if_pos hm, hb, if_pos hj]
          rw [hreorder]
          calc
            128 ^ (ell - j.val - 1) =
                (32 * 4) ^ (ell - j.val - 1) := by norm_num
            _ = 32 ^ (ell - j.val - 1) *
                4 ^ (ell - j.val - 1) := by rw [mul_pow]
            _ ≤ 32 ^ q * 4 ^ (ell - j.val - 1) :=
              Nat.mul_le_mul_right _ hpow
        · simp [largeAtom, Phase6PhiPotential.agentPhiW,
            Phase6PhiPotential.biasPhiW, hm, hb, hj]
  · simp [largeAtom, Phase6PhiPotential.agentPhiW, hm]

private theorem sum_largeAtom_le
    (ell q : ℕ) (c : InputCfg n)
    (hcut : noIndexBelow (ell - q) c) :
    (c.map (largeAtom ell)).sum ≤
      32 ^ q *
        (c.map (fun a => Phase6PhiPotential.agentPhiW ell a)).sum := by
  revert hcut
  induction c using Multiset.induction_on with
  | empty =>
      intro _
      simp
  | cons a c ih =>
      intro hcut
      have hhead := largeAtom_le_pow_mul_phiAtom
        (n := n) ell q (a ::ₘ c) hcut a (Multiset.mem_cons_self a c)
      have hcutTail : noIndexBelow (ell - q) c := by
        intro b hb hm tau j hbias
        exact hcut b (Multiset.mem_cons_of_mem hb) hm tau j hbias
      have htail := ih hcutTail
      simpa only [Multiset.map_cons, Multiset.sum_cons, Nat.mul_add] using
        Nat.add_le_add hhead htail

/-- Lemma 10's deterministic factorization:
`128^d = 32^d * 4^d`, and the cutoff gives `d ≤ q`. -/
theorem shallowLargePotential_le_pow_mul_phiMass
    (ell q : ℕ) (c : InputCfg n)
    (hcut : noIndexBelow (ell - q) c) :
    LatePotential.shallowLargePotential ell c ≤
      32 ^ q * Phase6PhiPotential.phiMass ell c := by
  have hL : LatePotential.shallowLargePotential ell c =
      (c.map (largeAtom ell)).sum := by
    unfold LatePotential.shallowLargePotential
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp only [largeAtom]
    by_cases hm : a.role = .main
    · rcases hb : a.bias with _ | ⟨s, j⟩ <;> simp [hm, hb]
    · simp [hm]
  have hP : Phase6PhiPotential.phiMass ell c =
      (c.map (fun a => Phase6PhiPotential.agentPhiW ell a)).sum := rfl
  rw [hL, hP]
  exact sum_largeAtom_le ell q c hcut

private theorem agentPhiW_eq_shallowAtom
    {L K : ℕ} (ell : ℕ) (a : AgentState L K) :
    Phase6PhiPotential.agentPhiW ell a = shallowAtom ell a := by
  by_cases hm : a.role = .main
  · cases hb : a.bias with
    | zero =>
        simp [Phase6PhiPotential.agentPhiW,
          Phase6PhiPotential.biasPhiW, shallowAtom, hm, hb]
    | dyadic tau j =>
        by_cases hj : j.val < ell
        · have hreorder : ell - 1 - j.val = ell - j.val - 1 := by omega
          simp [Phase6PhiPotential.agentPhiW,
            Phase6PhiPotential.biasPhiW, shallowAtom,
            hm, hb, hj, hreorder]
        · simp [Phase6PhiPotential.agentPhiW,
            Phase6PhiPotential.biasPhiW, shallowAtom, hm, hb, hj]
  · simp [Phase6PhiPotential.agentPhiW, shallowAtom, hm]

/-- Exact name relation for the paper's `φ_ell`. -/
theorem phiMass_eq_shallowPotential
    (ell : ℕ) (c : InputCfg n) :
    Phase6PhiPotential.phiMass ell c = shallowPotential ell c := by
  have hP : Phase6PhiPotential.phiMass ell c =
      (c.map (fun a => Phase6PhiPotential.agentPhiW ell a)).sum := rfl
  have hS : shallowPotential ell c = (c.map (shallowAtom ell)).sum := by
    unfold shallowPotential
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp only [shallowAtom]
    by_cases hm : a.role = .main
    · rcases hb : a.bias with _ | ⟨s, j⟩ <;> simp [hm, hb]
    · simp [hm]
  rw [hP, hS]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro a _
  exact agentPhiW_eq_shallowAtom ell a

/-- The exact `.001 M` bound is already a `SmallReadout` field. -/
theorem seed_phiMass_scaled_le
    {init c : InputCfg n} {M ell : ℕ} {sigma : Sign}
    (h : LateSeedReadout init M ell sigma c) :
    1000 * Phase6PhiPotential.phiMass ell c ≤ M := by
  rw [phiMass_eq_shallowPotential]
  exact h.toSmallReadout.potential

/-- Equation (46) before replacing `M` by `n`. -/
theorem seed_largePotential_scaled_le_main
    {init c : InputCfg n} {M ell : ℕ} {sigma : Sign}
    (h : LateSeedReadout init M ell sigma c) :
    1000 * LatePotential.shallowLargePotential ell c ≤
      32 ^ terminalCutoff n * M := by
  have hlarge := shallowLargePotential_le_pow_mul_phiMass
    ell (terminalCutoff n) c h.oldIndexCutoff
  have hphi := seed_phiMass_scaled_le h
  calc
    1000 * LatePotential.shallowLargePotential ell c
        ≤ 1000 *
          (32 ^ terminalCutoff n * Phase6PhiPotential.phiMass ell c) :=
      Nat.mul_le_mul_left 1000 hlarge
    _ = 32 ^ terminalCutoff n *
          (1000 * Phase6PhiPotential.phiMass ell c) := by ring
    _ ≤ 32 ^ terminalCutoff n * M :=
      Nat.mul_le_mul_left (32 ^ terminalCutoff n) hphi

/-- The role split gives `M ≤ n`; this is the paper's `.001 n` form. -/
theorem seed_largePotential_scaled_le_population
    {init c : InputCfg n} {M C R ell : ℕ} {sigma : Sign}
    (h : LateSeedReadout init M ell sigma c)
    (hdensity : StrongSeedDensity n M C R) :
    1000 * LatePotential.shallowLargePotential ell c ≤
      32 ^ terminalCutoff n * n := by
  have hupper := hdensity.mains_upper
  have hmain : M ≤ n := by omega
  exact (seed_largePotential_scaled_le_main h).trans
    (Nat.mul_le_mul_left (32 ^ terminalCutoff n) hmain)

/-- The actually available density constant is stronger:
`φ_ell ≤ 13 n / 25000 = .00052 n`. -/
theorem seed_largePotential_scaled_le_strong
    {init c : InputCfg n} {M C R ell : ℕ} {sigma : Sign}
    (h : LateSeedReadout init M ell sigma c)
    (hdensity : StrongSeedDensity n M C R) :
    25000 * LatePotential.shallowLargePotential ell c ≤
      13 * 32 ^ terminalCutoff n * n := by
  have hmain := seed_largePotential_scaled_le_main h
  calc
    25000 * LatePotential.shallowLargePotential ell c
        = 25 * (1000 * LatePotential.shallowLargePotential ell c) := by ring
    _ ≤ 25 * (32 ^ terminalCutoff n * M) :=
      Nat.mul_le_mul_left 25 hmain
    _ = 32 ^ terminalCutoff n * (25 * M) := by ring
    _ ≤ 32 ^ terminalCutoff n * (13 * n) :=
      Nat.mul_le_mul_left (32 ^ terminalCutoff n) hdensity.mains_upper
    _ = 13 * 32 ^ terminalCutoff n * n := by ring

end LateSharpInitialPotential
end Ripple.PopulationProtocol.ExactMajority

end
