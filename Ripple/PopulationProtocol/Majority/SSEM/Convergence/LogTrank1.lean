import Ripple.PopulationProtocol.Majority.SSEM.Convergence.LogRegimeFinal
import Ripple.PopulationProtocol.Majority.SSEM.UpperBound.Time.GenericTrank

namespace SSEM

attribute [local instance] Classical.propDecidable

-- `ranking_goal_of_runPairs_RankingEndpoint_trank` is provided by
-- `LogRegimeFinal` (over the section variable `τ`) and imported above; the
-- earlier duplicate here has been removed to avoid a re-declaration clash.

/-- Trank-parametric version of the strong entry seed-prefix obligation. -/
def MedCorrectLiveProducesStrongSeedOrProgressTrank
    [Inhabited (Fin n × Fin n)]
    (trank Rmax Emax Dmax : ℕ) (hn : 0 < n) : Prop :=
  ∀ D : Config (AgentState n) Opinion n,
    InSswap D →
    (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
      1 ≤ (D μ).1.timer) →
    0 < wrongAnswerCount D →
    (∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
      (D μ).1.answer = majorityAnswer D) →
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs
        (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) D L
      CorrectResetSeedStrong Rmax C' ∨
        (InSswap C' ∧ ResAns (majorityAnswer C') C')

/-- Trank-parametric version of the strong reset-leaf seed-prefix obligation. -/
def ReservoirCaseProducesStrongSeedOrProgressTrank
    [Inhabited (Fin n × Fin n)]
    (trank Rmax Emax Dmax : ℕ) (hn : 0 < n) : Prop :=
  ∀ D : Config (AgentState n) Opinion n,
    InSswap D →
    ResAns (majorityAnswer D) D →
    0 < phiCount D →
    ((∀ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n →
        (D μ).1.answer = majorityAnswer D) ∨
     (∃ μ : Fin n, (D μ).1.rank.val + 1 = ceilHalf n ∧
        (D μ).1.timer = 0)) →
    ∃ L : List (Fin n × Fin n),
      let C' := runPairs
        (protocolPEM n trank Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) D L
      CorrectResetSeedStrong Rmax C' ∨
        (InSswap C' ∧ ResAns (majorityAnswer C') C' ∧
          phiCount C' < phiCount D)

/-!
### Correctness at `trank = 1`

The entire log-regime convergence chain in `LogTreeReset`,
`LogRegimeConvergence` and `LogRegimeFinal` is parametric in a free section
variable `τ : ℕ` (the timer-rank used by `transitionPEM`).  Nothing in the
reset/recruit/drain/ranking machinery couples `τ` to `Rmax`: the coupling that
historically appeared in the statements (`protocolPEM n Rmax Rmax …`) was pure
interface hardcoding.  Consequently the assembled correctness keystone
`P_EM_solves_SSEM_log` holds for *every* `τ`, and in particular at `τ = 1`,
which is the exact protocol instance carried by the complexity keystone
`PEM_expectedParallelTime_On_faithful_log` (`PEMProtocol n 1`).

The following theorem re-lands `P_EM_solves_SSEM_log` at `τ = 1` with no extra
hypotheses, so the correctness and complexity results now speak about the same
`protocolPEM n 1 Rmax (rankDeltaOSSR Rmax Emax Dmax hn)` instance. -/
theorem P_EM_solves_SSEM_log_trank1
    [Inhabited (Fin n × Fin n)]
    {Rmax Emax Dmax : ℕ} {hn : 0 < n}
    (hn4 : 4 ≤ n)
    (hDmax1 : 1 < Dmax)
    (hRlog : 2 * Nat.clog 2 n + 2 ≤ Rmax) :
    SolvesSSEM (protocolPEM n 1 Rmax (rankDeltaOSSR Rmax Emax Dmax hn)) n :=
  P_EM_solves_SSEM_log (τ := 1)
    (Rmax := Rmax) (Emax := Emax) (Dmax := Dmax) (hn := hn)
    hn4 hDmax1 hRlog

end SSEM
