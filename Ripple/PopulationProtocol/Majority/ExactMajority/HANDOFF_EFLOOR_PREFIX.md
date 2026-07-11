# HANDOFF: εfloor MGF — post-gated floor prefix (family2 letter, task 6d41629e, 2026-06-10)

Source: ChatGPT Pro (family2, Ripple connector). Delivered 20,926 B via bridge after MBP reload. Verbatim answer below.

---

The file already has the exact floor-consuming rate: phase0_mcrCount_decrease_prob_floor packages the combined MCR×MCR plus MCR×assignable mass into mcrCount * a₀ /(n(n−1)), and MilestonePhaseOn is present to carry a side invariant/floor through Janson. The remaining problem is exactly proving the floor side predicate with a prefix-sum bound, not rebuilding the Stage-1 milestone machinery.

Verdict: do not try to prove

∑ τ<t, (K^τ) c₀ {c | assignableCount c < a₀} ≤ n⁻²


from the all-MCR start. That statement is false as written: at τ = 0, pool = 0, so the sum already contains mass 1; and after Stage 1 has already succeeded, Rule 4 may later drain the CR side, so an ungated floor event after Post is irrelevant but still charged. The honest target is the warm-up-shifted, post-gated floor residual:

∑ τ ∈ Finset.range t,
  (K ^ (T₀ + τ)) c₀
    {c | assignableCount c < a₀ ∧ ¬ roleSplitGoodMile n hn2 c}
  ≤ εfloor n


or equivalently use a gate

floorOrDoneGate n a₀ hn2 :=
  floorGate n a₀ ∪ {c | roleSplitGoodMile n hn2 c}


so “floor failure after success” is not counted.

This is the one design change I would make to the current _final form. The existing phase0_stage1_whp_final specializes S := floorGate n a₀, so its residual is the full floorGateᶜ prefix, not post-gated; the theorem currently ends with

((t : ℝ≥0∞) * q +
  ∑ τ ∈ Finset.range t, ((NonuniformMajority L K).transitionKernel ^ τ) c₀
    (floorGate n a₀)ᶜ)


which is structurally correct as an upper bound, but too crude for the desired n^{-2} floor residual. 

RoleSplitConcentration

1. Honest region decomposition

The key current code is already right: floorGate is exactly the gate consumed by the floor-to-rate bridge:

def floorGate (n a₀ : ℕ) : Set (Config (AgentState L K)) :=
  {c | Multiset.card c = n ∧ a₀ ≤ assignableCount c ∧
    (∀ a ∈ c, a.role = .mcr → a.phase.val = 0)}


and the bridge is

theorem phase0_mcrCount_decrease_prob_floor ...
  (h_floor : a₀ ≤ assignableCount c) :
  ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
      {c' | mcrCount c' < mcrCount c}
    ≥ ofReal ((mcrCount c * a₀ : ℕ) / (n * (n - 1) : ℝ))


with floorRate n a₀ M = M * a₀ / (n * (n - 1)). 

RoleSplitConcentration

 

RoleSplitConcentration

 

RoleSplitConcentration

For the floor residual itself, split the process into these regions.

Region W: warm-up from pool = 0

Use a buffer level, not the final floor:

A₀ := a₀
A₁ := 2 * a₀


On

u = mcrCount c ≥ n / 2
pool = assignableCount c < A₁


R1 births dominate. R1 contributes +2 to pool, and Rule 4 contributes -2, with drain rate bounded by the unassigned-CR count squared, hence by pool^2. So for Φ(c) = exp (-s * pool c),

E[Φ(next) | c] / Φ(c)
≤ 1
  - pBirth(c) * (1 - exp(-2s))
  + pDeath(c) * (exp(2s) - 1)


where

pBirth(c) ≥ u(u-1)/(n(n-1)),
pDeath(c) ≤ crFresh(c)(crFresh(c)-1)/(n(n-1)) ≤ pool(c)^2/(n(n-1)).


On u ≥ n/2, pool ≤ 2a₀, and a₀ = n/10, one has roughly

pBirth ≥ 1/4,
pDeath ≤ 1/25,


so choose a fixed small s > 0 and get a contraction

∫⁻ c', expNegPool s c' ∂K c ≤ rWarm * expNegPool s c


with rWarm < 1.

This is the correct place to use WindowConcentration.windowDrift_tail: it is exactly the abstract “potential contracts on a window, so the multi-step tail is small” builder. Its hypothesis shape is

(hdrift : ∀ c, Q c →
  ∫⁻ c', Φ c' ∂(P.transitionKernel c) ≤ r * Φ c)


and the conclusion bounds the bad mass by r^t * Φ(c₀) / θ. 

WindowConcentration

Region M: main floor-maintenance while u ≥ uMin

Once pool ≥ 2a₀, the event you need to suppress is a drop back below a₀ before either Stage 1 succeeds or the low-u checkpoint is reached. Use the deficit potential

Φfloor c := ENNReal.ofReal (Real.exp (s * ((2*a₀ : ℝ) - assignableCount c)))


or equivalently exp(-s * pool) with threshold conversion. The drift is favorable only in the band

a₀ ≤ pool c ≤ 2*a₀
uMin ≤ mcrCount c


because the crude death bound is ≤ (2a₀)^2 / n^2, while R1 births are ≥ uMin^2 / n^2. Thus choose, for example,

uMin := 3 * a₀        -- or 4*a₀ for easier constants


so

uMin² > (2a₀)²


with slack for the exp(±2s) factors.

The supermartingale is again

E[exp(-s pool(next)) | c] ≤ rMid * exp(-s pool(c))


on the gated band. The gate should not be “all time”; it should be stopped at

roleSplitGoodMile n hn2 c ∨ mcrCount c < uMin ∨ assignableCount c < a₀


so the theorem proves “floor does not fail before the low-u checkpoint or success.”

Region L: low u < uMin

Do not try to prove the same exp(-s * pool) drift from R1 births here. It is genuinely false: R1 birth rate is now too small. Resolve the apparent circularity by making the residual post-gated and either:

add a low-u checkpoint theorem, started from the buffered event, proving completion before floor failure; or

use a stronger checkpoint predicate that includes a durable fresh-main/reservoir condition.

The minimal version I would formalize first is the checkpoint theorem:

def LowStartGood (n a₀ uMin : ℕ) (c : Config (AgentState L K)) : Prop :=
  cardPhaseShell n c ∧
  mcrCount c ≤ uMin ∧
  2 * a₀ ≤ assignableCount c


and prove a separate bound

((K ^ tLate) c) {c' | assignableCount c' < a₀ ∧ ¬ roleSplitGoodMile n hn2 c'}
  ≤ εlate n


from LowStartGood. This is the only genuinely new probabilistic piece beyond the warm-up/floor-maintenance MGF.

2. Warm-up theorem shape

The current phase0_stage1_whp_final cannot be started directly from Phase0Initial with linear a₀, because it requires

(hc₀ : c₀ ∈ floorGate n a₀)


but Phase0Initial has pool = 0. 

RoleSplitConcentration

So add a checkpoint theorem, not a direct replacement:

def Phase0WarmGood (n a₀ uMin : ℕ) (c : Config (AgentState L K)) : Prop :=
  cardPhaseShell (L := L) (K := K) n c ∧
  uMin ≤ ExactMajority.mcrCount (L := L) (K := K) c ∧
  2 * a₀ ≤ assignableCount (L := L) (K := K) c

theorem phase0_floor_warmup_whp
    (n a₀ uMin T₀ : ℕ) (εwarm : ℝ≥0∞)
    {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀)
    -- arithmetic constants, e.g. a₀ = n/10, uMin = 3*a₀, T₀ = C*n:
    (hwarm_arith : WarmupArithmetic n a₀ uMin T₀ εwarm)
    -- one-step MGF drift on the warm band:
    (hwarm_drift : WarmupPoolDrift (L := L) (K := K) n a₀ uMin) :
    ((NonuniformMajority L K).transitionKernel ^ T₀) c₀
      {c | ¬ Phase0WarmGood (L := L) (K := K) n a₀ uMin c}
      ≤ εwarm


The proof should instantiate WindowConcentration.windowDrift_tail with

Φ c = ENNReal.ofReal (Real.exp (-s * (assignableCount c : ℝ)))
Q c = cardPhaseShell n c ∧ uMin ≤ mcrCount c ∧ assignableCount c < 2*a₀
Post c = 2*a₀ ≤ assignableCount c
θ = ENNReal.ofReal (Real.exp (-s * (2*a₀ : ℝ)))


Use windowDrift_tail, not killK_now, for warm-up, because warm-up is a direct “hit a floor before leaving a window” MGF estimate. killK_now is better for the milestone engine, where alive successors must automatically satisfy the gate; the file already uses that idea via alive_support_gate. 

GatedKillNow

3. Per-region drift lemma statement

Make the drift lemma kernel-local and rate-parametric first, then instantiate with protocol rule lemmas. This keeps the analytic inequality independent of transition bookkeeping.

noncomputable def poolExpNeg (s : ℝ) :
    Config (AgentState L K) → ℝ≥0∞ :=
  fun c => ENNReal.ofReal
    (Real.exp (-s * (assignableCount (L := L) (K := K) c : ℝ)))

structure PoolDriftRegion (n a₀ uMin Ahi : ℕ)
    (c : Config (AgentState L K)) : Prop where
  shell : cardPhaseShell (L := L) (K := K) n c
  u_ge : uMin ≤ ExactMajority.mcrCount (L := L) (K := K) c
  pool_le : assignableCount (L := L) (K := K) c ≤ Ahi

theorem pool_expNeg_one_step_drift
    (n a₀ uMin Ahi : ℕ) (s : ℝ) (r : ℝ≥0∞)
    (hs : 0 < s)
    -- protocol-rate facts:
    (hbirth : ∀ c, PoolDriftRegion (L := L) (K := K) n a₀ uMin Ahi c →
      birthR1Mass (L := L) (K := K) c ≥
        ENNReal.ofReal (((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ)))
    (hdeath : ∀ c, PoolDriftRegion (L := L) (K := K) n a₀ uMin Ahi c →
      r4FreshCRDrainMass (L := L) (K := K) c ≤
        ENNReal.ofReal (((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ)))
    -- scalar inequality saying births dominate deaths after exponential tilting:
    (hfav :
      ScalarPoolFav s n uMin Ahi r) :
    ∀ c, PoolDriftRegion (L := L) (K := K) n a₀ uMin Ahi c →
      ∫⁻ c', poolExpNeg (L := L) (K := K) s c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ r * poolExpNeg (L := L) (K := K) s c


The scalar condition should be exactly the inequality

1 - b*(1-exp(-2s)) + d*(exp(2s)-1) ≤ r


where

b = uMin*(uMin-1)/(n*(n-1)),
d = Ahi*Ahi/(n*(n-1)).


For Ahi = 2*a₀, uMin = 3*a₀ or 4*a₀, small fixed s, this gives r < 1.

4. Assembled floor-prefix theorem

I would add the assembled theorem in a post-gated form and then separately use it to refine phase0_stage1_whp_final.

def floorFailsBeforePost (n a₀ : ℕ) (hn2 : 2 ≤ n)
    (c : Config (AgentState L K)) : Prop :=
  assignableCount (L := L) (K := K) c < a₀ ∧
  ¬ roleSplitGoodMile (L := L) (K := K) n hn2 c

theorem floor_prefix_le
    (n a₀ uMin T₀ t : ℕ) (hn2 : 2 ≤ n)
    (εwarm εmid εlate : ℝ≥0∞)
    {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀)
    -- warm-up reaches buffer:
    (hwarm :
      ((NonuniformMajority L K).transitionKernel ^ T₀) c₀
        {c | ¬ Phase0WarmGood (L := L) (K := K) n a₀ uMin c}
        ≤ εwarm)
    -- from warm-good states, floor failure before low-u/post is small:
    (hmid :
      ∀ c, Phase0WarmGood (L := L) (K := K) n a₀ uMin c →
        ∑ τ ∈ Finset.range t,
          ((NonuniformMajority L K).transitionKernel ^ τ) c
            {c' | assignableCount (L := L) (K := K) c' < a₀ ∧
                  uMin ≤ ExactMajority.mcrCount (L := L) (K := K) c' ∧
                  ¬ roleSplitGoodMile (L := L) (K := K) n hn2 c'}
        ≤ εmid)
    -- low-u checkpoint completion before floor failure:
    (hlate :
      ∀ c, LowStartGood (L := L) (K := K) n a₀ uMin c →
        ∑ τ ∈ Finset.range t,
          ((NonuniformMajority L K).transitionKernel ^ τ) c
            {c' | floorFailsBeforePost (L := L) (K := K) n a₀ hn2 c'}
        ≤ εlate) :
    ∑ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
        {c | floorFailsBeforePost (L := L) (K := K) n a₀ hn2 c}
      ≤ εwarm + εmid + εlate


Then define

def εfloor (n : ℕ) : ℝ≥0∞ :=
  εwarm n + εmid n + εlate n


and set the intended final target as

theorem floor_prefix_le_inv_sq
    ... :
    ∑ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
        {c | floorFailsBeforePost (L := L) (K := K) n a₀ hn2 c}
      ≤ ENNReal.ofReal (((n : ℝ)^2)⁻¹)


after choosing constants so each piece is, say, ≤ 1/(3 n²).

5. How it plugs into existing code

The existing structural chain is already good:

roleSplitKernelMilestone builds the killed-kernel milestone witness with rate floorRate n a₀ (n - i.val). 

RoleSplitConcentration

roleSplitKernelMilestone_pMin_meanTime proves the Janson potential becomes harmonic-sum/logarithmic and independent of a₀, i.e. the floor cancels in pMin * meanTime. 

RoleSplitConcentration

real_bad_le_janson_add_escape is the abstract assembly: real bad mass ≤ Janson tail + escape prefix. 

RoleSplitConcentration

kill_escape_le_prefix_union is the exact generic prefix-union escape lemma. 

GatedEscape

phase0_stage1_whp instantiates the witness and exposes only q plus the prefix residual. 

RoleSplitConcentration

So the minimal edit is not to rebuild Janson or killed kernels. Add only:

def floorOrDoneGate (n a₀ : ℕ) (hn2 : 2 ≤ n) :
    Set (Config (AgentState L K)) :=
  floorGate (L := L) (K := K) n a₀ ∪
    {c | roleSplitGoodMile (L := L) (K := K) n hn2 c}


then a variant of _final whose prefix term is

∑ τ ∈ Finset.range t,
  (K^τ) c₀ {c | assignableCount c < a₀ ∧ ¬ roleSplitGoodMile n hn2 c}


rather than full floorGateᶜ.

That is the honest endpoint: Janson tail + warm-up failure + post-gated floor-prefix failure. The current branch already has the first term and the floor-to-rate bridge; the last remaining Lean work is exactly the MGF proof that the post-gated floor prefix is small.

The clean answer is: do not try to make floorGate n a₀ true from time 0. From the all-MCR start, assignableCount = 0, so an unshifted

∑ τ ∈ Finset.range t, (K ^ τ) c₀ {c | assignableCount c < a₀}


is already at least 1. The correct final residual must either start after a warm-up checkpoint T₀ = Θ(n), or use a regime-dependent floor, for example floor 0 before T₀ and floor a₀ after T₀.

The branch already has the right structural endpoint: phase0_stage1_whp_final bounds Stage-1 bad mass by Janson plus

((t : ℝ≥0∞) * q +
  ∑ τ ∈ Finset.range t, ((NonuniformMajority L K).transitionKernel ^ τ) c₀
    (floorGate (L := L) (K := K) n a₀)ᶜ)


where floorGate is the card/phase shell plus a₀ ≤ assignableCount. 

RoleSplitConcentration

 The new work should only replace that prefix term by a warm-up-shifted floor-prefix theorem.

1. Region decomposition

Let

pool c := assignableCount (L := L) (K := K) c
u c    := ExactMajority.mcrCount (L := L) (K := K) c


Use constants such as

a₀    := n / 10
Ahi   := 2 * a₀
uMin  := 3 * a₀     -- or 4*a₀ if you want easier scalar inequalities
T₀    := C₀ * n


The drift of exp(-s * pool) is favorable only in a band where u is still linear. The one-step scalar inequality is:

E[exp(-s pool')] / exp(-s pool)
≤ 1
  - pBirth * (1 - exp(-2s))
  + pDeath * (exp(2s) - 1).


Here

pBirth ≥ u(u-1)/(n(n-1)),
pDeath ≤ freshCR(freshCR-1)/(n(n-1)) ≤ pool²/(n(n-1)).


So on

pool ≤ Ahi,    u ≥ uMin,


you get favorable drift whenever roughly

uMin² > Ahi².


With Ahi = 2a₀ and uMin = 3a₀, births dominate deaths by a fixed constant factor.

The branch’s existing floor-to-rate bridge is exactly the consumer of this floor:

theorem phase0_mcrCount_decrease_prob_floor
    (c : Config (AgentState L K)) (n a₀ : ℕ)
    ...
    (h_floor : a₀ ≤ assignableCount (L := L) (K := K) c) :
    ((NonuniformMajority L K).stepDistOrSelf c).toMeasure
        {c' | ExactMajority.mcrCount (L := L) (K := K) c' <
          ExactMajority.mcrCount (L := L) (K := K) c} ≥
      ENNReal.ofReal
        (((ExactMajority.mcrCount (L := L) (K := K) c * a₀ : ℕ) : ℝ) /
          (n * (n - 1) : ℝ))


and the rate is already named:

noncomputable def floorRate (n a₀ M : ℕ) : ℝ :=
  ((M * a₀ : ℕ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))


RoleSplitConcentration

So the right split is:

WARM-UP:
  u ≥ n/2, pool < 2a₀.
  Show pool reaches 2a₀ by T₀ = Θ(n) whp.

MAINTENANCE:
  u ≥ uMin, pool ∈ [a₀, 2a₀].
  Show pool does not fall below a₀ before either success or low-u.

LATE:
  u < uMin.
  Do not use exp(-s pool) birth drift here. Instead stop the floor analysis at low-u
  and charge the remaining time to the milestone/Janson completion tail, or use a
  joint “floor-or-done” gate.


The late regime is where a naive proof becomes circular. If u < uMin, R1 births are no longer strong enough. The fix is to stop the floor martingale at

roleSplitGoodMile n hn2 c ∨ u c < uMin ∨ pool c < a₀


and then handle the low-u window by the same milestone progress/Janson tail, not by pool drift.

2. Warm-up shape

From pool = 0, use a checkpoint theorem:

def Phase0WarmGood (n a₀ uMin : ℕ) (c : Config (AgentState L K)) : Prop :=
  cardPhaseShell (L := L) (K := K) n c ∧
  uMin ≤ ExactMajority.mcrCount (L := L) (K := K) c ∧
  2 * a₀ ≤ assignableCount (L := L) (K := K) c


Target:

theorem phase0_floor_warmup_whp
    (n a₀ uMin T₀ : ℕ) (εwarm : ℝ≥0∞)
    {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀)
    (hwarm_drift : WarmupPoolDrift (L := L) (K := K) n a₀ uMin T₀ εwarm) :
    ((NonuniformMajority L K).transitionKernel ^ T₀) c₀
      {c | ¬ Phase0WarmGood (L := L) (K := K) n a₀ uMin c}
      ≤ εwarm


This should plug into WindowConcentration.windowDrift_tail, not into killK_now. The WindowConcentration builder already has exactly the needed form: given a measurable potential Φ, an absorbing/window predicate Q, and a drift

∀ c, Q c →
  ∫⁻ c', Φ c' ∂(P.transitionKernel c) ≤ r * Φ c


it gives a kernel-level tail

(P.transitionKernel ^ t) c₀ {c | ¬ Post c} ≤ r ^ t * Φ c₀ / θ


WindowConcentration

For warm-up, use

Φ c := ENNReal.ofReal
  (Real.exp (-s * (assignableCount (L := L) (K := K) c : ℝ)))

Post c := 2 * a₀ ≤ assignableCount (L := L) (K := K) c
Q c :=
  cardPhaseShell (L := L) (K := K) n c ∧
  n / 2 ≤ ExactMajority.mcrCount (L := L) (K := K) c ∧
  assignableCount (L := L) (K := K) c < 2 * a₀


Then ¬ Post implies Φ ≥ exp(-s * (2a₀)), so Markov’s inequality gives the warm-up tail.

3. Per-region drift lemma

Minimize new machinery by proving a single abstract one-step pool drift lemma whose hypotheses are protocol-rate facts.

noncomputable def poolExpNeg (s : ℝ) :
    Config (AgentState L K) → ℝ≥0∞ :=
  fun c =>
    ENNReal.ofReal
      (Real.exp (-s * (assignableCount (L := L) (K := K) c : ℝ)))

def PoolDriftRegion (n a₀ uMin Ahi : ℕ)
    (c : Config (AgentState L K)) : Prop :=
  cardPhaseShell (L := L) (K := K) n c ∧
  uMin ≤ ExactMajority.mcrCount (L := L) (K := K) c ∧
  assignableCount (L := L) (K := K) c ≤ Ahi


Then:

theorem pool_expNeg_one_step_drift
    (n a₀ uMin Ahi : ℕ) (s : ℝ) (r : ℝ≥0∞)
    (hs : 0 < s)
    (hbirth :
      ∀ c, PoolDriftRegion (L := L) (K := K) n a₀ uMin Ahi c →
        birthR1Mass (L := L) (K := K) c ≥
          ENNReal.ofReal
            (((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ)))
    (hdeath :
      ∀ c, PoolDriftRegion (L := L) (K := K) n a₀ uMin Ahi c →
        r4FreshCRDrainMass (L := L) (K := K) c ≤
          ENNReal.ofReal
            (((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ)))
    (hfav :
      ScalarPoolFav s n uMin Ahi r) :
    ∀ c, PoolDriftRegion (L := L) (K := K) n a₀ uMin Ahi c →
      ∫⁻ c', poolExpNeg (L := L) (K := K) s c'
          ∂((NonuniformMajority L K).transitionKernel c)
        ≤ r * poolExpNeg (L := L) (K := K) s c


ScalarPoolFav should just expand to the real inequality

def ScalarPoolFav (s : ℝ) (n uMin Ahi : ℕ) (r : ℝ≥0∞) : Prop :=
  ENNReal.ofReal
    (1
      - (((uMin * (uMin - 1) : ℕ) : ℝ) / (n * (n - 1) : ℝ)) *
          (1 - Real.exp (-2*s))
      + (((Ahi * Ahi : ℕ) : ℝ) / (n * (n - 1) : ℝ)) *
          (Real.exp (2*s) - 1))
    ≤ r


This is intentionally rate-parametric. The protocol-specific lemmas birthR1Mass and r4FreshCRDrainMass are the only new count-mass facts.

4. Assembled floor prefix

Use a shifted theorem. This is the honest target:

def floorBadAfterWarmup (n a₀ : ℕ) :
    Set (Config (AgentState L K)) :=
  {c | assignableCount (L := L) (K := K) c < a₀}

theorem floor_prefix_le
    (n a₀ uMin T₀ t : ℕ)
    (εwarm εmid εlate : ℝ≥0∞)
    {c₀ : Config (AgentState L K)}
    (hinit : Phase0Initial (L := L) (K := K) n c₀)
    (hwarm :
      ((NonuniformMajority L K).transitionKernel ^ T₀) c₀
        {c | ¬ Phase0WarmGood (L := L) (K := K) n a₀ uMin c}
        ≤ εwarm)
    (hmid :
      ∀ c, Phase0WarmGood (L := L) (K := K) n a₀ uMin c →
        ∑ τ ∈ Finset.range t,
          ((NonuniformMajority L K).transitionKernel ^ τ) c
            {c' | assignableCount (L := L) (K := K) c' < a₀ ∧
                  uMin ≤ ExactMajority.mcrCount (L := L) (K := K) c'}
        ≤ εmid)
    (hlate :
      ∀ c, Phase0WarmGood (L := L) (K := K) n a₀ uMin c →
        ∑ τ ∈ Finset.range t,
          ((NonuniformMajority L K).transitionKernel ^ τ) c
            {c' | assignableCount (L := L) (K := K) c' < a₀ ∧
                  ExactMajority.mcrCount (L := L) (K := K) c' < uMin}
        ≤ εlate) :
    ∑ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
        {c | assignableCount (L := L) (K := K) c < a₀}
      ≤ εwarm + εmid + εlate


Then expose the paper-scale version:

def εfloor (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((n : ℝ) ^ 2)⁻¹)

theorem floor_prefix_le_inv_sq
    ... :
    ∑ τ ∈ Finset.range t,
      ((NonuniformMajority L K).transitionKernel ^ (T₀ + τ)) c₀
        {c | assignableCount (L := L) (K := K) c < a₀}
      ≤ εfloor n


For plugging into the branch, the cleanest path is:

phase0_floor_warmup_whp: use WindowConcentration.windowDrift_tail.

pool_expNeg_one_step_drift: feeds that same window-drift engine for the mid regime.

floor_prefix_le: pure union/checkpoint composition.

Refine phase0_stage1_whp_final by replacing its raw prefix with the shifted floor_prefix_le.

Do not add a new Janson engine. The branch already has roleSplitKernelMilestone, KernelMilestone, killK_now, and real_bad_le_janson_add_escape. The existing witness already proves that the floor-driven Janson potential is logarithmic:

theorem roleSplitKernelMilestone_pMin_meanTime ... :
  (roleSplitKernelMilestone ...).pMin *
    (roleSplitKernelMilestone ...).meanTime =
    ∑ i : Fin (n - 1), (2 : ℝ) / ((n : ℝ) - (i.val : ℝ))


RoleSplitConcentration

So the residual really is only the warm-up-shifted floor prefix. The rest of the branch is already structurally ready.

---

## STATUS — FloorPrefix.lean delivered (2026-06-10, opus line)

New append-only file `Probability/FloorPrefix.lean` (733 lines, namespace
`ExactMajority.FloorPrefix`). Single-file `lake env lean` EXIT_0; every headline
`#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; no sorry / admit / axiom /
native_decide. Three commits (one per stage group) + this doc commit, each pushed to
`origin main` and mirrored to `xiangyazi24/Ripple opus-wip`.

### Per-stage verdict

**Stage 1 — defs + scalar layer: PROVEN.**
- `poolExpNeg`, `PoolDriftRegion`, `ScalarPoolFav` (exactly per §3); `Phase0WarmGood`,
  `LowStartGood`, `floorFailsBeforePost`, `floorOrDoneGate` (§1–§2, §5).
- `scalarPoolFav_core` (STRICT favorability `d(e^{2s}-1) < b(1-e^{-2s})` at `b=9/100`,
  `d=4/100`, `s=1/10`, via `Real.exp_bound'` + `Real.add_one_le_exp`), `scalarPoolFav_lt_one`
  (`r<1`), `scalarPoolFav_instance`.

**Stage 2 — one-step pool drift: analytic core PROVEN; protocol masses NAMED.**
- `pool_expNeg_one_step_drift_abstract` (PROVEN, 0-sorry): the genuinely-new analytic
  content. Splits the one-step successor measure into birth/death/neutral bands (per-step
  pool change in `[-2,+2]`), exponentially tilts, and via `toReal` mass bookkeeping proves
  `∫ poolExpNeg dK ≤ (1 - b(1-e^{-2s}) + d(e^{2s}-1))·poolExpNeg`. Mirrors `ClockRealSeed`'s
  `lintegral_add_compl` split, extended to 3 bands.
- `pool_expNeg_one_step_drift` (PROVEN wrapper, §3 headline) — masses fixed to
  `b = uMin(uMin-1)/(n(n-1))`, `d = Ahi²/(n(n-1))`, favorability via `ScalarPoolFav`.
- `birthR1Mass`, `r4FreshCRDrainMass` (defs = the real-kernel band masses).
- **NAMED hypotheses** (the genuinely-large remaining protocol work — exact statements):
  * `hbirth : ∀ c ∈ PoolDriftRegion, ofReal(uMin(uMin-1)/(n(n-1))) ≤ birthR1Mass c`
    (Rule-1 `MCR,MCR→Main,CR` birth mass; the `+2` model is CONFIRMED by the proven
    per-rule `assignable_rule2_s_stays`/`assignable_rule3_conserved` in RoleSplitConcentration).
  * `hdeath : ∀ c ∈ PoolDriftRegion, r4FreshCRDrainMass c ≤ ofReal(Ahi²/(n(n-1)))`
    (fresh-CR-pair drain mass ≤ pool²/(n(n-1))).
  * `hstep : ∀ c ∈ PoolDriftRegion, ∀ᵐ c', (pool c : ℤ) - 2 ≤ (pool c' : ℤ)` (the ±2
    per-step interaction range — a deterministic support fact).

**Stage 3 — warm-up tail: engine connection PROVEN; warm reach NAMED.**
- `midBand_gated_tail` (PROVEN): the genuine Stage-2 → engine wiring. Instantiates
  `GatedDrift.gated_real_tail_full` at `poolExpNeg`, giving the mid-band kernel tail
  `t·η + rᵗ·Φx/θ` from the one-step drift.
- `phase0_floor_warmup_whp` — warm-up checkpoint with the reach mass as named hypothesis.

**Stage 4 — assembly: PROVEN.**
- `midBandBad`/`lateBandBad` + `floorFailsBeforePost_subset` (pointwise region cover by the
  `u`-trichotomy). `floor_prefix_le` (PROVEN, pure `measure_union_le` + `Finset.sum_le_sum`
  composition): the post-gated floor prefix ≤ `εwarm+εmid+εlate`. `εfloor n := n⁻²`,
  `floor_prefix_le_inv_sq` capstone.

### Blueprint claims that turned out WRONG against the real repo

1. **`s = 1/2` is TOO LARGE.** At `s=1/2` the tilted drift multiplier is `> 1` (not
   contractive). The favorability needs small `s`; `s=1/10` gives `r ≈ 0.993 < 1`. (The
   crude `9/4`-style `exp` bound for `e^{0.2}-1` is also too loose — the tight `exp_bound'`
   value `≈0.222` is required.)

2. **`windowDrift_tail` does NOT apply to the warm-up / mid band.** Its `hQ_abs` hypothesis
   requires the window to be one-step-support closed (absorbing). The warm-up band
   `{pool < 2a₀ ∧ u ≥ uMin}` is NOT absorbing (a Rule-1 birth crosses `2a₀`; conversions
   drop `u`). The honest non-absorbing engine is `GatedDrift.gated_real_tail_full`.

3. **The gated engines require `1 ≤ r`** (the killed potential must dominate the cemetery
   transition). So `gated_real_tail_full` gives the escape form `t·η + rᵗ·Φx/θ`, NOT a
   decaying `rᵗ`. A genuinely-contractive `r<1` floor prefix therefore needs the
   absorbing-window reformulation (stopped/killed gate); this is why `εmid`/`εlate` stay
   named in the assembly rather than discharged by a single contractive engine call.

4. The blueprint's Rule-4 "fresh-CR drain −2" / "R1 +2" mass MODEL is directionally
   correct, but the per-rule `assignableCount` accounting already proven in
   RoleSplitConcentration (the 2026-06-10 paper-faithful fix) shows Rules 2 and 3 are
   pool-CONSERVING (Δ=0), and only Rule 1 contributes `+2` — so the honest birth mass is
   carried entirely by Rule-1 `MCR,MCR` interactions, as encoded in `birthR1Mass`.

### Remaining work (for a follow-up line)

The three named protocol hypotheses (`hbirth`/`hdeath`/`hstep`) and the warm reach are the
genuinely-new count-mass discharges against the real `Phase0Transition` /
`interactionPMF` (mirror `phase0_mcrCount_decrease_prob_oneSided`'s rectangle-mass route).
The `εmid`/`εlate` contractive prefix bound needs the absorbing-window (killed-kernel)
reformulation per finding (3).

---

## STATUS UPDATE — FloorMasses.lean: the three protocol masses DISCHARGED (2026-06-10, opus line)

`Probability/FloorMasses.lean` (734 lines, append-only, namespace `ExactMajority.FloorMasses`)
discharges the three named protocol hypotheses of `FloorPrefix.pool_expNeg_one_step_drift`.
Single-file EXIT_0, every headline axiom-clean (`⊆ [propext, Classical.choice, Quot.sound]`),
0 sorry/admit/axiom/native_decide.  4 commits on `origin main`, mirrored to opus-wip.

- **hstep** (`pool_step_ge_ae`): FULLY DISCHARGED, unconditional (region-free), via
  `HourCouplingV2.countP_stepOrSelf_diff_le_two`.
- **hbirth** (`hbirth_of_freshMcr_floor`): DISCHARGED via the `freshMcrF×ˢfreshMcrF` R1 birth
  rectangle (route = `phase0_mcrCount_decrease_prob_oneSided` mirror).  Honest count is
  `freshMcrCount` (unassigned phase-0 MCR), not `mcrCount`; holds verbatim once
  `uMin ≤ freshMcrCount`.
- **hdeath** (`hdeath_of_block`): infrastructure (`stepDist_toMeasure_eq_preimage` dual +
  `block_pair_prob_le_sq` + `pair_block_sq_le_buffer`) + adapter.  hdeath is NOT verbatim
  true on the region: R4's drop set is the `CR×CR` block (`(crCount/n)²`, total CR count, not
  the pool), and `phaseEpidemicUpdate` is a second drain path.  `hdeath_of_block` consumes the
  containment + `crCount ≤ Ahi` as documented residual facts.
- **wire-up** (`pool_expNeg_one_step_drift_floorMasses`): instantiates the FloorPrefix drift at
  `s = 1/10` with all three masses + the proven `< 1` favorability.

See `DOTY_POST63_CAMPAIGN.md` (εfloor protocol masses section) for the full verdict.

---

## FINDING 3 RESOLVED — the contractive `r<1` killed engine, `Probability/KilledAffineTail.lean` (2026-06-10, 0-sorry axiom-clean)

FloorPrefix finding 3: the gated engines (`gated_real_tail_full`) require `1 ≤ r`, so the mid-band
tail is the NON-decaying escape form `t·η + rᵗΦx/θ` — useless for the genuinely-contractive `r<1`
mid-band (`εmid`/`εlate`).  **The `1 ≤ r` was SPURIOUS** (`GatedGeometricDrift.killK_drift` never
uses it: `killΦ none = 0` makes the dead-branch killed drift `0 ≤ r·0 + b` trivial for any `r ≥ 0`).
The new killed affine engine takes `a ≥ 0` ARBITRARY:

- **`FloorPrefix.midBand_killed_contractive_tail`** — the killed pool-MGF tail
  `(killK_now^t)(some x){θ≤killΦ(poolExpNeg s)} ≤ (rᵗ·poolExpNeg(x) + b∑rⁱ)/θ` at ANY rate `r`
  (in particular `r<1`, where it GENUINELY decays as `rᵗ`).  This is the exact-shape engine lemma
  the mid-band needed; the old engine could not provide it.
- **`midBand_real_contractive_tail`** — the real pool-deficit mass = contractive killed tail +
  escape (`real_le_killed_affine_tail_add_escape` at `poolExpNeg`).

Re-cut `midBand_gated_tail` against `midBand_killed_contractive_tail`: instantiate `Φ := poolExpNeg
s`, `a := r` (the Stage-2 contraction rate, `< 1`), `b := 0` (pool drift is purely multiplicative),
`θ := exp(-s·a₀)`; the killed term decays, and the `εmid` prefix is its aggregate plus the floor-exit
escape bridge.  STATUS: contractive engine lemma DELIVERED 0-sorry axiom-clean; the `εmid`/`εlate`
named-hypothesis discharge is now an instantiation (escape via the deterministic floor-exit bridge),
no longer blocked on `1 ≤ r`.

---

## KilledTailConsumers Deliverables 2 & 3 LANDED (2026-06-10, resumed opus line)

`Probability/KilledTailConsumers.lean` (581 lines, append-only) — predecessor's Deliverable 1
(top-split tail, b94a951d) + this line's Deliverables 2 & 3. Single-file `lake env lean … EXIT 0`;
every headline `#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; 0 sorry/admit/axiom/
native_decide. Two commits (d09a2b74 D2, bd3b8e96 D3).

### Deliverable 3 — εmid FINAL SHAPE (the contractive route, no `1 ≤ r`)

`FloorPrefix.midBand_floorFail_prefix_floorMasses` is the εmid final form:

```
∑ τ ∈ range t, (Kᵗ) c₀ {assignableCount < a₀}
  ≤ ∑ τ ∈ range t,
      ( (floorMassesRate n uMin Ahi ^ τ * poolExpNeg (1/10) c₀ + 0·∑ rⁱ)
          / ofReal(exp(-(1/10)·a₀))
        + (killK_now K (poolDriftRegionSet n uMin Ahi) ^ τ)(some c₀){none} )
```

The leading term DECAYS as `rᵗ` (`r = floorMassesRate < 1`, the proven favorability multiplier),
which the old `gated_real_tail_full` route (`midBand_gated_tail`, `1 ≤ r`) could not give. Wiring:
`FloorMasses.pool_expNeg_one_step_drift_floorMasses` (s=1/10, immigration b=0) → the affine drift
on `poolDriftRegionSet n uMin Ahi` → `KilledAffineTail.midBand_real_contractive_tail` per step
(threshold link `{pool<a₀} ⊆ {ofReal(exp(-s·a₀)) ≤ poolExpNeg s}` =
`floorFail_subset_poolExpNeg_thresh`) → `Finset.sum_le_sum`. The FloorMasses region hypotheses stay
EXPLICIT named args: `hfresh : ∀ c ∈ region, uMin ≤ freshMcrCount c` (Rule-1 birth feeder) and the
drain-block `Sblk`/`hSstep`/`hblock`/`hAn` (the hdeath containment) — exactly where they are
protocol-open. This is the εmid feeder `floor_prefix_le`'s `hmid` slot consumes (the per-prefix
mid-band floor-failure mass), with a decaying leading term. **FINDING 3 fully discharged into an
εmid headline, no longer blocked on `1 ≤ r`.**

### Deliverable 2 — Gap-2 status (UNCONDITIONAL killed window delivered; reachability residual precise)

The killed engine RELOCATES but does not REMOVE the Gap-2 reachability need (see the file's own
section doc + `gap2_allPhase0_window_whp_of_reachability` / `Gap2_reachability_target`): the escape
prefix `escape ≤ ∑_σ (Kˢ)c₀{1≤Φ_clock}` is structurally the REAL chain's side masses, and
`{¬noClockAtZero} ⊆ {1≤Φ_clock}` makes the recursion non-contracting — so closing it still needs
the absorbing-drift-region maintenance (`Gap2_reachability_target`), which lives in the role-split
layer, NOT in the engine.

NEW headline this line: `phase0_killed_window_unconditional` — the strongest UNCONDITIONAL killed-
side statement. KEY OBSERVATION the predecessor's residual note missed: at `Phase0Initial n c₀`
EVERY agent is RoleMCR, so `Φ_clock(c₀) = 0` (no clock summands), hence in the clean killed budget
`aᵗ·Φ_clock(c₀) + b·∑aⁱ` the LEADING TERM VANISHES — the killed (surviving-trajectory) clock-zero
mass is governed purely by fresh-clock immigration `b = ofReal(e^{−s·50(L+1)})`:

```
(killK_now^τ)(some c₀){1 ≤ killΦ Φ_s} ≤ ofReal(e^{−s·50(L+1)}) · ∑_{i<τ} ofReal(1+2(eˢ−1)/n)ⁱ
```

Hypothesis surface = `Phase0Initial n c₀` + arithmetic (`2 ≤ n`, `0 ≤ s`); NO absorbing Q, NO hτ,
NO escape reachability (the killed kernel makes the surviving trajectory gate-confined by
construction). `phase0_killed_window_unconditional_closed` (s=1) takes the immigration numeric
`b·∑aⁱ ≤ B` as an explicit hypothesis (the geometric-sum closure to `e^{−44(L+1)}`-scale, same
arithmetic as `phase0_numerics_real` applied to the immigration tail). Supporting lemmas:
`clockCounterPotential_eq_zero_of_allMcr`, `phase0Initial_mem_phase0Gate`.

---

## STATUS — LateFloor.lean: the εlate / `hlate` slot DELIVERED (2026-06-10, opus line)

New append-only file `Probability/LateFloor.lean` (namespace `ExactMajority.FloorPrefix`,
extends it). Single-file `lake env lean … LateFloor.lean` EXIT_0; every headline
`#print axioms ⊆ [propext, Classical.choice, Quot.sound]`; no sorry/admit/axiom/native_decide.
Built on uisai2 `/dev/shm/xhuan5/Ripple` (bucket `v4.30.0 @ c5ea00351c28`, mathlib via
`lake exe cache get`); 3572-job module build clean.

### What this discharges

`FloorPrefix.floor_prefix_le`'s named `hlate` hypothesis — the low-`u` checkpoint completion:
from `LowStartGood` (`shell ∧ mcrCount ≤ uMin ∧ pool ≥ 2a₀`), the run completes Stage 1
(`roleSplitGoodMile`: mcr drained) before the floor fails, failure ≤ εlate. The slot shape is
the late-band prefix `∑ τ ∈ range t, (K^(T₀+τ)) c₀ {lateBandBad n a₀ uMin hn2}` where
`lateBandBad = shell ∧ mcrCount < uMin ∧ pool < a₀ ∧ ¬roleSplitGoodMile`.

### The race-bound structure that WORKED

The honest argument is a **race via a dual pointwise cover** (Stage 1):
`lateBandBad ⊆ {pool < a₀}` AND `lateBandBad ⊆ {¬roleSplitGoodMile}` — the two ends of the
race (`lateBandBad_subset_floorFail`, `lateBandBad_subset_notDone`, pure logic). Then:

* **slow side (the genuinely-new low-`u` floor-deficit MGF)** — route through
  `{pool < a₀}` into the CONTRACTIVE killed engine. `lateBand_step_contractive` =
  `measure_mono (subset_floorFail)` then `FloorPrefix.midBand_floorFail_step_contractive` (from
  `KilledAffineTail`/`KilledTailConsumers`, `r < 1` allowed because `killΦ none = 0` made the old
  `1 ≤ r` spurious). The per-step late-band mass ≤ `(rᵗ·poolExpNeg(x) + b∑rⁱ)/exp(-s·a₀)` +
  gate-exit escape, a GENUINELY DECAYING `rᵗ` leading term. `lateBand_prefix_contractive` sums it.
* **fast side (completion tail)** — `late_completion_tail` = `real_bad_le_janson_add_escape` with
  the floor-driven `roleSplitKernelMilestone` (`pMin·meanTime = Θ(log n)`), exposing the low-`u`
  milestone start condition as the named `hPre_low` (the generic `LowStartGood` checkpoint, unlike
  the all-MCR `Phase0Initial`, must carry "no milestone fired yet"). The race's fast alternative.

The key insight the blueprint flagged ("floor martingale stalls, R1 births too weak"): the
low-`u` drift parameters `(r, b)` are carried as the NAMED `hdrift_G` hypothesis on the late-band
gate — because in Region L the multiplicative birth contraction stalls, the honest drift has an
immigration term `b > 0`, but the killed tail still decays when `r < 1`. That is exactly the
"only genuinely new probabilistic piece" — formalized as the contractive-engine instantiation,
with the stalled-martingale drift the precisely-named residual.

### Where εlate landed numerically

`εlate n := ofReal((3n²)⁻¹) = 1/(3n²)` (blueprint §4: each of εwarm/εmid/εlate ≤ 1/(3n²) so the
floor prefix ≤ n⁻² in `floor_prefix_le_inv_sq`). `late_prefix_le_inv` is the paper-scale capstone:
from a per-prefix late-band bound fitting under `1/(3n²)`, the late prefix ≤ `1/(3n²)`. The
calibration is honest because the leading term genuinely DECAYS as `rᵗ` (no `1 ≤ r`).

### The final `hlate` surface (what's wired vs named)

* `floor_prefix_le_with_late` — `FloorPrefix.floor_prefix_le` with the `hlate` slot discharged by
  `late_prefix_le` (the contractive route); `hshell`/`hmid` stay their existing
  `FloorPrefix`/`KilledTailConsumers` feeders. This is the form the εfloor assembly consumes.
* PRECISELY-NAMED residuals (the honest Region-L count-mass, after genuine attack):
  - `hdrift_G : ∀ x ∈ G, ∫ poolExpNeg s d(K x) ≤ r·poolExpNeg s x + b` — the low-`u` affine pool
    drift `(r, b)` on the late-band gate (the stalled-martingale regime; `r < 1`, `b > 0`);
  - the gate-exit (cemetery) escape mass — the deterministic floor-exit bridge, structurally the
    same as `escape_le_threshold_prefix` / the Gap-2 first-escape pattern;
  - `hPre_low` — the milestone start condition from the generic `LowStartGood` checkpoint (the
    race's fast-side alternative input).

### Axiom audit (all 9 headlines)

`lateBandBad_subset_floorFail`/`_notDone` ⊆ `[propext, Quot.sound]`; the other 7
(`late_pool_step_ge_ae`, `late_completion_tail`, `lateBand_step_contractive`,
`lateBand_prefix_contractive`, `late_prefix_le`, `floor_prefix_le_with_late`,
`late_prefix_le_inv`) ⊆ `[propext, Classical.choice, Quot.sound]`. No sorry/admit/axiom/
native_decide.
