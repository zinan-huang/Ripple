# Agent-level scheduler and the configuration chain

Statement and paper proof for the second half of the counting–measure bridge: the uniform
random scheduler run on labelled agents, observed through the configuration (the multiset of
agent states), is the configuration Markov chain `Protocol.transitionKernel` of the
exact-majority development. Together with `Ripple.CountingBridge` (counts of scheduler words
equal probabilities under the uniform product measure), this lets a count computed on
labelled scheduler words, as a model checker computes it, be read as a probability of the
configuration chain on which the time theorems are stated.

## Setting

- `Λ` a finite state type with decidable equality, `P : Protocol Λ` with transition
  `δ : Λ → Λ → Λ × Λ`.
- `n ≥ 2` agents, labelled by `Fin n`. An agent assignment is `a : Fin n → Λ`; its
  configuration is `cfg a := Multiset.map a Finset.univ.val`, of cardinality `n`.
- The pair alphabet `Pairs n := {p : Fin n × Fin n // p.1 ≠ p.2}`, of cardinality
  `n (n - 1)`; the letter law is uniform on `Pairs n`.
- The labelled step `lstep a (i, j)` sets agent `i` to `(δ (a i) (a j)).1` and agent `j` to
  `(δ (a i) (a j)).2`, other agents unchanged (`i ≠ j`, so the two updates commute).
- A run `lrun a ω T` folds `lstep` over the first `T` letters of `ω : ℕ → Pairs n`; the
  scheduler measure is `Measure.infinitePi (fun _ => uniform (Pairs n))`.

The configuration-level objects are those of
`Ripple/PopulationProtocol/ExactMajority/Probability/Scheduler.lean` and `MarkovChain.lean`:
`Config.interactionCount`, `Config.totalPairs`, `Protocol.stepOrSelf`, `Protocol.stepDist`,
`Protocol.stepDistOrSelf`, `Protocol.transitionKernel`.

## Lemma 1 (one labelled step is one configuration step)

For `i ≠ j`, `cfg (lstep a (i, j)) = P.stepOrSelf (cfg a) (a i) (a j)`.

*Proof.* Since `i ≠ j`, `{a i, a j} ≤ cfg a` (two distinct agents carry these states; if
`a i = a j` that state has count at least two), so `stepOrSelf` takes its applicable branch
and returns `cfg a - {a i, a j} + {p.1, p.2}` with `p = δ (a i) (a j)`. On the labelled side,
`cfg (lstep a (i, j))` removes the old states of agents `i` and `j` and adds the new ones;
the other `n - 2` agents contribute the same multiset on both sides. ∎

## Lemma 2 (pair counts)

For states `s₁, s₂`, the number of pairs `(i, j)` in `Pairs n` with `a i = s₁` and
`a j = s₂` is `Config.interactionCount (cfg a) s₁ s₂`, and `|Pairs n| = Config.totalPairs (cfg a)`.

*Proof.* If `s₁ ≠ s₂`, choose `i` among the `count s₁` agents in state `s₁` and `j` among the
`count s₂` agents in `s₂`; they are automatically distinct. If `s₁ = s₂`, choose an ordered
pair of distinct agents among `count s₁`: `count s₁ (count s₁ - 1)`. The total is
`n (n - 1) = card (n - 1)`. ∎

## Proposition 3 (one-step lumping)

`PMF.map (fun p => cfg (lstep a p)) (uniform (Pairs n)) = P.stepDist (cfg a) hc`, where
`hc : 2 ≤ (cfg a).card`.

*Proof.* `stepDist c = PMF.map (scheduledStep P c) (interactionPMF c)` and `interactionPMF c`
gives the state pair `(s₁, s₂)` mass `interactionCount c s₁ s₂ / totalPairs c`. Push the
uniform law on `Pairs n` forward by `p ↦ (a p.1, a p.2)`: by Lemma 2 its mass at `(s₁, s₂)` is
the same ratio, so the pushforward is `interactionPMF (cfg a)`. By Lemma 1,
`cfg ∘ lstep a = scheduledStep P (cfg a) ∘ (p ↦ (a p.1, a p.2))`. Compose the two maps. ∎

## Theorem 4 (multi-step lumping)

For every `T`, the law of `cfg (lrun a ω T)` under the scheduler measure is
`(P.transitionKernel ^ T) (cfg a)`.

*Proof.* Induction on `T`. `T = 0`: both sides are the Dirac mass at `cfg a`. Step: the first
`T` letters and letter `T` are independent under the product measure, so the law of
`cfg (lrun a ω (T + 1))` is obtained from the joint law of `lrun a ω T` (an assignment) and an
independent uniform letter. Conditioning on `lrun a ω T = b`, Proposition 3 gives the law
`P.stepDist (cfg b)`, which equals `P.stepDistOrSelf (cfg b)` because `(cfg b).card = n ≥ 2`;
it depends on `b` only through `cfg b`. Hence the law at `T + 1` is the law at `T` composed with
`transitionKernel`, which is `transitionKernel ^ (T + 1)` applied to `cfg a` by the induction
hypothesis. ∎

The Lean proof can avoid conditioning: the map `ω ↦ (prefix of length T, letter T)` sends the
product measure to the product of the prefix law and the uniform letter law
(`Measure.infinitePi` splits over a finite set of coordinates and its complement), and the
composition is a `Measure.bind` over a finite (discrete) space.

## Corollary 5 (counts are configuration-chain probabilities)

For a configuration predicate `Q`, the number of scheduler words of length `T` along which
`cfg (lrun a ·)` avoids `Q` at times `0, …, T`, divided by `(n (n - 1)) ^ T`, is the
probability that the configuration chain started at `cfg a` avoids `Q` up to time `T`. The
same holds for first-hit counts and truncated expected hitting times.

*Proof.* The counting bridge identifies the normalized count with the product-measure
probability of the corresponding cylinder event of the labelled run; the event depends on `ω`
only through `cfg ∘ lrun a ω`, whose finite-dimensional laws are those of the configuration
chain by Theorem 4 extended to joint laws at times `0, …, T` (same induction, carrying the
whole path). ∎

## Scope

Theorem 4 and Corollary 5 are about the chain with the degenerate fallback `stepDistOrSelf`
only through populations of size at least two, where it coincides with `stepDist`. The
exact-majority time theorems are stated for `transitionKernel`; Corollary 5 is how a
model-checked count on labelled words becomes a statement about that kernel.
