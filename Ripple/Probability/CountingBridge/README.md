# Word counts and uniform letter sequences

Import `Ripple.Probability.CountingBridge` to obtain the complete API.

Let `α` be a finite nonempty alphabet (`[Fintype α] [Nonempty α]`, with
`[MeasurableSpace α] [DiscreteMeasurableSpace α]` for the measure-theoretic
statements). The measure `μ α` on `ℕ → α` is the infinite product of the uniform laws
`PMF.uniformOfFintype α`. `«prefix» T ω` is the word of the first `T` letters, read in
increasing time order. A deterministic transition `next : S → α → S` and a target
`P : S → Prop` define the run `run next x ω t` and its hitting time
`τ next P x ω : ℕ∞`, which tests the initial state at time zero and equals `⊤` when the
run never reaches `P`.

The combinatorial side counts words. `Words.allWords α T` enumerates the words of length
`T` as a multiset by appending one letter at a time; `Words.wordSum α T f` evaluates `f`
on the reverse of each enumerated word. The reversed enumeration grows at the head, which
gives the first-letter recursion `wordSum_succ`; since reversal permutes the words of
length `T`, `wordSum_eq_sum_tuples` identifies the word sum with the plain sum over all
words. Every count divided by `Fintype.card α ^ T` is the probability of the
corresponding event under `μ α`.

| Module | Contents | Main results |
| --- | --- | --- |
| `Counts` | Words, enumeration, word sums; first-hit counts, rational probabilities, `AlmostSurelyHits`, `ExpectedHittingTimeAtMost` (namespaces `Words`, `FirstHit`) | `Words.wordSum_succ`, `Words.wordSum_eq_sum_tuples` |
| `WordLaw` | The measure `μ α`, prefixes, cylinder law | `cylinder_measure`, `lintegral_word_function`, `measurable_prefix` |
| `Hitting` | Runs and the hitting time `τ`; word indicators as events of `τ` | `measurable_τ`, `τ_of_not_target`, `costWord_prefix`, `lintegral_min_hit_eq`, `lintegral_hit_eq_iSup` |
| `Events` | Survival and first-hit probabilities; almost-sure hitting | `survival_measure_count`, `survival_measure`, `firstHit_measure`, `truncatedExpectation_eq_lintegral`, `ae_hits_iff` |
| `Expectation` | Expectation as the supremum of partial first moments | `lintegral_hit_eq_iSup_partial`, `expected_iff`, `expectedHittingTimeAtMost_iff` |
| `Endpoint` | Stopping trees (namespace `StoppingTree`) and endpoint sums | `wordSum_foldl_eq_endpointSum`, `lintegral_endpointSum` |
| `Stopping` | Prefix sigma algebras; first-prefix events and transfer of uniform continuation bounds | `prefixSigma_mono`, `measure_prefix_event`, `first_prefix_count_transfer`, `first_prefix_fraction_transfer`, `first_prefix_measure_transfer` |
| `Geometric` | Waiting for a letter from a nonempty set `G` | `geometric_success_measure`, `lintegral_hit_eq_tsum_survival`, `geometric_hitting_mean` (mean `card α / card G`), `geometric_hitting_mean_fin` (mean `n / k`) |

Rational quantities enter `ℝ≥0∞` as `ENNReal.ofReal (q : ℝ)`, for example in
`survival_measure`, `firstHit_measure` and `truncatedExpectation_eq_lintegral`.
`expected_iff` takes a bound `B : ℚ≥0`; `expectedHittingTimeAtMost_iff` takes
`B : ℚ` with the premise `0 ≤ B`.
