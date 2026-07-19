# Ripple

> 📄 **Technical report:** [*Ripple: An Open, AI-Formalized Lean 4 Framework for Computing with CRNs*](https://arxiv.org/abs/2607.13531) (Chen & Huang) — the full paper, with complete references and detailed proofs. The DNA 32 poster paper, now on arXiv (arXiv:2607.13531).

An open, AI-formalized **Lean 4 framework for the mathematics of computing with chemical reaction networks** — from CRN-computable real numbers and their compilation down to large-population protocols, through the stochastic-to-deterministic bridge (Kurtz's mean-field theorem), to two classical Turing-completeness theorems and three landmark population-protocol majority results. Everything builds with **zero `sorry`**; the only axioms beyond Lean's standard three are two named assumptions in the BGP construction (Stone–Weierstrass + continuous-iteration steps — see `BoundedUniversality/GPAC/BGPConstruction.lean`). Trust beyond the kernel: `native_decide` is used in the modular-forms thread and in `LPP/ExampleGammaCompiled.lean`.

## Where the name comes from

"Ripple" is a mishearing — by an AI. The author said *repo* (short for *repository*) in a voice message; the speech-recognition model heard *ripple*. The transcription stuck as the name — because the underlying research actually did start small and ripple outward.

It began as a homework exercise in Jack Lutz's class at Iowa State: *can you compute rational numbers with a chemical reaction network?* That grew into algebraic numbers, then transcendentals (e, π, the Euler–Mascheroni constant γ, ln 2), then the shape of the whole real-time class, then weaker population-protocol refinements, then — on the other side — stronger infinite-time analogues. Each layer was a new ripple from the same class exercise.

This repository is the Lean 4 counterpart to that trajectory.

## Scope

**The CRN-computability line** — the repository's spine:

1. Huang, Klinge, Lathrop, Li, Lutz — *Real-time computability of real numbers by chemical reaction networks*, Nat. Comput. 2019.
2. Huang, Klinge, Lathrop — *Real-time equivalence of CRNs and analog computers*, DNA 25 (2019).
3. Huang, Huls — *Computing real numbers with large-population protocols*, DNA 28 (2022).
4. Chen, Huang — *Bounded analog complexity of real numbers* (submitted, 2026).

**Turing-completeness, one theorem on each side of the model ladder:**

5. Bournez, Graça, Pouly — *Polynomial time corresponds to solutions of polynomial ODEs of polynomial length*, J. ACM 2017 (deterministic GPAC/PIVP side).
6. Soloveichik, Cook, Winfree, Bruck — *Computation with finite stochastic chemical reaction networks*, Nat. Comput. 2008 (stochastic side).

**Population-protocol majority — three landmark protocols:**

7. Angluin, Aspnes, Eisenstat — *A simple population protocol for fast robust approximate majority*, Distributed Computing 2008.
8. Doty, Eftekhari, Gąsieniec, Severson, Uznański, Viglietta — time- and space-optimal stable exact majority, FOCS 2021.
9. Kanaya, Eguchi, Sasada, Ooshita, Inoue — *Time- and space-optimal silent self-stabilizing exact majority in population protocols*, SSS 2025.
10. Burman, Chen, Chen, Doty, Nowak, Severson, Xu — *Time-optimal self-stabilizing leader election in population protocols*, PODC 2021 (source of the Optimal-Silent-SSR ranking subprotocol that (9) composes with).

**The probabilistic foundation** — the mean-field limit connecting stochastic CRN dynamics (CTMCs) to their deterministic ODE approximations (GPACs):

11. Kurtz — *Solutions of ordinary differential equations as limits of pure jump Markov processes*, J. Appl. Probab. 1970 (convergence in probability).
12. Kurtz — *The relationship between stochastic and deterministic models for chemical reactions*, J. Chem. Phys. 1972 (Chebyshev deviation bound and CLT).
13. Kurtz — *Strong approximation theorems for density dependent Markov chains*, Stochastic Process. Appl. 1978 (a.s. O(log N/√N) rate).
14. Ethier, Kurtz — *Markov Processes: Characterization and Convergence*, Wiley 1986.

**Classical mathematics in service of the number constructions:** van der Poorten's account (1979) of Apéry's ζ(3) recurrences, formalized via an explicit Zeilberger witness; Cassels' elementary descent (1960) for the Catalan equation; Ramanujan's 1914 modular 1/π series, with the surrounding reduction machine-checked (Clausen, Picard–Fuchs, Chowla–Selberg) and the CM evaluation `j((1+√−163)/2) = −640320³` fully verified through the level-41 modular polynomial Φ₄₁.

The goal is to treat all of this as one unified, extensible pipeline: a CRN in its mass-action limit is a polynomial ODE system, a population protocol is its finite-N stochastic shadow, and Kurtz's theorem is the verified bridge between them.

## What is formalized (as of 2026-07-15)

A prose tour; the [technical report](https://arxiv.org/abs/2607.13531) gives the precise statements and proofs.

### The model ladder

The core is a single Lean notion of what it means for a bounded CRN/GPAC to *compute* a real number in real time, together with the machinery that moves computations down the ladder of models: the GPAC/PIVP layer with bounded-time complexity; the dual-rail compiler; and the four-stage compilation into **large-population protocols**, whose main theorem — every bounded certified PIVP admitting a CRN decomposition is LPP-computable — is unconditional, as is the construction placing every algebraic number in [0,1] inside the LPP class. Because the computable class is a Lean type, adding a new number is a plug-in: supply a PIVP, prove boundedness and a convergence modulus, and the pipeline does the rest.

### Computable numbers

The famous constants e, π, ln 2, γ, the Dottie number, and Catalan's constant G are certified CRN-computable, each with an explicit polynomial IVP and machine-checked convergence bound. **Apéry's constant ζ(3)** is done twice: a certified real-time construction via the Fermi–Dirac integral, and a methodologically novel *series-encoding* route through its holonomic generating function, built on a formalized Frobenius theory of regular-singular ODEs — along with a formalization-discovered obstruction that sharply delimits where the series route works.

### The stochastic bridge: CTMCs and Kurtz's mean-field theorem

A continuous-time Markov chain theory built from the ground up (none previously existed in Mathlib), through to **three machine-checked versions of Kurtz's theorem**: convergence in probability, almost-sure convergence at rate O(log N/√N), and a CLT-scale second-moment bound. Supporting probability infrastructure — integral Grönwall, Doob's inequality at a random index, Bennett and discrete Freedman inequalities — is general-purpose and reusable by anyone formalizing stochastic kinetics or mean-field limits, whether or not they care about computable numbers.

### Two Turing-completeness theorems

Both classical universality results of the field are machine-checked end to end: the Bournez–Graça–Pouly construction (polynomial ODEs simulate arbitrary Turing machines) on the deterministic side, and the Soloveichik–Cook–Winfree–Bruck construction (finite stochastic CRNs are Turing-universal with bounded error) on the stochastic side. Bounded-domain extensions of the BGP construction are in preparation.

### Three landmark majority protocols

The largest pillar of the repository. For the Angluin–Aspnes–Eisenstat 3-state approximate majority protocol, Ripple formalizes the *full probabilistic convergence theorem* — the O(n log n) high-probability bound, not just stable correctness. For the Doty et al. exact majority protocol, the deterministic correctness chain, the O(n log n) high-probability convergence time, and a polynomial state bound. For the Kanaya et al. silent self-stabilizing exact majority protocol, all four of the paper's theorems — including the impossibility result and the space lower bound — composed with a full formalization of the Burman et al. ranking subprotocol; the top-level theorem for the composed protocol is unconditional for every n ≥ 4.

### Gaps exposed by formalization

Machine-checking surfaced genuine gaps in published proofs — in each case the published *theorem* survives, but a proof step or construction does not:

- **Approximate majority (AAE 2008).** The central-region multiplicative drift inequality suggested by the original proof sketch is *false* — there is an explicit n = 4 counterexample. The Lean proof replaces it with a product-form supermartingale argument.
- **LPP compilation (DNA 28).** The published compilation can transiently leave the unit interval, breaking an unstated assumption; the formalized fix inserts a saturating low-pass filter, and the repaired theorem is now unconditional.
- **Algebraic numbers in the urn model.** The arbitrary-degree claim silently rests on Catalan's conjecture (Mihăilescu's theorem). Formalizing Cassels' 1960 descent pinned down exactly what the elementary argument gives (a divisibility conclusion) and what it does not (non-existence) — a dependency on a genuinely deep theorem that the informal presentation hides.

Beyond repairs, formalization also *produced* new mathematics: the zero-init non-collapse theorem (`zero_init_no_collapse` in `Ripple/Core/`) — in a bounded, zero-initialized CRN, any species that ever becomes positive stays bounded away from zero, so 0 is not non-trivially computable from zero initialization — was conjectured, stated, and proved inside the framework. And the series-encoding recipe applied to Ramanujan's modular 1/π series surfaces a sharp open problem: the series anchor is a fixed point of the drive, so the natural encoding provably does not converge to π exactly.

## How it was built

Essentially all of the Lean — roughly three-quarters of a million lines — was written by AI agents running *publicly available* models (Anthropic's Claude, OpenAI's GPT), orchestrated by standard agentic coding tools, with the human contribution concentrated on choosing the statements, the proof strategies, and the curation. Every AI-proposed proof is compiled and kernel-checked before acceptance: AI proposes, only the Lean kernel certifies. The workflow is reproducible by anyone with the same public toolchain; the technical report's §"The Formalization Method" documents it.

## Trust footprint

Zero `sorry`. Two named `axiom` declarations exist in `BoundedUniversality/GPAC/BGPConstruction.lean` (Stone–Weierstrass polynomial-approximation step and robust continuous-iteration step of the BGP construction) — these are documented gaps in a superseded route; the headline theorem `bounded_pivp_turing_complete` does NOT depend on them. `#print axioms` on all headline results reports only Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Trust beyond the kernel: `native_decide` is used in finitely many places — in the modular-forms thread (Φ₄₁ Sturm and root checks for the CM-163 evaluation) and in `LPP/ExampleGammaCompiled.lean` (26 occurrences for γ mean-field compilation verification) — to discharge large decidable computations.

## What remains open

`OPEN_PROBLEMS.md` tracks the research frontier, headlined by the 1/π fixed-point obstruction and the second-floor (regular-singular arrival) question for series encodings; the technical report's gap and open-problem sections give the precise statements.

## Building

```bash
# Prerequisites: elan + Lake (https://leanprover.github.io/)
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get    # pull Mathlib oleans
lake build
```

Takes 10–20 minutes on first build (mostly Mathlib).

## Using Ripple

**To check a claim instead of trusting it.** Every headline result is an ordinary Lean theorem; the kernel will tell you exactly what it rests on:

```lean
import Ripple.Number.AperyFermi

#print axioms apery_fermi_is_crn_computable
-- 'apery_fermi_is_crn_computable' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Three standard axioms, nothing else — that check is the whole point of the repository, and it works the same way for any theorem here.

**To use it as a library.** Ripple builds on Mathlib `v4.30.0` (Lean `v4.30.0`); from a project on the same toolchain, add to your `lakefile.toml`:

```toml
[[require]]
name = "Ripple"
git  = "https://github.com/zinan-huang/Ripple"
rev  = "main"
```

**To add your own computable number.** This is the intended extension path, and it is a plug-in: write down your polynomial IVP, prove boundedness and an exponential convergence modulus, and the pipeline gives you the rest — `CertifiedBoundedTimeComputable` (in `Ripple/Core/`) is the single definition of "computes α", and `bounded_crn_is_lpp_computable_unconditional` then hands you large-population-protocol computability for free. `Ripple/Number/CatalanCertified.lean` (a 4-variable IVP, self-contained) is the model to imitate.

**To take pieces.** The probabilistic layers know nothing about CRNs: `CTMC/`, `Kurtz/`, and `Probability/` are a standalone verified toolkit for anyone formalizing continuous-time Markov chains, mean-field limits, or concentration bounds — the parts of this development that did not previously exist in Mathlib.

**Where to start reading.** `Core/PIVP.lean` (the model) → `Core/CRNPipeline.lean` (what "computes" means) → one certified number (`Number/CatalanCertified.lean`) → the LPP main theorem (`LPP/BoundedLPP.lean`) → `Kurtz/MeanField.lean` (the stochastic bridge). The [technical report](https://arxiv.org/abs/2607.13531) is the guided tour of the same route.

## Structure

```
Ripple/
├── Core/                  GPAC/PIVP, bounded-time complexity, CRN pipeline, zero-init non-collapse
├── DualRail/              dual-rail encoding of polynomial dynamics
├── LPP/                   large-population-protocol compilation + unconditional main theorem
├── Number/                e, π, ln 2, γ, Dottie, Catalan G, ζ(3) (Fermi–Dirac + Apéry series)
│   ├── Frobenius/         regular-singular Frobenius theory; Apéry conifold
│   ├── Hypergeometric/    Clausen, Picard–Fuchs Wronskian, Chowla–Selberg; Ramanujan reduction
│   └── Modular/           modular forms, Φ₄₁, CM-163, j(τ₁₆₃)
├── CTMC/                  DTMC/CTMC, density process, random-index Doob, absorbing states
├── Kurtz/                 Kurtz mean-field theorem (weak / strong / CLT-scale)
├── Probability/           Bennett exponential-moment lemma, discrete Freedman inequality
├── PopulationProtocol/    majority: approximate (AAE), exact (Doty et al.),
│                          self-stabilizing (Kanaya et al.) + Burman ranking subprotocol
├── sCRNUniversality/      stochastic CRN Turing completeness (SCWB 2008)
├── BoundedUniversality/   GPAC Turing completeness (BGP 2017); bounded extensions in preparation
├── ODE/                   scalar convergence barriers
└── Analysis/              stable Grönwall lemma
```

`OPEN_PROBLEMS.md` lists the current research frontier; `WORK_LOG.md` and `CHECKPOINT.md` track session-level progress.

## References

The full bibliography is in the [technical report](https://arxiv.org/abs/2607.13531). BibTeX for the repository's spine:

```bibtex
@article{HKLLM18,
  author  = {Huang, Xiang and Klinge, Titus H. and Lathrop, James I. and Li, Xiaoyuan and Lutz, Jack H.},
  title   = {Real-time computability of real numbers by chemical reaction networks},
  journal = {Natural Computing},
  volume  = {18},
  pages   = {63--73},
  year    = {2019},
  doi     = {10.1007/s11047-018-9706-x}
}

@inproceedings{HKL19,
  author    = {Huang, Xiang and Klinge, Titus H. and Lathrop, James I.},
  title     = {Real-time equivalence of chemical reaction networks and analog computers},
  booktitle = {DNA Computing and Molecular Programming (DNA 25)},
  series    = {LNCS},
  volume    = {11648},
  pages     = {37--53},
  year      = {2019},
  doi       = {10.1007/978-3-030-26807-7_3}
}

@inproceedings{HH22,
  author    = {Huang, Xiang and Huls, Rachel},
  title     = {Computing real numbers with large-population protocols},
  booktitle = {DNA Computing and Molecular Programming (DNA 28)},
  series    = {LNCS},
  volume    = {13467},
  pages     = {55--71},
  year      = {2022},
  doi       = {10.1007/978-3-031-13502-6_4}
}

@unpublished{CH26,
  author = {Chen, Ho-Lin and Huang, Xiang},
  title  = {Bounded analog complexity},
  note   = {To appear, DNA 32; arXiv:2607.12234},
  year   = {2026}
}
```

Mean-field limit (Kurtz theorem):

```bibtex
@article{Kurtz70,
  author  = {Kurtz, Thomas G.},
  title   = {Solutions of ordinary differential equations as limits of pure jump {M}arkov processes},
  journal = {Journal of Applied Probability},
  volume  = {7},
  number  = {1},
  pages   = {49--58},
  year    = {1970},
  doi     = {10.2307/3212147}
}

@article{Kurtz72,
  author  = {Kurtz, Thomas G.},
  title   = {The relationship between stochastic and deterministic models for chemical reactions},
  journal = {The Journal of Chemical Physics},
  volume  = {57},
  number  = {7},
  pages   = {2976--2978},
  year    = {1972}
}

@article{Kurtz78,
  author  = {Kurtz, Thomas G.},
  title   = {Strong approximation theorems for density dependent {M}arkov chains},
  journal = {Stochastic Processes and their Applications},
  volume  = {6},
  number  = {3},
  pages   = {223--240},
  year    = {1978}
}

@book{EthierKurtz86,
  author    = {Ethier, Stewart N. and Kurtz, Thomas G.},
  title     = {Markov Processes: Characterization and Convergence},
  publisher = {Wiley},
  year      = {1986},
  edition   = {2nd ed., 2005},
  doi       = {10.1002/9780470316658}
}
```

## Citing

If this formalization is useful in your work, cite the [technical report](https://arxiv.org/abs/2607.13531) and/or the relevant paper above. The repository itself is a living artifact — referencing the commit hash alongside the paper is more informative than the repo alone.

## License

Apache-2.0, matching Mathlib. See `LICENSE`.
