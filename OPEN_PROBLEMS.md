# Open Problems in CRN Computable Numbers
## Formalized using the Ripple Framework

### Status Legend
- **PROVED**: Fully verified in Lean (0 sorry)
- **STATED**: Statement formalized, proof open
- **PARTIAL**: Some components proved
- **OPEN**: Not yet formalized

---

## 1. Structural Results

### 1.1 LPPs = GPACs on [0,1] (Main Theorem of [LPP])
**Status: STATED** (Stages.lean `gpac_to_lpp`)

The four-stage construction is stated but sorry'd. Each stage is independently
valuable:
- Stage 1 (quadraticization) — standard, follows [Carothers et al. 2005]
- Stage 2 (CRN → TPP cubic) — λ-trick + balancing dilation, needs careful accounting
- Stage 3 (TPP → PP quadratic) — self-product z_{i,j} = x_i·x_j
- Stage 4 (PP → PLPP) — ε-trick + coefficient bookkeeping

**Key difficulty**: Stages 2-3 require tracking polynomial degree and sign
constraints through multiple transformations. Lean's `MvPolynomial` or a
custom syntactic layer is needed.

### 1.2 Product Protocol Closure
**Status: STATED** (Stages.lean `lpp_computable_mul`)

LPP-computable numbers are closed under multiplication. The construction
(Lemma 11 in [LPP]) builds z_{i,j} = x_i·y_j and is essentially Stage 3
of the main theorem applied to the Cartesian product of two LPPs.

### 1.3 Unimolecular Protocols Compute Only Rationals
**Status: STATED** (Stages.lean `lpup_computes_rational`)

Lemma 10 in [LPP]. Proof requires formalizing functional graphs and
convergence of mass to cycles.

---

## 2. Bounded Analog Complexity ([BAC])

### 2.1 Bounded Surrogate Compilation
**Status: PARTIAL** (Compilation.lean)

The bounded surrogate U_{n,m} = f^m/(1+f^n) is defined and basic properties
proved (boundedness, diagonal identity, tendsto). The compilation theorem
`bounded_compilation` exists but uses a placeholder proof.

**Open**: Construct the actual ODE for the bounded surrogate system. Given
x' = p(x), the surrogate U = x^n/(1+x^n) satisfies a polynomial ODE
U' = P(U, 1-U, ...) that can be derived by chain rule and algebraic
manipulation.

### 2.2 Exponentiation Closure
**Status: STATED** (CRNPipeline.lean `closure_exponentiation`)

If α > 0 and β are CRN-computable, then α^β is CRN-computable.
Proof from [BAC] §6 requires:
- exp/ln are CRN-computable (follows from e being RT-CRN-computable)
- PIVP composition preserves bounded-time computability
- The identity α^β = exp(β·ln(α))

### 2.3 CRN Readout Complexity Preservation
**Status: STATED** (CRNPipeline.lean `crn_readout_preserves_complexity`)

The readout subtraction module (low-pass filter δ̇ + α·δ = α·ε(t))
preserves time complexity up to a constant. Proof requires:
- Solving the first-order linear ODE with integrating factor
- Bounding the convolution integral ∫₀ᵗ αe^{-α(t-s)}ε(s)ds
- Two regime analysis (input-limited vs module-limited)

---

## 3. Specific Numbers

### 3.1 ½e⁻¹ is LPP-Computable
**Status: PROVED** (Example.lean `halfExpNegOne_lpp`)

Complete IsLPPComputable witness with 0 sorry. The first transcendental
number proved LPP-computable in this framework.

### 3.2 Famous Constants are RT-CRN-Computable
**Status: PROVED** (Number/*.lean)

All fully verified (0 sorry):
- e (Euler.lean)
- π (Pi.lean)
- ln 2 (Ln2.lean)
- γ (EulerGamma.lean, most complex proof in the project)

### 3.3 ζ(3) is CRN-Computable
**Status: OPEN**

The Apéry constant. Current approach (Apery.lean) uses `realtime_const`
placeholder. Research direction from experiments/FINDINGS.md:
- ODE: x²(4+x)F''' + x(10+3x)F'' + (2+x)F' = 1
- Generates ζ(3) via Apéry's generating function
- **Obstacle**: singular point at x=0 needs regularization for PIVP form
- **Question**: Is ζ(3) in the first floor (real-time) or does it require
  polynomial time? Current manual proof is second-floor.

### 3.4 Catalan's Constant is CRN-Computable
**Status: OPEN**

From [LPP] Corollary 19: G = ½∫₀^∞ t/cosh(t) dt can be computed by:
  G' = R(1-V), R' = E-R, E' = -E, V' = (1-V)²·(-2E²)
with G(0)=0, R(0)=0, E(0)=1, V(0)=½. This is a concrete PIVP.

---

## 4. Research Questions

### 4.1 Can LPP-computable numbers use a single output variable?
Currently, LPP computability requires marking a *set* of states.
Is there a single-output characterization? (Open Question from [LPP] §4)

### 4.2 What is the complexity hierarchy for LPP computation?
The GPAC→LPP translation introduces at most linear slowdown
(from the balancing dilation in Stage 2). Is this tight?
Can we define LPP-analogues of the bounded complexity floors?

### 4.3 Scarce-variable population protocols
Protocols with some variables at O(1) population (not tending to ∞)
escape Kurtz's theorem. What can they compute?
(Open direction from [LPP] §4)

### 4.4 Black-and-white k-PPs
Two-state k-PPs with restricted products can compute some algebraic
numbers (e.g., (3-√5)/2) but not all rationals (e.g., not 1/5).
What is the exact characterization? (See [LPP] §4, reference [16])

### 4.5 PP → NAP construction: is it general?
**Status: OPEN (TODO after Phase D closes)**

Given a population protocol, [BD] (Huang-Huls, DNA 30) provides an
algorithm (cubing + r²-trick) that converts it to a NAP. Existing
case studies in `Ripple/LPP/NAP.lean` confirm the construction on
specific examples, but we have **not** proved it is general — i.e.,
that every PP (or every 4-PP after the r²-trick) admits a cubing that
produces a NAP satisfying the splitting-feasibility condition.

What we currently have:
- `NAP Splitting Feasibility` statement (combinatorial, on exponent
  vectors and factorizations)
- Worked examples where the construction succeeds

What we need:
- A general theorem: "for any PP π, cubing(r²-trick(π)) is a NAP"
- Alternative: identify the class of PPs for which the construction
  succeeds, and characterize the gap (if any)

Dad flagged this 2026-04-19: "我们有例子能成功转成, 但是我不确定这是不是一个
general 的办法." Revisit after saturating-surrogate Phase D closes.

---

## 5. Infrastructure Priorities

1. **is_solution placeholder removal** — The `PIVP.Solution` type uses
   `is_solution : True` as a placeholder. Making this a real ODE solution
   constraint would make all downstream theorems non-vacuous.

2. **Polynomial degree tracking** — Stages 1-3 of the LPP construction
   require reasoning about polynomial degree and homogeneity. A syntactic
   layer for degree-bounded polynomials would unlock these proofs.

3. **Simplex invariance** — Many LPP proofs need the fact that the
   probability simplex {x ≥ 0, Σx_i = 1} is invariant under conservative
   systems. A general invariance theorem would be valuable.

---

*Generated from the Ripple framework, 2026-04-15.*
*Papers: [RTCRN2] DNA 25, [LPP] DNA 28, [BAC] DNA 32.*
