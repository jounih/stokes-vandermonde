# Scope Note: Distinct-Density Prime Towers, Universal Strong `ℂ({x})` Lift, Conditional `RH → G_Λ`, & Analytic Certification Toolkit

**Audit ledgers:** [`Statements/DistinctDensityPrimes.lean`](../Statements/DistinctDensityPrimes.lean) · [`Statements/HigherOrderStrongAndRH.lean`](../Statements/HigherOrderStrongAndRH.lean)  
**Full proofs:** [`PakPrimes/DistinctDensityPrimes.lean`](../PakPrimes/DistinctDensityPrimes.lean) (`5,059` lines) · [`PakPrimes/HigherOrderStrongDTrans.lean`](../PakPrimes/HigherOrderStrongDTrans.lean) (`3,644` lines) · [`PakPrimes/RiemannHypothesisStokes.lean`](../PakPrimes/RiemannHypothesisStokes.lean) (`1,719` lines) · [`PakPrimes/CogenticAnalyticToolkit.lean`](../PakPrimes/CogenticAnalyticToolkit.lean) (`1,722` lines)

## What Is Formalized
1. **Distinct-Density Prime Towers (Unconditional on `HasDensityPNT` input):**
   - Unconditional joint algebraic independence over `ℂ` of all derivatives of shifted logarithmic branches `{I_+(u - log δ_i)}` for any injective family of positive densities `δ_i > 0`.
   - Joint differential independence over `ℂ(x)` of any finite or countably infinite dyadic family of sequence OGFs `∑ a_i(n) x^n` satisfying quantitative density asymptotics `HasDensityPNT (a i) (δ i)` (e.g., primes in nested arithmetic progressions `p ≡ 1 mod 2^k` via quantitative Dirichlet PNT).
2. **Universal Strong `ℂ({x})` Lift (Unconditional):**
   - Lifts the entire rotated-ray, arbitrary-pole-order `HigherOrderStokes` engine from `ℂ(x)` to `StronglyDTransOverMeromorphicGerms` (`ℂ({x})`), covering Bernoulli, `tan`, `sec`, `sec^p`, Euler–Genocchi powers, trigamma, and rotated Lambert OGFs.
3. **Conditional `RH → G_Λ` Bridge (Explicitly Conditional on `RiemannHypothesis`):**
   - Proves the *implication* `(RiemannHypothesis ∧ InfinitelyManyCriticalLineZeros) →` D-transcendence over `ℂ(x)` and strong D-transcendence over `ℂ({x})` of the von Mangoldt Borel-Laplace series `G_Λ`. **This theorem does NOT assume or prove RH; `RiemannHypothesis` is an explicit hypothesis of the theorem.**
4. **Analytic Certification Toolkit (`CogenticAnalyticToolkit`, Unconditional):**
   - Multi-scale geometric exponential filter bank Plancherel spectral-dominance inequalities (`K ≥ 10`) and exact rational Collatz–Wielandt spectral-radius upper bounds.

## What Is NOT Formalized Here
- Quantitative Dirichlet PNT (`HasDensityPNT` for arithmetic progressions `p ≡ 1 mod 2^k`) is taken as an explicit hypothesis in `DistinctDensityPrimes.lean` (unlike `PakNthPrime.lean`, which discharges standard PNT from `MediumPNT`).
- *(Updated in `v3.3.0`)*: Elementary RH-independent strong $\mathbb{C}(\{t\})$ D-transcendence of `G_Λ` (at both `s₀ = 2` and `s₀ = 1/2`) is now proved unconditionally via the negative-real-axis trivial-zero ray in [`Statements/UnconditionalPrimes.lean`](../Statements/UnconditionalPrimes.lean) (see [`docs/geometry-and-unconditional-primes.md`](geometry-and-unconditional-primes.md)).
