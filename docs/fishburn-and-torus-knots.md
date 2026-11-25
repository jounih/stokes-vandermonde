# Scope Note: Fishburn Series (Bostan–Di Vizio–Raschel §2.2.6) & All Torus Knots `T(p, q)`

**Statement spec:** [`Statements/FishburnTorusKnots.lean`](../Statements/FishburnTorusKnots.lean)  
**Proof modules:** [`PakPrimes/BranchPointStokes.lean`](../PakPrimes/BranchPointStokes.lean), [`PakPrimes/FishburnTorusKnots.lean`](../PakPrimes/FishburnTorusKnots.lean), [`PakPrimes/FishburnStrongDTrans.lean`](../PakPrimes/FishburnStrongDTrans.lean)

## Formalized in Lean 4 (v3.1.0-rc)

- **Zagier's 2001 formal identity (`zagier_2001_thm3`):** Formalized unconditionally from scratch in `PowerSeries ℂ`:
  $$P(1 - e^{-24t}) = e^t \sum_{k \ge 0} \frac{T_k}{k!} t^k,$$
  where $P(x) = \sum_{m \ge 0} \prod_{j=1}^m (1 - (1 - x)^j)$ is the literal divergent Fishburn ordinary generating function (OEIS A022493) and $T_k$ are Glaisher's $T$-numbers ($\sin(2s)/(2\cos(3s)) = \sum T_k s^{2k+1}/(2k+1)!$, OEIS A002439).
- **Bostan–Di Vizio–Raschel open question — BOTH over $\mathbb{C}(x)$ AND over $\mathbb{C}(\{x\})$:**
  - `fishburn_ogf_dTrans_over_ratFunc`: Unconditional D-transcendence of $P(x)$ over $\mathbb{C}(x)$, matching the literal wording of Bostan, Di Vizio, and Raschel (*Amer. J. Math.* 146(6), 2024, §2.2.6) and Pak–Yeliussizov Conjecture 1.
  - `fishburn_ogf_stronglyDTrans_over_meromorphicGerms`: Unconditional **strong** D-transcendence of $P(x)$ over the full field $\mathbb{C}(\{x\})$ (`FractionRing ConvergentPowerSeries`, bridged to Mathlib's `AnalyticAt ℂ _ 0` via `isConvergentPS_iff_exists_analyticAt`) of convergent meromorphic germs at $0$, matching the stronger base field of Bostan–Di Vizio–Raschel Theorem 3 and Klazar (2003).
- **All torus knots $T(p, q)$ ($\forall p, q \ge 2$):** Unconditional D-transcendence over $\mathbb{C}(t)$ and strong D-transcendence over $\mathbb{C}(\{t\})$ for both the Euler formal series $\sum (T_k^{(p,q)}/k!) t^k$ and the alternating Lawrence–Zagier / Hikami perturbative WRT formal power series $\sum ((-1)^k T_k^{(p,q)}/k!) t^k$, via the exact half-integer Abel branch-point Borel–Stokes engine (`BranchPointStokes.lean` + `FishburnStrongDTrans.lean`) on the active simple poles $\{n \ge 1 : p \nmid n \land q \nmid n\}$.
