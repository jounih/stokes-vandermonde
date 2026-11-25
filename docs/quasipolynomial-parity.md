# Scope Note: Quasipolynomial Euler-Product Parity Dichotomy

**Statement spec:** [`Statements/QuasipolynomialParity.lean`](../Statements/QuasipolynomialParity.lean)  
**Proof modules:** [`PakPrimes/QuasipolynomialEulerParity.lean`](../PakPrimes/QuasipolynomialEulerParity.lean), [`PakPrimes/QuasipolynomialIFF.lean`](../PakPrimes/QuasipolynomialIFF.lean), [`PakPrimes/HarmonicTrapShift.lean`](../PakPrimes/HarmonicTrapShift.lean)

## Formalized in Lean 4 (v3.0.0)

- **Odd-part obstruction for arbitrary period $M \ge 1$ and degree $D \ge 0$:** For any quasipolynomial $P : \mathbb{Z} \to \mathbb{C}$ whose odd part $P^-(n) = (P(n) - P(-n))/2$ is not identically zero, and any weight $w : \mathbb{N} \to \mathbb{C}$ eventually agreeing with $P$, both the Lambert series $H_w(q) = \sum_{n \ge 1} \frac{w(n) n q^n}{1 - q^n}$ and the weighted Euler product $G_w(q) = \prod_{n \ge 1} (1 - q^n)^{-w(n)}$ (including the literal infinite product `PakPrimes.HarmonicTrap.bose g` in `PowerSeries.WithPiTopology` when $g : \mathbb{N} \to \mathbb{N}$) satisfy no nonzero algebraic differential equation over $\mathbb{C}(q)$.
- **Complete `IFF` converse for periods $M = 1$ and $M = 2$:** Formal Ramanujan ODEs for $(E_2, E_4, E_6)$ in `PowerSeries ℂ` establish that for every period-$1$ and period-$2$ quasipolynomial $P$, $H_P(q)$ and $G_P(q)$ are D-algebraic over $\mathbb{C}(q)$ **if and only if** $P^- \equiv 0$. Note the structural distinction: when $P^- \equiv 0$, it is the **logarithmic derivative** $H_P(q)$ that is (quasi)modular (a linear combination of Eisenstein series); the Euler product $G_P(q)$ itself is therefore D-algebraic (Liouvillian over modular forms), though for degree $D \ge 2$ it is not modular (e.g., $Z_{S^3}(q) = \prod_{n \ge 1}(1-q^n)^{-n^2}$ has $\theta \log Z_{S^3} = (E_4 - 1)/240$ and grows as $\exp(\frac{\pi^4}{45 u^3})$ as $q = e^{-u} \to 1^-$).
- **All-dimension conformal scalar on $S^s$ ($\forall s \ge 2$):** The thermal Lambert series and partition function $Z_{S^s}(q)$ of a free conformally coupled scalar on $S^s$ are D-algebraic over $\mathbb{C}(q)$ **if and only if $s$ is odd**.
- **Unconditional 3-tuple joint differential independence over $\mathbb{C}(q)$:** MacMahon's plane-partition product $M(q) = \prod (1 - q^n)^{-n}$, partitions into parts $\equiv 1 \bmod 5$, and partitions into parts $\equiv 2 \bmod 5$ are jointly differentially independent over $\mathbb{C}(q)$.

## Not Formalized in v3.0.0

- **General-period ($M \ge 3$) converse in Lean:** For even quasipolynomials of arbitrary period $M \ge 3$, D-algebraicity follows classically from level-$M$ Eisenstein series (Klein, Schoeneberg, Robins) and finite-dimensionality of modular rings; only periods $M = 1$ and $M = 2$ (plus concrete higher-period controls such as non-multiples of 5) have their converse formalized in Lean in `v3.0.0`.
- **Priority / literature check:** Classical cases ($w(n) = n$ MacMahon/Chowla–Chowla, $w(n) = 1$ Dedekind $\eta$, Eisenstein parity rules) are classical; an external priority check on the general quasipolynomial parity formulation is underway.
