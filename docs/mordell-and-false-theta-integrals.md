# Scope Note: Mordell, Eichler, and Stieltjes Integrals over `ℂ(u)`

**Statement spec:** [`Statements/MordellAndFalseThetaIntegrals.lean`](../Statements/MordellAndFalseThetaIntegrals.lean)  
**Proof modules:** [`PakPrimes/MockThetaAndHurwitz.lean`](../PakPrimes/MockThetaAndHurwitz.lean), [`PakPrimes/FalseThetaDichotomy.lean`](../PakPrimes/FalseThetaDichotomy.lean), [`PakPrimes/MockModularWeightOne.lean`](../PakPrimes/MockModularWeightOne.lean)

## Formalized in Lean 4 (v3.0.0)

- **Individual D-transcendence over $\mathbb{C}(u)$:** Unconditional Lean 4 proofs that the Mordell integrals associated with Ramanujan's third-order mock theta functions $f$ and $\omega$, the split Eichler integral for Zagier's Hurwitz theta shadow, the sinh and Kontsevich false-theta Mordell integrals, and the Rogers false-theta Stieltjes transform each satisfy no nonzero algebraic differential equation over $\mathbb{C}(u)$.
- **5-tuple joint differential independence over $\mathbb{C}(u)$:** Unconditional multi-function Stokes–Vandermonde proof that the five mock/false Mordell integrals are jointly differentially independent over $\mathbb{C}(u)$.
- **Algebraic Chazy ODE:** Formal derivation of $2 D^3 E_2 - 2 E_2 D^2 E_2 + 3 (D E_2)^2 = 0$ from Ramanujan's differential system for $(E_2, E_4, E_6)$.

## Not Formalized in v3.0.0 (Important Scope Boundary)

- **Literal $q$-series $f(q), \omega(q), H(q), \Psi(q)$ in $\mathbb{C}[[q]]$:** The theorems in `v3.0.0` apply to the **Mordell, Eichler, and Stieltjes integral transforms over $\mathbb{C}(u)$**, not directly to the $q$-series $f(q), \omega(q), H(q), \Psi(q)$ in $\mathbb{C}[[q]]$. Branch-point Stokes machinery and literal $q$-series theorems (including Tier-2 Watson–Zwegers modular transfer for $f(q), \omega(q), H(q)$ and unconditional Gaussian-integral transfer for $\Psi(q)$) are staged separately for `v3.1.0` pending statement-spec review.
