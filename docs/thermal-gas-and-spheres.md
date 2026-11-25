# Scope Note: Relativistic Quantum Gases, Equations of State, Casimir, and Spheres

**Statement spec:** [`Statements/ThermalGasAndSpheres.lean`](../Statements/ThermalGasAndSpheres.lean)  
**Proof modules:** [`PakPrimes/ThermalGasParity.lean`](../PakPrimes/ThermalGasParity.lean), [`PakPrimes/ThermalGasEOS.lean`](../PakPrimes/ThermalGasEOS.lean), [`PakPrimes/QuasipolynomialIFF.lean`](../PakPrimes/QuasipolynomialIFF.lean)

## Formalized in Lean 4 (v3.0.0)

- **Relativistic ideal gas dimensional parity ($\mu = 0$, $m > 0$):** For both Bose and Fermi statistics, the thermal pressure $P_d(T)$ satisfies an explicit order-3 polynomial ADE in spatial dimension $d = 2$ (D-algebraic), while $P_1(T)$ and $P_3(T)$ satisfy no nonzero algebraic differential equation over $\mathbb{C}(T)$ (D-transcendental).
- **Equations of state $P(\varepsilon)$ and squared sound speeds $c_s^2(\varepsilon) = P'(\varepsilon)$:** In $d = 1$ and $d = 3$, both the relativistic Bose and relativistic Fermi equations of state and sound speeds satisfy no nonzero ADE over $\mathbb{C}(\varepsilon)$, with positivity of entropy and heat capacity proved unconditionally inside Lean (zero auxiliary derivative hypotheses).
- **Massive Casimir energy & force parity:** In $d = 2$ spatial dimensions, the massive scalar Casimir energy and force satisfy explicit polynomial ADEs; in $d = 1$ and $d = 3$, neither satisfies any nonzero ADE over $\mathbb{C}(L)$.
- **Free conformal scalar on $S^s$ ($\forall s \ge 2$):** Explicit proofs for $S^1, S^2, S^3$ in `ThermalGasEOS.lean` and the general all-dimension theorem in `QuasipolynomialIFF.lean` proving $Z_{S^s}$ is D-algebraic iff $s$ is odd. **Variable convention:** the energy levels on $S^s$ are $E_\ell = \ell + (s-1)/2$, so indexing by the integer $j = 2E_\ell = 2\ell + s - 1$ writes the partition function in the variable $x = q^{1/2}$ (so $x^2 = q$ is the physical Boltzmann factor $e^{-\beta}$). Passing between $q$ and $x = q^{1/2}$ is an algebraic change of variable and preserves D-algebraicity over $\mathbb{C}(q)$.

## Not Formalized in v3.0.0

- **Nonzero chemical potential ($\mu \neq 0$, BEC critical line $\mu = m$, Fermi surface $\mu > m$):** Verified analytically and numerically to 62 digits in the research archive, not yet formalized in Lean.
- **Interacting 1+1D TBA models (Lee–Yang, sinh-Gordon):** Analyzed on paper; not formalized in Lean.
