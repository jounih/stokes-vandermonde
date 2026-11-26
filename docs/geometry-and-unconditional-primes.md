# Scope Note: 3D/2D Hyperbolic Selberg, All-CROSS Spectral Parity & Heat Traces, and Elementary RH-Independent Prime Moments

**Audit ledgers:** [`Statements/SelbergHyperbolic.lean`](../Statements/SelbergHyperbolic.lean) · [`Statements/RankOneSymmetric.lean`](../Statements/RankOneSymmetric.lean) · [`Statements/UnconditionalPrimes.lean`](../Statements/UnconditionalPrimes.lean)  
**Full proofs:** [`PakPrimes/SelbergHyperbolic3DDTrans.lean`](../PakPrimes/SelbergHyperbolic3DDTrans.lean) (`1,386` lines) · [`PakPrimes/SelbergHyperbolicDTrans.lean`](../PakPrimes/SelbergHyperbolicDTrans.lean) (`1,393` lines) · [`PakPrimes/RankOneSymmetricParity.lean`](../PakPrimes/RankOneSymmetricParity.lean) (`7,281` lines) · [`PakPrimes/UnconditionalPrimeDTrans.lean`](../PakPrimes/UnconditionalPrimeDTrans.lean) (`2,320` lines)

---

## 1. 3D & 2D Compact Hyperbolic Selberg–Stokes–Vandermonde (`Statements/SelbergHyperbolic.lean`)

### What Is Formalized
- **3D compact orientable hyperbolic manifolds $M = \mathbb{H}^3 / \Gamma$ (`SelbergHyperbolic3DDTrans.lean`):**
  - Takes the explicit analytic input structure `CompactHyperbolic3DSelbergData` encapsulating the classical Selberg zeta function $Z_\Gamma^{3\mathrm{D}}$: entirety of $Z$, self-adjoint 3D Selberg RH (every non-real zero lies on $\mathrm{Re}\,s = 1$), finite real zeros in $[0, 2]$ with **zero trivial zeros anywhere in $\mathbb{C}$**, Weyl infinitude of distinct critical-line zeros $1 + i r$ ($r > 0$), uniform right-half-plane bound on $\mathrm{Re}\,s \ge 3$, and the pure-polynomial reflection law
    $$\frac{Z'(2-s)}{Z(2-s)} + \frac{Z'(s)}{Z(s)} = \frac{\mathrm{Vol}(M)}{\pi}(s-1)^2,$$
    equivalently at $s = 1 + \xi$: $Z'(1-\xi)/Z(1-\xi) + Z'(1+\xi)/Z(1+\xi) = +\frac{\mathrm{Vol}(M)}{\pi}\xi^2$ (`selberg3D_func_eq_critical_shift`).
  - Because the 3D reflection factor is a pure polynomial $+\frac{\mathrm{Vol}(M)}{\pi}\xi^2$ with **zero trivial zeros**, the infinitely many critical-line spectral poles at $\xi = i r_n$ (of arbitrary multiplicity, with zero eigenvalue-simplicity assumption) drive 100% of the Stokes–Vandermonde proof along the rotated ray $\theta_0 = \pi/2$.
  - Proves strong differential transcendence over convergent meromorphic germs $\mathbb{C}(\{t\})$ of `ogfOfEGF (phiSelberg3D D)` and `formalSeries (phiSelberg3D D)`, together with $\mathbb{C}\{1/u\}$ and $\mathbb{C}(u)$ analytic ADE obstructions for `G_Selberg3D_laplace D`.
- **2D compact hyperbolic surfaces $M = \mathbb{H}^2 / \Gamma$ of genus $g \ge 2$ (`SelbergHyperbolicDTrans.lean`):**
  - Takes the analogous analytic input structure `CompactHyperbolicSelbergData` (self-adjoint Selberg RH on $\mathrm{Re}\,s = 1/2$, finite small real zeros in $(0, 1]$, Weyl infinitude, right-half-plane bound on $\mathrm{Re}\,s \ge 3/2$, and exact cotangent reflection law), derives the shifted functional equation $(2g - 2)\cdot 2\pi\xi \tan(\pi\xi)$ (`func_eq_critical_shift`), and proves the exact same strong $\mathbb{C}(\{t\})$, $\mathbb{C}\{1/u\}$, and $\mathbb{C}(u)$ D-transcendence theorems along $\theta_0 = \pi/2$ (which automatically avoids the negative-real-axis trivial zeros of $Z_\Gamma^{2\mathrm{D}}$).

### What Is NOT Formalized Here
- Constructing a concrete instance of `CompactHyperbolic3DSelbergData` or `CompactHyperbolicSelbergData` from a cocompact Kleinian group $\Gamma \subset \mathrm{PSL}_2(\mathbb{C})$ or Fuchsian group $\Gamma \subset \mathrm{PSL}_2(\mathbb{R})$ via the Selberg trace formula is **not** formalized inside Lean; those classical analytic properties of $Z_\Gamma$ are bundled explicitly as fields of the data structures.

---

## 2. All-CROSS Spectral Parity, Wave-EGF, ADE 3-Manifolds, & Unconditional Heat Traces (`Statements/RankOneSymmetric.lean`)

### What Is Formalized
1. **Complete Cartan CROSS Bosonic Euler-Product Classification (`cross_simplyConnected_dAlg_iff`, `cross_all_dAlg_iff`):**
   - Across all simply connected compact rank-1 symmetric spaces ($S^s$, $\mathbb{C}\mathbb{P}^n$, $\mathbb{H}\mathbb{P}^n$, $\mathbb{O}\mathbb{P}^2$), the conformal bosonic Euler product is D-algebraic over $\mathbb{C}(q)$ **if and only if $M$ is an odd sphere $S^{2r+1}$**.
   - Including non-simply-connected $\mathbb{R}\mathbb{P}^s$, across **all** compact rank-1 symmetric spaces the bosonic Euler product is D-algebraic over $\mathbb{C}(q)$ **if and only if $\dim_{\mathbb{R}} M$ is odd** (uniquely $S^{2r+1}$ and $\mathbb{R}\mathbb{P}^{2r+1}$).
2. **Unconditional Strong $\mathbb{C}(\{t\})$ Wave-EGF D-Transcendence:**
   - Proves unconditional strong differential transcendence over convergent meromorphic germs $\mathbb{C}(\{t\})$ of `ogfOfEGF` for the regularized wave EGF across all four even-dimensional simply connected CROSS families (`evenSphere_waveEGF_ogf_stronglyDTrans`, `cpn_waveEGF_ogf_stronglyDTrans`, `hpn_waveEGF_ogf_stronglyDTrans`, `op2_waveEGF_ogf_stronglyDTrans`), along with exact integer leading Borel pole coefficients ($2$, $\binom{2n}{n}$, Catalan $C_{2n}$, and $78$).
3. **ADE Spherical 3-Manifolds ($S^3 / I^*$, $S^3 / O^*$, $S^3 / T^*$, $S^3 / D_m^*$):**
   - Proves exact formal `PowerSeries ℂ` Molien identities for all four binary polyhedral families (`poincareSphere_molien_identity`, `octahedralSphere_molien_identity`, `tetrahedralSphere_molien_identity`, `binaryDihedralSphere_molien_identity`) and universal palindromic Gorenstein even parity (`adeSphere3QP_oddPart_eq_zero`, `adeSphere3QP_borelAmp_eq_zero`, and all specialized `oddPart = 0` / `borelAmp = 0` theorems).
   - **Important distinction on $S^3 / I^*$:** The classical spherical-harmonic multiplicity quasipolynomial $b_{I^*}(u) = u \cdot c_{I^*}(u - 1)$ on the Poincaré homology sphere has strict **even** parity (`oddPart = 0`, period $60$), and is a different mathematical object from the **odd** periodic character $\chi_{60}$ governing the quantum WRT invariant / Lawrence–Zagier false theta function of $S^3 / I^*$.
4. **Unconditional All-CROSS Heat-Trace D-Transcendence over $\mathbb{C}(t)$:**
   - Proves unconditional differential transcendence over $\mathbb{C}(t)$ as $t \to 0^+$ of the two base spectral heat traces `baseHeatInt` ($\sum_{n \ge 1} n e^{-t n^2}$) and `baseHeatHalf` ($\sum_{k \ge 0} (k + 1/2) e^{-t (k + 1/2)^2}$) via half-integer Abel branch-point resurgence (`baseHeatInt_no_rat_ade`, `baseHeatHalf_no_rat_ade`).
   - Reduces every even-dimensional simply connected CROSS shifted spectral heat trace via exact constant-coefficient linear differential operators $H_M(t) = P_M(-\partial_t) H_{\mathrm{base}}(t)$ and differential-operator ADE transfer, yielding unconditional $\mathbb{C}(t)$-D-transcendence for every even sphere $S^{2d}$, $\mathbb{C}\mathbb{P}^n$, $\mathbb{H}\mathbb{P}^n$, and $\mathbb{O}\mathbb{P}^2$ (`evenCROSS_heatTrace_no_rat_ade`, `evenSphere_heatTrace_no_rat_ade`, `cpn_heatTrace_no_rat_ade`, `hpn_heatTrace_no_rat_ade`, `op2_heatTrace_no_rat_ade`).

### What Is NOT Formalized Here
- The Weyl multiplicity polynomials and ADE Molien series are defined directly from their classical closed-form expressions rather than derived inside Lean from representation theory on $L^2(M)$ or Molien's invariant-ring theorem.
- For the higher-period ADE spherical 3-manifolds ($M \in \{12, 24, 60, 4m\}$), vanishing of `oddPart` and `borelAmp` removes the odd-parity Stokes obstruction; explicit higher-level modular D-algebraicity witnesses over $\mathbb{C}(q)$ are not formalized here.
- The heat-trace theorems establish differential transcendence over rational functions $\mathbb{C}(t)$ as $t \to 0^+$ (not strong $\mathbb{C}(\{t\})$ D-transcendence of the heat traces).

---

## 3. Elementary RH-Independent Prime Von Mangoldt Moments (`Statements/UnconditionalPrimes.lean`)

### What Is Formalized
- **100% elementary and completely independent of RH/GRH**, Hardy's infinitude of critical-line zeros, or any numerical zero table.
- **Asymmetric basepoint $s_0 = 2$ (literal convergent von Mangoldt moments):**
  - Defines `phiLambdaAtTwo w = -ζ'(2 + w) / ζ(2 + w)` and proves `phiLambdaAtTwo_eq_LSeries_vonMangoldt`, identifying it on $\mathrm{Re}\,w > -1$ with the literal Dirichlet series $\sum_{m \ge 1} \Lambda(m) m^{-(2 + w)}$ (whose $n$-th Taylor coefficient at $w = 0$ is literally $(-1)^n \sum_{m \ge 2} \Lambda(m) (\log m)^n / m^2$, and where central reflection $w \mapsto -w$ does not cancel $-\zeta'/\zeta$).
  - Proves unconditional strong $\mathbb{C}(\{t\})$ D-transcendence of `ogfOfEGF phiLambdaAtTwo` and `formalSeries phiLambdaAtTwo`, and unconditional $\mathbb{C}\{1/u\}$ and $\mathbb{C}(u)$ analytic ADE obstructions for `G_Lambda_atTwo_laplace`.
- **Critical-line basepoint $s_0 = 1/2$ (`G_Lambda`):**
  - Proves an elementary 2nd-difference Euler-accelerated Dirichlet $\eta$ nonvanishing certificate `riemannZeta_ne_zero_on_box` showing $\zeta(s) \neq 0$ on the closed box $[0, 1] \times [-1/2, 1/2]$ (away from $s = 1$), enabling the negative-real-axis trivial-zero Stokes ray $\theta_0 = \pi$ to clear the critical strip completely without any assumption on nontrivial zeros.
  - Proves unconditional strong $\mathbb{C}(\{t\})$ D-transcendence of `ogfOfEGF phiLambda` and `G_Lambda = formalSeries phiLambda`, plus $\mathbb{C}\{1/u\}$ and $\mathbb{C}(u)$ analytic ADE obstructions for `G_Lambda_laplace`.

### Scope & Methodological Distinction vs. `Statements/HigherOrderStrongAndRH.lean`
- `UnconditionalPrimeDTrans.lean` extracts Stokes jumps along the negative real ray $\theta_0 = \pi$ from the simple trivial zeros $s = -2(m+1)$ (and the pole $s = 1$ at $s_0 = 2$), making the proof completely elementary and independent of nontrivial zeros.
- `RiemannHypothesisStokes.lean` / `HigherOrderStrongAndRH.lean` (`v3.2.0`) is retained separately as an independent proof route extracting Stokes jumps along the imaginary axis $\theta_0 = \pi/2$ directly from critical-line zeros under the explicit hypothesis `RiemannHypothesis ∧ InfinitelyManyCriticalLineZeros`.
