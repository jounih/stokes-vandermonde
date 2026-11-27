# Scope Note: All-$d$ Marked-Wave Engine, Unconditional Partitions into Squares $P_2(q)$, Jump-Point Multivariate Engine, & 3D/1D Ideal Quantum Gases (`v3.5.0`–`v3.6.0`)

**Root module:** [`PakStokesAllD.lean`](../PakStokesAllD.lean)  
**Full proofs (`22,898` lines across 13 modules):**
- **Wave 8 (`6,257` lines, `v3.5.0`):** [`BesicovitchCore.lean`](../PakStokes/AllD/BesicovitchCore.lean) (`688` lines) · [`UniversalThimble.lean`](../PakStokes/AllD/UniversalThimble.lean) (`691` lines) · [`ExtremeRayProjection.lean`](../PakStokes/AllD/ExtremeRayProjection.lean) (`953` lines) · [`AllDFormalTransfer.lean`](../PakStokes/AllD/AllDFormalTransfer.lean) (`1,138` lines) · [`TrackedWaves.lean`](../PakStokes/AllD/TrackedWaves.lean) (`981` lines) · [`AllDThetaDTrans.lean`](../PakStokes/AllD/AllDThetaDTrans.lean) (`1,806` lines)
- **Wave 9 (`6,810` lines, `v3.5.0`):** [`SquaresPartitionAnalytic.lean`](../PakStokes/AllD/SquaresPartitionAnalytic.lean) (`1,676` lines) · [`PowerPartitions.lean`](../PakStokes/AllD/PowerPartitions.lean) (`5,134` lines)
- **Wave 10 (`1,516` lines, `v3.5.0`):** [`JumpPointMultivariate.lean`](../PakStokes/AllD/JumpPointMultivariate.lean) (`1,516` lines)
- **Wave 11 (`8,230` lines, `v3.6.0`):** [`SquareQuotientsAndDivisors.lean`](../PakStokes/AllD/SquareQuotientsAndDivisors.lean) (`3,079` lines) · [`Bec3DAnalytic.lean`](../PakStokes/AllD/Bec3DAnalytic.lean) (`3,003` lines) · [`Bec3DDiffTrans.lean`](../PakStokes/AllD/Bec3DDiffTrans.lean) (`2,148` lines)
- **Root aggregator (`85` lines):** [`PakStokesAllD.lean`](../PakStokesAllD.lean)

*(Transitive base cubic-theta infrastructure: 36 unmodified modules from [`jounih/pak-cubic-theta@6a1cfe5a`](https://github.com/jounih/pak-cubic-theta/tree/6a1cfe5adb4d4e533b7ca7703120cdea09ebe2fa) vendored under [`vendor/pak-cubic-theta/`](../vendor/pak-cubic-theta/), audited by CI and replayed from scratch by `leanchecker --fresh PakStokesAllD`.)*

---

## 1. Wave 8: All-$d$ Marked-Wave Engine & Unconditional Cubic Waring/Dilations (`PakStokes/AllD/{BesicovitchCore,UniversalThimble,ExtremeRayProjection,AllDFormalTransfer,TrackedWaves,AllDThetaDTrans}.lean`)

### What Is Proved 100% Unconditionally from Mathlib (Plus Vendored `PakStokes` at $d = 3$)
1. **Unconditional All-$d$ Algebraic & Geometric Foundations:**
   - **Besicovitch's Theorem (1940) for all $r \ge 2$** (`besicovitch_rfree_linearIndependent`): elementary normalized-trace proof of $\mathbb{Q}$-linear independence of $r$-free real radicals $b^{1/r}$, giving $\mathbb{Q}$-linear independence of distinct prime-power actions $k^{d/(d-1)}$ ($d \ge 3$) and zero-tilt injectivity of `ActionKey d → ℂ`.
   - **Critical-Value-Free Left Half-Plane Theorem** (`universalPoly_no_nonzero_critValue_in_LHP`): for every $d \ge 3$, zero nonzero critical values of $P_d(w) = w^d - dw + (d-1)$ lie in $\{\mathrm{Re}\,\zeta \le 0\}$, together with exact upper half-plane saddle counts ($d/2$ for even $d$, $2 \lfloor(d+1)/4\rfloor$ for odd $d$), rotated phase identity, and Beta-averaged kernel bounds.
   - **Extreme-Ray Projection & Generalized Marked Jacobian** (`extremeRay_face_iff`, `extremeRayProj`, `independent_of_marked_jacobian_domain`): projects active-half-space expansions onto the extreme ray $\mathcal{E}_d = \mathbb{R}_{\ge 0} A_0(d)$ and proves algebraic independence over any characteristic-zero domain whenever the marked Jacobian determinant is a non-zero-divisor (not just a unit).
   - **Formal Transfer & Waring Lifting** (`allD_formal_transfer`, `waring_algebraicIndependent_of_base`, `iterQDeriv_eq_sum`): connects real-ray expansions to formal power series $\Theta_d(q) = \sum_{n \ge 0} q^{n^d}$, dilations $\Theta_d(q^a)$, and Waring powers $\Theta_d(q)^k$.
2. **Unconditional Cubic ($d = 3$) Flagship Theorems (ZERO External Hypotheses):**
   - Instantiated via the concrete witness `stokesProfileThree : AllDStokesProfile 3 (by decide)` built directly from the kernel-checked cubic-theta modules:
     - `theta_3_non_ade_via_allD`: $\Theta_3(q)$ satisfies no nontrivial ADE over $\mathbb{C}(q)$;
     - `theta_3_waring_power_non_ade`: **every cubic Waring power** $\Theta_3(q)^k$ ($k \ge 1$) satisfies no nontrivial ADE over $\mathbb{C}(q)$;
     - `theta_3_dilations_diff_indep`: **every finite family of distinct positive-integer cubic dilations** $\{\Theta_3(q^{a_1}), \dots, \Theta_3(q^{a_s})\}$ ($a : \mathrm{Fin}\,s \to \mathbb{N}_+$ injective) is jointly differentially independent over $\mathbb{C}(q)$.

### Explicitly Parameterized Scope Boundary for General $d \ge 4$
- The general all-$d$ ($d \ge 3$) master theorems (`theta_d_marked_wave_non_ade`, `theta_d_waring_power_non_ade`, `theta_d_dilations_diff_indep`, `theta_d_dfree_dilations_diff_indep`) take an analytic input package `P : AllDStokesProfile d hd` encoding the steepest-descent + Beta-averaged `RayDensity` decomposition of `regularThetaD d` on $p > 0$.
- **Honesty boundary:** `AllDStokesProfile` is currently instantiated unconditionally in Lean **only at $d = 3$** (`stokesProfileThree`). Constructing the analytic contour-deformation steepest-descent profile `AllDStokesProfile d hd` for $d \ge 4$ inside Lean remains open future work.

---

## 2. Wave 9: 100% Unconditional Partitions into Squares $P_2(q)$ & All-$d$ Power Partitions (`SquaresPartitionAnalytic.lean`, `PowerPartitions.lean`)

### What Is Proved 100% Unconditionally from Mathlib (ZERO External Hypotheses!)
1. **Exact Closed-Form Poisson-Summation / Cotangent-Residue Identity for $d = 2$** (`squares_partition_analytic_identity`):
   - Proved directly from Mathlib's Fourier inversion and Poisson summation: for every $X > 0$,
     $$2 X^{-3} \sum_{n=1}^{\infty} \frac{n^2}{e^{n^2/X^2} - 1} = C_2 - X^{-1} - \sum_{k=1}^{\infty}\sum_{m=1}^{\infty} \sqrt{m}\bigl(A_0 e^{-A_0 k\sqrt{m}\,X} + A_1 e^{-A_1 k\sqrt{m}\,X}\bigr),$$
     discharging `powerPartStokesProfileTwo : PowerPartStokesProfile 2 (by decide)` completely inside Lean with zero external assumptions.
2. **100% Unconditional Partitions-into-Squares Flagship Theorems ($d = 2$):**
   Let $P_2(q) = \prod_{n \ge 1}(1 - q^{n^2})^{-1}$ be the generating function of **partitions into squares**, and $F_2(q) = q P_2'(q)/P_2(q) = \sum_{n \ge 1} n^2 q^{n^2}/(1 - q^{n^2})$ its logarithmic derivative. With **ZERO external hypotheses**:
   - `logDerivPowerPart_2_non_ade`: $F_2(q)$ satisfies no nontrivial ADE over $\mathbb{C}(q)$;
   - `powerPart_2_non_ade`: **$P_2(q)$ satisfies no nontrivial ADE over $\mathbb{C}(q)$**;
   - `powerPart_2_zpow_non_ade`: **every nonzero integer power $P_2(q)^k$ ($k \in \mathbb{Z} \setminus \{0\}$)** satisfies no nontrivial ADE over $\mathbb{C}(q)$ (including $P_2(q)^{-1} = \prod_{n \ge 1}(1 - q^{n^2})$);
   - `logDerivPowerPart_2_dilations_diff_indep` & `powerPart_2_dilations_diff_indep`: for **every finite family of distinct positive integers** $a_1, \dots, a_s \in \mathbb{N}_+$, the dilated square-partition products $\{P_2(q^{a_1}), \dots, P_2(q^{a_s})\}$ (and their log-derivatives $\{F_2(q^{a_i})\}$) are **jointly differentially independent over $\mathbb{C}(q)$**.
3. **Unconditional All-$d$ ($d \ge 2$) Kolchin & Constant-Vandermonde Engine:**
   - Prime multiplicity identity `powerPartMult_prime` ($c_d(p) = 1$ for every prime $p$ and $d \ge 2$), zero-tilt extreme-ray projection onto constant-amplitude expansions, Kolchin logarithmic-derivative transfer, and exact constant $J \times J$ prime Vandermonde non-vanishing.

### Explicitly Parameterized Scope Boundary for $d \ge 3$ Power Partitions
- For general $d \ge 2$, the master theorems (`logDerivPowerPart_non_ade`, `powerPart_non_ade`, `powerPart_zpow_non_ade`, `logDerivPowerPart_dilations_diff_indep`, `powerPart_dilations_diff_indep`) take `P : PowerPartStokesProfile d hd` (a single polar polynomial in $X^{-1}$ plus the pure-exponential wave decomposition of the rescaled log-derivative on $X > 0$).
- **Honesty boundary:** `PowerPartStokesProfile d hd` is instantiated unconditionally in Lean **at $d = 2$** (`powerPartStokesProfileTwo`). Constructing the analytic Poisson/residue decomposition `PowerPartStokesProfile d hd` for $d \ge 3$ (e.g., partitions into cubes $P_3(q)$) inside Lean remains open future work.

---

## 3. Wave 10: Unconditional Algebraic Jump-Point Derivation Engine & Multivariate Diagonal Witnesses (`JumpPointMultivariate.lean`)

### What Is Proved 100% Unconditionally from Mathlib
1. **Jump-Point Existence & Collision Immunity** (`jumpPoints_exist`, `jumpPoint_no_multi_pos_sum`):
   - For any well-founded positive spectrum $A \subset (0, \infty)$ of infinite $\mathbb{Q}$-rank, there exist infinitely many **jump points** $a \in \mathrm{JumpSet}(A)$ (elements lying outside the $\mathbb{Q}$-span of $A \cap (-\infty, a)$).
   - At every jump point, off-ray positive collisions vanish identically (`jumpPoint_no_multi_pos_sum`), bypassing the $s = 2$ off-ray collision obstruction that breaks naive extreme-ray arguments in dimension $m \ge 2$.
2. **Formal Exponential & Transseries Derivation Engine** (`monoidDeriv`, `hahnDeriv`, `monoidDeriv_aeval`, `hahnDeriv_aeval`, `jumpPoint_minimal_relation_vandermonde`, `jumpPoint_transseries_algebraicIndependent`, `jumpPoint_transseries_no_poly_ade`):
   - Proves algebraic independence of all derivatives $(Y, D_X Y, \dots, D_X^{J-1} Y)$ over the full asymptotic coefficient ring `AsympCoeff` (and hence non-existence of any polynomial ADE over $\mathbb{C}[X]$) for any well-ordered positive transseries $Y \in \mathrm{HahnSeries}\,\mathbb{R}\,(\mathrm{HahnSeries}\,\mathbb{R}\,\mathbb{C})$ supported on $A$ with nonzero jump-point amplitudes.
3. **Besicovitch Wulff-Ray Bridge & Concrete Multivariate Non-Vacuity Witnesses** (`wulffRay_infinite_qrank`, `multivariate_evenForm_algebraic_dtrans`, `multivariate_jumpPoint_non_ade`, `multivariate_jumpPoint_non_ade_over_poly`, `diagQuartic2D_offray_collision`, `diagForm_algebraic_dtrans`, `diagForm_transseries_non_ade`, `diagQuartic2D_non_ade`):
   - Connects `BesicovitchCore` Wulff rays $\{c_0 k^{d/(d-1)} : k \ge 1\}$ ($d \ge 3$, arbitrary real $c_0 > 0$) to infinite $\mathbb{Q}$-rank (`wulffRay_infinite_qrank`).
   - Constructs explicit formal diagonal-form transseries `diagFormTransSeries m d` for every dimension $m \ge 1$ and degree $d \ge 3$ with exact positive-Hessian saddle prefactor $X^{m/2}$, explicitly exhibits genuine $s = 2$ off-ray collisions in the 2D quartic spectrum (`diagQuartic2D_offray_collision`), and proves differential transcendence over `AsympCoeff` and $\mathbb{C}[X]$ (`diagForm_transseries_non_ade`, `diagQuartic2D_non_ade`).

### Explicit Scope Boundary for Wave 10
- **Honesty boundary (Formal Transseries vs. Analytic Heat Trace):** Wave 10 is a **100% unconditional algebraic transseries engine**. It proves that the formal transseries $Y$ supported on a well-ordered positive dual action spectrum containing a Wulff ray with nonzero jump-point amplitudes satisfies no nontrivial ADE over `AsympCoeff` or $\mathbb{C}[X]$.
- Connecting this formal transseries engine to a **specific analytic multivariate heat trace** (such as $\sum_{(x,y) \in \mathbb{Z}^2} e^{-t(x^4 + y^4)}$) requires proving the analytic resurgent/asymptotic representation (that a real/analytic ADE satisfied by the heat trace transfers to the formal transseries `diagFormTransSeries m d`, and that the dual saddle contributions match the positive-Hessian amplitudes), which is **not** formalized in Lean in `v3.5.0`–`v3.6.0`.

---

## 4. Wave 11: 100% Unconditional 3D Bose–Einstein Condensate, 3D Fermi–Dirac Gas, Joint 1D+3D Quantum Gases, Square Divisors $L_{2,0}(q)$, & Quotient-Rank Forest (`v3.6.0`)

All results in Wave 11 (`SquareQuotientsAndDivisors.lean`, `Bec3DAnalytic.lean`, `Bec3DDiffTrans.lean` — `8,230` lines total) are proved **100% unconditionally from Mathlib** (zero custom axioms, zero external analytic hypotheses, zero Bessel/Mellin/contour assumptions beyond Mathlib).

### What Is Proved 100% Unconditionally from Mathlib
1. **General Multiplicative Quotient-Rank Transfer & Square-Partition Forest (`SquareQuotientsAndDivisors.lean`):**
   - `monomial_family_diff_indep_of_logDeriv` & `distinctSource_quotient_pow_diff_indep`: for any family of units $U_j \in \mathbb{C}[[q]]^\times$ whose log-derivatives $F_j$ are jointly differentially independent over $\mathbb{C}(q)$ and any integer matrix $M \in \mathbb{Z}^{r \times n}$ with $\mathbb{Q}$-linearly independent rows, the Laurent monomials $Y_i = \prod_j U_j^{M_{ij}}$ are jointly differentially independent over $\mathbb{C}(q)$.
   - Applied unconditionally to Wave 9's square-partition dilations $\{P_2(q^a)\}$:
     - `squarePart_monomial_family_diff_indep` (arbitrary full-row-rank integer matrix $M$ on $\{P_2(q^{a_j})\}$);
     - `squarePart_forest_quotients_diff_indep` (any finite edge family $(u_i, v_i)$ with injective $u$ and $u_i < v_i$ gives jointly differentially independent quotients $\{P_2(q^{u_i})/P_2(q^{v_i})\}$);
     - `distinctSquaresPart_eq_eulerProd` ($Q_2(q) = \prod_{n \ge 1}(1 + q^{n^2}) = P_2(q)/P_2(q^2)$), `kRegularSquares_eq_eulerProd`, `overpartSquares_eq_mul` ($\overline{P}_2(q) = P_2(q)^2/P_2(q^2)$);
     - `distinctSquares_non_ade`, `overpartSquares_non_ade`, `distinctSquares_overpartSquares_joint_diff_indep` (joint independence of $(Q_2(q), \overline{P}_2(q))$ over $\mathbb{C}(q)$);
     - `kRegularSquares_dilations_diff_indep`, `distinctSquares_dilations_diff_indep`, `fermi1D_non_ade`, and `fermi1D_dilations_diff_indep` for the 1D periodic-box ideal Fermi–Dirac gas $Z_{\mathrm{FD}}^{(1)}(q) = \prod_{n \in \mathbb{Z}\setminus\{0\}}(1 + q^{n^2}) = Q_2(q)^2$.
2. **Unified `d = 2` Zero-Tilt Engine (`SqRayProfile`) & Square-Divisor Series $L_{2,0}(q)$ (`SquareQuotientsAndDivisors.lean`):**
   - `sqRayProfile_dilations_diff_indep` & `sqRayProfile_non_ade`: reusable $d = 2$ zero-tilt wave-profile engine for any formal series $F \in \mathbb{C}[[q]]$ with polynomial coefficient growth and elementary Stokes waves along `{sqRay0, sqRay1}` having non-vanishing prime extreme-ray amplitudes.
   - `squareDivisor_analytic_identity`: exact 1-term elementary Poisson-summation identity on $X > 0$ for $\sum_{n \ge 1} (e^{n^2/X^2} - 1)^{-1} = L_{2,0}(e^{-1/X^2})$.
   - `squareDivisor_non_ade` & `squareDivisor_dilations_diff_indep`: the square-divisor generating function $L_{2,0}(q) = \sum_{N \ge 1} d_{\square}(N) q^N$ ($d_{\square}(N) = \#\{n \ge 1 : n^2 \mid N\}$) and every finite family of distinct positive-integer dilations $\{L_{2,0}(q^{a_i})\}$ are differentially transcendental / jointly differentially independent over $\mathbb{C}(q)$.
3. **Physical 3D Ideal Bose–Einstein Condensate & 3D Ideal Fermi–Dirac Gas (`Bec3DAnalytic.lean`, `Bec3DDiffTrans.lean`):**
   - Let $r_3(N) = \#\{(a,b,c) \in \mathbb{Z}^3 : a^2 + b^2 + c^2 = N\}$, $Z_{\mathrm{BEC}}^{(3)}(q) = \prod_{n \in \mathbb{Z}^3 \setminus \{0\}}(1 - q^{|n|^2})^{-1} = \prod_{N \ge 1}(1 - q^N)^{-r_3(N)}$, $F_{\mathrm{BEC}}^{(3)}(q) = q \frac{d}{dq} \log Z_{\mathrm{BEC}}^{(3)}(q)$, and $Z_{\mathrm{FD}}^{(3)}(q) = Z_{\mathrm{BEC}}^{(3)}(q)/Z_{\mathrm{BEC}}^{(3)}(q^2) = \prod_{n \in \mathbb{Z}^3 \setminus \{0\}}(1 + q^{|n|^2})$ (verified by `fermi3DSeries_eq_eulerProd`).
   - `bec3D_analytic_identity`: exact closed-form 3D iterated Poisson summation + elementary $K_{1/2}$ Gaussian integral identity on $X > 0$:
     $$\sum_{N=1}^{\infty} \frac{r_3(N)\,N}{e^{N/X^2} - 1} = C_{\mathrm{BEC}}^{(3)} X^5 - X^2 + X^4 \sum_{d=1}^{\infty}\sum_{j=1}^{\infty} \frac{r_3(d)\,j}{\sqrt{d}}\bigl(-2\pi^2 i\,e^{-A_0 \sqrt{dj}\,X} + 2\pi^2 i\,e^{-A_1 \sqrt{dj}\,X}\bigr).$$
   - Unconditional differential transcendence & joint independence over $\mathbb{C}(q)$:
     - `logDerivBec3D_non_ade`, `logDerivBec3D_dilations_diff_indep`;
     - `bec3D_non_ade`, `bec3D_zpow_non_ade` (every $k \in \mathbb{Z} \setminus \{0\}$), `bec3D_dilations_diff_indep`;
     - `fermi3D_non_ade`, `fermi3D_dilations_diff_indep`;
     - `bec3D_fermi3D_joint_diff_indep` (single-temperature joint differential independence of $(Z_{\mathrm{BEC}}^{(3)}(q), Z_{\mathrm{FD}}^{(3)}(q))$);
     - `bec3D_bose_fermi_quotient_rank` (arbitrary full-row-rank integer matrix $M$ on $\{Z_{\mathrm{BEC}}^{(3)}(q^{a_j})\}$) and `bec3D_forest_quotients_diff_indep`.
4. **Coupled 1D + 3D Ideal Quantum Gases (`Bec3DDiffTrans.lean`):**
   - Combining Legendre's three-square obstruction ($r_3(p) = 0$ for $p \equiv 7 \bmod 8$), Fermat's two-square theorem ($r_3(p) \ge 1$ for $p \equiv 1 \bmod 4$), and Mathlib's Dirichlet theorem on primes in arithmetic progressions (`Nat.forall_exists_prime_gt_and_modEq`), proves exact $(2J) \times (2J)$ prime-block determinant non-vanishing on ray `sqRay0`:
     - `logDeriv_bec1D_bec3D_dilations_diff_indep` & `bec1D_bec3D_dilations_diff_indep`: for any finite injective family $a_1, \dots, a_s \in \mathbb{N}_+$, the $2s$ series $\{P_2(q^{a_i}), Z_{\mathrm{BEC}}^{(3)}(q^{a_i})\}$ are jointly differentially independent over $\mathbb{C}(q)$;
     - `powerPart2_bec3D_joint_diff_indep`: $(P_2(q), Z_{\mathrm{BEC}}^{(3)}(q))$ are jointly differentially independent over $\mathbb{C}(q)$;
     - `bec1D_bec3D_joint_diff_indep`: $(Z_{\mathrm{BEC}}^{(1)}(q), Z_{\mathrm{BEC}}^{(3)}(q))$ are jointly differentially independent over $\mathbb{C}(q)$;
     - `quantumGases_1D_3D_bose_fermi_joint_diff_indep`: **all four** ideal quantum gas partition functions $(Z_{\mathrm{BEC}}^{(1)}(q), Z_{\mathrm{FD}}^{(1)}(q), Z_{\mathrm{BEC}}^{(3)}(q), Z_{\mathrm{FD}}^{(3)}(q))$ are simultaneously jointly differentially independent over $\mathbb{C}(q)$ at a single temperature variable $q$.

### Explicit Scope Boundary for Wave 11
- **What is formalized:** Non-relativistic ideal Bose–Einstein and Fermi–Dirac grand partition functions on periodic cubic boxes $\mathbb{T}^1$ (1D) and $\mathbb{T}^3$ (3D) with discrete quadratic spectrum $|n|^2$ ($n \in \mathbb{Z}^D \setminus \{0\}$) at **unit fugacity $z = 1$** (formal power series in $q = e^{-\beta}$ over $\mathbb{C}(q)$), together with the square-divisor series $L_{2,0}(q)$ and multiplicative Laurent-monomial / forest quotients.
- **What is NOT formalized in Wave 11:** 2D or 4D ideal BEC/Fermi gases on $\mathbb{T}^2$ or $\mathbb{T}^4$, general complex fugacity $z \neq 1$, Dirichlet mod-$N$ character twists, mock theta functions, and analytic hyperbolic heat traces are **not** formalized in Wave 11. Likewise, $d \ge 4$ `AllDStokesProfile` (Wave 8) and $d \ge 3$ `PowerPartStokesProfile` (Wave 9) remain parameterized interfaces.
