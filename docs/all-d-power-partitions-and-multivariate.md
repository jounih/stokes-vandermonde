# Scope Note: All-$d$ Marked-Wave Engine, Unconditional Partitions into Squares $P_2(q)$, & Jump-Point Multivariate Engine (`v3.5.0`)

**Root module:** [`PakStokesAllD.lean`](../PakStokesAllD.lean)  
**Full proofs (`14,643` lines across 10 modules):**
- **Wave 8 (`6,257` lines):** [`BesicovitchCore.lean`](../PakStokes/AllD/BesicovitchCore.lean) (`688` lines) · [`UniversalThimble.lean`](../PakStokes/AllD/UniversalThimble.lean) (`691` lines) · [`ExtremeRayProjection.lean`](../PakStokes/AllD/ExtremeRayProjection.lean) (`953` lines) · [`AllDFormalTransfer.lean`](../PakStokes/AllD/AllDFormalTransfer.lean) (`1,138` lines) · [`TrackedWaves.lean`](../PakStokes/AllD/TrackedWaves.lean) (`981` lines) · [`AllDThetaDTrans.lean`](../PakStokes/AllD/AllDThetaDTrans.lean) (`1,806` lines)
- **Wave 9 (`6,810` lines):** [`SquaresPartitionAnalytic.lean`](../PakStokes/AllD/SquaresPartitionAnalytic.lean) (`1,676` lines) · [`PowerPartitions.lean`](../PakStokes/AllD/PowerPartitions.lean) (`5,134` lines)
- **Wave 10 (`1,516` lines):** [`JumpPointMultivariate.lean`](../PakStokes/AllD/JumpPointMultivariate.lean) (`1,516` lines)
- **Root aggregator (`60` lines):** [`PakStokesAllD.lean`](../PakStokesAllD.lean)

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
- Connecting this formal transseries engine to a **specific analytic multivariate heat trace** (such as $\sum_{(x,y) \in \mathbb{Z}^2} e^{-t(x^4 + y^4)}$) requires proving the analytic resurgent/asymptotic representation (that a real/analytic ADE satisfied by the heat trace transfers to the formal transseries `diagFormTransSeries m d`, and that the dual saddle contributions match the positive-Hessian amplitudes), which is **not** formalized in Lean in `v3.5.0`.
