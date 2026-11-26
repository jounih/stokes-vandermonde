module

public import PakPrimes.FiniteContourStokes
public import PakPrimes.UnconditionalPrimeDTrans
public import PakPrimes.SpectralPositivity
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.TaylorSeries

/-! # Unconditional (Zero-RH) Completed-$\xi$ Strong `ℂ({t})` D-Transcendence & RH-Free Cramér Positivity

This module formalizes the completed Riemann $\xi$-function (`completedXi`) and proves two
complementary zero-RH results:

## Part A: 100% Unconditional Theorems Over Mathlib Plus This Repository's Proved Modules (No Extra Hypotheses, ZERO RH)
Every theorem in Sections 1–5 depends on **ZERO** unproven hypotheses, **ZERO** `RiemannHypothesis`,
**ZERO** numerical zero tables, and **ZERO** external axioms (only `[propext, Classical.choice, Quot.sound]`):

1. **Entire Completed $\xi$-Function & Zero-Free Horizontal Strip (`completedXi_ne_zero_of_abs_im_le_half`)**:
   Defining `completedXi s := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2`, we prove directly from
   Mathlib plus this repository's proved modules (with no extra hypotheses) that `completedXi` is
   entire, satisfies `completedXi (1 - s) = completedXi s`, agrees with
   `(1/2) * s * (s - 1) * completedRiemannZeta s` away from `{0, 1}`, and is nonzero on
   `{s | s.re ≤ 0} ∪ {s | 1 ≤ s.re} ∪ ([0, 1] × [-1/2, 1/2])` — hence on the entire horizontal strip
   `{s : ℂ | |s.im| ≤ 1 / 2}` (and in particular at every real point `c : ℝ`).
2. **Unconditional Infinitude of Nontrivial Zeros (`completedXi_zeros_infinite`)**:
   Proved directly from Mathlib plus this repository's proved modules, with no extra hypotheses
   (without Stirling's formula, Hadamard factorization, or Riemann–von Mangoldt):
   - The Jacobi-theta Mellin representation `completedRiemannZeta₀ s = (hurwitzEvenFEPair 0).Λ₀ (s/2) / 2`
     splits symmetrically via `mellin_comp_rpow` and geometric-series bounds on `cosKernel 0 t - 1`
     to give an explicit global upper bound `‖completedXi z‖ ≤ (2 * R) ^ (Nat.ceil R + 4)` on
     `‖z‖ ≤ R` (`R ≥ 4`).
   - Assuming finitely many zeros, we factor them out as `completedXi z = P z * exp (h z)` using
     `Complex.exists_continuousOn_eqOn_exp_comp`, apply Maximum Modulus + `Complex.borelCaratheodory`
     + `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` to show `iteratedDeriv k h 0 = 0`
     for all `k ≥ 2` (so `h` is affine `A + B * z`), and contradict the exact factorial lower bound
     `‖completedXi (2 * n)‖ ≥ (n - 1)! / π ^ n` from `completedZeta_eq_tsum_of_one_lt_re` and
     `Complex.Gamma_nat_eq_factorial`.
3. **Unconditional Strong `ℂ({t})` D-Transcendence at Every Real Center (`completedXi_ogf_stronglyDTrans`,
   `completedXi_formalSeries_stronglyDTrans`)**:
   Instantiating `FiniteContourStokes.entireLogDeriv_ogf_stronglyDTrans` on `phiXiAt c w := -ξ'(c + w) / ξ(c + w)`
   yields zero-RH strong `ℂ({t})` differential transcendence in the formal variable `t = 1/u` for
   the factorial-moment / formal-Laplace series of `-ξ'/ξ` at every real center `c : ℝ` (including
   `c = 1/2`). Note that these theorems are in `t = 1/u` for the factorial-moment / formal-Laplace
   series of `-ξ'/ξ`, NOT for `ζ(s)` directly as a function of `s`.
4. **Unconditional Joint Multi-Center Differential Independence (`completedXi_joint_ogf_stronglyDTrans`)**:
   For ANY finite family of pairwise distinct real centers `c : Fin d → ℝ`, the left-extremal
   accumulation abscissa `L = sSup {x | {ρ ∈ Z_ξ | ρ.re < x}.Finite}` yields infinitely many zeros
   in `[L - ε, L + ε)` avoiding all shifted bad bands, producing a block upper-triangular
   Vandermonde matrix of nonzero determinant and hence joint differential independence in `t = 1/u`
   over `ℂ({t})` for the factorial-moment / formal-Laplace series of `-ξ'(c_i + w)/ξ(c_i + w)`.
5. **Unconditional Real-Axis Laplace Integral ADE Obstruction (`completedXi_laplace_no_conv_ade`)**:
   Using the zero-free strip `{|w.im| ≤ 1/2}` and `phiLambda_expType_pos_real_unconditional` + Gamma
   recurrence `Γ(y + 1) = y Γ(y)`, the actual real-axis Laplace integral `B_xi c u` has full
   `1/u`-asymptotic expansion `formalSeries (phiXiAt c)` and satisfies no nontrivial convergent-germ
   ADE over `ℂ{1/u}` at any real center `c : ℝ` (again in `u` / `1/u`, not for `ζ(s)` in `s`).

## Part B: RH-Free Cramér Positivity & Strict Hankel Positive Definiteness (via `PakPrimes.SpectralPositivity`)
Section 6 specializes the unified spectral-positivity and Hankel positive-definiteness interface
of `PakPrimes.SpectralPositivity` (integrating Codex's `PositiveDensity.lean` theorems
`xi_lower_from_estimates`, `square_integral_pos`, and `hankel_form`) to the `(15, 20, 1)` parameter
regime via `CramerLowZeroData := SpectralLowZeroData 15 20 1`.

**Scope transparency**: Every theorem in Section 6 is **explicitly parameterized** by
`CramerLowZeroData := SpectralLowZeroData 15 20 1`, recording ONLY a lead real ordinate
`0 < γ₁ ≤ 15`, an optional finite list `γ_low : List ℝ` of additional positive critical-line
low ordinates (`[]` for Riemann $\xi$), tail zeros with `Re γ ≥ 20` and `|Im γ| < 1/2`, and
the convergent weight bound `∑ (4 + (Re γ)²)⁻¹ < 1` — with **NO `RiemannHypothesis` assumed**
(`Im γ` may take arbitrary values in `(-1/2, 1/2)`).

**Honesty boundary**: The structure is NOT connected in Lean to the zeros of `completedXi`,
$L(s, \chi_{-4})$, or $L(s, \Delta)$. That $\gamma_1, \gamma_{\mathrm{low}}, \gamma_{\mathrm{tail}}$
enumerate exactly those zeros with multiplicity, the low-height verification, the Hadamard bound
$\sum (4 + (\operatorname{Re}\gamma)^2)^{-1} < C$, and the identity relating `spectralMoment` to
the Taylor coefficients of $\xi'/\xi$ are all external. The theorems hold for any data satisfying
the fields.

The exact same unified `PakPrimes.SpectralPositivity` interface simultaneously covers:
- Dirichlet $\beta$ (`SpectralLowZeroData 7 16 10`, with `γ_low` holding the additional low
  critical-line ordinates below `16`, zero GRH),
- Ramanujan's $\Delta$ (`SpectralLowZeroData 10 16 10`, with `γ_low` holding the additional low
  critical-line ordinate below `16`, zero GRH), and
- the subtracted compact hyperbolic manifold spectral measure `dν(y) = y K_X(√y) dy` in dimensions
  `d = 2, 3` (`SubtractedHyperbolicSpectralData`, with exact moment formula
  `ν_k = 2 (2k + 3)! ∑_j r_j^{-(2k+4)}`).
-/

set_option maxHeartbeats 1200000

public section
namespace PakPrimes.CompletedXiDTrans

open Complex Real Filter MeasureTheory Set MvPolynomial
open PakPrimes.BorelStokesVandermonde
open PakPrimes.GeneralTheorem2
open PakPrimes.FishburnStrongDTrans
open PakPrimes.HigherOrderStrongDTrans
open PakPrimes.PakYeliussizovEGF
open PakPrimes.RiemannHypothesisStokes
open PakPrimes.UnconditionalPrimeDTrans
open PakPrimes.FiniteContourStokes
open PakPrimes.SpectralPositivity
open scoped Topology Interval BigOperators Matrix

noncomputable section

/-! ### 1. Completed Riemann $\xi$-Function & Unconditional Zero-Free Horizontal Strip -/

/-- The completed Riemann $\xi$-function
`ξ(s) = (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2`, which is entire on `ℂ` and agrees
with `(1 / 2) * s * (s - 1) * completedRiemannZeta s` away from `{0, 1}`. -/
@[expose] def completedXi (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- `completedXi` is entire on `ℂ`. -/
theorem differentiable_completedXi : Differentiable ℂ completedXi := by
  unfold completedXi
  exact (((differentiable_id.mul (differentiable_id.sub (differentiable_const 1))).mul
    differentiable_completedZeta₀).add (differentiable_const 1)).div_const 2

/-- Away from `{0, 1}`, `completedXi s = s * (s - 1) * completedRiemannZeta s / 2`. -/
theorem completedXi_eq_mul_completedRiemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    completedXi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  unfold completedXi
  rw [completedRiemannZeta_eq]
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp [hs0, h1s]
  ring

/-- Functional equation `ξ(1 - s) = ξ(s)` on all of `ℂ`. -/
theorem completedXi_one_sub (s : ℂ) : completedXi (1 - s) = completedXi s := by
  unfold completedXi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- Value at `s = 0`: `ξ(0) = 1 / 2`. -/
@[simp] theorem completedXi_zero : completedXi 0 = 1 / 2 := by
  simp [completedXi]

/-- Value at `s = 1`: `ξ(1) = 1 / 2`. -/
@[simp] theorem completedXi_one : completedXi 1 = 1 / 2 := by
  simp [completedXi]

private lemma gammaR_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gammaℝ s ≠ 0 := by
  rw [Gammaℝ_def]
  refine mul_ne_zero ?_ ?_
  · rw [Ne, Complex.cpow_eq_zero_iff]
    rintro ⟨hpi, _⟩
    exact Real.pi_ne_zero (Complex.ofReal_eq_zero.mp hpi)
  · refine Complex.Gamma_ne_zero fun m hm => ?_
    have hre := congrArg Complex.re hm
    simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]

/-- For `0 < s.re` and `s ≠ 1`, `completedXi s = s * (s - 1) * Gammaℝ s * riemannZeta s / 2`. -/
theorem completedXi_eq_mul_zeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    completedXi s = s * (s - 1) * Gammaℝ s * riemannZeta s / 2 := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have hg : Gammaℝ s ≠ 0 := gammaR_ne_zero_of_re_pos hs
  rw [completedXi_eq_mul_completedRiemannZeta hs0 hs1, riemannZeta_def_of_ne_zero hs0]
  field_simp [hg]

/-- Unconditional non-vanishing on `{s : ℂ | 1 ≤ s.re}`. -/
theorem completedXi_ne_zero_of_re_ge_one {s : ℂ} (hs : 1 ≤ s.re) : completedXi s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst hs1; rw [completedXi_one]; norm_num
  · have hs_pos : 0 < s.re := by linarith
    have hs0 : s ≠ 0 := fun h => by simp [h] at hs_pos
    rw [completedXi_eq_mul_zeta hs_pos hs1]
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
        (gammaR_ne_zero_of_re_pos hs_pos))
        (riemannZeta_ne_zero_of_one_le_re hs))
      two_ne_zero

/-- Unconditional non-vanishing on `{s : ℂ | s.re ≤ 0}` by the functional equation. -/
theorem completedXi_ne_zero_of_re_le_zero {s : ℂ} (hs : s.re ≤ 0) : completedXi s ≠ 0 := by
  rw [← completedXi_one_sub]
  exact completedXi_ne_zero_of_re_ge_one (by simp; linarith)

/-- Unconditional non-vanishing on the entire horizontal strip `{s : ℂ | |s.im| ≤ 1 / 2}`. -/
theorem completedXi_ne_zero_of_abs_im_le_half {s : ℂ} (him : |s.im| ≤ 1 / 2) :
    completedXi s ≠ 0 := by
  by_cases hle0 : s.re ≤ 0
  · exact completedXi_ne_zero_of_re_le_zero hle0
  · by_cases hge1 : 1 ≤ s.re
    · exact completedXi_ne_zero_of_re_ge_one hge1
    · push Not at hle0 hge1
      have hs0 : s ≠ 0 := fun h => by simp [h] at hle0
      have hs1 : s ≠ 1 := fun h => by simp [h] at hge1
      rw [completedXi_eq_mul_zeta hle0 hs1]
      exact div_ne_zero
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))
          (gammaR_ne_zero_of_re_pos hle0))
          (riemannZeta_ne_zero_on_box s hle0.le hge1.le him hs1))
        two_ne_zero

/-- Unconditional non-vanishing at every real point `c : ℝ`. -/
theorem completedXi_ne_zero_of_real (c : ℝ) : completedXi (c : ℂ) ≠ 0 :=
  completedXi_ne_zero_of_abs_im_le_half (by simp)

/-- Every zero of `completedXi` lies strictly inside the critical strip `0 < Re ρ < 1`,
satisfies `1 / 2 < |Im ρ|`, and is a nontrivial zero of `riemannZeta`. -/
theorem completedXi_zero_mem_strip {ρ : ℂ} (hρ : completedXi ρ = 0) :
    0 < ρ.re ∧ ρ.re < 1 ∧ 1 / 2 < |ρ.im| ∧ riemannZeta ρ = 0 := by
  have hre0 : 0 < ρ.re := by
    by_contra! hle
    exact completedXi_ne_zero_of_re_le_zero hle hρ
  have hre1 : ρ.re < 1 := by
    by_contra! hge
    exact completedXi_ne_zero_of_re_ge_one hge hρ
  have him : 1 / 2 < |ρ.im| := by
    by_contra! hle
    exact completedXi_ne_zero_of_abs_im_le_half hle hρ
  have hρ0 : ρ ≠ 0 := fun h => by simp [h] at hre0
  have hρ1 : ρ ≠ 1 := fun h => by simp [h] at hre1
  have hζ : riemannZeta ρ = 0 := by
    rw [completedXi_eq_mul_zeta hre0 hρ1] at hρ
    have hmul : ρ * (ρ - 1) * Gammaℝ ρ * riemannZeta ρ = 0 := (div_eq_zero_iff.mp hρ).resolve_right two_ne_zero
    have hpre : ρ * (ρ - 1) * Gammaℝ ρ ≠ 0 :=
      mul_ne_zero (mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1)) (gammaR_ne_zero_of_re_pos hre0)
    exact (mul_eq_zero.mp hmul).resolve_left hpre
  exact ⟨hre0, hre1, him, hζ⟩

/-! ### 2. Unconditional Mellin Upper Bound & Infinitude of Zeros of `completedXi` -/

private lemma cosKernel_zero_sub_one_bound {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ HurwitzZeta.cosKernel 0 t - 1 ∧
      HurwitzZeta.cosKernel 0 t - 1 ≤ 4 * Real.exp (-Real.pi * t) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hsum := HurwitzZeta.hasSum_nat_cosKernel₀ 0 ht0
  have hsum' : HasSum (fun n : ℕ => 2 * Real.exp (-Real.pi * ((n + 1 : ℝ) ^ 2) * t))
      (HurwitzZeta.cosKernel 0 t - 1) := by
    refine hsum.congr_fun fun n => ?_
    simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
  have hge0 : 0 ≤ HurwitzZeta.cosKernel 0 t - 1 := by
    rw [← hsum'.tsum_eq]
    exact tsum_nonneg fun n => by positivity
  have hpi_gt1 : 1 < Real.pi := by linarith [Real.pi_gt_three]
  have hexp_le_half : Real.exp (-Real.pi * t) ≤ 1 / 2 := by
    have h1 : (2 : ℝ) ≤ Real.exp (Real.pi * t) := by
      have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      exact he.trans (Real.exp_le_exp.mpr (by nlinarith))
    rw [show -Real.pi * t = -(Real.pi * t) by ring, Real.exp_neg]
    exact inv_le_of_inv_le₀ (by norm_num) (by simpa using h1)
  have hgeom_sum : HasSum (fun n : ℕ => (2 * Real.exp (-Real.pi * t)) * (Real.exp (-Real.pi * t)) ^ n)
      ((2 * Real.exp (-Real.pi * t)) * (1 - Real.exp (-Real.pi * t))⁻¹) :=
    (hasSum_geometric_of_lt_one (Real.exp_pos _).le (lt_of_le_of_lt hexp_le_half (by norm_num))).mul_left _
  have hterm_le : ∀ n : ℕ,
      2 * Real.exp (-Real.pi * ((n + 1 : ℝ) ^ 2) * t) ≤
        (2 * Real.exp (-Real.pi * t)) * (Real.exp (-Real.pi * t)) ^ n := by
    intro n
    have hsq : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hexp_n : Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t) ≤
        Real.exp (-Real.pi * ((n : ℝ) + 1) * t) := by
      apply Real.exp_le_exp.mpr
      have hpit : 0 < Real.pi * t := mul_pos Real.pi_pos ht0
      nlinarith
    have hpow : Real.exp (-Real.pi * ((n : ℝ) + 1) * t) =
        Real.exp (-Real.pi * t) * (Real.exp (-Real.pi * t)) ^ n := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1; ring
    calc 2 * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t)
        ≤ 2 * Real.exp (-Real.pi * ((n : ℝ) + 1) * t) := by linarith
      _ = (2 * Real.exp (-Real.pi * t)) * (Real.exp (-Real.pi * t)) ^ n := by rw [hpow]; ring
  have hle_sum : HurwitzZeta.cosKernel 0 t - 1 ≤
      (2 * Real.exp (-Real.pi * t)) * (1 - Real.exp (-Real.pi * t))⁻¹ := by
    rw [← hsum'.tsum_eq, ← hgeom_sum.tsum_eq]
    exact hsum'.summable.tsum_le_tsum hterm_le hgeom_sum.summable
  have hinv_le : (1 - Real.exp (-Real.pi * t))⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]
    linarith
  refine ⟨hge0, hle_sum.trans ?_⟩
  have hnn : 0 ≤ 2 * Real.exp (-Real.pi * t) := by positivity
  calc (2 * Real.exp (-Real.pi * t)) * (1 - Real.exp (-Real.pi * t))⁻¹
      ≤ (2 * Real.exp (-Real.pi * t)) * 2 := mul_le_mul_of_nonneg_left hinv_le hnn
    _ = 4 * Real.exp (-Real.pi * t) := by ring

private lemma integrableOn_exp_neg_mul_pow (N : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-a * t) * t ^ N) (Ioi (0 : ℝ)) volume := by
  have hint := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (N : ℝ))
    (by linarith [Nat.cast_nonneg (α := ℝ) N]) one_pos ha
  refine hint.congr_fun (fun t _ => ?_) measurableSet_Ioi
  dsimp only
  rw [Real.rpow_natCast, Real.rpow_one, mul_comm]

private lemma integrableOn_exp_neg_pi_mul_pow (N : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-Real.pi * t) * t ^ N) (Ioi (0 : ℝ)) volume :=
  integrableOn_exp_neg_mul_pow N Real.pi_pos

private lemma realLaplace_monomial_pos (m : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-a * t) * t ^ m = (m.factorial : ℝ) / a ^ (m + 1) := by
  have hC := Minor.complexLaplace_monomial m (by simpa using ha : (0 : ℝ) < (a : ℂ).re)
  have hcomm := Complex.ofRealCLM.integral_comp_comm (integrableOn_exp_neg_mul_pow m ha)
  have hrew : (fun t : ℝ => Complex.exp (-(a : ℂ) * (t : ℂ)) * (t : ℂ) ^ m) =
      fun t : ℝ => Complex.ofRealCLM (Real.exp (-a * t) * t ^ m) := by
    funext t
    change Complex.exp (-(a : ℂ) * (t : ℂ)) * (t : ℂ) ^ m = ((Real.exp (-a * t) * t ^ m : ℝ) : ℂ)
    rw [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_pow, Complex.ofReal_mul,
      Complex.ofReal_neg]
  rw [hrew, hcomm] at hC
  have hre := congrArg Complex.re hC
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_re] at hre
  rw [hre]
  have hcast : ((m.factorial : ℂ) / (a : ℂ) ^ (m + 1)) =
      (((m.factorial : ℝ) / a ^ (m + 1) : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, Complex.ofReal_re]

private lemma realLaplace_monomial_pi (N : ℕ) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-Real.pi * t) * t ^ N = (N.factorial : ℝ) / Real.pi ^ (N + 1) :=
  realLaplace_monomial_pos N Real.pi_pos

private lemma norm_mellin_cosKernel_Ioi_le (w : ℂ) (N : ℕ) (hN : w.re ≤ (N : ℝ)) :
    ‖mellin ((Ioi (1 : ℝ)).indicator (fun x : ℝ => (((HurwitzZeta.cosKernel 0 x - 1 : ℝ) : ℂ)))) w‖ ≤
      4 * (N.factorial : ℝ) := by
  let ψ : ℝ → ℂ := (Ioi (1 : ℝ)).indicator (fun x : ℝ => (((HurwitzZeta.cosKernel 0 x - 1 : ℝ) : ℂ)))
  have hrew : mellin ψ w = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * (((HurwitzZeta.cosKernel 0 t - 1 : ℝ) : ℂ)) := by
    unfold mellin ψ
    have hsmul : ∀ t : ℝ, (t : ℂ) ^ (w - 1) • (Ioi (1 : ℝ)).indicator (fun x : ℝ => (((HurwitzZeta.cosKernel 0 x - 1 : ℝ) : ℂ))) t =
        (Ioi (1 : ℝ)).indicator (fun x : ℝ => (x : ℂ) ^ (w - 1) * (((HurwitzZeta.cosKernel 0 x - 1 : ℝ) : ℂ))) t := by
      intro t; by_cases ht : t ∈ Ioi (1 : ℝ) <;> simp [ht]
    simp_rw [hsmul]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
  rw [hrew]
  have hdom0 : IntegrableOn (fun t : ℝ => 4 * (Real.exp (-Real.pi * t) * t ^ N)) (Ioi (0 : ℝ)) volume :=
    (integrableOn_exp_neg_pi_mul_pow N).const_mul 4
  have hdom1 : IntegrableOn (fun t : ℝ => 4 * (Real.exp (-Real.pi * t) * t ^ N)) (Ioi (1 : ℝ)) volume :=
    hdom0.mono_set (Ioi_subset_Ioi zero_le_one)
  have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * (((HurwitzZeta.cosKernel 0 t - 1 : ℝ) : ℂ))) (Ioi (1 : ℝ)) := by
    refine ContinuousOn.mul ?_ ?_
    · refine continuousOn_of_forall_continuousAt fun t ht => ?_
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      exact Complex.continuousAt_ofReal_cpow_const t (w - 1) (Or.inr ht0.ne')
    · exact Complex.continuous_ofReal.comp_continuousOn
        (((HurwitzZeta.continuousOn_cosKernel 0).mono (Ioi_subset_Ioi zero_le_one)).sub continuousOn_const)
  have hpt : ∀ t ∈ Ioi (1 : ℝ),
      ‖(t : ℂ) ^ (w - 1) * (((HurwitzZeta.cosKernel 0 t - 1 : ℝ) : ℂ))‖ ≤
        4 * (Real.exp (-Real.pi * t) * t ^ N) := by
    intro t ht
    have ht1 : 1 ≤ t := le_of_lt ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re,
      Complex.norm_real, Real.norm_eq_abs]
    have ⟨h0, hle⟩ := cosKernel_zero_sub_one_bound ht1
    rw [abs_of_nonneg h0]
    have hrpow : t ^ (w.re - 1) ≤ t ^ N := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    calc t ^ (w.re - 1) * (HurwitzZeta.cosKernel 0 t - 1)
        ≤ t ^ N * (4 * Real.exp (-Real.pi * t)) :=
          mul_le_mul hrpow hle h0 (pow_nonneg ht0.le N)
      _ = 4 * (Real.exp (-Real.pi * t) * t ^ N) := by ring
  have hint1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * (((HurwitzZeta.cosKernel 0 t - 1 : ℝ) : ℂ)))
      (Ioi (1 : ℝ)) volume := by
    refine hdom1.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hpt t ht
  calc ‖∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) * (((HurwitzZeta.cosKernel 0 t - 1 : ℝ) : ℂ))‖
      ≤ ∫ t in Ioi (1 : ℝ), ‖(t : ℂ) ^ (w - 1) * (((HurwitzZeta.cosKernel 0 t - 1 : ℝ) : ℂ))‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (1 : ℝ), 4 * (Real.exp (-Real.pi * t) * t ^ N) :=
        MeasureTheory.setIntegral_mono_on hint1.norm hdom1 measurableSet_Ioi hpt
    _ ≤ ∫ t in Ioi (0 : ℝ), 4 * (Real.exp (-Real.pi * t) * t ^ N) := by
        refine MeasureTheory.setIntegral_mono_set hdom0 ?_ (Eventually.of_forall (Ioi_subset_Ioi zero_le_one))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (by norm_num) (mul_nonneg (Real.exp_pos _).le (pow_nonneg ht.le N))
    _ = 4 * ((N.factorial : ℝ) / Real.pi ^ (N + 1)) := by
        rw [MeasureTheory.integral_const_mul, realLaplace_monomial_pi N]
    _ ≤ 4 * (N.factorial : ℝ) := by
        have hpi_pow : (1 : ℝ) ≤ Real.pi ^ (N + 1) := one_le_pow₀ (by linarith [Real.pi_gt_three])
        have hdiv : (N.factorial : ℝ) / Real.pi ^ (N + 1) ≤ (N.factorial : ℝ) :=
          div_le_self (Nat.cast_nonneg _) hpi_pow
        linarith

private lemma completedRiemannZeta₀_eq_mellin_split (s : ℂ) :
    let ψ : ℝ → ℂ := (Ioi (1 : ℝ)).indicator (fun x : ℝ => (((HurwitzZeta.cosKernel 0 x - 1 : ℝ) : ℂ)))
    completedRiemannZeta₀ s = (mellin ψ (s / 2) + mellin ψ (1 / 2 - s / 2)) / 2 := by
  intro ψ
  change ((HurwitzZeta.hurwitzEvenFEPair 0).Λ₀ (s / 2)) / 2 = (mellin ψ (s / 2) + mellin ψ (1 / 2 - s / 2)) / 2
  congr 1
  set P := HurwitzZeta.hurwitzEvenFEPair 0
  have hP_symm : P.symm = P := HurwitzZeta.hurwitzEvenFEPair_zero_symm
  have hψ_int : ∀ z : ℂ, MellinConvergent ψ z := by
    intro z
    let N : ℕ := Nat.ceil (max 0 z.re)
    have hN : z.re ≤ (N : ℝ) := (le_max_right 0 z.re).trans (Nat.le_ceil _)
    have hdom0 : IntegrableOn (fun t : ℝ => 4 * (Real.exp (-Real.pi * t) * t ^ N)) (Ioi (0 : ℝ)) volume :=
      (integrableOn_exp_neg_pi_mul_pow N).const_mul 4
    have hdom1 : IntegrableOn (fun t : ℝ => 4 * (Real.exp (-Real.pi * t) * t ^ N)) (Ioi (1 : ℝ)) volume :=
      hdom0.mono_set (Ioi_subset_Ioi zero_le_one)
    have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * (((HurwitzZeta.cosKernel 0 t - 1 : ℝ) : ℂ))) (Ioi (1 : ℝ)) := by
      refine ContinuousOn.mul ?_ ?_
      · refine continuousOn_of_forall_continuousAt fun t ht => ?_
        have ht0 : 0 < t := lt_trans zero_lt_one ht
        exact Complex.continuousAt_ofReal_cpow_const t (z - 1) (Or.inr ht0.ne')
      · exact Complex.continuous_ofReal.comp_continuousOn
          (((HurwitzZeta.continuousOn_cosKernel 0).mono (Ioi_subset_Ioi zero_le_one)).sub continuousOn_const)
    have hint1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) * (((HurwitzZeta.cosKernel 0 t - 1 : ℝ) : ℂ)))
        (Ioi (1 : ℝ)) volume := by
      refine hdom1.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 ≤ t := le_of_lt ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.sub_re, Complex.one_re,
        Complex.norm_real, Real.norm_eq_abs]
      have ⟨h0, hle⟩ := cosKernel_zero_sub_one_bound ht1
      rw [abs_of_nonneg h0]
      have hrpow : t ^ (z.re - 1) ≤ t ^ N := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
      calc t ^ (z.re - 1) * (HurwitzZeta.cosKernel 0 t - 1)
          ≤ t ^ N * (4 * Real.exp (-Real.pi * t)) :=
            mul_le_mul hrpow hle h0 (pow_nonneg ht0.le N)
        _ = 4 * (Real.exp (-Real.pi * t) * t ^ N) := by ring
    change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (z - 1) • ψ t) (Ioi (0 : ℝ)) volume
    have hsmul : (fun t : ℝ => (t : ℂ) ^ (z - 1) • ψ t) =
        (Ioi (1 : ℝ)).indicator (fun t : ℝ => (t : ℂ) ^ (z - 1) * (((HurwitzZeta.cosKernel 0 t - 1 : ℝ) : ℂ))) := by
      funext t; by_cases ht : t ∈ Ioi (1 : ℝ) <;> simp [ψ, ht]
    rw [IntegrableOn, hsmul, MeasureTheory.integrable_indicator_iff measurableSet_Ioi,
      MeasureTheory.IntegrableOn, Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.mpr (Ioi_subset_Ioi zero_le_one)]
    exact hint1
  have hinv_mellin : mellin (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) • ψ (1 / t)) (s / 2) =
      mellin ψ (1 / 2 - s / 2) := by
    have h1 := mellin_cpow_smul (fun t : ℝ => ψ (1 / t)) (s / 2) (-(1 / 2 : ℂ))
    have h2 := mellin_comp_rpow ψ (s / 2 - 1 / 2) (-1 : ℝ)
    simp only [abs_neg, abs_one, one_smul, ofReal_neg, ofReal_one, div_neg, div_one,
      rpow_neg_one, ← one_div] at h2
    rw [h1, show s / 2 + -(1 / 2 : ℂ) = s / 2 - 1 / 2 by ring, h2]
    congr 1; ring
  have hinv_conv : MellinConvergent (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) • ψ (1 / t)) (s / 2) := by
    change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) • ((t : ℂ) ^ (-(1 / 2 : ℂ)) • ψ (1 / t))) (Ioi (0 : ℝ)) volume
    have himg : (fun x : ℝ => x⁻¹) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
      ext y; simp only [mem_image, mem_Ioi]
      exact ⟨fun ⟨x, hx, hxy⟩ => hxy ▸ inv_pos.mpr hx, fun hy => ⟨y⁻¹, inv_pos.mpr hy, inv_inv y⟩⟩
    have hinj : Set.InjOn (fun x : ℝ => x⁻¹) (Ioi (0 : ℝ)) := fun _ _ _ _ h => inv_injective h
    have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun t : ℝ => t⁻¹) (-(x ^ 2)⁻¹) (Ioi (0 : ℝ)) x :=
      fun x hx => (hasDerivAt_inv (ne_of_gt hx)).hasDerivWithinAt
    have hbase : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (1 / 2 - s / 2 - 1) • ψ y) (Ioi (0 : ℝ)) volume :=
      hψ_int (1 / 2 - s / 2)
    rw [← himg, MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj] at hbase
    refine hbase.congr_fun (fun t ht => ?_) measurableSet_Ioi
    dsimp only
    have ht0 : 0 < t := ht
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
    rw [abs_neg, abs_inv, abs_of_pos (pow_pos ht0 2), smul_eq_mul, smul_eq_mul,
      smul_eq_mul, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow, ← mul_assoc,
      ← mul_assoc, one_div t]
    congr 1
    have hinv_cp : ∀ w : ℂ, ((t⁻¹ : ℝ) : ℂ) ^ w = (t : ℂ) ^ (-w) := fun w => by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (inv_ne_zero ht0.ne')),
        Complex.cpow_def_of_ne_zero htC, ← Complex.ofReal_log (inv_pos.mpr ht0).le, Real.log_inv,
        Complex.ofReal_neg, Complex.ofReal_log ht0.le]
      congr 1; ring
    have hinv_sq : ((t : ℂ) ^ 2)⁻¹ = (t : ℂ) ^ (-2 : ℂ) := by
      rw [Complex.cpow_neg, Complex.cpow_two]
    rw [hinv_cp, hinv_sq, ← Complex.cpow_add _ _ htC, ← Complex.cpow_add _ _ htC]
    congr 1; ring
  have hae : ∀ t ∈ Ioi (0 : ℝ), t ≠ 1 →
      P.f_modif t = ψ t + (t : ℂ) ^ (-(1 / 2 : ℂ)) • ψ (1 / t) := by
    intro t ht ht1
    rcases lt_or_gt_of_ne ht1 with hlt | hgt
    · have h1t : (1 : ℝ) < 1 / t := by rw [lt_div_iff₀ ht]; linarith
      have hψt : ψ t = 0 := Set.indicator_of_notMem (notMem_Ioi.mpr hlt.le) _
      have hψinv : ψ (1 / t) = (((HurwitzZeta.cosKernel 0 (1 / t) - 1 : ℝ) : ℂ)) :=
        Set.indicator_of_mem (show 1 / t ∈ Ioi (1 : ℝ) from h1t) _
      have hfe := P.hf_modif_FE (1 / t) (div_pos one_pos ht)
      rw [one_div_one_div] at hfe
      have hgm : P.g_modif (1 / t) = (((HurwitzZeta.cosKernel 0 (1 / t) - 1 : ℝ) : ℂ)) := by
        unfold WeakFEPair.g_modif
        simp only [Pi.add_apply, Set.indicator_of_mem (show 1 / t ∈ Ioi (1 : ℝ) from h1t),
          Set.indicator_of_notMem (notMem_Ioo_of_ge h1t.le),
          add_zero, P, HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply, Complex.ofReal_sub, Complex.ofReal_one]
      rw [hfe, hgm, hψt, zero_add, hψinv]
      change ((1 : ℂ) * ↑((1 / t) ^ (1 / 2 : ℝ))) • _ = (t : ℂ) ^ (-(1 / 2 : ℂ)) • _
      congr 1
      rw [one_mul, one_div, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, Complex.ofReal_cpow ht.le]
      push_cast; rfl
    · have h1t : 1 / t < (1 : ℝ) := by rw [div_lt_iff₀ ht]; linarith
      have hψinv : ψ (1 / t) = 0 := Set.indicator_of_notMem (notMem_Ioi.mpr h1t.le) _
      have hψt : ψ t = (((HurwitzZeta.cosKernel 0 t - 1 : ℝ) : ℂ)) :=
        Set.indicator_of_mem (show t ∈ Ioi (1 : ℝ) from hgt) _
      rw [hψinv, smul_zero, add_zero, hψt]
      unfold WeakFEPair.f_modif
      simp only [Pi.add_apply, Set.indicator_of_mem (show t ∈ Ioi (1 : ℝ) from hgt),
        Set.indicator_of_notMem (notMem_Ioo_of_ge hgt.le),
        add_zero, P, HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply,
        HurwitzZeta.evenKernel_eq_cosKernel_of_zero, ↓reduceIte, Complex.ofReal_sub, Complex.ofReal_one]
  have heq : P.Λ₀ (s / 2) = mellin (fun t : ℝ => ψ t + (t : ℂ) ^ (-(1 / 2 : ℂ)) • ψ (1 / t)) (s / 2) := by
    unfold WeakFEPair.Λ₀ mellin
    refine MeasureTheory.setIntegral_congr_ae measurableSet_Ioi ?_
    have hne1 : ∀ᵐ t : ℝ ∂volume, t ≠ 1 := by rw [ae_iff]; simp
    filter_upwards [hne1] with t ht1 ht0
    rw [hae t ht0 ht1]
  rw [heq, (hasMellin_add (hψ_int (s / 2)) hinv_conv).2, hinv_mellin]

private lemma factorial_le_pow_self (N : ℕ) : (N.factorial : ℝ) ≤ (N : ℝ) ^ N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, pow_succ']
    have hle : (n : ℝ) ^ n ≤ ((n + 1 : ℕ) : ℝ) ^ n :=
      pow_le_pow_left₀ (Nat.cast_nonneg n) (by exact_mod_cast Nat.le_succ n) n
    exact mul_le_mul_of_nonneg_left (ih.trans hle) (Nat.cast_nonneg _)

/-- **Unconditional Global Growth Bound on `completedXi`**:
For every `R ≥ 4` and every `z ∈ ℂ` with `‖z‖ ≤ R`,
`‖completedXi z‖ ≤ (2 * R) ^ (Nat.ceil R + 4)`. -/
theorem norm_completedXi_le {R : ℝ} (hR : 4 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖completedXi z‖ ≤ (2 * R) ^ (Nat.ceil R + 4) := by
  let N : ℕ := Nat.ceil R + 1
  have hN_ge : R + 1 ≤ (N : ℝ) := by
    dsimp only [N]; push_cast; linarith [Nat.le_ceil R]
  have hN_le : (N : ℝ) ≤ 2 * R := by
    dsimp only [N]; push_cast
    have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ R by linarith)
    linarith
  have hw1 : (z / 2).re ≤ (N : ℝ) := by
    have h1 : (z / 2).re ≤ ‖z / 2‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
    rw [norm_div, Complex.norm_ofNat] at h1
    linarith
  have hw2 : (1 / 2 - z / 2).re ≤ (N : ℝ) := by
    have h1 : (-z / 2).re ≤ ‖-z / 2‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
    rw [norm_div, norm_neg, Complex.norm_ofNat] at h1
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re, Complex.neg_re] at h1 ⊢
    linarith
  have hZ0 : ‖completedRiemannZeta₀ z‖ ≤ 4 * (N.factorial : ℝ) := by
    rw [completedRiemannZeta₀_eq_mellin_split z]
    rw [norm_div, Complex.norm_ofNat]
    have hm1 := norm_mellin_cosKernel_Ioi_le (z / 2) N hw1
    have hm2 := norm_mellin_cosKernel_Ioi_le (1 / 2 - z / 2) N hw2
    calc ‖mellin _ (z / 2) + mellin _ (1 / 2 - z / 2)‖ / 2
        ≤ (‖mellin _ (z / 2)‖ + ‖mellin _ (1 / 2 - z / 2)‖) / 2 := by
          gcongr; exact norm_add_le _ _
      _ ≤ (4 * (N.factorial : ℝ) + 4 * (N.factorial : ℝ)) / 2 := by linarith
      _ = 4 * (N.factorial : ℝ) := by ring
  have hfac_le : (N.factorial : ℝ) ≤ (2 * R) ^ N :=
    (factorial_le_pow_self N).trans (pow_le_pow_left₀ (Nat.cast_nonneg N) hN_le N)
  have hfac_ge1 : (1 : ℝ) ≤ (2 * R) ^ N := one_le_pow₀ (by linarith)
  have hpoly : ‖z * (z - 1)‖ ≤ R * (R + 1) := by
    rw [norm_mul]
    have hz1 : ‖z - 1‖ ≤ R + 1 := by
      calc ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le z 1
        _ ≤ R + 1 := by rw [norm_one]; linarith
    exact mul_le_mul hz hz1 (norm_nonneg _) (by linarith)
  unfold completedXi
  rw [norm_div, Complex.norm_ofNat]
  have hnum : ‖z * (z - 1) * completedRiemannZeta₀ z + 1‖ ≤
      R * (R + 1) * (4 * (2 * R) ^ N) + 1 := by
    calc ‖z * (z - 1) * completedRiemannZeta₀ z + 1‖
        ≤ ‖z * (z - 1)‖ * ‖completedRiemannZeta₀ z‖ + ‖(1 : ℂ)‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ R * (R + 1) * (4 * (2 * R) ^ N) + 1 := by
          rw [norm_one]
          gcongr
          exact hZ0.trans (by linarith)
  have hcoeff : 2 * R * (R + 1) + 1 ≤ (2 * R) ^ 3 := by
    have hR2 : 16 ≤ R ^ 2 := by nlinarith
    have hR3 : 64 ≤ R ^ 3 := by nlinarith
    have h3 : (2 * R) ^ 3 = 8 * R ^ 3 := by ring
    rw [h3]; nlinarith
  have hstep : (R * (R + 1) * (4 * (2 * R) ^ N) + 1) / 2 ≤ (2 * R) ^ (N + 3) := by
    calc (R * (R + 1) * (4 * (2 * R) ^ N) + 1) / 2
        ≤ (2 * R * (R + 1) + 1) * (2 * R) ^ N := by nlinarith
      _ ≤ (2 * R) ^ 3 * (2 * R) ^ N := mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = (2 * R) ^ (N + 3) := by rw [← pow_add, add_comm 3 N]
  have hpow_eq : N + 3 = Nat.ceil R + 4 := by dsimp only [N]
  rw [← hpow_eq]
  exact (div_le_div_of_nonneg_right hnum zero_le_two).trans hstep

/-- Exact factorial lower bound at positive even integers `s = 2 * (n + 1)`:
`((n.factorial : ℝ) / Real.pi ^ (n + 1)) ≤ ‖completedXi (2 * (n + 1))‖`. -/
theorem norm_completedXi_two_mul_ge (n : ℕ) :
    (n.factorial : ℝ) / Real.pi ^ (n + 1) ≤ ‖completedXi ((2 * (n + 1) : ℕ) : ℂ)‖ := by
  let s : ℂ := ((2 * (n + 1) : ℕ) : ℂ)
  have hs_re : 1 < s.re := by
    dsimp only [s]; simp only [Complex.natCast_re]; exact_mod_cast (show 1 < 2 * (n + 1) by omega)
  have hs0 : s ≠ 0 := by
    dsimp only [s]; exact_mod_cast (show 2 * (n + 1) ≠ 0 by omega)
  have hs1 : s ≠ 1 := by
    dsimp only [s]; exact_mod_cast (show 2 * (n + 1) ≠ 1 by omega)
  rw [completedXi_eq_mul_completedRiemannZeta hs0 hs1, completedZeta_eq_tsum_of_one_lt_re hs_re]
  have hs_half : s / 2 = ((n + 1 : ℕ) : ℂ) := by
    dsimp only [s]; push_cast; ring
  have hGamma : Complex.Gamma (s / 2) = (n.factorial : ℂ) := by
    rw [hs_half, Nat.cast_add, Nat.cast_one, Complex.Gamma_nat_eq_factorial]
  have hpi_pow : (Real.pi : ℂ) ^ (-s / 2) = (((Real.pi ^ (n + 1))⁻¹ : ℝ) : ℂ) := by
    have hneg : -s / 2 = -((n + 1 : ℕ) : ℂ) := by rw [neg_div, hs_half]
    rw [hneg, Complex.cpow_neg, Complex.cpow_natCast, Complex.ofReal_inv, Complex.ofReal_pow]
  have hsum_ge1 : (1 : ℝ) ≤ ‖∑' m : ℕ, (1 : ℂ) / (m : ℂ) ^ s‖ := by
    have hsumR : Summable (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ (2 * (n + 1))) := by
      exact Real.summable_one_div_nat_pow.mpr (by omega)
    have hcast_eq : (∑' m : ℕ, (1 : ℂ) / (m : ℂ) ^ s) =
        ((∑' m : ℕ, (1 : ℝ) / (m : ℝ) ^ (2 * (n + 1)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      refine tsum_congr fun m => ?_
      dsimp only [s]
      rw [Complex.cpow_natCast, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_pow,
        Complex.ofReal_natCast]
    rw [hcast_eq, Complex.norm_real, Real.norm_eq_abs]
    have hle_sum : (1 : ℝ) / ((1 : ℕ) : ℝ) ^ (2 * (n + 1)) ≤
        ∑' m : ℕ, (1 : ℝ) / (m : ℝ) ^ (2 * (n + 1)) :=
      hsumR.le_tsum 1 (fun k _ => by positivity)
    simp only [Nat.cast_one, one_pow, div_one] at hle_sum
    exact hle_sum.trans (le_abs_self _)
  have hpre_ge : (1 : ℝ) ≤ ‖s * (s - 1) / 2‖ := by
    have hcast : s * (s - 1) / 2 = ((((2 * (n + 1) : ℕ) : ℝ) * (((2 * (n + 1) : ℕ) : ℝ) - 1) / 2 : ℝ) : ℂ) := by
      dsimp only [s]; push_cast; rfl
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    have hn1 : (2 : ℝ) ≤ ((2 * (n + 1) : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 2 * (n + 1) by omega)
    have h1 : (1 : ℝ) ≤ ((2 * (n + 1) : ℕ) : ℝ) * (((2 * (n + 1) : ℕ) : ℝ) - 1) / 2 := by nlinarith
    exact h1.trans (le_abs_self _)
  rw [show s * (s - 1) * ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * ∑' m : ℕ, 1 / (m : ℂ) ^ s) / 2 =
      (s * (s - 1) / 2) * ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) * (∑' m : ℕ, 1 / (m : ℂ) ^ s) by ring]
  rw [norm_mul, norm_mul, norm_mul, hpi_pow, hGamma, Complex.norm_real, Complex.norm_natCast,
    Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg Real.pi_pos.le _))]
  have hbase : (Real.pi ^ (n + 1))⁻¹ * (n.factorial : ℝ) = (n.factorial : ℝ) / Real.pi ^ (n + 1) := by ring
  rw [hbase]
  have hnn : 0 ≤ (n.factorial : ℝ) / Real.pi ^ (n + 1) := by positivity
  calc (n.factorial : ℝ) / Real.pi ^ (n + 1)
      = 1 * ((n.factorial : ℝ) / Real.pi ^ (n + 1)) * 1 := by ring
    _ ≤ ‖s * (s - 1) / 2‖ * ((n.factorial : ℝ) / Real.pi ^ (n + 1)) * ‖∑' m : ℕ, (1 : ℂ) / (m : ℂ) ^ s‖ := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right hpre_ge hnn) hsum_ge1 zero_le_one (by positivity)

/-- Entire factorization of a single zero `a : ℂ` out of an entire function `f`. -/
private lemma exists_entire_factor_single_complex {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf_ne : ∃ s₀ : ℂ, f s₀ ≠ 0) (a : ℂ) :
    ∃ F : ℂ → ℂ,
      Differentiable ℂ F ∧
      (∀ s : ℂ, f s = (s - a) ^ analyticOrderNatAt f a * F s) ∧
      F a ≠ 0 := by
  have hf_an : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  have hne_top : analyticOrderAt f a ≠ ⊤ := by
    intro htop
    have hzero : ∀ s ∈ Set.univ, f s = 0 :=
      hf_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ a)
        (analyticOrderAt_eq_top.mp htop)
    obtain ⟨s₀, hs₀⟩ := hf_ne
    exact hs₀ (hzero s₀ (Set.mem_univ s₀))
  obtain ⟨g, hg_ana, hg_ne, hfg⟩ := (hf_an a (Set.mem_univ a)).analyticOrderAt_ne_top.mp hne_top
  let m : ℕ := analyticOrderNatAt f a
  let F : ℂ → ℂ := fun z => if z = a then g a else f z / (z - a) ^ m
  have hFg : F =ᶠ[𝓝 a] g := by
    filter_upwards [hfg] with z hz
    dsimp only [F]
    by_cases hza : z = a
    · subst hza; simp
    · simp only [hza, ↓reduceIte]
      have hz' : f z = (z - a) ^ m * g z := by simpa [m, smul_eq_mul] using hz
      have hpow : (z - a) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hza)
      rw [hz', mul_div_cancel_left₀ _ hpow]
  have hF_diff : Differentiable ℂ F := by
    intro z
    by_cases hza : z = a
    · subst hza
      exact (hg_ana.congr hFg.symm).differentiableAt
    · have hFz : F =ᶠ[𝓝 z] fun w => f w / (w - a) ^ m := by
        filter_upwards [isOpen_ne.mem_nhds hza] with w hwa
        simp [F, hwa]
      have hdiv : DifferentiableAt ℂ (fun w => f w / (w - a) ^ m) z :=
        (hf z).div (((differentiableAt_id).sub (differentiableAt_const a)).pow m)
          (pow_ne_zero m (sub_ne_zero.mpr hza))
      exact hdiv.congr_of_eventuallyEq hFz
  have hF_eq : ∀ s : ℂ, f s = (s - a) ^ m * F s := by
    intro s
    by_cases hsa : s = a
    · subst hsa
      have h0 := hfg.self_of_nhds
      simpa [F, m, smul_eq_mul] using h0
    · simp only [F, hsa, ↓reduceIte]
      have hpow : (s - a) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hsa)
      rw [mul_div_cancel₀ _ hpow]
  refine ⟨F, hF_diff, hF_eq, by simpa [F] using hg_ne⟩

/-- Entire factorization of a finite set `S : Finset ℂ` of zeros out of an entire function `f`. -/
private lemma exists_entire_factor_finset_complex {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf_ne : ∃ s₀ : ℂ, f s₀ ≠ 0) (S : Finset ℂ) :
    ∃ F : ℂ → ℂ,
      Differentiable ℂ F ∧
      (∀ s : ℂ, f s = (∏ x ∈ S, (s - x) ^ analyticOrderNatAt f x) * F s) ∧
      (∀ x ∈ S, F x ≠ 0) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨f, hf, fun s => by simp, fun x hx => absurd hx (Finset.notMem_empty x)⟩
  | @insert a S ha ih =>
    obtain ⟨F₁, hF₁_diff, hF₁_eq, hF₁_ne⟩ := ih
    let Q : ℂ → ℂ := fun s => ∏ x ∈ S, (s - x) ^ analyticOrderNatAt f x
    have hF₁_notzero : ∃ s₀ : ℂ, F₁ s₀ ≠ 0 := by
      obtain ⟨s₀, hs₀⟩ := hf_ne
      refine ⟨s₀, fun h0 => hs₀ ?_⟩
      rw [hF₁_eq s₀, h0, mul_zero]
    have hQ_an : AnalyticAt ℂ Q a :=
      Finset.analyticAt_fun_prod S fun x _ => (analyticAt_id.sub analyticAt_const).pow _
    have hQ_ne : Q a ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun x hx => pow_ne_zero _ (sub_ne_zero.mpr fun h => ha (h ▸ hx))
    have hF₁_an : AnalyticAt ℂ F₁ a :=
      (hF₁_diff.differentiableOn.analyticOnNhd isOpen_univ) a (Set.mem_univ _)
    have hord_eq : analyticOrderNatAt F₁ a = analyticOrderNatAt f a := by
      have hf_eq_fn : f = Q * F₁ := funext hF₁_eq
      have hord : analyticOrderAt f a = analyticOrderAt F₁ a := by
        rw [hf_eq_fn, analyticOrderAt_mul hQ_an hF₁_an, hQ_an.analyticOrderAt_eq_zero.mpr hQ_ne,
          zero_add]
      simp only [analyticOrderNatAt, hord]
    obtain ⟨F₂, hF₂_diff, hF₂_eq, hF₂_ne⟩ := exists_entire_factor_single_complex hF₁_diff hF₁_notzero a
    refine ⟨F₂, hF₂_diff, fun s => ?_, fun x hx => ?_⟩
    · rw [hF₁_eq s, hF₂_eq s, hord_eq, Finset.prod_insert ha]
      ring
    · rcases Finset.mem_insert.mp hx with rfl | hxS
      · exact hF₂_ne
      · intro h0
        apply hF₁_ne x hxS
        rw [hF₂_eq x, h0, mul_zero]

/-- Any zero-free entire function `g : ℂ → ℂ` admits an entire logarithm `h : ℂ → ℂ`
with `Complex.exp (h z) = g z` for all `z : ℂ`. -/
private lemma exists_entire_log {g : ℂ → ℂ} (hg : Differentiable ℂ g) (hg0 : ∀ z : ℂ, g z ≠ 0) :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ ∀ z : ℂ, Complex.exp (h z) = g z := by
  have huniv_sc : IsSimplyConnected (Set.univ : Set ℂ) :=
    (Homeomorph.Set.univ ℂ).toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance
  have h0_notmem : (0 : ℂ) ∉ g '' (Set.univ : Set ℂ) := by
    rintro ⟨z, _, hz⟩; exact hg0 z hz
  obtain ⟨h, hh_cont, hh_exp⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp huniv_sc isOpen_univ hg.continuous.continuousOn h0_notmem
  have hh_exp_all : ∀ z : ℂ, Complex.exp (h z) = g z := fun z => hh_exp (Set.mem_univ z)
  have hh_cont_all : Continuous h := continuousOn_univ.mp hh_cont
  have hh_diff : Differentiable ℂ h := by
    intro z₀
    have hnhds : ∀ᶠ w in 𝓝 z₀, ‖h w - h z₀‖ < Real.pi := by
      have hc : ContinuousAt (fun w : ℂ => ‖h w - h z₀‖) z₀ :=
        ((hh_cont_all.continuousAt (x := z₀)).sub continuousAt_const).norm
      have h1 : Tendsto (fun w => ‖h w - h z₀‖) (𝓝 z₀) (𝓝 0) := by
        simpa using hc.tendsto
      exact h1.eventually (gt_mem_nhds Real.pi_pos)
    have hloc : h =ᶠ[𝓝 z₀] fun w => h z₀ + Complex.log (g w / g z₀) := by
      filter_upwards [hnhds] with w hw
      have him : |(h w - h z₀).im| < Real.pi := (Complex.abs_im_le_norm _).trans_lt hw
      have hexp_div : g w / g z₀ = Complex.exp (h w - h z₀) := by
        rw [Complex.exp_sub, hh_exp_all w, hh_exp_all z₀]
      rw [hexp_div, Complex.log_exp (abs_lt.mp him).1 (abs_lt.mp him).2.le]
      ring
    have hlog_diff : DifferentiableAt ℂ (fun w => h z₀ + Complex.log (g w / g z₀)) z₀ := by
      have hdiv : DifferentiableAt ℂ (fun w => g w / g z₀) z₀ :=
        (hg z₀).div_const (g z₀)
      have hslit : g z₀ / g z₀ ∈ Complex.slitPlane := by
        rw [div_self (hg0 z₀)]; exact Or.inl zero_lt_one
      exact (differentiableAt_const _).add (hdiv.clog hslit)
    exact hlog_diff.congr_of_eventuallyEq hloc
  exact ⟨h, hh_diff, hh_exp_all⟩

private lemma prod_le_prod_real {ι : Type*} (s : Finset ι) {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa := hf a (Finset.mem_insert_self a s)
    have hfga := hfg a (Finset.mem_insert_self a s)
    have hfs : 0 ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have ih' := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
    exact mul_le_mul hfga ih' hfs (hfa.trans hfga)

/-- **100% Unconditional Infinitude of Zeros of `completedXi` (Mathlib Plus This Repository's Proved Modules, No Extra Hypotheses, ZERO RH)**:
The completed Riemann $\xi$-function has infinitely many zeros in `ℂ` (all lying strictly inside
`0 < Re ρ < 1` with `|Im ρ| > 1 / 2`). -/
theorem completedXi_zeros_infinite : {ρ : ℂ | completedXi ρ = 0}.Infinite := by
  intro hfin
  let S : Finset ℂ := hfin.toFinset
  have hS_mem : ∀ z : ℂ, z ∈ S ↔ completedXi z = 0 := fun z => by
    simp [S]
  have hne : ∃ s₀ : ℂ, completedXi s₀ ≠ 0 := ⟨0, by simp⟩
  obtain ⟨g, hg_diff, hfac, hg_ne_S⟩ :=
    exists_entire_factor_finset_complex differentiable_completedXi hne S
  let P : ℂ → ℂ := fun z => ∏ ρ ∈ S, (z - ρ) ^ analyticOrderNatAt completedXi ρ
  have hg_ne : ∀ z : ℂ, g z ≠ 0 := by
    intro z
    by_cases hz : z ∈ S
    · exact hg_ne_S z hz
    · intro h0
      have hxi0 : completedXi z = 0 := by rw [hfac z, h0, mul_zero]
      exact hz ((hS_mem z).mpr hxi0)
  obtain ⟨h, hh_diff, hh_exp⟩ := exists_entire_log hg_diff hg_ne
  -- Radius above all zeros in S
  let R₁ : ℝ := max 6 (1 + ∑ ρ ∈ S, ‖ρ‖)
  have hR₁_ge6 : 6 ≤ R₁ := le_max_left _ _
  have hP_ge1 : ∀ {R : ℝ}, R₁ ≤ R → ∀ z ∈ Metric.sphere (0 : ℂ) R, 1 ≤ ‖P z‖ := by
    intro R hR z hz
    rw [mem_sphere_zero_iff_norm] at hz
    dsimp only [P]
    rw [norm_prod, ← Finset.prod_const_one]
    refine prod_le_prod_real S (fun _ _ => zero_le_one) fun ρ hρ => ?_
    rw [norm_pow]
    refine one_le_pow₀ ?_
    have hρ_le : ‖ρ‖ ≤ ∑ ρ' ∈ S, ‖ρ'‖ :=
      Finset.single_le_sum (f := fun ρ' : ℂ => ‖ρ'‖) (fun _ _ => norm_nonneg _) hρ
    have hR_ge : 1 + ∑ ρ' ∈ S, ‖ρ'‖ ≤ R := (le_max_right _ _).trans hR
    have htri : ‖z‖ - ‖ρ‖ ≤ ‖z - ρ‖ := norm_sub_norm_le z ρ
    linarith
  -- Upper bound on `(h z).re` on `ball 0 R` for all `R ≥ R₁`
  have hh_re_le : ∀ {R : ℝ}, R₁ ≤ R → ∀ z ∈ Metric.ball (0 : ℂ) R,
      (h z).re ≤ 2 * R * Real.log (2 * R) := by
    intro R hR z hz
    have hR4 : 4 ≤ R := by linarith
    have hR6 : 6 ≤ R := by linarith
    have hfrontier : ∀ w ∈ frontier (Metric.ball (0 : ℂ) R), ‖g w‖ ≤ (2 * R) ^ (Nat.ceil R + 4) := by
      intro w hw
      rw [frontier_ball (0 : ℂ) (by linarith : R ≠ 0)] at hw
      have hw_norm : ‖w‖ = R := mem_sphere_zero_iff_norm.mp hw
      have hP1 : 1 ≤ ‖P w‖ := hP_ge1 hR w hw
      have hmul : ‖P w‖ * ‖g w‖ = ‖completedXi w‖ := by rw [← norm_mul, ← hfac w]
      have hg_le : ‖g w‖ ≤ ‖completedXi w‖ := by
        calc ‖g w‖ = 1 * ‖g w‖ := (one_mul _).symm
          _ ≤ ‖P w‖ * ‖g w‖ := mul_le_mul_of_nonneg_right hP1 (norm_nonneg _)
          _ = ‖completedXi w‖ := hmul
      exact hg_le.trans (norm_completedXi_le hR4 hw_norm.le)
    have hgz_le : ‖g z‖ ≤ (2 * R) ^ (Nat.ceil R + 4) :=
      Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
        hg_diff.differentiableOn.diffContOnCl hfrontier (subset_closure hz)
    have hexp_le : Real.exp (h z).re ≤ (2 * R) ^ (Nat.ceil R + 4) := by
      rwa [← Complex.norm_exp, hh_exp z]
    have h2R_pos : 0 < 2 * R := by linarith
    have hlog_le : (h z).re ≤ ((Nat.ceil R + 4 : ℕ) : ℝ) * Real.log (2 * R) := by
      have h1 := Real.log_le_log (Real.exp_pos _) hexp_le
      rwa [Real.log_exp, Real.log_pow] at h1
    have hdeg_le : ((Nat.ceil R + 4 : ℕ) : ℝ) ≤ 2 * R := by
      push_cast
      have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ R by linarith)
      linarith
    have hlog_nn : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
    exact hlog_le.trans (mul_le_mul_of_nonneg_right hdeg_le hlog_nn)
  -- Show `iteratedDeriv k h 0 = 0` for all `k ≥ 2` via Borel-Carathéodory + Cauchy estimate
  have hderiv_zero : ∀ k : ℕ, 2 ≤ k → iteratedDeriv k h 0 = 0 := by
    intro k hk
    by_contra hne_k
    have hpos_k : 0 < ‖iteratedDeriv k h 0‖ := norm_pos_iff.mpr hne_k
    -- For every R ≥ R₁, bound `‖iteratedDeriv k h 0‖ ≤ C_k / √R`
    have hbd_R : ∀ R : ℝ, R₁ ≤ R →
        ‖iteratedDeriv k h 0‖ ≤
          (k.factorial : ℝ) * (8 * Real.sqrt 2 * R * Real.sqrt R + 3 * ‖h 0‖) / (R / 2) ^ 2 := by
      intro R hR
      have hR6 : 6 ≤ R := by linarith
      have hR_pos : 0 < R := by linarith
      have hM_pos : 0 < 2 * R * Real.log (2 * R) :=
        mul_pos (by linarith) (Real.log_pos (by linarith))
      have hBC : ∀ z ∈ Metric.sphere (0 : ℂ) (R / 2),
          ‖h z‖ ≤ 8 * Real.sqrt 2 * R * Real.sqrt R + 3 * ‖h 0‖ := by
        intro z hz
        have hz_norm : ‖z‖ = R / 2 := mem_sphere_zero_iff_norm.mp hz
        have hz_ball : z ∈ Metric.ball (0 : ℂ) R := by
          rw [Metric.mem_ball, dist_zero_right, hz_norm]; linarith
        have hbc := Complex.borelCaratheodory hM_pos hh_diff.differentiableOn
          (fun w hw => hh_re_le hR w hw) hR_pos hz_ball
        rw [hz_norm] at hbc
        have hsimp : 2 * (2 * R * Real.log (2 * R)) * (R / 2) / (R - R / 2) +
            ‖h 0‖ * (R + R / 2) / (R - R / 2) =
            4 * R * Real.log (2 * R) + 3 * ‖h 0‖ := by
          field_simp [hR_pos.ne']; ring
        rw [hsimp] at hbc
        have hlog_sqrt : Real.log (2 * R) ≤ 2 * Real.sqrt (2 * R) := by
          have hs_pos : 0 < Real.sqrt (2 * R) := Real.sqrt_pos.mpr (by linarith)
          have hsq : Real.log (2 * R) = 2 * Real.log (Real.sqrt (2 * R)) := by
            rw [show (2 : ℝ) * Real.log (Real.sqrt (2 * R)) = ((2 : ℕ) : ℝ) * Real.log (Real.sqrt (2 * R)) by norm_num,
              ← Real.log_pow, Real.sq_sqrt (by linarith)]
          rw [hsq]
          linarith [Real.log_le_sub_one_of_pos hs_pos]
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hlog_sqrt
        calc ‖h z‖ ≤ 4 * R * Real.log (2 * R) + 3 * ‖h 0‖ := hbc
          _ ≤ 4 * R * (2 * (Real.sqrt 2 * Real.sqrt R)) + 3 * ‖h 0‖ := by
              gcongr
          _ = 8 * Real.sqrt 2 * R * Real.sqrt R + 3 * ‖h 0‖ := by ring
      have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (half_pos hR_pos)
        hh_diff.differentiableOn.diffContOnCl hBC
      have hpow_ge : (R / 2) ^ 2 ≤ (R / 2) ^ k :=
        pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ R / 2) hk
      exact hcauchy.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hpow_ge)
    -- Pick R huge enough that RHS < ‖iteratedDeriv k h 0‖
    let B : ℝ := 4 * (k.factorial : ℝ) * (8 * Real.sqrt 2 + 3 * ‖h 0‖) + 1
    have hB_pos : 0 < B := by positivity
    let R : ℝ := max R₁ ((B / ‖iteratedDeriv k h 0‖ + 1) ^ 2)
    have hR_ge : R₁ ≤ R := le_max_left _ _
    have hR_ge_sq : (B / ‖iteratedDeriv k h 0‖ + 1) ^ 2 ≤ R := le_max_right _ _
    have hR_pos : 0 < R := by linarith
    have hsqrt_ge : B / ‖iteratedDeriv k h 0‖ + 1 ≤ Real.sqrt R := by
      have hnn : 0 ≤ B / ‖iteratedDeriv k h 0‖ + 1 := by positivity
      calc B / ‖iteratedDeriv k h 0‖ + 1 = Real.sqrt ((B / ‖iteratedDeriv k h 0‖ + 1) ^ 2) :=
            (Real.sqrt_sq hnn).symm
        _ ≤ Real.sqrt R := Real.sqrt_le_sqrt hR_ge_sq
    have hsqrt_pos : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR_pos
    have hR_ge1 : 1 ≤ R * Real.sqrt R := by
      have h1 : 1 ≤ Real.sqrt R := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by linarith)
      nlinarith
    have hnum_le : (k.factorial : ℝ) * (8 * Real.sqrt 2 * R * Real.sqrt R + 3 * ‖h 0‖) / (R / 2) ^ 2 ≤
        B / Real.sqrt R := by
      have hrhs : (k.factorial : ℝ) * (8 * Real.sqrt 2 * R * Real.sqrt R + 3 * ‖h 0‖) / (R / 2) ^ 2 =
          4 * (k.factorial : ℝ) * (8 * Real.sqrt 2 * R * Real.sqrt R + 3 * ‖h 0‖) / R ^ 2 := by
        field_simp [hR_pos.ne']; ring
      rw [hrhs, div_le_div_iff₀ (pow_pos hR_pos 2) hsqrt_pos]
      have hsq : Real.sqrt R * Real.sqrt R = R := Real.mul_self_sqrt hR_pos.le
      have hLHS : 4 * (k.factorial : ℝ) * (8 * Real.sqrt 2 * R * Real.sqrt R + 3 * ‖h 0‖) * Real.sqrt R ≤
          4 * (k.factorial : ℝ) * (8 * Real.sqrt 2 + 3 * ‖h 0‖) * (R * Real.sqrt R * Real.sqrt R) := by
        have h1 : 8 * Real.sqrt 2 * R * Real.sqrt R + 3 * ‖h 0‖ ≤
            (8 * Real.sqrt 2 + 3 * ‖h 0‖) * (R * Real.sqrt R) := by
          have hnn : 0 ≤ 3 * ‖h 0‖ := by positivity
          nlinarith
        calc 4 * (k.factorial : ℝ) * (8 * Real.sqrt 2 * R * Real.sqrt R + 3 * ‖h 0‖) * Real.sqrt R
            ≤ 4 * (k.factorial : ℝ) * ((8 * Real.sqrt 2 + 3 * ‖h 0‖) * (R * Real.sqrt R)) * Real.sqrt R := by
              gcongr
          _ = 4 * (k.factorial : ℝ) * (8 * Real.sqrt 2 + 3 * ‖h 0‖) * (R * Real.sqrt R * Real.sqrt R) := by ring
      calc 4 * (k.factorial : ℝ) * (8 * Real.sqrt 2 * R * Real.sqrt R + 3 * ‖h 0‖) * Real.sqrt R
          ≤ 4 * (k.factorial : ℝ) * (8 * Real.sqrt 2 + 3 * ‖h 0‖) * (R * (Real.sqrt R * Real.sqrt R)) := by
            linarith
        _ = 4 * (k.factorial : ℝ) * (8 * Real.sqrt 2 + 3 * ‖h 0‖) * R ^ 2 := by rw [hsq, sq]
        _ ≤ B * R ^ 2 := by dsimp only [B]; nlinarith [pow_pos hR_pos 2]
    have hlt : B / Real.sqrt R < ‖iteratedDeriv k h 0‖ := by
      rw [div_lt_iff₀ hsqrt_pos]
      have h1 : B + ‖iteratedDeriv k h 0‖ ≤ ‖iteratedDeriv k h 0‖ * Real.sqrt R := by
        have hmul := mul_le_mul_of_nonneg_left hsqrt_ge hpos_k.le
        rw [mul_add, mul_div_cancel₀ _ hpos_k.ne', mul_one] at hmul
        exact hmul
      linarith
    linarith [hbd_R R hR_ge]
  -- Hence `h z = h 0 + deriv h 0 * z` globally on `ℂ` via Taylor series
  have hh_affine : ∀ z : ℂ, h z = h 0 + deriv h 0 * z := by
    intro z
    have htay := Complex.taylorSeries_eq_on_ball' (c := (0 : ℂ)) (r := ‖z‖ + 1)
      (hz := by rw [Metric.mem_ball, dist_zero_right]; linarith) hh_diff.differentiableOn
    rw [← htay]
    have hsupp : ∀ k : ℕ, k ∉ Finset.range 2 →
        ((k.factorial : ℂ)⁻¹ * iteratedDeriv k h 0 * (z - 0) ^ k) = 0 := by
      intro k hk
      simp only [Finset.mem_range, not_lt] at hk
      rw [hderiv_zero k hk, mul_zero, zero_mul]
    rw [tsum_eq_sum hsupp, Finset.sum_range_succ, Finset.sum_range_one]
    simp [iteratedDeriv_zero, iteratedDeriv_one]
  -- Exponential upper bound at `z = 2 * (n + 1)` contradicts factorial lower bound!
  let d : ℕ := ∑ ρ ∈ S, analyticOrderNatAt completedXi ρ
  let A : ℝ := ‖h 0‖
  let B : ℝ := ‖deriv h 0‖
  let K : ℝ := Real.pi * ((2 + R₁) ^ d * Real.exp (2 * B + 1))
  have hK_pos : 0 < K := by positivity
  let C₀ : ℝ := (d.factorial : ℝ) * Real.exp A
  have hC₀_pos : 0 < C₀ := by positivity
  have hupper_all : ∀ n : ℕ, (n.factorial : ℝ) ≤ C₀ * K * K ^ n := by
    intro n
    let z : ℂ := ((2 * (n + 1) : ℕ) : ℂ)
    have hlow := norm_completedXi_two_mul_ge n
    have hP_bd : ‖P z‖ ≤ ((2 + R₁) * ((n + 1 : ℕ) : ℝ)) ^ d := by
      dsimp only [P]
      rw [norm_prod]
      simp_rw [norm_pow]
      have hterm : ∀ ρ ∈ S, ‖z - ρ‖ ^ analyticOrderNatAt completedXi ρ ≤
          ((2 + R₁) * ((n + 1 : ℕ) : ℝ)) ^ analyticOrderNatAt completedXi ρ := by
        intro ρ hρ
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
        have hρ_le : ‖ρ‖ ≤ R₁ :=
          (Finset.single_le_sum (f := fun ρ' : ℂ => ‖ρ'‖) (fun _ _ => norm_nonneg _) hρ).trans
            (by linarith [le_max_right 6 (1 + ∑ ρ' ∈ S, ‖ρ'‖)])
        have hz_norm : ‖z‖ = 2 * ((n + 1 : ℕ) : ℝ) := by
          dsimp only [z]; rw [Complex.norm_natCast]; push_cast; ring
        have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
        calc ‖z - ρ‖ ≤ ‖z‖ + ‖ρ‖ := norm_sub_le z ρ
          _ ≤ 2 * ((n + 1 : ℕ) : ℝ) + R₁ := by linarith
          _ ≤ (2 + R₁) * ((n + 1 : ℕ) : ℝ) := by nlinarith
      calc ∏ ρ ∈ S, ‖z - ρ‖ ^ analyticOrderNatAt completedXi ρ
          ≤ ∏ ρ ∈ S, ((2 + R₁) * ((n + 1 : ℕ) : ℝ)) ^ analyticOrderNatAt completedXi ρ :=
            prod_le_prod_real S (fun _ _ => pow_nonneg (norm_nonneg _) _) hterm
        _ = ((2 + R₁) * ((n + 1 : ℕ) : ℝ)) ^ d := by
            rw [← Finset.prod_pow_eq_pow_sum]
    have hpow_exp : ((n + 1 : ℕ) : ℝ) ^ d ≤ (d.factorial : ℝ) * Real.exp ((n + 1 : ℕ) : ℝ) := by
      have h1 := Real.pow_div_factorial_le_exp ((n + 1 : ℕ) : ℝ) (Nat.cast_nonneg _) d
      rwa [div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos d)), mul_comm] at h1
    have hg_bd : ‖g z‖ ≤ Real.exp (A + 2 * B * ((n + 1 : ℕ) : ℝ)) := by
      rw [← hh_exp z, Complex.norm_exp, hh_affine z]
      apply Real.exp_le_exp.mpr
      have h1 : (h 0 + deriv h 0 * z).re ≤ ‖h 0 + deriv h 0 * z‖ :=
        (le_abs_self _).trans (Complex.abs_re_le_norm _)
      have hz_norm : ‖z‖ = 2 * ((n + 1 : ℕ) : ℝ) := by
        dsimp only [z]; rw [Complex.norm_natCast]; push_cast; ring
      calc (h 0 + deriv h 0 * z).re ≤ ‖h 0 + deriv h 0 * z‖ := h1
        _ ≤ ‖h 0‖ + ‖deriv h 0 * z‖ := norm_add_le _ _
        _ = A + 2 * B * ((n + 1 : ℕ) : ℝ) := by rw [norm_mul, hz_norm]; dsimp only [A, B]; ring
    have hxi_bd : ‖completedXi z‖ ≤ C₀ * (((2 + R₁) ^ d * Real.exp (2 * B + 1)) ^ (n + 1)) := by
      rw [hfac z, norm_mul]
      have hP_bd' : ‖P z‖ ≤ (2 + R₁) ^ d * ((d.factorial : ℝ) * Real.exp ((n + 1 : ℕ) : ℝ)) := by
        rw [mul_pow] at hP_bd
        exact hP_bd.trans (mul_le_mul_of_nonneg_left hpow_exp (by positivity))
      have hpow_ge : (2 + R₁) ^ d ≤ ((2 + R₁) ^ d) ^ (n + 1) := by
        have hbase : (1 : ℝ) ≤ (2 + R₁) ^ d := one_le_pow₀ (by linarith)
        calc (2 + R₁) ^ d = ((2 + R₁) ^ d) ^ 1 := (pow_one _).symm
          _ ≤ ((2 + R₁) ^ d) ^ (n + 1) := pow_le_pow_right₀ hbase (Nat.succ_pos n)
      calc ‖P z‖ * ‖g z‖
          ≤ ((2 + R₁) ^ d * ((d.factorial : ℝ) * Real.exp ((n + 1 : ℕ) : ℝ))) *
              Real.exp (A + 2 * B * ((n + 1 : ℕ) : ℝ)) :=
            mul_le_mul hP_bd' hg_bd (norm_nonneg _) (by positivity)
        _ = C₀ * ((2 + R₁) ^ d * Real.exp ((2 * B + 1) * ((n + 1 : ℕ) : ℝ))) := by
            dsimp only [C₀]
            have hexp_mul : Real.exp ((n + 1 : ℕ) : ℝ) * Real.exp (A + 2 * B * ((n + 1 : ℕ) : ℝ)) =
                Real.exp A * Real.exp ((2 * B + 1) * ((n + 1 : ℕ) : ℝ)) := by
              rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
            linear_combination (2 + R₁) ^ d * (d.factorial : ℝ) * hexp_mul
        _ ≤ C₀ * (((2 + R₁) ^ d) ^ (n + 1) * (Real.exp (2 * B + 1)) ^ (n + 1)) := by
            rw [← Real.exp_nat_mul, mul_comm ((n + 1 : ℕ) : ℝ)]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hpow_ge (by positivity)) hC₀_pos.le
        _ = C₀ * (((2 + R₁) ^ d * Real.exp (2 * B + 1)) ^ (n + 1)) := by rw [← mul_pow]
    have hcomb : (n.factorial : ℝ) / Real.pi ^ (n + 1) ≤
        C₀ * (((2 + R₁) ^ d * Real.exp (2 * B + 1)) ^ (n + 1)) := hlow.trans hxi_bd
    rw [div_le_iff₀ (pow_pos Real.pi_pos _)] at hcomb
    calc (n.factorial : ℝ)
        ≤ C₀ * ((2 + R₁) ^ d * Real.exp (2 * B + 1)) ^ (n + 1) * Real.pi ^ (n + 1) := hcomb
      _ = C₀ * K ^ (n + 1) := by dsimp only [K]; rw [mul_pow]; ring
      _ = C₀ * K * K ^ n := by rw [pow_succ']; ring
  -- Contradict `K^n / n! → 0`
  have htend := (Real.summable_pow_div_factorial K).tendsto_atTop_zero
  have hev := htend.eventually (gt_mem_nhds (show (0 : ℝ) < (C₀ * K)⁻¹ by positivity))
  obtain ⟨n, hn⟩ := hev.exists
  have h1 := hupper_all n
  have h2 : (C₀ * K)⁻¹ ≤ K ^ n / (n.factorial : ℝ) := by
    rw [le_div_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos n)), inv_mul_le_iff₀ (mul_pos hC₀_pos hK_pos)]
    linarith
  linarith

/-! ### 3. Unconditional Scalar Strong `ℂ({t})` D-Transcendence at Every Real Center -/

/-- Shifted negative logarithmic derivative of the completed Riemann $\xi$-function at center `c`:
`phiXiAt c w = -ξ'(c + w) / ξ(c + w)`. -/
@[expose] def phiXiAt (c w : ℂ) : ℂ :=
  -deriv completedXi (c + w) / completedXi (c + w)

/-- Canonical symmetric completed-$\xi$ Borel kernel centered at `s = 1 / 2`:
`phiXi w = -ξ'(1/2 + w) / ξ(1/2 + w)`. -/
@[expose] def phiXi (w : ℂ) : ℂ :=
  phiXiAt (1 / 2) w

/-- **Unconditional `PlaneSimplePoleData` Package for `phiXiAt (c : ℂ)`** at every real center `c : ℝ`.
All poles are simple with negative-integer residues equal to `-ord_ρ(ξ)`, with ZERO RH assumed. -/
@[expose] def phiXiAt_planeSimplePoleData (c : ℝ) : PlaneSimplePoleData (phiXiAt (c : ℂ)) :=
  entireLogDeriv_planeSimplePoleData differentiable_completedXi (completedXi_ne_zero_of_real c)

/-- The pole set of `phiXiAt_planeSimplePoleData c` is `{w | completedXi (c + w) = 0}`, which is infinite. -/
theorem phiXiAt_poles_infinite (c : ℝ) : (phiXiAt_planeSimplePoleData c).poles.Infinite := by
  have hpoles : (phiXiAt_planeSimplePoleData c).poles =
      (fun ρ : ℂ => ρ - (c : ℂ)) '' {ρ : ℂ | completedXi ρ = 0} := by
    ext w
    change completedXi ((c : ℂ) + w) = 0 ↔ w ∈ (fun ρ : ℂ => ρ - (c : ℂ)) '' {ρ : ℂ | completedXi ρ = 0}
    constructor
    · intro hw; exact ⟨(c : ℂ) + w, hw, by ring⟩
    · rintro ⟨ρ, hρ, rfl⟩; simpa [add_sub_cancel] using hρ
  rw [hpoles]
  exact completedXi_zeros_infinite.image (fun a _ b _ h => by linear_combination h)

/-- **100% Unconditional Convergent-Germ ADE Obstruction for `completedXi` (`c : ℝ`)**:
At every real center `c : ℝ`, the factorial-moment / formal-Laplace series `formalSeries (phiXiAt c)`
of `-ξ'(c + w)/ξ(c + w)` satisfies no nonzero ADE over `ℂ{w}` with respect to `d_u` (in `t = 1/u`,
not for `ζ(s)` directly as a function of `s`) — with ZERO RH and no extra hypotheses beyond
Mathlib plus this repository's proved modules. -/
theorem completedXi_no_conv_ade (c : ℝ) {r : ℕ}
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : formalEvalConv (formalSeries (phiXiAt (c : ℂ))) Q = 0) : Q = 0 :=
  finite_contour_no_conv_ade (phiXiAt_planeSimplePoleData c) (phiXiAt_poles_infinite c) Q hQ

/-- **100% Unconditional Strong `ℂ({t})` D-Transcendence of `ogfOfEGF (phiXiAt c)`**:
For EVERY real center `c : ℝ` (including `c = 1/2`), the factorial-moment / ordinary generating
function `ogfOfEGF (phiXiAt c)` of `-ξ'(c + w)/ξ(c + w)` is strongly differentially transcendental
in `t = 1/u` over convergent meromorphic germs `ℂ({t})` (not for `ζ(s)` directly as a function
of `s`) — ZERO RH, from Mathlib plus this repository's proved modules with no extra hypotheses. -/
theorem completedXi_ogf_stronglyDTrans (c : ℝ) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF (phiXiAt (c : ℂ))) :=
  finite_contour_ogf_stronglyDTrans (phiXiAt_planeSimplePoleData c) (phiXiAt_poles_infinite c)

/-- **100% Unconditional Strong `ℂ({t})` D-Transcendence of `formalSeries (phiXiAt c)`**:
For EVERY real center `c : ℝ`, the factorial-moment / formal-Laplace series
`formalSeries (phiXiAt c)` of `-ξ'(c + w)/ξ(c + w)` is strongly differentially transcendental in
`t = 1/u` over `ℂ({t})` (not for `ζ(s)` directly as a function of `s`) — ZERO RH. -/
theorem completedXi_formalSeries_stronglyDTrans (c : ℝ) :
    StronglyDTransOverMeromorphicGerms (formalSeries (phiXiAt (c : ℂ))) :=
  finite_contour_formalSeries_stronglyDTrans (phiXiAt_planeSimplePoleData c) (phiXiAt_poles_infinite c)

/-- Specialization at the canonical symmetric center `c = 1 / 2`: `ogfOfEGF phiXi` (the
factorial-moment / formal-Laplace OGF of `-ξ'(1/2 + w)/ξ(1/2 + w)` in `t = 1/u`) is
unconditionally strongly D-transcendental over `ℂ({t})`. -/
theorem phiXi_ogf_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF phiXi) := by
  have heq : phiXi = phiXiAt (((1 / 2 : ℝ) : ℂ)) := by
    funext w; unfold phiXi; push_cast; rfl
  rw [heq]
  exact completedXi_ogf_stronglyDTrans (1 / 2)

/-- Specialization at the canonical symmetric center `c = 1 / 2`: `formalSeries phiXi` (the
formal-Laplace series of `-ξ'(1/2 + w)/ξ(1/2 + w)` in `t = 1/u`) is unconditionally strongly
D-transcendental over `ℂ({t})`. -/
theorem phiXi_formalSeries_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms (formalSeries phiXi) := by
  have heq : phiXi = phiXiAt (((1 / 2 : ℝ) : ℂ)) := by
    funext w; unfold phiXi; push_cast; rfl
  rw [heq]
  exact completedXi_formalSeries_stronglyDTrans (1 / 2)

/-! ### 4. Unconditional Joint Multi-Center Differential Independence over `ℂ({t})` -/

/-- Determinant of a block upper-triangular matrix over `ℂ` indexed by `Fin d × Fin m`:
if all blocks strictly below the block diagonal (`j < i`) vanish, then `A.det` equals the product
of the determinants of the diagonal `m × m` blocks. -/
private lemma det_blockUpperTriangular {d m : ℕ}
    (A : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ)
    (hzero : ∀ i j : Fin d, j < i → ∀ k l : Fin m, A (i, k) (j, l) = 0) :
    A.det = ∏ i : Fin d, (Matrix.of fun k l : Fin m => A (i, k) (i, l)).det := by
  induction d with
  | zero =>
    have hA : A = 1 := by ext ⟨i, _⟩; exact Fin.elim0 i
    rw [Finset.univ_eq_empty, Finset.prod_empty, hA, Matrix.det_one]
  | succ n ih =>
    -- Split `Fin (n + 1) × Fin m` into `(Fin n × Fin m) ⊕ Fin m` putting `Fin.last n` last
    let e : (Fin (n + 1) × Fin m) ≃ ((Fin n × Fin m) ⊕ Fin m) :=
      { toFun := fun p =>
          if h : p.1.val < n then Sum.inl (⟨p.1.val, h⟩, p.2) else Sum.inr p.2
        invFun := fun s => match s with
          | Sum.inl (i, k) => (i.castSucc, k)
          | Sum.inr k => (Fin.last n, k)
        left_inv := fun ⟨i, k⟩ => by
          by_cases h : i.val < n
          · simp only [h, ↓reduceDIte]; ext <;> simp
          · simp only [h, ↓reduceDIte]
            have hi : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
            subst hi; rfl
        right_inv := fun s => by
          cases s with
          | inl p => simp [p.1.isLt]
          | inr k => simp }
    let B : Matrix ((Fin n × Fin m) ⊕ Fin m) ((Fin n × Fin m) ⊕ Fin m) ℂ :=
      Matrix.reindex e e A
    have hdet_eq : A.det = B.det := (Matrix.det_reindex_self e A).symm
    let B₁₁ : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
      Matrix.of fun p q => A (p.1.castSucc, p.2) (q.1.castSucc, q.2)
    let B₁₂ : Matrix (Fin n × Fin m) (Fin m) ℂ :=
      Matrix.of fun p l => A (p.1.castSucc, p.2) (Fin.last n, l)
    let B₂₂ : Matrix (Fin m) (Fin m) ℂ :=
      Matrix.of fun k l => A (Fin.last n, k) (Fin.last n, l)
    have hB_eq : B = Matrix.fromBlocks B₁₁ B₁₂ 0 B₂₂ := by
      ext r c
      cases r with
      | inl p =>
        cases c with
        | inl q => simp [B, B₁₁, e]
        | inr l => simp [B, B₁₂, e]
      | inr k =>
        cases c with
        | inl q =>
          simp only [B, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁,
            Matrix.zero_apply]
          exact hzero (Fin.last n) q.1.castSucc (Fin.castSucc_lt_last q.1) k q.2
        | inr l => simp [B, B₂₂, e]
    rw [hdet_eq, hB_eq, Matrix.det_fromBlocks_zero₂₁]
    have hB₁₁_zero : ∀ i j : Fin n, j < i → ∀ k l : Fin m, B₁₁ (i, k) (j, l) = 0 := by
      intro i j hji k l
      exact hzero i.castSucc j.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hji) k l
    rw [ih B₁₁ hB₁₁_zero, Fin.prod_univ_castSucc]
    rfl

/-- Given an injective map `c : Fin d → ℝ`, there exists a permutation `e : Fin d ≃ Fin d`
sorting `c ∘ e` in strictly increasing order. -/
private lemma exists_perm_strictMono {d : ℕ} (c : Fin d → ℝ) (hc : Function.Injective c) :
    ∃ e : Fin d ≃ Fin d, StrictMono (c ∘ e) := by
  let S : Finset ℝ := Finset.univ.image c
  have hcard : S.card = d := by
    rw [Finset.card_image_of_injective _ hc, Finset.card_fin]
  let f : Fin d ↪o ℝ := S.orderEmbOfFin hcard
  have hmem : ∀ i : Fin d, ∃ j : Fin d, c j = f i := by
    intro i
    have hi : f i ∈ S := Finset.orderEmbOfFin_mem S hcard i
    exact Finset.mem_image.mp hi |> fun ⟨j, _, hj⟩ => ⟨j, hj⟩
  choose g hg using hmem
  have hg_inj : Function.Injective g := fun a b hab => by
    have h1 : f a = f b := by rw [← hg a, ← hg b, hab]
    exact f.injective h1
  let e : Fin d ≃ Fin d := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg_inj)
  refine ⟨e, fun a b hab => ?_⟩
  change c (g a) < c (g b)
  rw [hg a, hg b]
  exact f.strictMono hab

/-- **100% Unconditional Joint Multi-Center Differential Independence over `ℂ({t})` (ZERO RH!)**:
For ANY finite family of pairwise distinct real centers `c : Fin d → ℝ`, the factorial-moment /
formal-Laplace ordinary generating functions `ogfOfEGF (phiXiAt (c 0)), ..., ogfOfEGF (phiXiAt (c (d - 1)))`
of `-ξ'(c_i + w)/ξ(c_i + w)` are **jointly** differentially independent in `t = 1/u` over
convergent meromorphic germs `ℂ({t})` (not for `ζ(s)` directly as a function of `s`). -/
theorem completedXi_joint_ogf_stronglyDTrans {d : ℕ} (c : Fin d → ℝ) (hc : Function.Injective c) :
    JointlyStronglyDTransOverMeromorphicGerms (fun i => ogfOfEGF (phiXiAt (c i : ℂ))) := by
  -- Handle d = 0 directly (empty index set)
  rcases Nat.eq_zero_or_pos d with rfl | hd_pos
  · refine jointlyStronglyDTransOverMeromorphicGerms_of_convergent fun {r} P hP => ?_
    have hconst : P = MvPolynomial.C (P.coeff 0) := by
      apply MvPolynomial.ext; intro α
      by_cases hα : α = 0
      · subst hα; simp
      · exfalso; apply hα; ext ⟨i, _⟩; exact Fin.elim0 i
    rw [hconst, MvPolynomial.eval₂_C] at hP
    have h0 : P.coeff 0 = 0 := toPS_injective (hP.trans (map_zero toPS).symm)
    rw [hconst, h0, map_zero]
  -- For d > 0, apply `finite_contour_joint_ogf_stronglyDTrans` with extremal-strip block Vandermonde
  let h : ∀ i : Fin d, PlaneSimplePoleData (phiXiAt (c i : ℂ)) := fun i => phiXiAt_planeSimplePoleData (c i)
  refine finite_contour_joint_ogf_stronglyDTrans h fun r => ?_
  -- Step 1: Sort centers strictly increasingly via permutation `e`
  obtain ⟨e, he_mono⟩ := exists_perm_strictMono c hc
  let c' : Fin d → ℝ := c ∘ e
  let h' : ∀ i : Fin d, PlaneSimplePoleData (phiXiAt (c' i : ℂ)) := fun i => h (e i)
  -- Step 2: Minimum positive gap δ > 0 between distinct sorted centers
  obtain ⟨δ, hδ_pos, hδ_gap⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i j : Fin d, i < j → δ ≤ c' j - c' i := by
    let pairs : Finset (Fin d × Fin d) := Finset.univ.filter (fun p => p.1 < p.2)
    by_cases hne : pairs.Nonempty
    · obtain ⟨p₀, hp₀_mem, hp₀_min⟩ := pairs.exists_min_image (fun p => c' p.2 - c' p.1) hne
      have hlt : p₀.1 < p₀.2 := (Finset.mem_filter.mp hp₀_mem).2
      refine ⟨c' p₀.2 - c' p₀.1, sub_pos.mpr (he_mono hlt), fun i j hij => ?_⟩
      exact hp₀_min (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)
    · refine ⟨1, zero_lt_one, fun i j hij => ?_⟩
      exfalso; exact hne ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩
  -- Step 3: Left-extremal accumulation abscissa L ∈ [0, 1] of Z_ξ
  let Z : Set ℂ := {ρ : ℂ | completedXi ρ = 0}
  have hZ_inf : Z.Infinite := completedXi_zeros_infinite
  let A : Set ℝ := {x : ℝ | {ρ ∈ Z | ρ.re < x}.Finite}
  have hA_ne : A.Nonempty := by
    refine ⟨0, ?_⟩
    change {ρ ∈ Z | ρ.re < 0}.Finite
    have hemp : {ρ ∈ Z | ρ.re < 0} = ∅ := by
      ext ρ; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
      intro hρ; exact (completedXi_zero_mem_strip hρ).1.le
    rw [hemp]; exact Set.finite_empty
  have hA_bdd : BddAbove A := by
    refine ⟨1, fun x hx => ?_⟩
    by_contra! hgt
    change {ρ ∈ Z | ρ.re < x}.Finite at hx
    have heq : {ρ ∈ Z | ρ.re < x} = Z := by
      ext ρ; simp only [Set.mem_ofPred_eq, and_iff_left_iff_imp]
      intro hρ; exact (completedXi_zero_mem_strip hρ).2.1.trans hgt
    rw [heq] at hx
    exact hZ_inf hx
  let L : ℝ := sSup A
  let ε : ℝ := δ / 4
  have hε_pos : 0 < ε := by positivity
  -- Left of L - ε has finitely many zeros
  have hF_bad_fin : {ρ ∈ Z | ρ.re < L - ε}.Finite := by
    obtain ⟨x, hxA, hxgt⟩ := exists_lt_of_lt_csSup hA_ne (show L - ε < L by linarith)
    exact hxA.subset fun ρ hρ => ⟨hρ.1, hρ.2.trans hxgt⟩
  -- Left of L + ε has infinitely many zeros
  have hLeft_inf : {ρ ∈ Z | ρ.re < L + ε}.Infinite := by
    intro hfin
    have hmem : L + ε ∈ A := hfin
    have hle : L + ε ≤ L := le_csSup hA_bdd hmem
    linarith
  -- Hence the strip [L - ε, L + ε) has infinitely many zeros
  let Strip : Set ℂ := {ρ ∈ Z | L - ε ≤ ρ.re ∧ ρ.re < L + ε}
  have hStrip_inf : Strip.Infinite := by
    intro hfin
    have hsub : {ρ ∈ Z | ρ.re < L + ε} ⊆ {ρ ∈ Z | ρ.re < L - ε} ∪ Strip := by
      intro ρ ⟨hρZ, hρlt⟩
      by_cases hlt : ρ.re < L - ε
      · exact Or.inl ⟨hρZ, hlt⟩
      · exact Or.inr ⟨hρZ, not_lt.mp hlt, hρlt⟩
    exact hLeft_inf ((hF_bad_fin.union hfin).subset hsub)
  -- Step 4: Exclude finitely many translates of F_bad
  let F_bad : Set ℂ := {ρ ∈ Z | ρ.re < L - ε}
  let E_bad : Set ℂ := ⋃ (p : Fin d × Fin d), (fun ρ' : ℂ => ρ' + ((c' p.1 - c' p.2 : ℝ) : ℂ)) '' F_bad
  have hE_bad_fin : E_bad.Finite :=
    Set.finite_iUnion fun _ => hF_bad_fin.image _
  have hGood_inf : (Strip \ E_bad).Infinite := hStrip_inf.sdiff hE_bad_fin
  -- Step 5: Pick r + 1 distinct zeros ρ₀, ..., ρᵣ ∈ Strip \ E_bad
  obtain ⟨S_ρ, hS_sub, hS_card⟩ := hGood_inf.exists_subset_card_eq (r + 1)
  let eS : Fin (r + 1) ≃ S_ρ := (S_ρ.equivFin.trans (finCongr hS_card)).symm
  let ρ : Fin (r + 1) → ℂ := fun k => (eS k).val
  have hρ_inj : Function.Injective ρ := fun a b hab => eS.injective (Subtype.ext hab)
  have hρ_mem : ∀ k, ρ k ∈ Strip \ E_bad := fun k => hS_sub (Finset.mem_coe.mpr (eS k).property)
  -- Step 6: Build sorted-center pole family ω' (i, k) = ρ k - c' i
  let ω' : Fin d × Fin (r + 1) → ℂ := fun p => ρ p.2 - (c' p.1 : ℂ)
  have hω'_mem_own : ∀ (i : Fin d) (k : Fin (r + 1)), ω' (i, k) ∈ (h' i).poles := by
    intro i k
    have hρk : completedXi (ρ k) = 0 := (hρ_mem k).1.1
    change completedXi ((c' i : ℂ) + (ρ k - (c' i : ℂ))) = 0
    simpa [add_sub_cancel] using hρk
  have hω'_not_prev : ∀ {i j : Fin d}, j < i → ∀ k : Fin (r + 1), ω' (i, k) ∉ (h' j).poles := by
    intro i j hji k hmem
    -- If ω' (i, k) ∈ (h' j).poles, then ρ' = ρ k - c' i + c' j ∈ Z with Re ρ' < L - ε
    let ρ' : ℂ := (c' j : ℂ) + ω' (i, k)
    have hρ'_Z : ρ' ∈ Z := hmem
    have hρ'_re : ρ'.re < L - ε := by
      have hgap := hδ_gap j i hji
      have hρk_lt : (ρ k).re < L + ε := (hρ_mem k).1.2.2
      dsimp only [ρ', ω']
      simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re]
      dsimp only [ε] at hρk_lt ⊢
      linarith
    have hρ'_bad : ρ' ∈ F_bad := ⟨hρ'_Z, hρ'_re⟩
    have hρk_bad : ρ k ∈ E_bad := by
      refine Set.mem_iUnion.mpr ⟨(i, j), ⟨ρ', hρ'_bad, ?_⟩⟩
      dsimp only [ρ', ω']; push_cast; ring
    exact (hρ_mem k).2 hρk_bad
  -- Step 7: Show the sorted matrix M' has nonzero determinant
  let M' : Matrix (Fin d × Fin (r + 1)) (Fin d × Fin (r + 1)) ℂ :=
    Matrix.of fun p q => jointVec h' (ω' p) q
  have hM'_zero : ∀ i j : Fin d, j < i → ∀ k l : Fin (r + 1), M' (i, k) (j, l) = 0 := by
    intro i j hji k l
    change jointVec h' (ω' (i, k)) (j, l) = 0
    unfold jointVec
    simp [PlaneSimplePoleData.extRes, hω'_not_prev hji k]
  have hM'_det_ne : M'.det ≠ 0 := by
    rw [det_blockUpperTriangular M' hM'_zero]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    let D_i : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
      Matrix.of fun k l => M' (i, k) (i, l)
    let rowScale : Fin (r + 1) → ℂ := fun k => (h' i).res (ω' (i, k))
    let nodes : Fin (r + 1) → ℂ := fun k => -ω' (i, k)
    have hD_eq : D_i = Matrix.diagonal rowScale * Matrix.vandermonde nodes := by
      ext k l
      simp only [D_i, M', Matrix.of_apply, Matrix.diagonal_mul, Matrix.vandermonde_apply,
        rowScale, nodes, jointVec, PlaneSimplePoleData.extRes, hω'_mem_own i k, ↓reduceIte]
    change D_i.det ≠ 0
    rw [hD_eq, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_vandermonde]
    refine mul_ne_zero ?_ ?_
    · refine Finset.prod_ne_zero_iff.mpr fun k _ => (h' i).res_ne_zero (ω' (i, k)) (hω'_mem_own i k)
    · refine Finset.prod_ne_zero_iff.mpr fun a _ => Finset.prod_ne_zero_iff.mpr fun b hb => ?_
      rw [Finset.mem_Ioi] at hb
      refine sub_ne_zero.mpr fun heq => ?_
      have hω_eq : ω' (i, b) = ω' (i, a) := by linear_combination -heq
      have hρ_eq : ρ b = ρ a := by dsimp only [ω'] at hω_eq; linear_combination hω_eq
      exact ne_of_gt hb (hρ_inj hρ_eq)
  -- Step 8: Permute indices back from sorted `c' = c ∘ e` to original `c`
  let σ : (Fin d × Fin (r + 1)) ≃ (Fin d × Fin (r + 1)) :=
    Equiv.prodCongr e.symm (Equiv.refl (Fin (r + 1)))
  let ω : Fin d × Fin (r + 1) → ℂ := fun p => ω' (σ p)
  have hpoles_eq : ∀ (j : Fin d), (h j).poles = (h' (e.symm j)).poles := fun j => by
    change (h j).poles = (h (e (e.symm j))).poles
    have hej : e (e.symm j) = j := e.apply_symm_apply j
    rw [hej]
  have hextRes_eq : ∀ (j : Fin d) (z : ℂ), (h j).extRes z = (h' (e.symm j)).extRes z := fun j z => by
    change (h j).extRes z = (h (e (e.symm j))).extRes z
    have hej : e (e.symm j) = j := e.apply_symm_apply j
    rw [hej]
  refine ⟨ω, fun p => ?_, ?_⟩
  · refine Set.mem_iUnion.mpr ⟨p.1, ?_⟩
    have hmem' : ω p ∈ (h' (e.symm p.1)).poles := hω'_mem_own (e.symm p.1) p.2
    rwa [← hpoles_eq p.1] at hmem'
  · have hmat : (Matrix.of fun p q => jointVec h (ω p) q) = Matrix.reindex σ.symm σ.symm M' := by
      ext ⟨i, k⟩ ⟨j, l⟩
      simp only [Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        M', σ, ω, Equiv.prodCongr_apply, Equiv.refl_apply, Prod.map_apply]
      unfold jointVec
      rw [hextRes_eq j]
    change (Matrix.of fun p q => jointVec h (ω p) q).det ≠ 0
    rw [hmat, Matrix.det_reindex_self]
    exact hM'_det_ne

/-! ### 5. Unconditional Real-Axis Laplace Integral `B_xi` & `ℂ{1/u}` ADE Obstruction -/

/-- The actual real-axis Laplace integral of the completed-$\xi$ logarithmic derivative
centered at `c : ℝ`:
`B_xi c u = ∫_{0}^{∞} e^{-u w} (-ξ'(c + w) / ξ(c + w)) dw`. -/
@[expose] def B_xi (c : ℝ) (u : ℝ) : ℂ :=
  ∫ w in Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * (w : ℂ)) * phiXiAt (c : ℂ) (w : ℂ)

/-- Elementary linear bound on the real logarithmic derivative of `Complex.Gamma` for `y ≥ 1`,
proved directly from `Complex.Gamma_add_one` without trigamma series. -/
private lemma norm_logDeriv_Gamma_real_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, 1 ≤ y →
      ‖deriv Complex.Gamma (y : ℂ) / Complex.Gamma (y : ℂ)‖ ≤ M + y := by
  have hG_an : ∀ y : ℝ, 0 < y → AnalyticAt ℂ Complex.Gamma (y : ℂ) := fun y hy => by
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hdiff : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := fun z hz => by
      refine (Complex.differentiableAt_Gamma z fun m hm => ?_).differentiableWithinAt
      have hre := congrArg Complex.re hm
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      linarith [Nat.cast_nonneg (α := ℝ) m, show (0 : ℝ) < z.re from hz]
    exact (hdiff.analyticOnNhd hopen) (y : ℂ) (by simpa using hy)
  have hG_ne : ∀ y : ℝ, 0 < y → Complex.Gamma (y : ℂ) ≠ 0 := fun y hy =>
    Complex.Gamma_ne_zero fun m hm => by
      have hre := congrArg Complex.re hm
      simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
      linarith [Nat.cast_nonneg (α := ℝ) m]
  have hcont : ContinuousOn (fun y : ℝ => deriv Complex.Gamma (y : ℂ) / Complex.Gamma (y : ℂ)) (Icc 1 2) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy.1
    have hana := (hG_an y hy0).deriv.div (hG_an y hy0) (hG_ne y hy0)
    exact (hana.continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let M : ℝ := max M₀ 0
  have hM_nn : 0 ≤ M := le_max_right _ _
  -- Recurrence: `Γ'(z+1)/Γ(z+1) = Γ'(z)/Γ(z) + 1/z` for `Re z > 0`
  have hstep : ∀ y : ℝ, 0 < y →
      deriv Complex.Gamma ((y + 1 : ℝ) : ℂ) / Complex.Gamma ((y + 1 : ℝ) : ℂ) =
        deriv Complex.Gamma (y : ℂ) / Complex.Gamma (y : ℂ) + 1 / (y : ℂ) := by
    intro y hy
    have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    have hshift : HasDerivAt (fun z : ℂ => Complex.Gamma (z + 1)) (deriv Complex.Gamma ((y : ℂ) + 1)) (y : ℂ) := by
      have h1 := (hG_an (y + 1) (by linarith)).differentiableAt.hasDerivAt
      rw [Complex.ofReal_add, Complex.ofReal_one] at h1
      exact (h1.comp (y : ℂ) ((hasDerivAt_id (y : ℂ)).add_const 1)).congr_deriv (mul_one _)
    have hmul : HasDerivAt (fun z : ℂ => z * Complex.Gamma z)
        (1 * Complex.Gamma (y : ℂ) + (y : ℂ) * deriv Complex.Gamma (y : ℂ)) (y : ℂ) :=
      (hasDerivAt_id (y : ℂ)).mul (hG_an y hy).differentiableAt.hasDerivAt
    have heq : (fun z : ℂ => Complex.Gamma (z + 1)) =ᶠ[𝓝 (y : ℂ)] (fun z : ℂ => z * Complex.Gamma z) := by
      filter_upwards [isOpen_ne.mem_nhds hyC] with z hz
      exact Complex.Gamma_add_one z hz
    have hd_eq : deriv Complex.Gamma ((y : ℂ) + 1) =
        Complex.Gamma (y : ℂ) + (y : ℂ) * deriv Complex.Gamma (y : ℂ) := by
      have h := (hshift.congr_of_eventuallyEq heq.symm).unique hmul
      simpa using h
    rw [Complex.ofReal_add, Complex.ofReal_one, hd_eq, Complex.Gamma_add_one (y : ℂ) hyC]
    have hgy := hG_ne y hy
    field_simp [hyC, hgy]
    ring
  have hind : ∀ (n : ℕ) (y₀ : ℝ), 1 ≤ y₀ → y₀ ≤ 2 →
      ‖deriv Complex.Gamma ((y₀ + n : ℝ) : ℂ) / Complex.Gamma ((y₀ + n : ℝ) : ℂ)‖ ≤ M + n := by
    intro n
    induction n with
    | zero =>
      intro y₀ h1 h2
      simp only [Nat.cast_zero, add_zero]
      exact (hM₀ y₀ ⟨h1, h2⟩).trans (le_max_left _ _)
    | succ k ih =>
      intro y₀ h1 h2
      have hrew : y₀ + ((k + 1 : ℕ) : ℝ) = (y₀ + (k : ℝ)) + 1 := by push_cast; ring
      rw [hrew, hstep (y₀ + (k : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) k])]
      have h1k : (1 : ℝ) ≤ y₀ + (k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
      have hinv : ‖(1 : ℂ) / ((y₀ + (k : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        exact div_le_one_of_le₀ h1k (by linarith)
      calc ‖deriv Complex.Gamma ((y₀ + (k : ℝ) : ℝ) : ℂ) / Complex.Gamma ((y₀ + (k : ℝ) : ℝ) : ℂ) +
              1 / ((y₀ + (k : ℝ) : ℝ) : ℂ)‖
          ≤ ‖deriv Complex.Gamma ((y₀ + (k : ℝ) : ℝ) : ℂ) / Complex.Gamma ((y₀ + (k : ℝ) : ℝ) : ℂ)‖ +
              ‖(1 : ℂ) / ((y₀ + (k : ℝ) : ℝ) : ℂ)‖ := norm_add_le _ _
        _ ≤ (M + (k : ℝ)) + 1 := add_le_add (ih y₀ h1 h2) hinv
        _ = M + ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  refine ⟨M, hM_nn, fun y hy => ?_⟩
  let n : ℕ := Nat.floor y - 1
  have hfl_ge1 : 1 ≤ Nat.floor y := Nat.le_floor (by exact_mod_cast hy)
  have hn_cast : (n : ℝ) = (Nat.floor y : ℝ) - 1 := by
    dsimp only [n]; rw [Nat.cast_sub hfl_ge1, Nat.cast_one]
  let y₀ : ℝ := y - (n : ℝ)
  have hy₀_ge1 : 1 ≤ y₀ := by
    dsimp only [y₀]; rw [hn_cast]; linarith [Nat.floor_le (show (0 : ℝ) ≤ y by linarith)]
  have hy₀_le2 : y₀ ≤ 2 := by
    dsimp only [y₀]; rw [hn_cast]; linarith [Nat.lt_floor_add_one y]
  have hy_eq : y = y₀ + (n : ℝ) := by dsimp only [y₀]; ring
  rw [hy_eq]
  exact (hind n y₀ hy₀_ge1 hy₀_le2).trans (by linarith)

/-- **Unconditional Positive Real-Axis `ExpType` Bound for `phiXiAt (c : ℂ)`** (`c : ℝ`):
Using `phiLambda_expType_pos_real_unconditional` and `norm_logDeriv_Gamma_real_le`,
`phiXiAt (c : ℂ)` has exponential type along `[0, ∞)` for every `c : ℝ`. -/
theorem phiXiAt_expType_pos_real (c : ℝ) :
    ExpType (Minor.pull (1 : ℂ) (phiXiAt (c : ℂ))) := by
  let R₀ : ℝ := max 0 (2 - c)
  have hR₀_nn : 0 ≤ R₀ := le_max_left _ _
  have hcont : ContinuousOn (fun v : ℝ => Minor.pull (1 : ℂ) (phiXiAt (c : ℂ)) v) (Icc 0 R₀) := by
    intro v _
    have hne : completedXi ((c : ℂ) + (v : ℂ)) ≠ 0 := by
      rw [← Complex.ofReal_add]; exact completedXi_ne_zero_of_real (c + v)
    have hana : AnalyticAt ℂ (phiXiAt (c : ℂ)) (v : ℂ) := by
      have hdiff_on := differentiable_completedXi.differentiableOn.analyticOnNhd isOpen_univ
      have hxi : AnalyticAt ℂ completedXi ((c : ℂ) + (v : ℂ)) := hdiff_on _ (Set.mem_univ _)
      have hadd : AnalyticAt ℂ (fun w : ℂ => (c : ℂ) + w) (v : ℂ) := analyticAt_const.add analyticAt_id
      unfold phiXiAt
      exact (hxi.deriv.comp hadd).neg.div (hxi.comp hadd) hne
    have hcomp : ContinuousAt (fun x : ℝ => phiXiAt (c : ℂ) (x : ℂ)) v :=
      hana.continuousAt.comp Complex.continuous_ofReal.continuousAt
    simpa [Minor.pull] using hcomp.continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨M_Γ, hM_Γ_nn, hΓ_bd⟩ := norm_logDeriv_Gamma_real_le
  obtain ⟨C_Λ, α_Λ, hC_Λ_nn, hα_Λ_nn, hΛ_bd⟩ := phiLambda_expType_pos_real_unconditional
  let α : ℝ := max 1 α_Λ
  have hα_ge1 : 1 ≤ α := le_max_left _ _
  have hα_geΛ : α_Λ ≤ α := le_max_right _ _
  have hα_nn : 0 ≤ α := by linarith
  let K₁ : ℝ := 5 / 2 + |Real.log Real.pi| / 2 + M_Γ / 2 + |c| / 4 + 1 / 4
  let C : ℝ := max (max M₀ 0) (K₁ + C_Λ * Real.exp (α_Λ * |c - 1 / 2|))
  have hC_nn : 0 ≤ C := le_trans (le_max_right M₀ 0) (le_max_left _ _)
  refine ⟨C, α, hC_nn, hα_nn, fun v hv => ?_⟩
  have hexp_ge1 : 1 ≤ Real.exp (α * v) := Real.one_le_exp (mul_nonneg hα_nn hv)
  by_cases hvR : v ≤ R₀
  · calc ‖Minor.pull (1 : ℂ) (phiXiAt (c : ℂ)) v‖
        ≤ M₀ := hM₀ v ⟨hv, hvR⟩
      _ ≤ C := (le_max_left M₀ 0).trans (le_max_left _ _)
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * Real.exp (α * v) := mul_le_mul_of_nonneg_left hexp_ge1 hC_nn
  · push Not at hvR
    have hx_gt2 : 2 < c + v := by
      have : 2 - c < v := lt_of_le_of_lt (le_max_right 0 (2 - c)) hvR
      linarith
    let x : ℝ := c + v
    let s : ℂ := (x : ℂ)
    have hs_re : 2 < s.re := by simpa [s] using hx_gt2
    have hs0 : s ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hs1 : s - 1 ≠ 0 := by
      intro h0; have hre := congrArg Complex.re h0; simp [s] at hre; linarith
    have hζ_ne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
    have hG_ne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero fun m hm => by
      have hre := congrArg Complex.re hm
      simp only [s, Complex.div_ofNat_re, Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
      linarith [Nat.cast_nonneg (α := ℝ) m]
    have hpi_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      rintro ⟨hpi, _⟩; exact Real.pi_ne_zero (Complex.ofReal_eq_zero.mp hpi)
    -- Logarithmic derivative decomposition of `completedXi` at `s = x > 2`
    have hlogd : deriv completedXi s / completedXi s =
        1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
        (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) / 2 +
        deriv riemannZeta s / riemannZeta s := by
      have hloc : completedXi =ᶠ[𝓝 s]
          fun z : ℂ => ((1 / 2 : ℂ) * (z * (z - 1)) * ((Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2))) *
            riemannZeta z := by
        have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
        filter_upwards [hopen.mem_nhds (by linarith : 1 < s.re)] with z hz
        have hz1 : z ≠ 1 := fun h => by simp [h] at hz
        rw [completedXi_eq_mul_zeta (lt_trans zero_lt_one hz) hz1, Gammaℝ_def]
        ring
      have hd_poly : HasDerivAt (fun z : ℂ => z * (z - 1)) (2 * s - 1) s := by
        have h := (hasDerivAt_id s).fun_mul ((hasDerivAt_id s).sub_const 1)
        exact h.congr_deriv (by simp; ring)
      have hd_pi : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
          ((-(Real.log Real.pi : ℂ) / 2) * (Real.pi : ℂ) ^ (-s / 2)) s := by
        have h1 : HasDerivAt (fun z : ℂ => -z / 2) ((-1 : ℂ) / 2) s :=
          (hasDerivAt_id s).neg.div_const 2
        have hpiC : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        have h2 := h1.const_cpow (Or.inl hpiC)
        refine h2.congr_deriv ?_
        rw [← Complex.ofReal_log Real.pi_pos.le]; ring
      have hd_G : HasDerivAt (fun z : ℂ => Complex.Gamma (z / 2))
          ((1 / 2 : ℂ) * deriv Complex.Gamma (s / 2)) s := by
        have hdiffG : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
          Complex.differentiableAt_Gamma (s / 2) fun m hm => by
            have hre := congrArg Complex.re hm
            simp only [s, Complex.div_ofNat_re, Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
            linarith [Nat.cast_nonneg (α := ℝ) m]
        have h := hdiffG.hasDerivAt.comp s ((hasDerivAt_id s).div_const 2)
        exact h.congr_deriv (by ring)
      have hd_ζ : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
        (differentiableAt_riemannZeta (fun h => hs1 (sub_eq_zero.mpr h))).hasDerivAt
      have hd_all := ((((hd_poly.const_mul (1 / 2 : ℂ)).fun_mul (hd_pi.fun_mul hd_G)).fun_mul hd_ζ)).congr_of_eventuallyEq hloc
      have hderiv_val : deriv completedXi s = _ := hd_all.deriv
      have hval : completedXi s =
          ((1 / 2 : ℂ) * (s * (s - 1)) * ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2))) * riemannZeta s :=
        hloc.self_of_nhds
      rw [hderiv_val, hval]
      field_simp [hs0, hs1, hpi_ne, hG_ne, hζ_ne]
      ring
    -- Bound each piece
    have hinv_s : ‖(1 : ℂ) / s‖ ≤ 1 / 2 := by
      rw [norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      exact div_le_div_of_nonneg_left zero_le_one two_pos (by linarith)
    have hinv_s1 : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 := by
      have hcast : s - 1 = ((x - 1 : ℝ) : ℂ) := by dsimp only [s]; push_cast; rfl
      rw [hcast, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      exact div_le_one_of_le₀ (by linarith) (by linarith)
    have hpi_bd : ‖(Real.log Real.pi : ℂ) / 2‖ = |Real.log Real.pi| / 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat]
    have hG_norm : ‖(deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) / 2‖ ≤
        M_Γ / 2 + (|c| / 4 + 1 / 4) * Real.exp (α * v) := by
      have hs2 : s / 2 = ((x / 2 : ℝ) : ℂ) := by dsimp only [s]; push_cast; rfl
      rw [norm_div, Complex.norm_ofNat, hs2]
      have h1 := hΓ_bd (x / 2) (by dsimp only [x]; linarith)
      have hv_exp : v ≤ Real.exp (α * v) := by
        have h1e : 1 + α * v ≤ Real.exp (α * v) := by linarith [Real.add_one_le_exp (α * v)]
        nlinarith
      have hx_le : x ≤ |c| + v := by dsimp only [x]; linarith [le_abs_self c]
      calc ‖deriv Complex.Gamma ((x / 2 : ℝ) : ℂ) / Complex.Gamma ((x / 2 : ℝ) : ℂ)‖ / 2
          ≤ (M_Γ + x / 2) / 2 := by linarith
        _ ≤ M_Γ / 2 + |c| / 4 + v / 4 := by linarith
        _ ≤ M_Γ / 2 + (|c| / 4) * Real.exp (α * v) + (1 / 4) * Real.exp (α * v) := by
            have hc1 : |c| / 4 ≤ (|c| / 4) * Real.exp (α * v) :=
              le_mul_of_one_le_right (by positivity) hexp_ge1
            linarith
        _ = M_Γ / 2 + (|c| / 4 + 1 / 4) * Real.exp (α * v) := by ring
    have hζ_norm : ‖deriv riemannZeta s / riemannZeta s‖ ≤
        C_Λ * Real.exp (α_Λ * |c - 1 / 2|) * Real.exp (α * v) + 1 := by
      let u : ℝ := x - 1 / 2
      have hu_nn : 0 ≤ u := by dsimp only [u, x]; linarith
      have hu_ne : (u : ℂ) ≠ 1 / 2 := by
        intro h0; have hre := congrArg Complex.re h0; simp [u, x] at hre; linarith
      have hs_eq : (1 / 2 : ℂ) + (u : ℂ) = s := by dsimp only [u, s]; push_cast; ring
      have hraw := phiLambda_eq_raw hu_ne (by rwa [hs_eq])
      rw [phiLambdaRaw, hs_eq] at hraw
      have hsub_eq : (u : ℂ) - 1 / 2 = s - 1 := by dsimp only [u, s]; push_cast; ring
      have hrel : deriv riemannZeta s / riemannZeta s = -phiLambda (u : ℂ) - 1 / (s - 1) := by
        rw [hraw, hsub_eq]; ring
      rw [hrel]
      have hΛu : ‖phiLambda (u : ℂ)‖ ≤ C_Λ * Real.exp (α_Λ * u) := by
        simpa [Minor.pull] using hΛ_bd u hu_nn
      have hu_le : u ≤ |c - 1 / 2| + v := by
        dsimp only [u, x]; linarith [le_abs_self (c - 1 / 2)]
      have hexp_u : Real.exp (α_Λ * u) ≤ Real.exp (α_Λ * |c - 1 / 2|) * Real.exp (α * v) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h1 : α_Λ * u ≤ α_Λ * |c - 1 / 2| + α_Λ * v := by nlinarith
        have h2 : α_Λ * v ≤ α * v := mul_le_mul_of_nonneg_right hα_geΛ hv
        linarith
      calc ‖-phiLambda (u : ℂ) - 1 / (s - 1)‖
          ≤ ‖-phiLambda (u : ℂ)‖ + ‖(1 : ℂ) / (s - 1)‖ := norm_sub_le _ _
        _ = ‖phiLambda (u : ℂ)‖ + ‖(1 : ℂ) / (s - 1)‖ := by rw [norm_neg]
        _ ≤ C_Λ * Real.exp (α_Λ * u) + 1 := add_le_add hΛu hinv_s1
        _ ≤ C_Λ * (Real.exp (α_Λ * |c - 1 / 2|) * Real.exp (α * v)) + 1 := by gcongr
        _ = C_Λ * Real.exp (α_Λ * |c - 1 / 2|) * Real.exp (α * v) + 1 := by ring
    -- Combine all 5 bounds
    have hphi_eq : Minor.pull (1 : ℂ) (phiXiAt (c : ℂ)) v = -(deriv completedXi s / completedXi s) := by
      simp only [Minor.pull, one_mul, phiXiAt, neg_div]
      congr 1; dsimp only [s, x]; push_cast; rfl
    rw [hphi_eq, norm_neg, hlogd]
    have htri : ‖1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
          (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) / 2 +
          deriv riemannZeta s / riemannZeta s‖ ≤
        ‖(1 : ℂ) / s‖ + ‖(1 : ℂ) / (s - 1)‖ + ‖(Real.log Real.pi : ℂ) / 2‖ +
          ‖(deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) / 2‖ +
          ‖deriv riemannZeta s / riemannZeta s‖ := by
      have h1 := norm_add_le (1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
          (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) / 2) (deriv riemannZeta s / riemannZeta s)
      have h2 := norm_add_le (1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2)
          ((deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) / 2)
      have h3 := norm_sub_le (1 / s + 1 / (s - 1)) ((Real.log Real.pi : ℂ) / 2)
      have h4 := norm_add_le ((1 : ℂ) / s) ((1 : ℂ) / (s - 1))
      linarith
    have hconst_le : (5 / 2 + |Real.log Real.pi| / 2 + M_Γ / 2) ≤
        (5 / 2 + |Real.log Real.pi| / 2 + M_Γ / 2) * Real.exp (α * v) :=
      le_mul_of_one_le_right (by positivity) hexp_ge1
    have hC_ge : K₁ + C_Λ * Real.exp (α_Λ * |c - 1 / 2|) ≤ C := le_max_right _ _
    calc ‖1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 +
            (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) / 2 +
            deriv riemannZeta s / riemannZeta s‖
        ≤ 1 / 2 + 1 + |Real.log Real.pi| / 2 + (M_Γ / 2 + (|c| / 4 + 1 / 4) * Real.exp (α * v)) +
            (C_Λ * Real.exp (α_Λ * |c - 1 / 2|) * Real.exp (α * v) + 1) := by linarith
      _ = (5 / 2 + |Real.log Real.pi| / 2 + M_Γ / 2) +
            (|c| / 4 + 1 / 4 + C_Λ * Real.exp (α_Λ * |c - 1 / 2|)) * Real.exp (α * v) := by ring
      _ ≤ (K₁ + C_Λ * Real.exp (α_Λ * |c - 1 / 2|)) * Real.exp (α * v) := by
            dsimp only [K₁]; linarith
      _ ≤ C * Real.exp (α * v) := mul_le_mul_of_nonneg_right hC_ge (Real.exp_pos _).le

/-- **Unconditional All-Orders Asymptotic Expansion of `B_xi c` and All Its Derivatives**:
At every real center `c : ℝ` and every derivative order `j : ℕ`, `iteratedDeriv j (B_xi c)` has
full `1 / u`-asymptotic expansion `d_u^[j] (formalSeries (phiXiAt c))` as `u → +∞`. -/
theorem B_xi_hasAsympExp (c : ℝ) (j : ℕ) :
    HasAsympExp (iteratedDeriv j (B_xi c)) (d_u^[j] (formalSeries (phiXiAt (c : ℂ)))) := by
  let U : Set ℂ := {w : ℂ | |w.im| < 1 / 2}
  have hU : Domain U := by
    refine ⟨isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const,
      fun z hz t ht => ?_⟩
    change |((t : ℂ) * z).im| < 1 / 2
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      abs_mul, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg _) ht.2).trans_lt hz
  have hray : ContainsRay U (1 : ℂ) := fun t _ => by
    change |((1 : ℂ) * (t : ℂ)).im| < 1 / 2
    simp
  let a : Minor := ⟨0, phiXiAt (c : ℂ)⟩
  have ha_an : AnalyticOnNhd ℂ a.density U := by
    intro w hw
    have hne : completedXi ((c : ℂ) + w) ≠ 0 := by
      refine completedXi_ne_zero_of_abs_im_le_half ?_
      have him : ((c : ℂ) + w).im = w.im := by simp
      rw [him]; exact le_of_lt hw
    have hxi := (differentiable_completedXi.differentiableOn.analyticOnNhd isOpen_univ)
      ((c : ℂ) + w) (Set.mem_univ _)
    have hadd : AnalyticAt ℂ (fun z : ℂ => (c : ℂ) + z) w := analyticAt_const.add analyticAt_id
    unfold a phiXiAt
    exact (hxi.deriv.comp hadd).neg.div (hxi.comp hadd) hne
  have ha_good : a.Good U (1 : ℂ) := ⟨ha_an, phiXiAt_expType_pos_real c⟩
  have hval_eq : (fun t : ℝ => a.value (1 : ℂ) (t : ℂ)) = B_xi c := by
    funext u
    simp only [Minor.value, complexLaplace, damped, Minor.pull, a, B_xi, zero_add, one_mul, mul_one]
  have hser_eq : a.toSeries = formalSeries (phiXiAt (c : ℂ)) := by
    ext k; cases k <;> simp [Minor.toSeries, formalSeries, a]
  rw [← hval_eq, ← hser_eq]
  -- Standard Minor asymptotic expansion (identical to `minor_value_hasAsympExp_uncond`)
  let ej : BorelExpr := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  obtain ⟨good_j, rep_j⟩ := ej.represents hU hray ha_good
  have h1re : (0 : ℝ) < (1 : ℂ).re := by simp
  have hjet_eq := (BorelExpr.jetIter_eval_eq_iteratedDeriv a hU hray ha_good h1re j).1
  have hser_j : (ej.residual a).toSeries = d_u^[j] a.toSeries := by
    have h0 : (0 : ℂ) ∈ U := by simp [U]
    clear good_j rep_j hjet_eq
    induction j with
    | zero => rfl
    | succ k ih =>
      have hgk := ((Nat.iterate BorelExpr.jet k BorelExpr.leaf).represents hU hray ha_good).1.1 0 h0
      dsimp only [ej]
      rw [Function.iterate_succ_apply' BorelExpr.jet k BorelExpr.leaf,
        Function.iterate_succ_apply' d_u k a.toSeries]
      exact (Minor.toSeries_jet hgk).trans (congrArg d_u ih)
  have ht_far : Tendsto (fun u : ℝ => (u : ℂ)) atTop (BorelStokesVandermonde.far (1 : ℂ)) := by
    rw [BorelStokesVandermonde.far, tendsto_comap_iff]
    have heq : ((fun p : ℂ => (p * (1 : ℂ)).re) ∘ fun u : ℝ => (u : ℂ)) = id := by
      funext u; simp
    rw [heq]; exact tendsto_id
  intro M
  cases M with
  | zero =>
    obtain ⟨C, _, hC⟩ := Minor.value_asymptotic (ej.residual a) hU hray good_j h1re 0
    refine ⟨C + ‖(ej.residual a).atom‖, ?_⟩
    filter_upwards [hC, hjet_eq, ht_far.eventually rep_j, eventually_ge_atTop (1 : ℝ)] with u hu hje hre hu1
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, div_one]
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, zero_add, pow_one] at hu
    rw [← hje, hre]
    have h1 : ‖(ej.residual a).value (1 : ℂ) (u : ℂ)‖ ≤
        ‖(ej.residual a).value (1 : ℂ) (u : ℂ) - (ej.residual a).atom‖ + ‖(ej.residual a).atom‖ := by
      simpa [sub_add_cancel] using
        norm_add_le ((ej.residual a).value (1 : ℂ) (u : ℂ) - (ej.residual a).atom) (ej.residual a).atom
    have hC0 : 0 ≤ C := by
      have hnn := norm_nonneg ((ej.residual a).value (1 : ℂ) (u : ℂ) - (ej.residual a).atom)
      exact (div_nonneg_iff.mp (hnn.trans hu)).resolve_right (fun h => by linarith) |>.1
    have hCu : C / u ≤ C := by
      calc C / u ≤ C / 1 := div_le_div_of_nonneg_left hC0 zero_lt_one hu1
        _ = C := div_one C
    linarith
  | succ m =>
    obtain ⟨C, _, hC⟩ := Minor.value_asymptotic (ej.residual a) hU hray good_j h1re m
    refine ⟨C, ?_⟩
    filter_upwards [hC, hjet_eq, ht_far.eventually rep_j] with u hu hje hre
    rw [← hje, hre]
    have hsum : ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k (d_u^[j] a.toSeries) * ((u : ℂ)⁻¹ ^ k) =
        (ej.residual a).atom + ∑ k ∈ Finset.range m,
          iteratedDeriv k (ej.residual a).density 0 * ((u : ℂ)⁻¹ ^ (k + 1)) := by
      rw [← hser_j, Finset.sum_range_succ']
      simp only [Minor.toSeries, PowerSeries.coeff_mk, pow_zero, mul_one, add_comm]
    rw [hsum]
    simpa [sub_sub] using hu

/-- **100% Unconditional Analytic Convergent-Germ ADE Obstruction for `B_xi c`**:
For EVERY real center `c : ℝ`, the actual real-axis Laplace integral `B_xi c u` of
`-ξ'(c + w)/ξ(c + w)` satisfies NO nontrivial algebraic differential equation in `u` with
convergent `ℂ{1/u}` coefficients as `u → +∞` (in `t = 1/u` / `u`, not for `ζ(s)` directly as a
function of `s`). -/
theorem completedXi_laplace_no_conv_ade (c : ℝ) {r : ℕ}
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : ∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (B_xi c) u)
        (evalConvMvPoly Q (u : ℂ)⁻¹) = 0) :
    Q = 0 := by
  have hasymp : HasAsympExp
      (fun u : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (B_xi c) u)
        (evalConvMvPoly Q (u : ℂ)⁻¹))
      (formalEvalConv (formalSeries (phiXiAt (c : ℂ))) Q) :=
    HasAsympExp.mvPolynomial_evalConv (fun j : Fin (r + 1) => B_xi_hasAsympExp c j.val) Q
  have hflat : formalEvalConv (formalSeries (phiXiAt (c : ℂ))) Q = 0 :=
    HasAsympExp.eq_zero_of_flat hasymp (fun N => ⟨0, by filter_upwards [hQ] with u hu; simp [hu]⟩)
  exact completedXi_no_conv_ade c Q hflat

/-! ### 6. RH-Free Cramér Positivity & Strict Hankel Positive Definiteness (via `SpectralPositivity`)

This section instantiates the unified spectral-positivity and Hankel positive-definiteness
interface from `PakPrimes.SpectralPositivity` (built directly on Codex's `PositiveDensity.lean`
theorems `xi_lower_from_estimates`, `square_integral_pos`, and `hankel_form`) for the parameter
regime `h = 15, H = 20, C = 1`.

**Honesty boundary**: Every theorem in this section is explicitly parameterized by
`CramerLowZeroData := SpectralLowZeroData 15 20 1`, recording ONLY a lead real ordinate
`0 < γ₁ ≤ 15`, an optional finite list `γ_low : List ℝ` of additional positive critical-line
ordinates (`[]` for Riemann $\xi$), tail zeros with `Re γ ≥ 20` and `|Im γ| < 1/2`, and
`∑ (4 + (Re γ)²)⁻¹ < 1`. **NO `RiemannHypothesis` is assumed**: `Im γ` may take arbitrary values
in `(-1/2, 1/2)`. The structure is NOT connected in Lean to the zeros of `completedXi`,
$L(s, \chi_{-4})$, or $L(s, \Delta)$. That $\gamma_1, \gamma_{\mathrm{low}}, \gamma_{\mathrm{tail}}$
enumerate exactly those zeros with multiplicity, the low-height verification, the Hadamard bound
$\sum (4 + (\operatorname{Re}\gamma)^2)^{-1} < C$, and the identity relating `spectralMoment` to
the Taylor coefficients of $\xi'/\xi$ are all external. The theorems hold for any data satisfying
the fields.

For the sibling instantiations of the exact same unified interface to Dirichlet $\beta$
(`SpectralLowZeroData 7 16 10`, with `γ_low = [10.24..., 12.99...]`), Ramanujan's $\Delta$
(`SpectralLowZeroData 10 16 10`, with `γ_low = [13.91...]`), and the subtracted compact hyperbolic
manifold measure `dν(y) = y K_X(√y) dy` ($d = 2, 3$, `SubtractedHyperbolicSpectralData`), see
`PakPrimes.SpectralPositivity`.
-/

/-- Parameterized RH-free low-ordinate spectral data for the `(15, 20, 1)` regime (intended for
Riemann $\xi$ with `γ_low = []`; NO `RiemannHypothesis` assumed).

**Honesty boundary**: The structure is NOT connected in Lean to the zeros of `completedXi`,
$L(s, \chi_{-4})$, or $L(s, \Delta)$. That $\gamma_1, \gamma_{\mathrm{low}}, \gamma_{\mathrm{tail}}$
enumerate exactly those zeros with multiplicity, the low-height verification, the Hadamard bound
$\sum (4 + (\operatorname{Re}\gamma)^2)^{-1} < C$, and the identity relating `spectralMoment` to
the Taylor coefficients of $\xi'/\xi$ are all external. The theorems hold for any data satisfying
the fields. -/
abbrev CramerLowZeroData := SpectralLowZeroData 15 20 1

/-- The real Cramér spectral kernel
`K(x) = e^{-γ₁ x} + ∑_{γ ∈ γ_low} e^{-γ x} + ∑_n e^{-(Re γ_n) x} cos((Im γ_n) x)` for `x > 0`. -/
abbrev cramerDensity (D : CramerLowZeroData) : ℝ → ℝ := spectralDensity D

/-- The `k`-th Stieltjes moment `μ_k = ∫_{0}^{∞} y^k K(√y) dy` associated to `D : CramerLowZeroData`
(the identity relating `cramerMoment` to the Taylor coefficients of $\xi'/\xi$ is external). -/
abbrev cramerMoment (D : CramerLowZeroData) : ℕ → ℝ := spectralMoment D

/-- The shifted `n × n` Hankel moment matrix `(μ_{i + j + s})_{0 ≤ i, j < n}` associated to
`D : CramerLowZeroData` (unlinked in Lean to `completedXi`). -/
abbrev cramerHankel (D : CramerLowZeroData) (s n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  spectralHankel D s n

/-- Absolute summability of the tail series in `cramerDensity D x` for every `x > 0` and any
`D : CramerLowZeroData` (unlinked in Lean to `completedXi`; see `CramerLowZeroData`). -/
theorem cramerDensity_tail_summable (D : CramerLowZeroData) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => Real.exp (-(D.γ_tail n).re * x) * Real.cos ((D.γ_tail n).im * x)) :=
  spectralDensity_tail_summable D hx

/-- **Codex's 5-Line RH-Free Positivity Lemma (`xi_lower_from_estimates`)**:
For every `x > 0` and any `D : CramerLowZeroData`, `(99 / 100) * Real.exp (-15 * x) ≤ cramerDensity D x`
(with ZERO RH assumed; unlinked in Lean to `completedXi`, see `CramerLowZeroData`). -/
theorem cramerDensity_ge_lower_bound (D : CramerLowZeroData) {x : ℝ} (hx : 0 < x) :
    (99 / 100 : ℝ) * Real.exp (-15 * x) ≤ cramerDensity D x :=
  xiDensity_ge_lower_bound D hx

/-- Strict positivity `0 < cramerDensity D x` for every `x > 0` and any `D : CramerLowZeroData`
(zero RH; unlinked in Lean to `completedXi`, see `CramerLowZeroData`). -/
theorem cramerDensity_pos (D : CramerLowZeroData) {x : ℝ} (hx : 0 < x) :
    0 < cramerDensity D x :=
  xiDensity_pos D hx

/-- Continuity of `cramerDensity D` on `(0, ∞)` for any `D : CramerLowZeroData`. -/
theorem cramerDensity_continuousOn (D : CramerLowZeroData) :
    ContinuousOn (cramerDensity D) (Ioi (0 : ℝ)) :=
  spectralDensity_continuousOn D

/-- Integrability of every Stieltjes power moment `y ↦ y^k * K(√y)` on `(0, ∞)` for any
`D : CramerLowZeroData`. -/
theorem cramerMoment_integrable (D : CramerLowZeroData) (k : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ k * cramerDensity D (Real.sqrt y)) (Ioi (0 : ℝ)) volume :=
  spectralMoment_integrable D k

/-- Strict positivity `0 < cramerMoment D k` for any `D : CramerLowZeroData` (zero RH; unlinked
in Lean to `completedXi` or Taylor coefficients of $\xi'/\xi$, see `CramerLowZeroData`). -/
theorem cramerMoment_pos (D : CramerLowZeroData) (k : ℕ) :
    0 < cramerMoment D k :=
  xiMoment_pos D k

/-- **RH-Free Strict Positive Definiteness of All Shifted Hankel Matrices**:
For every shift `s : ℕ`, dimension `n : ℕ`, and any `D : CramerLowZeroData`, `cramerHankel D s n`
is strictly positive definite (via Codex's `square_integral_pos` and `hankel_form`, without
assuming `RiemannHypothesis`; unlinked in Lean to `completedXi`, see `CramerLowZeroData`). -/
theorem cramerHankel_posDef (D : CramerLowZeroData) (s n : ℕ) :
    (cramerHankel D s n).PosDef :=
  xiHankel_posDef D s n

/-- **Strict Positivity of the Shifted Hankel Quadratic Form (Zero RH)**:
For every `s n : ℕ`, any `D : CramerLowZeroData`, and every nonzero vector `v : Fin n → ℝ`,
`v ⬝ᵥ (cramerHankel D s n *ᵥ v) > 0` (unlinked in Lean to `completedXi`, see `CramerLowZeroData`). -/
theorem cramerHankel_quadForm_pos (D : CramerLowZeroData) (s n : ℕ) {v : Fin n → ℝ} (hv : v ≠ 0) :
    0 < v ⬝ᵥ (cramerHankel D s n *ᵥ v) := by
  simpa only [star_trivial] using (cramerHankel_posDef D s n).dotProduct_mulVec_pos hv

/-- **RH-Free Strict Positivity of All Shifted Hankel Determinants**:
For every `s n : ℕ` and any `D : CramerLowZeroData`, `0 < (cramerHankel D s n).det` (unlinked in
Lean to `completedXi`, see `CramerLowZeroData`). -/
theorem cramerHankel_det_pos (D : CramerLowZeroData) (s n : ℕ) :
    0 < (cramerHankel D s n).det :=
  xiHankel_det_pos D s n

end
end PakPrimes.CompletedXiDTrans
