module

public import PakPrimes.HigherOrderStokes
public import PakPrimes.AutonomousTransfer
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! # Relativistic Ideal Gas Dimensional-Parity Theorem (2D D-Algebraicity vs 1D/3D Differential Transcendence)

This module formalizes both halves of the Relativistic Ideal Gas Dimensional-Parity Theorem
for a massive ideal relativistic Bose or Fermi gas at zero chemical potential (`m > 0`, `T > 0`):

1. **Even Dimension (`d = 2`) — D-Algebraicity:**
   Both `bosePressure2D m` and `fermiPressure2D m` satisfy explicit nonzero order-3 quadratic
   algebraic differential equations over `ℂ[T]`:
   `m² T⁴ P'''(T) - m² T³ P''(T) - m³ Q(T) ∓ 2π Q(T)² = 0`,
   where `Q(T) = T² P''(T) - 3 T P'(T) + 3 P(T)`.

2. **Odd Dimension (`d = 1` and `d = 3`) — Differential Transcendence:**
   Both `bosePressure1D m`, `fermiPressure1D m`, `bosePressure3D m`, and `fermiPressure3D m`
   satisfy NO nonzero algebraic differential equation over `ℂ[T]` or `ℂ(T)`.
   The proof establishes:
   - The exact Matsubara-mode identities `H1''(y) = (1/4) S_bose(y) - 1/(4y) + 1/(8 y^{3/2})`
     (via Mathlib's `cot_series_rep`) and `H3'(y) = -(4π)⁻¹ H1(y)`.
   - Two-step slit-domain analytic continuation flipping individual thermal mode branches
     `(z + a_k)^{-3/2}` one by one, combined with finite-difference Vandermonde induction.
   - Differential-algebra transfer via `PakPrimes.PrimeNome.autonomous_readout`.
-/

set_option maxHeartbeats 1200000

public section
namespace PakPrimes.ThermalGasParity

open Complex Real Filter Set MvPolynomial MeasureTheory
open PakPrimes.HigherOrderStokes
open PakPrimes.PrimeNome
open scoped Topology Pointwise

noncomputable section

/-! ### 1. Exact Definitions of 2D Bose and Fermi Pressures & Order-3 ODEs -/

/-- Exact 2D relativistic ideal Bose gas pressure at mass `m > 0` and temperature `T > 0`:
`B_m(T) = T³ / (2π) * ∑' k, (1 + (k+1) m / T) / (k+1)³ * exp(-((k+1) m / T))`. -/
@[expose] def bosePressure2D (m T : ℝ) : ℝ :=
  T ^ 3 / (2 * Real.pi) *
    ∑' k : ℕ, (1 + ((k : ℝ) + 1) * m / T) / ((k : ℝ) + 1) ^ 3 *
      Real.exp (-(((k : ℝ) + 1) * m / T))

/-- Exact 2D relativistic ideal Fermi gas pressure via the Bose–Fermi doubling identity:
`F_m(T) = B_m(T) - (1/4) B_{2m}(T)`. -/
@[expose] def fermiPressure2D (m T : ℝ) : ℝ :=
  bosePressure2D m T - (1 / 4 : ℝ) * bosePressure2D (2 * m) T

/-- The explicit order-3 quadratic differential polynomial over `ℂ[T]` satisfied by
2D relativistic Bose (`σ = 1`) and Fermi (`σ = -1`) pressures:
`m² T⁴ Y₃ - m² T³ Y₂ - m³ Q - σ · 2π Q²`, where `Q = T² Y₂ - 3 T Y₁ + 3 Y₀`. -/
@[expose] def odePoly2D (m σ : ℂ) : MvPolynomial (Fin 4) (Polynomial ℂ) :=
  let T : Polynomial ℂ := Polynomial.X
  let Q : MvPolynomial (Fin 4) (Polynomial ℂ) :=
    C (T ^ 2) * X 2 - C (3 * T) * X 1 + C 3 * X 0
  C (Polynomial.C (m ^ 2) * T ^ 4) * X 3 - C (Polynomial.C (m ^ 2) * T ^ 3) * X 2 -
    C (Polynomial.C (m ^ 3)) * Q - C (Polynomial.C (σ * (2 * (Real.pi : ℂ)))) * Q ^ 2

theorem odePoly2D_ne_zero {m : ℝ} (hm : 0 < m) (σ : ℂ) :
    odePoly2D (m : ℂ) σ ≠ 0 := by
  intro h0
  have hev := congrArg (fun P => MvPolynomial.eval (fun j : Fin 4 => if j = 3 then (1 : ℂ) else 0)
    (evalU P (1 : ℂ))) h0
  simp only [odePoly2D, evalU, map_zero, map_sub, map_add, map_mul, map_pow, MvPolynomial.map_C,
    MvPolynomial.map_X, MvPolynomial.eval_C, MvPolynomial.eval_X, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, ↓reduceIte,
    Fin.reduceEq, one_pow, mul_one, mul_zero, sub_zero, add_zero, zero_pow two_ne_zero] at hev
  exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hm.ne') hev

private lemma summable_poly_mul_exp_neg {a : ℝ} (ha : 0 < a) (p : ℕ) :
    Summable (fun k : ℕ => (((k : ℝ) + 1) ^ p) * Real.exp (-(((k : ℝ) + 1) * a))) := by
  have hr_pos : 0 < Real.exp (-a) := Real.exp_pos _
  have hr_lt : Real.exp (-a) < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha)
  have hshift : Summable (fun n : ℕ => (n : ℝ) ^ p * (Real.exp (-a)) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one p (r := Real.exp (-a))
      (by rw [Real.norm_eq_abs, abs_of_pos hr_pos]; exact hr_lt)
  have hgeom : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ p * (Real.exp (-a)) ^ (k + 1)) := by
    have hcomp := hshift.comp_injective Nat.succ_injective
    refine hcomp.congr fun k => ?_
    simp [Function.comp, Nat.cast_add, Nat.cast_one]
  refine hgeom.congr fun k => ?_
  rw [← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

private lemma hasDerivAt_bose2D_term0 (m : ℝ) (k : ℕ) {T : ℝ} (hT : 0 < T) :
    HasDerivAt
      (fun t : ℝ => (t ^ 3 + ((k : ℝ) + 1) * m * t ^ 2) / ((k : ℝ) + 1) ^ 3 *
        Real.exp (-(((k : ℝ) + 1) * m / t)))
      ((3 * T ^ 2 + 3 * ((k : ℝ) + 1) * m * T + (((k : ℝ) + 1) * m) ^ 2) / ((k : ℝ) + 1) ^ 3 *
        Real.exp (-(((k : ℝ) + 1) * m / T))) T := by
  set n : ℝ := (k : ℝ) + 1
  have hn : n ≠ 0 := by positivity
  have hpoly : HasDerivAt (fun t : ℝ => (t ^ 3 + n * m * t ^ 2) / n ^ 3)
      ((3 * T ^ 2 + n * m * (2 * T)) / n ^ 3) T := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ 3) (3 * T ^ 2) T := by
      simpa using hasDerivAt_pow 3 T
    have h2 : HasDerivAt (fun t : ℝ => n * m * t ^ 2) (n * m * (2 * T)) T := by
      simpa using (hasDerivAt_pow 2 T).const_mul (n * m)
    exact (h1.add h2).div_const (n ^ 3)
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(n * m / t)))
      (Real.exp (-(n * m / T)) * (n * m / T ^ 2)) T := by
    have hdiv : HasDerivAt (fun t : ℝ => -(n * m / t)) (n * m / T ^ 2) T := by
      have hinv := hasDerivAt_inv hT.ne'
      have := (hinv.const_mul (-(n * m)))
      convert this using 1
      · ext t; ring
      · field_simp [hT.ne']
    exact hdiv.exp
  convert hpoly.mul hexp using 1
  field_simp [hT.ne', hn]
  ring

private lemma hasDerivAt_bose2D_term1 (m : ℝ) (k : ℕ) {T : ℝ} (hT : 0 < T) :
    HasDerivAt
      (fun t : ℝ => (3 * t ^ 2 + 3 * ((k : ℝ) + 1) * m * t + (((k : ℝ) + 1) * m) ^ 2) /
        ((k : ℝ) + 1) ^ 3 * Real.exp (-(((k : ℝ) + 1) * m / t)))
      ((6 * T + 6 * ((k : ℝ) + 1) * m + 3 * (((k : ℝ) + 1) * m) ^ 2 / T +
          (((k : ℝ) + 1) * m) ^ 3 / T ^ 2) / ((k : ℝ) + 1) ^ 3 *
        Real.exp (-(((k : ℝ) + 1) * m / T))) T := by
  set n : ℝ := (k : ℝ) + 1
  have hn : n ≠ 0 := by positivity
  have hpoly : HasDerivAt
      (fun t : ℝ => (3 * t ^ 2 + 3 * n * m * t + (n * m) ^ 2) / n ^ 3)
      ((3 * (2 * T) + 3 * n * m) / n ^ 3) T := by
    have h1 : HasDerivAt (fun t : ℝ => 3 * t ^ 2) (3 * (2 * T)) T := by
      simpa using (hasDerivAt_pow 2 T).const_mul (3 : ℝ)
    have h2 : HasDerivAt (fun t : ℝ => 3 * n * m * t) (3 * n * m) T := by
      simpa using (hasDerivAt_id T).const_mul (3 * n * m)
    exact ((h1.add h2).add_const ((n * m) ^ 2)).div_const (n ^ 3)
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(n * m / t)))
      (Real.exp (-(n * m / T)) * (n * m / T ^ 2)) T := by
    have hdiv : HasDerivAt (fun t : ℝ => -(n * m / t)) (n * m / T ^ 2) T := by
      have hinv := hasDerivAt_inv hT.ne'
      have := (hinv.const_mul (-(n * m)))
      convert this using 1
      · ext t; ring
      · field_simp [hT.ne']
    exact hdiv.exp
  convert hpoly.mul hexp using 1
  field_simp [hT.ne', hn]
  ring

private lemma bosePressure2D_eq_tsum {m T : ℝ} (hT : 0 < T) :
    bosePressure2D m T =
      (2 * Real.pi)⁻¹ *
        ∑' k : ℕ, (T ^ 3 + ((k : ℝ) + 1) * m * T ^ 2) / ((k : ℝ) + 1) ^ 3 *
          Real.exp (-(((k : ℝ) + 1) * m / T)) := by
  unfold bosePressure2D
  rw [div_eq_mul_inv, mul_comm (T ^ 3), mul_assoc, ← tsum_mul_left]
  congr 1; apply tsum_congr; intro k
  field_simp [hT.ne']

private lemma pow_le_cube_of_one_le {n : ℝ} (hn : 1 ≤ n) :
    1 ≤ n ^ 3 ∧ n ≤ n ^ 3 ∧ n ^ 2 ≤ n ^ 3 := by
  have h2 : 1 ≤ n ^ 2 := by nlinarith
  have h1 : n ≤ n ^ 2 := by nlinarith
  exact ⟨by nlinarith, by nlinarith, by nlinarith⟩

private lemma hasDerivAt_bosePressure2D {m T : ℝ} (hm : 0 < m) (hT : 0 < T) :
    HasDerivAt (bosePressure2D m)
      ((2 * Real.pi)⁻¹ *
        ∑' k : ℕ, (3 * T ^ 2 + 3 * ((k : ℝ) + 1) * m * T + (((k : ℝ) + 1) * m) ^ 2) /
          ((k : ℝ) + 1) ^ 3 * Real.exp (-(((k : ℝ) + 1) * m / T))) T := by
  let f : ℕ → ℝ → ℝ := fun k t =>
    (t ^ 3 + ((k : ℝ) + 1) * m * t ^ 2) / ((k : ℝ) + 1) ^ 3 * Real.exp (-(((k : ℝ) + 1) * m / t))
  let f' : ℕ → ℝ → ℝ := fun k t =>
    (3 * t ^ 2 + 3 * ((k : ℝ) + 1) * m * t + (((k : ℝ) + 1) * m) ^ 2) / ((k : ℝ) + 1) ^ 3 *
      Real.exp (-(((k : ℝ) + 1) * m / t))
  let R : ℝ := 2 * T
  let u : ℕ → ℝ := fun k =>
    (3 * R ^ 2 + 3 * m * R + m ^ 2) * Real.exp (-(((k : ℝ) + 1) * (m / R)))
  have hu : Summable u := by
    have h0 := summable_poly_mul_exp_neg (div_pos hm (by positivity : 0 < R)) 0
    simpa [u] using h0.mul_left (3 * R ^ 2 + 3 * m * R + m ^ 2)
  have hball : Metric.ball T (T / 2) ∈ 𝓝 T := Metric.ball_mem_nhds T (half_pos hT)
  have hbound : ∀ k : ℕ, ∀ t ∈ Metric.ball T (T / 2), ‖f' k t‖ ≤ u k := by
    intro k t ht
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
    have ht_pos : 0 < t := by linarith
    have ht_le : t ≤ R := by linarith
    set n : ℝ := (k : ℝ) + 1
    have hn1 : 1 ≤ n := by linarith [Nat.cast_nonneg (α := ℝ) k]
    obtain ⟨h1n, h2n, h3n⟩ := pow_le_cube_of_one_le hn1
    have hnum_nonneg : 0 ≤ (3 * t ^ 2 + 3 * n * m * t + (n * m) ^ 2) / n ^ 3 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnum_nonneg (Real.exp_pos _).le)]
    have hexp_le : Real.exp (-(n * m / t)) ≤ Real.exp (-(n * (m / R))) := by
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff]
      have : n * (m / R) = n * m / R := by ring
      rw [this]
      exact div_le_div_of_nonneg_left (by positivity) ht_pos ht_le
    have hfrac_le : (3 * t ^ 2 + 3 * n * m * t + (n * m) ^ 2) / n ^ 3 ≤
        3 * R ^ 2 + 3 * m * R + m ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : 3 * t ^ 2 ≤ 3 * R ^ 2 * n ^ 3 := by nlinarith
      have h2 : 3 * n * m * t ≤ 3 * m * R * n ^ 3 := by
        have hmt : 3 * m * t ≤ 3 * m * R := by nlinarith
        have hmul : 3 * m * t * n ≤ 3 * m * R * n ^ 3 :=
          mul_le_mul hmt h2n (by positivity) (by positivity)
        linarith
      have h3 : (n * m) ^ 2 ≤ m ^ 2 * n ^ 3 := by nlinarith [sq_nonneg m]
      linarith
    exact mul_le_mul hfrac_le hexp_le (Real.exp_pos _).le (by positivity)
  have hf_sum : Summable (fun k => f k T) := by
    have h0 := summable_poly_mul_exp_neg (div_pos hm hT) 0
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (h0.mul_left (T ^ 3 + m * T ^ 2))
    dsimp only [f]
    set n : ℝ := (k : ℝ) + 1
    have hn1 : 1 ≤ n := by linarith [Nat.cast_nonneg (α := ℝ) k]
    obtain ⟨h1n, h2n, _⟩ := pow_le_cube_of_one_le hn1
    have hfrac : (T ^ 3 + n * m * T ^ 2) / n ^ 3 ≤ T ^ 3 + m * T ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [pow_pos hT 3, mul_pos hm (pow_pos hT 2)]
    have hexp : Real.exp (-(n * m / T)) = Real.exp (-(n * (m / T))) := by congr 1; ring
    rw [hexp, pow_zero, one_mul]
    exact mul_le_mul_of_nonneg_right hfrac (Real.exp_pos _).le
  have htsum : HasDerivAt (fun t => ∑' k, f k t) (∑' k, f' k T) T :=
    hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball (convex_ball T (T / 2)).isPreconnected
      (fun k t ht => by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
        exact hasDerivAt_bose2D_term0 m k (by linarith))
      hbound (Metric.mem_ball_self (half_pos hT)) hf_sum (Metric.mem_ball_self (half_pos hT))
  have hscaled := htsum.const_mul (2 * Real.pi)⁻¹
  refine hscaled.congr_of_eventuallyEq ?_
  filter_upwards [hball] with t ht
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
  exact bosePressure2D_eq_tsum (by linarith)

private lemma hasDerivAt_deriv_bosePressure2D {m T : ℝ} (hm : 0 < m) (hT : 0 < T) :
    HasDerivAt (deriv (bosePressure2D m))
      ((2 * Real.pi)⁻¹ *
        ∑' k : ℕ, (6 * T + 6 * ((k : ℝ) + 1) * m + 3 * (((k : ℝ) + 1) * m) ^ 2 / T +
            (((k : ℝ) + 1) * m) ^ 3 / T ^ 2) / ((k : ℝ) + 1) ^ 3 *
          Real.exp (-(((k : ℝ) + 1) * m / T))) T := by
  let f : ℕ → ℝ → ℝ := fun k t =>
    (3 * t ^ 2 + 3 * ((k : ℝ) + 1) * m * t + (((k : ℝ) + 1) * m) ^ 2) / ((k : ℝ) + 1) ^ 3 *
      Real.exp (-(((k : ℝ) + 1) * m / t))
  let f' : ℕ → ℝ → ℝ := fun k t =>
    (6 * t + 6 * ((k : ℝ) + 1) * m + 3 * (((k : ℝ) + 1) * m) ^ 2 / t +
        (((k : ℝ) + 1) * m) ^ 3 / t ^ 2) / ((k : ℝ) + 1) ^ 3 *
      Real.exp (-(((k : ℝ) + 1) * m / t))
  let R : ℝ := 2 * T
  let L : ℝ := T / 2
  have hL : 0 < L := half_pos hT
  let C0 : ℝ := 6 * R + 6 * m + 3 * m ^ 2 / L + m ^ 3 / L ^ 2
  let u : ℕ → ℝ := fun k => C0 * Real.exp (-(((k : ℝ) + 1) * (m / R)))
  have hu : Summable u := by
    have h0 := summable_poly_mul_exp_neg (div_pos hm (by positivity : 0 < R)) 0
    simpa [u] using h0.mul_left C0
  have hball : Metric.ball T (T / 2) ∈ 𝓝 T := Metric.ball_mem_nhds T (half_pos hT)
  have hbound : ∀ k : ℕ, ∀ t ∈ Metric.ball T (T / 2), ‖f' k t‖ ≤ u k := by
    intro k t ht
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
    have ht_ge : L ≤ t := by dsimp only [L]; linarith
    have ht_pos : 0 < t := lt_of_lt_of_le hL ht_ge
    have ht_le : t ≤ R := by linarith
    set n : ℝ := (k : ℝ) + 1
    have hn1 : 1 ≤ n := by linarith [Nat.cast_nonneg (α := ℝ) k]
    obtain ⟨h1n, h2n, h3n⟩ := pow_le_cube_of_one_le hn1
    have hnum_nonneg : 0 ≤ (6 * t + 6 * n * m + 3 * (n * m) ^ 2 / t + (n * m) ^ 3 / t ^ 2) / n ^ 3 := by
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnum_nonneg (Real.exp_pos _).le)]
    have hexp_le : Real.exp (-(n * m / t)) ≤ Real.exp (-(n * (m / R))) := by
      apply Real.exp_le_exp.mpr
      rw [neg_le_neg_iff]
      have : n * (m / R) = n * m / R := by ring
      rw [this]
      exact div_le_div_of_nonneg_left (by positivity) ht_pos ht_le
    have hfrac_le :
        (6 * t + 6 * n * m + 3 * (n * m) ^ 2 / t + (n * m) ^ 3 / t ^ 2) / n ^ 3 ≤ C0 := by
      rw [div_le_iff₀ (by positivity)]
      have h1 : 6 * t ≤ 6 * R * n ^ 3 := by
        have h6 : 6 * t ≤ 6 * R := by linarith
        nlinarith
      have h2 : 6 * n * m ≤ 6 * m * n ^ 3 := by nlinarith
      have h3 : 3 * (n * m) ^ 2 / t ≤ (3 * m ^ 2 / L) * n ^ 3 := by
        have hinv : t⁻¹ ≤ L⁻¹ := inv_anti₀ hL ht_ge
        calc 3 * (n * m) ^ 2 / t = 3 * m ^ 2 * n ^ 2 * t⁻¹ := by ring
          _ ≤ 3 * m ^ 2 * n ^ 2 * L⁻¹ := by gcongr
          _ = (3 * m ^ 2 / L) * n ^ 2 := by ring
          _ ≤ (3 * m ^ 2 / L) * n ^ 3 := by gcongr
      have h4 : (n * m) ^ 3 / t ^ 2 ≤ (m ^ 3 / L ^ 2) * n ^ 3 := by
        have hinv : (t ^ 2)⁻¹ ≤ (L ^ 2)⁻¹ := inv_anti₀ (pow_pos hL 2) (by nlinarith)
        calc (n * m) ^ 3 / t ^ 2 = m ^ 3 * n ^ 3 * (t ^ 2)⁻¹ := by ring
          _ ≤ m ^ 3 * n ^ 3 * (L ^ 2)⁻¹ := by gcongr
          _ = (m ^ 3 / L ^ 2) * n ^ 3 := by ring
      dsimp only [C0]
      linarith
    exact mul_le_mul hfrac_le hexp_le (Real.exp_pos _).le (by positivity)
  have hf_sum : Summable (fun k => f k T) := by
    have h0 := summable_poly_mul_exp_neg (div_pos hm hT) 0
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (h0.mul_left (3 * T ^ 2 + 3 * m * T + m ^ 2))
    dsimp only [f]
    set n : ℝ := (k : ℝ) + 1
    have hn1 : 1 ≤ n := by linarith [Nat.cast_nonneg (α := ℝ) k]
    obtain ⟨h1n, h2n, h3n⟩ := pow_le_cube_of_one_le hn1
    have hfrac : (3 * T ^ 2 + 3 * n * m * T + (n * m) ^ 2) / n ^ 3 ≤
        3 * T ^ 2 + 3 * m * T + m ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [pow_pos hT 2, mul_pos hm hT, sq_nonneg m]
    have hexp : Real.exp (-(n * m / T)) = Real.exp (-(n * (m / T))) := by congr 1; ring
    rw [hexp, pow_zero, one_mul]
    exact mul_le_mul_of_nonneg_right hfrac (Real.exp_pos _).le
  have htsum : HasDerivAt (fun t => ∑' k, f k t) (∑' k, f' k T) T :=
    hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball (convex_ball T (T / 2)).isPreconnected
      (fun k t ht => by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
        exact hasDerivAt_bose2D_term1 m k (by linarith))
      hbound (Metric.mem_ball_self (half_pos hT)) hf_sum (Metric.mem_ball_self (half_pos hT))
  have hscaled := htsum.const_mul (2 * Real.pi)⁻¹
  refine hscaled.congr_of_eventuallyEq ?_
  filter_upwards [hball] with t ht
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
  exact (hasDerivAt_bosePressure2D hm (by linarith)).deriv

private lemma bosePressure2D_Q_eq {m T : ℝ} (hm : 0 < m) (hT : 0 < T) :
    T ^ 2 * iteratedDeriv 2 (bosePressure2D m) T -
      3 * T * iteratedDeriv 1 (bosePressure2D m) T +
      3 * bosePressure2D m T =
      m ^ 3 / (2 * Real.pi) * (Real.exp (-(m / T)) / (1 - Real.exp (-(m / T)))) := by
  have hd1 : iteratedDeriv 1 (bosePressure2D m) T =
      (2 * Real.pi)⁻¹ *
        ∑' k : ℕ, (3 * T ^ 2 + 3 * ((k : ℝ) + 1) * m * T + (((k : ℝ) + 1) * m) ^ 2) /
          ((k : ℝ) + 1) ^ 3 * Real.exp (-(((k : ℝ) + 1) * m / T)) := by
    rw [iteratedDeriv_one]
    exact (hasDerivAt_bosePressure2D hm hT).deriv
  have hd2 : iteratedDeriv 2 (bosePressure2D m) T =
      (2 * Real.pi)⁻¹ *
        ∑' k : ℕ, (6 * T + 6 * ((k : ℝ) + 1) * m + 3 * (((k : ℝ) + 1) * m) ^ 2 / T +
            (((k : ℝ) + 1) * m) ^ 3 / T ^ 2) / ((k : ℝ) + 1) ^ 3 *
          Real.exp (-(((k : ℝ) + 1) * m / T)) := by
    have h2eq : iteratedDeriv 2 (bosePressure2D m) T = deriv (deriv (bosePressure2D m)) T := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [h2eq]
    exact (hasDerivAt_deriv_bosePressure2D hm hT).deriv
  rw [hd1, hd2, bosePressure2D_eq_tsum hT]
  let e : ℕ → ℝ := fun k => Real.exp (-(((k : ℝ) + 1) * m / T))
  have he_sum : Summable e := by
    have h0 := summable_poly_mul_exp_neg (div_pos hm hT) 0
    refine h0.congr fun k => ?_
    simp only [e, pow_zero, one_mul]; congr 1; ring
  have hs0 : Summable (fun k : ℕ =>
      (T ^ 3 + ((k : ℝ) + 1) * m * T ^ 2) / ((k : ℝ) + 1) ^ 3 * e k) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (he_sum.mul_left (T ^ 3 + m * T ^ 2))
    set n : ℝ := (k : ℝ) + 1
    have hn1 : 1 ≤ n := by linarith [Nat.cast_nonneg (α := ℝ) k]
    obtain ⟨h1n, h2n, _⟩ := pow_le_cube_of_one_le hn1
    have hfrac : (T ^ 3 + n * m * T ^ 2) / n ^ 3 ≤ T ^ 3 + m * T ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [pow_pos hT 3, mul_pos hm (pow_pos hT 2)]
    exact mul_le_mul_of_nonneg_right hfrac (Real.exp_pos _).le
  have hs1 : Summable (fun k : ℕ =>
      (3 * T ^ 2 + 3 * ((k : ℝ) + 1) * m * T + (((k : ℝ) + 1) * m) ^ 2) /
        ((k : ℝ) + 1) ^ 3 * e k) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (he_sum.mul_left (3 * T ^ 2 + 3 * m * T + m ^ 2))
    set n : ℝ := (k : ℝ) + 1
    have hn1 : 1 ≤ n := by linarith [Nat.cast_nonneg (α := ℝ) k]
    obtain ⟨h1n, h2n, h3n⟩ := pow_le_cube_of_one_le hn1
    have hfrac : (3 * T ^ 2 + 3 * n * m * T + (n * m) ^ 2) / n ^ 3 ≤
        3 * T ^ 2 + 3 * m * T + m ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [pow_pos hT 2, mul_pos hm hT, sq_nonneg m]
    exact mul_le_mul_of_nonneg_right hfrac (Real.exp_pos _).le
  have hs2 : Summable (fun k : ℕ =>
      (6 * T + 6 * ((k : ℝ) + 1) * m + 3 * (((k : ℝ) + 1) * m) ^ 2 / T +
          (((k : ℝ) + 1) * m) ^ 3 / T ^ 2) / ((k : ℝ) + 1) ^ 3 * e k) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (he_sum.mul_left (6 * T + 6 * m + 3 * m ^ 2 / T + m ^ 3 / T ^ 2))
    set n : ℝ := (k : ℝ) + 1
    have hn1 : 1 ≤ n := by linarith [Nat.cast_nonneg (α := ℝ) k]
    obtain ⟨h1n, h2n, h3n⟩ := pow_le_cube_of_one_le hn1
    have hfrac : (6 * T + 6 * n * m + 3 * (n * m) ^ 2 / T + (n * m) ^ 3 / T ^ 2) / n ^ 3 ≤
        6 * T + 6 * m + 3 * m ^ 2 / T + m ^ 3 / T ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have h3' : 3 * (n * m) ^ 2 / T = (3 * m ^ 2 / T) * n ^ 2 := by ring
      have h4' : (n * m) ^ 3 / T ^ 2 = (m ^ 3 / T ^ 2) * n ^ 3 := by ring
      rw [h3', h4']
      have hc3 : 0 ≤ 3 * m ^ 2 / T := by positivity
      nlinarith
    exact mul_le_mul_of_nonneg_right hfrac (Real.exp_pos _).le
  have hcomb :
      T ^ 2 * ((2 * Real.pi)⁻¹ * ∑' k : ℕ,
          (6 * T + 6 * ((k : ℝ) + 1) * m + 3 * (((k : ℝ) + 1) * m) ^ 2 / T +
            (((k : ℝ) + 1) * m) ^ 3 / T ^ 2) / ((k : ℝ) + 1) ^ 3 * e k) -
      3 * T * ((2 * Real.pi)⁻¹ * ∑' k : ℕ,
          (3 * T ^ 2 + 3 * ((k : ℝ) + 1) * m * T + (((k : ℝ) + 1) * m) ^ 2) /
            ((k : ℝ) + 1) ^ 3 * e k) +
      3 * ((2 * Real.pi)⁻¹ * ∑' k : ℕ,
          (T ^ 3 + ((k : ℝ) + 1) * m * T ^ 2) / ((k : ℝ) + 1) ^ 3 * e k) =
      (2 * Real.pi)⁻¹ * ∑' k : ℕ, m ^ 3 * e k := by
    have hpull : ∀ (c : ℝ) (g : ℕ → ℝ), c * ((2 * Real.pi)⁻¹ * ∑' k, g k) =
        (2 * Real.pi)⁻¹ * ∑' k, c * g k := by
      intro c g
      rw [← mul_assoc, mul_comm c, mul_assoc, tsum_mul_left]
    rw [hpull, hpull, hpull, ← mul_sub, ← mul_add]
    congr 1
    rw [← (hs2.mul_left (T ^ 2)).tsum_sub (hs1.mul_left (3 * T)),
      ← ((hs2.mul_left (T ^ 2)).sub (hs1.mul_left (3 * T))).tsum_add (hs0.mul_left 3)]
    apply tsum_congr; intro k
    set n : ℝ := (k : ℝ) + 1
    have hn : n ≠ 0 := by positivity
    field_simp [hT.ne', hn]
    ring
  rw [hcomb, tsum_mul_left]
  have hgeom : ∑' k : ℕ, e k = Real.exp (-(m / T)) / (1 - Real.exp (-(m / T))) := by
    set r : ℝ := Real.exp (-(m / T))
    have hr_lt : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (div_pos hm hT))
    have hr_nonneg : 0 ≤ r := (Real.exp_pos _).le
    have he_eq : e = fun k : ℕ => r * r ^ k := by
      ext k
      simp only [e, r, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    rw [he_eq, tsum_mul_left, tsum_geometric_of_lt_one hr_nonneg hr_lt, div_eq_mul_inv]
  rw [hgeom]
  ring

private lemma bosePressure2D_real_ode {m T : ℝ} (hm : 0 < m) (hT : 0 < T) :
    let Q := T ^ 2 * iteratedDeriv 2 (bosePressure2D m) T -
      3 * T * iteratedDeriv 1 (bosePressure2D m) T + 3 * bosePressure2D m T
    m ^ 2 * T ^ 4 * iteratedDeriv 3 (bosePressure2D m) T -
      m ^ 2 * T ^ 3 * iteratedDeriv 2 (bosePressure2D m) T -
      m ^ 3 * Q - 2 * Real.pi * Q ^ 2 = 0 := by
  let Qfn : ℝ → ℝ := fun t =>
    t ^ 2 * iteratedDeriv 2 (bosePressure2D m) t -
      3 * t * iteratedDeriv 1 (bosePressure2D m) t + 3 * bosePressure2D m t
  let gfn : ℝ → ℝ := fun t =>
    m ^ 3 / (2 * Real.pi) * (Real.exp (-(m / t)) / (1 - Real.exp (-(m / t))))
  have heq : Qfn =ᶠ[𝓝 T] gfn := by
    filter_upwards [isOpen_Ioi.mem_nhds hT] with t ht
    exact bosePressure2D_Q_eq hm ht
  have hexp_ne : 1 - Real.exp (-(m / T)) ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (div_pos hm hT))))
  have hg_deriv : HasDerivAt gfn
      (m ^ 3 / (2 * Real.pi) *
        (Real.exp (-(m / T)) * (m / T ^ 2) / (1 - Real.exp (-(m / T))) ^ 2)) T := by
    have hdiv : HasDerivAt (fun t : ℝ => -(m / t)) (m / T ^ 2) T := by
      have := (hasDerivAt_inv hT.ne').const_mul (-m)
      convert this using 1
      · ext t; ring
      · field_simp [hT.ne']
    have he := hdiv.exp
    have hden : HasDerivAt (fun t : ℝ => 1 - Real.exp (-(m / t)))
        (-(Real.exp (-(m / T)) * (m / T ^ 2))) T := by
      simpa using (hasDerivAt_const T (1 : ℝ)).fun_sub he
    have hq := he.div hden hexp_ne
    convert hq.const_mul (m ^ 3 / (2 * Real.pi)) using 1
    field_simp [hexp_ne]
    ring
  have hQ_deriv : HasDerivAt Qfn
      (m ^ 3 / (2 * Real.pi) *
        (Real.exp (-(m / T)) * (m / T ^ 2) / (1 - Real.exp (-(m / T))) ^ 2)) T :=
    hg_deriv.congr_of_eventuallyEq heq
  have hd0 : HasDerivAt (bosePressure2D m) (iteratedDeriv 1 (bosePressure2D m) T) T := by
    rw [iteratedDeriv_one]
    exact (hasDerivAt_bosePressure2D hm hT).differentiableAt.hasDerivAt
  have hd1 : HasDerivAt (iteratedDeriv 1 (bosePressure2D m))
      (iteratedDeriv 2 (bosePressure2D m) T) T := by
    have h1 : iteratedDeriv 1 (bosePressure2D m) = deriv (bosePressure2D m) :=
      iteratedDeriv_one
    rw [h1, iteratedDeriv_succ, iteratedDeriv_one]
    exact (hasDerivAt_deriv_bosePressure2D hm hT).differentiableAt.hasDerivAt
  have hB2_eq : iteratedDeriv 2 (bosePressure2D m) =ᶠ[𝓝 T]
      fun t => (Qfn t + 3 * t * iteratedDeriv 1 (bosePressure2D m) t - 3 * bosePressure2D m t) /
        t ^ 2 := by
    filter_upwards [isOpen_Ioi.mem_nhds hT] with t (ht : 0 < t)
    dsimp only [Qfn]
    field_simp [ht.ne']
    ring
  have hB2_diff : DifferentiableAt ℝ (iteratedDeriv 2 (bosePressure2D m)) T := by
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hB2_eq
    have hnum : DifferentiableAt ℝ
        (fun t => Qfn t + 3 * t * iteratedDeriv 1 (bosePressure2D m) t - 3 * bosePressure2D m t) T :=
      (hQ_deriv.differentiableAt.add
        (((differentiableAt_id.const_mul 3).mul hd1.differentiableAt))).sub
        (hd0.differentiableAt.const_mul 3)
    exact hnum.div (differentiableAt_id.pow 2) (pow_ne_zero 2 hT.ne')
  have hd2 : HasDerivAt (iteratedDeriv 2 (bosePressure2D m))
      (iteratedDeriv 3 (bosePressure2D m) T) T := by
    have h3 : iteratedDeriv 3 (bosePressure2D m) T = deriv (iteratedDeriv 2 (bosePressure2D m)) T := by
      rw [iteratedDeriv_succ]
    rw [h3]
    exact hB2_diff.hasDerivAt
  have hQ_deriv' : HasDerivAt Qfn
      (T ^ 2 * iteratedDeriv 3 (bosePressure2D m) T -
        T * iteratedDeriv 2 (bosePressure2D m) T) T := by
    have h1 := ((hasDerivAt_pow 2 T).fun_mul hd2)
    have h2 := (((hasDerivAt_id T).const_mul (3 : ℝ)).fun_mul hd1)
    have h3 := hd0.const_mul (3 : ℝ)
    refine HasDerivAt.congr_deriv ((h1.fun_sub h2).fun_add h3) ?_
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq]
    ring
  have hderiv_eq : T ^ 2 * iteratedDeriv 3 (bosePressure2D m) T -
      T * iteratedDeriv 2 (bosePressure2D m) T =
      m ^ 3 / (2 * Real.pi) *
        (Real.exp (-(m / T)) * (m / T ^ 2) / (1 - Real.exp (-(m / T))) ^ 2) :=
    hQ_deriv'.unique hQ_deriv
  have hQ_val : Qfn T = gfn T := bosePressure2D_Q_eq hm hT
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  dsimp only [Qfn, gfn] at hQ_val ⊢
  rw [hQ_val]
  have hkey : m ^ 2 * T ^ 4 * iteratedDeriv 3 (bosePressure2D m) T -
      m ^ 2 * T ^ 3 * iteratedDeriv 2 (bosePressure2D m) T =
      m ^ 2 * T ^ 2 * (T ^ 2 * iteratedDeriv 3 (bosePressure2D m) T -
        T * iteratedDeriv 2 (bosePressure2D m) T) := by ring
  rw [hkey, hderiv_eq]
  field_simp [hT.ne', hpi, hexp_ne]
  ring

private lemma iteratedDeriv_ofReal_comp (f : ℝ → ℝ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun t : ℝ => (f t : ℂ)) x = ((iteratedDeriv k f x : ℝ) : ℂ) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have heq : iteratedDeriv k (fun t : ℝ => (f t : ℂ)) =
        fun t : ℝ => ((iteratedDeriv k f t : ℝ) : ℂ) := funext ih
    rw [heq]
    by_cases hd : DifferentiableAt ℝ (iteratedDeriv k f) x
    · exact (hd.hasDerivAt.ofReal_comp).deriv
    · have hnd : ¬ DifferentiableAt ℝ (fun t : ℝ => ((iteratedDeriv k f t : ℝ) : ℂ)) x := by
        intro hc
        have hr : DifferentiableAt ℝ (fun t : ℝ => Complex.reCLM ((iteratedDeriv k f t : ℝ) : ℂ)) x :=
          DifferentiableAt.comp x (Complex.reCLM.differentiableAt) hc
        exact hd (by simpa using hr)
      rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hnd]
      simp

/-- **Even Dimension (`d = 2`) Bose D-Algebraicity**:
For every positive mass `m > 0`, the exact 2D relativistic Bose pressure `bosePressure2D m`
satisfies the explicit nonzero order-3 algebraic differential equation `odePoly2D m 1` over `ℂ[T]`
at every `T > 0`. -/
theorem bosePressure2D_dAlgebraic {m : ℝ} (hm : 0 < m) :
    ∃ P : MvPolynomial (Fin 4) (Polynomial ℂ), P ≠ 0 ∧
      ∀ T : ℝ, 0 < T →
        MvPolynomial.eval
          (fun j : Fin 4 => iteratedDeriv j.val (fun t : ℝ => (bosePressure2D m t : ℂ)) T)
          (evalU P (T : ℂ)) = 0 := by
  refine ⟨odePoly2D (m : ℂ) 1, odePoly2D_ne_zero hm 1, fun T hT => ?_⟩
  have hreal := bosePressure2D_real_ode hm hT
  have hcast := congrArg (fun x : ℝ => (x : ℂ)) hreal
  simp only [odePoly2D, evalU, map_sub, map_add, map_mul, map_pow, MvPolynomial.map_C,
    MvPolynomial.map_X, MvPolynomial.eval_C, MvPolynomial.eval_X, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, one_mul,
    iteratedDeriv_ofReal_comp] at hcast ⊢
  simpa [iteratedDeriv_zero] using hcast

private lemma fermiPressure2D_Q_eq {m T : ℝ} (hm : 0 < m) (hT : 0 < T) :
    T ^ 2 * iteratedDeriv 2 (fermiPressure2D m) T -
      3 * T * iteratedDeriv 1 (fermiPressure2D m) T +
      3 * fermiPressure2D m T =
      m ^ 3 / (2 * Real.pi) * (Real.exp (-(m / T)) / (1 + Real.exp (-(m / T)))) := by
  have hm2 : 0 < 2 * m := by linarith
  have hd2_1 : DifferentiableAt ℝ (deriv (bosePressure2D m)) T :=
    (hasDerivAt_deriv_bosePressure2D hm hT).differentiableAt
  have hd2_2 : DifferentiableAt ℝ (deriv (bosePressure2D (2 * m))) T :=
    (hasDerivAt_deriv_bosePressure2D hm2 hT).differentiableAt
  have hF1 : ∀ t : ℝ, 0 < t →
      deriv (fermiPressure2D m) t =
        deriv (bosePressure2D m) t - (1 / 4 : ℝ) * deriv (bosePressure2D (2 * m)) t := by
    intro t ht
    have h1 := (hasDerivAt_bosePressure2D hm ht).differentiableAt.hasDerivAt
    have h2 := ((hasDerivAt_bosePressure2D hm2 ht).differentiableAt.hasDerivAt).const_mul (1 / 4 : ℝ)
    exact (h1.fun_sub h2).deriv
  have hF1_T : iteratedDeriv 1 (fermiPressure2D m) T =
      iteratedDeriv 1 (bosePressure2D m) T - (1 / 4 : ℝ) * iteratedDeriv 1 (bosePressure2D (2 * m)) T := by
    simp only [iteratedDeriv_one]
    exact hF1 T hT
  have hF2_T : iteratedDeriv 2 (fermiPressure2D m) T =
      iteratedDeriv 2 (bosePressure2D m) T - (1 / 4 : ℝ) * iteratedDeriv 2 (bosePressure2D (2 * m)) T := by
    have h2eq : ∀ f : ℝ → ℝ, iteratedDeriv 2 f T = deriv (deriv f) T := by
      intro f; rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [h2eq, h2eq, h2eq]
    have hev : deriv (fermiPressure2D m) =ᶠ[𝓝 T]
        fun t => deriv (bosePressure2D m) t - (1 / 4 : ℝ) * deriv (bosePressure2D (2 * m)) t := by
      filter_upwards [isOpen_Ioi.mem_nhds hT] with t ht
      exact hF1 t ht
    rw [hev.deriv_eq]
    exact (hd2_1.hasDerivAt.fun_sub (hd2_2.hasDerivAt.const_mul (1 / 4 : ℝ))).deriv
  rw [hF1_T, hF2_T]
  have hQ1 := bosePressure2D_Q_eq hm hT
  have hQ2 := bosePressure2D_Q_eq hm2 hT
  have hlin : T ^ 2 * (iteratedDeriv 2 (bosePressure2D m) T -
        (1 / 4 : ℝ) * iteratedDeriv 2 (bosePressure2D (2 * m)) T) -
      3 * T * (iteratedDeriv 1 (bosePressure2D m) T -
        (1 / 4 : ℝ) * iteratedDeriv 1 (bosePressure2D (2 * m)) T) +
      3 * fermiPressure2D m T =
      (T ^ 2 * iteratedDeriv 2 (bosePressure2D m) T -
        3 * T * iteratedDeriv 1 (bosePressure2D m) T + 3 * bosePressure2D m T) -
      (1 / 4 : ℝ) * (T ^ 2 * iteratedDeriv 2 (bosePressure2D (2 * m)) T -
        3 * T * iteratedDeriv 1 (bosePressure2D (2 * m)) T + 3 * bosePressure2D (2 * m) T) := by
    unfold fermiPressure2D; ring
  rw [hlin, hQ1, hQ2]
  set z : ℝ := Real.exp (-(m / T))
  have hz2 : Real.exp (-(2 * m / T)) = z ^ 2 := by
    dsimp only [z]
    rw [sq, ← Real.exp_add]
    congr 1; ring
  rw [hz2]
  have hz_pos : 0 < z := Real.exp_pos _
  have hz_lt : z < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (div_pos hm hT))
  have h1 : 1 - z ≠ 0 := by linarith
  have h2 : 1 + z ≠ 0 := by linarith
  have h3 : 1 - z ^ 2 ≠ 0 := by nlinarith
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp [h1, h2, h3, hpi]
  ring

private lemma fermiPressure2D_real_ode {m T : ℝ} (hm : 0 < m) (hT : 0 < T) :
    let Q := T ^ 2 * iteratedDeriv 2 (fermiPressure2D m) T -
      3 * T * iteratedDeriv 1 (fermiPressure2D m) T + 3 * fermiPressure2D m T
    m ^ 2 * T ^ 4 * iteratedDeriv 3 (fermiPressure2D m) T -
      m ^ 2 * T ^ 3 * iteratedDeriv 2 (fermiPressure2D m) T -
      m ^ 3 * Q + 2 * Real.pi * Q ^ 2 = 0 := by
  have hm2 : 0 < 2 * m := by linarith
  let Qfn : ℝ → ℝ := fun t =>
    t ^ 2 * iteratedDeriv 2 (fermiPressure2D m) t -
      3 * t * iteratedDeriv 1 (fermiPressure2D m) t + 3 * fermiPressure2D m t
  let gfn : ℝ → ℝ := fun t =>
    m ^ 3 / (2 * Real.pi) * (Real.exp (-(m / t)) / (1 + Real.exp (-(m / t))))
  have heq : Qfn =ᶠ[𝓝 T] gfn := by
    filter_upwards [isOpen_Ioi.mem_nhds hT] with t ht
    exact fermiPressure2D_Q_eq hm ht
  have hexp_ne : 1 + Real.exp (-(m / T)) ≠ 0 := by positivity
  have hg_deriv : HasDerivAt gfn
      (m ^ 3 / (2 * Real.pi) *
        (Real.exp (-(m / T)) * (m / T ^ 2) / (1 + Real.exp (-(m / T))) ^ 2)) T := by
    have hdiv : HasDerivAt (fun t : ℝ => -(m / t)) (m / T ^ 2) T := by
      have := (hasDerivAt_inv hT.ne').const_mul (-m)
      convert this using 1
      · ext t; ring
      · field_simp [hT.ne']
    have he := hdiv.exp
    have hden : HasDerivAt (fun t : ℝ => 1 + Real.exp (-(m / t)))
        (Real.exp (-(m / T)) * (m / T ^ 2)) T := by
      simpa using (hasDerivAt_const T (1 : ℝ)).fun_add he
    have hq := he.div hden hexp_ne
    convert hq.const_mul (m ^ 3 / (2 * Real.pi)) using 1
    field_simp [hexp_ne]
    ring
  have hQ_deriv : HasDerivAt Qfn
      (m ^ 3 / (2 * Real.pi) *
        (Real.exp (-(m / T)) * (m / T ^ 2) / (1 + Real.exp (-(m / T))) ^ 2)) T :=
    hg_deriv.congr_of_eventuallyEq heq
  have hd0 : HasDerivAt (fermiPressure2D m) (iteratedDeriv 1 (fermiPressure2D m) T) T := by
    rw [iteratedDeriv_one]
    have h1 := (hasDerivAt_bosePressure2D hm hT).differentiableAt
    have h2 := (hasDerivAt_bosePressure2D hm2 hT).differentiableAt.const_mul (1 / 4 : ℝ)
    exact (h1.fun_sub h2).hasDerivAt
  have hd1 : HasDerivAt (iteratedDeriv 1 (fermiPressure2D m))
      (iteratedDeriv 2 (fermiPressure2D m) T) T := by
    have h1 : iteratedDeriv 1 (fermiPressure2D m) = deriv (fermiPressure2D m) :=
      iteratedDeriv_one
    rw [h1, iteratedDeriv_succ, iteratedDeriv_one]
    have hev : deriv (fermiPressure2D m) =ᶠ[𝓝 T]
        fun t => deriv (bosePressure2D m) t - (1 / 4 : ℝ) * deriv (bosePressure2D (2 * m)) t := by
      filter_upwards [isOpen_Ioi.mem_nhds hT] with t ht
      have ha := (hasDerivAt_bosePressure2D hm ht).differentiableAt.hasDerivAt
      have hb := ((hasDerivAt_bosePressure2D hm2 ht).differentiableAt.hasDerivAt).const_mul (1 / 4 : ℝ)
      exact (ha.fun_sub hb).deriv
    have hdiff : DifferentiableAt ℝ (deriv (fermiPressure2D m)) T := by
      refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
      exact (hasDerivAt_deriv_bosePressure2D hm hT).differentiableAt.fun_sub
        ((hasDerivAt_deriv_bosePressure2D hm2 hT).differentiableAt.const_mul (1 / 4 : ℝ))
    exact hdiff.hasDerivAt
  have hB2_eq : iteratedDeriv 2 (fermiPressure2D m) =ᶠ[𝓝 T]
      fun t => (Qfn t + 3 * t * iteratedDeriv 1 (fermiPressure2D m) t - 3 * fermiPressure2D m t) /
        t ^ 2 := by
    filter_upwards [isOpen_Ioi.mem_nhds hT] with t (ht : 0 < t)
    dsimp only [Qfn]
    field_simp [ht.ne']
    ring
  have hB2_diff : DifferentiableAt ℝ (iteratedDeriv 2 (fermiPressure2D m)) T := by
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hB2_eq
    have hnum : DifferentiableAt ℝ
        (fun t => Qfn t + 3 * t * iteratedDeriv 1 (fermiPressure2D m) t - 3 * fermiPressure2D m t) T :=
      (hQ_deriv.differentiableAt.add
        (((differentiableAt_id.const_mul 3).mul hd1.differentiableAt))).sub
        (hd0.differentiableAt.const_mul 3)
    exact hnum.div (differentiableAt_id.pow 2) (pow_ne_zero 2 hT.ne')
  have hd2 : HasDerivAt (iteratedDeriv 2 (fermiPressure2D m))
      (iteratedDeriv 3 (fermiPressure2D m) T) T := by
    have h3 : iteratedDeriv 3 (fermiPressure2D m) T = deriv (iteratedDeriv 2 (fermiPressure2D m)) T := by
      rw [iteratedDeriv_succ]
    rw [h3]
    exact hB2_diff.hasDerivAt
  have hQ_deriv' : HasDerivAt Qfn
      (T ^ 2 * iteratedDeriv 3 (fermiPressure2D m) T -
        T * iteratedDeriv 2 (fermiPressure2D m) T) T := by
    have h1 := ((hasDerivAt_pow 2 T).fun_mul hd2)
    have h2 := (((hasDerivAt_id T).const_mul (3 : ℝ)).fun_mul hd1)
    have h3 := hd0.const_mul (3 : ℝ)
    refine HasDerivAt.congr_deriv ((h1.fun_sub h2).fun_add h3) ?_
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq]
    ring
  have hderiv_eq : T ^ 2 * iteratedDeriv 3 (fermiPressure2D m) T -
      T * iteratedDeriv 2 (fermiPressure2D m) T =
      m ^ 3 / (2 * Real.pi) *
        (Real.exp (-(m / T)) * (m / T ^ 2) / (1 + Real.exp (-(m / T))) ^ 2) :=
    hQ_deriv'.unique hQ_deriv
  have hQ_val : Qfn T = gfn T := fermiPressure2D_Q_eq hm hT
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  dsimp only [Qfn, gfn] at hQ_val ⊢
  rw [hQ_val]
  have hkey : m ^ 2 * T ^ 4 * iteratedDeriv 3 (fermiPressure2D m) T -
      m ^ 2 * T ^ 3 * iteratedDeriv 2 (fermiPressure2D m) T =
      m ^ 2 * T ^ 2 * (T ^ 2 * iteratedDeriv 3 (fermiPressure2D m) T -
        T * iteratedDeriv 2 (fermiPressure2D m) T) := by ring
  rw [hkey, hderiv_eq]
  field_simp [hT.ne', hpi, hexp_ne]
  ring

/-- **Even Dimension (`d = 2`) Fermi D-Algebraicity**:
For every positive mass `m > 0`, the exact 2D relativistic Fermi pressure `fermiPressure2D m`
satisfies the explicit nonzero order-3 algebraic differential equation `odePoly2D m (-1)` over `ℂ[T]`
at every `T > 0`. -/
theorem fermiPressure2D_dAlgebraic {m : ℝ} (hm : 0 < m) :
    ∃ P : MvPolynomial (Fin 4) (Polynomial ℂ), P ≠ 0 ∧
      ∀ T : ℝ, 0 < T →
        MvPolynomial.eval
          (fun j : Fin 4 => iteratedDeriv j.val (fun t : ℝ => (fermiPressure2D m t : ℂ)) T)
          (evalU P (T : ℂ)) = 0 := by
  refine ⟨odePoly2D (m : ℂ) (-1), odePoly2D_ne_zero hm (-1), fun T hT => ?_⟩
  have hreal := fermiPressure2D_real_ode hm hT
  have hcast := congrArg (fun x : ℝ => (x : ℂ)) hreal
  simp only [odePoly2D, evalU, map_sub, map_add, map_mul, map_pow, MvPolynomial.map_C,
    MvPolynomial.map_X, MvPolynomial.eval_C, MvPolynomial.eval_X, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, neg_one_mul,
    iteratedDeriv_ofReal_comp] at hcast ⊢
  simpa [iteratedDeriv_zero] using hcast

/-! ### 2. Branch-Flipping Monodromy & Vandermonde Transcendence for Matsubara Mode Series -/

/-- A separated quadratically-growing sequence of positive Matsubara mode locations `a_k > 0`. -/
structure ModeSeq where
  a : ℕ → ℝ
  a_pos : ∀ k : ℕ, 0 < a k
  δ : ℝ
  δ_pos : 0 < δ
  sep : ∀ k : ℕ, a k + δ ≤ a (k + 1)
  c : ℝ
  c_pos : 0 < c
  quad : ∀ k : ℕ, c * ((k : ℝ) + 1) ^ 2 ≤ a k

/-- Bosonic Matsubara mode locations `a_k = (k + 1)²`. -/
@[expose] def boseModes : ModeSeq where
  a := fun k => ((k : ℝ) + 1) ^ 2
  a_pos := fun k => by positivity
  δ := 3
  δ_pos := by norm_num
  sep := fun k => by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    push_cast; nlinarith
  c := 1
  c_pos := by norm_num
  quad := fun k => by simp

/-- Fermionic Matsubara mode locations `a_k = (k + 1/2)²`. -/
@[expose] def fermiModes : ModeSeq where
  a := fun k => ((k : ℝ) + 1 / 2) ^ 2
  a_pos := fun k => by positivity
  δ := 2
  δ_pos := by norm_num
  sep := fun k => by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    push_cast; nlinarith
  c := 1 / 4
  c_pos := by norm_num
  quad := fun k => by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith

private lemma ModeSeq.strictMono (ms : ModeSeq) : StrictMono ms.a := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  linarith [ms.sep k, ms.δ_pos]

private lemma ModeSeq.le_add_mul (ms : ModeSeq) (k m : ℕ) (h : k < m) :
    ms.a k + ms.δ ≤ ms.a m := by
  have h1 : k + 1 ≤ m := h
  have h2 : ms.a (k + 1) ≤ ms.a m := ms.strictMono.monotone h1
  linarith [ms.sep k]

/-- Principal branch `(z + b)^{-3/2}` with branch cut along `(-∞, -b]`. -/
@[expose] def modeTermL (b : ℝ) (z : ℂ) : ℂ :=
  (z + (b : ℂ)) ^ (-(3 : ℂ) / 2)

/-- Upward-cut branch `exp(3πi/4) (i (z + b))^{-3/2}` with branch cut along `-b + i[0, ∞)`. -/
@[expose] def modeTermU (b : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (3 * (Real.pi : ℂ) * Complex.I / 4) * (Complex.I * (z + (b : ℂ))) ^ (-(3 : ℂ) / 2)

/-- The Matsubara mode series `S_a(z) = ∑' k, (z + a_k)^{-3/2}`. -/
@[expose] def modeSeries (ms : ModeSeq) (z : ℂ) : ℂ :=
  ∑' k : ℕ, modeTermL (ms.a k) z

/-- The Matsubara mode series with signs flipped at all indices in `F : Finset ℕ`. -/
@[expose] def modeSeriesFlipped (ms : ModeSeq) (F : Finset ℕ) (z : ℂ) : ℂ :=
  modeSeries ms z - 2 * ∑ k ∈ F, modeTermL (ms.a k) z

/-- A slit domain `ℂ \ ((-∞, M] ∪ ⋃_{s ∈ S} (s + i[0, ∞)))`. -/
private def slitDomain (M : ℝ) (S : Finset ℝ) : Set ℂ :=
  {z : ℂ | ¬(z.im = 0 ∧ z.re ≤ M) ∧ ∀ s ∈ S, ¬(z.re = s ∧ 0 ≤ z.im)}

private lemma isOpen_slitDomain (M : ℝ) (S : Finset ℝ) : IsOpen (slitDomain M S) := by
  have h1 : IsOpen {z : ℂ | ¬(z.im = 0 ∧ z.re ≤ M)} := by
    have hc : IsClosed {z : ℂ | z.im = 0 ∧ z.re ≤ M} :=
      (isClosed_eq Complex.continuous_im continuous_const).inter
        (isClosed_le Complex.continuous_re continuous_const)
    exact hc.isOpen_compl
  have h2 : IsOpen {z : ℂ | ∀ s ∈ S, ¬(z.re = s ∧ 0 ≤ z.im)} := by
    have heq : {z : ℂ | ∀ s ∈ S, ¬(z.re = s ∧ 0 ≤ z.im)} =
        ⋂ s ∈ S, {z : ℂ | ¬(z.re = s ∧ 0 ≤ z.im)} := by ext z; simp
    rw [heq]
    refine isOpen_biInter_finset fun s _ => ?_
    have hc : IsClosed {z : ℂ | z.re = s ∧ 0 ≤ z.im} :=
      (isClosed_eq Complex.continuous_re continuous_const).inter
        (isClosed_le continuous_const Complex.continuous_im)
    exact hc.isOpen_compl
  exact h1.inter h2

private lemma joinedIn_segment {U : Set ℂ} {a b : ℂ}
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, (1 - (t : ℂ)) * a + (t : ℂ) * b ∈ U) :
    JoinedIn U a b := by
  refine ⟨{
    toFun := fun t => (1 - ((t : ℝ) : ℂ)) * a + ((t : ℝ) : ℂ) * b
    continuous_toFun := by fun_prop
    source' := by simp
    target' := by simp
  }, fun t => hseg t t.2⟩

private lemma isPreconnected_slitDomain (M : ℝ) (S : Finset ℝ) {ε : ℝ} (hε : 0 < ε)
    (hS : ∀ s ∈ S, M + ε < s) : IsPreconnected (slitDomain M S) := by
  have hbase : (-Complex.I) ∈ slitDomain M S := by
    refine ⟨?_, fun s _ => ?_⟩ <;> simp
  have hjoin_neg_im : ∀ w : ℂ, w.im < 0 → JoinedIn (slitDomain M S) w (-Complex.I) := by
    intro w hw
    refine joinedIn_segment fun t ht => ?_
    have him : ((1 - (t : ℂ)) * w + (t : ℂ) * (-Complex.I)).im < 0 := by
      simp only [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
        Complex.sub_im, Complex.one_im, Complex.ofReal_im, sub_zero, zero_mul, add_zero,
        Complex.I_re, Complex.neg_im, Complex.I_im, mul_neg, mul_one]
      have ht0 : 0 ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      rcases eq_or_lt_of_le ht1 with rfl | hlt <;> nlinarith
    refine ⟨fun h => by linarith [h.1], fun s _ h => by linarith [h.2]⟩
  have hjoin_vert : ∀ w : ℂ, M < w.re → (∀ s ∈ S, w.re ≠ s) →
      JoinedIn (slitDomain M S) w (w.re - Complex.I) := by
    intro w hM hwS
    refine joinedIn_segment fun t ht => ?_
    have hre : ((1 - (t : ℂ)) * w + (t : ℂ) * ((w.re : ℂ) - Complex.I)).re = w.re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
        Complex.sub_im, Complex.one_im, Complex.ofReal_im, sub_zero, zero_mul, sub_self,
        Complex.I_re, Complex.I_im, zero_sub, mul_neg]
      ring
    refine ⟨fun h => by linarith [h.2], fun s hs h => hwS s hs (hre.symm.trans h.1)⟩
  have hpath : IsPathConnected (slitDomain M S) := by
    refine ⟨-Complex.I, hbase, fun z hz => ?_⟩
    by_cases him : z.im < 0
    · exact (hjoin_neg_im z him).symm
    · push Not at him
      by_cases hre : M < z.re
      · have hzS : ∀ s ∈ S, z.re ≠ s := fun s hs h => hz.2 s hs ⟨h, him⟩
        have j1 := hjoin_vert z hre hzS
        have j2 := hjoin_neg_im ((z.re : ℂ) - Complex.I) (by simp)
        exact (j1.trans j2).symm
      · push Not at hre
        have him_pos : 0 < z.im := by
          rcases eq_or_lt_of_le him with h0 | hpos
          · exact absurd ⟨h0.symm, hre⟩ hz.1
          · exact hpos
        let w : ℂ := ((M + ε / 2 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I
        have j0 : JoinedIn (slitDomain M S) z w := by
          refine joinedIn_segment fun t ht => ?_
          have hre_seg : ((1 - (t : ℂ)) * z + (t : ℂ) * w).re ≤ M + ε / 2 := by
            simp only [w, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.one_re,
              Complex.ofReal_re, Complex.sub_im, Complex.one_im, Complex.ofReal_im, sub_zero,
              zero_mul, sub_self, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
            have ht0 : 0 ≤ t := ht.1
            have ht1 : t ≤ 1 := ht.2
            nlinarith
          have him_seg : ((1 - (t : ℂ)) * z + (t : ℂ) * w).im = z.im := by
            simp only [w, Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.one_re,
              Complex.ofReal_re, Complex.sub_im, Complex.one_im, Complex.ofReal_im, sub_zero,
              zero_mul, add_zero, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
            ring
          refine ⟨fun h => by linarith [h.1], fun s hs h => ?_⟩
          have hs_gt := hS s hs
          linarith [h.1]
        have hwM : M < w.re := by simp [w]; linarith
        have hwS : ∀ s ∈ S, w.re ≠ s := fun s hs => by
          simp only [w, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
          linarith [hS s hs]
        have j1 := hjoin_vert w hwM hwS
        have j2 := hjoin_neg_im ((w.re : ℂ) - Complex.I) (by simp)
        exact ((j0.trans j1).trans j2).symm
  exact hpath.isConnected.isPreconnected

private lemma modeTermL_analyticOnNhd (b : ℝ) :
    AnalyticOnNhd ℂ (modeTermL b) {z : ℂ | ¬(z.im = 0 ∧ z.re ≤ -b)} := by
  have hopen : IsOpen {z : ℂ | ¬(z.im = 0 ∧ z.re ≤ -b)} := by
    have hc : IsClosed {z : ℂ | z.im = 0 ∧ z.re ≤ -b} :=
      (isClosed_eq Complex.continuous_im continuous_const).inter
        (isClosed_le Complex.continuous_re continuous_const)
    exact hc.isOpen_compl
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hopen
  have hslit : z + (b : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases him : z.im = 0
    · left
      have hgt : -b < z.re := lt_of_not_ge fun hle => hz ⟨him, hle⟩
      simp; linarith
    · right
      simpa using him
  exact ((differentiableAt_id.add (differentiableAt_const (b : ℂ))).cpow_const
    hslit).differentiableWithinAt

private lemma modeTermU_analyticOnNhd (b : ℝ) :
    AnalyticOnNhd ℂ (modeTermU b) {z : ℂ | ¬(z.re = -b ∧ 0 ≤ z.im)} := by
  have hopen : IsOpen {z : ℂ | ¬(z.re = -b ∧ 0 ≤ z.im)} := by
    have hc : IsClosed {z : ℂ | z.re = -b ∧ 0 ≤ z.im} :=
      (isClosed_eq Complex.continuous_re continuous_const).inter
        (isClosed_le continuous_const Complex.continuous_im)
    exact hc.isOpen_compl
  refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hopen
  have hslit : Complex.I * (z + (b : ℂ)) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases hre : z.re = -b
    · left
      have hlt : z.im < 0 := lt_of_not_ge fun hge => hz ⟨hre, hge⟩
      simp [hlt]
    · right
      simp only [Complex.mul_im, Complex.I_re, Complex.add_im, Complex.ofReal_im, add_zero,
        zero_mul, Complex.I_im, Complex.add_re, Complex.ofReal_re, one_mul, zero_add]
      intro h0
      exact hre (by linarith)
  have hdiff : DifferentiableAt ℂ (fun w : ℂ => Complex.I * (w + (b : ℂ))) z :=
    (differentiableAt_const Complex.I).mul (differentiableAt_id.add (differentiableAt_const (b : ℂ)))
  exact ((differentiableAt_const _).mul (hdiff.cpow_const hslit)).differentiableWithinAt

private lemma modeTermU_eq_modeTermL_of_pos (b : ℝ) {x : ℝ} (hx : 0 < x + b) :
    modeTermU b (x : ℂ) = modeTermL b (x : ℂ) := by
  unfold modeTermU modeTermL
  set r : ℝ := x + b
  have hr : 0 < r := hx
  have hxb : (x : ℂ) + (b : ℂ) = (r : ℂ) := by push_cast [r]; rfl
  rw [hxb]
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hir_ne : Complex.I * (r : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero hr_ne
  rw [Complex.cpow_def_of_ne_zero hir_ne, Complex.cpow_def_of_ne_zero hr_ne, ← Complex.exp_add]
  have hlog : Complex.log (Complex.I * (r : ℂ)) = Complex.log (r : ℂ) + (Real.pi : ℂ) * Complex.I / 2 := by
    rw [Complex.log, Complex.log]
    have hnorm : ‖Complex.I * (r : ℂ)‖ = ‖(r : ℂ)‖ := by simp
    have harg1 : (Complex.I * (r : ℂ)).arg = Real.pi / 2 := by
      have : Complex.I * (r : ℂ) = (r : ℂ) * Complex.I := mul_comm _ _
      rw [this, Complex.arg_real_mul Complex.I hr, Complex.arg_I]
    have harg2 : (r : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg hr.le
    rw [hnorm, harg1, harg2]
    push_cast
    ring
  rw [hlog]
  congr 1
  ring

private lemma modeTermU_eq_neg_modeTermL_of_QUL (b : ℝ) {z : ℂ} (hre : z.re < -b) (him : 0 < z.im) :
    modeTermU b z = -modeTermL b z := by
  unfold modeTermU modeTermL
  set w : ℂ := z + (b : ℂ)
  have hw_re : w.re < 0 := by simp [w]; linarith
  have hw_im : 0 < w.im := by simp [w, him]
  have hw_ne : w ≠ 0 := fun h => by rw [h] at hw_im; simp at hw_im
  have hiw_ne : Complex.I * w ≠ 0 := mul_ne_zero Complex.I_ne_zero hw_ne
  have harg_w : Real.pi / 2 < w.arg := by
    have hnn_arg : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr hw_im.le
    have hcos_neg : Real.cos w.arg < 0 := by
      rw [Complex.cos_arg hw_ne]
      exact div_neg_of_neg_of_pos hw_re (norm_pos_iff.mpr hw_ne)
    by_contra hle
    push Not at hle
    have hcos_nn : 0 ≤ Real.cos w.arg :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hle⟩
    linarith
  have hlog : Complex.log (Complex.I * w) = Complex.log w - 3 * (Real.pi : ℂ) * Complex.I / 2 := by
    rw [Complex.log, Complex.log]
    have hnorm : ‖Complex.I * w‖ = ‖w‖ := by simp
    have harg_iw : (Complex.I * w).arg = w.arg - 3 * Real.pi / 2 := by
      set θ : ℝ := w.arg - 3 * Real.pi / 2
      have hθ_gt : -Real.pi < θ := by dsimp only [θ]; linarith [harg_w]
      have hθ_le : θ ≤ Real.pi := by dsimp only [θ]; linarith [Complex.arg_le_pi w, Real.pi_pos]
      have hpolar : Complex.I * w = (‖w‖ : ℂ) * (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I) := by
        rw [← Complex.exp_mul_I]
        have h1 : (θ : ℂ) * Complex.I = (w.arg : ℂ) * Complex.I - 3 * (Real.pi : ℂ) * Complex.I / 2 := by
          push_cast [θ]; ring
        rw [h1, sub_eq_add_neg, Complex.exp_add, ← mul_assoc, Complex.norm_mul_exp_arg_mul_I]
        have he : Complex.exp (-(3 * (Real.pi : ℂ) * Complex.I / 2)) = Complex.I := by
          have : -(3 * (Real.pi : ℂ) * Complex.I / 2) =
              ((Real.pi : ℂ) / 2) * Complex.I + (-2 * (Real.pi : ℂ) * Complex.I) := by ring
          rw [this, Complex.exp_add, Complex.exp_pi_div_two_mul_I]
          have h2pi : Complex.exp (-2 * (Real.pi : ℂ) * Complex.I) = 1 := by
            have : -2 * (Real.pi : ℂ) * Complex.I = -(2 * (Real.pi : ℂ) * Complex.I) := by ring
            rw [this, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
          rw [h2pi, mul_one]
        rw [he, mul_comm]
      rw [hpolar, Complex.arg_mul_cos_add_sin_mul_I (norm_pos_iff.mpr hw_ne) ⟨hθ_gt, hθ_le⟩]
    rw [hnorm, harg_iw]
    push_cast
    ring
  rw [Complex.cpow_def_of_ne_zero hiw_ne, Complex.cpow_def_of_ne_zero hw_ne, ← Complex.exp_add, hlog]
  have hexp : 3 * (Real.pi : ℂ) * Complex.I / 4 +
      (Complex.log w - 3 * (Real.pi : ℂ) * Complex.I / 2) * (-(3 : ℂ) / 2) =
      Complex.log w * (-(3 : ℂ) / 2) + 3 * (Real.pi : ℂ) * Complex.I := by ring
  rw [hexp, Complex.exp_add]
  have h3pi : Complex.exp (3 * (Real.pi : ℂ) * Complex.I) = -1 := by
    have : 3 * (Real.pi : ℂ) * Complex.I = (Real.pi : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I := by ring
    rw [this, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_two_pi_mul_I, mul_one]
  rw [h3pi, mul_neg_one]

private lemma norm_cpow_neg_three_halves {w : ℂ} (hw : w ≠ 0) :
    ‖w ^ (-(3 : ℂ) / 2)‖ = ‖w‖ ^ (-(3 : ℝ) / 2) := by
  rw [Complex.cpow_def_of_ne_zero hw, Complex.norm_exp]
  have hre : (Complex.log w * (-(3 : ℂ) / 2)).re = Real.log ‖w‖ * (-(3 : ℝ) / 2) := by
    simp [Complex.log_re]
  rw [hre, Real.rpow_def_of_pos (norm_pos_iff.mpr hw)]

private lemma modeSeries_tail_analyticOnNhd (ms : ModeSeq) (N : ℕ) :
    AnalyticOnNhd ℂ (fun z => ∑' k : ℕ, modeTermL (ms.a (N + k)) z)
      {z : ℂ | ¬(z.im = 0 ∧ z.re ≤ -ms.a N)} := by
  have hopen : IsOpen {z : ℂ | ¬(z.im = 0 ∧ z.re ≤ -ms.a N)} := by
    have hc : IsClosed {z : ℂ | z.im = 0 ∧ z.re ≤ -ms.a N} :=
      (isClosed_eq Complex.continuous_im continuous_const).inter
        (isClosed_le Complex.continuous_re continuous_const)
    exact hc.isOpen_compl
  intro z₀ hz₀
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hopen z₀ hz₀
  obtain ⟨K, hK⟩ := exists_nat_gt (Real.sqrt (2 * (‖z₀‖ + r) / ms.c))
  have hbound_a : ∀ k : ℕ, K ≤ k → 2 * (‖z₀‖ + r) ≤ ms.a (N + k) := by
    intro k hk
    have h1 : Real.sqrt (2 * (‖z₀‖ + r) / ms.c) < (N + k : ℝ) + 1 := by
      have hk' : (K : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
      have hN' : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    have hsq : 2 * (‖z₀‖ + r) / ms.c ≤ ((N + k : ℝ) + 1) ^ 2 := by
      have hc := ms.c_pos
      have hnn : 0 ≤ 2 * (‖z₀‖ + r) / ms.c := by positivity
      calc 2 * (‖z₀‖ + r) / ms.c = (Real.sqrt (2 * (‖z₀‖ + r) / ms.c)) ^ 2 :=
            (Real.sq_sqrt hnn).symm
        _ ≤ ((N + k : ℝ) + 1) ^ 2 := by nlinarith [Real.sqrt_nonneg (2 * (‖z₀‖ + r) / ms.c)]
    have hquad := ms.quad (N + k)
    have hmul : 2 * (‖z₀‖ + r) ≤ ms.c * ((N + k : ℝ) + 1) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hsq ms.c_pos.le
      rwa [mul_div_cancel₀ _ ms.c_pos.ne'] at this
    have hcast : ((N + k : ℕ) : ℝ) = (N : ℝ) + (k : ℝ) := Nat.cast_add N k
    rw [hcast] at hquad
    linarith
  have hnorm_ge : ∀ k : ℕ, K ≤ k → ∀ w ∈ Metric.ball z₀ r,
      (ms.c / 2) * ((k : ℝ) + 1) ^ 2 ≤ ‖w + (ms.a (N + k) : ℂ)‖ := by
    intro k hk w hw
    have hw_norm : ‖w‖ ≤ ‖z₀‖ + r := by
      have hdist : ‖w - z₀‖ < r := by simpa [dist_eq_norm] using Metric.mem_ball.mp hw
      have := norm_add_le (w - z₀) z₀
      have heq : (w - z₀) + z₀ = w := sub_add_cancel w z₀
      rw [heq] at this
      linarith
    have ha_ge : 2 * ‖w‖ ≤ ms.a (N + k) := by linarith [hbound_a k hk]
    have hrev : ms.a (N + k) - ‖w‖ ≤ ‖w + (ms.a (N + k) : ℂ)‖ := by
      have htri := norm_sub_norm_le (ms.a (N + k) : ℂ) (-w)
      have h1 : (ms.a (N + k) : ℂ) - (-w) = w + (ms.a (N + k) : ℂ) := by ring
      rw [h1, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (ms.a_pos (N + k))] at htri
      exact htri
    have hquad : ms.c * ((k : ℝ) + 1) ^ 2 ≤ ms.a (N + k) := by
      have hq := ms.quad (N + k)
      have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hcast : ((N + k : ℕ) : ℝ) = (N : ℝ) + (k : ℝ) := Nat.cast_add N k
      rw [hcast] at hq
      have hsq : ((k : ℝ) + 1) ^ 2 ≤ ((N : ℝ) + (k : ℝ) + 1) ^ 2 := by nlinarith
      nlinarith [ms.c_pos]
    have hhalf : (ms.c / 2) * ((k : ℝ) + 1) ^ 2 ≤ ms.a (N + k) / 2 := by linarith
    linarith
  let u : ℕ → ℝ := fun k => (ms.c / 2) ^ (-(3 : ℝ) / 2) * ((k : ℝ) + 1) ^ (-(3 : ℝ))
  have hu : Summable u := by
    have hp : Summable (fun n : ℕ => ((n : ℝ) ^ (3 : ℝ))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    have hcomp := hp.comp_injective Nat.succ_injective
    have h1 : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (-(3 : ℝ))) := by
      refine hcomp.congr fun k => ?_
      simp only [Function.comp, Nat.cast_succ]
      rw [Real.rpow_neg (by positivity)]
    exact h1.mul_left _
  have htail_bound : ∀ k : ℕ, ∀ w ∈ Metric.ball z₀ r,
      ‖modeTermL (ms.a (N + (K + k))) w‖ ≤ u k := by
    intro k w hw
    have hge := hnorm_ge (K + k) (Nat.le_add_right K k) w hw
    have hpos_rhs : 0 < (ms.c / 2) * ((k : ℝ) + 1) ^ 2 := by
      have := ms.c_pos; positivity
    have hge' : (ms.c / 2) * ((k : ℝ) + 1) ^ 2 ≤ ‖w + (ms.a (N + (K + k)) : ℂ)‖ := by
      have hle : ((k : ℝ) + 1) ^ 2 ≤ (((K + k : ℕ) : ℝ) + 1) ^ 2 := by
        have : (k : ℝ) + 1 ≤ ((K + k : ℕ) : ℝ) + 1 := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) K]
        nlinarith
      have hc2 : 0 < ms.c / 2 := half_pos ms.c_pos
      nlinarith
    have hw_ne : w + (ms.a (N + (K + k)) : ℂ) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hge'; linarith
    unfold modeTermL
    rw [norm_cpow_neg_three_halves hw_ne]
    calc ‖w + (ms.a (N + (K + k)) : ℂ)‖ ^ (-(3 : ℝ) / 2)
        ≤ ((ms.c / 2) * ((k : ℝ) + 1) ^ 2) ^ (-(3 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_nonpos hpos_rhs hge' (by norm_num)
      _ = (ms.c / 2) ^ (-(3 : ℝ) / 2) * (((k : ℝ) + 1) ^ 2) ^ (-(3 : ℝ) / 2) :=
          Real.mul_rpow (by linarith [ms.c_pos]) (by positivity)
      _ = u k := by
          dsimp only [u]
          congr 1
          rw [← Real.rpow_natCast ((k : ℝ) + 1) 2, ← Real.rpow_mul (by positivity)]
          norm_num
  have hterm_diff : ∀ j : ℕ, DifferentiableOn ℂ (modeTermL (ms.a (N + j))) (Metric.ball z₀ r) := by
    intro j w hw
    have hmem : w ∈ {z : ℂ | ¬(z.im = 0 ∧ z.re ≤ -ms.a (N + j))} := by
      intro h
      have hle : ms.a N ≤ ms.a (N + j) := ms.strictMono.monotone (Nat.le_add_right N j)
      exact hr_sub hw ⟨h.1, by linarith [h.2]⟩
    exact ((modeTermL_analyticOnNhd (ms.a (N + j)) w hmem).differentiableAt).differentiableWithinAt
  have htail_diff : DifferentiableOn ℂ (fun w => ∑' k : ℕ, modeTermL (ms.a (N + (K + k))) w)
      (Metric.ball z₀ r) :=
    differentiableOn_tsum_of_summable_norm hu (fun k => hterm_diff (K + k))
      Metric.isOpen_ball htail_bound
  have hfin_diff : DifferentiableOn ℂ
      (fun w => ∑ k ∈ Finset.range K, modeTermL (ms.a (N + k)) w) (Metric.ball z₀ r) :=
    DifferentiableOn.fun_sum fun k _ => hterm_diff k
  have hsum_eq : ∀ w ∈ Metric.ball z₀ r,
      (∑' k : ℕ, modeTermL (ms.a (N + k)) w) =
        (∑ k ∈ Finset.range K, modeTermL (ms.a (N + k)) w) +
          ∑' k : ℕ, modeTermL (ms.a (N + (K + k))) w := by
    intro w hw
    have hsumm : Summable (fun k : ℕ => modeTermL (ms.a (N + k)) w) := by
      rw [← summable_nat_add_iff K]
      refine Summable.of_norm_bounded hu fun k => ?_
      have hcomm : k + K = K + k := Nat.add_comm k K
      rw [hcomm]
      exact htail_bound k w hw
    rw [← hsumm.sum_add_tsum_nat_add K]
    congr 1; apply tsum_congr; intro k; congr 2; omega
  have htot_diff : DifferentiableOn ℂ (fun w => ∑' k : ℕ, modeTermL (ms.a (N + k)) w)
      (Metric.ball z₀ r) :=
    (hfin_diff.add htail_diff).congr hsum_eq
  exact (htot_diff.analyticOnNhd Metric.isOpen_ball) z₀ (Metric.mem_ball_self hr_pos)

private lemma modeSeries_summable_of_pos (ms : ModeSeq) {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => modeTermL (ms.a k) (x : ℂ)) := by
  have hp : Summable (fun n : ℕ => ((n : ℝ) ^ (3 : ℝ))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  have hu : Summable (fun k : ℕ => ms.c ^ (-(3 : ℝ) / 2) * ((k : ℝ) + 1) ^ (-(3 : ℝ))) := by
    refine ((hp.comp_injective Nat.succ_injective).congr fun k => ?_).mul_left _
    simp only [Function.comp, Nat.cast_succ]
    rw [Real.rpow_neg (by positivity)]
  refine Summable.of_norm_bounded hu fun k => ?_
  unfold modeTermL
  have hpos : 0 < x + ms.a k := by linarith [ms.a_pos k]
  have hne : (x : ℂ) + (ms.a k : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_add]; exact Complex.ofReal_ne_zero.mpr hpos.ne'
  rw [norm_cpow_neg_three_halves hne, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpos]
  have hge : ms.c * ((k : ℝ) + 1) ^ 2 ≤ x + ms.a k := by linarith [ms.quad k]
  calc (x + ms.a k) ^ (-(3 : ℝ) / 2)
      ≤ (ms.c * ((k : ℝ) + 1) ^ 2) ^ (-(3 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_nonpos (by have := ms.c_pos; positivity) hge (by norm_num)
    _ = ms.c ^ (-(3 : ℝ) / 2) * (((k : ℝ) + 1) ^ 2) ^ (-(3 : ℝ) / 2) :=
        Real.mul_rpow ms.c_pos.le (by positivity)
    _ = ms.c ^ (-(3 : ℝ) / 2) * ((k : ℝ) + 1) ^ (-(3 : ℝ)) := by
        congr 1
        rw [← Real.rpow_natCast ((k : ℝ) + 1) 2, ← Real.rpow_mul (by positivity)]
        norm_num

private lemma analyticOnNhd_eval_const_jet {N : ℕ} (R : MvPolynomial (Fin (N + 1)) ℂ)
    {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) :
    AnalyticOnNhd ℂ (fun z => MvPolynomial.eval (fun j : Fin (N + 1) => iteratedDeriv j.val f z) R) U := by
  intro z hz
  induction R using MvPolynomial.induction_on with
  | C c => simpa using analyticAt_const
  | add A B hA hB =>
    simp only [map_add]
    exact hA.add hB
  | mul_X A j hA =>
    have hjet : AnalyticAt ℂ (iteratedDeriv j.val f) z := by
      rw [iteratedDeriv_eq_iterate]
      exact (hf.iterated_deriv j.val) z hz
    simp only [map_mul, MvPolynomial.eval_X]
    exact hA.mul hjet

/-- **Two-Step Slit-Domain Branch-Flipping Lemma**:
If a constant-coefficient ODE `R` vanishes on `modeSeriesFlipped ms F` on `(0, ∞)`,
then it also vanishes on `modeSeriesFlipped ms (insert m F)` on `(0, ∞)` for every `m ∉ F`. -/
private lemma modeSeriesFlipped_step (ms : ModeSeq) {N : ℕ} (R : MvPolynomial (Fin (N + 1)) ℂ)
    (F : Finset ℕ) (m : ℕ) (hm : m ∉ F)
    (hF : ∀ x : ℝ, 0 < x →
      MvPolynomial.eval
        (fun j : Fin (N + 1) => iteratedDeriv j.val (modeSeriesFlipped ms F) (x : ℂ)) R = 0) :
    ∀ x : ℝ, 0 < x →
      MvPolynomial.eval
        (fun j : Fin (N + 1) => iteratedDeriv j.val (modeSeriesFlipped ms (insert m F)) (x : ℂ)) R = 0 := by
  -- Define the common analytic background R_bg on Ω_m = slitDomain (-ms.a (m+1)) (image (-ms.a) (range m))
  let signF : ℕ → ℂ := fun k => if k ∈ F then -1 else 1
  let Rbg : ℂ → ℂ := fun z =>
    (∑ k ∈ Finset.range m, signF k * modeTermU (ms.a k) z) +
      (∑' k : ℕ, modeTermL (ms.a (m + 1 + k)) z) -
      2 * ∑ k ∈ F.filter (fun k => m < k), modeTermL (ms.a k) z
  let S_A : Finset ℝ := (Finset.range m).image (fun k => -ms.a k)
  let S_B : Finset ℝ := (Finset.range (m + 1)).image (fun k => -ms.a k)
  let ΩA : Set ℂ := slitDomain (-ms.a m) S_A
  let ΩB : Set ℂ := slitDomain (-ms.a (m + 1)) S_B
  have hΩA_open : IsOpen ΩA := isOpen_slitDomain _ _
  have hΩB_open : IsOpen ΩB := isOpen_slitDomain _ _
  have hΩA_conn : IsPreconnected ΩA := by
    refine isPreconnected_slitDomain (-ms.a m) S_A (half_pos ms.δ_pos) fun s hs => ?_
    rcases Finset.mem_image.mp hs with ⟨k, hk, rfl⟩
    have hlt : k < m := Finset.mem_range.mp hk
    linarith [ms.le_add_mul k m hlt, ms.δ_pos]
  have hΩB_conn : IsPreconnected ΩB := by
    refine isPreconnected_slitDomain (-ms.a (m + 1)) S_B (half_pos ms.δ_pos) fun s hs => ?_
    rcases Finset.mem_image.mp hs with ⟨k, hk, rfl⟩
    have hlt : k < m + 1 := Finset.mem_range.mp hk
    linarith [ms.le_add_mul k (m + 1) hlt, ms.δ_pos]
  -- Rbg is analytic on both ΩA and ΩB
  have hRbg_ana : ∀ M : ℝ, ∀ S : Finset ℝ,
      -ms.a (m + 1) ≤ M →
      (∀ k < m, -ms.a k ∈ S) →
      AnalyticOnNhd ℂ Rbg (slitDomain M S) := by
    intro M S hM_le hS
    -- Actually, we just need: z ∈ slitDomain M S → z ∉ (-∞, -ms.a (m+1)]!
    -- Since -ms.a (m+1) ≤ M, z.re ≤ -ms.a (m+1) → z.re ≤ M!
    have h1 : AnalyticOnNhd ℂ (fun z => ∑ k ∈ Finset.range m, signF k * modeTermU (ms.a k) z)
        (slitDomain M S) := by
      intro z hz
      have hterm : ∀ k ∈ Finset.range m, AnalyticAt ℂ (fun w => signF k * modeTermU (ms.a k) w) z := by
        intro k hk
        exact analyticAt_const.mul
          (modeTermU_analyticOnNhd (ms.a k) z (hz.2 (-ms.a k) (hS k (Finset.mem_range.mp hk))))
      exact Finset.analyticAt_fun_sum (Finset.range m) hterm
    have h2 : AnalyticOnNhd ℂ (fun z => ∑' k : ℕ, modeTermL (ms.a (m + 1 + k)) z)
        (slitDomain M S) := by
      intro z hz
      refine modeSeries_tail_analyticOnNhd ms (m + 1) z ?_
      intro h; exact hz.1 ⟨h.1, by linarith [h.2]⟩
    have h3 : AnalyticOnNhd ℂ
        (fun z => 2 * ∑ k ∈ F.filter (fun k => m < k), modeTermL (ms.a k) z)
        (slitDomain M S) := by
      intro z hz
      refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun k hk => ?_)
      have hmk : m + 1 ≤ k := (Finset.mem_filter.mp hk).2
      have hale : ms.a (m + 1) ≤ ms.a k := ms.strictMono.monotone hmk
      refine modeTermL_analyticOnNhd (ms.a k) z ?_
      intro h; exact hz.1 ⟨h.1, by linarith [h.2]⟩
    intro z hz
    exact ((h1 z hz).add (h2 z hz)).sub (h3 z hz)
  have hRbg_A : AnalyticOnNhd ℂ Rbg ΩA :=
    hRbg_ana (-ms.a m) S_A (by linarith [ms.sep m, ms.δ_pos]) fun k hk =>
      Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  have hRbg_B : AnalyticOnNhd ℂ Rbg ΩB :=
    hRbg_ana (-ms.a (m + 1)) S_B le_rfl fun k hk =>
      Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_lt hk), rfl⟩
  let fA : ℂ → ℂ := fun z => modeTermL (ms.a m) z + Rbg z
  let fB : ℂ → ℂ := fun z => -modeTermU (ms.a m) z + Rbg z
  have hfA_ana : AnalyticOnNhd ℂ fA ΩA := by
    intro z hz
    exact (modeTermL_analyticOnNhd (ms.a m) z hz.1).add (hRbg_A z hz)
  have hfB_ana : AnalyticOnNhd ℂ fB ΩB := by
    intro z hz
    have hmS : -ms.a m ∈ S_B := Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (Nat.lt_succ_self m), rfl⟩
    exact (modeTermU_analyticOnNhd (ms.a m) z (hz.2 (-ms.a m) hmS)).neg.add (hRbg_B z hz)
  -- On (0, ∞), fA = modeSeriesFlipped ms F and fB = modeSeriesFlipped ms (insert m F)
  have hpos_mem_A : ∀ x : ℝ, 0 < x → (x : ℂ) ∈ ΩA := by
    intro x hx
    refine ⟨?_, fun s hs => ?_⟩
    · simp only [Complex.ofReal_im, Complex.ofReal_re, true_and, not_le]
      linarith [ms.a_pos m]
    · rcases Finset.mem_image.mp hs with ⟨k, _, rfl⟩
      simp only [Complex.ofReal_re, Complex.ofReal_im, le_refl, and_true]
      linarith [ms.a_pos k]
  have hpos_mem_B : ∀ x : ℝ, 0 < x → (x : ℂ) ∈ ΩB := by
    intro x hx
    refine ⟨?_, fun s hs => ?_⟩
    · simp only [Complex.ofReal_im, Complex.ofReal_re, true_and, not_le]
      linarith [ms.a_pos (m + 1)]
    · rcases Finset.mem_image.mp hs with ⟨k, _, rfl⟩
      simp only [Complex.ofReal_re, Complex.ofReal_im, le_refl, and_true]
      linarith [ms.a_pos k]
  have hsplit_pos : ∀ x : ℝ, 0 < x →
      modeSeriesFlipped ms F (x : ℂ) = fA (x : ℂ) ∧
        modeSeriesFlipped ms (insert m F) (x : ℂ) = fB (x : ℂ) := by
    intro x hx
    have hsumm := modeSeries_summable_of_pos ms hx
    have htsum_split : modeSeries ms (x : ℂ) =
        (∑ k ∈ Finset.range m, modeTermL (ms.a k) (x : ℂ)) +
          modeTermL (ms.a m) (x : ℂ) +
          ∑' k : ℕ, modeTermL (ms.a (m + 1 + k)) (x : ℂ) := by
      unfold modeSeries
      rw [← hsumm.sum_add_tsum_nat_add (m + 1), Finset.sum_range_succ]
      congr 1; apply tsum_congr; intro k; congr 2; omega
    have hU_eq : ∀ k ∈ Finset.range m, modeTermU (ms.a k) (x : ℂ) = modeTermL (ms.a k) (x : ℂ) := by
      intro k _; exact modeTermU_eq_modeTermL_of_pos (ms.a k) (by linarith [ms.a_pos k])
    have hU_m : modeTermU (ms.a m) (x : ℂ) = modeTermL (ms.a m) (x : ℂ) :=
      modeTermU_eq_modeTermL_of_pos (ms.a m) (by linarith [ms.a_pos m])
    have hF_split : ∑ k ∈ F, modeTermL (ms.a k) (x : ℂ) =
        (∑ k ∈ F.filter (fun k => k < m), modeTermL (ms.a k) (x : ℂ)) +
          ∑ k ∈ F.filter (fun k => m < k), modeTermL (ms.a k) (x : ℂ) := by
      have hdisj : Disjoint (F.filter (fun k => k < m)) (F.filter (fun k => m < k)) := by
        rw [Finset.disjoint_filter]; intro k _ h1 h2; omega
      rw [← Finset.sum_union hdisj]
      congr 1; ext k
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hk
        have hne : k ≠ m := fun h => hm (h ▸ hk)
        rcases lt_or_gt_of_ne hne with h | h
        · exact Or.inl ⟨hk, h⟩
        · exact Or.inr ⟨hk, h⟩
      · rintro (⟨hk, _⟩ | ⟨hk, _⟩) <;> exact hk
    have hrange_diff :
        (∑ k ∈ Finset.range m, modeTermL (ms.a k) (x : ℂ)) -
          2 * ∑ k ∈ F.filter (fun k => k < m), modeTermL (ms.a k) (x : ℂ) =
        ∑ k ∈ Finset.range m, signF k * modeTermU (ms.a k) (x : ℂ) := by
      have hsub_sum : ∑ k ∈ F.filter (fun k => k < m), modeTermL (ms.a k) (x : ℂ) =
          ∑ k ∈ Finset.range m, if k ∈ F then modeTermL (ms.a k) (x : ℂ) else 0 := by
        rw [← Finset.sum_filter]
        congr 1; ext k; simp [and_comm]
      rw [hsub_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hU_eq k hk]
      by_cases hkF : k ∈ F
      · simp [signF, hkF]; ring
      · simp [signF, hkF]
    have hA_eq : modeSeriesFlipped ms F (x : ℂ) = fA (x : ℂ) := by
      unfold modeSeriesFlipped
      dsimp only [fA, Rbg]
      rw [htsum_split, hF_split, ← hrange_diff]
      ring
    have hB_eq : modeSeriesFlipped ms (insert m F) (x : ℂ) = fB (x : ℂ) := by
      unfold modeSeriesFlipped
      rw [Finset.sum_insert hm]
      have : modeSeries ms (x : ℂ) - 2 * (modeTermL (ms.a m) (x : ℂ) + ∑ k ∈ F, modeTermL (ms.a k) (x : ℂ)) =
          modeSeriesFlipped ms F (x : ℂ) - 2 * modeTermL (ms.a m) (x : ℂ) := by
        unfold modeSeriesFlipped; ring
      rw [this, hA_eq]
      dsimp only [fA, fB]
      rw [hU_m]; ring
    exact ⟨hA_eq, hB_eq⟩
  -- Step 1: R(J_N fA) vanishes on (0, ∞), hence on all of ΩA by identity theorem
  let gA : ℂ → ℂ := fun z => MvPolynomial.eval (fun j : Fin (N + 1) => iteratedDeriv j.val fA z) R
  let gB : ℂ → ℂ := fun z => MvPolynomial.eval (fun j : Fin (N + 1) => iteratedDeriv j.val fB z) R
  have hgA_ana : AnalyticOnNhd ℂ gA ΩA := analyticOnNhd_eval_const_jet R hfA_ana
  have hgB_ana : AnalyticOnNhd ℂ gB ΩB := analyticOnNhd_eval_const_jet R hfB_ana
  have hgA_pos : ∀ x : ℝ, 0 < x → gA (x : ℂ) = 0 := by
    intro x hx
    have heq_nhds : fA =ᶠ[𝓝 (x : ℂ)] modeSeriesFlipped ms F := by
      have hopen_re : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
      have hre_mem : {w : ℂ | 0 < w.re} ∈ 𝓝 (x : ℂ) := hopen_re.mem_nhds (by simpa using hx)
      -- Wait: fA and modeSeriesFlipped ms F agree on all w with 0 < w.re!
      -- Even simpler: they are both analytic on {w | 0 < w.re}, and agree on (0, ∞)!
      have hsubA : {w : ℂ | 0 < w.re} ⊆ ΩA := by
        intro w (hw : 0 < w.re)
        refine ⟨fun h => by linarith [h.2, ms.a_pos m], fun s hs h => ?_⟩
        rcases Finset.mem_image.mp hs with ⟨k, _, rfl⟩
        linarith [h.1, ms.a_pos k]
      have hMS_ana : AnalyticOnNhd ℂ (modeSeriesFlipped ms F) {w : ℂ | 0 < w.re} := by
        intro w (hw : 0 < w.re)
        have hms0 : AnalyticAt ℂ (modeSeries ms) w := by
          have h0 : modeSeries ms = fun z => ∑' k : ℕ, modeTermL (ms.a (0 + k)) z := by
            ext z; simp [modeSeries]
          rw [h0]
          exact modeSeries_tail_analyticOnNhd ms 0 w (fun h => by linarith [h.2, ms.a_pos 0])
        have hfin : AnalyticAt ℂ (fun z => 2 * ∑ k ∈ F, modeTermL (ms.a k) z) w :=
          analyticAt_const.mul (Finset.analyticAt_fun_sum F fun k _ =>
            modeTermL_analyticOnNhd (ms.a k) w (fun h => by linarith [h.2, ms.a_pos k]))
        exact hms0.sub hfin
      have hconn_re : IsPreconnected {w : ℂ | 0 < w.re} :=
        (convex_halfSpace_re_gt 0).isPreconnected
      have hdiff_ana : AnalyticOnNhd ℂ (fun w => fA w - modeSeriesFlipped ms F w) {w : ℂ | 0 < w.re} :=
        fun w hw => (hfA_ana w (hsubA hw)).sub (hMS_ana w hw)
      have hfreq : ∃ᶠ w in 𝓝[≠] ((1 : ℝ) : ℂ), fA w - modeSeriesFlipped ms F w = 0 := by
        rw [Filter.frequently_iff]
        intro s hs
        rw [mem_nhdsWithin] at hs
        obtain ⟨u, hu_open, hu1, hus⟩ := hs
        obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hu_open _ hu1
        refine ⟨((1 + r / 2 : ℝ) : ℂ), hus ⟨hr_sub ?_, ?_⟩, ?_⟩
        · rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs]
          have : (1 + r / 2) - 1 = r / 2 := by ring
          rw [this, abs_of_pos (half_pos hr_pos)]
          linarith
        · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro h0
          have := congrArg Complex.re h0
          simp at this
          linarith
        · have hpos : (0 : ℝ) < 1 + r / 2 := by linarith
          rw [(hsplit_pos (1 + r / 2) hpos).1, sub_self]
      have hzero_re : Set.EqOn (fun w => fA w - modeSeriesFlipped ms F w) 0 {w : ℂ | 0 < w.re} :=
        hdiff_ana.eqOn_zero_of_preconnected_of_frequently_eq_zero hconn_re (by simp) hfreq
      filter_upwards [hre_mem] with w hw
      exact sub_eq_zero.mp (hzero_re hw)
    have hderiv_eq : ∀ j : ℕ, iteratedDeriv j fA (x : ℂ) =
        iteratedDeriv j (modeSeriesFlipped ms F) (x : ℂ) :=
      fun j => heq_nhds.iteratedDeriv_eq j
    dsimp only [gA]
    simp_rw [hderiv_eq]
    exact hF x hx
  have hgA_zero : Set.EqOn gA 0 ΩA := by
    refine hgA_ana.eqOn_zero_of_preconnected_of_frequently_eq_zero hΩA_conn
      (hpos_mem_A 1 zero_lt_one) ?_
    rw [Filter.frequently_iff]
    intro s hs
    rw [mem_nhdsWithin] at hs
    obtain ⟨u, hu_open, hu1, hus⟩ := hs
    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hu_open _ hu1
    refine ⟨((1 + r / 2 : ℝ) : ℂ), hus ⟨hr_sub ?_, ?_⟩, hgA_pos (1 + r / 2) (by linarith)⟩
    · rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]
      have : (1 + r / 2) - 1 = r / 2 := by ring
      rw [this, abs_of_pos (half_pos hr_pos)]
      linarith
    · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
  -- Step 2: On the upper-left quadrant QUL = {z | z.re < -ms.a m ∧ 0 < z.im} ∩ ΩA ∩ ΩB,
  -- fB = fA, so gB = gA = 0 on a neighborhood of z_UL = (-ms.a m - δ/2) + I!
  let zUL : ℂ := ((-ms.a m - ms.δ / 2 : ℝ) : ℂ) + Complex.I
  have hzUL_A : zUL ∈ ΩA := by
    refine ⟨?_, fun s hs => ?_⟩
    · simp [zUL]
    · rcases Finset.mem_image.mp hs with ⟨k, hk, rfl⟩
      simp only [zUL, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero, Complex.add_im,
        Complex.ofReal_im, Complex.I_im, zero_add, zero_le_one, and_true]
      linarith [ms.le_add_mul k m (Finset.mem_range.mp hk), ms.δ_pos]
  have hzUL_B : zUL ∈ ΩB := by
    refine ⟨?_, fun s hs => ?_⟩
    · simp [zUL]
    · rcases Finset.mem_image.mp hs with ⟨k, hk, rfl⟩
      simp only [zUL, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero, Complex.add_im,
        Complex.ofReal_im, Complex.I_im, zero_add, zero_le_one, and_true]
      have hle : ms.a k ≤ ms.a m := ms.strictMono.monotone (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
      linarith [ms.δ_pos]
  have hfB_eq_fA_nhds : fB =ᶠ[𝓝 zUL] fA := by
    let QUL : Set ℂ := {w : ℂ | w.re < -ms.a m ∧ 0 < w.im}
    have hQUL_open : IsOpen QUL :=
      (isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt continuous_const Complex.continuous_im)
    have hzUL_QUL : zUL ∈ QUL := by
      refine ⟨?_, ?_⟩ <;> simp [zUL, ms.δ_pos]
    filter_upwards [hQUL_open.mem_nhds hzUL_QUL] with w hw
    dsimp only [fA, fB]
    rw [modeTermU_eq_neg_modeTermL_of_QUL (ms.a m) hw.1 hw.2, neg_neg]
  have hgB_eq_zero_nhds : ∀ᶠ w in 𝓝 zUL, gB w = 0 := by
    have hQUL_open : IsOpen {w : ℂ | w.re < -ms.a m ∧ 0 < w.im} :=
      (isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt continuous_const Complex.continuous_im)
    have hzUL_QUL : zUL ∈ {w : ℂ | w.re < -ms.a m ∧ 0 < w.im} := by
      refine ⟨?_, ?_⟩ <;> simp [zUL, ms.δ_pos]
    filter_upwards [hΩA_open.mem_nhds hzUL_A, hQUL_open.mem_nhds hzUL_QUL] with w hwA hwQ
    have hfB_eq_w : fB =ᶠ[𝓝 w] fA := by
      filter_upwards [hQUL_open.mem_nhds hwQ] with u hu
      dsimp only [fA, fB]
      rw [modeTermU_eq_neg_modeTermL_of_QUL (ms.a m) hu.1 hu.2, neg_neg]
    have hd : ∀ j : ℕ, iteratedDeriv j fB w = iteratedDeriv j fA w :=
      fun j => hfB_eq_w.iteratedDeriv_eq j
    dsimp only [gB]
    simp_rw [hd]
    exact hgA_zero hwA
  have hgB_zero : Set.EqOn gB 0 ΩB := by
    refine hgB_ana.eqOn_zero_of_preconnected_of_frequently_eq_zero hΩB_conn hzUL_B ?_
    exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds hgB_eq_zero_nhds).frequently
  -- Step 3: Restrict gB = 0 back to (0, ∞) ⊂ ΩB!
  intro x hx
  have heq_nhds : fB =ᶠ[𝓝 (x : ℂ)] modeSeriesFlipped ms (insert m F) := by
    have hopen_re : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hre_mem : {w : ℂ | 0 < w.re} ∈ 𝓝 (x : ℂ) := hopen_re.mem_nhds (by simpa using hx)
    have hsubB : {w : ℂ | 0 < w.re} ⊆ ΩB := by
      intro w (hw : 0 < w.re)
      refine ⟨fun h => by linarith [h.2, ms.a_pos (m + 1)], fun s hs h => ?_⟩
      rcases Finset.mem_image.mp hs with ⟨k, _, rfl⟩
      linarith [h.1, ms.a_pos k]
    have hMS_ana : AnalyticOnNhd ℂ (modeSeriesFlipped ms (insert m F)) {w : ℂ | 0 < w.re} := by
      intro w (hw : 0 < w.re)
      have hms0 : AnalyticAt ℂ (modeSeries ms) w := by
        have h0 : modeSeries ms = fun z => ∑' k : ℕ, modeTermL (ms.a (0 + k)) z := by
          ext z; simp [modeSeries]
        rw [h0]
        exact modeSeries_tail_analyticOnNhd ms 0 w (fun h => by linarith [h.2, ms.a_pos 0])
      have hfin : AnalyticAt ℂ (fun z => 2 * ∑ k ∈ insert m F, modeTermL (ms.a k) z) w :=
        analyticAt_const.mul (Finset.analyticAt_fun_sum (insert m F) fun k _ =>
          modeTermL_analyticOnNhd (ms.a k) w (fun h => by linarith [h.2, ms.a_pos k]))
      exact hms0.sub hfin
    have hconn_re : IsPreconnected {w : ℂ | 0 < w.re} :=
      (convex_halfSpace_re_gt 0).isPreconnected
    have hdiff_ana : AnalyticOnNhd ℂ
        (fun w => fB w - modeSeriesFlipped ms (insert m F) w) {w : ℂ | 0 < w.re} :=
      fun w hw => (hfB_ana w (hsubB hw)).sub (hMS_ana w hw)
    have hfreq : ∃ᶠ w in 𝓝[≠] ((1 : ℝ) : ℂ), fB w - modeSeriesFlipped ms (insert m F) w = 0 := by
      rw [Filter.frequently_iff]
      intro s hs
      rw [mem_nhdsWithin] at hs
      obtain ⟨u, hu_open, hu1, hus⟩ := hs
      obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hu_open _ hu1
      refine ⟨((1 + r / 2 : ℝ) : ℂ), hus ⟨hr_sub ?_, ?_⟩, ?_⟩
      · rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs]
        have : (1 + r / 2) - 1 = r / 2 := by ring
        rw [this, abs_of_pos (half_pos hr_pos)]
        linarith
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h0
        have := congrArg Complex.re h0
        simp at this
        linarith
      · have hpos : (0 : ℝ) < 1 + r / 2 := by linarith
        rw [(hsplit_pos (1 + r / 2) hpos).2, sub_self]
    have hzero_re : Set.EqOn (fun w => fB w - modeSeriesFlipped ms (insert m F) w) 0
        {w : ℂ | 0 < w.re} :=
      hdiff_ana.eqOn_zero_of_preconnected_of_frequently_eq_zero hconn_re (by simp) hfreq
    filter_upwards [hre_mem] with w hw
    exact sub_eq_zero.mp (hzero_re hw)
  have hderiv_eq : ∀ j : ℕ, iteratedDeriv j (modeSeriesFlipped ms (insert m F)) (x : ℂ) =
      iteratedDeriv j fB (x : ℂ) :=
    fun j => (heq_nhds.iteratedDeriv_eq j).symm
  simp_rw [hderiv_eq]
  exact hgB_zero (hpos_mem_B x hx)

private lemma modeSeriesFlipped_all (ms : ModeSeq) {N : ℕ} (R : MvPolynomial (Fin (N + 1)) ℂ)
    (hR : ∀ x : ℝ, 0 < x →
      MvPolynomial.eval (fun j : Fin (N + 1) => iteratedDeriv j.val (modeSeries ms) (x : ℂ)) R = 0) :
    ∀ F : Finset ℕ, ∀ x : ℝ, 0 < x →
      MvPolynomial.eval
        (fun j : Fin (N + 1) => iteratedDeriv j.val (modeSeriesFlipped ms F) (x : ℂ)) R = 0 := by
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro x hx
    have heq : modeSeriesFlipped ms ∅ = modeSeries ms := by
      ext z; simp [modeSeriesFlipped]
    rw [heq]
    exact hR x hx
  | @insert m F hm ih =>
    exact modeSeriesFlipped_step ms R F m hm ih

/-! #### Finite-Difference Vandermonde Vanishing & Mode-Series Transcendence -/

private lemma iteratedDeriv_modeTermL (b : ℝ) (j : ℕ) {z : ℂ} (hz : ¬(z.im = 0 ∧ z.re ≤ -b)) :
    iteratedDeriv j (modeTermL b) z =
      (∏ l ∈ Finset.range j, (-(3 : ℂ) / 2 - (l : ℂ))) *
        (z + (b : ℂ)) ^ (-(3 : ℂ) / 2 - (j : ℂ)) := by
  have hgen : ∀ (α : ℂ) (k : ℕ), ∀ w : ℂ, ¬(w.im = 0 ∧ w.re ≤ -b) →
      iteratedDeriv k (fun u : ℂ => (u + (b : ℂ)) ^ α) w =
        (∏ l ∈ Finset.range k, (α - (l : ℂ))) * (w + (b : ℂ)) ^ (α - (k : ℂ)) := by
    intro α k
    induction k with
    | zero =>
      intro w _
      simp
    | succ k ih =>
      intro w hw
      have hopen : IsOpen {u : ℂ | ¬(u.im = 0 ∧ u.re ≤ -b)} := by
        have hc : IsClosed {u : ℂ | u.im = 0 ∧ u.re ≤ -b} :=
          (isClosed_eq Complex.continuous_im continuous_const).inter
            (isClosed_le Complex.continuous_re continuous_const)
        exact hc.isOpen_compl
      have hev : iteratedDeriv k (fun u : ℂ => (u + (b : ℂ)) ^ α) =ᶠ[𝓝 w]
          fun u : ℂ => (∏ l ∈ Finset.range k, (α - (l : ℂ))) * (u + (b : ℂ)) ^ (α - (k : ℂ)) := by
        filter_upwards [hopen.mem_nhds hw] with u hu
        exact ih u hu
      rw [iteratedDeriv_succ, hev.deriv_eq]
      have hslit : w + (b : ℂ) ∈ Complex.slitPlane := by
        rw [Complex.mem_slitPlane_iff]
        by_cases him : w.im = 0
        · left
          have hgt : -b < w.re := lt_of_not_ge fun hle => hw ⟨him, hle⟩
          simp; linarith
        · right; simpa using him
      have hadd : HasDerivAt (fun u : ℂ => u + (b : ℂ)) 1 w := by
        simpa using (hasDerivAt_id w).add_const (b : ℂ)
      have hcpow : HasDerivAt (fun u : ℂ => (u + (b : ℂ)) ^ (α - (k : ℂ)))
          ((α - (k : ℂ)) * (w + (b : ℂ)) ^ (α - (k : ℂ) - 1) * 1) w :=
        hadd.cpow_const hslit
      have hmul := hcpow.const_mul (∏ l ∈ Finset.range k, (α - (l : ℂ)))
      rw [hmul.deriv, Finset.prod_range_succ]
      have hexp : α - (k : ℂ) - 1 = α - ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [hexp]
      ring
  exact hgen (-(3 : ℂ) / 2) j z hz

private lemma modeJump_spans (ms : ModeSeq) (r M : ℕ) :
    let v : ℕ → Fin (r + 1) → ℂ := fun k j => -2 * iteratedDeriv j.val (modeTermL (ms.a k)) 1
    ∀ y : Fin (r + 1) → ℂ, ∃ α : Fin (r + 1) → ℂ,
      ∑ i : Fin (r + 1), α i • v (M + i.val) = y := by
  intro v y
  let c : Fin (r + 1) → ℂ := fun j => -2 * ∏ l ∈ Finset.range j.val, (-(3 : ℂ) / 2 - (l : ℂ))
  let d : Fin (r + 1) → ℂ := fun i => ((1 : ℂ) + (ms.a (M + i.val) : ℂ)) ^ (-(3 : ℂ) / 2)
  let w : Fin (r + 1) → ℂ := fun i => ((1 : ℂ) + (ms.a (M + i.val) : ℂ))⁻¹
  let A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.of fun i j => v (M + i.val) j
  have hA_eq : A = Matrix.diagonal d * Matrix.vandermonde w * Matrix.diagonal c := by
    ext i j
    simp only [A, Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.vandermonde_apply, v, c, d, w]
    have h1 : ¬((1 : ℂ).im = 0 ∧ (1 : ℂ).re ≤ -ms.a (M + i.val)) := by
      simp; linarith [ms.a_pos (M + i.val)]
    rw [iteratedDeriv_modeTermL (ms.a (M + i.val)) j.val h1]
    have hpos : (0 : ℝ) < 1 + ms.a (M + i.val) := by linarith [ms.a_pos (M + i.val)]
    have hne : (1 : ℂ) + (ms.a (M + i.val) : ℂ) ≠ 0 := by
      have : (1 : ℂ) + (ms.a (M + i.val) : ℂ) = ((1 + ms.a (M + i.val) : ℝ) : ℂ) := by push_cast; rfl
      rw [this]; exact Complex.ofReal_ne_zero.mpr hpos.ne'
    have hcpow : ((1 : ℂ) + (ms.a (M + i.val) : ℂ)) ^ (-(3 : ℂ) / 2 - (j.val : ℂ)) =
        ((1 : ℂ) + (ms.a (M + i.val) : ℂ)) ^ (-(3 : ℂ) / 2) *
          (((1 : ℂ) + (ms.a (M + i.val) : ℂ))⁻¹) ^ j.val := by
      rw [sub_eq_add_neg, Complex.cpow_add _ _ hne, Complex.cpow_neg, Complex.cpow_natCast, inv_pow]
    rw [hcpow]
    ring
  have hc_ne : ∀ j : Fin (r + 1), c j ≠ 0 := by
    intro j
    refine mul_ne_zero (by norm_num) (Finset.prod_ne_zero_iff.mpr fun l _ => ?_)
    intro h0
    have hre := congrArg Complex.re h0
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.neg_re, Complex.re_ofNat,
      Complex.natCast_re, Complex.zero_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) l]
  have hd_ne : ∀ i : Fin (r + 1), d i ≠ 0 := by
    intro i
    have hpos : (0 : ℝ) < 1 + ms.a (M + i.val) := by linarith [ms.a_pos (M + i.val)]
    have hne : (1 : ℂ) + (ms.a (M + i.val) : ℂ) ≠ 0 := by
      have : (1 : ℂ) + (ms.a (M + i.val) : ℂ) = ((1 + ms.a (M + i.val) : ℝ) : ℂ) := by push_cast; rfl
      rw [this]; exact Complex.ofReal_ne_zero.mpr hpos.ne'
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hne)
  have hw_inj : Function.Injective w := by
    intro i₁ i₂ h
    have h1 : (1 : ℂ) + (ms.a (M + i₁.val) : ℂ) = (1 : ℂ) + (ms.a (M + i₂.val) : ℂ) :=
      inv_injective h
    have h2 : ms.a (M + i₁.val) = ms.a (M + i₂.val) := by
      have hre := congrArg Complex.re h1
      simp at hre
      exact hre
    have h3 : M + i₁.val = M + i₂.val := ms.strictMono.injective h2
    exact Fin.ext (Nat.add_left_cancel h3)
  have hdet_ne : A.det ≠ 0 := by
    rw [hA_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
      Matrix.det_vandermonde]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => hd_ne i
    · refine Finset.prod_ne_zero_iff.mpr fun i _ =>
        Finset.prod_ne_zero_iff.mpr fun j hj => ?_
      rw [Finset.mem_Ioi] at hj
      exact sub_ne_zero.mpr fun h => (ne_of_gt hj) (hw_inj h)
    · exact Finset.prod_ne_zero_iff.mpr fun j _ => hc_ne j
  refine ⟨Matrix.vecMul y A⁻¹, ?_⟩
  ext j
  have hmul : Matrix.vecMul (Matrix.vecMul y A⁻¹) A = y := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet_ne),
      Matrix.vecMul_one]
  have hj := congrFun hmul j
  simpa [Matrix.vecMul, dotProduct, A, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hj

private def shiftMvPoly {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ℂ) (v : Fin (r + 1) → ℂ) :
    MvPolynomial (Fin (r + 1)) ℂ :=
  MvPolynomial.aeval (fun i => X i + C (v i)) Q

private lemma eval_shiftMvPoly {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ℂ)
    (v y : Fin (r + 1) → ℂ) :
    MvPolynomial.eval y (shiftMvPoly Q v) = MvPolynomial.eval (y + v) Q := by
  unfold shiftMvPoly
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add A B hA hB => rw [map_add, map_add, map_add, hA, hB]
  | mul_X A i hA =>
    rw [map_mul, map_mul, map_mul, hA]
    simp [Pi.add_apply]

private lemma totalDegree_pow_shift_sub {r : ℕ} (i : Fin (r + 1)) (c : ℂ) (k : ℕ) :
    ((X i + C c) ^ k - X i ^ k).totalDegree + 1 ≤ k ∨ (X i + C c) ^ k - X i ^ k = 0 := by
  by_cases hk : k = 0
  · exact Or.inr (by simp [hk])
  · left
    rw [add_pow, Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self,
      pow_zero, mul_one, add_sub_cancel_right]
    have hle : (∑ l ∈ Finset.range k,
        (X i : MvPolynomial (Fin (r + 1)) ℂ) ^ l * C c ^ (k - l) *
          (k.choose l : MvPolynomial (Fin (r + 1)) ℂ)).totalDegree ≤ k - 1 := by
      refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun l hl => ?_)
      have hlt : l < k := Finset.mem_range.mp hl
      have h1 : ((X i : MvPolynomial (Fin (r + 1)) ℂ) ^ l * C c ^ (k - l) *
            (k.choose l : MvPolynomial (Fin (r + 1)) ℂ)).totalDegree ≤
          ((X i : MvPolynomial (Fin (r + 1)) ℂ) ^ l).totalDegree +
            (C c ^ (k - l) * (k.choose l : MvPolynomial (Fin (r + 1)) ℂ)).totalDegree := by
        rw [mul_assoc]; exact MvPolynomial.totalDegree_mul _ _
      have h2 : ((X i : MvPolynomial (Fin (r + 1)) ℂ) ^ l).totalDegree ≤ l := by
        calc ((X i : MvPolynomial (Fin (r + 1)) ℂ) ^ l).totalDegree
            ≤ l * (X i : MvPolynomial (Fin (r + 1)) ℂ).totalDegree := MvPolynomial.totalDegree_pow _ _
          _ ≤ l * 1 := by simp [MvPolynomial.totalDegree_X]
          _ = l := mul_one l
      have h3 : (C c ^ (k - l) * (k.choose l : MvPolynomial (Fin (r + 1)) ℂ)).totalDegree = 0 := by
        have : C c ^ (k - l) * (k.choose l : MvPolynomial (Fin (r + 1)) ℂ) =
            C (c ^ (k - l) * (k.choose l : ℂ)) := by simp [map_mul, map_pow]
        rw [this, MvPolynomial.totalDegree_C]
      omega
    omega

private lemma totalDegree_shiftMvPoly_sub_le {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ℂ)
    (v : Fin (r + 1) → ℂ) {D : ℕ} (hQ : Q.totalDegree ≤ D + 1) :
    (shiftMvPoly Q v - Q).totalDegree ≤ D := by
  have hmon : ∀ (m : Fin (r + 1) →₀ ℕ) (a : ℂ), m.sum (fun _ e => e) ≤ D + 1 →
      (shiftMvPoly (monomial m a) v - monomial m a).totalDegree ≤ D := by
    intro m a hm
    have heq_mon : monomial m a = C a * ∏ i : Fin (r + 1), X i ^ (m i) := by
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    have hprod : ∀ s : Finset (Fin (r + 1)),
        ((∏ i ∈ s, (X i + C (v i)) ^ (m i)) - ∏ i ∈ s, X i ^ (m i)).totalDegree + 1 ≤
          ∑ i ∈ s, m i ∨
        (∏ i ∈ s, (X i + C (v i)) ^ (m i)) - ∏ i ∈ s, X i ^ (m i) = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact Or.inr (by simp)
      | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
        set A : MvPolynomial (Fin (r + 1)) ℂ := X i ^ (m i)
        set B : MvPolynomial (Fin (r + 1)) ℂ := ∏ j ∈ s, X j ^ (m j)
        set RA : MvPolynomial (Fin (r + 1)) ℂ := (X i + C (v i)) ^ (m i) - A
        set RB : MvPolynomial (Fin (r + 1)) ℂ := (∏ j ∈ s, (X j + C (v j)) ^ (m j)) - B
        have hdecomp : (X i + C (v i)) ^ (m i) * (∏ j ∈ s, (X j + C (v j)) ^ (m j)) - A * B =
            A * RB + RA * B + RA * RB := by
          dsimp only [RA, RB]; ring
        rw [hdecomp]
        have hdegA : A.totalDegree ≤ m i := by
          calc A.totalDegree ≤ m i * (X i : MvPolynomial (Fin (r + 1)) ℂ).totalDegree :=
                MvPolynomial.totalDegree_pow _ _
            _ = m i := by simp [MvPolynomial.totalDegree_X]
        have hdegB : B.totalDegree ≤ ∑ j ∈ s, m j := by
          calc B.totalDegree ≤ ∑ j ∈ s, (X j ^ (m j) : MvPolynomial (Fin (r + 1)) ℂ).totalDegree :=
                MvPolynomial.totalDegree_finsetProd _ _
            _ ≤ ∑ j ∈ s, m j := Finset.sum_le_sum fun j _ => by
                calc (X j ^ (m j) : MvPolynomial (Fin (r + 1)) ℂ).totalDegree
                    ≤ m j * (X j : MvPolynomial (Fin (r + 1)) ℂ).totalDegree :=
                      MvPolynomial.totalDegree_pow _ _
                  _ = m j := by simp [MvPolynomial.totalDegree_X]
        have hRA : RA.totalDegree + 1 ≤ m i ∨ RA = 0 :=
          totalDegree_pow_shift_sub i (v i) (m i)
        by_cases hsum0 : m i + ∑ j ∈ s, m j = 0
        · right
          have hmi0 : m i = 0 := by omega
          have hs0 : ∀ j ∈ s, m j = 0 := fun j hj => by
            have := Finset.single_le_sum (f := fun j => m j) (fun _ _ => Nat.zero_le _) hj
            omega
          have hRA0 : RA = 0 := by simp [RA, A, hmi0]
          have hRB0 : RB = 0 := by
            dsimp only [RB, B]
            have h1 : ∏ j ∈ s, (X j + C (v j)) ^ (m j) = 1 :=
              Finset.prod_eq_one fun j hj => by simp [hs0 j hj]
            have h2 : ∏ j ∈ s, (X j : MvPolynomial (Fin (r + 1)) ℂ) ^ (m j) = 1 :=
              Finset.prod_eq_one fun j hj => by simp [hs0 j hj]
            rw [h1, h2, sub_self]
          simp [hRA0, hRB0]
        · left
          have h1 : (A * RB).totalDegree + 1 ≤ m i + ∑ j ∈ s, m j := by
            rcases ih with hRB | hRB0
            · have := MvPolynomial.totalDegree_mul A RB; omega
            · rw [hRB0, mul_zero, MvPolynomial.totalDegree_zero]; omega
          have h2 : (RA * B).totalDegree + 1 ≤ m i + ∑ j ∈ s, m j := by
            rcases hRA with hRA' | hRA0
            · have := MvPolynomial.totalDegree_mul RA B; omega
            · rw [hRA0, zero_mul, MvPolynomial.totalDegree_zero]; omega
          have h3 : (RA * RB).totalDegree + 1 ≤ m i + ∑ j ∈ s, m j := by
            rcases hRA with hRA' | hRA0
            · rcases ih with hRB' | hRB0
              · have := MvPolynomial.totalDegree_mul RA RB; omega
              · rw [hRB0, mul_zero, MvPolynomial.totalDegree_zero]; omega
            · rw [hRA0, zero_mul, MvPolynomial.totalDegree_zero]; omega
          have hadd1 := MvPolynomial.totalDegree_add (A * RB) (RA * B)
          have hadd2 := MvPolynomial.totalDegree_add (A * RB + RA * B) (RA * RB)
          omega
    rw [heq_mon]
    have hshift : shiftMvPoly (C a * ∏ i : Fin (r + 1), X i ^ (m i)) v =
        C a * ∏ i : Fin (r + 1), (X i + C (v i)) ^ (m i) := by
      simp [shiftMvPoly, map_mul, map_prod, map_pow]
    rw [hshift, ← mul_sub]
    have hmul := MvPolynomial.totalDegree_mul (C a)
      ((∏ i : Fin (r + 1), (X i + C (v i)) ^ (m i)) - ∏ i : Fin (r + 1), X i ^ (m i))
    rw [MvPolynomial.totalDegree_C, zero_add] at hmul
    have hmsum : ∑ i : Fin (r + 1), m i = m.sum (fun _ e => e) := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    rcases hprod Finset.univ with hdeg | h0
    · omega
    · rw [h0, mul_zero, MvPolynomial.totalDegree_zero]; exact Nat.zero_le D
  have hQ_eq : Q = ∑ m ∈ Q.support, monomial m (Q.coeff m) := Q.as_sum
  have hdiff_eq : shiftMvPoly Q v - Q =
      ∑ m ∈ Q.support, (shiftMvPoly (monomial m (Q.coeff m)) v - monomial m (Q.coeff m)) := by
    conv_lhs => rw [hQ_eq]
    unfold shiftMvPoly
    rw [map_sum, Finset.sum_sub_distrib]
  rw [hdiff_eq]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  refine hmon m (Q.coeff m) ?_
  exact (MvPolynomial.le_totalDegree hm).trans hQ

private lemma mvPoly_periodic_all_scalar {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ℂ)
    (v : Fin (r + 1) → ℂ)
    (hper : ∀ y : Fin (r + 1) → ℂ, MvPolynomial.eval (y + v) Q = MvPolynomial.eval y Q) :
    ∀ y : Fin (r + 1) → ℂ, ∀ t : ℂ, MvPolynomial.eval (y + t • v) Q = MvPolynomial.eval y Q := by
  intro y t
  let p : Polynomial ℂ :=
    MvPolynomial.aeval (fun i => Polynomial.C (y i) + Polynomial.C (v i) * Polynomial.X) Q -
      Polynomial.C (MvPolynomial.eval y Q)
  have hp_eval : ∀ s : ℂ, p.eval s = MvPolynomial.eval (y + s • v) Q - MvPolynomial.eval y Q := by
    intro s
    dsimp only [p]
    rw [Polynomial.eval_sub, Polynomial.eval_C]
    congr 1
    clear hper p
    induction Q using MvPolynomial.induction_on with
    | C c => simp
    | add A B hA hB => rw [map_add, Polynomial.eval_add, map_add, hA, hB]
    | mul_X A i hA =>
      rw [map_mul, Polynomial.eval_mul, map_mul, hA]
      simp only [MvPolynomial.aeval_X, MvPolynomial.eval_X, Polynomial.eval_add,
        Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      ring
  have hp_nat : ∀ n : ℕ, p.eval (n : ℂ) = 0 := by
    intro n
    rw [hp_eval, sub_eq_zero]
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep : y + ((n + 1 : ℕ) : ℂ) • v = (y + (n : ℂ) • v) + v := by
        ext i; simp [add_mul, add_assoc]
      rw [hstep, hper, ih]
  have hp_zero : p = 0 := by
    by_contra hp_ne
    have hfin : (Set.range (fun n : ℕ => (n : ℂ))).Finite := by
      refine (p.roots.toFinset.finite_toSet).subset ?_
      rintro _ ⟨n, rfl⟩
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp_ne).mpr (hp_nat n))
    exact (Set.infinite_range_of_injective Nat.cast_injective) hfin
  have := hp_eval t
  rw [hp_zero, Polynomial.eval_zero] at this
  exact sub_eq_zero.mp this.symm

private lemma finite_diff_vandermonde_vanish (ms : ModeSeq) {r : ℕ} :
    ∀ D : ℕ, ∀ (Q : MvPolynomial (Fin (r + 1)) ℂ), Q.totalDegree ≤ D →
      ∀ (y₀ : Fin (r + 1) → ℂ) (M : ℕ),
        (∀ F : Finset ℕ, (∀ k ∈ F, M ≤ k) → F.card ≤ D →
          MvPolynomial.eval
            (y₀ + ∑ k ∈ F, (fun j : Fin (r + 1) => -2 * iteratedDeriv j.val (modeTermL (ms.a k)) 1))
            Q = 0) →
        Q = 0 := by
  intro D
  induction D with
  | zero =>
    intro Q hQ y₀ M hvan
    have hdeg0 : Q.totalDegree = 0 := Nat.eq_zero_of_le_zero hQ
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hdeg0
    have h0 := hvan ∅ (fun _ h => absurd h (Finset.notMem_empty _)) (by simp)
    rw [hdeg0] at h0 ⊢
    simp only [MvPolynomial.eval_C] at h0
    rw [h0, map_zero]
  | succ D ih =>
    intro Q hQ y₀ M hvan
    let v : ℕ → Fin (r + 1) → ℂ := fun k j => -2 * iteratedDeriv j.val (modeTermL (ms.a k)) 1
    have hper_basis : ∀ i : Fin (r + 1), ∀ y : Fin (r + 1) → ℂ,
        MvPolynomial.eval (y + v (M + i.val)) Q = MvPolynomial.eval y Q := by
      intro i
      let Q' : MvPolynomial (Fin (r + 1)) ℂ := shiftMvPoly Q (v (M + i.val)) - Q
      have hQ'_deg : Q'.totalDegree ≤ D := totalDegree_shiftMvPoly_sub_le Q (v (M + i.val)) hQ
      have hQ'_zero : Q' = 0 := by
        refine ih Q' hQ'_deg y₀ (M + r + 1) fun F hFM hFcard => ?_
        have hnot : M + i.val ∉ F := by
          intro hmem
          have hge := hFM (M + i.val) hmem
          omega
        have h1 := hvan (insert (M + i.val) F)
          (fun k hk => by
            rcases Finset.mem_insert.mp hk with rfl | hkF
            · omega
            · have := hFM k hkF; omega)
          (by rw [Finset.card_insert_of_notMem hnot]; omega)
        have h2 := hvan F (fun k hk => by have := hFM k hk; omega) (by omega)
        dsimp only [Q']
        rw [map_sub, eval_shiftMvPoly]
        rw [Finset.sum_insert hnot] at h1
        have hadd : y₀ + ∑ k ∈ F, v k + v (M + i.val) = y₀ + (v (M + i.val) + ∑ k ∈ F, v k) := by
          ext j; simp only [Pi.add_apply]; ring
        rw [hadd, h1, h2, sub_self]
      intro y
      have hev := congrArg (MvPolynomial.eval y) hQ'_zero
      dsimp only [Q'] at hev
      rw [map_sub, eval_shiftMvPoly, map_zero] at hev
      exact sub_eq_zero.mp hev
    have hval_all : ∀ y : Fin (r + 1) → ℂ, MvPolynomial.eval y Q = 0 := by
      intro y
      obtain ⟨α, hα⟩ := modeJump_spans ms r M (y - y₀)
      have hstep : ∀ s : Finset (Fin (r + 1)),
          MvPolynomial.eval (y₀ + ∑ i ∈ s, α i • v (M + i.val)) Q = MvPolynomial.eval y₀ Q := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | @insert i s hi ihs =>
          rw [Finset.sum_insert hi]
          have hrearr : y₀ + (α i • v (M + i.val) + ∑ j ∈ s, α j • v (M + j.val)) =
              (y₀ + ∑ j ∈ s, α j • v (M + j.val)) + α i • v (M + i.val) := by
            ext j; simp only [Pi.add_apply]; ring
          rw [hrearr, mvPoly_periodic_all_scalar Q (v (M + i.val)) (hper_basis i), ihs]
      have hy0 : MvPolynomial.eval y₀ Q = 0 := by
        have h0 := hvan ∅ (fun _ h => absurd h (Finset.notMem_empty _)) (by simp)
        simpa using h0
      have hy_eq : y = y₀ + ∑ i : Fin (r + 1), α i • v (M + i.val) := by
        rw [hα]; ext j; simp
      rw [hy_eq, hstep Finset.univ, hy0]
    exact MvPolynomial.funext fun y => by rw [hval_all y, map_zero]

/-- **Matsubara Mode Series Constant-Coefficient Differential Transcendence**:
For any separated quadratically-growing mode sequence `ms`, the series
`S(z) = ∑' k, (z + a_k)^{-3/2}` satisfies NO nonzero constant-coefficient algebraic
differential equation on `(0, ∞)`. -/
theorem modeSeries_no_const_ade (ms : ModeSeq) {N : ℕ} (R : MvPolynomial (Fin (N + 1)) ℂ)
    (hR : ∀ x : ℝ, 0 < x →
      MvPolynomial.eval (fun j : Fin (N + 1) => iteratedDeriv j.val (modeSeries ms) (x : ℂ)) R = 0) :
    R = 0 := by
  have hall := modeSeriesFlipped_all ms R hR
  refine finite_diff_vandermonde_vanish ms R.totalDegree R le_rfl
    (fun j : Fin (N + 1) => iteratedDeriv j.val (modeSeries ms) 1) 0 ?_
  intro F _ _
  have h1 := hall F 1 zero_lt_one
  have hjet : (fun j : Fin (N + 1) => iteratedDeriv j.val (modeSeriesFlipped ms F) 1) =
      (fun j : Fin (N + 1) => iteratedDeriv j.val (modeSeries ms) 1) +
        ∑ k ∈ F, (fun j : Fin (N + 1) => -2 * iteratedDeriv j.val (modeTermL (ms.a k)) 1) := by
    ext j
    have hms_ana : AnalyticAt ℂ (modeSeries ms) 1 := by
      have h0 : modeSeries ms = fun z => ∑' k : ℕ, modeTermL (ms.a (0 + k)) z := by
        ext z; simp [modeSeries]
      rw [h0]
      exact modeSeries_tail_analyticOnNhd ms 0 1 (by simp; linarith [ms.a_pos 0])
    have hterm_ana : ∀ k ∈ F, AnalyticAt ℂ (modeTermL (ms.a k)) 1 := fun k _ =>
      modeTermL_analyticOnNhd (ms.a k) 1 (by simp; linarith [ms.a_pos k])
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have h1_mem : (1 : ℂ) ∈ {w : ℂ | 0 < w.re} := by simp
    have hms_smooth : ContDiffAt ℂ j.val (modeSeries ms) 1 := hms_ana.contDiffAt
    have hterm_smooth : ∀ k ∈ F, ContDiffAt ℂ j.val (modeTermL (ms.a k)) 1 :=
      fun k hk => (hterm_ana k hk).contDiffAt
    have hfin_smooth : ContDiffAt ℂ j.val (fun z => ∑ k ∈ F, modeTermL (ms.a k) z) 1 :=
      ContDiffAt.sum hterm_smooth
    have hflip_eq : modeSeriesFlipped ms F =
        fun z => modeSeries ms z - (2 : ℂ) • ∑ k ∈ F, modeTermL (ms.a k) z := by
      ext z; simp [modeSeriesFlipped, smul_eq_mul]
    rw [hflip_eq, iteratedDeriv_fun_sub hms_smooth (hfin_smooth.const_smul (2 : ℂ))]
    have hsmul : iteratedDeriv j.val (fun y => (2 : ℂ) • ∑ k ∈ F, modeTermL (ms.a k) y) 1 =
        (2 : ℂ) • iteratedDeriv j.val (fun y => ∑ k ∈ F, modeTermL (ms.a k) y) 1 :=
      iteratedDeriv_const_smul_field (c := (2 : ℂ)) (n := j.val)
        (f := fun y => ∑ k ∈ F, modeTermL (ms.a k) y) (x := 1)
    rw [hsmul, iteratedDeriv_fun_sum hterm_smooth]
    simp only [Pi.add_apply, Finset.sum_apply, Finset.mul_sum, smul_eq_mul, neg_mul,
      Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [← hjet]
  simpa using h1

/-! ### 3. Exact 1D & 3D Thermal Pressure Integrals, Bose–Fermi Doubling, and Matsubara Identities -/

/-- The dimensionless thermal Bose integrand `g(v) = -log(1 - exp(-2π √v))` for `v > 0`. -/
@[expose] def gThermal (v : ℝ) : ℝ :=
  -Real.log (1 - Real.exp (-2 * Real.pi * Real.sqrt v))

/-- The normalized 1D thermal pressure integral `H₁(y) = (2π)⁻¹ ∫_{-∞}^∞ g(p² + y) dp`. -/
@[expose] def H1 (y : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ p : ℝ, gThermal (p ^ 2 + y)

/-- The normalized 3D thermal pressure integral `H₃(y) = (2π²)⁻¹ ∫_0^∞ p² g(p² + y) dp`. -/
@[expose] def H3 (y : ℝ) : ℝ :=
  (2 * Real.pi ^ 2)⁻¹ * ∫ p in Set.Ioi (0 : ℝ), p ^ 2 * gThermal (p ^ 2 + y)

/-- Exact 1D relativistic ideal Bose gas pressure:
`B_{m,1}(T) = -T ∫_{-∞}^∞ log(1 - exp(-√(p² + m²)/T)) dp/(2π)`. -/
@[expose] def bosePressure1D (m T : ℝ) : ℝ :=
  -T * (2 * Real.pi)⁻¹ * ∫ p : ℝ, Real.log (1 - Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T))

/-- Exact 1D relativistic ideal Fermi gas pressure:
`F_{m,1}(T) = T ∫_{-∞}^∞ log(1 + exp(-√(p² + m²)/T)) dp/(2π)`. -/
@[expose] def fermiPressure1D (m T : ℝ) : ℝ :=
  T * (2 * Real.pi)⁻¹ * ∫ p : ℝ, Real.log (1 + Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T))

/-- Exact 3D relativistic ideal Bose gas pressure (radial momentum integral):
`B_{m,3}(T) = -T / (2π²) ∫_0^∞ p² log(1 - exp(-√(p² + m²)/T)) dp`. -/
@[expose] def bosePressure3D (m T : ℝ) : ℝ :=
  -T * (2 * Real.pi ^ 2)⁻¹ *
    ∫ p in Set.Ioi (0 : ℝ), p ^ 2 * Real.log (1 - Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T))

/-- Exact 3D relativistic ideal Fermi gas pressure (radial momentum integral):
`F_{m,3}(T) = T / (2π²) ∫_0^∞ p² log(1 + exp(-√(p² + m²)/T)) dp`. -/
@[expose] def fermiPressure3D (m T : ℝ) : ℝ :=
  T * (2 * Real.pi ^ 2)⁻¹ *
    ∫ p in Set.Ioi (0 : ℝ), p ^ 2 * Real.log (1 + Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T))

/-! #### Exponential Decay & Integrability Bounds -/

private lemma neg_log_one_sub_le {t : ℝ} (ht1 : t < 1) :
    -Real.log (1 - t) ≤ t / (1 - t) := by
  have hpos : 0 < (1 - t)⁻¹ := inv_pos.mpr (by linarith)
  have hlog := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_inv] at hlog
  have heq : (1 - t)⁻¹ - 1 = t / (1 - t) := by
    field_simp [show 1 - t ≠ 0 by linarith]
    ring
  linarith

private lemma gThermal_nonneg {v : ℝ} (hv : 0 < v) : 0 ≤ gThermal v := by
  unfold gThermal
  have he_pos : 0 < Real.exp (-2 * Real.pi * Real.sqrt v) := Real.exp_pos _
  have he_lt : Real.exp (-2 * Real.pi * Real.sqrt v) < 1 := by
    rw [Real.exp_lt_one_iff]
    have hsq : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
    nlinarith [Real.pi_pos]
  have h1 : 1 - Real.exp (-2 * Real.pi * Real.sqrt v) ≤ 1 := by linarith
  have h2 : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt v) := by linarith
  have hlog : Real.log (1 - Real.exp (-2 * Real.pi * Real.sqrt v)) ≤ 0 :=
    Real.log_nonpos h2.le h1
  linarith

private lemma gThermal_le_exp {v y₀ : ℝ} (hy₀ : 0 < y₀) (hv : y₀ ≤ v) :
    gThermal v ≤ (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹ *
      Real.exp (-2 * Real.pi * Real.sqrt v) := by
  unfold gThermal
  have hv_pos : 0 < v := lt_of_lt_of_le hy₀ hv
  have he_lt : Real.exp (-2 * Real.pi * Real.sqrt v) < 1 := by
    rw [Real.exp_lt_one_iff]
    have hsq : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv_pos
    nlinarith [Real.pi_pos]
  have he_le : Real.exp (-2 * Real.pi * Real.sqrt v) ≤ Real.exp (-2 * Real.pi * Real.sqrt y₀) := by
    apply Real.exp_le_exp.mpr
    have hsq : Real.sqrt y₀ ≤ Real.sqrt v := Real.sqrt_le_sqrt hv
    nlinarith [Real.pi_pos]
  have hden_pos : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt y₀) := by
    have : Real.exp (-2 * Real.pi * Real.sqrt y₀) < 1 := by
      rw [Real.exp_lt_one_iff]
      have hsq : 0 < Real.sqrt y₀ := Real.sqrt_pos.mpr hy₀
      nlinarith [Real.pi_pos]
    linarith
  have h1 := neg_log_one_sub_le he_lt
  calc -Real.log (1 - Real.exp (-2 * Real.pi * Real.sqrt v))
      ≤ Real.exp (-2 * Real.pi * Real.sqrt v) / (1 - Real.exp (-2 * Real.pi * Real.sqrt v)) := h1
    _ ≤ Real.exp (-2 * Real.pi * Real.sqrt v) / (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀)) := by
        exact div_le_div_of_nonneg_left (Real.exp_pos _).le hden_pos (by linarith)
    _ = (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹ *
          Real.exp (-2 * Real.pi * Real.sqrt v) := by ring

private lemma integrable_pow_mul_exp_neg_abs {a : ℝ} (ha : 0 < a) (k : ℕ) :
    Integrable (fun p : ℝ => |p| ^ k * Real.exp (-a * |p|)) := by
  -- Use comparison with integrableOn_exp_mul_Ioi via |p|^k ≤ C * exp((a/2)*|p|)
  have hpos : 0 < a / 2 := half_pos ha
  have hIoi : IntegrableOn (fun p : ℝ => Real.exp (-(a / 2) * p)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hIic : IntegrableOn (fun p : ℝ => Real.exp ((a / 2) * p)) (Set.Iic 0) := by
    have hcomp := (integrableOn_exp_mul_Ioi (a := -(a / 2)) (by linarith) 0).comp_neg
    have hcongr : IntegrableOn (fun p : ℝ => Real.exp ((a / 2) * p)) (Set.Iio 0) := by
      have heq : -Set.Ioi (0 : ℝ) = Set.Iio 0 := by ext x; simp
      rw [heq] at hcomp
      exact hcomp.congr_fun (fun p _ => by simp) measurableSet_Iio
    exact hcongr.congr_set_ae MeasureTheory.Iio_ae_eq_Iic.symm
  have hexp_abs : Integrable (fun p : ℝ => Real.exp (-(a / 2) * |p|)) := by
    rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
    refine IntegrableOn.union ?_ ?_
    · exact hIic.congr_fun (fun p hp => by
        rw [abs_of_nonpos (Set.mem_Iic.mp hp)]; ring_nf) measurableSet_Iic
    · exact hIoi.congr_fun (fun p hp => by
        rw [abs_of_pos (Set.mem_Ioi.mp hp)]) measurableSet_Ioi
  -- Bound |p|^k * exp(-a|p|) ≤ (k! / (a/2)^k) * exp(-(a/2)|p|)
  have hbound : ∀ p : ℝ, ‖|p| ^ k * Real.exp (-a * |p|)‖ ≤
      ((Nat.factorial k : ℝ) / (a / 2) ^ k) * Real.exp (-(a / 2) * |p|) := by
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hpow := Real.pow_div_factorial_le_exp ((a / 2) * |p|) (by positivity) k
    have hmul : |p| ^ k ≤ ((Nat.factorial k : ℝ) / (a / 2) ^ k) * Real.exp ((a / 2) * |p|) := by
      have h1 : (a / 2) ^ k * |p| ^ k / (Nat.factorial k : ℝ) ≤ Real.exp ((a / 2) * |p|) := by
        rwa [mul_pow] at hpow
      have hfac : (0 : ℝ) < Nat.factorial k := Nat.cast_pos.mpr (Nat.factorial_pos k)
      have ha2k : (0 : ℝ) < (a / 2) ^ k := pow_pos hpos k
      rw [div_le_iff₀ hfac] at h1
      rw [div_mul_eq_mul_div, le_div_iff₀ ha2k]
      nlinarith
    calc |p| ^ k * Real.exp (-a * |p|)
        ≤ ((Nat.factorial k : ℝ) / (a / 2) ^ k) * Real.exp ((a / 2) * |p|) *
            Real.exp (-a * |p|) := mul_le_mul_of_nonneg_right hmul (Real.exp_pos _).le
      _ = ((Nat.factorial k : ℝ) / (a / 2) ^ k) * Real.exp (-(a / 2) * |p|) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2; ring
  exact (hexp_abs.const_mul _).mono' (by fun_prop) (Eventually.of_forall hbound)

private lemma continuous_gThermal_comp {y : ℝ} (hy : 0 < y) :
    Continuous (fun p : ℝ => gThermal (p ^ 2 + y)) := by
  unfold gThermal
  refine Continuous.neg (Continuous.log (by fun_prop) fun p => ?_)
  have hv : 0 < p ^ 2 + y := by positivity
  have hsq : 0 < Real.sqrt (p ^ 2 + y) := Real.sqrt_pos.mpr hv
  have he : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
  linarith

private lemma integrable_gThermal_comp {y : ℝ} (hy : 0 < y) :
    Integrable (fun p : ℝ => gThermal (p ^ 2 + y)) := by
  let C : ℝ := (1 - Real.exp (-2 * Real.pi * Real.sqrt y))⁻¹
  have hexp := (integrable_pow_mul_exp_neg_abs (a := 2 * Real.pi) (by positivity) 0).const_mul C
  refine hexp.mono' (continuous_gThermal_comp hy).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  have hv : y ≤ p ^ 2 + y := by linarith [sq_nonneg p]
  have hnn : 0 ≤ gThermal (p ^ 2 + y) := gThermal_nonneg (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have h1 := gThermal_le_exp hy hv
  have hsq : |p| ≤ Real.sqrt (p ^ 2 + y) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  have hexp_le : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≤ Real.exp (-(2 * Real.pi) * |p|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hC_nn : 0 ≤ C := by
    dsimp only [C]
    have hsqy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
    have he : Real.exp (-2 * Real.pi * Real.sqrt y) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
    positivity
  have hres : gThermal (p ^ 2 + y) ≤ C * Real.exp (-(2 * Real.pi) * |p|) :=
    h1.trans (mul_le_mul_of_nonneg_left hexp_le hC_nn)
  simpa [pow_zero, one_mul] using hres

private lemma integrableOn_sq_mul_gThermal {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun p : ℝ => p ^ 2 * gThermal (p ^ 2 + y)) (Set.Ioi 0) := by
  let C : ℝ := (1 - Real.exp (-2 * Real.pi * Real.sqrt y))⁻¹
  have hexp : IntegrableOn (fun p : ℝ => C * (|p| ^ 2 * Real.exp (-(2 * Real.pi) * |p|))) (Set.Ioi 0) :=
    ((integrable_pow_mul_exp_neg_abs (a := 2 * Real.pi) (by positivity) 2).const_mul C).integrableOn
  refine hexp.mono' ((continuous_pow 2).mul (continuous_gThermal_comp hy)).aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  have hv : y ≤ p ^ 2 + y := by linarith [sq_nonneg p]
  have hnn : 0 ≤ p ^ 2 * gThermal (p ^ 2 + y) := mul_nonneg (sq_nonneg p) (gThermal_nonneg (by positivity))
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  have h1 := gThermal_le_exp hy hv
  have hsq : |p| ≤ Real.sqrt (p ^ 2 + y) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  have hexp_le : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≤ Real.exp (-(2 * Real.pi) * |p|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hC_nn : 0 ≤ C := by
    dsimp only [C]
    have hsqy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
    have he : Real.exp (-2 * Real.pi * Real.sqrt y) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
    positivity
  have hle : gThermal (p ^ 2 + y) ≤ C * Real.exp (-(2 * Real.pi) * |p|) :=
    h1.trans (mul_le_mul_of_nonneg_left hexp_le hC_nn)
  calc p ^ 2 * gThermal (p ^ 2 + y)
      ≤ p ^ 2 * (C * Real.exp (-(2 * Real.pi) * |p|)) := mul_le_mul_of_nonneg_left hle (sq_nonneg p)
    _ = C * (|p| ^ 2 * Real.exp (-(2 * Real.pi) * |p|)) := by rw [sq_abs]; ring

/-! #### Scaling & Bose–Fermi Doubling Identities (`d = 1` and `d = 3`) -/

theorem bosePressure1D_eq_H1 {m T : ℝ} (hT : 0 < T) :
    bosePressure1D m T = 2 * Real.pi * T ^ 2 * H1 (m ^ 2 / (2 * Real.pi * T) ^ 2) := by
  unfold bosePressure1D H1 gThermal
  have hc : 0 < 2 * Real.pi * T := by positivity
  have hsub := MeasureTheory.Measure.integral_comp_mul_left
    (g := fun p : ℝ => -Real.log (1 - Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T))) (2 * Real.pi * T)
  have hsub' : ∫ p : ℝ, Real.log (1 - Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T)) =
      -(2 * Real.pi * T) * ∫ q : ℝ, -Real.log (1 - Real.exp (-2 * Real.pi * Real.sqrt (q ^ 2 + m ^ 2 / (2 * Real.pi * T) ^ 2))) := by
    have h1 : ∫ q : ℝ, -Real.log (1 - Real.exp (-Real.sqrt ((2 * Real.pi * T * q) ^ 2 + m ^ 2) / T)) =
        (2 * Real.pi * T)⁻¹ * ∫ p : ℝ, -Real.log (1 - Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T)) := by
      simpa [abs_of_pos (inv_pos.mpr hc), abs_of_pos hT, smul_eq_mul] using hsub
    have h2 : ∫ q : ℝ, -Real.log (1 - Real.exp (-Real.sqrt ((2 * Real.pi * T * q) ^ 2 + m ^ 2) / T)) =
        ∫ q : ℝ, -Real.log (1 - Real.exp (-2 * Real.pi * Real.sqrt (q ^ 2 + m ^ 2 / (2 * Real.pi * T) ^ 2))) := by
      congr 1; ext q
      have hrad : Real.sqrt ((2 * Real.pi * T * q) ^ 2 + m ^ 2) / T =
          2 * Real.pi * Real.sqrt (q ^ 2 + m ^ 2 / (2 * Real.pi * T) ^ 2) := by
        have hfac : (2 * Real.pi * T * q) ^ 2 + m ^ 2 =
            (2 * Real.pi * T) ^ 2 * (q ^ 2 + m ^ 2 / (2 * Real.pi * T) ^ 2) := by
          field_simp [hc.ne']
        rw [hfac, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc.le]
        field_simp [hT.ne']
      rw [neg_div, hrad]
      congr 3; ring
    have hneg_rhs : ∫ p : ℝ, -Real.log (1 - Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T)) =
        -∫ p : ℝ, Real.log (1 - Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T)) :=
      MeasureTheory.integral_neg _
    rw [h2, hneg_rhs] at h1
    have hmul := congrArg (fun x => -(2 * Real.pi * T) * x) h1
    field_simp [hc.ne'] at hmul ⊢
    linarith
  rw [hsub']
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp [hpi]

/-- **1D Bose–Fermi Doubling Identity**: `F_{m,1}(T) = B_{m,1}(T) - (1/2) B_{2m,1}(T)`. -/
theorem fermiPressure1D_doubling {m T : ℝ} (hm : 0 < m) (hT : 0 < T) :
    fermiPressure1D m T = bosePressure1D m T - (1 / 2 : ℝ) * bosePressure1D (2 * m) T := by
  have hint_m : Integrable (fun p : ℝ => Real.log (1 - Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T))) := by
    have hc : 0 < 2 * Real.pi * T := by positivity
    have h1 := integrable_gThermal_comp (y := m ^ 2 / (2 * Real.pi * T) ^ 2) (by positivity)
    have h2 := h1.comp_div hc.ne'
    refine (h2.neg).congr (Eventually.of_forall fun p => ?_)
    dsimp only [Pi.neg_apply, Function.comp, gThermal]
    rw [neg_neg]
    have hrad : 2 * Real.pi * Real.sqrt ((p / (2 * Real.pi * T)) ^ 2 + m ^ 2 / (2 * Real.pi * T) ^ 2) =
        Real.sqrt (p ^ 2 + m ^ 2) / T := by
      have hfac : (p / (2 * Real.pi * T)) ^ 2 + m ^ 2 / (2 * Real.pi * T) ^ 2 =
          (p ^ 2 + m ^ 2) / (2 * Real.pi * T) ^ 2 := by ring
      rw [hfac, Real.sqrt_div (by positivity), Real.sqrt_sq hc.le]
      field_simp [hT.ne', (show (2 * Real.pi : ℝ) ≠ 0 by positivity)]
    rw [neg_div]
    congr 3
    linarith
  have hint_2m : Integrable (fun p : ℝ => Real.log (1 - Real.exp (-2 * Real.sqrt (p ^ 2 + m ^ 2) / T))) := by
    have hc' : 0 < Real.pi * T := by positivity
    have h1 := integrable_gThermal_comp (y := (2 * m) ^ 2 / (2 * Real.pi * T) ^ 2) (by positivity)
    have h2 := h1.comp_div hc'.ne'
    refine (h2.neg).congr (Eventually.of_forall fun p => ?_)
    dsimp only [Pi.neg_apply, Function.comp, gThermal]
    rw [neg_neg]
    have hrad : 2 * Real.pi * Real.sqrt ((p / (Real.pi * T)) ^ 2 + (2 * m) ^ 2 / (2 * Real.pi * T) ^ 2) =
        2 * Real.sqrt (p ^ 2 + m ^ 2) / T := by
      have hfac : (p / (Real.pi * T)) ^ 2 + (2 * m) ^ 2 / (2 * Real.pi * T) ^ 2 =
          (p ^ 2 + m ^ 2) / (Real.pi * T) ^ 2 := by field_simp [hc'.ne']
      rw [hfac, Real.sqrt_div (by positivity), Real.sqrt_sq hc'.le]
      field_simp [hT.ne', Real.pi_ne_zero]
    have hneg : -2 * Real.sqrt (p ^ 2 + m ^ 2) / T = -(2 * Real.sqrt (p ^ 2 + m ^ 2) / T) := by ring
    rw [hneg]
    congr 3
    linarith
  have hlog_id : ∀ p : ℝ,
      Real.log (1 + Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T)) =
        Real.log (1 - Real.exp (-2 * Real.sqrt (p ^ 2 + m ^ 2) / T)) -
          Real.log (1 - Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T)) := by
    intro p
    set q : ℝ := Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T)
    have hq_pos : 0 < q := Real.exp_pos _
    have hq_lt : q < 1 := by
      rw [Real.exp_lt_one_iff]
      have hsq : 0 < Real.sqrt (p ^ 2 + m ^ 2) := Real.sqrt_pos.mpr (by positivity)
      exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hsq) hT
    have hq2 : Real.exp (-2 * Real.sqrt (p ^ 2 + m ^ 2) / T) = q ^ 2 := by
      dsimp only [q]; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hq2]
    have hfac : 1 - q ^ 2 = (1 - q) * (1 + q) := by ring
    rw [hfac, Real.log_mul (by linarith) (by linarith)]
    ring
  have hscale : ∫ p : ℝ, Real.log (1 - Real.exp (-2 * Real.sqrt (p ^ 2 + m ^ 2) / T)) =
      (1 / 2 : ℝ) * ∫ q : ℝ, Real.log (1 - Real.exp (-Real.sqrt (q ^ 2 + (2 * m) ^ 2) / T)) := by
    have hsub := MeasureTheory.Measure.integral_comp_mul_left
      (g := fun q : ℝ => Real.log (1 - Real.exp (-Real.sqrt (q ^ 2 + (2 * m) ^ 2) / T))) (2 : ℝ)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹), smul_eq_mul] at hsub
    rw [one_div, ← hsub]
    congr 1; ext p
    have hsq : Real.sqrt ((2 * p) ^ 2 + (2 * m) ^ 2) = 2 * Real.sqrt (p ^ 2 + m ^ 2) := by
      have : (2 * p) ^ 2 + (2 * m) ^ 2 = 2 ^ 2 * (p ^ 2 + m ^ 2) := by ring
      rw [this, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [hsq]; congr 3; ring
  unfold fermiPressure1D bosePressure1D
  simp_rw [hlog_id]
  rw [MeasureTheory.integral_sub hint_2m hint_m, hscale]
  ring

theorem bosePressure3D_eq_H3 {m T : ℝ} (hT : 0 < T) :
    bosePressure3D m T = 8 * Real.pi ^ 3 * T ^ 4 * H3 (m ^ 2 / (2 * Real.pi * T) ^ 2) := by
  unfold bosePressure3D H3 gThermal
  have hc : 0 < 2 * Real.pi * T := by positivity
  have hsub := MeasureTheory.integral_comp_mul_left_Ioi
    (g := fun p : ℝ => p ^ 2 * (-Real.log (1 - Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T))))
    0 hc
  simp only [smul_eq_mul, mul_zero] at hsub
  have hneg : ∫ p in Set.Ioi (0 : ℝ), p ^ 2 * Real.log (1 - Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T)) =
      -∫ p in Set.Ioi (0 : ℝ), p ^ 2 * (-Real.log (1 - Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T))) := by
    rw [← MeasureTheory.integral_neg]
    congr 1; ext p; ring
  rw [hneg]
  have hscale : ∫ p in Set.Ioi (0 : ℝ), p ^ 2 * (-Real.log (1 - Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T))) =
      (2 * Real.pi * T) ^ 3 *
        ∫ q in Set.Ioi (0 : ℝ), q ^ 2 * (-Real.log (1 - Real.exp (-2 * Real.pi * Real.sqrt (q ^ 2 + m ^ 2 / (2 * Real.pi * T) ^ 2)))) := by
    have hmul := congrArg (fun x => (2 * Real.pi * T) * x) hsub
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at hmul
    rw [← hmul]
    have hpull : (2 * Real.pi * T) *
        ∫ q in Set.Ioi (0 : ℝ), (2 * Real.pi * T * q) ^ 2 *
          (-Real.log (1 - Real.exp (-Real.sqrt ((2 * Real.pi * T * q) ^ 2 + m ^ 2) / T))) =
        (2 * Real.pi * T) ^ 3 *
        ∫ q in Set.Ioi (0 : ℝ), q ^ 2 *
          (-Real.log (1 - Real.exp (-2 * Real.pi * Real.sqrt (q ^ 2 + m ^ 2 / (2 * Real.pi * T) ^ 2)))) := by
      rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
      congr 1; ext q
      have hrad : Real.sqrt ((2 * Real.pi * T * q) ^ 2 + m ^ 2) / T =
          2 * Real.pi * Real.sqrt (q ^ 2 + m ^ 2 / (2 * Real.pi * T) ^ 2) := by
        have hfac : (2 * Real.pi * T * q) ^ 2 + m ^ 2 =
            (2 * Real.pi * T) ^ 2 * (q ^ 2 + m ^ 2 / (2 * Real.pi * T) ^ 2) := by
          field_simp [hc.ne']
        rw [hfac, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc.le]
        field_simp [hT.ne']
      rw [neg_div, hrad]
      have : -(2 * Real.pi * Real.sqrt (q ^ 2 + m ^ 2 / (2 * Real.pi * T) ^ 2)) =
          -2 * Real.pi * Real.sqrt (q ^ 2 + m ^ 2 / (2 * Real.pi * T) ^ 2) := by ring
      rw [this]
      ring
    exact hpull
  rw [hscale]
  have hpi : (2 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp [hpi]
  ring

/-- **3D Bose–Fermi Doubling Identity**: `F_{m,3}(T) = B_{m,3}(T) - (1/8) B_{2m,3}(T)`. -/
theorem fermiPressure3D_doubling {m T : ℝ} (hm : 0 < m) (hT : 0 < T) :
    fermiPressure3D m T = bosePressure3D m T - (1 / 8 : ℝ) * bosePressure3D (2 * m) T := by
  have hc : 0 < 2 * Real.pi * T := by positivity
  have hint_m : IntegrableOn
      (fun p : ℝ => p ^ 2 * Real.log (1 - Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T))) (Set.Ioi 0) := by
    have h1 : Integrable (fun p : ℝ => p ^ 2 * gThermal (p ^ 2 + m ^ 2 / (2 * Real.pi * T) ^ 2)) := by
      let y1 : ℝ := m ^ 2 / (2 * Real.pi * T) ^ 2
      have hy1 : 0 < y1 := by positivity
      let C1 : ℝ := (1 - Real.exp (-2 * Real.pi * Real.sqrt y1))⁻¹
      refine ((integrable_pow_mul_exp_neg_abs (a := 2 * Real.pi) (by positivity) 2).const_mul C1).mono'
        ((continuous_pow 2).mul (continuous_gThermal_comp hy1)).aestronglyMeasurable
        (Eventually.of_forall fun p => ?_)
      have hnn : 0 ≤ p ^ 2 * gThermal (p ^ 2 + y1) := mul_nonneg (sq_nonneg p) (gThermal_nonneg (by positivity))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have h1 := gThermal_le_exp hy1 (by linarith [sq_nonneg p] : y1 ≤ p ^ 2 + y1)
      have hsq : |p| ≤ Real.sqrt (p ^ 2 + y1) := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
      have hexp_le : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y1)) ≤ Real.exp (-(2 * Real.pi) * |p|) := by
        apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
      have hC1 : 0 ≤ C1 := by
        dsimp only [C1]
        have : Real.exp (-2 * Real.pi * Real.sqrt y1) < 1 := by
          rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hy1]
        positivity
      have hle := h1.trans (mul_le_mul_of_nonneg_left hexp_le hC1)
      calc p ^ 2 * gThermal (p ^ 2 + y1) ≤ p ^ 2 * (C1 * Real.exp (-(2 * Real.pi) * |p|)) :=
            mul_le_mul_of_nonneg_left hle (sq_nonneg p)
        _ = C1 * (|p| ^ 2 * Real.exp (-(2 * Real.pi) * |p|)) := by rw [sq_abs]; ring
    have h2 := (h1.comp_div hc.ne').integrableOn (s := Set.Ioi 0)
    refine (h2.const_mul (-(2 * Real.pi * T) ^ 2)).congr (Eventually.of_forall fun p => ?_)
    dsimp only [Function.comp, gThermal]
    have hrad : 2 * Real.pi * Real.sqrt ((p / (2 * Real.pi * T)) ^ 2 + m ^ 2 / (2 * Real.pi * T) ^ 2) =
        Real.sqrt (p ^ 2 + m ^ 2) / T := by
      have hfac : (p / (2 * Real.pi * T)) ^ 2 + m ^ 2 / (2 * Real.pi * T) ^ 2 =
          (p ^ 2 + m ^ 2) / (2 * Real.pi * T) ^ 2 := by ring
      rw [hfac, Real.sqrt_div (by positivity), Real.sqrt_sq hc.le]
      field_simp [hT.ne', (show (2 * Real.pi : ℝ) ≠ 0 by positivity)]
    have hneg : -2 * Real.pi * Real.sqrt ((p / (2 * Real.pi * T)) ^ 2 + m ^ 2 / (2 * Real.pi * T) ^ 2) =
        -Real.sqrt (p ^ 2 + m ^ 2) / T := by rw [neg_div, ← hrad]; ring
    rw [hneg]
    field_simp [hc.ne']
  have hint_2m : IntegrableOn
      (fun p : ℝ => p ^ 2 * Real.log (1 - Real.exp (-2 * Real.sqrt (p ^ 2 + m ^ 2) / T))) (Set.Ioi 0) := by
    have hc' : 0 < Real.pi * T := by positivity
    have h1 : Integrable (fun p : ℝ => p ^ 2 * gThermal (p ^ 2 + (2 * m) ^ 2 / (2 * Real.pi * T) ^ 2)) := by
      let y2 : ℝ := (2 * m) ^ 2 / (2 * Real.pi * T) ^ 2
      have hy2 : 0 < y2 := by positivity
      let C2 : ℝ := (1 - Real.exp (-2 * Real.pi * Real.sqrt y2))⁻¹
      refine ((integrable_pow_mul_exp_neg_abs (a := 2 * Real.pi) (by positivity) 2).const_mul C2).mono'
        ((continuous_pow 2).mul (continuous_gThermal_comp hy2)).aestronglyMeasurable
        (Eventually.of_forall fun p => ?_)
      have hnn : 0 ≤ p ^ 2 * gThermal (p ^ 2 + y2) := mul_nonneg (sq_nonneg p) (gThermal_nonneg (by positivity))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have h1 := gThermal_le_exp hy2 (by linarith [sq_nonneg p] : y2 ≤ p ^ 2 + y2)
      have hsq : |p| ≤ Real.sqrt (p ^ 2 + y2) := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
      have hexp_le : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y2)) ≤ Real.exp (-(2 * Real.pi) * |p|) := by
        apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
      have hC2 : 0 ≤ C2 := by
        dsimp only [C2]
        have : Real.exp (-2 * Real.pi * Real.sqrt y2) < 1 := by
          rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hy2]
        positivity
      have hle := h1.trans (mul_le_mul_of_nonneg_left hexp_le hC2)
      calc p ^ 2 * gThermal (p ^ 2 + y2) ≤ p ^ 2 * (C2 * Real.exp (-(2 * Real.pi) * |p|)) :=
            mul_le_mul_of_nonneg_left hle (sq_nonneg p)
        _ = C2 * (|p| ^ 2 * Real.exp (-(2 * Real.pi) * |p|)) := by rw [sq_abs]; ring
    have h2 := (h1.comp_div hc'.ne').integrableOn (s := Set.Ioi 0)
    refine (h2.const_mul (-(Real.pi * T) ^ 2)).congr (Eventually.of_forall fun p => ?_)
    dsimp only [Function.comp, gThermal]
    have hrad : 2 * Real.pi * Real.sqrt ((p / (Real.pi * T)) ^ 2 + (2 * m) ^ 2 / (2 * Real.pi * T) ^ 2) =
        2 * Real.sqrt (p ^ 2 + m ^ 2) / T := by
      have hfac : (p / (Real.pi * T)) ^ 2 + (2 * m) ^ 2 / (2 * Real.pi * T) ^ 2 =
          (p ^ 2 + m ^ 2) / (Real.pi * T) ^ 2 := by field_simp [hc'.ne']
      rw [hfac, Real.sqrt_div (by positivity), Real.sqrt_sq hc'.le]
      field_simp [hT.ne', Real.pi_ne_zero]
    have hneg : -2 * Real.pi * Real.sqrt ((p / (Real.pi * T)) ^ 2 + (2 * m) ^ 2 / (2 * Real.pi * T) ^ 2) =
        -2 * Real.sqrt (p ^ 2 + m ^ 2) / T := by
      have : -2 * Real.sqrt (p ^ 2 + m ^ 2) / T = -(2 * Real.sqrt (p ^ 2 + m ^ 2) / T) := by ring
      rw [this, ← hrad]; ring
    rw [hneg]
    field_simp [hc'.ne']
  have hlog_id : ∀ p : ℝ,
      p ^ 2 * Real.log (1 + Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T)) =
        p ^ 2 * Real.log (1 - Real.exp (-2 * Real.sqrt (p ^ 2 + m ^ 2) / T)) -
          p ^ 2 * Real.log (1 - Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T)) := by
    intro p
    set q : ℝ := Real.exp (-Real.sqrt (p ^ 2 + m ^ 2) / T)
    have hq_pos : 0 < q := Real.exp_pos _
    have hq_lt : q < 1 := by
      rw [Real.exp_lt_one_iff]
      have hsq : 0 < Real.sqrt (p ^ 2 + m ^ 2) := Real.sqrt_pos.mpr (by positivity)
      exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hsq) hT
    have hq2 : Real.exp (-2 * Real.sqrt (p ^ 2 + m ^ 2) / T) = q ^ 2 := by
      dsimp only [q]; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hq2]
    have hfac : 1 - q ^ 2 = (1 - q) * (1 + q) := by ring
    rw [hfac, Real.log_mul (by linarith) (by linarith)]
    ring
  have hscale : ∫ p in Set.Ioi (0 : ℝ), p ^ 2 * Real.log (1 - Real.exp (-2 * Real.sqrt (p ^ 2 + m ^ 2) / T)) =
      (1 / 8 : ℝ) * ∫ q in Set.Ioi (0 : ℝ), q ^ 2 * Real.log (1 - Real.exp (-Real.sqrt (q ^ 2 + (2 * m) ^ 2) / T)) := by
    have hsub := MeasureTheory.integral_comp_mul_left_Ioi
      (g := fun q : ℝ => q ^ 2 * Real.log (1 - Real.exp (-Real.sqrt (q ^ 2 + (2 * m) ^ 2) / T)))
      0 (by norm_num : (0 : ℝ) < 2)
    simp only [smul_eq_mul, mul_zero] at hsub
    have hpull : (4 : ℝ) * ∫ p in Set.Ioi (0 : ℝ), p ^ 2 * Real.log (1 - Real.exp (-2 * Real.sqrt (p ^ 2 + m ^ 2) / T)) =
        (2 : ℝ)⁻¹ * ∫ q in Set.Ioi (0 : ℝ), q ^ 2 * Real.log (1 - Real.exp (-Real.sqrt (q ^ 2 + (2 * m) ^ 2) / T)) := by
      rw [← hsub, ← MeasureTheory.integral_const_mul]
      congr 1; ext p
      have hsq : Real.sqrt ((2 * p) ^ 2 + (2 * m) ^ 2) = 2 * Real.sqrt (p ^ 2 + m ^ 2) := by
        have : (2 * p) ^ 2 + (2 * m) ^ 2 = 2 ^ 2 * (p ^ 2 + m ^ 2) := by ring
        rw [this, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
      rw [hsq]
      have : -(2 * Real.sqrt (p ^ 2 + m ^ 2)) / T = -2 * Real.sqrt (p ^ 2 + m ^ 2) / T := by ring
      rw [this]; ring
    linarith
  unfold fermiPressure3D bosePressure3D
  simp_rw [hlog_id]
  rw [MeasureTheory.integral_sub hint_2m hint_m, hscale]
  ring

/-! #### Derivatives of `gThermal` via Mathlib's `cot_series_rep'` -/

private lemma hasDerivAt_gThermal {v : ℝ} (hv : 0 < v) :
    HasDerivAt gThermal
      (-Real.pi / Real.sqrt v *
        (Real.exp (-2 * Real.pi * Real.sqrt v) / (1 - Real.exp (-2 * Real.pi * Real.sqrt v)))) v := by
  have hsq : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have h1 : HasDerivAt (fun x : ℝ => -2 * Real.pi * Real.sqrt x)
      (-2 * Real.pi * (1 / (2 * Real.sqrt v))) v :=
    (Real.hasDerivAt_sqrt hv.ne').const_mul (-2 * Real.pi)
  have h2 := h1.exp
  have h3 : HasDerivAt (fun x : ℝ => 1 - Real.exp (-2 * Real.pi * Real.sqrt x))
      (-(Real.exp (-2 * Real.pi * Real.sqrt v) * (-2 * Real.pi * (1 / (2 * Real.sqrt v))))) v := by
    simpa using (hasDerivAt_const v (1 : ℝ)).fun_sub h2
  have hne : 1 - Real.exp (-2 * Real.pi * Real.sqrt v) ≠ 0 := by
    have : Real.exp (-2 * Real.pi * Real.sqrt v) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
    linarith
  have h4 := (h3.log hne).neg
  refine h4.congr_deriv ?_
  field_simp [hsq.ne', hne]

private lemma deriv_gThermal_eq_tsum {v : ℝ} (hv : 0 < v) :
    deriv gThermal v =
      Real.pi / (2 * Real.sqrt v) - 1 / (2 * v) - ∑' n : ℕ, 1 / (v + ((n : ℝ) + 1) ^ 2) := by
  rw [(hasDerivAt_gThermal hv).deriv]
  set s : ℝ := Real.sqrt v
  have hs : 0 < s := Real.sqrt_pos.mpr hv
  have hs2 : s ^ 2 = v := Real.sq_sqrt hv.le
  let z : ℂ := Complex.I * (s : ℂ)
  have hz_mem : z ∈ integerComplement := by
    simp only [integerComplement, Set.mem_compl_iff, Set.mem_range, not_exists]
    intro n hn
    have him := congrArg Complex.im hn
    simp [z] at him
    linarith
  have hcot := cot_series_rep' hz_mem
  have hexp_cast : Complex.exp (-2 * (Real.pi : ℂ) * (s : ℂ)) =
      ((Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; push_cast; rfl
  have hcot_lhs : (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) =
      -Complex.I * (Real.pi : ℂ) *
        (1 + 2 * Complex.exp (-2 * (Real.pi : ℂ) * (s : ℂ)) /
          (1 - Complex.exp (-2 * (Real.pi : ℂ) * (s : ℂ)))) := by
    rw [Complex.cot_pi_eq_exp_ratio]
    have hexp_eq : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z) =
        Complex.exp (-2 * (Real.pi : ℂ) * (s : ℂ)) := by
      congr 1; simp [z]; ring_nf; rw [Complex.I_sq]; ring
    rw [hexp_eq]
    set E : ℂ := Complex.exp (-2 * (Real.pi : ℂ) * (s : ℂ))
    have he_lt : Real.exp (-2 * Real.pi * s) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
    have hden : 1 - E ≠ 0 := by
      intro h0
      have hre := congrArg Complex.re h0
      have hE : E = ((Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) := hexp_cast
      rw [hE] at hre
      simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.zero_re] at hre
      linarith
    field_simp [Complex.I_ne_zero, hden]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hcot_rhs : ∑' n : ℕ, (1 / (z - ((n : ℂ) + 1)) + 1 / (z + ((n : ℂ) + 1))) =
      (-Complex.I * (2 * (s : ℂ))) * ∑' n : ℕ, ((1 / (v + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) := by
    rw [← tsum_mul_left]
    apply tsum_congr; intro n
    have hn_pos : (0 : ℝ) < v + ((n : ℝ) + 1) ^ 2 := by positivity
    have h1 : z - ((n : ℂ) + 1) ≠ 0 := by
      intro h0; have him := congrArg Complex.im h0; simp [z] at him; linarith
    have h2 : z + ((n : ℂ) + 1) ≠ 0 := by
      intro h0; have him := congrArg Complex.im h0; simp [z] at him; linarith
    have h3 : (v : ℂ) + ((n : ℂ) + 1) ^ 2 ≠ 0 := by
      have : (v : ℂ) + ((n : ℂ) + 1) ^ 2 = ((v + ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
      rw [this]; exact Complex.ofReal_ne_zero.mpr hn_pos.ne'
    push_cast
    field_simp [h1, h2, h3]
    dsimp only [z]
    have hsc : (s : ℂ) ^ 2 = (v : ℂ) := by exact_mod_cast hs2
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination -2 * Complex.I * (s : ℂ) * hsc + 2 * Complex.I * (s : ℂ) ^ 3 * hI2
  have hinv_z : 1 / z = -Complex.I / (s : ℂ) := by
    dsimp only [z]
    have hs_ne : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    field_simp [Complex.I_ne_zero, hs_ne]
    rw [Complex.I_sq]; ring
  rw [hcot_lhs, hinv_z, hcot_rhs] at hcot
  have him_eq := congrArg Complex.im hcot
  have hsumm_v : Summable (fun n : ℕ => 1 / (v + ((n : ℝ) + 1) ^ 2)) := by
    have hp : Summable (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    have h2 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
      refine (hp.comp_injective Nat.succ_injective).congr fun n => ?_
      simp only [Function.comp, Nat.cast_succ, one_div]
      congr 1; exact_mod_cast (Real.rpow_natCast ((n : ℝ) + 1) 2)
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h2
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have htsum_cast : (∑' n : ℕ, ((1 / (v + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ)) =
      ((∑' n : ℕ, 1 / (v + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) :=
    (Complex.ofRealCLM.map_tsum hsumm_v).symm
  rw [htsum_cast, hexp_cast] at him_eq
  have hre_lhs :
      (-Complex.I * (Real.pi : ℂ) *
        (1 + 2 * ((Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) /
          (1 - ((Real.exp (-2 * Real.pi * s) : ℝ) : ℂ))) -
        -Complex.I / (s : ℂ)).im =
      -(Real.pi * (1 + 2 * Real.exp (-2 * Real.pi * s) / (1 - Real.exp (-2 * Real.pi * s))) - 1 / s) := by
    have hcast1 : (1 + 2 * ((Real.exp (-2 * Real.pi * s) : ℝ) : ℂ) /
        (1 - ((Real.exp (-2 * Real.pi * s) : ℝ) : ℂ))) =
        ((1 + 2 * Real.exp (-2 * Real.pi * s) / (1 - Real.exp (-2 * Real.pi * s)) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hcast1]
    simp only [Complex.sub_im, Complex.mul_im, Complex.I_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.neg_im, Complex.I_im, mul_zero,
      zero_add, neg_mul, one_mul, Complex.div_ofReal_im]
    ring
  have hre_rhs :
      ((-Complex.I * (2 * (s : ℂ))) * ((∑' n : ℕ, 1 / (v + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ)).im =
      -(2 * s * ∑' n : ℕ, 1 / (v + ((n : ℝ) + 1) ^ 2)) := by
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_im, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, mul_zero, sub_zero, add_zero, zero_add, neg_mul, one_mul]
  rw [hre_lhs, hre_rhs] at him_eq
  have hden : 1 - Real.exp (-2 * Real.pi * s) ≠ 0 := by
    have : Real.exp (-2 * Real.pi * s) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
    linarith
  have hv_eq : v = s ^ 2 := hs2.symm
  rw [hv_eq]
  set E : ℝ := Real.exp (-2 * Real.pi * s)
  set T : ℝ := ∑' n : ℕ, 1 / (s ^ 2 + ((n : ℝ) + 1) ^ 2)
  have him_clean : Real.pi * (1 + 2 * E / (1 - E)) - 1 / s = 2 * s * T := by
    dsimp only [T]; rw [← hv_eq]; linarith
  field_simp [hs.ne', hden] at him_clean ⊢
  nlinarith

private lemma hasDerivAt_deriv_gThermal_tsum {v : ℝ} (hv : 0 < v) :
    HasDerivAt (deriv gThermal)
      (-Real.pi / (4 * v ^ ((3 : ℝ) / 2)) + 1 / (2 * v ^ 2) +
        ∑' n : ℕ, 1 / (v + ((n : ℝ) + 1) ^ 2) ^ 2) v := by
  let S : ℝ → ℝ := fun x => ∑' n : ℕ, 1 / (x + ((n : ℝ) + 1) ^ 2)
  have hS_deriv : HasDerivAt S (∑' n : ℕ, -(1 / (v + ((n : ℝ) + 1) ^ 2) ^ 2)) v := by
    let u : ℕ → ℝ := fun n => 1 / (((n : ℝ) + 1) ^ 4)
    have hu : Summable u := by
      have hp : Summable (fun n : ℕ => ((n : ℝ) ^ (4 : ℝ))⁻¹) :=
        Real.summable_nat_rpow_inv.mpr (by norm_num)
      refine (hp.comp_injective Nat.succ_injective).congr fun n => ?_
      simp only [u, Function.comp, Nat.cast_succ, one_div]
      congr 1; exact_mod_cast (Real.rpow_natCast ((n : ℝ) + 1) 4)
    have hf_sum : Summable (fun n : ℕ => 1 / (v + ((n : ℝ) + 1) ^ 2)) := by
      have hp : Summable (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) :=
        Real.summable_nat_rpow_inv.mpr (by norm_num)
      have h2 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
        refine (hp.comp_injective Nat.succ_injective).congr fun n => ?_
        simp only [Function.comp, Nat.cast_succ, one_div]
        congr 1; exact_mod_cast (Real.rpow_natCast ((n : ℝ) + 1) 2)
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h2
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    dsimp only [S]
    refine hasDerivAt_tsum_of_isPreconnected
      (g := fun (n : ℕ) (x : ℝ) => 1 / (x + ((n : ℝ) + 1) ^ 2))
      (g' := fun (n : ℕ) (x : ℝ) => -(1 / (x + ((n : ℝ) + 1) ^ 2) ^ 2))
      hu (isOpen_Ioi (a := (0 : ℝ)))
      (isPreconnected_Ioi (a := (0 : ℝ))) ?_ ?_ (Set.mem_Ioi.mpr hv) hf_sum (Set.mem_Ioi.mpr hv)
    · intro n x (hx : 0 < x)
      have hne : x + ((n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
      have h1 : HasDerivAt (fun t : ℝ => t + ((n : ℝ) + 1) ^ 2) 1 x :=
        (hasDerivAt_id x).add_const _
      convert h1.inv hne using 1
      · ext t; simp [one_div]
      · ring
    · intro n x (hx : 0 < x)
      rw [Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
      dsimp only [u]
      have hge : ((n : ℝ) + 1) ^ 4 ≤ (x + ((n : ℝ) + 1) ^ 2) ^ 2 := by
        have h1 : ((n : ℝ) + 1) ^ 2 ≤ x + ((n : ℝ) + 1) ^ 2 := by linarith
        nlinarith [sq_nonneg ((n : ℝ) + 1)]
      exact one_div_le_one_div_of_le (by positivity) hge
  have hterm1 : HasDerivAt (fun x : ℝ => Real.pi / (2 * Real.sqrt x))
      (-Real.pi / (4 * v ^ ((3 : ℝ) / 2))) v := by
    have hsq := Real.hasDerivAt_sqrt hv.ne'
    have hden : HasDerivAt (fun x : ℝ => 2 * Real.sqrt x) (2 * (1 / (2 * Real.sqrt v))) v :=
      hsq.const_mul 2
    have hne : 2 * Real.sqrt v ≠ 0 := by positivity
    convert (hden.inv hne).const_mul Real.pi using 1
    · ext x; simp [div_eq_mul_inv]
    · have hv32 : v ^ ((3 : ℝ) / 2) = v * Real.sqrt v := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hv.le (by norm_num)]; norm_num
      rw [hv32]
      have hsq2 : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv.le
      field_simp [hv.ne', (Real.sqrt_pos.mpr hv).ne']
      nlinarith
  have hterm2 : HasDerivAt (fun x : ℝ => 1 / (2 * x)) (-(1 / (2 * v ^ 2))) v := by
    have h1 := ((hasDerivAt_inv hv.ne').const_mul (2 : ℝ)⁻¹)
    convert h1 using 1
    · ext x; field_simp
    · field_simp [hv.ne']
  have hcomb := (hterm1.fun_sub hterm2).fun_sub hS_deriv
  refine (hcomb.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [isOpen_Ioi.mem_nhds hv] with x hx
    exact deriv_gThermal_eq_tsum hx
  · rw [tsum_neg]; ring

private lemma hasDerivAt_deriv_gThermal_exp {v : ℝ} (hv : 0 < v) :
    HasDerivAt (deriv gThermal)
      (Real.pi / (2 * v ^ ((3 : ℝ) / 2)) *
          (Real.exp (-2 * Real.pi * Real.sqrt v) / (1 - Real.exp (-2 * Real.pi * Real.sqrt v))) +
        Real.pi ^ 2 / v *
          (Real.exp (-2 * Real.pi * Real.sqrt v) / (1 - Real.exp (-2 * Real.pi * Real.sqrt v)) ^ 2)) v := by
  have hsq_pos : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hne : 1 - Real.exp (-2 * Real.pi * Real.sqrt v) ≠ 0 := by
    have : Real.exp (-2 * Real.pi * Real.sqrt v) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
    linarith
  have h1 : HasDerivAt (fun x : ℝ => -Real.pi / Real.sqrt x)
      (Real.pi / (2 * v ^ ((3 : ℝ) / 2))) v := by
    have hsq := Real.hasDerivAt_sqrt hv.ne'
    convert (hsq.inv hsq_pos.ne').const_mul (-Real.pi) using 1
    · ext x; simp [div_eq_mul_inv]
    · have hv32 : v ^ ((3 : ℝ) / 2) = v * Real.sqrt v := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hv.le (by norm_num)]; norm_num
      rw [hv32]
      have hsq2 : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv.le
      field_simp [hv.ne', hsq_pos.ne']
      nlinarith
  have h2 : HasDerivAt
      (fun x : ℝ => Real.exp (-2 * Real.pi * Real.sqrt x) / (1 - Real.exp (-2 * Real.pi * Real.sqrt x)))
      ((-Real.pi / Real.sqrt v) * Real.exp (-2 * Real.pi * Real.sqrt v) /
        (1 - Real.exp (-2 * Real.pi * Real.sqrt v)) ^ 2) v := by
    have hexp_arg : HasDerivAt (fun x : ℝ => -2 * Real.pi * Real.sqrt x)
        (-2 * Real.pi * (1 / (2 * Real.sqrt v))) v :=
      (Real.hasDerivAt_sqrt hv.ne').const_mul (-2 * Real.pi)
    have he := hexp_arg.exp
    have hden : HasDerivAt (fun x : ℝ => 1 - Real.exp (-2 * Real.pi * Real.sqrt x))
        (-(Real.exp (-2 * Real.pi * Real.sqrt v) * (-2 * Real.pi * (1 / (2 * Real.sqrt v))))) v := by
      simpa using (hasDerivAt_const v (1 : ℝ)).fun_sub he
    convert he.div hden hne using 1
    field_simp [hsq_pos.ne', hne]
    ring
  refine ((h1.fun_mul h2).congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [isOpen_Ioi.mem_nhds hv] with x hx
    exact (hasDerivAt_gThermal hx).deriv
  · have hsq2 : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv.le
    have hv32 : v ^ ((3 : ℝ) / 2) = v * Real.sqrt v := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hv.le (by norm_num)]; norm_num
    rw [hv32]
    field_simp [hv.ne', hsq_pos.ne', hne]
    congr 1
    linear_combination -2 * Real.pi * hsq2

/-! #### Elementary Closed-Form Momentum Integrals -/

private lemma integrable_and_integral_rpow_neg_three_halves {a : ℝ} (ha : 0 < a) :
    Integrable (fun p : ℝ => (p ^ 2 + a) ^ (-(3 : ℝ) / 2)) ∧
      ∫ p : ℝ, (p ^ 2 + a) ^ (-(3 : ℝ) / 2) = 2 / a := by
  let F : ℝ → ℝ := fun p => p / (a * Real.sqrt (p ^ 2 + a))
  have hderiv : ∀ p : ℝ, HasDerivAt F ((p ^ 2 + a) ^ (-(3 : ℝ) / 2)) p := by
    intro p
    have hpos : 0 < p ^ 2 + a := by positivity
    have hsq : 0 < Real.sqrt (p ^ 2 + a) := Real.sqrt_pos.mpr hpos
    have hinner : HasDerivAt (fun x : ℝ => x ^ 2 + a) (2 * p) p := by
      simpa using (hasDerivAt_pow 2 p).add_const a
    have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (x ^ 2 + a))
        ((1 / (2 * Real.sqrt (p ^ 2 + a))) * (2 * p)) p :=
      (Real.hasDerivAt_sqrt hpos.ne').comp p hinner
    have hden := hsqrt.const_mul a
    have hdiv := (hasDerivAt_id p).fun_div hden (mul_ne_zero ha.ne' hsq.ne')
    refine hdiv.congr_deriv ?_
    have h32 : (p ^ 2 + a) ^ (-(3 : ℝ) / 2) = ((p ^ 2 + a) * Real.sqrt (p ^ 2 + a))⁻¹ := by
      rw [neg_div, Real.rpow_neg hpos.le, Real.sqrt_eq_rpow,
        ← Real.rpow_one_add' hpos.le (by norm_num)]
      norm_num
    rw [h32]
    have hsq2 : Real.sqrt (p ^ 2 + a) ^ 2 = p ^ 2 + a := Real.sq_sqrt hpos.le
    simp only [id_eq]
    field_simp [ha.ne', hpos.ne', hsq.ne']
    nlinarith
  have htend_top : Tendsto F atTop (𝓝 (1 / a)) := by
    have hratio : ∀ᶠ p : ℝ in atTop, F p = (1 / a) * (1 + a / p ^ 2) ^ (-(1 : ℝ) / 2) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp
      dsimp only [F]
      have hfac : p ^ 2 + a = p ^ 2 * (1 + a / p ^ 2) := by field_simp [hp.ne']
      rw [hfac, Real.sqrt_mul (sq_nonneg p), Real.sqrt_sq hp.le, Real.sqrt_eq_rpow, neg_div,
        Real.rpow_neg (by positivity)]
      field_simp [ha.ne', hp.ne']
    rw [tendsto_congr' hratio]
    have hinv : Tendsto (fun p : ℝ => a / p ^ 2) atTop (𝓝 0) := by
      have hp2 : Tendsto (fun p : ℝ => p ^ 2) atTop atTop :=
        (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
      exact tendsto_const_nhds.div_atTop hp2
    have h1 : Tendsto (fun p : ℝ => 1 + a / p ^ 2) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hinv
    have h2 : Tendsto (fun p : ℝ => (1 + a / p ^ 2) ^ (-(1 : ℝ) / 2)) atTop (𝓝 ((1 : ℝ) ^ (-(1 : ℝ) / 2))) :=
      (Real.continuousAt_rpow_const 1 (-(1 : ℝ) / 2) (Or.inl one_ne_zero)).tendsto.comp h1
    simpa using h2.const_mul (1 / a)
  have htend_bot : Tendsto F atBot (𝓝 (-(1 / a))) := by
    have hodd : ∀ p : ℝ, F (-p) = -F p := by intro p; simp [F]; ring
    have hcomp : Tendsto (fun p : ℝ => -F (-p)) atBot (𝓝 (-(1 / a))) :=
      (htend_top.comp tendsto_neg_atBot_atTop).neg
    refine hcomp.congr fun p => ?_
    rw [hodd, neg_neg]
  have hint : Integrable (fun p : ℝ => (p ^ 2 + a) ^ (-(3 : ℝ) / 2)) := by
    let C : ℝ := (Real.sqrt a * min 1 a)⁻¹
    have hmin_pos : 0 < min 1 a := lt_min zero_lt_one ha
    refine (integrable_inv_one_add_sq.const_mul C).mono'
      ((Continuous.rpow_const (by fun_prop) fun p => Or.inl (by positivity)).aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    have hpos : 0 < p ^ 2 + a := by positivity
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h32 : (p ^ 2 + a) ^ (-(3 : ℝ) / 2) = ((p ^ 2 + a) * Real.sqrt (p ^ 2 + a))⁻¹ := by
      rw [neg_div, Real.rpow_neg hpos.le, Real.sqrt_eq_rpow,
        ← Real.rpow_one_add' hpos.le (by norm_num)]
      norm_num
    rw [h32]
    have hge1 : Real.sqrt a ≤ Real.sqrt (p ^ 2 + a) := Real.sqrt_le_sqrt (by linarith [sq_nonneg p])
    have hge2 : min 1 a * (1 + p ^ 2) ≤ p ^ 2 + a := by
      have hm1 : min 1 a ≤ 1 := min_le_left 1 a
      have hm2 : min 1 a ≤ a := min_le_right 1 a
      nlinarith [sq_nonneg p]
    have hprod : Real.sqrt a * min 1 a * (1 + p ^ 2) ≤ (p ^ 2 + a) * Real.sqrt (p ^ 2 + a) := by
      calc Real.sqrt a * min 1 a * (1 + p ^ 2)
          = (min 1 a * (1 + p ^ 2)) * Real.sqrt a := by ring
        _ ≤ (p ^ 2 + a) * Real.sqrt (p ^ 2 + a) :=
            mul_le_mul hge2 hge1 (Real.sqrt_nonneg a) hpos.le
    dsimp only [C]
    rw [← mul_inv]
    exact inv_anti₀ (mul_pos (mul_pos (Real.sqrt_pos.mpr ha) hmin_pos) (by linarith [sq_nonneg p])) hprod
  have hval := integral_of_hasDerivAt_of_tendsto hderiv hint htend_bot htend_top
  exact ⟨hint, by rw [hval]; ring⟩

private lemma integrable_and_integral_inv_sq_add_sq {a : ℝ} (ha : 0 < a) :
    Integrable (fun p : ℝ => 1 / (p ^ 2 + a) ^ 2) ∧
      ∫ p : ℝ, 1 / (p ^ 2 + a) ^ 2 = Real.pi / (2 * a ^ ((3 : ℝ) / 2)) := by
  let s : ℝ := Real.sqrt a
  have hs : 0 < s := Real.sqrt_pos.mpr ha
  have hs2 : s ^ 2 = a := Real.sq_sqrt ha.le
  let F : ℝ → ℝ := fun p => (2 * a)⁻¹ * (p / (p ^ 2 + a) + s⁻¹ * Real.arctan (p / s))
  have hderiv : ∀ p : ℝ, HasDerivAt F (1 / (p ^ 2 + a) ^ 2) p := by
    intro p
    have hpos : 0 < p ^ 2 + a := by positivity
    have h1 : HasDerivAt (fun x : ℝ => x / (x ^ 2 + a))
        ((1 * (p ^ 2 + a) - p * (2 * p)) / (p ^ 2 + a) ^ 2) p := by
      have hd : HasDerivAt (fun x : ℝ => x ^ 2 + a) (2 * p) p := by
        simpa using (hasDerivAt_pow 2 p).add_const a
      exact (hasDerivAt_id p).div hd hpos.ne'
    have h2 : HasDerivAt (fun x : ℝ => s⁻¹ * Real.arctan (x / s))
        (s⁻¹ * ((1 + (p / s) ^ 2)⁻¹ * s⁻¹)) p := by
      have hd : HasDerivAt (fun x : ℝ => x / s) (1 / s) p :=
        (hasDerivAt_id p).div_const s
      have harc := hd.arctan
      convert harc.const_mul s⁻¹ using 1
      ring
    convert (h1.add h2).const_mul (2 * a)⁻¹ using 1
    have hden2 : 1 + (p / s) ^ 2 ≠ 0 := by positivity
    field_simp [ha.ne', hs.ne', hpos.ne', hden2]
    nlinarith [hs2]
  have htend_top : Tendsto F atTop (𝓝 (Real.pi / (4 * a ^ ((3 : ℝ) / 2)))) := by
    have h1 : Tendsto (fun p : ℝ => p / (p ^ 2 + a)) atTop (𝓝 0) := by
      have hle : ∀ᶠ p : ℝ in atTop, p / (p ^ 2 + a) ≤ 1 / p := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp
        rw [div_le_div_iff₀ (by positivity) hp]
        nlinarith
      have hge : ∀ᶠ p : ℝ in atTop, (0 : ℝ) ≤ p / (p ^ 2 + a) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp; positivity
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_const_nhds.div_atTop tendsto_id) hge hle
    have h2 : Tendsto (fun p : ℝ => s⁻¹ * Real.arctan (p / s)) atTop (𝓝 (s⁻¹ * (Real.pi / 2))) := by
      have hdiv : Tendsto (fun p : ℝ => p / s) atTop atTop :=
        Tendsto.atTop_div_const hs tendsto_id
      exact ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hdiv).const_mul s⁻¹
    have hsum := (h1.add h2).const_mul (2 * a)⁻¹
    convert hsum using 1
    have ha32 : a ^ ((3 : ℝ) / 2) = a * s := by
      dsimp only [s]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' ha.le (by norm_num)]; norm_num
    rw [ha32]
    field_simp [ha.ne', hs.ne']
    ring
  have htend_bot : Tendsto F atBot (𝓝 (-(Real.pi / (4 * a ^ ((3 : ℝ) / 2))))) := by
    have hodd : ∀ p : ℝ, F (-p) = -F p := by
      intro p; simp only [F, neg_sq, neg_div, Real.arctan_neg]; ring
    have hcomp : Tendsto (fun p : ℝ => -F (-p)) atBot (𝓝 (-(Real.pi / (4 * a ^ ((3 : ℝ) / 2))))) :=
      (htend_top.comp tendsto_neg_atBot_atTop).neg
    refine hcomp.congr fun p => ?_
    rw [hodd, neg_neg]
  have hint : Integrable (fun p : ℝ => 1 / (p ^ 2 + a) ^ 2) := by
    let C : ℝ := (a * min 1 a)⁻¹
    have hmin_pos : 0 < min 1 a := lt_min zero_lt_one ha
    refine (integrable_inv_one_add_sq.const_mul C).mono'
      ((continuous_const.div (by fun_prop) fun p => by positivity).aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), one_div]
    have hge1 : a ≤ p ^ 2 + a := by linarith [sq_nonneg p]
    have hge2 : min 1 a * (1 + p ^ 2) ≤ p ^ 2 + a := by
      have hm1 : min 1 a ≤ 1 := min_le_left 1 a
      have hm2 : min 1 a ≤ a := min_le_right 1 a
      nlinarith [sq_nonneg p]
    have hprod : a * min 1 a * (1 + p ^ 2) ≤ (p ^ 2 + a) ^ 2 := by
      have h0 : 0 ≤ min 1 a * (1 + p ^ 2) := mul_nonneg hmin_pos.le (by linarith [sq_nonneg p])
      calc a * min 1 a * (1 + p ^ 2) = a * (min 1 a * (1 + p ^ 2)) := by ring
        _ ≤ (p ^ 2 + a) * (p ^ 2 + a) := mul_le_mul hge1 hge2 h0 (by linarith [sq_nonneg p])
        _ = (p ^ 2 + a) ^ 2 := by ring
    dsimp only [C]
    rw [← mul_inv]
    exact inv_anti₀ (mul_pos (mul_pos ha hmin_pos) (by linarith [sq_nonneg p])) hprod
  have hval := integral_of_hasDerivAt_of_tendsto hderiv hint htend_bot htend_top
  exact ⟨hint, by rw [hval]; ring⟩

/-! #### Differentiation Under the Integral Sign for `H1`, `H1'`, and `H3` -/

private lemma hasDerivAt_H1 {y : ℝ} (hy : 0 < y) :
    HasDerivAt H1 ((2 * Real.pi)⁻¹ * ∫ p : ℝ, deriv gThermal (p ^ 2 + y)) y := by
  let y₀ : ℝ := y / 2
  have hy₀ : 0 < y₀ := half_pos hy
  let C : ℝ := (Real.pi / Real.sqrt y₀) * (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹
  let bound : ℝ → ℝ := fun p => C * Real.exp (-(2 * Real.pi) * |p|)
  have hbound_int : Integrable bound := by
    simpa [bound, pow_zero, one_mul] using
      (integrable_pow_mul_exp_neg_abs (a := 2 * Real.pi) (by positivity) 0).const_mul C
  have hderiv_int : HasDerivAt (fun t : ℝ => ∫ p : ℝ, gThermal (p ^ 2 + t))
      (∫ p : ℝ, deriv gThermal (p ^ 2 + y)) y := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun t p => gThermal (p ^ 2 + t))
      (F' := fun t p => deriv gThermal (p ^ 2 + t))
      (bound := bound)
      (Metric.ball_mem_nhds y (half_pos hy))
      ?_ ?_ ?_ ?_ hbound_int ?_).2
    · filter_upwards [Metric.ball_mem_nhds y (half_pos hy)] with t ht
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      have ht_pos : 0 < t := by linarith
      exact (integrable_gThermal_comp ht_pos).aestronglyMeasurable
    · exact integrable_gThermal_comp hy
    · have hcont : Continuous (fun p : ℝ => deriv gThermal (p ^ 2 + y)) := by
        have heq : (fun p : ℝ => deriv gThermal (p ^ 2 + y)) =
            fun p : ℝ => -Real.pi / Real.sqrt (p ^ 2 + y) *
              (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
                (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) := by
          ext p; exact (hasDerivAt_gThermal (by positivity)).deriv
        rw [heq]
        refine Continuous.mul ?_ (Continuous.div (by fun_prop) (by fun_prop) fun p => ?_)
        · exact continuous_const.div (by fun_prop) fun p => (Real.sqrt_pos.mpr (by positivity)).ne'
        · have hsq : 0 < Real.sqrt (p ^ 2 + y) := Real.sqrt_pos.mpr (by positivity)
          have he : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) < 1 := by
            rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
          linarith
      exact hcont.aestronglyMeasurable
    · filter_upwards with p
      intro t ht
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      have ht_ge : y₀ ≤ t := by dsimp only [y₀]; linarith
      have hv_ge : y₀ ≤ p ^ 2 + t := by linarith [sq_nonneg p]
      have hv_pos : 0 < p ^ 2 + t := lt_of_lt_of_le hy₀ hv_ge
      rw [(hasDerivAt_gThermal hv_pos).deriv, Real.norm_eq_abs]
      have hsq_ge : Real.sqrt y₀ ≤ Real.sqrt (p ^ 2 + t) := Real.sqrt_le_sqrt hv_ge
      have hsq_p : |p| ≤ Real.sqrt (p ^ 2 + t) := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
      have he_le1 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) ≤
          Real.exp (-2 * Real.pi * Real.sqrt y₀) := by
        apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
      have he_le2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) ≤
          Real.exp (-(2 * Real.pi) * |p|) := by
        apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
      have hden0 : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt y₀) := by
        have : Real.exp (-2 * Real.pi * Real.sqrt y₀) < 1 := by
          rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hy₀]
        linarith
      have hden : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) := by linarith
      have hfrac_nn : 0 ≤ Real.pi / Real.sqrt (p ^ 2 + t) *
          (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)))) := by positivity
      have habs : |-Real.pi / Real.sqrt (p ^ 2 + t) *
          (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))))| =
          Real.pi / Real.sqrt (p ^ 2 + t) *
            (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
              (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)))) := by
        have : -Real.pi / Real.sqrt (p ^ 2 + t) *
            (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
              (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)))) =
            -(Real.pi / Real.sqrt (p ^ 2 + t) *
              (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
                (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))))) := by ring
        rw [this, abs_neg, abs_of_nonneg hfrac_nn]
      rw [habs]
      have h1 : Real.pi / Real.sqrt (p ^ 2 + t) ≤ Real.pi / Real.sqrt y₀ :=
        div_le_div_of_nonneg_left Real.pi_pos.le (Real.sqrt_pos.mpr hy₀) hsq_ge
      have h2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
          (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))) ≤
          (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹ * Real.exp (-(2 * Real.pi) * |p|) := by
        rw [inv_mul_eq_div]
        calc Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
              (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)))
            ≤ Real.exp (-(2 * Real.pi) * |p|) /
                (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))) :=
              div_le_div_of_nonneg_right he_le2 hden.le
          _ ≤ Real.exp (-(2 * Real.pi) * |p|) /
                (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀)) :=
              div_le_div_of_nonneg_left (Real.exp_pos _).le hden0 (by linarith)
      dsimp only [bound, C]
      calc Real.pi / Real.sqrt (p ^ 2 + t) *
            (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
              (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))))
          ≤ (Real.pi / Real.sqrt y₀) *
              ((1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹ * Real.exp (-(2 * Real.pi) * |p|)) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (Real.pi / Real.sqrt y₀) * (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹ *
              Real.exp (-(2 * Real.pi) * |p|) := by ring
    · filter_upwards with p
      intro t ht
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      have hv_pos : 0 < p ^ 2 + t := by linarith [sq_nonneg p]
      rw [(hasDerivAt_gThermal hv_pos).deriv]
      exact (hasDerivAt_gThermal hv_pos).comp_const_add (p ^ 2) t
  exact hderiv_int.const_mul (2 * Real.pi)⁻¹

private lemma hasDerivAt_deriv_H1 {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv H1) ((2 * Real.pi)⁻¹ * ∫ p : ℝ, iteratedDeriv 2 gThermal (p ^ 2 + y)) y := by
  let y₀ : ℝ := y / 2
  have hy₀ : 0 < y₀ := half_pos hy
  have hden0 : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt y₀) := by
    have : Real.exp (-2 * Real.pi * Real.sqrt y₀) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hy₀]
    linarith
  let C : ℝ := Real.pi / (2 * y₀ ^ ((3 : ℝ) / 2)) * (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹ +
    Real.pi ^ 2 / y₀ * ((1 - Real.exp (-2 * Real.pi * Real.sqrt y₀)) ^ 2)⁻¹
  let bound : ℝ → ℝ := fun p => C * Real.exp (-(2 * Real.pi) * |p|)
  have hbound_int : Integrable bound := by
    simpa [bound, pow_zero, one_mul] using
      (integrable_pow_mul_exp_neg_abs (a := 2 * Real.pi) (by positivity) 0).const_mul C
  have h2_eq : ∀ v : ℝ, 0 < v →
      iteratedDeriv 2 gThermal v =
        Real.pi / (2 * v ^ ((3 : ℝ) / 2)) *
            (Real.exp (-2 * Real.pi * Real.sqrt v) / (1 - Real.exp (-2 * Real.pi * Real.sqrt v))) +
          Real.pi ^ 2 / v *
            (Real.exp (-2 * Real.pi * Real.sqrt v) / (1 - Real.exp (-2 * Real.pi * Real.sqrt v)) ^ 2) := by
    intro v hv
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (hasDerivAt_deriv_gThermal_exp hv).deriv
  have hint_g1 : ∀ t : ℝ, 0 < t → Integrable (fun p : ℝ => deriv gThermal (p ^ 2 + t)) := by
    intro t ht
    let Ct : ℝ := (Real.pi / Real.sqrt t) * (1 - Real.exp (-2 * Real.pi * Real.sqrt t))⁻¹
    have hexp := (integrable_pow_mul_exp_neg_abs (a := 2 * Real.pi) (by positivity) 0).const_mul Ct
    refine hexp.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hcont : Continuous (fun p : ℝ => deriv gThermal (p ^ 2 + t)) := by
        have heq : (fun p : ℝ => deriv gThermal (p ^ 2 + t)) =
            fun p : ℝ => -Real.pi / Real.sqrt (p ^ 2 + t) *
              (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
                (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)))) := by
          ext p; exact (hasDerivAt_gThermal (by positivity)).deriv
        rw [heq]
        refine Continuous.mul ?_ (Continuous.div (by fun_prop) (by fun_prop) fun p => ?_)
        · exact continuous_const.div (by fun_prop) fun p => (Real.sqrt_pos.mpr (by positivity)).ne'
        · have hsq : 0 < Real.sqrt (p ^ 2 + t) := Real.sqrt_pos.mpr (by positivity)
          have he : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) < 1 := by
            rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
          linarith
      exact hcont.aestronglyMeasurable
    · have hv_ge : t ≤ p ^ 2 + t := by linarith [sq_nonneg p]
      have hv_pos : 0 < p ^ 2 + t := by positivity
      rw [(hasDerivAt_gThermal hv_pos).deriv, Real.norm_eq_abs]
      have hsq_ge : Real.sqrt t ≤ Real.sqrt (p ^ 2 + t) := Real.sqrt_le_sqrt hv_ge
      have hsq_p : |p| ≤ Real.sqrt (p ^ 2 + t) := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
      have he_le1 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) ≤
          Real.exp (-2 * Real.pi * Real.sqrt t) := by
        apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
      have he_le2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) ≤
          Real.exp (-(2 * Real.pi) * |p|) := by
        apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
      have hdent : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt t) := by
        have : Real.exp (-2 * Real.pi * Real.sqrt t) < 1 := by
          rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr ht]
        linarith
      have hden : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) := by linarith
      have habs : |-Real.pi / Real.sqrt (p ^ 2 + t) *
          (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))))| =
          Real.pi / Real.sqrt (p ^ 2 + t) *
            (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
              (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)))) := by
        have hnn : 0 ≤ Real.pi / Real.sqrt (p ^ 2 + t) *
            (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
              (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)))) := by positivity
        have : -Real.pi / Real.sqrt (p ^ 2 + t) *
            (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
              (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)))) =
            -(Real.pi / Real.sqrt (p ^ 2 + t) *
              (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
                (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))))) := by ring
        rw [this, abs_neg, abs_of_nonneg hnn]
      rw [habs]
      have h1 : Real.pi / Real.sqrt (p ^ 2 + t) ≤ Real.pi / Real.sqrt t :=
        div_le_div_of_nonneg_left Real.pi_pos.le (Real.sqrt_pos.mpr ht) hsq_ge
      have h2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
          (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))) ≤
          (1 - Real.exp (-2 * Real.pi * Real.sqrt t))⁻¹ * Real.exp (-(2 * Real.pi) * |p|) := by
        rw [inv_mul_eq_div]
        exact (div_le_div_of_nonneg_right he_le2 hden.le).trans
          (div_le_div_of_nonneg_left (Real.exp_pos _).le hdent (by linarith))
      simp only [pow_zero, one_mul, Ct]
      calc Real.pi / Real.sqrt (p ^ 2 + t) *
            (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
              (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))))
          ≤ (Real.pi / Real.sqrt t) *
              ((1 - Real.exp (-2 * Real.pi * Real.sqrt t))⁻¹ * Real.exp (-(2 * Real.pi) * |p|)) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (Real.pi / Real.sqrt t) * (1 - Real.exp (-2 * Real.pi * Real.sqrt t))⁻¹ *
              Real.exp (-(2 * Real.pi) * |p|) := by ring
  have hderiv_int : HasDerivAt (fun t : ℝ => ∫ p : ℝ, deriv gThermal (p ^ 2 + t))
      (∫ p : ℝ, iteratedDeriv 2 gThermal (p ^ 2 + y)) y := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun t p => deriv gThermal (p ^ 2 + t))
      (F' := fun t p => iteratedDeriv 2 gThermal (p ^ 2 + t))
      (bound := bound)
      (Metric.ball_mem_nhds y (half_pos hy))
      ?_ ?_ ?_ ?_ hbound_int ?_).2
    · filter_upwards [Metric.ball_mem_nhds y (half_pos hy)] with t ht
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      exact (hint_g1 t (by linarith)).aestronglyMeasurable
    · exact hint_g1 y hy
    · have hcont : Continuous (fun p : ℝ => iteratedDeriv 2 gThermal (p ^ 2 + y)) := by
        have heq : (fun p : ℝ => iteratedDeriv 2 gThermal (p ^ 2 + y)) =
            fun p : ℝ => Real.pi / (2 * (p ^ 2 + y) ^ ((3 : ℝ) / 2)) *
                (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
                  (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) +
              Real.pi ^ 2 / (p ^ 2 + y) *
                (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
                  (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) ^ 2) := by
          ext p; exact h2_eq (p ^ 2 + y) (by positivity)
        rw [heq]
        have hden_ne : ∀ p : ℝ, 1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≠ 0 := fun p => by
          have : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) < 1 := by
            rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr (by positivity : 0 < p ^ 2 + y)]
          linarith
        refine Continuous.add ?_ ?_
        · refine (continuous_const.div ?_ fun p => by positivity).mul
            (Continuous.div (by fun_prop) (by fun_prop) hden_ne)
          exact continuous_const.mul (Continuous.rpow_const (by fun_prop) fun p => Or.inl (by positivity))
        · refine (continuous_const.div (by fun_prop) fun p => by positivity).mul
            (Continuous.div (by fun_prop) (by fun_prop) fun p => pow_ne_zero 2 (hden_ne p))
      exact hcont.aestronglyMeasurable
    · filter_upwards with p
      intro t ht
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      have ht_ge : y₀ ≤ t := by dsimp only [y₀]; linarith
      have hv_ge : y₀ ≤ p ^ 2 + t := by linarith [sq_nonneg p]
      have hv_pos : 0 < p ^ 2 + t := lt_of_lt_of_le hy₀ hv_ge
      rw [h2_eq (p ^ 2 + t) hv_pos]
      have hsq_ge : Real.sqrt y₀ ≤ Real.sqrt (p ^ 2 + t) := Real.sqrt_le_sqrt hv_ge
      have hsq_p : |p| ≤ Real.sqrt (p ^ 2 + t) := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
      have he_le1 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) ≤
          Real.exp (-2 * Real.pi * Real.sqrt y₀) := by
        apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
      have he_le2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) ≤
          Real.exp (-(2 * Real.pi) * |p|) := by
        apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
      have hden : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) := by linarith
      have hnn : 0 ≤ Real.pi / (2 * (p ^ 2 + t) ^ ((3 : ℝ) / 2)) *
            (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
              (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)))) +
          Real.pi ^ 2 / (p ^ 2 + t) *
            (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
              (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))) ^ 2) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hrpow_le : y₀ ^ ((3 : ℝ) / 2) ≤ (p ^ 2 + t) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow hy₀.le hv_ge (by norm_num)
      have ht1 : Real.pi / (2 * (p ^ 2 + t) ^ ((3 : ℝ) / 2)) *
          (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)))) ≤
          Real.pi / (2 * y₀ ^ ((3 : ℝ) / 2)) * (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹ *
            Real.exp (-(2 * Real.pi) * |p|) := by
        have ha1 : Real.pi / (2 * (p ^ 2 + t) ^ ((3 : ℝ) / 2)) ≤ Real.pi / (2 * y₀ ^ ((3 : ℝ) / 2)) :=
          div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by linarith)
        have ha2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))) ≤
            (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹ * Real.exp (-(2 * Real.pi) * |p|) := by
          rw [inv_mul_eq_div]
          exact (div_le_div_of_nonneg_right he_le2 hden.le).trans
            (div_le_div_of_nonneg_left (Real.exp_pos _).le hden0 (by linarith))
        calc Real.pi / (2 * (p ^ 2 + t) ^ ((3 : ℝ) / 2)) *
              (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
                (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))))
            ≤ Real.pi / (2 * y₀ ^ ((3 : ℝ) / 2)) *
                ((1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹ * Real.exp (-(2 * Real.pi) * |p|)) :=
              mul_le_mul ha1 ha2 (by positivity) (by positivity)
          _ = _ := by ring
      have ht2 : Real.pi ^ 2 / (p ^ 2 + t) *
          (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))) ^ 2) ≤
          Real.pi ^ 2 / y₀ * ((1 - Real.exp (-2 * Real.pi * Real.sqrt y₀)) ^ 2)⁻¹ *
            Real.exp (-(2 * Real.pi) * |p|) := by
        have hb1 : Real.pi ^ 2 / (p ^ 2 + t) ≤ Real.pi ^ 2 / y₀ :=
          div_le_div_of_nonneg_left (by positivity) hy₀ hv_ge
        have hden_sq : (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀)) ^ 2 ≤
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))) ^ 2 := by nlinarith
        have hb2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))) ^ 2 ≤
            ((1 - Real.exp (-2 * Real.pi * Real.sqrt y₀)) ^ 2)⁻¹ * Real.exp (-(2 * Real.pi) * |p|) := by
          rw [inv_mul_eq_div]
          exact (div_le_div_of_nonneg_right he_le2 (by positivity)).trans
            (div_le_div_of_nonneg_left (Real.exp_pos _).le (pow_pos hden0 2) hden_sq)
        calc Real.pi ^ 2 / (p ^ 2 + t) *
              (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
                (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))) ^ 2)
            ≤ Real.pi ^ 2 / y₀ *
                (((1 - Real.exp (-2 * Real.pi * Real.sqrt y₀)) ^ 2)⁻¹ * Real.exp (-(2 * Real.pi) * |p|)) :=
              mul_le_mul hb1 hb2 (by positivity) (by positivity)
          _ = _ := by ring
      dsimp only [bound, C]
      linarith
    · filter_upwards with p
      intro t ht
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      have hv_pos : 0 < p ^ 2 + t := by linarith [sq_nonneg p]
      rw [h2_eq (p ^ 2 + t) hv_pos]
      exact (hasDerivAt_deriv_gThermal_exp hv_pos).comp_const_add (p ^ 2) t
  have hscaled := hderiv_int.const_mul (2 * Real.pi)⁻¹
  refine hscaled.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht
  exact (hasDerivAt_H1 ht).deriv

/-- **Lemma 1 (Part 1, `H1''` Matsubara Identity)**:
For every `y > 0`,
`H₁''(y) = (1/4) ∑' n, (y + (n+1)²)^{-3/2} - 1/(4y) + 1/(8 y^{3/2})`. -/
theorem H1_deriv2 {y : ℝ} (hy : 0 < y) :
    iteratedDeriv 2 H1 y =
      (1 / 4 : ℝ) * ∑' n : ℕ, (y + ((n : ℝ) + 1) ^ 2) ^ (-(3 : ℝ) / 2) -
        1 / (4 * y) + 1 / (8 * y ^ ((3 : ℝ) / 2)) := by
  have h2eq : iteratedDeriv 2 H1 y = deriv (deriv H1) y := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2eq, (hasDerivAt_deriv_H1 hy).deriv]
  have hg2 : ∀ p : ℝ, iteratedDeriv 2 gThermal (p ^ 2 + y) =
      -Real.pi / (4 * (p ^ 2 + y) ^ ((3 : ℝ) / 2)) + 1 / (2 * (p ^ 2 + y) ^ 2) +
        ∑' n : ℕ, 1 / (p ^ 2 + y + ((n : ℝ) + 1) ^ 2) ^ 2 := by
    intro p
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (hasDerivAt_deriv_gThermal_tsum (by positivity)).deriv
  simp_rw [hg2]
  have hint1 : Integrable (fun p : ℝ => -Real.pi / (4 * (p ^ 2 + y) ^ ((3 : ℝ) / 2))) := by
    refine ((integrable_and_integral_rpow_neg_three_halves hy).1.const_mul (-Real.pi / 4)).congr
      (Eventually.of_forall fun p => ?_)
    dsimp only
    rw [show (-(3 : ℝ) / 2) = -((3 : ℝ) / 2) by ring, Real.rpow_neg (by positivity)]; ring
  have hint2 : Integrable (fun p : ℝ => 1 / (2 * (p ^ 2 + y) ^ 2)) := by
    refine ((integrable_and_integral_inv_sq_add_sq hy).1.const_mul (1 / 2 : ℝ)).congr
      (Eventually.of_forall fun p => ?_)
    dsimp only; field_simp
  let fn : ℕ → ℝ → ℝ := fun n p => 1 / (p ^ 2 + (y + ((n : ℝ) + 1) ^ 2)) ^ 2
  have hfn_meas : ∀ n : ℕ, AEStronglyMeasurable (fn n) volume := fun n =>
    (continuous_const.div (by fun_prop) fun p => by positivity).aestronglyMeasurable
  have hfn_int : ∀ n : ℕ, Integrable (fn n) := fun n =>
    (integrable_and_integral_inv_sq_add_sq (by positivity : 0 < y + ((n : ℝ) + 1) ^ 2)).1
  have hfn_val : ∀ n : ℕ, ∫ p : ℝ, fn n p = Real.pi / (2 * (y + ((n : ℝ) + 1) ^ 2) ^ ((3 : ℝ) / 2)) := fun n =>
    (integrable_and_integral_inv_sq_add_sq (by positivity : 0 < y + ((n : ℝ) + 1) ^ 2)).2
  have hsum_val : Summable (fun n : ℕ => Real.pi / (2 * (y + ((n : ℝ) + 1) ^ 2) ^ ((3 : ℝ) / 2))) := by
    have hp : Summable (fun n : ℕ => ((n : ℝ) ^ (3 : ℝ))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    have h3 : Summable (fun n : ℕ => (Real.pi / 2) * ((n : ℝ) + 1) ^ (-(3 : ℝ))) := by
      refine ((hp.comp_injective Nat.succ_injective).congr fun n => ?_).mul_left (Real.pi / 2)
      simp only [Function.comp, Nat.cast_succ]
      rw [Real.rpow_neg (by positivity)]
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h3
    have hle : ((n : ℝ) + 1) ^ 2 ≤ y + ((n : ℝ) + 1) ^ 2 := by linarith
    have hrpow : ((n : ℝ) + 1) ^ (3 : ℝ) ≤ (y + ((n : ℝ) + 1) ^ 2) ^ ((3 : ℝ) / 2) := by
      have h1 : (((n : ℝ) + 1) ^ 2) ^ ((3 : ℝ) / 2) ≤ (y + ((n : ℝ) + 1) ^ 2) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) hle (by norm_num)
      have h2 : (((n : ℝ) + 1) ^ 2) ^ ((3 : ℝ) / 2) = ((n : ℝ) + 1) ^ (3 : ℝ) := by
        rw [← Real.rpow_natCast ((n : ℝ) + 1) 2, ← Real.rpow_mul (by positivity)]
        norm_num
      linarith
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv]
    calc Real.pi / (2 * (y + ((n : ℝ) + 1) ^ 2) ^ ((3 : ℝ) / 2))
        = (Real.pi / 2) / (y + ((n : ℝ) + 1) ^ 2) ^ ((3 : ℝ) / 2) := by ring
      _ ≤ (Real.pi / 2) / ((n : ℝ) + 1) ^ (3 : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hrpow
  have hlintegral_ne : ∑' n : ℕ, ∫⁻ p : ℝ, ‖fn n p‖ₑ ≠ ⊤ := by
    have heq : ∀ n : ℕ, ∫⁻ p : ℝ, ‖fn n p‖ₑ =
        ENNReal.ofReal (Real.pi / (2 * (y + ((n : ℝ) + 1) ^ 2) ^ ((3 : ℝ) / 2))) := by
      intro n
      rw [← hfn_val n, ← ofReal_integral_norm_eq_lintegral_eNorm (hfn_int n)]
      congr 1; apply integral_congr_ae; filter_upwards with p
      rw [Real.norm_eq_abs, abs_of_pos (by dsimp only [fn]; positivity)]
    simp_rw [heq]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum_val]
    exact ENNReal.ofReal_ne_top
  have htsum_eq : ∫ p : ℝ, ∑' n : ℕ, fn n p = ∑' n : ℕ, ∫ p : ℝ, fn n p :=
    MeasureTheory.integral_tsum hfn_meas hlintegral_ne
  have hint3 : Integrable (fun p : ℝ => ∑' n : ℕ, fn n p) := by
    have hsumm_p : ∀ p : ℝ, Summable (fun n : ℕ => fn n p) := by
      intro p
      have hp : Summable (fun n : ℕ => ((n : ℝ) ^ (4 : ℝ))⁻¹) :=
        Real.summable_nat_rpow_inv.mpr (by norm_num)
      have h4 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 4) := by
        refine (hp.comp_injective Nat.succ_injective).congr fun n => ?_
        simp only [Function.comp, Nat.cast_succ, one_div]
        congr 1; exact_mod_cast (Real.rpow_natCast ((n : ℝ) + 1) 4)
      refine Summable.of_nonneg_of_le (fun n => by dsimp only [fn]; positivity) (fun n => ?_) h4
      dsimp only [fn]
      have hge : ((n : ℝ) + 1) ^ 4 ≤ (p ^ 2 + (y + ((n : ℝ) + 1) ^ 2)) ^ 2 := by
        have h1 : ((n : ℝ) + 1) ^ 2 ≤ p ^ 2 + (y + ((n : ℝ) + 1) ^ 2) := by linarith [sq_nonneg p]
        nlinarith [sq_nonneg ((n : ℝ) + 1)]
      exact one_div_le_one_div_of_le (by positivity) hge
    have hmeas_sum : AEStronglyMeasurable (fun p : ℝ => ∑' n : ℕ, fn n p) volume :=
      aestronglyMeasurable_of_tendsto_ae atTop
        (fun N => Finset.aestronglyMeasurable_fun_sum _ fun n _ => hfn_meas n)
        (Eventually.of_forall fun p => (hsumm_p p).hasSum.tendsto_sum_nat)
    refine ⟨hmeas_sum, ?_⟩
    rw [hasFiniteIntegral_iff_eNorm]
    calc ∫⁻ p : ℝ, ‖∑' n : ℕ, fn n p‖ₑ
        ≤ ∫⁻ p : ℝ, ∑' n : ℕ, ‖fn n p‖ₑ :=
          lintegral_mono fun p => eNorm_tsum_le_tsum_eNorm
      _ = ∑' n : ℕ, ∫⁻ p : ℝ, ‖fn n p‖ₑ :=
          lintegral_tsum fun n => (hfn_meas n).eNorm
      _ < ⊤ := lt_top_iff_ne_top.mpr hlintegral_ne
  have hfn_rearr : ∀ p : ℝ, (∑' n : ℕ, 1 / (p ^ 2 + y + ((n : ℝ) + 1) ^ 2) ^ 2) = ∑' n : ℕ, fn n p := by
    intro p; apply tsum_congr; intro n; simp only [fn, add_assoc]
  simp_rw [hfn_rearr]
  have hint12 : Integrable (fun p : ℝ => -Real.pi / (4 * (p ^ 2 + y) ^ ((3 : ℝ) / 2)) + 1 / (2 * (p ^ 2 + y) ^ 2)) :=
    hint1.add hint2
  rw [MeasureTheory.integral_add hint12 hint3,
    MeasureTheory.integral_add hint1 hint2, htsum_eq]
  have hv1 : ∫ p : ℝ, -Real.pi / (4 * (p ^ 2 + y) ^ ((3 : ℝ) / 2)) = -Real.pi / (2 * y) := by
    have heq : (fun p : ℝ => -Real.pi / (4 * (p ^ 2 + y) ^ ((3 : ℝ) / 2))) =
        fun p : ℝ => (-Real.pi / 4) * (p ^ 2 + y) ^ (-(3 : ℝ) / 2) := by
      ext p; rw [show (-(3 : ℝ) / 2) = -((3 : ℝ) / 2) by ring, Real.rpow_neg (by positivity)]; ring
    rw [heq, MeasureTheory.integral_const_mul, (integrable_and_integral_rpow_neg_three_halves hy).2]
    ring
  have hv2 : ∫ p : ℝ, 1 / (2 * (p ^ 2 + y) ^ 2) = Real.pi / (4 * y ^ ((3 : ℝ) / 2)) := by
    have heq : (fun p : ℝ => 1 / (2 * (p ^ 2 + y) ^ 2)) =
        fun p : ℝ => (1 / 2 : ℝ) * (1 / (p ^ 2 + y) ^ 2) := by ext p; field_simp
    rw [heq, MeasureTheory.integral_const_mul, (integrable_and_integral_inv_sq_add_sq hy).2]
    ring
  have hv3 : ∑' n : ℕ, ∫ p : ℝ, fn n p =
      (Real.pi / 2) * ∑' n : ℕ, (y + ((n : ℝ) + 1) ^ 2) ^ (-(3 : ℝ) / 2) := by
    simp_rw [hfn_val]
    rw [← tsum_mul_left]
    apply tsum_congr; intro n
    rw [show (-(3 : ℝ) / 2) = -((3 : ℝ) / 2) by ring, Real.rpow_neg (by positivity)]
    ring
  rw [hv1, hv2, hv3]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]
  ring

/-- **Lemma 1 (Part 2, Dimensional Lifting Identity `H₃'(y) = -(4π)⁻¹ H₁(y)`)**: -/
theorem H3_deriv {y : ℝ} (hy : 0 < y) :
    HasDerivAt H3 (-(4 * Real.pi)⁻¹ * H1 y) y := by
  let y₀ : ℝ := y / 2
  have hy₀ : 0 < y₀ := half_pos hy
  let C : ℝ := (Real.pi / Real.sqrt y₀) * (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹
  let bound : ℝ → ℝ := fun p => C * (|p| ^ 2 * Real.exp (-(2 * Real.pi) * |p|))
  have hbound_int : IntegrableOn bound (Set.Ioi 0) :=
    ((integrable_pow_mul_exp_neg_abs (a := 2 * Real.pi) (by positivity) 2).const_mul C).integrableOn
  have hderiv_int : HasDerivAt (fun t : ℝ => ∫ p in Set.Ioi (0 : ℝ), p ^ 2 * gThermal (p ^ 2 + t))
      (∫ p in Set.Ioi (0 : ℝ), p ^ 2 * deriv gThermal (p ^ 2 + y)) y := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun t p => p ^ 2 * gThermal (p ^ 2 + t))
      (F' := fun t p => p ^ 2 * deriv gThermal (p ^ 2 + t))
      (bound := bound)
      (Metric.ball_mem_nhds y (half_pos hy))
      ?_ ?_ ?_ ?_ hbound_int ?_).2
    · filter_upwards [Metric.ball_mem_nhds y (half_pos hy)] with t ht
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      exact (integrableOn_sq_mul_gThermal (by linarith)).aestronglyMeasurable
    · exact integrableOn_sq_mul_gThermal hy
    · have hcont : Continuous (fun p : ℝ => p ^ 2 * deriv gThermal (p ^ 2 + y)) := by
        have heq : (fun p : ℝ => p ^ 2 * deriv gThermal (p ^ 2 + y)) =
            fun p : ℝ => p ^ 2 * (-Real.pi / Real.sqrt (p ^ 2 + y) *
              (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
                (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))))) := by
          ext p; rw [(hasDerivAt_gThermal (by positivity)).deriv]
        rw [heq]
        refine (continuous_pow 2).mul (Continuous.mul ?_ (Continuous.div (by fun_prop) (by fun_prop) fun p => ?_))
        · exact continuous_const.div (by fun_prop) fun p => (Real.sqrt_pos.mpr (by positivity)).ne'
        · have hsq : 0 < Real.sqrt (p ^ 2 + y) := Real.sqrt_pos.mpr (by positivity)
          have he : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) < 1 := by
            rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
          linarith
      exact hcont.aestronglyMeasurable
    · filter_upwards with p
      intro t ht
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      have ht_ge : y₀ ≤ t := by dsimp only [y₀]; linarith
      have hv_ge : y₀ ≤ p ^ 2 + t := by linarith [sq_nonneg p]
      have hv_pos : 0 < p ^ 2 + t := lt_of_lt_of_le hy₀ hv_ge
      rw [(hasDerivAt_gThermal hv_pos).deriv, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg p)]
      have hsq_ge : Real.sqrt y₀ ≤ Real.sqrt (p ^ 2 + t) := Real.sqrt_le_sqrt hv_ge
      have hsq_p : |p| ≤ Real.sqrt (p ^ 2 + t) := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
      have he_le1 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) ≤
          Real.exp (-2 * Real.pi * Real.sqrt y₀) := by
        apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
      have he_le2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) ≤
          Real.exp (-(2 * Real.pi) * |p|) := by
        apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
      have hden0 : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt y₀) := by
        have : Real.exp (-2 * Real.pi * Real.sqrt y₀) < 1 := by
          rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hy₀]
        linarith
      have hden : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) := by linarith
      have hfrac_nn : 0 ≤ Real.pi / Real.sqrt (p ^ 2 + t) *
          (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)))) := by positivity
      have habs : |-Real.pi / Real.sqrt (p ^ 2 + t) *
          (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))))| =
          Real.pi / Real.sqrt (p ^ 2 + t) *
            (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
              (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)))) := by
        have : -Real.pi / Real.sqrt (p ^ 2 + t) *
            (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
              (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)))) =
            -(Real.pi / Real.sqrt (p ^ 2 + t) *
              (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
                (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))))) := by ring
        rw [this, abs_neg, abs_of_nonneg hfrac_nn]
      rw [habs]
      have h1 : Real.pi / Real.sqrt (p ^ 2 + t) ≤ Real.pi / Real.sqrt y₀ :=
        div_le_div_of_nonneg_left Real.pi_pos.le (Real.sqrt_pos.mpr hy₀) hsq_ge
      have h2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
          (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))) ≤
          (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹ * Real.exp (-(2 * Real.pi) * |p|) := by
        rw [inv_mul_eq_div]
        exact (div_le_div_of_nonneg_right he_le2 hden.le).trans
          (div_le_div_of_nonneg_left (Real.exp_pos _).le hden0 (by linarith))
      have hprod : Real.pi / Real.sqrt (p ^ 2 + t) *
            (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
              (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)))) ≤
          C * Real.exp (-(2 * Real.pi) * |p|) := by
        dsimp only [C]
        calc Real.pi / Real.sqrt (p ^ 2 + t) *
              (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
                (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t))))
            ≤ (Real.pi / Real.sqrt y₀) *
                ((1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹ * Real.exp (-(2 * Real.pi) * |p|)) :=
              mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = _ := by ring
      dsimp only [bound]
      calc p ^ 2 * (Real.pi / Real.sqrt (p ^ 2 + t) *
              (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)) /
                (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + t)))))
          ≤ p ^ 2 * (C * Real.exp (-(2 * Real.pi) * |p|)) :=
            mul_le_mul_of_nonneg_left hprod (sq_nonneg p)
        _ = C * (|p| ^ 2 * Real.exp (-(2 * Real.pi) * |p|)) := by rw [sq_abs]; ring
    · filter_upwards with p
      intro t ht
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
      have hv_pos : 0 < p ^ 2 + t := by linarith [sq_nonneg p]
      rw [(hasDerivAt_gThermal hv_pos).deriv]
      exact ((hasDerivAt_gThermal hv_pos).comp_const_add (p ^ 2) t).const_mul (p ^ 2)
  -- Integration by parts on (0, ∞): ∫_0^∞ p² g'(p²+y) dp = -(1/2) ∫_0^∞ g(p²+y) dp = -(π/2) H₁(y)
  have hibp : ∫ p in Set.Ioi (0 : ℝ), p ^ 2 * deriv gThermal (p ^ 2 + y) =
      -(Real.pi / 2) * H1 y := by
    have hcont_g : Continuous (fun p : ℝ => gThermal (p ^ 2 + y)) := continuous_gThermal_comp hy
    have hcont_gp : Continuous (fun p : ℝ => 2 * p * deriv gThermal (p ^ 2 + y)) := by
      have heq : (fun p : ℝ => 2 * p * deriv gThermal (p ^ 2 + y)) =
          fun p : ℝ => 2 * p * (-Real.pi / Real.sqrt (p ^ 2 + y) *
            (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
              (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))))) := by
        ext p; rw [(hasDerivAt_gThermal (by positivity)).deriv]
      rw [heq]
      refine (continuous_const.mul continuous_id).mul
        (Continuous.mul ?_ (Continuous.div (by fun_prop) (by fun_prop) fun p => ?_))
      · exact continuous_const.div (by fun_prop) fun p => (Real.sqrt_pos.mpr (by positivity)).ne'
      · have hsq : 0 < Real.sqrt (p ^ 2 + y) := Real.sqrt_pos.mpr (by positivity)
        have he : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) < 1 := by
          rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos]
        linarith
    have hibp_R : ∀ R : ℝ,
        ∫ p in (0 : ℝ)..R, p * (2 * p * deriv gThermal (p ^ 2 + y)) =
          R * gThermal (R ^ 2 + y) - ∫ p in (0 : ℝ)..R, gThermal (p ^ 2 + y) := by
      intro R
      have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (u := fun p : ℝ => p) (v := fun p : ℝ => gThermal (p ^ 2 + y))
        (u' := fun _ => (1 : ℝ)) (v' := fun p : ℝ => 2 * p * deriv gThermal (p ^ 2 + y))
        (a := 0) (b := R)
        (fun x _ => hasDerivAt_id x)
        (fun x _ => by
          have hv : 0 < x ^ 2 + y := by positivity
          have h1 := (hasDerivAt_gThermal hv).comp x ((hasDerivAt_pow 2 x).add_const y)
          rw [(hasDerivAt_gThermal hv).deriv]
          refine h1.congr_deriv ?_
          simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)
        intervalIntegrable_const
        (hcont_gp.intervalIntegrable 0 R)
      simpa using h
    have hint_lhs : IntegrableOn (fun p : ℝ => p * (2 * p * deriv gThermal (p ^ 2 + y))) (Set.Ioi 0) := by
      have h1 : IntegrableOn (fun p : ℝ => p ^ 2 * deriv gThermal (p ^ 2 + y)) (Set.Ioi 0) := by
        refine hbound_int.mono' (by
          have hcont : Continuous (fun p : ℝ => p ^ 2 * deriv gThermal (p ^ 2 + y)) := by
            have heq : (fun p : ℝ => p ^ 2 * deriv gThermal (p ^ 2 + y)) =
                fun p : ℝ => (1 / 2 : ℝ) * p * (2 * p * deriv gThermal (p ^ 2 + y)) := by ext p; ring
            rw [heq]; exact (continuous_const.mul continuous_id).mul hcont_gp
          exact hcont.aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
        have hv_ge : y₀ ≤ p ^ 2 + y := by dsimp only [y₀]; linarith [sq_nonneg p]
        have hv_pos : 0 < p ^ 2 + y := lt_of_lt_of_le hy₀ hv_ge
        rw [(hasDerivAt_gThermal hv_pos).deriv, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg p)]
        have hsq_ge : Real.sqrt y₀ ≤ Real.sqrt (p ^ 2 + y) := Real.sqrt_le_sqrt hv_ge
        have hsq_p : |p| ≤ Real.sqrt (p ^ 2 + y) := by
          rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
        have he_le1 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≤
            Real.exp (-2 * Real.pi * Real.sqrt y₀) := by
          apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
        have he_le2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) ≤
            Real.exp (-(2 * Real.pi) * |p|) := by
          apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
        have hden0 : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt y₀) := by
          have : Real.exp (-2 * Real.pi * Real.sqrt y₀) < 1 := by
            rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hy₀]
          linarith
        have hden : 0 < 1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) := by linarith
        have habs : |-Real.pi / Real.sqrt (p ^ 2 + y) *
            (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
              (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))))| =
            Real.pi / Real.sqrt (p ^ 2 + y) *
              (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
                (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) := by
          have hnn : 0 ≤ Real.pi / Real.sqrt (p ^ 2 + y) *
              (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
                (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) := by positivity
          have : -Real.pi / Real.sqrt (p ^ 2 + y) *
              (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
                (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) =
              -(Real.pi / Real.sqrt (p ^ 2 + y) *
                (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
                  (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))))) := by ring
          rw [this, abs_neg, abs_of_nonneg hnn]
        rw [habs]
        have h1 : Real.pi / Real.sqrt (p ^ 2 + y) ≤ Real.pi / Real.sqrt y₀ :=
          div_le_div_of_nonneg_left Real.pi_pos.le (Real.sqrt_pos.mpr hy₀) hsq_ge
        have h2 : Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
            (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))) ≤
            (1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹ * Real.exp (-(2 * Real.pi) * |p|) := by
          rw [inv_mul_eq_div]
          exact (div_le_div_of_nonneg_right he_le2 hden.le).trans
            (div_le_div_of_nonneg_left (Real.exp_pos _).le hden0 (by linarith))
        have hprod : Real.pi / Real.sqrt (p ^ 2 + y) *
              (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
                (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))) ≤
            C * Real.exp (-(2 * Real.pi) * |p|) := by
          dsimp only [C]
          calc Real.pi / Real.sqrt (p ^ 2 + y) *
                (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
                  (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y))))
              ≤ (Real.pi / Real.sqrt y₀) *
                  ((1 - Real.exp (-2 * Real.pi * Real.sqrt y₀))⁻¹ * Real.exp (-(2 * Real.pi) * |p|)) :=
                mul_le_mul h1 h2 (by positivity) (by positivity)
            _ = _ := by ring
        dsimp only [bound]
        calc p ^ 2 * (Real.pi / Real.sqrt (p ^ 2 + y) *
                (Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)) /
                  (1 - Real.exp (-2 * Real.pi * Real.sqrt (p ^ 2 + y)))))
            ≤ p ^ 2 * (C * Real.exp (-(2 * Real.pi) * |p|)) :=
              mul_le_mul_of_nonneg_left hprod (sq_nonneg p)
          _ = C * (|p| ^ 2 * Real.exp (-(2 * Real.pi) * |p|)) := by rw [sq_abs]; ring
      exact (h1.const_mul 2).congr (Eventually.of_forall fun p => by ring)
    have htend_lhs : Tendsto (fun R : ℝ => ∫ p in (0 : ℝ)..R, p * (2 * p * deriv gThermal (p ^ 2 + y)))
        atTop (𝓝 (∫ p in Set.Ioi (0 : ℝ), p * (2 * p * deriv gThermal (p ^ 2 + y)))) :=
      intervalIntegral_tendsto_integral_Ioi 0 hint_lhs tendsto_id
    have htend_rhs_int : Tendsto (fun R : ℝ => ∫ p in (0 : ℝ)..R, gThermal (p ^ 2 + y))
        atTop (𝓝 (∫ p in Set.Ioi (0 : ℝ), gThermal (p ^ 2 + y))) :=
      intervalIntegral_tendsto_integral_Ioi 0 (integrable_gThermal_comp hy).integrableOn tendsto_id
    have htend_bdry : Tendsto (fun R : ℝ => R * gThermal (R ^ 2 + y)) atTop (𝓝 0) := by
      let C1 : ℝ := (1 - Real.exp (-2 * Real.pi * Real.sqrt y))⁻¹
      have hC1 : 0 ≤ C1 := by
        dsimp only [C1]
        have : Real.exp (-2 * Real.pi * Real.sqrt y) < 1 := by
          rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, Real.sqrt_pos.mpr hy]
        positivity
      have htop : Tendsto (fun R : ℝ => C1 * (R * Real.exp (-2 * Real.pi * R))) atTop (𝓝 0) := by
        have h1 : Tendsto (fun R : ℝ => (2 * Real.pi * R) * Real.exp (-(2 * Real.pi * R))) atTop (𝓝 0) := by
          have hlin : Tendsto (fun R : ℝ => 2 * Real.pi * R) atTop atTop :=
            Tendsto.const_mul_atTop (by positivity) tendsto_id
          have hexp0 : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (𝓝 0) := by
            have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
            simpa using this
          exact hexp0.comp hlin
        have h2 := h1.const_mul (C1 / (2 * Real.pi))
        simp only [mul_zero] at h2
        refine h2.congr fun R => ?_
        have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
        have heq_exp : Real.exp (-(2 * Real.pi * R)) = Real.exp (-2 * Real.pi * R) := by
          congr 1; ring
        rw [heq_exp]
        field_simp [hpi]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop ?_ ?_
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
        exact mul_nonneg hR (gThermal_nonneg (by positivity))
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
        have hle := gThermal_le_exp hy (by linarith [sq_nonneg R] : y ≤ R ^ 2 + y)
        have hsq : R ≤ Real.sqrt (R ^ 2 + y) := by
          calc R = Real.sqrt (R ^ 2) := (Real.sqrt_sq hR).symm
            _ ≤ Real.sqrt (R ^ 2 + y) := Real.sqrt_le_sqrt (by linarith)
        have hexp : Real.exp (-2 * Real.pi * Real.sqrt (R ^ 2 + y)) ≤ Real.exp (-2 * Real.pi * R) := by
          apply Real.exp_le_exp.mpr; nlinarith [Real.pi_pos]
        have hle2 : gThermal (R ^ 2 + y) ≤ C1 * Real.exp (-2 * Real.pi * R) :=
          hle.trans (mul_le_mul_of_nonneg_left hexp hC1)
        calc R * gThermal (R ^ 2 + y) ≤ R * (C1 * Real.exp (-2 * Real.pi * R)) :=
              mul_le_mul_of_nonneg_left hle2 hR
          _ = C1 * (R * Real.exp (-2 * Real.pi * R)) := by ring
    have htend_rhs : Tendsto (fun R : ℝ => R * gThermal (R ^ 2 + y) - ∫ p in (0 : ℝ)..R, gThermal (p ^ 2 + y))
        atTop (𝓝 (0 - ∫ p in Set.Ioi (0 : ℝ), gThermal (p ^ 2 + y))) :=
      htend_bdry.sub htend_rhs_int
    have heq_lim : ∫ p in Set.Ioi (0 : ℝ), p * (2 * p * deriv gThermal (p ^ 2 + y)) =
        -∫ p in Set.Ioi (0 : ℝ), gThermal (p ^ 2 + y) := by
      have huniq := tendsto_nhds_unique (htend_lhs.congr hibp_R) htend_rhs
      linarith
    have heven : ∫ p in Set.Ioi (0 : ℝ), gThermal (p ^ 2 + y) = Real.pi * H1 y := by
      unfold H1
      have hsplit : ∫ p : ℝ, gThermal (p ^ 2 + y) =
          (∫ p in Set.Iic (0 : ℝ), gThermal (p ^ 2 + y)) +
            ∫ p in Set.Ioi (0 : ℝ), gThermal (p ^ 2 + y) := by
        rw [← MeasureTheory.setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
          (integrable_gThermal_comp hy).integrableOn (integrable_gThermal_comp hy).integrableOn,
          Set.Iic_union_Ioi, MeasureTheory.setIntegral_univ]
      have hneg_eq : ∫ p in Set.Iic (0 : ℝ), gThermal (p ^ 2 + y) =
          ∫ p in Set.Ioi (0 : ℝ), gThermal (p ^ 2 + y) := by
        rw [MeasureTheory.setIntegral_congr_set MeasureTheory.Iio_ae_eq_Iic.symm]
        rw [← MeasureTheory.integral_indicator measurableSet_Iio,
          ← MeasureTheory.integral_indicator measurableSet_Ioi]
        have hneg_comp := MeasureTheory.Measure.integral_comp_mul_left
          (g := fun p : ℝ => Set.indicator (Set.Ioi 0) (fun q => gThermal (q ^ 2 + y)) p) (-1 : ℝ)
        simp only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul] at hneg_comp
        rw [← hneg_comp]
        congr 1; ext p
        by_cases hp : p < 0
        · have hp' : 0 < -p := by linarith
          simp [Set.indicator, hp, hp']
        · have hp' : ¬(0 < -p) := by linarith
          simp [Set.indicator, hp, hp']
      rw [hneg_eq] at hsplit
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp [hpi]
      linarith
    have hfactor : ∫ p in Set.Ioi (0 : ℝ), p * (2 * p * deriv gThermal (p ^ 2 + y)) =
        2 * ∫ p in Set.Ioi (0 : ℝ), p ^ 2 * deriv gThermal (p ^ 2 + y) := by
      rw [← MeasureTheory.integral_const_mul]
      congr 1; ext p; ring
    rw [hfactor, heven] at heq_lim
    linarith
  have hscaled := hderiv_int.const_mul (2 * Real.pi ^ 2)⁻¹
  refine hscaled.congr_deriv ?_
  rw [hibp]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]
  ring

/-! #### Bose–Fermi Matsubara Cancellation (`S_bose(y) - 8 S_bose(4y) = -S_fermi(y)`) -/

private lemma modeSeries_bose_sub_fermi {y : ℝ} (hy : 0 < y) :
    modeSeries boseModes (y : ℂ) - 8 * modeSeries boseModes ((4 * y : ℝ) : ℂ) =
      -modeSeries fermiModes (y : ℂ) := by
  have hterm_scale : ∀ n : ℕ,
      (8 : ℂ) * modeTermL (boseModes.a n) ((4 * y : ℝ) : ℂ) =
        modeTermL (((n : ℝ) + 1) ^ 2 / 4) (y : ℂ) := by
    intro n
    unfold modeTermL boseModes
    have hpos : (0 : ℝ) < y + ((n : ℝ) + 1) ^ 2 / 4 := by positivity
    have h4 : (4 * y : ℝ) + ((n : ℝ) + 1) ^ 2 = 4 * (y + ((n : ℝ) + 1) ^ 2 / 4) := by ring
    have h4c : ((4 * y : ℝ) : ℂ) + ((((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) =
        ((4 * (y + ((n : ℝ) + 1) ^ 2 / 4) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_add, h4]
    have h1c : (y : ℂ) + ((((n : ℝ) + 1) ^ 2 / 4 : ℝ) : ℂ) =
        ((y + ((n : ℝ) + 1) ^ 2 / 4 : ℝ) : ℂ) := by
      rw [← Complex.ofReal_add]
    rw [h4c, h1c]
    have hcpow_real : ∀ r : ℝ, 0 < r → ((r : ℂ) ^ (-(3 : ℂ) / 2)) = ((r ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) := by
      intro r hr
      have hre : (-(3 : ℂ) / 2) = (((-(3 : ℝ) / 2 : ℝ) : ℂ)) := by push_cast; rfl
      rw [hre, Complex.ofReal_cpow hr.le]
    rw [hcpow_real _ (by positivity), hcpow_real _ hpos]
    have hr : (8 : ℝ) * (4 * (y + ((n : ℝ) + 1) ^ 2 / 4)) ^ (-(3 : ℝ) / 2) =
        (y + ((n : ℝ) + 1) ^ 2 / 4) ^ (-(3 : ℝ) / 2) := by
      rw [Real.mul_rpow (by norm_num) hpos.le]
      have h4p : (4 : ℝ) ^ (-(3 : ℝ) / 2) = (8 : ℝ)⁻¹ := by
        have h2 : (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num
        rw [h2, ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [h4p]
      ring
    exact_mod_cast hr
  have h8 : (8 : ℂ) * modeSeries boseModes ((4 * y : ℝ) : ℂ) =
      ∑' n : ℕ, modeTermL (((n : ℝ) + 1) ^ 2 / 4) (y : ℂ) := by
    unfold modeSeries
    rw [← tsum_mul_left]
    exact tsum_congr hterm_scale
  have hsumm_bose := modeSeries_summable_of_pos boseModes hy
  have hsumm_fermi := modeSeries_summable_of_pos fermiModes hy
  have hsplit : ∑' n : ℕ, modeTermL (((n : ℝ) + 1) ^ 2 / 4) (y : ℂ) =
      modeSeries fermiModes (y : ℂ) + modeSeries boseModes (y : ℂ) := by
    have hsumm_all : Summable (fun n : ℕ => modeTermL (((n : ℝ) + 1) ^ 2 / 4) (y : ℂ)) := by
      have h4 := (modeSeries_summable_of_pos boseModes (by positivity : 0 < 4 * y)).mul_left (8 : ℂ)
      exact h4.congr hterm_scale
    have heven : (fun k : ℕ => modeTermL ((((2 * k : ℕ) : ℝ) + 1) ^ 2 / 4) (y : ℂ)) =
        fun k : ℕ => modeTermL (fermiModes.a k) (y : ℂ) := by
      ext k; unfold fermiModes; congr 2; push_cast; ring
    have hodd : (fun k : ℕ => modeTermL ((((2 * k + 1 : ℕ) : ℝ) + 1) ^ 2 / 4) (y : ℂ)) =
        fun k : ℕ => modeTermL (boseModes.a k) (y : ℂ) := by
      ext k; unfold boseModes; congr 2; push_cast; ring
    have hts := tsum_even_add_odd (f := fun n : ℕ => modeTermL (((n : ℝ) + 1) ^ 2 / 4) (y : ℂ))
      (by rw [heven]; exact hsumm_fermi) (by rw [hodd]; exact hsumm_bose)
    rw [← hts, heven, hodd]
    rfl
  rw [h8, hsplit]
  ring

/-! ### 4. Differential-Algebra Transfer & Odd-Dimension Differential Transcendence (`d = 1, 3`) -/

private lemma modeSeries_analyticOnNhd_rePos (ms : ModeSeq) :
    AnalyticOnNhd ℂ (modeSeries ms) {w : ℂ | 0 < w.re} := by
  intro w (hw : 0 < w.re)
  have h0 : modeSeries ms = fun z => ∑' k : ℕ, modeTermL (ms.a (0 + k)) z := by
    ext z; simp [modeSeries]
  rw [h0]
  exact modeSeries_tail_analyticOnNhd ms 0 w (fun h => by linarith [h.2, ms.a_pos 0])

private lemma modeSeries_real_analyticOnNhd (ms : ModeSeq) :
    AnalyticOnNhd ℝ (fun y : ℝ => modeSeries ms (y : ℂ)) (Set.Ioi 0) := by
  intro y (hy : 0 < y)
  have hana := modeSeries_analyticOnNhd_rePos ms (y : ℂ) (by simpa using hy)
  exact (hana.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt y)

private lemma iteratedDeriv_modeSeries_ofReal (ms : ModeSeq) (k : ℕ) {y : ℝ} (hy : 0 < y) :
    iteratedDeriv k (fun t : ℝ => modeSeries ms (t : ℂ)) y =
      iteratedDeriv k (modeSeries ms) (y : ℂ) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
    have hev : iteratedDeriv k (fun t : ℝ => modeSeries ms (t : ℂ)) =ᶠ[𝓝 y]
        fun t : ℝ => iteratedDeriv k (modeSeries ms) (t : ℂ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht
      exact ih ht
    rw [iteratedDeriv_succ, hev.deriv_eq, iteratedDeriv_succ]
    have hana_k : AnalyticOnNhd ℂ (iteratedDeriv k (modeSeries ms)) {w : ℂ | 0 < w.re} := by
      rw [iteratedDeriv_eq_iterate]
      exact (modeSeries_analyticOnNhd_rePos ms).iterated_deriv k
    have hdiff : HasDerivAt (iteratedDeriv k (modeSeries ms))
        (deriv (iteratedDeriv k (modeSeries ms)) (y : ℂ)) (y : ℂ) :=
      (hana_k (y : ℂ) (by simpa using hy)).differentiableAt.hasDerivAt
    have hcomp := hdiff.scomp y (hasDerivAt_id' y).ofReal_comp
    have hcomp' : HasDerivAt (fun t : ℝ => iteratedDeriv k (modeSeries ms) (t : ℂ))
        ((1 : ℝ) • deriv (iteratedDeriv k (modeSeries ms)) (y : ℂ)) y := hcomp
    simpa [smul_eq_mul] using hcomp'.deriv

private lemma H1_deriv2_complex {y : ℝ} (hy : 0 < y) :
    iteratedDeriv 2 (fun t : ℝ => (H1 t : ℂ)) y =
      (1 / 4 : ℂ) * modeSeries boseModes (y : ℂ) - 1 / (4 * (y : ℂ)) +
        1 / (8 * ((y ^ ((3 : ℝ) / 2) : ℝ) : ℂ)) := by
  rw [iteratedDeriv_ofReal_comp, H1_deriv2 hy]
  have hsum_real : Summable (fun n : ℕ => (y + ((n : ℝ) + 1) ^ 2) ^ (-(3 : ℝ) / 2)) := by
    have hp : Summable (fun n : ℕ => ((n : ℝ) ^ (3 : ℝ))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    have h3 : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(3 : ℝ))) := by
      refine (hp.comp_injective Nat.succ_injective).congr fun n => ?_
      simp only [Function.comp, Nat.cast_succ]
      rw [Real.rpow_neg (by positivity)]
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h3
    have hle : ((n : ℝ) + 1) ^ 2 ≤ y + ((n : ℝ) + 1) ^ 2 := by linarith
    calc (y + ((n : ℝ) + 1) ^ 2) ^ (-(3 : ℝ) / 2)
        ≤ (((n : ℝ) + 1) ^ 2) ^ (-(3 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hle (by norm_num)
      _ = ((n : ℝ) + 1) ^ (-(3 : ℝ)) := by
          rw [← Real.rpow_natCast ((n : ℝ) + 1) 2, ← Real.rpow_mul (by positivity)]
          norm_num
  have hms_eq : (∑' n : ℕ, (((y + ((n : ℝ) + 1) ^ 2) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ)) =
      modeSeries boseModes (y : ℂ) := by
    unfold modeSeries modeTermL boseModes
    apply tsum_congr; intro n
    have hpos : (0 : ℝ) < y + ((n : ℝ) + 1) ^ 2 := by positivity
    have hre : (-(3 : ℂ) / 2) = (((-(3 : ℝ) / 2 : ℝ) : ℂ)) := by push_cast; rfl
    have hcast : (y : ℂ) + ((((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) =
        ((y + ((n : ℝ) + 1) ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, hre, Complex.ofReal_cpow hpos.le]
  push_cast
  rw [hms_eq]

private lemma contDiffOn_of_deriv_contDiffOn {f g : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ x ∈ U, HasDerivAt f (g x) x) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) :
    ContDiffOn ℝ (⊤ : ℕ∞) f U := by
  rw [contDiffOn_infty]
  intro n
  induction n with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  | succ n _ =>
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen hU]
    refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (hg.of_le (by simp)).congr fun x hx => (hd x hx).deriv

private lemma contDiffOn_iteratedDeriv_infty {f : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (k : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv k f) U := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [iteratedDeriv_succ]
    rw [contDiffOn_infty]
    intro n
    have h1 : ContDiffOn ℝ ((n : ℕ∞) + 1) (iteratedDeriv k f) U := ih.of_le (by simp)
    exact (contDiffOn_succ_iff_deriv_of_isOpen hU).mp h1 |>.2.2

private lemma H1_contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => (H1 y : ℂ)) (Set.Ioi 0) := by
  have h2_smooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : ℝ => (1 / 4 : ℂ) * modeSeries boseModes (y : ℂ) - 1 / (4 * (y : ℂ)) +
        1 / (8 * ((y ^ ((3 : ℝ) / 2) : ℝ) : ℂ))) (Set.Ioi 0) := by
    have hms : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => modeSeries boseModes (y : ℂ)) (Set.Ioi 0) :=
      (modeSeries_real_analyticOnNhd boseModes).contDiffOn isOpen_Ioi.uniqueDiffOn
    have hinv_r : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => (4 * y)⁻¹) (Set.Ioi 0) :=
      (contDiffOn_const.mul contDiffOn_id).inv fun y (hy : 0 < y) => mul_ne_zero (by norm_num) hy.ne'
    have hinv : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => (1 : ℂ) / (4 * (y : ℂ))) (Set.Ioi 0) := by
      refine (Complex.ofRealCLM.contDiff.comp_contDiffOn hinv_r).congr fun y _ => ?_
      simp [one_div]
    have hrpow : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => (8 * y ^ ((3 : ℝ) / 2))⁻¹) (Set.Ioi 0) :=
      (contDiffOn_const.mul (contDiffOn_id.rpow_const_of_ne fun y (hy : 0 < y) => hy.ne')).inv
        fun y (hy : 0 < y) => mul_ne_zero (by norm_num) (Real.rpow_pos_of_pos hy _).ne'
    have hinv2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => (1 : ℂ) / (8 * ((y ^ ((3 : ℝ) / 2) : ℝ) : ℂ)))
        (Set.Ioi 0) := by
      refine (Complex.ofRealCLM.contDiff.comp_contDiffOn hrpow).congr fun y _ => ?_
      simp [one_div]
    exact ((contDiffOn_const.mul hms).sub hinv).add hinv2
  have hd1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => ((deriv H1 y : ℝ) : ℂ)) (Set.Ioi 0) := by
    refine contDiffOn_of_deriv_contDiffOn isOpen_Ioi (fun y (hy : 0 < y) => ?_) h2_smooth
    have hreal : HasDerivAt (deriv H1) (iteratedDeriv 2 H1 y) y := by
      have h2eq : iteratedDeriv 2 H1 y = deriv (deriv H1) y := by
        rw [iteratedDeriv_succ, iteratedDeriv_one]
      rw [h2eq]
      exact (hasDerivAt_deriv_H1 hy).differentiableAt.hasDerivAt
    have hcomp := hreal.ofReal_comp
    rw [← iteratedDeriv_ofReal_comp, H1_deriv2_complex hy] at hcomp
    exact hcomp
  refine contDiffOn_of_deriv_contDiffOn isOpen_Ioi (fun y (hy : 0 < y) => ?_) hd1
  exact ((hasDerivAt_H1 hy).differentiableAt.hasDerivAt).ofReal_comp

private lemma H3_contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => (H3 y : ℂ)) (Set.Ioi 0) := by
  refine contDiffOn_of_deriv_contDiffOn (g := fun y : ℝ => (-(4 * (Real.pi : ℂ))⁻¹) * (H1 y : ℂ))
    isOpen_Ioi (fun y (hy : 0 < y) => ?_) (contDiffOn_const.mul H1_contDiffOn)
  simpa using (H3_deriv hy).ofReal_comp

/-! #### Ordinary ODE Extraction & Pullback Closure along `τ(y) = c / √y` -/

private noncomputable def polyToMvNat : Polynomial ℂ →+* MvPolynomial ℕ ℂ :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)

private lemma eval_polyToMvNat (p : Polynomial ℂ) (y : ℕ → ℂ) :
    MvPolynomial.eval y (polyToMvNat p) = p.eval (y 0) := by
  have h : (MvPolynomial.eval y).comp polyToMvNat = Polynomial.evalRingHom (y 0) := by
    apply Polynomial.ringHom_ext
    · intro c; simp [polyToMvNat]
    · simp [polyToMvNat]
  exact RingHom.congr_fun h p

private noncomputable def mvPolyToMvNat {r : ℕ} :
    MvPolynomial (Fin (r + 1)) (Polynomial ℂ) →+* MvPolynomial ℕ ℂ :=
  MvPolynomial.eval₂Hom polyToMvNat (fun j : Fin (r + 1) => MvPolynomial.X (j.val + 1))

private lemma eval_mvPolyToMvNat {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (y : ℕ → ℂ) :
    MvPolynomial.eval y (mvPolyToMvNat P) =
      MvPolynomial.eval (fun j : Fin (r + 1) => y (j.val + 1)) (evalU P (y 0)) := by
  have h : (MvPolynomial.eval y).comp (mvPolyToMvNat (r := r)) =
      (MvPolynomial.eval (fun j : Fin (r + 1) => y (j.val + 1))).comp
        (MvPolynomial.map (Polynomial.evalRingHom (y 0))) := by
    apply MvPolynomial.ringHom_ext
    · intro p; simp [mvPolyToMvNat, eval_polyToMvNat]
    · intro j; simp [mvPolyToMvNat]
  exact RingHom.congr_fun h P

private lemma eq_zero_of_eval_evalU_eq_zero {r : ℕ}
    {P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)}
    (h : ∀ (u : ℂ) (x : Fin (r + 1) → ℂ), MvPolynomial.eval x (evalU P u) = 0) :
    P = 0 := by
  rw [MvPolynomial.ext_iff]
  intro α
  rw [show (0 : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)).coeff α = 0 from rfl]
  apply Polynomial.funext
  intro u
  rw [Polynomial.eval_zero]
  have hU0 : evalU P u = 0 := MvPolynomial.funext (h u)
  have hc := congrArg (fun Q : MvPolynomial (Fin (r + 1)) ℂ => Q.coeff α) hU0
  rw [evalU, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom] at hc
  exact hc

private lemma mvPolyToMvNat_eq_zero_imp {r : ℕ}
    {P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)} (hP : mvPolyToMvNat P = 0) :
    P = 0 := by
  refine eq_zero_of_eval_evalU_eq_zero fun u x => ?_
  let y : ℕ → ℂ := fun n =>
    if n = 0 then u else x ⟨(n - 1) % (r + 1), Nat.mod_lt _ (Nat.succ_pos r)⟩
  have hy0 : y 0 = u := by simp [y]
  have hyj : ∀ j : Fin (r + 1), y (j.val + 1) = x j := by
    intro j
    simp [y, Nat.mod_eq_of_lt j.isLt]
  have h1 := eval_mvPolyToMvNat P y
  rw [hP, map_zero, hy0] at h1
  simpa [hyj] using h1.symm

private def jetVec (f : ℝ → ℂ) (n : ℕ) (i : Fin (n + 1)) (x : ℝ) : ℂ :=
  if i.val = 0 then (x : ℂ) else iteratedDeriv (i.val - 1) f x

private def topSep (f : ℝ → ℂ) (n : ℕ) (Q : MvPolynomial (Fin (n + 1)) ℂ) (x : ℝ) : ℂ :=
  MvPolynomial.eval (fun j => jetVec f n j x) (MvPolynomial.pderiv (Fin.last n) Q)

private lemma exists_ordinary_ode_Ioi (f : ℝ → ℂ) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hP_ne : P ≠ 0)
    (hP_vanish : ∀ x : ℝ, 0 < x →
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f x) (evalU P (x : ℂ)) = 0) :
    ∃ (n : ℕ) (Q : MvPolynomial (Fin (n + 1)) ℂ) (x₀ : ℝ),
      0 < n ∧ 0 < x₀ ∧ topSep f n Q x₀ ≠ 0 ∧
      ∀ z : ℝ, 0 < z → MvPolynomial.eval (fun j => jetVec f n j z) Q = 0 := by
  classical
  let y : ℕ → ℝ → ℂ := fun i x => if i = 0 then (x : ℂ) else iteratedDeriv (i - 1) f x
  have hmv_ne : mvPolyToMvNat P ≠ 0 := fun h0 => hP_ne (mvPolyToMvNat_eq_zero_imp h0)
  have hmv_vanish : ∀ x ∈ Set.Ioi (0 : ℝ), MvPolynomial.eval (fun i => y i x) (mvPolyToMvNat P) = 0 := by
    intro x hx
    rw [eval_mvPolyToMvNat]
    have hy0 : y 0 x = (x : ℂ) := by simp [y]
    have hyj : ∀ j : Fin (r + 1), y (j.val + 1) x = iteratedDeriv j.val f x := by
      intro j; simp [y]
    rw [hy0]
    simp_rw [hyj]
    exact hP_vanish x hx
  obtain ⟨n, Q, x₀, hx₀, hS_ne, hQ_vanish⟩ :=
    ordinary_relation (Set.Ioi (0 : ℝ)) ⟨1, zero_lt_one⟩ y ⟨mvPolyToMvNat P, hmv_ne, hmv_vanish⟩
  have hn_ne : n ≠ 0 := by
    rintro rfl
    let q : Polynomial ℂ := MvPolynomial.eval₂ Polynomial.C (fun _ : Fin 1 => Polynomial.X) Q
    have hq_eval : ∀ (T : MvPolynomial (Fin 1) ℂ) (c : ℂ),
        (MvPolynomial.eval₂ Polynomial.C (fun _ : Fin 1 => Polynomial.X) T).eval c =
          MvPolynomial.eval (fun _ : Fin 1 => c) T := by
      intro T c
      induction T using MvPolynomial.induction_on with
      | C a => simp
      | add a b ha hb => simp [MvPolynomial.eval₂_add, ha, hb]
      | mul_X a i ha => simp [MvPolynomial.eval₂_mul, ha]
    have hq0 : q = 0 := by
      by_contra hq_ne
      have hU_inf : (Set.Ioi (0 : ℝ)).Infinite := Set.Ioi_infinite 0
      have hCU_inf : (Complex.ofReal '' Set.Ioi (0 : ℝ)).Infinite :=
        hU_inf.image (Complex.ofReal_injective.injOn)
      obtain ⟨w, hwU, hwnot⟩ := hCU_inf.exists_notMem_finset q.roots.toFinset
      obtain ⟨z, hzU, rfl⟩ := hwU
      have hvan := hQ_vanish z hzU
      have hy_fin : (fun i : Fin 1 => y i.val z) = fun _ : Fin 1 => (z : ℂ) := by
        funext i; fin_cases i; simp [y]
      rw [hy_fin, ← hq_eval Q (z : ℂ)] at hvan
      exact hwnot (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq_ne).mpr hvan))
    have hQ0 : Q = 0 := by
      apply MvPolynomial.funext
      intro w
      have hw : w = fun _ : Fin 1 => w 0 := funext fun i => by fin_cases i; rfl
      rw [hw, ← hq_eval Q (w 0), show eval₂ Polynomial.C (fun _ : Fin 1 => Polynomial.X) Q = q from rfl,
        hq0, Polynomial.eval_zero, map_zero]
    have hp0 : MvPolynomial.pderiv (Fin.last 0) Q = 0 := by rw [hQ0, map_zero]
    rw [hp0, map_zero] at hS_ne
    exact hS_ne rfl
  have hjet_eq : ∀ z : ℝ, (fun i : Fin (n + 1) => y i.val z) = fun i => jetVec f n i z := by
    intro z; ext i; simp [y, jetVec]
  refine ⟨n, Q, x₀, Nat.pos_of_ne_zero hn_ne, hx₀, ?_, ?_⟩
  · simpa [topSep, hjet_eq x₀] using hS_ne
  · intro z hz
    simpa [hjet_eq z] using hQ_vanish z hz

private lemma generated_finset_sum {ι α : Type} [Fintype ι] [DecidableEq α]
    (w : ι → ℝ → ℂ) (y₀ : ℝ) (s : Finset α) (f : α → ℝ → ℂ)
    (hf : ∀ a ∈ s, Generated w y₀ (f a)) :
    Generated w y₀ (fun y => ∑ a ∈ s, f a y) := by
  induction s using Finset.induction_on with
  | empty => exact (Generated.const (u := w) (x := y₀) 0).congr (Eventually.of_forall fun _ => by simp)
  | @insert a s ha ih =>
    refine ((hf a (Finset.mem_insert_self a s)).add
      (ih fun b hb => hf b (Finset.mem_insert_of_mem hb))).congr (Eventually.of_forall fun y => ?_)
    simp [Finset.sum_insert ha]

/-- Pullback of an ordinary differential algebra for `f` on `(0, ∞)` along `τ(y) = c / √y`.
Every `y`-derivative of `wState` lies in `Generated wState y₀`, and `f (τ y)`, `τ y`, `(τ y)⁻¹`
all lie in `Generated wState y₀`. -/
private lemma pullback_ordinary_algebra {f : ℝ → ℂ} (hf_smooth : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioi 0))
    {c : ℝ} (hc : 0 < c) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hP_ne : P ≠ 0)
    (hP_vanish : ∀ T : ℝ, 0 < T →
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f T) (evalU P (T : ℂ)) = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ → ℂ) (y₀ : ℝ),
      0 < y₀ ∧
      (∀ᶠ y in 𝓝 y₀, ∀ i, DifferentiableAt ℝ (w i) y) ∧
      (∀ i, Generated w y₀ (_root_.deriv (w i))) ∧
      Generated w y₀ (fun y : ℝ => ((c / Real.sqrt y : ℝ) : ℂ)) ∧
      Generated w y₀ (fun y : ℝ => (((c / Real.sqrt y : ℝ) : ℂ))⁻¹) ∧
      Generated w y₀ (fun y : ℝ => f (c / Real.sqrt y)) := by
  classical
  obtain ⟨n, Q, T₀, hn, hT₀, hS0, hQ_vanish⟩ := exists_ordinary_ode_Ioi f P hP_ne hP_vanish
  let τ : ℝ → ℝ := fun y => c / Real.sqrt y
  let y₀ : ℝ := c ^ 2 / T₀ ^ 2
  have hy₀ : 0 < y₀ := by positivity
  have hτ_pos : ∀ y : ℝ, 0 < y → 0 < τ y := fun y hy => div_pos hc (Real.sqrt_pos.mpr hy)
  have hτ_y₀ : τ y₀ = T₀ := by
    dsimp only [τ, y₀]
    rw [Real.sqrt_div (sq_nonneg c), Real.sqrt_sq hc.le, Real.sqrt_sq hT₀.le]
    field_simp [hc.ne', hT₀.ne']
  have hτ_deriv : ∀ y : ℝ, 0 < y →
      HasDerivAt τ (-(2 * c ^ 2)⁻¹ * (τ y) ^ 3) y := by
    intro y hy
    have hsq : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
    have h1 := ((Real.hasDerivAt_sqrt hy.ne').inv hsq.ne').const_mul c
    refine (h1.congr_of_eventuallyEq (Eventually.of_forall fun t => by simp [τ, div_eq_mul_inv])).congr_deriv ?_
    have hsq2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
    dsimp only [τ]
    field_simp [hc.ne', hsq.ne', hy.ne']
  -- Define uState on T > 0, then pull back via τ to wState on y > 0
  let v := jetVec f n
  let S : ℝ → ℂ := topSep f n Q
  let ι := Fin (n + 1) ⊕ Fin 2
  let u : ι → ℝ → ℂ := fun idx T =>
    match idx with
    | Sum.inl i => v i T
    | Sum.inr 0 => (S T)⁻¹
    | Sum.inr 1 => (T : ℂ)⁻¹
  let w : ι → ℝ → ℂ := fun idx y => u idx (τ y)
  have hτ_cont : ContinuousAt τ y₀ := (hτ_deriv y₀ hy₀).continuousAt
  have hd_v : ∀ T : ℝ, 0 < T → ∀ i : Fin (n + 1), DifferentiableAt ℝ (v i) T := by
    intro T hT i
    obtain ⟨k, hk⟩ := i
    cases k with
    | zero =>
      have hv0 : v ⟨0, hk⟩ = fun t : ℝ => (t : ℂ) := by ext t; simp [v, jetVec]
      rw [hv0]
      exact Complex.ofRealCLM.differentiableAt
    | succ k =>
      have hvk : v ⟨k + 1, hk⟩ = iteratedDeriv k f := by ext t; simp [v, jetVec]
      rw [hvk]
      have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (iteratedDeriv k f) (Set.Ioi 0) :=
        contDiffOn_iteratedDeriv_infty isOpen_Ioi hf_smooth k
      exact (hsm.contDiffAt (isOpen_Ioi.mem_nhds hT)).differentiableAt (by simp)
  have hS_diff : ∀ T : ℝ, 0 < T → DifferentiableAt ℝ S T := by
    intro T hT
    have hp : ∀ R : MvPolynomial (Fin (n + 1)) ℂ,
        DifferentiableAt ℝ (fun t => MvPolynomial.eval (fun j => v j t) R) T := by
      intro R
      induction R using MvPolynomial.induction_on with
      | C a => simp [differentiableAt_const]
      | add A B hA hB =>
        have : (fun t => MvPolynomial.eval (fun j => v j t) (A + B)) =
            fun t => MvPolynomial.eval (fun j => v j t) A + MvPolynomial.eval (fun j => v j t) B := by
          ext t; simp
        rw [this]; exact hA.add hB
      | mul_X A j hA =>
        have : (fun t => MvPolynomial.eval (fun j => v j t) (A * X j)) =
            fun t => MvPolynomial.eval (fun j => v j t) A * v j t := by
          ext t; simp
        rw [this]; exact hA.mul (hd_v T hT j)
    exact hp (MvPolynomial.pderiv (Fin.last n) Q)
  have hS_ne_nhds : ∀ᶠ T in 𝓝 T₀, S T ≠ 0 :=
    (hS_diff T₀ hT₀).continuousAt.eventually_ne hS0
  have hS_ne_y : ∀ᶠ y in 𝓝 y₀, S (τ y) ≠ 0 := by
    have := hτ_cont.preimage_mem_nhds (by rwa [hτ_y₀] : {T | S T ≠ 0} ∈ 𝓝 (τ y₀))
    exact this
  have hsmooth_w : ∀ᶠ y in 𝓝 y₀, ∀ idx : ι, DifferentiableAt ℝ (w idx) y := by
    filter_upwards [isOpen_Ioi.mem_nhds hy₀, hS_ne_y] with y hy hSy
    intro idx
    have hτy := hτ_pos y hy
    have hdτ : DifferentiableAt ℝ τ y := (hτ_deriv y hy).differentiableAt
    rcases idx with i | k
    · exact (hd_v (τ y) hτy i).comp y hdτ
    · fin_cases k
      · exact ((hS_diff (τ y) hτy).inv hSy).comp y hdτ
      · have hinv_ofReal : DifferentiableAt ℝ (fun t : ℝ => (t : ℂ)⁻¹) (τ y) :=
          Complex.ofRealCLM.differentiableAt.inv (Complex.ofReal_ne_zero.mpr hτy.ne')
        exact hinv_ofReal.comp y hdτ
  -- Express deriv (v (Fin.last n)) T on a neighborhood of T₀ via polynomial_chain on Q(v(T)) = 0
  let top : Fin (n + 1) := Fin.last n
  let g : Fin (n + 1) → ℝ → ℂ := fun i T =>
    MvPolynomial.eval (fun j => v j T) (MvPolynomial.pderiv i Q)
  have hchain : ∀ T : ℝ, 0 < T →
      ∑ i : Fin (n + 1), g i T * _root_.deriv (v i) T = 0 := by
    intro T hT
    have hq_const : (fun t => MvPolynomial.eval (fun j => v j t) Q) =ᶠ[𝓝 T] fun _ => (0 : ℂ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hT] with t ht
      exact hQ_vanish t ht
    have hpc := polynomial_chain Q v (fun i => _root_.deriv (v i)) T
      (fun i => (hd_v T hT i).hasDerivAt)
    have h0 := hpc.deriv.symm.trans (hq_const.deriv_eq.trans (deriv_const T (0 : ℂ)))
    exact h0
  have hdv_lt : ∀ (i : Fin (n + 1)) (hi : i ≠ top), ∀ T : ℝ, 0 < T →
      _root_.deriv (v i) T = if i.val = 0 then 1 else v ⟨i.val + 1, by
        have hne : i.val ≠ n := fun h => hi (Fin.ext h)
        omega⟩ T := by
    intro i hi T hT
    obtain ⟨k, hk⟩ := i
    cases k with
    | zero =>
      have hv0 : v ⟨0, hk⟩ = fun t : ℝ => (t : ℂ) := by ext t; simp [v, jetVec]
      rw [hv0]; simp [(hasDerivAt_id' T).ofReal_comp.deriv]
    | succ k =>
      have hk_lt : k + 1 < n := by
        have hne : k + 1 ≠ n := fun h => hi (Fin.ext h)
        omega
      have hvk : v ⟨k + 1, hk⟩ = iteratedDeriv k f := by ext t; simp [v, jetVec]
      rw [hvk]
      simp [v, jetVec, iteratedDeriv_succ]
  -- Now prove Generated w y₀ for every w idx and its y-derivative!
  have gw : ∀ idx : ι, Generated w y₀ (w idx) := fun idx => Generated.coord idx
  have gc : ∀ a : ℂ, Generated w y₀ (fun _ => a) := fun a => Generated.const a
  have gτ : Generated w y₀ (fun y : ℝ => ((τ y : ℝ) : ℂ)) := by
    simpa [w, u, v, jetVec] using gw (Sum.inl ⟨0, Nat.succ_pos n⟩)
  have gτ_inv : Generated w y₀ (fun y : ℝ => (((τ y : ℝ) : ℂ))⁻¹) := by
    simpa [w, u] using gw (Sum.inr 1)
  have gf : Generated w y₀ (fun y : ℝ => f (τ y)) := by
    simpa [w, u, v, jetVec] using gw (Sum.inl ⟨1, Nat.succ_lt_succ hn⟩)
  have ginvS : Generated w y₀ (fun y : ℝ => (S (τ y))⁻¹) := by
    simpa [w, u] using gw (Sum.inr 0)
  have g_τ_deriv : Generated w y₀ (fun y : ℝ => ((-(2 * c ^ 2)⁻¹ * (τ y) ^ 3 : ℝ) : ℂ)) := by
    refine ((gc ((-(2 * c ^ 2)⁻¹ : ℝ) : ℂ)).mul (gτ.pow 3)).congr ?_
    filter_upwards with y; push_cast; rfl
  -- Helper: any polynomial in v (τ y) is in Generated w y₀
  have gpoly_v : ∀ R : MvPolynomial (Fin (n + 1)) ℂ,
      Generated w y₀ (fun y => MvPolynomial.eval (fun j => v j (τ y)) R) := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C a => exact (gc a).congr (Eventually.of_forall fun y => by simp)
    | add A B hA hB => exact (hA.add hB).congr (Eventually.of_forall fun y => by simp)
    | mul_X A j hA => exact (hA.mul (gw (Sum.inl j))).congr (Eventually.of_forall fun y => by simp [w, u])
  have g_dv_lt : ∀ i : Fin (n + 1), i ≠ top →
      Generated w y₀ (fun y => _root_.deriv (v i) (τ y)) := by
    intro i hi
    by_cases h0 : i.val = 0
    · refine (gc 1).congr ?_
      filter_upwards [isOpen_Ioi.mem_nhds hy₀] with y hy
      rw [hdv_lt i hi (τ y) (hτ_pos y hy), ite_eq_left_iff.mpr fun h => absurd h0 h]
    · have hlt : i.val + 1 < n + 1 := by
        have hne : i.val ≠ n := fun h => hi (Fin.ext h)
        omega
      refine (gw (Sum.inl ⟨i.val + 1, hlt⟩)).congr ?_
      filter_upwards [isOpen_Ioi.mem_nhds hy₀] with y hy
      rw [hdv_lt i hi (τ y) (hτ_pos y hy), ite_eq_right_iff.mpr fun h => absurd h h0]
  -- deriv (v top) (τ y) = - (S (τ y))⁻¹ * ∑_{i ≠ top} g i (τ y) * deriv (v i) (τ y)
  have g_dv_top : Generated w y₀ (fun y => _root_.deriv (v top) (τ y)) := by
    have hsum_gen : Generated w y₀
        (fun y => ∑ i ∈ Finset.univ.erase top, g i (τ y) * _root_.deriv (v i) (τ y)) := by
      refine generated_finset_sum w y₀ _ _ fun i hi => ?_
      exact (gpoly_v (MvPolynomial.pderiv i Q)).mul (g_dv_lt i (Finset.ne_of_mem_erase hi))
    refine (((gc (-1)).mul ginvS).mul hsum_gen).congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hy₀, hS_ne_y] with y hy hSy
    have hch := hchain (τ y) (hτ_pos y hy)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ top)] at hch
    have hgtop : g top (τ y) = S (τ y) := rfl
    rw [hgtop] at hch
    have hsol : S (τ y) * _root_.deriv (v top) (τ y) =
        -(∑ i ∈ Finset.univ.erase top, g i (τ y) * _root_.deriv (v i) (τ y)) :=
      eq_neg_of_add_eq_zero_left hch
    dsimp only [Pi.mul_apply]
    calc (-1 : ℂ) * (S (τ y))⁻¹ * ∑ i ∈ Finset.univ.erase top, g i (τ y) * _root_.deriv (v i) (τ y)
        = (S (τ y))⁻¹ * (-(∑ i ∈ Finset.univ.erase top, g i (τ y) * _root_.deriv (v i) (τ y))) := by ring
      _ = (S (τ y))⁻¹ * (S (τ y) * _root_.deriv (v top) (τ y)) := by rw [← hsol]
      _ = _root_.deriv (v top) (τ y) := by rw [← mul_assoc, inv_mul_cancel₀ hSy, one_mul]
  have g_dv : ∀ i : Fin (n + 1), Generated w y₀ (fun y => _root_.deriv (v i) (τ y)) := by
    intro i
    by_cases hi : i = top
    · subst hi; exact g_dv_top
    · exact g_dv_lt i hi
  have hdv_y : ∀ i : Fin (n + 1), Generated w y₀ (_root_.deriv (w (Sum.inl i))) := by
    intro i
    refine (g_τ_deriv.mul (g_dv i)).congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hy₀] with y hy
    have hcomp := (hd_v (τ y) (hτ_pos y hy) i).hasDerivAt.scomp y (hτ_deriv y hy)
    have hcomp' : HasDerivAt (w (Sum.inl i)) ((-(2 * c ^ 2)⁻¹ * (τ y) ^ 3) • _root_.deriv (v i) (τ y)) y :=
      hcomp
    simpa [Complex.real_smul] using hcomp'.deriv.symm
  have hclosed_w : ∀ idx : ι, Generated w y₀ (_root_.deriv (w idx)) := by
    intro idx
    rcases idx with i | k
    · exact hdv_y i
    · fin_cases k
      · -- deriv (fun y => (S (τ y))⁻¹) = -(S (τ y))⁻² * deriv (fun y => S (τ y)) y
        have hdS_gen : Generated w y₀ (fun y => _root_.deriv (fun t => S (τ t)) y) := by
          have hS_chain : Generated w y₀
              (fun y => ∑ i : Fin (n + 1),
                MvPolynomial.eval (fun j => v j (τ y)) (MvPolynomial.pderiv i (MvPolynomial.pderiv top Q)) *
                  _root_.deriv (w (Sum.inl i)) y) :=
            generated_finset_sum w y₀ _ _ fun i _ => (gpoly_v _).mul (hdv_y i)
          refine hS_chain.congr ?_
          filter_upwards [isOpen_Ioi.mem_nhds hy₀] with y hy
          have hpc := polynomial_chain (MvPolynomial.pderiv top Q) (fun i => w (Sum.inl i))
            (fun i => _root_.deriv (w (Sum.inl i))) y
            (fun i => ((hd_v (τ y) (hτ_pos y hy) i).comp y (hτ_deriv y hy).differentiableAt).hasDerivAt)
          exact hpc.deriv.symm
        refine (((gc (-1)).mul (ginvS.pow 2)).mul hdS_gen).congr ?_
        filter_upwards [isOpen_Ioi.mem_nhds hy₀, hS_ne_y] with y hy hSy
        have hS_comp : DifferentiableAt ℝ (fun t => S (τ t)) y :=
          (hS_diff (τ y) (hτ_pos y hy)).comp y (hτ_deriv y hy).differentiableAt
        have hi := (hS_comp.hasDerivAt.fun_inv hSy).deriv
        change (-1 : ℂ) * ((S (τ y))⁻¹) ^ 2 * _root_.deriv (fun t => S (τ t)) y =
          _root_.deriv (fun t => (S (τ t))⁻¹) y
        rw [hi]; ring
      · -- deriv (fun y => (τ y : ℂ)⁻¹) = -τ'(y) * (τ y)⁻² = (2 c²)⁻¹ * τ y
        refine ((gc (((2 * c ^ 2)⁻¹ : ℝ) : ℂ)).mul gτ).congr ?_
        filter_upwards [isOpen_Ioi.mem_nhds hy₀] with y hy
        have hτy := hτ_pos y hy
        have hτc : HasDerivAt (fun t : ℝ => (τ t : ℂ)) ((-(2 * c ^ 2)⁻¹ * (τ y) ^ 3 : ℝ) : ℂ) y :=
          (hτ_deriv y hy).ofReal_comp
        have hi := (hτc.fun_inv (Complex.ofReal_ne_zero.mpr hτy.ne')).deriv
        change (((2 * c ^ 2)⁻¹ : ℝ) : ℂ) * (τ y : ℂ) = _root_.deriv (fun t : ℝ => ((τ t : ℝ) : ℂ)⁻¹) y
        rw [hi]
        push_cast
        have hτc_ne : (τ y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτy.ne'
        field_simp [hτc_ne]
  exact ⟨ι, inferInstance, w, y₀, hy₀, hsmooth_w, hclosed_w, gτ, gτ_inv, gf⟩

/-- Master contradiction lemma: if `modeSeries ms (y : ℂ)` lies in a finite differential algebra
`Generated w y₀` at some `y₀ > 0`, then we get `False` via `autonomous_readout` + Identity Theorem
+ `modeSeries_no_const_ade`. -/
private lemma false_of_modeSeries_generated (ms : ModeSeq) {ι : Type} [Fintype ι]
    (w : ι → ℝ → ℂ) {y₀ : ℝ} (hy₀ : 0 < y₀)
    (hsmooth : ∀ᶠ y in 𝓝 y₀, ∀ i, DifferentiableAt ℝ (w i) y)
    (hclosed : ∀ i, Generated w y₀ (_root_.deriv (w i)))
    (hreadout : Generated w y₀ (fun y : ℝ => modeSeries ms (y : ℂ))) : False := by
  obtain ⟨R, hR_ne, hR_nhds⟩ :=
    autonomous_readout w y₀ (fun y : ℝ => modeSeries ms (y : ℂ)) hreadout hsmooth hclosed
  let evalR : ℝ → ℂ := fun y =>
    MvPolynomial.eval
      (fun j : Fin (Fintype.card ι + 1) => iteratedDeriv j.val (fun t : ℝ => modeSeries ms (t : ℂ)) y) R
  have hevalR_ana : AnalyticOnNhd ℝ evalR (Set.Ioi 0) := by
    intro y hy
    clear hR_ne hR_nhds
    dsimp only [evalR]
    induction R using MvPolynomial.induction_on with
    | C a => simpa using analyticAt_const
    | add A B hA hB => simp only [map_add]; exact hA.add hB
    | mul_X A j hA =>
      have hjet : AnalyticAt ℝ (iteratedDeriv j.val (fun t : ℝ => modeSeries ms (t : ℂ))) y := by
        rw [iteratedDeriv_eq_iterate]
        exact ((modeSeries_real_analyticOnNhd ms).iterated_deriv j.val) y hy
      simp only [map_mul, MvPolynomial.eval_X]
      exact hA.mul hjet
  have hevalR_zero : Set.EqOn evalR 0 (Set.Ioi 0) :=
    hevalR_ana.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_Ioi hy₀
      ((Filter.Eventually.filter_mono nhdsWithin_le_nhds hR_nhds).frequently)
  have hR_zero : R = 0 := by
    refine modeSeries_no_const_ade ms R fun x hx => ?_
    have h0 := hevalR_zero hx
    dsimp only [evalR] at h0
    have hjet : (fun j : Fin (Fintype.card ι + 1) =>
        iteratedDeriv j.val (fun t : ℝ => modeSeries ms (t : ℂ)) x) =
        fun j : Fin (Fintype.card ι + 1) => iteratedDeriv j.val (modeSeries ms) (x : ℂ) := by
      ext j; exact iteratedDeriv_modeSeries_ofReal ms j.val hx
    rw [hjet] at h0
    exact h0
  exact hR_ne hR_zero

/-! #### Odd-Dimension (`d = 1` and `d = 3`) Bose & Fermi Differential Transcendence over `ℂ[T]` -/

/-- **1D Relativistic Bose Pressure Differential Transcendence over `ℂ[T]`**:
For every positive mass `m > 0`, `bosePressure1D m` satisfies NO nonzero algebraic differential
equation over `ℂ[T]`. -/
theorem bosePressure1D_no_ade {m : ℝ} (hm : 0 < m) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ T : ℝ, 0 < T →
      MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (bosePressure1D m t : ℂ)) T)
        (evalU P (T : ℂ)) = 0) :
    P = 0 := by
  by_contra hP_ne
  let c : ℝ := m / (2 * Real.pi)
  have hc : 0 < c := div_pos hm (by positivity)
  have hf_eq : ∀ T : ℝ, 0 < T →
      (bosePressure1D m T : ℂ) = (2 * (Real.pi : ℂ)) * (T : ℂ) ^ 2 * (H1 (c ^ 2 / T ^ 2) : ℂ) := by
    intro T hT
    rw [bosePressure1D_eq_H1 hT]
    have hy : m ^ 2 / (2 * Real.pi * T) ^ 2 = c ^ 2 / T ^ 2 := by dsimp only [c]; field_simp
    rw [hy]; push_cast; ring
  have hf_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun T : ℝ => (bosePressure1D m T : ℂ)) (Set.Ioi 0) := by
    have hmap : MapsTo (fun T : ℝ => c ^ 2 / T ^ 2) (Set.Ioi 0) (Set.Ioi 0) := fun T (hT : 0 < T) => by
      change 0 < c ^ 2 / T ^ 2; positivity
    have hdiv : ContDiffOn ℝ (⊤ : ℕ∞) (fun T : ℝ => c ^ 2 / T ^ 2) (Set.Ioi 0) :=
      contDiffOn_const.div (contDiffOn_id.pow 2) fun T (hT : 0 < T) => pow_ne_zero 2 hT.ne'
    have hH1_comp : ContDiffOn ℝ (⊤ : ℕ∞) (fun T : ℝ => (H1 (c ^ 2 / T ^ 2) : ℂ)) (Set.Ioi 0) :=
      H1_contDiffOn.comp hdiv hmap
    have hrhs : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun T : ℝ => (2 * (Real.pi : ℂ)) * (T : ℂ) ^ 2 * (H1 (c ^ 2 / T ^ 2) : ℂ)) (Set.Ioi 0) :=
      (contDiffOn_const.mul ((Complex.ofRealCLM.contDiff.contDiffOn).pow 2)).mul hH1_comp
    exact hrhs.congr fun T hT => hf_eq T hT
  obtain ⟨ι, _, w, y₀, hy₀, hsmooth, hclosed, gτ, gτ_inv, gf⟩ :=
    pullback_ordinary_algebra hf_smooth hc P hP_ne hP
  have gc : ∀ a : ℂ, Generated w y₀ (fun _ => a) := fun a => Generated.const a
  have gH1 : Generated w y₀ (fun y : ℝ => (H1 y : ℂ)) := by
    refine (((gc ((2 * (Real.pi : ℂ))⁻¹)).mul (gτ_inv.pow 2)).mul gf).congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hy₀] with y (hy : 0 < y)
    have hτ_pos : 0 < c / Real.sqrt y := div_pos hc (Real.sqrt_pos.mpr hy)
    dsimp only [Pi.mul_apply, Pi.pow_apply]
    rw [hf_eq (c / Real.sqrt y) hτ_pos]
    have hy_eq : c ^ 2 / (c / Real.sqrt y) ^ 2 = y := by
      have hc_ne : c ≠ 0 := hc.ne'
      rw [div_pow c (Real.sqrt y), Real.sq_sqrt hy.le]
      field_simp [hc_ne, hy.ne']
    rw [hy_eq]
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hτne : ((c / Real.sqrt y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ_pos.ne'
    field_simp [hpi, hτne]
  have gH1_d2 : Generated w y₀ (iteratedDeriv 2 (fun y : ℝ => (H1 y : ℂ))) := by
    have hd1 : Generated w y₀ (_root_.deriv (fun y : ℝ => (H1 y : ℂ))) := gH1.deriv hsmooth hclosed
    have hd2 : Generated w y₀ (_root_.deriv (_root_.deriv (fun y : ℝ => (H1 y : ℂ)))) :=
      hd1.deriv hsmooth hclosed
    refine hd2.congr (Eventually.of_forall fun y => ?_)
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have gS : Generated w y₀ (fun y : ℝ => modeSeries boseModes (y : ℂ)) := by
    refine ((((gc 4).mul gH1_d2).add ((gc ((c ^ 2 : ℂ)⁻¹)).mul (gτ.pow 2))).sub
      ((gc ((2 * (c : ℂ) ^ 3)⁻¹)).mul (gτ.pow 3))).congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hy₀] with y (hy : 0 < y)
    dsimp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    rw [H1_deriv2_complex hy]
    have hsq2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
    have hsq3 : Real.sqrt y ^ 3 = y ^ ((3 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy.le]; norm_num
    have hτ2 : (((c / Real.sqrt y : ℝ) : ℂ)) ^ 2 = (c : ℂ) ^ 2 / (y : ℂ) := by
      have : (c / Real.sqrt y) ^ 2 = c ^ 2 / y := by rw [div_pow, hsq2]
      exact_mod_cast this
    have hτ3 : (((c / Real.sqrt y : ℝ) : ℂ)) ^ 3 = (c : ℂ) ^ 3 / ((y ^ ((3 : ℝ) / 2) : ℝ) : ℂ) := by
      have : (c / Real.sqrt y) ^ 3 = c ^ 3 / y ^ ((3 : ℝ) / 2) := by rw [div_pow, hsq3]
      exact_mod_cast this
    rw [hτ2, hτ3]
    have hc_ne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    have hy_ne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    have hy32_ne : ((y ^ ((3 : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    field_simp [hc_ne, hy_ne, hy32_ne]
    ring
  exact false_of_modeSeries_generated boseModes w hy₀ hsmooth hclosed gS

/-- **1D Relativistic Fermi Pressure Differential Transcendence over `ℂ[T]`**:
For every positive mass `m > 0`, `fermiPressure1D m` satisfies NO nonzero algebraic differential
equation over `ℂ[T]`. -/
theorem fermiPressure1D_no_ade {m : ℝ} (hm : 0 < m) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ T : ℝ, 0 < T →
      MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (fermiPressure1D m t : ℂ)) T)
        (evalU P (T : ℂ)) = 0) :
    P = 0 := by
  by_contra hP_ne
  let c : ℝ := m / (2 * Real.pi)
  have hc : 0 < c := div_pos hm (by positivity)
  let H1F : ℝ → ℂ := fun y => (H1 y : ℂ) - (1 / 2 : ℂ) * (H1 (4 * y) : ℂ)
  have hf_eq : ∀ T : ℝ, 0 < T →
      (fermiPressure1D m T : ℂ) = (2 * (Real.pi : ℂ)) * (T : ℂ) ^ 2 * H1F (c ^ 2 / T ^ 2) := by
    intro T hT
    rw [fermiPressure1D_doubling hm hT, bosePressure1D_eq_H1 hT, bosePressure1D_eq_H1 hT]
    have hy1 : m ^ 2 / (2 * Real.pi * T) ^ 2 = c ^ 2 / T ^ 2 := by dsimp only [c]; field_simp
    have hy2 : (2 * m) ^ 2 / (2 * Real.pi * T) ^ 2 = 4 * (c ^ 2 / T ^ 2) := by
      dsimp only [c]; field_simp; ring
    rw [hy1, hy2]
    dsimp only [H1F]; push_cast; ring
  have hH1F_smooth : ContDiffOn ℝ (⊤ : ℕ∞) H1F (Set.Ioi 0) := by
    have h4 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => (H1 (4 * y) : ℂ)) (Set.Ioi 0) :=
      H1_contDiffOn.comp (contDiffOn_const.mul contDiffOn_id) (fun y (hy : 0 < y) => by change 0 < 4 * y; linarith)
    exact H1_contDiffOn.sub (contDiffOn_const.mul h4)
  have hf_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun T : ℝ => (fermiPressure1D m T : ℂ)) (Set.Ioi 0) := by
    have hmap : MapsTo (fun T : ℝ => c ^ 2 / T ^ 2) (Set.Ioi 0) (Set.Ioi 0) := fun T (hT : 0 < T) => by
      change 0 < c ^ 2 / T ^ 2; positivity
    have hdiv : ContDiffOn ℝ (⊤ : ℕ∞) (fun T : ℝ => c ^ 2 / T ^ 2) (Set.Ioi 0) :=
      contDiffOn_const.div (contDiffOn_id.pow 2) fun T (hT : 0 < T) => pow_ne_zero 2 hT.ne'
    have hrhs : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun T : ℝ => (2 * (Real.pi : ℂ)) * (T : ℂ) ^ 2 * H1F (c ^ 2 / T ^ 2)) (Set.Ioi 0) :=
      (contDiffOn_const.mul ((Complex.ofRealCLM.contDiff.contDiffOn).pow 2)).mul (hH1F_smooth.comp hdiv hmap)
    exact hrhs.congr fun T hT => hf_eq T hT
  obtain ⟨ι, _, w, y₀, hy₀, hsmooth, hclosed, gτ, gτ_inv, gf⟩ :=
    pullback_ordinary_algebra hf_smooth hc P hP_ne hP
  have gc : ∀ a : ℂ, Generated w y₀ (fun _ => a) := fun a => Generated.const a
  have gH1F : Generated w y₀ H1F := by
    refine (((gc ((2 * (Real.pi : ℂ))⁻¹)).mul (gτ_inv.pow 2)).mul gf).congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hy₀] with y (hy : 0 < y)
    have hτ_pos : 0 < c / Real.sqrt y := div_pos hc (Real.sqrt_pos.mpr hy)
    dsimp only [Pi.mul_apply, Pi.pow_apply]
    rw [hf_eq (c / Real.sqrt y) hτ_pos]
    have hy_eq : c ^ 2 / (c / Real.sqrt y) ^ 2 = y := by
      have hc_ne : c ≠ 0 := hc.ne'
      rw [div_pow c (Real.sqrt y), Real.sq_sqrt hy.le]
      field_simp [hc_ne, hy.ne']
    rw [hy_eq]
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hτne : ((c / Real.sqrt y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ_pos.ne'
    field_simp [hpi, hτne]
  have gH1F_d2 : Generated w y₀ (iteratedDeriv 2 H1F) := by
    have hd1 := gH1F.deriv hsmooth hclosed
    have hd2 := hd1.deriv hsmooth hclosed
    refine hd2.congr (Eventually.of_forall fun y => ?_)
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hH1F_d2_eq : ∀ y : ℝ, 0 < y →
      iteratedDeriv 2 H1F y = -(1 / 4 : ℂ) * modeSeries fermiModes (y : ℂ) + 1 / (4 * (y : ℂ)) := by
    intro y hy
    have h4y : 0 < 4 * y := by linarith
    have hd1 : ∀ t : ℝ, 0 < t →
        _root_.deriv H1F t = _root_.deriv (fun s : ℝ => (H1 s : ℂ)) t -
          2 * _root_.deriv (fun s : ℝ => (H1 s : ℂ)) (4 * t) := by
      intro t ht
      have h1 := ((H1_contDiffOn.contDiffAt (isOpen_Ioi.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
      have h2 := (((H1_contDiffOn.contDiffAt (isOpen_Ioi.mem_nhds (by linarith : 0 < 4 * t))).differentiableAt
        (by simp)).hasDerivAt).scomp t ((hasDerivAt_id' t).const_mul (4 : ℝ))
      have hsub := h1.fun_sub (h2.const_mul (1 / 2 : ℂ))
      refine hsub.deriv.trans ?_
      simp only [Complex.real_smul]; push_cast; ring
    have hev : _root_.deriv H1F =ᶠ[𝓝 y] fun t : ℝ =>
        _root_.deriv (fun s : ℝ => (H1 s : ℂ)) t -
          2 * _root_.deriv (fun s : ℝ => (H1 s : ℂ)) (4 * t) := by
      filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht; exact hd1 t ht
    have h2 : iteratedDeriv 2 H1F y =
        iteratedDeriv 2 (fun s : ℝ => (H1 s : ℂ)) y -
          8 * iteratedDeriv 2 (fun s : ℝ => (H1 s : ℂ)) (4 * y) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq]
      have hsm_d1 : ContDiffOn ℝ (⊤ : ℕ∞) (_root_.deriv (fun s : ℝ => (H1 s : ℂ))) (Set.Ioi 0) := by
        simpa [iteratedDeriv_one] using contDiffOn_iteratedDeriv_infty isOpen_Ioi H1_contDiffOn 1
      have ha := ((hsm_d1.contDiffAt (isOpen_Ioi.mem_nhds hy)).differentiableAt (by simp)).hasDerivAt
      have hb0 := (((hsm_d1.contDiffAt (isOpen_Ioi.mem_nhds h4y)).differentiableAt (by simp)).hasDerivAt).scomp y
        ((hasDerivAt_id' y).const_mul (4 : ℝ))
      have hb : HasDerivAt (fun t : ℝ => _root_.deriv (fun s : ℝ => (H1 s : ℂ)) (4 * t))
          ((4 * 1 : ℝ) • _root_.deriv (_root_.deriv (fun s : ℝ => (H1 s : ℂ))) (4 * y)) y := hb0
      rw [(ha.fun_sub (hb.const_mul (2 : ℂ))).deriv]
      have h2a : iteratedDeriv 2 (fun s : ℝ => (H1 s : ℂ)) y =
          _root_.deriv (_root_.deriv (fun s : ℝ => (H1 s : ℂ))) y := by
        rw [iteratedDeriv_succ, iteratedDeriv_one]
      have h2b : iteratedDeriv 2 (fun s : ℝ => (H1 s : ℂ)) (4 * y) =
          _root_.deriv (_root_.deriv (fun s : ℝ => (H1 s : ℂ))) (4 * y) := by
        rw [iteratedDeriv_succ, iteratedDeriv_one]
      rw [h2a, h2b]; simp only [Complex.real_smul]; push_cast; ring
    rw [h2, H1_deriv2_complex hy, H1_deriv2_complex h4y]
    have h4pow : (4 * y) ^ ((3 : ℝ) / 2) = 8 * y ^ ((3 : ℝ) / 2) := by
      rw [Real.mul_rpow (by norm_num) hy.le]
      have h43 : (4 : ℝ) ^ ((3 : ℝ) / 2) = 8 := by
        have : (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num
        rw [this, ← Real.rpow_mul (by norm_num)]; norm_num
      rw [h43]
    rw [h4pow]
    push_cast
    have hy_ne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    have hy32_ne : ((y ^ ((3 : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    have hcancel := modeSeries_bose_sub_fermi hy
    have h4y_cast : (4 * (y : ℂ)) = ((4 * y : ℝ) : ℂ) := by push_cast; rfl
    rw [← h4y_cast] at hcancel
    linear_combination (1 / 4 : ℂ) * hcancel
  have gS : Generated w y₀ (fun y : ℝ => modeSeries fermiModes (y : ℂ)) := by
    refine (((gc (-4)).mul gH1F_d2).add ((gc ((c ^ 2 : ℂ)⁻¹)).mul (gτ.pow 2))).congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hy₀] with y (hy : 0 < y)
    dsimp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    rw [hH1F_d2_eq y hy]
    have hsq2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
    have hτ2 : (((c / Real.sqrt y : ℝ) : ℂ)) ^ 2 = (c : ℂ) ^ 2 / (y : ℂ) := by
      have : (c / Real.sqrt y) ^ 2 = c ^ 2 / y := by rw [div_pow, hsq2]
      exact_mod_cast this
    rw [hτ2]
    have hc_ne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    have hy_ne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    field_simp [hc_ne, hy_ne]
    ring
  exact false_of_modeSeries_generated fermiModes w hy₀ hsmooth hclosed gS

/-- **3D Relativistic Bose Pressure Differential Transcendence over `ℂ[T]`**:
For every positive mass `m > 0`, `bosePressure3D m` satisfies NO nonzero algebraic differential
equation over `ℂ[T]`. -/
theorem bosePressure3D_no_ade {m : ℝ} (hm : 0 < m) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ T : ℝ, 0 < T →
      MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (bosePressure3D m t : ℂ)) T)
        (evalU P (T : ℂ)) = 0) :
    P = 0 := by
  by_contra hP_ne
  let c : ℝ := m / (2 * Real.pi)
  have hc : 0 < c := div_pos hm (by positivity)
  have hf_eq : ∀ T : ℝ, 0 < T →
      (bosePressure3D m T : ℂ) = (8 * (Real.pi : ℂ) ^ 3) * (T : ℂ) ^ 4 * (H3 (c ^ 2 / T ^ 2) : ℂ) := by
    intro T hT
    rw [bosePressure3D_eq_H3 hT]
    have hy : m ^ 2 / (2 * Real.pi * T) ^ 2 = c ^ 2 / T ^ 2 := by dsimp only [c]; field_simp
    rw [hy]; push_cast; ring
  have hf_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun T : ℝ => (bosePressure3D m T : ℂ)) (Set.Ioi 0) := by
    have hmap : MapsTo (fun T : ℝ => c ^ 2 / T ^ 2) (Set.Ioi 0) (Set.Ioi 0) := fun T (hT : 0 < T) => by
      change 0 < c ^ 2 / T ^ 2; positivity
    have hdiv : ContDiffOn ℝ (⊤ : ℕ∞) (fun T : ℝ => c ^ 2 / T ^ 2) (Set.Ioi 0) :=
      contDiffOn_const.div (contDiffOn_id.pow 2) fun T (hT : 0 < T) => pow_ne_zero 2 hT.ne'
    have hH3_comp : ContDiffOn ℝ (⊤ : ℕ∞) (fun T : ℝ => (H3 (c ^ 2 / T ^ 2) : ℂ)) (Set.Ioi 0) :=
      H3_contDiffOn.comp hdiv hmap
    have hrhs : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun T : ℝ => (8 * (Real.pi : ℂ) ^ 3) * (T : ℂ) ^ 4 * (H3 (c ^ 2 / T ^ 2) : ℂ)) (Set.Ioi 0) :=
      (contDiffOn_const.mul ((Complex.ofRealCLM.contDiff.contDiffOn).pow 4)).mul hH3_comp
    exact hrhs.congr fun T hT => hf_eq T hT
  obtain ⟨ι, _, w, y₀, hy₀, hsmooth, hclosed, gτ, gτ_inv, gf⟩ :=
    pullback_ordinary_algebra hf_smooth hc P hP_ne hP
  have gc : ∀ a : ℂ, Generated w y₀ (fun _ => a) := fun a => Generated.const a
  have gH3 : Generated w y₀ (fun y : ℝ => (H3 y : ℂ)) := by
    refine (((gc ((8 * (Real.pi : ℂ) ^ 3)⁻¹)).mul (gτ_inv.pow 4)).mul gf).congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hy₀] with y (hy : 0 < y)
    have hτ_pos : 0 < c / Real.sqrt y := div_pos hc (Real.sqrt_pos.mpr hy)
    dsimp only [Pi.mul_apply, Pi.pow_apply]
    rw [hf_eq (c / Real.sqrt y) hτ_pos]
    have hy_eq : c ^ 2 / (c / Real.sqrt y) ^ 2 = y := by
      have hc_ne : c ≠ 0 := hc.ne'
      rw [div_pow c (Real.sqrt y), Real.sq_sqrt hy.le]
      field_simp [hc_ne, hy.ne']
    rw [hy_eq]
    have hpi : (8 * (Real.pi : ℂ) ^ 3) ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    have hτne : ((c / Real.sqrt y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ_pos.ne'
    field_simp [hpi, hτne]
  have gH1 : Generated w y₀ (fun y : ℝ => (H1 y : ℂ)) := by
    refine ((gc (-(4 * (Real.pi : ℂ)))).mul (gH3.deriv hsmooth hclosed)).congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hy₀] with y (hy : 0 < y)
    dsimp only [Pi.mul_apply]
    have hd := (H3_deriv hy).ofReal_comp.deriv
    rw [hd]
    have hpi : (4 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    push_cast
    field_simp [hpi]
  have gH1_d2 : Generated w y₀ (iteratedDeriv 2 (fun y : ℝ => (H1 y : ℂ))) := by
    have hd1 := gH1.deriv hsmooth hclosed
    have hd2 := hd1.deriv hsmooth hclosed
    refine hd2.congr (Eventually.of_forall fun y => ?_)
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have gS : Generated w y₀ (fun y : ℝ => modeSeries boseModes (y : ℂ)) := by
    refine ((((gc 4).mul gH1_d2).add ((gc ((c ^ 2 : ℂ)⁻¹)).mul (gτ.pow 2))).sub
      ((gc ((2 * (c : ℂ) ^ 3)⁻¹)).mul (gτ.pow 3))).congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hy₀] with y (hy : 0 < y)
    dsimp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    rw [H1_deriv2_complex hy]
    have hsq2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
    have hsq3 : Real.sqrt y ^ 3 = y ^ ((3 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hy.le]; norm_num
    have hτ2 : (((c / Real.sqrt y : ℝ) : ℂ)) ^ 2 = (c : ℂ) ^ 2 / (y : ℂ) := by
      have : (c / Real.sqrt y) ^ 2 = c ^ 2 / y := by rw [div_pow, hsq2]
      exact_mod_cast this
    have hτ3 : (((c / Real.sqrt y : ℝ) : ℂ)) ^ 3 = (c : ℂ) ^ 3 / ((y ^ ((3 : ℝ) / 2) : ℝ) : ℂ) := by
      have : (c / Real.sqrt y) ^ 3 = c ^ 3 / y ^ ((3 : ℝ) / 2) := by rw [div_pow, hsq3]
      exact_mod_cast this
    rw [hτ2, hτ3]
    have hc_ne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    have hy_ne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    have hy32_ne : ((y ^ ((3 : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    field_simp [hc_ne, hy_ne, hy32_ne]
    ring
  exact false_of_modeSeries_generated boseModes w hy₀ hsmooth hclosed gS

/-- **3D Relativistic Fermi Pressure Differential Transcendence over `ℂ[T]`**:
For every positive mass `m > 0`, `fermiPressure3D m` satisfies NO nonzero algebraic differential
equation over `ℂ[T]`. -/
theorem fermiPressure3D_no_ade {m : ℝ} (hm : 0 < m) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ T : ℝ, 0 < T →
      MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (fermiPressure3D m t : ℂ)) T)
        (evalU P (T : ℂ)) = 0) :
    P = 0 := by
  by_contra hP_ne
  let c : ℝ := m / (2 * Real.pi)
  have hc : 0 < c := div_pos hm (by positivity)
  let H3F : ℝ → ℂ := fun y => (H3 y : ℂ) - (1 / 8 : ℂ) * (H3 (4 * y) : ℂ)
  let H1F : ℝ → ℂ := fun y => (H1 y : ℂ) - (1 / 2 : ℂ) * (H1 (4 * y) : ℂ)
  have hf_eq : ∀ T : ℝ, 0 < T →
      (fermiPressure3D m T : ℂ) = (8 * (Real.pi : ℂ) ^ 3) * (T : ℂ) ^ 4 * H3F (c ^ 2 / T ^ 2) := by
    intro T hT
    rw [fermiPressure3D_doubling hm hT, bosePressure3D_eq_H3 hT, bosePressure3D_eq_H3 hT]
    have hy1 : m ^ 2 / (2 * Real.pi * T) ^ 2 = c ^ 2 / T ^ 2 := by dsimp only [c]; field_simp
    have hy2 : (2 * m) ^ 2 / (2 * Real.pi * T) ^ 2 = 4 * (c ^ 2 / T ^ 2) := by
      dsimp only [c]; field_simp; ring
    rw [hy1, hy2]
    dsimp only [H3F]; push_cast; ring
  have hH3F_smooth : ContDiffOn ℝ (⊤ : ℕ∞) H3F (Set.Ioi 0) := by
    have h4 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => (H3 (4 * y) : ℂ)) (Set.Ioi 0) :=
      H3_contDiffOn.comp (contDiffOn_const.mul contDiffOn_id) (fun y (hy : 0 < y) => by change 0 < 4 * y; linarith)
    exact H3_contDiffOn.sub (contDiffOn_const.mul h4)
  have hf_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun T : ℝ => (fermiPressure3D m T : ℂ)) (Set.Ioi 0) := by
    have hmap : MapsTo (fun T : ℝ => c ^ 2 / T ^ 2) (Set.Ioi 0) (Set.Ioi 0) := fun T (hT : 0 < T) => by
      change 0 < c ^ 2 / T ^ 2; positivity
    have hdiv : ContDiffOn ℝ (⊤ : ℕ∞) (fun T : ℝ => c ^ 2 / T ^ 2) (Set.Ioi 0) :=
      contDiffOn_const.div (contDiffOn_id.pow 2) fun T (hT : 0 < T) => pow_ne_zero 2 hT.ne'
    have hrhs : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun T : ℝ => (8 * (Real.pi : ℂ) ^ 3) * (T : ℂ) ^ 4 * H3F (c ^ 2 / T ^ 2)) (Set.Ioi 0) :=
      (contDiffOn_const.mul ((Complex.ofRealCLM.contDiff.contDiffOn).pow 4)).mul (hH3F_smooth.comp hdiv hmap)
    exact hrhs.congr fun T hT => hf_eq T hT
  obtain ⟨ι, _, w, y₀, hy₀, hsmooth, hclosed, gτ, gτ_inv, gf⟩ :=
    pullback_ordinary_algebra hf_smooth hc P hP_ne hP
  have gc : ∀ a : ℂ, Generated w y₀ (fun _ => a) := fun a => Generated.const a
  have gH3F : Generated w y₀ H3F := by
    refine (((gc ((8 * (Real.pi : ℂ) ^ 3)⁻¹)).mul (gτ_inv.pow 4)).mul gf).congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hy₀] with y (hy : 0 < y)
    have hτ_pos : 0 < c / Real.sqrt y := div_pos hc (Real.sqrt_pos.mpr hy)
    dsimp only [Pi.mul_apply, Pi.pow_apply]
    rw [hf_eq (c / Real.sqrt y) hτ_pos]
    have hy_eq : c ^ 2 / (c / Real.sqrt y) ^ 2 = y := by
      have hc_ne : c ≠ 0 := hc.ne'
      rw [div_pow c (Real.sqrt y), Real.sq_sqrt hy.le]
      field_simp [hc_ne, hy.ne']
    rw [hy_eq]
    have hpi : (8 * (Real.pi : ℂ) ^ 3) ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    have hτne : ((c / Real.sqrt y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ_pos.ne'
    field_simp [hpi, hτne]
  have gH1F : Generated w y₀ H1F := by
    refine ((gc (-(4 * (Real.pi : ℂ)))).mul (gH3F.deriv hsmooth hclosed)).congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hy₀] with y (hy : 0 < y)
    have h4y : 0 < 4 * y := by linarith
    have h1 := (H3_deriv hy).ofReal_comp
    have h20 := ((H3_deriv h4y).ofReal_comp).scomp y ((hasDerivAt_id' y).const_mul (4 : ℝ))
    have h2 : HasDerivAt (fun t : ℝ => (H3 (4 * t) : ℂ))
        ((4 * 1 : ℝ) • ((-(4 * Real.pi)⁻¹ * H1 (4 * y) : ℝ) : ℂ)) y := h20
    have hd := (h1.fun_sub (h2.const_mul (1 / 8 : ℂ))).deriv
    change -(4 * (Real.pi : ℂ)) * _root_.deriv H3F y = H1F y
    rw [hd]
    dsimp only [H1F]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simp only [Complex.real_smul]
    push_cast
    field_simp [hpi]
    ring
  have gH1F_d2 : Generated w y₀ (iteratedDeriv 2 H1F) := by
    have hd1 := gH1F.deriv hsmooth hclosed
    have hd2 := hd1.deriv hsmooth hclosed
    refine hd2.congr (Eventually.of_forall fun y => ?_)
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hH1F_d2_eq : ∀ y : ℝ, 0 < y →
      iteratedDeriv 2 H1F y = -(1 / 4 : ℂ) * modeSeries fermiModes (y : ℂ) + 1 / (4 * (y : ℂ)) := by
    intro y hy
    have h4y : 0 < 4 * y := by linarith
    have hd1 : ∀ t : ℝ, 0 < t →
        _root_.deriv H1F t = _root_.deriv (fun s : ℝ => (H1 s : ℂ)) t -
          2 * _root_.deriv (fun s : ℝ => (H1 s : ℂ)) (4 * t) := by
      intro t ht
      have h1 := ((H1_contDiffOn.contDiffAt (isOpen_Ioi.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
      have h2 := (((H1_contDiffOn.contDiffAt (isOpen_Ioi.mem_nhds (by linarith : 0 < 4 * t))).differentiableAt
        (by simp)).hasDerivAt).scomp t ((hasDerivAt_id' t).const_mul (4 : ℝ))
      have hsub := h1.fun_sub (h2.const_mul (1 / 2 : ℂ))
      refine hsub.deriv.trans ?_
      simp only [Complex.real_smul]; push_cast; ring
    have hev : _root_.deriv H1F =ᶠ[𝓝 y] fun t : ℝ =>
        _root_.deriv (fun s : ℝ => (H1 s : ℂ)) t -
          2 * _root_.deriv (fun s : ℝ => (H1 s : ℂ)) (4 * t) := by
      filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht; exact hd1 t ht
    have h2 : iteratedDeriv 2 H1F y =
        iteratedDeriv 2 (fun s : ℝ => (H1 s : ℂ)) y -
          8 * iteratedDeriv 2 (fun s : ℝ => (H1 s : ℂ)) (4 * y) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one, hev.deriv_eq]
      have hsm_d1 : ContDiffOn ℝ (⊤ : ℕ∞) (_root_.deriv (fun s : ℝ => (H1 s : ℂ))) (Set.Ioi 0) := by
        simpa [iteratedDeriv_one] using contDiffOn_iteratedDeriv_infty isOpen_Ioi H1_contDiffOn 1
      have ha := ((hsm_d1.contDiffAt (isOpen_Ioi.mem_nhds hy)).differentiableAt (by simp)).hasDerivAt
      have hb0 := (((hsm_d1.contDiffAt (isOpen_Ioi.mem_nhds h4y)).differentiableAt (by simp)).hasDerivAt).scomp y
        ((hasDerivAt_id' y).const_mul (4 : ℝ))
      have hb : HasDerivAt (fun t : ℝ => _root_.deriv (fun s : ℝ => (H1 s : ℂ)) (4 * t))
          ((4 * 1 : ℝ) • _root_.deriv (_root_.deriv (fun s : ℝ => (H1 s : ℂ))) (4 * y)) y := hb0
      rw [(ha.fun_sub (hb.const_mul (2 : ℂ))).deriv]
      have h2a : iteratedDeriv 2 (fun s : ℝ => (H1 s : ℂ)) y =
          _root_.deriv (_root_.deriv (fun s : ℝ => (H1 s : ℂ))) y := by
        rw [iteratedDeriv_succ, iteratedDeriv_one]
      have h2b : iteratedDeriv 2 (fun s : ℝ => (H1 s : ℂ)) (4 * y) =
          _root_.deriv (_root_.deriv (fun s : ℝ => (H1 s : ℂ))) (4 * y) := by
        rw [iteratedDeriv_succ, iteratedDeriv_one]
      rw [h2a, h2b]; simp only [Complex.real_smul]; push_cast; ring
    rw [h2, H1_deriv2_complex hy, H1_deriv2_complex h4y]
    have h4pow : (4 * y) ^ ((3 : ℝ) / 2) = 8 * y ^ ((3 : ℝ) / 2) := by
      rw [Real.mul_rpow (by norm_num) hy.le]
      have h43 : (4 : ℝ) ^ ((3 : ℝ) / 2) = 8 := by
        have : (4 : ℝ) = 2 ^ (2 : ℝ) := by norm_num
        rw [this, ← Real.rpow_mul (by norm_num)]; norm_num
      rw [h43]
    rw [h4pow]
    push_cast
    have hcancel := modeSeries_bose_sub_fermi hy
    have h4y_cast : (4 * (y : ℂ)) = ((4 * y : ℝ) : ℂ) := by push_cast; rfl
    rw [← h4y_cast] at hcancel
    linear_combination (1 / 4 : ℂ) * hcancel
  have gS : Generated w y₀ (fun y : ℝ => modeSeries fermiModes (y : ℂ)) := by
    refine (((gc (-4)).mul gH1F_d2).add ((gc ((c ^ 2 : ℂ)⁻¹)).mul (gτ.pow 2))).congr ?_
    filter_upwards [isOpen_Ioi.mem_nhds hy₀] with y (hy : 0 < y)
    dsimp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    rw [hH1F_d2_eq y hy]
    have hsq2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
    have hτ2 : (((c / Real.sqrt y : ℝ) : ℂ)) ^ 2 = (c : ℂ) ^ 2 / (y : ℂ) := by
      have : (c / Real.sqrt y) ^ 2 = c ^ 2 / y := by rw [div_pow, hsq2]
      exact_mod_cast this
    rw [hτ2]
    have hc_ne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    have hy_ne : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    field_simp [hc_ne, hy_ne]
    ring
  exact false_of_modeSeries_generated fermiModes w hy₀ hsmooth hclosed gS

/-! #### Rational-Coefficient (`ℂ(T)`) Differential Transcendence & Unified Parity Theorem -/

private noncomputable def clearDenomPoly {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) :
    Polynomial ℂ :=
  ∏ α ∈ P.support, (P.coeff α).denom

private noncomputable def clearDenomMvPoly {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) :
    MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
  ∑ α ∈ P.support, MvPolynomial.monomial α
    ((P.coeff α).num * ∏ β ∈ P.support.erase α, (P.coeff β).denom)

private lemma clearDenomMvPoly_coeff {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (α : Fin (r + 1) →₀ ℕ) :
    (clearDenomMvPoly P).coeff α =
      (P.coeff α).num * ∏ β ∈ P.support.erase α, (P.coeff β).denom := by
  classical
  unfold clearDenomMvPoly
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · simp
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · have hP0 : P.coeff α = 0 := MvPolynomial.notMem_support_iff.mp hα
    rw [hP0, RatFunc.num_zero, zero_mul, Finset.sum_eq_zero]
    intro β hβ
    have hne : β ≠ α := fun h => hα (h ▸ hβ)
    simp [hne]

private lemma clearDenomMvPoly_eq_zero_iff {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) :
    clearDenomMvPoly P = 0 ↔ P = 0 := by
  constructor
  · intro h0
    ext α
    have hc := congrArg (fun Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) => Q.coeff α) h0
    change (clearDenomMvPoly P).coeff α = 0 at hc
    rw [clearDenomMvPoly_coeff] at hc
    have hden_ne : (∏ β ∈ P.support.erase α, (P.coeff β).denom) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun _ _ => RatFunc.denom_ne_zero _
    have hnum0 : (P.coeff α).num = 0 := (mul_eq_zero.mp hc).resolve_right hden_ne
    exact RatFunc.num_eq_zero_iff.mp hnum0
  · rintro rfl
    simp [clearDenomMvPoly]

private lemma evalU_clearDenomMvPoly {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) {u : ℂ}
    (hu : ∀ β ∈ P.support, (P.coeff β).denom.eval u ≠ 0) :
    evalU (clearDenomMvPoly P) u = (clearDenomPoly P).eval u • evalRatU P u := by
  classical
  ext α
  rw [evalU, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom, clearDenomMvPoly_coeff,
    MvPolynomial.coeff_smul, smul_eq_mul, evalRatU, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · simp only [↓reduceIte, ratEval, clearDenomPoly, Polynomial.eval_prod]
      rw [← Finset.mul_prod_erase P.support (fun β => (P.coeff β).denom.eval u) hα,
        Polynomial.eval_mul, Polynomial.eval_prod]
      field_simp [hu α hα]
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · have hP0 : P.coeff α = 0 := MvPolynomial.notMem_support_iff.mp hα
    rw [hP0, RatFunc.num_zero, zero_mul, Polynomial.eval_zero, Finset.sum_eq_zero]
    · simp
    · intro β hβ
      rw [ite_eq_right_iff]
      intro hβα
      subst hβα
      exact absurd hβ hα

private lemma clearDenom_vanish_Ioi {r : ℕ} {f : ℝ → ℂ}
    (hf_smooth : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioi 0))
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ T : ℝ, 0 < T →
      (∀ β ∈ P.support, (P.coeff β).denom.eval (T : ℂ) ≠ 0) →
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f T) (evalRatU P (T : ℂ)) = 0) :
    ∀ T : ℝ, 0 < T →
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f T)
        (evalU (clearDenomMvPoly P) (T : ℂ)) = 0 := by
  let g : ℝ → ℂ := fun T =>
    MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f T)
      (evalU (clearDenomMvPoly P) (T : ℂ))
  have hg_cont : ContinuousOn g (Set.Ioi 0) := by
    have hpoly : ∀ Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ),
        ContinuousOn (fun T : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f T)
          (evalU Q (T : ℂ))) (Set.Ioi 0) := by
      intro Q
      induction Q using MvPolynomial.induction_on with
      | C p =>
        simp only [evalU, MvPolynomial.map_C, MvPolynomial.eval_C, Polynomial.coe_evalRingHom]
        have hp_cont : Continuous (fun z : ℂ => p.eval z) := by
          induction p using Polynomial.induction_on' with
          | add a b ha hb => simp only [Polynomial.eval_add]; exact ha.add hb
          | monomial n a => simp only [Polynomial.eval_monomial]; exact continuous_const.mul (continuous_pow n)
        exact (hp_cont.comp Complex.continuous_ofReal).continuousOn
      | add A B hA hB =>
        simp only [evalU, map_add]; exact hA.add hB
      | mul_X A j hA =>
        simp only [evalU, map_mul, MvPolynomial.map_X, MvPolynomial.eval_X]
        have hjet : ContinuousOn (iteratedDeriv j.val f) (Set.Ioi 0) :=
          (contDiffOn_iteratedDeriv_infty isOpen_Ioi hf_smooth j.val).continuousOn
        exact hA.mul hjet
    exact hpoly (clearDenomMvPoly P)
  intro T hT
  -- The denominator roots are finite, so g vanishes on a dense subset of (0, ∞) near T
  let roots : Finset ℂ := P.support.biUnion fun β => (P.coeff β).denom.roots.toFinset
  have hfreq : ∃ᶠ t in 𝓝 T, g t = 0 := by
    rw [Filter.frequently_iff]
    intro s hs
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
    let δ : ℝ := min ε (T / 2)
    have hδ : 0 < δ := lt_min hε (half_pos hT)
    have hIoo_inf : (Set.Ioo (T - δ) (T + δ)).Infinite := Set.Ioo_infinite (by linarith)
    have hC_inf : (Complex.ofReal '' Set.Ioo (T - δ) (T + δ)).Infinite :=
      hIoo_inf.image Complex.ofReal_injective.injOn
    obtain ⟨w, hw, hwnot⟩ := hC_inf.exists_notMem_finset roots
    obtain ⟨t, ht, rfl⟩ := hw
    have ht_pos : 0 < t := by
      have : δ ≤ T / 2 := min_le_right _ _
      linarith [ht.1]
    have ht_ball : t ∈ Metric.ball T ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      have : δ ≤ ε := min_le_left _ _
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hden_ne : ∀ β ∈ P.support, (P.coeff β).denom.eval (t : ℂ) ≠ 0 := by
      intro β hβ h0
      apply hwnot
      exact Finset.mem_biUnion.mpr ⟨β, hβ,
        Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (RatFunc.denom_ne_zero _)).mpr h0)⟩
    refine ⟨t, hball ht_ball, ?_⟩
    dsimp only [g]
    rw [evalU_clearDenomMvPoly P hden_ne, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
      hP t ht_pos hden_ne, mul_zero]
  have hcont_at : ContinuousAt g T := hg_cont.continuousAt (isOpen_Ioi.mem_nhds hT)
  exact isClosed_singleton.mem_of_frequently_of_tendsto hfreq hcont_at

/-- **1D Relativistic Bose Pressure Differential Transcendence over `ℂ(T)`**. -/
theorem bosePressure1D_no_rat_ade {m : ℝ} (hm : 0 < m) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ T : ℝ, 0 < T →
      (∀ β ∈ P.support, (P.coeff β).denom.eval (T : ℂ) ≠ 0) →
      MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (bosePressure1D m t : ℂ)) T)
        (evalRatU P (T : ℂ)) = 0) :
    P = 0 := by
  let c : ℝ := m / (2 * Real.pi)
  have hf_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun T : ℝ => (bosePressure1D m T : ℂ)) (Set.Ioi 0) := by
    have hmap : MapsTo (fun T : ℝ => c ^ 2 / T ^ 2) (Set.Ioi 0) (Set.Ioi 0) := fun T (hT : 0 < T) => by
      change 0 < c ^ 2 / T ^ 2; positivity
    have hdiv : ContDiffOn ℝ (⊤ : ℕ∞) (fun T : ℝ => c ^ 2 / T ^ 2) (Set.Ioi 0) :=
      contDiffOn_const.div (contDiffOn_id.pow 2) fun T (hT : 0 < T) => pow_ne_zero 2 hT.ne'
    have hrhs : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun T : ℝ => (2 * (Real.pi : ℂ)) * (T : ℂ) ^ 2 * (H1 (c ^ 2 / T ^ 2) : ℂ)) (Set.Ioi 0) :=
      (contDiffOn_const.mul ((Complex.ofRealCLM.contDiff.contDiffOn).pow 2)).mul (H1_contDiffOn.comp hdiv hmap)
    exact hrhs.congr fun T (hT : 0 < T) => by
      rw [bosePressure1D_eq_H1 hT]
      have hy : m ^ 2 / (2 * Real.pi * T) ^ 2 = c ^ 2 / T ^ 2 := by dsimp only [c]; field_simp
      rw [hy]; push_cast; ring
  exact (clearDenomMvPoly_eq_zero_iff P).mp
    (bosePressure1D_no_ade hm (clearDenomMvPoly P) (clearDenom_vanish_Ioi hf_smooth P hP))

/-- **1D Relativistic Fermi Pressure Differential Transcendence over `ℂ(T)`**. -/
theorem fermiPressure1D_no_rat_ade {m : ℝ} (hm : 0 < m) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ T : ℝ, 0 < T →
      (∀ β ∈ P.support, (P.coeff β).denom.eval (T : ℂ) ≠ 0) →
      MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (fermiPressure1D m t : ℂ)) T)
        (evalRatU P (T : ℂ)) = 0) :
    P = 0 := by
  let c : ℝ := m / (2 * Real.pi)
  have hf_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun T : ℝ => (fermiPressure1D m T : ℂ)) (Set.Ioi 0) := by
    have h4 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => (H1 (4 * y) : ℂ)) (Set.Ioi 0) :=
      H1_contDiffOn.comp (contDiffOn_const.mul contDiffOn_id) (fun y (hy : 0 < y) => by change 0 < 4 * y; linarith)
    have hH1F : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => (H1 y : ℂ) - (1 / 2 : ℂ) * (H1 (4 * y) : ℂ)) (Set.Ioi 0) :=
      H1_contDiffOn.sub (contDiffOn_const.mul h4)
    have hmap : MapsTo (fun T : ℝ => c ^ 2 / T ^ 2) (Set.Ioi 0) (Set.Ioi 0) := fun T (hT : 0 < T) => by
      change 0 < c ^ 2 / T ^ 2; positivity
    have hdiv : ContDiffOn ℝ (⊤ : ℕ∞) (fun T : ℝ => c ^ 2 / T ^ 2) (Set.Ioi 0) :=
      contDiffOn_const.div (contDiffOn_id.pow 2) fun T (hT : 0 < T) => pow_ne_zero 2 hT.ne'
    have hrhs : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun T : ℝ => (2 * (Real.pi : ℂ)) * (T : ℂ) ^ 2 *
          ((H1 (c ^ 2 / T ^ 2) : ℂ) - (1 / 2 : ℂ) * (H1 (4 * (c ^ 2 / T ^ 2)) : ℂ))) (Set.Ioi 0) :=
      (contDiffOn_const.mul ((Complex.ofRealCLM.contDiff.contDiffOn).pow 2)).mul (hH1F.comp hdiv hmap)
    exact hrhs.congr fun T (hT : 0 < T) => by
      rw [fermiPressure1D_doubling hm hT, bosePressure1D_eq_H1 hT, bosePressure1D_eq_H1 hT]
      have hy1 : m ^ 2 / (2 * Real.pi * T) ^ 2 = c ^ 2 / T ^ 2 := by dsimp only [c]; field_simp
      have hy2 : (2 * m) ^ 2 / (2 * Real.pi * T) ^ 2 = 4 * (c ^ 2 / T ^ 2) := by
        dsimp only [c]; field_simp; ring
      rw [hy1, hy2]; push_cast; ring
  exact (clearDenomMvPoly_eq_zero_iff P).mp
    (fermiPressure1D_no_ade hm (clearDenomMvPoly P) (clearDenom_vanish_Ioi hf_smooth P hP))

/-- **3D Relativistic Bose Pressure Differential Transcendence over `ℂ(T)`**. -/
theorem bosePressure3D_no_rat_ade {m : ℝ} (hm : 0 < m) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ T : ℝ, 0 < T →
      (∀ β ∈ P.support, (P.coeff β).denom.eval (T : ℂ) ≠ 0) →
      MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (bosePressure3D m t : ℂ)) T)
        (evalRatU P (T : ℂ)) = 0) :
    P = 0 := by
  let c : ℝ := m / (2 * Real.pi)
  have hf_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun T : ℝ => (bosePressure3D m T : ℂ)) (Set.Ioi 0) := by
    have hmap : MapsTo (fun T : ℝ => c ^ 2 / T ^ 2) (Set.Ioi 0) (Set.Ioi 0) := fun T (hT : 0 < T) => by
      change 0 < c ^ 2 / T ^ 2; positivity
    have hdiv : ContDiffOn ℝ (⊤ : ℕ∞) (fun T : ℝ => c ^ 2 / T ^ 2) (Set.Ioi 0) :=
      contDiffOn_const.div (contDiffOn_id.pow 2) fun T (hT : 0 < T) => pow_ne_zero 2 hT.ne'
    have hrhs : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun T : ℝ => (8 * (Real.pi : ℂ) ^ 3) * (T : ℂ) ^ 4 * (H3 (c ^ 2 / T ^ 2) : ℂ)) (Set.Ioi 0) :=
      (contDiffOn_const.mul ((Complex.ofRealCLM.contDiff.contDiffOn).pow 4)).mul (H3_contDiffOn.comp hdiv hmap)
    exact hrhs.congr fun T (hT : 0 < T) => by
      rw [bosePressure3D_eq_H3 hT]
      have hy : m ^ 2 / (2 * Real.pi * T) ^ 2 = c ^ 2 / T ^ 2 := by dsimp only [c]; field_simp
      rw [hy]; push_cast; ring
  exact (clearDenomMvPoly_eq_zero_iff P).mp
    (bosePressure3D_no_ade hm (clearDenomMvPoly P) (clearDenom_vanish_Ioi hf_smooth P hP))

/-- **3D Relativistic Fermi Pressure Differential Transcendence over `ℂ(T)`**. -/
theorem fermiPressure3D_no_rat_ade {m : ℝ} (hm : 0 < m) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ T : ℝ, 0 < T →
      (∀ β ∈ P.support, (P.coeff β).denom.eval (T : ℂ) ≠ 0) →
      MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (fermiPressure3D m t : ℂ)) T)
        (evalRatU P (T : ℂ)) = 0) :
    P = 0 := by
  let c : ℝ := m / (2 * Real.pi)
  have hf_smooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun T : ℝ => (fermiPressure3D m T : ℂ)) (Set.Ioi 0) := by
    have h4 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => (H3 (4 * y) : ℂ)) (Set.Ioi 0) :=
      H3_contDiffOn.comp (contDiffOn_const.mul contDiffOn_id) (fun y (hy : 0 < y) => by change 0 < 4 * y; linarith)
    have hH3F : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => (H3 y : ℂ) - (1 / 8 : ℂ) * (H3 (4 * y) : ℂ)) (Set.Ioi 0) :=
      H3_contDiffOn.sub (contDiffOn_const.mul h4)
    have hmap : MapsTo (fun T : ℝ => c ^ 2 / T ^ 2) (Set.Ioi 0) (Set.Ioi 0) := fun T (hT : 0 < T) => by
      change 0 < c ^ 2 / T ^ 2; positivity
    have hdiv : ContDiffOn ℝ (⊤ : ℕ∞) (fun T : ℝ => c ^ 2 / T ^ 2) (Set.Ioi 0) :=
      contDiffOn_const.div (contDiffOn_id.pow 2) fun T (hT : 0 < T) => pow_ne_zero 2 hT.ne'
    have hrhs : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun T : ℝ => (8 * (Real.pi : ℂ) ^ 3) * (T : ℂ) ^ 4 *
          ((H3 (c ^ 2 / T ^ 2) : ℂ) - (1 / 8 : ℂ) * (H3 (4 * (c ^ 2 / T ^ 2)) : ℂ))) (Set.Ioi 0) :=
      (contDiffOn_const.mul ((Complex.ofRealCLM.contDiff.contDiffOn).pow 4)).mul (hH3F.comp hdiv hmap)
    exact hrhs.congr fun T (hT : 0 < T) => by
      rw [fermiPressure3D_doubling hm hT, bosePressure3D_eq_H3 hT, bosePressure3D_eq_H3 hT]
      have hy1 : m ^ 2 / (2 * Real.pi * T) ^ 2 = c ^ 2 / T ^ 2 := by dsimp only [c]; field_simp
      have hy2 : (2 * m) ^ 2 / (2 * Real.pi * T) ^ 2 = 4 * (c ^ 2 / T ^ 2) := by
        dsimp only [c]; field_simp; ring
      rw [hy1, hy2]; push_cast; ring
  exact (clearDenomMvPoly_eq_zero_iff P).mp
    (fermiPressure3D_no_ade hm (clearDenomMvPoly P) (clearDenom_vanish_Ioi hf_smooth P hP))

/-- **Unified Relativistic Ideal Gas Dimensional-Parity Theorem (`d = 2` vs `d = 1, 3`)**:
For every positive mass `m > 0`:
1. In even dimension `d = 2`, both the relativistic Bose and Fermi pressures are differentially
   algebraic over `ℂ[T]` (each satisfies an explicit nonzero order-3 quadratic ODE).
2. In odd dimensions `d = 1` and `d = 3`, both the relativistic Bose and Fermi pressures are
   differentially transcendental over `ℂ(T)`. -/
theorem relativistic_ideal_gas_dimensional_parity {m : ℝ} (hm : 0 < m) :
    (∃ P : MvPolynomial (Fin 4) (Polynomial ℂ), P ≠ 0 ∧
      ∀ T : ℝ, 0 < T →
        MvPolynomial.eval
          (fun j : Fin 4 => iteratedDeriv j.val (fun t : ℝ => (bosePressure2D m t : ℂ)) T)
          (evalU P (T : ℂ)) = 0) ∧
    (∃ P : MvPolynomial (Fin 4) (Polynomial ℂ), P ≠ 0 ∧
      ∀ T : ℝ, 0 < T →
        MvPolynomial.eval
          (fun j : Fin 4 => iteratedDeriv j.val (fun t : ℝ => (fermiPressure2D m t : ℂ)) T)
          (evalU P (T : ℂ)) = 0) ∧
    (∀ {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ T : ℝ, 0 < T →
        (∀ β ∈ P.support, (P.coeff β).denom.eval (T : ℂ) ≠ 0) →
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (bosePressure1D m t : ℂ)) T)
          (evalRatU P (T : ℂ)) = 0) → P = 0) ∧
    (∀ {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ T : ℝ, 0 < T →
        (∀ β ∈ P.support, (P.coeff β).denom.eval (T : ℂ) ≠ 0) →
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (fermiPressure1D m t : ℂ)) T)
          (evalRatU P (T : ℂ)) = 0) → P = 0) ∧
    (∀ {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ T : ℝ, 0 < T →
        (∀ β ∈ P.support, (P.coeff β).denom.eval (T : ℂ) ≠ 0) →
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (bosePressure3D m t : ℂ)) T)
          (evalRatU P (T : ℂ)) = 0) → P = 0) ∧
    (∀ {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ T : ℝ, 0 < T →
        (∀ β ∈ P.support, (P.coeff β).denom.eval (T : ℂ) ≠ 0) →
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (fermiPressure3D m t : ℂ)) T)
          (evalRatU P (T : ℂ)) = 0) → P = 0) :=
  ⟨bosePressure2D_dAlgebraic hm, fermiPressure2D_dAlgebraic hm,
    fun P hP => bosePressure1D_no_rat_ade hm P hP,
    fun P hP => fermiPressure1D_no_rat_ade hm P hP,
    fun P hP => bosePressure3D_no_rat_ade hm P hP,
    fun P hP => fermiPressure3D_no_rat_ade hm P hP⟩

end
end PakPrimes.ThermalGasParity
