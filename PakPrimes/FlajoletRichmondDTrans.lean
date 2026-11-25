module

public import PakPrimes.AutonomousTransfer
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic

/-! # Unconditional Differential Transcendence of Flajolet–Richmond Generalized Digital Trees

This module provides a 100% unconditional, zero-hypothesis, kernel-verified Lean 4 formalization
resolving **Bostan–Di Vizio–Raschel (Amer. J. Math. 146(6), 2024, §2.2.6, Example #3)**:
the Flajolet–Richmond generalized digital tree exponential generating function `f_b(t)` solving
```
  f_b^{(b)}(t) = 2 e^{t/2} f_b(t/2) + e^t,   f_0 = 0,   f_1 = ⋯ = f_b = 1
```
is **differentially transcendental over `ℂ(t)` for every integer `b ≥ 2`**, while at the edge case
`b = 1` it collapses to the D-finite function `f_1(t) = t e^t` (Poisson transform `h_1(t) = t`,
rational inverse Borel transform `G_1(t) = t`), correcting the missing `b ≥ 2` hypothesis on p. 12
of Bostan–Di Vizio–Raschel.

## Proof Architecture (6 Self-Contained Steps, Zero External Black Boxes)

1. **Combinatorial Definitions & Exact `b = 1` Edge Case**:
   Defines `frPoissonCoeff b`, `frCoeff b`, `frEGF b`, `frPoisson b`, and `frEGFSeries b`,
   proves the exponential growth bound `‖frPoissonCoeff b n‖ ≤ (2^b + 3)^n`, establishes the
   differential-difference equation `frEGF_diff_eq` and initial values `frEGF_init`, and resolves
   the `b = 1` rational/D-finite case (`frEGF_one`, `frPoisson_one`, `frEGF_one_isDAlgebraic`).
2. **Global Meromorphic `G_b`, Infinite Product `Π_b`, Elliptic `Ψ_b`, and `K_b > 0`**:
   Constructs `G_mero b`, `Pi_b b`, `Psi_b b`, `T_b b`, proves the telescoping decomposition
   `ξ G_mero(1/ξ) = Π_b(ξ) (Ψ_b(-log_2 ξ) - T_b(ξ))`, proves `K_b > 2 / (3 P_∞^b) > 0` for all
   `b ≥ 2`, and derives the exact order-`b` Laurent expansion of `Ψ_b` at `u₀ = i π / log 2`.
3. **Rectangle Cauchy Residue Integral, Gamma Reflection & Poisson Summation**:
   Computes all Fourier coefficients `Ψ̂_b(k)` directly via a single rectangle residue integral
   around `[-1/2, 1/2] × [0, 2π / log 2]` (no Weierstrass `℘` required), applies Euler's
   reflection formula `Complex.Gamma_mul_Gamma_one_sub` to collapse `Φ̂_b(k)` onto a nonzero
   polynomial `Q_b` of degree `b - 2`, and uses periodization / Fourier summation on
   `A(x) = x · masterLacunary x` to prove `v_b'(x) = C_b + (log 2) Q_b(θ) A(x)`.
4. **Finite Trapezoid Contour Deformation & All-Derivatives Asymptotic Reduction**:
   Represents `frPoisson^{(j)}(x)` as a square Cauchy integral, deforms it via four convex pieces
   in `ℂ \ [-1, 0]` to a finite trapezoid `T(1/x)` with `|arg ξ| ≤ 3π/4`, evaluates the scaling
   limit via Hankel's reciprocal-Gamma integral, and extracts a polynomial ADE for `v_b` from any
   polynomial ADE for `frPoisson b` via `2^N`-scaling.
5. **Master Shift-and-Scale D-Transcendence Theorem & Differential Field Transfer**:
   Proves `masterLacunary (2^{-N} s) = 2^N masterLacunary s`,
   `masterLacunary (x + 2πi n) = masterLacunary x + shiftRemainder n x` with `shiftRemainder n`
   entire and `iteratedDeriv j (shiftRemainder 1) 0 ≠ 0`, and deduces `masterLacunary_no_ade`
   by weight-homogeneous extraction and minimal total-degree descent. Transfers non-existence of
   ADEs across `v_b → A → masterLacunary` and `frEGF → frPoisson` inside the differential field
   of meromorphic functions on `{Re z > 0}` via transcendence degree bounds.
6. **Formal Power Series Differential Transcendence over `RatFunc ℂ`**:
   Exports `frPoisson_no_ade`, `frEGF_no_ade`, `frEGFSeries_dTrans_over_ratFunc`, and
   `frEGFSeries_algebraicIndependent` for all integers `b ≥ 2`.
-/

set_option maxHeartbeats 1600000

public section
namespace PakPrimes.FlajoletRichmondDTrans

open Complex Real Filter MeasureTheory Set MvPolynomial
open PakPrimes.BorelStokesVandermonde PakPrimes.PrimeNome
open scoped Topology Interval BigOperators

noncomputable section

/-! ## Section 1: Combinatorial Definitions, `b = 1` Edge Case, and Functional Equations -/

/-- The Poisson transform coefficient sequence `c_n = frPoissonCoeff b n` of Flajolet–Richmond
generalized digital trees with bucket parameter `b`, defined by strong recursion:
* `c_0 = 0`,
* `c_k = (-1)^(k - 1)` for `1 ≤ k < b`,
* `c_{n + b} = 2^(1 - n) c_n + δ_{n, 0} - ∑_{j=0}^{b-1} C(b, j) c_{n + j}` for `n ≥ 0` (`b ≥ 1`).
For `b = 0`, returns `0`. -/
@[expose] def frPoissonCoeff (b : ℕ) : ℕ → ℂ
  | n =>
    if b = 0 then 0
    else if n = 0 then 0
    else if n < b then (-1 : ℂ) ^ (n - 1)
    else
      let m := n - b
      (2 : ℂ) ^ (1 - (m : ℤ)) * frPoissonCoeff b m + (if m = 0 then (1 : ℂ) else 0) -
        ∑ j : Fin b, ((b.choose j.val : ℕ) : ℂ) * frPoissonCoeff b (m + j.val)
termination_by n => n
decreasing_by
  · omega
  · have := j.isLt; omega

/-- The expected number `f_{b, n} = frCoeff b n` of nonempty nodes in a Flajolet–Richmond
generalized digital tree of size `n` with bucket parameter `b`:
`f_{b, n} = ∑_{k=0}^n C(n, k) c_{b, k}`. -/
@[expose] def frCoeff (b n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℕ) : ℂ) * frPoissonCoeff b k

/-- Formal exponential generating series `∑_{n ≥ 0} (f_{b, n} / n!) t^n ∈ ℂ⟦t⟧`. -/
@[expose] def frEGFSeries (b : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => frCoeff b n / (n.factorial : ℂ)

/-- Formal Poisson generating series `∑_{n ≥ 0} (c_{b, n} / n!) t^n ∈ ℂ⟦t⟧`. -/
@[expose] def frPoissonSeries (b : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => frPoissonCoeff b n / (n.factorial : ℂ)

/-- Entire exponential generating function `f_b(t) = ∑_{n ≥ 0} f_{b, n} t^n / n!`. -/
@[expose] def frEGF (b : ℕ) (t : ℂ) : ℂ :=
  ∑' n : ℕ, frCoeff b n * t ^ n / (n.factorial : ℂ)

/-- Poisson transform `h_b(t) = e^{-t} f_b(t)` of the Flajolet–Richmond EGF. -/
@[expose] def frPoisson (b : ℕ) (t : ℂ) : ℂ :=
  Complex.exp (-t) * frEGF b t

lemma frPoissonCoeff_zero (b : ℕ) : frPoissonCoeff b 0 = 0 := by
  rw [frPoissonCoeff]
  by_cases hb : b = 0 <;> simp [hb]

lemma frPoissonCoeff_lt {b k : ℕ} (hk1 : 1 ≤ k) (hkb : k < b) :
    frPoissonCoeff b k = (-1 : ℂ) ^ (k - 1) := by
  rw [frPoissonCoeff]
  have hb : b ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  simp [hb, hk0, hkb]

lemma frPoissonCoeff_recurrence {b : ℕ} (hb : 1 ≤ b) (m : ℕ) :
    frPoissonCoeff b (m + b) =
      (2 : ℂ) ^ (1 - (m : ℤ)) * frPoissonCoeff b m + (if m = 0 then (1 : ℂ) else 0) -
        ∑ j ∈ Finset.range b, ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (m + j) := by
  conv_lhs => rw [frPoissonCoeff]
  have hb0 : b ≠ 0 := by omega
  have hmb0 : m + b ≠ 0 := by omega
  have hnotlt : ¬ (m + b < b) := by omega
  simp only [hb0, hmb0, hnotlt, ↓reduceIte, Nat.add_sub_cancel]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun j => ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (m + j))]

/-- Equivalent additive form of the Poisson recurrence:
`∑_{j=0}^b C(b, j) c_{m + j} = 2^(1 - m) c_m + δ_{m, 0}`. -/
lemma frPoissonCoeff_sum_choose {b : ℕ} (hb : 1 ≤ b) (m : ℕ) :
    ∑ j ∈ Finset.range (b + 1), ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (m + j) =
      (2 : ℂ) ^ (1 - (m : ℤ)) * frPoissonCoeff b m + (if m = 0 then (1 : ℂ) else 0) := by
  rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul,
    frPoissonCoeff_recurrence hb m]
  ring

/-- Exact initial values `f_{b, 0} = 0` and `f_{b, k} = 1` for all `1 ≤ k ≤ b`. -/
theorem frEGF_init (b : ℕ) (hb : 1 ≤ b) :
    frCoeff b 0 = 0 ∧ ∀ k, 1 ≤ k → k ≤ b → frCoeff b k = 1 := by
  refine ⟨?_, ?_⟩
  · simp [frCoeff, frPoissonCoeff_zero]
  · intro k hk1 hkb
    rcases lt_or_eq_of_le hkb with hlt | rfl
    · unfold frCoeff
      rw [Finset.sum_range_succ', Nat.choose_zero_right, Nat.cast_one, one_mul,
        frPoissonCoeff_zero, add_zero]
      have hterm : ∀ i ∈ Finset.range k,
          ((k.choose (i + 1) : ℕ) : ℂ) * frPoissonCoeff b (i + 1) =
            -(((k.choose (i + 1) : ℕ) : ℂ) * (-1 : ℂ) ^ (i + 1)) := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [frPoissonCoeff_lt (by omega) (by omega)]
        simp only [Nat.add_sub_cancel, pow_succ]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib]
      have hbinom := add_pow (-1 : ℂ) (1 : ℂ) k
      have hzero : ((-1 : ℂ) + 1) ^ k = 0 := by
        rw [neg_add_cancel, zero_pow (by omega)]
      rw [hzero] at hbinom
      simp only [one_pow, mul_one] at hbinom
      rw [Finset.sum_range_succ', pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] at hbinom
      have hsum : ∑ i ∈ Finset.range k, ((k.choose (i + 1) : ℕ) : ℂ) * (-1 : ℂ) ^ (i + 1) = -1 := by
        have hcomm : ∑ i ∈ Finset.range k, ((k.choose (i + 1) : ℕ) : ℂ) * (-1 : ℂ) ^ (i + 1) =
            ∑ i ∈ Finset.range k, (-1 : ℂ) ^ (i + 1) * ((k.choose (i + 1) : ℕ) : ℂ) := by
          refine Finset.sum_congr rfl fun i _ => mul_comm _ _
        rw [hcomm]
        linear_combination -hbinom
      rw [hsum, neg_neg]
    · unfold frCoeff
      have h0 := frPoissonCoeff_sum_choose hb 0
      simp only [zero_add, frPoissonCoeff_zero, mul_zero, ↓reduceIte, zero_add] at h0
      exact h0

/-- Exponential growth bound `‖frPoissonCoeff b n‖ ≤ (2^b + 3)^n` for all `b ≥ 1` and `n ≥ 0`. -/
lemma norm_frPoissonCoeff_le {b : ℕ} (hb : 1 ≤ b) (n : ℕ) :
    ‖frPoissonCoeff b n‖ ≤ ((2 ^ b + 3 : ℕ) : ℝ) ^ n := by
  let R : ℝ := ((2 ^ b + 3 : ℕ) : ℝ)
  have hR1 : (1 : ℝ) ≤ R := by
    dsimp only [R]; exact_mod_cast (show 1 ≤ 2 ^ b + 3 from le_trans (by omega : 1 ≤ 3) (Nat.le_add_left 3 _))
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp [frPoissonCoeff_zero]
    · by_cases hlt : n < b
      · rw [frPoissonCoeff_lt (by omega) hlt]
        simp only [norm_pow, norm_neg, norm_one, one_pow]
        exact one_le_pow₀ hR1
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + b := ⟨n - b, by omega⟩
        rw [frPoissonCoeff_recurrence hb m]
        have hpow_le : ∀ k ≤ m + b - 1, R ^ k ≤ R ^ (m + b - 1) := fun k hk =>
          pow_le_pow_right₀ hR1 hk
        have hm_le : m ≤ m + b - 1 := by omega
        have h2pow : ‖(2 : ℂ) ^ (1 - (m : ℤ))‖ ≤ 2 := by
          rw [norm_zpow, Complex.norm_ofNat]
          calc (2 : ℝ) ^ (1 - (m : ℤ)) ≤ (2 : ℝ) ^ (1 : ℤ) :=
                zpow_le_zpow_right₀ (by norm_num) (by omega)
            _ = 2 := by norm_num
        have hterm1 : ‖(2 : ℂ) ^ (1 - (m : ℤ)) * frPoissonCoeff b m‖ ≤ 2 * R ^ (m + b - 1) := by
          rw [norm_mul]
          calc ‖(2 : ℂ) ^ (1 - (m : ℤ))‖ * ‖frPoissonCoeff b m‖
              ≤ 2 * R ^ m := mul_le_mul h2pow (ih m (by omega)) (norm_nonneg _) (by positivity)
            _ ≤ 2 * R ^ (m + b - 1) := mul_le_mul_of_nonneg_left (hpow_le m hm_le) (by positivity)
        have hterm2 : ‖(if m = 0 then (1 : ℂ) else 0)‖ ≤ R ^ (m + b - 1) := by
          split_ifs
          · rw [norm_one]; exact one_le_pow₀ hR1
          · rw [norm_zero]; exact pow_nonneg hRpos.le _
        have hterm3 :
            ‖∑ j ∈ Finset.range b, ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (m + j)‖ ≤
              (((2 ^ b : ℕ) : ℝ) - 1) * R ^ (m + b - 1) := by
          calc ‖∑ j ∈ Finset.range b, ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (m + j)‖
              ≤ ∑ j ∈ Finset.range b, ‖((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (m + j)‖ :=
                norm_sum_le _ _
            _ ≤ ∑ j ∈ Finset.range b, (b.choose j : ℝ) * R ^ (m + b - 1) := by
                refine Finset.sum_le_sum fun j hj => ?_
                rw [Finset.mem_range] at hj
                rw [norm_mul, Complex.norm_natCast]
                exact mul_le_mul_of_nonneg_left
                  ((ih (m + j) (by omega)).trans (hpow_le (m + j) (by omega)))
                  (Nat.cast_nonneg _)
            _ = (∑ j ∈ Finset.range b, (b.choose j : ℝ)) * R ^ (m + b - 1) :=
                (Finset.sum_mul _ _ _).symm
            _ = (((2 ^ b : ℕ) : ℝ) - 1) * R ^ (m + b - 1) := by
                congr 1
                have hsum := Nat.sum_range_choose b
                rw [Finset.sum_range_succ, Nat.choose_self] at hsum
                have hsumR : (∑ j ∈ Finset.range b, (b.choose j : ℝ)) + 1 = ((2 ^ b : ℕ) : ℝ) := by
                  exact_mod_cast hsum
                linarith
        calc ‖(2 : ℂ) ^ (1 - (m : ℤ)) * frPoissonCoeff b m + (if m = 0 then (1 : ℂ) else 0) -
                ∑ j ∈ Finset.range b, ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (m + j)‖
            ≤ ‖(2 : ℂ) ^ (1 - (m : ℤ)) * frPoissonCoeff b m + (if m = 0 then (1 : ℂ) else 0)‖ +
                ‖∑ j ∈ Finset.range b, ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (m + j)‖ :=
              norm_sub_le _ _
          _ ≤ ‖(2 : ℂ) ^ (1 - (m : ℤ)) * frPoissonCoeff b m‖ +
                ‖(if m = 0 then (1 : ℂ) else 0)‖ +
                ‖∑ j ∈ Finset.range b, ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (m + j)‖ := by
              linarith [norm_add_le ((2 : ℂ) ^ (1 - (m : ℤ)) * frPoissonCoeff b m)
                (if m = 0 then (1 : ℂ) else 0)]
          _ ≤ 2 * R ^ (m + b - 1) + R ^ (m + b - 1) + (((2 ^ b : ℕ) : ℝ) - 1) * R ^ (m + b - 1) := by
              linarith
          _ = (((2 ^ b : ℕ) : ℝ) + 2) * R ^ (m + b - 1) := by ring
          _ ≤ R * R ^ (m + b - 1) := by
              refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hRpos.le _)
              dsimp only [R]; push_cast; linarith
          _ = R ^ (m + b) := by
              rw [← pow_succ', show m + b - 1 + 1 = m + b by omega]

/-- Exponential growth bound `‖frCoeff b n‖ ≤ (2^b + 4)^n` for all `b ≥ 1` and `n ≥ 0`. -/
lemma norm_frCoeff_le {b : ℕ} (hb : 1 ≤ b) (n : ℕ) :
    ‖frCoeff b n‖ ≤ ((2 ^ b + 4 : ℕ) : ℝ) ^ n := by
  unfold frCoeff
  calc ‖∑ k ∈ Finset.range (n + 1), ((n.choose k : ℕ) : ℂ) * frPoissonCoeff b k‖
      ≤ ∑ k ∈ Finset.range (n + 1), ‖((n.choose k : ℕ) : ℂ) * frPoissonCoeff b k‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * ((2 ^ b + 3 : ℕ) : ℝ) ^ k := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left (norm_frPoissonCoeff_le hb k) (Nat.cast_nonneg _)
    _ = (((2 ^ b + 3 : ℕ) : ℝ) + 1) ^ n := by
        rw [add_pow]
        refine Finset.sum_congr rfl fun k _ => by simp [mul_comm]
    _ = ((2 ^ b + 4 : ℕ) : ℝ) ^ n := by push_cast; ring

/-- Summability of the Poisson EGF series `∑ c_{b, n} t^n / n!` for all `t : ℂ`. -/
lemma summable_frPoisson_term {b : ℕ} (hb : 1 ≤ b) (t : ℂ) :
    Summable (fun n : ℕ => frPoissonCoeff b n * t ^ n / (n.factorial : ℂ)) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => (((2 ^ b + 3 : ℕ) : ℝ) * ‖t‖) ^ n / (n.factorial : ℝ))
    (Real.summable_pow_div_factorial _) fun n => ?_
  rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, mul_pow]
  gcongr
  exact norm_frPoissonCoeff_le hb n

/-- Summability of the Flajolet–Richmond EGF series `∑ f_{b, n} t^n / n!` for all `t : ℂ`. -/
lemma summable_frEGF_term {b : ℕ} (hb : 1 ≤ b) (t : ℂ) :
    Summable (fun n : ℕ => frCoeff b n * t ^ n / (n.factorial : ℂ)) := by
  refine Summable.of_norm_bounded (g := fun n : ℕ => (((2 ^ b + 4 : ℕ) : ℝ) * ‖t‖) ^ n / (n.factorial : ℝ))
    (Real.summable_pow_div_factorial _) fun n => ?_
  rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, mul_pow]
  gcongr
  exact norm_frCoeff_le hb n

/-- Exact binomial convolution identity `frEGF b t = exp t * ∑' n, c_{b, n} t^n / n!`. -/
lemma frEGF_eq_exp_mul_tsum {b : ℕ} (hb : 1 ≤ b) (t : ℂ) :
    frEGF b t = Complex.exp t * ∑' n : ℕ, frPoissonCoeff b n * t ^ n / (n.factorial : ℂ) := by
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  dsimp only
  have h1 : Summable (fun n : ℕ => ‖t ^ n / (n.factorial : ℂ)‖) := by
    have := Real.summable_pow_div_factorial ‖t‖
    simpa only [norm_div, norm_pow, Complex.norm_natCast] using this
  have h2 : Summable (fun n : ℕ => ‖frPoissonCoeff b n * t ^ n / (n.factorial : ℂ)‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (Real.summable_pow_div_factorial (((2 ^ b + 3 : ℕ) : ℝ) * ‖t‖))
    rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, mul_pow]
    gcongr
    exact norm_frPoissonCoeff_le hb n
  rw [← (hasSum_sum_range_mul_of_summable_norm h1 h2).tsum_eq]
  unfold frEGF
  refine tsum_congr fun n => ?_
  rw [← Finset.sum_range_reflect]
  unfold frCoeff
  rw [Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp hk
  have hsub : n - (n - k) = k := Nat.sub_sub_self hkn
  have hch := Nat.choose_mul_factorial_mul_factorial hkn
  have hchC : ((n.choose k : ℕ) : ℂ) * (k.factorial : ℂ) * ((n - k).factorial : ℂ) = (n.factorial : ℂ) := by
    exact_mod_cast hch
  have hpow : t ^ (n - k) * t ^ k = t ^ n := by rw [← pow_add, Nat.sub_add_cancel hkn]
  have hkf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hnkf : ((n - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))
  have hnf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  simp only [Nat.succ_sub_one]
  rw [hsub]
  field_simp [hkf, hnkf, hnf]
  rw [← hchC]
  linear_combination (frPoissonCoeff b k * (n.choose k : ℂ) * (k.factorial : ℂ) * ((n - k).factorial : ℂ)) * hpow.symm

/-- Exact Taylor series representation of `frPoisson b t = ∑' n, frPoissonCoeff b n * t^n / n!`. -/
theorem frPoisson_eq_tsum {b : ℕ} (hb : 1 ≤ b) (t : ℂ) :
    frPoisson b t = ∑' n : ℕ, frPoissonCoeff b n * t ^ n / (n.factorial : ℂ) := by
  unfold frPoisson
  rw [frEGF_eq_exp_mul_tsum hb t, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

/-- General entire exponential power series helper: if `‖a n‖ ≤ R^n`, then `f(t) = ∑ a_n t^n / n!`
is entire and has exact `k`-th derivative `∑ a_{n+k} t^n / n!`. -/
private lemma hasDerivAt_egf_tsum {a : ℕ → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (ha : ∀ n, ‖a n‖ ≤ R ^ n) (t : ℂ) :
    HasDerivAt (fun z : ℂ => ∑' n : ℕ, a n * z ^ n / (n.factorial : ℂ))
      (∑' n : ℕ, a (n + 1) * t ^ n / (n.factorial : ℂ)) t := by
  let S : ℝ := ‖t‖ + 1
  have hS : 0 < S := by positivity
  have hball : Metric.ball t 1 ∈ 𝓝 t := Metric.ball_mem_nhds t zero_lt_one
  have hu : ∀ n : ℕ, 0 ≤ R ^ (n + 1) * S ^ n / (n.factorial : ℝ) := fun n => by positivity
  have hsum_u : Summable (fun n : ℕ => R ^ (n + 1) * S ^ n / (n.factorial : ℝ)) := by
    have h1 : Summable (fun n : ℕ => R * ((R * S) ^ n / (n.factorial : ℝ))) :=
      (Real.summable_pow_div_factorial (R * S)).mul_left R
    refine h1.congr fun n => ?_
    rw [mul_pow, pow_succ']; ring
  have hderiv_term : ∀ (n : ℕ) (z : ℂ),
      HasDerivAt (fun w : ℂ => a n * w ^ n / (n.factorial : ℂ))
        (if n = 0 then 0 else a n * z ^ (n - 1) / ((n - 1).factorial : ℂ)) z := by
    intro n z
    cases n with
    | zero =>
      simpa using hasDerivAt_const z (a 0)
    | succ m =>
      have h1 : HasDerivAt (fun w : ℂ => a (m + 1) * w ^ (m + 1) / ((m + 1).factorial : ℂ))
          (a (m + 1) * (((m + 1 : ℕ) : ℂ) * z ^ m) / ((m + 1).factorial : ℂ)) z := by
        simpa using ((hasDerivAt_pow (m + 1) z).const_mul (a (m + 1))).div_const (((m + 1).factorial : ℂ))
      convert h1 using 1
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [Nat.factorial_succ, Nat.cast_mul]
      have hm1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
      have hmf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
      field_simp [hm1, hmf]
  have hbound : ∀ (n : ℕ) (z : ℂ), z ∈ Metric.ball t 1 →
      ‖(if n = 0 then (0 : ℂ) else a n * z ^ (n - 1) / ((n - 1).factorial : ℂ))‖ ≤
        (if n = 0 then (0 : ℝ) else R ^ n * S ^ (n - 1) / ((n - 1).factorial : ℝ)) := by
    intro n z hz
    cases n with
    | zero => simp
    | succ m =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      have hzS : ‖z‖ ≤ S := by
        have hdist : ‖z - t‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
        have htri : ‖z‖ ≤ ‖z - t‖ + ‖t‖ := by
          calc ‖z‖ = ‖(z - t) + t‖ := by ring_nf
            _ ≤ ‖z - t‖ + ‖t‖ := norm_add_le _ _
        linarith
      rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast]
      gcongr
      exact ha (m + 1)
  have hsum_bound : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else R ^ n * S ^ (n - 1) / ((n - 1).factorial : ℝ)) := by
    rw [← summable_nat_add_iff 1]
    simpa using hsum_u
  have hsum_f : Summable (fun n : ℕ => a n * t ^ n / (n.factorial : ℂ)) := by
    refine Summable.of_norm_bounded (g := fun n => (R * ‖t‖) ^ n / (n.factorial : ℝ))
      (Real.summable_pow_div_factorial _) fun n => ?_
    rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, mul_pow]
    gcongr
    exact ha n
  have hmain := hasDerivAt_tsum_of_isPreconnected (g := fun n z => a n * z ^ n / (n.factorial : ℂ))
    (g' := fun n z => if n = 0 then 0 else a n * z ^ (n - 1) / ((n - 1).factorial : ℂ))
    hsum_bound Metric.isOpen_ball (convex_ball t 1).isPreconnected
    (fun n z _ => hderiv_term n z) hbound (Metric.mem_ball_self zero_lt_one) hsum_f
    (Metric.mem_ball_self zero_lt_one)
  convert hmain using 1
  have hsum_eval : Summable (fun n : ℕ => if n = 0 then (0 : ℂ) else a n * t ^ (n - 1) / ((n - 1).factorial : ℂ)) :=
    Summable.of_norm_bounded hsum_bound fun n => hbound n t (Metric.mem_ball_self zero_lt_one)
  rw [hsum_eval.tsum_eq_zero_add]
  simp

private lemma iteratedDeriv_egf_tsum {a : ℕ → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (ha : ∀ n, ‖a n‖ ≤ R ^ n) (k : ℕ) (t : ℂ) :
    iteratedDeriv k (fun z : ℂ => ∑' n : ℕ, a n * z ^ n / (n.factorial : ℂ)) t =
      ∑' n : ℕ, a (n + k) * t ^ n / (n.factorial : ℂ) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hfn : iteratedDeriv k (fun z : ℂ => ∑' n : ℕ, a n * z ^ n / (n.factorial : ℂ)) =
        fun z : ℂ => ∑' n : ℕ, a (n + k) * z ^ n / (n.factorial : ℂ) :=
      funext ih
    rw [hfn]
    have ha' : ∀ n, ‖a (n + k)‖ ≤ (R + 1) ^ k * (R + 1) ^ n := fun n => by
      calc ‖a (n + k)‖ ≤ R ^ (n + k) := ha (n + k)
        _ ≤ (R + 1) ^ (n + k) := pow_le_pow_left₀ hR (by linarith) _
        _ = (R + 1) ^ k * (R + 1) ^ n := by rw [pow_add, mul_comm]
    -- Apply `hasDerivAt_egf_tsum` after scaling out `(R + 1)^k`
    have hscale : HasDerivAt
        (fun z : ℂ => ((R + 1 : ℝ) : ℂ) ^ k * ∑' n : ℕ, (a (n + k) / ((R + 1 : ℝ) : ℂ) ^ k) * z ^ n / (n.factorial : ℂ))
        (((R + 1 : ℝ) : ℂ) ^ k * ∑' n : ℕ, (a (n + 1 + k) / ((R + 1 : ℝ) : ℂ) ^ k) * t ^ n / (n.factorial : ℂ)) t := by
      have hsub := hasDerivAt_egf_tsum (a := fun n => a (n + k) / ((R + 1 : ℝ) : ℂ) ^ k)
        (R := R + 1) (by positivity) (fun n => by
          rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          rw [div_le_iff₀ (by positivity)]
          linarith [ha' n]) t
      exact hsub.const_mul _
    have hR1ne : ((R + 1 : ℝ) : ℂ) ^ k ≠ 0 := pow_ne_zero k (Complex.ofReal_ne_zero.mpr (by positivity))
    have hlhs_eq : (fun z : ℂ => ((R + 1 : ℝ) : ℂ) ^ k *
          ∑' n : ℕ, (a (n + k) / ((R + 1 : ℝ) : ℂ) ^ k) * z ^ n / (n.factorial : ℂ)) =
        fun z : ℂ => ∑' n : ℕ, a (n + k) * z ^ n / (n.factorial : ℂ) := by
      funext z
      rw [← tsum_mul_left]
      refine tsum_congr fun n => ?_
      field_simp [hR1ne]
    have hrhs_eq : ((R + 1 : ℝ) : ℂ) ^ k *
          ∑' n : ℕ, (a (n + 1 + k) / ((R + 1 : ℝ) : ℂ) ^ k) * t ^ n / (n.factorial : ℂ) =
        ∑' n : ℕ, a (n + (k + 1)) * t ^ n / (n.factorial : ℂ) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun n => ?_
      rw [show n + 1 + k = n + (k + 1) by omega]
      field_simp [hR1ne]
    rw [hlhs_eq, hrhs_eq] at hscale
    exact hscale.deriv

lemma frPoisson_differentiable {b : ℕ} (hb : 1 ≤ b) : Differentiable ℂ (frPoisson b) := by
  intro t
  have hfn : frPoisson b = fun z => ∑' n : ℕ, frPoissonCoeff b n * z ^ n / (n.factorial : ℂ) :=
    funext (frPoisson_eq_tsum hb)
  rw [hfn]
  exact (hasDerivAt_egf_tsum (Nat.cast_nonneg _) (norm_frPoissonCoeff_le hb) t).differentiableAt

lemma frEGF_differentiable {b : ℕ} (hb : 1 ≤ b) : Differentiable ℂ (frEGF b) := by
  intro t
  exact (hasDerivAt_egf_tsum (Nat.cast_nonneg _) (norm_frCoeff_le hb) t).differentiableAt

lemma iteratedDeriv_frPoisson {b : ℕ} (hb : 1 ≤ b) (k : ℕ) (t : ℂ) :
    iteratedDeriv k (frPoisson b) t =
      ∑' n : ℕ, frPoissonCoeff b (n + k) * t ^ n / (n.factorial : ℂ) := by
  have hfn : frPoisson b = fun z => ∑' n : ℕ, frPoissonCoeff b n * z ^ n / (n.factorial : ℂ) :=
    funext (frPoisson_eq_tsum hb)
  rw [hfn]
  exact iteratedDeriv_egf_tsum (Nat.cast_nonneg _) (norm_frPoissonCoeff_le hb) k t

lemma iteratedDeriv_frEGF {b : ℕ} (hb : 1 ≤ b) (k : ℕ) (t : ℂ) :
    iteratedDeriv k (frEGF b) t =
      ∑' n : ℕ, frCoeff b (n + k) * t ^ n / (n.factorial : ℂ) :=
  iteratedDeriv_egf_tsum (Nat.cast_nonneg _) (norm_frCoeff_le hb) k t

/-- Exact pantograph ODE for the Poisson transform:
`∑_{j=0}^b C(b, j) h_b^{(j)}(t) = 2 h_b(t / 2) + 1`. -/
theorem frPoisson_diff_eq (b : ℕ) (hb : 1 ≤ b) (t : ℂ) :
    ∑ j ∈ Finset.range (b + 1), ((b.choose j : ℕ) : ℂ) * iteratedDeriv j (frPoisson b) t =
      2 * frPoisson b (t / 2) + 1 := by
  have hsum_j : ∀ j ∈ Finset.range (b + 1),
      Summable (fun n : ℕ => ((b.choose j : ℕ) : ℂ) * (frPoissonCoeff b (n + j) * t ^ n / (n.factorial : ℂ))) := by
    intro j _
    let R : ℝ := ((2 ^ b + 3 : ℕ) : ℝ)
    refine Summable.of_norm_bounded
      (g := fun n : ℕ => (b.choose j : ℝ) * R ^ j * ((R * ‖t‖) ^ n / (n.factorial : ℝ)))
      ((Real.summable_pow_div_factorial (R * ‖t‖)).mul_left _) fun n => ?_
    rw [norm_mul, norm_div, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_natCast, mul_pow]
    have hle := norm_frPoissonCoeff_le hb (n + j)
    rw [pow_add] at hle
    have h1 : (b.choose j : ℝ) * (‖frPoissonCoeff b (n + j)‖ * ‖t‖ ^ n / (n.factorial : ℝ)) ≤
        (b.choose j : ℝ) * (R ^ n * R ^ j * ‖t‖ ^ n / (n.factorial : ℝ)) := by
      gcongr
    calc (b.choose j : ℝ) * (‖frPoissonCoeff b (n + j)‖ * ‖t‖ ^ n / (n.factorial : ℝ))
        ≤ (b.choose j : ℝ) * (R ^ n * R ^ j * ‖t‖ ^ n / (n.factorial : ℝ)) := h1
      _ = (b.choose j : ℝ) * R ^ j * (R ^ n * ‖t‖ ^ n / (n.factorial : ℝ)) := by ring
  have hlhs : ∑ j ∈ Finset.range (b + 1), ((b.choose j : ℕ) : ℂ) * iteratedDeriv j (frPoisson b) t =
      ∑' n : ℕ, ((2 : ℂ) ^ (1 - (n : ℤ)) * frPoissonCoeff b n + (if n = 0 then (1 : ℂ) else 0)) *
        t ^ n / (n.factorial : ℂ) := by
    simp_rw [iteratedDeriv_frPoisson hb, ← tsum_mul_left]
    rw [← Summable.tsum_finsetSum hsum_j]
    refine tsum_congr fun n => ?_
    have hpull : ∑ j ∈ Finset.range (b + 1),
          ((b.choose j : ℕ) : ℂ) * (frPoissonCoeff b (n + j) * t ^ n / (n.factorial : ℂ)) =
        (∑ j ∈ Finset.range (b + 1), ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (n + j)) *
          t ^ n / (n.factorial : ℂ) := by
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [hpull, frPoissonCoeff_sum_choose hb n]
  rw [hlhs, frPoisson_eq_tsum hb (t / 2), ← tsum_mul_left]
  have h1 : Summable (fun n : ℕ => (2 : ℂ) ^ (1 - (n : ℤ)) * frPoissonCoeff b n * t ^ n / (n.factorial : ℂ)) := by
    refine (summable_frPoisson_term hb (t / 2)).mul_left 2 |>.congr fun n => ?_
    rw [div_pow, zpow_sub₀ (by norm_num : (2 : ℂ) ≠ 0), zpow_one, zpow_natCast]
    ring
  have h2 : Summable (fun n : ℕ => (if n = 0 then (1 : ℂ) else 0) * t ^ n / (n.factorial : ℂ)) :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by
      simp only [Finset.mem_singleton] at hn; simp [hn]
  have hsplit : (∑' n : ℕ, ((2 : ℂ) ^ (1 - (n : ℤ)) * frPoissonCoeff b n + (if n = 0 then (1 : ℂ) else 0)) *
        t ^ n / (n.factorial : ℂ)) =
      (∑' n : ℕ, (2 : ℂ) ^ (1 - (n : ℤ)) * frPoissonCoeff b n * t ^ n / (n.factorial : ℂ)) +
      (∑' n : ℕ, (if n = 0 then (1 : ℂ) else 0) * t ^ n / (n.factorial : ℂ)) := by
    rw [← h1.tsum_add h2]
    refine tsum_congr fun n => by ring
  rw [hsplit]
  congr 1
  · refine tsum_congr fun n => ?_
    rw [div_pow, zpow_sub₀ (by norm_num : (2 : ℂ) ≠ 0), zpow_one, zpow_natCast]
    ring
  · rw [tsum_eq_single 0]
    · simp
    · intro n hn; simp [hn]

/-- Leibniz formula for `iteratedDeriv b (fun z => exp z * h z)`. -/
private lemma iteratedDeriv_exp_mul {h : ℂ → ℂ} (hh : Differentiable ℂ h) (b : ℕ) (t : ℂ) :
    iteratedDeriv b (fun z : ℂ => Complex.exp z * h z) t =
      Complex.exp t * ∑ j ∈ Finset.range (b + 1), ((b.choose j : ℕ) : ℂ) * iteratedDeriv j h t := by
  induction b generalizing t with
  | zero => simp
  | succ b ih =>
    rw [iteratedDeriv_succ]
    have hfn : iteratedDeriv b (fun z : ℂ => Complex.exp z * h z) =
        fun z : ℂ => Complex.exp z * ∑ j ∈ Finset.range (b + 1), ((b.choose j : ℕ) : ℂ) * iteratedDeriv j h z :=
      funext ih
    rw [hfn]
    have hdiff_iter : ∀ j : ℕ, Differentiable ℂ (iteratedDeriv j h) := fun j =>
      (hh.contDiff (n := (⊤ : WithTop ℕ∞))).differentiable_iteratedDeriv j (by simp)
    have hsum_deriv : HasDerivAt
        (fun z : ℂ => ∑ j ∈ Finset.range (b + 1), ((b.choose j : ℕ) : ℂ) * iteratedDeriv j h z)
        (∑ j ∈ Finset.range (b + 1), ((b.choose j : ℕ) : ℂ) * iteratedDeriv (j + 1) h t) t := by
      have h1 := HasDerivAt.fun_sum (u := Finset.range (b + 1))
        (A := fun j z => ((b.choose j : ℕ) : ℂ) * iteratedDeriv j h z)
        (A' := fun j => ((b.choose j : ℕ) : ℂ) * iteratedDeriv (j + 1) h t)
        fun j _ => by
          rw [iteratedDeriv_succ]
          exact ((hdiff_iter j t).hasDerivAt).const_mul _
      exact h1
    have hprod := (Complex.hasDerivAt_exp t).fun_mul hsum_deriv
    rw [hprod.deriv]
    have hpascal : Complex.exp t *
          (∑ j ∈ Finset.range (b + 1), ((b.choose j : ℕ) : ℂ) * iteratedDeriv j h t) +
        Complex.exp t *
          (∑ j ∈ Finset.range (b + 1), ((b.choose j : ℕ) : ℂ) * iteratedDeriv (j + 1) h t) =
        Complex.exp t *
          (∑ j ∈ Finset.range (b + 1 + 1), (((b + 1).choose j : ℕ) : ℂ) * iteratedDeriv j h t) := by
      rw [← mul_add]
      congr 1
      rw [Finset.sum_range_succ' (fun j => (((b + 1).choose j : ℕ) : ℂ) * iteratedDeriv j h t) (b + 1),
        Nat.choose_zero_right, Nat.cast_one, one_mul]
      rw [Finset.sum_range_succ' (fun j => ((b.choose j : ℕ) : ℂ) * iteratedDeriv j h t) b,
        Nat.choose_zero_right, Nat.cast_one, one_mul]
      rw [Finset.sum_range_succ (fun j => ((b.choose j : ℕ) : ℂ) * iteratedDeriv (j + 1) h t) b,
        Nat.choose_self, Nat.cast_one, one_mul]
      rw [Finset.sum_range_succ (fun j => (((b + 1).choose (j + 1) : ℕ) : ℂ) * iteratedDeriv (j + 1) h t) b,
        Nat.choose_self, Nat.cast_one, one_mul]
      have hmid : (∑ j ∈ Finset.range b, ((b.choose (j + 1) : ℕ) : ℂ) * iteratedDeriv (j + 1) h t) +
            (∑ j ∈ Finset.range b, ((b.choose j : ℕ) : ℂ) * iteratedDeriv (j + 1) h t) =
          ∑ j ∈ Finset.range b, (((b + 1).choose (j + 1) : ℕ) : ℂ) * iteratedDeriv (j + 1) h t := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Nat.choose_succ_succ, Nat.cast_add]
        ring
      linear_combination hmid
    exact hpascal

/-- **Exact Flajolet–Richmond [FR92, Lem. 1] / BDR §2.2.6 Difference-Differential Equation:**
For every integer `b ≥ 1` and all `t : ℂ`,
`iteratedDeriv b (frEGF b) t = 2 * exp (t / 2) * frEGF b (t / 2) + exp t`. -/
theorem frEGF_diff_eq (b : ℕ) (hb : 1 ≤ b) (t : ℂ) :
    iteratedDeriv b (frEGF b) t = 2 * Complex.exp (t / 2) * frEGF b (t / 2) + Complex.exp t := by
  have hfn : frEGF b = fun z : ℂ => Complex.exp z * frPoisson b z := by
    funext z
    rw [frPoisson_eq_tsum hb z, frEGF_eq_exp_mul_tsum hb z]
  rw [hfn, iteratedDeriv_exp_mul (frPoisson_differentiable hb) b t, frPoisson_diff_eq b hb t]
  have hexp : Complex.exp t = Complex.exp (t / 2) * Complex.exp (t / 2) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [mul_add, mul_one]
  congr 1
  rw [hexp]
  ring

/-! ### Exact `b = 1` Edge-Case Correction to Bostan–Di Vizio–Raschel (AJM 2024, p. 12) -/

lemma frPoissonCoeff_one (n : ℕ) : frPoissonCoeff 1 n = if n = 1 then 1 else 0 := by
  cases n with
  | zero => simp [frPoissonCoeff_zero]
  | succ m =>
    induction m with
    | zero =>
      have h := frPoissonCoeff_recurrence (b := 1) le_rfl 0
      simp [frPoissonCoeff_zero] at h
      exact h
    | succ k ih =>
      have h := frPoissonCoeff_recurrence (b := 1) le_rfl (k + 1)
      simp only [Finset.range_one, Finset.sum_singleton, Nat.choose_zero_right, Nat.cast_one,
        one_mul, add_zero, Nat.succ_ne_zero, ↓reduceIte] at h
      have hne : k + 1 + 1 ≠ 1 := by omega
      simp only [hne, ↓reduceIte]
      rw [h, ih]
      cases k with
      | zero => norm_num
      | succ j =>
        simp

lemma frCoeff_one (n : ℕ) : frCoeff 1 n = (n : ℂ) := by
  unfold frCoeff
  simp_rw [frPoissonCoeff_one]
  cases n with
  | zero => simp
  | succ m =>
    rw [Finset.sum_eq_single 1]
    · simp [Nat.choose_one_right]
    · intro k _ hk1; simp [hk1]
    · intro h1; exfalso; exact h1 (Finset.mem_range.mpr (by omega))

/-- At `b = 1`, the Poisson transform collapses to the linear polynomial `frPoisson 1 t = t`. -/
theorem frPoisson_one (t : ℂ) : frPoisson 1 t = t := by
  rw [frPoisson_eq_tsum le_rfl t]
  rw [tsum_eq_single 1]
  · simp [frPoissonCoeff_one]
  · intro n hn; simp [frPoissonCoeff_one, hn]

/-- At `b = 1`, the Flajolet–Richmond EGF collapses to `frEGF 1 t = t * exp t`. -/
theorem frEGF_one (t : ℂ) : frEGF 1 t = t * Complex.exp t := by
  have h := frPoisson_one t
  unfold frPoisson at h
  calc frEGF 1 t = Complex.exp t * (Complex.exp (-t) * frEGF 1 t) := by
        rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
    _ = Complex.exp t * t := by rw [h]
    _ = t * Complex.exp t := mul_comm _ _

/-- Explicit first-order linear ODE satisfied by `frEGF 1`: `t * f'(t) - (t + 1) * f(t) = 0`. -/
theorem frEGF_one_ode (t : ℂ) :
    t * deriv (frEGF 1) t - (t + 1) * frEGF 1 t = 0 := by
  have hfn : frEGF 1 = fun z : ℂ => z * Complex.exp z := funext frEGF_one
  rw [hfn]
  have hd : HasDerivAt (fun z : ℂ => z * Complex.exp z) (1 * Complex.exp t + t * Complex.exp t) t :=
    (hasDerivAt_id t).mul (Complex.hasDerivAt_exp t)
  rw [hd.deriv]
  ring

/-- Formal series identity `X * (frEGFSeries 1)' = (X + 1) * frEGFSeries 1` in `ℂ⟦X⟧`. -/
lemma frEGFSeries_one_ode_ps :
    PowerSeries.X * PowerSeries.derivative (frEGFSeries 1) =
      (PowerSeries.X + 1) * frEGFSeries 1 := by
  ext n
  cases n with
  | zero =>
    simp [frEGFSeries, frCoeff_one]
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
      add_mul, one_mul, map_add, PowerSeries.coeff_succ_X_mul]
    simp only [frEGFSeries, PowerSeries.coeff_mk, frCoeff_one]
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hm1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
    have hmf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    field_simp [hm1, hmf]

/-- **Exact `b = 1` Edge-Case Correction:** `frEGFSeries 1` is D-finite (hence D-algebraic over
`ℂ(t)`), witnessing that BDR p. 12 requires `b ≥ 2`. -/
theorem frEGF_one_isDAlgebraic :
    ¬ AlgebraicIndependent ℂ (seriesCoordinates (frEGFSeries 1)) := by
  intro hind
  rw [algebraicIndependent_iff] at hind
  let Q : MvPolynomial ℕ ℂ :=
    MvPolynomial.X 0 * MvPolynomial.X 2 - (MvPolynomial.X 0 + 1) * MvPolynomial.X 1
  have hQ0 : MvPolynomial.aeval (seriesCoordinates (frEGFSeries 1)) Q = 0 := by
    simp only [Q, map_sub, map_mul, map_add, map_one, aeval_X, seriesCoordinates, seriesJet,
      Function.iterate_zero, Function.iterate_one, id_eq]
    exact sub_eq_zero.mpr frEGFSeries_one_ode_ps
  have hQeq0 : Q = 0 := hind Q hQ0
  let x : ℕ → ℂ := fun i => if i = 0 ∨ i = 2 then 1 else 0
  have hev := congrArg (MvPolynomial.eval x) hQeq0
  simp [Q, x] at hev

/-! ## Section 2: `P_∞`, Strict Positivity of `K_b`, Entire `Π_b`, Global `G_mero`, and Elliptic `Ψ_b` -/

private lemma two_zpow_neg_succ_real (r : ℕ) :
    (2 : ℝ) ^ (-(r + 1 : ℤ)) = (1 / 2 : ℝ) ^ (r + 1) := by
  rw [show (-(r + 1 : ℤ)) = -((r + 1 : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast, one_div, inv_pow]

private lemma two_zpow_neg_succ_complex (r : ℕ) :
    (2 : ℂ) ^ (-(r + 1 : ℤ)) = ((2 : ℂ) ^ (r + 1))⁻¹ := by
  rw [show (-(r + 1 : ℤ)) = -((r + 1 : ℕ) : ℤ) by push_cast; ring,
    zpow_neg, zpow_natCast]

private lemma real_finset_prod_le_prod {ι : Type*} {s : Finset ι} {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_le_mul (hfg a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
          (fun i hi => hfg i (Finset.mem_insert_of_mem hi)))
      (Finset.prod_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (le_trans (hf a (Finset.mem_insert_self a s)) (hfg a (Finset.mem_insert_self a s)))

private lemma differentiableAt_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (z : ℂ)
    (hf : ∀ i ∈ s, DifferentiableAt ℂ (f i) z) :
    DifferentiableAt ℂ (fun w => ∏ i ∈ s, f i w) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [differentiableAt_const]
  | insert a s ha ih =>
    have hfun : (fun w => ∏ i ∈ insert a s, f i w) = fun w => f a w * ∏ i ∈ s, f i w := by
      funext w; exact Finset.prod_insert ha
    rw [hfun]
    exact (hf a (Finset.mem_insert_self a s)).mul (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Shifting a `HasProd` on `ℕ` in `ℂ` by 1 (without assuming invertibility of `f 0`). -/
private lemma hasProd_of_shift_one {f : ℕ → ℂ} {P : ℂ}
    (hshift : HasProd (fun k : ℕ => f (k + 1)) P) :
    HasProd f (f 0 * P) := by
  rw [HasProd, Metric.tendsto_nhds] at hshift ⊢
  intro ε hε
  have hcont : ContinuousAt (fun x : ℂ => f 0 * x) P := continuousAt_const.mul continuousAt_id
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hδ_map⟩ := hcont ε hε
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.mp (hshift δ hδ)
  refine Filter.eventually_atTop.mpr ⟨insert 0 (s₀.image Nat.succ), fun s hs => ?_⟩
  have h0s : 0 ∈ s := hs (Finset.mem_insert_self 0 _)
  let t : Finset ℕ := (s.erase 0).image (· - 1)
  have ht_ge : s₀ ≤ t := by
    intro k hk
    refine Finset.mem_image.mpr ⟨k + 1, Finset.mem_erase.mpr ⟨Nat.succ_ne_zero k,
      hs (Finset.mem_insert_of_mem (Finset.mem_image_of_mem Nat.succ hk))⟩, Nat.add_sub_cancel k 1⟩
  have hprod_eq : ∏ i ∈ s, f i = f 0 * ∏ k ∈ t, f (k + 1) := by
    rw [← Finset.mul_prod_erase s f h0s]
    congr 1
    symm
    refine Finset.prod_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
    · intro k hk
      rcases Finset.mem_image.mp hk with ⟨m, hm, rfl⟩
      have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
      rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]
      exact hm
    · intro a _ b _ h; exact Nat.succ_injective h
    · intro m hm
      have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
      exact ⟨m - 1, Finset.mem_image_of_mem (· - 1) hm, Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)⟩
    · intro _ _; rfl
  rw [hprod_eq]
  exact hδ_map (hs₀ t ht_ge)

/-- Shifting a `HasProd` on `ℕ` in `ℂ` by any `J : ℕ`. -/
private lemma hasProd_of_shift {f : ℕ → ℂ} {P : ℂ} (J : ℕ)
    (hshift : HasProd (fun k : ℕ => f (k + J)) P) :
    HasProd f ((∏ j ∈ Finset.range J, f j) * P) := by
  induction J generalizing f with
  | zero => simpa using hshift
  | succ J ih =>
    have h1 : HasProd (fun k : ℕ => f (k + 1)) ((∏ j ∈ Finset.range J, f (j + 1)) * P) := by
      apply ih (f := fun k => f (k + 1))
      simpa [add_assoc, add_comm 1 J] using hshift
    have h2 := hasProd_of_shift_one h1
    rw [Finset.prod_range_succ']
    convert h2 using 1
    ring

/-- The `q`-Pochhammer constant `P_∞ = (1/2; 1/2)_∞ = ∏_{r ≥ 1} (1 - 2^{-r}) ≈ 0.288788`. -/
@[expose] def P_inf : ℝ :=
  ∏' r : ℕ, (1 - (2 : ℝ) ^ (-(r + 1 : ℤ)))

private lemma log_one_sub_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    -2 * x ≤ Real.log (1 - x) ∧ Real.log (1 - x) ≤ 0 := by
  have h1x : 0 < 1 - x := by linarith
  refine ⟨?_, ?_⟩
  · have hinv := Real.log_le_sub_one_of_pos (inv_pos.mpr h1x)
    rw [Real.log_inv] at hinv
    have hfrac : (1 - x)⁻¹ - 1 ≤ 2 * x := by
      have h1 : (1 - x)⁻¹ - 1 = x / (1 - x) := by field_simp [h1x.ne']; ring
      rw [h1, div_le_iff₀ h1x]
      nlinarith
    linarith
  · exact (Real.log_le_sub_one_of_pos h1x).trans (by linarith)

private lemma summable_log_P_inf :
    Summable (fun r : ℕ => Real.log (1 - (2 : ℝ) ^ (-(r + 1 : ℤ)))) := by
  have hgeom : Summable (fun r : ℕ => (2 : ℝ) * (1 / 2 : ℝ) ^ (r + 1)) := by
    have h := (summable_geometric_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left (1 : ℝ)
    refine h.congr fun r => ?_
    rw [pow_succ']; ring
  refine Summable.of_norm_bounded hgeom fun r => ?_
  rw [two_zpow_neg_succ_real]
  have hle : (1 / 2 : ℝ) ^ (r + 1) ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ (r + 1) ≤ (1 / 2 : ℝ) ^ 1 := pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
      _ = 1 / 2 := pow_one _
  have hb := log_one_sub_bounds (by positivity) hle
  rw [Real.norm_eq_abs, abs_of_nonpos hb.2]
  linarith [hb.1]

lemma hasProd_P_inf :
    HasProd (fun r : ℕ => 1 - (2 : ℝ) ^ (-(r + 1 : ℤ)))
      (Real.exp (∑' r : ℕ, Real.log (1 - (2 : ℝ) ^ (-(r + 1 : ℤ))))) := by
  have hsum := summable_log_P_inf.hasSum
  have htend := (Real.continuous_exp.tendsto _).comp hsum
  have hfn : (Real.exp ∘ fun s : Finset ℕ => ∑ r ∈ s, Real.log (1 - (2 : ℝ) ^ (-(r + 1 : ℤ)))) =
      fun s : Finset ℕ => ∏ r ∈ s, (1 - (2 : ℝ) ^ (-(r + 1 : ℤ))) := by
    funext s
    simp only [Function.comp_apply, Real.exp_sum]
    refine Finset.prod_congr rfl fun r _ => ?_
    apply Real.exp_log
    rw [two_zpow_neg_succ_real]
    have hp : (1 / 2 : ℝ) ^ (r + 1) ≤ 1 / 2 := by
      calc (1 / 2 : ℝ) ^ (r + 1) ≤ (1 / 2 : ℝ) ^ 1 := pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
        _ = 1 / 2 := pow_one _
    linarith
  rw [hfn] at htend
  exact htend

lemma P_inf_eq_exp_tsum :
    P_inf = Real.exp (∑' r : ℕ, Real.log (1 - (2 : ℝ) ^ (-(r + 1 : ℤ)))) :=
  hasProd_P_inf.tprod_eq

theorem P_inf_pos : 0 < P_inf := by
  rw [P_inf_eq_exp_tsum]; exact Real.exp_pos _

lemma P_inf_lt_one : P_inf < 1 := by
  rw [P_inf_eq_exp_tsum, Real.exp_lt_one_iff]
  have h0 : Real.log (1 - (2 : ℝ) ^ (-((0 : ℕ) + 1 : ℤ))) < 0 := by
    apply Real.log_neg <;> norm_num
  have hle : ∑' r : ℕ, Real.log (1 - (2 : ℝ) ^ (-(r + 1 : ℤ))) ≤
      Real.log (1 - (2 : ℝ) ^ (-((0 : ℕ) + 1 : ℤ))) := by
    rw [summable_log_P_inf.tsum_eq_zero_add]
    have hnonpos : ∑' r : ℕ, Real.log (1 - (2 : ℝ) ^ (-((r + 1 : ℕ) + 1 : ℤ))) ≤ 0 := by
      apply tsum_nonpos
      intro r
      rw [two_zpow_neg_succ_real]
      have hp : (1 / 2 : ℝ) ^ (r + 1 + 1) ≤ 1 / 2 := by
        calc (1 / 2 : ℝ) ^ (r + 1 + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
              pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
          _ = 1 / 2 := pow_one _
      exact (log_one_sub_bounds (by positivity) hp).2
    linarith
  linarith

/-- Positive real term `a_b(k) = ((1 - 2^{-(k+1)}) ∏_{r=1}^k (2^r - 1)^b)^{-1}` in `K_b`. -/
@[expose] def kTerm (b k : ℕ) : ℝ :=
  1 / ((1 - (2 : ℝ) ^ (-(k + 1 : ℤ))) * ∏ r ∈ Finset.range k, ((2 : ℝ) ^ (r + 1) - 1) ^ b)

/-- Exact leading pole coefficient `K_b` of `(1 + w)^{-b}` in `Ψ_b(-log_2 w)` at `w = -1`:
`K_b = P_∞^{-b} * ∑_{k ≥ 0} (-1)^{b k} / ((1 - 2^{-(k+1)}) ∏_{r=1}^k (2^r - 1)^b)`. -/
@[expose] def K_b (b : ℕ) : ℝ :=
  (∑' k : ℕ, (-1 : ℝ) ^ (b * k) * kTerm b k) / P_inf ^ b

private lemma one_sub_two_zpow_pos (k : ℕ) : 0 < 1 - (2 : ℝ) ^ (-(k + 1 : ℤ)) := by
  rw [two_zpow_neg_succ_real]
  have hp : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ (k + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
      _ = 1 / 2 := pow_one _
  linarith

private lemma two_pow_succ_sub_one_pos (r : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ (r + 1) - 1 := by
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (r + 1) := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (2 : ℝ) ^ (r + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

lemma kTerm_pos (b k : ℕ) : 0 < kTerm b k := by
  unfold kTerm
  apply div_pos one_pos
  apply mul_pos (one_sub_two_zpow_pos k)
  apply Finset.prod_pos
  intro r _
  exact pow_pos (lt_of_lt_of_le zero_lt_one (two_pow_succ_sub_one_pos r)) b

lemma kTerm_zero (b : ℕ) : kTerm b 0 = 2 := by
  unfold kTerm; norm_num

lemma kTerm_one (b : ℕ) : kTerm b 1 = 4 / 3 := by
  unfold kTerm
  simp only [Finset.range_one, Finset.prod_singleton, zero_add, pow_one]
  norm_num

lemma kTerm_succ_lt {b k : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) :
    kTerm b (k + 1) < (1 / 9 : ℝ) * kTerm b k := by
  unfold kTerm
  have h1 : 0 < 1 - (2 : ℝ) ^ (-(k + 1 : ℤ)) := one_sub_two_zpow_pos k
  have h2 : 0 < 1 - (2 : ℝ) ^ (-((k + 1 : ℕ) + 1 : ℤ)) := one_sub_two_zpow_pos (k + 1)
  have hlt12 : 1 - (2 : ℝ) ^ (-(k + 1 : ℤ)) < 1 - (2 : ℝ) ^ (-((k + 1 : ℕ) + 1 : ℤ)) := by
    have : (2 : ℝ) ^ (-((k + 1 : ℕ) + 1 : ℤ)) < (2 : ℝ) ^ (-(k + 1 : ℤ)) :=
      zpow_lt_zpow_right₀ (by norm_num) (by omega)
    linarith
  have hprod_pos : 0 < ∏ r ∈ Finset.range k, ((2 : ℝ) ^ (r + 1) - 1) ^ b :=
    Finset.prod_pos fun r _ => pow_pos (lt_of_lt_of_le zero_lt_one (two_pow_succ_sub_one_pos r)) b
  have h9 : (9 : ℝ) ≤ ((2 : ℝ) ^ (k + 1) - 1) ^ b := by
    have h3 : (3 : ℝ) ≤ (2 : ℝ) ^ (k + 1) - 1 := by
      have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
        calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
          _ ≤ (2 : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    calc (9 : ℝ) = (3 : ℝ) ^ 2 := by norm_num
      _ ≤ (3 : ℝ) ^ b := pow_le_pow_right₀ (by norm_num) hb
      _ ≤ ((2 : ℝ) ^ (k + 1) - 1) ^ b := pow_le_pow_left₀ (by norm_num) h3 b
  rw [Finset.prod_range_succ]
  have ha : (1 - (2 : ℝ) ^ (-(k + 1 : ℤ))) * 9 <
      (1 - (2 : ℝ) ^ (-((k + 1 : ℕ) + 1 : ℤ))) * ((2 : ℝ) ^ (k + 1) - 1) ^ b := by
    calc (1 - (2 : ℝ) ^ (-(k + 1 : ℤ))) * 9
        < (1 - (2 : ℝ) ^ (-((k + 1 : ℕ) + 1 : ℤ))) * 9 := mul_lt_mul_of_pos_right hlt12 (by norm_num)
      _ ≤ (1 - (2 : ℝ) ^ (-((k + 1 : ℕ) + 1 : ℤ))) * ((2 : ℝ) ^ (k + 1) - 1) ^ b :=
          mul_le_mul_of_nonneg_left h9 h2.le
  have hden_gt : ((1 - (2 : ℝ) ^ (-(k + 1 : ℤ))) * ∏ r ∈ Finset.range k, ((2 : ℝ) ^ (r + 1) - 1) ^ b) * 9 <
      (1 - (2 : ℝ) ^ (-((k + 1 : ℕ) + 1 : ℤ))) *
        ((∏ r ∈ Finset.range k, ((2 : ℝ) ^ (r + 1) - 1) ^ b) * ((2 : ℝ) ^ (k + 1) - 1) ^ b) := by
    have hb_mul := mul_lt_mul_of_pos_right ha hprod_pos
    linarith
  have hden_pos1 : 0 < ((1 - (2 : ℝ) ^ (-(k + 1 : ℤ))) * ∏ r ∈ Finset.range k, ((2 : ℝ) ^ (r + 1) - 1) ^ b) * 9 :=
    mul_pos (mul_pos h1 hprod_pos) (by norm_num)
  rw [one_div_mul_one_div_rev]
  exact one_div_lt_one_div_of_lt hden_pos1 hden_gt

lemma kTerm_le_geom {b : ℕ} (hb : 2 ≤ b) (k : ℕ) :
    kTerm b (k + 1) ≤ (4 / 3 : ℝ) * (1 / 9 : ℝ) ^ k := by
  induction k with
  | zero => simp [kTerm_one]
  | succ k ih =>
    calc kTerm b (k + 1 + 1)
        ≤ (1 / 9 : ℝ) * kTerm b (k + 1) := (kTerm_succ_lt hb (by omega)).le
      _ ≤ (1 / 9 : ℝ) * ((4 / 3 : ℝ) * (1 / 9 : ℝ) ^ k) := mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (4 / 3 : ℝ) * (1 / 9 : ℝ) ^ (k + 1) := by rw [pow_succ']; ring

lemma summable_kTerm {b : ℕ} (hb : 2 ≤ b) : Summable (kTerm b) := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun k => (kTerm_pos b (k + 1)).le) (kTerm_le_geom hb) ?_
  exact (summable_geometric_of_lt_one (by positivity) (by norm_num)).mul_left (4 / 3 : ℝ)

lemma summable_signed_kTerm {b : ℕ} (hb : 2 ≤ b) :
    Summable (fun k : ℕ => (-1 : ℝ) ^ (b * k) * kTerm b k) := by
  refine Summable.of_norm_bounded (summable_kTerm hb) fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (kTerm_pos b k)]

/-- **Exact strict lower bound `K_b > 2 / (3 P_∞^b)` for every integer `b ≥ 2`.** -/
theorem K_b_gt_lower_bound (b : ℕ) (hb : 2 ≤ b) :
    2 / (3 * P_inf ^ b) < K_b b := by
  unfold K_b
  have hPpos : 0 < P_inf ^ b := pow_pos P_inf_pos b
  rw [show (2 : ℝ) / (3 * P_inf ^ b) = (2 / 3 : ℝ) / P_inf ^ b by ring,
    div_lt_div_iff_of_pos_right hPpos]
  rcases Nat.even_or_odd b with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have hsign : ∀ k : ℕ, (-1 : ℝ) ^ ((m + m) * k) * kTerm (m + m) k = kTerm (m + m) k := fun k => by
      have hev : Even ((m + m) * k) := ⟨m * k, by ring⟩
      rw [hev.neg_one_pow, one_mul]
    simp_rw [hsign]
    have hge : kTerm (m + m) 0 ≤ ∑' k : ℕ, kTerm (m + m) k :=
      (summable_kTerm hb).le_tsum 0 fun k _ => (kTerm_pos _ k).le
    rw [kTerm_zero] at hge
    linarith
  · have hsign : ∀ k : ℕ, (-1 : ℝ) ^ ((2 * m + 1) * k) * kTerm (2 * m + 1) k =
        (-1 : ℝ) ^ k * kTerm (2 * m + 1) k := fun k => by
      congr 1
      rw [show (2 * m + 1) * k = 2 * (m * k) + k by ring, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
    simp_rw [hsign]
    have hsum := summable_signed_kTerm hb
    simp_rw [hsign] at hsum
    rw [hsum.tsum_eq_zero_add]
    have hsum1 : Summable (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * kTerm (2 * m + 1) (k + 1)) :=
      (summable_nat_add_iff 1).mpr hsum
    rw [hsum1.tsum_eq_zero_add]
    have hsum2 : Summable (fun k : ℕ => (-1 : ℝ) ^ (k + 2) * kTerm (2 * m + 1) (k + 2)) :=
      (summable_nat_add_iff 1).mpr hsum1
    have hpair_pos : 0 < ∑' k : ℕ, (-1 : ℝ) ^ (k + 2) * kTerm (2 * m + 1) (k + 2) := by
      have heven : Summable (fun j : ℕ => (-1 : ℝ) ^ (2 * j + 2) * kTerm (2 * m + 1) (2 * j + 2)) :=
        hsum2.comp_injective (fun _ _ h => by omega)
      have hodd : Summable (fun j : ℕ => (-1 : ℝ) ^ (2 * j + 1 + 2) * kTerm (2 * m + 1) (2 * j + 1 + 2)) :=
        hsum2.comp_injective (fun _ _ h => by omega)
      rw [← tsum_even_add_odd heven hodd, ← heven.tsum_add hodd]
      have hterm_pos : ∀ j : ℕ,
          0 < (-1 : ℝ) ^ (2 * j + 2) * kTerm (2 * m + 1) (2 * j + 2) +
              (-1 : ℝ) ^ (2 * j + 1 + 2) * kTerm (2 * m + 1) (2 * j + 1 + 2) := fun j => by
        have he1 : Even (2 * j + 2) := ⟨j + 1, by ring⟩
        have ho1 : Odd (2 * j + 1 + 2) := ⟨j + 1, by ring⟩
        rw [he1.neg_one_pow, ho1.neg_one_pow, one_mul, neg_one_mul]
        have hlt := kTerm_succ_lt hb (k := 2 * j + 2) (by omega)
        have hpos := kTerm_pos (2 * m + 1) (2 * j + 2)
        have hidx : 2 * j + 1 + 2 = (2 * j + 2) + 1 := by omega
        rw [hidx]
        linarith
      have hge0 : (-1 : ℝ) ^ (2 * 0 + 2) * kTerm (2 * m + 1) (2 * 0 + 2) +
            (-1 : ℝ) ^ (2 * 0 + 1 + 2) * kTerm (2 * m + 1) (2 * 0 + 1 + 2) ≤
          ∑' j : ℕ, ((-1 : ℝ) ^ (2 * j + 2) * kTerm (2 * m + 1) (2 * j + 2) +
            (-1 : ℝ) ^ (2 * j + 1 + 2) * kTerm (2 * m + 1) (2 * j + 1 + 2)) :=
        (heven.add hodd).le_tsum 0 fun j _ => (hterm_pos j).le
      linarith [hterm_pos 0]
    have hpair_pos' : 0 < ∑' k : ℕ, (-1 : ℝ) ^ (k + 1 + 1) * kTerm (2 * m + 1) (k + 1 + 1) := by
      simpa [add_assoc] using hpair_pos
    simp only [zero_add, pow_zero, one_mul, pow_one, neg_one_mul, kTerm_zero, kTerm_one]
    linarith

/-- **Strict positivity `0 < K_b b` for every integer `b ≥ 2`.** -/
theorem K_b_pos (b : ℕ) (hb : 2 ≤ b) : 0 < K_b b :=
  lt_trans (div_pos (by norm_num) (mul_pos (by norm_num) (pow_pos P_inf_pos b)))
    (K_b_gt_lower_bound b hb)

/-! ### Entire Infinite Product `Π_1(ξ) = ∏_{j ≥ 1} (1 + 2^{-j} ξ)` and `Π_b(ξ) = Π_1(ξ)^b` -/

/-- Entire `q`-Pochhammer infinite product `Π_1(ξ) = ∏_{j ≥ 1} (1 + 2^{-j} ξ)`. -/
@[expose] def Pi_1 (ξ : ℂ) : ℂ :=
  ∏' j : ℕ, (1 + (2 : ℂ) ^ (-(j + 1 : ℤ)) * ξ)

/-- Entire infinite product `Π_b(ξ) = (Π_1(ξ))^b = ∏_{j ≥ 1} (1 + 2^{-j} ξ)^b`. -/
@[expose] def Pi_b (b : ℕ) (ξ : ℂ) : ℂ :=
  (Pi_1 ξ) ^ b

/-- Tail logarithm `∑_{k ≥ 0} log (1 + 2^{-(J + k + 1)} ξ)`, holomorphic on `‖ξ‖ < 2^J / 2`. -/
@[expose] def tailLog (J : ℕ) (ξ : ℂ) : ℂ :=
  ∑' k : ℕ, Complex.log (1 + (2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * ξ)

private lemma norm_two_zpow_mul_le {J k : ℕ} {ξ : ℂ} (hξ : ‖ξ‖ ≤ (2 : ℝ) ^ J / 2) :
    ‖(2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * ξ‖ ≤ (1 / 2 : ℝ) ^ (k + 2) := by
  rw [norm_mul, norm_zpow, Complex.norm_ofNat, zpow_neg, zpow_natCast, ← inv_pow]
  calc (2⁻¹ : ℝ) ^ (J + k + 1) * ‖ξ‖
      ≤ (2⁻¹ : ℝ) ^ (J + k + 1) * ((2 : ℝ) ^ J / 2) :=
        mul_le_mul_of_nonneg_left hξ (by positivity)
    _ = (1 / 2 : ℝ) ^ (k + 2) := by
        rw [show J + k + 1 = J + (k + 1) by omega, pow_add, pow_succ', inv_pow]
        have h2J : (2 : ℝ) ^ J ≠ 0 := by positivity
        field_simp [h2J]
        ring

private lemma summable_tailLog {J : ℕ} {ξ : ℂ} (hξ : ‖ξ‖ ≤ (2 : ℝ) ^ J / 2) :
    Summable (fun k : ℕ => Complex.log (1 + (2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * ξ)) := by
  have hgeom : Summable (fun k : ℕ => (3 / 2 : ℝ) * (1 / 2 : ℝ) ^ (k + 2)) := by
    have h := (summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
      ((3 / 2 : ℝ) * (1 / 2 : ℝ) ^ 2)
    refine h.congr fun k => ?_
    rw [pow_add]; ring
  refine Summable.of_norm_bounded hgeom fun k => ?_
  have hle := norm_two_zpow_mul_le (k := k) hξ
  have hhalf : ‖(2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * ξ‖ ≤ 1 / 2 :=
    hle.trans (by
      calc (1 / 2 : ℝ) ^ (k + 2) ≤ (1 / 2 : ℝ) ^ 1 :=
            pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
        _ = 1 / 2 := pow_one _)
  exact (Complex.norm_log_one_add_half_le_self hhalf).trans (mul_le_mul_of_nonneg_left hle (by positivity))

private lemma hasProd_tailLog {J : ℕ} {ξ : ℂ} (hξ : ‖ξ‖ ≤ (2 : ℝ) ^ J / 2) :
    HasProd (fun k : ℕ => 1 + (2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * ξ)
      (Complex.exp (tailLog J ξ)) := by
  have hsum := (summable_tailLog hξ).hasSum
  have htend := (Complex.continuous_exp.tendsto _).comp hsum
  have hfn : (Complex.exp ∘ fun s : Finset ℕ =>
        ∑ k ∈ s, Complex.log (1 + (2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * ξ)) =
      fun s : Finset ℕ => ∏ k ∈ s, (1 + (2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * ξ) := by
    funext s
    simp only [Function.comp_apply, Complex.exp_sum]
    refine Finset.prod_congr rfl fun k _ => ?_
    apply Complex.exp_log
    intro h0
    have hnorm : ‖(2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * ξ‖ = 1 := by
      have : (2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * ξ = -1 := by linear_combination h0
      rw [this, norm_neg, norm_one]
    have hle := (norm_two_zpow_mul_le (k := k) hξ).trans (show (1 / 2 : ℝ) ^ (k + 2) ≤ 1 / 4 from by
      calc (1 / 2 : ℝ) ^ (k + 2) ≤ (1 / 2 : ℝ) ^ 2 :=
            pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
        _ = 1 / 4 := by norm_num)
    linarith
  rw [hfn] at htend
  exact htend

private lemma hasProd_Pi_1_factor (J : ℕ) {ξ : ℂ} (hξ : ‖ξ‖ ≤ (2 : ℝ) ^ J / 2) :
    HasProd (fun j : ℕ => 1 + (2 : ℂ) ^ (-(j + 1 : ℤ)) * ξ)
      ((∏ j ∈ Finset.range J, (1 + (2 : ℂ) ^ (-(j + 1 : ℤ)) * ξ)) * Complex.exp (tailLog J ξ)) := by
  have hsh : HasProd (fun k : ℕ => 1 + (2 : ℂ) ^ (-((k + J : ℕ) + 1 : ℤ)) * ξ) (Complex.exp (tailLog J ξ)) := by
    convert hasProd_tailLog hξ using 1
    funext k
    congr 3
    push_cast; ring
  exact hasProd_of_shift J hsh

lemma Pi_1_eq_fin_mul_exp {J : ℕ} {ξ : ℂ} (hξ : ‖ξ‖ ≤ (2 : ℝ) ^ J / 2) :
    Pi_1 ξ = (∏ j ∈ Finset.range J, (1 + (2 : ℂ) ^ (-(j + 1 : ℤ)) * ξ)) * Complex.exp (tailLog J ξ) :=
  (hasProd_Pi_1_factor J hξ).tprod_eq

lemma Pi_1_hasProd (ξ : ℂ) :
    HasProd (fun j : ℕ => 1 + (2 : ℂ) ^ (-(j + 1 : ℤ)) * ξ) (Pi_1 ξ) := by
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, ‖ξ‖ ≤ (2 : ℝ) ^ J / 2 := by
    refine ⟨Nat.ceil (2 * ‖ξ‖) + 1, ?_⟩
    have h1 : (Nat.ceil (2 * ‖ξ‖) + 1 : ℝ) < (2 : ℝ) ^ (Nat.ceil (2 * ‖ξ‖) + 1) := by
      exact_mod_cast Nat.lt_two_pow_self
    have h2 : 2 * ‖ξ‖ ≤ (Nat.ceil (2 * ‖ξ‖) : ℝ) := Nat.le_ceil _
    linarith
  rw [Pi_1_eq_fin_mul_exp hJ]
  exact hasProd_Pi_1_factor J hJ

private lemma differentiableOn_tailLog (J : ℕ) :
    DifferentiableOn ℂ (tailLog J) (Metric.ball 0 ((2 : ℝ) ^ J / 2)) := by
  intro ξ hξ
  have hξ_lt : ‖ξ‖ < (2 : ℝ) ^ J / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hξ
  have hsum_bound : Summable (fun k : ℕ => (2 : ℝ) * (2⁻¹ : ℝ) ^ (J + k + 1)) := by
    have h := (summable_geometric_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num) (by norm_num)).mul_left
      (2 * (2⁻¹ : ℝ) ^ (J + 1))
    refine h.congr fun k => ?_
    rw [show J + k + 1 = (J + 1) + k by omega, pow_add]; ring
  have hderiv : ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball 0 ((2 : ℝ) ^ J / 2) →
      HasDerivAt (fun w : ℂ => Complex.log (1 + (2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * w))
        ((2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) / (1 + (2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * z)) z := by
    intro k z hz
    have hz_le : ‖z‖ ≤ (2 : ℝ) ^ J / 2 := le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
    have hnorm := (norm_two_zpow_mul_le (k := k) hz_le).trans (show (1 / 2 : ℝ) ^ (k + 2) ≤ 1 / 4 from by
      calc (1 / 2 : ℝ) ^ (k + 2) ≤ (1 / 2 : ℝ) ^ 2 :=
            pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
        _ = 1 / 4 := by norm_num)
    have hslit : 1 + (2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * z ∈ Complex.slitPlane := by
      left
      have hre_neg : -((2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * z).re ≤
          ‖(2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * z‖ := by
        simpa using Complex.re_le_norm (-((2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * z))
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have hinner : HasDerivAt (fun w : ℂ => 1 + (2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * w)
        ((2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ))) z := by
      simpa using ((hasDerivAt_id z).const_mul ((2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)))).const_add 1
    have hcomp := (Complex.hasDerivAt_log hslit).comp z hinner
    simpa [Function.comp_def, div_eq_inv_mul] using hcomp
  have hbound : ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball 0 ((2 : ℝ) ^ J / 2) →
      ‖(2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) / (1 + (2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * z)‖ ≤
        (2 : ℝ) * (2⁻¹ : ℝ) ^ (J + k + 1) := by
    intro k z hz
    have hz_le : ‖z‖ ≤ (2 : ℝ) ^ J / 2 := le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hz)
    have hnorm := (norm_two_zpow_mul_le (k := k) hz_le).trans (show (1 / 2 : ℝ) ^ (k + 2) ≤ 1 / 2 from by
      calc (1 / 2 : ℝ) ^ (k + 2) ≤ (1 / 2 : ℝ) ^ 1 :=
            pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
        _ = 1 / 2 := pow_one _)
    have hden_ge : (1 / 2 : ℝ) ≤ ‖1 + (2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * z‖ := by
      have htri := norm_sub_norm_le (1 : ℂ) (-((2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * z))
      simp only [sub_neg_eq_add, norm_one, norm_neg] at htri
      linarith
    rw [norm_div, norm_zpow, Complex.norm_ofNat, zpow_neg, zpow_natCast, ← inv_pow]
    calc (2⁻¹ : ℝ) ^ (J + k + 1) / ‖1 + (2 : ℂ) ^ (-((J + k + 1 : ℕ) : ℤ)) * z‖
        ≤ (2⁻¹ : ℝ) ^ (J + k + 1) / (1 / 2) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hden_ge
      _ = 2 * (2⁻¹ : ℝ) ^ (J + k + 1) := by ring
  have hd := hasDerivAt_tsum_of_isPreconnected hsum_bound Metric.isOpen_ball
    (convex_ball (0 : ℂ) ((2 : ℝ) ^ J / 2)).isPreconnected hderiv hbound hξ
    (summable_tailLog hξ_lt.le) hξ
  exact hd.differentiableAt.differentiableWithinAt

lemma Pi_1_differentiable : Differentiable ℂ Pi_1 := by
  intro ξ
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, ‖ξ‖ < (2 : ℝ) ^ J / 2 := by
    refine ⟨Nat.ceil (2 * ‖ξ‖) + 2, ?_⟩
    have h1 : (Nat.ceil (2 * ‖ξ‖) + 2 : ℝ) < (2 : ℝ) ^ (Nat.ceil (2 * ‖ξ‖) + 2) := by
      exact_mod_cast Nat.lt_two_pow_self
    have h2 : 2 * ‖ξ‖ ≤ (Nat.ceil (2 * ‖ξ‖) : ℝ) := Nat.le_ceil _
    linarith
  have hmem : ξ ∈ Metric.ball (0 : ℂ) ((2 : ℝ) ^ J / 2) := by
    simpa [Metric.mem_ball, dist_eq_norm] using hJ
  have heq : Pi_1 =ᶠ[𝓝 ξ] fun w : ℂ =>
      (∏ j ∈ Finset.range J, (1 + (2 : ℂ) ^ (-(j + 1 : ℤ)) * w)) * Complex.exp (tailLog J w) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hmem] with w hw
    exact Pi_1_eq_fin_mul_exp (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hw))
  have hdiff_fin : DifferentiableAt ℂ
      (fun w : ℂ => ∏ j ∈ Finset.range J, (1 + (2 : ℂ) ^ (-(j + 1 : ℤ)) * w)) ξ :=
    differentiableAt_finset_prod _ _ _ fun j _ => by fun_prop
  have hdiff_tail : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (tailLog J w)) ξ :=
    ((differentiableOn_tailLog J ξ hmem).differentiableAt (Metric.isOpen_ball.mem_nhds hmem)).cexp
  exact (hdiff_fin.mul hdiff_tail).congr_of_eventuallyEq heq

lemma Pi_b_differentiable (b : ℕ) : Differentiable ℂ (Pi_b b) :=
  Pi_1_differentiable.pow b

lemma Pi_1_zero : Pi_1 0 = 1 := by
  unfold Pi_1; simp

lemma Pi_b_zero (b : ℕ) : Pi_b b 0 = 1 := by
  simp [Pi_b, Pi_1_zero]

lemma Pi_1_neg_one : Pi_1 (-1) = (P_inf : ℂ) := by
  have hreal := hasProd_P_inf
  have htend := (Complex.continuous_ofReal.tendsto _).comp hreal
  have hfn : (Complex.ofReal ∘ fun s : Finset ℕ => ∏ r ∈ s, (1 - (2 : ℝ) ^ (-(r + 1 : ℤ)))) =
      fun s : Finset ℕ => ∏ r ∈ s, (1 + (2 : ℂ) ^ (-(r + 1 : ℤ)) * (-1)) := by
    funext s
    simp only [Function.comp_apply, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun r _ => ?_
    push_cast; ring
  rw [hfn, ← P_inf_eq_exp_tsum] at htend
  exact HasProd.tprod_eq htend

lemma Pi_b_neg_one (b : ℕ) : Pi_b b (-1) = (P_inf : ℂ) ^ b := by
  simp [Pi_b, Pi_1_neg_one]

lemma Pi_1_ne_zero {ξ : ℂ} (hξ : ∀ j : ℕ, 1 + (2 : ℂ) ^ (-(j + 1 : ℤ)) * ξ ≠ 0) :
    Pi_1 ξ ≠ 0 := by
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, ‖ξ‖ ≤ (2 : ℝ) ^ J / 2 := by
    refine ⟨Nat.ceil (2 * ‖ξ‖) + 1, ?_⟩
    have h1 : (Nat.ceil (2 * ‖ξ‖) + 1 : ℝ) < (2 : ℝ) ^ (Nat.ceil (2 * ‖ξ‖) + 1) := by
      exact_mod_cast Nat.lt_two_pow_self
    have h2 : 2 * ‖ξ‖ ≤ (Nat.ceil (2 * ‖ξ‖) : ℝ) := Nat.le_ceil _
    linarith
  rw [Pi_1_eq_fin_mul_exp hJ]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => hξ j) (Complex.exp_ne_zero _)

lemma Pi_b_ne_zero (b : ℕ) {ξ : ℂ} (hξ : ∀ j : ℕ, 1 + (2 : ℂ) ^ (-(j + 1 : ℤ)) * ξ ≠ 0) :
    Pi_b b ξ ≠ 0 :=
  pow_ne_zero b (Pi_1_ne_zero hξ)

lemma Pi_1_two_mul (ξ : ℂ) : Pi_1 (2 * ξ) = (1 + ξ) * Pi_1 ξ := by
  have hfn : (fun j : ℕ => 1 + (2 : ℂ) ^ (-((j + 1 : ℕ) + 1 : ℤ)) * (2 * ξ)) =
      fun j : ℕ => 1 + (2 : ℂ) ^ (-(j + 1 : ℤ)) * ξ := by
    funext j
    have h2 : (2 : ℂ) ^ (-((j + 1 : ℕ) + 1 : ℤ)) * 2 = (2 : ℂ) ^ (-(j + 1 : ℤ)) := by
      rw [show (-((j + 1 : ℕ) + 1 : ℤ)) = -(j + 1 : ℤ) - 1 by omega,
        zpow_sub_one₀ (by norm_num : (2 : ℂ) ≠ 0)]
      ring
    calc 1 + (2 : ℂ) ^ (-((j + 1 : ℕ) + 1 : ℤ)) * (2 * ξ)
        = 1 + ((2 : ℂ) ^ (-((j + 1 : ℕ) + 1 : ℤ)) * 2) * ξ := by ring
      _ = 1 + (2 : ℂ) ^ (-(j + 1 : ℤ)) * ξ := by rw [h2]
  have hpξ : HasProd (fun j : ℕ => 1 + (2 : ℂ) ^ (-((j + 1 : ℕ) + 1 : ℤ)) * (2 * ξ)) (Pi_1 ξ) := by
    rw [hfn]; exact Pi_1_hasProd ξ
  have hp2 : HasProd (fun j : ℕ => 1 + (2 : ℂ) ^ (-(j + 1 : ℤ)) * (2 * ξ))
      ((1 + (2 : ℂ) ^ (-(0 + 1 : ℤ)) * (2 * ξ)) * Pi_1 ξ) :=
    hasProd_of_shift_one (f := fun j : ℕ => 1 + (2 : ℂ) ^ (-(j + 1 : ℤ)) * (2 * ξ)) hpξ
  have h0' : 1 + (2 : ℂ) ^ (-(0 + 1 : ℤ)) * (2 * ξ) = 1 + ξ := by
    rw [zero_add, zpow_neg_one]; ring
  rw [h0'] at hp2
  exact hp2.tprod_eq

lemma Pi_b_two_mul (b : ℕ) (ξ : ℂ) : Pi_b b (2 * ξ) = (1 + ξ) ^ b * Pi_b b ξ := by
  simp only [Pi_b, Pi_1_two_mul, mul_pow]

lemma Pi_1_pow_two_mul (m : ℕ) (ξ : ℂ) :
    Pi_1 ((2 : ℂ) ^ m * ξ) = Pi_1 ξ * ∏ r ∈ Finset.range m, (1 + (2 : ℂ) ^ r * ξ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, Pi_1_two_mul, ih, Finset.prod_range_succ]
    ring

lemma Pi_b_pow_two_mul (b m : ℕ) (ξ : ℂ) :
    Pi_b b ((2 : ℂ) ^ m * ξ) = Pi_b b ξ * ∏ r ∈ Finset.range m, (1 + (2 : ℂ) ^ r * ξ) ^ b := by
  simp only [Pi_b, Pi_1_pow_two_mul, mul_pow, Finset.prod_pow]

/-! ### Global Meromorphic `G_mero`, Local `G_series`, Elliptic `Ψ_b`, and Decomposition -/

/-- Local OGF / inverse Borel power series `G_series b t = ∑_{n ≥ 0} c_{b, n} t^n`. -/
@[expose] def G_series (b : ℕ) (t : ℂ) : ℂ :=
  ∑' n : ℕ, frPoissonCoeff b n * t ^ n

/-- `k`-th term of the super-exponentially convergent global meromorphic series for `G_b(t)`. -/
@[expose] def G_meroTerm (b k : ℕ) (t : ℂ) : ℂ :=
  (2 : ℂ) ^ (-((b * (k * (k - 1) / 2) : ℕ) : ℤ)) * t ^ (k * b + 1) /
    ((1 + t / (2 : ℂ) ^ k) * ∏ j ∈ Finset.range k, (1 + t / (2 : ℂ) ^ j) ^ b)

/-- Global meromorphic expansion of `G_b(t)` on `ℂ \ {-2^k : k ≥ 0}`. -/
@[expose] def G_mero (b : ℕ) (t : ℂ) : ℂ :=
  ∑' k : ℕ, G_meroTerm b k t

/-- Inverse Laplace / Borel function `L_b(ξ) = ξ⁻¹ G_mero b (ξ⁻¹)` on `ℂ \ [-1, 0]`. -/
@[expose] def L_b (b : ℕ) (ξ : ℂ) : ℂ :=
  ξ⁻¹ * G_mero b ξ⁻¹

/-- The `m`-th term of the doubly periodic series `Ψ_b`. -/
@[expose] def psiTerm (b : ℕ) (w : ℂ) : ℂ :=
  w / ((1 + w) * Pi_b b w)

/-- Doubly periodic elliptic function `Ψ_b(u) = ∑_{m ∈ ℤ} 2^{m - u} / ((1 + 2^{m - u}) Π_b(2^{m - u}))`. -/
@[expose] def Psi_b (b : ℕ) (u : ℂ) : ℂ :=
  ∑' m : ℤ, psiTerm b ((2 : ℂ) ^ m * Complex.exp (-((Real.log 2 : ℝ) : ℂ) * u))

/-- Holomorphic tail `T_b(ξ) = ∑_{k ≥ 0} psiTerm b (2^{-(k+1)} ξ)` on `‖ξ‖ < 2`. -/
@[expose] def T_b (b : ℕ) (ξ : ℂ) : ℂ :=
  ∑' k : ℕ, psiTerm b ((2 : ℂ) ^ (-(k + 1 : ℤ)) * ξ)

/-- Exact term-by-term algebraic identity linking `ξ * G_meroTerm b k ξ⁻¹` to `Pi_b b ξ * psiTerm b (2^k ξ)`. -/
lemma xi_mul_G_meroTerm_inv {b : ℕ} (k : ℕ) {ξ : ℂ} (hξ : ξ ≠ 0)
    (hPi : Pi_b b ξ ≠ 0) :
    ξ * G_meroTerm b k ξ⁻¹ = Pi_b b ξ * psiTerm b ((2 : ℂ) ^ k * ξ) := by
  unfold G_meroTerm psiTerm
  rw [Pi_b_pow_two_mul]
  have h2k : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  have hfac_k : 1 + ξ⁻¹ / (2 : ℂ) ^ k = (1 + (2 : ℂ) ^ k * ξ) / ((2 : ℂ) ^ k * ξ) := by
    field_simp [hξ, h2k]; ring
  have hprod_eq : ∏ j ∈ Finset.range k, (1 + ξ⁻¹ / (2 : ℂ) ^ j) ^ b =
      (∏ j ∈ Finset.range k, (1 + (2 : ℂ) ^ j * ξ) ^ b) /
        ((2 : ℂ) ^ (b * (k * (k - 1) / 2)) * ξ ^ (k * b)) := by
    have hsum_range : ∑ j ∈ Finset.range k, j = k * (k - 1) / 2 := Finset.sum_range_id k
    have hterm : ∀ j ∈ Finset.range k,
        (1 + ξ⁻¹ / (2 : ℂ) ^ j) ^ b = (1 + (2 : ℂ) ^ j * ξ) ^ b / (((2 : ℂ) ^ j) ^ b * ξ ^ b) := by
      intro j _
      have h2j : (2 : ℂ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
      rw [← mul_pow, ← div_pow]
      congr 1
      field_simp [hξ, h2j]; ring
    rw [Finset.prod_congr rfl hterm, Finset.prod_div_distrib, Finset.prod_mul_distrib]
    congr 1
    have h2prod : (∏ j ∈ Finset.range k, ((2 : ℂ) ^ j) ^ b) = (2 : ℂ) ^ (b * (k * (k - 1) / 2)) := by
      rw [Finset.prod_pow, Finset.prod_pow_eq_pow_sum, hsum_range, ← pow_mul, mul_comm _ b]
    have hξprod : (∏ _j ∈ Finset.range k, ξ ^ b) = ξ ^ (k * b) := by
      rw [Finset.prod_const, Finset.card_range, ← pow_mul, mul_comm b k]
    rw [h2prod, hξprod]
  rw [hfac_k, hprod_eq]
  have hnum : (2 : ℂ) ^ (-((b * (k * (k - 1) / 2) : ℕ) : ℤ)) * (ξ⁻¹) ^ (k * b + 1) =
      ((2 : ℂ) ^ (b * (k * (k - 1) / 2)) * ξ ^ (k * b) * ξ)⁻¹ := by
    rw [zpow_neg, zpow_natCast, inv_pow, pow_succ, mul_inv, mul_inv]
    ring
  rw [hnum]
  have h2pow_ne : (2 : ℂ) ^ (b * (k * (k - 1) / 2)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hξpow_ne : ξ ^ (k * b) ≠ 0 := pow_ne_zero _ hξ
  by_cases hdenom : (1 + (2 : ℂ) ^ k * ξ) * ∏ j ∈ Finset.range k, (1 + (2 : ℂ) ^ j * ξ) ^ b = 0
  · rcases mul_eq_zero.mp hdenom with h1 | h2
    · simp [h1]
    · simp [h2]
  · have h1 : 1 + (2 : ℂ) ^ k * ξ ≠ 0 := (mul_ne_zero_iff.mp hdenom).1
    have h2 : ∏ j ∈ Finset.range k, (1 + (2 : ℂ) ^ j * ξ) ^ b ≠ 0 := (mul_ne_zero_iff.mp hdenom).2
    field_simp [hξ, hPi, h2k, h2pow_ne, hξpow_ne, h1, h2]

/-- Lower bound `‖1 + 2^r * w‖ ≥ 2^(r - 1) * ‖w‖` once `2^r * ‖w‖ ≥ 2`. -/
private lemma norm_one_add_two_pow_mul_ge {r : ℕ} {w : ℂ} (h : 2 ≤ (2 : ℝ) ^ r * ‖w‖) :
    (2 : ℝ) ^ r * ‖w‖ / 2 ≤ ‖1 + (2 : ℂ) ^ r * w‖ := by
  have htri := norm_sub_norm_le ((2 : ℂ) ^ r * w) (-1)
  simp only [sub_neg_eq_add, norm_neg, norm_one, norm_mul, norm_pow, Complex.norm_ofNat] at htri
  rw [add_comm] at htri
  linarith

/-- Uniform super-exponential bound for `G_meroTerm b k t` on `{‖t‖ ≤ R, ∀ j, δ ≤ ‖1 + t / 2^j‖}`. -/
private lemma norm_G_meroTerm_le_uniform {b : ℕ} (hb : 1 ≤ b) {R δ : ℝ} (hR : 1 ≤ R) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℂ), ‖t‖ ≤ R → (∀ j : ℕ, δ ≤ ‖1 + t / (2 : ℂ) ^ j‖) →
      ∀ k : ℕ, ‖G_meroTerm b k t‖ ≤ C * (1 / 2 : ℝ) ^ k := by
  let J₀ : ℕ := Nat.ceil (2 * R) + 1
  have h2J : 2 * R ≤ (2 : ℝ) ^ J₀ := by
    have h1 : (Nat.ceil (2 * R) + 1 : ℝ) < (2 : ℝ) ^ J₀ := by
      exact_mod_cast Nat.lt_two_pow_self
    linarith [Nat.le_ceil (2 * R)]
  let L : ℕ := Nat.ceil (4 * R) + 3
  let M : ℕ := 2 * (L + 1) + 2
  let c₀ : ℝ := (min δ (1 / 2)) ^ (J₀ * b) * δ
  have hc₀ : 0 < c₀ := mul_pos (pow_pos (lt_min hδ (by norm_num)) _) hδ
  let C_fin : ℝ := (Finset.range M).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
    (fun k => (2 : ℝ) ^ k * (R ^ (k * b + 1) / (c₀ * (1 / 2 : ℝ) ^ (k * b))))
  refine ⟨max C_fin (R / c₀), le_trans (by positivity) (le_max_right _ _), fun t htR htδ k => ?_⟩
  have hhalf_ge : ∀ j ≥ J₀, (1 / 2 : ℝ) ≤ ‖1 + t / (2 : ℂ) ^ j‖ := fun j hj => by
    have hle : ‖t / (2 : ℂ) ^ j‖ ≤ 1 / 2 := by
      rw [norm_div, norm_pow, Complex.norm_ofNat, div_le_iff₀ (by positivity)]
      have h2j : (2 : ℝ) ^ J₀ ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) hj
      linarith
    have htri := norm_sub_norm_le (1 : ℂ) (-(t / (2 : ℂ) ^ j))
    simp only [sub_neg_eq_add, norm_one, norm_neg] at htri
    linarith
  have hprod_lb : (min δ (1 / 2)) ^ (J₀ * b) * (1 / 2 : ℝ) ^ (k * b) ≤
      ‖∏ j ∈ Finset.range k, (1 + t / (2 : ℂ) ^ j) ^ b‖ := by
    rw [norm_prod]
    have hmin_pos : 0 < min δ (1 / 2) := lt_min hδ (by norm_num)
    have hmin_le1 : min δ (1 / 2) ≤ 1 := (min_le_right _ _).trans (by norm_num)
    calc (min δ (1 / 2)) ^ (J₀ * b) * (1 / 2 : ℝ) ^ (k * b)
        = (min δ (1 / 2)) ^ (J₀ * b) * ∏ _j ∈ Finset.range k, (1 / 2 : ℝ) ^ b := by
          rw [Finset.prod_const, Finset.card_range, ← pow_mul, mul_comm b k]
      _ ≤ (∏ j ∈ Finset.range k, (if j < J₀ then (min δ (1 / 2)) ^ b else (1 / 2 : ℝ) ^ b)) := by
          have h1 : (∏ j ∈ Finset.range k, (if j < J₀ then (min δ (1 / 2)) ^ b else (1 / 2 : ℝ) ^ b)) =
              (∏ j ∈ (Finset.range k).filter (· < J₀), (min δ (1 / 2)) ^ b) *
              (∏ j ∈ (Finset.range k).filter (fun j => ¬ j < J₀), (1 / 2 : ℝ) ^ b) := by
            rw [← Finset.prod_filter_mul_prod_filter_not (Finset.range k) (· < J₀)]
            congr 1
            · exact Finset.prod_congr rfl fun j hj => by simp [(Finset.mem_filter.mp hj).2]
            · exact Finset.prod_congr rfl fun j hj => by simp [(Finset.mem_filter.mp hj).2]
          rw [h1]
          simp only [Finset.prod_const, Finset.card_range, ← pow_mul]
          have hcard1 : ((Finset.range k).filter (· < J₀)).card ≤ J₀ := by
            calc ((Finset.range k).filter (· < J₀)).card ≤ (Finset.range J₀).card :=
                  Finset.card_le_card fun j hj => Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
              _ = J₀ := Finset.card_range J₀
          have hcard2 : ((Finset.range k).filter (fun j => ¬ j < J₀)).card ≤ k := by
            calc ((Finset.range k).filter (fun j => ¬ j < J₀)).card ≤ (Finset.range k).card :=
                  Finset.card_filter_le _ _
              _ = k := Finset.card_range k
          refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
          · rw [mul_comm b _]
            exact pow_le_pow_of_le_one hmin_pos.le hmin_le1 (Nat.mul_le_mul_right b hcard1)
          · exact pow_le_pow_of_le_one (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
              (Nat.mul_le_mul_left b hcard2)
      _ ≤ ∏ j ∈ Finset.range k, ‖(1 + t / (2 : ℂ) ^ j) ^ b‖ := by
          refine real_finset_prod_le_prod (fun j _ => by split_ifs <;> positivity) fun j _ => ?_
          rw [norm_pow]
          split_ifs with hj
          · exact pow_le_pow_left₀ (by positivity) ((min_le_left _ _).trans (htδ j)) b
          · exact pow_le_pow_left₀ (by positivity) (hhalf_ge j (by omega)) b
  have hden_ge : c₀ * (1 / 2 : ℝ) ^ (k * b) ≤
      ‖(1 + t / (2 : ℂ) ^ k) * ∏ j ∈ Finset.range k, (1 + t / (2 : ℂ) ^ j) ^ b‖ := by
    rw [norm_mul]
    dsimp only [c₀]
    calc (min δ (1 / 2)) ^ (J₀ * b) * δ * (1 / 2 : ℝ) ^ (k * b)
        = δ * ((min δ (1 / 2)) ^ (J₀ * b) * (1 / 2 : ℝ) ^ (k * b)) := by ring
      _ ≤ ‖1 + t / (2 : ℂ) ^ k‖ * ‖∏ j ∈ Finset.range k, (1 + t / (2 : ℂ) ^ j) ^ b‖ :=
          mul_le_mul (htδ k) hprod_lb (by positivity) (norm_nonneg _)
  have hbase : ‖G_meroTerm b k t‖ ≤
      (2 : ℝ) ^ (-((b * (k * (k - 1) / 2) : ℕ) : ℤ)) * R ^ (k * b + 1) /
        (c₀ * (1 / 2 : ℝ) ^ (k * b)) := by
    unfold G_meroTerm
    rw [norm_div, norm_mul, norm_zpow, Complex.norm_ofNat, norm_pow]
    refine div_le_div₀ (by positivity) ?_ (by positivity) hden_ge
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) htR _) (by positivity)
  by_cases hkM : k < M
  · have hsup : (2 : ℝ) ^ k * (R ^ (k * b + 1) / (c₀ * (1 / 2 : ℝ) ^ (k * b))) ≤ C_fin :=
      Finset.le_sup' (f := fun j => (2 : ℝ) ^ j * (R ^ (j * b + 1) / (c₀ * (1 / 2 : ℝ) ^ (j * b))))
        (Finset.mem_range.mpr hkM)
    have hpow_le1 : (2 : ℝ) ^ (-((b * (k * (k - 1) / 2) : ℕ) : ℤ)) ≤ 1 := by
      rw [zpow_neg, zpow_natCast]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    calc ‖G_meroTerm b k t‖
        ≤ 1 * R ^ (k * b + 1) / (c₀ * (1 / 2 : ℝ) ^ (k * b)) := hbase.trans (by gcongr)
      _ = ((2 : ℝ) ^ k * (R ^ (k * b + 1) / (c₀ * (1 / 2 : ℝ) ^ (k * b)))) * (1 / 2 : ℝ) ^ k := by
          have h2h : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
          linear_combination -(R ^ (k * b + 1) / (c₀ * (1 / 2 : ℝ) ^ (k * b))) * h2h
      _ ≤ max C_fin (R / c₀) * (1 / 2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right (hsup.trans (le_max_left _ _)) (by positivity)
  · push Not at hkM
    have htri_ge : L * (k * b) + k ≤ b * (k * (k - 1) / 2) := by
      have hdiv : 2 * (L + 1) ≤ k - 1 := by omega
      have hhalf : (L + 1) * k ≤ k * (k - 1) / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        calc (L + 1) * k * 2 = k * (2 * (L + 1)) := by ring
          _ ≤ k * (k - 1) := Nat.mul_le_mul_left k hdiv
      calc L * (k * b) + k ≤ L * (k * b) + b * k := Nat.add_le_add_left (Nat.le_mul_of_pos_left k hb) _
        _ = b * ((L + 1) * k) := by ring
        _ ≤ b * (k * (k - 1) / 2) := Nat.mul_le_mul_left b hhalf
    have h2R_lt : 2 * R ≤ (2 : ℝ) ^ L := by
      have h1 : (L : ℝ) < (2 : ℝ) ^ L := by exact_mod_cast Nat.lt_two_pow_self
      dsimp only [L] at h1 ⊢
      push_cast at h1
      linarith [Nat.le_ceil (4 * R)]
    have hkill_mul : (2 * R) ^ (k * b) * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (b * (k * (k - 1) / 2)) := by
      calc (2 * R) ^ (k * b) * (2 : ℝ) ^ k
          ≤ ((2 : ℝ) ^ L) ^ (k * b) * (2 : ℝ) ^ k :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h2R_lt _) (by positivity)
        _ = (2 : ℝ) ^ (L * (k * b) + k) := by rw [← pow_mul, ← pow_add]
        _ ≤ (2 : ℝ) ^ (b * (k * (k - 1) / 2)) := pow_le_pow_right₀ (by norm_num) htri_ge
    have hkill : (2 : ℝ) ^ (-((b * (k * (k - 1) / 2) : ℕ) : ℤ)) * R ^ (k * b + 1) /
          (c₀ * (1 / 2 : ℝ) ^ (k * b)) ≤ (R / c₀) * (1 / 2 : ℝ) ^ k := by
      rw [zpow_neg, zpow_natCast, pow_succ, one_div, inv_pow]
      have h2tri : (2 : ℝ) ^ (b * (k * (k - 1) / 2)) ≠ 0 := by positivity
      have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
      have h2kb : (2 : ℝ) ^ (k * b) ≠ 0 := by positivity
      have hrew : ((2 : ℝ) ^ (b * (k * (k - 1) / 2)))⁻¹ * (R ^ (k * b) * R) / (c₀ * ((2 : ℝ) ^ (k * b))⁻¹) =
          (R / c₀) * ((2 * R) ^ (k * b) / (2 : ℝ) ^ (b * (k * (k - 1) / 2))) := by
        rw [mul_pow]; field_simp [h2tri, h2kb, hc₀.ne']
      rw [hrew]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [div_le_iff₀ (by positivity), inv_pow, inv_mul_eq_div, le_div_iff₀ (by positivity)]
      linarith [hkill_mul]
    exact hbase.trans (hkill.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))

lemma summable_G_meroTerm {b : ℕ} (hb : 1 ≤ b) {t : ℂ} (ht : ∀ j : ℕ, 1 + t / (2 : ℂ) ^ j ≠ 0) :
    Summable (fun k : ℕ => G_meroTerm b k t) := by
  let R : ℝ := max 1 ‖t‖
  let J₀ : ℕ := Nat.ceil (2 * R) + 1
  have h2J : 2 * R ≤ (2 : ℝ) ^ J₀ := by
    have h1 : (Nat.ceil (2 * R) + 1 : ℝ) < (2 : ℝ) ^ J₀ := by exact_mod_cast Nat.lt_two_pow_self
    linarith [Nat.le_ceil (2 * R)]
  have hne_fin : (Finset.range (J₀ + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  let δ : ℝ := min (1 / 2) ((Finset.range (J₀ + 1)).inf' hne_fin (fun j => ‖1 + t / (2 : ℂ) ^ j‖))
  have hδ : 0 < δ := by
    refine lt_min (by norm_num) ?_
    rw [Finset.lt_inf'_iff]
    intro j _
    exact norm_pos_iff.mpr (ht j)
  have htδ : ∀ j : ℕ, δ ≤ ‖1 + t / (2 : ℂ) ^ j‖ := fun j => by
    by_cases hj : j < J₀ + 1
    · exact (min_le_right _ _).trans
        (Finset.inf'_le (f := fun i => ‖1 + t / (2 : ℂ) ^ i‖) (Finset.mem_range.mpr hj))
    · have hle : ‖t / (2 : ℂ) ^ j‖ ≤ 1 / 2 := by
        rw [norm_div, norm_pow, Complex.norm_ofNat, div_le_iff₀ (by positivity)]
        have h2j : (2 : ℝ) ^ J₀ ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
        have htR : ‖t‖ ≤ R := le_max_right _ _
        linarith
      have htri := norm_sub_norm_le (1 : ℂ) (-(t / (2 : ℂ) ^ j))
      simp only [sub_neg_eq_add, norm_one, norm_neg] at htri
      exact (min_le_left _ _).trans (by linarith)
  obtain ⟨C, _, hC⟩ := norm_G_meroTerm_le_uniform hb (le_max_left 1 ‖t‖) hδ
  refine Summable.of_norm_bounded (g := fun k => C * (1 / 2 : ℝ) ^ k)
    ((summable_geometric_of_lt_one (by positivity) (by norm_num)).mul_left C)
    (hC t (le_max_right _ _) htδ)

/-- Exact functional equation `G_mero b t = t / (1 + t) + 2 * (t / (1 + t))^b * G_mero b (t / 2)`. -/
lemma G_mero_func_eq {b : ℕ} (hb : 1 ≤ b) {t : ℂ} (ht : ∀ j : ℕ, 1 + t / (2 : ℂ) ^ j ≠ 0) :
    G_mero b t = t / (1 + t) + 2 * (t / (1 + t)) ^ b * G_mero b (t / 2) := by
  have hsum := summable_G_meroTerm hb ht
  unfold G_mero
  rw [hsum.tsum_eq_zero_add, ← tsum_mul_left]
  congr 1
  · unfold G_meroTerm; simp
  · refine tsum_congr fun k => ?_
    unfold G_meroTerm
    have htri : (k + 1) * k / 2 = k * (k - 1) / 2 + k := by
      cases k with
      | zero => simp
      | succ m =>
        have h1 : (m + 1 + 1) * (m + 1) = (m + 1) * m + 2 * (m + 1) := by ring
        rw [h1, Nat.add_mul_div_left _ _ (by norm_num)]
        simp
    have hpow2 : (2 : ℂ) ^ (-((b * ((k + 1) * k / 2) : ℕ) : ℤ)) =
        2 * (2 : ℂ) ^ (-((b * (k * (k - 1) / 2) : ℕ) : ℤ)) / (2 : ℂ) ^ (k * b + 1) := by
      rw [htri, mul_add, Nat.cast_add, neg_add, zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0),
        pow_succ, mul_comm b k]
      simp only [zpow_neg, zpow_natCast]
      have h2k : (2 : ℂ) ^ (k * b) ≠ 0 := pow_ne_zero _ (by norm_num)
      have h2t : (2 : ℂ) ^ (b * (k * (k - 1) / 2)) ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp [h2k, h2t]
    have hprod_shift : ∏ j ∈ Finset.range (k + 1), (1 + t / (2 : ℂ) ^ j) ^ b =
        (1 + t) ^ b * ∏ j ∈ Finset.range k, (1 + t / 2 / (2 : ℂ) ^ j) ^ b := by
      rw [Finset.prod_range_succ', pow_zero, div_one, mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [pow_succ', div_div, mul_comm (2 : ℂ) ((2 : ℂ) ^ j)]
    have hdiv_shift : 1 + t / (2 : ℂ) ^ (k + 1) = 1 + t / 2 / (2 : ℂ) ^ k := by
      rw [pow_succ', div_div, mul_comm (2 : ℂ) ((2 : ℂ) ^ k)]
    simp only [Nat.add_sub_cancel]
    rw [hpow2, hprod_shift, hdiv_shift, div_pow t 2, div_pow t (1 + t)]
    have h1t : 1 + t ≠ 0 := by simpa using ht 0
    have h1tb : (1 + t) ^ b ≠ 0 := pow_ne_zero b h1t
    have h2kb : (2 : ℂ) ^ (k * b + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have htk : t ^ ((k + 1) * b + 1) = t ^ b * t ^ (k * b + 1) := by
      rw [← pow_add]; congr 1; ring
    rw [htk]
    field_simp [h1tb, h2kb]

/-- `G_mero b` is holomorphic on `ℂ \ {-2^j : j ≥ 0}`. -/
lemma G_mero_differentiableOn {b : ℕ} (hb : 1 ≤ b) :
    DifferentiableOn ℂ (G_mero b) {t : ℂ | ∀ j : ℕ, 1 + t / (2 : ℂ) ^ j ≠ 0} := by
  intro t₀ ht₀
  -- Construct a small ball `Metric.ball t₀ ε` on which `∀ j, δ ≤ ‖1 + t / 2^j‖`.
  let R : ℝ := ‖t₀‖ + 2
  let J₀ : ℕ := Nat.ceil (2 * R) + 1
  have h2J : 2 * R ≤ (2 : ℝ) ^ J₀ := by
    have h1 : (Nat.ceil (2 * R) + 1 : ℝ) < (2 : ℝ) ^ J₀ := by exact_mod_cast Nat.lt_two_pow_self
    linarith [Nat.le_ceil (2 * R)]
  have hne_fin : (Finset.range (J₀ + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  let m₀ : ℝ := (Finset.range (J₀ + 1)).inf' hne_fin (fun j => ‖1 + t₀ / (2 : ℂ) ^ j‖)
  have hm₀ : 0 < m₀ := by
    dsimp only [m₀]; rw [Finset.lt_inf'_iff]; intro j _; exact norm_pos_iff.mpr (ht₀ j)
  let ε : ℝ := min 1 (m₀ / 2)
  have hε : 0 < ε := lt_min zero_lt_one (half_pos hm₀)
  let δ : ℝ := min (1 / 2) (m₀ / 2)
  have hδ : 0 < δ := lt_min (by norm_num) (half_pos hm₀)
  have hball_ok : ∀ t ∈ Metric.ball t₀ ε, ‖t‖ ≤ R ∧ ∀ j : ℕ, δ ≤ ‖1 + t / (2 : ℂ) ^ j‖ := by
    intro t ht
    have hdist : ‖t - t₀‖ < ε := by simpa [Metric.mem_ball, dist_eq_norm] using ht
    have htR : ‖t‖ ≤ R := by
      have htri : ‖t‖ ≤ ‖t - t₀‖ + ‖t₀‖ := by
        calc ‖t‖ = ‖(t - t₀) + t₀‖ := by ring_nf
          _ ≤ ‖t - t₀‖ + ‖t₀‖ := norm_add_le _ _
      have hε1 : ε ≤ 1 := min_le_left _ _
      dsimp only [R]; linarith
    refine ⟨htR, fun j => ?_⟩
    by_cases hj : j < J₀ + 1
    · have h0 : m₀ ≤ ‖1 + t₀ / (2 : ℂ) ^ j‖ :=
        Finset.inf'_le (f := fun i => ‖1 + t₀ / (2 : ℂ) ^ i‖) (Finset.mem_range.mpr hj)
      have hdiff : ‖(1 + t / (2 : ℂ) ^ j) - (1 + t₀ / (2 : ℂ) ^ j)‖ ≤ ‖t - t₀‖ := by
        rw [show (1 + t / (2 : ℂ) ^ j) - (1 + t₀ / (2 : ℂ) ^ j) = (t - t₀) / (2 : ℂ) ^ j by ring,
          norm_div, norm_pow, Complex.norm_ofNat]
        exact div_le_self (norm_nonneg _) (one_le_pow₀ (by norm_num))
      have htri := norm_sub_norm_le (1 + t₀ / (2 : ℂ) ^ j) (1 + t / (2 : ℂ) ^ j)
      rw [norm_sub_rev] at htri
      have hεm : ε ≤ m₀ / 2 := min_le_right _ _
      exact (min_le_right _ _).trans (by linarith)
    · have hle : ‖t / (2 : ℂ) ^ j‖ ≤ 1 / 2 := by
        rw [norm_div, norm_pow, Complex.norm_ofNat, div_le_iff₀ (by positivity)]
        have h2j : (2 : ℝ) ^ J₀ ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
      have htri := norm_sub_norm_le (1 : ℂ) (-(t / (2 : ℂ) ^ j))
      simp only [sub_neg_eq_add, norm_one, norm_neg] at htri
      exact (min_le_left _ _).trans (by linarith)
  have hR1 : 1 ≤ R := by change 1 ≤ ‖t₀‖ + 2; linarith [norm_nonneg t₀]
  obtain ⟨C, _, hC⟩ := norm_G_meroTerm_le_uniform hb hR1 hδ
  have hpart_diff : ∀ N : ℕ, DifferentiableOn ℂ (fun t => ∑ k ∈ Finset.range N, G_meroTerm b k t) (Metric.ball t₀ ε) := by
    intro N
    refine DifferentiableOn.fun_sum fun k _ => ?_
    intro t ht
    have hok := (hball_ok t ht).2
    have hne : ∀ j : ℕ, 1 + t / (2 : ℂ) ^ j ≠ 0 := fun j => norm_pos_iff.mp (lt_of_lt_of_le hδ (hok j))
    unfold G_meroTerm
    refine (DifferentiableAt.div (by fun_prop) ?_ ?_).differentiableWithinAt
    · exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => 1 + z / (2 : ℂ) ^ k) t).mul
        (differentiableAt_finset_prod _ _ _ fun j _ => by fun_prop)
    · exact mul_ne_zero (hne k) (Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero b (hne j))
  have hunif : TendstoUniformlyOn (fun N t => ∑ k ∈ Finset.range N, G_meroTerm b k t) (G_mero b)
      atTop (Metric.ball t₀ ε) := by
    refine tendstoUniformlyOn_tsum_nat (u := fun k => C * (1 / 2 : ℝ) ^ k)
      ((summable_geometric_of_lt_one (by positivity) (by norm_num)).mul_left C) ?_
    intro k t ht
    exact hC t (hball_ok t ht).1 (hball_ok t ht).2 k
  have hdiff_ball : DifferentiableOn ℂ (G_mero b) (Metric.ball t₀ ε) :=
    hunif.tendstoLocallyUniformlyOn.differentiableOn (Filter.Eventually.of_forall hpart_diff) Metric.isOpen_ball
  exact (hdiff_ball t₀ (Metric.mem_ball_self hε)).differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)) |>.differentiableWithinAt

/-- Local binomial identity `∑_{k=1}^N C(b, N - k) (-1)^{k-1} = C(b - 1, N - 1)` for `1 ≤ N < b`. -/
private lemma sum_choose_alt_eq {b N : ℕ} (hN1 : 1 ≤ N) (hNb : N < b) :
    ∑ k ∈ Finset.Icc 1 N, ((b.choose (N - k) : ℕ) : ℂ) * (-1 : ℂ) ^ (k - 1) =
      (((b - 1).choose (N - 1) : ℕ) : ℂ) := by
  induction N with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      simp
    | succ r =>
      have hsplit : ∑ k ∈ Finset.Icc 1 (r + 2), ((b.choose (r + 2 - k) : ℕ) : ℂ) * (-1 : ℂ) ^ (k - 1) =
          ((b.choose (r + 1) : ℕ) : ℂ) -
            ∑ k ∈ Finset.Icc 1 (r + 1), ((b.choose (r + 1 - k) : ℕ) : ℂ) * (-1 : ℂ) ^ (k - 1) := by
        have hIco : Finset.Ico (1 + 1) (r + 2 + 1) = (Finset.Icc 1 (r + 1)).map
            ⟨Nat.succ, Nat.succ_injective⟩ := by
          ext x; simp only [Finset.mem_Ico, Finset.mem_map, Finset.mem_Icc,
            Function.Embedding.coeFn_mk]
          constructor
          · intro hx; exact ⟨x - 1, ⟨by omega, by omega⟩, by omega⟩
          · rintro ⟨y, hy, rfl⟩; omega
        rw [show Finset.Icc 1 (r + 2) = Finset.Ico 1 (r + 2 + 1) from rfl,
          Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < r + 2 + 1), hIco, Finset.sum_map]
        simp only [Nat.sub_self, pow_zero, mul_one, Function.Embedding.coeFn_mk,
          show r + 2 - 1 = r + 1 by omega]
        rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
        congr 1
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_Icc] at hk
        rw [show r + 2 - (k + 1) = r + 1 - k by omega, show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]
        ring
      rw [hsplit, ih (by omega) (by omega)]
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [Nat.choose_succ_succ b' r, Nat.cast_add]
      ring

/-- Local functional equation `(1 + t)^b * G_series b t = 2 * t^b * G_series b (t / 2) + t * (1 + t)^(b - 1)`
for `‖t‖ < 1 / (2 * (2^b + 3))`. -/
lemma G_series_func_eq {b : ℕ} (hb : 1 ≤ b) {t : ℂ}
    (ht : ‖t‖ < 1 / (2 * ((2 ^ b + 3 : ℕ) : ℝ))) :
    (1 + t) ^ b * G_series b t = 2 * t ^ b * G_series b (t / 2) + t * (1 + t) ^ (b - 1) := by
  let R : ℝ := ((2 ^ b + 3 : ℕ) : ℝ)
  have hRpos : 0 < R := by dsimp only [R]; positivity
  have hRt : R * ‖t‖ < 1 / 2 := by
    have h1 : ‖t‖ * (2 * R) < 1 := (lt_div_iff₀ (by positivity)).mp ht
    linarith
  have hsum_G : Summable (fun n : ℕ => frPoissonCoeff b n * t ^ n) := by
    refine Summable.of_norm_bounded (g := fun n => (R * ‖t‖) ^ n)
      (summable_geometric_of_lt_one (by positivity) (by linarith)) fun n => ?_
    rw [norm_mul, norm_pow, mul_pow]
    exact mul_le_mul_of_nonneg_right (norm_frPoissonCoeff_le hb n) (pow_nonneg (norm_nonneg _) n)
  have hsum_G2 : Summable (fun n : ℕ => frPoissonCoeff b n * (t / 2) ^ n) := by
    refine Summable.of_norm_bounded (g := fun n => (R * ‖t‖) ^ n)
      (summable_geometric_of_lt_one (by positivity) (by linarith)) fun n => ?_
    rw [norm_mul, norm_pow, norm_div, Complex.norm_ofNat, mul_pow]
    exact mul_le_mul (norm_frPoissonCoeff_le hb n)
      (pow_le_pow_left₀ (by positivity) (div_le_self (norm_nonneg _) (by norm_num)) n)
      (by positivity) (by positivity)
  have hlhs_expand : (1 + t) ^ b * G_series b t =
      ∑' N : ℕ, (∑ j ∈ Finset.range (b + 1),
        if j ≤ N then ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (N - j) else 0) * t ^ N := by
    rw [add_comm 1 t, add_pow, Finset.sum_mul]
    simp only [one_pow, mul_one]
    have hshift : ∀ j ∈ Finset.range (b + 1),
        t ^ j * ((b.choose j : ℕ) : ℂ) * G_series b t =
          ∑' N : ℕ, (if j ≤ N then ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (N - j) else 0) * t ^ N := by
      intro j _
      unfold G_series
      rw [← tsum_mul_left]
      have hsum_j : Summable (fun N : ℕ =>
          (if j ≤ N then ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (N - j) else 0) * t ^ N) := by
        rw [← summable_nat_add_iff j]
        refine (hsum_G.mul_left (t ^ j * ((b.choose j : ℕ) : ℂ))).congr fun n => ?_
        simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, pow_add]
        ring
      rw [← hsum_j.sum_add_tsum_nat_add j]
      have hzero : ∑ N ∈ Finset.range j,
          (if j ≤ N then ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (N - j) else 0) * t ^ N = 0 :=
        Finset.sum_eq_zero fun N hN => by
          have : ¬ (j ≤ N) := by rw [Finset.mem_range] at hN; omega
          simp [this]
      rw [hzero, zero_add]
      refine tsum_congr fun n => ?_
      simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, pow_add]
      ring
    rw [Finset.sum_congr rfl hshift]
    have hsum_all : ∀ j ∈ Finset.range (b + 1),
        Summable (fun N : ℕ => (if j ≤ N then ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (N - j) else 0) * t ^ N) := by
      intro j _
      rw [← summable_nat_add_iff j]
      refine (hsum_G.mul_left (t ^ j * ((b.choose j : ℕ) : ℂ))).congr fun n => ?_
      simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, pow_add]
      ring
    rw [← Summable.tsum_finsetSum hsum_all]
    refine tsum_congr fun N => ?_
    rw [Finset.sum_mul]
  -- Now expand RHS as a single power series in `t` and compare coefficients!
  have hrhs1 : 2 * t ^ b * G_series b (t / 2) =
      ∑' N : ℕ, (if b ≤ N then (2 : ℂ) ^ (1 - ((N - b : ℕ) : ℤ)) * frPoissonCoeff b (N - b) else 0) * t ^ N := by
    unfold G_series
    rw [← tsum_mul_left]
    have hsum_r : Summable (fun N : ℕ =>
        (if b ≤ N then (2 : ℂ) ^ (1 - ((N - b : ℕ) : ℤ)) * frPoissonCoeff b (N - b) else 0) * t ^ N) := by
      rw [← summable_nat_add_iff b]
      refine (hsum_G2.mul_left (2 * t ^ b)).congr fun n => ?_
      simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, pow_add, div_pow,
        zpow_sub₀ (by norm_num : (2 : ℂ) ≠ 0), zpow_one, zpow_natCast]
      ring
    rw [← hsum_r.sum_add_tsum_nat_add b]
    have hzero : ∑ N ∈ Finset.range b,
        (if b ≤ N then (2 : ℂ) ^ (1 - ((N - b : ℕ) : ℤ)) * frPoissonCoeff b (N - b) else 0) * t ^ N = 0 :=
      Finset.sum_eq_zero fun N hN => by
        have : ¬ (b ≤ N) := by rw [Finset.mem_range] at hN; omega
        simp [this]
    rw [hzero, zero_add]
    refine tsum_congr fun n => ?_
    simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, pow_add, div_pow,
      zpow_sub₀ (by norm_num : (2 : ℂ) ≠ 0), zpow_one, zpow_natCast]
    ring
  have hrhs2 : t * (1 + t) ^ (b - 1) =
      ∑' N : ℕ, (if 1 ≤ N ∧ N ≤ b then (((b - 1).choose (N - 1) : ℕ) : ℂ) else 0) * t ^ N := by
    rw [tsum_eq_sum (s := Finset.Icc 1 b) (fun N hN => by
      simp only [Finset.mem_Icc] at hN; simp [hN])]
    rw [add_comm 1 t, add_pow, Finset.mul_sum]
    simp only [one_pow, mul_one]
    have hbij : Finset.Icc 1 b = (Finset.range b).map ⟨Nat.succ, Nat.succ_injective⟩ := by
      ext N; simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
      constructor
      · intro h; exact ⟨N - 1, by omega, by omega⟩
      · rintro ⟨k, hk, rfl⟩; omega
    rw [hbij, Finset.sum_map, show b - 1 + 1 = b by omega]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    have h1k : 1 ≤ k.succ ∧ k.succ ≤ b := ⟨by omega, by omega⟩
    simp only [Function.Embedding.coeFn_mk, h1k, and_self, ↓reduceIte, Nat.succ_sub_one, pow_succ']
    ring
  have hsum_r1 : Summable (fun N : ℕ =>
      (if b ≤ N then (2 : ℂ) ^ (1 - ((N - b : ℕ) : ℤ)) * frPoissonCoeff b (N - b) else 0) * t ^ N) := by
    rw [← summable_nat_add_iff b]
    refine (hsum_G2.mul_left (2 * t ^ b)).congr fun n => ?_
    simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, pow_add, div_pow,
      zpow_sub₀ (by norm_num : (2 : ℂ) ≠ 0), zpow_one, zpow_natCast]
    ring
  have hsum_r2 : Summable (fun N : ℕ =>
      (if 1 ≤ N ∧ N ≤ b then (((b - 1).choose (N - 1) : ℕ) : ℂ) else 0) * t ^ N) :=
    summable_of_ne_finset_zero (s := Finset.Icc 1 b) fun N hN => by
      simp only [Finset.mem_Icc] at hN; simp [hN]
  rw [hlhs_expand, hrhs1, hrhs2, ← hsum_r1.tsum_add hsum_r2]
  refine tsum_congr fun N => ?_
  rw [← add_mul]
  congr 1
  by_cases hNb : b ≤ N
  · obtain ⟨m, rfl⟩ : ∃ m, N = m + b := ⟨N - b, by omega⟩
    have hcoeff_lhs : (∑ j ∈ Finset.range (b + 1),
        if j ≤ m + b then ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (m + b - j) else 0) =
        ∑ j ∈ Finset.range (b + 1), ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (m + j) := by
      have hdrop : (∑ j ∈ Finset.range (b + 1),
          if j ≤ m + b then ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (m + b - j) else 0) =
          ∑ j ∈ Finset.range (b + 1), ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (m + b - j) :=
        Finset.sum_congr rfl fun j hj => by
          rw [Finset.mem_range] at hj; simp [show j ≤ m + b by omega]
      rw [hdrop, ← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      simp only [Nat.succ_sub_one]
      rw [Nat.choose_symm (by omega : j ≤ b), show m + b - (b - j) = m + j by omega]
    rw [hcoeff_lhs, frPoissonCoeff_sum_choose hb m]
    simp only [show b ≤ m + b by omega, ↓reduceIte, Nat.add_sub_cancel]
    by_cases hm : m = 0
    · subst hm; simp [hb]
    · simp [hm]
  · push Not at hNb
    simp only [show ¬ (b ≤ N) by omega, ↓reduceIte, zero_add]
    by_cases hN0 : N = 0
    · subst hN0; simp [frPoissonCoeff_zero]
    · have hcond : 1 ≤ N ∧ N ≤ b := ⟨by omega, by omega⟩
      simp only [hcond, and_self, ↓reduceIte]
      rw [← sum_choose_alt_eq (by omega) hNb]
      -- Reindex `j ∈ range (b + 1)` with `j ≤ N` to `k = N - j ∈ Icc 1 N` (noting `k = 0` has `c_0 = 0`)!
      have hfilt : (∑ j ∈ Finset.range (b + 1),
          if j ≤ N then ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (N - j) else 0) =
          ∑ j ∈ Finset.range N, ((b.choose j : ℕ) : ℂ) * frPoissonCoeff b (N - j) := by
        rw [← Finset.sum_filter]
        have hsub : (Finset.range (b + 1)).filter (· ≤ N) = Finset.range (N + 1) := by
          ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
        rw [hsub, Finset.sum_range_succ, Nat.sub_self, frPoissonCoeff_zero, mul_zero, add_zero]
      rw [hfilt]
      refine Finset.sum_bij (fun j _ => N - j) ?_ ?_ ?_ ?_
      · intro j hj; rw [Finset.mem_range] at hj; rw [Finset.mem_Icc]; omega
      · intro j₁ hj₁ j₂ hj₂ h; rw [Finset.mem_range] at hj₁ hj₂; omega
      · intro k hk; rw [Finset.mem_Icc] at hk; exact ⟨N - k, Finset.mem_range.mpr (by omega), by omega⟩
      · intro j hj
        rw [Finset.mem_range] at hj
        rw [show N - (N - j) = j by omega, frPoissonCoeff_lt (by omega) (by omega)]

/-- Exact identity `G_series b t = G_mero b t` on the disk `‖t‖ < 1 / (2 * (2^b + 3))`. -/
theorem G_series_eq_G_mero {b : ℕ} (hb : 1 ≤ b) {t : ℂ}
    (ht : ‖t‖ < 1 / (2 * ((2 ^ b + 3 : ℕ) : ℝ))) :
    G_series b t = G_mero b t := by
  let R : ℝ := ((2 ^ b + 3 : ℕ) : ℝ)
  have hR4 : (4 : ℝ) ≤ R := by
    dsimp only [R]; exact_mod_cast (show 4 ≤ 2 ^ b + 3 by
      have : 1 ≤ 2 ^ b := Nat.one_le_pow b 2 (by norm_num); omega)
  let r₀ : ℝ := 1 / (2 * R)
  have hr₀_le : r₀ ≤ 1 / 8 := by
    dsimp only [r₀]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hno_pole : ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → ∀ j : ℕ, 1 + z / (2 : ℂ) ^ j ≠ 0 := by
    intro z hz j h0
    have hnorm : ‖z / (2 : ℂ) ^ j‖ = 1 := by
      have : z / (2 : ℂ) ^ j = -1 := by linear_combination h0
      rw [this, norm_neg, norm_one]
    have hle : ‖z / (2 : ℂ) ^ j‖ ≤ 1 / 2 := by
      rw [norm_div, norm_pow, Complex.norm_ofNat]
      exact (div_le_self (norm_nonneg _) (one_le_pow₀ (by norm_num))).trans hz
    linarith
  have hD_step : ∀ z : ℂ, ‖z‖ < r₀ →
      G_series b z - G_mero b z = 2 * (z / (1 + z)) ^ b * (G_series b (z / 2) - G_mero b (z / 2)) := by
    intro z hz
    have hz_half : ‖z‖ ≤ 1 / 2 := le_trans hz.le (hr₀_le.trans (by norm_num))
    have h1z : 1 + z ≠ 0 := by simpa using hno_pole z hz_half 0
    have h1zb : (1 + z) ^ b ≠ 0 := pow_ne_zero b h1z
    have hser := G_series_func_eq hb hz
    have hmero := G_mero_func_eq hb (hno_pole z hz_half)
    have hser' : G_series b z = z / (1 + z) + 2 * (z / (1 + z)) ^ b * G_series b (z / 2) := by
      rw [div_pow]
      have hpow : (1 + z) ^ b = (1 + z) * (1 + z) ^ (b - 1) := by
        rw [← pow_succ', show b - 1 + 1 = b by omega]
      apply mul_left_cancel₀ h1zb
      rw [hser]
      field_simp [h1zb, h1z]
      rw [hpow]; ring
    linear_combination hser' - hmero
  -- Bound `‖G_series b z - G_mero b z‖ ≤ M_bd` uniformly on `‖z‖ ≤ ‖t‖ < r₀`:
  have hC_ser : ∀ z : ℂ, ‖z‖ ≤ ‖t‖ → ‖G_series b z‖ ≤ 2 := by
    intro z hz
    have hRt : R * ‖z‖ ≤ 1 / 2 := by
      have h1 : ‖t‖ * (2 * R) < 1 := (lt_div_iff₀ (by positivity)).mp ht
      nlinarith
    have hsum_bd : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
      summable_geometric_of_lt_one (by positivity) (by norm_num)
    have hsum_z : Summable (fun n : ℕ => ‖frPoissonCoeff b n * z ^ n‖) := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hsum_bd
      rw [norm_mul, norm_pow]
      calc ‖frPoissonCoeff b n‖ * ‖z‖ ^ n ≤ R ^ n * ‖z‖ ^ n :=
            mul_le_mul_of_nonneg_right (norm_frPoissonCoeff_le hb n) (pow_nonneg (norm_nonneg _) n)
        _ = (R * ‖z‖) ^ n := (mul_pow _ _ _).symm
        _ ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ (by positivity) hRt n
    calc ‖G_series b z‖ ≤ ∑' n : ℕ, ‖frPoissonCoeff b n * z ^ n‖ := norm_tsum_le_tsum_norm hsum_z
      _ ≤ ∑' n : ℕ, (1 / 2 : ℝ) ^ n := hsum_z.tsum_le_tsum (fun n => by
          rw [norm_mul, norm_pow]
          calc ‖frPoissonCoeff b n‖ * ‖z‖ ^ n ≤ R ^ n * ‖z‖ ^ n :=
                mul_le_mul_of_nonneg_right (norm_frPoissonCoeff_le hb n) (pow_nonneg (norm_nonneg _) n)
            _ = (R * ‖z‖) ^ n := (mul_pow _ _ _).symm
            _ ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ (by positivity) hRt n) hsum_bd
      _ = 2 := by rw [tsum_geometric_of_lt_one (by positivity) (by norm_num)]; norm_num
  obtain ⟨C_m, hCm0, hCm⟩ := norm_G_meroTerm_le_uniform hb (R := 1) (δ := 1 / 2) le_rfl (by norm_num)
  have hC_mero : ∀ z : ℂ, ‖z‖ ≤ ‖t‖ → ‖G_mero b z‖ ≤ 2 * C_m := by
    intro z hz
    have hz_half : ‖z‖ ≤ 1 / 2 := le_trans hz (le_trans ht.le (hr₀_le.trans (by norm_num)))
    have hz1 : ‖z‖ ≤ 1 := hz_half.trans (by norm_num)
    have hδz : ∀ j : ℕ, (1 / 2 : ℝ) ≤ ‖1 + z / (2 : ℂ) ^ j‖ := fun j => by
      have hle : ‖z / (2 : ℂ) ^ j‖ ≤ 1 / 2 := by
        rw [norm_div, norm_pow, Complex.norm_ofNat]
        exact (div_le_self (norm_nonneg _) (one_le_pow₀ (by norm_num))).trans hz_half
      have htri := norm_sub_norm_le (1 : ℂ) (-(z / (2 : ℂ) ^ j))
      simp only [sub_neg_eq_add, norm_one, norm_neg] at htri
      linarith
    have hsum_bd : Summable (fun k : ℕ => C_m * (1 / 2 : ℝ) ^ k) :=
      (summable_geometric_of_lt_one (by positivity) (by norm_num)).mul_left C_m
    have hsum_z : Summable (fun k : ℕ => ‖G_meroTerm b k z‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hCm z hz1 hδz) hsum_bd
    calc ‖G_mero b z‖ ≤ ∑' k : ℕ, ‖G_meroTerm b k z‖ := norm_tsum_le_tsum_norm hsum_z
      _ ≤ ∑' k : ℕ, C_m * (1 / 2 : ℝ) ^ k := hsum_z.tsum_le_tsum (hCm z hz1 hδz) hsum_bd
      _ = 2 * C_m := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (by norm_num)]; ring
  -- Contraction factor `‖2 * (z / (1 + z))^b‖ ≤ 2 / 7` for `‖z‖ ≤ 1 / 8`:
  have hfac_le : ∀ z : ℂ, ‖z‖ ≤ 1 / 8 → ‖2 * (z / (1 + z)) ^ b‖ ≤ 2 / 7 := by
    intro z hz
    have hden : (7 / 8 : ℝ) ≤ ‖1 + z‖ := by
      have htri := norm_sub_norm_le (1 : ℂ) (-z)
      simp only [sub_neg_eq_add, norm_one, norm_neg] at htri
      linarith
    have hq : ‖z / (1 + z)‖ ≤ 1 / 7 := by
      rw [norm_div, div_le_iff₀ (by linarith)]
      linarith
    rw [norm_mul, Complex.norm_ofNat, norm_pow]
    calc 2 * ‖z / (1 + z)‖ ^ b ≤ 2 * (1 / 7 : ℝ) ^ b :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hq b) (by norm_num)
      _ ≤ 2 * (1 / 7 : ℝ) ^ 1 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by positivity) (by norm_num) hb) (by norm_num)
      _ = 2 / 7 := by norm_num
  -- By induction on `N`, `‖G_series b t - G_mero b t‖ ≤ (2 / 7)^N * (2 + 2 * C_m)`!
  have hiter : ∀ N : ℕ, ‖G_series b t - G_mero b t‖ ≤ (2 / 7 : ℝ) ^ N * (2 + 2 * C_m) := by
    intro N
    have hgen : ∀ (n : ℕ) (z : ℂ), ‖z‖ ≤ ‖t‖ →
        ‖G_series b z - G_mero b z‖ ≤ (2 / 7 : ℝ) ^ n * (2 + 2 * C_m) := by
      intro n
      induction n with
      | zero =>
        intro z hz
        simp only [pow_zero, one_mul]
        exact (norm_sub_le _ _).trans (add_le_add (hC_ser z hz) (hC_mero z hz))
      | succ n ih =>
        intro z hz
        have hz_r0 : ‖z‖ < r₀ := lt_of_le_of_lt hz ht
        have hz_18 : ‖z‖ ≤ 1 / 8 := le_trans hz_r0.le hr₀_le
        rw [hD_step z hz_r0, norm_mul, pow_succ', mul_assoc]
        have hz2 : ‖z / 2‖ ≤ ‖t‖ := by
          rw [norm_div, Complex.norm_ofNat]; linarith [norm_nonneg z]
        exact mul_le_mul (hfac_le z hz_18) (ih (z / 2) hz2) (norm_nonneg _) (by positivity)
    exact hgen N t le_rfl
  have hzero : ‖G_series b t - G_mero b t‖ = 0 := by
    refine le_antisymm ?_ (norm_nonneg _)
    have htend : Tendsto (fun N : ℕ => (2 / 7 : ℝ) ^ N * (2 + 2 * C_m)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num : (2 / 7 : ℝ) < 1)).mul_const (2 + 2 * C_m)
    exact ge_of_tendsto' htend hiter
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- Exact Laurent expansion of `L_b b ξ = ξ⁻¹ * G_mero b ξ⁻¹ = ∑' n, c_{b, n} * ξ^{-(n + 1)}`
for `‖ξ‖ > 2 * (2^b + 3)`. -/
lemma L_b_eq_tsum {b : ℕ} (hb : 1 ≤ b) {ξ : ℂ} (hξ : 2 * ((2 ^ b + 3 : ℕ) : ℝ) < ‖ξ‖) :
    L_b b ξ = ∑' n : ℕ, frPoissonCoeff b n * (ξ⁻¹) ^ (n + 1) := by
  have hξ_pos : 0 < ‖ξ‖ := lt_trans (by positivity) hξ
  have hinv : ‖ξ⁻¹‖ < 1 / (2 * ((2 ^ b + 3 : ℕ) : ℝ)) := by
    rw [norm_inv, one_div]
    exact inv_strictAnti₀ (by positivity) hξ
  unfold L_b
  rw [← G_series_eq_G_mero hb hinv]
  unfold G_series
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [pow_succ]; ring

/-! ### Holomorphicity, Double Periodicity, Decomposition, and Order-`b` Pole of `Ψ_b` -/

/-- `T_b b ξ` is holomorphic on `Metric.ball 0 2` with `T_b b 0 = 0`. -/
lemma T_b_zero (b : ℕ) : T_b b 0 = 0 := by
  unfold T_b psiTerm; simp

private lemma norm_Pi_1_ge_on_ball {w : ℂ} (hw : ‖w‖ ≤ 1) :
    P_inf ≤ ‖Pi_1 w‖ := by
  have hprod := Pi_1_hasProd w
  have htend := (continuous_norm.tendsto _).comp hprod
  have hfn : (norm ∘ fun s : Finset ℕ => ∏ j ∈ s, (1 + (2 : ℂ) ^ (-(j + 1 : ℤ)) * w)) =
      fun s : Finset ℕ => ∏ j ∈ s, ‖1 + (2 : ℂ) ^ (-(j + 1 : ℤ)) * w‖ := by
    funext s; simp [norm_prod]
  rw [hfn] at htend
  refine ge_of_tendsto htend (Filter.Eventually.of_forall fun s => ?_)
  have hle1 : ∀ j : ℕ, 1 - (2 : ℝ) ^ (-(j + 1 : ℤ)) ≤ ‖1 + (2 : ℂ) ^ (-(j + 1 : ℤ)) * w‖ := fun j => by
    have htri := norm_sub_norm_le (1 : ℂ) (-((2 : ℂ) ^ (-(j + 1 : ℤ)) * w))
    simp only [sub_neg_eq_add, norm_one, norm_neg, norm_mul, norm_zpow, Complex.norm_ofNat] at htri
    have hmul : (2 : ℝ) ^ (-(j + 1 : ℤ)) * ‖w‖ ≤ (2 : ℝ) ^ (-(j + 1 : ℤ)) :=
      mul_le_of_le_one_right (by positivity) hw
    linarith
  have hfin_ge : P_inf ≤ ∏ j ∈ s, (1 - (2 : ℝ) ^ (-(j + 1 : ℤ))) := by
    rw [P_inf_eq_exp_tsum]
    have hexp_s : ∏ j ∈ s, (1 - (2 : ℝ) ^ (-(j + 1 : ℤ))) =
        Real.exp (∑ j ∈ s, Real.log (1 - (2 : ℝ) ^ (-(j + 1 : ℤ)))) := by
      rw [Real.exp_sum]
      refine Finset.prod_congr rfl fun j _ => (Real.exp_log (one_sub_two_zpow_pos j)).symm
    rw [hexp_s]
    apply Real.exp_le_exp.mpr
    have hle_neg : ∑ j ∈ s, (-Real.log (1 - (2 : ℝ) ^ (-(j + 1 : ℤ)))) ≤
        ∑' j : ℕ, (-Real.log (1 - (2 : ℝ) ^ (-(j + 1 : ℤ)))) :=
      summable_log_P_inf.neg.sum_le_tsum s fun j _ => by
        rw [two_zpow_neg_succ_real]
        have hp : (1 / 2 : ℝ) ^ (j + 1) ≤ 1 / 2 := by
          calc (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
                pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
            _ = 1 / 2 := pow_one _
        linarith [(log_one_sub_bounds (by positivity) hp).2]
    rw [Finset.sum_neg_distrib, tsum_neg] at hle_neg
    linarith
  exact hfin_ge.trans (real_finset_prod_le_prod (fun j _ => (one_sub_two_zpow_pos j).le) fun j _ => hle1 j)

lemma norm_psiTerm_le_of_norm_le {b : ℕ} {w : ℂ} (hw : ‖w‖ ≤ 3 / 4) :
    ‖psiTerm b w‖ ≤ (4 / P_inf ^ b) * ‖w‖ := by
  unfold psiTerm
  rw [norm_div, norm_mul]
  have h1w : (1 / 4 : ℝ) ≤ ‖1 + w‖ := by
    have htri := norm_sub_norm_le (1 : ℂ) (-w)
    simp only [sub_neg_eq_add, norm_one, norm_neg] at htri
    linarith
  have hPi : P_inf ^ b ≤ ‖Pi_b b w‖ := by
    rw [Pi_b, norm_pow]
    exact pow_le_pow_left₀ P_inf_pos.le (norm_Pi_1_ge_on_ball (hw.trans (by norm_num))) b
  have hPpos : 0 < P_inf ^ b := pow_pos P_inf_pos b
  calc ‖w‖ / (‖1 + w‖ * ‖Pi_b b w‖)
      ≤ ‖w‖ / ((1 / 4 : ℝ) * P_inf ^ b) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
          (mul_le_mul h1w hPi hPpos.le (norm_nonneg _))
    _ = (4 / P_inf ^ b) * ‖w‖ := by field_simp [hPpos.ne']

lemma summable_T_b_term (b : ℕ) {ξ : ℂ} (hξ : ‖ξ‖ < 2) :
    Summable (fun k : ℕ => psiTerm b ((2 : ℂ) ^ (-(k + 1 : ℤ)) * ξ)) := by
  rw [← summable_nat_add_iff 1]
  have hgeom : Summable (fun k : ℕ => (4 / P_inf ^ b) * ‖ξ‖ * (1 / 2 : ℝ) ^ (k + 2)) := by
    have h := (summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
      ((4 / P_inf ^ b) * ‖ξ‖ * (1 / 2 : ℝ) ^ 2)
    refine h.congr fun k => ?_
    rw [pow_add]; ring
  refine Summable.of_norm_bounded hgeom fun k => ?_
  have hw : ‖(2 : ℂ) ^ (-((k + 1 : ℕ) + 1 : ℤ)) * ξ‖ ≤ 3 / 4 := by
    rw [norm_mul, norm_zpow, Complex.norm_ofNat, two_zpow_neg_succ_real]
    have h2 : (1 / 2 : ℝ) ^ (k + 1 + 1) ≤ 1 / 4 := by
      calc (1 / 2 : ℝ) ^ (k + 1 + 1) ≤ (1 / 2 : ℝ) ^ 2 :=
            pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
        _ = 1 / 4 := by norm_num
    nlinarith [norm_nonneg ξ]
  refine (norm_psiTerm_le_of_norm_le hw).trans_eq ?_
  rw [norm_mul, norm_zpow, Complex.norm_ofNat, two_zpow_neg_succ_real]
  ring

lemma T_b_differentiableOn (b : ℕ) :
    DifferentiableOn ℂ (T_b b) (Metric.ball 0 (3 / 2 : ℝ)) := by
  have hgeom : Summable (fun k : ℕ => (4 / P_inf ^ b) * (3 / 2 : ℝ) * (1 / 2 : ℝ) ^ (k + 1)) := by
    have h := (summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
      ((4 / P_inf ^ b) * (3 / 2 : ℝ) * (1 / 2 : ℝ))
    refine h.congr fun k => ?_
    rw [pow_succ']; ring
  have hunif : TendstoUniformlyOn
      (fun N ξ => ∑ k ∈ Finset.range N, psiTerm b ((2 : ℂ) ^ (-(k + 1 : ℤ)) * ξ))
      (T_b b) atTop (Metric.ball 0 (3 / 2 : ℝ)) := by
    refine tendstoUniformlyOn_tsum_nat hgeom ?_
    intro k ξ hξ
    have hξlt : ‖ξ‖ < 3 / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hξ
    have hw : ‖(2 : ℂ) ^ (-(k + 1 : ℤ)) * ξ‖ ≤ 3 / 4 := by
      rw [norm_mul, norm_zpow, Complex.norm_ofNat, two_zpow_neg_succ_real]
      have h2 : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 / 2 := by
        calc (1 / 2 : ℝ) ^ (k + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
              pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
          _ = 1 / 2 := pow_one _
      nlinarith [norm_nonneg ξ]
    refine (norm_psiTerm_le_of_norm_le hw).trans ?_
    rw [norm_mul, norm_zpow, Complex.norm_ofNat, two_zpow_neg_succ_real]
    have hPpos : 0 < P_inf ^ b := pow_pos P_inf_pos b
    calc (4 / P_inf ^ b) * ((1 / 2 : ℝ) ^ (k + 1) * ‖ξ‖)
        ≤ (4 / P_inf ^ b) * ((1 / 2 : ℝ) ^ (k + 1) * (3 / 2 : ℝ)) := by gcongr
      _ = (4 / P_inf ^ b) * (3 / 2 : ℝ) * (1 / 2 : ℝ) ^ (k + 1) := by ring
  refine hunif.tendstoLocallyUniformlyOn.differentiableOn (Filter.Eventually.of_forall fun N => ?_) Metric.isOpen_ball
  refine DifferentiableOn.fun_sum fun k _ => ?_
  intro ξ hξ
  have hξlt : ‖ξ‖ < 3 / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hξ
  have hw : ‖(2 : ℂ) ^ (-(k + 1 : ℤ)) * ξ‖ < 3 / 4 := by
    rw [norm_mul, norm_zpow, Complex.norm_ofNat, two_zpow_neg_succ_real]
    have h2 : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 / 2 := by
      calc (1 / 2 : ℝ) ^ (k + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
            pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
        _ = 1 / 2 := pow_one _
    have h2pos : 0 < (1 / 2 : ℝ) ^ (k + 1) := by positivity
    nlinarith [norm_nonneg ξ]
  have h1ne : 1 + (2 : ℂ) ^ (-(k + 1 : ℤ)) * ξ ≠ 0 := by
    intro h0
    have : ‖(2 : ℂ) ^ (-(k + 1 : ℤ)) * ξ‖ = 1 := by
      have h1 : (2 : ℂ) ^ (-(k + 1 : ℤ)) * ξ = -1 := by linear_combination h0
      rw [h1, norm_neg, norm_one]
    linarith
  have hPine : Pi_b b ((2 : ℂ) ^ (-(k + 1 : ℤ)) * ξ) ≠ 0 := by
    refine Pi_b_ne_zero b fun j h0 => ?_
    have : ‖(2 : ℂ) ^ (-(j + 1 : ℤ)) * ((2 : ℂ) ^ (-(k + 1 : ℤ)) * ξ)‖ = 1 := by
      have h1 : (2 : ℂ) ^ (-(j + 1 : ℤ)) * ((2 : ℂ) ^ (-(k + 1 : ℤ)) * ξ) = -1 := by linear_combination h0
      rw [h1, norm_neg, norm_one]
    rw [norm_mul, norm_zpow, Complex.norm_ofNat, two_zpow_neg_succ_real] at this
    have h2 : (1 / 2 : ℝ) ^ (j + 1) ≤ 1 / 2 := by
      calc (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
            pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
        _ = 1 / 2 := pow_one _
    nlinarith [norm_nonneg ((2 : ℂ) ^ (-(k + 1 : ℤ)) * ξ)]
  unfold psiTerm
  refine (DifferentiableAt.div (by fun_prop)
    ((by fun_prop : DifferentiableAt ℂ (fun z => 1 + (2 : ℂ) ^ (-(k + 1 : ℤ)) * z) ξ).mul
      ((Pi_b_differentiable b _).comp ξ (by fun_prop)))
    (mul_ne_zero h1ne hPine)).differentiableWithinAt

/-- Non-pole domain for `w ↦ ∑_{m ∈ ℤ} psiTerm b (2^m w)`: `w ≠ 0` and `∀ m : ℤ, 1 + 2^m w ≠ 0`. -/
@[expose] def PsiWDomain : Set ℂ :=
  {w : ℂ | w ≠ 0 ∧ ∀ m : ℤ, 1 + (2 : ℂ) ^ m * w ≠ 0}

/-- Non-pole domain for `Ψ_b(u)`: `∀ m : ℤ, 1 + 2^m * exp(-log 2 * u) ≠ 0`. -/
@[expose] def PsiDomain : Set ℂ :=
  {u : ℂ | ∀ m : ℤ, 1 + (2 : ℂ) ^ m * Complex.exp (-((Real.log 2 : ℝ) : ℂ) * u) ≠ 0}

lemma PsiWDomain_Pi_b_ne_zero {b : ℕ} {w : ℂ} (hw : w ∈ PsiWDomain) :
    Pi_b b w ≠ 0 :=
  Pi_b_ne_zero b fun j => hw.2 (-(j + 1 : ℤ))

/-- Helper: splitting `∑' m : ℤ, f m` into `∑' k : ℕ, f k + ∑' k : ℕ, f (-(k + 1))`. -/
private lemma tsum_int_eq_nat_add_negSucc {f : ℤ → ℂ} (hf : Summable f) :
    ∑' m : ℤ, f m = (∑' k : ℕ, f (k : ℤ)) + ∑' k : ℕ, f (-(k + 1 : ℤ)) := by
  let e : ℕ ⊕ ℕ ≃ ℤ :=
    { toFun := Sum.elim (fun k : ℕ => (k : ℤ)) (fun k : ℕ => -(k + 1 : ℤ))
      invFun := fun m => if 0 ≤ m then Sum.inl m.toNat else Sum.inr (-m - 1).toNat
      left_inv := fun x => by
        cases x with
        | inl k => simp
        | inr k =>
          change (if 0 ≤ -(k + 1 : ℤ) then Sum.inl (-(k + 1 : ℤ)).toNat
                  else Sum.inr (-(-(k + 1 : ℤ)) - 1).toNat) = Sum.inr k
          simp only [show ¬ (0 ≤ -(k + 1 : ℤ)) by omega, ↓reduceIte]
          congr 1; omega
      right_inv := fun m => by
        by_cases hm : 0 ≤ m
        · simp only [hm, ↓reduceIte, Sum.elim_inl]; omega
        · simp only [hm, ↓reduceIte, Sum.elim_inr]; omega }
  have h1 : Summable (fun k : ℕ => f (k : ℤ)) := hf.comp_injective Int.ofNat_injective
  have h2 : Summable (fun k : ℕ => f (-(k + 1 : ℤ))) := hf.comp_injective (fun a b h => by omega)
  rw [← e.tsum_eq]
  exact Summable.tsum_sum (f := f ∘ e) h1 h2

/-- Helper: summability of `m ↦ psiTerm b (2^m * w)` on `ℤ` for `w ∈ PsiWDomain`. -/
lemma summable_psiTerm_int {b : ℕ} (hb : 1 ≤ b) {w : ℂ} (hw : w ∈ PsiWDomain) :
    Summable (fun m : ℤ => psiTerm b ((2 : ℂ) ^ m * w)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨?_, ?_⟩
  · -- `m : ℕ`: `Pi_b b w * psiTerm b (2^m w) = w * G_meroTerm b m w⁻¹`!
    have hPi : Pi_b b w ≠ 0 := PsiWDomain_Pi_b_ne_zero hw
    have hno_pole : ∀ j : ℕ, 1 + w⁻¹ / (2 : ℂ) ^ j ≠ 0 := fun j h0 => by
      have h2j : (2 : ℂ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
      have : 1 + (2 : ℂ) ^ (j : ℤ) * w = 0 := by
        rw [zpow_natCast]
        have hmul := congrArg (· * ((2 : ℂ) ^ j * w)) h0
        simp only [zero_mul] at hmul
        linear_combination hmul - (by field_simp [hw.1, h2j]; ring :
          (1 + w⁻¹ / (2 : ℂ) ^ j) * ((2 : ℂ) ^ j * w) - ((2 : ℂ) ^ j * w + 1) = 0)
      exact hw.2 j this
    have hsumG := summable_G_meroTerm hb hno_pole
    refine (hsumG.mul_left (w / Pi_b b w)).congr fun k => ?_
    have heq := xi_mul_G_meroTerm_inv (b := b) k hw.1 hPi
    have hpow : (2 : ℂ) ^ (k : ℤ) = (2 : ℂ) ^ k := zpow_natCast _ _
    rw [hpow]
    field_simp [hPi] at heq ⊢
    linear_combination heq
  · -- `-(m : ℕ)`: for large `m`, `‖2^{-m} w‖ ≤ 3/4` so geometrically summable!
    obtain ⟨K, hK⟩ : ∃ K : ℕ, ‖w‖ ≤ (3 / 4 : ℝ) * (2 : ℝ) ^ K := by
      refine ⟨Nat.ceil (2 * ‖w‖) + 1, ?_⟩
      have h1 : (Nat.ceil (2 * ‖w‖) + 1 : ℝ) < (2 : ℝ) ^ (Nat.ceil (2 * ‖w‖) + 1) := by
        exact_mod_cast Nat.lt_two_pow_self
      linarith [Nat.le_ceil (2 * ‖w‖)]
    rw [← summable_nat_add_iff K]
    refine Summable.of_norm_bounded
      (g := fun m : ℕ => (4 / P_inf ^ b) * (3 / 4 : ℝ) * (1 / 2 : ℝ) ^ m)
      ((summable_geometric_of_lt_one (by positivity) (by norm_num)).mul_left _) fun m => ?_
    have hnorm : ‖(2 : ℂ) ^ (-((m + K : ℕ) : ℤ)) * w‖ ≤ (3 / 4 : ℝ) * (1 / 2 : ℝ) ^ m := by
      rw [norm_mul, norm_zpow, Complex.norm_ofNat, zpow_neg, zpow_natCast, pow_add, one_div, inv_pow]
      have h2K : (2 : ℝ) ^ K ≠ 0 := by positivity
      calc ((2 : ℝ) ^ m * (2 : ℝ) ^ K)⁻¹ * ‖w‖
          ≤ ((2 : ℝ) ^ m * (2 : ℝ) ^ K)⁻¹ * ((3 / 4 : ℝ) * (2 : ℝ) ^ K) :=
            mul_le_mul_of_nonneg_left hK (by positivity)
        _ = (3 / 4 : ℝ) * ((2 : ℝ) ^ m)⁻¹ := by field_simp [h2K]
    have h34 : ‖(2 : ℂ) ^ (-((m + K : ℕ) : ℤ)) * w‖ ≤ 3 / 4 :=
      hnorm.trans (mul_le_of_le_one_right (by positivity)
        (pow_le_one₀ (by positivity) (by norm_num)))
    exact (norm_psiTerm_le_of_norm_le h34).trans (by
      have hPpos : 0 < P_inf ^ b := pow_pos P_inf_pos b
      calc (4 / P_inf ^ b) * ‖(2 : ℂ) ^ (-((m + K : ℕ) : ℤ)) * w‖
          ≤ (4 / P_inf ^ b) * ((3 / 4 : ℝ) * (1 / 2 : ℝ) ^ m) := by gcongr
        _ = (4 / P_inf ^ b) * (3 / 4 : ℝ) * (1 / 2 : ℝ) ^ m := by ring)

/-- Exact telescoping decomposition: for all `ξ ∈ PsiWDomain`,
`ξ * G_mero b ξ⁻¹ = Pi_b b ξ * (Psi_b b (-Complex.log ξ / Real.log 2) - T_b b ξ)`. -/
theorem xi_mul_G_mero_inv_eq {b : ℕ} (hb : 1 ≤ b) {ξ : ℂ} (hξ : ξ ∈ PsiWDomain) :
    ξ * G_mero b ξ⁻¹ =
      Pi_b b ξ * (Psi_b b (-Complex.log ξ / ((Real.log 2 : ℝ) : ℂ)) - T_b b ξ) := by
  have hlog2 : ((Real.log 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  have hexp : Complex.exp (-((Real.log 2 : ℝ) : ℂ) * (-Complex.log ξ / ((Real.log 2 : ℝ) : ℂ))) = ξ := by
    have hsimp : -((Real.log 2 : ℝ) : ℂ) * (-Complex.log ξ / ((Real.log 2 : ℝ) : ℂ)) = Complex.log ξ := by
      field_simp [hlog2]
    rw [hsimp, Complex.exp_log hξ.1]
  unfold Psi_b
  simp_rw [hexp]
  have hsum := summable_psiTerm_int hb hξ
  rw [tsum_int_eq_nat_add_negSucc hsum]
  change ξ * G_mero b ξ⁻¹ = Pi_b b ξ * ((∑' k : ℕ, psiTerm b ((2 : ℂ) ^ (k : ℤ) * ξ)) + T_b b ξ - T_b b ξ)
  rw [add_sub_cancel_right]
  unfold G_mero
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun k => by
    rw [zpow_natCast]
    exact xi_mul_G_meroTerm_inv k hξ.1 (PsiWDomain_Pi_b_ne_zero hξ)

/-- Double periodicity of `Ψ_b`: `Ψ_b(u + 1) = Ψ_b(u)`. -/
lemma Psi_b_add_one (b : ℕ) (u : ℂ) : Psi_b b (u + 1) = Psi_b b u := by
  unfold Psi_b
  have hstep : ∀ m : ℤ,
      (2 : ℂ) ^ m * Complex.exp (-((Real.log 2 : ℝ) : ℂ) * (u + 1)) =
        (2 : ℂ) ^ (m - 1) * Complex.exp (-((Real.log 2 : ℝ) : ℂ) * u) := fun m => by
    have hmul : -((Real.log 2 : ℝ) : ℂ) * (u + 1) =
        -((Real.log 2 : ℝ) : ℂ) * u + (-((Real.log 2 : ℝ) : ℂ)) := by ring
    rw [hmul, Complex.exp_add, Complex.exp_neg, ← Complex.ofReal_exp,
      Real.exp_log (by norm_num : (0 : ℝ) < 2), Complex.ofReal_ofNat,
      zpow_sub_one₀ (by norm_num : (2 : ℂ) ≠ 0)]
    ring
  simp_rw [hstep]
  exact (Equiv.subRight (1 : ℤ)).tsum_eq
    (fun m : ℤ => psiTerm b ((2 : ℂ) ^ m * Complex.exp (-((Real.log 2 : ℝ) : ℂ) * u)))

lemma Psi_b_add_nat (b k : ℕ) (u : ℂ) : Psi_b b (u + (k : ℂ)) = Psi_b b u := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Psi_b_add_one, ih]

/-- Vertical period `τ_fr = 2 π i / log 2`. -/
@[expose] def tauFR : ℂ :=
  ((2 * Real.pi / Real.log 2 : ℝ) : ℂ) * I

/-- Double periodicity of `Ψ_b`: `Ψ_b(u + 2 π i / log 2) = Ψ_b(u)`. -/
lemma Psi_b_add_tau (b : ℕ) (u : ℂ) : Psi_b b (u + tauFR) = Psi_b b u := by
  unfold Psi_b tauFR
  have hlog2 : ((Real.log 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  have hexp : Complex.exp (-((Real.log 2 : ℝ) : ℂ) * (u + ((2 * Real.pi / Real.log 2 : ℝ) : ℂ) * I)) =
      Complex.exp (-((Real.log 2 : ℝ) : ℂ) * u) := by
    have harg : -((Real.log 2 : ℝ) : ℂ) * (u + ((2 * Real.pi / Real.log 2 : ℝ) : ℂ) * I) =
        -((Real.log 2 : ℝ) : ℂ) * u + (-(2 * (Real.pi : ℂ) * I)) := by
      push_cast; field_simp [hlog2]; ring
    rw [harg, Complex.exp_add, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]
  simp_rw [hexp]

/-- `Ψ_b` is holomorphic on `PsiDomain`. -/
lemma Psi_b_differentiableOn {b : ℕ} (hb : 1 ≤ b) :
    DifferentiableOn ℂ (Psi_b b) PsiDomain := by
  intro u₀ hu₀
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖Complex.exp (-((Real.log 2 : ℝ) : ℂ) * (u₀ + (N : ℂ)))‖ < 1 / 2 := by
    let x₀ : ℝ := Real.exp (-Real.log 2 * u₀.re)
    refine ⟨Nat.ceil (2 * x₀) + 2, ?_⟩
    rw [Complex.norm_exp]
    have hre : (-((Real.log 2 : ℝ) : ℂ) * (u₀ + ((Nat.ceil (2 * x₀) + 2 : ℕ) : ℂ))).re =
        -Real.log 2 * u₀.re - Real.log 2 * ((Nat.ceil (2 * x₀) + 2 : ℕ) : ℝ) := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_re, Complex.add_im, Complex.natCast_re, Complex.natCast_im, neg_zero, zero_mul, sub_zero]
      ring
    rw [hre, sub_eq_add_neg, Real.exp_add, show -(Real.log 2 * ((Nat.ceil (2 * x₀) + 2 : ℕ) : ℝ)) =
        (((Nat.ceil (2 * x₀) + 2 : ℕ) : ℝ) * (-Real.log 2)) by ring,
      Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), inv_pow]
    have h1 : (Nat.ceil (2 * x₀) + 2 : ℝ) < (2 : ℝ) ^ (Nat.ceil (2 * x₀) + 2) := by
      exact_mod_cast Nat.lt_two_pow_self
    have h2 : 2 * x₀ ≤ (Nat.ceil (2 * x₀) : ℝ) := Nat.le_ceil _
    have hgt : 2 * x₀ < (2 : ℝ) ^ (Nat.ceil (2 * x₀) + 2) := by linarith
    have hpos : 0 < (2 : ℝ) ^ (Nat.ceil (2 * x₀) + 2) := by positivity
    rw [mul_inv_lt_iff₀ hpos]
    dsimp only [x₀] at hgt ⊢
    linarith
  let g_map : ℂ → ℂ := fun u => Complex.exp (-((Real.log 2 : ℝ) : ℂ) * (u + (N : ℂ)))
  have hg_cont : Continuous g_map := by fun_prop
  have hg_lt : ‖g_map u₀‖ < 1 / 2 := hN
  have hg_mem : g_map u₀ ∈ PsiWDomain := by
    refine ⟨Complex.exp_ne_zero _, fun m => ?_⟩
    have h2N : g_map u₀ = (2 : ℂ) ^ (-(N : ℤ)) * Complex.exp (-((Real.log 2 : ℝ) : ℂ) * u₀) := by
      dsimp only [g_map]
      rw [mul_add, Complex.exp_add, mul_comm (Complex.exp (-((Real.log 2 : ℝ) : ℂ) * u₀))]
      congr 1
      rw [show -((Real.log 2 : ℝ) : ℂ) * (N : ℂ) = (N : ℂ) * (-((Real.log 2 : ℝ) : ℂ)) by ring,
        Complex.exp_nat_mul, Complex.exp_neg, ← Complex.ofReal_exp,
        Real.exp_log (by norm_num : (0 : ℝ) < 2), Complex.ofReal_ofNat, zpow_neg, zpow_natCast, inv_pow]
    rw [h2N, ← mul_assoc, ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)]
    exact hu₀ (m + -(N : ℤ))
  have hinv_mem : (g_map u₀)⁻¹ ∈ {t : ℂ | ∀ j : ℕ, 1 + t / (2 : ℂ) ^ j ≠ 0} := by
    intro j h0
    have h2j : (2 : ℂ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
    have : 1 + (2 : ℂ) ^ (j : ℤ) * g_map u₀ = 0 := by
      rw [zpow_natCast]
      have hmul := congrArg (· * ((2 : ℂ) ^ j * g_map u₀)) h0
      simp only [zero_mul] at hmul
      linear_combination hmul - (by field_simp [hg_mem.1, h2j]; ring :
        (1 + (g_map u₀)⁻¹ / (2 : ℂ) ^ j) * ((2 : ℂ) ^ j * g_map u₀) - ((2 : ℂ) ^ j * g_map u₀ + 1) = 0)
    exact hg_mem.2 j this
  have hopen_G : {t : ℂ | ∀ j : ℕ, 1 + t / (2 : ℂ) ^ j ≠ 0} ∈ 𝓝 (g_map u₀)⁻¹ := by
    let t₀ := (g_map u₀)⁻¹
    let R : ℝ := ‖t₀‖ + 2
    let J₀ : ℕ := Nat.ceil (2 * R) + 1
    have h2J : 2 * R ≤ (2 : ℝ) ^ J₀ := by
      have h1 : (Nat.ceil (2 * R) + 1 : ℝ) < (2 : ℝ) ^ J₀ := by exact_mod_cast Nat.lt_two_pow_self
      linarith [Nat.le_ceil (2 * R)]
    have hne_fin : (Finset.range (J₀ + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
    let m₀ : ℝ := (Finset.range (J₀ + 1)).inf' hne_fin (fun j => ‖1 + t₀ / (2 : ℂ) ^ j‖)
    have hm₀ : 0 < m₀ := by
      dsimp only [m₀]; rw [Finset.lt_inf'_iff]; intro j _; exact norm_pos_iff.mpr (hinv_mem j)
    refine Filter.mem_of_superset (Metric.ball_mem_nhds t₀ (lt_min zero_lt_one (half_pos hm₀))) fun t ht j => ?_
    have hdist : ‖t - t₀‖ < min 1 (m₀ / 2) := by simpa [Metric.mem_ball, dist_eq_norm] using ht
    by_cases hj : j < J₀ + 1
    · have h0 : m₀ ≤ ‖1 + t₀ / (2 : ℂ) ^ j‖ :=
        Finset.inf'_le (f := fun i => ‖1 + t₀ / (2 : ℂ) ^ i‖) (Finset.mem_range.mpr hj)
      have hdiff : ‖(1 + t / (2 : ℂ) ^ j) - (1 + t₀ / (2 : ℂ) ^ j)‖ ≤ ‖t - t₀‖ := by
        rw [show (1 + t / (2 : ℂ) ^ j) - (1 + t₀ / (2 : ℂ) ^ j) = (t - t₀) / (2 : ℂ) ^ j by ring,
          norm_div, norm_pow, Complex.norm_ofNat]
        exact div_le_self (norm_nonneg _) (one_le_pow₀ (by norm_num))
      have htri := norm_sub_norm_le (1 + t₀ / (2 : ℂ) ^ j) (1 + t / (2 : ℂ) ^ j)
      rw [norm_sub_rev] at htri
      have hpos : 0 < ‖1 + t / (2 : ℂ) ^ j‖ := by linarith [min_le_right 1 (m₀ / 2)]
      exact norm_pos_iff.mp hpos
    · have htR : ‖t‖ ≤ R := by
        have htri : ‖t‖ ≤ ‖t - t₀‖ + ‖t₀‖ := by
          calc ‖t‖ = ‖(t - t₀) + t₀‖ := by ring_nf
            _ ≤ ‖t - t₀‖ + ‖t₀‖ := norm_add_le _ _
        linarith [min_le_left 1 (m₀ / 2)]
      have hle : ‖t / (2 : ℂ) ^ j‖ ≤ 1 / 2 := by
        rw [norm_div, norm_pow, Complex.norm_ofNat, div_le_iff₀ (by positivity)]
        have h2j : (2 : ℝ) ^ J₀ ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
      have htri := norm_sub_norm_le (1 : ℂ) (-(t / (2 : ℂ) ^ j))
      simp only [sub_neg_eq_add, norm_one, norm_neg] at htri
      exact norm_pos_iff.mp (by linarith)
  have hnhds1 : {u : ℂ | ‖g_map u‖ < 1} ∈ 𝓝 u₀ :=
    (isOpen_lt (continuous_norm.comp hg_cont) continuous_const).mem_nhds (hg_lt.trans (by norm_num))
  have hnhds2 : (fun u => (g_map u)⁻¹) ⁻¹' {t : ℂ | ∀ j : ℕ, 1 + t / (2 : ℂ) ^ j ≠ 0} ∈ 𝓝 u₀ :=
    ((hg_cont.continuousAt.inv₀ hg_mem.1).preimage_mem_nhds hopen_G)
  have hev_eq : Psi_b b =ᶠ[𝓝 u₀]
      fun u : ℂ => g_map u * G_mero b (g_map u)⁻¹ / Pi_b b (g_map u) + T_b b (g_map u) := by
    filter_upwards [hnhds1, hnhds2] with u hu1 hu2
    have hgu_ne : g_map u ≠ 0 := Complex.exp_ne_zero _
    have hgu_mem : g_map u ∈ PsiWDomain := by
      refine ⟨hgu_ne, fun m => ?_⟩
      cases m with
      | ofNat k =>
        intro h0
        have h2k : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
        have h0' : 1 + (g_map u)⁻¹ / (2 : ℂ) ^ k = 0 := by
          have hmul := congrArg (· / ((2 : ℂ) ^ k * g_map u)) h0
          simp only [Int.ofNat_eq_natCast, zpow_natCast, zero_div] at hmul
          have hident : (1 + (2 : ℂ) ^ k * g_map u) / ((2 : ℂ) ^ k * g_map u) =
              1 + (g_map u)⁻¹ / (2 : ℂ) ^ k := by
            field_simp [hgu_ne, h2k]; ring
          rw [← hident]; exact hmul
        exact hu2 k h0'
      | negSucc k =>
        intro h0
        have hnorm : ‖(2 : ℂ) ^ (Int.negSucc k) * g_map u‖ = 1 := by
          have : (2 : ℂ) ^ (Int.negSucc k) * g_map u = -1 := by linear_combination h0
          rw [this, norm_neg, norm_one]
        rw [norm_mul, norm_zpow, Complex.norm_ofNat, Int.negSucc_eq, two_zpow_neg_succ_real] at hnorm
        have hle1 : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := pow_le_one₀ (by positivity) (by norm_num)
        have hprod_lt : (1 / 2 : ℝ) ^ (k + 1) * ‖g_map u‖ < 1 := by nlinarith [norm_nonneg (g_map u)]
        linarith
    have hdecomp := xi_mul_G_mero_inv_eq hb hgu_mem
    have hPi_ne : Pi_b b (g_map u) ≠ 0 := PsiWDomain_Pi_b_ne_zero hgu_mem
    have hlog2 : ((Real.log 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
    have hPsi_eq : Psi_b b (-Complex.log (g_map u) / ((Real.log 2 : ℝ) : ℂ)) = Psi_b b u := by
      rw [← Psi_b_add_nat b N u]
      unfold Psi_b
      have hexp : Complex.exp (-((Real.log 2 : ℝ) : ℂ) * (-Complex.log (g_map u) / ((Real.log 2 : ℝ) : ℂ))) =
          g_map u := by
        have hsimp : -((Real.log 2 : ℝ) : ℂ) * (-Complex.log (g_map u) / ((Real.log 2 : ℝ) : ℂ)) =
            Complex.log (g_map u) := by field_simp [hlog2]
        rw [hsimp, Complex.exp_log hgu_ne]
      simp_rw [hexp]
      rfl
    rw [hPsi_eq] at hdecomp
    apply mul_left_cancel₀ hPi_ne
    rw [mul_add, mul_div_cancel₀ _ hPi_ne]
    linear_combination -hdecomp
  have hdiff_rhs : DifferentiableAt ℂ
      (fun u : ℂ => g_map u * G_mero b (g_map u)⁻¹ / Pi_b b (g_map u) + T_b b (g_map u)) u₀ := by
    have hg_diff : DifferentiableAt ℂ g_map u₀ := by dsimp only [g_map]; fun_prop
    have hG_diff : DifferentiableAt ℂ (G_mero b) (g_map u₀)⁻¹ :=
      (G_mero_differentiableOn hb _ hinv_mem).differentiableAt hopen_G
    have hT_diff : DifferentiableAt ℂ (T_b b) (g_map u₀) :=
      (T_b_differentiableOn b _ (by simpa [Metric.mem_ball, dist_eq_norm] using hg_lt.trans (by norm_num))).differentiableAt
        (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_eq_norm] using hg_lt.trans (by norm_num)))
    refine DifferentiableAt.add ?_ (hT_diff.comp u₀ hg_diff)
    exact (hg_diff.mul (hG_diff.comp u₀ (hg_diff.inv hg_mem.1))).div
      ((Pi_b_differentiable b _).comp u₀ hg_diff) (PsiWDomain_Pi_b_ne_zero hg_mem)
  exact (hdiff_rhs.congr_of_eventuallyEq hev_eq).differentiableWithinAt

/-! ### Exact Order-`b` Laurent Expansion of `Ψ_b(u)` at `u₀ = i π / log 2` -/

/-- The unique pole `u₀ = i π / log 2 = τ / 2` of `Ψ_b` in `[-1/2, 1/2] × [0, 2π / log 2]`. -/
@[expose] def uPole : ℂ :=
  ((Real.pi / Real.log 2 : ℝ) : ℂ) * I

/-- Cleared holomorphic function `H_b(w) = (1 + w)^b ∑_{m ∈ ℤ} psiTerm b (2^m w)` on `‖w + 1‖ < 1/4`. -/
@[expose] def H_pole (b : ℕ) (w : ℂ) : ℂ :=
  (1 + w) ^ b * T_b b w +
    (1 + w) ^ (b - 1) * (w / Pi_b b w) +
    ∑' k : ℕ, (2 : ℂ) ^ (k + 1) * w /
      ((1 + (2 : ℂ) ^ (k + 1) * w) * Pi_b b w * ∏ r ∈ Finset.range k, (1 + (2 : ℂ) ^ (r + 1) * w) ^ b)

private lemma norm_H_pole_pos_term_le {b : ℕ} (hb : 2 ≤ b) {w : ℂ} (hw : ‖w + 1‖ ≤ 1 / 4) (k : ℕ) :
    ‖(2 : ℂ) ^ (k + 1) * w /
      ((1 + (2 : ℂ) ^ (k + 1) * w) * Pi_b b w * ∏ r ∈ Finset.range k, (1 + (2 : ℂ) ^ (r + 1) * w) ^ b)‖ ≤
      (5 / ((3 / 32 : ℝ) * P_inf) ^ b) * (1 / 2 : ℝ) ^ k := by
  have hw_le : ‖w‖ ≤ 5 / 4 := by
    have htri : ‖w‖ ≤ ‖w + 1‖ + ‖(-1 : ℂ)‖ := by
      calc ‖w‖ = ‖(w + 1) + (-1)‖ := by ring_nf
        _ ≤ ‖w + 1‖ + ‖(-1 : ℂ)‖ := norm_add_le _ _
    simp only [norm_neg, norm_one] at htri; linarith
  have hw_ge : (3 / 4 : ℝ) ≤ ‖w‖ := by
    have h1 : (1 : ℝ) ≤ ‖w + 1‖ + ‖w‖ := by
      calc (1 : ℝ) = ‖(1 : ℂ)‖ := norm_one.symm
        _ = ‖(w + 1) - w‖ := by ring_nf
        _ ≤ ‖w + 1‖ + ‖w‖ := norm_sub_le _ _
    linarith
  have hfac_ge : ∀ r : ℕ, (1 / 2 : ℝ) * (2 : ℝ) ^ r ≤ ‖1 + (2 : ℂ) ^ (r + 1) * w‖ := fun r => by
    have htri := norm_sub_norm_le ((2 : ℂ) ^ (r + 1) * w) (-1)
    simp only [sub_neg_eq_add, norm_neg, norm_one, norm_mul, norm_pow, Complex.norm_ofNat] at htri
    rw [add_comm ((2 : ℂ) ^ (r + 1) * w) 1] at htri
    rw [pow_succ'] at htri
    have h2r : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
    nlinarith
  have hfac_ge1 : ∀ r : ℕ, 1 ≤ r → (2 : ℝ) ≤ ‖1 + (2 : ℂ) ^ (r + 1) * w‖ := fun r hr => by
    have htri := norm_sub_norm_le ((2 : ℂ) ^ (r + 1) * w) (-1)
    simp only [sub_neg_eq_add, norm_neg, norm_one, norm_mul, norm_pow, Complex.norm_ofNat] at htri
    rw [add_comm ((2 : ℂ) ^ (r + 1) * w) 1] at htri
    have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (r + 1) := by
      calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ (2 : ℝ) ^ (r + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  have hPpos : 0 < P_inf := P_inf_pos
  have hPi_ge : ((3 / 8 : ℝ) * P_inf) ^ b ≤ ‖Pi_b b w‖ := by
    rw [Pi_b, norm_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ b
    have h2 : Pi_1 w = (1 + w / 2) * Pi_1 (w / 2) := by
      have := Pi_1_two_mul (w / 2)
      rwa [show 2 * (w / 2) = w by ring] at this
    rw [h2, norm_mul]
    have hw2_le : ‖w / 2‖ ≤ 1 := by
      rw [norm_div, Complex.norm_ofNat]; linarith
    have h1w2 : (3 / 8 : ℝ) ≤ ‖1 + w / 2‖ := by
      have htri := norm_sub_norm_le (1 : ℂ) (-(w / 2))
      simp only [sub_neg_eq_add, norm_one, norm_neg, norm_div, Complex.norm_ofNat] at htri
      linarith
    exact mul_le_mul h1w2 (norm_Pi_1_ge_on_ball hw2_le) P_inf_pos.le (by positivity)
  have hprod_ge : (1 / 4 : ℝ) ^ b * (2 : ℝ) ^ k ≤ ‖∏ r ∈ Finset.range k, (1 + (2 : ℂ) ^ (r + 1) * w) ^ b‖ := by
    rw [norm_prod]
    cases k with
    | zero =>
      simp only [Finset.range_zero, Finset.prod_empty, pow_zero, mul_one]
      exact pow_le_one₀ (by positivity) (by norm_num)
    | succ m =>
      rw [Finset.prod_range_succ']
      have h0 : (1 / 2 : ℝ) ^ b ≤ ‖(1 + (2 : ℂ) ^ (0 + 1) * w) ^ b‖ := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (by positivity) (by simpa using hfac_ge 0) b
      have hrest : ((2 : ℝ) ^ b) ^ m ≤ ∏ r ∈ Finset.range m, ‖(1 + (2 : ℂ) ^ (r + 1 + 1) * w) ^ b‖ := by
        calc ((2 : ℝ) ^ b) ^ m = ∏ _r ∈ Finset.range m, (2 : ℝ) ^ b := by
              rw [Finset.prod_const, Finset.card_range]
          _ ≤ ∏ r ∈ Finset.range m, ‖(1 + (2 : ℂ) ^ (r + 1 + 1) * w) ^ b‖ := by
              refine real_finset_prod_le_prod (fun _ _ => by positivity) fun r _ => ?_
              rw [norm_pow]
              exact pow_le_pow_left₀ (by positivity) (hfac_ge1 (r + 1) (by omega)) b
      have hstep : (1 / 4 : ℝ) ^ b * (2 : ℝ) ^ (m + 1) ≤ ((2 : ℝ) ^ b) ^ m * (1 / 2 : ℝ) ^ b := by
        rw [← pow_mul, show (1 / 4 : ℝ) ^ b = (1 / 2 : ℝ) ^ b * (1 / 2 : ℝ) ^ b by
          rw [← mul_pow]; norm_num, mul_assoc]
        have hhalf_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ b := by positivity
        rw [mul_comm ((2 : ℝ) ^ (b * m))]
        refine mul_le_mul_of_nonneg_left ?_ hhalf_pos.le
        rw [show (1 / 2 : ℝ) ^ b = ((2 : ℝ) ^ b)⁻¹ from (by rw [one_div, inv_pow])]
        rw [inv_mul_le_iff₀ (by positivity), ← pow_add]
        exact pow_le_pow_right₀ (by norm_num) (by nlinarith)
      exact hstep.trans (mul_le_mul hrest h0 (by positivity) (by positivity))
  have hden_ge : ((1 / 2 : ℝ) * (2 : ℝ) ^ k) * ((3 / 8 : ℝ) * P_inf) ^ b * ((1 / 4 : ℝ) ^ b * (2 : ℝ) ^ k) ≤
      ‖(1 + (2 : ℂ) ^ (k + 1) * w) * Pi_b b w * ∏ r ∈ Finset.range k, (1 + (2 : ℂ) ^ (r + 1) * w) ^ b‖ := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (hfac_ge k) hPi_ge (by positivity) (norm_nonneg _)) hprod_ge
      (by positivity) (by positivity)
  have hnum_le : ‖(2 : ℂ) ^ (k + 1) * w‖ ≤ (5 / 2 : ℝ) * (2 : ℝ) ^ k := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat, pow_succ']
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k]
  rw [norm_div]
  calc ‖(2 : ℂ) ^ (k + 1) * w‖ /
        ‖(1 + (2 : ℂ) ^ (k + 1) * w) * Pi_b b w * ∏ r ∈ Finset.range k, (1 + (2 : ℂ) ^ (r + 1) * w) ^ b‖
      ≤ ((5 / 2 : ℝ) * (2 : ℝ) ^ k) /
          (((1 / 2 : ℝ) * (2 : ℝ) ^ k) * ((3 / 8 : ℝ) * P_inf) ^ b * ((1 / 4 : ℝ) ^ b * (2 : ℝ) ^ k)) :=
        div_le_div₀ (by positivity) hnum_le (by positivity) hden_ge
    _ = (5 / ((3 / 32 : ℝ) * P_inf) ^ b) * (1 / 2 : ℝ) ^ k := by
        have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
        have hcomb : ((3 / 8 : ℝ) * P_inf) ^ b * (1 / 4 : ℝ) ^ b = ((3 / 32 : ℝ) * P_inf) ^ b := by
          rw [← mul_pow]; congr 1; ring
        have hden_ne : ((3 / 32 : ℝ) * P_inf) ^ b ≠ 0 := by positivity
        calc ((5 / 2 : ℝ) * (2 : ℝ) ^ k) /
              (((1 / 2 : ℝ) * (2 : ℝ) ^ k) * ((3 / 8 : ℝ) * P_inf) ^ b * ((1 / 4 : ℝ) ^ b * (2 : ℝ) ^ k))
            = ((5 / 2 : ℝ) * (2 : ℝ) ^ k) /
                (((1 / 2 : ℝ) * (2 : ℝ) ^ k) * (((3 / 8 : ℝ) * P_inf) ^ b * (1 / 4 : ℝ) ^ b) * (2 : ℝ) ^ k) := by ring
          _ = ((5 / 2 : ℝ) * (2 : ℝ) ^ k) /
                (((1 / 2 : ℝ) * (2 : ℝ) ^ k) * ((3 / 32 : ℝ) * P_inf) ^ b * (2 : ℝ) ^ k) := by rw [hcomb]
          _ = (5 / ((3 / 32 : ℝ) * P_inf) ^ b) * (1 / 2 : ℝ) ^ k := by
                rw [show (1 / 2 : ℝ) ^ k = ((2 : ℝ) ^ k)⁻¹ from (by rw [one_div, inv_pow])]
                field_simp [h2k, hden_ne]

private lemma H_pole_differentiableOn {b : ℕ} (hb : 2 ≤ b) :
    DifferentiableOn ℂ (H_pole b) (Metric.ball (-1 : ℂ) (1 / 4)) := by
  unfold H_pole
  have hT : DifferentiableOn ℂ (fun w => (1 + w) ^ b * T_b b w) (Metric.ball (-1 : ℂ) (1 / 4)) := by
    refine (by fun_prop : DifferentiableOn ℂ (fun w : ℂ => (1 + w) ^ b) _).mul ?_
    refine (T_b_differentiableOn b).mono fun w hw => ?_
    have hdist : ‖w + 1‖ < 1 / 4 := by simpa [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add] using hw
    have hw_lt : ‖w‖ < 3 / 2 := by
      have htri : ‖w‖ ≤ ‖w + 1‖ + ‖(-1 : ℂ)‖ := by
        calc ‖w‖ = ‖(w + 1) + (-1)‖ := by ring_nf
          _ ≤ ‖w + 1‖ + ‖(-1 : ℂ)‖ := norm_add_le _ _
      simp only [norm_neg, norm_one] at htri; linarith
    simpa [Metric.mem_ball, dist_eq_norm] using hw_lt
  have hPi_ne : ∀ w ∈ Metric.ball (-1 : ℂ) (1 / 4), Pi_b b w ≠ 0 := fun w hw => by
    have hdist : ‖w + 1‖ < 1 / 4 := by simpa [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add] using hw
    have hw_le : ‖w‖ ≤ 5 / 4 := by
      have htri : ‖w‖ ≤ ‖w + 1‖ + ‖(-1 : ℂ)‖ := by
        calc ‖w‖ = ‖(w + 1) + (-1)‖ := by ring_nf
          _ ≤ ‖w + 1‖ + ‖(-1 : ℂ)‖ := norm_add_le _ _
      simp only [norm_neg, norm_one] at htri; linarith
    refine Pi_b_ne_zero b fun j h0 => ?_
    have : ‖(2 : ℂ) ^ (-(j + 1 : ℤ)) * w‖ = 1 := by
      have h1 : (2 : ℂ) ^ (-(j + 1 : ℤ)) * w = -1 := by linear_combination h0
      rw [h1, norm_neg, norm_one]
    rw [norm_mul, norm_zpow, Complex.norm_ofNat, two_zpow_neg_succ_real] at this
    have h2 : (1 / 2 : ℝ) ^ (j + 1) ≤ 1 / 2 := by
      calc (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
            pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
        _ = 1 / 2 := pow_one _
    nlinarith [norm_nonneg w]
  have h0 : DifferentiableOn ℂ (fun w => (1 + w) ^ (b - 1) * (w / Pi_b b w)) (Metric.ball (-1 : ℂ) (1 / 4)) := by
    intro w hw
    refine (DifferentiableAt.mul (by fun_prop)
      ((differentiableAt_id).div (Pi_b_differentiable b w) (hPi_ne w hw))).differentiableWithinAt
  have hpos : DifferentiableOn ℂ
      (fun w => ∑' k : ℕ, (2 : ℂ) ^ (k + 1) * w /
        ((1 + (2 : ℂ) ^ (k + 1) * w) * Pi_b b w * ∏ r ∈ Finset.range k, (1 + (2 : ℂ) ^ (r + 1) * w) ^ b))
      (Metric.ball (-1 : ℂ) (1 / 4)) := by
    have hunif : TendstoUniformlyOn
        (fun N w => ∑ k ∈ Finset.range N, (2 : ℂ) ^ (k + 1) * w /
          ((1 + (2 : ℂ) ^ (k + 1) * w) * Pi_b b w * ∏ r ∈ Finset.range k, (1 + (2 : ℂ) ^ (r + 1) * w) ^ b))
        (fun w => ∑' k : ℕ, (2 : ℂ) ^ (k + 1) * w /
          ((1 + (2 : ℂ) ^ (k + 1) * w) * Pi_b b w * ∏ r ∈ Finset.range k, (1 + (2 : ℂ) ^ (r + 1) * w) ^ b))
        atTop (Metric.ball (-1 : ℂ) (1 / 4)) := by
      refine tendstoUniformlyOn_tsum_nat
        (u := fun k => (5 / ((3 / 32 : ℝ) * P_inf) ^ b) * (1 / 2 : ℝ) ^ k)
        ((summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left _) ?_
      intro k w hw
      have hdist : ‖w + 1‖ ≤ 1 / 4 := le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add] using hw)
      exact norm_H_pole_pos_term_le hb hdist k
    refine hunif.tendstoLocallyUniformlyOn.differentiableOn (Filter.Eventually.of_forall fun N => ?_) Metric.isOpen_ball
    refine DifferentiableOn.fun_sum fun k _ w hw => ?_
    have hdist : ‖w + 1‖ < 1 / 4 := by simpa [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add] using hw
    have hw_ge : (3 / 4 : ℝ) ≤ ‖w‖ := by
      have h1 : (1 : ℝ) ≤ ‖w + 1‖ + ‖w‖ := by
        calc (1 : ℝ) = ‖(1 : ℂ)‖ := norm_one.symm
          _ = ‖(w + 1) - w‖ := by ring_nf
          _ ≤ ‖w + 1‖ + ‖w‖ := norm_sub_le _ _
      linarith
    have hfac_ne : ∀ r : ℕ, 1 + (2 : ℂ) ^ (r + 1) * w ≠ 0 := fun r h0 => by
      have hnorm : ‖(2 : ℂ) ^ (r + 1) * w‖ = 1 := by
        have : (2 : ℂ) ^ (r + 1) * w = -1 := by linear_combination h0
        rw [this, norm_neg, norm_one]
      rw [norm_mul, norm_pow, Complex.norm_ofNat] at hnorm
      have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (r + 1) := by
        calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (2 : ℝ) ^ (r + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    refine (DifferentiableAt.div (by fun_prop)
      (((by fun_prop : DifferentiableAt ℂ (fun z => 1 + (2 : ℂ) ^ (k + 1) * z) w).mul
        (Pi_b_differentiable b w)).mul
        (differentiableAt_finset_prod (Finset.range k) (fun r z => (1 + (2 : ℂ) ^ (r + 1) * z) ^ b) w
          fun r _ => by fun_prop))
      (mul_ne_zero (mul_ne_zero (hfac_ne k) (hPi_ne w hw))
        (Finset.prod_ne_zero_iff.mpr fun r _ => pow_ne_zero b (hfac_ne r)))).differentiableWithinAt
  exact (hT.add h0).add hpos

private lemma H_pole_neg_one {b : ℕ} (hb : 2 ≤ b) :
    H_pole b (-1) = (K_b b : ℂ) := by
  unfold H_pole
  have h1 : (1 + (-1 : ℂ)) ^ b = 0 := by rw [add_neg_cancel, zero_pow (by omega)]
  have h2 : (1 + (-1 : ℂ)) ^ (b - 1) = 0 := by rw [add_neg_cancel, zero_pow (by omega)]
  rw [h1, zero_mul, h2, zero_mul, zero_add, zero_add, Pi_b_neg_one]
  unfold K_b
  rw [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_tsum, div_eq_mul_inv, ← tsum_mul_right]
  refine tsum_congr fun k => ?_
  unfold kTerm
  push_cast
  have h2k : (2 : ℂ) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hPne : (P_inf : ℂ) ^ b ≠ 0 := pow_ne_zero b (Complex.ofReal_ne_zero.mpr P_inf_pos.ne')
  have h2pow_re : ∀ r : ℕ, ((2 : ℂ) ^ (r + 1)).re = (2 : ℝ) ^ (r + 1) := fun r => by
    have : ((2 : ℂ) ^ (r + 1)) = (((2 : ℝ) ^ (r + 1) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_re]
  have hfac1 : (2 : ℂ) ^ (k + 1) * (-1) / (1 + (2 : ℂ) ^ (k + 1) * (-1)) =
      1 / (1 - (2 : ℂ) ^ (-(k + 1 : ℤ))) := by
    rw [two_zpow_neg_succ_complex]
    have h2ge : (2 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (2 : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hden1 : 1 + (2 : ℂ) ^ (k + 1) * (-1) ≠ 0 := by
      intro h0
      have hre := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.one_re, Complex.neg_re,
        Complex.zero_re, mul_neg, mul_one, h2pow_re] at hre
      linarith
    have hden2 : 1 - ((2 : ℂ) ^ (k + 1))⁻¹ ≠ 0 := by
      intro h0
      have h1 : ((2 : ℂ) ^ (k + 1))⁻¹ = 1 := by linear_combination -h0
      have h2 : (2 : ℂ) ^ (k + 1) = 1 := inv_eq_one.mp h1
      have h3 := congrArg Complex.re h2
      rw [h2pow_re, Complex.one_re] at h3
      linarith
    rw [div_eq_div_iff hden1 hden2]
    field_simp [h2k]
    ring
  have hprod : ∏ r ∈ Finset.range k, (1 + (2 : ℂ) ^ (r + 1) * (-1)) ^ b =
      (-1 : ℂ) ^ (b * k) * ∏ r ∈ Finset.range k, ((2 : ℂ) ^ (r + 1) - 1) ^ b := by
    have hterm : ∀ r ∈ Finset.range k,
        (1 + (2 : ℂ) ^ (r + 1) * (-1)) ^ b = (-1 : ℂ) ^ b * ((2 : ℂ) ^ (r + 1) - 1) ^ b := fun r _ => by
      rw [← mul_pow]; congr 1; ring
    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  have hsign_inv : ((-1 : ℂ) ^ (b * k))⁻¹ = (-1 : ℂ) ^ (b * k) := by
    rw [← inv_pow, inv_neg, inv_one]
  rw [hprod]
  have hprod_ne : ∏ r ∈ Finset.range k, ((2 : ℂ) ^ (r + 1) - 1) ^ b ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun r _ => pow_ne_zero b ?_
    intro h0
    have h1 := congrArg Complex.re h0
    simp only [Complex.sub_re, h2pow_re, Complex.one_re, Complex.zero_re] at h1
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (r + 1) := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (2 : ℝ) ^ (r + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hsign_ne : (-1 : ℂ) ^ (b * k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h1sub_ne : 1 - (2 : ℂ) ^ (-(k + 1 : ℤ)) ≠ 0 := by
    have : (1 - (2 : ℂ) ^ (-(k + 1 : ℤ))) = (((1 - (2 : ℝ) ^ (-(k + 1 : ℤ))) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [this]
    exact Complex.ofReal_ne_zero.mpr (one_sub_two_zpow_pos k).ne'
  calc (2 : ℂ) ^ (k + 1) * (-1) /
        ((1 + (2 : ℂ) ^ (k + 1) * (-1)) * (P_inf : ℂ) ^ b *
          ((-1 : ℂ) ^ (b * k) * ∏ r ∈ Finset.range k, ((2 : ℂ) ^ (r + 1) - 1) ^ b))
      = ((2 : ℂ) ^ (k + 1) * (-1) / (1 + (2 : ℂ) ^ (k + 1) * (-1))) *
          ((-1 : ℂ) ^ (b * k))⁻¹ *
          ((∏ r ∈ Finset.range k, ((2 : ℂ) ^ (r + 1) - 1) ^ b)⁻¹ * ((P_inf : ℂ) ^ b)⁻¹) := by
        field_simp [hPne, hprod_ne, hsign_ne]
    _ = (1 / (1 - (2 : ℂ) ^ (-(k + 1 : ℤ)))) * (-1 : ℂ) ^ (b * k) *
          ((∏ r ∈ Finset.range k, ((2 : ℂ) ^ (r + 1) - 1) ^ b)⁻¹ * ((P_inf : ℂ) ^ b)⁻¹) := by
        rw [hfac1, hsign_inv]
    _ = (-1 : ℂ) ^ (b * k) * (1 / ((1 - (2 : ℂ) ^ (-(k + 1 : ℤ))) *
          ∏ r ∈ Finset.range k, ((2 : ℂ) ^ (r + 1) - 1) ^ b)) * ((P_inf : ℂ) ^ b)⁻¹ := by
        field_simp [h1sub_ne, hprod_ne, hPne]

private lemma H_pole_eq_mul_Psi {b : ℕ} (hb : 2 ≤ b) {w : ℂ} (hw : ‖w + 1‖ < 1 / 4) (hwne : w ≠ -1) :
    H_pole b w = (1 + w) ^ b * ∑' m : ℤ, psiTerm b ((2 : ℂ) ^ m * w) := by
  have hw_dom : w ∈ PsiWDomain := by
    refine ⟨fun h0 => by rw [h0, zero_add, norm_one] at hw; norm_num at hw, fun m h0 => ?_⟩
    cases m with
    | ofNat k =>
      cases k with
      | zero =>
        change 1 + (2 : ℂ) ^ (0 : ℤ) * w = 0 at h0
        rw [zpow_zero, one_mul] at h0
        exact hwne (by linear_combination h0)
      | succ r =>
        have hw_ge : (3 / 4 : ℝ) ≤ ‖w‖ := by
          have h1 : (1 : ℝ) ≤ ‖w + 1‖ + ‖w‖ := by
            calc (1 : ℝ) = ‖(1 : ℂ)‖ := norm_one.symm
              _ = ‖(w + 1) - w‖ := by ring_nf
              _ ≤ ‖w + 1‖ + ‖w‖ := norm_sub_le _ _
          linarith
        change 1 + (2 : ℂ) ^ ((r + 1 : ℕ) : ℤ) * w = 0 at h0
        rw [zpow_natCast] at h0
        have hnorm : ‖(2 : ℂ) ^ (r + 1) * w‖ = 1 := by
          have : (2 : ℂ) ^ (r + 1) * w = -1 := by linear_combination h0
          rw [this, norm_neg, norm_one]
        rw [norm_mul, norm_pow, Complex.norm_ofNat] at hnorm
        have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ (r + 1) := by
          calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one _).symm
            _ ≤ (2 : ℝ) ^ (r + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        nlinarith
    | negSucc k =>
      have hw_le : ‖w‖ ≤ 5 / 4 := by
        have htri : ‖w‖ ≤ ‖w + 1‖ + ‖(-1 : ℂ)‖ := by
          calc ‖w‖ = ‖(w + 1) + (-1)‖ := by ring_nf
            _ ≤ ‖w + 1‖ + ‖(-1 : ℂ)‖ := norm_add_le _ _
        simp only [norm_neg, norm_one] at htri; linarith
      have hnorm : ‖(2 : ℂ) ^ (Int.negSucc k) * w‖ = 1 := by
        have : (2 : ℂ) ^ (Int.negSucc k) * w = -1 := by linear_combination h0
        rw [this, norm_neg, norm_one]
      rw [norm_mul, norm_zpow, Complex.norm_ofNat, Int.negSucc_eq, two_zpow_neg_succ_real] at hnorm
      have h2 : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 / 2 := by
        calc (1 / 2 : ℝ) ^ (k + 1) ≤ (1 / 2 : ℝ) ^ 1 :=
              pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
          _ = 1 / 2 := pow_one _
      nlinarith [norm_nonneg w]
  have hsum := summable_psiTerm_int (by omega : 1 ≤ b) hw_dom
  have h1 : Summable (fun k : ℕ => psiTerm b ((2 : ℂ) ^ (k : ℤ) * w)) :=
    hsum.comp_injective Int.ofNat_injective
  have hsplit : ∑' m : ℤ, psiTerm b ((2 : ℂ) ^ m * w) =
      T_b b w + psiTerm b w + ∑' k : ℕ, psiTerm b ((2 : ℂ) ^ (k + 1) * w) := by
    rw [tsum_int_eq_nat_add_negSucc hsum, h1.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zpow_zero, one_mul, zpow_natCast]
    change (psiTerm b w + ∑' k : ℕ, psiTerm b ((2 : ℂ) ^ (k + 1) * w)) + T_b b w = _
    ring
  rw [hsplit, mul_add, mul_add, ← tsum_mul_left]
  unfold H_pole
  congr 1
  · congr 1
    unfold psiTerm
    have h1w : 1 + w ≠ 0 := fun h0 => hwne (by linear_combination h0)
    have hpow : (1 + w) ^ b = (1 + w) ^ (b - 1) * (1 + w) := by
      rw [← pow_succ, show b - 1 + 1 = b by omega]
    rw [hpow]; field_simp [h1w]
  · refine tsum_congr fun k => ?_
    unfold psiTerm
    rw [Pi_b_pow_two_mul b (k + 1) w, Finset.prod_range_succ', pow_zero, one_mul]
    have h1w : 1 + w ≠ 0 := fun h0 => hwne (by linear_combination h0)
    have h1wb : (1 + w) ^ b ≠ 0 := pow_ne_zero b h1w
    have hPi_ne : Pi_b b w ≠ 0 := PsiWDomain_Pi_b_ne_zero hw_dom
    field_simp [h1wb, hPi_ne]

/-- Iterated `dslope` Taylor remainder: `g u = ∑_{j < n} taylorRem g c j c * (u - c)^j + (u - c)^n * taylorRem g c n u`. -/
@[expose] def taylorRem (g : ℂ → ℂ) (c : ℂ) : ℕ → ℂ → ℂ
  | 0 => g
  | n + 1 => dslope (taylorRem g c n) c

private lemma taylorRem_differentiableOn {g : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (Metric.ball c r)) (n : ℕ) :
    DifferentiableOn ℂ (taylorRem g c n) (Metric.ball c r) := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    change DifferentiableOn ℂ (dslope (taylorRem g c n) c) (Metric.ball c r)
    exact (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).mpr ih

private lemma taylorRem_decomp (g : ℂ → ℂ) (c : ℂ) (n : ℕ) (u : ℂ) :
    g u = (∑ j ∈ Finset.range n, taylorRem g c j c * (u - c) ^ j) +
      (u - c) ^ n * taylorRem g c n u := by
  induction n with
  | zero => simp [taylorRem]
  | succ n ih =>
    rw [ih, Finset.sum_range_succ]
    have hstep : taylorRem g c n u = taylorRem g c n c + (u - c) * taylorRem g c (n + 1) u := by
      change taylorRem g c n u = taylorRem g c n c + (u - c) * dslope (taylorRem g c n) c u
      have := sub_smul_dslope (taylorRem g c n) c u
      rw [smul_eq_mul] at this
      linear_combination -this
    rw [hstep, pow_succ]
    ring

/-- The auxiliary function `u ↦ 1 + exp(-log 2 * u)`, vanishing simply at `uPole = i π / log 2`. -/
@[expose] def poleFactor (u : ℂ) : ℂ :=
  1 + Complex.exp (-((Real.log 2 : ℝ) : ℂ) * u)

private lemma poleFactor_uPole : poleFactor uPole = 0 := by
  unfold poleFactor uPole
  have hlog2 : ((Real.log 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  have harg : -((Real.log 2 : ℝ) : ℂ) * (((Real.pi / Real.log 2 : ℝ) : ℂ) * I) =
      -((Real.pi : ℂ) * I) := by
    push_cast; field_simp [hlog2]
  rw [harg, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one, add_neg_cancel]

private lemma dslope_poleFactor_uPole :
    dslope poleFactor uPole uPole = ((Real.log 2 : ℝ) : ℂ) := by
  rw [dslope_same]
  have hd : HasDerivAt poleFactor
      (-((Real.log 2 : ℝ) : ℂ) * Complex.exp (-((Real.log 2 : ℝ) : ℂ) * uPole)) uPole := by
    unfold poleFactor
    have h1 : HasDerivAt (fun u : ℂ => -((Real.log 2 : ℝ) : ℂ) * u) (-((Real.log 2 : ℝ) : ℂ)) uPole := by
      simpa using (hasDerivAt_id uPole).const_mul (-((Real.log 2 : ℝ) : ℂ))
    have h2 : HasDerivAt (fun u : ℂ => 1 + Complex.exp (-((Real.log 2 : ℝ) : ℂ) * u))
        (Complex.exp (-((Real.log 2 : ℝ) : ℂ) * uPole) * -((Real.log 2 : ℝ) : ℂ)) uPole :=
      (Complex.hasDerivAt_exp _).comp uPole h1 |>.const_add 1
    simpa [mul_comm] using h2
  rw [hd.deriv]
  have h1 : Complex.exp (-((Real.log 2 : ℝ) : ℂ) * uPole) = -1 := by
    have := poleFactor_uPole; unfold poleFactor at this; linear_combination this
  rw [h1]; ring

/-- Cleared local holomorphic numerator `G_loc b u = (u - uPole)^b * Ψ_b(u)` on `Metric.ball uPole (1 / 8)`. -/
@[expose] def G_loc (b : ℕ) (u : ℂ) : ℂ :=
  H_pole b (Complex.exp (-((Real.log 2 : ℝ) : ℂ) * u)) / (dslope poleFactor uPole u) ^ b

/-- Exact Laurent coefficients `c_{-r}` (`1 ≤ r ≤ b`) of `Ψ_b` at `uPole`:
`laurentC b r := taylorRem (G_loc b) uPole (b - r) uPole`. -/
@[expose] def laurentC (b r : ℕ) : ℂ :=
  taylorRem (G_loc b) uPole (b - r) uPole

/-- Holomorphic part of `Ψ_b` on `Metric.ball uPole (1 / 8)` after subtracting the order-`b` pole. -/
@[expose] def Psi_holo (b : ℕ) (u : ℂ) : ℂ :=
  taylorRem (G_loc b) uPole b u

private lemma norm_exp_sub_one_le_two_mul {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - 1‖ ≤ 2 * ‖z‖ := by
  have hexp : Complex.exp z - 1 = ∑' k : ℕ, z ^ (k + 1) / ((k + 1).factorial : ℂ) := by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
    dsimp only
    have hsum : Summable (fun n : ℕ => z ^ n / (n.factorial : ℂ)) := by
      refine Summable.of_norm_bounded (Real.summable_pow_div_factorial ‖z‖) fun n => ?_
      rw [norm_div, norm_pow, Complex.norm_natCast]
    rw [hsum.tsum_eq_zero_add]
    simp
  rw [hexp]
  have hsum_bd : Summable (fun k : ℕ => ‖z‖ * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by positivity) (by norm_num)).mul_left ‖z‖
  have hfac : ∀ k : ℕ, (2 : ℝ) ^ k ≤ ((k + 1).factorial : ℝ) := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Nat.factorial_succ, Nat.cast_mul]
      have h2 : (2 : ℝ) ≤ ((k + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ k + 1 + 1 by omega)
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k]
  have hterm : ∀ k : ℕ, ‖z ^ (k + 1) / ((k + 1).factorial : ℂ)‖ ≤ ‖z‖ * (1 / 2 : ℝ) ^ k := fun k => by
    rw [norm_div, norm_pow, Complex.norm_natCast, pow_succ']
    have hzk : ‖z‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hz
    have hnum : ‖z‖ * ‖z‖ ^ k ≤ ‖z‖ := mul_le_of_le_one_right (norm_nonneg _) hzk
    calc ‖z‖ * ‖z‖ ^ k / ((k + 1).factorial : ℝ)
        ≤ ‖z‖ / (2 : ℝ) ^ k := div_le_div₀ (norm_nonneg _) hnum (by positivity) (hfac k)
      _ = ‖z‖ * (1 / 2 : ℝ) ^ k := by rw [one_div, inv_pow, div_eq_mul_inv]
  have hsum_n : Summable (fun k : ℕ => ‖z ^ (k + 1) / ((k + 1).factorial : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsum_bd
  calc ‖∑' k : ℕ, z ^ (k + 1) / ((k + 1).factorial : ℂ)‖
      ≤ ∑' k : ℕ, ‖z ^ (k + 1) / ((k + 1).factorial : ℂ)‖ := norm_tsum_le_tsum_norm hsum_n
    _ ≤ ∑' k : ℕ, ‖z‖ * (1 / 2 : ℝ) ^ k := hsum_n.tsum_le_tsum hterm hsum_bd
    _ = 2 * ‖z‖ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) (by norm_num)]; ring

private lemma poleFactor_mem_ball {u : ℂ} (hu : u ∈ Metric.ball uPole (1 / 8)) :
    Complex.exp (-((Real.log 2 : ℝ) : ℂ) * u) ∈ Metric.ball (-1 : ℂ) (1 / 4) := by
  have hdist : ‖u - uPole‖ < 1 / 8 := by simpa [Metric.mem_ball, dist_eq_norm] using hu
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt1 : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]
  have hexp_u0 : Complex.exp (-((Real.log 2 : ℝ) : ℂ) * uPole) = -1 := by
    have := poleFactor_uPole; unfold poleFactor at this; linear_combination this
  have hrew : Complex.exp (-((Real.log 2 : ℝ) : ℂ) * u) - (-1) =
      -(Complex.exp (-((Real.log 2 : ℝ) : ℂ) * (u - uPole)) - 1) := by
    have harg : -((Real.log 2 : ℝ) : ℂ) * u =
        -((Real.log 2 : ℝ) : ℂ) * uPole + (-((Real.log 2 : ℝ) : ℂ) * (u - uPole)) := by ring
    rw [harg, Complex.exp_add, hexp_u0]; ring
  rw [Metric.mem_ball, dist_eq_norm, hrew, norm_neg]
  have hz_norm : ‖-((Real.log 2 : ℝ) : ℂ) * (u - uPole)‖ < 1 / 8 := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hlog2_pos.le]
    nlinarith [norm_nonneg (u - uPole)]
  have hbd := norm_exp_sub_one_le_two_mul (hz_norm.le.trans (by norm_num))
  linarith

private lemma dslope_poleFactor_ne_zero {u : ℂ} (hu : u ∈ Metric.ball uPole (1 / 8)) :
    dslope poleFactor uPole u ≠ 0 := by
  by_cases heq : u = uPole
  · subst heq; rw [dslope_poleFactor_uPole]
    exact Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  · rw [dslope_of_ne _ heq, slope_def_field, poleFactor_uPole, sub_zero]
    refine div_ne_zero ?_ (sub_ne_zero.mpr heq)
    intro h0
    have hexp_u0 : Complex.exp (-((Real.log 2 : ℝ) : ℂ) * uPole) = -1 := by
      have := poleFactor_uPole; unfold poleFactor at this; linear_combination this
    have hexp1 : Complex.exp (-((Real.log 2 : ℝ) : ℂ) * (u - uPole)) = 1 := by
      have harg : -((Real.log 2 : ℝ) : ℂ) * u =
          -((Real.log 2 : ℝ) : ℂ) * uPole + (-((Real.log 2 : ℝ) : ℂ) * (u - uPole)) := by ring
      have hpf : Complex.exp (-((Real.log 2 : ℝ) : ℂ) * u) = -1 := by
        unfold poleFactor at h0; linear_combination h0
      rw [harg, Complex.exp_add, hexp_u0] at hpf
      linear_combination -hpf
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp1
    have hdist : ‖u - uPole‖ < 1 / 8 := by simpa [Metric.mem_ball, dist_eq_norm] using hu
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2_lt1 : Real.log 2 < 1 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]
    have hz_norm : ‖-((Real.log 2 : ℝ) : ℂ) * (u - uPole)‖ < 1 / 8 := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hlog2_pos.le]
      nlinarith [norm_nonneg (u - uPole)]
    rw [hn, norm_mul, norm_mul, norm_mul, Complex.norm_intCast, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one] at hz_norm
    by_cases hn0 : n = 0
    · subst hn0
      simp only [Int.cast_zero, zero_mul] at hn
      have hlog2_ne : -((Real.log 2 : ℝ) : ℂ) ≠ 0 :=
        neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hlog2_pos.ne')
      exact heq (sub_eq_zero.mp ((mul_eq_zero.mp hn).resolve_left hlog2_ne))
    · have habs : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
      have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      nlinarith

lemma G_loc_differentiableOn {b : ℕ} (hb : 2 ≤ b) :
    DifferentiableOn ℂ (G_loc b) (Metric.ball uPole (1 / 8)) := by
  intro u hu
  have h1 : DifferentiableAt ℂ (fun z => H_pole b (Complex.exp (-((Real.log 2 : ℝ) : ℂ) * z))) u := by
    have hH := (H_pole_differentiableOn hb _ (poleFactor_mem_ball hu)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (poleFactor_mem_ball hu))
    have hexp_d : DifferentiableAt ℂ (fun z : ℂ => Complex.exp (-((Real.log 2 : ℝ) : ℂ) * z)) u := by fun_prop
    exact hH.comp u hexp_d
  have hpf_diff : DifferentiableOn ℂ poleFactor (Metric.ball uPole (1 / 8)) := by
    unfold poleFactor; fun_prop
  have h2 : DifferentiableAt ℂ (fun z => (dslope poleFactor uPole z) ^ b) u := by
    have hd := ((Complex.differentiableOn_dslope
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 8)))).mpr hpf_diff u hu).differentiableAt
      (Metric.isOpen_ball.mem_nhds hu)
    exact hd.pow b
  exact (h1.div h2 (pow_ne_zero b (dslope_poleFactor_ne_zero hu))).differentiableWithinAt

/-- Exact leading Laurent coefficient `c_{-b} = K_b / (log 2)^b ≠ 0` at `uPole = i π / log 2`. -/
lemma laurentC_top {b : ℕ} (hb : 2 ≤ b) :
    laurentC b b = (K_b b : ℂ) / ((Real.log 2 : ℝ) : ℂ) ^ b := by
  unfold laurentC
  rw [Nat.sub_self]
  change G_loc b uPole = _
  unfold G_loc
  have hexp_u0 : Complex.exp (-((Real.log 2 : ℝ) : ℂ) * uPole) = -1 := by
    have := poleFactor_uPole; unfold poleFactor at this; linear_combination this
  rw [hexp_u0, H_pole_neg_one hb, dslope_poleFactor_uPole]

lemma laurentC_top_ne_zero {b : ℕ} (hb : 2 ≤ b) : laurentC b b ≠ 0 := by
  rw [laurentC_top hb]
  exact div_ne_zero (Complex.ofReal_ne_zero.mpr (K_b_pos b hb).ne')
    (pow_ne_zero b (Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'))

lemma Psi_holo_differentiableOn {b : ℕ} (hb : 2 ≤ b) :
    DifferentiableOn ℂ (Psi_holo b) (Metric.ball uPole (1 / 8)) :=
  taylorRem_differentiableOn (by norm_num) (G_loc_differentiableOn hb) b

/-- **Exact order-`b` Laurent expansion of `Ψ_b(u)` on `Metric.ball uPole (1 / 8) \ {uPole}`:**
`Ψ_b(u) = ∑_{r = 1}^b laurentC b r / (u - uPole)^r + Psi_holo b u`. -/
theorem Psi_b_laurent_at_uPole {b : ℕ} (hb : 2 ≤ b) {u : ℂ}
    (hu : u ∈ Metric.ball uPole (1 / 8)) (hne : u ≠ uPole) :
    Psi_b b u = (∑ r ∈ Finset.Icc 1 b, laurentC b r / (u - uPole) ^ r) + Psi_holo b u := by
  have hsub : u - uPole ≠ 0 := sub_ne_zero.mpr hne
  have hG : G_loc b u = (u - uPole) ^ b * Psi_b b u := by
    unfold G_loc
    have hd : dslope poleFactor uPole u = poleFactor u / (u - uPole) := by
      rw [dslope_of_ne _ hne, slope_def_field, poleFactor_uPole, sub_zero]
    rw [hd, div_pow]
    have hpf_ne : poleFactor u ≠ 0 := by
      have := dslope_poleFactor_ne_zero hu
      rw [hd] at this
      exact left_ne_zero_of_mul (div_eq_mul_inv (poleFactor u) (u - uPole) ▸ this)
    have hwp : Complex.exp (-((Real.log 2 : ℝ) : ℂ) * u) ≠ -1 := fun h0 =>
      hpf_ne (by unfold poleFactor; rw [h0]; ring)
    have hHp := H_pole_eq_mul_Psi hb
      (by simpa [Metric.mem_ball, dist_eq_norm, sub_neg_eq_add] using poleFactor_mem_ball hu) hwp
    rw [hHp]
    unfold poleFactor Psi_b
    have hpow_ne : (1 + Complex.exp (-((Real.log 2 : ℝ) : ℂ) * u)) ^ b ≠ 0 := pow_ne_zero b hpf_ne
    have hsub_b : (u - uPole) ^ b ≠ 0 := pow_ne_zero b hsub
    have halg : ∀ a p q : ℂ, p ≠ 0 → q ≠ 0 → (p * a) / (p / q) = q * a := fun a p q hp hq => by
      field_simp [hp, hq]
    exact halg _ _ _ hpow_ne hsub_b
  have hdec := taylorRem_decomp (G_loc b) uPole b u
  rw [hG] at hdec
  have hsub_b : (u - uPole) ^ b ≠ 0 := pow_ne_zero b hsub
  have hdiv : Psi_b b u =
      (∑ j ∈ Finset.range b, taylorRem (G_loc b) uPole j uPole * (u - uPole) ^ j) / (u - uPole) ^ b +
        Psi_holo b u := by
    unfold Psi_holo
    field_simp [hsub_b]
    linear_combination hdec
  rw [hdiv]
  congr 1
  rw [Finset.sum_div]
  refine Finset.sum_bij (fun j _ => b - j) ?_ ?_ ?_ ?_
  · intro j hj; rw [Finset.mem_range] at hj; rw [Finset.mem_Icc]; omega
  · intro j₁ hj₁ j₂ hj₂ h; rw [Finset.mem_range] at hj₁ hj₂; omega
  · intro r hr; rw [Finset.mem_Icc] at hr; exact ⟨b - r, Finset.mem_range.mpr (by omega), by omega⟩
  · intro j hj
    rw [Finset.mem_range] at hj
    unfold laurentC
    rw [show b - (b - j) = j by omega]
    have hpow : (u - uPole) ^ b = (u - uPole) ^ j * (u - uPole) ^ (b - j) := by
      rw [← pow_add, Nat.add_sub_of_le (by omega)]
    rw [hpow]
    have hj_ne : (u - uPole) ^ j ≠ 0 := pow_ne_zero j hsub
    have hbj_ne : (u - uPole) ^ (b - j) ≠ 0 := pow_ne_zero (b - j) hsub
    field_simp [hj_ne, hbj_ne]

/-! ## Section 3: Rectangle Residue Integral, Exact Fourier Coefficients, Gamma Reflection & Poisson Summation -/

section Section3

open PakPrimes.BorelStokesVandermonde (rectIntegral rectIntegral_eq_zero_of_differentiableOn
  rectIntegral_sub_rectIntegral rectIntegral_const_mul rectIntegral_hsplit rectIntegral_inv_sub)

/-! ### Identity Theorem Helper & Rectangle Contour Primitives -/

/-- Identity theorem on an open preconnected set `U ⊆ ℂ` containing a real open interval `(a, b)`. -/
private lemma eqOn_of_differentiableOn_eq_on_real_interval {f g : ℂ → ℂ} {U : Set ℂ}
    (hU_open : IsOpen U) (hU_conn : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {a b : ℝ} (hab : a < b)
    (hsub : ∀ x : ℝ, a < x → x < b → (x : ℂ) ∈ U)
    (heq : ∀ x : ℝ, a < x → x < b → f (x : ℂ) = g (x : ℂ)) :
    Set.EqOn f g U := by
  let x₀ : ℝ := (a + b) / 2
  have hx₀a : a < x₀ := by dsimp only [x₀]; linarith
  have hx₀b : x₀ < b := by dsimp only [x₀]; linarith
  have hz₀ : (x₀ : ℂ) ∈ U := hsub x₀ hx₀a hx₀b
  have hfreq : ∃ᶠ z in nhdsWithin (x₀ : ℂ) {(x₀ : ℂ)}ᶜ, f z = g z := by
    rw [Filter.frequently_iff]
    intro s hs
    rw [Metric.mem_nhdsWithin_iff] at hs
    obtain ⟨ε, hε, hεs⟩ := hs
    let δ : ℝ := min (ε / 2) ((b - a) / 4)
    have hδ_pos : 0 < δ := lt_min (half_pos hε) (by linarith)
    have hδ_lt_ε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
    have hx_a : a < x₀ + δ := by dsimp only [x₀]; linarith
    have hx_b : x₀ + δ < b := by
      have h1 : δ ≤ (b - a) / 4 := min_le_right _ _
      dsimp only [x₀]; linarith
    refine ⟨((x₀ + δ : ℝ) : ℂ), hεs ⟨?_, ?_⟩, heq (x₀ + δ) hx_a hx_b⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      rw [show ((x₀ + δ : ℝ) : ℂ) - (x₀ : ℂ) = (δ : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg hδ_pos.le]
      exact hδ_lt_ε
    · intro h0
      have hre := congrArg Complex.re h0
      simp only [Complex.ofReal_re] at hre
      linarith
  exact (hf.analyticOnNhd hU_open).eqOn_of_preconnected_of_frequently_eq
    (hg.analyticOnNhd hU_open) hU_conn hz₀ hfreq

private lemma rectIntegral_add {f g : ℂ → ℂ} {z w : ℂ}
    (hb₁ : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (z.im : ℂ) * I)) volume z.re w.re)
    (hb₂ : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (z.im : ℂ) * I)) volume z.re w.re)
    (ht₁ : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (w.im : ℂ) * I)) volume z.re w.re)
    (ht₂ : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (w.im : ℂ) * I)) volume z.re w.re)
    (hr₁ : IntervalIntegrable (fun y : ℝ => f ((w.re : ℂ) + (y : ℂ) * I)) volume z.im w.im)
    (hr₂ : IntervalIntegrable (fun y : ℝ => g ((w.re : ℂ) + (y : ℂ) * I)) volume z.im w.im)
    (hl₁ : IntervalIntegrable (fun y : ℝ => f ((z.re : ℂ) + (y : ℂ) * I)) volume z.im w.im)
    (hl₂ : IntervalIntegrable (fun y : ℝ => g ((z.re : ℂ) + (y : ℂ) * I)) volume z.im w.im) :
    rectIntegral (fun ζ => f ζ + g ζ) z w = rectIntegral f z w + rectIntegral g z w := by
  unfold rectIntegral
  rw [intervalIntegral.integral_add hb₁ hb₂, intervalIntegral.integral_add ht₁ ht₂,
    intervalIntegral.integral_add hr₁ hr₂, intervalIntegral.integral_add hl₁ hl₂]
  ring

private lemma intervalIntegrable_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (a b : ℝ)
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun t => ∑ i ∈ s, f i t) volume a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [intervalIntegrable_const]
  | insert x s hx ih =>
    have hfun : (fun t => ∑ i ∈ insert x s, f i t) = fun t => f x t + ∑ i ∈ s, f i t := by
      funext t; exact Finset.sum_insert hx
    rw [hfun]
    exact (hf x (Finset.mem_insert_self x s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma rectIntegral_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (z w : ℂ)
    (hb : ∀ i ∈ s, IntervalIntegrable (fun x : ℝ => f i ((x : ℂ) + (z.im : ℂ) * I)) volume z.re w.re)
    (ht : ∀ i ∈ s, IntervalIntegrable (fun x : ℝ => f i ((x : ℂ) + (w.im : ℂ) * I)) volume z.re w.re)
    (hr : ∀ i ∈ s, IntervalIntegrable (fun y : ℝ => f i ((w.re : ℂ) + (y : ℂ) * I)) volume z.im w.im)
    (hl : ∀ i ∈ s, IntervalIntegrable (fun y : ℝ => f i ((z.re : ℂ) + (y : ℂ) * I)) volume z.im w.im) :
    rectIntegral (fun ζ => ∑ i ∈ s, f i ζ) z w = ∑ i ∈ s, rectIntegral (f i) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rectIntegral]
  | insert a s ha ih =>
    have hfun : (fun ζ => ∑ i ∈ insert a s, f i ζ) = fun ζ => f a ζ + ∑ i ∈ s, f i ζ := by
      funext ζ; exact Finset.sum_insert ha
    rw [hfun, Finset.sum_insert ha]
    have hb_s : IntervalIntegrable (fun x : ℝ => ∑ i ∈ s, f i ((x : ℂ) + (z.im : ℂ) * I)) volume z.re w.re :=
      intervalIntegrable_finset_sum s (fun i x => f i ((x : ℂ) + (z.im : ℂ) * I)) _ _
        fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have ht_s : IntervalIntegrable (fun x : ℝ => ∑ i ∈ s, f i ((x : ℂ) + (w.im : ℂ) * I)) volume z.re w.re :=
      intervalIntegrable_finset_sum s (fun i x => f i ((x : ℂ) + (w.im : ℂ) * I)) _ _
        fun i hi => ht i (Finset.mem_insert_of_mem hi)
    have hr_s : IntervalIntegrable (fun y : ℝ => ∑ i ∈ s, f i ((w.re : ℂ) + (y : ℂ) * I)) volume z.im w.im :=
      intervalIntegrable_finset_sum s (fun i y => f i ((w.re : ℂ) + (y : ℂ) * I)) _ _
        fun i hi => hr i (Finset.mem_insert_of_mem hi)
    have hl_s : IntervalIntegrable (fun y : ℝ => ∑ i ∈ s, f i ((z.re : ℂ) + (y : ℂ) * I)) volume z.im w.im :=
      intervalIntegrable_finset_sum s (fun i y => f i ((z.re : ℂ) + (y : ℂ) * I)) _ _
        fun i hi => hl i (Finset.mem_insert_of_mem hi)
    rw [rectIntegral_add (hb a (Finset.mem_insert_self a s)) hb_s
      (ht a (Finset.mem_insert_self a s)) ht_s
      (hr a (Finset.mem_insert_self a s)) hr_s
      (hl a (Finset.mem_insert_self a s)) hl_s]
    rw [ih (fun i hi => hb i (Finset.mem_insert_of_mem hi))
      (fun i hi => ht i (Finset.mem_insert_of_mem hi))
      (fun i hi => hr i (Finset.mem_insert_of_mem hi))
      (fun i hi => hl i (Finset.mem_insert_of_mem hi))]

private lemma rectIntegral_congr_boundary {f g : ℂ → ℂ} {z w : ℂ}
    (hb : ∀ x ∈ Set.uIcc z.re w.re, f ((x : ℂ) + (z.im : ℂ) * I) = g ((x : ℂ) + (z.im : ℂ) * I))
    (ht : ∀ x ∈ Set.uIcc z.re w.re, f ((x : ℂ) + (w.im : ℂ) * I) = g ((x : ℂ) + (w.im : ℂ) * I))
    (hr : ∀ y ∈ Set.uIcc z.im w.im, f ((w.re : ℂ) + (y : ℂ) * I) = g ((w.re : ℂ) + (y : ℂ) * I))
    (hl : ∀ y ∈ Set.uIcc z.im w.im, f ((z.re : ℂ) + (y : ℂ) * I) = g ((z.re : ℂ) + (y : ℂ) * I)) :
    rectIntegral f z w = rectIntegral g z w := by
  unfold rectIntegral
  rw [intervalIntegral.integral_congr hb, intervalIntegral.integral_congr ht,
    intervalIntegral.integral_congr hr, intervalIntegral.integral_congr hl]

private lemma rectIntegral_vsplit {f : ℂ → ℂ} {x₁ x₂ y₁ y₀ y₂ : ℝ}
    (hr₁ : IntervalIntegrable (fun y : ℝ => f ((x₂ : ℂ) + (y : ℂ) * I)) volume y₁ y₀)
    (hr₂ : IntervalIntegrable (fun y : ℝ => f ((x₂ : ℂ) + (y : ℂ) * I)) volume y₀ y₂)
    (hl₁ : IntervalIntegrable (fun y : ℝ => f ((x₁ : ℂ) + (y : ℂ) * I)) volume y₁ y₀)
    (hl₂ : IntervalIntegrable (fun y : ℝ => f ((x₁ : ℂ) + (y : ℂ) * I)) volume y₀ y₂) :
    rectIntegral f ((x₁ : ℂ) + (y₁ : ℂ) * I) ((x₂ : ℂ) + (y₂ : ℂ) * I) =
      rectIntegral f ((x₁ : ℂ) + (y₁ : ℂ) * I) ((x₂ : ℂ) + (y₀ : ℂ) * I) +
      rectIntegral f ((x₁ : ℂ) + (y₀ : ℂ) * I) ((x₂ : ℂ) + (y₂ : ℂ) * I) := by
  unfold rectIntegral
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    mul_zero, Complex.ofReal_im, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  rw [← intervalIntegral.integral_add_adjacent_intervals hr₁ hr₂,
    ← intervalIntegral.integral_add_adjacent_intervals hl₁ hl₂]
  ring

private lemma rectIntegral_translate (f : ℂ → ℂ) (z w c : ℂ) :
    rectIntegral (fun ζ => f (ζ - c)) (z + c) (w + c) = rectIntegral f z w := by
  unfold rectIntegral
  simp only [Complex.add_re, Complex.add_im]
  have h1 : (∫ x : ℝ in (z.re + c.re)..(w.re + c.re),
      f (((x : ℂ) + ((z.im + c.im : ℝ) : ℂ) * I) - c)) =
      ∫ x : ℝ in z.re..w.re, f ((x : ℂ) + (z.im : ℂ) * I) := by
    have hfun : (fun x : ℝ => f (((x : ℂ) + ((z.im + c.im : ℝ) : ℂ) * I) - c)) =
        fun x : ℝ => f (((x - c.re : ℝ) : ℂ) + (z.im : ℂ) * I) := by
      funext x; congr 1
      apply Complex.ext <;> simp
    rw [hfun]
    simpa [add_sub_cancel_right] using
      intervalIntegral.integral_comp_sub_right (fun t : ℝ => f ((t : ℂ) + (z.im : ℂ) * I)) c.re
        (a := z.re + c.re) (b := w.re + c.re)
  have h2 : (∫ x : ℝ in (z.re + c.re)..(w.re + c.re),
      f (((x : ℂ) + ((w.im + c.im : ℝ) : ℂ) * I) - c)) =
      ∫ x : ℝ in z.re..w.re, f ((x : ℂ) + (w.im : ℂ) * I) := by
    have hfun : (fun x : ℝ => f (((x : ℂ) + ((w.im + c.im : ℝ) : ℂ) * I) - c)) =
        fun x : ℝ => f (((x - c.re : ℝ) : ℂ) + (w.im : ℂ) * I) := by
      funext x; congr 1
      apply Complex.ext <;> simp
    rw [hfun]
    simpa [add_sub_cancel_right] using
      intervalIntegral.integral_comp_sub_right (fun t : ℝ => f ((t : ℂ) + (w.im : ℂ) * I)) c.re
        (a := z.re + c.re) (b := w.re + c.re)
  have h3 : (∫ y : ℝ in (z.im + c.im)..(w.im + c.im),
      f ((((w.re + c.re : ℝ) : ℂ) + (y : ℂ) * I) - c)) =
      ∫ y : ℝ in z.im..w.im, f ((w.re : ℂ) + (y : ℂ) * I) := by
    have hfun : (fun y : ℝ => f ((((w.re + c.re : ℝ) : ℂ) + (y : ℂ) * I) - c)) =
        fun y : ℝ => f ((w.re : ℂ) + ((y - c.im : ℝ) : ℂ) * I) := by
      funext y; congr 1
      apply Complex.ext <;> simp
    rw [hfun]
    simpa [add_sub_cancel_right] using
      intervalIntegral.integral_comp_sub_right (fun t : ℝ => f ((w.re : ℂ) + (t : ℂ) * I)) c.im
        (a := z.im + c.im) (b := w.im + c.im)
  have h4 : (∫ y : ℝ in (z.im + c.im)..(w.im + c.im),
      f ((((z.re + c.re : ℝ) : ℂ) + (y : ℂ) * I) - c)) =
      ∫ y : ℝ in z.im..w.im, f ((z.re : ℂ) + (y : ℂ) * I) := by
    have hfun : (fun y : ℝ => f ((((z.re + c.re : ℝ) : ℂ) + (y : ℂ) * I) - c)) =
        fun y : ℝ => f ((z.re : ℂ) + ((y - c.im : ℝ) : ℂ) * I) := by
      funext y; congr 1
      apply Complex.ext <;> simp
    rw [hfun]
    simpa [add_sub_cancel_right] using
      intervalIntegral.integral_comp_sub_right (fun t : ℝ => f ((z.re : ℂ) + (t : ℂ) * I)) c.im
        (a := z.im + c.im) (b := w.im + c.im)
  rw [h1, h2, h3, h4]

private lemma rectIntegral_eq_zero_of_primitive {f F : ℂ → ℂ} {z w : ℂ}
    (hbot : ∀ x ∈ Set.uIcc z.re w.re, HasDerivAt F (f ((x : ℂ) + (z.im : ℂ) * I)) ((x : ℂ) + (z.im : ℂ) * I))
    (htop : ∀ x ∈ Set.uIcc z.re w.re, HasDerivAt F (f ((x : ℂ) + (w.im : ℂ) * I)) ((x : ℂ) + (w.im : ℂ) * I))
    (hright : ∀ y ∈ Set.uIcc z.im w.im, HasDerivAt F (f ((w.re : ℂ) + (y : ℂ) * I)) ((w.re : ℂ) + (y : ℂ) * I))
    (hleft : ∀ y ∈ Set.uIcc z.im w.im, HasDerivAt F (f ((z.re : ℂ) + (y : ℂ) * I)) ((z.re : ℂ) + (y : ℂ) * I))
    (hb_int : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (z.im : ℂ) * I)) volume z.re w.re)
    (ht_int : IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (w.im : ℂ) * I)) volume z.re w.re)
    (hr_int : IntervalIntegrable (fun y : ℝ => f ((w.re : ℂ) + (y : ℂ) * I)) volume z.im w.im)
    (hl_int : IntervalIntegrable (fun y : ℝ => f ((z.re : ℂ) + (y : ℂ) * I)) volume z.im w.im) :
    rectIntegral f z w = 0 := by
  have h1 : (∫ x : ℝ in z.re..w.re, f ((x : ℂ) + (z.im : ℂ) * I)) =
      F ((w.re : ℂ) + (z.im : ℂ) * I) - F ((z.re : ℂ) + (z.im : ℂ) * I) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => F ((t : ℂ) + (z.im : ℂ) * I)) (fun x hx => ?_) hb_int
    have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) + (z.im : ℂ) * I) 1 x := by
      simpa using Complex.ofRealCLM.hasDerivAt.add_const ((z.im : ℂ) * I)
    simpa [Function.comp_def] using (hbot x hx).comp x hlin
  have h2 : (∫ x : ℝ in z.re..w.re, f ((x : ℂ) + (w.im : ℂ) * I)) =
      F ((w.re : ℂ) + (w.im : ℂ) * I) - F ((z.re : ℂ) + (w.im : ℂ) * I) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => F ((t : ℂ) + (w.im : ℂ) * I)) (fun x hx => ?_) ht_int
    have hlin : HasDerivAt (fun t : ℝ => (t : ℂ) + (w.im : ℂ) * I) 1 x := by
      simpa using Complex.ofRealCLM.hasDerivAt.add_const ((w.im : ℂ) * I)
    simpa [Function.comp_def] using (htop x hx).comp x hlin
  have h3 : I * (∫ y : ℝ in z.im..w.im, f ((w.re : ℂ) + (y : ℂ) * I)) =
      F ((w.re : ℂ) + (w.im : ℂ) * I) - F ((w.re : ℂ) + (z.im : ℂ) * I) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => F ((w.re : ℂ) + (t : ℂ) * I)) (fun y hy => ?_) (hr_int.const_mul I)
    have hlin : HasDerivAt (fun t : ℝ => (w.re : ℂ) + (t : ℂ) * I) I y := by
      simpa using (Complex.ofRealCLM.hasDerivAt.mul_const I).const_add (w.re : ℂ)
    have hc := (hright y hy).comp y hlin
    simpa [Function.comp_def, mul_comm] using hc
  have h4 : I * (∫ y : ℝ in z.im..w.im, f ((z.re : ℂ) + (y : ℂ) * I)) =
      F ((z.re : ℂ) + (w.im : ℂ) * I) - F ((z.re : ℂ) + (z.im : ℂ) * I) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => F ((z.re : ℂ) + (t : ℂ) * I)) (fun y hy => ?_) (hl_int.const_mul I)
    have hlin : HasDerivAt (fun t : ℝ => (z.re : ℂ) + (t : ℂ) * I) I y := by
      simpa using (Complex.ofRealCLM.hasDerivAt.mul_const I).const_add (z.re : ℂ)
    have hc := (hleft y hy).comp y hlin
    simpa [Function.comp_def, mul_comm] using hc
  unfold rectIntegral
  rw [h1, h2, h3, h4]
  ring

private lemma rectIntegral_inv_sub_centered (u₀ : ℂ) {ε : ℝ} (hε : 0 < ε) :
    rectIntegral (fun ζ => (ζ - u₀)⁻¹)
      (u₀ - (ε : ℂ) - (ε : ℂ) * I) (u₀ + (ε : ℂ) + (ε : ℂ) * I) =
      2 * (Real.pi : ℂ) * I := by
  have hz : u₀ - (ε : ℂ) - (ε : ℂ) * I = ((-ε : ℝ) : ℂ) - (ε : ℂ) * I + u₀ := by push_cast; ring
  have hw : u₀ + (ε : ℂ) + (ε : ℂ) * I = (ε : ℂ) + (ε : ℂ) * I + u₀ := by ring
  rw [hz, hw]
  have ht := rectIntegral_translate (fun ζ : ℂ => ζ⁻¹) (((-ε : ℝ) : ℂ) - (ε : ℂ) * I)
    ((ε : ℂ) + (ε : ℂ) * I) u₀
  rw [ht]
  have h0 := rectIntegral_inv_sub (a₁ := -ε) (c₀ := 0) (a₂ := ε) (b := ε) (by linarith) hε hε
  simpa using h0

private lemma rectIntegral_inv_sub_pow_eq_zero (u₀ : ℂ) {z w : ℂ}
    (hb : ∀ x ∈ Set.uIcc z.re w.re, ((x : ℂ) + (z.im : ℂ) * I) ≠ u₀)
    (ht : ∀ x ∈ Set.uIcc z.re w.re, ((x : ℂ) + (w.im : ℂ) * I) ≠ u₀)
    (hr : ∀ y ∈ Set.uIcc z.im w.im, ((w.re : ℂ) + (y : ℂ) * I) ≠ u₀)
    (hl : ∀ y ∈ Set.uIcc z.im w.im, ((z.re : ℂ) + (y : ℂ) * I) ≠ u₀)
    {p : ℕ} (hp : 2 ≤ p) :
    rectIntegral (fun ζ => ((ζ - u₀) ^ p)⁻¹) z w = 0 := by
  let F : ℂ → ℂ := fun ζ => (-((p - 1 : ℕ) : ℂ))⁻¹ * ((ζ - u₀) ^ (p - 1))⁻¹
  have hp1_ne : ((p - 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show p - 1 ≠ 0 by omega)
  have hderiv : ∀ ζ : ℂ, ζ ≠ u₀ → HasDerivAt F (((ζ - u₀) ^ p)⁻¹) ζ := fun ζ hne => by
    have hsub : ζ - u₀ ≠ 0 := sub_ne_zero.mpr hne
    have hd1 : HasDerivAt (fun ξ : ℂ => (ξ - u₀) ^ (p - 1))
        (((p - 1 : ℕ) : ℂ) * (ζ - u₀) ^ (p - 1 - 1)) ζ := by
      simpa using ((hasDerivAt_id ζ).sub_const u₀).fun_pow (p - 1)
    have hd2 : HasDerivAt (fun ξ : ℂ => ((ξ - u₀) ^ (p - 1))⁻¹)
        (-(((p - 1 : ℕ) : ℂ) * (ζ - u₀) ^ (p - 1 - 1)) / ((ζ - u₀) ^ (p - 1)) ^ 2) ζ :=
      hd1.inv (pow_ne_zero (p - 1) hsub)
    have hd3 := hd2.const_mul (-((p - 1 : ℕ) : ℂ))⁻¹
    convert hd3 using 1
    have hpow_p : (ζ - u₀) ^ p = (ζ - u₀) ^ (p - 1 - 1) * (ζ - u₀) ^ 2 := by
      rw [← pow_add]; congr 1; omega
    have hpow_sq : ((ζ - u₀) ^ (p - 1)) ^ 2 = (ζ - u₀) ^ (p - 1 - 1) * (ζ - u₀) ^ p := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    have h1 : (ζ - u₀) ^ (p - 1 - 1) ≠ 0 := pow_ne_zero _ hsub
    have h2 : (ζ - u₀) ^ p ≠ 0 := pow_ne_zero _ hsub
    rw [hpow_sq]
    field_simp [hp1_ne, h1, h2]
  have hcont_on : ∀ {a b : ℝ} {γ : ℝ → ℂ}, Continuous γ → (∀ t ∈ Set.uIcc a b, γ t ≠ u₀) →
      IntervalIntegrable (fun t => ((γ t - u₀) ^ p)⁻¹) volume a b := by
    intro a b γ hγ hne
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ (ContinuousOn.pow (hγ.continuousOn.sub continuousOn_const) p) fun t ht => ?_
    exact pow_ne_zero p (sub_ne_zero.mpr (hne t ht))
  exact rectIntegral_eq_zero_of_primitive
    (fun x hx => hderiv _ (hb x hx))
    (fun x hx => hderiv _ (ht x hx))
    (fun y hy => hderiv _ (hr y hy))
    (fun y hy => hderiv _ (hl y hy))
    (hcont_on (by fun_prop) hb)
    (hcont_on (by fun_prop) ht)
    (hcont_on (by fun_prop) hr)
    (hcont_on (by fun_prop) hl)

/-- Entire Taylor remainder `expTail c r w = ∑_{n ≥ 0} c^(n+r) / (n+r)! * w^n`. -/
@[expose] def expTail (c : ℂ) (r : ℕ) (w : ℂ) : ℂ :=
  ∑' n : ℕ, c ^ (n + r) / ((n + r).factorial : ℂ) * w ^ n

private lemma summable_expTail (c : ℂ) (r : ℕ) (w : ℂ) :
    Summable (fun n : ℕ => c ^ (n + r) / ((n + r).factorial : ℂ) * w ^ n) := by
  have hsum : Summable (fun n : ℕ => ‖c‖ ^ (n + r) / ((n + r).factorial : ℝ) * ‖w‖ ^ n) := by
    have hexp : Summable (fun m : ℕ => (‖c‖ * max 1 ‖w‖) ^ m / (m.factorial : ℝ)) := by
      simpa [div_eq_mul_inv] using Real.summable_pow_div_factorial (‖c‖ * max 1 ‖w‖)
    have hshift := (summable_nat_add_iff r).mpr hexp
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hshift
    rw [mul_pow]
    have hw_le : ‖w‖ ^ n ≤ (max 1 ‖w‖) ^ (n + r) := by
      calc ‖w‖ ^ n ≤ (max 1 ‖w‖) ^ n := pow_le_pow_left₀ (norm_nonneg _) (le_max_right 1 ‖w‖) n
        _ ≤ (max 1 ‖w‖) ^ (n + r) := pow_le_pow_right₀ (le_max_left 1 ‖w‖) (Nat.le_add_right n r)
    calc ‖c‖ ^ (n + r) / ((n + r).factorial : ℝ) * ‖w‖ ^ n
        = ‖c‖ ^ (n + r) * ‖w‖ ^ n / ((n + r).factorial : ℝ) := by ring
      _ ≤ ‖c‖ ^ (n + r) * (max 1 ‖w‖) ^ (n + r) / ((n + r).factorial : ℝ) := by gcongr
  refine Summable.of_norm_bounded hsum fun n => ?_
  rw [norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_natCast]

private lemma expTail_differentiable (c : ℂ) (r : ℕ) : Differentiable ℂ (expTail c r) := by
  intro w₀
  let R : ℝ := ‖w₀‖ + 2
  have hmem : w₀ ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]; dsimp only [R]; linarith
  have hbound_sum : Summable (fun n : ℕ => ‖c‖ ^ (n + r) / ((n + r).factorial : ℝ) * R ^ n) := by
    have hexp : Summable (fun m : ℕ => (‖c‖ * max 1 R) ^ m / (m.factorial : ℝ)) := by
      simpa [div_eq_mul_inv] using Real.summable_pow_div_factorial (‖c‖ * max 1 R)
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_nat_add_iff r).mpr hexp)
    rw [mul_pow]
    have hR_le : R ^ n ≤ (max 1 R) ^ (n + r) := by
      calc R ^ n ≤ (max 1 R) ^ n := pow_le_pow_left₀ (by dsimp only [R]; positivity) (le_max_right 1 R) n
        _ ≤ (max 1 R) ^ (n + r) := pow_le_pow_right₀ (le_max_left 1 R) (Nat.le_add_right n r)
    calc ‖c‖ ^ (n + r) / ((n + r).factorial : ℝ) * R ^ n
        = ‖c‖ ^ (n + r) * R ^ n / ((n + r).factorial : ℝ) := by ring
      _ ≤ ‖c‖ ^ (n + r) * (max 1 R) ^ (n + r) / ((n + r).factorial : ℝ) := by gcongr
  have hunif : TendstoUniformlyOn
      (fun N w => ∑ n ∈ Finset.range N, c ^ (n + r) / ((n + r).factorial : ℂ) * w ^ n)
      (expTail c r) atTop (Metric.ball (0 : ℂ) R) := by
    refine tendstoUniformlyOn_tsum_nat hbound_sum fun n w hw => ?_
    have hwR : ‖w‖ ≤ R := le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hw)
    rw [norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hwR n) (by positivity)
  have hdiff_ball : DifferentiableOn ℂ (expTail c r) (Metric.ball (0 : ℂ) R) :=
    hunif.tendstoLocallyUniformlyOn.differentiableOn
      (Filter.Eventually.of_forall fun N => DifferentiableOn.fun_sum fun n _ => by fun_prop)
      Metric.isOpen_ball
  exact (hdiff_ball w₀ hmem).differentiableAt (Metric.isOpen_ball.mem_nhds hmem)

private lemma exp_eq_taylor_add_expTail (c : ℂ) (r : ℕ) (w : ℂ) :
    Complex.exp (c * w) =
      (∑ m ∈ Finset.range r, c ^ m / (m.factorial : ℂ) * w ^ m) + w ^ r * expTail c r w := by
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div (𝔸 := ℂ)]
  dsimp only
  have hsum : Summable (fun m : ℕ => (c * w) ^ m / (m.factorial : ℂ)) := by
    refine Summable.of_norm_bounded (g := fun m => ‖c * w‖ ^ m / (m.factorial : ℝ))
      (by simpa [div_eq_mul_inv] using Real.summable_pow_div_factorial ‖c * w‖) fun m => ?_
    rw [norm_div, norm_pow, Complex.norm_natCast]
  rw [← hsum.sum_add_tsum_nat_add r]
  congr 1
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_pow]; ring
  · unfold expTail
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [mul_pow, pow_add w n r]; ring

/-- Exact residue integral of `exp (c * u) / (u - u₀)^r` around a centered square of half-side `ε > 0`. -/
private lemma rectIntegral_exp_div_pow (c u₀ : ℂ) {ε : ℝ} (hε : 0 < ε) {r : ℕ} (hr : 1 ≤ r) :
    rectIntegral (fun u => Complex.exp (c * u) / (u - u₀) ^ r)
      (u₀ - (ε : ℂ) - (ε : ℂ) * I) (u₀ + (ε : ℂ) + (ε : ℂ) * I) =
      2 * (Real.pi : ℂ) * I * Complex.exp (c * u₀) * c ^ (r - 1) / ((r - 1).factorial : ℂ) := by
  let z := u₀ - (ε : ℂ) - (ε : ℂ) * I
  let w := u₀ + (ε : ℂ) + (ε : ℂ) * I
  have hz_re : z.re = u₀.re - ε := by dsimp only [z]; simp
  have hz_im : z.im = u₀.im - ε := by dsimp only [z]; simp
  have hw_re : w.re = u₀.re + ε := by dsimp only [w]; simp
  have hw_im : w.im = u₀.im + ε := by dsimp only [w]; simp
  have hb_ne : ∀ x ∈ Set.uIcc z.re w.re, ((x : ℂ) + (z.im : ℂ) * I) ≠ u₀ := fun x _ h0 => by
    have him := congrArg Complex.im h0; simp [hz_im] at him; linarith
  have ht_ne : ∀ x ∈ Set.uIcc z.re w.re, ((x : ℂ) + (w.im : ℂ) * I) ≠ u₀ := fun x _ h0 => by
    have him := congrArg Complex.im h0; simp [hw_im] at him; linarith
  have hr_ne : ∀ y ∈ Set.uIcc z.im w.im, ((w.re : ℂ) + (y : ℂ) * I) ≠ u₀ := fun y _ h0 => by
    have hre := congrArg Complex.re h0; simp [hw_re] at hre; linarith
  have hl_ne : ∀ y ∈ Set.uIcc z.im w.im, ((z.re : ℂ) + (y : ℂ) * I) ≠ u₀ := fun y _ h0 => by
    have hre := congrArg Complex.re h0; simp [hz_re] at hre; linarith
  have hfactor : (fun u => Complex.exp (c * u) / (u - u₀) ^ r) =
      fun u => Complex.exp (c * u₀) * (Complex.exp (c * (u - u₀)) / (u - u₀) ^ r) := by
    funext u
    rw [show c * u = c * u₀ + c * (u - u₀) by ring, Complex.exp_add]; ring
  rw [hfactor, rectIntegral_const_mul]
  -- Split `exp(c(u - u₀)) / (u - u₀)^r` on boundary points `u ≠ u₀` using `exp_eq_taylor_add_expTail`.
  have hsplit_pt : ∀ u : ℂ, u ≠ u₀ →
      Complex.exp (c * (u - u₀)) / (u - u₀) ^ r =
        (∑ m ∈ Finset.range r, (c ^ m / (m.factorial : ℂ)) * ((u - u₀) ^ (r - m))⁻¹) +
          expTail c r (u - u₀) := fun u hne => by
    have hsub : u - u₀ ≠ 0 := sub_ne_zero.mpr hne
    rw [exp_eq_taylor_add_expTail c r (u - u₀), add_div, mul_div_cancel_left₀ _ (pow_ne_zero r hsub),
      Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    have hpow : (u - u₀) ^ r = (u - u₀) ^ m * (u - u₀) ^ (r - m) := by
      rw [← pow_add, Nat.add_sub_of_le (by omega)]
    rw [hpow]
    have h1 : (u - u₀) ^ m ≠ 0 := pow_ne_zero m hsub
    have h2 : (u - u₀) ^ (r - m) ≠ 0 := pow_ne_zero (r - m) hsub
    field_simp [h1, h2]
  have hcongr : rectIntegral (fun u => Complex.exp (c * (u - u₀)) / (u - u₀) ^ r) z w =
      rectIntegral (fun u => (∑ m ∈ Finset.range r, (c ^ m / (m.factorial : ℂ)) * ((u - u₀) ^ (r - m))⁻¹) +
        expTail c r (u - u₀)) z w :=
    rectIntegral_congr_boundary (fun x hx => hsplit_pt _ (hb_ne x hx))
      (fun x hx => hsplit_pt _ (ht_ne x hx))
      (fun y hy => hsplit_pt _ (hr_ne y hy))
      (fun y hy => hsplit_pt _ (hl_ne y hy))
  rw [hcongr]
  have hint_pow : ∀ (m : ℕ) {a b : ℝ} {γ : ℝ → ℂ}, Continuous γ → (∀ t ∈ Set.uIcc a b, γ t ≠ u₀) →
      IntervalIntegrable (fun t => (c ^ m / (m.factorial : ℂ)) * ((γ t - u₀) ^ (r - m))⁻¹) volume a b := by
    intro m a b γ hγ hne
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (ContinuousOn.inv₀
      (ContinuousOn.pow (hγ.continuousOn.sub continuousOn_const) _) fun t ht =>
      pow_ne_zero _ (sub_ne_zero.mpr (hne t ht)))
  have hint_sum : ∀ {a b : ℝ} {γ : ℝ → ℂ}, Continuous γ → (∀ t ∈ Set.uIcc a b, γ t ≠ u₀) →
      IntervalIntegrable (fun t => ∑ m ∈ Finset.range r, (c ^ m / (m.factorial : ℂ)) * ((γ t - u₀) ^ (r - m))⁻¹)
        volume a b := by
    intro a b γ hγ hne
    exact intervalIntegrable_finset_sum (Finset.range r)
      (fun m t => (c ^ m / (m.factorial : ℂ)) * ((γ t - u₀) ^ (r - m))⁻¹) _ _
      fun m _ => hint_pow m hγ hne
  have hint_tail : ∀ {a b : ℝ} {γ : ℝ → ℂ}, Continuous γ →
      IntervalIntegrable (fun t => expTail c r (γ t - u₀)) volume a b := by
    intro a b γ hγ
    exact ((expTail_differentiable c r).continuous.comp (hγ.sub continuous_const)).intervalIntegrable a b
  rw [rectIntegral_add (hint_sum (by fun_prop) hb_ne) (hint_tail (by fun_prop))
    (hint_sum (by fun_prop) ht_ne) (hint_tail (by fun_prop))
    (hint_sum (by fun_prop) hr_ne) (hint_tail (by fun_prop))
    (hint_sum (by fun_prop) hl_ne) (hint_tail (by fun_prop))]
  have htail_zero : rectIntegral (fun u => expTail c r (u - u₀)) z w = 0 :=
    rectIntegral_eq_zero_of_differentiableOn
      (((expTail_differentiable c r).comp (differentiable_id.sub (differentiable_const u₀))).differentiableOn)
  rw [htail_zero, add_zero, rectIntegral_finset_sum (Finset.range r) _ z w
    (fun m _ => hint_pow m (by fun_prop) hb_ne)
    (fun m _ => hint_pow m (by fun_prop) ht_ne)
    (fun m _ => hint_pow m (by fun_prop) hr_ne)
    (fun m _ => hint_pow m (by fun_prop) hl_ne)]
  have hsum_eval : ∑ m ∈ Finset.range r,
      rectIntegral (fun u => (c ^ m / (m.factorial : ℂ)) * ((u - u₀) ^ (r - m))⁻¹) z w =
      (c ^ (r - 1) / ((r - 1).factorial : ℂ)) * (2 * (Real.pi : ℂ) * I) := by
    rw [Finset.sum_eq_single (r - 1)]
    · rw [rectIntegral_const_mul, show r - (r - 1) = 1 by omega]
      simp only [pow_one]
      rw [rectIntegral_inv_sub_centered u₀ hε]
    · intro m hm hne
      rw [Finset.mem_range] at hm
      rw [rectIntegral_const_mul, rectIntegral_inv_sub_pow_eq_zero u₀ hb_ne ht_ne hr_ne hl_ne (by omega),
        mul_zero]
    · intro hmem; exfalso; exact hmem (Finset.mem_range.mpr (by omega))
  rw [hsum_eval]
  ring

/-! ### Pole Localization of `Ψ_b` in `[-1/2, 1/2] × [0, 2π / log 2]` -/

private lemma two_zpow_eq_cexp (m : ℤ) :
    (2 : ℂ) ^ m = Complex.exp ((m : ℂ) * ((Real.log 2 : ℝ) : ℂ)) := by
  have hreal : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
  have hcast := congrArg Complex.ofReal hreal
  simpa [Complex.ofReal_exp] using hcast

private lemma uPole_re : uPole.re = 0 := by
  unfold uPole
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]

private lemma uPole_im : uPole.im = Real.pi / Real.log 2 := by
  unfold uPole
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
    Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]

/-- Characterization of poles of `Ψ_b`: `u ∉ PsiDomain` iff `u.re ∈ ℤ` and `u.im ∈ (2ℤ + 1) π / log 2`. -/
private lemma not_mem_PsiDomain_iff (u : ℂ) :
    u ∉ PsiDomain ↔ ∃ m n : ℤ, u.re = (m : ℝ) ∧ u.im = -((2 * (n : ℝ) + 1) * Real.pi / Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2re : (2 : ℂ).re = 2 := rfl
  have h2im : (2 : ℂ).im = 0 := rfl
  change ¬ (∀ m : ℤ, 1 + (2 : ℂ) ^ m * Complex.exp (-((Real.log 2 : ℝ) : ℂ) * u) ≠ 0) ↔ _
  simp only [not_forall, not_ne_iff]
  constructor
  · rintro ⟨m, hm⟩
    have hexp_eq : Complex.exp (((m : ℂ) - u) * ((Real.log 2 : ℝ) : ℂ)) = Complex.exp ((Real.pi : ℂ) * I) := by
      rw [Complex.exp_pi_mul_I]
      have h1 : (2 : ℂ) ^ m * Complex.exp (-((Real.log 2 : ℝ) : ℂ) * u) = -1 := by linear_combination hm
      rw [two_zpow_eq_cexp, ← Complex.exp_add] at h1
      convert h1 using 2; ring
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp_eq
    refine ⟨m, n, ?_, ?_⟩
    · have hre := congrArg Complex.re hn
      simp only [Complex.mul_re, Complex.sub_re, Complex.intCast_re, Complex.ofReal_re,
        Complex.sub_im, Complex.intCast_im, Complex.ofReal_im, mul_zero, sub_zero,
        Complex.add_re, Complex.I_re, Complex.I_im, Complex.mul_im, mul_one, zero_add,
        h2re, h2im] at hre
      nlinarith
    · have him := congrArg Complex.im hn
      simp only [Complex.mul_im, Complex.sub_re, Complex.intCast_re, Complex.ofReal_re,
        Complex.sub_im, Complex.intCast_im, Complex.ofReal_im, mul_zero, add_zero, zero_sub,
        Complex.add_im, Complex.I_re, Complex.I_im, Complex.mul_re, mul_one, sub_zero,
        h2re, h2im, zero_add] at him
      have hlin : -u.im * Real.log 2 = (2 * (n : ℝ) + 1) * Real.pi := by linarith
      rw [eq_neg_iff_add_eq_zero]
      have hmul : (u.im + (2 * (n : ℝ) + 1) * Real.pi / Real.log 2) * Real.log 2 = 0 := by
        rw [add_mul, div_mul_cancel₀ _ hlog2.ne']; linarith
      exact (mul_eq_zero.mp hmul).resolve_right hlog2.ne'
  · rintro ⟨m, n, hre, him⟩
    refine ⟨m, ?_⟩
    have harg : ((m : ℂ) * ((Real.log 2 : ℝ) : ℂ)) + (-((Real.log 2 : ℝ) : ℂ) * u) =
        (Real.pi : ℂ) * I + (n : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.ofReal_re,
          Complex.intCast_im, Complex.ofReal_im, mul_zero, sub_zero, Complex.neg_re, Complex.neg_im,
          neg_zero, zero_mul, Complex.I_re, Complex.I_im, mul_one, add_zero, h2re, h2im,
          Complex.mul_im, hre]
        ring
      · simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.ofReal_im, mul_zero,
          Complex.intCast_im, Complex.ofReal_re, zero_mul, add_zero, Complex.neg_re, Complex.neg_im,
          neg_zero, zero_add, Complex.I_re, Complex.I_im, mul_one, h2re, h2im,
          Complex.mul_re, sub_zero]
        rw [him]
        field_simp [hlog2.ne']
        ring
    rw [two_zpow_eq_cexp, ← Complex.exp_add, harg, Complex.exp_add, Complex.exp_pi_mul_I,
      Complex.exp_int_mul_two_pi_mul_I]
    ring

/-- The entire open strip `|u.im| < π / log 2` is free of poles of `Ψ_b`. -/
lemma mem_PsiDomain_of_abs_im_lt {u : ℂ} (hu : |u.im| < Real.pi / Real.log 2) : u ∈ PsiDomain := by
  by_contra hnot
  obtain ⟨_, n, _, him⟩ := (not_mem_PsiDomain_iff u).mp hnot
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : |(2 * (n : ℝ) + 1)| ≥ 1 := by
    have hint : (1 : ℤ) ≤ |2 * n + 1| := Int.one_le_abs (by omega)
    exact_mod_cast hint
  have habs : |u.im| = |(2 * (n : ℝ) + 1)| * (Real.pi / Real.log 2) := by
    rw [him, abs_neg, mul_div_assoc, abs_mul, abs_of_pos (div_pos Real.pi_pos hlog2)]
  nlinarith [div_pos Real.pi_pos hlog2]

/-- Inside the closed fundamental rectangle `[-1/2, 1/2] × [0, 2π / log 2]`, the unique pole of `Ψ_b`
is `uPole = (π / log 2) * I`. -/
private lemma mem_PsiDomain_of_fundRect_ne_uPole {u : ℂ}
    (hre1 : -1 / 2 ≤ u.re) (hre2 : u.re ≤ 1 / 2)
    (him1 : 0 ≤ u.im) (him2 : u.im ≤ 2 * Real.pi / Real.log 2)
    (hne : u ≠ uPole) : u ∈ PsiDomain := by
  by_contra hnot
  obtain ⟨m, n, hre, him⟩ := (not_mem_PsiDomain_iff u).mp hnot
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm0 : m = 0 := by
    have h1 : (-1 : ℝ) < (m : ℝ) := by linarith
    have h2 : (m : ℝ) < (1 : ℝ) := by linarith
    have h1' : (-1 : ℤ) < m := by exact_mod_cast h1
    have h2' : m < (1 : ℤ) := by exact_mod_cast h2
    omega
  have hn1 : n = -1 := by
    have hpi_pos : 0 < Real.pi / Real.log 2 := div_pos Real.pi_pos hlog2
    have h1 : 0 ≤ -(2 * (n : ℝ) + 1) := by
      have : 0 ≤ -(2 * (n : ℝ) + 1) * (Real.pi / Real.log 2) := by
        have hrew : -(2 * (n : ℝ) + 1) * (Real.pi / Real.log 2) = -((2 * (n : ℝ) + 1) * Real.pi / Real.log 2) := by ring
        linarith
      exact nonneg_of_mul_nonneg_left this hpi_pos
    have h2 : -(2 * (n : ℝ) + 1) ≤ 2 := by
      have : -(2 * (n : ℝ) + 1) * (Real.pi / Real.log 2) ≤ 2 * (Real.pi / Real.log 2) := by
        have hrew : -(2 * (n : ℝ) + 1) * (Real.pi / Real.log 2) = -((2 * (n : ℝ) + 1) * Real.pi / Real.log 2) := by ring
        have hrew2 : 2 * (Real.pi / Real.log 2) = 2 * Real.pi / Real.log 2 := by ring
        linarith
      exact le_of_mul_le_mul_right this hpi_pos
    have h1' : (0 : ℤ) ≤ -(2 * n + 1) := by exact_mod_cast h1
    have h2' : -(2 * n + 1) ≤ (2 : ℤ) := by exact_mod_cast h2
    omega
  apply hne
  apply Complex.ext
  · rw [hre, hm0, Int.cast_zero]; unfold uPole; simp only [Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]
  · rw [him, hn1]; unfold uPole; simp only [Int.cast_neg, Int.cast_one, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    ring

/-! ### Exact Fourier Coefficients `Ψ̂_b(k)` via Single Rectangle Residue Integral -/

/-- Half-nome `qHalf = exp(-2π² / log 2) = q^(1/2) ∈ (0, 1)`. -/
@[expose] def qHalf : ℝ := Real.exp (-2 * Real.pi ^ 2 / Real.log 2)

lemma qHalf_pos : 0 < qHalf := Real.exp_pos _

lemma qHalf_lt_one : qHalf < 1 := by
  unfold qHalf
  rw [Real.exp_lt_one_iff]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  exact div_neg_of_neg_of_pos (by linarith) hlog2

/-- Imaginary Mellin frequency `χ_k = (2π k / log 2) * I`. -/
@[expose] def chiFR (k : ℤ) : ℂ := ((2 * Real.pi * (k : ℝ) / Real.log 2 : ℝ) : ℂ) * I

/-- `k`-th Fourier coefficient of `Ψ_b` on `[-1/2, 1/2]`. -/
@[expose] def Psi_hat (b : ℕ) (k : ℤ) : ℂ :=
  ∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
    Psi_b b (t : ℂ) * Complex.exp (-2 * (Real.pi : ℂ) * I * (k : ℂ) * (t : ℂ))

/-- Exact polynomial `Q_b(s)` of degree `b - 2` governing the Fourier coefficients of `Φ_b`. -/
@[expose] def Q_b (b : ℕ) : Polynomial ℂ :=
  ∑ r ∈ Finset.Icc 2 b,
    Polynomial.C (laurentC b r * (-((Real.log 2 : ℝ) : ℂ)) ^ (r - 1) / (((r - 1).factorial : ℕ) : ℂ)) *
      Polynomial.X ^ (r - 2)

lemma Q_b_coeff_top {b : ℕ} (hb : 2 ≤ b) :
    (Q_b b).coeff (b - 2) =
      (-1 : ℂ) ^ (b - 1) * (K_b b : ℂ) / ((((b - 1).factorial : ℕ) : ℂ) * ((Real.log 2 : ℝ) : ℂ)) := by
  unfold Q_b
  change (Polynomial.lcoeff ℂ (b - 2)) _ = _
  rw [map_sum, Finset.sum_eq_single b]
  · simp only [Polynomial.lcoeff_apply]
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one, laurentC_top hb]
    have hlog_ne : ((Real.log 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
    have hfac_ne : (((b - 1).factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (b - 1)
    rw [neg_eq_neg_one_mul, mul_pow]
    have hpow : ((Real.log 2 : ℝ) : ℂ) ^ b =
        ((Real.log 2 : ℝ) : ℂ) ^ (b - 1) * ((Real.log 2 : ℝ) : ℂ) := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [hpow]
    have hpow_ne : ((Real.log 2 : ℝ) : ℂ) ^ (b - 1) ≠ 0 := pow_ne_zero _ hlog_ne
    field_simp [hlog_ne, hfac_ne, hpow_ne]
  · intro r hr hne
    rw [Finset.mem_Icc] at hr
    simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      show ¬ (b - 2 = r - 2) by omega, ↓reduceIte, mul_zero]
  · intro hmem; exfalso; exact hmem (Finset.mem_Icc.mpr ⟨hb, le_rfl⟩)

lemma Q_b_ne_zero {b : ℕ} (hb : 2 ≤ b) : Q_b b ≠ 0 := by
  intro h0
  have hc := congrArg (fun P : Polynomial ℂ => P.coeff (b - 2)) h0
  rw [Polynomial.coeff_zero, Q_b_coeff_top hb] at hc
  have hnum : (-1 : ℂ) ^ (b - 1) * (K_b b : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (Complex.ofReal_ne_zero.mpr (K_b_pos b hb).ne')
  have hden : (((b - 1).factorial : ℕ) : ℂ) * ((Real.log 2 : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (b - 1))
      (Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne')
  exact div_ne_zero hnum hden hc

lemma Q_b_natDegree {b : ℕ} (hb : 2 ≤ b) : (Q_b b).natDegree = b - 2 := by
  refine le_antisymm ?_ ?_
  · unfold Q_b
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun r hr => ?_
    rw [Finset.mem_Icc] at hr
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [Q_b_coeff_top hb]
    exact div_ne_zero
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (Complex.ofReal_ne_zero.mpr (K_b_pos b hb).ne'))
      (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (b - 1))
        (Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'))

private lemma qHalf_zpow_eq_cexp (k : ℤ) :
    (qHalf : ℂ) ^ k = Complex.exp (-2 * (Real.pi : ℂ) ^ 2 * (k : ℂ) / ((Real.log 2 : ℝ) : ℂ)) := by
  have hreal : qHalf ^ k = Real.exp (-2 * Real.pi ^ 2 * (k : ℝ) / Real.log 2) := by
    unfold qHalf
    rw [← Real.rpow_intCast, ← Real.exp_mul]
    congr 1; ring
  have hcast := congrArg Complex.ofReal hreal
  simpa [Complex.ofReal_exp] using hcast

lemma sin_pi_mul_chiFR (k : ℤ) :
    2 * I * Complex.sin ((Real.pi : ℂ) * chiFR k) = (qHalf : ℂ) ^ k - (qHalf : ℂ) ^ (-k) := by
  rw [Complex.sin]
  have h1 : (Real.pi : ℂ) * chiFR k * I = -2 * (Real.pi : ℂ) ^ 2 * (k : ℂ) / ((Real.log 2 : ℝ) : ℂ) := by
    unfold chiFR
    push_cast
    have hI2 : I * I = -1 := Complex.I_mul_I
    calc (Real.pi : ℂ) * ((2 * (Real.pi : ℂ) * (k : ℂ) / ((Real.log 2 : ℝ) : ℂ)) * I) * I
        = (2 * (Real.pi : ℂ) ^ 2 * (k : ℂ) / ((Real.log 2 : ℝ) : ℂ)) * (I * I) := by ring
      _ = -2 * (Real.pi : ℂ) ^ 2 * (k : ℂ) / ((Real.log 2 : ℝ) : ℂ) := by rw [hI2]; ring
  have h2 : -((Real.pi : ℂ) * chiFR k) * I = -2 * (Real.pi : ℂ) ^ 2 * ((-k : ℤ) : ℂ) / ((Real.log 2 : ℝ) : ℂ) := by
    rw [neg_mul, h1]; push_cast; ring
  rw [h1, h2, ← qHalf_zpow_eq_cexp k, ← qHalf_zpow_eq_cexp (-k)]
  have hI2 : I * I = -1 := Complex.I_mul_I
  calc 2 * I * (((qHalf : ℂ) ^ (-k) - (qHalf : ℂ) ^ k) * I / 2)
      = ((qHalf : ℂ) ^ (-k) - (qHalf : ℂ) ^ k) * (I * I) := by ring
    _ = (qHalf : ℂ) ^ k - (qHalf : ℂ) ^ (-k) := by rw [hI2]; ring

/-- Single rectangle Cauchy residue identity for `Ψ_b(u) e^{-2π i k u}` on `[-1/2, 1/2] × [0, 2π / log 2]`. -/
private lemma Psi_hat_residue_eq {b : ℕ} (hb : 2 ≤ b) (k : ℤ) :
    (1 - (qHalf : ℂ) ^ (-2 * k)) * Psi_hat b k =
      2 * (Real.pi : ℂ) * I * (qHalf : ℂ) ^ (-k) *
        ∑ r ∈ Finset.Icc 1 b, laurentC b r * (-2 * (Real.pi : ℂ) * I * (k : ℂ)) ^ (r - 1) /
          (((r - 1).factorial : ℕ) : ℂ) := by
  let f : ℂ → ℂ := fun u => Psi_b b u * Complex.exp (-2 * (Real.pi : ℂ) * I * (k : ℂ) * u)
  let T : ℝ := 2 * Real.pi / Real.log 2
  let y₀ : ℝ := Real.pi / Real.log 2
  let ε : ℝ := 1 / 32
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt1 : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]
  have hy₀_gt3 : (3 : ℝ) < y₀ := by
    dsimp only [y₀]
    rw [lt_div_iff₀ hlog2_pos]
    linarith [Real.pi_gt_three]
  have hT_eq : T = 2 * y₀ := by dsimp only [T, y₀]; ring
  have hf_diff : DifferentiableOn ℂ f PsiDomain :=
    (Psi_b_differentiableOn (by omega : 1 ≤ b)).mul (by fun_prop)
  -- Helper: any closed rectangle contained in `PsiDomain` has continuous edges and zero `rectIntegral`.
  have hint_edge_h : ∀ {x₁ x₂ y : ℝ},
      (∀ x ∈ Set.uIcc x₁ x₂, ((x : ℂ) + (y : ℂ) * I) ∈ PsiDomain) →
      IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (y : ℂ) * I)) volume x₁ x₂ := by
    intro x₁ x₂ y hmem
    refine ContinuousOn.intervalIntegrable ?_
    exact (hf_diff.continuousOn.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + (y : ℂ) * I).continuousOn
      fun x hx => hmem x hx)
  have hint_edge_v : ∀ {x y₁ y₂ : ℝ},
      (∀ y ∈ Set.uIcc y₁ y₂, ((x : ℂ) + (y : ℂ) * I) ∈ PsiDomain) →
      IntervalIntegrable (fun y : ℝ => f ((x : ℂ) + (y : ℂ) * I)) volume y₁ y₂ := by
    intro x y₁ y₂ hmem
    refine ContinuousOn.intervalIntegrable ?_
    exact (hf_diff.continuousOn.comp (by fun_prop : Continuous fun y : ℝ => (x : ℂ) + (y : ℂ) * I).continuousOn
      fun y hy => hmem y hy)
  -- Step 1: Evaluate LHS `rectIntegral f (-1/2 + 0*I) (1/2 + T*I)`.
  have hLHS : rectIntegral f (((-1 / 2 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I)
      (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * I) = (1 - (qHalf : ℂ) ^ (-2 * k)) * Psi_hat b k := by
    unfold rectIntegral
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one,
      zero_add, Complex.ofReal_zero, zero_mul]
    -- Vertical edges cancel by `Psi_b_add_one`!
    have hvert : (∫ y : ℝ in (0 : ℝ)..T, f (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) =
        ∫ y : ℝ in (0 : ℝ)..T, f (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
      refine intervalIntegral.integral_congr fun y _ => ?_
      dsimp only [f]
      have harg : (((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) = (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) + 1 := by
        push_cast; ring
      rw [harg, Psi_b_add_one b, mul_add, Complex.exp_add,
        show -2 * (Real.pi : ℂ) * I * (k : ℂ) * 1 = ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) by
          push_cast; ring,
        Complex.exp_int_mul_two_pi_mul_I, mul_one]
    -- Top edge equals `qHalf^(-2k) * bottom edge` by `Psi_b_add_tau`!
    have htop : (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ), f ((x : ℂ) + (T : ℂ) * I)) =
        (qHalf : ℂ) ^ (-2 * k) * Psi_hat b k := by
      unfold Psi_hat
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => ?_
      dsimp only [f]
      have htau : (T : ℂ) * I = tauFR := rfl
      rw [htau, Psi_b_add_tau b, mul_add, Complex.exp_add]
      have hexp_tau : Complex.exp (-2 * (Real.pi : ℂ) * I * (k : ℂ) * tauFR) =
          (qHalf : ℂ) ^ (-2 * k) := by
        rw [qHalf_zpow_eq_cexp (-2 * k)]
        congr 1
        unfold tauFR
        rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat, Int.cast_mul,
          Int.cast_neg, Int.cast_ofNat]
        have hI2 : I * I = -1 := Complex.I_mul_I
        calc -2 * (Real.pi : ℂ) * I * (k : ℂ) * (2 * (Real.pi : ℂ) / ((Real.log 2 : ℝ) : ℂ) * I)
            = -(4 * (Real.pi : ℂ) ^ 2 * (k : ℂ) / ((Real.log 2 : ℝ) : ℂ)) * (I * I) := by ring
          _ = -2 * (Real.pi : ℂ) ^ 2 * (-2 * (k : ℂ)) / ((Real.log 2 : ℝ) : ℂ) := by rw [hI2]; ring
      rw [hexp_tau]; ring
    rw [hvert, htop]
    change Psi_hat b k - (qHalf : ℂ) ^ (-2 * k) * Psi_hat b k +
        I * (∫ y in (0 : ℝ)..T, f (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) -
        I * (∫ y in (0 : ℝ)..T, f (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) = _
    ring
  -- Step 2: Punch out the inner square `[-ε, ε] × [y₀ - ε, y₀ + ε]` around `uPole`.
  have hmem_top' : ∀ x : ℝ, -1 / 2 ≤ x → x ≤ 1 / 2 → ((x : ℂ) + (T : ℂ) * I) ∈ PsiDomain :=
    fun x hx1 hx2 => mem_PsiDomain_of_fundRect_ne_uPole (by simpa using hx1) (by simpa using hx2)
      (by simp; dsimp only [T]; positivity) (by simp; rfl)
      (fun h0 => by
        have him := congrArg Complex.im h0
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, uPole_im] at him
        dsimp only [T] at him; linarith [div_pos Real.pi_pos hlog2_pos])
  have hsplit1 : rectIntegral f (((-1 / 2 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * I) =
      rectIntegral f (((-1 / 2 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) (((-ε : ℝ) : ℂ) + (T : ℂ) * I) +
      rectIntegral f (((-ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * I) :=
    rectIntegral_hsplit
      (hint_edge_h fun x _ => mem_PsiDomain_of_abs_im_lt (by simp [div_pos Real.pi_pos hlog2_pos]))
      (hint_edge_h fun x _ => mem_PsiDomain_of_abs_im_lt (by simp [div_pos Real.pi_pos hlog2_pos]))
      (hint_edge_h fun x hx => by
        rw [Set.uIcc_of_le (by dsimp only [ε]; norm_num)] at hx
        exact hmem_top' x hx.1 (by dsimp only [ε] at hx; linarith [hx.2]))
      (hint_edge_h fun x hx => by
        rw [Set.uIcc_of_le (by dsimp only [ε]; norm_num)] at hx
        exact hmem_top' x (by dsimp only [ε] at hx; linarith [hx.1]) hx.2)
  have hsplit2 : rectIntegral f (((-ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * I) =
      rectIntegral f (((-ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) ((ε : ℂ) + (T : ℂ) * I) +
      rectIntegral f ((ε : ℂ) + ((0 : ℝ) : ℂ) * I) (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * I) :=
    rectIntegral_hsplit
      (hint_edge_h fun x _ => mem_PsiDomain_of_abs_im_lt (by simp [div_pos Real.pi_pos hlog2_pos]))
      (hint_edge_h fun x _ => mem_PsiDomain_of_abs_im_lt (by simp [div_pos Real.pi_pos hlog2_pos]))
      (hint_edge_h fun x hx => by
        rw [Set.uIcc_of_le (by dsimp only [ε]; norm_num)] at hx
        exact hmem_top' x (by dsimp only [ε] at hx; linarith [hx.1]) (by dsimp only [ε] at hx; linarith [hx.2]))
      (hint_edge_h fun x hx => by
        rw [Set.uIcc_of_le (by dsimp only [ε]; norm_num)] at hx
        exact hmem_top' x (by dsimp only [ε] at hx; linarith [hx.1]) hx.2)
  have hmem_v : ∀ x : ℝ, (x = -ε ∨ x = ε) → ∀ y : ℝ, 0 ≤ y → y ≤ T → ((x : ℂ) + (y : ℂ) * I) ∈ PsiDomain :=
    fun x hx y hy1 hy2 => mem_PsiDomain_of_fundRect_ne_uPole
      (by simp; rcases hx with rfl | rfl <;> (dsimp only [ε]; norm_num))
      (by simp; rcases hx with rfl | rfl <;> (dsimp only [ε]; norm_num))
      (by simpa using hy1) (by simpa using hy2)
      (fun h0 => by
        have hre := congrArg Complex.re h0
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, uPole_re] at hre
        rcases hx with rfl | rfl <;> (dsimp only [ε] at hre; norm_num at hre))
  have hsplit3 : rectIntegral f (((-ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) ((ε : ℂ) + (T : ℂ) * I) =
      rectIntegral f (((-ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) ((ε : ℂ) + ((y₀ - ε : ℝ) : ℂ) * I) +
      rectIntegral f (((-ε : ℝ) : ℂ) + ((y₀ - ε : ℝ) : ℂ) * I) ((ε : ℂ) + (T : ℂ) * I) :=
    rectIntegral_vsplit
      (hint_edge_v fun y hy => by
        rw [Set.uIcc_of_le (by dsimp only [ε]; linarith)] at hy
        exact hmem_v ε (Or.inr rfl) y hy.1 (by dsimp only [ε] at hy; linarith [hy.2]))
      (hint_edge_v fun y hy => by
        rw [Set.uIcc_of_le (by dsimp only [ε]; linarith)] at hy
        exact hmem_v ε (Or.inr rfl) y (by dsimp only [ε] at hy; linarith [hy.1]) hy.2)
      (hint_edge_v fun y hy => by
        rw [Set.uIcc_of_le (by dsimp only [ε]; linarith)] at hy
        exact hmem_v (-ε) (Or.inl rfl) y hy.1 (by dsimp only [ε] at hy; linarith [hy.2]))
      (hint_edge_v fun y hy => by
        rw [Set.uIcc_of_le (by dsimp only [ε]; linarith)] at hy
        exact hmem_v (-ε) (Or.inl rfl) y (by dsimp only [ε] at hy; linarith [hy.1]) hy.2)
  have hsplit4 : rectIntegral f (((-ε : ℝ) : ℂ) + ((y₀ - ε : ℝ) : ℂ) * I) ((ε : ℂ) + (T : ℂ) * I) =
      rectIntegral f (((-ε : ℝ) : ℂ) + ((y₀ - ε : ℝ) : ℂ) * I) ((ε : ℂ) + ((y₀ + ε : ℝ) : ℂ) * I) +
      rectIntegral f (((-ε : ℝ) : ℂ) + ((y₀ + ε : ℝ) : ℂ) * I) ((ε : ℂ) + (T : ℂ) * I) :=
    rectIntegral_vsplit
      (hint_edge_v fun y hy => by
        rw [Set.uIcc_of_le (by dsimp only [ε]; linarith)] at hy
        exact hmem_v ε (Or.inr rfl) y (by dsimp only [ε] at hy; linarith [hy.1]) (by dsimp only [ε] at hy; linarith [hy.2]))
      (hint_edge_v fun y hy => by
        rw [Set.uIcc_of_le (by dsimp only [ε]; linarith)] at hy
        exact hmem_v ε (Or.inr rfl) y (by dsimp only [ε] at hy; linarith [hy.1]) hy.2)
      (hint_edge_v fun y hy => by
        rw [Set.uIcc_of_le (by dsimp only [ε]; linarith)] at hy
        exact hmem_v (-ε) (Or.inl rfl) y (by dsimp only [ε] at hy; linarith [hy.1]) (by dsimp only [ε] at hy; linarith [hy.2]))
      (hint_edge_v fun y hy => by
        rw [Set.uIcc_of_le (by dsimp only [ε]; linarith)] at hy
        exact hmem_v (-ε) (Or.inl rfl) y (by dsimp only [ε] at hy; linarith [hy.1]) hy.2)
  -- The four outer sub-rectangles avoid `uPole`, hence lie in `PsiDomain`, so their integrals vanish!
  have hzero_left : rectIntegral f (((-1 / 2 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) (((-ε : ℝ) : ℂ) + (T : ℂ) * I) = 0 := by
    refine rectIntegral_eq_zero_of_differentiableOn (hf_diff.mono fun u hu => ?_)
    simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      mul_one, zero_add] at hu
    rw [Set.uIcc_of_le (by dsimp only [ε]; norm_num), Set.uIcc_of_le (by dsimp only [T]; positivity)] at hu
    exact mem_PsiDomain_of_fundRect_ne_uPole hu.1.1 (by dsimp only [ε] at hu; linarith [hu.1.2]) hu.2.1 hu.2.2
      (fun h0 => by have hre := congrArg Complex.re h0; rw [uPole_re] at hre; dsimp only [ε] at hu; linarith [hu.1.2])
  have hzero_right : rectIntegral f ((ε : ℂ) + ((0 : ℝ) : ℂ) * I) (((1 / 2 : ℝ) : ℂ) + (T : ℂ) * I) = 0 := by
    refine rectIntegral_eq_zero_of_differentiableOn (hf_diff.mono fun u hu => ?_)
    simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      mul_one, zero_add] at hu
    rw [Set.uIcc_of_le (by dsimp only [ε]; norm_num), Set.uIcc_of_le (by dsimp only [T]; positivity)] at hu
    exact mem_PsiDomain_of_fundRect_ne_uPole (by dsimp only [ε] at hu; linarith [hu.1.1]) hu.1.2 hu.2.1 hu.2.2
      (fun h0 => by have hre := congrArg Complex.re h0; rw [uPole_re] at hre; dsimp only [ε] at hu; linarith [hu.1.1])
  have hzero_bot : rectIntegral f (((-ε : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) ((ε : ℂ) + ((y₀ - ε : ℝ) : ℂ) * I) = 0 := by
    refine rectIntegral_eq_zero_of_differentiableOn (hf_diff.mono fun u hu => ?_)
    simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      mul_one, zero_add] at hu
    rw [Set.uIcc_of_le (by dsimp only [ε]; norm_num), Set.uIcc_of_le (by dsimp only [ε]; linarith)] at hu
    exact mem_PsiDomain_of_fundRect_ne_uPole (by dsimp only [ε] at hu; linarith [hu.1.1])
      (by dsimp only [ε] at hu; linarith [hu.1.2]) hu.2.1 (by dsimp only [ε] at hu; linarith [hu.2.2])
      (fun h0 => by have him := congrArg Complex.im h0; rw [uPole_im] at him; dsimp only [ε, y₀] at hu; linarith [hu.2.2])
  have hzero_top : rectIntegral f (((-ε : ℝ) : ℂ) + ((y₀ + ε : ℝ) : ℂ) * I) ((ε : ℂ) + (T : ℂ) * I) = 0 := by
    refine rectIntegral_eq_zero_of_differentiableOn (hf_diff.mono fun u hu => ?_)
    simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      mul_one, zero_add] at hu
    rw [Set.uIcc_of_le (by dsimp only [ε]; norm_num), Set.uIcc_of_le (by dsimp only [ε]; linarith)] at hu
    exact mem_PsiDomain_of_fundRect_ne_uPole (by dsimp only [ε] at hu; linarith [hu.1.1])
      (by dsimp only [ε] at hu; linarith [hu.1.2]) (by dsimp only [ε] at hu; linarith [hu.2.1]) hu.2.2
      (fun h0 => by have him := congrArg Complex.im h0; rw [uPole_im] at him; dsimp only [ε, y₀] at hu; linarith [hu.2.1])
  have hinner_eq : (1 - (qHalf : ℂ) ^ (-2 * k)) * Psi_hat b k =
      rectIntegral f (uPole - (ε : ℂ) - (ε : ℂ) * I) (uPole + (ε : ℂ) + (ε : ℂ) * I) := by
    rw [← hLHS, hsplit1, hzero_left, zero_add, hsplit2, hzero_right, add_zero,
      hsplit3, hzero_bot, zero_add, hsplit4, hzero_top, add_zero]
    congr 1 <;> (unfold uPole; dsimp only [y₀]; push_cast; ring)
  rw [hinner_eq]
  -- Step 3: Evaluate the inner square integral using `Psi_b_laurent_at_uPole` and `rectIntegral_exp_div_pow`.
  let z := uPole - (ε : ℂ) - (ε : ℂ) * I
  let w := uPole + (ε : ℂ) + (ε : ℂ) * I
  have hz_re : z.re = -ε := by dsimp only [z]; simp [uPole_re]
  have hz_im : z.im = y₀ - ε := by dsimp only [z]; simp [uPole_im, y₀]
  have hw_re : w.re = ε := by dsimp only [w]; simp [uPole_re]
  have hw_im : w.im = y₀ + ε := by dsimp only [w]; simp [uPole_im, y₀]
  have hbox_ball : Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im ⊆ Metric.ball uPole (1 / 8) := by
    intro u hu
    simp only [Complex.mem_reProdIm, hz_re, hz_im, hw_re, hw_im] at hu
    rw [Set.uIcc_of_le (by dsimp only [ε]; norm_num), Set.uIcc_of_le (by dsimp only [ε]; linarith)] at hu
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : ‖u - uPole‖ ≤ |(u - uPole).re| + |(u - uPole).im| := Complex.norm_le_abs_re_add_abs_im _
    have hre_abs : |(u - uPole).re| ≤ ε := by
      rw [Complex.sub_re, uPole_re, sub_zero, abs_le]; exact hu.1
    have him_abs : |(u - uPole).im| ≤ ε := by
      rw [Complex.sub_im, uPole_im, abs_le]
      dsimp only [y₀] at hu
      exact ⟨by linarith [hu.2.1], by linarith [hu.2.2]⟩
    dsimp only [ε] at hre_abs him_abs
    linarith
  have hb_in : ∀ x ∈ Set.uIcc z.re w.re, ((x : ℂ) + (z.im : ℂ) * I) ∈ Metric.ball uPole (1 / 8) ∧
      ((x : ℂ) + (z.im : ℂ) * I) ≠ uPole := fun x hx =>
    ⟨hbox_ball ⟨by simpa using hx, by simp⟩, fun h0 => by
      have him := congrArg Complex.im h0
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, hz_im, uPole_im] at him
      dsimp only [ε, y₀] at him; linarith⟩
  have ht_in : ∀ x ∈ Set.uIcc z.re w.re, ((x : ℂ) + (w.im : ℂ) * I) ∈ Metric.ball uPole (1 / 8) ∧
      ((x : ℂ) + (w.im : ℂ) * I) ≠ uPole := fun x hx =>
    ⟨hbox_ball ⟨by simpa using hx, by simp⟩, fun h0 => by
      have him := congrArg Complex.im h0
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, hw_im, uPole_im] at him
      dsimp only [ε, y₀] at him; linarith⟩
  have hr_in : ∀ y ∈ Set.uIcc z.im w.im, ((w.re : ℂ) + (y : ℂ) * I) ∈ Metric.ball uPole (1 / 8) ∧
      ((w.re : ℂ) + (y : ℂ) * I) ≠ uPole := fun y hy =>
    ⟨hbox_ball ⟨by simp, by simpa using hy⟩, fun h0 => by
      have hre := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, hw_re, uPole_re] at hre
      dsimp only [ε] at hre; linarith⟩
  have hl_in : ∀ y ∈ Set.uIcc z.im w.im, ((z.re : ℂ) + (y : ℂ) * I) ∈ Metric.ball uPole (1 / 8) ∧
      ((z.re : ℂ) + (y : ℂ) * I) ≠ uPole := fun y hy =>
    ⟨hbox_ball ⟨by simp, by simpa using hy⟩, fun h0 => by
      have hre := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, hz_re, uPole_re] at hre
      dsimp only [ε] at hre; linarith⟩
  let c : ℂ := -2 * (Real.pi : ℂ) * I * (k : ℂ)
  have hlaur_pt : ∀ u : ℂ, u ∈ Metric.ball uPole (1 / 8) → u ≠ uPole →
      f u = (∑ r ∈ Finset.Icc 1 b, laurentC b r * (Complex.exp (c * u) / (u - uPole) ^ r)) +
        Psi_holo b u * Complex.exp (c * u) := fun u hu hne => by
    dsimp only [f, c]
    rw [Psi_b_laurent_at_uPole hb hu hne, add_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun r _ => by ring
  have hcongr : rectIntegral f z w =
      rectIntegral (fun u => (∑ r ∈ Finset.Icc 1 b, laurentC b r * (Complex.exp (c * u) / (u - uPole) ^ r)) +
        Psi_holo b u * Complex.exp (c * u)) z w :=
    rectIntegral_congr_boundary
      (fun x hx => hlaur_pt _ (hb_in x hx).1 (hb_in x hx).2)
      (fun x hx => hlaur_pt _ (ht_in x hx).1 (ht_in x hx).2)
      (fun y hy => hlaur_pt _ (hr_in y hy).1 (hr_in y hy).2)
      (fun y hy => hlaur_pt _ (hl_in y hy).1 (hl_in y hy).2)
  change rectIntegral f z w = _
  rw [hcongr]
  have hint_term : ∀ (r : ℕ) {a₁ a₂ : ℝ} {γ : ℝ → ℂ}, Continuous γ → (∀ t ∈ Set.uIcc a₁ a₂, γ t ≠ uPole) →
      IntervalIntegrable (fun t => laurentC b r * (Complex.exp (c * γ t) / (γ t - uPole) ^ r)) volume a₁ a₂ := by
    intro r a₁ a₂ γ hγ hne
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (ContinuousOn.div
      ((Complex.continuous_exp.comp (continuous_const.mul hγ)).continuousOn)
      (ContinuousOn.pow (hγ.continuousOn.sub continuousOn_const) r) fun t ht =>
      pow_ne_zero r (sub_ne_zero.mpr (hne t ht)))
  have hint_sum : ∀ {a₁ a₂ : ℝ} {γ : ℝ → ℂ}, Continuous γ → (∀ t ∈ Set.uIcc a₁ a₂, γ t ≠ uPole) →
      IntervalIntegrable (fun t => ∑ r ∈ Finset.Icc 1 b, laurentC b r * (Complex.exp (c * γ t) / (γ t - uPole) ^ r))
        volume a₁ a₂ := by
    intro a₁ a₂ γ hγ hne
    exact intervalIntegrable_finset_sum (Finset.Icc 1 b)
      (fun r t => laurentC b r * (Complex.exp (c * γ t) / (γ t - uPole) ^ r)) _ _
      fun r _ => hint_term r hγ hne
  have hholo_diff : DifferentiableOn ℂ (fun u => Psi_holo b u * Complex.exp (c * u)) (Metric.ball uPole (1 / 8)) :=
    (Psi_holo_differentiableOn hb).mul (by fun_prop)
  have hint_holo : ∀ {a₁ a₂ : ℝ} {γ : ℝ → ℂ}, Continuous γ →
      (∀ t ∈ Set.uIcc a₁ a₂, γ t ∈ Metric.ball uPole (1 / 8)) →
      IntervalIntegrable (fun t => Psi_holo b (γ t) * Complex.exp (c * γ t)) volume a₁ a₂ := by
    intro a₁ a₂ γ hγ hmem
    exact ContinuousOn.intervalIntegrable (hholo_diff.continuousOn.comp hγ.continuousOn fun t ht => hmem t ht)
  rw [rectIntegral_add
    (hint_sum (by fun_prop) fun x hx => (hb_in x hx).2) (hint_holo (by fun_prop) fun x hx => (hb_in x hx).1)
    (hint_sum (by fun_prop) fun x hx => (ht_in x hx).2) (hint_holo (by fun_prop) fun x hx => (ht_in x hx).1)
    (hint_sum (by fun_prop) fun y hy => (hr_in y hy).2) (hint_holo (by fun_prop) fun y hy => (hr_in y hy).1)
    (hint_sum (by fun_prop) fun y hy => (hl_in y hy).2) (hint_holo (by fun_prop) fun y hy => (hl_in y hy).1)]
  have hholo_zero : rectIntegral (fun u => Psi_holo b u * Complex.exp (c * u)) z w = 0 :=
    rectIntegral_eq_zero_of_differentiableOn (hholo_diff.mono hbox_ball)
  rw [hholo_zero, add_zero, rectIntegral_finset_sum (Finset.Icc 1 b) _ z w
    (fun r _ => hint_term r (by fun_prop) fun x hx => (hb_in x hx).2)
    (fun r _ => hint_term r (by fun_prop) fun x hx => (ht_in x hx).2)
    (fun r _ => hint_term r (by fun_prop) fun y hy => (hr_in y hy).2)
    (fun r _ => hint_term r (by fun_prop) fun y hy => (hl_in y hy).2)]
  have hexp_uPole : Complex.exp (c * uPole) = (qHalf : ℂ) ^ (-k) := by
    rw [qHalf_zpow_eq_cexp (-k)]
    congr 1
    dsimp only [c]; unfold uPole
    push_cast
    have hI2 : I * I = -1 := Complex.I_mul_I
    calc -2 * (Real.pi : ℂ) * I * (k : ℂ) * ((Real.pi : ℂ) / ((Real.log 2 : ℝ) : ℂ) * I)
        = -(2 * (Real.pi : ℂ) ^ 2 * (k : ℂ) / ((Real.log 2 : ℝ) : ℂ)) * (I * I) := by ring
      _ = -2 * (Real.pi : ℂ) ^ 2 * -(k : ℂ) / ((Real.log 2 : ℝ) : ℂ) := by rw [hI2]; ring
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.mem_Icc] at hr
  rw [rectIntegral_const_mul, rectIntegral_exp_div_pow c uPole (by dsimp only [ε]; norm_num) hr.1, hexp_uPole]
  dsimp only [c]; ring

/-- Setting `k = 0` in the rectangle residue identity forces the simple-pole residue `c_{-1} = 0`. -/
lemma laurentC_one_eq_zero {b : ℕ} (hb : 2 ≤ b) : laurentC b 1 = 0 := by
  have h0 := Psi_hat_residue_eq hb 0
  simp only [mul_zero, neg_zero, zpow_zero, sub_self, zero_mul, Int.cast_zero, mul_one] at h0
  have hsum : ∑ r ∈ Finset.Icc 1 b, laurentC b r * (0 : ℂ) ^ (r - 1) / (((r - 1).factorial : ℕ) : ℂ) =
      laurentC b 1 := by
    rw [Finset.sum_eq_single 1]
    · simp
    · intro r hr hne
      rw [Finset.mem_Icc] at hr
      rw [zero_pow (by omega), mul_zero, zero_div]
    · intro hmem; exfalso; exact hmem (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  rw [hsum] at h0
  have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) Complex.I_ne_zero
  exact (mul_eq_zero.mp h0.symm).resolve_left h2pi

/-- Exact sine-product formula `sin(π χ_k) * Ψ̂_b(k) = π * χ_k * Q_b(χ_k)` for all `k : ℤ`. -/
theorem sin_mul_Psi_hat {b : ℕ} (hb : 2 ≤ b) (k : ℤ) :
    Complex.sin ((Real.pi : ℂ) * chiFR k) * Psi_hat b k =
      (Real.pi : ℂ) * chiFR k * (Q_b b).eval (chiFR k) := by
  by_cases hk : k = 0
  · subst hk; simp [chiFR]
  have hres := Psi_hat_residue_eq hb k
  have hq_ne : (qHalf : ℂ) ^ (-k) ≠ 0 := zpow_ne_zero (-k) (Complex.ofReal_ne_zero.mpr qHalf_pos.ne')
  have hlhs_fac : 1 - (qHalf : ℂ) ^ (-2 * k) = (qHalf : ℂ) ^ (-k) * ((qHalf : ℂ) ^ k - (qHalf : ℂ) ^ (-k)) := by
    have hq0 : (qHalf : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr qHalf_pos.ne'
    rw [mul_sub, ← zpow_add₀ hq0, ← zpow_add₀ hq0]
    simp [show -k + k = 0 by omega, show -k + -k = -2 * k by omega]
  rw [hlhs_fac, mul_assoc, mul_comm (2 * (Real.pi : ℂ) * I) ((qHalf : ℂ) ^ (-k)), mul_assoc] at hres
  have hcancel := mul_left_cancel₀ hq_ne hres
  rw [← sin_pi_mul_chiFR k] at hcancel
  have h2I : (2 * I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hdrop1 : ∑ r ∈ Finset.Icc 1 b, laurentC b r * (-2 * (Real.pi : ℂ) * I * (k : ℂ)) ^ (r - 1) /
        (((r - 1).factorial : ℕ) : ℂ) =
      ∑ r ∈ Finset.Icc 2 b, laurentC b r * (-2 * (Real.pi : ℂ) * I * (k : ℂ)) ^ (r - 1) /
        (((r - 1).factorial : ℕ) : ℂ) := by
    have hIcc : Finset.Icc 1 b = insert 1 (Finset.Icc 2 b) := by
      ext r; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.sum_insert (by simp), laurentC_one_eq_zero hb, zero_mul, zero_div, zero_add]
  have hQ_eval : (Q_b b).eval (chiFR k) * chiFR k =
      ∑ r ∈ Finset.Icc 2 b, laurentC b r * (-2 * (Real.pi : ℂ) * I * (k : ℂ)) ^ (r - 1) /
        (((r - 1).factorial : ℕ) : ℂ) := by
    unfold Q_b
    change (Polynomial.evalRingHom (chiFR k)) _ * chiFR k = _
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_Icc] at hr
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    have hchi : -2 * (Real.pi : ℂ) * I * (k : ℂ) = -((Real.log 2 : ℝ) : ℂ) * chiFR k := by
      unfold chiFR
      have hlog_ne : ((Real.log 2 : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
      push_cast; field_simp [hlog_ne]
    rw [hchi, mul_pow]
    have hpow : (chiFR k) ^ (r - 1) = (chiFR k) ^ (r - 2) * chiFR k := by
      rw [← pow_succ, show r - 2 + 1 = r - 1 by omega]
    rw [hpow]; ring
  rw [hdrop1, ← hQ_eval] at hcancel
  apply mul_left_cancel₀ h2I
  linear_combination hcancel

private lemma sin_pi_mul_chiFR_ne_zero {k : ℤ} (hk : k ≠ 0) :
    Complex.sin ((Real.pi : ℂ) * chiFR k) ≠ 0 := by
  intro h0
  have h := sin_pi_mul_chiFR k
  rw [h0, mul_zero] at h
  have heq : (qHalf : ℂ) ^ k = (qHalf : ℂ) ^ (-k) := by linear_combination -h
  have hreal : qHalf ^ k = qHalf ^ (-k) := by exact_mod_cast heq
  have hsq : qHalf ^ (2 * k) = 1 := by
    have hq0 : qHalf ≠ 0 := qHalf_pos.ne'
    have h1 : qHalf ^ k * qHalf ^ k = qHalf ^ (-k) * qHalf ^ k := by rw [hreal]
    rw [← zpow_add₀ hq0, ← zpow_add₀ hq0, neg_add_cancel, zpow_zero, show k + k = 2 * k by omega] at h1
    exact h1
  rcases lt_or_gt_of_ne hk with hlt | hgt
  · have hpos : (0 : ℤ) < -(2 * k) := by omega
    have hlt1 : qHalf ^ (-(2 * k)) < 1 := by
      lift -(2 * k) to ℕ using hpos.le with n hn
      rw [zpow_natCast]
      exact pow_lt_one₀ qHalf_pos.le qHalf_lt_one (by omega)
    have hinv : qHalf ^ (-(2 * k)) = 1 := by rw [zpow_neg, hsq, inv_one]
    linarith
  · have hpos : (0 : ℤ) < 2 * k := by omega
    have hlt1 : qHalf ^ (2 * k) < 1 := by
      lift (2 * k) to ℕ using hpos.le with n hn
      rw [zpow_natCast]
      exact pow_lt_one₀ qHalf_pos.le qHalf_lt_one (by omega)
    linarith

lemma Psi_hat_eq_of_ne_zero {b : ℕ} (hb : 2 ≤ b) {k : ℤ} (hk : k ≠ 0) :
    Psi_hat b k = (Real.pi : ℂ) * chiFR k * (Q_b b).eval (chiFR k) /
      Complex.sin ((Real.pi : ℂ) * chiFR k) := by
  rw [eq_div_iff (sin_pi_mul_chiFR_ne_zero hk), mul_comm]
  exact sin_mul_Psi_hat hb k

/-- Sharp lower bound `‖sin(π χ_k)‖ ≥ (1/4) exp(2π² |k| / log 2)` for `k ≠ 0`. -/
private lemma norm_sin_pi_mul_chiFR_ge {k : ℤ} (hk : k ≠ 0) :
    (1 / 4 : ℝ) * Real.exp (2 * Real.pi ^ 2 * |(k : ℝ)| / Real.log 2) ≤
      ‖Complex.sin ((Real.pi : ℂ) * chiFR k)‖ := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt1 : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]
  have harg : (Real.pi : ℂ) * chiFR k = (((2 * Real.pi ^ 2 * (k : ℝ) / Real.log 2 : ℝ) : ℂ)) * I := by
    unfold chiFR; push_cast; ring
  rw [harg, Complex.sin_mul_I, ← Complex.ofReal_sinh, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]
  have hsinh_abs : ∀ x : ℝ, |Real.sinh x| = Real.sinh |x| := fun x => by
    rcases le_total 0 x with hx | hx
    · have hs : 0 ≤ Real.sinh x := by
        rw [Real.sinh_eq]
        have : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
        linarith
      rw [abs_of_nonneg hs, abs_of_nonneg hx]
    · have hs : Real.sinh x ≤ 0 := by
        rw [Real.sinh_eq]
        have : Real.exp x ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
        linarith
      rw [abs_of_nonpos hs, abs_of_nonpos hx, Real.sinh_neg]
  rw [hsinh_abs]
  let t : ℝ := 2 * Real.pi ^ 2 * |(k : ℝ)| / Real.log 2
  have habs_arg : |2 * Real.pi ^ 2 * (k : ℝ) / Real.log 2| = t := by
    dsimp only [t]
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi ^ 2), abs_of_pos hlog2_pos]
  rw [habs_arg, Real.sinh_eq]
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have ht_ge : (1 : ℝ) ≤ t := by
    dsimp only [t]
    rw [le_div_iff₀ hlog2_pos]
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith
  have hexp_ge2 : (2 : ℝ) ≤ Real.exp (2 * t) := by
    linarith [Real.add_one_le_exp (2 * t)]
  have hsub : Real.exp (-t) ≤ (1 / 2 : ℝ) * Real.exp t := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos t)]
    have hsq : Real.exp t * Real.exp t = Real.exp (2 * t) := by rw [← Real.exp_add]; congr 1; ring
    linarith
  linarith

/-- Polynomial growth bound for `(Q_b b).eval (chiFR k)`. -/
private lemma norm_Q_b_eval_chiFR_le (b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℤ,
      ‖(Q_b b).eval (chiFR k)‖ ≤ C * (1 + |(k : ℝ)|) ^ (Q_b b).natDegree := by
  let L : ℝ := 2 * Real.pi / Real.log 2
  have hL : 0 < L := div_pos (by positivity) (Real.log_pos (by norm_num))
  have hchi_le : ∀ k : ℤ, ‖chiFR k‖ ≤ L * (1 + |(k : ℝ)|) := fun k => by
    unfold chiFR
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      show 2 * Real.pi * (k : ℝ) / Real.log 2 = L * (k : ℝ) by dsimp only [L]; ring,
      abs_mul, abs_of_pos hL]
    nlinarith [abs_nonneg (k : ℝ)]
  let C : ℝ := ∑ m ∈ Finset.range ((Q_b b).natDegree + 1),
    ‖(Q_b b).coeff m‖ * (max 1 L) ^ (Q_b b).natDegree
  refine ⟨C, Finset.sum_nonneg fun m _ => by positivity, fun k => ?_⟩
  rw [Polynomial.eval_eq_sum_range]
  calc ‖∑ m ∈ Finset.range ((Q_b b).natDegree + 1), (Q_b b).coeff m * (chiFR k) ^ m‖
      ≤ ∑ m ∈ Finset.range ((Q_b b).natDegree + 1), ‖(Q_b b).coeff m * (chiFR k) ^ m‖ :=
        norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.range ((Q_b b).natDegree + 1),
          ‖(Q_b b).coeff m‖ * (max 1 L) ^ (Q_b b).natDegree * (1 + |(k : ℝ)|) ^ (Q_b b).natDegree := by
        refine Finset.sum_le_sum fun m hm => ?_
        rw [Finset.mem_range] at hm
        rw [norm_mul, norm_pow]
        have h1 : ‖chiFR k‖ ^ m ≤ (max 1 L * (1 + |(k : ℝ)|)) ^ m :=
          pow_le_pow_left₀ (norm_nonneg _)
            ((hchi_le k).trans (mul_le_mul_of_nonneg_right (le_max_right 1 L) (by positivity))) m
        have h2 : (max 1 L * (1 + |(k : ℝ)|)) ^ m ≤ (max 1 L * (1 + |(k : ℝ)|)) ^ (Q_b b).natDegree := by
          refine pow_le_pow_right₀ ?_ (by omega)
          have h1L : (1 : ℝ) ≤ max 1 L := le_max_left 1 L
          nlinarith [abs_nonneg (k : ℝ)]
        have h3 := h1.trans h2
        rw [mul_pow] at h3
        calc ‖(Q_b b).coeff m‖ * ‖chiFR k‖ ^ m
            ≤ ‖(Q_b b).coeff m‖ * ((max 1 L) ^ (Q_b b).natDegree * (1 + |(k : ℝ)|) ^ (Q_b b).natDegree) :=
              mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
          _ = ‖(Q_b b).coeff m‖ * (max 1 L) ^ (Q_b b).natDegree * (1 + |(k : ℝ)|) ^ (Q_b b).natDegree := by ring
    _ = C * (1 + |(k : ℝ)|) ^ (Q_b b).natDegree := by rw [← Finset.sum_mul]

/-- Super-exponential decay bound for `Ψ̂_b(k)`:
`‖Ψ̂_b(k)‖ ≤ C * (1 + |k|)^b * exp(-2π² |k| / log 2)`. -/
lemma norm_Psi_hat_le {b : ℕ} (hb : 2 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℤ,
      ‖Psi_hat b k‖ ≤ C * (1 + |(k : ℝ)|) ^ b * Real.exp (-2 * Real.pi ^ 2 * |(k : ℝ)| / Real.log 2) := by
  obtain ⟨C₀, hC₀, hQ⟩ := norm_Q_b_eval_chiFR_le b
  let L : ℝ := 2 * Real.pi / Real.log 2
  have hL : 0 < L := div_pos (by positivity) (Real.log_pos (by norm_num))
  let C : ℝ := max ‖Psi_hat b 0‖ (4 * Real.pi * L * C₀)
  refine ⟨C, le_trans (norm_nonneg _) (le_max_left _ _), fun k => ?_⟩
  by_cases hk : k = 0
  · subst hk
    simp only [Int.cast_zero, abs_zero, add_zero, one_pow, mul_one, mul_zero, zero_div, Real.exp_zero]
    exact le_max_left _ _
  rw [Psi_hat_eq_of_ne_zero hb hk, norm_div, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  have hchi : ‖chiFR k‖ ≤ L * (1 + |(k : ℝ)|) := by
    unfold chiFR
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      show 2 * Real.pi * (k : ℝ) / Real.log 2 = L * (k : ℝ) by dsimp only [L]; ring,
      abs_mul, abs_of_pos hL]
    nlinarith [abs_nonneg (k : ℝ)]
  have hdeg : (Q_b b).natDegree = b - 2 := Q_b_natDegree hb
  have hpow_le : (1 + |(k : ℝ)|) * (1 + |(k : ℝ)|) ^ (Q_b b).natDegree ≤ (1 + |(k : ℝ)|) ^ b := by
    rw [hdeg, ← pow_succ']
    exact pow_le_pow_right₀ (by linarith [abs_nonneg (k : ℝ)]) (by omega)
  have hnum : Real.pi * ‖chiFR k‖ * ‖(Q_b b).eval (chiFR k)‖ ≤
      Real.pi * L * C₀ * (1 + |(k : ℝ)|) ^ b := by
    calc Real.pi * ‖chiFR k‖ * ‖(Q_b b).eval (chiFR k)‖
        ≤ Real.pi * (L * (1 + |(k : ℝ)|)) * (C₀ * (1 + |(k : ℝ)|) ^ (Q_b b).natDegree) := by
          gcongr; exact hQ k
      _ = Real.pi * L * C₀ * ((1 + |(k : ℝ)|) * (1 + |(k : ℝ)|) ^ (Q_b b).natDegree) := by ring
      _ ≤ Real.pi * L * C₀ * (1 + |(k : ℝ)|) ^ b := by gcongr
  have hden := norm_sin_pi_mul_chiFR_ge hk
  calc Real.pi * ‖chiFR k‖ * ‖(Q_b b).eval (chiFR k)‖ / ‖Complex.sin ((Real.pi : ℂ) * chiFR k)‖
      ≤ (Real.pi * L * C₀ * (1 + |(k : ℝ)|) ^ b) /
          ((1 / 4 : ℝ) * Real.exp (2 * Real.pi ^ 2 * |(k : ℝ)| / Real.log 2)) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (4 * Real.pi * L * C₀) * (1 + |(k : ℝ)|) ^ b *
          Real.exp (-2 * Real.pi ^ 2 * |(k : ℝ)| / Real.log 2) := by
        rw [show -2 * Real.pi ^ 2 * |(k : ℝ)| / Real.log 2 = -(2 * Real.pi ^ 2 * |(k : ℝ)| / Real.log 2) by ring,
          Real.exp_neg]
        ring
    _ ≤ C * (1 + |(k : ℝ)|) ^ b * Real.exp (-2 * Real.pi ^ 2 * |(k : ℝ)| / Real.log 2) := by
        gcongr; exact le_max_right _ _

/-- Exponential decay beats any polynomial: `Summable (fun k : ℤ => (1 + |k|)^d * exp(-α |k|))` for `0 < α`. -/
private lemma summable_poly_mul_exp_neg_int (d : ℕ) {α : ℝ} (hα : 0 < α) :
    Summable (fun k : ℤ => (1 + |(k : ℝ)|) ^ d * Real.exp (-α * |(k : ℝ)|)) := by
  have hnat : ∀ s : ℝ, s = 1 ∨ s = -1 →
      Summable (fun n : ℕ => (1 + (n : ℝ)) ^ d * Real.exp (-α * (n : ℝ))) := fun _ _ => by
    -- Bound `(1 + n)^d * exp(-α n / 2)` using `t^d / d! ≤ exp t` with `t = (α / 2) * (1 + n)`.
    have hpoly : ∀ n : ℕ, (1 + (n : ℝ)) ^ d * Real.exp (-α * (n : ℝ)) ≤
        ((d.factorial : ℝ) / (α / 2) ^ d * Real.exp (α / 2)) * (Real.exp (-α / 2)) ^ n := fun n => by
      have h1 : ((α / 2) * (1 + (n : ℝ))) ^ d / (d.factorial : ℝ) ≤
          Real.exp ((α / 2) * (1 + (n : ℝ))) :=
        Real.pow_div_factorial_le_exp _ (by positivity) d
      have h2 : (1 + (n : ℝ)) ^ d ≤ ((d.factorial : ℝ) / (α / 2) ^ d) * Real.exp ((α / 2) * (1 + (n : ℝ))) := by
        rw [mul_pow] at h1
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have h1' : (α / 2) ^ d * (1 + (n : ℝ)) ^ d ≤ Real.exp ((α / 2) * (1 + (n : ℝ))) * (d.factorial : ℝ) :=
          (div_le_iff₀ (by positivity)).mp h1
        linarith
      calc (1 + (n : ℝ)) ^ d * Real.exp (-α * (n : ℝ))
          ≤ (((d.factorial : ℝ) / (α / 2) ^ d) * Real.exp ((α / 2) * (1 + (n : ℝ)))) *
              Real.exp (-α * (n : ℝ)) := mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = ((d.factorial : ℝ) / (α / 2) ^ d * Real.exp (α / 2)) * (Real.exp (-α / 2)) ^ n := by
            rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
            congr 2; ring
    refine Summable.of_nonneg_of_le (fun n => by positivity) hpoly ?_
    exact (summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (by linarith))).mul_left _
  have h1 : Summable (fun n : ℕ => (1 + |((n : ℤ) : ℝ)|) ^ d * Real.exp (-α * |((n : ℤ) : ℝ)|)) := by
    refine (hnat 1 (Or.inl rfl)).congr fun n => ?_
    simp [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  have h2 : Summable (fun n : ℕ => (1 + |((-(n + 1 : ℤ)) : ℝ)|) ^ d *
      Real.exp (-α * |((-(n + 1 : ℤ)) : ℝ)|)) := by
    have hshift := (summable_nat_add_iff 1).mpr (hnat 1 (Or.inl rfl))
    refine hshift.congr fun n => ?_
    have hcast : |((-(n + 1 : ℤ)) : ℝ)| = ((n + 1 : ℕ) : ℝ) := by
      push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]
    rw [hcast]
  let g : ℤ → ℝ := fun k => (1 + |(k : ℝ)|) ^ d * Real.exp (-α * |(k : ℝ)|)
  have hsplit : g = (fun k : ℤ => if 0 ≤ k then g k else 0) + (fun k : ℤ => if 0 ≤ k then 0 else g k) := by
    funext k; simp only [Pi.add_apply]; split_ifs <;> ring
  have hs1 : Summable (fun k : ℤ => if 0 ≤ k then g k else 0) := by
    refine (Int.ofNat_injective.summable_iff (f := fun k : ℤ => if 0 ≤ k then g k else 0) ?_).mp ?_
    · intro k hk
      have hneg : ¬ (0 ≤ k) := fun h0 => hk ⟨k.toNat, Int.toNat_of_nonneg h0⟩
      simp [hneg]
    · refine h1.congr fun n => ?_
      simp [g]
  have hs2 : Summable (fun k : ℤ => if 0 ≤ k then 0 else g k) := by
    let negIdx : ℕ → ℤ := fun n => -(n + 1 : ℤ)
    have hinj : Function.Injective negIdx := fun a b h => by dsimp only [negIdx] at h; omega
    refine (hinj.summable_iff (f := fun k : ℤ => if 0 ≤ k then 0 else g k) ?_).mp ?_
    · intro k hk
      have hpos : 0 ≤ k := by
        by_contra hlt
        exact hk ⟨(-k - 1).toNat, by
          dsimp only [negIdx]
          have hnn : 0 ≤ -k - 1 := by omega
          have := Int.toNat_of_nonneg hnn
          omega⟩
      simp [hpos]
    · refine h2.congr fun n => ?_
      have hneg : ¬ (0 ≤ negIdx n) := by dsimp only [negIdx]; omega
      change _ = if 0 ≤ negIdx n then 0 else g (negIdx n)
      simp only [hneg, ↓reduceIte, g, negIdx]
      push_cast; rfl
  change Summable g
  rw [hsplit]
  exact hs1.add hs2

/-- Reusable Fourier expansion lemma for any continuous `1`-periodic `g : ℝ → ℂ` with summable
Fourier coefficients on `[-1/2, 1/2]`. -/
private lemma fourier_series_one_periodic {g : ℝ → ℂ} (hcont : Continuous g)
    (hper : ∀ x : ℝ, g (x + 1) = g x)
    (hsum : Summable (fun k : ℤ =>
      ∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        g t * Complex.exp (-2 * (Real.pi : ℂ) * I * (k : ℂ) * (t : ℂ)))) :
    ∀ x : ℝ, g x = ∑' k : ℤ,
      (∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        g t * Complex.exp (-2 * (Real.pi : ℂ) * I * (k : ℂ) * (t : ℂ))) *
        Complex.exp (2 * (Real.pi : ℂ) * I * (k : ℂ) * (x : ℂ)) := by
  have : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  have hper_int : ∀ (m : ℤ) (x : ℝ), g (x + (m : ℝ)) = g x := by
    intro m
    induction m using Int.induction_on with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [show x + (((k : ℤ) + 1 : ℤ) : ℝ) = (x + ((k : ℤ) : ℝ)) + 1 by push_cast; ring, hper, ih]
    | pred k ih =>
      intro x
      have h1 := hper (x + (((-(k : ℤ) - 1 : ℤ) : ℝ)))
      rw [show x + (((-(k : ℤ) - 1 : ℤ) : ℝ)) + 1 = x + ((-(k : ℤ) : ℤ) : ℝ) by push_cast; ring, ih] at h1
      exact h1.symm
  let G : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨AddCircle.liftIco (1 : ℝ) (-1 / 2 : ℝ) g,
      AddCircle.liftIco_continuous (by simpa [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] using (hper (-1 / 2)).symm)
        hcont.continuousOn⟩
  have hG_apply : ∀ x : ℝ, G (x : AddCircle (1 : ℝ)) = g x := fun x => by
    let m : ℤ := ⌊x + 1 / 2⌋
    have hm1 : (m : ℝ) ≤ x + 1 / 2 := Int.floor_le (x + 1 / 2)
    have hm2 : x + 1 / 2 < (m : ℝ) + 1 := Int.lt_floor_add_one (x + 1 / 2)
    have hmem : x - (m : ℝ) ∈ Set.Ico (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1) := ⟨by linarith, by linarith⟩
    have hcoe : (x : AddCircle (1 : ℝ)) = ((x - (m : ℝ) : ℝ) : AddCircle (1 : ℝ)) := by
      rw [QuotientAddGroup.eq]
      refine ⟨-m, ?_⟩
      simp [zsmul_eq_mul]
      ring
    rw [hcoe]
    change AddCircle.liftIco (1 : ℝ) (-1 / 2 : ℝ) g ((x - (m : ℝ) : ℝ) : AddCircle (1 : ℝ)) = g x
    rw [AddCircle.liftIco_coe_apply hmem]
    have := hper_int (-m) x
    simpa [sub_eq_add_neg] using this
  have hcoeff : ∀ k : ℤ, fourierCoeff (⇑G) k =
      ∫ t : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        g t * Complex.exp (-2 * (Real.pi : ℂ) * I * (k : ℂ) * (t : ℂ)) := fun k => by
    rw [fourierCoeff_eq_intervalIntegral (⇑G) k (-1 / 2 : ℝ)]
    simp only [one_div, inv_one, one_smul, show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [hG_apply t, fourier_coe_apply]
    simp only [Int.cast_neg, Complex.ofReal_one, div_one, smul_eq_mul]
    ring_nf
  have hsumG : Summable (fourierCoeff (⇑G)) := hsum.congr fun k => (hcoeff k).symm
  have hhs := hasSum_fourier_series_of_summable hsumG
  intro x
  have heval := (ContinuousMap.evalCLM ℂ (x : AddCircle (1 : ℝ))).hasSum hhs
  have hval := heval.tsum_eq
  rw [ContinuousMap.evalCLM_apply, hG_apply x] at hval
  rw [← hval]
  refine tsum_congr fun k => ?_
  rw [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, hcoeff k, fourier_coe_apply]
  simp [smul_eq_mul]

/-- Exact Fourier series of `Ψ_b(u)` on the entire open strip `|u.im| < π / log 2`. -/
theorem Psi_b_fourier_series {b : ℕ} (hb : 2 ≤ b) {u : ℂ} (hu : |u.im| < Real.pi / Real.log 2) :
    Psi_b b u = ∑' k : ℤ, Psi_hat b k * Complex.exp (2 * (Real.pi : ℂ) * I * (k : ℂ) * u) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨C, hC, hPsi_bd⟩ := norm_Psi_hat_le hb
  have hsum_real : Summable (Psi_hat b) := by
    have hdom := (summable_poly_mul_exp_neg_int b (α := 2 * Real.pi ^ 2 / Real.log 2) (by positivity)).mul_left C
    refine Summable.of_norm_bounded hdom fun k => ?_
    have h := hPsi_bd k
    convert h using 1
    rw [mul_assoc]
    congr 2
    ring
  have hreal_eq : ∀ x : ℝ, Psi_b b (x : ℂ) =
      ∑' k : ℤ, Psi_hat b k * Complex.exp (2 * (Real.pi : ℂ) * I * (k : ℂ) * (x : ℂ)) := by
    have hcont : Continuous (fun x : ℝ => Psi_b b (x : ℂ)) :=
      (Psi_b_differentiableOn (by omega : 1 ≤ b)).continuousOn.comp_continuous Complex.continuous_ofReal
        fun x => mem_PsiDomain_of_abs_im_lt (by simp [div_pos Real.pi_pos hlog2])
    have hper : ∀ x : ℝ, Psi_b b ((x + 1 : ℝ) : ℂ) = Psi_b b (x : ℂ) := fun x => by
      push_cast; exact Psi_b_add_one b (x : ℂ)
    exact fourier_series_one_periodic hcont hper hsum_real
  -- Extend from `ℝ` to the open strip `S = {z | |z.im| < π / log 2}` by the identity theorem!
  let S : Set ℂ := {z : ℂ | |z.im| < Real.pi / Real.log 2}
  have hS_open : IsOpen S := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hS_conv : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    simp only [S, Set.mem_ofPred_eq, Complex.add_im, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at hx hy ⊢
    calc |a * x.im + b * y.im| ≤ |a * x.im| + |b * y.im| := abs_add_le _ _
      _ = a * |x.im| + b * |y.im| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ < a * (Real.pi / Real.log 2) + b * (Real.pi / Real.log 2) := by
          rcases eq_or_lt_of_le ha with rfl | ha'
          · have hb1 : b = 1 := by linarith
            subst hb1; simp [hy]
          · rcases eq_or_lt_of_le hb with rfl | hb'
            · have ha1 : a = 1 := by linarith
              subst ha1; simp [hx]
            · linarith [mul_lt_mul_of_pos_left hx ha', mul_lt_mul_of_pos_left hy hb']
      _ = Real.pi / Real.log 2 := by linear_combination (Real.pi / Real.log 2) * hab
  have hrhs_diff : DifferentiableOn ℂ
      (fun z : ℂ => ∑' k : ℤ, Psi_hat b k * Complex.exp (2 * (Real.pi : ℂ) * I * (k : ℂ) * z)) S := by
    intro z₀ hz₀
    simp only [S, Set.mem_ofPred_eq] at hz₀
    let δ : ℝ := (Real.pi / Real.log 2 - |z₀.im|) / 2
    have hδ : 0 < δ := half_pos (sub_pos.mpr hz₀)
    let M : ℝ := |z₀.im| + δ
    have hM_lt : M < Real.pi / Real.log 2 := by dsimp only [M, δ]; linarith
    let α : ℝ := 2 * Real.pi * (Real.pi / Real.log 2 - M)
    have hα : 0 < α := mul_pos (by positivity) (sub_pos.mpr hM_lt)
    have hbound_ball : ∀ (k : ℤ) (z : ℂ), z ∈ Metric.ball z₀ δ →
        ‖Psi_hat b k * Complex.exp (2 * (Real.pi : ℂ) * I * (k : ℂ) * z)‖ ≤
          C * (1 + |(k : ℝ)|) ^ b * Real.exp (-α * |(k : ℝ)|) := by
      intro k z hz
      have hdist : ‖z - z₀‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      have him_le : |z.im| ≤ M := by
        have h1 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
          rw [← Complex.sub_im]; exact Complex.abs_im_le_norm (z - z₀)
        have h2 : |z.im| ≤ |z.im - z₀.im| + |z₀.im| := by
          calc |z.im| = |(z.im - z₀.im) + z₀.im| := by ring_nf
            _ ≤ |z.im - z₀.im| + |z₀.im| := abs_add_le _ _
        dsimp only [M]; linarith
      have hexp_norm : ‖Complex.exp (2 * (Real.pi : ℂ) * I * (k : ℂ) * z)‖ ≤
          Real.exp (2 * Real.pi * M * |(k : ℝ)|) := by
        rw [Complex.norm_exp]
        have hre : (2 * (Real.pi : ℂ) * I * (k : ℂ) * z).re = -2 * Real.pi * (k : ℝ) * z.im := by
          simp [Complex.mul_re, Complex.mul_im]
        rw [hre]
        refine Real.exp_le_exp.mpr ?_
        have hle : -(2 * Real.pi * (k : ℝ) * z.im) ≤ |2 * Real.pi * (k : ℝ) * z.im| := neg_le_abs _
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at hle
        have hkm : |(k : ℝ)| * |z.im| ≤ |(k : ℝ)| * M :=
          mul_le_mul_of_nonneg_left him_le (abs_nonneg _)
        nlinarith [Real.pi_pos]
      rw [norm_mul]
      calc ‖Psi_hat b k‖ * ‖Complex.exp (2 * (Real.pi : ℂ) * I * (k : ℂ) * z)‖
          ≤ (C * (1 + |(k : ℝ)|) ^ b * Real.exp (-2 * Real.pi ^ 2 * |(k : ℝ)| / Real.log 2)) *
              Real.exp (2 * Real.pi * M * |(k : ℝ)|) :=
            mul_le_mul (hPsi_bd k) hexp_norm (norm_nonneg _) (by positivity)
        _ = C * (1 + |(k : ℝ)|) ^ b * Real.exp (-α * |(k : ℝ)|) := by
            rw [mul_assoc, ← Real.exp_add]
            congr 2
            dsimp only [α]; ring
    have hsum_dom : Summable (fun k : ℤ => C * (1 + |(k : ℝ)|) ^ b * Real.exp (-α * |(k : ℝ)|)) := by
      simpa [mul_assoc] using (summable_poly_mul_exp_neg_int b hα).mul_left C
    let negIdx : ℕ → ℤ := fun n => -(n + 1 : ℤ)
    have hneg_inj : Function.Injective negIdx := fun a₁ a₂ h => by dsimp only [negIdx] at h; omega
    have hsplit : ∀ z ∈ Metric.ball z₀ δ,
        (∑' k : ℤ, Psi_hat b k * Complex.exp (2 * (Real.pi : ℂ) * I * (k : ℂ) * z)) =
          (∑' n : ℕ, Psi_hat b (n : ℤ) * Complex.exp (2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ) * z)) +
          (∑' n : ℕ, Psi_hat b (negIdx n) * Complex.exp (2 * (Real.pi : ℂ) * I * ((negIdx n) : ℂ) * z)) := by
      intro z hz
      exact tsum_int_eq_nat_add_negSucc (Summable.of_norm_bounded hsum_dom fun k => hbound_ball k z hz)
    have hunif1 : TendstoUniformlyOn
        (fun N z => ∑ n ∈ Finset.range N, Psi_hat b (n : ℤ) * Complex.exp (2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ) * z))
        (fun z => ∑' n : ℕ, Psi_hat b (n : ℤ) * Complex.exp (2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ) * z))
        atTop (Metric.ball z₀ δ) :=
      tendstoUniformlyOn_tsum_nat (hsum_dom.comp_injective Int.ofNat_injective)
        fun n z hz => hbound_ball (n : ℤ) z hz
    have hunif2 : TendstoUniformlyOn
        (fun N z => ∑ n ∈ Finset.range N, Psi_hat b (negIdx n) * Complex.exp (2 * (Real.pi : ℂ) * I * ((negIdx n) : ℂ) * z))
        (fun z => ∑' n : ℕ, Psi_hat b (negIdx n) * Complex.exp (2 * (Real.pi : ℂ) * I * ((negIdx n) : ℂ) * z))
        atTop (Metric.ball z₀ δ) :=
      tendstoUniformlyOn_tsum_nat (hsum_dom.comp_injective hneg_inj)
        fun n z hz => hbound_ball (negIdx n) z hz
    have hd1 : DifferentiableOn ℂ (fun z => ∑' n : ℕ, Psi_hat b (n : ℤ) * Complex.exp (2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ) * z)) (Metric.ball z₀ δ) :=
      hunif1.tendstoLocallyUniformlyOn.differentiableOn
        (Filter.Eventually.of_forall fun N => DifferentiableOn.fun_sum fun n _ => by fun_prop)
        Metric.isOpen_ball
    have hd2 : DifferentiableOn ℂ (fun z => ∑' n : ℕ, Psi_hat b (negIdx n) * Complex.exp (2 * (Real.pi : ℂ) * I * ((negIdx n) : ℂ) * z)) (Metric.ball z₀ δ) :=
      hunif2.tendstoLocallyUniformlyOn.differentiableOn
        (Filter.Eventually.of_forall fun N => DifferentiableOn.fun_sum fun n _ => by fun_prop)
        Metric.isOpen_ball
    have hball_diff : DifferentiableOn ℂ
        (fun z => ∑' k : ℤ, Psi_hat b k * Complex.exp (2 * (Real.pi : ℂ) * I * (k : ℂ) * z))
        (Metric.ball z₀ δ) :=
      (hd1.add hd2).congr fun z hz => hsplit z hz
    exact ((hball_diff z₀ (Metric.mem_ball_self hδ)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))).differentiableWithinAt
  exact eqOn_of_differentiableOn_eq_on_real_interval hS_open hS_conv.isPreconnected
    ((Psi_b_differentiableOn (by omega : 1 ≤ b)).mono fun z hz => mem_PsiDomain_of_abs_im_lt hz)
    hrhs_diff (a := -1) (b := 1) (by norm_num)
    (fun x _ _ => by simp [S, div_pos Real.pi_pos hlog2])
    (fun x _ _ => hreal_eq x) hu

/-! ### Gamma Reflection, Sharp Decay of `Γ(1 - χ_k)`, `masterLacunary` Poisson Expansion, and Exact `v_b` ODE -/

/-- `k`-th Fourier coefficient of the Mellin-divided periodic fluctuation `Φ_b`. -/
@[expose] def Phi_hat (b : ℕ) (k : ℤ) : ℂ :=
  Psi_hat b k / Complex.Gamma (2 + chiFR k)

private lemma chiFR_re (k : ℤ) : (chiFR k).re = 0 := by
  unfold chiFR
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_zero]

private lemma chiFR_im (k : ℤ) : (chiFR k).im = 2 * Real.pi * (k : ℝ) / Real.log 2 := by
  unfold chiFR
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
    Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]

/-- Exact Euler-reflection collapse of `Φ̂_b(k)` onto the polynomial `Q_b(χ_k)` for all `k ≠ 0`. -/
theorem Phi_hat_eq_Q_b_mul_Gamma {b : ℕ} (hb : 2 ≤ b) {k : ℤ} (hk : k ≠ 0) :
    Phi_hat b k = (Q_b b).eval (chiFR k) / (1 + chiFR k) * Complex.Gamma (1 - chiFR k) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hchi_ne : chiFR k ≠ 0 := fun h0 => by
    have him := congrArg Complex.im h0
    rw [chiFR_im, Complex.zero_im] at him
    have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have hnum : 2 * Real.pi * (k : ℝ) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_pos.ne') hk'
    exact div_ne_zero hnum hlog2.ne' him
  have h1chi_ne : 1 + chiFR k ≠ 0 := fun h0 => by
    have hre := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.one_re, chiFR_re, add_zero, Complex.zero_re] at hre
    norm_num at hre
  have hG2 : Complex.Gamma (2 + chiFR k) = (1 + chiFR k) * chiFR k * Complex.Gamma (chiFR k) := by
    have h1 : (2 : ℂ) + chiFR k = (1 + chiFR k) + 1 := by ring
    have h2 : (1 : ℂ) + chiFR k = chiFR k + 1 := by ring
    rw [h1, Complex.Gamma_add_one (1 + chiFR k) h1chi_ne, h2, Complex.Gamma_add_one (chiFR k) hchi_ne]
    ring
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (chiFR k)
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * chiFR k) ≠ 0 := sin_pi_mul_chiFR_ne_zero hk
  have hGchi_ne : Complex.Gamma (chiFR k) ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hrefl
    exact div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne') hsin_ne hrefl.symm
  unfold Phi_hat
  rw [Psi_hat_eq_of_ne_zero hb hk, hG2]
  have hGamma_one_sub : Complex.Gamma (1 - chiFR k) =
      (Real.pi : ℂ) / (Complex.sin ((Real.pi : ℂ) * chiFR k) * Complex.Gamma (chiFR k)) := by
    rw [eq_div_iff (mul_ne_zero hsin_ne hGchi_ne)]
    have := congrArg (· * Complex.sin ((Real.pi : ℂ) * chiFR k)) hrefl
    rw [div_mul_cancel₀ _ hsin_ne] at this
    linear_combination this
  rw [hGamma_one_sub]
  field_simp [hsin_ne, h1chi_ne, hchi_ne, hGchi_ne]

/-- Exact modulus formula `‖Γ(1 - i y)‖² = π |y| / sinh(π |y|)` for every real `y ≠ 0`. -/
lemma norm_Gamma_one_sub_imag_sq {y : ℝ} (hy : y ≠ 0) :
    ‖Complex.Gamma (1 - (y : ℂ) * I)‖ ^ 2 = Real.pi * |y| / Real.sinh (Real.pi * |y|) := by
  have hyI : (y : ℂ) * I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hy) Complex.I_ne_zero
  have hconj : starRingEnd ℂ (Complex.Gamma (1 - (y : ℂ) * I)) = Complex.Gamma (1 + (y : ℂ) * I) := by
    rw [← Complex.Gamma_conj]
    congr 1
    simp [map_sub, Complex.conj_ofReal, Complex.conj_I]
  have hprod : Complex.Gamma (1 + (y : ℂ) * I) * Complex.Gamma (1 - (y : ℂ) * I) =
      ((Real.pi * y / Real.sinh (Real.pi * y) : ℝ) : ℂ) := by
    have h1 : (1 : ℂ) + (y : ℂ) * I = (y : ℂ) * I + 1 := by ring
    rw [h1, Complex.Gamma_add_one ((y : ℂ) * I) hyI, mul_assoc, Complex.Gamma_mul_Gamma_one_sub ((y : ℂ) * I)]
    have hsin : Complex.sin ((Real.pi : ℂ) * ((y : ℂ) * I)) = ((Real.sinh (Real.pi * y) : ℝ) : ℂ) * I := by
      rw [show (Real.pi : ℂ) * ((y : ℂ) * I) = (((Real.pi * y : ℝ) : ℂ)) * I by push_cast; ring,
        Complex.sin_mul_I, ← Complex.ofReal_sinh]
    rw [hsin]
    have hsinh_ne : ((Real.sinh (Real.pi * y) : ℝ) : ℂ) ≠ 0 := by
      refine Complex.ofReal_ne_zero.mpr fun h0 => hy ?_
      have harg0 : Real.pi * y = 0 := by
        rw [Real.sinh_eq] at h0
        have heq : Real.exp (Real.pi * y) = Real.exp (-(Real.pi * y)) := by linarith
        have := Real.exp_injective heq
        linarith
      exact (mul_eq_zero.mp harg0).resolve_left Real.pi_pos.ne'
    push_cast
    field_simp [hsinh_ne, Complex.I_ne_zero]
  have hnorm_sq : ‖Complex.Gamma (1 - (y : ℂ) * I)‖ ^ 2 =
      ‖Complex.Gamma (1 + (y : ℂ) * I) * Complex.Gamma (1 - (y : ℂ) * I)‖ := by
    rw [← hconj, norm_mul, RingHomIsometric.norm_map, sq]
  rw [hnorm_sq, hprod, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos Real.pi_pos]
  congr 1
  have hsinh_abs : ∀ x : ℝ, |Real.sinh x| = Real.sinh |x| := fun x => by
    rcases le_total 0 x with hx | hx
    · have hs : 0 ≤ Real.sinh x := by
        rw [Real.sinh_eq]; linarith [Real.exp_le_exp.mpr (show -x ≤ x by linarith)]
      rw [abs_of_nonneg hs, abs_of_nonneg hx]
    · have hs : Real.sinh x ≤ 0 := by
        rw [Real.sinh_eq]; linarith [Real.exp_le_exp.mpr (show x ≤ -x by linarith)]
      rw [abs_of_nonpos hs, abs_of_nonpos hx, Real.sinh_neg]
  rw [hsinh_abs, abs_mul, abs_of_pos Real.pi_pos]

/-- Sharp exponential decay bound for `Γ(1 - χ_k)` across all `k : ℤ` (retaining full exponent
`-π² |k| / log 2` so Dirichlet-type series converge on the entire open right half-plane `{0 < z.re}`). -/
lemma norm_Gamma_one_sub_chiFR_le (k : ℤ) :
    ‖Complex.Gamma (1 - chiFR k)‖ ≤
      (4 * Real.pi ^ 2 / Real.log 2 + 1) * (1 + |(k : ℝ)|) *
        Real.exp (-Real.pi ^ 2 * |(k : ℝ)| / Real.log 2) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt1 : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    linarith [Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)]
  by_cases hk : k = 0
  · subst hk
    simp only [chiFR, Int.cast_zero, mul_zero, zero_div, Complex.ofReal_zero, zero_mul, sub_zero,
      Complex.Gamma_one, norm_one, abs_zero, add_zero, mul_one, Real.exp_zero]
    have : 0 < 4 * Real.pi ^ 2 / Real.log 2 := by positivity
    linarith
  let y : ℝ := 2 * Real.pi * (k : ℝ) / Real.log 2
  have hy : y ≠ 0 := by
    dsimp only [y]
    exact div_ne_zero (mul_ne_zero (by positivity) (Int.cast_ne_zero.mpr hk)) hlog2_pos.ne'
  have hchi : chiFR k = (y : ℂ) * I := rfl
  rw [hchi]
  let t : ℝ := Real.pi * |y|
  have ht_eq : t = 2 * Real.pi ^ 2 * |(k : ℝ)| / Real.log 2 := by
    dsimp only [t, y]
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi), abs_of_pos hlog2_pos]
    ring
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have ht_ge1 : (1 : ℝ) ≤ t := by
    rw [ht_eq, le_div_iff₀ hlog2_pos]
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith
  have hsinh_ge : (1 / 4 : ℝ) * Real.exp t ≤ Real.sinh t := by
    rw [Real.sinh_eq]
    have h2 : (2 : ℝ) ≤ Real.exp (2 * t) := by linarith [Real.add_one_le_exp (2 * t)]
    have hsub : Real.exp (-t) ≤ (1 / 2 : ℝ) * Real.exp t := by
      rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos t)]
      have hsq : Real.exp t * Real.exp t = Real.exp (2 * t) := by rw [← Real.exp_add]; congr 1; ring
      linarith
    linarith
  have hsq_le : ‖Complex.Gamma (1 - (y : ℂ) * I)‖ ^ 2 ≤ (2 * t * Real.exp (-t / 2)) ^ 2 := by
    rw [norm_Gamma_one_sub_imag_sq hy]
    change t / Real.sinh t ≤ (2 * t * Real.exp (-t / 2)) ^ 2
    calc t / Real.sinh t ≤ t / ((1 / 4 : ℝ) * Real.exp t) :=
          div_le_div_of_nonneg_left (by linarith) (by positivity) hsinh_ge
      _ = 4 * t * Real.exp (-t) := by rw [Real.exp_neg]; ring
      _ ≤ 4 * t ^ 2 * Real.exp (-t) := by
          have ht2 : t ≤ t ^ 2 := by nlinarith
          have : 4 * t ≤ 4 * t ^ 2 := by linarith
          exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = (2 * t * Real.exp (-t / 2)) ^ 2 := by
          have hexp2 : (Real.exp (-t / 2)) ^ 2 = Real.exp (-t) := by
            rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
          rw [mul_pow, mul_pow, hexp2]; ring
  have hnorm_le : ‖Complex.Gamma (1 - (y : ℂ) * I)‖ ≤ 2 * t * Real.exp (-t / 2) := by
    nlinarith [norm_nonneg (Complex.Gamma (1 - (y : ℂ) * I)), show 0 ≤ 2 * t * Real.exp (-t / 2) by positivity]
  refine hnorm_le.trans ?_
  have hexp_eq : -t / 2 = -Real.pi ^ 2 * |(k : ℝ)| / Real.log 2 := by rw [ht_eq]; ring
  rw [hexp_eq]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  rw [ht_eq]
  have h2t : 2 * (2 * Real.pi ^ 2 * |(k : ℝ)| / Real.log 2) =
      (4 * Real.pi ^ 2 / Real.log 2) * |(k : ℝ)| := by ring
  rw [h2t]
  nlinarith [abs_nonneg (k : ℝ), show 0 < 4 * Real.pi ^ 2 / Real.log 2 by positivity]

/-- Sharp exponential decay bound for `Φ̂_b(k)` across all `k : ℤ`. -/
lemma norm_Phi_hat_le {b : ℕ} (hb : 2 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℤ,
      ‖Phi_hat b k‖ ≤ C * (1 + |(k : ℝ)|) ^ (b - 1) * Real.exp (-Real.pi ^ 2 * |(k : ℝ)| / Real.log 2) := by
  obtain ⟨C₀, hC₀, hQ⟩ := norm_Q_b_eval_chiFR_le b
  let C₁ : ℝ := 4 * Real.pi ^ 2 / Real.log 2 + 1
  have hC₁ : 0 < C₁ := by dsimp only [C₁]; positivity
  let C : ℝ := max ‖Phi_hat b 0‖ (C₀ * C₁)
  refine ⟨C, le_trans (norm_nonneg _) (le_max_left _ _), fun k => ?_⟩
  by_cases hk : k = 0
  · subst hk
    simp only [Int.cast_zero, abs_zero, add_zero, one_pow, mul_one, mul_zero, zero_div, Real.exp_zero]
    exact le_max_left _ _
  rw [Phi_hat_eq_Q_b_mul_Gamma hb hk, norm_mul, norm_div]
  have h1chi_ge : (1 : ℝ) ≤ ‖1 + chiFR k‖ := by
    have hre : (1 + chiFR k).re = 1 := by
      rw [Complex.add_re, Complex.one_re, chiFR_re, add_zero]
    calc (1 : ℝ) = (1 + chiFR k).re := hre.symm
      _ ≤ ‖1 + chiFR k‖ := Complex.re_le_norm _
  have hdeg : (Q_b b).natDegree = b - 2 := Q_b_natDegree hb
  have hdiv_le : ‖(Q_b b).eval (chiFR k)‖ / ‖1 + chiFR k‖ ≤ C₀ * (1 + |(k : ℝ)|) ^ (b - 2) := by
    calc ‖(Q_b b).eval (chiFR k)‖ / ‖1 + chiFR k‖
        ≤ ‖(Q_b b).eval (chiFR k)‖ := div_le_self (norm_nonneg _) h1chi_ge
      _ ≤ C₀ * (1 + |(k : ℝ)|) ^ (b - 2) := by rw [← hdeg]; exact hQ k
  have hG := norm_Gamma_one_sub_chiFR_le k
  calc ‖(Q_b b).eval (chiFR k)‖ / ‖1 + chiFR k‖ * ‖Complex.Gamma (1 - chiFR k)‖
      ≤ (C₀ * (1 + |(k : ℝ)|) ^ (b - 2)) *
          (C₁ * (1 + |(k : ℝ)|) * Real.exp (-Real.pi ^ 2 * |(k : ℝ)| / Real.log 2)) :=
        mul_le_mul hdiv_le hG (norm_nonneg _) (by positivity)
    _ = (C₀ * C₁) * ((1 + |(k : ℝ)|) ^ (b - 2) * (1 + |(k : ℝ)|)) *
          Real.exp (-Real.pi ^ 2 * |(k : ℝ)| / Real.log 2) := by ring
    _ = (C₀ * C₁) * (1 + |(k : ℝ)|) ^ (b - 1) * Real.exp (-Real.pi ^ 2 * |(k : ℝ)| / Real.log 2) := by
        rw [← pow_succ, show b - 2 + 1 = b - 1 by omega]
    _ ≤ C * (1 + |(k : ℝ)|) ^ (b - 1) * Real.exp (-Real.pi ^ 2 * |(k : ℝ)| / Real.log 2) := by
        gcongr; exact le_max_right _ _

/-! ### Reusable Differentiation Engine for `∑_{k ∈ ℤ} a_k exp(χ_k log z)` on `{0 < z.re}` -/

private lemma abs_arg_le_pi_div_two_sub {z : ℂ} (hz : 0 < z.re) :
    |z.arg| ≤ Real.pi / 2 - z.re / ‖z‖ := by
  have hne : z ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hz; linarith
  have hlt : |z.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have hcos : Real.cos |z.arg| = z.re / ‖z‖ := by
    rw [Real.cos_abs, Complex.cos_arg hne]
  have hsin : Real.sin (Real.pi / 2 - |z.arg|) = Real.cos |z.arg| := Real.sin_pi_div_two_sub _
  have hle : Real.sin (Real.pi / 2 - |z.arg|) ≤ Real.pi / 2 - |z.arg| :=
    Real.sin_le (by linarith)
  linarith

/-- Uniform norm bound for `exp (χ_k * log z)` on a compact ball `Metric.ball z₀ (z₀.re / 2) ⊆ {0 < z.re}`. -/
private lemma norm_exp_chiFR_log_le_on_ball {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    ∃ α : ℝ, 0 < α ∧ α < Real.pi ^ 2 / Real.log 2 ∧
      ∀ (k : ℤ) (z : ℂ), z ∈ Metric.ball z₀ (z₀.re / 2) →
        ‖Complex.exp (chiFR k * Complex.log z)‖ ≤ Real.exp (α * |(k : ℝ)|) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let r : ℝ := z₀.re / 2
  have hr : 0 < r := half_pos hz₀
  let c : ℝ := r / (‖z₀‖ + r)
  have hc_pos : 0 < c := by dsimp only [c]; positivity
  have hc_lt : c < Real.pi / 2 := by
    have hle1 : c ≤ 1 := by
      dsimp only [c]; rw [div_le_one (by positivity)]; linarith [norm_nonneg z₀]
    linarith [Real.pi_gt_three]
  let θ : ℝ := Real.pi / 2 - c
  have hθ_pos : 0 < θ := sub_pos.mpr hc_lt
  have hθ_lt : θ < Real.pi / 2 := by dsimp only [θ]; linarith
  refine ⟨2 * Real.pi * θ / Real.log 2, by positivity, ?_, fun k z hz => ?_⟩
  · rw [div_lt_div_iff_of_pos_right hlog2]
    nlinarith [Real.pi_pos]
  · have hdist : ‖z - z₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hz_re : r < z.re := by
      have h1 : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
        rw [← Complex.sub_re]; exact Complex.abs_re_le_norm (z - z₀)
      have h2 := (abs_lt.mp (lt_of_le_of_lt h1 hdist)).1
      dsimp only [r] at h2 ⊢; linarith
    have hz_norm : ‖z‖ ≤ ‖z₀‖ + r := by
      calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ ‖z₀‖ + r := by linarith
    have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr fun h0 => by rw [h0, Complex.zero_re] at hz_re; linarith
    have hratio : c ≤ z.re / ‖z‖ := by
      dsimp only [c]
      exact div_le_div₀ (by linarith) hz_re.le hz_pos hz_norm
    have harg_le : |z.arg| ≤ θ := by
      have := abs_arg_le_pi_div_two_sub (lt_trans hr hz_re)
      dsimp only [θ]; linarith
    rw [Complex.norm_exp]
    have hre : (chiFR k * Complex.log z).re = -(2 * Real.pi * (k : ℝ) / Real.log 2) * z.arg := by
      unfold chiFR
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
        Complex.I_im, mul_one, sub_zero, Complex.mul_im, add_zero, Complex.log_im]
      ring
    rw [hre]
    refine Real.exp_le_exp.mpr ?_
    have h1 : -(2 * Real.pi * (k : ℝ) / Real.log 2) * z.arg ≤
        |2 * Real.pi * (k : ℝ) / Real.log 2 * z.arg| := by
      simpa [neg_mul] using neg_le_abs (2 * Real.pi * (k : ℝ) / Real.log 2 * z.arg)
    rw [abs_mul, abs_div, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi),
      abs_of_pos hlog2] at h1
    have h2 : 2 * Real.pi * |(k : ℝ)| / Real.log 2 * |z.arg| ≤
        2 * Real.pi * θ / Real.log 2 * |(k : ℝ)| := by
      calc 2 * Real.pi * |(k : ℝ)| / Real.log 2 * |z.arg|
          ≤ 2 * Real.pi * |(k : ℝ)| / Real.log 2 * θ :=
            mul_le_mul_of_nonneg_left harg_le (by positivity)
        _ = 2 * Real.pi * θ / Real.log 2 * |(k : ℝ)| := by ring
    exact h1.trans h2

/-- Any Dirichlet-type Fourier series `∑_{k ∈ ℤ} a_k exp(χ_k log z)` whose coefficients satisfy
`‖a_k‖ ≤ C (1 + |k|)^d exp(-π² |k| / log 2)` is holomorphic on `{0 < z.re}` with exact term-by-term
derivative `z⁻¹ * ∑_{k ∈ ℤ} a_k χ_k exp(χ_k log z)`. -/
private lemma hasDerivAt_tsum_chiFR {a : ℤ → ℂ} {C : ℝ} {d : ℕ}
    (ha : ∀ k : ℤ, ‖a k‖ ≤ C * (1 + |(k : ℝ)|) ^ d * Real.exp (-Real.pi ^ 2 * |(k : ℝ)| / Real.log 2))
    {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    Summable (fun k : ℤ => a k * Complex.exp (chiFR k * Complex.log z₀)) ∧
    Summable (fun k : ℤ => a k * chiFR k * Complex.exp (chiFR k * Complex.log z₀)) ∧
    HasDerivAt (fun z : ℂ => ∑' k : ℤ, a k * Complex.exp (chiFR k * Complex.log z))
      (z₀⁻¹ * ∑' k : ℤ, a k * chiFR k * Complex.exp (chiFR k * Complex.log z₀)) z₀ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let r : ℝ := z₀.re / 2
  have hr : 0 < r := half_pos hz₀
  obtain ⟨α, hα_pos, hα_lt, hball_exp⟩ := norm_exp_chiFR_log_le_on_ball hz₀
  let β : ℝ := Real.pi ^ 2 / Real.log 2 - α
  have hβ : 0 < β := sub_pos.mpr hα_lt
  let L : ℝ := 2 * Real.pi / Real.log 2
  have hL : 0 < L := by positivity
  have hC0 : 0 ≤ C := by
    have h0 := ha 0
    simp only [Int.cast_zero, abs_zero, add_zero, one_pow, mul_one, mul_zero, zero_div, Real.exp_zero] at h0
    exact (norm_nonneg _).trans h0
  have hterm_bd : ∀ (k : ℤ) (z : ℂ), z ∈ Metric.ball z₀ r →
      ‖a k * Complex.exp (chiFR k * Complex.log z)‖ ≤
        C * (1 + |(k : ℝ)|) ^ d * Real.exp (-β * |(k : ℝ)|) := fun k z hz => by
    rw [norm_mul]
    calc ‖a k‖ * ‖Complex.exp (chiFR k * Complex.log z)‖
        ≤ (C * (1 + |(k : ℝ)|) ^ d * Real.exp (-Real.pi ^ 2 * |(k : ℝ)| / Real.log 2)) *
            Real.exp (α * |(k : ℝ)|) :=
          mul_le_mul (ha k) (hball_exp k z hz) (norm_nonneg _) (by positivity)
      _ = C * (1 + |(k : ℝ)|) ^ d * Real.exp (-β * |(k : ℝ)|) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; dsimp only [β]; ring
  have hderiv_bd : ∀ (k : ℤ) (z : ℂ), z ∈ Metric.ball z₀ r →
      ‖a k * (chiFR k * z⁻¹) * Complex.exp (chiFR k * Complex.log z)‖ ≤
        (C * L / r) * (1 + |(k : ℝ)|) ^ (d + 1) * Real.exp (-β * |(k : ℝ)|) := fun k z hz => by
    have hdist : ‖z - z₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hz_re : r < z.re := by
      have h1 : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
        rw [← Complex.sub_re]; exact Complex.abs_re_le_norm (z - z₀)
      have h2 := (abs_lt.mp (lt_of_le_of_lt h1 hdist)).1
      dsimp only [r] at h2 ⊢; linarith
    have hz_norm : r ≤ ‖z‖ := le_trans hz_re.le (Complex.re_le_norm z)
    have hchi_le : ‖chiFR k‖ ≤ L * (1 + |(k : ℝ)|) := by
      unfold chiFR
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        show 2 * Real.pi * (k : ℝ) / Real.log 2 = L * (k : ℝ) by dsimp only [L]; ring,
        abs_mul, abs_of_pos hL]
      nlinarith [abs_nonneg (k : ℝ)]
    have hinv_le : ‖z⁻¹‖ ≤ r⁻¹ := by
      rw [norm_inv]; exact inv_anti₀ hr hz_norm
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖a k‖ * (‖chiFR k‖ * ‖z⁻¹‖) * ‖Complex.exp (chiFR k * Complex.log z)‖
        = ‖chiFR k‖ * ‖z⁻¹‖ * ‖a k * Complex.exp (chiFR k * Complex.log z)‖ := by rw [norm_mul]; ring
      _ ≤ (L * (1 + |(k : ℝ)|)) * r⁻¹ * (C * (1 + |(k : ℝ)|) ^ d * Real.exp (-β * |(k : ℝ)|)) := by
          gcongr
          · exact hterm_bd k z hz
      _ = (C * L / r) * (1 + |(k : ℝ)|) ^ (d + 1) * Real.exp (-β * |(k : ℝ)|) := by
          rw [pow_succ]; ring
  have hsum0 : Summable (fun k : ℤ => C * (1 + |(k : ℝ)|) ^ d * Real.exp (-β * |(k : ℝ)|)) := by
    simpa [mul_assoc] using (summable_poly_mul_exp_neg_int d hβ).mul_left C
  have hsum1 : Summable (fun k : ℤ => (C * L / r) * (1 + |(k : ℝ)|) ^ (d + 1) * Real.exp (-β * |(k : ℝ)|)) := by
    simpa [mul_assoc] using (summable_poly_mul_exp_neg_int (d + 1) hβ).mul_left (C * L / r)
  have hmem0 : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
  have hs0 : Summable (fun k : ℤ => a k * Complex.exp (chiFR k * Complex.log z₀)) :=
    Summable.of_norm_bounded hsum0 fun k => hterm_bd k z₀ hmem0
  have hs1_raw : Summable (fun k : ℤ => a k * (chiFR k * z₀⁻¹) * Complex.exp (chiFR k * Complex.log z₀)) :=
    Summable.of_norm_bounded hsum1 fun k => hderiv_bd k z₀ hmem0
  have hs1 : Summable (fun k : ℤ => a k * chiFR k * Complex.exp (chiFR k * Complex.log z₀)) := by
    refine (hs1_raw.mul_left z₀).congr fun k => ?_
    have hz₀_ne : z₀ ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hz₀; linarith
    field_simp [hz₀_ne]
  refine ⟨hs0, hs1, ?_⟩
  -- Differentiate positive and negative `ℕ` halves separately via `hasDerivAt_tsum_of_isPreconnected`!
  have hterm_deriv : ∀ (k : ℤ) (z : ℂ), z ∈ Metric.ball z₀ r →
      HasDerivAt (fun w : ℂ => a k * Complex.exp (chiFR k * Complex.log w))
        (a k * (chiFR k * z⁻¹) * Complex.exp (chiFR k * Complex.log z)) z := by
    intro k z hz
    have hdist : ‖z - z₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hz_re : 0 < z.re := by
      have h1 : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
        rw [← Complex.sub_re]; exact Complex.abs_re_le_norm (z - z₀)
      have h2 := (abs_le.mp (h1.trans hdist.le)).1
      dsimp only [r] at h2; linarith
    have hslit : z ∈ Complex.slitPlane := Or.inl hz_re
    have hd_log : HasDerivAt (fun w : ℂ => chiFR k * Complex.log w) (chiFR k * z⁻¹) z :=
      (Complex.hasDerivAt_log hslit).const_mul (chiFR k)
    have hd_exp : HasDerivAt (fun w : ℂ => Complex.exp (chiFR k * Complex.log w))
        (Complex.exp (chiFR k * Complex.log z) * (chiFR k * z⁻¹)) z := hd_log.cexp
    simpa [mul_assoc, mul_left_comm, mul_comm] using hd_exp.const_mul (a k)
  let negIdx : ℕ → ℤ := fun n => -(n + 1 : ℤ)
  have hneg_inj : Function.Injective negIdx := fun a₁ a₂ h => by dsimp only [negIdx] at h; omega
  have hd_pos : HasDerivAt
      (fun w : ℂ => ∑' n : ℕ, a (n : ℤ) * Complex.exp (chiFR (n : ℤ) * Complex.log w))
      (∑' n : ℕ, a (n : ℤ) * (chiFR (n : ℤ) * z₀⁻¹) * Complex.exp (chiFR (n : ℤ) * Complex.log z₀)) z₀ :=
    hasDerivAt_tsum_of_isPreconnected (hsum1.comp_injective Int.ofNat_injective)
      Metric.isOpen_ball (convex_ball z₀ r).isPreconnected
      (fun n z hz => hterm_deriv (n : ℤ) z hz) (fun n z hz => hderiv_bd (n : ℤ) z hz)
      hmem0 (hs0.comp_injective Int.ofNat_injective) hmem0
  have hd_neg : HasDerivAt
      (fun w : ℂ => ∑' n : ℕ, a (negIdx n) * Complex.exp (chiFR (negIdx n) * Complex.log w))
      (∑' n : ℕ, a (negIdx n) * (chiFR (negIdx n) * z₀⁻¹) * Complex.exp (chiFR (negIdx n) * Complex.log z₀)) z₀ :=
    hasDerivAt_tsum_of_isPreconnected (hsum1.comp_injective hneg_inj)
      Metric.isOpen_ball (convex_ball z₀ r).isPreconnected
      (fun n z hz => hterm_deriv (negIdx n) z hz) (fun n z hz => hderiv_bd (negIdx n) z hz)
      hmem0 (hs0.comp_injective hneg_inj) hmem0
  have heq_nhds : (fun w : ℂ => ∑' k : ℤ, a k * Complex.exp (chiFR k * Complex.log w)) =ᶠ[𝓝 z₀]
      fun w : ℂ => (∑' n : ℕ, a (n : ℤ) * Complex.exp (chiFR (n : ℤ) * Complex.log w)) +
        (∑' n : ℕ, a (negIdx n) * Complex.exp (chiFR (negIdx n) * Complex.log w)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hmem0] with w hw
    exact tsum_int_eq_nat_add_negSucc (Summable.of_norm_bounded hsum0 fun k => hterm_bd k w hw)
  have hd_sum := (hd_pos.add hd_neg).congr_of_eventuallyEq heq_nhds
  convert hd_sum using 1
  rw [← tsum_mul_left, tsum_int_eq_nat_add_negSucc]
  · congr 1 <;> (refine tsum_congr fun n => ?_; ring)
  · exact hs1.mul_left z₀⁻¹

/-! ### Master Lacunary Function `masterLacunary`, `A_func`, and Poisson/Fourier Identity on `{0 < z.re}` -/

/-- Master lacunary dyadic exponential series `u(x) = ∑_{m ∈ ℤ} 2^m exp(-2^m x)` on `{0 < x.re}`. -/
@[expose] def masterLacunary (x : ℂ) : ℂ :=
  ∑' m : ℤ, (2 : ℂ) ^ m * Complex.exp (-(2 : ℂ) ^ m * x)

/-- Weighted dyadic series `A(x) = x · masterLacunary x = ∑_{m ∈ ℤ} (2^m x) exp(-2^m x)`. -/
@[expose] def A_func (x : ℂ) : ℂ := x * masterLacunary x

private lemma norm_masterLacunary_term_le {δ : ℝ} (hδ : 0 < δ) {x : ℂ} (hx : δ ≤ x.re) :
    (∀ m : ℕ, ‖(2 : ℂ) ^ (m : ℤ) * Complex.exp (-(2 : ℂ) ^ (m : ℤ) * x)‖ ≤ (2 / δ ^ 2) * (1 / 2 : ℝ) ^ m) ∧
    (∀ k : ℕ, ‖(2 : ℂ) ^ (-(k + 1 : ℤ)) * Complex.exp (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * x)‖ ≤ (1 / 2 : ℝ) ^ k) := by
  refine ⟨fun m => ?_, fun k => ?_⟩
  · rw [norm_mul, norm_zpow, Complex.norm_ofNat, zpow_natCast, Complex.norm_exp]
    have hre : (-(2 : ℂ) ^ (m : ℤ) * x).re = -(2 : ℝ) ^ m * x.re := by
      rw [zpow_natCast]
      have h2m : (2 : ℂ) ^ m = (((2 : ℝ) ^ m : ℝ) : ℂ) := by push_cast; rfl
      rw [neg_mul, h2m, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      ring
    rw [hre]
    have hpos : 0 ≤ (2 : ℝ) ^ m * δ := by positivity
    have hexp_ge : ((2 : ℝ) ^ m * δ) ^ 2 / 2 ≤ Real.exp ((2 : ℝ) ^ m * δ) := by
      simpa using Real.pow_div_factorial_le_exp ((2 : ℝ) ^ m * δ) hpos 2
    have hexp_le : Real.exp (-(2 : ℝ) ^ m * x.re) ≤ Real.exp (-((2 : ℝ) ^ m * δ)) :=
      Real.exp_le_exp.mpr (by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) m])
    have hinv_le : Real.exp (-((2 : ℝ) ^ m * δ)) ≤ 2 / ((2 : ℝ) ^ m * δ) ^ 2 := by
      rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
      linarith
    calc (2 : ℝ) ^ m * Real.exp (-(2 : ℝ) ^ m * x.re)
        ≤ (2 : ℝ) ^ m * (2 / ((2 : ℝ) ^ m * δ) ^ 2) :=
          mul_le_mul_of_nonneg_left (hexp_le.trans hinv_le) (by positivity)
      _ = (2 / δ ^ 2) * (1 / 2 : ℝ) ^ m := by
          rw [mul_pow, one_div, inv_pow]
          have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
          field_simp [h2m, hδ.ne']
  · rw [norm_mul, norm_zpow, Complex.norm_ofNat, two_zpow_neg_succ_real, Complex.norm_exp]
    have hre : (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * x).re = -(1 / 2 : ℝ) ^ (k + 1) * x.re := by
      rw [neg_mul, two_zpow_neg_succ_complex]
      have hcast : ((2 : ℂ) ^ (k + 1))⁻¹ = (((1 / 2 : ℝ) ^ (k + 1) : ℝ) : ℂ) := by
        rw [one_div, inv_pow]; push_cast; rfl
      rw [hcast, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      ring
    rw [hre]
    have hexp1 : Real.exp (-(1 / 2 : ℝ) ^ (k + 1) * x.re) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hx0 : 0 ≤ x.re := by linarith
      have : 0 ≤ (1 / 2 : ℝ) ^ (k + 1) * x.re := by positivity
      linarith
    calc (1 / 2 : ℝ) ^ (k + 1) * Real.exp (-(1 / 2 : ℝ) ^ (k + 1) * x.re)
        ≤ (1 / 2 : ℝ) ^ (k + 1) * 1 := mul_le_mul_of_nonneg_left hexp1 (by positivity)
      _ ≤ (1 / 2 : ℝ) ^ k := by
          rw [mul_one, pow_succ]; nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k]

lemma summable_masterLacunary_term {x : ℂ} (hx : 0 < x.re) :
    Summable (fun m : ℤ => (2 : ℂ) ^ m * Complex.exp (-(2 : ℂ) ^ m * x)) := by
  have hbd := norm_masterLacunary_term_le hx (le_rfl : x.re ≤ x.re)
  let f : ℤ → ℂ := fun m => (2 : ℂ) ^ m * Complex.exp (-(2 : ℂ) ^ m * x)
  have h1 : Summable (fun m : ℕ => f (m : ℤ)) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _) hbd.1
  let negIdx : ℕ → ℤ := fun k => -(k + 1 : ℤ)
  have hneg_inj : Function.Injective negIdx := fun a₁ a₂ h => by dsimp only [negIdx] at h; omega
  have h2 : Summable (fun k : ℕ => f (negIdx k)) :=
    Summable.of_norm_bounded (summable_geometric_of_lt_one (by norm_num) (by norm_num)) hbd.2
  have hsplit : f = (fun m : ℤ => if 0 ≤ m then f m else 0) + (fun m : ℤ => if 0 ≤ m then 0 else f m) := by
    funext m; simp only [Pi.add_apply]; split_ifs <;> ring
  have hs1 : Summable (fun m : ℤ => if 0 ≤ m then f m else 0) := by
    refine (Int.ofNat_injective.summable_iff (f := fun m : ℤ => if 0 ≤ m then f m else 0) ?_).mp ?_
    · intro m hm
      have hneg : ¬ (0 ≤ m) := fun h0 => hm ⟨m.toNat, Int.toNat_of_nonneg h0⟩
      simp [hneg]
    · exact h1.congr fun n => by simp
  have hs2 : Summable (fun m : ℤ => if 0 ≤ m then 0 else f m) := by
    refine (hneg_inj.summable_iff (f := fun m : ℤ => if 0 ≤ m then 0 else f m) ?_).mp ?_
    · intro m hm
      have hpos : 0 ≤ m := by
        by_contra hlt
        exact hm ⟨(-m - 1).toNat, by
          dsimp only [negIdx]
          have := Int.toNat_of_nonneg (show 0 ≤ -m - 1 by omega)
          omega⟩
      simp [hpos]
    · exact h2.congr fun n => by
        have hneg : ¬ (0 ≤ negIdx n) := by dsimp only [negIdx]; omega
        change f (negIdx n) = if 0 ≤ negIdx n then 0 else f (negIdx n)
        simp [hneg]
  change Summable f
  rw [hsplit]
  exact hs1.add hs2

lemma masterLacunary_differentiableOn :
    DifferentiableOn ℂ masterLacunary {z : ℂ | 0 < z.re} := by
  intro z₀ hz₀
  change 0 < z₀.re at hz₀
  let r : ℝ := z₀.re / 2
  have hr : 0 < r := half_pos hz₀
  have hre_ball : ∀ z ∈ Metric.ball z₀ r, r ≤ z.re := fun z hz => by
    have hdist : ‖z - z₀‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have h1 : |z.re - z₀.re| ≤ ‖z - z₀‖ := by
      rw [← Complex.sub_re]; exact Complex.abs_re_le_norm (z - z₀)
    have h2 := (abs_le.mp (h1.trans hdist.le)).1
    dsimp only [r] at h2 ⊢; linarith
  let negIdx : ℕ → ℤ := fun k => -(k + 1 : ℤ)
  have hsplit : ∀ z ∈ Metric.ball z₀ r, masterLacunary z =
      (∑' m : ℕ, (2 : ℂ) ^ (m : ℤ) * Complex.exp (-(2 : ℂ) ^ (m : ℤ) * z)) +
      (∑' k : ℕ, (2 : ℂ) ^ (negIdx k) * Complex.exp (-(2 : ℂ) ^ (negIdx k) * z)) := fun z hz =>
    tsum_int_eq_nat_add_negSucc (summable_masterLacunary_term (lt_of_lt_of_le hr (hre_ball z hz)))
  have hunif1 : TendstoUniformlyOn
      (fun N z => ∑ m ∈ Finset.range N, (2 : ℂ) ^ (m : ℤ) * Complex.exp (-(2 : ℂ) ^ (m : ℤ) * z))
      (fun z => ∑' m : ℕ, (2 : ℂ) ^ (m : ℤ) * Complex.exp (-(2 : ℂ) ^ (m : ℤ) * z))
      atTop (Metric.ball z₀ r) :=
    tendstoUniformlyOn_tsum_nat ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)
      fun m z hz => (norm_masterLacunary_term_le hr (hre_ball z hz)).1 m
  have hunif2 : TendstoUniformlyOn
      (fun N z => ∑ k ∈ Finset.range N, (2 : ℂ) ^ (negIdx k) * Complex.exp (-(2 : ℂ) ^ (negIdx k) * z))
      (fun z => ∑' k : ℕ, (2 : ℂ) ^ (negIdx k) * Complex.exp (-(2 : ℂ) ^ (negIdx k) * z))
      atTop (Metric.ball z₀ r) :=
    tendstoUniformlyOn_tsum_nat (summable_geometric_of_lt_one (by norm_num) (by norm_num))
      fun k z hz => (norm_masterLacunary_term_le hr (hre_ball z hz)).2 k
  have hd1 : DifferentiableOn ℂ (fun z => ∑' m : ℕ, (2 : ℂ) ^ (m : ℤ) * Complex.exp (-(2 : ℂ) ^ (m : ℤ) * z))
      (Metric.ball z₀ r) :=
    hunif1.tendstoLocallyUniformlyOn.differentiableOn
      (Filter.Eventually.of_forall fun N => DifferentiableOn.fun_sum fun m _ => by fun_prop)
      Metric.isOpen_ball
  have hd2 : DifferentiableOn ℂ (fun z => ∑' k : ℕ, (2 : ℂ) ^ (negIdx k) * Complex.exp (-(2 : ℂ) ^ (negIdx k) * z))
      (Metric.ball z₀ r) :=
    hunif2.tendstoLocallyUniformlyOn.differentiableOn
      (Filter.Eventually.of_forall fun N => DifferentiableOn.fun_sum fun k _ => by fun_prop)
      Metric.isOpen_ball
  have hball : DifferentiableOn ℂ masterLacunary (Metric.ball z₀ r) :=
    (hd1.add hd2).congr fun z hz => hsplit z hz
  exact ((hball z₀ (Metric.mem_ball_self hr)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt

lemma A_func_differentiableOn : DifferentiableOn ℂ A_func {z : ℂ | 0 < z.re} :=
  differentiableOn_id.mul masterLacunary_differentiableOn

/-- Exact Poisson/Fourier series of `A_func z = z · masterLacunary z` across the entire open right
half-plane `{0 < z.re}`. -/
theorem A_func_fourier_rhp {z : ℂ} (hz : 0 < z.re) :
    A_func z = ((Real.log 2 : ℝ) : ℂ)⁻¹ *
      ∑' k : ℤ, Complex.Gamma (1 - chiFR k) * Complex.exp (chiFR k * Complex.log z) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Step 1: Prove the identity for positive reals `x > 0` by applying `fourier_series_one_periodic`
  -- to `g u = A_func (2^u)`.
  let g : ℝ → ℂ := fun u => A_func (((Real.exp (Real.log 2 * u) : ℝ) : ℂ))
  have hg_cont : Continuous g :=
    A_func_differentiableOn.continuousOn.comp_continuous
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
      fun u => by change 0 < ((Real.exp (Real.log 2 * u) : ℝ) : ℂ).re; rw [Complex.ofReal_re]; exact Real.exp_pos _
  have hg_per : ∀ u : ℝ, g (u + 1) = g u := fun u => by
    dsimp only [g]
    unfold A_func masterLacunary
    have hexp1 : ((Real.exp (Real.log 2 * (u + 1)) : ℝ) : ℂ) =
        2 * ((Real.exp (Real.log 2 * u) : ℝ) : ℂ) := by
      have hr : Real.exp (Real.log 2 * (u + 1)) = 2 * Real.exp (Real.log 2 * u) := by
        rw [mul_add, mul_one, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), mul_comm]
      exact_mod_cast hr
    rw [hexp1, ← tsum_mul_left, ← tsum_mul_left]
    rw [← (Equiv.addRight (-1 : ℤ)).tsum_eq]
    refine tsum_congr fun m => ?_
    change 2 * ((Real.exp (Real.log 2 * u) : ℝ) : ℂ) *
      ((2 : ℂ) ^ (m + (-1 : ℤ)) * Complex.exp (-(2 : ℂ) ^ (m + (-1 : ℤ)) *
        (2 * ((Real.exp (Real.log 2 * u) : ℝ) : ℂ)))) = _
    have hpow : (2 : ℂ) ^ (m + (-1 : ℤ)) * 2 = (2 : ℂ) ^ m := by
      rw [zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0), zpow_neg_one]; ring
    have harg : -(2 : ℂ) ^ (m + (-1 : ℤ)) * (2 * ((Real.exp (Real.log 2 * u) : ℝ) : ℂ)) =
        -(2 : ℂ) ^ m * ((Real.exp (Real.log 2 * u) : ℝ) : ℂ) := by
      calc -(2 : ℂ) ^ (m + (-1 : ℤ)) * (2 * ((Real.exp (Real.log 2 * u) : ℝ) : ℂ))
          = -((2 : ℂ) ^ (m + (-1 : ℤ)) * 2) * ((Real.exp (Real.log 2 * u) : ℝ) : ℂ) := by ring
        _ = -(2 : ℂ) ^ m * ((Real.exp (Real.log 2 * u) : ℝ) : ℂ) := by rw [hpow]
    rw [harg]
    calc 2 * ((Real.exp (Real.log 2 * u) : ℝ) : ℂ) *
          ((2 : ℂ) ^ (m + (-1 : ℤ)) * Complex.exp (-(2 : ℂ) ^ m * ((Real.exp (Real.log 2 * u) : ℝ) : ℂ)))
        = ((Real.exp (Real.log 2 * u) : ℝ) : ℂ) *
            (((2 : ℂ) ^ (m + (-1 : ℤ)) * 2) * Complex.exp (-(2 : ℂ) ^ m * ((Real.exp (Real.log 2 * u) : ℝ) : ℂ))) := by ring
      _ = _ := by rw [hpow]
  -- Compute the `k`-th Fourier coefficient of `g` by periodization + `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`!
  have hg_coeff : ∀ k : ℤ,
      (∫ u : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        g u * Complex.exp (-2 * (Real.pi : ℂ) * I * (k : ℂ) * (u : ℂ))) =
        ((Real.log 2 : ℝ) : ℂ)⁻¹ * Complex.Gamma (1 - chiFR k) := by
    intro k
    let h : ℝ → ℂ := fun v =>
      ((Real.exp (Real.log 2 * v) : ℝ) : ℂ) * Complex.exp (-((Real.exp (Real.log 2 * v) : ℝ) : ℂ)) *
        Complex.exp (-2 * (Real.pi : ℂ) * I * (k : ℂ) * (v : ℂ))
    -- Pointwise domination `‖h v‖ ≤ 2 * exp(-log 2 * |v|)` gives global integrability on `ℝ`!
    have hh_norm : ∀ v : ℝ, ‖h v‖ ≤ 2 * Real.exp (-Real.log 2 * |v|) := fun v => by
      dsimp only [h]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        Complex.norm_exp, Complex.norm_exp]
      have hre1 : (-((Real.exp (Real.log 2 * v) : ℝ) : ℂ)).re = -Real.exp (Real.log 2 * v) := by
        rw [Complex.neg_re, Complex.ofReal_re]
      have hre2 : (-2 * (Real.pi : ℂ) * I * (k : ℂ) * (v : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [hre1, hre2, Real.exp_zero, mul_one]
      let t : ℝ := Real.exp (Real.log 2 * v)
      have ht_pos : 0 < t := Real.exp_pos _
      rcases le_total 0 v with hv | hv
      · have hsq : t ^ 2 / 2 ≤ Real.exp t := by simpa using Real.pow_div_factorial_le_exp t ht_pos.le 2
        have h1 : t * Real.exp (-t) ≤ 2 / t := by
          rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) ht_pos]
          linarith
        have h2 : 2 / t = 2 * Real.exp (-Real.log 2 * |v|) := by
          dsimp only [t]; rw [abs_of_nonneg hv, div_eq_mul_inv, ← Real.exp_neg]; congr 2; ring
        exact h1.trans h2.le
      · have hexp1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        have h2 : t = Real.exp (-Real.log 2 * |v|) := by
          dsimp only [t]; rw [abs_of_nonpos hv]; congr 1; ring
        calc t * Real.exp (-t) ≤ t * 1 := mul_le_mul_of_nonneg_left hexp1 ht_pos.le
          _ = Real.exp (-Real.log 2 * |v|) := by rw [mul_one, h2]
          _ ≤ 2 * Real.exp (-Real.log 2 * |v|) := by linarith [Real.exp_pos (-Real.log 2 * |v|)]
    have hh_cont : Continuous h := by dsimp only [h]; fun_prop
    have hh_int : MeasureTheory.Integrable h volume := by
      have hdom_int : MeasureTheory.Integrable (fun v : ℝ => 2 * Real.exp (-Real.log 2 * |v|)) volume := by
        have hpos : MeasureTheory.IntegrableOn (fun v : ℝ => Real.exp (-Real.log 2 * v)) (Set.Ioi 0) volume :=
          integrableOn_exp_mul_Ioi (by linarith) 0
        have hneg : MeasureTheory.IntegrableOn (fun v : ℝ => Real.exp (Real.log 2 * v)) (Set.Iic 0) volume :=
          integrableOn_exp_mul_Iic hlog2 0
        have hpos' : MeasureTheory.IntegrableOn (fun v : ℝ => Real.exp (-Real.log 2 * |v|)) (Set.Ioi 0) volume :=
          hpos.congr_fun (fun v hv => by rw [abs_of_pos hv]) measurableSet_Ioi
        have hneg' : MeasureTheory.IntegrableOn (fun v : ℝ => Real.exp (-Real.log 2 * |v|)) (Set.Iic 0) volume :=
          hneg.congr_fun (fun v hv => by rw [abs_of_nonpos hv]; ring_nf) measurableSet_Iic
        have hunion : (Set.Iic (0 : ℝ) ∪ Set.Ioi (0 : ℝ)) = Set.univ := Set.Iic_union_Ioi
        have hall : MeasureTheory.IntegrableOn (fun v : ℝ => Real.exp (-Real.log 2 * |v|)) Set.univ volume := by
          rw [← hunion]; exact hneg'.union hpos'
        exact (MeasureTheory.integrableOn_univ.mp hall).const_mul 2
      exact hdom_int.mono' hh_cont.aestronglyMeasurable (Filter.Eventually.of_forall hh_norm)
    -- Step 1a: Rewrite `g u * exp(-2πi k u)` as `∑' m : ℤ, h (u + m)` and interchange `∫` and `∑'`.
    have hg_eq_tsum : ∀ u : ℝ, g u * Complex.exp (-2 * (Real.pi : ℂ) * I * (k : ℂ) * (u : ℂ)) =
        ∑' m : ℤ, h (u + (m : ℝ)) := fun u => by
      dsimp only [g, h]
      unfold A_func masterLacunary
      rw [mul_assoc, ← tsum_mul_right, ← tsum_mul_left]
      refine tsum_congr fun m => ?_
      have h2m : (2 : ℂ) ^ m * ((Real.exp (Real.log 2 * u) : ℝ) : ℂ) =
          ((Real.exp (Real.log 2 * (u + (m : ℝ))) : ℝ) : ℂ) := by
        rw [two_zpow_eq_cexp, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
        congr 1; push_cast; ring
      have hexp_shift : Complex.exp (-2 * (Real.pi : ℂ) * I * (k : ℂ) * ((u + (m : ℝ) : ℝ) : ℂ)) =
          Complex.exp (-2 * (Real.pi : ℂ) * I * (k : ℂ) * (u : ℂ)) := by
        push_cast
        rw [mul_add, Complex.exp_add,
          show -2 * (Real.pi : ℂ) * I * (k : ℂ) * (m : ℂ) = ((-(k * m) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) by
            push_cast; ring,
          Complex.exp_int_mul_two_pi_mul_I, mul_one]
      rw [hexp_shift]
      have harg_neg : -(2 : ℂ) ^ m * ((Real.exp (Real.log 2 * u) : ℝ) : ℂ) =
          -((Real.exp (Real.log 2 * (u + (m : ℝ))) : ℝ) : ℂ) := by
        rw [← h2m]; ring
      rw [harg_neg]
      calc ((Real.exp (Real.log 2 * u) : ℝ) : ℂ) *
            ((2 : ℂ) ^ m * Complex.exp (-((Real.exp (Real.log 2 * (u + (m : ℝ))) : ℝ) : ℂ)) *
              Complex.exp (-2 * (Real.pi : ℂ) * I * (k : ℂ) * (u : ℂ)))
          = ((2 : ℂ) ^ m * ((Real.exp (Real.log 2 * u) : ℝ) : ℂ)) *
              Complex.exp (-((Real.exp (Real.log 2 * (u + (m : ℝ))) : ℝ) : ℂ)) *
              Complex.exp (-2 * (Real.pi : ℂ) * I * (k : ℂ) * (u : ℂ)) := by ring
        _ = _ := by rw [h2m]
    -- Show `∑' m : ℤ, ∫⁻ u in Ioc (-1/2) (1/2), ‖h (u + m)‖ₑ ≠ ⊤`.
    have hlintegral_ne_top : ∑' m : ℤ, ∫⁻ u in Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ), ‖h (u + (m : ℝ))‖ₑ ≠ ⊤ := by
      have hbd_each : ∀ m : ℤ,
          ∫⁻ u in Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ), ‖h (u + (m : ℝ))‖ₑ ≤
            ENNReal.ofReal (4 * Real.exp (-Real.log 2 * |(m : ℝ)|)) := fun m => by
        calc ∫⁻ u in Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ), ‖h (u + (m : ℝ))‖ₑ
            ≤ ∫⁻ _u in Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ),
                ENNReal.ofReal (4 * Real.exp (-Real.log 2 * |(m : ℝ)|)) := by
              refine MeasureTheory.setLIntegral_mono' measurableSet_Ioc fun u hu => ?_
              rw [← ofReal_norm]
              refine ENNReal.ofReal_le_ofReal ?_
              have habs : |(m : ℝ)| - 1 / 2 ≤ |u + (m : ℝ)| := by
                have hu_abs : |u| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
                have htri := abs_sub_abs_le_abs_sub (u + (m : ℝ)) u
                simp only [add_sub_cancel_left] at htri
                have htri2 := abs_sub_abs_le_abs_sub ((m : ℝ)) (-u)
                rw [sub_neg_eq_add, abs_neg, add_comm] at htri2
                linarith
              calc ‖h (u + (m : ℝ))‖ ≤ 2 * Real.exp (-Real.log 2 * |u + (m : ℝ)|) := hh_norm _
                _ ≤ 2 * Real.exp (-Real.log 2 * (|(m : ℝ)| - 1 / 2)) :=
                    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by norm_num)
                _ = 2 * Real.exp (Real.log 2 / 2) * Real.exp (-Real.log 2 * |(m : ℝ)|) := by
                    rw [mul_assoc, ← Real.exp_add]; congr 2; ring
                _ ≤ 4 * Real.exp (-Real.log 2 * |(m : ℝ)|) := by
                    have hhalf : Real.exp (Real.log 2 / 2) ≤ 2 := by
                      calc Real.exp (Real.log 2 / 2) ≤ Real.exp (Real.log 2) :=
                            Real.exp_le_exp.mpr (by linarith)
                        _ = 2 := Real.exp_log (by norm_num)
                    nlinarith [Real.exp_pos (-Real.log 2 * |(m : ℝ)|)]
          _ = ENNReal.ofReal (4 * Real.exp (-Real.log 2 * |(m : ℝ)|)) := by
              rw [MeasureTheory.setLIntegral_const, Real.volume_Ioc]
              norm_num
      have hsum_real_m : Summable (fun m : ℤ => 4 * Real.exp (-Real.log 2 * |(m : ℝ)|)) := by
        have h0 := (summable_poly_mul_exp_neg_int 0 hlog2).mul_left 4
        simpa using h0
      refine ne_of_lt (lt_of_le_of_lt (tsum_le_tsum hbd_each) ?_)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum_real_m]
      exact ENNReal.ofReal_lt_top
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)]
    have hcongr_g : ∫ u in Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ),
        g u * Complex.exp (-2 * (Real.pi : ℂ) * I * (k : ℂ) * (u : ℂ)) =
        ∫ u in Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ), ∑' m : ℤ, h (u + (m : ℝ)) :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun u _ => hg_eq_tsum u
    rw [hcongr_g, MeasureTheory.integral_tsum (f := fun (m : ℤ) (u : ℝ) => h (u + (m : ℝ)))
      (fun m => (hh_cont.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
      hlintegral_ne_top]
    -- Translate each cell `Ioc (-1/2) (1/2)` to `Ico (m - 1/2) (m + 1/2)` and assemble via `integral_iUnion`!
    have hcell : ∀ m : ℤ, (∫ u in Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ), h (u + (m : ℝ))) =
        ∫ v in Set.Ico ((m : ℝ) - 1 / 2) ((m : ℝ) + 1 / 2), h v := fun m => by
      rw [← intervalIntegral.integral_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2),
        intervalIntegral.integral_comp_add_right h (m : ℝ),
        show (-1 / 2 : ℝ) + (m : ℝ) = (m : ℝ) - 1 / 2 by ring,
        show (1 / 2 : ℝ) + (m : ℝ) = (m : ℝ) + 1 / 2 by ring,
        intervalIntegral.integral_of_le (by linarith),
        ← MeasureTheory.integral_Ico_eq_integral_Ioc]
    rw [tsum_congr hcell]
    let cells : ℤ → Set ℝ := fun m => Set.Ico ((m : ℝ) - 1 / 2) ((m : ℝ) + 1 / 2)
    have hcells_union : (⋃ m : ℤ, cells m) = Set.univ := by
      ext v; simp only [Set.mem_iUnion, Set.mem_univ, iff_true, cells, Set.mem_Ico]
      refine ⟨⌊v + 1 / 2⌋, ?_, ?_⟩
      · linarith [Int.floor_le (v + 1 / 2)]
      · linarith [Int.lt_floor_add_one (v + 1 / 2)]
    have hcells_disj : Pairwise (Function.onFun Disjoint cells) := by
      intro m₁ m₂ hne
      change Disjoint (cells m₁) (cells m₂)
      rw [Set.disjoint_left]
      intro v hv₁ hv₂
      simp only [cells, Set.mem_Ico] at hv₁ hv₂
      have hlt1 : (m₁ : ℝ) < (m₂ : ℝ) + 1 := by linarith
      have hlt2 : (m₂ : ℝ) < (m₁ : ℝ) + 1 := by linarith
      have h1 : m₁ < m₂ + 1 := by exact_mod_cast hlt1
      have h2 : m₂ < m₁ + 1 := by exact_mod_cast hlt2
      omega
    have hunion_eq := MeasureTheory.integral_iUnion (f := h) (μ := volume) (s := cells)
      (fun _ => measurableSet_Ico) hcells_disj (by rw [hcells_union]; exact hh_int.integrableOn)
    rw [← hunion_eq, hcells_union, MeasureTheory.setIntegral_univ]
    -- Step 1b: Change variables `y = exp(log 2 * v)` via `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`!
    have hGamma_eq : Complex.Gamma (1 - chiFR k) =
        ∫ y in Set.Ioi (0 : ℝ), ((Real.exp (-y) : ℝ) : ℂ) * (y : ℂ) ^ ((1 - chiFR k) - 1) := by
      rw [Complex.Gamma_eq_integral]
      · rfl
      · rw [Complex.sub_re, Complex.one_re, chiFR_re, sub_zero]; norm_num
    have himg : (fun v : ℝ => Real.exp (Real.log 2 * v)) '' Set.univ = Set.Ioi (0 : ℝ) := by
      ext y; simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_Ioi]
      constructor
      · rintro ⟨v, rfl⟩; exact Real.exp_pos _
      · intro hy
        refine ⟨Real.log y / Real.log 2, ?_⟩
        rw [mul_div_cancel₀ _ hlog2.ne', Real.exp_log hy]
    have hchg := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Set.univ) (f := fun v : ℝ => Real.exp (Real.log 2 * v))
      (f' := fun v : ℝ => Real.log 2 * Real.exp (Real.log 2 * v))
      MeasurableSet.univ
      (fun v _ => by
        rw [hasDerivWithinAt_univ]
        have hd : HasDerivAt (fun x : ℝ => Real.log 2 * x) (Real.log 2) v := by
          simpa using (hasDerivAt_id v).const_mul (Real.log 2)
        have he := hd.exp
        convert he using 1; ring)
      (fun v₁ _ v₂ _ heq => by
        have := Real.exp_injective heq
        exact mul_left_cancel₀ hlog2.ne' this)
      (fun y : ℝ => ((Real.exp (-y) : ℝ) : ℂ) * (y : ℂ) ^ ((1 - chiFR k) - 1))
    rw [himg, ← hGamma_eq, MeasureTheory.setIntegral_univ] at hchg
    have hlog2_ne : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog2.ne'
    apply mul_left_cancel₀ hlog2_ne
    rw [mul_inv_cancel_left₀ hlog2_ne, ← MeasureTheory.integral_const_mul, hchg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    dsimp only
    rw [abs_of_pos (mul_pos hlog2 (Real.exp_pos _)), Complex.real_smul]
    have hcpow : (((Real.exp (Real.log 2 * v) : ℝ) : ℂ)) ^ ((1 - chiFR k) - 1) =
        Complex.exp (-2 * (Real.pi : ℂ) * I * (k : ℂ) * (v : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
        ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
      congr 1
      unfold chiFR
      push_cast
      field_simp [hlog2_ne]
      ring
    rw [hcpow, Complex.ofReal_exp]
    dsimp only [h]
    push_cast
    ring
  -- Step 2: Summability of `k ↦ (log 2)⁻¹ * Γ(1 - χ_k)` gives `A_func` Fourier series on `(0, ∞)`!
  have hsum_coeff : Summable (fun k : ℤ =>
      ∫ u : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        g u * Complex.exp (-2 * (Real.pi : ℂ) * I * (k : ℂ) * (u : ℂ))) := by
    have hdom := (summable_poly_mul_exp_neg_int 1 (α := Real.pi ^ 2 / Real.log 2) (by positivity)).mul_left
      (‖((Real.log 2 : ℝ) : ℂ)⁻¹‖ * (4 * Real.pi ^ 2 / Real.log 2 + 1))
    refine Summable.of_norm_bounded hdom fun k => ?_
    rw [hg_coeff k, norm_mul]
    have hG := norm_Gamma_one_sub_chiFR_le k
    calc ‖((Real.log 2 : ℝ) : ℂ)⁻¹‖ * ‖Complex.Gamma (1 - chiFR k)‖
        ≤ ‖((Real.log 2 : ℝ) : ℂ)⁻¹‖ *
            ((4 * Real.pi ^ 2 / Real.log 2 + 1) * (1 + |(k : ℝ)|) *
              Real.exp (-Real.pi ^ 2 * |(k : ℝ)| / Real.log 2)) :=
          mul_le_mul_of_nonneg_left hG (norm_nonneg _)
      _ = ‖((Real.log 2 : ℝ) : ℂ)⁻¹‖ * (4 * Real.pi ^ 2 / Real.log 2 + 1) *
            ((1 + |(k : ℝ)|) ^ 1 * Real.exp (-(Real.pi ^ 2 / Real.log 2) * |(k : ℝ)|)) := by
          rw [pow_one, show -(Real.pi ^ 2 / Real.log 2) * |(k : ℝ)| = -Real.pi ^ 2 * |(k : ℝ)| / Real.log 2 by ring]
          ring
  have hreal_eq : ∀ x : ℝ, 0 < x →
      A_func (x : ℂ) = ((Real.log 2 : ℝ) : ℂ)⁻¹ *
        ∑' k : ℤ, Complex.Gamma (1 - chiFR k) * Complex.exp (chiFR k * Complex.log (x : ℂ)) := by
    intro x hx
    have hfour := fourier_series_one_periodic hg_cont hg_per hsum_coeff (Real.log x / Real.log 2)
    have hgx : g (Real.log x / Real.log 2) = A_func (x : ℂ) := by
      dsimp only [g]
      rw [mul_div_cancel₀ _ hlog2.ne', Real.exp_log hx]
    rw [hgx] at hfour
    rw [hfour, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [hg_coeff k, ← Complex.ofReal_log hx.le]
    have harg : 2 * (Real.pi : ℂ) * I * (k : ℂ) * ((Real.log x / Real.log 2 : ℝ) : ℂ) =
        chiFR k * ((Real.log x : ℝ) : ℂ) := by
      unfold chiFR; push_cast; ring
    rw [harg]; ring
  -- Step 3: Extend from `(0, ∞)` to the open right half-plane `{0 < z.re}` by the identity theorem!
  let RHP : Set ℂ := {w : ℂ | 0 < w.re}
  have hRHP_open : IsOpen RHP := isOpen_lt continuous_const Complex.continuous_re
  have hRHP_conv : Convex ℝ RHP := by
    intro x hx y hy a b ha hb hab
    simp only [RHP, Set.mem_ofPred_eq, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hx hy ⊢
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1; simp [hy]
    · rcases eq_or_lt_of_le hb with rfl | hb'
      · have ha1 : a = 1 := by linarith
        subst ha1; simp [hx]
      · linarith [mul_pos ha' hx, mul_pos hb' hy]
  have hrhs_diff : DifferentiableOn ℂ
      (fun w : ℂ => ((Real.log 2 : ℝ) : ℂ)⁻¹ *
        ∑' k : ℤ, Complex.Gamma (1 - chiFR k) * Complex.exp (chiFR k * Complex.log w)) RHP := by
    intro w hw
    have hd := (hasDerivAt_tsum_chiFR (a := fun k => Complex.Gamma (1 - chiFR k))
      (C := 4 * Real.pi ^ 2 / Real.log 2 + 1) (d := 1)
      (fun k => by simpa [pow_one] using norm_Gamma_one_sub_chiFR_le k) hw).2.2
    exact (hd.const_mul _).differentiableAt.differentiableWithinAt
  exact eqOn_of_differentiableOn_eq_on_real_interval hRHP_open hRHP_conv.isPreconnected
    A_func_differentiableOn hrhs_diff (a := 1) (b := 2) (by norm_num)
    (fun x hx1 _ => by simp [RHP]; linarith)
    (fun x hx1 _ => hreal_eq x (by linarith)) hz

/-! ### Periodic Fluctuation `Φ_b`, Scaling Function `v_b`, Euler Operator, and Exact `v_b` ODE -/

/-- Periodic fluctuation `Φ_b(w) = ∑_{k ∈ ℤ} Φ̂_b(k) exp(2π i k w)`. -/
@[expose] def Phi_b (b : ℕ) (w : ℂ) : ℂ :=
  ∑' k : ℤ, Phi_hat b k * Complex.exp (2 * (Real.pi : ℂ) * I * (k : ℂ) * w)

/-- Scaling profile `v_b(z) = z · Φ_b(log z / log 2)` on `{0 < z.re}`. -/
@[expose] def v_b (b : ℕ) (z : ℂ) : ℂ :=
  z * Phi_b b (Complex.log z / ((Real.log 2 : ℝ) : ℂ))

/-- Euler derivative operator `θ(f)(z) = z · f'(z)`. -/
@[expose] def thetaOp (f : ℂ → ℂ) (z : ℂ) : ℂ := z * deriv f z

/-- `m`-fold iterate `θ^m(f)`. -/
@[expose] def thetaIter (m : ℕ) (f : ℂ → ℂ) : ℂ → ℂ := Nat.iterate thetaOp m f

/-- Polynomial Euler operator `Q(θ)(f)(z) = ∑_{m=0}^{\deg Q} Q_m · θ^m(f)(z)`. -/
@[expose] def eulerOp (Q : Polynomial ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ m ∈ Finset.range (Q.natDegree + 1), Q.coeff m * thetaIter m f z

/-- Constant offset `C_b = Φ̂_b(0) - Q_b(0)` in `v_b'(z) = C_b + (log 2) Q_b(θ) A(z)`. -/
@[expose] def C_b (b : ℕ) : ℂ := Phi_hat b 0 - (Q_b b).eval 0

lemma v_b_eq_tsum (b : ℕ) (z : ℂ) :
    v_b b z = z * ∑' k : ℤ, Phi_hat b k * Complex.exp (chiFR k * Complex.log z) := by
  unfold v_b Phi_b
  congr 1
  refine tsum_congr fun k => ?_
  congr 2
  unfold chiFR
  push_cast
  ring

/-- `m`-th Euler iterate of `A_func` on `{0 < z.re}` acts diagonally on every Fourier mode `χ_k`. -/
lemma thetaIter_A_func (m : ℕ) {z : ℂ} (hz : 0 < z.re) :
    thetaIter m A_func z = ((Real.log 2 : ℝ) : ℂ)⁻¹ *
      ∑' k : ℤ, (chiFR k) ^ m * Complex.Gamma (1 - chiFR k) * Complex.exp (chiFR k * Complex.log z) := by
  induction m generalizing z with
  | zero =>
    unfold thetaIter; simp only [Function.iterate_zero_apply, pow_zero, one_mul]
    exact A_func_fourier_rhp hz
  | succ m ih =>
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    let L : ℝ := 2 * Real.pi / Real.log 2
    have hL : 0 < L := by positivity
    have hchi_le : ∀ k : ℤ, ‖chiFR k‖ ≤ L * (1 + |(k : ℝ)|) := fun k => by
      unfold chiFR
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        show 2 * Real.pi * (k : ℝ) / Real.log 2 = L * (k : ℝ) by dsimp only [L]; ring,
        abs_mul, abs_of_pos hL]
      nlinarith [abs_nonneg (k : ℝ)]
    have ha_bd : ∀ k : ℤ, ‖(chiFR k) ^ m * Complex.Gamma (1 - chiFR k)‖ ≤
        (L ^ m * (4 * Real.pi ^ 2 / Real.log 2 + 1)) * (1 + |(k : ℝ)|) ^ (m + 1) *
          Real.exp (-Real.pi ^ 2 * |(k : ℝ)| / Real.log 2) := fun k => by
      rw [norm_mul, norm_pow]
      have h1 : ‖chiFR k‖ ^ m ≤ L ^ m * (1 + |(k : ℝ)|) ^ m := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hchi_le k) m
      have hG := norm_Gamma_one_sub_chiFR_le k
      calc ‖chiFR k‖ ^ m * ‖Complex.Gamma (1 - chiFR k)‖
          ≤ (L ^ m * (1 + |(k : ℝ)|) ^ m) *
              ((4 * Real.pi ^ 2 / Real.log 2 + 1) * (1 + |(k : ℝ)|) *
                Real.exp (-Real.pi ^ 2 * |(k : ℝ)| / Real.log 2)) :=
            mul_le_mul h1 hG (norm_nonneg _) (by positivity)
        _ = (L ^ m * (4 * Real.pi ^ 2 / Real.log 2 + 1)) * (1 + |(k : ℝ)|) ^ (m + 1) *
              Real.exp (-Real.pi ^ 2 * |(k : ℝ)| / Real.log 2) := by
            rw [pow_succ]; ring
    have hd := (hasDerivAt_tsum_chiFR ha_bd hz).2.2.const_mul ((Real.log 2 : ℝ) : ℂ)⁻¹
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have heq_nhds : thetaIter m A_func =ᶠ[𝓝 z]
        fun w : ℂ => ((Real.log 2 : ℝ) : ℂ)⁻¹ *
          ∑' k : ℤ, ((chiFR k) ^ m * Complex.Gamma (1 - chiFR k)) *
            Complex.exp (chiFR k * Complex.log w) := by
      filter_upwards [hopen.mem_nhds hz] with w hw
      exact ih hw
    have hd_iter : HasDerivAt (thetaIter m A_func)
        (((Real.log 2 : ℝ) : ℂ)⁻¹ *
          (z⁻¹ * ∑' k : ℤ, ((chiFR k) ^ m * Complex.Gamma (1 - chiFR k)) * chiFR k *
            Complex.exp (chiFR k * Complex.log z))) z :=
      hd.congr_of_eventuallyEq heq_nhds
    have hstep : thetaIter (m + 1) A_func z = thetaOp (thetaIter m A_func) z := by
      unfold thetaIter; rw [Function.iterate_succ_apply']
    rw [hstep]
    unfold thetaOp
    rw [hd_iter.deriv]
    have hz_ne : z ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hz; linarith
    have hcancel : z * (((Real.log 2 : ℝ) : ℂ)⁻¹ *
        (z⁻¹ * ∑' k : ℤ, ((chiFR k) ^ m * Complex.Gamma (1 - chiFR k)) * chiFR k *
          Complex.exp (chiFR k * Complex.log z))) =
        ((Real.log 2 : ℝ) : ℂ)⁻¹ *
          ∑' k : ℤ, ((chiFR k) ^ m * Complex.Gamma (1 - chiFR k)) * chiFR k *
            Complex.exp (chiFR k * Complex.log z) := by
      rw [← mul_assoc, mul_comm z ((Real.log 2 : ℝ) : ℂ)⁻¹, mul_assoc, ← mul_assoc z z⁻¹,
        mul_inv_cancel₀ hz_ne, one_mul]
    rw [hcancel]
    congr 1
    refine tsum_congr fun k => ?_
    rw [pow_succ]; ring

/-- Exact first-derivative formula for `v_b b` on `{0 < z.re}`. -/
lemma hasDerivAt_v_b {b : ℕ} (hb : 2 ≤ b) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (v_b b)
      (∑' k : ℤ, (1 + chiFR k) * Phi_hat b k * Complex.exp (chiFR k * Complex.log z)) z := by
  obtain ⟨C, _, hPhi⟩ := norm_Phi_hat_le hb
  obtain ⟨hs0, hs1, hd⟩ := hasDerivAt_tsum_chiFR hPhi hz
  have hmul := (hasDerivAt_id z).fun_mul hd
  dsimp only [id] at hmul
  have hfun : (fun w : ℂ => w * ∑' k : ℤ, Phi_hat b k * Complex.exp (chiFR k * Complex.log w)) = v_b b := by
    funext w; exact (v_b_eq_tsum b w).symm
  rw [hfun] at hmul
  convert hmul using 1
  have hz_ne : z ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hz; linarith
  have hcancel : 1 * (∑' k : ℤ, Phi_hat b k * Complex.exp (chiFR k * Complex.log z)) +
      z * (z⁻¹ * ∑' k : ℤ, Phi_hat b k * chiFR k * Complex.exp (chiFR k * Complex.log z)) =
      (∑' k : ℤ, Phi_hat b k * Complex.exp (chiFR k * Complex.log z)) +
      (∑' k : ℤ, Phi_hat b k * chiFR k * Complex.exp (chiFR k * Complex.log z)) := by
    rw [one_mul, ← mul_assoc, mul_inv_cancel₀ hz_ne, one_mul]
  rw [hcancel, ← hs0.tsum_add hs1]
  refine tsum_congr fun k => ?_
  ring

lemma v_b_differentiableOn {b : ℕ} (hb : 2 ≤ b) :
    DifferentiableOn ℂ (v_b b) {z : ℂ | 0 < z.re} :=
  fun _ hz => (hasDerivAt_v_b hb hz).differentiableAt.differentiableWithinAt

/-- **Crown Jewel of Section 3**: Exact linear differential identity linking `v_b'(z)` and `A(z) = z · masterLacunary z`
across the entire open right half-plane `{0 < z.re}`, with nonzero polynomial `Q_b b` of degree `b - 2`:
`deriv (v_b b) z = C_b b + (log 2) * Q_b(θ) A(z)`. -/
theorem deriv_v_b_eq_eulerOp_A_func {b : ℕ} (hb : 2 ≤ b) {z : ℂ} (hz : 0 < z.re) :
    deriv (v_b b) z = C_b b + ((Real.log 2 : ℝ) : ℂ) * eulerOp (Q_b b) A_func z := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_ne : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog2.ne'
  rw [(hasDerivAt_v_b hb hz).deriv]
  unfold eulerOp
  have heul : ((Real.log 2 : ℝ) : ℂ) *
      ∑ m ∈ Finset.range ((Q_b b).natDegree + 1), (Q_b b).coeff m * thetaIter m A_func z =
      ∑' k : ℤ, (Q_b b).eval (chiFR k) * Complex.Gamma (1 - chiFR k) *
        Complex.exp (chiFR k * Complex.log z) := by
    rw [Finset.mul_sum]
    have hterm_eq : ∀ m ∈ Finset.range ((Q_b b).natDegree + 1),
        ((Real.log 2 : ℝ) : ℂ) * ((Q_b b).coeff m * thetaIter m A_func z) =
          ∑' k : ℤ, (Q_b b).coeff m * (chiFR k) ^ m * Complex.Gamma (1 - chiFR k) *
            Complex.exp (chiFR k * Complex.log z) := fun m _ => by
      rw [thetaIter_A_func m hz, ← mul_assoc, mul_comm ((Real.log 2 : ℝ) : ℂ),
        mul_assoc, mul_inv_cancel_left₀ hlog2_ne, ← tsum_mul_left]
      refine tsum_congr fun k => by ring
    rw [Finset.sum_congr rfl hterm_eq]
    have hsum_each : ∀ m ∈ Finset.range ((Q_b b).natDegree + 1),
        Summable (fun k : ℤ => (Q_b b).coeff m * (chiFR k) ^ m * Complex.Gamma (1 - chiFR k) *
          Complex.exp (chiFR k * Complex.log z)) := by
      intro m _
      let L : ℝ := 2 * Real.pi / Real.log 2
      have hL : 0 < L := by positivity
      have hchi_le : ∀ k : ℤ, ‖chiFR k‖ ≤ L * (1 + |(k : ℝ)|) := fun k => by
        unfold chiFR
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          show 2 * Real.pi * (k : ℝ) / Real.log 2 = L * (k : ℝ) by dsimp only [L]; ring,
          abs_mul, abs_of_pos hL]
        nlinarith [abs_nonneg (k : ℝ)]
      have hraw := (hasDerivAt_tsum_chiFR
        (a := fun k => (Q_b b).coeff m * (chiFR k) ^ m * Complex.Gamma (1 - chiFR k))
        (C := ‖(Q_b b).coeff m‖ * L ^ m * (4 * Real.pi ^ 2 / Real.log 2 + 1)) (d := m + 1)
        (fun k => by
          rw [norm_mul, norm_mul, norm_pow]
          have h1 : ‖chiFR k‖ ^ m ≤ L ^ m * (1 + |(k : ℝ)|) ^ m := by
            rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hchi_le k) m
          have hG := norm_Gamma_one_sub_chiFR_le k
          calc ‖(Q_b b).coeff m‖ * ‖chiFR k‖ ^ m * ‖Complex.Gamma (1 - chiFR k)‖
              ≤ ‖(Q_b b).coeff m‖ * (L ^ m * (1 + |(k : ℝ)|) ^ m) *
                  ((4 * Real.pi ^ 2 / Real.log 2 + 1) * (1 + |(k : ℝ)|) *
                    Real.exp (-Real.pi ^ 2 * |(k : ℝ)| / Real.log 2)) := by
                gcongr
            _ = ‖(Q_b b).coeff m‖ * L ^ m * (4 * Real.pi ^ 2 / Real.log 2 + 1) *
                  (1 + |(k : ℝ)|) ^ (m + 1) * Real.exp (-Real.pi ^ 2 * |(k : ℝ)| / Real.log 2) := by
                rw [pow_succ]; ring) hz).1
      exact hraw
    rw [← Summable.tsum_finsetSum hsum_each]
    refine tsum_congr fun k => ?_
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul, Finset.sum_mul]
  rw [heul]
  -- Compare `LHS` and `RHS` term-by-term: identical at every `k ≠ 0`, differing by `C_b b` at `k = 0`!
  obtain ⟨C, _, hPhi⟩ := norm_Phi_hat_le hb
  obtain ⟨hs0, hs1, _⟩ := hasDerivAt_tsum_chiFR hPhi hz
  have hsum_L : Summable (fun k : ℤ => (1 + chiFR k) * Phi_hat b k * Complex.exp (chiFR k * Complex.log z)) :=
    (hs0.add hs1).congr fun k => by ring
  obtain ⟨C_Q, _, hQ⟩ := norm_Q_b_eval_chiFR_le b
  have hsum_R : Summable (fun k : ℤ => (Q_b b).eval (chiFR k) * Complex.Gamma (1 - chiFR k) *
      Complex.exp (chiFR k * Complex.log z)) :=
    (hasDerivAt_tsum_chiFR
      (a := fun k => (Q_b b).eval (chiFR k) * Complex.Gamma (1 - chiFR k))
      (C := C_Q * (4 * Real.pi ^ 2 / Real.log 2 + 1)) (d := (Q_b b).natDegree + 1)
      (fun k => by
        rw [norm_mul]
        calc ‖(Q_b b).eval (chiFR k)‖ * ‖Complex.Gamma (1 - chiFR k)‖
            ≤ (C_Q * (1 + |(k : ℝ)|) ^ (Q_b b).natDegree) *
                ((4 * Real.pi ^ 2 / Real.log 2 + 1) * (1 + |(k : ℝ)|) *
                  Real.exp (-Real.pi ^ 2 * |(k : ℝ)| / Real.log 2)) :=
              mul_le_mul (hQ k) (norm_Gamma_one_sub_chiFR_le k) (norm_nonneg _) (by positivity)
          _ = C_Q * (4 * Real.pi ^ 2 / Real.log 2 + 1) * (1 + |(k : ℝ)|) ^ ((Q_b b).natDegree + 1) *
                Real.exp (-Real.pi ^ 2 * |(k : ℝ)| / Real.log 2) := by
              rw [pow_succ]; ring) hz).1
  have hdiff : (∑' k : ℤ, (1 + chiFR k) * Phi_hat b k * Complex.exp (chiFR k * Complex.log z)) -
      (∑' k : ℤ, (Q_b b).eval (chiFR k) * Complex.Gamma (1 - chiFR k) *
        Complex.exp (chiFR k * Complex.log z)) = C_b b := by
    rw [← hsum_L.tsum_sub hsum_R, tsum_eq_single (0 : ℤ)]
    · unfold C_b chiFR
      simp [Complex.Gamma_one]
    · intro k hk
      rw [Phi_hat_eq_Q_b_mul_Gamma hb hk]
      have h1chi_ne : 1 + chiFR k ≠ 0 := fun h0 => by
        have hre := congrArg Complex.re h0
        rw [Complex.add_re, Complex.one_re, chiFR_re, add_zero, Complex.zero_re] at hre
        norm_num at hre
      field_simp [h1chi_ne]
      ring
  linear_combination hdiff

/-- Higher-order Fourier coefficients `vCoeff b j k = Ψ̂_b(k) / Γ(2 - j + χ_k)` for all derivatives
of `v_b b` on `{0 < z.re}` (used directly by Hankel scaling in Section 4). -/
@[expose] def vCoeff (b : ℕ) : ℕ → ℤ → ℂ
  | 0, k => Phi_hat b k
  | j + 1, k => ((1 - (j : ℂ)) + chiFR k) * vCoeff b j k

lemma vCoeff_eq_Psi_hat_div_Gamma (b j : ℕ) (k : ℤ) :
    vCoeff b j k = Psi_hat b k / Complex.Gamma (2 - (j : ℂ) + chiFR k) := by
  induction j with
  | zero => simp [vCoeff, Phi_hat]
  | succ j ih =>
    simp only [vCoeff, ih]
    by_cases hk : k = 0
    · subst hk
      simp only [chiFR, Int.cast_zero, mul_zero, zero_div, Complex.ofReal_zero, zero_mul, add_zero]
      cases j with
      | zero =>
        simp only [Nat.cast_zero, sub_zero, one_mul, zero_add, Nat.cast_one]
        rw [show (2 : ℂ) - 1 = 1 by ring, show (2 : ℂ) = 1 + 1 by ring,
          Complex.Gamma_add_one 1 one_ne_zero, one_mul]
      | succ m =>
        cases m with
        | zero =>
          simp [Complex.Gamma_zero]
        | succ r =>
          have h1 : (2 : ℂ) - ((r + 1 + 1 : ℕ) : ℂ) = -((r : ℕ) : ℂ) := by push_cast; ring
          have h2 : (2 : ℂ) - ((r + 1 + 1 + 1 : ℕ) : ℂ) = -((r + 1 : ℕ) : ℂ) := by push_cast; ring
          simp only [h1, h2, Complex.Gamma_neg_nat_eq_zero, div_zero, mul_zero]
    · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hs_ne : 2 - ((j + 1 : ℕ) : ℂ) + chiFR k ≠ 0 := fun h0 => by
        have him := congrArg Complex.im h0
        rw [Complex.add_im, Complex.sub_im, Complex.im_ofNat, Complex.natCast_im, sub_zero,
          zero_add, chiFR_im, Complex.zero_im] at him
        have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
        have hnum : 2 * Real.pi * (k : ℝ) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_pos.ne') hk'
        exact div_ne_zero hnum hlog2.ne' him
      have hshift : 2 - (j : ℂ) + chiFR k = (2 - ((j + 1 : ℕ) : ℂ) + chiFR k) + 1 := by push_cast; ring
      rw [hshift, Complex.Gamma_add_one (2 - ((j + 1 : ℕ) : ℂ) + chiFR k) hs_ne]
      have hfac : (1 - (j : ℂ)) + chiFR k = 2 - ((j + 1 : ℕ) : ℂ) + chiFR k := by push_cast; ring
      rw [hfac]
      by_cases hG : Complex.Gamma (2 - ((j + 1 : ℕ) : ℂ) + chiFR k) = 0
      · rw [hG]; simp
      · field_simp [hs_ne, hG]

private lemma norm_vCoeff_le {b : ℕ} (hb : 2 ≤ b) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℤ,
      ‖vCoeff b j k‖ ≤ C * (1 + |(k : ℝ)|) ^ (b - 1 + j) * Real.exp (-Real.pi ^ 2 * |(k : ℝ)| / Real.log 2) := by
  induction j with
  | zero => simpa [vCoeff] using norm_Phi_hat_le hb
  | succ j ih =>
    obtain ⟨C, hC, hbd⟩ := ih
    let L : ℝ := 2 * Real.pi / Real.log 2
    have hL : 0 < L := by positivity
    let M : ℝ := (1 + (j : ℝ)) + L
    have hM : 0 < M := by dsimp only [M]; positivity
    refine ⟨M * C, by positivity, fun k => ?_⟩
    simp only [vCoeff, norm_mul]
    have hfac : ‖(1 - (j : ℂ)) + chiFR k‖ ≤ M * (1 + |(k : ℝ)|) := by
      have h1 : ‖(1 : ℂ) - (j : ℂ)‖ ≤ 1 + (j : ℝ) := by
        calc ‖(1 : ℂ) - (j : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖(j : ℂ)‖ := norm_sub_le _ _
          _ = 1 + (j : ℝ) := by simp
      have h2 : ‖chiFR k‖ ≤ L * (1 + |(k : ℝ)|) := by
        unfold chiFR
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          show 2 * Real.pi * (k : ℝ) / Real.log 2 = L * (k : ℝ) by dsimp only [L]; ring,
          abs_mul, abs_of_pos hL]
        nlinarith [abs_nonneg (k : ℝ)]
      calc ‖(1 - (j : ℂ)) + chiFR k‖ ≤ ‖(1 : ℂ) - (j : ℂ)‖ + ‖chiFR k‖ := norm_add_le _ _
        _ ≤ (1 + (j : ℝ)) + L * (1 + |(k : ℝ)|) := add_le_add h1 h2
        _ ≤ ((1 + (j : ℝ)) + L) * (1 + |(k : ℝ)|) := by nlinarith [abs_nonneg (k : ℝ)]
    calc ‖(1 - (j : ℂ)) + chiFR k‖ * ‖vCoeff b j k‖
        ≤ (M * (1 + |(k : ℝ)|)) *
            (C * (1 + |(k : ℝ)|) ^ (b - 1 + j) * Real.exp (-Real.pi ^ 2 * |(k : ℝ)| / Real.log 2)) :=
          mul_le_mul hfac (hbd k) (norm_nonneg _) (by positivity)
      _ = (M * C) * (1 + |(k : ℝ)|) ^ (b - 1 + (j + 1)) * Real.exp (-Real.pi ^ 2 * |(k : ℝ)| / Real.log 2) := by
          rw [show b - 1 + (j + 1) = (b - 1 + j) + 1 by omega, pow_succ]; ring

/-- Closed-form Fourier expansion of ALL derivatives `iteratedDeriv j (v_b b) z` on `{0 < z.re}`:
`z^(j - 1) * v_b^{(j)}(z) = ∑_{k ∈ ℤ} (Ψ̂_b(k) / Γ(2 - j + χ_k)) · exp(χ_k log z)`. -/
theorem iteratedDeriv_v_b {b : ℕ} (hb : 2 ≤ b) (j : ℕ) {z : ℂ} (hz : 0 < z.re) :
    iteratedDeriv j (v_b b) z =
      z ^ (1 - (j : ℤ)) * ∑' k : ℤ, vCoeff b j k * Complex.exp (chiFR k * Complex.log z) := by
  induction j generalizing z with
  | zero =>
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero, zpow_one, vCoeff]
    exact v_b_eq_tsum b z
  | succ j ih =>
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have heq_nhds : iteratedDeriv j (v_b b) =ᶠ[𝓝 z]
        fun w : ℂ => w ^ (1 - (j : ℤ)) * ∑' k : ℤ, vCoeff b j k * Complex.exp (chiFR k * Complex.log w) := by
      filter_upwards [hopen.mem_nhds hz] with w hw
      exact ih hw
    obtain ⟨C, _, hbd⟩ := norm_vCoeff_le hb j
    obtain ⟨hs0, hs1, hd_sum⟩ := hasDerivAt_tsum_chiFR hbd hz
    have hz_ne : z ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hz; linarith
    have hd_pow : HasDerivAt (fun w : ℂ => w ^ (1 - (j : ℤ)))
        (((1 - (j : ℤ) : ℤ) : ℂ) * z ^ ((1 - (j : ℤ)) - 1)) z :=
      hasDerivAt_zpow (1 - (j : ℤ)) z (Or.inl hz_ne)
    have hd_prod := (hd_pow.mul hd_sum).congr_of_eventuallyEq heq_nhds
    rw [iteratedDeriv_succ, hd_prod.deriv]
    have hpow_eq : (1 - (j : ℤ)) - 1 = 1 - ((j + 1 : ℕ) : ℤ) := by push_cast; ring
    have hpow_inv : z ^ (1 - (j : ℤ)) * z⁻¹ = z ^ (1 - ((j + 1 : ℕ) : ℤ)) := by
      rw [← zpow_sub_one₀ hz_ne, hpow_eq]
    rw [hpow_eq, ← mul_assoc (z ^ (1 - (j : ℤ))) z⁻¹, hpow_inv]
    have hpull : (((1 - (j : ℤ) : ℤ) : ℂ) * z ^ (1 - ((j + 1 : ℕ) : ℤ))) *
          (∑' k : ℤ, vCoeff b j k * Complex.exp (chiFR k * Complex.log z)) +
        z ^ (1 - ((j + 1 : ℕ) : ℤ)) *
          (∑' k : ℤ, vCoeff b j k * chiFR k * Complex.exp (chiFR k * Complex.log z)) =
        z ^ (1 - ((j + 1 : ℕ) : ℤ)) *
          ((∑' k : ℤ, (1 - (j : ℂ)) * (vCoeff b j k * Complex.exp (chiFR k * Complex.log z))) +
           (∑' k : ℤ, vCoeff b j k * chiFR k * Complex.exp (chiFR k * Complex.log z))) := by
      rw [tsum_mul_left]; push_cast; ring
    rw [hpull, ← (hs0.mul_left (1 - (j : ℂ))).tsum_add hs1]
    congr 1
    refine tsum_congr fun k => ?_
    simp only [vCoeff]; ring

end Section3

/-! ## Section 4: Finite Trapezoid Contour Deformation, Hankel's Formula, All-Derivatives Asymptotics & `2^N`-Scaling Reduction -/

section Section4

open PakPrimes.BorelStokesVandermonde (rectIntegral rectIntegral_eq_zero_of_differentiableOn
  rectIntegral_sub_rectIntegral rectIntegral_const_mul rectIntegral_hsplit rectIntegral_inv_sub)

/-! ### Real-Axis vs. Complex Derivatives & Square Cauchy Integral for `frPoisson^{(j)}` -/

/-- For any entire function `f : ℂ → ℂ`, real-axis `iteratedDeriv` coincides with complex `iteratedDeriv`. -/
lemma iteratedDeriv_comp_ofReal_eq_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun t : ℝ => f (t : ℂ)) x = iteratedDeriv j f (x : ℂ) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hfun : iteratedDeriv j (fun t : ℝ => f (t : ℂ)) = fun t : ℝ => iteratedDeriv j f (t : ℂ) := by
      funext t; exact ih t
    rw [hfun]
    have hdiff_j : Differentiable ℂ (iteratedDeriv j f) :=
      (hf.contDiff (n := (⊤ : ℕ∞))).differentiable_iteratedDeriv j (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top j))
    have hd : HasDerivAt (iteratedDeriv j f) (deriv (iteratedDeriv j f) (x : ℂ)) (x : ℂ) :=
      (hdiff_j (x : ℂ)).hasDerivAt
    exact (hd.comp_ofReal).deriv

/-- Uniform convergence of `rectIntegral` for a uniformly convergent `ℕ`-indexed series on the boundary. -/
private lemma rectIntegral_tsum_of_uniform {f : ℕ → ℂ → ℂ} {z w : ℂ} {u : ℕ → ℝ}
    (hu : Summable u)
    (hcont : ∀ n : ℕ, ContinuousOn (f n) (Set.uIcc z.re w.re ×ℂ {z.im} ∪
      Set.uIcc z.re w.re ×ℂ {w.im} ∪ {w.re} ×ℂ Set.uIcc z.im w.im ∪ {z.re} ×ℂ Set.uIcc z.im w.im))
    (hb : ∀ n : ℕ, ∀ x ∈ Set.uIcc z.re w.re, ‖f n ((x : ℂ) + (z.im : ℂ) * I)‖ ≤ u n)
    (ht : ∀ n : ℕ, ∀ x ∈ Set.uIcc z.re w.re, ‖f n ((x : ℂ) + (w.im : ℂ) * I)‖ ≤ u n)
    (hr : ∀ n : ℕ, ∀ y ∈ Set.uIcc z.im w.im, ‖f n ((w.re : ℂ) + (y : ℂ) * I)‖ ≤ u n)
    (hl : ∀ n : ℕ, ∀ y ∈ Set.uIcc z.im w.im, ‖f n ((z.re : ℂ) + (y : ℂ) * I)‖ ≤ u n) :
    rectIntegral (fun ζ => ∑' n : ℕ, f n ζ) z w = ∑' n : ℕ, rectIntegral (f n) z w := by
  -- Prove edge-by-edge via `intervalIntegral.integral_tsum` (using `MeasureTheory.integral_tsum`).
  have hedge : ∀ (a b : ℝ) (γ : ℝ → ℂ), Continuous γ →
      (∀ n : ℕ, ContinuousOn (fun t => f n (γ t)) (Set.uIcc a b)) →
      (∀ n : ℕ, ∀ t ∈ Set.uIcc a b, ‖f n (γ t)‖ ≤ u n) →
      (∫ t : ℝ in a..b, ∑' n : ℕ, f n (γ t)) = ∑' n : ℕ, ∫ t : ℝ in a..b, f n (γ t) := by
    intro a b γ hγ hcf hbd
    have hdir : ∀ c d : ℝ, c ≤ d →
        (∀ n : ℕ, ContinuousOn (fun t => f n (γ t)) (Set.uIcc c d)) →
        (∀ n : ℕ, ∀ t ∈ Set.uIcc c d, ‖f n (γ t)‖ ≤ u n) →
        (∫ t : ℝ in c..d, ∑' n : ℕ, f n (γ t)) = ∑' n : ℕ, ∫ t : ℝ in c..d, f n (γ t) := by
      intro c d hcd hcf' hbd'
      rw [intervalIntegral.integral_of_le hcd]
      have hne_top : ∑' n : ℕ, ∫⁻ t in Set.Ioc c d, ‖f n (γ t)‖ₑ ≠ ⊤ := by
        have hle : ∀ n : ℕ, ∫⁻ t in Set.Ioc c d, ‖f n (γ t)‖ₑ ≤ ENNReal.ofReal ((d - c) * u n) := fun n => by
          calc ∫⁻ t in Set.Ioc c d, ‖f n (γ t)‖ₑ
              ≤ ∫⁻ _t in Set.Ioc c d, ENNReal.ofReal (u n) := by
                refine MeasureTheory.setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
                rw [← ofReal_norm]
                exact ENNReal.ofReal_le_ofReal (hbd' n t (by rw [Set.uIcc_of_le hcd]; exact ⟨ht.1.le, ht.2⟩))
            _ = ENNReal.ofReal (u n) * ENNReal.ofReal (d - c) := by
                rw [MeasureTheory.setLIntegral_const, Real.volume_Ioc]
            _ = ENNReal.ofReal ((d - c) * u n) := by
                rw [← ENNReal.ofReal_mul (le_trans (norm_nonneg (f n (γ c)))
                  (hbd' n c (by rw [Set.uIcc_of_le hcd]; exact ⟨le_rfl, hcd⟩))), mul_comm]
        have hu_nn : ∀ n : ℕ, 0 ≤ u n := fun n =>
          le_trans (norm_nonneg (f n (γ c))) (hbd' n c (by rw [Set.uIcc_of_le hcd]; exact ⟨le_rfl, hcd⟩))
        refine ne_of_lt (lt_of_le_of_lt (tsum_le_tsum hle) ?_)
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (sub_nonneg.mpr hcd) (hu_nn n))
          (hu.mul_left (d - c))]
        exact ENNReal.ofReal_lt_top
      have hmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (fun t => f n (γ t)) (volume.restrict (Set.Ioc c d)) :=
        fun n => ((hcf' n).mono (by rw [Set.uIcc_of_le hcd]; exact Set.Ioc_subset_Icc_self)).aestronglyMeasurable
          measurableSet_Ioc
      rw [MeasureTheory.integral_tsum (f := fun n t => f n (γ t)) hmeas hne_top]
      refine tsum_congr fun n => (intervalIntegral.integral_of_le hcd).symm
    rcases le_total a b with hab | hba
    · exact hdir a b hab hcf hbd
    · rw [intervalIntegral.integral_symm, hdir b a hba (fun n => by rw [Set.uIcc_comm]; exact hcf n)
        (fun n t ht => hbd n t (by rw [Set.uIcc_comm] at ht; exact ht)), ← tsum_neg]
      refine tsum_congr fun n => (intervalIntegral.integral_symm b a).symm
  have hcb : ∀ n : ℕ, ContinuousOn (fun x : ℝ => f n ((x : ℂ) + (z.im : ℂ) * I)) (Set.uIcc z.re w.re) :=
    fun n => (hcont n).comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + (z.im : ℂ) * I).continuousOn
      fun x hx => Or.inl (Or.inl (Or.inl ⟨by simpa using hx, by simp⟩))
  have hct : ∀ n : ℕ, ContinuousOn (fun x : ℝ => f n ((x : ℂ) + (w.im : ℂ) * I)) (Set.uIcc z.re w.re) :=
    fun n => (hcont n).comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + (w.im : ℂ) * I).continuousOn
      fun x hx => Or.inl (Or.inl (Or.inr ⟨by simpa using hx, by simp⟩))
  have hcr : ∀ n : ℕ, ContinuousOn (fun y : ℝ => f n ((w.re : ℂ) + (y : ℂ) * I)) (Set.uIcc z.im w.im) :=
    fun n => (hcont n).comp (by fun_prop : Continuous fun y : ℝ => (w.re : ℂ) + (y : ℂ) * I).continuousOn
      fun y hy => Or.inl (Or.inr ⟨by simp, by simpa using hy⟩)
  have hcl : ∀ n : ℕ, ContinuousOn (fun y : ℝ => f n ((z.re : ℂ) + (y : ℂ) * I)) (Set.uIcc z.im w.im) :=
    fun n => (hcont n).comp (by fun_prop : Continuous fun y : ℝ => (z.re : ℂ) + (y : ℂ) * I).continuousOn
      fun y hy => Or.inr ⟨by simp, by simpa using hy⟩
  have hs_b : Summable (fun n : ℕ => ∫ x : ℝ in z.re..w.re, f n ((x : ℂ) + (z.im : ℂ) * I)) :=
    Summable.of_norm_bounded (hu.mul_left |w.re - z.re|) fun n => by
      simpa [mul_comm] using intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => hb n x (Set.uIoc_subset_uIcc hx)
  have hs_t : Summable (fun n : ℕ => ∫ x : ℝ in z.re..w.re, f n ((x : ℂ) + (w.im : ℂ) * I)) :=
    Summable.of_norm_bounded (hu.mul_left |w.re - z.re|) fun n => by
      simpa [mul_comm] using intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ht n x (Set.uIoc_subset_uIcc hx)
  have hs_r : Summable (fun n : ℕ => ∫ y : ℝ in z.im..w.im, f n ((w.re : ℂ) + (y : ℂ) * I)) :=
    Summable.of_norm_bounded (hu.mul_left |w.im - z.im|) fun n => by
      simpa [mul_comm] using intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => hr n y (Set.uIoc_subset_uIcc hy)
  have hs_l : Summable (fun n : ℕ => ∫ y : ℝ in z.im..w.im, f n ((z.re : ℂ) + (y : ℂ) * I)) :=
    Summable.of_norm_bounded (hu.mul_left |w.im - z.im|) fun n => by
      simpa [mul_comm] using intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => hl n y (Set.uIoc_subset_uIcc hy)
  unfold rectIntegral
  rw [hedge z.re w.re _ (by fun_prop) hcb hb,
    hedge z.re w.re _ (by fun_prop) hct ht,
    hedge z.im w.im _ (by fun_prop) hcr hr,
    hedge z.im w.im _ (by fun_prop) hcl hl,
    ← tsum_mul_left, ← tsum_mul_left,
    ← hs_b.tsum_sub hs_t, ← (hs_b.sub hs_t).tsum_add (hs_r.mul_left I),
    ← ((hs_b.sub hs_t).add (hs_r.mul_left I)).tsum_sub (hs_l.mul_left I)]

/-- Large square radius `R₀(b) = 2 * (2^b + 3) + 2` outside all poles of `L_b b` and inside its Laurent series domain. -/
@[expose] def squareRadius (b : ℕ) : ℝ := 2 * ((2 ^ b + 3 : ℕ) : ℝ) + 2

lemma squareRadius_gt (b : ℕ) : 2 * ((2 ^ b + 3 : ℕ) : ℝ) < squareRadius b := by
  unfold squareRadius; linarith

lemma squareRadius_ge_ten (b : ℕ) : (10 : ℝ) ≤ squareRadius b := by
  unfold squareRadius
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ b := by exact_mod_cast Nat.one_le_pow b 2 (by norm_num)
  push_cast; linarith

/-- Exact square Cauchy integral representation for every derivative `iteratedDeriv j (frPoisson b) x`. -/
theorem iteratedDeriv_frPoisson_eq_rectIntegral {b : ℕ} (hb : 1 ≤ b) (j : ℕ) (x : ℂ) :
    iteratedDeriv j (frPoisson b) x =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        rectIntegral (fun ξ => ξ ^ j * Complex.exp (x * ξ) * L_b b ξ)
          ((-(squareRadius b) : ℂ) - (squareRadius b : ℂ) * I)
          ((squareRadius b : ℂ) + (squareRadius b : ℂ) * I) := by
  let R : ℝ := squareRadius b
  have hR_gt : 2 * ((2 ^ b + 3 : ℕ) : ℝ) < R := squareRadius_gt b
  have hR_pos : 0 < R := lt_of_lt_of_le (by norm_num) (squareRadius_ge_ten b)
  let z : ℂ := (-R : ℂ) - (R : ℂ) * I
  let w : ℂ := (R : ℂ) + (R : ℂ) * I
  have hz_re : z.re = -R := by dsimp only [z]; simp
  have hz_im : z.im = -R := by dsimp only [z]; simp
  have hw_re : w.re = R := by dsimp only [w]; simp
  have hw_im : w.im = R := by dsimp only [w]; simp
  -- Every point `ξ` on the boundary of `[-R, R]²` satisfies `R ≤ ‖ξ‖ ≤ 2 * R`.
  have hbd_norm : ∀ ξ : ℂ, (ξ ∈ Set.uIcc z.re w.re ×ℂ {z.im} ∪ Set.uIcc z.re w.re ×ℂ {w.im} ∪
      {w.re} ×ℂ Set.uIcc z.im w.im ∪ {z.re} ×ℂ Set.uIcc z.im w.im) → R ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 * R := by
    intro ξ hξ
    rw [hz_re, hz_im, hw_re, hw_im, Set.uIcc_of_le (by linarith : -R ≤ R)] at hξ
    rcases hξ with ((⟨hre, him⟩ | ⟨hre, him⟩) | ⟨hre, him⟩) | ⟨hre, him⟩
    · change ξ.im = -R at him
      have h1 : R ≤ ‖ξ‖ := by
        calc R = |ξ.im| := by rw [him, abs_neg, abs_of_pos hR_pos]
          _ ≤ ‖ξ‖ := Complex.abs_im_le_norm ξ
      have h2 : ‖ξ‖ ≤ 2 * R := (Complex.norm_le_abs_re_add_abs_im ξ).trans (by
        have : |ξ.re| ≤ R := abs_le.mpr hre
        rw [him, abs_neg, abs_of_pos hR_pos]; linarith)
      exact ⟨h1, h2⟩
    · change ξ.im = R at him
      have h1 : R ≤ ‖ξ‖ := by
        calc R = |ξ.im| := by rw [him, abs_of_pos hR_pos]
          _ ≤ ‖ξ‖ := Complex.abs_im_le_norm ξ
      have h2 : ‖ξ‖ ≤ 2 * R := (Complex.norm_le_abs_re_add_abs_im ξ).trans (by
        have : |ξ.re| ≤ R := abs_le.mpr hre
        rw [him, abs_of_pos hR_pos]; linarith)
      exact ⟨h1, h2⟩
    · change ξ.re = R at hre
      have h1 : R ≤ ‖ξ‖ := by
        calc R = |ξ.re| := by rw [hre, abs_of_pos hR_pos]
          _ ≤ ‖ξ‖ := Complex.abs_re_le_norm ξ
      have h2 : ‖ξ‖ ≤ 2 * R := (Complex.norm_le_abs_re_add_abs_im ξ).trans (by
        have : |ξ.im| ≤ R := abs_le.mpr him
        rw [hre, abs_of_pos hR_pos]; linarith)
      exact ⟨h1, h2⟩
    · change ξ.re = -R at hre
      have h1 : R ≤ ‖ξ‖ := by
        calc R = |ξ.re| := by rw [hre, abs_neg, abs_of_pos hR_pos]
          _ ≤ ‖ξ‖ := Complex.abs_re_le_norm ξ
      have h2 : ‖ξ‖ ≤ 2 * R := (Complex.norm_le_abs_re_add_abs_im ξ).trans (by
        have : |ξ.im| ≤ R := abs_le.mpr him
        rw [hre, abs_neg, abs_of_pos hR_pos]; linarith)
      exact ⟨h1, h2⟩
  -- Replace `L_b b ξ` on the boundary by its Laurent series `∑' n, frPoissonCoeff b n * ξ^{-(n+1)}`.
  have hcongr : rectIntegral (fun ξ => ξ ^ j * Complex.exp (x * ξ) * L_b b ξ) z w =
      rectIntegral (fun ξ => ∑' n : ℕ, frPoissonCoeff b n * (ξ ^ j * Complex.exp (x * ξ) / ξ ^ (n + 1))) z w := by
    have hpt : ∀ ξ : ℂ, 2 * ((2 ^ b + 3 : ℕ) : ℝ) < ‖ξ‖ →
        ξ ^ j * Complex.exp (x * ξ) * L_b b ξ =
          ∑' n : ℕ, frPoissonCoeff b n * (ξ ^ j * Complex.exp (x * ξ) / ξ ^ (n + 1)) := fun ξ hξ => by
      rw [L_b_eq_tsum hb hξ, ← tsum_mul_left]
      refine tsum_congr fun n => ?_
      rw [inv_pow, div_eq_mul_inv]; ring
    refine rectIntegral_congr_boundary
      (fun t ht => hpt _ (lt_of_lt_of_le hR_gt (hbd_norm _ (Or.inl (Or.inl (Or.inl ⟨by simpa using ht, by simp⟩)))).1))
      (fun t ht => hpt _ (lt_of_lt_of_le hR_gt (hbd_norm _ (Or.inl (Or.inl (Or.inr ⟨by simpa using ht, by simp⟩)))).1))
      (fun t ht => hpt _ (lt_of_lt_of_le hR_gt (hbd_norm _ (Or.inl (Or.inr ⟨by simp, by simpa using ht⟩))).1))
      (fun t ht => hpt _ (lt_of_lt_of_le hR_gt (hbd_norm _ (Or.inr ⟨by simp, by simpa using ht⟩)).1))
  -- Apply `rectIntegral_tsum_of_uniform` with geometric majorant!
  let M : ℝ := (2 * R) ^ j * Real.exp (‖x‖ * (2 * R)) / R
  have hM_nn : 0 ≤ M := by positivity
  have hterm_bd : ∀ (n : ℕ) (ξ : ℂ), R ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 * R →
      ‖frPoissonCoeff b n * (ξ ^ j * Complex.exp (x * ξ) / ξ ^ (n + 1))‖ ≤ M * (1 / 2 : ℝ) ^ n := by
    intro n ξ h1 h2
    have hcoeff := norm_frPoissonCoeff_le hb n
    have hexp_le : ‖Complex.exp (x * ξ)‖ ≤ Real.exp (‖x‖ * (2 * R)) := by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.mpr ?_
      calc (x * ξ).re ≤ ‖x * ξ‖ := Complex.re_le_norm _
        _ = ‖x‖ * ‖ξ‖ := norm_mul _ _
        _ ≤ ‖x‖ * (2 * R) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    have hpow_j : ‖ξ ^ j‖ ≤ (2 * R) ^ j := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h2 j
    have hpow_n : R ^ (n + 1) ≤ ‖ξ ^ (n + 1)‖ := by rw [norm_pow]; exact pow_le_pow_left₀ hR_pos.le h1 (n + 1)
    have hratio : ((2 ^ b + 3 : ℕ) : ℝ) / R ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hR_pos (by norm_num)]; linarith
    rw [norm_mul, norm_div, norm_mul]
    calc ‖frPoissonCoeff b n‖ * (‖ξ ^ j‖ * ‖Complex.exp (x * ξ)‖ / ‖ξ ^ (n + 1)‖)
        ≤ ((2 ^ b + 3 : ℕ) : ℝ) ^ n * ((2 * R) ^ j * Real.exp (‖x‖ * (2 * R)) / R ^ (n + 1)) := by
          refine mul_le_mul hcoeff ?_ (by positivity) (by positivity)
          exact div_le_div₀ (by positivity) (mul_le_mul hpow_j hexp_le (norm_nonneg _) (by positivity))
            (by positivity) hpow_n
      _ = M * (((2 ^ b + 3 : ℕ) : ℝ) / R) ^ n := by
          dsimp only [M]; rw [div_pow, pow_succ]; ring
      _ ≤ M * (1 / 2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio n) hM_nn
  have htsum_rect := rectIntegral_tsum_of_uniform
    (f := fun n ξ => frPoissonCoeff b n * (ξ ^ j * Complex.exp (x * ξ) / ξ ^ (n + 1)))
    (z := z) (w := w) (u := fun n => M * (1 / 2 : ℝ) ^ n)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left M)
    (fun n => by
      refine continuousOn_const.mul (ContinuousOn.div (by fun_prop) (by fun_prop) fun ξ hξ => ?_)
      have hne : ξ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR_pos (hbd_norm ξ hξ).1)
      exact pow_ne_zero (n + 1) hne)
    (fun n t ht => hterm_bd n _ (hbd_norm _ (Or.inl (Or.inl (Or.inl ⟨by simpa using ht, by simp⟩)))).1
      (hbd_norm _ (Or.inl (Or.inl (Or.inl ⟨by simpa using ht, by simp⟩)))).2)
    (fun n t ht => hterm_bd n _ (hbd_norm _ (Or.inl (Or.inl (Or.inr ⟨by simpa using ht, by simp⟩)))).1
      (hbd_norm _ (Or.inl (Or.inl (Or.inr ⟨by simpa using ht, by simp⟩)))).2)
    (fun n t ht => hterm_bd n _ (hbd_norm _ (Or.inl (Or.inr ⟨by simp, by simpa using ht⟩))).1
      (hbd_norm _ (Or.inl (Or.inr ⟨by simp, by simpa using ht⟩))).2)
    (fun n t ht => hterm_bd n _ (hbd_norm _ (Or.inr ⟨by simp, by simpa using ht⟩)).1
      (hbd_norm _ (Or.inr ⟨by simp, by simpa using ht⟩)).2)
  -- Evaluate each `n`-th rectangle integral!
  have heval_n : ∀ n : ℕ,
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        rectIntegral (fun ξ => frPoissonCoeff b n * (ξ ^ j * Complex.exp (x * ξ) / ξ ^ (n + 1))) z w =
      if j ≤ n then frPoissonCoeff b n * x ^ (n - j) / ((n - j).factorial : ℂ) else 0 := by
    intro n
    rw [rectIntegral_const_mul]
    by_cases hjn : j ≤ n
    · simp only [hjn, ↓reduceIte]
      have hpt : ∀ ξ : ℂ, ξ ≠ 0 → ξ ^ j * Complex.exp (x * ξ) / ξ ^ (n + 1) =
          Complex.exp (x * ξ) / (ξ - 0) ^ (n - j + 1) := fun ξ hne => by
        rw [sub_zero]
        have hpow : ξ ^ (n + 1) = ξ ^ j * ξ ^ (n - j + 1) := by rw [← pow_add]; congr 1; omega
        rw [hpow]
        have h1 : ξ ^ j ≠ 0 := pow_ne_zero j hne
        have h2 : ξ ^ (n - j + 1) ≠ 0 := pow_ne_zero _ hne
        field_simp [h1, h2]
      have hceq : rectIntegral (fun ξ => ξ ^ j * Complex.exp (x * ξ) / ξ ^ (n + 1)) z w =
          rectIntegral (fun ξ => Complex.exp (x * ξ) / (ξ - 0) ^ (n - j + 1)) z w :=
        rectIntegral_congr_boundary
          (fun t ht => hpt _ (norm_pos_iff.mp (lt_of_lt_of_le hR_pos
            (hbd_norm _ (Or.inl (Or.inl (Or.inl ⟨by simpa using ht, by simp⟩)))).1)))
          (fun t ht => hpt _ (norm_pos_iff.mp (lt_of_lt_of_le hR_pos
            (hbd_norm _ (Or.inl (Or.inl (Or.inr ⟨by simpa using ht, by simp⟩)))).1)))
          (fun t ht => hpt _ (norm_pos_iff.mp (lt_of_lt_of_le hR_pos
            (hbd_norm _ (Or.inl (Or.inr ⟨by simp, by simpa using ht⟩))).1)))
          (fun t ht => hpt _ (norm_pos_iff.mp (lt_of_lt_of_le hR_pos
            (hbd_norm _ (Or.inr ⟨by simp, by simpa using ht⟩)).1)))
      have hzw : z = (0 : ℂ) - (R : ℂ) - (R : ℂ) * I ∧ w = (0 : ℂ) + (R : ℂ) + (R : ℂ) * I := by
        dsimp only [z, w]; constructor <;> ring
      rw [hceq, hzw.1, hzw.2, rectIntegral_exp_div_pow x 0 hR_pos (by omega)]
      simp only [mul_zero, Complex.exp_zero, mul_one, Nat.add_sub_cancel]
      have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) Complex.I_ne_zero
      field_simp [h2pi]
    · simp only [hjn, ↓reduceIte]
      have hpt : ∀ ξ : ℂ, ξ ≠ 0 → ξ ^ j * Complex.exp (x * ξ) / ξ ^ (n + 1) =
          ξ ^ (j - n - 1) * Complex.exp (x * ξ) := fun ξ hne => by
        have hpow : ξ ^ j = ξ ^ (n + 1) * ξ ^ (j - n - 1) := by rw [← pow_add]; congr 1; omega
        rw [hpow]
        have h1 : ξ ^ (n + 1) ≠ 0 := pow_ne_zero _ hne
        field_simp [h1]
      have hceq : rectIntegral (fun ξ => ξ ^ j * Complex.exp (x * ξ) / ξ ^ (n + 1)) z w =
          rectIntegral (fun ξ => ξ ^ (j - n - 1) * Complex.exp (x * ξ)) z w :=
        rectIntegral_congr_boundary
          (fun t ht => hpt _ (norm_pos_iff.mp (lt_of_lt_of_le hR_pos
            (hbd_norm _ (Or.inl (Or.inl (Or.inl ⟨by simpa using ht, by simp⟩)))).1)))
          (fun t ht => hpt _ (norm_pos_iff.mp (lt_of_lt_of_le hR_pos
            (hbd_norm _ (Or.inl (Or.inl (Or.inr ⟨by simpa using ht, by simp⟩)))).1)))
          (fun t ht => hpt _ (norm_pos_iff.mp (lt_of_lt_of_le hR_pos
            (hbd_norm _ (Or.inl (Or.inr ⟨by simp, by simpa using ht⟩))).1)))
          (fun t ht => hpt _ (norm_pos_iff.mp (lt_of_lt_of_le hR_pos
            (hbd_norm _ (Or.inr ⟨by simp, by simpa using ht⟩)).1)))
      rw [hceq, rectIntegral_eq_zero_of_differentiableOn (by fun_prop), mul_zero, mul_zero]
  change iteratedDeriv j (frPoisson b) x = (2 * (Real.pi : ℂ) * I)⁻¹ * rectIntegral _ z w
  rw [hcongr, htsum_rect, ← tsum_mul_left, tsum_congr heval_n]
  have hsum_ite : Summable (fun n : ℕ => if j ≤ n then frPoissonCoeff b n * x ^ (n - j) / ((n - j).factorial : ℂ) else 0) := by
    rw [← summable_nat_add_iff j]
    have hexp := (Real.summable_pow_div_factorial (((2 ^ b + 3 : ℕ) : ℝ) * ‖x‖)).mul_left (((2 ^ b + 3 : ℕ) : ℝ) ^ j)
    refine Summable.of_norm_bounded hexp fun m => ?_
    simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, norm_div, norm_mul, norm_pow, Complex.norm_natCast]
    have hcoeff := norm_frPoissonCoeff_le hb (m + j)
    rw [pow_add] at hcoeff
    calc ‖frPoissonCoeff b (m + j)‖ * ‖x‖ ^ m / (m.factorial : ℝ)
        ≤ (((2 ^ b + 3 : ℕ) : ℝ) ^ m * ((2 ^ b + 3 : ℕ) : ℝ) ^ j) * ‖x‖ ^ m / (m.factorial : ℝ) := by gcongr
      _ = ((2 ^ b + 3 : ℕ) : ℝ) ^ j * ((((2 ^ b + 3 : ℕ) : ℝ) * ‖x‖) ^ m / (m.factorial : ℝ)) := by
          rw [mul_pow]; ring
  rw [← hsum_ite.sum_add_tsum_nat_add j]
  have hzero : ∑ n ∈ Finset.range j,
      (if j ≤ n then frPoissonCoeff b n * x ^ (n - j) / ((n - j).factorial : ℂ) else 0) = 0 :=
    Finset.sum_eq_zero fun n hn => by
      rw [Finset.mem_range] at hn; simp [show ¬ (j ≤ n) by omega]
  rw [hzero, zero_add, iteratedDeriv_frPoisson hb j x]
  refine tsum_congr fun m => by simp

/-! ### Explicit Holomorphic Primitive on Open Rectangles & Finite Trapezoid Contour Deformation -/

/-- Any holomorphic function `g` on an open rectangle `(a, b) × (c, d)` admits an explicit holomorphic
primitive `F` on `(a, b) × (c, d)` (proved directly from `rectIntegral_eq_zero_of_differentiableOn`). -/
private lemma exists_primitive_on_openRect {g : ℂ → ℂ} {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hg : DifferentiableOn ℂ g (Set.Ioo a b ×ℂ Set.Ioo c d)) :
    ∃ F : ℂ → ℂ, ∀ z ∈ Set.Ioo a b ×ℂ Set.Ioo c d, HasDerivAt F (g z) z := by
  let x₀ : ℝ := (a + b) / 2
  let y₀ : ℝ := (c + d) / 2
  have hx₀ : x₀ ∈ Set.Ioo a b := ⟨by dsimp only [x₀]; linarith, by dsimp only [x₀]; linarith⟩
  have hy₀ : y₀ ∈ Set.Ioo c d := ⟨by dsimp only [y₀]; linarith, by dsimp only [y₀]; linarith⟩
  let F : ℂ → ℂ := fun z =>
    (∫ t : ℝ in x₀..z.re, g ((t : ℂ) + (y₀ : ℂ) * I)) +
    I * (∫ s : ℝ in y₀..z.im, g ((z.re : ℂ) + (s : ℂ) * I))
  have hint_h : ∀ {x₁ x₂ y : ℝ}, x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b → y ∈ Set.Ioo c d →
      IntervalIntegrable (fun t : ℝ => g ((t : ℂ) + (y : ℂ) * I)) volume x₁ x₂ := by
    intro x₁ x₂ y hx₁ hx₂ hy
    refine ContinuousOn.intervalIntegrable ?_
    refine hg.continuousOn.comp (by fun_prop : Continuous fun t : ℝ => (t : ℂ) + (y : ℂ) * I).continuousOn fun t ht => ?_
    simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, zero_add]
    exact ⟨⟨lt_of_lt_of_le (lt_min hx₁.1 hx₂.1) ht.1, lt_of_le_of_lt ht.2 (max_lt hx₁.2 hx₂.2)⟩, hy⟩
  have hint_v : ∀ {x y₁ y₂ : ℝ}, x ∈ Set.Ioo a b → y₁ ∈ Set.Ioo c d → y₂ ∈ Set.Ioo c d →
      IntervalIntegrable (fun s : ℝ => g ((x : ℂ) + (s : ℂ) * I)) volume y₁ y₂ := by
    intro x y₁ y₂ hx hy₁ hy₂
    refine ContinuousOn.intervalIntegrable ?_
    refine hg.continuousOn.comp (by fun_prop : Continuous fun s : ℝ => (x : ℂ) + (s : ℂ) * I).continuousOn fun s hs => ?_
    simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, zero_add]
    exact ⟨hx, ⟨lt_of_lt_of_le (lt_min hy₁.1 hy₂.1) hs.1, lt_of_le_of_lt hs.2 (max_lt hy₁.2 hy₂.2)⟩⟩
  refine ⟨F, fun z hz => ?_⟩
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hU_open : IsOpen (Set.Ioo a b ×ℂ Set.Ioo c d) := isOpen_Ioo.reProdIm isOpen_Ioo
  have hg_cont : ContinuousAt g z := (hg.continuousOn.continuousAt (hU_open.mem_nhds hz))
  obtain ⟨δ₁, hδ₁, hball_sub⟩ := Metric.isOpen_iff.mp hU_open z hz
  obtain ⟨δ₂, hδ₂, hcont_eps⟩ := Metric.continuousAt_iff.mp hg_cont (ε / 2) (half_pos hε)
  let δ : ℝ := min (δ₁ / 2) (δ₂ / 2)
  have hδ : 0 < δ := lt_min (half_pos hδ₁) (half_pos hδ₂)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδ] with h hh
  have hh_lt : ‖h‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hh
  have hh_lt1 : ‖h‖ < δ₁ / 2 := lt_of_lt_of_le hh_lt (min_le_left _ _)
  have hh_lt2 : ‖h‖ < δ₂ / 2 := lt_of_lt_of_le hh_lt (min_le_right _ _)
  have hzh_mem : z + h ∈ Set.Ioo a b ×ℂ Set.Ioo c d := hball_sub (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; linarith)
  have hz_re_mem : z.re ∈ Set.Ioo a b := hz.1
  have hz_im_mem : z.im ∈ Set.Ioo c d := hz.2
  have hzh_re_mem : (z + h).re ∈ Set.Ioo a b := hzh_mem.1
  have hzh_im_mem : (z + h).im ∈ Set.Ioo c d := hzh_mem.2
  -- By Cauchy on `[z.re, (z + h).re] × [y₀, z.im]`, rewrite `F(z + h) - F(z)` along the two-segment L-path from `z` to `z + h`!
  have hrect0 : rectIntegral g ((z.re : ℂ) + (y₀ : ℂ) * I) (((z + h).re : ℂ) + (z.im : ℂ) * I) = 0 := by
    refine rectIntegral_eq_zero_of_differentiableOn (hg.mono fun ζ hζ => ?_)
    simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, zero_add] at hζ
    exact ⟨⟨lt_of_lt_of_le (lt_min hz_re_mem.1 hzh_re_mem.1) hζ.1.1,
        lt_of_le_of_lt hζ.1.2 (max_lt hz_re_mem.2 hzh_re_mem.2)⟩,
      ⟨lt_of_lt_of_le (lt_min hy₀.1 hz_im_mem.1) hζ.2.1,
        lt_of_le_of_lt hζ.2.2 (max_lt hy₀.2 hz_im_mem.2)⟩⟩
  have hF_diff : F (z + h) - F z =
      (∫ t : ℝ in z.re..(z + h).re, g ((t : ℂ) + (z.im : ℂ) * I)) +
      I * (∫ s : ℝ in z.im..(z + h).im, g (((z + h).re : ℂ) + (s : ℂ) * I)) := by
    dsimp only [F]
    have hsplit_x : (∫ t : ℝ in x₀..(z + h).re, g ((t : ℂ) + (y₀ : ℂ) * I)) =
        (∫ t : ℝ in x₀..z.re, g ((t : ℂ) + (y₀ : ℂ) * I)) +
        (∫ t : ℝ in z.re..(z + h).re, g ((t : ℂ) + (y₀ : ℂ) * I)) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hint_h hx₀ hz_re_mem hy₀) (hint_h hz_re_mem hzh_re_mem hy₀)).symm
    have hsplit_y : (∫ s : ℝ in y₀..(z + h).im, g (((z + h).re : ℂ) + (s : ℂ) * I)) =
        (∫ s : ℝ in y₀..z.im, g (((z + h).re : ℂ) + (s : ℂ) * I)) +
        (∫ s : ℝ in z.im..(z + h).im, g (((z + h).re : ℂ) + (s : ℂ) * I)) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hint_v hzh_re_mem hy₀ hz_im_mem) (hint_v hzh_re_mem hz_im_mem hzh_im_mem)).symm
    unfold rectIntegral at hrect0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
      Complex.mul_im, zero_add] at hrect0
    rw [hsplit_x, hsplit_y]
    linear_combination hrect0
  -- Subtract `h * g z = ((z + h).re - z.re) * g z + I * ((z + h).im - z.im) * g z`!
  have hh_decomp : h * g z =
      (∫ _t : ℝ in z.re..(z + h).re, g z) + I * (∫ _s : ℝ in z.im..(z + h).im, g z) := by
    rw [intervalIntegral.integral_const, intervalIntegral.integral_const, Complex.real_smul, Complex.real_smul]
    have hre : ((z + h).re - z.re : ℝ) = h.re := by simp
    have him : ((z + h).im - z.im : ℝ) = h.im := by simp
    rw [hre, him]
    have hmk : (h.re : ℂ) + I * (h.im : ℂ) = h := by apply Complex.ext <;> simp
    calc h * g z = ((h.re : ℂ) + I * (h.im : ℂ)) * g z := by rw [hmk]
      _ = (h.re : ℂ) * g z + I * ((h.im : ℂ) * g z) := by ring
  have hsub_eq : F (z + h) - F z - h * g z =
      (∫ t : ℝ in z.re..(z + h).re, (g ((t : ℂ) + (z.im : ℂ) * I) - g z)) +
      I * (∫ s : ℝ in z.im..(z + h).im, (g (((z + h).re : ℂ) + (s : ℂ) * I) - g z)) := by
    rw [hF_diff, hh_decomp,
      intervalIntegral.integral_sub (hint_h hz_re_mem hzh_re_mem hz_im_mem) intervalIntegrable_const,
      intervalIntegral.integral_sub (hint_v hzh_re_mem hz_im_mem hzh_im_mem) intervalIntegrable_const]
    ring
  rw [smul_eq_mul, hsub_eq]
  have hseg1 : ‖∫ t : ℝ in z.re..(z + h).re, (g ((t : ℂ) + (z.im : ℂ) * I) - g z)‖ ≤ (ε / 2) * ‖h‖ := by
    have hpt : ∀ t ∈ Set.uIcc z.re (z + h).re, ‖g ((t : ℂ) + (z.im : ℂ) * I) - g z‖ ≤ ε / 2 := fun t ht => by
      have hd_lt : dist ((t : ℂ) + (z.im : ℂ) * I) z < δ₂ := by
        rw [dist_eq_norm]
        have hdiff : ((t : ℂ) + (z.im : ℂ) * I) - z = ((t - z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp
        rw [hdiff, Complex.norm_real, Real.norm_eq_abs]
        have htz : |t - z.re| ≤ |h.re| := by
          rcases le_total 0 h.re with hhre | hhre
          · rw [Complex.add_re, Set.uIcc_of_le (by linarith)] at ht
            rw [abs_of_nonneg (by linarith [ht.1]), abs_of_nonneg hhre]; linarith [ht.2]
          · rw [Complex.add_re, Set.uIcc_of_ge (by linarith)] at ht
            rw [abs_of_nonpos (by linarith [ht.2]), abs_of_nonpos hhre]; linarith [ht.1]
        have hre_le : |h.re| ≤ ‖h‖ := Complex.abs_re_le_norm h
        linarith
      exact (by simpa [dist_eq_norm] using hcont_eps hd_lt : ‖g ((t : ℂ) + (z.im : ℂ) * I) - g z‖ < ε / 2).le
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => hpt t (Set.uIoc_subset_uIcc ht))
    have hlen : |(z + h).re - z.re| ≤ ‖h‖ := by
      rw [Complex.add_re, add_sub_cancel_left]; exact Complex.abs_re_le_norm h
    calc ‖∫ t : ℝ in z.re..(z + h).re, (g ((t : ℂ) + (z.im : ℂ) * I) - g z)‖
        ≤ (ε / 2) * |(z + h).re - z.re| := hle
      _ ≤ (ε / 2) * ‖h‖ := mul_le_mul_of_nonneg_left hlen (by linarith)
  have hseg2 : ‖I * ∫ s : ℝ in z.im..(z + h).im, (g (((z + h).re : ℂ) + (s : ℂ) * I) - g z)‖ ≤ (ε / 2) * ‖h‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
    have hpt : ∀ s ∈ Set.uIcc z.im (z + h).im, ‖g (((z + h).re : ℂ) + (s : ℂ) * I) - g z‖ ≤ ε / 2 := fun s hs => by
      have hd_lt : dist (((z + h).re : ℂ) + (s : ℂ) * I) z < δ₂ := by
        rw [dist_eq_norm]
        have hdiff : (((z + h).re : ℂ) + (s : ℂ) * I) - z = (h.re : ℂ) + ((s - z.im : ℝ) : ℂ) * I := by
          apply Complex.ext <;> simp
        rw [hdiff]
        have h1 : ‖(h.re : ℂ) + ((s - z.im : ℝ) : ℂ) * I‖ ≤ |h.re| + |s - z.im| := by
          calc ‖(h.re : ℂ) + ((s - z.im : ℝ) : ℂ) * I‖
              ≤ ‖(h.re : ℂ)‖ + ‖((s - z.im : ℝ) : ℂ) * I‖ := norm_add_le _ _
            _ = |h.re| + |s - z.im| := by
                rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
                  Real.norm_eq_abs, Real.norm_eq_abs]
        have hsz : |s - z.im| ≤ |h.im| := by
          rcases le_total 0 h.im with hhim | hhim
          · rw [Complex.add_im, Set.uIcc_of_le (by linarith)] at hs
            rw [abs_of_nonneg (by linarith [hs.1]), abs_of_nonneg hhim]; linarith [hs.2]
          · rw [Complex.add_im, Set.uIcc_of_ge (by linarith)] at hs
            rw [abs_of_nonpos (by linarith [hs.2]), abs_of_nonpos hhim]; linarith [hs.1]
        have hre_le : |h.re| ≤ ‖h‖ := Complex.abs_re_le_norm h
        have him_le : |h.im| ≤ ‖h‖ := Complex.abs_im_le_norm h
        linarith
      exact (by simpa [dist_eq_norm] using hcont_eps hd_lt : ‖g (((z + h).re : ℂ) + (s : ℂ) * I) - g z‖ < ε / 2).le
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => hpt s (Set.uIoc_subset_uIcc hs))
    have hlen : |(z + h).im - z.im| ≤ ‖h‖ := by
      rw [Complex.add_im, add_sub_cancel_left]; exact Complex.abs_im_le_norm h
    calc ‖∫ s : ℝ in z.im..(z + h).im, (g (((z + h).re : ℂ) + (s : ℂ) * I) - g z)‖
        ≤ (ε / 2) * |(z + h).im - z.im| := hle
      _ ≤ (ε / 2) * ‖h‖ := mul_le_mul_of_nonneg_left hlen (by linarith)
  calc ‖(∫ t : ℝ in z.re..(z + h).re, (g ((t : ℂ) + (z.im : ℂ) * I) - g z)) +
          I * (∫ s : ℝ in z.im..(z + h).im, (g (((z + h).re : ℂ) + (s : ℂ) * I) - g z))‖
      ≤ ‖∫ t : ℝ in z.re..(z + h).re, (g ((t : ℂ) + (z.im : ℂ) * I) - g z)‖ +
        ‖I * ∫ s : ℝ in z.im..(z + h).im, (g (((z + h).re : ℂ) + (s : ℂ) * I) - g z)‖ := norm_add_le _ _
    _ ≤ (ε / 2) * ‖h‖ + (ε / 2) * ‖h‖ := add_le_add hseg1 hseg2
    _ = ε * ‖h‖ := by ring

/-- Counter-clockwise 4-edge finite trapezoid contour integral `T(r, A)` enclosing `[-1, 0]`
for `0 < r ≤ 1/2` and `A = 2` (vertices `r ± ir`, `(r - A) ± i(r + A)`). -/
@[expose] def trapIntegral (g : ℂ → ℂ) (r A : ℝ) : ℂ :=
  (1 + I) * (∫ s : ℝ in (0 : ℝ)..A, g (((r - s : ℝ) : ℂ) - ((r + s : ℝ) : ℂ) * I)) +
  I * (∫ y : ℝ in (-r)..r, g ((r : ℂ) + (y : ℂ) * I)) +
  (-1 + I) * (∫ s : ℝ in (0 : ℝ)..A, g (((r - s : ℝ) : ℂ) + ((r + s : ℝ) : ℂ) * I)) -
  I * (∫ y : ℝ in (-(r + A))..(r + A), g (((r - A : ℝ) : ℂ) + (y : ℂ) * I))

/-- Domain `ℂ \ [-1, 0]` on which `L_b b` is holomorphic. -/
@[expose] def SlitNegUnit : Set ℂ := {ξ : ℂ | ¬ (ξ.im = 0 ∧ -1 ≤ ξ.re ∧ ξ.re ≤ 0)}

lemma L_b_differentiableOn_slitNegUnit {b : ℕ} (hb : 1 ≤ b) :
    DifferentiableOn ℂ (L_b b) SlitNegUnit := by
  intro ξ hξ
  have hξ_ne : ξ ≠ 0 := fun h0 => hξ ⟨by rw [h0, Complex.zero_im], by rw [h0, Complex.zero_re]; norm_num,
    by rw [h0, Complex.zero_re]⟩
  have hinv_mem : ∀ j : ℕ, 1 + ξ⁻¹ / (2 : ℂ) ^ j ≠ 0 := fun j h0 => by
    have h2j : (2 : ℂ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
    have hξ_eq : ξ = ((-(((2 : ℝ) ^ j)⁻¹) : ℝ) : ℂ) := by
      have h1 : ξ⁻¹ = -((2 : ℂ) ^ j) := by
        have hm := congrArg (· * (2 : ℂ) ^ j) h0
        simp only [zero_mul, add_mul, one_mul, div_mul_cancel₀ _ h2j] at hm
        linear_combination hm
      have h2 := congrArg Inv.inv h1
      rw [inv_inv, inv_neg] at h2
      rw [h2]; push_cast; rfl
    apply hξ
    rw [hξ_eq]
    have h2j_ge : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hinv_pos : 0 < ((2 : ℝ) ^ j)⁻¹ := by positivity
    have hinv_le1 : ((2 : ℝ) ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2j_ge
    exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; linarith, by rw [Complex.ofReal_re]; linarith⟩
  have hG_open : IsOpen {t : ℂ | ∀ j : ℕ, 1 + t / (2 : ℂ) ^ j ≠ 0} := by
    rw [Metric.isOpen_iff]
    intro t₀ ht₀
    let R : ℝ := ‖t₀‖ + 2
    let J₀ : ℕ := Nat.ceil (2 * R) + 1
    have h2J : 2 * R ≤ (2 : ℝ) ^ J₀ := by
      have h1 : (Nat.ceil (2 * R) + 1 : ℝ) < (2 : ℝ) ^ J₀ := by exact_mod_cast Nat.lt_two_pow_self
      linarith [Nat.le_ceil (2 * R)]
    have hne_fin : (Finset.range (J₀ + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
    let m₀ : ℝ := (Finset.range (J₀ + 1)).inf' hne_fin (fun j => ‖1 + t₀ / (2 : ℂ) ^ j‖)
    have hm₀ : 0 < m₀ := by
      dsimp only [m₀]; rw [Finset.lt_inf'_iff]; intro j _; exact norm_pos_iff.mpr (ht₀ j)
    refine ⟨min 1 (m₀ / 2), lt_min zero_lt_one (half_pos hm₀), fun t ht j => ?_⟩
    have hdist : ‖t - t₀‖ < min 1 (m₀ / 2) := by simpa [Metric.mem_ball, dist_eq_norm] using ht
    by_cases hj : j < J₀ + 1
    · have h0 : m₀ ≤ ‖1 + t₀ / (2 : ℂ) ^ j‖ :=
        Finset.inf'_le (f := fun i => ‖1 + t₀ / (2 : ℂ) ^ i‖) (Finset.mem_range.mpr hj)
      have hdiff : ‖(1 + t / (2 : ℂ) ^ j) - (1 + t₀ / (2 : ℂ) ^ j)‖ ≤ ‖t - t₀‖ := by
        rw [show (1 + t / (2 : ℂ) ^ j) - (1 + t₀ / (2 : ℂ) ^ j) = (t - t₀) / (2 : ℂ) ^ j by ring,
          norm_div, norm_pow, Complex.norm_ofNat]
        exact div_le_self (norm_nonneg _) (one_le_pow₀ (by norm_num))
      have htri := norm_sub_norm_le (1 + t₀ / (2 : ℂ) ^ j) (1 + t / (2 : ℂ) ^ j)
      rw [norm_sub_rev] at htri
      have hlt : ‖t - t₀‖ < m₀ / 2 := lt_of_lt_of_le hdist (min_le_right _ _)
      exact norm_pos_iff.mp (by linarith)
    · have htR : ‖t‖ ≤ R := by
        have h1 : ‖t‖ ≤ ‖t - t₀‖ + ‖t₀‖ := by calc ‖t‖ = ‖(t - t₀) + t₀‖ := by ring_nf
          _ ≤ ‖t - t₀‖ + ‖t₀‖ := norm_add_le _ _
        have hlt1 : ‖t - t₀‖ < 1 := lt_of_lt_of_le hdist (min_le_left _ _)
        dsimp only [R]; linarith
      have hle : ‖t / (2 : ℂ) ^ j‖ ≤ 1 / 2 := by
        rw [norm_div, norm_pow, Complex.norm_ofNat, div_le_iff₀ (by positivity)]
        have h2j : (2 : ℝ) ^ J₀ ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
      have htri := norm_sub_norm_le (1 : ℂ) (-(t / (2 : ℂ) ^ j))
      simp only [sub_neg_eq_add, norm_one, norm_neg] at htri
      exact norm_pos_iff.mp (by linarith)
  have hd_G : DifferentiableAt ℂ (G_mero b) ξ⁻¹ :=
    (G_mero_differentiableOn hb _ hinv_mem).differentiableAt (hG_open.mem_nhds hinv_mem)
  unfold L_b
  exact ((differentiableAt_inv hξ_ne).fun_mul
    (hd_G.comp ξ (differentiableAt_inv hξ_ne))).differentiableWithinAt

/-- Exact contour deformation from the big square `[-R, R]²` (`R ≥ 10`) to the finite trapezoid
`T(r, 2)` for any `g` holomorphic on `ℂ \ [-1, 0]` and any `r ∈ (0, 1/2]`. -/
private lemma rectIntegral_eq_trapIntegral {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g SlitNegUnit)
    {R r : ℝ} (hR : 10 ≤ R) (hr0 : 0 < r) (hr1 : r ≤ 1 / 2) :
    rectIntegral g ((-R : ℂ) - (R : ℂ) * I) ((R : ℂ) + (R : ℂ) * I) = trapIntegral g r 2 := by
  have hint_h : ∀ {x₁ x₂ y : ℝ}, (∀ x ∈ Set.uIcc x₁ x₂, ((x : ℂ) + (y : ℂ) * I) ∈ SlitNegUnit) →
      IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (y : ℂ) * I)) volume x₁ x₂ := by
    intro x₁ x₂ y hmem
    exact ContinuousOn.intervalIntegrable
      (hg.continuousOn.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + (y : ℂ) * I).continuousOn
        fun x hx => hmem x hx)
  have hint_v : ∀ {x y₁ y₂ : ℝ}, (∀ y ∈ Set.uIcc y₁ y₂, ((x : ℂ) + (y : ℂ) * I) ∈ SlitNegUnit) →
      IntervalIntegrable (fun y : ℝ => g ((x : ℂ) + (y : ℂ) * I)) volume y₁ y₂ := by
    intro x y₁ y₂ hmem
    exact ContinuousOn.intervalIntegrable
      (hg.continuousOn.comp (by fun_prop : Continuous fun y : ℝ => (x : ℂ) + (y : ℂ) * I).continuousOn
        fun y hy => hmem y hy)
  -- Step 1: Shrink `[-R, R]²` to `[r - 2, r] × [-(r + 2), r + 2]` by 4 rectangle splits!
  have hmem_im_ne : ∀ {x y : ℝ}, y ≠ 0 → ((x : ℂ) + (y : ℂ) * I) ∈ SlitNegUnit := by
    intro x y hy h; exact hy (by simpa using h.1)
  have hmem_re_lt : ∀ {x y : ℝ}, x < -1 → ((x : ℂ) + (y : ℂ) * I) ∈ SlitNegUnit := by
    intro x y hx h
    have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
    linarith [h.2.1]
  have hmem_re_pos : ∀ {x y : ℝ}, 0 < x → ((x : ℂ) + (y : ℂ) * I) ∈ SlitNegUnit := by
    intro x y hx h
    have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
    linarith [h.2.2]
  have hbox_eq : rectIntegral g ((-R : ℂ) - (R : ℂ) * I) ((R : ℂ) + (R : ℂ) * I) =
      rectIntegral g (((r - 2 : ℝ) : ℂ) + ((-(r + 2) : ℝ) : ℂ) * I)
        ((r : ℂ) + ((r + 2 : ℝ) : ℂ) * I) := by
    have hzw : ((-R : ℂ) - (R : ℂ) * I) = ((-R : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * I := by push_cast; ring
    rw [hzw]
    have hs1 := rectIntegral_hsplit (f := g) (x₁ := -R) (x₀ := r - 2) (x₂ := R) (y₁ := -R) (y₂ := R)
      (hint_h fun _ _ => hmem_im_ne (by linarith)) (hint_h fun _ _ => hmem_im_ne (by linarith))
      (hint_h fun _ _ => hmem_im_ne (by linarith)) (hint_h fun _ _ => hmem_im_ne (by linarith))
    have hs2 := rectIntegral_hsplit (f := g) (x₁ := r - 2) (x₀ := r) (x₂ := R) (y₁ := -R) (y₂ := R)
      (hint_h fun _ _ => hmem_im_ne (by linarith)) (hint_h fun _ _ => hmem_im_ne (by linarith))
      (hint_h fun _ _ => hmem_im_ne (by linarith)) (hint_h fun _ _ => hmem_im_ne (by linarith))
    have hs3 := rectIntegral_vsplit (f := g) (x₁ := r - 2) (x₂ := r) (y₁ := -R) (y₀ := -(r + 2)) (y₂ := R)
      (hint_v fun _ _ => hmem_re_pos hr0) (hint_v fun _ _ => hmem_re_pos hr0)
      (hint_v fun _ _ => hmem_re_lt (by linarith)) (hint_v fun _ _ => hmem_re_lt (by linarith))
    have hs4 := rectIntegral_vsplit (f := g) (x₁ := r - 2) (x₂ := r) (y₁ := -(r + 2)) (y₀ := r + 2) (y₂ := R)
      (hint_v fun _ _ => hmem_re_pos hr0) (hint_v fun _ _ => hmem_re_pos hr0)
      (hint_v fun _ _ => hmem_re_lt (by linarith)) (hint_v fun _ _ => hmem_re_lt (by linarith))
    have hz1 : rectIntegral g (((-R : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * I) (((r - 2 : ℝ) : ℂ) + (R : ℂ) * I) = 0 := by
      refine rectIntegral_eq_zero_of_differentiableOn (hg.mono fun ζ hζ => ?_)
      simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero] at hζ
      rw [Set.uIcc_of_le (by linarith)] at hζ
      exact fun h => by linarith [h.2.1, hζ.1.2]
    have hz2 : rectIntegral g ((r : ℂ) + ((-R : ℝ) : ℂ) * I) ((R : ℂ) + (R : ℂ) * I) = 0 := by
      refine rectIntegral_eq_zero_of_differentiableOn (hg.mono fun ζ hζ => ?_)
      simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero] at hζ
      rw [Set.uIcc_of_le (by linarith)] at hζ
      exact fun h => by linarith [h.2.2, hζ.1.1]
    have hz3 : rectIntegral g (((r - 2 : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * I) ((r : ℂ) + ((-(r + 2) : ℝ) : ℂ) * I) = 0 := by
      refine rectIntegral_eq_zero_of_differentiableOn (hg.mono fun ζ hζ => ?_)
      simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
        mul_one, zero_add] at hζ
      rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hζ
      exact fun h => by linarith [h.1, hζ.2.2]
    have hz4 : rectIntegral g (((r - 2 : ℝ) : ℂ) + ((r + 2 : ℝ) : ℂ) * I) ((r : ℂ) + (R : ℂ) * I) = 0 := by
      refine rectIntegral_eq_zero_of_differentiableOn (hg.mono fun ζ hζ => ?_)
      simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
        mul_one, zero_add] at hζ
      rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hζ
      exact fun h => by linarith [h.1, hζ.2.1]
    rw [hs1, hz1, zero_add, hs2, hz2, add_zero, hs3, hz3, zero_add, hs4, hz4, add_zero]
  -- Step 2: Cut off the top-right triangle in `{0 < Im}` and bottom-right triangle in `{Im < 0}` via `exists_primitive_on_openRect`!
  rw [hbox_eq]
  obtain ⟨F_top, hF_top⟩ := exists_primitive_on_openRect (g := g) (a := r - 3) (b := r + 1)
    (c := r / 2) (d := r + 3) (by linarith) (by linarith)
    (hg.mono fun ζ hζ h => by linarith [hζ.2.1, h.1])
  obtain ⟨F_bot, hF_bot⟩ := exists_primitive_on_openRect (g := g) (a := r - 3) (b := r + 1)
    (c := -(r + 3)) (d := -(r / 2)) (by linarith) (by linarith)
    (hg.mono fun ζ hζ h => by linarith [hζ.2.2, h.1])
  -- Helper for evaluating line integrals along linear segments inside an open rectangle:
  have hseg : ∀ (F : ℂ → ℂ) (a₁ b₁ c₁ d₁ : ℝ)
      (hsub : Set.Ioo a₁ b₁ ×ℂ Set.Ioo c₁ d₁ ⊆ SlitNegUnit)
      (hF : ∀ z ∈ Set.Ioo a₁ b₁ ×ℂ Set.Ioo c₁ d₁, HasDerivAt F (g z) z)
      (t₁ t₂ : ℝ) (p v : ℂ),
      (∀ t ∈ Set.uIcc t₁ t₂, p + (t : ℂ) * v ∈ Set.Ioo a₁ b₁ ×ℂ Set.Ioo c₁ d₁) →
      v * (∫ t : ℝ in t₁..t₂, g (p + (t : ℂ) * v)) = F (p + (t₂ : ℂ) * v) - F (p + (t₁ : ℂ) * v) := by
    intro F a₁ b₁ c₁ d₁ hsub hF t₁ t₂ p v hmem
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => F (p + (t : ℂ) * v)) (fun t ht => ?_) ?_
    · have hlin : HasDerivAt (fun s : ℝ => p + (s : ℂ) * v) v t := by
        simpa using (Complex.ofRealCLM.hasDerivAt.mul_const v).const_add p
      simpa [Function.comp_def, mul_comm] using (hF _ (hmem t ht)).comp t hlin
    · refine ContinuousOn.intervalIntegrable ?_
      exact continuousOn_const.mul (hg.continuousOn.comp
        (by fun_prop : Continuous fun t : ℝ => p + (t : ℂ) * v).continuousOn fun t ht => hsub (hmem t ht))
  have hsub_top : Set.Ioo (r - 3) (r + 1) ×ℂ Set.Ioo (r / 2) (r + 3) ⊆ SlitNegUnit :=
    fun ζ hζ h => by linarith [hζ.2.1, h.1]
  have hsub_bot : Set.Ioo (r - 3) (r + 1) ×ℂ Set.Ioo (-(r + 3)) (-(r / 2)) ⊆ SlitNegUnit :=
    fun ζ hζ h => by linarith [hζ.2.2, h.1]
  -- Top-right triangle: `I * ∫_r^{r+2} g(r + iy) dy - ∫_{r-2}^r g(x + i(r+2)) dx = (-1 + I) * ∫_0^2 g((r - s) + i(r + s)) ds`!
  have htri_top : I * (∫ y : ℝ in r..(r + 2), g ((r : ℂ) + (y : ℂ) * I)) -
      (∫ x : ℝ in (r - 2)..r, g ((x : ℂ) + ((r + 2 : ℝ) : ℂ) * I)) =
      (-1 + I) * (∫ s : ℝ in (0 : ℝ)..(2 : ℝ), g (((r - s : ℝ) : ℂ) + ((r + s : ℝ) : ℂ) * I)) := by
    have h1 := hseg F_top _ _ _ _ hsub_top hF_top r (r + 2) (r : ℂ) I (fun y hy => by
      rw [Set.uIcc_of_le (by linarith)] at hy
      simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
        Complex.mul_im, zero_add]
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩)
    have h2 := hseg F_top _ _ _ _ hsub_top hF_top (r - 2) r (((r + 2 : ℝ) : ℂ) * I) 1 (fun x hx => by
      rw [Set.uIcc_of_le (by linarith)] at hx
      simp only [mul_one, Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, zero_add,
        Complex.add_im, Complex.mul_im, add_zero]
      exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ⟨by linarith, by linarith⟩⟩)
    have h3 := hseg F_top _ _ _ _ hsub_top hF_top 0 2 ((r : ℂ) + (r : ℂ) * I) (-1 + I) (fun s hs => by
      rw [Set.uIcc_of_le (by norm_num)] at hs
      have hrew : ((r : ℂ) + (r : ℂ) * I) + (s : ℂ) * (-1 + I) = ((r - s : ℝ) : ℂ) + ((r + s : ℝ) : ℂ) * I := by
        push_cast; ring
      rw [hrew]
      simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
        Complex.mul_im, zero_add]
      exact ⟨⟨by linarith [hs.2], by linarith [hs.1]⟩, ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩)
    have h2' : (∫ x : ℝ in (r - 2)..r, g ((x : ℂ) + ((r + 2 : ℝ) : ℂ) * I)) =
        F_top ((r : ℂ) + ((r + 2 : ℝ) : ℂ) * I) - F_top (((r - 2 : ℝ) : ℂ) + ((r + 2 : ℝ) : ℂ) * I) := by
      simpa [one_mul, mul_one, add_comm] using h2
    have h3' : (-1 + I) * (∫ s : ℝ in (0 : ℝ)..(2 : ℝ), g (((r - s : ℝ) : ℂ) + ((r + s : ℝ) : ℂ) * I)) =
        F_top (((r - 2 : ℝ) : ℂ) + ((r + 2 : ℝ) : ℂ) * I) - F_top ((r : ℂ) + (r : ℂ) * I) := by
      have hrew_fn : (fun s : ℝ => g (((r : ℂ) + (r : ℂ) * I) + (s : ℂ) * (-1 + I))) =
          fun s : ℝ => g (((r - s : ℝ) : ℂ) + ((r + s : ℝ) : ℂ) * I) := by
        funext s; congr 1; push_cast; ring
      rw [hrew_fn] at h3
      convert h3 using 1
      congr 1 <;> (push_cast; ring)
    rw [h1, h2', h3']; ring
  -- Bottom-right triangle: `∫_{r-2}^r g(x - i(r+2)) dx + I * ∫_{-(r+2)}^{-r} g(r + iy) dy = (1 + I) * ∫_0^2 g((r - s) - i(r + s)) ds`!
  have htri_bot : (∫ x : ℝ in (r - 2)..r, g ((x : ℂ) + ((-(r + 2) : ℝ) : ℂ) * I)) +
      I * (∫ y : ℝ in (-(r + 2))..(-r), g ((r : ℂ) + (y : ℂ) * I)) =
      (1 + I) * (∫ s : ℝ in (0 : ℝ)..(2 : ℝ), g (((r - s : ℝ) : ℂ) - ((r + s : ℝ) : ℂ) * I)) := by
    have h1 := hseg F_bot _ _ _ _ hsub_bot hF_bot (-(r + 2)) (-r) (r : ℂ) I (fun y hy => by
      rw [Set.uIcc_of_le (by linarith)] at hy
      simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
        Complex.mul_im, zero_add]
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩)
    have h2 := hseg F_bot _ _ _ _ hsub_bot hF_bot (r - 2) r (((-(r + 2) : ℝ) : ℂ) * I) 1 (fun x hx => by
      rw [Set.uIcc_of_le (by linarith)] at hx
      simp only [mul_one, Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, zero_add,
        Complex.add_im, Complex.mul_im, add_zero]
      exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ⟨by linarith, by linarith⟩⟩)
    have h3 := hseg F_bot _ _ _ _ hsub_bot hF_bot 0 2 ((r : ℂ) - (r : ℂ) * I) (-1 - I) (fun s hs => by
      rw [Set.uIcc_of_le (by norm_num)] at hs
      have hrew : ((r : ℂ) - (r : ℂ) * I) + (s : ℂ) * (-1 - I) = ((r - s : ℝ) : ℂ) + ((-(r + s) : ℝ) : ℂ) * I := by
        push_cast; ring
      rw [hrew]
      simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
        Complex.mul_im, zero_add]
      exact ⟨⟨by linarith [hs.2], by linarith [hs.1]⟩, ⟨by linarith [hs.2], by linarith [hs.1]⟩⟩)
    have h2' : (∫ x : ℝ in (r - 2)..r, g ((x : ℂ) + ((-(r + 2) : ℝ) : ℂ) * I)) =
        F_bot ((r : ℂ) + ((-(r + 2) : ℝ) : ℂ) * I) - F_bot (((r - 2 : ℝ) : ℂ) + ((-(r + 2) : ℝ) : ℂ) * I) := by
      simpa [one_mul, mul_one, add_comm] using h2
    have h3' : (-1 - I) * (∫ s : ℝ in (0 : ℝ)..(2 : ℝ), g (((r - s : ℝ) : ℂ) - ((r + s : ℝ) : ℂ) * I)) =
        F_bot (((r - 2 : ℝ) : ℂ) + ((-(r + 2) : ℝ) : ℂ) * I) - F_bot ((r : ℂ) + ((-r : ℝ) : ℂ) * I) := by
      have hrew_fn : (fun s : ℝ => g (((r : ℂ) - (r : ℂ) * I) + (s : ℂ) * (-1 - I))) =
          fun s : ℝ => g (((r - s : ℝ) : ℂ) - ((r + s : ℝ) : ℂ) * I) := by
        funext s; congr 1; push_cast; ring
      rw [hrew_fn] at h3
      convert h3 using 1
      congr 1 <;> (push_cast; ring)
    rw [h1, h2']
    linear_combination h3'
  -- Assemble all 4 pieces of `rectIntegral` into `trapIntegral g r 2`!
  unfold rectIntegral trapIntegral
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, zero_add]
  have hright_split : (∫ y : ℝ in (-(r + 2))..(r + 2), g ((r : ℂ) + (y : ℂ) * I)) =
      (∫ y : ℝ in (-(r + 2))..(-r), g ((r : ℂ) + (y : ℂ) * I)) +
      (∫ y : ℝ in (-r)..r, g ((r : ℂ) + (y : ℂ) * I)) +
      (∫ y : ℝ in r..(r + 2), g ((r : ℂ) + (y : ℂ) * I)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := r)
      (hint_v fun _ _ => hmem_re_pos hr0) (hint_v fun _ _ => hmem_re_pos hr0),
      ← intervalIntegral.integral_add_adjacent_intervals (b := -r)
      (hint_v fun _ _ => hmem_re_pos hr0) (hint_v fun _ _ => hmem_re_pos hr0)]
  rw [hright_split]
  linear_combination htri_bot + htri_top

/-! ### Infinite Hankel Contour Integral & Exact Reciprocal-Gamma Formula `(2πi)⁻¹ ∫_{H_∞} ζ^{-s} e^ζ dζ = 1 / Γ(s)` -/

/-- Infinite 3-edge Hankel contour integral at radius `r > 0` (`arg ζ ∈ [-3π/4, 3π/4]`). -/
@[expose] def hankelIntegralR (r : ℝ) (f : ℂ → ℂ) : ℂ :=
  (1 + I) * (∫ u in Set.Ioi (0 : ℝ), f (((r - u : ℝ) : ℂ) - ((r + u : ℝ) : ℂ) * I)) +
  I * (∫ y : ℝ in (-r)..r, f ((r : ℂ) + (y : ℂ) * I)) +
  (-1 + I) * (∫ u in Set.Ioi (0 : ℝ), f (((r - u : ℝ) : ℂ) + ((r + u : ℝ) : ℂ) * I))

/-- Standard unit-radius infinite Hankel contour integral `H_∞` (`r = 1`). -/
@[expose] def hankelIntegral (f : ℂ → ℂ) : ℂ := hankelIntegralR 1 f

/-- Helper: `log(z * r) = log z + log r` and `log(z / r) = log z - log r` for `z ≠ 0` and real `r > 0`. -/
private lemma Complex.log_mul_ofReal_pos {z : ℂ} (hz : z ≠ 0) {r : ℝ} (hr : 0 < r) :
    Complex.log (z * (r : ℂ)) = Complex.log z + Complex.log (r : ℂ) := by
  refine Complex.log_mul hz (Complex.ofReal_ne_zero.mpr hr.ne') ?_
  rw [Complex.arg_ofReal_of_nonneg hr.le, add_zero]
  exact Complex.arg_mem_Ioc z

private lemma Complex.log_div_ofReal_pos {z : ℂ} (hz : z ≠ 0) {r : ℝ} (hr : 0 < r) :
    Complex.log (z / (r : ℂ)) = Complex.log z - Complex.log (r : ℂ) := by
  have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have h := Complex.log_mul_ofReal_pos (div_ne_zero hz hr_ne) hr
  rw [div_mul_cancel₀ _ hr_ne] at h
  linear_combination -h

/-- Every point on the Hankel rays `(r - u) ± i(r + u)` (`r > 0, u ≥ 0`) lies in `Complex.slitPlane`
with `|arg ζ| < 3π / 4` and `r + u ≤ ‖ζ‖ ≤ 2 * (r + u)`. -/
private lemma hankel_ray_props {r u : ℝ} (hr : 0 < r) (hu : 0 ≤ u) (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    let ζ : ℂ := ((r - u : ℝ) : ℂ) + ((sgn * (r + u) : ℝ) : ℂ) * I
    ζ ∈ Complex.slitPlane ∧ ζ ≠ 0 ∧ r + u ≤ ‖ζ‖ ∧ ‖ζ‖ ≤ 2 * (r + u) ∧ |ζ.arg| ≤ 3 * Real.pi / 4 := by
  intro ζ
  have him_eq : ζ.im = sgn * (r + u) := by dsimp only [ζ]; simp
  have hre_eq : ζ.re = r - u := by dsimp only [ζ]; simp
  have him_ne : ζ.im ≠ 0 := by
    rw [him_eq]; rcases hsgn with rfl | rfl <;> linarith
  have hslit : ζ ∈ Complex.slitPlane := Or.inr him_ne
  have hne : ζ ≠ 0 := fun h0 => him_ne (by rw [h0, Complex.zero_im])
  have habs_sgn : |sgn * (r + u)| = r + u := by
    rw [abs_mul, abs_of_pos (by linarith : 0 < r + u)]
    rcases hsgn with rfl | rfl <;> norm_num
  have hlb : r + u ≤ ‖ζ‖ := by
    calc r + u = |sgn * (r + u)| := habs_sgn.symm
      _ = |ζ.im| := by rw [him_eq]
      _ ≤ ‖ζ‖ := Complex.abs_im_le_norm ζ
  have hub : ‖ζ‖ ≤ 2 * (r + u) := by
    calc ‖ζ‖ ≤ |ζ.re| + |ζ.im| := Complex.norm_le_abs_re_add_abs_im ζ
      _ = |r - u| + |sgn * (r + u)| := by rw [hre_eq, him_eq]
      _ ≤ (r + u) + (r + u) := by
          have h1 : |r - u| ≤ r + u := abs_le.mpr ⟨by linarith, by linarith⟩
          linarith
      _ = 2 * (r + u) := by ring
  -- Bound `|ζ.arg| ≤ 3π/4`: since `ζ.re ≥ -|ζ.im|`, `cos |arg ζ| = ζ.re / ‖ζ‖ ≥ -1 / √2 = cos(3π/4)`!
  have harg : |ζ.arg| ≤ 3 * Real.pi / 4 := by
    have habs_le_pi : |ζ.arg| ≤ Real.pi := Complex.abs_arg_le_pi ζ
    have hcos_ge : Real.cos (3 * Real.pi / 4) ≤ Real.cos |ζ.arg| := by
      rw [Real.cos_abs, Complex.cos_arg hne,
        show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring, Real.cos_pi_sub, Real.cos_pi_div_four]
      rw [hre_eq]
      rcases le_total u r with hur | hru
      · have h1 : 0 ≤ (r - u) / ‖ζ‖ := div_nonneg (by linarith) (norm_nonneg _)
        have h2 : 0 ≤ Real.sqrt 2 / 2 := by positivity
        linarith
      · have hsq : 2 * (u - r) ^ 2 ≤ ‖ζ‖ ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre_eq, him_eq]
          rcases hsgn with rfl | rfl <;> nlinarith
        have hroot : Real.sqrt 2 * (u - r) ≤ ‖ζ‖ := by
          have hnn : 0 ≤ Real.sqrt 2 * (u - r) := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), norm_nonneg ζ]
        rw [le_div_iff₀ (norm_pos_iff.mpr hne)]
        have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
        nlinarith [Real.sqrt_nonneg 2]
    have hmem1 : |ζ.arg| ∈ Set.Icc (0 : ℝ) Real.pi := ⟨abs_nonneg _, habs_le_pi⟩
    have hmem2 : 3 * Real.pi / 4 ∈ Set.Icc (0 : ℝ) Real.pi := ⟨by positivity, by linarith [Real.pi_pos]⟩
    exact (Real.strictAntiOn_cos.le_iff_ge hmem2 hmem1).mp hcos_ge
  exact ⟨hslit, hne, hlb, hub, harg⟩

/-- Uniform growth bound for `‖exp(-s * log ζ)‖` when `r ≤ ‖ζ‖` and `‖ζ‖ ≤ M`. -/
private lemma norm_exp_neg_mul_log_le (s ζ : ℂ) (hζ : ζ ≠ 0) :
    ‖Complex.exp (-s * Complex.log ζ)‖ ≤
      (max 1 ‖ζ‖) ^ |s.re| * (max 1 ‖ζ‖⁻¹) ^ |s.re| * Real.exp (Real.pi * |s.im|) := by
  rw [Complex.norm_exp]
  have hre : (-s * Complex.log ζ).re = -s.re * Real.log ‖ζ‖ + s.im * ζ.arg := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.log_re, Complex.log_im]
    ring
  rw [hre, Real.exp_add]
  have h1 : Real.exp (-s.re * Real.log ‖ζ‖) ≤ (max 1 ‖ζ‖) ^ |s.re| * (max 1 ‖ζ‖⁻¹) ^ |s.re| := by
    have hn_pos : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
    have hlog_eq : Real.exp (-s.re * Real.log ‖ζ‖) = ‖ζ‖ ^ (-s.re) := by
      rw [Real.rpow_def_of_pos hn_pos, mul_comm]
    rw [hlog_eq]
    rcases le_total 0 s.re with hs | hs
    · have h1' : ‖ζ‖ ^ (-s.re) = (‖ζ‖⁻¹) ^ s.re := by rw [Real.rpow_neg hn_pos.le, Real.inv_rpow hn_pos.le]
      rw [h1', abs_of_nonneg hs]
      calc (‖ζ‖⁻¹) ^ s.re ≤ (max 1 ‖ζ‖⁻¹) ^ s.re := Real.rpow_le_rpow (by positivity) (le_max_right _ _) hs
        _ = 1 * (max 1 ‖ζ‖⁻¹) ^ s.re := (one_mul _).symm
        _ ≤ (max 1 ‖ζ‖) ^ s.re * (max 1 ‖ζ‖⁻¹) ^ s.re :=
            mul_le_mul_of_nonneg_right (Real.one_le_rpow (le_max_left 1 ‖ζ‖) hs) (by positivity)
    · rw [abs_of_nonpos hs]
      calc ‖ζ‖ ^ (-s.re) ≤ (max 1 ‖ζ‖) ^ (-s.re) := Real.rpow_le_rpow hn_pos.le (le_max_right _ _) (by linarith)
        _ = (max 1 ‖ζ‖) ^ (-s.re) * 1 := (mul_one _).symm
        _ ≤ (max 1 ‖ζ‖) ^ (-s.re) * (max 1 ‖ζ‖⁻¹) ^ (-s.re) :=
            mul_le_mul_of_nonneg_left (Real.one_le_rpow (le_max_left 1 ‖ζ‖⁻¹) (by linarith)) (by positivity)
  have h2 : Real.exp (s.im * ζ.arg) ≤ Real.exp (Real.pi * |s.im|) := by
    refine Real.exp_le_exp.mpr ?_
    calc s.im * ζ.arg ≤ |s.im * ζ.arg| := le_abs_self _
      _ = |s.im| * |ζ.arg| := abs_mul _ _
      _ ≤ |s.im| * Real.pi := mul_le_mul_of_nonneg_left (Complex.abs_arg_le_pi ζ) (abs_nonneg _)
      _ = Real.pi * |s.im| := mul_comm _ _
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)

/-- Polynomial-times-exponential integrability on `Ioi 0`: `u ↦ (1 + u)^n * exp(-c * u)` for `0 < c`. -/
private lemma integrableOn_one_add_pow_mul_exp_neg (n : ℕ) {c : ℝ} (hc : 0 < c) :
    MeasureTheory.IntegrableOn (fun u : ℝ => (1 + u) ^ n * Real.exp (-c * u)) (Set.Ioi 0) volume := by
  have hbd : ∀ u ∈ Set.Ioi (0 : ℝ), ‖(1 + u) ^ n * Real.exp (-c * u)‖ ≤
      ((n.factorial : ℝ) / (c / 2) ^ n * Real.exp (c / 2)) * Real.exp (-(c / 2) * u) := fun u hu => by
    have hu0 : 0 < u := hu
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : ((c / 2) * (1 + u)) ^ n / (n.factorial : ℝ) ≤ Real.exp ((c / 2) * (1 + u)) :=
      Real.pow_div_factorial_le_exp _ (by positivity) n
    have h2 : (1 + u) ^ n ≤ ((n.factorial : ℝ) / (c / 2) ^ n) * Real.exp ((c / 2) * (1 + u)) := by
      rw [mul_pow] at h1
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have h1' := (div_le_iff₀ (by positivity)).mp h1
      linarith
    calc (1 + u) ^ n * Real.exp (-c * u)
        ≤ (((n.factorial : ℝ) / (c / 2) ^ n) * Real.exp ((c / 2) * (1 + u))) * Real.exp (-c * u) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = ((n.factorial : ℝ) / (c / 2) ^ n * Real.exp (c / 2)) * Real.exp (-(c / 2) * u) := by
          rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]; congr 2; ring
  have hdom : MeasureTheory.IntegrableOn
      (fun u : ℝ => ((n.factorial : ℝ) / (c / 2) ^ n * Real.exp (c / 2)) * Real.exp (-(c / 2) * u))
      (Set.Ioi 0) volume :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _
  refine hdom.mono' (by fun_prop : Continuous fun u : ℝ => (1 + u) ^ n * Real.exp (-c * u)).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
  exact hbd u hu

/-- Integrability of the Hankel integrand `u ↦ exp(-s * log ζ(u)) * exp(ζ(u))` on `Ioi 0` for any `r > 0, s : ℂ`. -/
private lemma integrableOn_hankel_ray {r : ℝ} (hr : 0 < r) (s : ℂ) (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => Complex.exp (-s * Complex.log (((r - u : ℝ) : ℂ) + ((sgn * (r + u) : ℝ) : ℂ) * I)) *
        Complex.exp (((r - u : ℝ) : ℂ) + ((sgn * (r + u) : ℝ) : ℂ) * I)) (Set.Ioi 0) volume := by
  let N : ℕ := Nat.ceil |s.re|
  let C : ℝ := (max 1 (2 * max 1 r)) ^ N * (max 1 r⁻¹) ^ |s.re| * Real.exp (Real.pi * |s.im|) * Real.exp r
  have hbd : ∀ u ∈ Set.Ioi (0 : ℝ),
      ‖Complex.exp (-s * Complex.log (((r - u : ℝ) : ℂ) + ((sgn * (r + u) : ℝ) : ℂ) * I)) *
        Complex.exp (((r - u : ℝ) : ℂ) + ((sgn * (r + u) : ℝ) : ℂ) * I)‖ ≤
        C * ((1 + u) ^ N * Real.exp (-1 * u)) := fun u hu => by
    have hu0 : 0 ≤ u := le_of_lt hu
    obtain ⟨_, hne, hlb, hub, _⟩ := hankel_ray_props hr hu0 sgn hsgn
    let ζ : ℂ := ((r - u : ℝ) : ℂ) + ((sgn * (r + u) : ℝ) : ℂ) * I
    change ‖Complex.exp (-s * Complex.log ζ) * Complex.exp ζ‖ ≤ _
    rw [norm_mul, Complex.norm_exp ζ]
    have hre : ζ.re = r - u := by dsimp only [ζ]; simp
    have h1 := norm_exp_neg_mul_log_le s ζ hne
    have hmax1 : (max 1 ‖ζ‖) ^ |s.re| ≤ (max 1 (2 * max 1 r)) ^ N * (1 + u) ^ N := by
      have hle : max 1 ‖ζ‖ ≤ max 1 (2 * max 1 r) * (1 + u) := by
        refine max_le ?_ ?_
        · exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (by linarith)
        · calc ‖ζ‖ ≤ 2 * (r + u) := hub
            _ ≤ 2 * max 1 r * (1 + u) := by nlinarith [le_max_left (1 : ℝ) r, le_max_right (1 : ℝ) r]
            _ ≤ max 1 (2 * max 1 r) * (1 + u) :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
      have hge1 : 1 ≤ max 1 (2 * max 1 r) * (1 + u) :=
        one_le_mul_of_one_le_of_one_le (le_max_left _ _) (by linarith)
      calc (max 1 ‖ζ‖) ^ |s.re| ≤ (max 1 (2 * max 1 r) * (1 + u)) ^ |s.re| :=
            Real.rpow_le_rpow (by positivity) hle (abs_nonneg _)
        _ ≤ (max 1 (2 * max 1 r) * (1 + u)) ^ (N : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hge1 (Nat.le_ceil _)
        _ = (max 1 (2 * max 1 r) * (1 + u)) ^ N := Real.rpow_natCast _ N
        _ = (max 1 (2 * max 1 r)) ^ N * (1 + u) ^ N := mul_pow _ _ N
    have hmax2 : (max 1 ‖ζ‖⁻¹) ^ |s.re| ≤ (max 1 r⁻¹) ^ |s.re| := by
      refine Real.rpow_le_rpow (by positivity) (max_le_max_left 1 ?_) (abs_nonneg _)
      exact inv_anti₀ hr (by linarith)
    calc ‖Complex.exp (-s * Complex.log ζ)‖ * Real.exp ζ.re
        ≤ ((max 1 ‖ζ‖) ^ |s.re| * (max 1 ‖ζ‖⁻¹) ^ |s.re| * Real.exp (Real.pi * |s.im|)) *
            Real.exp (r - u) := by
          rw [hre]; exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ (((max 1 (2 * max 1 r)) ^ N * (1 + u) ^ N) * (max 1 r⁻¹) ^ |s.re| * Real.exp (Real.pi * |s.im|)) *
            (Real.exp r * Real.exp (-1 * u)) := by
          rw [show r - u = r + (-1 * u) by ring, Real.exp_add]
          gcongr
      _ = C * ((1 + u) ^ N * Real.exp (-1 * u)) := by dsimp only [C]; ring
  have hcont : ContinuousOn
      (fun u : ℝ => Complex.exp (-s * Complex.log (((r - u : ℝ) : ℂ) + ((sgn * (r + u) : ℝ) : ℂ) * I)) *
        Complex.exp (((r - u : ℝ) : ℂ) + ((sgn * (r + u) : ℝ) : ℂ) * I)) (Set.Ioi 0) := by
    intro u hu
    obtain ⟨hslit, _, _, _, _⟩ := hankel_ray_props hr (le_of_lt hu) sgn hsgn
    have hlin : ContinuousAt (fun t : ℝ => ((r - t : ℝ) : ℂ) + ((sgn * (r + t) : ℝ) : ℂ) * I) u := by fun_prop
    have hlog : ContinuousAt (fun t : ℝ => Complex.log (((r - t : ℝ) : ℂ) + ((sgn * (r + t) : ℝ) : ℂ) * I)) u :=
      ContinuousAt.comp (g := Complex.log) (Complex.hasDerivAt_log hslit).continuousAt hlin
    have hexp : ContinuousAt (fun t : ℝ => Complex.exp (((r - t : ℝ) : ℂ) + ((sgn * (r + t) : ℝ) : ℂ) * I)) u :=
      ContinuousAt.comp (g := Complex.exp) Complex.continuous_exp.continuousAt hlin
    exact (((hlog.const_mul (-s)).cexp).mul hexp).continuousWithinAt
  refine ((integrableOn_one_add_pow_mul_exp_neg N zero_lt_one).const_mul C).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
  exact hbd u hu

/-- Integration by parts along the Hankel contour: for EVERY `s : ℂ` and `r > 0`,
`hankelIntegralR r (ζ ↦ exp(-s * log ζ) * exp ζ) = s * hankelIntegralR r (ζ ↦ exp(-(s + 1) * log ζ) * exp ζ)`. -/
private lemma hankelIntegralR_ibp {r : ℝ} (hr : 0 < r) (s : ℂ) :
    hankelIntegralR r (fun ζ => Complex.exp (-s * Complex.log ζ) * Complex.exp ζ) =
      s * hankelIntegralR r (fun ζ => Complex.exp (-(s + 1) * Complex.log ζ) * Complex.exp ζ) := by
  let F : ℂ → ℂ := fun ζ => Complex.exp (-s * Complex.log ζ) * Complex.exp ζ
  let G : ℂ → ℂ := fun ζ => Complex.exp (-(s + 1) * Complex.log ζ) * Complex.exp ζ
  have hderiv : ∀ ζ ∈ Complex.slitPlane, HasDerivAt F (F ζ - s * G ζ) ζ := fun ζ hζ => by
    have hne : ζ ≠ 0 := Complex.slitPlane_ne_zero hζ
    have hd1 : HasDerivAt (fun w : ℂ => Complex.exp (-s * Complex.log w))
        (Complex.exp (-s * Complex.log ζ) * (-s * ζ⁻¹)) ζ :=
      ((Complex.hasDerivAt_log hζ).const_mul (-s)).cexp
    have hd2 : HasDerivAt Complex.exp (Complex.exp ζ) ζ := Complex.hasDerivAt_exp ζ
    have hprod := hd1.fun_mul hd2
    convert hprod using 1
    dsimp only [F, G]
    have hlog1 : Complex.exp (-(s + 1) * Complex.log ζ) = Complex.exp (-s * Complex.log ζ) * ζ⁻¹ := by
      rw [show -(s + 1) * Complex.log ζ = (-s * Complex.log ζ) + (-Complex.log ζ) by ring,
        Complex.exp_add, Complex.exp_neg, Complex.exp_log hne]
    rw [hlog1]; ring
  have htend_ray : ∀ sgn : ℝ, sgn = 1 ∨ sgn = -1 →
      Filter.Tendsto (fun u : ℝ => F (((r - u : ℝ) : ℂ) + ((sgn * (r + u) : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
    intro sgn hsgn
    rw [tendsto_zero_iff_norm_tendsto_zero]
    let N : ℕ := Nat.ceil |s.re|
    let C : ℝ := (max 1 (2 * max 1 r)) ^ N * (max 1 r⁻¹) ^ |s.re| * Real.exp (Real.pi * |s.im|) * Real.exp r
    have hbd : ∀ᶠ u : ℝ in atTop,
        ‖F (((r - u : ℝ) : ℂ) + ((sgn * (r + u) : ℝ) : ℂ) * I)‖ ≤
          (C * ((N + 1).factorial : ℝ) * Real.exp 1) / (1 + u) := by
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with u hu
      obtain ⟨_, hne, _, hub, _⟩ := hankel_ray_props hr hu sgn hsgn
      let ζ : ℂ := ((r - u : ℝ) : ℂ) + ((sgn * (r + u) : ℝ) : ℂ) * I
      have hre : ζ.re = r - u := by dsimp only [ζ]; simp
      have h1 := norm_exp_neg_mul_log_le s ζ hne
      have hmax1 : (max 1 ‖ζ‖) ^ |s.re| ≤ (max 1 (2 * max 1 r)) ^ N * (1 + u) ^ N := by
        have hle : max 1 ‖ζ‖ ≤ max 1 (2 * max 1 r) * (1 + u) := by
          refine max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (by linarith)) ?_
          calc ‖ζ‖ ≤ 2 * (r + u) := hub
            _ ≤ 2 * max 1 r * (1 + u) := by nlinarith [le_max_left (1 : ℝ) r, le_max_right (1 : ℝ) r]
            _ ≤ max 1 (2 * max 1 r) * (1 + u) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
        calc (max 1 ‖ζ‖) ^ |s.re| ≤ (max 1 (2 * max 1 r) * (1 + u)) ^ |s.re| :=
              Real.rpow_le_rpow (by positivity) hle (abs_nonneg _)
          _ ≤ (max 1 (2 * max 1 r) * (1 + u)) ^ (N : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (by linarith))
                (Nat.le_ceil _)
          _ = (max 1 (2 * max 1 r)) ^ N * (1 + u) ^ N := by rw [Real.rpow_natCast, mul_pow]
      have hmax2 : (max 1 ‖ζ‖⁻¹) ^ |s.re| ≤ (max 1 r⁻¹) ^ |s.re| := by
        refine Real.rpow_le_rpow (by positivity) (max_le_max_left 1 (inv_anti₀ hr (by linarith))) (abs_nonneg _)
      have hexp_neg_u : (1 + u) ^ N * Real.exp (-u) ≤ ((N + 1).factorial : ℝ) * Real.exp 1 / (1 + u) := by
        rw [le_div_iff₀ (by linarith : 0 < 1 + u)]
        have h1' : (1 + u) ^ (N + 1) ≤ Real.exp (1 + u) * ((N + 1).factorial : ℝ) :=
          (div_le_iff₀ (by positivity)).mp (Real.pow_div_factorial_le_exp (1 + u) (by linarith) (N + 1))
        calc (1 + u) ^ N * Real.exp (-u) * (1 + u)
            = (1 + u) ^ (N + 1) * Real.exp (-u) := by rw [pow_succ]; ring
          _ ≤ (Real.exp (1 + u) * ((N + 1).factorial : ℝ)) * Real.exp (-u) :=
              mul_le_mul_of_nonneg_right h1' (Real.exp_pos _).le
          _ = ((N + 1).factorial : ℝ) * (Real.exp (1 + u) * Real.exp (-u)) := by ring
          _ = ((N + 1).factorial : ℝ) * Real.exp 1 := by rw [← Real.exp_add]; congr 2; ring
      change ‖Complex.exp (-s * Complex.log ζ) * Complex.exp ζ‖ ≤ _
      rw [norm_mul, Complex.norm_exp ζ]
      calc ‖Complex.exp (-s * Complex.log ζ)‖ * Real.exp ζ.re
          ≤ ((max 1 ‖ζ‖) ^ |s.re| * (max 1 ‖ζ‖⁻¹) ^ |s.re| * Real.exp (Real.pi * |s.im|)) *
              (Real.exp r * Real.exp (-u)) := by
            rw [hre, sub_eq_add_neg, Real.exp_add]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ (((max 1 (2 * max 1 r)) ^ N * (1 + u) ^ N) * (max 1 r⁻¹) ^ |s.re| * Real.exp (Real.pi * |s.im|)) *
              (Real.exp r * Real.exp (-u)) := by gcongr
        _ = C * ((1 + u) ^ N * Real.exp (-u)) := by dsimp only [C]; ring
        _ ≤ C * (((N + 1).factorial : ℝ) * Real.exp 1 / (1 + u)) :=
            mul_le_mul_of_nonneg_left hexp_neg_u (by dsimp only [C]; positivity)
        _ = (C * ((N + 1).factorial : ℝ) * Real.exp 1) / (1 + u) := by ring
    exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbd
      (tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_mono (fun u : ℝ => le_add_of_nonneg_left zero_le_one) tendsto_id))
  -- Apply FTC on each of the 3 pieces of `hankelIntegralR r (F - s * G)`!
  have hbot : (1 + I) * (∫ u in Set.Ioi (0 : ℝ),
      (F (((r - u : ℝ) : ℂ) - ((r + u : ℝ) : ℂ) * I) - s * G (((r - u : ℝ) : ℂ) - ((r + u : ℝ) : ℂ) * I))) =
      F ((r : ℂ) - (r : ℂ) * I) := by
    have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
      (f := fun u : ℝ => F (((r - u : ℝ) : ℂ) - ((r + u : ℝ) : ℂ) * I))
      (f' := fun u : ℝ => (-1 - I) * (F (((r - u : ℝ) : ℂ) - ((r + u : ℝ) : ℂ) * I) -
        s * G (((r - u : ℝ) : ℂ) - ((r + u : ℝ) : ℂ) * I)))
      (a := 0) (m := 0)
      (by
        obtain ⟨hslit, _, _, _, _⟩ := hankel_ray_props hr le_rfl (-1) (Or.inr rfl)
        have hslit' : ((r - 0 : ℝ) : ℂ) - ((r + 0 : ℝ) : ℂ) * I ∈ Complex.slitPlane := by
          convert hslit using 1; push_cast; ring
        have hlin : ContinuousAt (fun u : ℝ => ((r - u : ℝ) : ℂ) - ((r + u : ℝ) : ℂ) * I) 0 := by fun_prop
        have hF0 : ContinuousAt F (((r - 0 : ℝ) : ℂ) - ((r + 0 : ℝ) : ℂ) * I) :=
          (hderiv _ hslit').continuousAt
        exact (ContinuousAt.comp (g := F) (f := fun u : ℝ => ((r - u : ℝ) : ℂ) - ((r + u : ℝ) : ℂ) * I)
          hF0 hlin).continuousWithinAt)
      (fun u hu => by
        obtain ⟨hslit, _, _, _, _⟩ := hankel_ray_props hr (le_of_lt hu) (-1) (Or.inr rfl)
        have hslit' : ((r - u : ℝ) : ℂ) - ((r + u : ℝ) : ℂ) * I ∈ Complex.slitPlane := by
          convert hslit using 1; push_cast; ring
        have hlin : HasDerivAt (fun t : ℝ => ((r - t : ℝ) : ℂ) - ((r + t : ℝ) : ℂ) * I) (-1 - I) u := by
          have h1 : HasDerivAt (fun t : ℝ => ((r - t : ℝ) : ℂ)) (-1) u := by
            have := ((hasDerivAt_id u).const_sub r).ofReal_comp; simpa using this
          have h2 : HasDerivAt (fun t : ℝ => ((r + t : ℝ) : ℂ) * I) I u := by
            have := ((hasDerivAt_id u).const_add r).ofReal_comp.mul_const I; simpa using this
          exact h1.fun_sub h2
        have hc := (hderiv _ hslit').comp u hlin
        simpa [Function.comp_def, mul_comm] using hc)
      (by
        have hi1 : MeasureTheory.IntegrableOn (fun u : ℝ => F (((r - u : ℝ) : ℂ) - ((r + u : ℝ) : ℂ) * I)) (Set.Ioi 0) volume :=
          (integrableOn_hankel_ray hr s (-1) (Or.inr rfl)).congr_fun
            (fun u _ => by dsimp only [F]; congr 2 <;> (push_cast; ring)) measurableSet_Ioi
        have hi2 : MeasureTheory.IntegrableOn (fun u : ℝ => s * G (((r - u : ℝ) : ℂ) - ((r + u : ℝ) : ℂ) * I)) (Set.Ioi 0) volume :=
          ((integrableOn_hankel_ray hr (s + 1) (-1) (Or.inr rfl)).congr_fun
            (fun u _ => by dsimp only [G]; congr 2 <;> (push_cast; ring)) measurableSet_Ioi).const_mul s
        exact (hi1.sub hi2).const_mul (-1 - I))
      (by
        have hcongr : (fun u : ℝ => F (((r - u : ℝ) : ℂ) - ((r + u : ℝ) : ℂ) * I)) =
            fun u : ℝ => F (((r - u : ℝ) : ℂ) + ((-1 * (r + u) : ℝ) : ℂ) * I) := by
          funext u; congr 1; push_cast; ring
        rw [hcongr]; exact htend_ray (-1) (Or.inr rfl))
    rw [MeasureTheory.integral_const_mul] at hftc
    simp only [sub_zero, add_zero, zero_sub] at hftc
    linear_combination -hftc
  have htop : (-1 + I) * (∫ u in Set.Ioi (0 : ℝ),
      (F (((r - u : ℝ) : ℂ) + ((r + u : ℝ) : ℂ) * I) - s * G (((r - u : ℝ) : ℂ) + ((r + u : ℝ) : ℂ) * I))) =
      -F ((r : ℂ) + (r : ℂ) * I) := by
    have hftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
      (f := fun u : ℝ => F (((r - u : ℝ) : ℂ) + ((r + u : ℝ) : ℂ) * I))
      (f' := fun u : ℝ => (-1 + I) * (F (((r - u : ℝ) : ℂ) + ((r + u : ℝ) : ℂ) * I) -
        s * G (((r - u : ℝ) : ℂ) + ((r + u : ℝ) : ℂ) * I)))
      (a := 0) (m := 0)
      (by
        obtain ⟨hslit, _, _, _, _⟩ := hankel_ray_props hr le_rfl 1 (Or.inl rfl)
        have hslit' : ((r - 0 : ℝ) : ℂ) + ((r + 0 : ℝ) : ℂ) * I ∈ Complex.slitPlane := by
          simpa [one_mul] using hslit
        have hlin : ContinuousAt (fun u : ℝ => ((r - u : ℝ) : ℂ) + ((r + u : ℝ) : ℂ) * I) 0 := by fun_prop
        have hF0 : ContinuousAt F (((r - 0 : ℝ) : ℂ) + ((r + 0 : ℝ) : ℂ) * I) :=
          (hderiv _ hslit').continuousAt
        exact (ContinuousAt.comp (g := F) (f := fun u : ℝ => ((r - u : ℝ) : ℂ) + ((r + u : ℝ) : ℂ) * I)
          hF0 hlin).continuousWithinAt)
      (fun u hu => by
        obtain ⟨hslit, _, _, _, _⟩ := hankel_ray_props hr (le_of_lt hu) 1 (Or.inl rfl)
        have hslit' : ((r - u : ℝ) : ℂ) + ((r + u : ℝ) : ℂ) * I ∈ Complex.slitPlane := by
          simpa [one_mul] using hslit
        have hlin : HasDerivAt (fun t : ℝ => ((r - t : ℝ) : ℂ) + ((r + t : ℝ) : ℂ) * I) (-1 + I) u := by
          have h1 : HasDerivAt (fun t : ℝ => ((r - t : ℝ) : ℂ)) (-1) u := by
            have := ((hasDerivAt_id u).const_sub r).ofReal_comp; simpa using this
          have h2 : HasDerivAt (fun t : ℝ => ((r + t : ℝ) : ℂ) * I) I u := by
            have := ((hasDerivAt_id u).const_add r).ofReal_comp.mul_const I; simpa using this
          exact h1.fun_add h2
        have hc := (hderiv _ hslit').comp u hlin
        simpa [Function.comp_def, mul_comm] using hc)
      (by
        have hi1 : MeasureTheory.IntegrableOn (fun u : ℝ => F (((r - u : ℝ) : ℂ) + ((r + u : ℝ) : ℂ) * I)) (Set.Ioi 0) volume :=
          (integrableOn_hankel_ray hr s 1 (Or.inl rfl)).congr_fun
            (fun u _ => by dsimp only [F]; simp [one_mul]) measurableSet_Ioi
        have hi2 : MeasureTheory.IntegrableOn (fun u : ℝ => s * G (((r - u : ℝ) : ℂ) + ((r + u : ℝ) : ℂ) * I)) (Set.Ioi 0) volume :=
          ((integrableOn_hankel_ray hr (s + 1) 1 (Or.inl rfl)).congr_fun
            (fun u _ => by dsimp only [G]; simp [one_mul]) measurableSet_Ioi).const_mul s
        exact (hi1.sub hi2).const_mul (-1 + I))
      (by simpa using htend_ray 1 (Or.inl rfl))
    rw [MeasureTheory.integral_const_mul] at hftc
    simpa only [sub_zero, add_zero, zero_sub] using hftc
  have hcap : I * (∫ y : ℝ in (-r)..r, (F ((r : ℂ) + (y : ℂ) * I) - s * G ((r : ℂ) + (y : ℂ) * I))) =
      F ((r : ℂ) + (r : ℂ) * I) - F ((r : ℂ) - (r : ℂ) * I) := by
    rw [← intervalIntegral.integral_const_mul]
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => F ((r : ℂ) + (y : ℂ) * I))
      (f' := fun y : ℝ => I * (F ((r : ℂ) + (y : ℂ) * I) - s * G ((r : ℂ) + (y : ℂ) * I)))
      (a := -r) (b := r)
      (fun y _ => by
        have hslit : (r : ℂ) + (y : ℂ) * I ∈ Complex.slitPlane := Or.inl (by simp [hr])
        have hlin : HasDerivAt (fun t : ℝ => (r : ℂ) + (t : ℂ) * I) I y := by
          simpa using (Complex.ofRealCLM.hasDerivAt.mul_const I).const_add (r : ℂ)
        simpa [Function.comp_def, mul_comm] using (hderiv _ hslit).comp y hlin)
      (by
        refine ContinuousOn.intervalIntegrable ?_
        refine continuousOn_const.mul (ContinuousOn.sub ?_ (continuousOn_const.mul ?_))
        · intro y _
          have hslit : (r : ℂ) + (y : ℂ) * I ∈ Complex.slitPlane := Or.inl (by simp [hr])
          have hlin : ContinuousAt (fun t : ℝ => (r : ℂ) + (t : ℂ) * I) y := by fun_prop
          have hlog : ContinuousAt (fun t : ℝ => Complex.log ((r : ℂ) + (t : ℂ) * I)) y :=
            ContinuousAt.comp (g := Complex.log) (Complex.hasDerivAt_log hslit).continuousAt hlin
          have hexp : ContinuousAt (fun t : ℝ => Complex.exp ((r : ℂ) + (t : ℂ) * I)) y :=
            ContinuousAt.comp (g := Complex.exp) Complex.continuous_exp.continuousAt hlin
          exact (((hlog.const_mul (-s)).cexp).mul hexp).continuousWithinAt
        · intro y _
          have hslit : (r : ℂ) + (y : ℂ) * I ∈ Complex.slitPlane := Or.inl (by simp [hr])
          have hlin : ContinuousAt (fun t : ℝ => (r : ℂ) + (t : ℂ) * I) y := by fun_prop
          have hlog : ContinuousAt (fun t : ℝ => Complex.log ((r : ℂ) + (t : ℂ) * I)) y :=
            ContinuousAt.comp (g := Complex.log) (Complex.hasDerivAt_log hslit).continuousAt hlin
          have hexp : ContinuousAt (fun t : ℝ => Complex.exp ((r : ℂ) + (t : ℂ) * I)) y :=
            ContinuousAt.comp (g := Complex.exp) Complex.continuous_exp.continuousAt hlin
          exact (((hlog.const_mul (-(s + 1))).cexp).mul hexp).continuousWithinAt)
    convert hftc using 1
    congr 1; push_cast; ring
  -- Split integrals in `hbot`, `hcap`, `htop` and combine!
  have hi_bot1 : MeasureTheory.IntegrableOn (fun u : ℝ => F (((r - u : ℝ) : ℂ) - ((r + u : ℝ) : ℂ) * I)) (Set.Ioi 0) volume :=
    (integrableOn_hankel_ray hr s (-1) (Or.inr rfl)).congr_fun
      (fun u _ => by dsimp only [F]; congr 2 <;> (push_cast; ring)) measurableSet_Ioi
  have hi_bot2 : MeasureTheory.IntegrableOn (fun u : ℝ => G (((r - u : ℝ) : ℂ) - ((r + u : ℝ) : ℂ) * I)) (Set.Ioi 0) volume :=
    (integrableOn_hankel_ray hr (s + 1) (-1) (Or.inr rfl)).congr_fun
      (fun u _ => by dsimp only [G]; congr 2 <;> (push_cast; ring)) measurableSet_Ioi
  have hi_top1 : MeasureTheory.IntegrableOn (fun u : ℝ => F (((r - u : ℝ) : ℂ) + ((r + u : ℝ) : ℂ) * I)) (Set.Ioi 0) volume :=
    (integrableOn_hankel_ray hr s 1 (Or.inl rfl)).congr_fun
      (fun u _ => by dsimp only [F]; simp [one_mul]) measurableSet_Ioi
  have hi_top2 : MeasureTheory.IntegrableOn (fun u : ℝ => G (((r - u : ℝ) : ℂ) + ((r + u : ℝ) : ℂ) * I)) (Set.Ioi 0) volume :=
    (integrableOn_hankel_ray hr (s + 1) 1 (Or.inl rfl)).congr_fun
      (fun u _ => by dsimp only [G]; simp [one_mul]) measurableSet_Ioi
  have hi_cap1 : IntervalIntegrable (fun y : ℝ => F ((r : ℂ) + (y : ℂ) * I)) volume (-r) r := by
    refine ContinuousOn.intervalIntegrable fun y _ => ?_
    have hslit : (r : ℂ) + (y : ℂ) * I ∈ Complex.slitPlane := Or.inl (by simp [hr])
    have hlin : ContinuousAt (fun t : ℝ => (r : ℂ) + (t : ℂ) * I) y := by fun_prop
    have hlog : ContinuousAt (fun t : ℝ => Complex.log ((r : ℂ) + (t : ℂ) * I)) y :=
      ContinuousAt.comp (g := Complex.log) (Complex.hasDerivAt_log hslit).continuousAt hlin
    have hexp : ContinuousAt (fun t : ℝ => Complex.exp ((r : ℂ) + (t : ℂ) * I)) y :=
      ContinuousAt.comp (g := Complex.exp) Complex.continuous_exp.continuousAt hlin
    exact (((hlog.const_mul (-s)).cexp).mul hexp).continuousWithinAt
  have hi_cap2 : IntervalIntegrable (fun y : ℝ => G ((r : ℂ) + (y : ℂ) * I)) volume (-r) r := by
    refine ContinuousOn.intervalIntegrable fun y _ => ?_
    have hslit : (r : ℂ) + (y : ℂ) * I ∈ Complex.slitPlane := Or.inl (by simp [hr])
    have hlin : ContinuousAt (fun t : ℝ => (r : ℂ) + (t : ℂ) * I) y := by fun_prop
    have hlog : ContinuousAt (fun t : ℝ => Complex.log ((r : ℂ) + (t : ℂ) * I)) y :=
      ContinuousAt.comp (g := Complex.log) (Complex.hasDerivAt_log hslit).continuousAt hlin
    have hexp : ContinuousAt (fun t : ℝ => Complex.exp ((r : ℂ) + (t : ℂ) * I)) y :=
      ContinuousAt.comp (g := Complex.exp) Complex.continuous_exp.continuousAt hlin
    exact (((hlog.const_mul (-(s + 1))).cexp).mul hexp).continuousWithinAt
  rw [MeasureTheory.integral_sub hi_bot1 (hi_bot2.const_mul s), MeasureTheory.integral_const_mul] at hbot
  rw [MeasureTheory.integral_sub hi_top1 (hi_top2.const_mul s), MeasureTheory.integral_const_mul] at htop
  rw [intervalIntegral.integral_sub hi_cap1 (hi_cap2.const_mul s), intervalIntegral.integral_const_mul] at hcap
  unfold hankelIntegralR
  linear_combination hbot + hcap + htop

/-- Radius independence of the Hankel integral: for any `0 < r ≤ 1` and any `s : ℂ`,
`hankelIntegralR r (ζ ↦ exp(-s * log ζ) * exp ζ) = hankelIntegral (ζ ↦ exp(-s * log ζ) * exp ζ)`. -/
private lemma hankelIntegralR_eq_hankelIntegral {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (s : ℂ) :
    hankelIntegralR r (fun ζ => Complex.exp (-s * Complex.log ζ) * Complex.exp ζ) =
      hankelIntegral (fun ζ => Complex.exp (-s * Complex.log ζ) * Complex.exp ζ) := by
  rcases eq_or_lt_of_le hr1 with rfl | hr_lt1
  · rfl
  let f : ℂ → ℂ := fun ζ => Complex.exp (-s * Complex.log ζ) * Complex.exp ζ
  have hf_diff : DifferentiableOn ℂ f Complex.slitPlane := fun ζ hζ =>
    ((((Complex.hasDerivAt_log hζ).const_mul (-s)).cexp.differentiableAt).mul
      (Complex.differentiable_exp ζ)).differentiableWithinAt
  -- For any cutoff `M ≥ 2`, deform the truncated contour `H_M(r)` to `H_M(1)` using 3 open rectangles in
  -- `{0 < Im}`, `{0 < Re}`, and `{Im < 0}`!
  have htrunc : ∀ M : ℝ, 2 ≤ M →
      ((1 + I) * (∫ u : ℝ in (0 : ℝ)..M, f (((r - u : ℝ) : ℂ) - ((r + u : ℝ) : ℂ) * I)) +
       I * (∫ y : ℝ in (-r)..r, f ((r : ℂ) + (y : ℂ) * I)) +
       (-1 + I) * (∫ u : ℝ in (0 : ℝ)..M, f (((r - u : ℝ) : ℂ) + ((r + u : ℝ) : ℂ) * I))) -
      ((1 + I) * (∫ u : ℝ in (0 : ℝ)..M, f (((1 - u : ℝ) : ℂ) - ((1 + u : ℝ) : ℂ) * I)) +
       I * (∫ y : ℝ in (-1 : ℝ)..(1 : ℝ), f ((1 : ℂ) + (y : ℂ) * I)) +
       (-1 + I) * (∫ u : ℝ in (0 : ℝ)..M, f (((1 - u : ℝ) : ℂ) + ((1 + u : ℝ) : ℂ) * I))) =
      (-1 - I) * (∫ t : ℝ in r..1, f (((t - M : ℝ) : ℂ) + ((t + M : ℝ) : ℂ) * I)) +
      (1 - I) * (∫ t : ℝ in r..1, f (((t - M : ℝ) : ℂ) - ((t + M : ℝ) : ℂ) * I)) := by
    intro M hM
    -- Reusable segment helper inside an open rectangle contained in `Complex.slitPlane`:
    have hseg : ∀ (F : ℂ → ℂ) (a₁ b₁ c₁ d₁ : ℝ)
        (hsub : Set.Ioo a₁ b₁ ×ℂ Set.Ioo c₁ d₁ ⊆ Complex.slitPlane)
        (hF : ∀ z ∈ Set.Ioo a₁ b₁ ×ℂ Set.Ioo c₁ d₁, HasDerivAt F (f z) z)
        (t₁ t₂ : ℝ) (p v : ℂ),
        (∀ t ∈ Set.uIcc t₁ t₂, p + (t : ℂ) * v ∈ Set.Ioo a₁ b₁ ×ℂ Set.Ioo c₁ d₁) →
        v * (∫ t : ℝ in t₁..t₂, f (p + (t : ℂ) * v)) = F (p + (t₂ : ℂ) * v) - F (p + (t₁ : ℂ) * v) := by
      intro F a₁ b₁ c₁ d₁ hsub hF t₁ t₂ p v hmem
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t : ℝ => F (p + (t : ℂ) * v)) (fun t ht => ?_) ?_
      · have hlin : HasDerivAt (fun w : ℝ => p + (w : ℂ) * v) v t := by
          simpa using (Complex.ofRealCLM.hasDerivAt.mul_const v).const_add p
        simpa [Function.comp_def, mul_comm] using (hF _ (hmem t ht)).comp t hlin
      · refine ContinuousOn.intervalIntegrable ?_
        exact continuousOn_const.mul (hf_diff.continuousOn.comp
          (by fun_prop : Continuous fun t : ℝ => p + (t : ℂ) * v).continuousOn fun t ht => hsub (hmem t ht))
    -- Piece 1: Right trapezoid in `{0 < Re}` connecting `r ± ir` and `1 ± i` along `t ± it` (`t ∈ [r, 1]`):
    have hsub_R : Set.Ioo (r / 2) 2 ×ℂ Set.Ioo (-2) 2 ⊆ Complex.slitPlane :=
      fun ζ hζ => Or.inl (by linarith [hζ.1.1])
    obtain ⟨F_R, hF_R⟩ := exists_primitive_on_openRect (g := f) (a := r / 2) (b := 2) (c := -2) (d := 2)
      (by linarith) (by norm_num) (hf_diff.mono hsub_R)
    have hpiece_R : I * (∫ y : ℝ in (-r)..r, f ((r : ℂ) + (y : ℂ) * I)) -
        I * (∫ y : ℝ in (-1 : ℝ)..(1 : ℝ), f ((1 : ℂ) + (y : ℂ) * I)) =
        (1 - I) * (∫ t : ℝ in r..1, f ((t : ℂ) - (t : ℂ) * I)) -
        (1 + I) * (∫ t : ℝ in r..1, f ((t : ℂ) + (t : ℂ) * I)) := by
      have h1 := hseg F_R _ _ _ _ hsub_R hF_R (-r) r (r : ℂ) I (fun y hy => by
        rw [Set.uIcc_of_le (by linarith)] at hy
        simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
          Complex.mul_im, zero_add]
        exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩)
      have h2 := hseg F_R _ _ _ _ hsub_R hF_R (-1) 1 (1 : ℂ) I (fun y hy => by
        rw [Set.uIcc_of_le (by norm_num)] at hy
        simp only [Complex.mem_reProdIm, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
          Complex.one_im, Complex.mul_im, Complex.ofReal_re, zero_add]
        exact ⟨⟨by linarith, by norm_num⟩, ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩)
      have h3 := hseg F_R _ _ _ _ hsub_R hF_R r 1 0 (1 + I) (fun t ht => by
        rw [Set.uIcc_of_le hr1] at ht
        have hrew : (0 : ℂ) + (t : ℂ) * (1 + I) = (t : ℂ) + (t : ℂ) * I := by ring
        rw [hrew]
        simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
          Complex.mul_im, zero_add]
        exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩)
      have h4 := hseg F_R _ _ _ _ hsub_R hF_R r 1 0 (1 - I) (fun t ht => by
        rw [Set.uIcc_of_le hr1] at ht
        have hrew : (0 : ℂ) + (t : ℂ) * (1 - I) = (t : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
        rw [hrew]
        simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
          Complex.mul_im, zero_add]
        exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩)
      have h3' : (1 + I) * (∫ t : ℝ in r..1, f ((t : ℂ) + (t : ℂ) * I)) =
          F_R ((1 : ℂ) + (1 : ℂ) * I) - F_R ((r : ℂ) + (r : ℂ) * I) := by
        simpa [zero_add, mul_add, mul_one] using h3
      have h4' : (1 - I) * (∫ t : ℝ in r..1, f ((t : ℂ) - (t : ℂ) * I)) =
          F_R ((1 : ℂ) + ((-1 : ℝ) : ℂ) * I) - F_R ((r : ℂ) + ((-r : ℝ) : ℂ) * I) := by
        have hf4 : (fun t : ℝ => f ((0 : ℂ) + (t : ℂ) * (1 - I))) = fun t : ℝ => f ((t : ℂ) - (t : ℂ) * I) := by
          funext t; congr 1; ring
        rw [hf4] at h4
        convert h4 using 1
        congr 1 <;> (push_cast; ring)
      rw [h1, h2, h3', h4']
      simp only [Complex.ofReal_one, one_mul]; ring
    -- Piece 2: Top parallelogram in `{0 < Im}` bounded by `H_top(r)`, `H_top(1)`, `t + it`, `(t - M) + i(t + M)`:
    have hsub_T : Set.Ioo (-M - 2) 2 ×ℂ Set.Ioo (r / 2) (M + 2) ⊆ Complex.slitPlane :=
      fun ζ hζ => Or.inr (by linarith [hζ.2.1])
    obtain ⟨F_T, hF_T⟩ := exists_primitive_on_openRect (g := f) (a := -M - 2) (b := 2)
      (c := r / 2) (d := M + 2) (by linarith) (by linarith) (hf_diff.mono hsub_T)
    have hpiece_T : (-1 + I) * (∫ u : ℝ in (0 : ℝ)..M, f (((r - u : ℝ) : ℂ) + ((r + u : ℝ) : ℂ) * I)) -
        (-1 + I) * (∫ u : ℝ in (0 : ℝ)..M, f (((1 - u : ℝ) : ℂ) + ((1 + u : ℝ) : ℂ) * I)) -
        (1 + I) * (∫ t : ℝ in r..1, f ((t : ℂ) + (t : ℂ) * I)) =
        (-1 - I) * (∫ t : ℝ in r..1, f (((t - M : ℝ) : ℂ) + ((t + M : ℝ) : ℂ) * I)) := by
      have h1 := hseg F_T _ _ _ _ hsub_T hF_T 0 M ((r : ℂ) + (r : ℂ) * I) (-1 + I) (fun u hu => by
        rw [Set.uIcc_of_le (by linarith)] at hu
        have hrew : ((r : ℂ) + (r : ℂ) * I) + (u : ℂ) * (-1 + I) = ((r - u : ℝ) : ℂ) + ((r + u : ℝ) : ℂ) * I := by
          push_cast; ring
        rw [hrew]
        simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
          Complex.mul_im, zero_add]
        exact ⟨⟨by linarith [hu.2], by linarith [hu.1]⟩, ⟨by linarith [hu.1], by linarith [hu.2]⟩⟩)
      have h2 := hseg F_T _ _ _ _ hsub_T hF_T 0 M ((1 : ℂ) + (1 : ℂ) * I) (-1 + I) (fun u hu => by
        rw [Set.uIcc_of_le (by linarith)] at hu
        have hrew : ((1 : ℂ) + (1 : ℂ) * I) + (u : ℂ) * (-1 + I) = ((1 - u : ℝ) : ℂ) + ((1 + u : ℝ) : ℂ) * I := by
          push_cast; ring
        rw [hrew]
        simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
          Complex.mul_im, zero_add]
        exact ⟨⟨by linarith [hu.2], by linarith [hu.1]⟩, ⟨by linarith [hu.1], by linarith [hu.2]⟩⟩)
      have h3 := hseg F_T _ _ _ _ hsub_T hF_T r 1 0 (1 + I) (fun t ht => by
        rw [Set.uIcc_of_le hr1] at ht
        have hrew : (0 : ℂ) + (t : ℂ) * (1 + I) = (t : ℂ) + (t : ℂ) * I := by ring
        rw [hrew]
        simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
          Complex.mul_im, zero_add]
        exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩)
      have h4 := hseg F_T _ _ _ _ hsub_T hF_T r 1 ((-M : ℂ) + (M : ℂ) * I) (1 + I) (fun t ht => by
        rw [Set.uIcc_of_le hr1] at ht
        have hrew : ((-M : ℂ) + (M : ℂ) * I) + (t : ℂ) * (1 + I) = ((t - M : ℝ) : ℂ) + ((t + M : ℝ) : ℂ) * I := by
          push_cast; ring
        rw [hrew]
        simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
          Complex.mul_im, zero_add]
        exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩)
      have h1' : (-1 + I) * (∫ u : ℝ in (0 : ℝ)..M, f (((r - u : ℝ) : ℂ) + ((r + u : ℝ) : ℂ) * I)) =
          F_T (((r - M : ℝ) : ℂ) + ((r + M : ℝ) : ℂ) * I) - F_T ((r : ℂ) + (r : ℂ) * I) := by
        have hfn : (fun u : ℝ => f (((r : ℂ) + (r : ℂ) * I) + (u : ℂ) * (-1 + I))) =
            fun u : ℝ => f (((r - u : ℝ) : ℂ) + ((r + u : ℝ) : ℂ) * I) := by funext u; congr 1; push_cast; ring
        rw [hfn] at h1; convert h1 using 1; congr 1 <;> (push_cast; ring)
      have h2' : (-1 + I) * (∫ u : ℝ in (0 : ℝ)..M, f (((1 - u : ℝ) : ℂ) + ((1 + u : ℝ) : ℂ) * I)) =
          F_T (((1 - M : ℝ) : ℂ) + ((1 + M : ℝ) : ℂ) * I) - F_T ((1 : ℂ) + (1 : ℂ) * I) := by
        have hfn : (fun u : ℝ => f (((1 : ℂ) + (1 : ℂ) * I) + (u : ℂ) * (-1 + I))) =
            fun u : ℝ => f (((1 - u : ℝ) : ℂ) + ((1 + u : ℝ) : ℂ) * I) := by funext u; congr 1; push_cast; ring
        rw [hfn] at h2; convert h2 using 1; congr 1 <;> (push_cast; ring)
      have h3' : (1 + I) * (∫ t : ℝ in r..1, f ((t : ℂ) + (t : ℂ) * I)) =
          F_T ((1 : ℂ) + (1 : ℂ) * I) - F_T ((r : ℂ) + (r : ℂ) * I) := by
        simpa [zero_add, mul_add, mul_one] using h3
      have h4' : (1 + I) * (∫ t : ℝ in r..1, f (((t - M : ℝ) : ℂ) + ((t + M : ℝ) : ℂ) * I)) =
          F_T (((1 - M : ℝ) : ℂ) + ((1 + M : ℝ) : ℂ) * I) - F_T (((r - M : ℝ) : ℂ) + ((r + M : ℝ) : ℂ) * I) := by
        have hfn : (fun t : ℝ => f (((-M : ℂ) + (M : ℂ) * I) + (t : ℂ) * (1 + I))) =
            fun t : ℝ => f (((t - M : ℝ) : ℂ) + ((t + M : ℝ) : ℂ) * I) := by funext t; congr 1; push_cast; ring
        rw [hfn] at h4; convert h4 using 1; congr 1 <;> (push_cast; ring)
      rw [h1', h2', h3']; linear_combination h4'
    -- Piece 3: Bottom parallelogram in `{Im < 0}` bounded by `H_bot(r)`, `H_bot(1)`, `t - it`, `(t - M) - i(t + M)`:
    have hsub_B : Set.Ioo (-M - 2) 2 ×ℂ Set.Ioo (-(M + 2)) (-(r / 2)) ⊆ Complex.slitPlane :=
      fun ζ hζ => Or.inr (by linarith [hζ.2.2])
    obtain ⟨F_B, hF_B⟩ := exists_primitive_on_openRect (g := f) (a := -M - 2) (b := 2)
      (c := -(M + 2)) (d := -(r / 2)) (by linarith) (by linarith) (hf_diff.mono hsub_B)
    have hpiece_B : (1 + I) * (∫ u : ℝ in (0 : ℝ)..M, f (((r - u : ℝ) : ℂ) - ((r + u : ℝ) : ℂ) * I)) -
        (1 + I) * (∫ u : ℝ in (0 : ℝ)..M, f (((1 - u : ℝ) : ℂ) - ((1 + u : ℝ) : ℂ) * I)) +
        (1 - I) * (∫ t : ℝ in r..1, f ((t : ℂ) - (t : ℂ) * I)) =
        (1 - I) * (∫ t : ℝ in r..1, f (((t - M : ℝ) : ℂ) - ((t + M : ℝ) : ℂ) * I)) := by
      have h1 := hseg F_B _ _ _ _ hsub_B hF_B 0 M ((r : ℂ) - (r : ℂ) * I) (-1 - I) (fun u hu => by
        rw [Set.uIcc_of_le (by linarith)] at hu
        have hrew : ((r : ℂ) - (r : ℂ) * I) + (u : ℂ) * (-1 - I) = ((r - u : ℝ) : ℂ) + ((-(r + u) : ℝ) : ℂ) * I := by
          push_cast; ring
        rw [hrew]
        simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
          Complex.mul_im, zero_add]
        exact ⟨⟨by linarith [hu.2], by linarith [hu.1]⟩, ⟨by linarith [hu.2], by linarith [hu.1]⟩⟩)
      have h2 := hseg F_B _ _ _ _ hsub_B hF_B 0 M ((1 : ℂ) - (1 : ℂ) * I) (-1 - I) (fun u hu => by
        rw [Set.uIcc_of_le (by linarith)] at hu
        have hrew : ((1 : ℂ) - (1 : ℂ) * I) + (u : ℂ) * (-1 - I) = ((1 - u : ℝ) : ℂ) + ((-(1 + u) : ℝ) : ℂ) * I := by
          push_cast; ring
        rw [hrew]
        simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
          Complex.mul_im, zero_add]
        exact ⟨⟨by linarith [hu.2], by linarith [hu.1]⟩, ⟨by linarith [hu.2], by linarith [hu.1]⟩⟩)
      have h3 := hseg F_B _ _ _ _ hsub_B hF_B r 1 0 (1 - I) (fun t ht => by
        rw [Set.uIcc_of_le hr1] at ht
        have hrew : (0 : ℂ) + (t : ℂ) * (1 - I) = (t : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
        rw [hrew]
        simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
          Complex.mul_im, zero_add]
        exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩)
      have h4 := hseg F_B _ _ _ _ hsub_B hF_B r 1 ((-M : ℂ) - (M : ℂ) * I) (1 - I) (fun t ht => by
        rw [Set.uIcc_of_le hr1] at ht
        have hrew : ((-M : ℂ) - (M : ℂ) * I) + (t : ℂ) * (1 - I) = ((t - M : ℝ) : ℂ) + ((-(t + M) : ℝ) : ℂ) * I := by
          push_cast; ring
        rw [hrew]
        simp only [Complex.mem_reProdIm, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.add_im,
          Complex.mul_im, zero_add]
        exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩)
      have h1' : (-1 - I) * (∫ u : ℝ in (0 : ℝ)..M, f (((r - u : ℝ) : ℂ) - ((r + u : ℝ) : ℂ) * I)) =
          F_B (((r - M : ℝ) : ℂ) - ((r + M : ℝ) : ℂ) * I) - F_B ((r : ℂ) - (r : ℂ) * I) := by
        have hfn : (fun u : ℝ => f (((r : ℂ) - (r : ℂ) * I) + (u : ℂ) * (-1 - I))) =
            fun u : ℝ => f (((r - u : ℝ) : ℂ) - ((r + u : ℝ) : ℂ) * I) := by funext u; congr 1; push_cast; ring
        rw [hfn] at h1; convert h1 using 1; congr 1 <;> (push_cast; ring)
      have h2' : (-1 - I) * (∫ u : ℝ in (0 : ℝ)..M, f (((1 - u : ℝ) : ℂ) - ((1 + u : ℝ) : ℂ) * I)) =
          F_B (((1 - M : ℝ) : ℂ) - ((1 + M : ℝ) : ℂ) * I) - F_B ((1 : ℂ) - (1 : ℂ) * I) := by
        have hfn : (fun u : ℝ => f (((1 : ℂ) - (1 : ℂ) * I) + (u : ℂ) * (-1 - I))) =
            fun u : ℝ => f (((1 - u : ℝ) : ℂ) - ((1 + u : ℝ) : ℂ) * I) := by funext u; congr 1; push_cast; ring
        rw [hfn] at h2; convert h2 using 1; congr 1 <;> (push_cast; ring)
      have h3' : (1 - I) * (∫ t : ℝ in r..1, f ((t : ℂ) - (t : ℂ) * I)) =
          F_B ((1 : ℂ) - (1 : ℂ) * I) - F_B ((r : ℂ) - (r : ℂ) * I) := by
        have hfn : (fun t : ℝ => f ((0 : ℂ) + (t : ℂ) * (1 - I))) = fun t : ℝ => f ((t : ℂ) - (t : ℂ) * I) := by
          funext t; congr 1; ring
        rw [hfn] at h3; convert h3 using 1; congr 1 <;> (push_cast; ring)
      have h4' : (1 - I) * (∫ t : ℝ in r..1, f (((t - M : ℝ) : ℂ) - ((t + M : ℝ) : ℂ) * I)) =
          F_B (((1 - M : ℝ) : ℂ) - ((1 + M : ℝ) : ℂ) * I) - F_B (((r - M : ℝ) : ℂ) - ((r + M : ℝ) : ℂ) * I) := by
        have hfn : (fun t : ℝ => f (((-M : ℂ) - (M : ℂ) * I) + (t : ℂ) * (1 - I))) =
            fun t : ℝ => f (((t - M : ℝ) : ℂ) - ((t + M : ℝ) : ℂ) * I) := by funext t; congr 1; push_cast; ring
        rw [hfn] at h4; convert h4 using 1; congr 1 <;> (push_cast; ring)
      rw [h3', h4']; linear_combination -h1' + h2'
    linear_combination hpiece_R + hpiece_T + hpiece_B
  -- Send `M → ∞`: LHS tends to `hankelIntegralR r f - hankelIntegral f`, RHS tends to `0`!
  have htend_tail : ∀ sgn : ℝ, sgn = 1 ∨ sgn = -1 →
      Filter.Tendsto (fun M : ℝ => ∫ t : ℝ in r..1, f (((t - M : ℝ) : ℂ) + ((sgn * (t + M) : ℝ) : ℂ) * I))
        atTop (𝓝 0) := by
    intro sgn hsgn
    rw [tendsto_zero_iff_norm_tendsto_zero]
    let N : ℕ := Nat.ceil |s.re|
    let C : ℝ := (2 : ℝ) ^ N * (max 1 r⁻¹) ^ |s.re| * Real.exp (Real.pi * |s.im|) * Real.exp 1
    have hbd : ∀ᶠ M : ℝ in atTop,
        ‖∫ t : ℝ in r..1, f (((t - M : ℝ) : ℂ) + ((sgn * (t + M) : ℝ) : ℂ) * I)‖ ≤
          (C * ((N + 1).factorial : ℝ) * Real.exp 1) / (1 + M) := by
      filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with M hM
      have hpt : ∀ t ∈ Set.uIoc r 1,
          ‖f (((t - M : ℝ) : ℂ) + ((sgn * (t + M) : ℝ) : ℂ) * I)‖ ≤
            (C * ((N + 1).factorial : ℝ) * Real.exp 1) / (1 + M) := fun t ht => by
        rw [Set.uIoc_of_le hr1] at ht
        obtain ⟨_, hne, hlb, hub, _⟩ := hankel_ray_props (lt_trans hr0 ht.1) (by linarith : 0 ≤ M) sgn hsgn
        let ζ : ℂ := ((t - M : ℝ) : ℂ) + ((sgn * (t + M) : ℝ) : ℂ) * I
        have hre : ζ.re = t - M := by dsimp only [ζ]; simp
        have h1 := norm_exp_neg_mul_log_le s ζ hne
        have hmax1 : (max 1 ‖ζ‖) ^ |s.re| ≤ (2 : ℝ) ^ N * (1 + M) ^ N := by
          have hle : max 1 ‖ζ‖ ≤ 2 * (1 + M) := by
            refine max_le (by linarith) ?_
            calc ‖ζ‖ ≤ 2 * (t + M) := hub
              _ ≤ 2 * (1 + M) := by linarith [ht.2]
          calc (max 1 ‖ζ‖) ^ |s.re| ≤ (2 * (1 + M)) ^ |s.re| :=
                Real.rpow_le_rpow (by positivity) hle (abs_nonneg _)
            _ ≤ (2 * (1 + M)) ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil _)
            _ = (2 : ℝ) ^ N * (1 + M) ^ N := by rw [Real.rpow_natCast, mul_pow]
        have hmax2 : (max 1 ‖ζ‖⁻¹) ^ |s.re| ≤ (max 1 r⁻¹) ^ |s.re| :=
          Real.rpow_le_rpow (by positivity) (max_le_max_left 1 (inv_anti₀ hr0 (by linarith [ht.1]))) (abs_nonneg _)
        have hexp_M : (1 + M) ^ N * Real.exp (-M) ≤ ((N + 1).factorial : ℝ) * Real.exp 1 / (1 + M) := by
          rw [le_div_iff₀ (by linarith : 0 < 1 + M)]
          have h1' : (1 + M) ^ (N + 1) ≤ Real.exp (1 + M) * ((N + 1).factorial : ℝ) :=
            (div_le_iff₀ (by positivity)).mp (Real.pow_div_factorial_le_exp (1 + M) (by linarith) (N + 1))
          calc (1 + M) ^ N * Real.exp (-M) * (1 + M)
              = (1 + M) ^ (N + 1) * Real.exp (-M) := by rw [pow_succ]; ring
            _ ≤ (Real.exp (1 + M) * ((N + 1).factorial : ℝ)) * Real.exp (-M) :=
                mul_le_mul_of_nonneg_right h1' (Real.exp_pos _).le
            _ = ((N + 1).factorial : ℝ) * (Real.exp (1 + M) * Real.exp (-M)) := by ring
            _ = ((N + 1).factorial : ℝ) * Real.exp 1 := by rw [← Real.exp_add]; congr 2; ring
        change ‖Complex.exp (-s * Complex.log ζ) * Complex.exp ζ‖ ≤ _
        rw [norm_mul, Complex.norm_exp ζ, hre]
        calc ‖Complex.exp (-s * Complex.log ζ)‖ * Real.exp (t - M)
            ≤ ((max 1 ‖ζ‖) ^ |s.re| * (max 1 ‖ζ‖⁻¹) ^ |s.re| * Real.exp (Real.pi * |s.im|)) *
                (Real.exp 1 * Real.exp (-M)) := by
              refine mul_le_mul h1 ?_ (Real.exp_pos _).le (by positivity)
              rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [ht.2])
          _ ≤ (((2 : ℝ) ^ N * (1 + M) ^ N) * (max 1 r⁻¹) ^ |s.re| * Real.exp (Real.pi * |s.im|)) *
                (Real.exp 1 * Real.exp (-M)) := by gcongr
          _ = C * ((1 + M) ^ N * Real.exp (-M)) := by dsimp only [C]; ring
          _ ≤ C * (((N + 1).factorial : ℝ) * Real.exp 1 / (1 + M)) :=
              mul_le_mul_of_nonneg_left hexp_M (by dsimp only [C]; positivity)
          _ = (C * ((N + 1).factorial : ℝ) * Real.exp 1) / (1 + M) := by ring
      calc ‖∫ t : ℝ in r..1, f (((t - M : ℝ) : ℂ) + ((sgn * (t + M) : ℝ) : ℂ) * I)‖
          ≤ ((C * ((N + 1).factorial : ℝ) * Real.exp 1) / (1 + M)) * |1 - r| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hpt
        _ ≤ ((C * ((N + 1).factorial : ℝ) * Real.exp 1) / (1 + M)) * 1 := by
            have habs : |1 - r| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
            exact mul_le_mul_of_nonneg_left habs (by dsimp only [C]; positivity)
        _ = (C * ((N + 1).factorial : ℝ) * Real.exp 1) / (1 + M) := mul_one _
    exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbd
      (tendsto_const_nhds.div_atTop (Filter.tendsto_atTop_mono (fun u : ℝ => le_add_of_nonneg_left zero_le_one) tendsto_id))
  have htend_rhs : Filter.Tendsto (fun M : ℝ =>
      (-1 - I) * (∫ t : ℝ in r..1, f (((t - M : ℝ) : ℂ) + ((t + M : ℝ) : ℂ) * I)) +
      (1 - I) * (∫ t : ℝ in r..1, f (((t - M : ℝ) : ℂ) - ((t + M : ℝ) : ℂ) * I))) atTop (𝓝 0) := by
    have h1 := (htend_tail 1 (Or.inl rfl)).const_mul (-1 - I)
    have h2 := (htend_tail (-1) (Or.inr rfl)).const_mul (1 - I)
    have h2_0 : Filter.Tendsto (fun M : ℝ => (1 - I) * ∫ t : ℝ in r..1, f (((t - M : ℝ) : ℂ) + ((-1 * (t + M) : ℝ) : ℂ) * I))
        atTop (𝓝 0) := by simpa only [mul_zero] using h2
    have h2' : Filter.Tendsto (fun M : ℝ => (1 - I) * ∫ t : ℝ in r..1, f (((t - M : ℝ) : ℂ) - ((t + M : ℝ) : ℂ) * I))
        atTop (𝓝 0) := by
      refine h2_0.congr fun M => ?_
      congr 1; refine intervalIntegral.integral_congr fun t _ => ?_; congr 1; push_cast; ring
    simpa [one_mul] using h1.add h2'
  have htend_lhs : Filter.Tendsto (fun M : ℝ =>
      ((1 + I) * (∫ u : ℝ in (0 : ℝ)..M, f (((r - u : ℝ) : ℂ) - ((r + u : ℝ) : ℂ) * I)) +
       I * (∫ y : ℝ in (-r)..r, f ((r : ℂ) + (y : ℂ) * I)) +
       (-1 + I) * (∫ u : ℝ in (0 : ℝ)..M, f (((r - u : ℝ) : ℂ) + ((r + u : ℝ) : ℂ) * I))) -
      ((1 + I) * (∫ u : ℝ in (0 : ℝ)..M, f (((1 - u : ℝ) : ℂ) - ((1 + u : ℝ) : ℂ) * I)) +
       I * (∫ y : ℝ in (-1 : ℝ)..(1 : ℝ), f ((1 : ℂ) + (y : ℂ) * I)) +
       (-1 + I) * (∫ u : ℝ in (0 : ℝ)..M, f (((1 - u : ℝ) : ℂ) + ((1 + u : ℝ) : ℂ) * I))))
      atTop (𝓝 (hankelIntegralR r f - hankelIntegral f)) := by
    have ht_ray : ∀ (r' : ℝ) (hr' : 0 < r') (sgn : ℝ) (hsgn : sgn = 1 ∨ sgn = -1),
        Filter.Tendsto (fun M : ℝ => ∫ u : ℝ in (0 : ℝ)..M, f (((r' - u : ℝ) : ℂ) + ((sgn * (r' + u) : ℝ) : ℂ) * I))
          atTop (𝓝 (∫ u in Set.Ioi (0 : ℝ), f (((r' - u : ℝ) : ℂ) + ((sgn * (r' + u) : ℝ) : ℂ) * I))) :=
      fun r' hr' sgn hsgn => MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
        (integrableOn_hankel_ray hr' s sgn hsgn) tendsto_id
    have hr_bot := (ht_ray r hr0 (-1) (Or.inr rfl)).const_mul (1 + I)
    have hr_top := (ht_ray r hr0 1 (Or.inl rfl)).const_mul (-1 + I)
    have h1_bot := (ht_ray 1 zero_lt_one (-1) (Or.inr rfl)).const_mul (1 + I)
    have h1_top := (ht_ray 1 zero_lt_one 1 (Or.inl rfl)).const_mul (-1 + I)
    have hcongr_neg : ∀ (r' : ℝ) (u : ℝ), ((r' - u : ℝ) : ℂ) + ((-1 * (r' + u) : ℝ) : ℂ) * I =
        ((r' - u : ℝ) : ℂ) - ((r' + u : ℝ) : ℂ) * I := fun r' u => by push_cast; ring
    simp_rw [hcongr_neg] at hr_bot h1_bot
    simp only [one_mul] at hr_top h1_top
    exact ((hr_bot.add tendsto_const_nhds).add hr_top).sub ((h1_bot.add tendsto_const_nhds).add h1_top)
  have hsub0 : hankelIntegralR r f - hankelIntegral f = 0 :=
    tendsto_nhds_unique htend_lhs (htend_rhs.congr' (by
      filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with M hM
      exact (htrunc M hM).symm))
  exact sub_eq_zero.mp hsub0

/-- Analytic Laplace integral of `u^{-s}` on `{0 < w.re}` for `0 < s.re < 1`:
`∫_0^∞ exp(-s * log u) * exp(-w * u) du = exp(-(1 - s) * log w) * Γ(1 - s)`. -/
private lemma laplace_rpow_eq_Gamma {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) {w : ℂ} (hw : 0 < w.re) :
    (∫ u in Set.Ioi (0 : ℝ), Complex.exp (-s * Complex.log (u : ℂ)) * Complex.exp (-w * (u : ℂ))) =
      Complex.exp (-(1 - s) * Complex.log w) * Complex.Gamma (1 - s) := by
  -- Helper: integrability of `u ↦ u ^ (-s.re) * exp(-c * u)` on `Ioi 0` for any `c > 0`.
  have hint_dom : ∀ c : ℝ, 0 < c →
      MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (-s.re) * Real.exp (-c * u)) (Set.Ioi 0) volume := by
    intro c hc
    have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
    rw [hsplit]
    refine MeasureTheory.IntegrableOn.union ?_ ?_
    · have hrpow : MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (-s.re)) (Set.Ioc 0 1) volume :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
          (intervalIntegral.intervalIntegrable_rpow' (by linarith))
      refine hrpow.mono' (by
        have hcont : ContinuousOn (fun u : ℝ => u ^ (-s.re) * Real.exp (-c * u)) (Set.Ioc 0 1) :=
          (ContinuousOn.rpow_const continuousOn_id fun u (hu : u ∈ Set.Ioc 0 1) => Or.inl (ne_of_gt hu.1)).mul (by fun_prop)
        exact hcont.aestronglyMeasurable measurableSet_Ioc) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
      have hu_nn : 0 ≤ u ^ (-s.re) := Real.rpow_nonneg hu.1.le _
      rw [Real.norm_of_nonneg (mul_nonneg hu_nn (Real.exp_pos _).le)]
      exact mul_le_of_le_one_right hu_nn (Real.exp_le_one_iff.mpr (by nlinarith [hu.1]))
    · have hexp : MeasureTheory.IntegrableOn (fun u : ℝ => Real.exp (-c * u)) (Set.Ioi 1) volume :=
        integrableOn_exp_mul_Ioi (by linarith) 1
      refine hexp.mono' (by
        have hcont : ContinuousOn (fun u : ℝ => u ^ (-s.re) * Real.exp (-c * u)) (Set.Ioi 1) :=
          (ContinuousOn.rpow_const continuousOn_id fun u (hu : u ∈ Set.Ioi 1) =>
            Or.inl (ne_of_gt (lt_trans zero_lt_one hu))).mul (by fun_prop)
        exact hcont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      have hu1 : 1 < u := hu
      have hu_nn : 0 ≤ u ^ (-s.re) := Real.rpow_nonneg (by linarith) _
      rw [Real.norm_of_nonneg (mul_nonneg hu_nn (Real.exp_pos _).le)]
      have hle1 : u ^ (-s.re) ≤ 1 := by
        rw [Real.rpow_neg (by linarith)]
        exact inv_le_one_of_one_le₀ (Real.one_le_rpow hu1.le hs0.le)
      exact mul_le_of_le_one_left (Real.exp_pos _).le hle1
  -- Step 1: Prove the identity for real `x > 0` by change of variables `t = x * u` in `Complex.Gamma_eq_integral`.
  have hreal : ∀ x : ℝ, 0 < x →
      (∫ u in Set.Ioi (0 : ℝ), Complex.exp (-s * Complex.log (u : ℂ)) * Complex.exp (-(x : ℂ) * (u : ℂ))) =
        Complex.exp (-(1 - s) * Complex.log (x : ℂ)) * Complex.Gamma (1 - s) := by
    intro x hx
    have hGamma : Complex.Gamma (1 - s) =
        ∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ ((1 - s) - 1) := by
      rw [Complex.Gamma_eq_integral (by simp [hs1])]; rfl
    have himg : (fun u : ℝ => x * u) '' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
      ext t; simp only [Set.mem_image, Set.mem_Ioi]
      exact ⟨fun ⟨u, hu, h⟩ => h ▸ mul_pos hx hu, fun ht => ⟨t / x, div_pos ht hx, mul_div_cancel₀ t hx.ne'⟩⟩
    have hchg := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Set.Ioi (0 : ℝ)) (f := fun u : ℝ => x * u) (f' := fun _ => x)
      measurableSet_Ioi
      (fun u _ => by simpa using ((hasDerivAt_id u).const_mul x).hasDerivWithinAt)
      (fun u₁ _ u₂ _ h => mul_left_cancel₀ hx.ne' h)
      (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ) * (t : ℂ) ^ ((1 - s) - 1))
    rw [himg, ← hGamma] at hchg
    rw [hchg, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu_pos : 0 < u := hu
    rw [abs_of_pos hx, Complex.real_smul, Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (mul_pos hx hu_pos).ne')]
    have hlog_mul : Complex.log ((x * u : ℝ) : ℂ) = Complex.log (x : ℂ) + Complex.log (u : ℂ) := by
      rw [← Complex.ofReal_log (mul_pos hx hu_pos).le, ← Complex.ofReal_log hx.le, ← Complex.ofReal_log hu_pos.le,
        Real.log_mul hx.ne' hu_pos.ne', Complex.ofReal_add]
    have hexp_x : Complex.exp (-(1 - s) * Complex.log (x : ℂ)) * (x : ℂ) =
        Complex.exp (s * Complex.log (x : ℂ)) := by
      have hx_eq : (x : ℂ) = Complex.exp (Complex.log (x : ℂ)) :=
        (Complex.exp_log (Complex.ofReal_ne_zero.mpr hx.ne')).symm
      conv_lhs => arg 2; rw [hx_eq]
      rw [← Complex.exp_add]; congr 1; ring
    have hexp_all : Complex.exp (-(1 - s) * Complex.log (x : ℂ)) *
        ((x : ℂ) * (((Real.exp (-(x * u)) : ℝ) : ℂ) * Complex.exp (Complex.log ((x * u : ℝ) : ℂ) * (1 - s - 1)))) =
        Complex.exp (-s * Complex.log (u : ℂ)) * Complex.exp (-(x : ℂ) * (u : ℂ)) := by
      rw [← mul_assoc, hexp_x, hlog_mul, Complex.ofReal_exp,
        mul_left_comm (Complex.exp (s * Complex.log (x : ℂ))), ← Complex.exp_add]
      rw [mul_comm (Complex.exp ((-(x * u) : ℝ) : ℂ))]
      congr 1
      · congr 1; ring
      · push_cast; ring
    exact hexp_all.symm
  -- Step 2: Show the LHS is holomorphic on `{0 < w.re}` via `hasDerivAt_integral_of_dominated_loc_of_deriv_le`!
  let RHP : Set ℂ := {z : ℂ | 0 < z.re}
  have hRHP_open : IsOpen RHP := isOpen_lt continuous_const Complex.continuous_re
  have hRHP_conv : Convex ℝ RHP := by
    intro x hx y hy a b ha hb hab
    simp only [RHP, Set.mem_ofPred_eq, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hx hy ⊢
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1; simp [hy]
    · rcases eq_or_lt_of_le hb with rfl | hb'
      · have ha1 : a = 1 := by linarith
        subst ha1; simp [hx]
      · linarith [mul_pos ha' hx, mul_pos hb' hy]
  have hlhs_diff : DifferentiableOn ℂ
      (fun z : ℂ => ∫ u in Set.Ioi (0 : ℝ), Complex.exp (-s * Complex.log (u : ℂ)) * Complex.exp (-z * (u : ℂ))) RHP := by
    intro w₀ hw₀
    change 0 < w₀.re at hw₀
    let δ : ℝ := w₀.re / 2
    have hδ : 0 < δ := half_pos hw₀
    let B : Set ℂ := Metric.ball w₀ δ
    have hB_mem : B ∈ 𝓝 w₀ := Metric.ball_mem_nhds w₀ hδ
    have hre_B : ∀ z ∈ B, δ ≤ z.re := fun z hz => by
      have hdist : ‖z - w₀‖ < δ := by simpa [B, Metric.mem_ball, dist_eq_norm] using hz
      have h1 : |z.re - w₀.re| ≤ ‖z - w₀‖ := by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm (z - w₀)
      have h2 := (abs_lt.mp (lt_of_le_of_lt h1 hdist)).1
      dsimp only [δ] at h2 ⊢; linarith
    have hmeas : ∀ z : ℂ, MeasureTheory.AEStronglyMeasurable
        (fun u : ℝ => Complex.exp (-s * Complex.log (u : ℂ)) * Complex.exp (-z * (u : ℂ)))
        (volume.restrict (Set.Ioi 0)) := fun z => by
      have hcont : ContinuousOn (fun u : ℝ => Complex.exp (-s * Complex.log (u : ℂ)) * Complex.exp (-z * (u : ℂ)))
          (Set.Ioi 0) := by
        intro u hu
        have hslit : (u : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using hu)
        exact (((((Complex.hasDerivAt_log hslit).continuousAt).comp Complex.continuous_ofReal.continuousAt).const_mul (-s)).cexp.mul
          (by fun_prop : Continuous fun t : ℝ => Complex.exp (-z * (t : ℂ))).continuousAt).continuousWithinAt
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    have hmeas' : MeasureTheory.AEStronglyMeasurable
        (fun u : ℝ => -(u : ℂ) * Complex.exp (-s * Complex.log (u : ℂ)) * Complex.exp (-w₀ * (u : ℂ)))
        (volume.restrict (Set.Ioi 0)) := by
      have hcont : ContinuousOn (fun u : ℝ => -(u : ℂ) * Complex.exp (-s * Complex.log (u : ℂ)) * Complex.exp (-w₀ * (u : ℂ)))
          (Set.Ioi 0) := by
        intro u hu
        have hslit : (u : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using hu)
        exact ((continuous_neg.comp Complex.continuous_ofReal).continuousAt.mul
          (((((Complex.hasDerivAt_log hslit).continuousAt).comp Complex.continuous_ofReal.continuousAt).const_mul (-s)).cexp) |>.mul
          (by fun_prop : Continuous fun t : ℝ => Complex.exp (-w₀ * (t : ℂ))).continuousAt).continuousWithinAt
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    have hnorm_u : ∀ (z : ℂ) (u : ℝ), 0 < u →
        ‖Complex.exp (-s * Complex.log (u : ℂ)) * Complex.exp (-z * (u : ℂ))‖ =
          u ^ (-s.re) * Real.exp (-z.re * u) := fun z u hu => by
      rw [norm_mul, Complex.norm_exp, Complex.norm_exp, ← Complex.ofReal_log hu.le]
      have h1 : (-s * ((Real.log u : ℝ) : ℂ)).re = -s.re * Real.log u := by
        simp [Complex.mul_re]
      have h2 : (-z * (u : ℂ)).re = -z.re * u := by simp [Complex.mul_re]
      rw [h1, h2, Real.rpow_def_of_pos hu, mul_comm (Real.log u)]
    have hint0 : MeasureTheory.Integrable
        (fun u : ℝ => Complex.exp (-s * Complex.log (u : ℂ)) * Complex.exp (-w₀ * (u : ℂ)))
        (volume.restrict (Set.Ioi 0)) := by
      refine (hint_dom w₀.re hw₀).mono' (hmeas w₀) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      rw [hnorm_u w₀ u hu]
    have hbound_int : MeasureTheory.Integrable
        (fun u : ℝ => (1 + u) ^ 1 * Real.exp (-δ * u)) (volume.restrict (Set.Ioi 0)) :=
      integrableOn_one_add_pow_mul_exp_neg 1 hδ
    have hd_int := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (F := fun z u => Complex.exp (-s * Complex.log (u : ℂ)) * Complex.exp (-z * (u : ℂ)))
      (F' := fun z u => -(u : ℂ) * Complex.exp (-s * Complex.log (u : ℂ)) * Complex.exp (-z * (u : ℂ)))
      (bound := fun u : ℝ => (1 + u) ^ 1 * Real.exp (-δ * u))
      hB_mem (Filter.Eventually.of_forall hmeas) hint0 hmeas'
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu z hz
        have hu_pos : 0 < u := hu
        rw [mul_assoc, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hu_pos.le, hnorm_u z u hu_pos,
          ← mul_assoc]
        have hu_pow : u * u ^ (-s.re) ≤ (1 + u) ^ 1 := by
          rw [pow_one, show u * u ^ (-s.re) = u ^ (1 - s.re) from (by
            rw [sub_eq_add_neg, Real.rpow_add hu_pos, Real.rpow_one])]
          rcases le_total u 1 with hu1 | hu1
          · exact (Real.rpow_le_one hu_pos.le hu1 (by linarith)).trans (by linarith)
          · exact (Real.rpow_le_rpow_of_exponent_le hu1 (by linarith : 1 - s.re ≤ 1)).trans (by rw [Real.rpow_one]; linarith)
        have hexp_le : Real.exp (-z.re * u) ≤ Real.exp (-δ * u) :=
          Real.exp_le_exp.mpr (by nlinarith [hre_B z hz])
        exact mul_le_mul hu_pow hexp_le (Real.exp_pos _).le (by positivity))
      hbound_int
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u _ z _
        have hd1 : HasDerivAt (fun w : ℂ => Complex.exp (-w * (u : ℂ)))
            (Complex.exp (-z * (u : ℂ)) * (-(u : ℂ))) z := by
          have := ((hasDerivAt_id z).neg.mul_const (u : ℂ)).cexp
          simpa using this
        have hd2 := hd1.const_mul (Complex.exp (-s * Complex.log (u : ℂ)))
        convert hd2 using 1; ring)
    exact hd_int.2.differentiableAt.differentiableWithinAt
  have hrhs_diff : DifferentiableOn ℂ
      (fun z : ℂ => Complex.exp (-(1 - s) * Complex.log z) * Complex.Gamma (1 - s)) RHP := fun z hz =>
    ((((Complex.hasDerivAt_log (Or.inl hz)).const_mul (-(1 - s))).cexp.differentiableAt).mul_const _).differentiableWithinAt
  exact eqOn_of_differentiableOn_eq_on_real_interval hRHP_open hRHP_conv.isPreconnected
    hlhs_diff hrhs_diff (a := 1) (b := 2) (by norm_num)
    (fun x hx1 _ => by change 0 < (x : ℂ).re; simp; linarith)
    (fun x hx1 _ => hreal x (by linarith)) hw

private lemma arg_pos_of_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < z.arg := by
  by_contra hle; push Not at hle
  have hne : z ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hz; linarith
  have hsin_pos : 0 < Real.sin z.arg := by
    rw [Complex.sin_arg]; exact div_pos hz (norm_pos_iff.mpr hne)
  have hsin_nonpos : Real.sin z.arg ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le hle (Complex.neg_pi_lt_arg z).le
  linarith

/-- Exact log differences `log(-1 + I) - log(1 - I) = π * I` and `log(-1 - I) - log(1 + I) = -π * I`. -/
private lemma clog_neg_one_add_I_sub :
    Complex.log (-1 + I) - Complex.log (1 - I) = (Real.pi : ℂ) * I := by
  have h1 : (-1 + I : ℂ) ≠ 0 := fun h0 => by have := congrArg Complex.re h0; simp at this
  have h2 : (1 - I : ℂ) ≠ 0 := fun h0 => by have := congrArg Complex.re h0; simp at this
  have hexp : Complex.exp (Complex.log (-1 + I) - Complex.log (1 - I)) = Complex.exp ((Real.pi : ℂ) * I) := by
    rw [Complex.exp_sub, Complex.exp_log h1, Complex.exp_log h2, Complex.exp_pi_mul_I]
    field_simp [h2]; ring
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have him := congrArg Complex.im hn
  simp only [Complex.sub_im, Complex.log_im, Complex.add_im, Complex.mul_im, Complex.mul_re,
    Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero,
    add_zero, sub_zero, Complex.intCast_re, Complex.intCast_im, zero_mul, Complex.re_ofNat,
    Complex.im_ofNat] at him
  have harg1_pos : 0 < (-1 + I : ℂ).arg := arg_pos_of_im_pos (by simp)
  have harg1_le : (-1 + I : ℂ).arg ≤ Real.pi := Complex.arg_le_pi _
  have harg2_neg : (1 - I : ℂ).arg < 0 := Complex.arg_neg_iff.mpr (by simp)
  have harg2_gt : -Real.pi < (1 - I : ℂ).arg := Complex.neg_pi_lt_arg _
  have hn0 : n = 0 := by
    have hlt1 : (-1 : ℝ) < 2 * (n : ℝ) := by nlinarith [Real.pi_pos]
    have hlt2 : 2 * (n : ℝ) < 1 := by nlinarith [Real.pi_pos]
    have h1' : (-1 : ℤ) < 2 * n := by exact_mod_cast hlt1
    have h2' : 2 * n < (1 : ℤ) := by exact_mod_cast hlt2
    omega
  rw [hn, hn0]; simp

private lemma clog_neg_one_sub_I_sub :
    Complex.log (-1 - I) - Complex.log (1 + I) = -((Real.pi : ℂ) * I) := by
  have h1 : (-1 - I : ℂ) ≠ 0 := fun h0 => by have := congrArg Complex.re h0; simp at this
  have h2 : (1 + I : ℂ) ≠ 0 := fun h0 => by have := congrArg Complex.re h0; simp at this
  have hexp : Complex.exp (Complex.log (-1 - I) - Complex.log (1 + I)) = Complex.exp (-((Real.pi : ℂ) * I)) := by
    rw [Complex.exp_sub, Complex.exp_log h1, Complex.exp_log h2, Complex.exp_neg, Complex.exp_pi_mul_I, inv_neg, inv_one]
    field_simp [h2]; ring
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have him := congrArg Complex.im hn
  simp only [Complex.sub_im, Complex.log_im, Complex.add_im, Complex.neg_im, Complex.mul_im,
    Complex.mul_re, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re,
    mul_zero, add_zero, sub_zero, Complex.intCast_re, Complex.intCast_im, zero_mul,
    Complex.re_ofNat, Complex.im_ofNat] at him
  have harg1_neg : (-1 - I : ℂ).arg < 0 := Complex.arg_neg_iff.mpr (by simp)
  have harg1_gt : -Real.pi < (-1 - I : ℂ).arg := Complex.neg_pi_lt_arg _
  have harg2_pos : 0 < (1 + I : ℂ).arg := arg_pos_of_im_pos (by simp)
  have harg2_le : (1 + I : ℂ).arg ≤ Real.pi := Complex.arg_le_pi _
  have hn0 : n = 0 := by
    have hlt1 : (-1 : ℝ) < 2 * (n : ℝ) := by nlinarith [Real.pi_pos]
    have hlt2 : 2 * (n : ℝ) < 1 := by nlinarith [Real.pi_pos]
    have h1' : (-1 : ℤ) < 2 * n := by exact_mod_cast hlt1
    have h2' : 2 * n < (1 : ℤ) := by exact_mod_cast hlt2
    omega
  rw [hn, hn0]; simp

/-- Hankel's reciprocal-Gamma formula in the open strip `0 < s.re < 1` (by sending `r → 0⁺`). -/
private lemma hankelIntegral_cpow_exp_strip {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (2 * (Real.pi : ℂ) * I)⁻¹ * hankelIntegral (fun ζ => Complex.exp (-s * Complex.log ζ) * Complex.exp ζ) =
      (Complex.Gamma s)⁻¹ := by
  let f : ℂ → ℂ := fun ζ => Complex.exp (-s * Complex.log ζ) * Complex.exp ζ
  let seq : ℕ → ℝ := fun n => 1 / ((n + 2 : ℕ) : ℝ)
  have hseq_pos : ∀ n : ℕ, 0 < seq n := fun n => by dsimp only [seq]; positivity
  have hseq_le1 : ∀ n : ℕ, seq n ≤ 1 := fun n => by
    dsimp only [seq]; rw [div_le_one (by positivity)]; norm_cast; omega
  have hseq_tend : Filter.Tendsto seq atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).congr fun n => by
      dsimp only [Function.comp_def, seq]; push_cast; ring
  have hconst : ∀ n : ℕ, hankelIntegralR (seq n) f = hankelIntegral f :=
    fun n => hankelIntegralR_eq_hankelIntegral (hseq_pos n) (hseq_le1 n) s
  -- 1) Vertical cap vanishes as `r = seq n → 0⁺`: `‖I * ∫_{-r}^r f(r + iy) dy‖ ≤ C * r^(1 - s.re) → 0`.
  have hcap_tend : Filter.Tendsto
      (fun n : ℕ => I * ∫ y : ℝ in (-(seq n))..(seq n), f ((seq n : ℂ) + (y : ℂ) * I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbd : ∀ n : ℕ, ‖I * ∫ y : ℝ in (-(seq n))..(seq n), f ((seq n : ℂ) + (y : ℂ) * I)‖ ≤
        (2 * Real.exp (Real.pi * |s.im|) * Real.exp 1) * (seq n) ^ (1 - s.re) := fun n => by
      rw [norm_mul, Complex.norm_I, one_mul]
      have hpt : ∀ y ∈ Set.uIoc (-(seq n)) (seq n),
          ‖f ((seq n : ℂ) + (y : ℂ) * I)‖ ≤
            (Real.exp (Real.pi * |s.im|) * Real.exp 1) * (seq n) ^ (-s.re) := fun y _ => by
        let ζ : ℂ := (seq n : ℂ) + (y : ℂ) * I
        have hre : ζ.re = seq n := by dsimp only [ζ]; simp
        have hnorm_ge : seq n ≤ ‖ζ‖ := by rw [← hre]; exact Complex.re_le_norm ζ
        have hne : ζ ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (hseq_pos n) hnorm_ge)
        dsimp only [f]
        rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
        have hre1 : (-s * Complex.log ζ).re = -s.re * Real.log ‖ζ‖ + s.im * ζ.arg := by
          simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.log_re, Complex.log_im]; ring
        rw [hre1, Real.exp_add, hre]
        have hpow_le : Real.exp (-s.re * Real.log ‖ζ‖) ≤ (seq n) ^ (-s.re) := by
          rw [show Real.exp (-s.re * Real.log ‖ζ‖) = ‖ζ‖ ^ (-s.re) from (by
            rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hne), mul_comm])]
          rw [Real.rpow_neg (norm_nonneg _), Real.rpow_neg (hseq_pos n).le]
          exact inv_anti₀ (Real.rpow_pos_of_pos (hseq_pos n) _)
            (Real.rpow_le_rpow (hseq_pos n).le hnorm_ge hs0.le)
        have harg_le : Real.exp (s.im * ζ.arg) ≤ Real.exp (Real.pi * |s.im|) :=
          Real.exp_le_exp.mpr (by
            calc s.im * ζ.arg ≤ |s.im * ζ.arg| := le_abs_self _
              _ = |s.im| * |ζ.arg| := abs_mul _ _
              _ ≤ |s.im| * Real.pi := mul_le_mul_of_nonneg_left (Complex.abs_arg_le_pi ζ) (abs_nonneg _)
              _ = Real.pi * |s.im| := mul_comm _ _)
        have hexp1 : Real.exp (seq n) ≤ Real.exp 1 := Real.exp_le_exp.mpr (hseq_le1 n)
        calc Real.exp (-s.re * Real.log ‖ζ‖) * Real.exp (s.im * ζ.arg) * Real.exp (seq n)
            ≤ (seq n) ^ (-s.re) * Real.exp (Real.pi * |s.im|) * Real.exp 1 := by gcongr
          _ = (Real.exp (Real.pi * |s.im|) * Real.exp 1) * (seq n) ^ (-s.re) := by ring
      calc ‖∫ y : ℝ in (-(seq n))..(seq n), f ((seq n : ℂ) + (y : ℂ) * I)‖
          ≤ ((Real.exp (Real.pi * |s.im|) * Real.exp 1) * (seq n) ^ (-s.re)) * |seq n - -(seq n)| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hpt
        _ = (2 * Real.exp (Real.pi * |s.im|) * Real.exp 1) * ((seq n) ^ (-s.re) * seq n) := by
            rw [sub_neg_eq_add, abs_of_pos (show 0 < seq n + seq n by linarith [hseq_pos n])]; ring
        _ = (2 * Real.exp (Real.pi * |s.im|) * Real.exp 1) * (seq n) ^ (1 - s.re) := by
            congr 1; rw [sub_eq_add_neg, Real.rpow_add (hseq_pos n), Real.rpow_one, mul_comm]
    have ht0 : Filter.Tendsto (fun n : ℕ => (2 * Real.exp (Real.pi * |s.im|) * Real.exp 1) * (seq n) ^ (1 - s.re))
        atTop (𝓝 0) := by
      have h0 : Filter.Tendsto (fun t : ℝ => t ^ (1 - s.re)) (𝓝 0) (𝓝 0) := by
        simpa [Real.zero_rpow (show (1 - s.re : ℝ) ≠ 0 by linarith)] using
          (Real.continuous_rpow_const (show (0 : ℝ) ≤ 1 - s.re by linarith)).tendsto 0
      simpa using (h0.comp hseq_tend).const_mul (2 * Real.exp (Real.pi * |s.im|) * Real.exp 1)
    exact squeeze_zero (fun _ => norm_nonneg _) hbd ht0
  -- 2) Ray dominated convergence as `r = seq n → 0⁺`:
  have hdom_ray : MeasureTheory.IntegrableOn
      (fun u : ℝ => (Real.exp (Real.pi * |s.im|) * Real.exp 1) * (u ^ (-s.re) * Real.exp (-1 * u)))
      (Set.Ioi 0) volume := by
    have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
    have hi : MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (-s.re) * Real.exp (-1 * u)) (Set.Ioi 0) volume := by
      rw [hsplit]
      refine MeasureTheory.IntegrableOn.union ?_ ?_
      · have hrpow : MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (-s.re)) (Set.Ioc 0 1) volume :=
          (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
            (intervalIntegral.intervalIntegrable_rpow' (by linarith))
        refine hrpow.mono' (by
          have hcont : ContinuousOn (fun u : ℝ => u ^ (-s.re) * Real.exp (-1 * u)) (Set.Ioc 0 1) :=
            (ContinuousOn.rpow_const continuousOn_id fun u (hu : u ∈ Set.Ioc 0 1) => Or.inl (ne_of_gt hu.1)).mul (by fun_prop)
          exact hcont.aestronglyMeasurable measurableSet_Ioc) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
        have hu_nn : 0 ≤ u ^ (-s.re) := Real.rpow_nonneg hu.1.le _
        rw [Real.norm_of_nonneg (mul_nonneg hu_nn (Real.exp_pos _).le)]
        exact mul_le_of_le_one_right hu_nn (Real.exp_le_one_iff.mpr (by linarith [hu.1]))
      · refine (integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 1).mono' (by
          have hcont : ContinuousOn (fun u : ℝ => u ^ (-s.re) * Real.exp (-1 * u)) (Set.Ioi 1) :=
            (ContinuousOn.rpow_const continuousOn_id fun u (hu : u ∈ Set.Ioi 1) =>
              Or.inl (ne_of_gt (lt_trans zero_lt_one hu))).mul (by fun_prop)
          exact hcont.aestronglyMeasurable measurableSet_Ioi) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
        have hu1 : 1 < u := hu
        have hu_nn : 0 ≤ u ^ (-s.re) := Real.rpow_nonneg (by linarith) _
        rw [Real.norm_of_nonneg (mul_nonneg hu_nn (Real.exp_pos _).le)]
        have hle1 : u ^ (-s.re) ≤ 1 := by
          rw [Real.rpow_neg (by linarith)]
          exact inv_le_one_of_one_le₀ (Real.one_le_rpow hu1.le hs0.le)
        exact mul_le_of_le_one_left (Real.exp_pos _).le hle1
    exact hi.const_mul _
  have hray_tend : ∀ sgn : ℝ, sgn = 1 ∨ sgn = -1 →
      Filter.Tendsto
        (fun n : ℕ => ∫ u in Set.Ioi (0 : ℝ),
          f (((seq n - u : ℝ) : ℂ) + ((sgn * (seq n + u) : ℝ) : ℂ) * I))
        atTop
        (𝓝 (∫ u in Set.Ioi (0 : ℝ),
          f (((-u : ℝ) : ℂ) + ((sgn * u : ℝ) : ℂ) * I))) := by
    intro sgn hsgn
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun u : ℝ => (Real.exp (Real.pi * |s.im|) * Real.exp 1) * (u ^ (-s.re) * Real.exp (-1 * u)))
      (Filter.Eventually.of_forall fun n => (integrableOn_hankel_ray (hseq_pos n) s sgn hsgn).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun n => ?_)
      hdom_ray ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := hu
      obtain ⟨_, hne, hlb, _, _⟩ := hankel_ray_props (hseq_pos n) hu0.le sgn hsgn
      let ζ : ℂ := ((seq n - u : ℝ) : ℂ) + ((sgn * (seq n + u) : ℝ) : ℂ) * I
      have hre : ζ.re = seq n - u := by dsimp only [ζ]; simp
      dsimp only [f]
      rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
      have hre1 : (-s * Complex.log ζ).re = -s.re * Real.log ‖ζ‖ + s.im * ζ.arg := by
        simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.log_re, Complex.log_im]; ring
      rw [hre1, Real.exp_add, hre]
      have hpow_le : Real.exp (-s.re * Real.log ‖ζ‖) ≤ u ^ (-s.re) := by
        rw [show Real.exp (-s.re * Real.log ‖ζ‖) = ‖ζ‖ ^ (-s.re) from (by
          rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hne), mul_comm])]
        rw [Real.rpow_neg (norm_nonneg _), Real.rpow_neg hu0.le]
        exact inv_anti₀ (Real.rpow_pos_of_pos hu0 _)
          (Real.rpow_le_rpow hu0.le (by linarith [hseq_pos n]) hs0.le)
      have harg_le : Real.exp (s.im * ζ.arg) ≤ Real.exp (Real.pi * |s.im|) :=
        Real.exp_le_exp.mpr (by
          calc s.im * ζ.arg ≤ |s.im * ζ.arg| := le_abs_self _
            _ = |s.im| * |ζ.arg| := abs_mul _ _
            _ ≤ |s.im| * Real.pi := mul_le_mul_of_nonneg_left (Complex.abs_arg_le_pi ζ) (abs_nonneg _)
            _ = Real.pi * |s.im| := mul_comm _ _)
      have hexp_le : Real.exp (seq n - u) ≤ Real.exp 1 * Real.exp (-1 * u) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith [hseq_le1 n])
      calc Real.exp (-s.re * Real.log ‖ζ‖) * Real.exp (s.im * ζ.arg) * Real.exp (seq n - u)
          ≤ u ^ (-s.re) * Real.exp (Real.pi * |s.im|) * (Real.exp 1 * Real.exp (-1 * u)) := by gcongr
        _ = (Real.exp (Real.pi * |s.im|) * Real.exp 1) * (u ^ (-s.re) * Real.exp (-1 * u)) := by ring
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := hu
      have hslit_lim : (((-u : ℝ) : ℂ) + ((sgn * u : ℝ) : ℂ) * I) ∈ Complex.slitPlane := by
        refine Or.inr ?_
        rw [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
        rcases hsgn with rfl | rfl <;> linarith
      have hf_cont : ContinuousAt f (((-u : ℝ) : ℂ) + ((sgn * u : ℝ) : ℂ) * I) :=
        (((((Complex.hasDerivAt_log hslit_lim).continuousAt).const_mul (-s)).cexp).mul Complex.continuous_exp.continuousAt)
      have harg_tend : Filter.Tendsto
          (fun n : ℕ => ((seq n - u : ℝ) : ℂ) + ((sgn * (seq n + u) : ℝ) : ℂ) * I)
          atTop (𝓝 (((-u : ℝ) : ℂ) + ((sgn * u : ℝ) : ℂ) * I)) := by
        have h1 : Filter.Tendsto (fun n : ℕ => ((seq n - u : ℝ) : ℂ)) atTop (𝓝 (((-u : ℝ) : ℂ))) := by
          have := (hseq_tend.sub (tendsto_const_nhds (x := u))).ofReal; simpa using this
        have h2 : Filter.Tendsto (fun n : ℕ => ((sgn * (seq n + u) : ℝ) : ℂ) * I) atTop
            (𝓝 (((sgn * u : ℝ) : ℂ) * I)) := by
          have := ((hseq_tend.add (tendsto_const_nhds (x := u))).const_mul sgn).ofReal.mul
            (tendsto_const_nhds (x := I))
          simpa using this
        exact h1.add h2
      exact hf_cont.tendsto.comp harg_tend
  -- Combine `r → 0⁺` limit of `hankelIntegralR (seq n) f = hankelIntegral f`!
  have hlim_eq : hankelIntegral f =
      (1 + I) * (∫ u in Set.Ioi (0 : ℝ), f (((-u : ℝ) : ℂ) - (u : ℂ) * I)) +
      (-1 + I) * (∫ u in Set.Ioi (0 : ℝ), f (((-u : ℝ) : ℂ) + (u : ℂ) * I)) := by
    have hbot_t := (hray_tend (-1) (Or.inr rfl)).const_mul (1 + I)
    have htop_t := (hray_tend 1 (Or.inl rfl)).const_mul (-1 + I)
    have hcongr_neg : ∀ (r' u : ℝ), ((r' - u : ℝ) : ℂ) + ((-1 * (r' + u) : ℝ) : ℂ) * I =
        ((r' - u : ℝ) : ℂ) - ((r' + u : ℝ) : ℂ) * I := fun r' u => by push_cast; ring
    have hcongr_lim : ∀ u : ℝ, ((-u : ℝ) : ℂ) + ((-1 * u : ℝ) : ℂ) * I =
        ((-u : ℝ) : ℂ) - (u : ℂ) * I := fun u => by push_cast; ring
    simp_rw [hcongr_neg, hcongr_lim] at hbot_t
    simp only [one_mul] at htop_t
    have hcomb := ((hbot_t.add hcap_tend).add htop_t)
    simp only [add_zero] at hcomb
    have hconst_tend : Filter.Tendsto (fun n : ℕ => hankelIntegralR (seq n) f) atTop (𝓝 (hankelIntegral f)) := by
      simp_rw [hconst]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hconst_tend hcomb
  -- Evaluate the two limiting ray integrals via `laplace_rpow_eq_Gamma`!
  have htop_eval : (-1 + I) * (∫ u in Set.Ioi (0 : ℝ), f (((-u : ℝ) : ℂ) + (u : ℂ) * I)) =
      -Complex.exp (-(Real.pi : ℂ) * I * s) * Complex.Gamma (1 - s) := by
    have hne : (-1 + I : ℂ) ≠ 0 := fun h0 => by have := congrArg Complex.re h0; simp at this
    have hcongr : ∀ u ∈ Set.Ioi (0 : ℝ),
        f (((-u : ℝ) : ℂ) + (u : ℂ) * I) =
          Complex.exp (-s * Complex.log (-1 + I)) *
            (Complex.exp (-s * Complex.log (u : ℂ)) * Complex.exp (-(1 - I) * (u : ℂ))) := fun u hu => by
      dsimp only [f]
      have hmul : ((-u : ℝ) : ℂ) + (u : ℂ) * I = (-1 + I) * (u : ℂ) := by push_cast; ring
      rw [hmul, Complex.log_mul_ofReal_pos hne hu, mul_add, Complex.exp_add]
      have harg : (-1 + I) * (u : ℂ) = -(1 - I) * (u : ℂ) := by ring
      rw [harg]; ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr, MeasureTheory.integral_const_mul,
      laplace_rpow_eq_Gamma hs0 hs1 (w := 1 - I) (by simp)]
    have h1I_ne : (1 - I : ℂ) ≠ 0 := fun h0 => by have := congrArg Complex.re h0; simp at this
    have hlog_eq : Complex.log (-1 + I) = Complex.log (1 - I) + (Real.pi : ℂ) * I := by
      linear_combination clog_neg_one_add_I_sub
    have hfac : (-1 + I) * (Complex.exp (-s * Complex.log (-1 + I)) * Complex.exp (-(1 - s) * Complex.log (1 - I))) =
        -Complex.exp (-(Real.pi : ℂ) * I * s) := by
      rw [hlog_eq, ← Complex.exp_add,
        show -s * (Complex.log (1 - I) + (Real.pi : ℂ) * I) + -(1 - s) * Complex.log (1 - I) =
          -Complex.log (1 - I) + (-(Real.pi : ℂ) * I * s) by ring,
        Complex.exp_add, Complex.exp_neg, Complex.exp_log h1I_ne]
      field_simp [h1I_ne]; ring
    calc (-1 + I) * (Complex.exp (-s * Complex.log (-1 + I)) *
            (Complex.exp (-(1 - s) * Complex.log (1 - I)) * Complex.Gamma (1 - s)))
        = ((-1 + I) * (Complex.exp (-s * Complex.log (-1 + I)) * Complex.exp (-(1 - s) * Complex.log (1 - I)))) *
            Complex.Gamma (1 - s) := by ring
      _ = -Complex.exp (-(Real.pi : ℂ) * I * s) * Complex.Gamma (1 - s) := by rw [hfac]
  have hbot_eval : (1 + I) * (∫ u in Set.Ioi (0 : ℝ), f (((-u : ℝ) : ℂ) - (u : ℂ) * I)) =
      Complex.exp ((Real.pi : ℂ) * I * s) * Complex.Gamma (1 - s) := by
    have hne : (-1 - I : ℂ) ≠ 0 := fun h0 => by have := congrArg Complex.re h0; simp at this
    have hcongr : ∀ u ∈ Set.Ioi (0 : ℝ),
        f (((-u : ℝ) : ℂ) - (u : ℂ) * I) =
          Complex.exp (-s * Complex.log (-1 - I)) *
            (Complex.exp (-s * Complex.log (u : ℂ)) * Complex.exp (-(1 + I) * (u : ℂ))) := fun u hu => by
      dsimp only [f]
      have hmul : ((-u : ℝ) : ℂ) - (u : ℂ) * I = (-1 - I) * (u : ℂ) := by push_cast; ring
      rw [hmul, Complex.log_mul_ofReal_pos hne hu, mul_add, Complex.exp_add]
      have harg : (-1 - I) * (u : ℂ) = -(1 + I) * (u : ℂ) := by ring
      rw [harg]; ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr, MeasureTheory.integral_const_mul,
      laplace_rpow_eq_Gamma hs0 hs1 (w := 1 + I) (by simp)]
    have h1I_ne : (1 + I : ℂ) ≠ 0 := fun h0 => by have := congrArg Complex.re h0; simp at this
    have hlog_eq : Complex.log (-1 - I) = Complex.log (1 + I) - (Real.pi : ℂ) * I := by
      linear_combination clog_neg_one_sub_I_sub
    have hfac : (1 + I) * (Complex.exp (-s * Complex.log (-1 - I)) * Complex.exp (-(1 - s) * Complex.log (1 + I))) =
        Complex.exp ((Real.pi : ℂ) * I * s) := by
      rw [hlog_eq, ← Complex.exp_add,
        show -s * (Complex.log (1 + I) - (Real.pi : ℂ) * I) + -(1 - s) * Complex.log (1 + I) =
          -Complex.log (1 + I) + ((Real.pi : ℂ) * I * s) by ring,
        Complex.exp_add, Complex.exp_neg, Complex.exp_log h1I_ne]
      field_simp [h1I_ne]
    calc (1 + I) * (Complex.exp (-s * Complex.log (-1 - I)) *
            (Complex.exp (-(1 - s) * Complex.log (1 + I)) * Complex.Gamma (1 - s)))
        = ((1 + I) * (Complex.exp (-s * Complex.log (-1 - I)) * Complex.exp (-(1 - s) * Complex.log (1 + I)))) *
            Complex.Gamma (1 - s) := by ring
      _ = Complex.exp ((Real.pi : ℂ) * I * s) * Complex.Gamma (1 - s) := by rw [hfac]
  -- Finish via `Complex.Gamma_mul_Gamma_one_sub s`!
  change (2 * (Real.pi : ℂ) * I)⁻¹ * hankelIntegral f = (Complex.Gamma s)⁻¹
  rw [hlim_eq, hbot_eval, htop_eval]
  have hsin : Complex.exp ((Real.pi : ℂ) * I * s) - Complex.exp (-(Real.pi : ℂ) * I * s) =
      2 * I * Complex.sin ((Real.pi : ℂ) * s) := by
    rw [Complex.sin]
    have hI2 : I * I = -1 := Complex.I_mul_I
    have h1 : -((Real.pi : ℂ) * s) * I = -(Real.pi : ℂ) * I * s := by ring
    have h2 : (Real.pi : ℂ) * s * I = (Real.pi : ℂ) * I * s := by ring
    rw [h1, h2]
    calc Complex.exp ((Real.pi : ℂ) * I * s) - Complex.exp (-(Real.pi : ℂ) * I * s)
        = (Complex.exp (-(Real.pi : ℂ) * I * s) - Complex.exp ((Real.pi : ℂ) * I * s)) * (I * I) := by rw [hI2]; ring
      _ = 2 * I * ((Complex.exp (-(Real.pi : ℂ) * I * s) - Complex.exp ((Real.pi : ℂ) * I * s)) * I / 2) := by ring
  have hcomb : Complex.exp ((Real.pi : ℂ) * I * s) * Complex.Gamma (1 - s) +
      -Complex.exp (-(Real.pi : ℂ) * I * s) * Complex.Gamma (1 - s) =
      2 * I * Complex.sin ((Real.pi : ℂ) * s) * Complex.Gamma (1 - s) := by
    rw [← hsin]; ring
  rw [hcomb]
  have hrefl := Complex.Gamma_mul_Gamma_one_sub s
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * s) ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := Complex.sin_eq_zero_iff.mp h0
    have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    have hs_int : s = (m : ℂ) := mul_left_cancel₀ hpi_ne (by linear_combination hm)
    have hre := congrArg Complex.re hs_int
    simp only [Complex.intCast_re] at hre
    have h1 : (0 : ℤ) < m := by exact_mod_cast (by linarith : (0 : ℝ) < (m : ℝ))
    have h2 : m < (1 : ℤ) := by exact_mod_cast (by linarith : (m : ℝ) < (1 : ℝ))
    omega
  have hGs_ne : Complex.Gamma s ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hrefl
    exact div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne') hsin_ne hrefl.symm
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hG1s : Complex.Gamma (1 - s) = (Real.pi : ℂ) / (Complex.sin ((Real.pi : ℂ) * s) * Complex.Gamma s) := by
    rw [eq_div_iff (mul_ne_zero hsin_ne hGs_ne)]
    have := congrArg (· * Complex.sin ((Real.pi : ℂ) * s)) hrefl
    rw [div_mul_cancel₀ _ hsin_ne] at this
    linear_combination this
  rw [hG1s]
  field_simp [hpi_ne, Complex.I_ne_zero, hsin_ne, hGs_ne]

/-- Continuity of `s ↦ hankelIntegral (ζ ↦ exp(-s * log ζ) * exp ζ)` on all of `ℂ`. -/
private lemma continuous_hankelIntegral_cpow_exp :
    Continuous (fun s : ℂ => hankelIntegral (fun ζ => Complex.exp (-s * Complex.log ζ) * Complex.exp ζ)) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  let R : ℝ := ‖s₀‖ + 2
  have hmem : s₀ ∈ Metric.ball (0 : ℂ) R := by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; dsimp only [R]; linarith
  -- Show continuity on `Metric.ball 0 R` via `MeasureTheory.continuous_of_dominated`!
  let B : Set ℂ := Metric.ball (0 : ℂ) R
  have hcont_ray : ∀ sgn : ℝ, sgn = 1 ∨ sgn = -1 →
      ContinuousOn (fun s : ℂ => ∫ u in Set.Ioi (0 : ℝ),
        Complex.exp (-s * Complex.log (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I)) *
        Complex.exp (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I)) B := by
    intro sgn hsgn
    rw [continuousOn_iff_continuous_domRestrict]
    let N : ℕ := Nat.ceil R
    let C : ℝ := (2 : ℝ) ^ N * Real.exp (Real.pi * R) * Real.exp 1
    refine MeasureTheory.continuous_of_dominated
      (bound := fun u : ℝ => C * ((1 + u) ^ N * Real.exp (-1 * u)))
      (fun s => (integrableOn_hankel_ray zero_lt_one s.1 sgn hsgn).aestronglyMeasurable)
      (fun s => ?_)
      ((integrableOn_one_add_pow_mul_exp_neg N zero_lt_one).const_mul C)
      (Filter.Eventually.of_forall fun u => by fun_prop)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
    have hs_lt : ‖s.1‖ < R := by rw [← dist_zero_right]; exact Metric.mem_ball.mp s.2
    have hs_re : |s.1.re| ≤ R := (Complex.abs_re_le_norm s.1).trans hs_lt.le
    have hs_im : |s.1.im| ≤ R := (Complex.abs_im_le_norm s.1).trans hs_lt.le
    obtain ⟨_, hne, hlb, hub, _⟩ := hankel_ray_props zero_lt_one (le_of_lt hu) sgn hsgn
    let ζ : ℂ := ((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I
    have hre : ζ.re = 1 - u := by dsimp only [ζ]; simp
    have h1 := norm_exp_neg_mul_log_le s.1 ζ hne
    have hinv_le1 : ‖ζ‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [hu.out])
    have hmax2 : (max 1 ‖ζ‖⁻¹) ^ |s.1.re| = 1 := by rw [max_eq_left hinv_le1, Real.one_rpow]
    have hmax1 : (max 1 ‖ζ‖) ^ |s.1.re| ≤ (2 : ℝ) ^ N * (1 + u) ^ N := by
      have hle : max 1 ‖ζ‖ ≤ 2 * (1 + u) := max_le (by linarith [hu.out]) hub
      calc (max 1 ‖ζ‖) ^ |s.1.re| ≤ (2 * (1 + u)) ^ |s.1.re| :=
            Real.rpow_le_rpow (by positivity) hle (abs_nonneg _)
        _ ≤ (2 * (1 + u)) ^ (N : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [hu.out]) (hs_re.trans (Nat.le_ceil R))
        _ = (2 : ℝ) ^ N * (1 + u) ^ N := by rw [Real.rpow_natCast, mul_pow]
    change ‖Complex.exp (-s.1 * Complex.log ζ) * Complex.exp ζ‖ ≤ _
    rw [norm_mul, Complex.norm_exp ζ, hre]
    calc ‖Complex.exp (-s.1 * Complex.log ζ)‖ * Real.exp (1 - u)
        ≤ ((max 1 ‖ζ‖) ^ |s.1.re| * (max 1 ‖ζ‖⁻¹) ^ |s.1.re| * Real.exp (Real.pi * |s.1.im|)) *
            (Real.exp 1 * Real.exp (-1 * u)) := by
          rw [show 1 - u = 1 + (-1 * u) by ring, Real.exp_add]
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (((2 : ℝ) ^ N * (1 + u) ^ N) * 1 * Real.exp (Real.pi * R)) *
            (Real.exp 1 * Real.exp (-1 * u)) := by
          have hu0 : 0 < u := hu
          rw [hmax2]; gcongr
      _ = C * ((1 + u) ^ N * Real.exp (-1 * u)) := by dsimp only [C]; ring
  have hcont_cap : ContinuousOn (fun s : ℂ => ∫ y : ℝ in (-1 : ℝ)..(1 : ℝ),
      Complex.exp (-s * Complex.log ((1 : ℂ) + (y : ℂ) * I)) * Complex.exp ((1 : ℂ) + (y : ℂ) * I)) B := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hrew : (Set.domRestrict B fun s : ℂ => ∫ y : ℝ in (-1 : ℝ)..(1 : ℝ),
        Complex.exp (-s * Complex.log ((1 : ℂ) + (y : ℂ) * I)) * Complex.exp ((1 : ℂ) + (y : ℂ) * I)) =
        fun s : B => ∫ y in Set.Ioc (-1 : ℝ) (1 : ℝ),
          Complex.exp (-s.1 * Complex.log ((1 : ℂ) + (y : ℂ) * I)) * Complex.exp ((1 : ℂ) + (y : ℂ) * I) := by
      funext s; exact intervalIntegral.integral_of_le (by norm_num)
    rw [hrew]
    let C : ℝ := (2 : ℝ) ^ (Nat.ceil R) * Real.exp (Real.pi * R) * Real.exp 1
    refine MeasureTheory.continuous_of_dominated (bound := fun _ : ℝ => C)
      (fun s => by
        have hcont : Continuous (fun y : ℝ => Complex.exp (-s.1 * Complex.log ((1 : ℂ) + (y : ℂ) * I)) *
            Complex.exp ((1 : ℂ) + (y : ℂ) * I)) := continuous_iff_continuousAt.mpr fun y => by
          have hslit : (1 : ℂ) + (y : ℂ) * I ∈ Complex.slitPlane := Or.inl (by simp)
          have hlin : ContinuousAt (fun t : ℝ => (1 : ℂ) + (t : ℂ) * I) y := by fun_prop
          have hlog : ContinuousAt (fun t : ℝ => Complex.log ((1 : ℂ) + (t : ℂ) * I)) y :=
            ContinuousAt.comp (g := Complex.log) (Complex.hasDerivAt_log hslit).continuousAt hlin
          have hexp : ContinuousAt (fun t : ℝ => Complex.exp ((1 : ℂ) + (t : ℂ) * I)) y :=
            ContinuousAt.comp (g := Complex.exp) Complex.continuous_exp.continuousAt hlin
          exact ((hlog.const_mul (-s.1)).cexp).mul hexp
        exact hcont.aestronglyMeasurable)
      (fun s => ?_) (MeasureTheory.integrableOn_const (by simp))
      (Filter.Eventually.of_forall fun y => by fun_prop)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
    have hs_lt : ‖s.1‖ < R := by rw [← dist_zero_right]; exact Metric.mem_ball.mp s.2
    have hs_re : |s.1.re| ≤ R := (Complex.abs_re_le_norm s.1).trans hs_lt.le
    have hs_im : |s.1.im| ≤ R := (Complex.abs_im_le_norm s.1).trans hs_lt.le
    let ζ : ℂ := (1 : ℂ) + (y : ℂ) * I
    have hre : ζ.re = 1 := by dsimp only [ζ]; simp
    have hnorm_ge1 : 1 ≤ ‖ζ‖ := by rw [← hre]; exact Complex.re_le_norm ζ
    have hnorm_le2 : ‖ζ‖ ≤ 2 := (Complex.norm_le_abs_re_add_abs_im ζ).trans (by
      have him : ζ.im = y := by dsimp only [ζ]; simp
      rw [hre, him, abs_one]; have : |y| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩; linarith)
    have hne : ζ ≠ 0 := norm_pos_iff.mp (by linarith)
    have h1 := norm_exp_neg_mul_log_le s.1 ζ hne
    have hmax2 : (max 1 ‖ζ‖⁻¹) ^ |s.1.re| = 1 := by rw [max_eq_left (inv_le_one_of_one_le₀ hnorm_ge1), Real.one_rpow]
    have hmax1 : (max 1 ‖ζ‖) ^ |s.1.re| ≤ (2 : ℝ) ^ (Nat.ceil R) := by
      calc (max 1 ‖ζ‖) ^ |s.1.re| ≤ (2 : ℝ) ^ |s.1.re| :=
            Real.rpow_le_rpow (by positivity) (max_le (by norm_num) hnorm_le2) (abs_nonneg _)
        _ ≤ (2 : ℝ) ^ ((Nat.ceil R : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (hs_re.trans (Nat.le_ceil R))
        _ = (2 : ℝ) ^ (Nat.ceil R) := Real.rpow_natCast _ _
    change ‖Complex.exp (-s.1 * Complex.log ζ) * Complex.exp ζ‖ ≤ _
    rw [norm_mul, Complex.norm_exp ζ, hre]
    calc ‖Complex.exp (-s.1 * Complex.log ζ)‖ * Real.exp 1
        ≤ ((max 1 ‖ζ‖) ^ |s.1.re| * (max 1 ‖ζ‖⁻¹) ^ |s.1.re| * Real.exp (Real.pi * |s.1.im|)) * Real.exp 1 :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ ((2 : ℝ) ^ (Nat.ceil R) * 1 * Real.exp (Real.pi * R)) * Real.exp 1 := by rw [hmax2]; gcongr
      _ = C := by dsimp only [C]; ring
  have hbot : ContinuousOn (fun s : ℂ => ∫ u in Set.Ioi (0 : ℝ),
      Complex.exp (-s * Complex.log (((1 - u : ℝ) : ℂ) - ((1 + u : ℝ) : ℂ) * I)) *
      Complex.exp (((1 - u : ℝ) : ℂ) - ((1 + u : ℝ) : ℂ) * I)) B :=
    (hcont_ray (-1) (Or.inr rfl)).congr fun s _ =>
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u _ => by
        congr 2 <;> (push_cast; ring)
  have htop : ContinuousOn (fun s : ℂ => ∫ u in Set.Ioi (0 : ℝ),
      Complex.exp (-s * Complex.log (((1 - u : ℝ) : ℂ) + ((1 + u : ℝ) : ℂ) * I)) *
      Complex.exp (((1 - u : ℝ) : ℂ) + ((1 + u : ℝ) : ℂ) * I)) B :=
    (hcont_ray 1 (Or.inl rfl)).congr fun s _ =>
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u _ => by simp [one_mul]
  have hall : ContinuousOn
      (fun s : ℂ => hankelIntegral (fun ζ => Complex.exp (-s * Complex.log ζ) * Complex.exp ζ)) B :=
    ((continuousOn_const.mul hbot).add (continuousOn_const.mul hcont_cap)).add (continuousOn_const.mul htop)
  exact hall.continuousAt (Metric.isOpen_ball.mem_nhds hmem)

/-- **Hankel's Reciprocal-Gamma Formula (Unconditional for ALL `s : ℂ`)**:
`(2πi)⁻¹ * ∫_{H_∞} exp(-s * log ζ) * exp(ζ) dζ = (Complex.Gamma s)⁻¹`. -/
theorem hankelIntegral_cpow_exp (s : ℂ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ * hankelIntegral (fun ζ => Complex.exp (-s * Complex.log ζ) * Complex.exp ζ) =
      (Complex.Gamma s)⁻¹ := by
  let H : ℂ → ℂ := fun w => (2 * (Real.pi : ℂ) * I)⁻¹ *
    hankelIntegral (fun ζ => Complex.exp (-w * Complex.log ζ) * Complex.exp ζ)
  have hH_ibp : ∀ w : ℂ, H w = w * H (w + 1) := fun w => by
    dsimp only [H]; unfold hankelIntegral
    rw [hankelIntegralR_ibp zero_lt_one w]; ring
  -- Step 1: Extend from `0 < w.re < 1` to ALL `w` with `w.re ∉ ℤ` by `H(w) = w * H(w + 1)`!
  have hnonint : ∀ w : ℂ, (∀ m : ℤ, w.re ≠ (m : ℝ)) → H w = (Complex.Gamma w)⁻¹ := by
    intro w hw
    have hshift_up : ∀ (n : ℕ) (z : ℂ), (∀ m : ℤ, z.re ≠ (m : ℝ)) →
        H (z + (n : ℂ)) = (Complex.Gamma (z + (n : ℂ)))⁻¹ → H z = (Complex.Gamma z)⁻¹ := by
      intro n
      induction n with
      | zero => intro z _ h; simpa using h
      | succ n ih =>
        intro z hz h
        have hstep : H (z + 1) = (Complex.Gamma (z + 1))⁻¹ := by
          apply ih (z + 1) (fun m hm => hz (m - 1) (by simp at hm; push_cast; linarith))
          simpa [add_assoc, add_comm (1 : ℂ) (n : ℂ)] using h
        have hz_ne : z ≠ 0 := fun h0 => hz 0 (by simp [h0])
        rw [hH_ibp z, hstep, Complex.Gamma_add_one z hz_ne, mul_inv]
        by_cases hG : Complex.Gamma z = 0
        · simp [hG]
        · field_simp [hz_ne, hG]
    have hshift_down : ∀ (n : ℕ) (z : ℂ), (∀ m : ℤ, z.re ≠ (m : ℝ)) →
        H z = (Complex.Gamma z)⁻¹ → H (z + (n : ℂ)) = (Complex.Gamma (z + (n : ℂ)))⁻¹ := by
      intro n
      induction n with
      | zero => intro z _ h; simpa using h
      | succ n ih =>
        intro z hz h
        have hprev := ih z hz h
        have hzn_ne : z + (n : ℂ) ≠ 0 := fun h0 => hz (-n) (by
          have hre := congrArg Complex.re h0; simp at hre; push_cast; linarith)
        have hibp := hH_ibp (z + (n : ℂ))
        rw [hprev] at hibp
        have hrew : z + ((n + 1 : ℕ) : ℂ) = (z + (n : ℂ)) + 1 := by push_cast; ring
        rw [hrew, Complex.Gamma_add_one (z + (n : ℂ)) hzn_ne, mul_inv]
        exact mul_left_cancel₀ hzn_ne (by
          rw [← hibp]; field_simp [hzn_ne])
    let m : ℤ := ⌊w.re⌋
    have hm_lt : (m : ℝ) < w.re := lt_of_le_of_ne (Int.floor_le w.re) (Ne.symm (hw m))
    have hm_gt : w.re < (m : ℝ) + 1 := Int.lt_floor_add_one w.re
    have hstrip : H (w - (m : ℂ)) = (Complex.Gamma (w - (m : ℂ)))⁻¹ :=
      hankelIntegral_cpow_exp_strip (by simp; linarith) (by simp; linarith)
    rcases le_or_gt 0 m with hm0 | hm0
    · lift m to ℕ using hm0 with k hk
      have := hshift_down k (w - (k : ℂ)) (fun r hr => hw (r + k) (by simp at hr; push_cast; linarith)) hstrip
      simpa using this
    · have hpos : 0 ≤ -m := by omega
      lift -m to ℕ using hpos with k hk
      have hmk : -(m : ℂ) = (k : ℂ) := by exact_mod_cast hk.symm
      have hstrip' : H (w + (k : ℂ)) = (Complex.Gamma (w + (k : ℂ)))⁻¹ := by
        simpa [sub_eq_add_neg, hmk] using hstrip
      exact hshift_up k w hw hstrip'
  -- Step 2: Handle non-positive integers `s = -m` directly from `H(w) = w * H(w + 1)`!
  by_cases hneg : ∃ m : ℕ, s = -(m : ℂ)
  · obtain ⟨m, rfl⟩ := hneg
    rw [Complex.Gamma_neg_nat_eq_zero, inv_zero]
    change H (-(m : ℂ)) = 0
    induction m with
    | zero => simpa using hH_ibp 0
    | succ m ih =>
      have h1 : -((m + 1 : ℕ) : ℂ) + 1 = -(m : ℂ) := by push_cast; ring
      rw [hH_ibp (-((m + 1 : ℕ) : ℂ)), h1, ih, mul_zero]
  · -- Step 3: For all other `s` (`∀ m : ℕ, s ≠ -m`), `Complex.Gamma` is continuous and nonzero at `s`.
    push Not at hneg
    by_cases hs_int : ∀ m : ℤ, s.re ≠ (m : ℝ)
    · exact hnonint s hs_int
    · push Not at hs_int
      obtain ⟨m₀, hm₀⟩ := hs_int
      let seq : ℕ → ℂ := fun n => s + (((1 / ((n + 2 : ℕ) : ℝ) : ℝ) : ℂ))
      have hseq_nonint : ∀ n : ℕ, ∀ m : ℤ, (seq n).re ≠ (m : ℝ) := fun n m h => by
        have hre : (seq n).re = (m₀ : ℝ) + 1 / ((n + 2 : ℕ) : ℝ) := by
          dsimp only [seq]; rw [Complex.add_re, hm₀, Complex.ofReal_re]
        rw [hre] at h
        have hpos : (0 : ℝ) < 1 / ((n + 2 : ℕ) : ℝ) := by positivity
        have hlt1 : (1 / ((n + 2 : ℕ) : ℝ)) < 1 := by
          rw [div_lt_one (by positivity)]; norm_cast; omega
        have h1 : (m₀ : ℤ) < m := by exact_mod_cast (by linarith : (m₀ : ℝ) < (m : ℝ))
        have h2 : m < m₀ + 1 := by
          exact_mod_cast (by push_cast; linarith : (m : ℝ) < ((m₀ + 1 : ℤ) : ℝ))
        omega
      have hseq_tend : Filter.Tendsto seq atTop (𝓝 s) := by
        have h0r : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
          (tendsto_one_div_add_atTop_nhds_zero_nat.comp (Filter.tendsto_add_atTop_nat 1)).congr fun n => by
            dsimp only [Function.comp_def]; push_cast; ring
        have h0 : Filter.Tendsto (fun n : ℕ => ((1 / ((n + 2 : ℕ) : ℝ) : ℝ) : ℂ)) atTop (𝓝 0) := by
          simpa using h0r.ofReal
        simpa [seq] using tendsto_const_nhds.add h0
      have hH_cont : Continuous H := continuous_const.mul continuous_hankelIntegral_cpow_exp
      have hH_tend : Filter.Tendsto (fun n : ℕ => H (seq n)) atTop (𝓝 (H s)) :=
        hH_cont.continuousAt.tendsto.comp hseq_tend
      have hGs_ne : Complex.Gamma s ≠ 0 := by
        by_cases hs_im : s.im = 0
        · -- `s = (m₀ : ℂ)` is a positive integer since `s ≠ -m` for all `m : ℕ`!
          have hs_eq : s = (m₀ : ℂ) := Complex.ext (by simp [hm₀]) (by simp [hs_im])
          have hm₀_pos : 0 < m₀ := by
            by_contra hle; push Not at hle
            have hnn : 0 ≤ -m₀ := by omega
            lift -m₀ to ℕ using hnn with k hk
            exact hneg k (by rw [hs_eq]; exact_mod_cast (show m₀ = -(k : ℤ) by omega))
          lift m₀ to ℕ using hm₀_pos.le with k hk
          obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
          rw [hs_eq, show (((r + 1 : ℕ) : ℤ) : ℂ) = (r : ℂ) + 1 by push_cast; ring, Complex.Gamma_nat_eq_factorial]
          exact_mod_cast Nat.factorial_ne_zero r
        · have hrefl := Complex.Gamma_mul_Gamma_one_sub s
          have hsin_ne : Complex.sin ((Real.pi : ℂ) * s) ≠ 0 := fun h0 => by
            obtain ⟨r, hr⟩ := Complex.sin_eq_zero_iff.mp h0
            have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
            have hs_r : s = (r : ℂ) := mul_left_cancel₀ hpi_ne (by linear_combination hr)
            exact hs_im (by rw [hs_r]; simp)
          intro h0
          rw [h0, zero_mul] at hrefl
          exact div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne') hsin_ne hrefl.symm
      have hG_inv_cont : ContinuousAt (fun w : ℂ => (Complex.Gamma w)⁻¹) s :=
        ((Complex.differentiableAt_Gamma s hneg).continuousAt).inv₀ hGs_ne
      have hG_tend : Filter.Tendsto (fun n : ℕ => (Complex.Gamma (seq n))⁻¹) atTop (𝓝 (Complex.Gamma s)⁻¹) :=
        hG_inv_cont.tendsto.comp hseq_tend
      exact tendsto_nhds_unique hH_tend (hG_tend.congr fun n => (hnonint (seq n) (hseq_nonint n)).symm)

/-! ### Uniform Strip Bound on `Ψ_b`, Inner Decomposition of `L_b`, and Exact Hankel–`v_b` Identity -/

/-- Uniform bound on `Ψ_b(u)` in the closed horizontal strip `|u.im| ≤ 3π / (4 log 2)`. -/
private lemma norm_Psi_b_strip_le {b : ℕ} (hb : 2 ≤ b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℂ, |u.im| ≤ 3 * Real.pi / (4 * Real.log 2) → ‖Psi_b b u‖ ≤ M := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨C, hC, hPsi_bd⟩ := norm_Psi_hat_le hb
  let α : ℝ := Real.pi ^ 2 / (2 * Real.log 2)
  have hα : 0 < α := by dsimp only [α]; positivity
  have hdom_sum : Summable (fun k : ℤ => C * (1 + |(k : ℝ)|) ^ b * Real.exp (-α * |(k : ℝ)|)) := by
    have h := (summable_poly_mul_exp_neg_int b (α := α) hα).mul_left C
    exact h.congr fun k => by ring
  refine ⟨∑' k : ℤ, C * (1 + |(k : ℝ)|) ^ b * Real.exp (-α * |(k : ℝ)|),
    tsum_nonneg fun k => by positivity, fun u hu => ?_⟩
  have hu_lt : |u.im| < Real.pi / Real.log 2 := by
    calc |u.im| ≤ 3 * Real.pi / (4 * Real.log 2) := hu
      _ < Real.pi / Real.log 2 := by
          rw [div_lt_div_iff₀ (by positivity) hlog2]
          nlinarith [Real.pi_pos, hlog2]
  rw [Psi_b_fourier_series hb hu_lt]
  have hterm : ∀ k : ℤ, ‖Psi_hat b k * Complex.exp (2 * (Real.pi : ℂ) * I * (k : ℂ) * u)‖ ≤
      C * (1 + |(k : ℝ)|) ^ b * Real.exp (-α * |(k : ℝ)|) := fun k => by
    rw [norm_mul, Complex.norm_exp]
    have hre : (2 * (Real.pi : ℂ) * I * (k : ℂ) * u).re = -2 * Real.pi * (k : ℝ) * u.im := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    have hexp_le : Real.exp (-2 * Real.pi * (k : ℝ) * u.im) ≤
        Real.exp (3 * Real.pi ^ 2 * |(k : ℝ)| / (2 * Real.log 2)) := by
      refine Real.exp_le_exp.mpr ?_
      have h1 : -2 * Real.pi * (k : ℝ) * u.im ≤ 2 * Real.pi * |(k : ℝ)| * |u.im| := by
        calc -2 * Real.pi * (k : ℝ) * u.im
            ≤ |-2 * Real.pi * (k : ℝ) * u.im| := le_abs_self _
          _ = 2 * Real.pi * |(k : ℝ)| * |u.im| := by
              rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2),
                abs_of_pos Real.pi_pos]
      calc -2 * Real.pi * (k : ℝ) * u.im
          ≤ 2 * Real.pi * |(k : ℝ)| * |u.im| := h1
        _ ≤ 2 * Real.pi * |(k : ℝ)| * (3 * Real.pi / (4 * Real.log 2)) :=
            mul_le_mul_of_nonneg_left hu (by positivity)
        _ = 3 * Real.pi ^ 2 * |(k : ℝ)| / (2 * Real.log 2) := by ring
    calc ‖Psi_hat b k‖ * Real.exp (-2 * Real.pi * (k : ℝ) * u.im)
        ≤ (C * (1 + |(k : ℝ)|) ^ b * Real.exp (-2 * Real.pi ^ 2 * |(k : ℝ)| / Real.log 2)) *
            Real.exp (3 * Real.pi ^ 2 * |(k : ℝ)| / (2 * Real.log 2)) :=
          mul_le_mul (hPsi_bd k) hexp_le (Real.exp_pos _).le (by positivity)
      _ = C * (1 + |(k : ℝ)|) ^ b *
            (Real.exp (-2 * Real.pi ^ 2 * |(k : ℝ)| / Real.log 2) *
             Real.exp (3 * Real.pi ^ 2 * |(k : ℝ)| / (2 * Real.log 2))) := by ring
      _ = C * (1 + |(k : ℝ)|) ^ b * Real.exp (-α * |(k : ℝ)|) := by
          rw [← Real.exp_add]; congr 2; dsimp only [α]; ring
  exact norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hdom_sum) |>.trans
    (Summable.tsum_le_tsum hterm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hdom_sum) hdom_sum)

/-- Every point of `Complex.slitPlane` belongs to `PsiWDomain`. -/
private lemma mem_PsiWDomain_of_slitPlane {ξ : ℂ} (hξ : ξ ∈ Complex.slitPlane) :
    ξ ∈ PsiWDomain := by
  refine ⟨Complex.slitPlane_ne_zero hξ, fun m h0 => ?_⟩
  have h2m_pos : (0 : ℝ) < (2 : ℝ) ^ m := zpow_pos (by norm_num) m
  have h2m_eq : (2 : ℂ) ^ m = (((2 : ℝ) ^ m : ℝ) : ℂ) := by
    rw [Complex.ofReal_zpow, Complex.ofReal_ofNat]
  rw [h2m_eq] at h0
  rcases hξ with hre | him
  · have := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.zero_re] at this
    nlinarith
  · have := congrArg Complex.im h0
    simp only [Complex.add_im, Complex.one_im, zero_add, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Complex.zero_im] at this
    exact him ((mul_eq_zero.mp this).resolve_left h2m_pos.ne')

/-- Near `ξ = 0` (`‖ξ‖ ≤ 3/4`, `|arg ξ| ≤ 3π/4`), `L_b b ξ = ξ⁻² Ψ_b(-log ξ / log 2) + O(‖ξ‖⁻¹)`. -/
private lemma L_b_inner_decomp {b : ℕ} (hb : 2 ≤ b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ : ℂ, ξ ∈ Complex.slitPlane → ‖ξ‖ ≤ 3 / 4 → |ξ.arg| ≤ 3 * Real.pi / 4 →
      ‖L_b b ξ - ξ⁻¹ ^ 2 * Psi_b b (-Complex.log ξ / ((Real.log 2 : ℝ) : ℂ))‖ ≤ M * ‖ξ‖⁻¹ := by
  have hb1 : 1 ≤ b := by omega
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨M_Psi, hM_Psi_nn, hPsi_bd⟩ := norm_Psi_b_strip_le hb
  let K : Set ℂ := Metric.closedBall 0 (3 / 4)
  have hK_comp : IsCompact K := isCompact_closedBall 0 (3 / 4)
  have hK_sub : K ⊆ Metric.ball 0 (3 / 2) := fun z hz => by
    rw [Metric.mem_ball, dist_zero_right]
    have : ‖z‖ ≤ 3 / 4 := by simpa [K, Metric.mem_closedBall, dist_zero_right] using hz
    linarith
  have hdPi : ContinuousOn (dslope (Pi_b b) 0) K := by
    have hd : DifferentiableOn ℂ (dslope (Pi_b b) 0) (Metric.ball 0 (3 / 2)) :=
      (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))).mpr
        (Pi_b_differentiable b).differentiableOn
    exact hd.continuousOn.mono hK_sub
  have hdT : ContinuousOn (dslope (T_b b) 0) K := by
    have hd : DifferentiableOn ℂ (dslope (T_b b) 0) (Metric.ball 0 (3 / 2)) :=
      (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))).mpr
        (T_b_differentiableOn b)
    exact hd.continuousOn.mono hK_sub
  have hPi_cont : ContinuousOn (Pi_b b) K := (Pi_b_differentiable b).continuous.continuousOn
  obtain ⟨M1, hM1⟩ := hK_comp.exists_bound_of_continuousOn hdPi
  obtain ⟨M2, hM2⟩ := hK_comp.exists_bound_of_continuousOn hdT
  obtain ⟨M3, hM3⟩ := hK_comp.exists_bound_of_continuousOn hPi_cont
  let M : ℝ := max 0 M1 * M_Psi + max 0 M3 * max 0 M2
  refine ⟨M, by positivity, fun ξ hξ_slit hξ_le harg => ?_⟩
  have hξ_memK : ξ ∈ K := by simpa [K, Metric.mem_closedBall, dist_zero_right] using hξ_le
  have hξ_ne : ξ ≠ 0 := Complex.slitPlane_ne_zero hξ_slit
  have hdecomp := xi_mul_G_mero_inv_eq hb1 (mem_PsiWDomain_of_slitPlane hξ_slit)
  have hL_eq : L_b b ξ = ξ⁻¹ ^ 2 * (ξ * G_mero b ξ⁻¹) := by
    unfold L_b; field_simp [hξ_ne]
  have hPi_eq : Pi_b b ξ = 1 + ξ * dslope (Pi_b b) 0 ξ := by
    have h := sub_smul_dslope (Pi_b b) 0 ξ
    rw [sub_zero, Pi_b_zero, smul_eq_mul] at h
    linear_combination -h
  have hT_eq : T_b b ξ = ξ * dslope (T_b b) 0 ξ := by
    have h := sub_smul_dslope (T_b b) 0 ξ
    rw [sub_zero, T_b_zero, sub_zero, smul_eq_mul] at h
    exact h.symm
  let u : ℂ := -Complex.log ξ / ((Real.log 2 : ℝ) : ℂ)
  have hsub_eq : L_b b ξ - ξ⁻¹ ^ 2 * Psi_b b u =
      ξ⁻¹ * (dslope (Pi_b b) 0 ξ * Psi_b b u - Pi_b b ξ * dslope (T_b b) 0 ξ) := by
    rw [hL_eq, hdecomp]
    change ξ⁻¹ ^ 2 * (Pi_b b ξ * (Psi_b b u - T_b b ξ)) - ξ⁻¹ ^ 2 * Psi_b b u = _
    have h1 : Pi_b b ξ * (Psi_b b u - T_b b ξ) - Psi_b b u =
        ξ * (dslope (Pi_b b) 0 ξ * Psi_b b u - Pi_b b ξ * dslope (T_b b) 0 ξ) := by
      calc Pi_b b ξ * (Psi_b b u - T_b b ξ) - Psi_b b u
          = (Pi_b b ξ - 1) * Psi_b b u - Pi_b b ξ * T_b b ξ := by ring
        _ = (ξ * dslope (Pi_b b) 0 ξ) * Psi_b b u - Pi_b b ξ * (ξ * dslope (T_b b) 0 ξ) := by
            rw [hPi_eq, add_sub_cancel_left, hT_eq]
        _ = ξ * (dslope (Pi_b b) 0 ξ * Psi_b b u - Pi_b b ξ * dslope (T_b b) 0 ξ) := by ring
    calc ξ⁻¹ ^ 2 * (Pi_b b ξ * (Psi_b b u - T_b b ξ)) - ξ⁻¹ ^ 2 * Psi_b b u
        = ξ⁻¹ ^ 2 * (Pi_b b ξ * (Psi_b b u - T_b b ξ) - Psi_b b u) := by ring
      _ = ξ⁻¹ ^ 2 * (ξ * (dslope (Pi_b b) 0 ξ * Psi_b b u - Pi_b b ξ * dslope (T_b b) 0 ξ)) := by rw [h1]
      _ = ξ⁻¹ * (dslope (Pi_b b) 0 ξ * Psi_b b u - Pi_b b ξ * dslope (T_b b) 0 ξ) := by
          field_simp [hξ_ne]
  have hu_im : |u.im| ≤ 3 * Real.pi / (4 * Real.log 2) := by
    have him : u.im = -ξ.arg / Real.log 2 := by
      dsimp only [u]; rw [Complex.div_ofReal_im, Complex.neg_im, Complex.log_im]
    rw [him, abs_div, abs_neg, abs_of_pos hlog2]
    calc |ξ.arg| / Real.log 2 ≤ (3 * Real.pi / 4) / Real.log 2 := div_le_div_of_nonneg_right harg hlog2.le
      _ = 3 * Real.pi / (4 * Real.log 2) := by ring
  rw [show L_b b ξ - ξ⁻¹ ^ 2 * Psi_b b (-Complex.log ξ / ((Real.log 2 : ℝ) : ℂ)) =
      L_b b ξ - ξ⁻¹ ^ 2 * Psi_b b u from rfl, hsub_eq, norm_mul, norm_inv]
  have hR_le : ‖dslope (Pi_b b) 0 ξ * Psi_b b u - Pi_b b ξ * dslope (T_b b) 0 ξ‖ ≤ M := by
    calc ‖dslope (Pi_b b) 0 ξ * Psi_b b u - Pi_b b ξ * dslope (T_b b) 0 ξ‖
        ≤ ‖dslope (Pi_b b) 0 ξ * Psi_b b u‖ + ‖Pi_b b ξ * dslope (T_b b) 0 ξ‖ := norm_sub_le _ _
      _ = ‖dslope (Pi_b b) 0 ξ‖ * ‖Psi_b b u‖ + ‖Pi_b b ξ‖ * ‖dslope (T_b b) 0 ξ‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ max 0 M1 * M_Psi + max 0 M3 * max 0 M2 := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul ((hM1 ξ hξ_memK).trans (le_max_right _ _)) (hPsi_bd u hu_im)
              (norm_nonneg _) (le_max_left _ _)
          · exact mul_le_mul ((hM3 ξ hξ_memK).trans (le_max_right _ _))
              ((hM2 ξ hξ_memK).trans (le_max_right _ _)) (norm_nonneg _) (le_max_left _ _)
  calc ‖ξ‖⁻¹ * ‖dslope (Pi_b b) 0 ξ * Psi_b b u - Pi_b b ξ * dslope (T_b b) 0 ξ‖
      ≤ ‖ξ‖⁻¹ * M := mul_le_mul_of_nonneg_left hR_le (inv_nonneg.mpr (norm_nonneg _))
    _ = M * ‖ξ‖⁻¹ := mul_comm _ _

/-- Uniform bound on `L_b b` on the outer compact region `‖ξ‖ ≤ 5 ∧ (ξ.re ≤ -3/2 ∨ 1/4 ≤ |ξ.im|)`. -/
private lemma L_b_outer_bound {b : ℕ} (hb : 1 ≤ b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ : ℂ, ‖ξ‖ ≤ 5 → (ξ.re ≤ -3 / 2 ∨ 1 / 4 ≤ |ξ.im|) → ‖L_b b ξ‖ ≤ M := by
  let K : Set ℂ := Metric.closedBall 0 5 ∩ ({ξ : ℂ | ξ.re ≤ -3 / 2} ∪ {ξ : ℂ | (1 / 4 : ℝ) ≤ |ξ.im|})
  have hK_comp : IsCompact K := (isCompact_closedBall 0 5).inter_right
    ((isClosed_le Complex.continuous_re continuous_const).union
      (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im)))
  have hK_sub : K ⊆ SlitNegUnit := fun ξ hξ hbad => by
    rcases hξ.2 with hre | him
    · change ξ.re ≤ -3 / 2 at hre; linarith [hbad.2.1]
    · change (1 / 4 : ℝ) ≤ |ξ.im| at him
      have him0 : ξ.im = 0 := hbad.1
      rw [him0, abs_zero] at him; linarith
  have hcont : ContinuousOn (L_b b) K := (L_b_differentiableOn_slitNegUnit hb).continuousOn.mono hK_sub
  obtain ⟨M, hM⟩ := hK_comp.exists_bound_of_continuousOn hcont
  exact ⟨max 0 M, le_max_left _ _, fun ξ h1 h2 =>
    (hM ξ ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using h1, h2⟩).trans (le_max_right _ _)⟩

/-- Integer power identity `ζ ^ m = exp (m * log ζ)` for all `ζ ≠ 0` and `m : ℤ`. -/
private lemma zpow_eq_exp_mul_log {ζ : ℂ} (hζ : ζ ≠ 0) (m : ℤ) :
    ζ ^ m = Complex.exp ((m : ℂ) * Complex.log ζ) := by
  cases m with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, Int.cast_natCast, Complex.exp_nat_mul, Complex.exp_log hζ]
  | negSucc n =>
    rw [zpow_negSucc, Int.cast_negSucc, neg_mul, Complex.exp_neg, Complex.exp_nat_mul, Complex.exp_log hζ]

/-- Strict argument bound `|z.arg| < π / 2` whenever `0 < z.re`. -/
private lemma abs_arg_lt_pi_div_two_of_re_pos {z : ℂ} (hz : 0 < z.re) : |z.arg| < Real.pi / 2 := by
  have hne : z ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hz; linarith
  have hcos_gt : Real.cos (Real.pi / 2) < Real.cos |z.arg| := by
    rw [Real.cos_pi_div_two, Real.cos_abs, Complex.cos_arg hne]
    exact div_pos hz (norm_pos_iff.mpr hne)
  have hm1 : |z.arg| ∈ Set.Icc (0 : ℝ) Real.pi := ⟨abs_nonneg _, Complex.abs_arg_le_pi z⟩
  have hm2 : Real.pi / 2 ∈ Set.Icc (0 : ℝ) Real.pi := ⟨by positivity, by linarith [Real.pi_pos]⟩
  exact (Real.strictAntiOn_cos.lt_iff_gt hm2 hm1).mp hcos_gt

/-- Helper: `Finset` sum of convergent sequences converges to the sum of limits. -/
private lemma tendsto_finset_sum_fr {α β ι : Type*} [AddCommMonoid β] [TopologicalSpace β]
    [ContinuousAdd β] {l : Filter α} {s : Finset ι} {f : ι → α → β} {a : ι → β}
    (hf : ∀ i ∈ s, Filter.Tendsto (f i) l (𝓝 (a i))) :
    Filter.Tendsto (fun x => ∑ i ∈ s, f i x) l (𝓝 (∑ i ∈ s, a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Helper: `Finset` product of convergent sequences converges to the product of limits. -/
private lemma tendsto_finset_prod_fr {α β ι : Type*} [CommMonoid β] [TopologicalSpace β]
    [ContinuousMul β] {l : Filter α} {s : Finset ι} {f : ι → α → β} {a : ι → β}
    (hf : ∀ i ∈ s, Filter.Tendsto (f i) l (𝓝 (a i))) :
    Filter.Tendsto (fun x => ∏ i ∈ s, f i x) l (𝓝 (∏ i ∈ s, a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds
  | insert i s hi ih =>
    simp_rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).mul (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Helper: `Finset` product of functions holomorphic on `U` is holomorphic on `U`. -/
private lemma differentiableOn_finset_prod_fr {ι : Type*} {s : Finset ι} {f : ι → ℂ → ℂ} {U : Set ℂ}
    (hf : ∀ i ∈ s, DifferentiableOn ℂ (f i) U) :
    DifferentiableOn ℂ (fun z => ∏ i ∈ s, f i z) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hrew : (fun z => ∏ j ∈ insert i s, f j z) = fun z => f i z * ∏ j ∈ s, f j z := by
      funext z; exact Finset.prod_insert hi
    rw [hrew]
    exact (hf i (Finset.mem_insert_self i s)).mul (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Helper: `a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ (f i)` for `a ≠ 0` in `ℂ`. -/
private lemma zpow_sum_complex {a : ℂ} (ha : a ≠ 0) {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]

/-- Helper: every `p : Polynomial ℂ` defines an entire function `z ↦ p.eval z`. -/
private lemma differentiable_poly_eval_complex (p : Polynomial ℂ) :
    Differentiable ℂ (fun z : ℂ => p.eval z) := by
  have hrew : (fun z : ℂ => p.eval z) = fun z : ℂ => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * z ^ i := by
    funext z; exact Polynomial.eval_eq_sum_range z
  rw [hrew]
  exact Differentiable.fun_sum fun i _ => (differentiable_const _).mul (differentiable_id.pow i)

/-- **Exact Hankel–`v_b` Identity**: for ALL `b ≥ 2`, `j : ℕ`, and `x > 0`,
`(2πi)⁻¹ ∫_{H_∞} ζ^{j-2} e^ζ Ψ_b((log x - log ζ) / log 2) dζ = x^{j-1} v_b^{(j)}(x)`. -/
private lemma hankelIntegral_Psi_b_eq_v_b {b : ℕ} (hb : 2 ≤ b) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    (2 * (Real.pi : ℂ) * I)⁻¹ * hankelIntegral (fun ζ =>
        ζ ^ ((j : ℤ) - 2) * Complex.exp ζ *
          Psi_b b ((Complex.log (x : ℂ) - Complex.log ζ) / ((Real.log 2 : ℝ) : ℂ))) =
      (x : ℂ) ^ ((j : ℤ) - 1) * iteratedDeriv j (v_b b) (x : ℂ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2C : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog2.ne'
  obtain ⟨C, hC, hPsi_bd⟩ := norm_Psi_hat_le hb
  let α : ℝ := Real.pi ^ 2 / (2 * Real.log 2)
  have hα : 0 < α := by dsimp only [α]; positivity
  let aK : ℤ → ℝ := fun k => C * (1 + |(k : ℝ)|) ^ b * Real.exp (-α * |(k : ℝ)|)
  have haK_sum : Summable aK := by
    have h := (summable_poly_mul_exp_neg_int b (α := α) hα).mul_left C
    exact h.congr fun k => by dsimp only [aK]; ring
  let c : ℤ → ℂ := fun k => Psi_hat b k * Complex.exp (chiFR k * Complex.log (x : ℂ))
  let F : ℤ → ℂ → ℂ := fun k ζ =>
    c k * (Complex.exp (-(2 - (j : ℂ) + chiFR k) * Complex.log ζ) * Complex.exp ζ)
  -- Pointwise series identity for all `ζ ≠ 0` with `|ζ.arg| ≤ 3π/4`:
  have hpt_eq : ∀ ζ : ℂ, ζ ≠ 0 → |ζ.arg| ≤ 3 * Real.pi / 4 →
      ζ ^ ((j : ℤ) - 2) * Complex.exp ζ *
          Psi_b b ((Complex.log (x : ℂ) - Complex.log ζ) / ((Real.log 2 : ℝ) : ℂ)) =
        ∑' k : ℤ, F k ζ := by
    intro ζ hζ harg
    have hu_im : |((Complex.log (x : ℂ) - Complex.log ζ) / ((Real.log 2 : ℝ) : ℂ)).im| <
        Real.pi / Real.log 2 := by
      have hlogx_im : (Complex.log (x : ℂ)).im = 0 := by
        rw [Complex.log_im, Complex.arg_ofReal_of_nonneg hx.le]
      rw [Complex.div_ofReal_im, Complex.sub_im, hlogx_im, Complex.log_im, zero_sub, abs_div, abs_neg,
        abs_of_pos hlog2]
      calc |ζ.arg| / Real.log 2 ≤ (3 * Real.pi / 4) / Real.log 2 := div_le_div_of_nonneg_right harg hlog2.le
        _ < Real.pi / Real.log 2 := by
            rw [div_lt_div_iff₀ hlog2 hlog2]; nlinarith [Real.pi_pos, hlog2]
    rw [Psi_b_fourier_series hb hu_im, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    dsimp only [F, c]
    rw [zpow_eq_exp_mul_log hζ ((j : ℤ) - 2)]
    have hexp_split : Complex.exp (2 * (Real.pi : ℂ) * I * (k : ℂ) *
          ((Complex.log (x : ℂ) - Complex.log ζ) / ((Real.log 2 : ℝ) : ℂ))) =
        Complex.exp (chiFR k * Complex.log (x : ℂ)) * Complex.exp (-chiFR k * Complex.log ζ) := by
      rw [← Complex.exp_add]; congr 1; unfold chiFR
      simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_intCast]
      field_simp [hlog2C]; ring
    have hexp_comb : Complex.exp ((((j : ℤ) - 2 : ℤ) : ℂ) * Complex.log ζ) *
          Complex.exp (-chiFR k * Complex.log ζ) =
        Complex.exp (-(2 - (j : ℂ) + chiFR k) * Complex.log ζ) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hexp_split]
    calc Complex.exp ((((j : ℤ) - 2 : ℤ) : ℂ) * Complex.log ζ) * Complex.exp ζ *
            (Psi_hat b k * (Complex.exp (chiFR k * Complex.log (x : ℂ)) * Complex.exp (-chiFR k * Complex.log ζ)))
        = (Psi_hat b k * Complex.exp (chiFR k * Complex.log (x : ℂ))) *
            ((Complex.exp ((((j : ℤ) - 2 : ℤ) : ℂ) * Complex.log ζ) * Complex.exp (-chiFR k * Complex.log ζ)) *
             Complex.exp ζ) := by ring
      _ = (Psi_hat b k * Complex.exp (chiFR k * Complex.log (x : ℂ))) *
            (Complex.exp (-(2 - (j : ℂ) + chiFR k) * Complex.log ζ) * Complex.exp ζ) := by rw [hexp_comb]
  -- Pointwise norm bound on `F k ζ` for `1 ≤ ‖ζ‖` and `|ζ.arg| ≤ 3π/4`:
  have hF_norm : ∀ (k : ℤ) (ζ : ℂ), 1 ≤ ‖ζ‖ → |ζ.arg| ≤ 3 * Real.pi / 4 →
      ‖F k ζ‖ ≤ aK k * (‖ζ‖ ^ j * Real.exp ζ.re) := by
    intro k ζ hnorm1 harg
    have hζ_ne : ζ ≠ 0 := norm_pos_iff.mp (by linarith)
    dsimp only [F, c]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, Complex.norm_exp]
    have hre_x : (chiFR k * Complex.log (x : ℂ)).re = 0 := by
      rw [Complex.mul_re, chiFR_re, zero_mul, Complex.log_im, Complex.arg_ofReal_of_nonneg hx.le,
        mul_zero, sub_zero]
    rw [hre_x, Real.exp_zero, mul_one]
    have hre_z : (-(2 - (j : ℂ) + chiFR k) * Complex.log ζ).re =
        ((j : ℝ) - 2) * Real.log ‖ζ‖ + (2 * Real.pi * (k : ℝ) / Real.log 2) * ζ.arg := by
      rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_re,
        Complex.natCast_im, chiFR_re, chiFR_im, Complex.log_re, Complex.log_im]
      ring
    rw [hre_z, Real.exp_add]
    have hpow_le : Real.exp (((j : ℝ) - 2) * Real.log ‖ζ‖) ≤ ‖ζ‖ ^ j := by
      rw [show Real.exp (((j : ℝ) - 2) * Real.log ‖ζ‖) = ‖ζ‖ ^ ((j : ℝ) - 2) from
        (by rw [Real.rpow_def_of_pos (by linarith), mul_comm])]
      calc ‖ζ‖ ^ ((j : ℝ) - 2) ≤ ‖ζ‖ ^ (j : ℝ) := Real.rpow_le_rpow_of_exponent_le hnorm1 (by linarith)
        _ = ‖ζ‖ ^ j := Real.rpow_natCast _ _
    have harg_le : Real.exp ((2 * Real.pi * (k : ℝ) / Real.log 2) * ζ.arg) ≤
        Real.exp (3 * Real.pi ^ 2 * |(k : ℝ)| / (2 * Real.log 2)) := by
      refine Real.exp_le_exp.mpr ?_
      calc (2 * Real.pi * (k : ℝ) / Real.log 2) * ζ.arg
          ≤ |(2 * Real.pi * (k : ℝ) / Real.log 2) * ζ.arg| := le_abs_self _
        _ = (2 * Real.pi * |(k : ℝ)| / Real.log 2) * |ζ.arg| := by
            rw [abs_mul, abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
              abs_of_pos Real.pi_pos, abs_of_pos hlog2]
        _ ≤ (2 * Real.pi * |(k : ℝ)| / Real.log 2) * (3 * Real.pi / 4) :=
            mul_le_mul_of_nonneg_left harg (by positivity)
        _ = 3 * Real.pi ^ 2 * |(k : ℝ)| / (2 * Real.log 2) := by ring
    calc ‖Psi_hat b k‖ * (Real.exp (((j : ℝ) - 2) * Real.log ‖ζ‖) *
            Real.exp ((2 * Real.pi * (k : ℝ) / Real.log 2) * ζ.arg) * Real.exp ζ.re)
        ≤ (C * (1 + |(k : ℝ)|) ^ b * Real.exp (-2 * Real.pi ^ 2 * |(k : ℝ)| / Real.log 2)) *
            (‖ζ‖ ^ j * Real.exp (3 * Real.pi ^ 2 * |(k : ℝ)| / (2 * Real.log 2)) * Real.exp ζ.re) := by
          refine mul_le_mul (hPsi_bd k) ?_ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul hpow_le harg_le (Real.exp_pos _).le (by positivity))
            (Real.exp_pos _).le
      _ = (C * (1 + |(k : ℝ)|) ^ b *
            (Real.exp (-2 * Real.pi ^ 2 * |(k : ℝ)| / Real.log 2) *
             Real.exp (3 * Real.pi ^ 2 * |(k : ℝ)| / (2 * Real.log 2)))) *
            (‖ζ‖ ^ j * Real.exp ζ.re) := by ring
      _ = aK k * (‖ζ‖ ^ j * Real.exp ζ.re) := by
          rw [← Real.exp_add]; dsimp only [aK, α]; congr 3; ring
  -- Interchange `∫` and `∑' k : ℤ` on the two infinite rays:
  have hray_swap : ∀ (sgn : ℝ), sgn = 1 ∨ sgn = -1 →
      (∫ u in Set.Ioi (0 : ℝ),
        let ζ : ℂ := ((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I
        ζ ^ ((j : ℤ) - 2) * Complex.exp ζ *
          Psi_b b ((Complex.log (x : ℂ) - Complex.log ζ) / ((Real.log 2 : ℝ) : ℂ))) =
      ∑' k : ℤ, ∫ u in Set.Ioi (0 : ℝ),
        F k (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I) := by
    intro sgn hsgn
    have hcongr : (∫ u in Set.Ioi (0 : ℝ),
        let ζ : ℂ := ((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I
        ζ ^ ((j : ℤ) - 2) * Complex.exp ζ *
          Psi_b b ((Complex.log (x : ℂ) - Complex.log ζ) / ((Real.log 2 : ℝ) : ℂ))) =
      ∫ u in Set.Ioi (0 : ℝ), ∑' k : ℤ, F k (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      obtain ⟨_, hne, _, _, harg⟩ := hankel_ray_props zero_lt_one (le_of_lt hu) sgn hsgn
      exact hpt_eq _ hne harg
    rw [hcongr]
    let g : ℤ → ℝ → ℂ := fun k u => F k (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I)
    have hmeas : ∀ k : ℤ, MeasureTheory.AEStronglyMeasurable (g k) (volume.restrict (Set.Ioi (0 : ℝ))) := fun k =>
      ((integrableOn_hankel_ray zero_lt_one (2 - (j : ℂ) + chiFR k) sgn hsgn).const_mul (c k)).aestronglyMeasurable
    have hdom_int := (integrableOn_one_add_pow_mul_exp_neg j zero_lt_one).const_mul ((2 : ℝ) ^ j * Real.exp 1)
    have hlint_le : ∀ k : ℤ, ∫⁻ u in Set.Ioi (0 : ℝ), ‖g k u‖ₑ ≤
        ENNReal.ofReal (aK k * ∫ u in Set.Ioi (0 : ℝ), (2 : ℝ) ^ j * Real.exp 1 * ((1 + u) ^ j * Real.exp (-1 * u))) := by
      intro k
      have hbound : ∀ u ∈ Set.Ioi (0 : ℝ),
          ‖g k u‖ ≤ aK k * ((2 : ℝ) ^ j * Real.exp 1 * ((1 + u) ^ j * Real.exp (-1 * u))) := fun u hu => by
        obtain ⟨_, _, hlb, hub, harg⟩ := hankel_ray_props zero_lt_one (le_of_lt hu) sgn hsgn
        have h1 : 1 ≤ ‖((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I‖ := by linarith [show (0 : ℝ) < u from hu]
        have hre : (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I).re = 1 - u := by simp
        calc ‖g k u‖
            ≤ aK k * (‖((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I‖ ^ j * Real.exp (1 - u)) := by
              simpa [g, hre] using hF_norm k _ h1 harg
          _ ≤ aK k * ((2 * (1 + u)) ^ j * (Real.exp 1 * Real.exp (-1 * u))) := by
              rw [show Real.exp (1 - u) = Real.exp 1 * Real.exp (-1 * u) by rw [← Real.exp_add]; congr 1; ring]
              have haK_nn : 0 ≤ aK k := by dsimp only [aK]; positivity
              gcongr
          _ = aK k * ((2 : ℝ) ^ j * Real.exp 1 * ((1 + u) ^ j * Real.exp (-1 * u))) := by rw [mul_pow]; ring
      have hg_int : MeasureTheory.IntegrableOn (g k) (Set.Ioi 0) volume :=
        (integrableOn_hankel_ray zero_lt_one (2 - (j : ℂ) + chiFR k) sgn hsgn).const_mul (c k)
      have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] fun u =>
          aK k * ((2 : ℝ) ^ j * Real.exp 1 * ((1 + u) ^ j * Real.exp (-1 * u))) := by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : 0 < u := hu; dsimp only [aK]; positivity
      calc ∫⁻ u in Set.Ioi (0 : ℝ), ‖g k u‖ₑ
          ≤ ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (aK k * ((2 : ℝ) ^ j * Real.exp 1 * ((1 + u) ^ j * Real.exp (-1 * u)))) := by
            refine MeasureTheory.lintegral_mono_ae ?_
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hbound u hu)
        _ = ENNReal.ofReal (∫ u in Set.Ioi (0 : ℝ), aK k * ((2 : ℝ) ^ j * Real.exp 1 * ((1 + u) ^ j * Real.exp (-1 * u)))) :=
            (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hdom_int.const_mul (aK k)) hnn).symm
        _ = ENNReal.ofReal (aK k * ∫ u in Set.Ioi (0 : ℝ), (2 : ℝ) ^ j * Real.exp 1 * ((1 + u) ^ j * Real.exp (-1 * u))) := by
            rw [MeasureTheory.integral_const_mul]
    have hsum_ne_top : ∑' k : ℤ, ∫⁻ u in Set.Ioi (0 : ℝ), ‖g k u‖ₑ ≠ ⊤ := by
      let I0 : ℝ := ∫ u in Set.Ioi (0 : ℝ), (2 : ℝ) ^ j * Real.exp 1 * ((1 + u) ^ j * Real.exp (-1 * u))
      have hI0_nn : 0 ≤ I0 := MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun u hu => by
        have hu0 : 0 < u := hu; positivity
      have htsum_le : ∑' k : ℤ, ∫⁻ u in Set.Ioi (0 : ℝ), ‖g k u‖ₑ ≤
          ENNReal.ofReal (∑' k : ℤ, aK k * I0) := by
        calc ∑' k : ℤ, ∫⁻ u in Set.Ioi (0 : ℝ), ‖g k u‖ₑ
            ≤ ∑' k : ℤ, ENNReal.ofReal (aK k * I0) := tsum_le_tsum hlint_le
          _ = ENNReal.ofReal (∑' k : ℤ, aK k * I0) :=
              (ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (by dsimp only [aK]; positivity) hI0_nn)
                (haK_sum.mul_right I0)).symm
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top htsum_le
    exact MeasureTheory.integral_tsum hmeas hsum_ne_top
  -- Interchange `∫` and `∑' k : ℤ` on the vertical cap `y ∈ [-1, 1]`:
  have hcap_swap :
      (∫ y : ℝ in (-1 : ℝ)..(1 : ℝ),
        let ζ : ℂ := (1 : ℂ) + (y : ℂ) * I
        ζ ^ ((j : ℤ) - 2) * Complex.exp ζ *
          Psi_b b ((Complex.log (x : ℂ) - Complex.log ζ) / ((Real.log 2 : ℝ) : ℂ))) =
      ∑' k : ℤ, ∫ y : ℝ in (-1 : ℝ)..(1 : ℝ), F k ((1 : ℂ) + (y : ℂ) * I) := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    have hcongr : (∫ y in Set.Ioc (-1 : ℝ) (1 : ℝ),
        let ζ : ℂ := (1 : ℂ) + (y : ℂ) * I
        ζ ^ ((j : ℤ) - 2) * Complex.exp ζ *
          Psi_b b ((Complex.log (x : ℂ) - Complex.log ζ) / ((Real.log 2 : ℝ) : ℂ))) =
      ∫ y in Set.Ioc (-1 : ℝ) (1 : ℝ), ∑' k : ℤ, F k ((1 : ℂ) + (y : ℂ) * I) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
      let ζ : ℂ := (1 : ℂ) + (y : ℂ) * I
      have hre : ζ.re = 1 := by dsimp only [ζ]; simp
      have hne : ζ ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hre; norm_num at hre
      have harg : |ζ.arg| ≤ 3 * Real.pi / 4 := by
        have hlt : |ζ.arg| < Real.pi / 2 := abs_arg_lt_pi_div_two_of_re_pos (by linarith)
        linarith [Real.pi_pos]
      exact hpt_eq ζ hne harg
    rw [hcongr]
    let g : ℤ → ℝ → ℂ := fun k y => F k ((1 : ℂ) + (y : ℂ) * I)
    have hmeas : ∀ k : ℤ, MeasureTheory.AEStronglyMeasurable (g k) (volume.restrict (Set.Ioc (-1 : ℝ) 1)) := fun k => by
      have hcont : Continuous (g k) := continuous_iff_continuousAt.mpr fun y => by
        have hslit : (1 : ℂ) + (y : ℂ) * I ∈ Complex.slitPlane := Or.inl (by simp)
        have hlin : ContinuousAt (fun t : ℝ => (1 : ℂ) + (t : ℂ) * I) y := by fun_prop
        have hlog : ContinuousAt (fun t : ℝ => Complex.log ((1 : ℂ) + (t : ℂ) * I)) y :=
          ContinuousAt.comp (g := Complex.log) (Complex.hasDerivAt_log hslit).continuousAt hlin
        have hexp : ContinuousAt (fun t : ℝ => Complex.exp ((1 : ℂ) + (t : ℂ) * I)) y :=
          ContinuousAt.comp (g := Complex.exp) Complex.continuous_exp.continuousAt hlin
        exact continuousAt_const.mul (((hlog.const_mul (-(2 - (j : ℂ) + chiFR k))).cexp).mul hexp)
      exact hcont.aestronglyMeasurable
    have hlint_le : ∀ k : ℤ, ∫⁻ y in Set.Ioc (-1 : ℝ) 1, ‖g k y‖ₑ ≤
        ENNReal.ofReal (aK k * (2 * (2 : ℝ) ^ j * Real.exp 1)) := by
      intro k
      have hbound : ∀ y ∈ Set.Ioc (-1 : ℝ) 1, ‖g k y‖ ≤ aK k * ((2 : ℝ) ^ j * Real.exp 1) := fun y hy => by
        let ζ : ℂ := (1 : ℂ) + (y : ℂ) * I
        have hre : ζ.re = 1 := by dsimp only [ζ]; simp
        have h1 : 1 ≤ ‖ζ‖ := by rw [← hre]; exact Complex.re_le_norm ζ
        have h2 : ‖ζ‖ ≤ 2 := (Complex.norm_le_abs_re_add_abs_im ζ).trans (by
          have him : ζ.im = y := by dsimp only [ζ]; simp
          rw [hre, him, abs_one]; have : |y| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩; linarith)
        have harg : |ζ.arg| ≤ 3 * Real.pi / 4 := by
          have hlt : |ζ.arg| < Real.pi / 2 := abs_arg_lt_pi_div_two_of_re_pos (by linarith)
          linarith [Real.pi_pos]
        calc ‖g k y‖ ≤ aK k * (‖ζ‖ ^ j * Real.exp 1) := by simpa [g, ζ, hre] using hF_norm k ζ h1 harg
          _ ≤ aK k * ((2 : ℝ) ^ j * Real.exp 1) := by
              have haK_nn : 0 ≤ aK k := by dsimp only [aK]; positivity
              gcongr
      calc ∫⁻ y in Set.Ioc (-1 : ℝ) 1, ‖g k y‖ₑ
          ≤ ∫⁻ _y in Set.Ioc (-1 : ℝ) 1, ENNReal.ofReal (aK k * ((2 : ℝ) ^ j * Real.exp 1)) := by
            refine MeasureTheory.lintegral_mono_ae ?_
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hbound y hy)
        _ = ENNReal.ofReal (aK k * ((2 : ℝ) ^ j * Real.exp 1)) * volume (Set.Ioc (-1 : ℝ) 1) := by
            rw [MeasureTheory.setLIntegral_const]
        _ = ENNReal.ofReal (aK k * (2 * (2 : ℝ) ^ j * Real.exp 1)) := by
            rw [Real.volume_Ioc, show (1 : ℝ) - -1 = 2 by ring, ← ENNReal.ofReal_mul (by dsimp only [aK]; positivity)]
            congr 1; ring
    have hsum_ne_top : ∑' k : ℤ, ∫⁻ y in Set.Ioc (-1 : ℝ) 1, ‖g k y‖ₑ ≠ ⊤ := by
      have htsum_le : ∑' k : ℤ, ∫⁻ y in Set.Ioc (-1 : ℝ) 1, ‖g k y‖ₑ ≤
          ENNReal.ofReal (∑' k : ℤ, aK k * (2 * (2 : ℝ) ^ j * Real.exp 1)) := by
        calc ∑' k : ℤ, ∫⁻ y in Set.Ioc (-1 : ℝ) 1, ‖g k y‖ₑ
            ≤ ∑' k : ℤ, ENNReal.ofReal (aK k * (2 * (2 : ℝ) ^ j * Real.exp 1)) := tsum_le_tsum hlint_le
          _ = ENNReal.ofReal (∑' k : ℤ, aK k * (2 * (2 : ℝ) ^ j * Real.exp 1)) :=
              (ENNReal.ofReal_tsum_of_nonneg (fun k => by dsimp only [aK]; positivity)
                (haK_sum.mul_right _)).symm
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top htsum_le
    rw [MeasureTheory.integral_tsum hmeas hsum_ne_top]
    refine tsum_congr fun k => (intervalIntegral.integral_of_le (by norm_num)).symm
  -- Assemble the 3 swapped pieces into `∑' k : ℤ, c k * hankelIntegral (...)`!
  have hbot_swap :
      (∫ u in Set.Ioi (0 : ℝ),
        let ζ : ℂ := ((1 - u : ℝ) : ℂ) - ((1 + u : ℝ) : ℂ) * I
        ζ ^ ((j : ℤ) - 2) * Complex.exp ζ *
          Psi_b b ((Complex.log (x : ℂ) - Complex.log ζ) / ((Real.log 2 : ℝ) : ℂ))) =
      ∑' k : ℤ, ∫ u in Set.Ioi (0 : ℝ), F k (((1 - u : ℝ) : ℂ) - ((1 + u : ℝ) : ℂ) * I) := by
    have h := hray_swap (-1) (Or.inr rfl)
    convert h using 1
    · refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      have heq : ((1 - u : ℝ) : ℂ) - ((1 + u : ℝ) : ℂ) * I =
          ((1 - u : ℝ) : ℂ) + ((-1 * (1 + u) : ℝ) : ℂ) * I := by push_cast; ring
      dsimp only; rw [heq]
    · refine tsum_congr fun k => MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      congr 1; push_cast; ring
  have htop_swap :
      (∫ u in Set.Ioi (0 : ℝ),
        let ζ : ℂ := ((1 - u : ℝ) : ℂ) + ((1 + u : ℝ) : ℂ) * I
        ζ ^ ((j : ℤ) - 2) * Complex.exp ζ *
          Psi_b b ((Complex.log (x : ℂ) - Complex.log ζ) / ((Real.log 2 : ℝ) : ℂ))) =
      ∑' k : ℤ, ∫ u in Set.Ioi (0 : ℝ), F k (((1 - u : ℝ) : ℂ) + ((1 + u : ℝ) : ℂ) * I) := by
    simpa [one_mul] using hray_swap 1 (Or.inl rfl)
  -- Summability of each of the 3 `k`-series:
  have hsum_ray : ∀ (sgn : ℝ), sgn = 1 ∨ sgn = -1 →
      Summable (fun k : ℤ => ∫ u in Set.Ioi (0 : ℝ), F k (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I)) := by
    intro sgn hsgn
    let I0 : ℝ := ∫ u in Set.Ioi (0 : ℝ), (2 : ℝ) ^ j * Real.exp 1 * ((1 + u) ^ j * Real.exp (-1 * u))
    have hdom_int := (integrableOn_one_add_pow_mul_exp_neg j zero_lt_one).const_mul ((2 : ℝ) ^ j * Real.exp 1)
    refine Summable.of_norm_bounded (haK_sum.mul_right I0) fun k => ?_
    calc ‖∫ u in Set.Ioi (0 : ℝ), F k (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I)‖
        ≤ ∫ u in Set.Ioi (0 : ℝ), ‖F k (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I)‖ :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ u in Set.Ioi (0 : ℝ), aK k * ((2 : ℝ) ^ j * Real.exp 1 * ((1 + u) ^ j * Real.exp (-1 * u))) := by
          refine MeasureTheory.setIntegral_mono_on
            ((integrableOn_hankel_ray zero_lt_one (2 - (j : ℂ) + chiFR k) sgn hsgn).const_mul (c k)).norm
            (hdom_int.const_mul (aK k)) measurableSet_Ioi fun u hu => ?_
          obtain ⟨_, _, hlb, hub, harg⟩ := hankel_ray_props zero_lt_one (le_of_lt hu) sgn hsgn
          have h1 : 1 ≤ ‖((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I‖ := by linarith [show (0 : ℝ) < u from hu]
          have hre : (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I).re = 1 - u := by simp
          calc ‖F k (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I)‖
              ≤ aK k * (‖((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I‖ ^ j * Real.exp (1 - u)) := by
                simpa [hre] using hF_norm k _ h1 harg
            _ ≤ aK k * ((2 * (1 + u)) ^ j * (Real.exp 1 * Real.exp (-1 * u))) := by
                rw [show Real.exp (1 - u) = Real.exp 1 * Real.exp (-1 * u) by rw [← Real.exp_add]; congr 1; ring]
                have haK_nn : 0 ≤ aK k := by dsimp only [aK]; positivity
                gcongr
            _ = aK k * ((2 : ℝ) ^ j * Real.exp 1 * ((1 + u) ^ j * Real.exp (-1 * u))) := by rw [mul_pow]; ring
      _ = aK k * I0 := MeasureTheory.integral_const_mul _ _
  have hsum_bot : Summable (fun k : ℤ => ∫ u in Set.Ioi (0 : ℝ), F k (((1 - u : ℝ) : ℂ) - ((1 + u : ℝ) : ℂ) * I)) :=
    (hsum_ray (-1) (Or.inr rfl)).congr fun k => MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u _ => by
      congr 1; push_cast; ring
  have hsum_top : Summable (fun k : ℤ => ∫ u in Set.Ioi (0 : ℝ), F k (((1 - u : ℝ) : ℂ) + ((1 + u : ℝ) : ℂ) * I)) :=
    (hsum_ray 1 (Or.inl rfl)).congr fun k => MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u _ => by
      simp [one_mul]
  have hsum_cap : Summable (fun k : ℤ => ∫ y : ℝ in (-1 : ℝ)..(1 : ℝ), F k ((1 : ℂ) + (y : ℂ) * I)) := by
    refine Summable.of_norm_bounded (haK_sum.mul_right (2 * (2 : ℝ) ^ j * Real.exp 1)) fun k => ?_
    have hpt : ∀ y ∈ Set.uIoc (-1 : ℝ) 1, ‖F k ((1 : ℂ) + (y : ℂ) * I)‖ ≤ aK k * ((2 : ℝ) ^ j * Real.exp 1) := by
      intro y hy
      rw [Set.uIoc_of_le (by norm_num)] at hy
      let ζ : ℂ := (1 : ℂ) + (y : ℂ) * I
      have hre : ζ.re = 1 := by dsimp only [ζ]; simp
      have h1 : 1 ≤ ‖ζ‖ := by rw [← hre]; exact Complex.re_le_norm ζ
      have h2 : ‖ζ‖ ≤ 2 := (Complex.norm_le_abs_re_add_abs_im ζ).trans (by
        have him : ζ.im = y := by dsimp only [ζ]; simp
        rw [hre, him, abs_one]; have : |y| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩; linarith)
      have harg : |ζ.arg| ≤ 3 * Real.pi / 4 := by
        have hlt : |ζ.arg| < Real.pi / 2 := abs_arg_lt_pi_div_two_of_re_pos (by linarith)
        linarith [Real.pi_pos]
      calc ‖F k ζ‖ ≤ aK k * (‖ζ‖ ^ j * Real.exp 1) := by simpa [ζ, hre] using hF_norm k ζ h1 harg
        _ ≤ aK k * ((2 : ℝ) ^ j * Real.exp 1) := by
            have haK_nn : 0 ≤ aK k := by dsimp only [aK]; positivity
            gcongr
    calc ‖∫ y : ℝ in (-1 : ℝ)..(1 : ℝ), F k ((1 : ℂ) + (y : ℂ) * I)‖
        ≤ (aK k * ((2 : ℝ) ^ j * Real.exp 1)) * |(1 : ℝ) - (-1 : ℝ)| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hpt
      _ = aK k * (2 * (2 : ℝ) ^ j * Real.exp 1) := by
          rw [show (1 : ℝ) - -1 = 2 by ring, abs_of_pos (by norm_num)]; ring
  -- Combine into `∑' k : ℤ` and apply `hankelIntegral_cpow_exp`!
  have hcombine : (2 * (Real.pi : ℂ) * I)⁻¹ * hankelIntegral (fun ζ =>
        ζ ^ ((j : ℤ) - 2) * Complex.exp ζ *
          Psi_b b ((Complex.log (x : ℂ) - Complex.log ζ) / ((Real.log 2 : ℝ) : ℂ))) =
      ∑' k : ℤ, c k * ((2 * (Real.pi : ℂ) * I)⁻¹ *
        hankelIntegral (fun ζ => Complex.exp (-(2 - (j : ℂ) + chiFR k) * Complex.log ζ) * Complex.exp ζ)) := by
    unfold hankelIntegral hankelIntegralR
    simp only [Complex.ofReal_one]
    rw [hbot_swap, hcap_swap, htop_swap, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
      ← (hsum_bot.mul_left (1 + I)).tsum_add (hsum_cap.mul_left I),
      ← ((hsum_bot.mul_left (1 + I)).add (hsum_cap.mul_left I)).tsum_add (hsum_top.mul_left (-1 + I)),
      ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    dsimp only [F]
    rw [MeasureTheory.integral_const_mul, intervalIntegral.integral_const_mul, MeasureTheory.integral_const_mul]
    ring
  rw [hcombine]
  have hterm_eval : ∀ k : ℤ,
      c k * ((2 * (Real.pi : ℂ) * I)⁻¹ *
        hankelIntegral (fun ζ => Complex.exp (-(2 - (j : ℂ) + chiFR k) * Complex.log ζ) * Complex.exp ζ)) =
      vCoeff b j k * Complex.exp (chiFR k * Complex.log (x : ℂ)) := fun k => by
    rw [hankelIntegral_cpow_exp (2 - (j : ℂ) + chiFR k), vCoeff_eq_Psi_hat_div_Gamma]
    dsimp only [c]; rw [div_eq_mul_inv]; ring
  simp_rw [hterm_eval]
  rw [iteratedDeriv_v_b hb j (by simpa using hx), ← mul_assoc,
    ← zpow_add₀ (Complex.ofReal_ne_zero.mpr hx.ne'), show ((j : ℤ) - 1) + (1 - (j : ℤ)) = 0 by ring,
    zpow_zero, one_mul]

/-! ### All-Derivatives Asymptotic Matching: `x^{j-1} (frPoisson^{(j)}(x) - v_b^{(j)}(x)) = O_j(1/x)` -/

/-- **All-Derivatives Asymptotic Expansion of the Poissonized Flajolet–Richmond Function**:
for every `b ≥ 2` and every derivative order `j : ℕ`, there is `C ≥ 0` such that for ALL `x ≥ 2`,
`‖x^{j-1} · (frPoisson^{(j)}(x) - v_b^{(j)}(x))‖ ≤ C / x`. -/
theorem frPoisson_iteratedDeriv_asymptotic {b : ℕ} (hb : 2 ≤ b) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
      ‖(x : ℂ) ^ ((j : ℤ) - 1) *
          (iteratedDeriv j (fun t : ℝ => frPoisson b (t : ℂ)) x -
            iteratedDeriv j (v_b b) (x : ℂ))‖ ≤ C / x := by
  have hb1 : 1 ≤ b := by omega
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨M_Psi, hM_Psi_nn, hPsi_bd⟩ := norm_Psi_b_strip_le hb
  obtain ⟨M_R, hM_R_nn, hR_bd⟩ := L_b_inner_decomp hb
  obtain ⟨M_L, hM_L_nn, hL_bd⟩ := L_b_outer_bound hb1
  -- Compact range `x ∈ [2, 8]`: continuous function is bounded by some `M_0`.
  have hcont_28 : ContinuousOn (fun x : ℝ =>
      (x : ℂ) ^ ((j : ℤ) - 1) *
        (iteratedDeriv j (fun t : ℝ => frPoisson b (t : ℂ)) x -
          iteratedDeriv j (v_b b) (x : ℂ))) (Set.Icc (2 : ℝ) 8) := by
    have h1 : ContinuousOn (fun x : ℝ => (x : ℂ) ^ ((j : ℤ) - 1)) (Set.Icc (2 : ℝ) 8) :=
      ContinuousOn.zpow₀ Complex.continuous_ofReal.continuousOn _ fun x hx =>
        Or.inl (Complex.ofReal_ne_zero.mpr (by linarith [hx.1]))
    have h2 : ContinuousOn (fun x : ℝ => iteratedDeriv j (fun t : ℝ => frPoisson b (t : ℂ)) x) (Set.Icc (2 : ℝ) 8) := by
      have heq : (fun x : ℝ => iteratedDeriv j (fun t : ℝ => frPoisson b (t : ℂ)) x) =
          fun x : ℝ => iteratedDeriv j (frPoisson b) (x : ℂ) :=
        funext fun x => iteratedDeriv_comp_ofReal_eq_of_differentiable (frPoisson_differentiable hb1) j x
      rw [heq]
      have hd : Differentiable ℂ (iteratedDeriv j (frPoisson b)) :=
        ((frPoisson_differentiable hb1).contDiff (n := (⊤ : ℕ∞))).differentiable_iteratedDeriv j
          (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top j))
      exact (hd.continuous.comp Complex.continuous_ofReal).continuousOn
    have h3 : ContinuousOn (fun x : ℝ => iteratedDeriv j (v_b b) (x : ℂ)) (Set.Icc (2 : ℝ) 8) := by
      have hdiff_v : DifferentiableOn ℂ (iteratedDeriv j (v_b b)) {z : ℂ | 0 < z.re} := by
        intro z hz
        have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
        have heq_nhds : iteratedDeriv j (v_b b) =ᶠ[𝓝 z]
            fun w : ℂ => w ^ (1 - (j : ℤ)) * ∑' k : ℤ, vCoeff b j k * Complex.exp (chiFR k * Complex.log w) := by
          filter_upwards [hopen.mem_nhds hz] with w hw
          exact iteratedDeriv_v_b hb j hw
        obtain ⟨Cv, _, hbdv⟩ := norm_vCoeff_le hb j
        obtain ⟨_, _, hd_sum⟩ := hasDerivAt_tsum_chiFR hbdv hz
        have hz_ne : z ≠ 0 := fun h0 => by rw [h0] at hz; simp at hz
        have hd_pow := hasDerivAt_zpow (1 - (j : ℤ)) z (Or.inl hz_ne)
        exact ((hd_pow.mul hd_sum).congr_of_eventuallyEq heq_nhds).differentiableAt.differentiableWithinAt
      exact hdiff_v.continuousOn.comp Complex.continuous_ofReal.continuousOn fun x hx => by
        show 0 < ((x : ℂ)).re; rw [Complex.ofReal_re]; linarith [hx.1]
    exact h1.mul (h2.sub h3)
  obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_28
  -- Explicit finite integral constants for `x ≥ 8`:
  let J1 : ℝ := ∫ u in Set.Ioi (0 : ℝ), (1 + u) ^ j * Real.exp (-1 * u)
  let Jhalf : ℝ := ∫ u in Set.Ioi (0 : ℝ), (1 + u) ^ j * Real.exp (-(1 / 2 : ℝ) * u)
  have hJ1_nn : 0 ≤ J1 := MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun u hu => by
    have hu0 : 0 < u := hu; positivity
  have hJhalf_nn : 0 ≤ Jhalf := MeasureTheory.setIntegral_nonneg measurableSet_Ioi fun u hu => by
    have hu0 : 0 < u := hu; positivity
  let C_rem : ℝ := (2 * Real.pi)⁻¹ * (4 * (2 : ℝ) ^ j * Real.exp 1 * M_R * J1 + 2 * (2 : ℝ) ^ j * Real.exp 1 * M_R)
  let C_out : ℝ := (2 * Real.pi)⁻¹ * (15 * (5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ))
  let C_tail : ℝ := (2 * Real.pi)⁻¹ * (32 * (2 : ℝ) ^ j * Real.exp 1 * M_Psi * Jhalf)
  let C_all : ℝ := max (8 * max 0 M0) (C_rem + C_out + C_tail)
  refine ⟨C_all, le_trans (by positivity) (le_max_left _ _), fun x hx2 => ?_⟩
  by_cases hx8 : x ≤ 8
  · calc ‖(x : ℂ) ^ ((j : ℤ) - 1) *
            (iteratedDeriv j (fun t : ℝ => frPoisson b (t : ℂ)) x -
              iteratedDeriv j (v_b b) (x : ℂ))‖
        ≤ max 0 M0 := (hM0 x ⟨hx2, hx8⟩).trans (le_max_right _ _)
      _ = (x * max 0 M0) / x := by field_simp [show x ≠ 0 by linarith]
      _ ≤ (8 * max 0 M0) / x := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hx8 (le_max_left _ _)) (by linarith)
      _ ≤ C_all / x := div_le_div_of_nonneg_right (le_max_left _ _) (by linarith)
  · push Not at hx8
    have hx_pos : 0 < x := by linarith
    have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx_pos.ne'
    let r : ℝ := 1 / x
    have hr_pos : 0 < r := by dsimp only [r]; positivity
    have hr_le : r ≤ 1 / 8 := by
      dsimp only [r]; rw [div_le_div_iff₀ hx_pos (by norm_num)]; linarith
    have hr_le_half : r ≤ 1 / 2 := by linarith
    -- Express `frPoisson^{(j)}(x)` as `(2πi)⁻¹ * trapIntegral g r 2`:
    let g : ℂ → ℂ := fun ξ => ξ ^ j * Complex.exp ((x : ℂ) * ξ) * L_b b ξ
    have hg_diff : DifferentiableOn ℂ g SlitNegUnit :=
      ((differentiable_id.pow j).differentiableOn.mul
        ((differentiable_const (x : ℂ)).mul differentiable_id).cexp.differentiableOn).mul
        (L_b_differentiableOn_slitNegUnit hb1)
    have hfr_trap : iteratedDeriv j (fun t : ℝ => frPoisson b (t : ℂ)) x =
        (2 * (Real.pi : ℂ) * I)⁻¹ * trapIntegral g r 2 := by
      rw [iteratedDeriv_comp_ofReal_eq_of_differentiable (frPoisson_differentiable hb1) j x,
        iteratedDeriv_frPoisson_eq_rectIntegral hb1 j (x : ℂ)]
      congr 1
      have hR10 : (10 : ℝ) ≤ squareRadius b := by
        unfold squareRadius
        have h2b : 4 ≤ 2 ^ b := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
        have : (7 : ℝ) ≤ ((2 ^ b + 3 : ℕ) : ℝ) := by exact_mod_cast (show 7 ≤ 2 ^ b + 3 by omega)
        linarith
      exact rectIntegral_eq_trapIntegral hg_diff hR10 hr_pos hr_le_half
    -- Helper main integrand `H(ζ)` for `hankelIntegral`:
    let H : ℂ → ℂ := fun ζ => ζ ^ ((j : ℤ) - 2) * Complex.exp ζ *
      Psi_b b ((Complex.log (x : ℂ) - Complex.log ζ) / ((Real.log 2 : ℝ) : ℂ))
    have hv_hankel : (x : ℂ) ^ ((j : ℤ) - 1) * iteratedDeriv j (v_b b) (x : ℂ) =
        (2 * (Real.pi : ℂ) * I)⁻¹ * hankelIntegral H :=
      (hankelIntegral_Psi_b_eq_v_b hb j hx_pos).symm
    -- Integrability of `g` along the rays and edges of `trapIntegral g r 2`:
    have hint_ray_g : ∀ (sgn : ℝ), sgn = 1 ∨ sgn = -1 → ∀ (a₁ a₂ : ℝ), 0 ≤ a₁ → a₁ ≤ a₂ →
        IntervalIntegrable (fun s : ℝ => g (((r - s : ℝ) : ℂ) + ((sgn * (r + s) : ℝ) : ℂ) * I)) volume a₁ a₂ := by
      intro sgn hsgn a₁ a₂ ha₁ ha₁₂
      refine ContinuousOn.intervalIntegrable ?_
      refine hg_diff.continuousOn.comp
        (by fun_prop : Continuous fun s : ℝ => ((r - s : ℝ) : ℂ) + ((sgn * (r + s) : ℝ) : ℂ) * I).continuousOn
        fun s hs => ?_
      rw [Set.uIcc_of_le ha₁₂] at hs
      have him_ne : (((r - s : ℝ) : ℂ) + ((sgn * (r + s) : ℝ) : ℂ) * I).im ≠ 0 := by
        simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
        rcases hsgn with rfl | rfl <;> linarith [hs.1]
      intro hbad; exact him_ne hbad.1
    -- Split `trapIntegral g r 2` into inner rays `[0, 1/4]`, cap `[-r, r]`, outer rays `[1/4, 2]`, and left edge:
    have hbot_split :
        (∫ s : ℝ in (0 : ℝ)..(2 : ℝ), g (((r - s : ℝ) : ℂ) - ((r + s : ℝ) : ℂ) * I)) =
        (∫ s : ℝ in (0 : ℝ)..(1 / 4 : ℝ), g (((r - s : ℝ) : ℂ) - ((r + s : ℝ) : ℂ) * I)) +
        (∫ s : ℝ in (1 / 4 : ℝ)..(2 : ℝ), g (((r - s : ℝ) : ℂ) - ((r + s : ℝ) : ℂ) * I)) := by
      have hfn : (fun s : ℝ => g (((r - s : ℝ) : ℂ) + ((-1 * (r + s) : ℝ) : ℂ) * I)) =
          fun s : ℝ => g (((r - s : ℝ) : ℂ) - ((r + s : ℝ) : ℂ) * I) :=
        funext fun s => by congr 1; push_cast; ring
      have hi1 := hint_ray_g (-1) (Or.inr rfl) 0 (1 / 4) le_rfl (by norm_num)
      have hi2 := hint_ray_g (-1) (Or.inr rfl) (1 / 4) 2 (by norm_num) (by norm_num)
      rw [hfn] at hi1 hi2
      exact (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm
    have htop_split :
        (∫ s : ℝ in (0 : ℝ)..(2 : ℝ), g (((r - s : ℝ) : ℂ) + ((r + s : ℝ) : ℂ) * I)) =
        (∫ s : ℝ in (0 : ℝ)..(1 / 4 : ℝ), g (((r - s : ℝ) : ℂ) + ((r + s : ℝ) : ℂ) * I)) +
        (∫ s : ℝ in (1 / 4 : ℝ)..(2 : ℝ), g (((r - s : ℝ) : ℂ) + ((r + s : ℝ) : ℂ) * I)) := by
      have hi1 := hint_ray_g 1 (Or.inl rfl) 0 (1 / 4) le_rfl (by norm_num)
      have hi2 := hint_ray_g 1 (Or.inl rfl) (1 / 4) 2 (by norm_num) (by norm_num)
      simp only [one_mul] at hi1 hi2
      exact (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm
    -- Rescale the inner cap & inner rays by `u = x * s` (`s = u / x`):
    have hcap_rescale : (x : ℂ) ^ ((j : ℤ) - 1) * (∫ y : ℝ in (-r)..r, g ((r : ℂ) + (y : ℂ) * I)) =
        ∫ w : ℝ in (-1 : ℝ)..(1 : ℝ), (x : ℂ) ^ ((j : ℤ) - 2) * g (((1 : ℂ) + (w : ℂ) * I) / (x : ℂ)) := by
      have hdiv := intervalIntegral.integral_comp_div
        (fun y : ℝ => g ((r : ℂ) + (y : ℂ) * I)) hx_pos.ne' (a := (-1 : ℝ)) (b := (1 : ℝ))
      have ha_eq : (-1 : ℝ) / x = -r := by dsimp only [r]; ring
      have hb_eq : (1 : ℝ) / x = r := rfl
      rw [ha_eq, hb_eq, Complex.real_smul] at hdiv
      have h1 : (∫ y : ℝ in (-r)..r, g ((r : ℂ) + (y : ℂ) * I)) =
          (x : ℂ)⁻¹ * ∫ w : ℝ in (-1 : ℝ)..(1 : ℝ), g (((1 : ℂ) + (w : ℂ) * I) / (x : ℂ)) := by
        have hstep : (x : ℂ) * (∫ y : ℝ in (-r)..r, g ((r : ℂ) + (y : ℂ) * I)) =
            ∫ w : ℝ in (-1 : ℝ)..(1 : ℝ), g (((1 : ℂ) + (w : ℂ) * I) / (x : ℂ)) := by
          rw [← hdiv]
          refine intervalIntegral.integral_congr fun w _ => ?_
          congr 1; dsimp only [r]; push_cast; field_simp [hx_ne]
        exact mul_left_cancel₀ hx_ne (by rw [← mul_assoc, mul_inv_cancel₀ hx_ne, one_mul]; exact hstep)
      rw [h1, ← mul_assoc, ← zpow_sub_one₀ hx_ne,
        show ((j : ℤ) - 1) - 1 = (j : ℤ) - 2 by ring, ← intervalIntegral.integral_const_mul]
    have hray_rescale : ∀ (sgn : ℝ), sgn = 1 ∨ sgn = -1 →
        (x : ℂ) ^ ((j : ℤ) - 1) * (∫ s : ℝ in (0 : ℝ)..(1 / 4 : ℝ),
          g (((r - s : ℝ) : ℂ) + ((sgn * (r + s) : ℝ) : ℂ) * I)) =
        ∫ u : ℝ in (0 : ℝ)..(x / 4), (x : ℂ) ^ ((j : ℤ) - 2) *
          g ((((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I) / (x : ℂ)) := by
      intro sgn hsgn
      have hdiv := intervalIntegral.integral_comp_div
        (fun s : ℝ => g (((r - s : ℝ) : ℂ) + ((sgn * (r + s) : ℝ) : ℂ) * I)) hx_pos.ne'
        (a := (0 : ℝ)) (b := x / 4)
      have ha_eq : (0 : ℝ) / x = 0 := zero_div x
      have hb_eq : (x / 4) / x = 1 / 4 := by field_simp [hx_pos.ne']
      rw [ha_eq, hb_eq, Complex.real_smul] at hdiv
      have h1 : (∫ s : ℝ in (0 : ℝ)..(1 / 4 : ℝ), g (((r - s : ℝ) : ℂ) + ((sgn * (r + s) : ℝ) : ℂ) * I)) =
          (x : ℂ)⁻¹ * ∫ u : ℝ in (0 : ℝ)..(x / 4),
            g ((((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I) / (x : ℂ)) := by
        have hstep : (x : ℂ) * (∫ s : ℝ in (0 : ℝ)..(1 / 4 : ℝ),
              g (((r - s : ℝ) : ℂ) + ((sgn * (r + s) : ℝ) : ℂ) * I)) =
            ∫ u : ℝ in (0 : ℝ)..(x / 4),
              g ((((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I) / (x : ℂ)) := by
          rw [← hdiv]
          refine intervalIntegral.integral_congr fun u _ => ?_
          congr 1; dsimp only [r]; push_cast; field_simp [hx_ne]
        exact mul_left_cancel₀ hx_ne (by rw [← mul_assoc, mul_inv_cancel₀ hx_ne, one_mul]; exact hstep)
      rw [h1, ← mul_assoc, ← zpow_sub_one₀ hx_ne,
        show ((j : ℤ) - 1) - 1 = (j : ℤ) - 2 by ring, ← intervalIntegral.integral_const_mul]
    -- Pointwise difference `(x : ℂ)^(j-2) * g(ζ / x) - H(ζ)` bound for `1 ≤ ‖ζ‖ ≤ 3x/4`, `|ζ.arg| ≤ 3π/4`:
    have hinner_pt : ∀ ζ : ℂ, ζ ∈ Complex.slitPlane → 1 ≤ ‖ζ‖ → ‖ζ‖ ≤ 3 * x / 4 → |ζ.arg| ≤ 3 * Real.pi / 4 →
        ‖(x : ℂ) ^ ((j : ℤ) - 2) * g (ζ / (x : ℂ)) - H ζ‖ ≤
          (M_R / x) * (‖ζ‖ ^ j * Real.exp ζ.re) := by
      intro ζ hζ_slit hnorm1 hnorm_le harg
      have hζ_ne : ζ ≠ 0 := Complex.slitPlane_ne_zero hζ_slit
      let ξ : ℂ := ζ / (x : ℂ)
      have hξ_slit : ξ ∈ Complex.slitPlane := by
        dsimp only [ξ]
        rw [div_eq_mul_inv, ← Complex.ofReal_inv]
        rcases hζ_slit with hre | him
        · left; rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]; positivity
        · right; rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
          exact mul_ne_zero him (inv_ne_zero hx_pos.ne')
      have hξ_norm : ‖ξ‖ ≤ 3 / 4 := by
        dsimp only [ξ]; rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hx_pos.le]
        rw [div_le_iff₀ hx_pos]; linarith
      have hξ_arg : |ξ.arg| ≤ 3 * Real.pi / 4 := by
        have hlog_div : Complex.log ξ = Complex.log ζ - Complex.log (x : ℂ) :=
          Complex.log_div_ofReal_pos hζ_ne hx_pos
        have harg_eq : ξ.arg = ζ.arg := by
          have := congrArg Complex.im hlog_div
          rw [Complex.log_im, Complex.sub_im, Complex.log_im, Complex.log_im,
            Complex.arg_ofReal_of_nonneg hx_pos.le, sub_zero] at this
          exact this
        rw [harg_eq]; exact harg
      have hlog_neg : -Complex.log ξ = Complex.log (x : ℂ) - Complex.log ζ := by
        rw [Complex.log_div_ofReal_pos hζ_ne hx_pos]; ring
      have hrew : (x : ℂ) ^ ((j : ℤ) - 2) * g ξ - H ζ =
          (x : ℂ) ^ ((j : ℤ) - 2) * ξ ^ j * Complex.exp ζ *
            (L_b b ξ - ξ⁻¹ ^ 2 * Psi_b b (-Complex.log ξ / ((Real.log 2 : ℝ) : ℂ))) := by
        dsimp only [g, H]
        have hxξ : (x : ℂ) * ξ = ζ := mul_div_cancel₀ ζ hx_ne
        have hpow_main : (x : ℂ) ^ ((j : ℤ) - 2) * ξ ^ j * ξ⁻¹ ^ 2 = ζ ^ ((j : ℤ) - 2) := by
          dsimp only [ξ]
          rw [div_pow, inv_div, div_pow, zpow_sub₀ hζ_ne, zpow_sub₀ hx_ne, zpow_natCast, zpow_natCast,
            show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, zpow_natCast]
          field_simp [hζ_ne, hx_ne]
        calc (x : ℂ) ^ ((j : ℤ) - 2) * (ξ ^ j * Complex.exp ((x : ℂ) * ξ) * L_b b ξ) -
                ζ ^ ((j : ℤ) - 2) * Complex.exp ζ *
                  Psi_b b ((Complex.log (x : ℂ) - Complex.log ζ) / ((Real.log 2 : ℝ) : ℂ))
            = (x : ℂ) ^ ((j : ℤ) - 2) * ξ ^ j * Complex.exp ζ * L_b b ξ -
                ((x : ℂ) ^ ((j : ℤ) - 2) * ξ ^ j * ξ⁻¹ ^ 2) * Complex.exp ζ *
                  Psi_b b (-Complex.log ξ / ((Real.log 2 : ℝ) : ℂ)) := by
                rw [hxξ, hlog_neg, hpow_main]; ring
          _ = (x : ℂ) ^ ((j : ℤ) - 2) * ξ ^ j * Complex.exp ζ *
                (L_b b ξ - ξ⁻¹ ^ 2 * Psi_b b (-Complex.log ξ / ((Real.log 2 : ℝ) : ℂ))) := by ring
      rw [hrew, norm_mul, norm_mul, norm_mul, Complex.norm_exp ζ]
      have hR := hR_bd ξ hξ_slit hξ_norm hξ_arg
      have hξ_norm_eq : ‖ξ‖ = ‖ζ‖ / x := by
        dsimp only [ξ]; rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hx_pos.le]
      have hpow_pref : ‖(x : ℂ) ^ ((j : ℤ) - 2)‖ * ‖ξ ^ j‖ * ‖ξ‖⁻¹ = (1 / x) * ‖ζ‖ ^ ((j : ℤ) - 1) := by
        rw [norm_zpow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hx_pos.le, hξ_norm_eq,
          div_pow, inv_div, zpow_sub₀ hx_pos.ne', zpow_natCast, zpow_sub₀ (by linarith : ‖ζ‖ ≠ 0),
          zpow_natCast, zpow_one, show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast]
        field_simp [hx_pos.ne', show ‖ζ‖ ≠ 0 by linarith]
      have hnorm_jm1 : ‖ζ‖ ^ ((j : ℤ) - 1) ≤ ‖ζ‖ ^ j := by
        rw [← Real.rpow_intCast, ← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hnorm1 (by push_cast; linarith)
      calc ‖(x : ℂ) ^ ((j : ℤ) - 2)‖ * ‖ξ ^ j‖ * Real.exp ζ.re *
              ‖L_b b ξ - ξ⁻¹ ^ 2 * Psi_b b (-Complex.log ξ / ((Real.log 2 : ℝ) : ℂ))‖
          ≤ ‖(x : ℂ) ^ ((j : ℤ) - 2)‖ * ‖ξ ^ j‖ * Real.exp ζ.re * (M_R * ‖ξ‖⁻¹) :=
            mul_le_mul_of_nonneg_left hR (by positivity)
        _ = (‖(x : ℂ) ^ ((j : ℤ) - 2)‖ * ‖ξ ^ j‖ * ‖ξ‖⁻¹) * (M_R * Real.exp ζ.re) := by ring
        _ = ((1 / x) * ‖ζ‖ ^ ((j : ℤ) - 1)) * (M_R * Real.exp ζ.re) := by rw [hpow_pref]
        _ ≤ ((1 / x) * ‖ζ‖ ^ j) * (M_R * Real.exp ζ.re) := by gcongr
        _ = (M_R / x) * (‖ζ‖ ^ j * Real.exp ζ.re) := by ring
    -- Bound 1: Inner cap difference `I * ∫_{-1}^1 (x^{j-2} g((1+iw)/x) - H(1+iw)) dw`:
    have hrem_cap : ‖I * ((x : ℂ) ^ ((j : ℤ) - 1) * (∫ y : ℝ in (-r)..r, g ((r : ℂ) + (y : ℂ) * I)) -
        ∫ w : ℝ in (-1 : ℝ)..(1 : ℝ), H ((1 : ℂ) + (w : ℂ) * I))‖ ≤
        (2 * (2 : ℝ) ^ j * Real.exp 1 * M_R) / x := by
      rw [hcap_rescale, norm_mul, Complex.norm_I, one_mul]
      have hi1 : IntervalIntegrable (fun w : ℝ => (x : ℂ) ^ ((j : ℤ) - 2) * g (((1 : ℂ) + (w : ℂ) * I) / (x : ℂ)))
          volume (-1) 1 := by
        refine ContinuousOn.intervalIntegrable ?_
        refine continuousOn_const.mul (hg_diff.continuousOn.comp
          (by fun_prop : Continuous fun w : ℝ => ((1 : ℂ) + (w : ℂ) * I) / (x : ℂ)).continuousOn fun w _ => ?_)
        intro hbad
        have hre : (((1 : ℂ) + (w : ℂ) * I) / (x : ℂ)).re = 1 / x := by
          rw [Complex.div_ofReal_re]; simp
        linarith [hbad.2.2, hx_pos]
      have hi2 : IntervalIntegrable (fun w : ℝ => H ((1 : ℂ) + (w : ℂ) * I)) volume (-1) 1 := by
        refine ContinuousOn.intervalIntegrable fun w _ => ?_
        let ζ : ℂ := (1 : ℂ) + (w : ℂ) * I
        have hslit : ζ ∈ Complex.slitPlane := Or.inl (by dsimp only [ζ]; simp)
        have hne : ζ ≠ 0 := Complex.slitPlane_ne_zero hslit
        have hlin : ContinuousAt (fun t : ℝ => (1 : ℂ) + (t : ℂ) * I) w := by fun_prop
        have hlog : ContinuousAt (fun t : ℝ => Complex.log ((1 : ℂ) + (t : ℂ) * I)) w :=
          ContinuousAt.comp (g := Complex.log) (Complex.hasDerivAt_log hslit).continuousAt hlin
        have hexp : ContinuousAt (fun t : ℝ => Complex.exp ((1 : ℂ) + (t : ℂ) * I)) w :=
          ContinuousAt.comp (g := Complex.exp) Complex.continuous_exp.continuousAt hlin
        have hpow : ContinuousAt (fun t : ℝ => ((1 : ℂ) + (t : ℂ) * I) ^ ((j : ℤ) - 2)) w :=
          ContinuousAt.zpow₀ hlin _ (Or.inl hne)
        have hu_lt : |((Complex.log (x : ℂ) - Complex.log ζ) / ((Real.log 2 : ℝ) : ℂ)).im| <
            Real.pi / Real.log 2 := by
          have hlogx_im : (Complex.log (x : ℂ)).im = 0 := by
            rw [Complex.log_im, Complex.arg_ofReal_of_nonneg hx_pos.le]
          rw [Complex.div_ofReal_im, Complex.sub_im, hlogx_im, Complex.log_im, zero_sub, abs_div, abs_neg,
            abs_of_pos hlog2]
          have hlt : |ζ.arg| < Real.pi / 2 := abs_arg_lt_pi_div_two_of_re_pos (by dsimp only [ζ]; simp)
          rw [div_lt_div_iff₀ hlog2 hlog2]; nlinarith [Real.pi_pos, hlog2]
        have hPsi_cont : ContinuousAt (Psi_b b) ((Complex.log (x : ℂ) - Complex.log ζ) / ((Real.log 2 : ℝ) : ℂ)) :=
          (((Psi_b_differentiableOn hb1).mono fun v hv => mem_PsiDomain_of_abs_im_lt hv).continuousOn).continuousAt
            ((isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).mem_nhds hu_lt)
        have hu_cont : ContinuousAt (fun t : ℝ =>
            (Complex.log (x : ℂ) - Complex.log ((1 : ℂ) + (t : ℂ) * I)) / ((Real.log 2 : ℝ) : ℂ)) w :=
          (continuousAt_const.sub hlog).div_const _
        exact ((hpow.mul hexp).mul (ContinuousAt.comp (g := Psi_b b) hPsi_cont hu_cont)).continuousWithinAt
      rw [← intervalIntegral.integral_sub hi1 hi2]
      have hpt : ∀ w ∈ Set.uIoc (-1 : ℝ) 1,
          ‖(x : ℂ) ^ ((j : ℤ) - 2) * g (((1 : ℂ) + (w : ℂ) * I) / (x : ℂ)) - H ((1 : ℂ) + (w : ℂ) * I)‖ ≤
            ((2 : ℝ) ^ j * Real.exp 1 * M_R) / x := by
        intro w hw
        rw [Set.uIoc_of_le (by norm_num)] at hw
        let ζ : ℂ := (1 : ℂ) + (w : ℂ) * I
        have hre : ζ.re = 1 := by dsimp only [ζ]; simp
        have h1 : 1 ≤ ‖ζ‖ := by rw [← hre]; exact Complex.re_le_norm ζ
        have h2 : ‖ζ‖ ≤ 2 := (Complex.norm_le_abs_re_add_abs_im ζ).trans (by
          have him : ζ.im = w := by dsimp only [ζ]; simp
          rw [hre, him, abs_one]; have : |w| ≤ 1 := abs_le.mpr ⟨by linarith [hw.1], hw.2⟩; linarith)
        have harg : |ζ.arg| ≤ 3 * Real.pi / 4 := by
          have hlt : |ζ.arg| < Real.pi / 2 := abs_arg_lt_pi_div_two_of_re_pos (by linarith)
          linarith [Real.pi_pos]
        calc ‖(x : ℂ) ^ ((j : ℤ) - 2) * g (ζ / (x : ℂ)) - H ζ‖
            ≤ (M_R / x) * (‖ζ‖ ^ j * Real.exp 1) := by
              simpa [hre] using hinner_pt ζ (Or.inl (by linarith)) h1 (by linarith) harg
          _ ≤ (M_R / x) * ((2 : ℝ) ^ j * Real.exp 1) := by gcongr
          _ = ((2 : ℝ) ^ j * Real.exp 1 * M_R) / x := by ring
      calc ‖∫ w : ℝ in (-1 : ℝ)..(1 : ℝ),
              ((x : ℂ) ^ ((j : ℤ) - 2) * g (((1 : ℂ) + (w : ℂ) * I) / (x : ℂ)) - H ((1 : ℂ) + (w : ℂ) * I))‖
          ≤ (((2 : ℝ) ^ j * Real.exp 1 * M_R) / x) * |(1 : ℝ) - (-1 : ℝ)| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hpt
        _ = (2 * (2 : ℝ) ^ j * Real.exp 1 * M_R) / x := by
            rw [show (1 : ℝ) - -1 = 2 by ring, abs_of_pos (by norm_num)]; ring
    -- Integrability of `H` along the infinite Hankel rays:
    have hint_ray_H : ∀ (sgn : ℝ), sgn = 1 ∨ sgn = -1 →
        MeasureTheory.IntegrableOn (fun u : ℝ => H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I))
          (Set.Ioi 0) volume := by
      intro sgn hsgn
      have hcont : ContinuousOn (fun u : ℝ => H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I)) (Set.Ioi 0) := by
        intro u hu
        obtain ⟨hslit, hne, _, _, harg⟩ := hankel_ray_props zero_lt_one (le_of_lt hu) sgn hsgn
        let ζ : ℂ := ((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I
        have hlin : ContinuousAt (fun t : ℝ => ((1 - t : ℝ) : ℂ) + ((sgn * (1 + t) : ℝ) : ℂ) * I) u := by fun_prop
        have hlog : ContinuousAt (fun t : ℝ => Complex.log (((1 - t : ℝ) : ℂ) + ((sgn * (1 + t) : ℝ) : ℂ) * I)) u :=
          ContinuousAt.comp (g := Complex.log) (Complex.hasDerivAt_log hslit).continuousAt hlin
        have hexp : ContinuousAt (fun t : ℝ => Complex.exp (((1 - t : ℝ) : ℂ) + ((sgn * (1 + t) : ℝ) : ℂ) * I)) u :=
          ContinuousAt.comp (g := Complex.exp) Complex.continuous_exp.continuousAt hlin
        have hpow : ContinuousAt (fun t : ℝ => (((1 - t : ℝ) : ℂ) + ((sgn * (1 + t) : ℝ) : ℂ) * I) ^ ((j : ℤ) - 2)) u :=
          ContinuousAt.zpow₀ hlin _ (Or.inl hne)
        have hu_lt : |((Complex.log (x : ℂ) - Complex.log ζ) / ((Real.log 2 : ℝ) : ℂ)).im| <
            Real.pi / Real.log 2 := by
          have hlogx_im : (Complex.log (x : ℂ)).im = 0 := by
            rw [Complex.log_im, Complex.arg_ofReal_of_nonneg hx_pos.le]
          rw [Complex.div_ofReal_im, Complex.sub_im, hlogx_im, Complex.log_im, zero_sub, abs_div, abs_neg,
            abs_of_pos hlog2]
          calc |ζ.arg| / Real.log 2 ≤ (3 * Real.pi / 4) / Real.log 2 := div_le_div_of_nonneg_right harg hlog2.le
            _ < Real.pi / Real.log 2 := by
                rw [div_lt_div_iff₀ hlog2 hlog2]; nlinarith [Real.pi_pos, hlog2]
        have hPsi_cont : ContinuousAt (Psi_b b) ((Complex.log (x : ℂ) - Complex.log ζ) / ((Real.log 2 : ℝ) : ℂ)) :=
          (((Psi_b_differentiableOn hb1).mono fun v hv => mem_PsiDomain_of_abs_im_lt hv).continuousOn).continuousAt
            ((isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).mem_nhds hu_lt)
        have hu_cont : ContinuousAt (fun t : ℝ =>
            (Complex.log (x : ℂ) - Complex.log (((1 - t : ℝ) : ℂ) + ((sgn * (1 + t) : ℝ) : ℂ) * I)) /
              ((Real.log 2 : ℝ) : ℂ)) u :=
          (continuousAt_const.sub hlog).div_const _
        exact ((hpow.mul hexp).mul (ContinuousAt.comp (g := Psi_b b) hPsi_cont hu_cont)).continuousWithinAt
      refine ((integrableOn_one_add_pow_mul_exp_neg j zero_lt_one).const_mul ((2 : ℝ) ^ j * Real.exp 1 * M_Psi)).mono'
        (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : 0 < u := hu
      obtain ⟨_, hne, hlb, hub, harg⟩ := hankel_ray_props zero_lt_one hu0.le sgn hsgn
      let ζ : ℂ := ((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I
      have hre : ζ.re = 1 - u := by dsimp only [ζ]; simp
      have hnorm1 : 1 ≤ ‖ζ‖ := by linarith
      have hu_im : |((Complex.log (x : ℂ) - Complex.log ζ) / ((Real.log 2 : ℝ) : ℂ)).im| ≤
          3 * Real.pi / (4 * Real.log 2) := by
        have hlogx_im : (Complex.log (x : ℂ)).im = 0 := by
          rw [Complex.log_im, Complex.arg_ofReal_of_nonneg hx_pos.le]
        rw [Complex.div_ofReal_im, Complex.sub_im, hlogx_im, Complex.log_im, zero_sub, abs_div, abs_neg,
          abs_of_pos hlog2]
        calc |ζ.arg| / Real.log 2 ≤ (3 * Real.pi / 4) / Real.log 2 := div_le_div_of_nonneg_right harg hlog2.le
          _ = 3 * Real.pi / (4 * Real.log 2) := by ring
      have hpow_le : ‖ζ ^ ((j : ℤ) - 2)‖ ≤ (2 : ℝ) ^ j * (1 + u) ^ j := by
        rw [norm_zpow, ← Real.rpow_intCast]
        calc ‖ζ‖ ^ (((j : ℤ) - 2 : ℤ) : ℝ) ≤ ‖ζ‖ ^ (j : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hnorm1 (by push_cast; linarith)
          _ = ‖ζ‖ ^ j := Real.rpow_natCast _ _
          _ ≤ (2 * (1 + u)) ^ j := pow_le_pow_left₀ (norm_nonneg _) hub j
          _ = (2 : ℝ) ^ j * (1 + u) ^ j := mul_pow _ _ _
      change ‖ζ ^ ((j : ℤ) - 2) * Complex.exp ζ * Psi_b b _‖ ≤ _
      rw [norm_mul, norm_mul, Complex.norm_exp ζ, hre,
        show Real.exp (1 - u) = Real.exp 1 * Real.exp (-1 * u) by rw [← Real.exp_add]; congr 1; ring]
      calc ‖ζ ^ ((j : ℤ) - 2)‖ * (Real.exp 1 * Real.exp (-1 * u)) * ‖Psi_b b _‖
          ≤ ((2 : ℝ) ^ j * (1 + u) ^ j) * (Real.exp 1 * Real.exp (-1 * u)) * M_Psi := by
            exact mul_le_mul (mul_le_mul_of_nonneg_right hpow_le (by positivity))
              (hPsi_bd _ hu_im) (norm_nonneg _) (by positivity)
        _ = (2 : ℝ) ^ j * Real.exp 1 * M_Psi * ((1 + u) ^ j * Real.exp (-1 * u)) := by ring
    -- Bound 2 + 3: Inner ray difference + infinite Hankel tail for each ray `sgn = ±1`!
    have hray_diff_bd : ∀ (sgn : ℝ), sgn = 1 ∨ sgn = -1 →
        ‖(x : ℂ) ^ ((j : ℤ) - 1) * (∫ s : ℝ in (0 : ℝ)..(1 / 4 : ℝ),
            g (((r - s : ℝ) : ℂ) + ((sgn * (r + s) : ℝ) : ℂ) * I)) -
          ∫ u in Set.Ioi (0 : ℝ), H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I)‖ ≤
          ((2 : ℝ) ^ j * Real.exp 1 * M_R * J1 + 8 * (2 : ℝ) ^ j * Real.exp 1 * M_Psi * Jhalf) / x := by
      intro sgn hsgn
      rw [hray_rescale sgn hsgn]
      have hH_split :
          (∫ u in Set.Ioi (0 : ℝ), H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I)) =
          (∫ u : ℝ in (0 : ℝ)..(x / 4), H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I)) +
          (∫ u in Set.Ioi (x / 4), H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I)) := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        have hunion : Set.Ioi (0 : ℝ) = Set.Ioc 0 (x / 4) ∪ Set.Ioi (x / 4) :=
          (Set.Ioc_union_Ioi_eq_Ioi (by linarith)).symm
        have hdisj : Disjoint (Set.Ioc (0 : ℝ) (x / 4)) (Set.Ioi (x / 4)) :=
          Set.disjoint_left.mpr fun u hu1 hu2 => not_lt_of_ge hu1.2 hu2
        have hint_all := hint_ray_H sgn hsgn
        rw [hunion] at hint_all
        rw [hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
          (hint_all.mono_set Set.subset_union_left) (hint_all.mono_set Set.subset_union_right)]
      rw [hH_split, show (∫ u : ℝ in (0 : ℝ)..(x / 4), (x : ℂ) ^ ((j : ℤ) - 2) *
            g ((((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I) / (x : ℂ))) -
          ((∫ u : ℝ in (0 : ℝ)..(x / 4), H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I)) +
           (∫ u in Set.Ioi (x / 4), H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I))) =
          ((∫ u : ℝ in (0 : ℝ)..(x / 4), (x : ℂ) ^ ((j : ℤ) - 2) *
            g ((((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I) / (x : ℂ))) -
           (∫ u : ℝ in (0 : ℝ)..(x / 4), H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I))) -
          (∫ u in Set.Ioi (x / 4), H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I)) by ring]
      -- Inner `[0, x/4]` remainder bound:
      have hbd_in : ‖(∫ u : ℝ in (0 : ℝ)..(x / 4), (x : ℂ) ^ ((j : ℤ) - 2) *
              g ((((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I) / (x : ℂ))) -
            (∫ u : ℝ in (0 : ℝ)..(x / 4), H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I))‖ ≤
          ((2 : ℝ) ^ j * Real.exp 1 * M_R * J1) / x := by
        rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith)]
        have hi_g : MeasureTheory.IntegrableOn
            (fun u : ℝ => (x : ℂ) ^ ((j : ℤ) - 2) * g ((((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I) / (x : ℂ)))
            (Set.Ioc 0 (x / 4)) volume := by
          refine (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
            (ContinuousOn.intervalIntegrable ?_)
          refine continuousOn_const.mul (hg_diff.continuousOn.comp
            (by fun_prop : Continuous fun u : ℝ =>
              (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I) / (x : ℂ)).continuousOn fun u hu => ?_)
          rw [Set.uIcc_of_le (by linarith)] at hu
          have him_ne : ((((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I) / (x : ℂ)).im ≠ 0 := by
            rw [Complex.div_ofReal_im]
            simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im, Complex.ofReal_re,
              Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
            refine div_ne_zero ?_ hx_pos.ne'
            rcases hsgn with rfl | rfl <;> linarith [hu.1]
          intro hbad; exact him_ne hbad.1
        have hi_H : MeasureTheory.IntegrableOn
            (fun u : ℝ => H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I))
            (Set.Ioc 0 (x / 4)) volume :=
          (hint_ray_H sgn hsgn).mono_set (fun u hu => hu.1)
        rw [← MeasureTheory.integral_sub hi_g hi_H]
        have hdom_J1 : MeasureTheory.IntegrableOn
            (fun u : ℝ => ((2 : ℝ) ^ j * Real.exp 1 * M_R / x) * ((1 + u) ^ j * Real.exp (-1 * u)))
            (Set.Ioi 0) volume :=
          (integrableOn_one_add_pow_mul_exp_neg j zero_lt_one).const_mul _
        calc ‖∫ u in Set.Ioc (0 : ℝ) (x / 4),
                ((x : ℂ) ^ ((j : ℤ) - 2) * g ((((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I) / (x : ℂ)) -
                 H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I))‖
            ≤ ∫ u in Set.Ioc (0 : ℝ) (x / 4),
                ‖(x : ℂ) ^ ((j : ℤ) - 2) * g ((((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I) / (x : ℂ)) -
                 H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I)‖ :=
              MeasureTheory.norm_integral_le_integral_norm _
          _ ≤ ∫ u in Set.Ioc (0 : ℝ) (x / 4),
                ((2 : ℝ) ^ j * Real.exp 1 * M_R / x) * ((1 + u) ^ j * Real.exp (-1 * u)) := by
              refine MeasureTheory.setIntegral_mono_on (hi_g.sub hi_H).norm
                (hdom_J1.mono_set (fun u hu => hu.1)) measurableSet_Ioc fun u hu => ?_
              obtain ⟨hslit, _, hlb, hub, harg⟩ := hankel_ray_props zero_lt_one (le_of_lt hu.1) sgn hsgn
              let ζ : ℂ := ((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I
              have hre : ζ.re = 1 - u := by dsimp only [ζ]; simp
              have hnorm1 : 1 ≤ ‖ζ‖ := by linarith [hu.1]
              have hnorm_le : ‖ζ‖ ≤ 3 * x / 4 := by
                calc ‖ζ‖ ≤ 2 * (1 + u) := hub
                  _ ≤ 2 * (1 + x / 4) := by linarith [hu.2]
                  _ ≤ 3 * x / 4 := by linarith
              calc ‖(x : ℂ) ^ ((j : ℤ) - 2) * g (ζ / (x : ℂ)) - H ζ‖
                  ≤ (M_R / x) * (‖ζ‖ ^ j * Real.exp (1 - u)) := by
                    simpa [hre] using hinner_pt ζ hslit hnorm1 hnorm_le harg
                _ ≤ (M_R / x) * ((2 * (1 + u)) ^ j * (Real.exp 1 * Real.exp (-1 * u))) := by
                    rw [show 1 - u = 1 + (-1 * u) by ring, Real.exp_add]
                    have hu0 : 0 < u := hu.1
                    gcongr
                _ = ((2 : ℝ) ^ j * Real.exp 1 * M_R / x) * ((1 + u) ^ j * Real.exp (-1 * u)) := by
                    rw [mul_pow]; ring
          _ ≤ ∫ u in Set.Ioi (0 : ℝ),
                ((2 : ℝ) ^ j * Real.exp 1 * M_R / x) * ((1 + u) ^ j * Real.exp (-1 * u)) := by
              refine MeasureTheory.setIntegral_mono_set hdom_J1 ?_
                (Filter.Eventually.of_forall fun u hu => hu.1)
              filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
              have hu0 : 0 < u := hu; positivity
          _ = ((2 : ℝ) ^ j * Real.exp 1 * M_R * J1) / x := by
              rw [MeasureTheory.integral_const_mul]; dsimp only [J1]; ring
      -- Infinite tail `u ∈ (x/4, ∞)` bound:
      have hbd_tail : ‖∫ u in Set.Ioi (x / 4),
            H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I)‖ ≤
          (8 * (2 : ℝ) ^ j * Real.exp 1 * M_Psi * Jhalf) / x := by
        have hdom_half : MeasureTheory.IntegrableOn
            (fun u : ℝ => (8 * (2 : ℝ) ^ j * Real.exp 1 * M_Psi / x) * ((1 + u) ^ j * Real.exp (-(1 / 2 : ℝ) * u)))
            (Set.Ioi 0) volume :=
          (integrableOn_one_add_pow_mul_exp_neg j (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _
        have hi_tail : MeasureTheory.IntegrableOn
            (fun u : ℝ => H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I))
            (Set.Ioi (x / 4)) volume :=
          (hint_ray_H sgn hsgn).mono_set (fun u hu => lt_trans (by linarith : (0 : ℝ) < x / 4) hu)
        have hexp_x8 : Real.exp (-(x / 8)) ≤ 8 / x := by
          have h1 : x / 8 ≤ Real.exp (x / 8) := by linarith [Real.add_one_le_exp (x / 8)]
          rw [Real.exp_neg]
          calc (Real.exp (x / 8))⁻¹ ≤ (x / 8)⁻¹ := inv_anti₀ (by linarith) h1
            _ = 8 / x := by field_simp [hx_pos.ne']
        calc ‖∫ u in Set.Ioi (x / 4), H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I)‖
            ≤ ∫ u in Set.Ioi (x / 4), ‖H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I)‖ :=
              MeasureTheory.norm_integral_le_integral_norm _
          _ ≤ ∫ u in Set.Ioi (x / 4),
                (8 * (2 : ℝ) ^ j * Real.exp 1 * M_Psi / x) * ((1 + u) ^ j * Real.exp (-(1 / 2 : ℝ) * u)) := by
              refine MeasureTheory.setIntegral_mono_on hi_tail.norm
                (hdom_half.mono_set (fun u hu => lt_trans (by linarith) hu)) measurableSet_Ioi fun u hu => ?_
              have hu_gt : x / 4 < u := hu
              have hu0 : 0 < u := lt_trans (by linarith) hu_gt
              obtain ⟨_, _, hlb, hub, harg⟩ := hankel_ray_props zero_lt_one hu0.le sgn hsgn
              let ζ : ℂ := ((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I
              have hre : ζ.re = 1 - u := by dsimp only [ζ]; simp
              have hnorm1 : 1 ≤ ‖ζ‖ := by linarith
              have hu_im : |((Complex.log (x : ℂ) - Complex.log ζ) / ((Real.log 2 : ℝ) : ℂ)).im| ≤
                  3 * Real.pi / (4 * Real.log 2) := by
                have hlogx_im : (Complex.log (x : ℂ)).im = 0 := by
                  rw [Complex.log_im, Complex.arg_ofReal_of_nonneg hx_pos.le]
                rw [Complex.div_ofReal_im, Complex.sub_im, hlogx_im, Complex.log_im, zero_sub, abs_div, abs_neg,
                  abs_of_pos hlog2]
                calc |ζ.arg| / Real.log 2 ≤ (3 * Real.pi / 4) / Real.log 2 := div_le_div_of_nonneg_right harg hlog2.le
                  _ = 3 * Real.pi / (4 * Real.log 2) := by ring
              have hpow_le : ‖ζ ^ ((j : ℤ) - 2)‖ ≤ (2 : ℝ) ^ j * (1 + u) ^ j := by
                rw [norm_zpow, ← Real.rpow_intCast]
                calc ‖ζ‖ ^ (((j : ℤ) - 2 : ℤ) : ℝ) ≤ ‖ζ‖ ^ (j : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le hnorm1 (by push_cast; linarith)
                  _ = ‖ζ‖ ^ j := Real.rpow_natCast _ _
                  _ ≤ (2 * (1 + u)) ^ j := pow_le_pow_left₀ (norm_nonneg _) hub j
                  _ = (2 : ℝ) ^ j * (1 + u) ^ j := mul_pow _ _ _
              have hexp_split : Real.exp (1 - u) ≤ Real.exp 1 * (8 / x) * Real.exp (-(1 / 2 : ℝ) * u) := by
                have h1 : Real.exp (1 - u) = Real.exp 1 * Real.exp (-(u / 2)) * Real.exp (-(1 / 2 : ℝ) * u) := by
                  rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
                have h2 : Real.exp (-(u / 2)) ≤ Real.exp (-(x / 8)) :=
                  Real.exp_le_exp.mpr (by linarith)
                rw [h1]
                calc Real.exp 1 * Real.exp (-(u / 2)) * Real.exp (-(1 / 2 : ℝ) * u)
                    ≤ Real.exp 1 * Real.exp (-(x / 8)) * Real.exp (-(1 / 2 : ℝ) * u) := by gcongr
                  _ ≤ Real.exp 1 * (8 / x) * Real.exp (-(1 / 2 : ℝ) * u) := by gcongr
              change ‖ζ ^ ((j : ℤ) - 2) * Complex.exp ζ * Psi_b b _‖ ≤ _
              rw [norm_mul, norm_mul, Complex.norm_exp ζ, hre]
              calc ‖ζ ^ ((j : ℤ) - 2)‖ * Real.exp (1 - u) * ‖Psi_b b _‖
                  ≤ ((2 : ℝ) ^ j * (1 + u) ^ j) * (Real.exp 1 * (8 / x) * Real.exp (-(1 / 2 : ℝ) * u)) * M_Psi := by
                    exact mul_le_mul (mul_le_mul hpow_le hexp_split (Real.exp_pos _).le (by positivity))
                      (hPsi_bd _ hu_im) (norm_nonneg _) (by positivity)
                _ = (8 * (2 : ℝ) ^ j * Real.exp 1 * M_Psi / x) * ((1 + u) ^ j * Real.exp (-(1 / 2 : ℝ) * u)) := by ring
          _ ≤ ∫ u in Set.Ioi (0 : ℝ),
                (8 * (2 : ℝ) ^ j * Real.exp 1 * M_Psi / x) * ((1 + u) ^ j * Real.exp (-(1 / 2 : ℝ) * u)) := by
              refine MeasureTheory.setIntegral_mono_set hdom_half ?_
                (Filter.Eventually.of_forall fun u hu => lt_trans (by linarith) hu)
              filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
              have hu0 : 0 < u := hu; positivity
          _ = (8 * (2 : ℝ) ^ j * Real.exp 1 * M_Psi * Jhalf) / x := by
              rw [MeasureTheory.integral_const_mul]; dsimp only [Jhalf]; ring
      calc ‖((∫ u : ℝ in (0 : ℝ)..(x / 4), (x : ℂ) ^ ((j : ℤ) - 2) *
              g ((((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I) / (x : ℂ))) -
             (∫ u : ℝ in (0 : ℝ)..(x / 4), H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I))) -
            (∫ u in Set.Ioi (x / 4), H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I))‖
          ≤ ‖(∫ u : ℝ in (0 : ℝ)..(x / 4), (x : ℂ) ^ ((j : ℤ) - 2) *
                g ((((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I) / (x : ℂ))) -
              (∫ u : ℝ in (0 : ℝ)..(x / 4), H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I))‖ +
            ‖∫ u in Set.Ioi (x / 4), H (((1 - u : ℝ) : ℂ) + ((sgn * (1 + u) : ℝ) : ℂ) * I)‖ := norm_sub_le _ _
        _ ≤ ((2 : ℝ) ^ j * Real.exp 1 * M_R * J1) / x +
            (8 * (2 : ℝ) ^ j * Real.exp 1 * M_Psi * Jhalf) / x := add_le_add hbd_in hbd_tail
        _ = ((2 : ℝ) ^ j * Real.exp 1 * M_R * J1 + 8 * (2 : ℝ) ^ j * Real.exp 1 * M_Psi * Jhalf) / x := by ring
    -- Bound 4: Outer slanted rays (`s ∈ [1/4, 2]`) + Left vertical edge (`Re ξ = r - 2`):
    have hpow_exp_x8 : x ^ ((j : ℤ) - 1) * Real.exp (-(x / 8)) ≤
        ((8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)) / x := by
      have h1 : (x / 8) ^ (j + 1) ≤ Real.exp (x / 8) * ((j + 1).factorial : ℝ) :=
        (div_le_iff₀ (by positivity)).mp (Real.pow_div_factorial_le_exp (x / 8) (by linarith) (j + 1))
      have h2 : x ^ (j + 1) * Real.exp (-(x / 8)) ≤ (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ) := by
        rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
        have hx8_pow : x ^ (j + 1) = (8 : ℝ) ^ (j + 1) * (x / 8) ^ (j + 1) := by
          rw [← mul_pow]; congr 1; ring
        rw [hx8_pow]
        calc (8 : ℝ) ^ (j + 1) * (x / 8) ^ (j + 1)
            ≤ (8 : ℝ) ^ (j + 1) * (Real.exp (x / 8) * ((j + 1).factorial : ℝ)) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ) * Real.exp (x / 8) := by ring
      have hx_jm1 : x ^ ((j : ℤ) - 1) ≤ x ^ j := by
        rw [← Real.rpow_intCast, ← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
      rw [le_div_iff₀ hx_pos]
      calc x ^ ((j : ℤ) - 1) * Real.exp (-(x / 8)) * x
          ≤ x ^ j * Real.exp (-(x / 8)) * x := by gcongr
        _ = x ^ (j + 1) * Real.exp (-(x / 8)) := by rw [pow_succ]; ring
        _ ≤ (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ) := h2
    have houter_pt : ∀ ξ : ℂ, ‖ξ‖ ≤ 5 → ξ.re ≤ -1 / 8 → (ξ.re ≤ -3 / 2 ∨ 1 / 4 ≤ |ξ.im|) →
        ‖(x : ℂ) ^ ((j : ℤ) - 1) * g ξ‖ ≤
          ((5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)) / x := by
      intro ξ hnorm5 hre8 hK
      dsimp only [g]
      rw [norm_mul, norm_mul, norm_mul, norm_zpow, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg hx_pos.le, Complex.norm_exp ((x : ℂ) * ξ)]
      have hre_prod : ((x : ℂ) * ξ).re = x * ξ.re := by simp
      rw [hre_prod]
      have hexp_le : Real.exp (x * ξ.re) ≤ Real.exp (-(x / 8)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have hpow5 : ‖ξ‖ ^ j ≤ (5 : ℝ) ^ j := pow_le_pow_left₀ (norm_nonneg _) hnorm5 j
      have hL5 : ‖L_b b ξ‖ ≤ M_L := hL_bd ξ hnorm5 hK
      calc x ^ ((j : ℤ) - 1) * (‖ξ‖ ^ j * Real.exp (x * ξ.re) * ‖L_b b ξ‖)
          = (‖ξ‖ ^ j * ‖L_b b ξ‖) * (x ^ ((j : ℤ) - 1) * Real.exp (x * ξ.re)) := by ring
        _ ≤ ((5 : ℝ) ^ j * M_L) * (x ^ ((j : ℤ) - 1) * Real.exp (-(x / 8))) := by
            refine mul_le_mul (mul_le_mul hpow5 hL5 (norm_nonneg _) (by positivity))
              (mul_le_mul_of_nonneg_left hexp_le (zpow_nonneg hx_pos.le _)) (by positivity) (by positivity)
        _ ≤ ((5 : ℝ) ^ j * M_L) * (((8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)) / x) :=
            mul_le_mul_of_nonneg_left hpow_exp_x8 (by positivity)
        _ = ((5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)) / x := by ring
    have houter_ray : ∀ (sgn : ℝ), sgn = 1 ∨ sgn = -1 →
        ‖(x : ℂ) ^ ((j : ℤ) - 1) * ∫ s : ℝ in (1 / 4 : ℝ)..(2 : ℝ),
            g (((r - s : ℝ) : ℂ) + ((sgn * (r + s) : ℝ) : ℂ) * I)‖ ≤
          (2 * (5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)) / x := by
      intro sgn hsgn
      rw [← intervalIntegral.integral_const_mul]
      have hpt : ∀ s ∈ Set.uIoc (1 / 4 : ℝ) 2,
          ‖(x : ℂ) ^ ((j : ℤ) - 1) * g (((r - s : ℝ) : ℂ) + ((sgn * (r + s) : ℝ) : ℂ) * I)‖ ≤
            ((5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)) / x := by
        intro s hs
        rw [Set.uIoc_of_le (by norm_num)] at hs
        let ζ : ℂ := ((r - s : ℝ) : ℂ) + ((sgn * (r + s) : ℝ) : ℂ) * I
        have hre : ζ.re = r - s := by dsimp only [ζ]; simp
        have him : ζ.im = sgn * (r + s) := by dsimp only [ζ]; simp
        have hnorm5 : ‖ζ‖ ≤ 5 := (Complex.norm_le_abs_re_add_abs_im ζ).trans (by
          rw [hre, him]
          have h1 : |r - s| ≤ 2 := abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩
          have h2 : |sgn * (r + s)| ≤ 3 := by
            rw [abs_mul]; rcases hsgn with rfl | rfl <;>
              (simp only [abs_one, abs_neg, one_mul]; rw [abs_of_pos (by linarith [hs.1])]; linarith [hs.2])
          linarith)
        have hre8 : ζ.re ≤ -1 / 8 := by rw [hre]; linarith [hs.1]
        have him4 : 1 / 4 ≤ |ζ.im| := by
          rw [him, abs_mul]
          rcases hsgn with rfl | rfl <;>
            (simp only [abs_one, abs_neg, one_mul]; rw [abs_of_pos (by linarith [hs.1])]; linarith [hs.1])
        exact houter_pt ζ hnorm5 hre8 (Or.inr him4)
      calc ‖∫ s : ℝ in (1 / 4 : ℝ)..(2 : ℝ), (x : ℂ) ^ ((j : ℤ) - 1) *
              g (((r - s : ℝ) : ℂ) + ((sgn * (r + s) : ℝ) : ℂ) * I)‖
          ≤ (((5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)) / x) * |(2 : ℝ) - 1 / 4| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hpt
        _ ≤ (((5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)) / x) * 2 := by
            have habs : |(2 : ℝ) - 1 / 4| ≤ 2 := by norm_num
            exact mul_le_mul_of_nonneg_left habs (by positivity)
        _ = (2 * (5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)) / x := by ring
    have houter_left :
        ‖(x : ℂ) ^ ((j : ℤ) - 1) * (I * ∫ y : ℝ in (-(r + 2))..(r + 2),
            g (((r - 2 : ℝ) : ℂ) + (y : ℂ) * I))‖ ≤
          (5 * (5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)) / x := by
      rw [show (x : ℂ) ^ ((j : ℤ) - 1) * (I * ∫ y : ℝ in (-(r + 2))..(r + 2), g (((r - 2 : ℝ) : ℂ) + (y : ℂ) * I)) =
          I * ∫ y : ℝ in (-(r + 2))..(r + 2), (x : ℂ) ^ ((j : ℤ) - 1) * g (((r - 2 : ℝ) : ℂ) + (y : ℂ) * I) by
          rw [intervalIntegral.integral_const_mul]; ring, norm_mul, Complex.norm_I, one_mul]
      have hpt : ∀ y ∈ Set.uIoc (-(r + 2)) (r + 2),
          ‖(x : ℂ) ^ ((j : ℤ) - 1) * g (((r - 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
            ((5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)) / x := by
        intro y hy
        rw [Set.uIoc_of_le (by linarith)] at hy
        let ζ : ℂ := ((r - 2 : ℝ) : ℂ) + (y : ℂ) * I
        have hre : ζ.re = r - 2 := by dsimp only [ζ]; simp
        have him : ζ.im = y := by dsimp only [ζ]; simp
        have hnorm5 : ‖ζ‖ ≤ 5 := (Complex.norm_le_abs_re_add_abs_im ζ).trans (by
          rw [hre, him]
          have h1 : |r - 2| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
          have h2 : |y| ≤ r + 2 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
          linarith)
        exact houter_pt ζ hnorm5 (by rw [hre]; linarith) (Or.inl (by rw [hre]; linarith))
      calc ‖∫ y : ℝ in (-(r + 2))..(r + 2), (x : ℂ) ^ ((j : ℤ) - 1) * g (((r - 2 : ℝ) : ℂ) + (y : ℂ) * I)‖
          ≤ (((5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)) / x) * |(r + 2) - -(r + 2)| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hpt
        _ ≤ (((5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)) / x) * 5 := by
            have habs : |(r + 2) - -(r + 2)| ≤ 5 := by
              rw [sub_neg_eq_add, abs_of_pos (by linarith)]; linarith
            exact mul_le_mul_of_nonneg_left habs (by positivity)
        _ = (5 * (5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)) / x := by ring
    -- Combine ALL 5 error terms with `‖1 + I‖ ≤ 2`, `‖-1 + I‖ ≤ 2`, `‖(2πi)⁻¹‖ = (2π)⁻¹`!
    have hnorm_1pI : ‖(1 : ℂ) + I‖ ≤ 2 := (norm_add_le _ _).trans (by simp; norm_num)
    have hnorm_m1pI : ‖(-1 : ℂ) + I‖ ≤ 2 := (norm_add_le _ _).trans (by simp; norm_num)
    have hnorm_2piI : ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
      rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    have hbot_diff := hray_diff_bd (-1) (Or.inr rfl)
    have htop_diff := hray_diff_bd 1 (Or.inl rfl)
    have hbot_diff' : ‖(x : ℂ) ^ ((j : ℤ) - 1) * (∫ s : ℝ in (0 : ℝ)..(1 / 4 : ℝ),
            g (((r - s : ℝ) : ℂ) - ((r + s : ℝ) : ℂ) * I)) -
          ∫ u in Set.Ioi (0 : ℝ), H (((1 - u : ℝ) : ℂ) - ((1 + u : ℝ) : ℂ) * I)‖ ≤
          ((2 : ℝ) ^ j * Real.exp 1 * M_R * J1 + 8 * (2 : ℝ) ^ j * Real.exp 1 * M_Psi * Jhalf) / x := by
      convert hbot_diff using 2
      congr 1
      · congr 1; refine intervalIntegral.integral_congr fun s _ => ?_; congr 1; push_cast; ring
      · refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_; congr 1; push_cast; ring
    have htop_diff' : ‖(x : ℂ) ^ ((j : ℤ) - 1) * (∫ s : ℝ in (0 : ℝ)..(1 / 4 : ℝ),
            g (((r - s : ℝ) : ℂ) + ((r + s : ℝ) : ℂ) * I)) -
          ∫ u in Set.Ioi (0 : ℝ), H (((1 - u : ℝ) : ℂ) + ((1 + u : ℝ) : ℂ) * I)‖ ≤
          ((2 : ℝ) ^ j * Real.exp 1 * M_R * J1 + 8 * (2 : ℝ) ^ j * Real.exp 1 * M_Psi * Jhalf) / x := by
      simpa [one_mul] using htop_diff
    have houter_bot' : ‖(x : ℂ) ^ ((j : ℤ) - 1) * (∫ s : ℝ in (1 / 4 : ℝ)..(2 : ℝ),
            g (((r - s : ℝ) : ℂ) - ((r + s : ℝ) : ℂ) * I))‖ ≤
          (2 * (5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)) / x := by
      convert houter_ray (-1) (Or.inr rfl) using 2
      congr 1; refine intervalIntegral.integral_congr fun s _ => ?_; congr 1; push_cast; ring
    have houter_top' : ‖(x : ℂ) ^ ((j : ℤ) - 1) * (∫ s : ℝ in (1 / 4 : ℝ)..(2 : ℝ),
            g (((r - s : ℝ) : ℂ) + ((r + s : ℝ) : ℂ) * I))‖ ≤
          (2 * (5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)) / x := by
      simpa [one_mul] using houter_ray 1 (Or.inl rfl)
    have hdecomp_total :
        (x : ℂ) ^ ((j : ℤ) - 1) *
            (iteratedDeriv j (fun t : ℝ => frPoisson b (t : ℂ)) x - iteratedDeriv j (v_b b) (x : ℂ)) =
        (2 * (Real.pi : ℂ) * I)⁻¹ * (
          (1 + I) * ((x : ℂ) ^ ((j : ℤ) - 1) * (∫ s : ℝ in (0 : ℝ)..(1 / 4 : ℝ), g (((r - s : ℝ) : ℂ) - ((r + s : ℝ) : ℂ) * I)) -
            ∫ u in Set.Ioi (0 : ℝ), H (((1 - u : ℝ) : ℂ) - ((1 + u : ℝ) : ℂ) * I)) +
          I * ((x : ℂ) ^ ((j : ℤ) - 1) * (∫ y : ℝ in (-r)..r, g ((r : ℂ) + (y : ℂ) * I)) -
            ∫ w : ℝ in (-1 : ℝ)..(1 : ℝ), H ((1 : ℂ) + (w : ℂ) * I)) +
          (-1 + I) * ((x : ℂ) ^ ((j : ℤ) - 1) * (∫ s : ℝ in (0 : ℝ)..(1 / 4 : ℝ), g (((r - s : ℝ) : ℂ) + ((r + s : ℝ) : ℂ) * I)) -
            ∫ u in Set.Ioi (0 : ℝ), H (((1 - u : ℝ) : ℂ) + ((1 + u : ℝ) : ℂ) * I)) +
          (1 + I) * ((x : ℂ) ^ ((j : ℤ) - 1) * (∫ s : ℝ in (1 / 4 : ℝ)..(2 : ℝ), g (((r - s : ℝ) : ℂ) - ((r + s : ℝ) : ℂ) * I))) +
          (-1 + I) * ((x : ℂ) ^ ((j : ℤ) - 1) * (∫ s : ℝ in (1 / 4 : ℝ)..(2 : ℝ), g (((r - s : ℝ) : ℂ) + ((r + s : ℝ) : ℂ) * I))) -
          (x : ℂ) ^ ((j : ℤ) - 1) * (I * ∫ y : ℝ in (-(r + 2))..(r + 2), g (((r - 2 : ℝ) : ℂ) + (y : ℂ) * I))) := by
      rw [mul_sub, hv_hankel, hfr_trap]
      unfold trapIntegral hankelIntegral hankelIntegralR
      simp only [Complex.ofReal_one]
      rw [hbot_split, htop_split]
      ring
    rw [hdecomp_total, norm_mul, hnorm_2piI]
    let Z1 := (1 + I) * ((x : ℂ) ^ ((j : ℤ) - 1) * (∫ s : ℝ in (0 : ℝ)..(1 / 4 : ℝ), g (((r - s : ℝ) : ℂ) - ((r + s : ℝ) : ℂ) * I)) -
        ∫ u in Set.Ioi (0 : ℝ), H (((1 - u : ℝ) : ℂ) - ((1 + u : ℝ) : ℂ) * I))
    let Z2 := I * ((x : ℂ) ^ ((j : ℤ) - 1) * (∫ y : ℝ in (-r)..r, g ((r : ℂ) + (y : ℂ) * I)) -
        ∫ w : ℝ in (-1 : ℝ)..(1 : ℝ), H ((1 : ℂ) + (w : ℂ) * I))
    let Z3 := (-1 + I) * ((x : ℂ) ^ ((j : ℤ) - 1) * (∫ s : ℝ in (0 : ℝ)..(1 / 4 : ℝ), g (((r - s : ℝ) : ℂ) + ((r + s : ℝ) : ℂ) * I)) -
        ∫ u in Set.Ioi (0 : ℝ), H (((1 - u : ℝ) : ℂ) + ((1 + u : ℝ) : ℂ) * I))
    let Z4 := (1 + I) * ((x : ℂ) ^ ((j : ℤ) - 1) * (∫ s : ℝ in (1 / 4 : ℝ)..(2 : ℝ), g (((r - s : ℝ) : ℂ) - ((r + s : ℝ) : ℂ) * I)))
    let Z5 := (-1 + I) * ((x : ℂ) ^ ((j : ℤ) - 1) * (∫ s : ℝ in (1 / 4 : ℝ)..(2 : ℝ), g (((r - s : ℝ) : ℂ) + ((r + s : ℝ) : ℂ) * I)))
    let Z6 := (x : ℂ) ^ ((j : ℤ) - 1) * (I * ∫ y : ℝ in (-(r + 2))..(r + 2), g (((r - 2 : ℝ) : ℂ) + (y : ℂ) * I))
    let A1 := ‖Z1‖; let A2 := ‖Z2‖; let A3 := ‖Z3‖; let A4 := ‖Z4‖; let A5 := ‖Z5‖; let A6 := ‖Z6‖
    have htri : ‖Z1 + Z2 + Z3 + Z4 + Z5 - Z6‖ ≤ A1 + A2 + A3 + A4 + A5 + A6 := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
      refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
      refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
      exact norm_add_le _ _
    have hA1 : A1 ≤ 2 * (((2 : ℝ) ^ j * Real.exp 1 * M_R * J1 + 8 * (2 : ℝ) ^ j * Real.exp 1 * M_Psi * Jhalf) / x) := by
      dsimp only [A1, Z1]; rw [norm_mul]; exact mul_le_mul hnorm_1pI hbot_diff' (norm_nonneg _) (by norm_num)
    have hA2 : A2 ≤ (2 * (2 : ℝ) ^ j * Real.exp 1 * M_R) / x := hrem_cap
    have hA3 : A3 ≤ 2 * (((2 : ℝ) ^ j * Real.exp 1 * M_R * J1 + 8 * (2 : ℝ) ^ j * Real.exp 1 * M_Psi * Jhalf) / x) := by
      dsimp only [A3, Z3]; rw [norm_mul]; exact mul_le_mul hnorm_m1pI htop_diff' (norm_nonneg _) (by norm_num)
    have hA4 : A4 ≤ 2 * ((2 * (5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)) / x) := by
      dsimp only [A4, Z4]; rw [norm_mul]; exact mul_le_mul hnorm_1pI houter_bot' (norm_nonneg _) (by norm_num)
    have hA5 : A5 ≤ 2 * ((2 * (5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)) / x) := by
      dsimp only [A5, Z5]; rw [norm_mul]; exact mul_le_mul hnorm_m1pI houter_top' (norm_nonneg _) (by norm_num)
    have hA6 : A6 ≤ (5 * (5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ)) / x := houter_left
    have hsum6 : (2 * Real.pi)⁻¹ * (A1 + A2 + A3 + A4 + A5 + A6) ≤ (C_rem + C_out + C_tail) / x := by
      have hsum_le : A1 + A2 + A3 + A4 + A5 + A6 ≤
          (4 * (2 : ℝ) ^ j * Real.exp 1 * M_R * J1 + 2 * (2 : ℝ) ^ j * Real.exp 1 * M_R +
           13 * (5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ) +
           32 * (2 : ℝ) ^ j * Real.exp 1 * M_Psi * Jhalf) / x :=
        (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hA1 hA2) hA3) hA4) hA5) hA6).trans
          (le_of_eq (by ring))
      have h13_le_15 : (13 : ℝ) * (5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ) ≤
          15 * (5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ) := by
        have : 0 ≤ (5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ) := by positivity
        linarith
      calc (2 * Real.pi)⁻¹ * (A1 + A2 + A3 + A4 + A5 + A6)
          ≤ (2 * Real.pi)⁻¹ * ((4 * (2 : ℝ) ^ j * Real.exp 1 * M_R * J1 + 2 * (2 : ℝ) ^ j * Real.exp 1 * M_R +
              15 * (5 : ℝ) ^ j * M_L * (8 : ℝ) ^ (j + 1) * ((j + 1).factorial : ℝ) +
              32 * (2 : ℝ) ^ j * Real.exp 1 * M_Psi * Jhalf) / x) := by
            refine mul_le_mul_of_nonneg_left (hsum_le.trans (div_le_div_of_nonneg_right (by linarith) hx_pos.le))
              (by positivity)
        _ = (C_rem + C_out + C_tail) / x := by dsimp only [C_rem, C_out, C_tail]; ring
    calc (2 * Real.pi)⁻¹ * ‖Z1 + Z2 + Z3 + Z4 + Z5 - Z6‖
        ≤ (2 * Real.pi)⁻¹ * (A1 + A2 + A3 + A4 + A5 + A6) := mul_le_mul_of_nonneg_left htri (by positivity)
      _ ≤ (C_rem + C_out + C_tail) / x := hsum6
      _ ≤ C_all / x := div_le_div_of_nonneg_right (le_max_right _ _) hx_pos.le

/-! ### `2^N`-Scaling Reduction: Any ADE for `frPoisson b` Forces a Nonzero ADE for `v_b b` on `{0 < z.re}` -/

/-- Exact `2`-scaling invariance of `x^{j-1} v_b^{(j)}(x)` on `(0, ∞)`. -/
private lemma v_b_scaled_two_pow_mul {b : ℕ} (hb : 2 ≤ b) (j N : ℕ) {x : ℝ} (hx : 0 < x) :
    (((2 : ℝ) ^ N * x : ℝ) : ℂ) ^ ((j : ℤ) - 1) * iteratedDeriv j (v_b b) (((2 : ℝ) ^ N * x : ℝ) : ℂ) =
      (x : ℂ) ^ ((j : ℤ) - 1) * iteratedDeriv j (v_b b) (x : ℂ) := by
  have h2N_pos : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
  have h2Nx_pos : (0 : ℝ) < (2 : ℝ) ^ N * x := mul_pos h2N_pos hx
  have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have h2Nx_ne : (((2 : ℝ) ^ N * x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h2Nx_pos.ne'
  rw [iteratedDeriv_v_b hb j (by rw [Complex.ofReal_re]; exact h2Nx_pos),
    iteratedDeriv_v_b hb j (by rw [Complex.ofReal_re]; exact hx),
    ← mul_assoc, ← zpow_add₀ h2Nx_ne, show ((j : ℤ) - 1) + (1 - (j : ℤ)) = 0 by ring, zpow_zero, one_mul,
    ← mul_assoc, ← zpow_add₀ hx_ne, show ((j : ℤ) - 1) + (1 - (j : ℤ)) = 0 by ring, zpow_zero, one_mul]
  refine tsum_congr fun k => ?_
  congr 1
  have hlog_eq : Complex.log (((2 : ℝ) ^ N * x : ℝ) : ℂ) =
      (N : ℂ) * ((Real.log 2 : ℝ) : ℂ) + Complex.log (x : ℂ) := by
    rw [← Complex.ofReal_log h2Nx_pos.le, ← Complex.ofReal_log hx.le,
      Real.log_mul h2N_pos.ne' hx.ne', Real.log_pow]
    push_cast; ring
  have hlog2C : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  rw [hlog_eq, mul_add, Complex.exp_add]
  have hper : Complex.exp (chiFR k * ((N : ℂ) * ((Real.log 2 : ℝ) : ℂ))) = 1 := by
    have hmul : chiFR k * ((N : ℂ) * ((Real.log 2 : ℝ) : ℂ)) =
        (((k * (N : ℤ) : ℤ) : ℂ)) * (2 * (Real.pi : ℂ) * I) := by
      unfold chiFR; push_cast; field_simp [hlog2C]
    rw [hmul, Complex.exp_int_mul_two_pi_mul_I]
  rw [hper, one_mul]

/-- Auxiliary polynomial-division limit: for `p : Polynomial ℂ` with `p.natDegree ≤ d` and `x₀ > 0`,
`p.eval (2^N * x₀) / (2^N * x₀)^d → p.coeff d` as `N → ∞`. -/
private lemma tendsto_poly_eval_div_pow_two_pow {p : Polynomial ℂ} {d : ℕ} (hd : p.natDegree ≤ d)
    {x₀ : ℝ} (hx₀ : 0 < x₀) :
    Filter.Tendsto (fun N : ℕ => p.eval (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) / (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) ^ d)
      atTop (𝓝 (p.coeff d)) := by
  have hrew : ∀ N : ℕ, p.eval (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) / (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) ^ d =
      ∑ m ∈ Finset.range (d + 1), p.coeff m * ((((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) ^ (d - m))⁻¹ := by
    intro N
    have hne : (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.sum_div]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmd : m ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hpow : (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) ^ d =
        (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) ^ m * (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) ^ (d - m) := by
      rw [← pow_add, Nat.add_sub_of_le hmd]
    rw [hpow]
    field_simp [hne]
  simp_rw [hrew]
  have htarget : p.coeff d = ∑ m ∈ Finset.range (d + 1), if m = d then p.coeff d else 0 := by
    rw [Finset.sum_ite_eq' (Finset.range (d + 1)) d (fun _ => p.coeff d)]
    simp
  rw [htarget]
  refine tendsto_finset_sum_fr fun m hm => ?_
  by_cases hmd : m = d
  · subst hmd
    simp only [Nat.sub_self, pow_zero, inv_one, mul_one, ite_true]
    exact tendsto_const_nhds
  · simp only [hmd, ite_false]
    have hpos : 0 < d - m := by have := Finset.mem_range.mp hm; omega
    have hinv0 : Filter.Tendsto (fun N : ℕ => ((((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) ^ (d - m))⁻¹) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have heq : (fun N : ℕ => ‖((((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) ^ (d - m))⁻¹‖) =
          fun N : ℕ => x₀⁻¹ ^ (d - m) * ((1 / 2 : ℝ) ^ (d - m)) ^ N := by
        funext N
        rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity),
          mul_pow, mul_inv, ← inv_pow, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm N (d - m),
          one_div, mul_comm, inv_pow x₀]
      rw [heq]
      have hbase_lt1 : (1 / 2 : ℝ) ^ (d - m) < 1 :=
        pow_lt_one₀ (by norm_num) (by norm_num) hpos.ne'
      have hgeom : Filter.Tendsto (fun N : ℕ => ((1 / 2 : ℝ) ^ (d - m)) ^ N) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hbase_lt1
      simpa using hgeom.const_mul (x₀⁻¹ ^ (d - m))
    simpa using hinv0.const_mul (p.coeff m)

/-- **`2^N`-Scaling Reduction (Step 4B)**:
Any nonzero algebraic differential equation over `ℂ[x]` satisfied by `frPoisson b` on `(0, ∞)`
forces a nonzero algebraic differential equation over `ℂ[z]` satisfied by `v_b b` on ALL of `{0 < z.re}`! -/
theorem exists_nonzero_ade_v_b_of_frPoisson_ade {b : ℕ} (hb : 2 ≤ b) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hP_ne : P ≠ 0)
    (hP : ∀ x : ℝ, 0 < x →
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => frPoisson b (t : ℂ)) x)
        (P.map (Polynomial.evalRingHom (x : ℂ))) = 0) :
    ∃ Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ), Q ≠ 0 ∧
      ∀ z : ℂ, 0 < z.re →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (v_b b) z)
          (Q.map (Polynomial.evalRingHom z)) = 0 := by
  classical
  -- Step 1: Substitute `Y_j = x^{1 - j} Z_j` and clear negative powers of `x` via `M = max_α ∑_j j α_j`:
  let wt : (Fin (r + 1) →₀ ℕ) → ℕ := fun α => ∑ j : Fin (r + 1), j.val * α j
  let M : ℕ := P.support.sup wt
  let exp1 : (Fin (r + 1) →₀ ℕ) → ℕ := fun α => M + α ⟨0, Nat.zero_lt_succ r⟩ - ∑ j : Fin (r + 1), (j.val - 1) * α j
  have hexp1_int : ∀ α ∈ P.support,
      ((exp1 α : ℕ) : ℤ) = (M : ℤ) + ∑ j : Fin (r + 1), (1 - (j.val : ℤ)) * (α j : ℤ) := by
    intro α hα
    have hwt : wt α ≤ M := Finset.le_sup hα
    have hle : ∑ j : Fin (r + 1), (j.val - 1) * α j ≤ wt α := by
      refine Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have hsub : ∑ j : Fin (r + 1), (j.val - 1) * α j ≤ M + α ⟨0, Nat.zero_lt_succ r⟩ := by omega
    dsimp only [exp1]
    rw [Nat.cast_sub hsub, Nat.cast_add, Nat.cast_sum]
    have hsum_split : (α ⟨0, Nat.zero_lt_succ r⟩ : ℤ) - ∑ j : Fin (r + 1), (((j.val - 1) * α j : ℕ) : ℤ) =
        ∑ j : Fin (r + 1), (1 - (j.val : ℤ)) * (α j : ℤ) := by
      have h0 : ∑ j : Fin (r + 1), (1 - (j.val : ℤ)) * (α j : ℤ) =
          (1 - ((⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)).val : ℤ)) * (α ⟨0, Nat.zero_lt_succ r⟩ : ℤ) +
          ∑ j ∈ Finset.univ.erase ⟨0, Nat.zero_lt_succ r⟩, (1 - (j.val : ℤ)) * (α j : ℤ) :=
        (Finset.add_sum_erase Finset.univ (fun j : Fin (r + 1) => (1 - (j.val : ℤ)) * (α j : ℤ)) (Finset.mem_univ _)).symm
      have h1 : ∑ j : Fin (r + 1), (((j.val - 1) * α j : ℕ) : ℤ) =
          ((((⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)).val - 1) * α ⟨0, Nat.zero_lt_succ r⟩ : ℕ) : ℤ) +
          ∑ j ∈ Finset.univ.erase ⟨0, Nat.zero_lt_succ r⟩, (((j.val - 1) * α j : ℕ) : ℤ) :=
        (Finset.add_sum_erase Finset.univ (fun j : Fin (r + 1) => (((j.val - 1) * α j : ℕ) : ℤ)) (Finset.mem_univ _)).symm
      rw [h0, h1]
      have herase : ∑ j ∈ Finset.univ.erase ⟨0, Nat.zero_lt_succ r⟩, (1 - (j.val : ℤ)) * (α j : ℤ) =
          -(∑ j ∈ Finset.univ.erase ⟨0, Nat.zero_lt_succ r⟩, (((j.val - 1) * α j : ℕ) : ℤ)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj0 : 1 ≤ j.val := by
          have hne : j ≠ ⟨0, Nat.zero_lt_succ r⟩ := Finset.ne_of_mem_erase hj
          have : j.val ≠ 0 := fun h => hne (Fin.ext h)
          omega
        rw [Nat.cast_mul, Nat.cast_sub hj0]; push_cast; ring
      rw [herase]; simp [sub_eq_add_neg]
    linarith
  let P1 : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
    ∑ α ∈ P.support, MvPolynomial.monomial α (P.coeff α * Polynomial.X ^ exp1 α)
  have hP1_coeff : ∀ α : Fin (r + 1) →₀ ℕ,
      P1.coeff α = if α ∈ P.support then P.coeff α * Polynomial.X ^ exp1 α else 0 := by
    intro α
    dsimp only [P1]
    rw [MvPolynomial.coeff_sum]
    simp_rw [MvPolynomial.coeff_monomial]
    by_cases hα : α ∈ P.support
    · rw [Finset.sum_eq_single α]
      · simp [hα]
      · intro β _ hβα; simp [hβα]
      · intro hnot; exact absurd hα hnot
    · simp only [hα, ↓reduceIte]
      exact Finset.sum_eq_zero fun β hβ => by
        have hne : β ≠ α := fun h => hα (h ▸ hβ)
        simp [hne]
  have hP1_ne : P1 ≠ 0 := by
    have hsup : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hP_ne
    obtain ⟨α₀, hα₀⟩ := hsup
    intro h0
    have hc : P1.coeff α₀ = 0 := by simp [h0]
    rw [hP1_coeff α₀] at hc
    simp only [hα₀, ↓reduceIte] at hc
    exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hα₀) (pow_ne_zero _ Polynomial.X_ne_zero) hc
  -- Verify `P1` vanishes on `Z_j(x) = x^{j-1} frPoisson^{(j)}(x)` for all `x > 0`!
  let Z : ℝ → Fin (r + 1) → ℂ := fun x j =>
    (x : ℂ) ^ ((j.val : ℤ) - 1) * iteratedDeriv j.val (fun t : ℝ => frPoisson b (t : ℂ)) x
  let W : ℝ → Fin (r + 1) → ℂ := fun x j =>
    (x : ℂ) ^ ((j.val : ℤ) - 1) * iteratedDeriv j.val (v_b b) (x : ℂ)
  have hP1_eval : ∀ x : ℝ, 0 < x →
      MvPolynomial.eval (Z x) (P1.map (Polynomial.evalRingHom (x : ℂ))) = 0 := by
    intro x hx
    have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hval : MvPolynomial.eval (Z x) (P1.map (Polynomial.evalRingHom (x : ℂ))) =
        (x : ℂ) ^ M * MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => frPoisson b (t : ℂ)) x)
          (P.map (Polynomial.evalRingHom (x : ℂ))) := by
      rw [MvPolynomial.eval_map, MvPolynomial.eval_map, MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq',
        Finset.mul_sum]
      have hsub_sup : P1.support ⊆ P.support := fun α hα => by
        rw [MvPolynomial.mem_support_iff, hP1_coeff α] at hα
        by_contra hnot; simp only [hnot, ↓reduceIte] at hα; exact hα rfl
      rw [Finset.sum_subset hsub_sup (fun α _ hnot => by
        rw [MvPolynomial.notMem_support_iff.mp hnot, map_zero, zero_mul])]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [hP1_coeff α]
      simp only [hα, ↓reduceIte, map_mul, map_pow, Polynomial.coe_evalRingHom, Polynomial.eval_X]
      have hprod_Z : ∏ j : Fin (r + 1), (Z x j) ^ (α j) =
          (x : ℂ) ^ (∑ j : Fin (r + 1), ((j.val : ℤ) - 1) * (α j : ℤ)) *
            ∏ j : Fin (r + 1), (iteratedDeriv j.val (fun t : ℝ => frPoisson b (t : ℂ)) x) ^ (α j) := by
        dsimp only [Z]
        simp_rw [mul_pow]
        rw [Finset.prod_mul_distrib]
        congr 1
        rw [zpow_sum_complex hx_ne]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← zpow_natCast, ← zpow_mul]
      rw [hprod_Z]
      have hpow_cancel : (x : ℂ) ^ exp1 α * (x : ℂ) ^ (∑ j : Fin (r + 1), ((j.val : ℤ) - 1) * (α j : ℤ)) =
          (x : ℂ) ^ M := by
        rw [← zpow_natCast (x : ℂ) (exp1 α), ← zpow_natCast (x : ℂ) M, ← zpow_add₀ hx_ne]
        congr 1
        rw [hexp1_int α hα]
        have hsum_zero : (∑ j : Fin (r + 1), (1 - (j.val : ℤ)) * (α j : ℤ)) +
            (∑ j : Fin (r + 1), ((j.val : ℤ) - 1) * (α j : ℤ)) = 0 := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_eq_zero fun j _ => by ring
        linarith
      calc (Polynomial.eval (x : ℂ) (P.coeff α) * (x : ℂ) ^ exp1 α) *
              ((x : ℂ) ^ (∑ j : Fin (r + 1), ((j.val : ℤ) - 1) * (α j : ℤ)) *
                ∏ j : Fin (r + 1), (iteratedDeriv j.val (fun t : ℝ => frPoisson b (t : ℂ)) x) ^ (α j))
          = Polynomial.eval (x : ℂ) (P.coeff α) *
              ((x : ℂ) ^ exp1 α * (x : ℂ) ^ (∑ j : Fin (r + 1), ((j.val : ℤ) - 1) * (α j : ℤ))) *
              ∏ j : Fin (r + 1), (iteratedDeriv j.val (fun t : ℝ => frPoisson b (t : ℂ)) x) ^ (α j) := by ring
        _ = (x : ℂ) ^ M * (Polynomial.eval (x : ℂ) (P.coeff α) *
              ∏ j : Fin (r + 1), (iteratedDeriv j.val (fun t : ℝ => frPoisson b (t : ℂ)) x) ^ (α j)) := by
            rw [hpow_cancel]; ring
    rw [hval, hP x hx, mul_zero]
  -- Step 2: Extract top `X`-degree `d` of `P1` to obtain nonzero constant-coefficient `Q0` vanishing on `W x`!
  let d : ℕ := P1.support.sup fun α => (P1.coeff α).natDegree
  let Q0 : MvPolynomial (Fin (r + 1)) ℂ :=
    ∑ α ∈ P1.support, MvPolynomial.monomial α ((P1.coeff α).coeff d)
  have hQ0_coeff : ∀ α : Fin (r + 1) →₀ ℕ, Q0.coeff α = (P1.coeff α).coeff d := by
    intro α
    dsimp only [Q0]
    rw [MvPolynomial.coeff_sum]
    simp_rw [MvPolynomial.coeff_monomial]
    by_cases hα : α ∈ P1.support
    · rw [Finset.sum_eq_single α]
      · simp
      · intro β _ hβα; simp [hβα]
      · intro hnot; exact absurd hα hnot
    · rw [MvPolynomial.notMem_support_iff.mp hα, Polynomial.coeff_zero]
      exact Finset.sum_eq_zero fun β hβ => by
        have hne : β ≠ α := fun h => hα (h ▸ hβ)
        simp [hne]
  have hQ0_ne : Q0 ≠ 0 := by
    obtain ⟨α₀, hα₀, hmax⟩ := Finset.exists_mem_eq_sup P1.support (MvPolynomial.support_nonempty.mpr hP1_ne)
      (fun α => (P1.coeff α).natDegree)
    intro h0
    have hc : Q0.coeff α₀ = 0 := by simp [h0]
    rw [hQ0_coeff α₀] at hc
    have hd_eq : d = (P1.coeff α₀).natDegree := hmax
    rw [hd_eq] at hc
    exact Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hα₀) hc
  -- For every `x₀ ∈ (2, 3)`, send `N → ∞` along `x_N = 2^N * x₀`!
  have hZ_tend : ∀ (x₀ : ℝ), 2 ≤ x₀ → ∀ j : Fin (r + 1),
      Filter.Tendsto (fun N : ℕ => Z ((2 : ℝ) ^ N * x₀) j) atTop (𝓝 (W x₀ j)) := by
    intro x₀ hx₀ j
    obtain ⟨C, hC, hasymp⟩ := frPoisson_iteratedDeriv_asymptotic hb j.val
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbd : ∀ N : ℕ, ‖Z ((2 : ℝ) ^ N * x₀) j - W x₀ j‖ ≤ (C / x₀) * (1 / 2 : ℝ) ^ N := by
      intro N
      have h2Nx : 2 ≤ (2 : ℝ) ^ N * x₀ := by
        have h2N : (1 : ℝ) ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
        nlinarith
      have hW_inv : W ((2 : ℝ) ^ N * x₀) j = W x₀ j :=
        v_b_scaled_two_pow_mul hb j.val N (by linarith)
      rw [← hW_inv]
      have hsub : Z ((2 : ℝ) ^ N * x₀) j - W ((2 : ℝ) ^ N * x₀) j =
          (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) ^ ((j.val : ℤ) - 1) *
            (iteratedDeriv j.val (fun t : ℝ => frPoisson b (t : ℂ)) ((2 : ℝ) ^ N * x₀) -
              iteratedDeriv j.val (v_b b) (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ)) := by
        dsimp only [Z, W]; ring
      rw [hsub]
      calc ‖(((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) ^ ((j.val : ℤ) - 1) *
              (iteratedDeriv j.val (fun t : ℝ => frPoisson b (t : ℂ)) ((2 : ℝ) ^ N * x₀) -
                iteratedDeriv j.val (v_b b) (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ))‖
          ≤ C / ((2 : ℝ) ^ N * x₀) := hasymp ((2 : ℝ) ^ N * x₀) h2Nx
        _ = (C / x₀) * (1 / 2 : ℝ) ^ N := by rw [one_div_pow]; field_simp [show x₀ ≠ 0 by linarith]
    have ht0 : Filter.Tendsto (fun N : ℕ => (C / x₀) * (1 / 2 : ℝ) ^ N) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (C / x₀)
    exact squeeze_zero (fun _ => norm_nonneg _) hbd ht0
  have hQ0_vanish : ∀ x₀ : ℝ, 2 < x₀ → x₀ < 3 → MvPolynomial.eval (W x₀) Q0 = 0 := by
    intro x₀ hx2 _
    have hx₀ : 0 < x₀ := by linarith
    have hzero_seq : ∀ N : ℕ,
        ∑ α ∈ P1.support,
          ((P1.coeff α).eval (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) / (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) ^ d) *
            ∏ j : Fin (r + 1), (Z ((2 : ℝ) ^ N * x₀) j) ^ (α j) = 0 := by
      intro N
      have h2Nx_pos : 0 < (2 : ℝ) ^ N * x₀ := by positivity
      have h0 := hP1_eval ((2 : ℝ) ^ N * x₀) h2Nx_pos
      rw [MvPolynomial.eval_map, MvPolynomial.eval₂_eq'] at h0
      have hdiv0 : (∑ α ∈ P1.support, (P1.coeff α).eval (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) *
            ∏ j : Fin (r + 1), (Z ((2 : ℝ) ^ N * x₀) j) ^ (α j)) /
          (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) ^ d = 0 := by
        have h0' : ∑ α ∈ P1.support, (P1.coeff α).eval (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) *
            ∏ j : Fin (r + 1), (Z ((2 : ℝ) ^ N * x₀) j) ^ (α j) = 0 := by
          simpa only [Polynomial.coe_evalRingHom] using h0
        rw [h0', zero_div]
      rw [Finset.sum_div] at hdiv0
      simpa only [mul_div_right_comm] using hdiv0
    have htend : Filter.Tendsto (fun N : ℕ =>
        ∑ α ∈ P1.support,
          ((P1.coeff α).eval (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) / (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) ^ d) *
            ∏ j : Fin (r + 1), (Z ((2 : ℝ) ^ N * x₀) j) ^ (α j))
        atTop (𝓝 (MvPolynomial.eval (W x₀) Q0)) := by
      rw [MvPolynomial.eval_eq']
      have hsub_sup : Q0.support ⊆ P1.support := fun α hα => by
        rw [MvPolynomial.mem_support_iff, hQ0_coeff α] at hα
        by_contra hnot
        rw [MvPolynomial.notMem_support_iff.mp hnot, Polynomial.coeff_zero] at hα
        exact hα rfl
      rw [Finset.sum_subset hsub_sup (fun α _ hnot => by
        rw [MvPolynomial.notMem_support_iff.mp hnot, zero_mul])]
      refine tendsto_finset_sum_fr fun α hα => ?_
      rw [hQ0_coeff α]
      have hd_le : (P1.coeff α).natDegree ≤ d := Finset.le_sup (f := fun β => (P1.coeff β).natDegree) hα
      have hc_tend := tendsto_poly_eval_div_pow_two_pow hd_le hx₀
      have hp_tend : Filter.Tendsto (fun N : ℕ => ∏ j : Fin (r + 1), (Z ((2 : ℝ) ^ N * x₀) j) ^ (α j))
          atTop (𝓝 (∏ j : Fin (r + 1), (W x₀ j) ^ (α j))) :=
        tendsto_finset_prod_fr fun j _ => (hZ_tend x₀ hx2.le j).pow (α j)
      exact hc_tend.mul hp_tend
    have ht0 : Filter.Tendsto (fun N : ℕ =>
        ∑ α ∈ P1.support,
          ((P1.coeff α).eval (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) / (((2 : ℝ) ^ N * x₀ : ℝ) : ℂ) ^ d) *
            ∏ j : Fin (r + 1), (Z ((2 : ℝ) ^ N * x₀) j) ^ (α j)) atTop (𝓝 0) := by
      simp_rw [hzero_seq]; exact tendsto_const_nhds
    exact tendsto_nhds_unique htend ht0
  -- Step 3: Substitute `W_j(z) = z^{j-1} v_b^{(j)}(z)` back into `Q0`, clear `z^{-α_0}` via `M' = sup α_0`, and extend!
  let M' : ℕ := Q0.support.sup fun α => α ⟨0, Nat.zero_lt_succ r⟩
  let exp2 : (Fin (r + 1) →₀ ℕ) → ℕ := fun α => (M' - α ⟨0, Nat.zero_lt_succ r⟩) + ∑ j : Fin (r + 1), (j.val - 1) * α j
  have hexp2_int : ∀ α ∈ Q0.support,
      ((exp2 α : ℕ) : ℤ) = (M' : ℤ) + ∑ j : Fin (r + 1), ((j.val : ℤ) - 1) * (α j : ℤ) := by
    intro α hα
    have hle : α ⟨0, Nat.zero_lt_succ r⟩ ≤ M' := Finset.le_sup (f := fun β : Fin (r + 1) →₀ ℕ => β ⟨0, Nat.zero_lt_succ r⟩) hα
    dsimp only [exp2]
    rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_sum]
    have hsum_split : (∑ j : Fin (r + 1), ((j.val : ℤ) - 1) * (α j : ℤ)) =
        -(α ⟨0, Nat.zero_lt_succ r⟩ : ℤ) + ∑ j : Fin (r + 1), (((j.val - 1) * α j : ℕ) : ℤ) := by
      have h0 : ∑ j : Fin (r + 1), ((j.val : ℤ) - 1) * (α j : ℤ) =
          (((⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)).val : ℤ) - 1) * (α ⟨0, Nat.zero_lt_succ r⟩ : ℤ) +
          ∑ j ∈ Finset.univ.erase ⟨0, Nat.zero_lt_succ r⟩, ((j.val : ℤ) - 1) * (α j : ℤ) :=
        (Finset.add_sum_erase Finset.univ (fun j : Fin (r + 1) => ((j.val : ℤ) - 1) * (α j : ℤ)) (Finset.mem_univ _)).symm
      have h1 : ∑ j : Fin (r + 1), (((j.val - 1) * α j : ℕ) : ℤ) =
          ((((⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)).val - 1) * α ⟨0, Nat.zero_lt_succ r⟩ : ℕ) : ℤ) +
          ∑ j ∈ Finset.univ.erase ⟨0, Nat.zero_lt_succ r⟩, (((j.val - 1) * α j : ℕ) : ℤ) :=
        (Finset.add_sum_erase Finset.univ (fun j : Fin (r + 1) => (((j.val - 1) * α j : ℕ) : ℤ)) (Finset.mem_univ _)).symm
      rw [h0, h1]
      have herase : ∑ j ∈ Finset.univ.erase ⟨0, Nat.zero_lt_succ r⟩, ((j.val : ℤ) - 1) * (α j : ℤ) =
          ∑ j ∈ Finset.univ.erase ⟨0, Nat.zero_lt_succ r⟩, (((j.val - 1) * α j : ℕ) : ℤ) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj0 : 1 ≤ j.val := by
          have hne : j ≠ ⟨0, Nat.zero_lt_succ r⟩ := Finset.ne_of_mem_erase hj
          have : j.val ≠ 0 := fun h => hne (Fin.ext h)
          omega
        rw [Nat.cast_mul, Nat.cast_sub hj0]; push_cast; ring
      rw [herase]; simp [sub_eq_add_neg]
    linarith
  let Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
    ∑ α ∈ Q0.support, MvPolynomial.monomial α (Polynomial.C (Q0.coeff α) * Polynomial.X ^ exp2 α)
  have hQ_coeff : ∀ α : Fin (r + 1) →₀ ℕ,
      Q.coeff α = if α ∈ Q0.support then Polynomial.C (Q0.coeff α) * Polynomial.X ^ exp2 α else 0 := by
    intro α
    dsimp only [Q]
    rw [MvPolynomial.coeff_sum]
    simp_rw [MvPolynomial.coeff_monomial]
    by_cases hα : α ∈ Q0.support
    · rw [Finset.sum_eq_single α]
      · simp [hα]
      · intro β _ hβα; simp [hβα]
      · intro hnot; exact absurd hα hnot
    · simp only [hα, ↓reduceIte]
      exact Finset.sum_eq_zero fun β hβ => by
        have hne : β ≠ α := fun h => hα (h ▸ hβ)
        simp [hne]
  have hQ_ne : Q ≠ 0 := by
    obtain ⟨α₀, hα₀⟩ := MvPolynomial.support_nonempty.mpr hQ0_ne
    intro h0
    have hc : Q.coeff α₀ = 0 := by simp [h0]
    rw [hQ_coeff α₀] at hc
    simp only [hα₀, ↓reduceIte] at hc
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hα₀))
      (pow_ne_zero _ Polynomial.X_ne_zero) hc
  -- Verify `Q` vanishes on `(2, 3)`:
  have hQ_real : ∀ x : ℝ, 2 < x → x < 3 →
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (v_b b) (x : ℂ))
        (Q.map (Polynomial.evalRingHom (x : ℂ))) = 0 := by
    intro x hx2 hx3
    have hx_ne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hval : MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (v_b b) (x : ℂ))
          (Q.map (Polynomial.evalRingHom (x : ℂ))) =
        (x : ℂ) ^ M' * MvPolynomial.eval (W x) Q0 := by
      rw [MvPolynomial.eval_map, MvPolynomial.eval₂_eq', MvPolynomial.eval_eq', Finset.mul_sum]
      have hsub_sup : Q.support ⊆ Q0.support := fun α hα => by
        rw [MvPolynomial.mem_support_iff, hQ_coeff α] at hα
        by_contra hnot; simp only [hnot, ↓reduceIte] at hα; exact hα rfl
      rw [Finset.sum_subset hsub_sup (fun α _ hnot => by
        rw [MvPolynomial.notMem_support_iff.mp hnot, map_zero, zero_mul])]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [hQ_coeff α]
      simp only [hα, ↓reduceIte, map_mul, map_pow, Polynomial.coe_evalRingHom,
        Polynomial.eval_C, Polynomial.eval_X]
      have hprod_W : ∏ j : Fin (r + 1), (W x j) ^ (α j) =
          (x : ℂ) ^ (∑ j : Fin (r + 1), ((j.val : ℤ) - 1) * (α j : ℤ)) *
            ∏ j : Fin (r + 1), (iteratedDeriv j.val (v_b b) (x : ℂ)) ^ (α j) := by
        dsimp only [W]
        simp_rw [mul_pow]
        rw [Finset.prod_mul_distrib]
        congr 1
        rw [zpow_sum_complex hx_ne]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← zpow_natCast, ← zpow_mul]
      rw [hprod_W]
      have hpow_eq : (x : ℂ) ^ exp2 α = (x : ℂ) ^ M' * (x : ℂ) ^ (∑ j : Fin (r + 1), ((j.val : ℤ) - 1) * (α j : ℤ)) := by
        rw [← zpow_natCast (x : ℂ) (exp2 α), ← zpow_natCast (x : ℂ) M', ← zpow_add₀ hx_ne, hexp2_int α hα]
      rw [hpow_eq]; ring
    rw [hval, hQ0_vanish x hx2 hx3, mul_zero]
  -- Extend from `(2, 3)` to ALL `{z : ℂ | 0 < z.re}` by identity theorem!
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hdiff_v : ∀ j : ℕ, DifferentiableOn ℂ (iteratedDeriv j (v_b b)) U := by
    intro j z hz
    have heq_nhds : iteratedDeriv j (v_b b) =ᶠ[𝓝 z]
        fun w : ℂ => w ^ (1 - (j : ℤ)) * ∑' k : ℤ, vCoeff b j k * Complex.exp (chiFR k * Complex.log w) := by
      filter_upwards [hU_open.mem_nhds hz] with w hw
      exact iteratedDeriv_v_b hb j hw
    obtain ⟨Cv, _, hbdv⟩ := norm_vCoeff_le hb j
    obtain ⟨_, _, hd_sum⟩ := hasDerivAt_tsum_chiFR hbdv hz
    have hz_ne : z ≠ 0 := fun h0 => by rw [h0] at hz; simp [U] at hz
    have hd_pow := hasDerivAt_zpow (1 - (j : ℤ)) z (Or.inl hz_ne)
    exact ((hd_pow.mul hd_sum).congr_of_eventuallyEq heq_nhds).differentiableAt.differentiableWithinAt
  have hdiff_Q : DifferentiableOn ℂ (fun z : ℂ =>
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (v_b b) z)
        (Q.map (Polynomial.evalRingHom z))) U := by
    have hrew : (fun z : ℂ =>
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (v_b b) z)
          (Q.map (Polynomial.evalRingHom z))) =
        fun z : ℂ => ∑ α ∈ Q.support, (Q.coeff α).eval z *
          ∏ j : Fin (r + 1), (iteratedDeriv j.val (v_b b) z) ^ (α j) := by
      funext z; rw [MvPolynomial.eval_map, MvPolynomial.eval₂_eq']; rfl
    rw [hrew]
    refine DifferentiableOn.fun_sum fun α _ => ?_
    refine ((differentiable_poly_eval_complex _).differentiableOn).mul ?_
    exact differentiableOn_finset_prod_fr fun j _ => (hdiff_v j.val).pow (α j)
  have hzero_U := eqOn_of_differentiableOn_eq_on_real_interval hU_open hU_conn hdiff_Q
    (differentiableOn_const 0) (by norm_num : (2 : ℝ) < 3)
    (fun x hx2 _ => by show 0 < ((x : ℂ)).re; rw [Complex.ofReal_re]; linarith) hQ_real
  exact ⟨Q, hQ_ne, fun z hz => hzero_U hz⟩

end Section4

/-! ## Section 5: Master Shift-and-Scale D-Transcendence & Differential Field `trdeg` Transfer -/

section Section5

open PakPrimes.BorelStokesVandermonde (degree_pderiv_lt all_partials_zero)

/-! ### 5A. Master Lacunary Function: Exact Scaling, Shift Remainder, Entireness & Nonvanishing Derivatives -/

/-- Entire remainder series arising from the `2πi n` shift of `masterLacunary`:
`F_n(x) = ∑_{k ≥ 0} 2^{-(k+1)} (exp(-2πi n · 2^{-(k+1)}) - 1) exp(-2^{-(k+1)} x)`. -/
@[expose] def shiftRemainder (n : ℤ) (x : ℂ) : ℂ :=
  ∑' k : ℕ, (2 : ℂ) ^ (-(k + 1 : ℤ)) *
    (Complex.exp (-2 * (Real.pi : ℂ) * I * (n : ℂ) * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1) *
    Complex.exp (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * x)

/-- Exact `2`-scaling functional equation for `masterLacunary` on `{0 < s.re}`:
`masterLacunary (2^{-N} s) = 2^N masterLacunary s` for all `N : ℤ`. -/
theorem masterLacunary_scaling (N : ℤ) (s : ℂ) (_hs : 0 < s.re) :
    masterLacunary ((2 : ℂ) ^ (-N) * s) = (2 : ℂ) ^ N * masterLacunary s := by
  unfold masterLacunary
  rw [← tsum_mul_left]
  rw [← Equiv.tsum_eq (Equiv.addRight N)]
  refine tsum_congr fun m => ?_
  change (2 : ℂ) ^ (m + N) * Complex.exp (-(2 : ℂ) ^ (m + N) * ((2 : ℂ) ^ (-N) * s)) =
    (2 : ℂ) ^ N * ((2 : ℂ) ^ m * Complex.exp (-(2 : ℂ) ^ m * s))
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  have hpow1 : (2 : ℂ) ^ (m + N) = (2 : ℂ) ^ N * (2 : ℂ) ^ m := by
    rw [zpow_add₀ h2ne, mul_comm]
  have hpow2 : (2 : ℂ) ^ (m + N) * ((2 : ℂ) ^ (-N) * s) = (2 : ℂ) ^ m * s := by
    rw [← mul_assoc, ← zpow_add₀ h2ne, show m + N + -N = m by ring]
  rw [neg_mul, hpow2, ← neg_mul, hpow1]; ring

/-- Exact `2πi n` shift identity for `masterLacunary` on `{0 < x.re}`:
`masterLacunary (x + 2πi n) = masterLacunary x + shiftRemainder n x`. -/
theorem masterLacunary_shift (n : ℤ) (x : ℂ) (hx : 0 < x.re) :
    masterLacunary (x + 2 * (Real.pi : ℂ) * I * (n : ℂ)) =
      masterLacunary x + shiftRemainder n x := by
  have hx_shift : 0 < (x + 2 * (Real.pi : ℂ) * I * (n : ℂ)).re := by
    rw [Complex.add_re]
    have h0 : (2 * (Real.pi : ℂ) * I * (n : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [h0, add_zero]; exact hx
  have hsum1 := summable_masterLacunary_term hx_shift
  have hsum2 := summable_masterLacunary_term hx
  unfold masterLacunary shiftRemainder
  rw [tsum_int_eq_nat_add_negSucc hsum1, tsum_int_eq_nat_add_negSucc hsum2]
  have hnat_eq : (∑' m : ℕ, (2 : ℂ) ^ (m : ℤ) * Complex.exp (-(2 : ℂ) ^ (m : ℤ) * (x + 2 * (Real.pi : ℂ) * I * (n : ℂ)))) =
      ∑' m : ℕ, (2 : ℂ) ^ (m : ℤ) * Complex.exp (-(2 : ℂ) ^ (m : ℤ) * x) := by
    refine tsum_congr fun m => ?_
    congr 1
    have hexp_arg : -(2 : ℂ) ^ (m : ℤ) * (x + 2 * (Real.pi : ℂ) * I * (n : ℂ)) =
        -(2 : ℂ) ^ (m : ℤ) * x + (((-((2 : ℤ) ^ m * n) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I)) := by
      rw [zpow_natCast]; push_cast; ring
    rw [hexp_arg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hneg_sum1 : Summable (fun k : ℕ =>
      (2 : ℂ) ^ (-(k + 1 : ℤ)) * Complex.exp (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * (x + 2 * (Real.pi : ℂ) * I * (n : ℂ)))) := by
    have h := hsum1.comp_injective (fun a b (h : Int.negSucc a = Int.negSucc b) => Int.negSucc.inj h)
    exact h.congr fun k => by simp [Int.negSucc_eq]
  have hneg_sum2 : Summable (fun k : ℕ =>
      (2 : ℂ) ^ (-(k + 1 : ℤ)) * Complex.exp (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * x)) := by
    have h := hsum2.comp_injective (fun a b (h : Int.negSucc a = Int.negSucc b) => Int.negSucc.inj h)
    exact h.congr fun k => by simp [Int.negSucc_eq]
  have hneg_diff : (∑' k : ℕ, (2 : ℂ) ^ (-(k + 1 : ℤ)) *
        Complex.exp (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * (x + 2 * (Real.pi : ℂ) * I * (n : ℂ)))) -
      (∑' k : ℕ, (2 : ℂ) ^ (-(k + 1 : ℤ)) * Complex.exp (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * x)) =
      ∑' k : ℕ, (2 : ℂ) ^ (-(k + 1 : ℤ)) *
        (Complex.exp (-2 * (Real.pi : ℂ) * I * (n : ℂ) * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1) *
        Complex.exp (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * x) := by
    rw [← hneg_sum1.tsum_sub hneg_sum2]
    refine tsum_congr fun k => ?_
    have harg : -(2 : ℂ) ^ (-(k + 1 : ℤ)) * (x + 2 * (Real.pi : ℂ) * I * (n : ℂ)) =
        -2 * (Real.pi : ℂ) * I * (n : ℂ) * (2 : ℂ) ^ (-(k + 1 : ℤ)) +
        -(2 : ℂ) ^ (-(k + 1 : ℤ)) * x := by ring
    rw [harg, Complex.exp_add]; ring
  rw [hnat_eq]
  linear_combination hneg_diff

/-- Helper: termwise differentiation of the `m`-th derivative series of `shiftRemainder n`. -/
private lemma hasDerivAt_shiftRemainder_iter (n : ℤ) (m : ℕ) (z₀ : ℂ) :
    HasDerivAt
      (fun z : ℂ => ∑' k : ℕ, (-1 : ℂ) ^ m * (2 : ℂ) ^ (-(((m + 1) * (k + 1) : ℕ) : ℤ)) *
        (Complex.exp (-2 * (Real.pi : ℂ) * I * (n : ℂ) * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1) *
        Complex.exp (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * z))
      (∑' k : ℕ, (-1 : ℂ) ^ (m + 1) * (2 : ℂ) ^ (-(((m + 2) * (k + 1) : ℕ) : ℤ)) *
        (Complex.exp (-2 * (Real.pi : ℂ) * I * (n : ℂ) * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1) *
        Complex.exp (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * z₀)) z₀ := by
  let g : ℕ → ℂ → ℂ := fun k z =>
    (-1 : ℂ) ^ m * (2 : ℂ) ^ (-(((m + 1) * (k + 1) : ℕ) : ℤ)) *
      (Complex.exp (-2 * (Real.pi : ℂ) * I * (n : ℂ) * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1) *
      Complex.exp (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * z)
  let g' : ℕ → ℂ → ℂ := fun k z =>
    (-1 : ℂ) ^ (m + 1) * (2 : ℂ) ^ (-(((m + 2) * (k + 1) : ℕ) : ℤ)) *
      (Complex.exp (-2 * (Real.pi : ℂ) * I * (n : ℂ) * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1) *
      Complex.exp (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * z)
  have hnorm_fac : ∀ k : ℕ,
      ‖Complex.exp (-2 * (Real.pi : ℂ) * I * (n : ℂ) * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1‖ ≤ 2 := fun k => by
    let r : ℝ := (2 : ℝ) ^ (-(k + 1 : ℤ))
    have h2r : (2 : ℂ) ^ (-(k + 1 : ℤ)) = (r : ℂ) := by
      dsimp only [r]; rw [Complex.ofReal_zpow, Complex.ofReal_ofNat]
    have hre0 : (-2 * (Real.pi : ℂ) * I * (n : ℂ) * (2 : ℂ) ^ (-(k + 1 : ℤ))).re = 0 := by
      rw [h2r]; simp [Complex.mul_re, Complex.mul_im]
    calc ‖Complex.exp (-2 * (Real.pi : ℂ) * I * (n : ℂ) * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1‖
        ≤ ‖Complex.exp (-2 * (Real.pi : ℂ) * I * (n : ℂ) * (2 : ℂ) ^ (-(k + 1 : ℤ)))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [Complex.norm_exp, hre0, Real.exp_zero, norm_one]
      _ = 2 := by norm_num
  have hnorm_exp : ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball z₀ 1 →
      ‖Complex.exp (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * z)‖ ≤ Real.exp (‖z₀‖ + 1) := fun k z hz => by
    have hz_le : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have h1 : ‖z - z₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ 1 + ‖z₀‖ := by linarith
        _ = ‖z₀‖ + 1 := add_comm _ _
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have hpow_le1 : ‖-(2 : ℂ) ^ (-(k + 1 : ℤ))‖ ≤ 1 := by
      rw [norm_neg, norm_zpow, Complex.norm_ofNat, zpow_neg,
        show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    calc (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * z).re ≤ ‖-(2 : ℂ) ^ (-(k + 1 : ℤ)) * z‖ := Complex.re_le_norm _
      _ = ‖-(2 : ℂ) ^ (-(k + 1 : ℤ))‖ * ‖z‖ := norm_mul _ _
      _ ≤ 1 * (‖z₀‖ + 1) := mul_le_mul hpow_le1 hz_le (norm_nonneg _) zero_le_one
      _ = ‖z₀‖ + 1 := one_mul _
  have hpow2_le : ∀ (p k : ℕ), 1 ≤ p → ‖(2 : ℂ) ^ (-((p * (k + 1) : ℕ) : ℤ))‖ ≤ (1 / 2 : ℝ) ^ k := fun p k hp => by
    rw [norm_zpow, Complex.norm_ofNat, zpow_neg, zpow_natCast, one_div_pow, one_div]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show k ≤ p * (k + 1) by nlinarith))
  let u : ℕ → ℝ := fun k => (2 * Real.exp (‖z₀‖ + 1)) * (1 / 2 : ℝ) ^ k
  have hu_sum : Summable u := (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hsum_g0 : Summable (fun k : ℕ => g k z₀) := by
    refine Summable.of_norm_bounded hu_sum fun k => ?_
    dsimp only [g, u]
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc ‖(2 : ℂ) ^ (-(((m + 1) * (k + 1) : ℕ) : ℤ))‖ *
            ‖Complex.exp (-2 * (Real.pi : ℂ) * I * (n : ℂ) * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1‖ *
            ‖Complex.exp (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * z₀)‖
        ≤ (1 / 2 : ℝ) ^ k * 2 * Real.exp (‖z₀‖ + 1) :=
          mul_le_mul (mul_le_mul (hpow2_le (m + 1) k (by omega)) (hnorm_fac k) (norm_nonneg _) (by positivity))
            (hnorm_exp k z₀ (Metric.mem_ball_self zero_lt_one)) (norm_nonneg _) (by positivity)
      _ = 2 * Real.exp (‖z₀‖ + 1) * (1 / 2 : ℝ) ^ k := by ring
  have hderiv_each : ∀ k : ℕ, ∀ z ∈ Metric.ball z₀ 1, HasDerivAt (g k) (g' k z) z := fun k z _ => by
    have hd : HasDerivAt (g k)
        ((-1 : ℂ) ^ m * (2 : ℂ) ^ (-(((m + 1) * (k + 1) : ℕ) : ℤ)) *
          (Complex.exp (-2 * (Real.pi : ℂ) * I * (n : ℂ) * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1) *
          (Complex.exp (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * z) * (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * 1))) z :=
      ((hasDerivAt_id z).const_mul (-(2 : ℂ) ^ (-(k + 1 : ℤ)))).cexp.const_mul _
    refine hd.congr_deriv ?_
    dsimp only [g']
    have h2ne : (2 : ℂ) ≠ 0 := by norm_num
    have hpow_comb : (2 : ℂ) ^ (-(((m + 1) * (k + 1) : ℕ) : ℤ)) * (2 : ℂ) ^ (-(k + 1 : ℤ)) =
        (2 : ℂ) ^ (-(((m + 2) * (k + 1) : ℕ) : ℤ)) := by
      rw [← zpow_add₀ h2ne]; congr 1; push_cast; ring
    rw [pow_succ, ← hpow_comb]; ring
  have hbd_g' : ∀ k : ℕ, ∀ z ∈ Metric.ball z₀ 1, ‖g' k z‖ ≤ u k := fun k z hz => by
    dsimp only [g', u]
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc ‖(2 : ℂ) ^ (-(((m + 2) * (k + 1) : ℕ) : ℤ))‖ *
            ‖Complex.exp (-2 * (Real.pi : ℂ) * I * (n : ℂ) * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1‖ *
            ‖Complex.exp (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * z)‖
        ≤ (1 / 2 : ℝ) ^ k * 2 * Real.exp (‖z₀‖ + 1) :=
          mul_le_mul (mul_le_mul (hpow2_le (m + 2) k (by omega)) (hnorm_fac k) (norm_nonneg _) (by positivity))
            (hnorm_exp k z hz) (norm_nonneg _) (by positivity)
      _ = 2 * Real.exp (‖z₀‖ + 1) * (1 / 2 : ℝ) ^ k := by ring
  exact hasDerivAt_tsum_of_isPreconnected hu_sum Metric.isOpen_ball (convex_ball z₀ 1).isPreconnected
    hderiv_each hbd_g' (Metric.mem_ball_self zero_lt_one) hsum_g0 (Metric.mem_ball_self zero_lt_one)

/-- Closed-form termwise `j`-th derivative of the entire shift remainder `shiftRemainder n`. -/
theorem iteratedDeriv_shiftRemainder (n : ℤ) (j : ℕ) (x : ℂ) :
    iteratedDeriv j (shiftRemainder n) x =
      ∑' k : ℕ, (-1 : ℂ) ^ j * (2 : ℂ) ^ (-(((j + 1) * (k + 1) : ℕ) : ℤ)) *
        (Complex.exp (-2 * (Real.pi : ℂ) * I * (n : ℂ) * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1) *
        Complex.exp (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * x) := by
  induction j generalizing x with
  | zero =>
    simp only [iteratedDeriv_zero, pow_zero, one_mul, zero_add, Nat.cast_add, Nat.cast_one]
    unfold shiftRemainder
    refine tsum_congr fun k => by congr 3
  | succ j ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv j (shiftRemainder n) =
        fun z : ℂ => ∑' k : ℕ, (-1 : ℂ) ^ j * (2 : ℂ) ^ (-(((j + 1) * (k + 1) : ℕ) : ℤ)) *
          (Complex.exp (-2 * (Real.pi : ℂ) * I * (n : ℂ) * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1) *
          Complex.exp (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * z) := funext ih
    rw [hfun]
    exact (hasDerivAt_shiftRemainder_iter n j x).deriv

/-- Every shift remainder `shiftRemainder n` is an entire function on `ℂ`. -/
theorem shiftRemainder_differentiable (n : ℤ) : Differentiable ℂ (shiftRemainder n) := by
  intro z₀
  have hfun : shiftRemainder n =
      fun z : ℂ => ∑' k : ℕ, (-1 : ℂ) ^ (0 : ℕ) * (2 : ℂ) ^ (-((((0 : ℕ) + 1) * (k + 1) : ℕ) : ℤ)) *
        (Complex.exp (-2 * (Real.pi : ℂ) * I * (n : ℂ) * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1) *
        Complex.exp (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * z) := by
    funext z; simpa using iteratedDeriv_shiftRemainder n 0 z
  rw [hfun]
  exact (hasDerivAt_shiftRemainder_iter n 0 z₀).differentiableAt

/-- **Nonvanishing of ALL Derivatives of `shiftRemainder 1` at `0`**:
For EVERY `j : ℕ`, `iteratedDeriv j (shiftRemainder 1) 0 ≠ 0`
(exact real-part sign bound `(-1)^j · Re(F_1^{(j)}(0)) ≤ -2^{-j} < 0`). -/
theorem shiftRemainder_one_iteratedDeriv_zero_ne_zero (j : ℕ) :
    iteratedDeriv j (shiftRemainder 1) 0 ≠ 0 := by
  rw [iteratedDeriv_shiftRemainder 1 j 0]
  have hsimp : (∑' k : ℕ, (-1 : ℂ) ^ j * (2 : ℂ) ^ (-(((j + 1) * (k + 1) : ℕ) : ℤ)) *
        (Complex.exp (-2 * (Real.pi : ℂ) * I * (1 : ℤ) * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1) *
        Complex.exp (-(2 : ℂ) ^ (-(k + 1 : ℤ)) * 0)) =
      (-1 : ℂ) ^ j * ∑' k : ℕ, (2 : ℂ) ^ (-(((j + 1) * (k + 1) : ℕ) : ℤ)) *
        (Complex.exp (-2 * (Real.pi : ℂ) * I * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => by simp [mul_assoc]
  rw [hsimp]
  refine mul_ne_zero (pow_ne_zero j (by norm_num)) ?_
  let term : ℕ → ℂ := fun k => (2 : ℂ) ^ (-(((j + 1) * (k + 1) : ℕ) : ℤ)) *
    (Complex.exp (-2 * (Real.pi : ℂ) * I * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1)
  have hsum : Summable term := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_left 2)
      fun k => ?_
    dsimp only [term]
    rw [norm_mul, norm_zpow, Complex.norm_ofNat, zpow_neg, zpow_natCast]
    have hpow : ((2 : ℝ) ^ ((j + 1) * (k + 1)))⁻¹ ≤ (1 / 2 : ℝ) ^ k := by
      rw [one_div_pow, one_div]
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show k ≤ (j + 1) * (k + 1) by nlinarith))
    have hfac : ‖Complex.exp (-2 * (Real.pi : ℂ) * I * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1‖ ≤ 2 := by
      let r : ℝ := (2 : ℝ) ^ (-(k + 1 : ℤ))
      have h2r : (2 : ℂ) ^ (-(k + 1 : ℤ)) = (r : ℂ) := by
        dsimp only [r]; rw [Complex.ofReal_zpow, Complex.ofReal_ofNat]
      have hre0 : (-2 * (Real.pi : ℂ) * I * (2 : ℂ) ^ (-(k + 1 : ℤ))).re = 0 := by
        rw [h2r]; simp [Complex.mul_re, Complex.mul_im]
      calc ‖Complex.exp (-2 * (Real.pi : ℂ) * I * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1‖
          ≤ ‖Complex.exp (-2 * (Real.pi : ℂ) * I * (2 : ℂ) ^ (-(k + 1 : ℤ)))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [Complex.norm_exp, hre0, Real.exp_zero, norm_one]; norm_num
    calc ((2 : ℝ) ^ ((j + 1) * (k + 1)))⁻¹ * ‖Complex.exp (-2 * (Real.pi : ℂ) * I * (2 : ℂ) ^ (-(k + 1 : ℤ))) - 1‖
        ≤ (1 / 2 : ℝ) ^ k * 2 := mul_le_mul hpow hfac (norm_nonneg _) (by positivity)
      _ = 2 * (1 / 2 : ℝ) ^ k := mul_comm _ _
  have hre_term : ∀ k : ℕ, (term k).re =
      (2 : ℝ) ^ (-(((j + 1) * (k + 1) : ℕ) : ℤ)) * (Real.cos (2 * Real.pi * (2 : ℝ) ^ (-(k + 1 : ℤ))) - 1) := by
    intro k
    dsimp only [term]
    let r1 : ℝ := (2 : ℝ) ^ (-(((j + 1) * (k + 1) : ℕ) : ℤ))
    let r2 : ℝ := (2 : ℝ) ^ (-(k + 1 : ℤ))
    have h2a : (2 : ℂ) ^ (-(((j + 1) * (k + 1) : ℕ) : ℤ)) = (r1 : ℂ) := by
      dsimp only [r1]; rw [Complex.ofReal_zpow, Complex.ofReal_ofNat]
    have h2b : (2 : ℂ) ^ (-(k + 1 : ℤ)) = (r2 : ℂ) := by
      dsimp only [r2]; rw [Complex.ofReal_zpow, Complex.ofReal_ofNat]
    rw [h2a, h2b, Complex.re_ofReal_mul, Complex.sub_re, Complex.one_re, Complex.exp_re]
    have harg_re : (-2 * (Real.pi : ℂ) * I * (r2 : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    have harg_im : (-2 * (Real.pi : ℂ) * I * (r2 : ℂ)).im = -(2 * Real.pi * r2) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [harg_re, Real.exp_zero, one_mul, harg_im, Real.cos_neg]
  have hre_le_zero : ∀ k : ℕ, (term k).re ≤ 0 := fun k => by
    rw [hre_term k]
    exact mul_nonpos_of_nonneg_of_nonpos (zpow_nonneg (by norm_num) _)
      (sub_nonpos.mpr (Real.cos_le_one _))
  have hre_zero_lt : (term 0).re < 0 := by
    rw [hre_term 0]
    have hcos : Real.cos (2 * Real.pi * (2 : ℝ) ^ (-((0 : ℕ) + 1 : ℤ))) = -1 := by
      have : 2 * Real.pi * (2 : ℝ) ^ (-((0 : ℕ) + 1 : ℤ)) = Real.pi := by norm_num; ring
      rw [this, Real.cos_pi]
    rw [hcos]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(((j + 1) * (0 + 1) : ℕ) : ℤ)) := zpow_pos (by norm_num) _
    linarith
  have hre_sum_neg : (∑' k : ℕ, term k).re < 0 := by
    rw [Complex.re_tsum hsum]
    have hsum_re : Summable (fun k : ℕ => (term k).re) := Complex.reCLM.summable hsum
    rw [hsum_re.tsum_eq_zero_add]
    have htail : ∑' k : ℕ, (term (k + 1)).re ≤ 0 := by
      have hle := Summable.tsum_le_tsum (fun k => hre_le_zero (k + 1))
        (hsum_re.comp_injective Nat.succ_injective) summable_zero
      simpa using hle
    linarith
  intro h0
  rw [h0, Complex.zero_re] at hre_sum_neg
  linarith

/-- Higher-derivative scaling law for `masterLacunary`:
`masterLacunary^{(j)}(2^{-N} s) = 2^{(j+1) N} masterLacunary^{(j)}(s)` on `{0 < s.re}`. -/
private lemma iteratedDeriv_masterLacunary_scaling (N : ℤ) (j : ℕ) {s : ℂ} (hs : 0 < s.re) :
    iteratedDeriv j masterLacunary ((2 : ℂ) ^ (-N) * s) =
      (2 : ℂ) ^ (((j + 1 : ℕ) : ℤ) * N) * iteratedDeriv j masterLacunary s := by
  induction j generalizing s with
  | zero =>
    simp only [iteratedDeriv_zero, zero_add, Nat.cast_one, one_mul]
    exact masterLacunary_scaling N s hs
  | succ j ih =>
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2N_pos : (0 : ℝ) < (2 : ℝ) ^ (-N) := zpow_pos (by norm_num) (-N)
    have h2N_eq : (2 : ℂ) ^ (-N) = (((2 : ℝ) ^ (-N) : ℝ) : ℂ) := by
      rw [Complex.ofReal_zpow, Complex.ofReal_ofNat]
    have hdiff_j : ∀ m : ℕ, DifferentiableOn ℂ (iteratedDeriv m masterLacunary) {w : ℂ | 0 < w.re} := by
      intro m
      have han : AnalyticOnNhd ℂ masterLacunary {w : ℂ | 0 < w.re} :=
        masterLacunary_differentiableOn.analyticOnNhd hopen
      clear ih
      induction m with
      | zero => simpa using masterLacunary_differentiableOn
      | succ m ihm =>
        have : AnalyticOnNhd ℂ (iteratedDeriv m masterLacunary) {w : ℂ | 0 < w.re} := ihm.analyticOnNhd hopen
        simpa [iteratedDeriv_succ] using this.deriv.differentiableOn
    have heq_nhds : (fun w : ℂ => iteratedDeriv j masterLacunary ((2 : ℂ) ^ (-N) * w)) =ᶠ[𝓝 s]
        fun w : ℂ => (2 : ℂ) ^ (((j + 1 : ℕ) : ℤ) * N) * iteratedDeriv j masterLacunary w := by
      filter_upwards [hopen.mem_nhds hs] with w hw
      exact ih hw
    have hs_scaled : 0 < ((2 : ℂ) ^ (-N) * s).re := by
      rw [h2N_eq, Complex.re_ofReal_mul]; exact mul_pos h2N_pos hs
    have hd_lhs : HasDerivAt (fun w : ℂ => iteratedDeriv j masterLacunary ((2 : ℂ) ^ (-N) * w))
        (iteratedDeriv (j + 1) masterLacunary ((2 : ℂ) ^ (-N) * s) * (2 : ℂ) ^ (-N)) s := by
      have hd1 : HasDerivAt (iteratedDeriv j masterLacunary)
          (iteratedDeriv (j + 1) masterLacunary ((2 : ℂ) ^ (-N) * s)) ((2 : ℂ) ^ (-N) * s) := by
        rw [iteratedDeriv_succ]
        exact ((hdiff_j j).differentiableAt (hopen.mem_nhds hs_scaled)).hasDerivAt
      have hd2 : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ (-N) * w) ((2 : ℂ) ^ (-N)) s := by
        simpa using (hasDerivAt_id s).const_mul ((2 : ℂ) ^ (-N))
      exact hd1.comp s hd2
    have hd_rhs : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ (((j + 1 : ℕ) : ℤ) * N) * iteratedDeriv j masterLacunary w)
        ((2 : ℂ) ^ (((j + 1 : ℕ) : ℤ) * N) * iteratedDeriv (j + 1) masterLacunary s) s := by
      have hd1 : HasDerivAt (iteratedDeriv j masterLacunary) (iteratedDeriv (j + 1) masterLacunary s) s := by
        rw [iteratedDeriv_succ]
        exact ((hdiff_j j).differentiableAt (hopen.mem_nhds hs)).hasDerivAt
      exact hd1.const_mul _
    have huniq := hd_lhs.unique (hd_rhs.congr_of_eventuallyEq heq_nhds)
    have h2ne : (2 : ℂ) ≠ 0 := by norm_num
    have hmul := congrArg (fun z : ℂ => z * (2 : ℂ) ^ N) huniq
    rw [mul_assoc, ← zpow_add₀ h2ne, neg_add_cancel, zpow_zero, mul_one] at hmul
    rw [hmul, mul_right_comm, ← zpow_add₀ h2ne]
    congr 2; push_cast; ring

/-- Higher-derivative shift law for `masterLacunary`:
`masterLacunary^{(j)}(s + 2πi n) = masterLacunary^{(j)}(s) + (shiftRemainder n)^{(j)}(s)` on `{0 < s.re}`. -/
private lemma iteratedDeriv_masterLacunary_shift (n : ℤ) (j : ℕ) {s : ℂ} (hs : 0 < s.re) :
    iteratedDeriv j masterLacunary (s + 2 * (Real.pi : ℂ) * I * (n : ℂ)) =
      iteratedDeriv j masterLacunary s + iteratedDeriv j (shiftRemainder n) s := by
  induction j generalizing s with
  | zero =>
    simp only [iteratedDeriv_zero]
    exact masterLacunary_shift n s hs
  | succ j ih =>
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hdiff_j : ∀ m : ℕ, DifferentiableOn ℂ (iteratedDeriv m masterLacunary) {w : ℂ | 0 < w.re} := by
      intro m
      clear ih
      induction m with
      | zero => simpa using masterLacunary_differentiableOn
      | succ m ihm =>
        simpa [iteratedDeriv_succ] using (ihm.analyticOnNhd hopen).deriv.differentiableOn
    have hdiff_F : Differentiable ℂ (iteratedDeriv j (shiftRemainder n)) :=
      ((shiftRemainder_differentiable n).contDiff (n := (⊤ : ℕ∞))).differentiable_iteratedDeriv j
        (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top j))
    have heq_nhds : (fun w : ℂ => iteratedDeriv j masterLacunary (w + 2 * (Real.pi : ℂ) * I * (n : ℂ))) =ᶠ[𝓝 s]
        fun w : ℂ => iteratedDeriv j masterLacunary w + iteratedDeriv j (shiftRemainder n) w := by
      filter_upwards [hopen.mem_nhds hs] with w hw
      exact ih hw
    have hs_shift : 0 < (s + 2 * (Real.pi : ℂ) * I * (n : ℂ)).re := by
      rw [Complex.add_re]
      have h0 : (2 * (Real.pi : ℂ) * I * (n : ℂ)).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
      rw [h0, add_zero]; exact hs
    have hd_lhs : HasDerivAt (fun w : ℂ => iteratedDeriv j masterLacunary (w + 2 * (Real.pi : ℂ) * I * (n : ℂ)))
        (iteratedDeriv (j + 1) masterLacunary (s + 2 * (Real.pi : ℂ) * I * (n : ℂ))) s := by
      have hd1 : HasDerivAt (iteratedDeriv j masterLacunary)
          (iteratedDeriv (j + 1) masterLacunary (s + 2 * (Real.pi : ℂ) * I * (n : ℂ)))
          (s + 2 * (Real.pi : ℂ) * I * (n : ℂ)) := by
        rw [iteratedDeriv_succ]
        exact ((hdiff_j j).differentiableAt (hopen.mem_nhds hs_shift)).hasDerivAt
      have hd2 : HasDerivAt (fun w : ℂ => w + 2 * (Real.pi : ℂ) * I * (n : ℂ)) 1 s :=
        (hasDerivAt_id s).add_const (2 * (Real.pi : ℂ) * I * (n : ℂ))
      have hc := hd1.comp s hd2
      rw [mul_one] at hc
      exact hc
    have hd_rhs : HasDerivAt (fun w : ℂ => iteratedDeriv j masterLacunary w + iteratedDeriv j (shiftRemainder n) w)
        (iteratedDeriv (j + 1) masterLacunary s + iteratedDeriv (j + 1) (shiftRemainder n) s) s := by
      have hd1 : HasDerivAt (iteratedDeriv j masterLacunary) (iteratedDeriv (j + 1) masterLacunary s) s := by
        rw [iteratedDeriv_succ]
        exact ((hdiff_j j).differentiableAt (hopen.mem_nhds hs)).hasDerivAt
      have hd2 : HasDerivAt (iteratedDeriv j (shiftRemainder n)) (iteratedDeriv (j + 1) (shiftRemainder n) s) s := by
        rw [iteratedDeriv_succ]
        exact (hdiff_F s).hasDerivAt
      exact hd1.add hd2
    exact hd_lhs.unique (hd_rhs.congr_of_eventuallyEq heq_nhds)

/-! ### 5B. Steps 5–6: Unconditional Shift-and-Scale D-Transcendence of `masterLacunary` -/

/-- First-order multivariate Taylor identity with continuous quadratic remainder `R(a, h, τ)`. -/
private lemma mvPoly_taylor_first_order {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ) :
    ∃ R : (Fin (r + 1) → ℂ) → (Fin (r + 1) → ℂ) → ℂ → ℂ,
      (∀ a : Fin (r + 1) → ℂ, Continuous fun p : (Fin (r + 1) → ℂ) × ℂ => R a p.1 p.2) ∧
      ∀ (a h : Fin (r + 1) → ℂ) (τ : ℂ),
        MvPolynomial.eval (fun j => a j + τ * h j) P =
          MvPolynomial.eval a P +
          τ * (∑ j : Fin (r + 1), MvPolynomial.eval a (MvPolynomial.pderiv j P) * h j) +
          τ ^ 2 * R a h τ := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨fun _ _ _ => 0, fun _ => continuous_const, fun a h τ => ?_⟩
    simp
  | add P Q ihP ihQ =>
    obtain ⟨RP, hRP_cont, hRP⟩ := ihP
    obtain ⟨RQ, hRQ_cont, hRQ⟩ := ihQ
    refine ⟨fun a h τ => RP a h τ + RQ a h τ, fun a => (hRP_cont a).add (hRQ_cont a), fun a h τ => ?_⟩
    simp only [map_add, Finset.sum_add_distrib, add_mul, hRP, hRQ]
    ring
  | mul_X P i ihP =>
    obtain ⟨RP, hRP_cont, hRP⟩ := ihP
    let L : (Fin (r + 1) → ℂ) → (Fin (r + 1) → ℂ) → ℂ :=
      fun a h => ∑ j : Fin (r + 1), MvPolynomial.eval a (MvPolynomial.pderiv j P) * h j
    refine ⟨fun a h τ => RP a h τ * a i + L a h * h i + τ * RP a h τ * h i, fun a => ?_, fun a h τ => ?_⟩
    · have hL_cont : Continuous fun p : (Fin (r + 1) → ℂ) × ℂ => L a p.1 := by
        dsimp only [L]
        have hsum_cont : ∀ (s : Finset (Fin (r + 1))),
            Continuous fun p : (Fin (r + 1) → ℂ) × ℂ =>
              ∑ j ∈ s, MvPolynomial.eval a (MvPolynomial.pderiv j P) * p.1 j := by
          intro s
          induction s using Finset.induction_on with
          | empty => simp [continuous_const]
          | insert j s hj ih =>
            have hrew : (fun p : (Fin (r + 1) → ℂ) × ℂ =>
                ∑ k ∈ insert j s, MvPolynomial.eval a (MvPolynomial.pderiv k P) * p.1 k) =
                fun p => MvPolynomial.eval a (MvPolynomial.pderiv j P) * p.1 j +
                  ∑ k ∈ s, MvPolynomial.eval a (MvPolynomial.pderiv k P) * p.1 k := by
              funext p; exact Finset.sum_insert hj
            rw [hrew]
            exact (continuous_const.mul ((continuous_apply j).comp continuous_fst)).add ih
        exact hsum_cont Finset.univ
      have hhi_cont : Continuous fun p : (Fin (r + 1) → ℂ) × ℂ => p.1 i :=
        (continuous_apply i).comp continuous_fst
      exact (((hRP_cont a).mul continuous_const).add (hL_cont.mul hhi_cont)).add
        ((continuous_snd.mul (hRP_cont a)).mul hhi_cont)
    · rw [map_mul, MvPolynomial.eval_X, hRP a h τ, map_mul, MvPolynomial.eval_X]
      have hsum_X : ∑ j : Fin (r + 1), MvPolynomial.eval a (MvPolynomial.pderiv j (P * MvPolynomial.X i)) * h j =
          L a h * a i + MvPolynomial.eval a P * h i := by
        have hterm : ∀ j : Fin (r + 1),
            MvPolynomial.eval a (MvPolynomial.pderiv j (P * MvPolynomial.X i)) * h j =
              (MvPolynomial.eval a (MvPolynomial.pderiv j P) * h j) * a i +
              (if j = i then MvPolynomial.eval a P * h i else 0) := fun j => by
          rw [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, smul_eq_mul, smul_eq_mul,
            map_add, map_mul, map_mul, MvPolynomial.eval_X]
          by_cases hji : j = i
          · subst hji; simp; ring
          · simp [hji, Ne.symm hji]; ring
        simp_rw [hterm, Finset.sum_add_distrib, ← Finset.sum_mul]
        simp [L]
      rw [hsum_X]
      ring

/-- Helper: `2^{-(m * N)} → 0` in `ℂ` as `N → ∞` for every `m ≥ 1`. -/
private lemma tendsto_two_zpow_neg_mul_zero (m : ℕ) (hm : 0 < m) :
    Filter.Tendsto (fun N : ℕ => (2 : ℂ) ^ (-(((m : ℕ) : ℤ) * (N : ℤ)))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have heq : (fun N : ℕ => ‖(2 : ℂ) ^ (-(((m : ℕ) : ℤ) * (N : ℤ)))‖) = fun N : ℕ => ((1 / 2 : ℝ) ^ m) ^ N := by
    funext N
    rw [norm_zpow, Complex.norm_ofNat, zpow_neg,
      show ((m : ℕ) : ℤ) * (N : ℤ) = ((m * N : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    simp only [one_div, inv_pow, ← pow_mul]
  rw [heq]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
    (pow_lt_one₀ (by norm_num) (by norm_num) hm.ne')

/-- If `pderiv j P = 0` in `MvPolynomial (Fin (r + 1)) ℂ`, then every monomial in `P.support` has `α j = 0`. -/
private lemma coeff_zero_of_pderiv_eq_zero {r : ℕ} {P : MvPolynomial (Fin (r + 1)) ℂ} {j : Fin (r + 1)}
    (hpd : MvPolynomial.pderiv j P = 0) {α : Fin (r + 1) →₀ ℕ} (hα : α ∈ P.support) :
    α j = 0 := by
  by_contra hpos
  have h1 : 1 ≤ α j := Nat.pos_of_ne_zero hpos
  let β : Fin (r + 1) →₀ ℕ := α - Finsupp.single j 1
  have hβ_add : β + Finsupp.single j 1 = α := by
    ext k
    simp only [β, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
    by_cases hkj : k = j
    · subst hkj; simp; omega
    · simp [Ne.symm hkj]
  have hc : (MvPolynomial.pderiv j P).coeff β = 0 := by simp [hpd]
  rw [MvPolynomial.coeff_pderiv, hβ_add] at hc
  have hne : ((β j : ℕ) + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (β j)
  have hα_ne : P.coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα
  exact mul_ne_zero hα_ne hne hc

/-- Weight of a multi-index `α : Fin (r + 1) →₀ ℕ` under `u^{(j)}` scaling weight `j + 1`. -/
private def jetWeight {r : ℕ} (α : Fin (r + 1) →₀ ℕ) : ℕ :=
  ∑ j : Fin (r + 1), (j.val + 1) * α j

/-- If `P` is weight-homogeneous of weight `W`, then `pderiv j₀ P` is weight-homogeneous of weight `W - (j₀ + 1)`. -/
private lemma pderiv_weight_homog {r W : ℕ} {P : MvPolynomial (Fin (r + 1)) ℂ}
    (hhom : ∀ α ∈ P.support, jetWeight α = W) (j₀ : Fin (r + 1)) :
    ∀ β ∈ (MvPolynomial.pderiv j₀ P).support, jetWeight β = W - (j₀.val + 1) := by
  intro β hβ
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hβ
  have hmem : β + Finsupp.single j₀ 1 ∈ P.support :=
    MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hβ)
  have hW := hhom (β + Finsupp.single j₀ 1) hmem
  have hadd : jetWeight (β + Finsupp.single j₀ 1) = jetWeight β + (j₀.val + 1) := by
    unfold jetWeight
    simp only [Finsupp.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single j₀]
    · simp
    · intro k _ hkj; simp [Ne.symm hkj]
    · intro h; exact absurd (Finset.mem_univ j₀) h
  omega

/-- **Step 6 (Infinite Descent on Total Degree)**:
No nonzero constant-coefficient weight-homogeneous polynomial `P₀ ∈ ℂ[U_0, ..., U_r]`
can vanish on `(masterLacunary(s), ..., masterLacunary^{(r)}(s))` for all `0 < s.re`. -/
private lemma masterLacunary_no_const_homog_ade {r : ℕ} :
    ∀ (D : ℕ) (P₀ : MvPolynomial (Fin (r + 1)) ℂ) (W : ℕ),
      P₀.totalDegree ≤ D →
      P₀ ≠ 0 →
      (∀ α ∈ P₀.support, jetWeight α = W) →
      (∀ s : ℂ, 0 < s.re →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val masterLacunary s) P₀ = 0) →
      False := by
  intro D
  induction D with
  | zero =>
    intro P₀ _ hdeg hne _ hvan
    have hdeg0 : P₀.totalDegree = 0 := Nat.le_zero.mp hdeg
    have hconst : P₀ = MvPolynomial.C (P₀.coeff 0) := by
      ext α
      by_cases hα : α = 0
      · subst hα; simp
      · rw [MvPolynomial.coeff_C]
        simp only [Ne.symm hα, ↓reduceIte]
        by_contra hnz
        have hmem : α ∈ P₀.support := MvPolynomial.mem_support_iff.mpr hnz
        have hsum_le : α.sum (fun _ e => e) ≤ P₀.totalDegree :=
          Finset.le_sup (f := fun s : Fin (r + 1) →₀ ℕ => s.sum fun _ e => e) hmem
        rw [hdeg0] at hsum_le
        have hzero : α = 0 := by
          ext j
          have hj : α j ≤ α.sum (fun _ e => e) := by
            rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
            exact Finset.single_le_sum (f := fun k => α k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
          simp only [Finsupp.coe_zero, Pi.zero_apply]
          omega
        exact hα hzero
    have hc_ne : P₀.coeff 0 ≠ 0 := fun hc0 => hne (by rw [hconst, hc0, map_zero])
    have h1 := hvan 1 (by simp)
    rw [hconst, MvPolynomial.eval_C] at h1
    exact hc_ne h1
  | succ D ih =>
    intro P₀ W hdeg hne hhom hvan
    -- Pick the smallest variable index `j₀` with `pderiv j₀ P₀ ≠ 0`!
    let S : Finset (Fin (r + 1)) := Finset.univ.filter fun j => MvPolynomial.pderiv j P₀ ≠ 0
    have hS_ne : S.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hall : ∀ j : Fin (r + 1), MvPolynomial.pderiv j P₀ = 0 := fun j => by
        by_contra hnz
        have : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hnz⟩
        rw [hempty] at this; exact Finset.notMem_empty j this
      have hconst := all_partials_zero P₀ hall
      have hc_ne : P₀.coeff 0 ≠ 0 := fun h0 => hne (by rw [hconst, h0, map_zero])
      have h1 := hvan 1 (by simp)
      rw [hconst, MvPolynomial.eval_C] at h1
      exact hc_ne h1
    let j₀ : Fin (r + 1) := S.min' hS_ne
    have hj₀_mem : j₀ ∈ S := Finset.min'_mem S hS_ne
    have hpd_ne : MvPolynomial.pderiv j₀ P₀ ≠ 0 := (Finset.mem_filter.mp hj₀_mem).2
    have hpd_lt_zero : ∀ j : Fin (r + 1), j < j₀ → MvPolynomial.pderiv j P₀ = 0 := fun j hlt => by
      by_contra hnz
      have hmem : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hnz⟩
      exact not_le_of_gt hlt (Finset.min'_le S j hmem)
    have hP₀_pos : 0 < P₀.totalDegree := by
      by_contra h0
      have hdeg0 : P₀.totalDegree = 0 := by omega
      have hconst : P₀ = MvPolynomial.C (P₀.coeff 0) := by
        ext α
        by_cases hα : α = 0
        · subst hα; simp
        · rw [MvPolynomial.coeff_C]
          simp only [Ne.symm hα, ↓reduceIte]
          by_contra hnz
          have hmem : α ∈ P₀.support := MvPolynomial.mem_support_iff.mpr hnz
          have hsum_le : α.sum (fun _ e => e) ≤ P₀.totalDegree :=
            Finset.le_sup (f := fun s : Fin (r + 1) →₀ ℕ => s.sum fun _ e => e) hmem
          rw [hdeg0] at hsum_le
          have hzero : α = 0 := by
            ext j
            have hj : α j ≤ α.sum (fun _ e => e) := by
              rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
              exact Finset.single_le_sum (f := fun k => α k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
            simp only [Finsupp.coe_zero, Pi.zero_apply]; omega
          exact hα hzero
      rw [hconst, MvPolynomial.pderiv_C] at hpd_ne
      exact hpd_ne rfl
    have hpd_deg : (MvPolynomial.pderiv j₀ P₀).totalDegree ≤ D := by
      have hlt := degree_pderiv_lt j₀ P₀ hP₀_pos
      omega
    have hpd_hom : ∀ β ∈ (MvPolynomial.pderiv j₀ P₀).support, jetWeight β = W - (j₀.val + 1) :=
      pderiv_weight_homog hhom j₀
    -- Show `pderiv j₀ P₀` vanishes on `(u(s), ..., u^{(r)}(s))` for EVERY `0 < s.re`!
    obtain ⟨R, hR_cont, hR_eq⟩ := mvPoly_taylor_first_order P₀
    have hpd_van : ∀ s : ℂ, 0 < s.re →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val masterLacunary s)
          (MvPolynomial.pderiv j₀ P₀) = 0 := by
      intro s hs
      let a : Fin (r + 1) → ℂ := fun j => iteratedDeriv j.val masterLacunary s
      let τ : ℕ → ℂ := fun N => (2 : ℂ) ^ (-(((j₀.val + 1 : ℕ) : ℤ) * (N : ℤ)))
      let h : ℕ → Fin (r + 1) → ℂ := fun N j =>
        if j < j₀ then 0
        else (2 : ℂ) ^ (-(((j.val - j₀.val : ℕ) : ℤ) * (N : ℤ))) *
          iteratedDeriv j.val (shiftRemainder 1) ((2 : ℂ) ^ (-(N : ℤ)) * s)
      let hLim : Fin (r + 1) → ℂ := fun j =>
        if j = j₀ then iteratedDeriv j₀.val (shiftRemainder 1) 0 else 0
      -- For every `N : ℕ`, `P₀(a + τ N • h N) = 0`!
      have hP0_shifted : ∀ N : ℕ, MvPolynomial.eval (fun j => a j + τ N * h N j) P₀ = 0 := by
        intro N
        have h2N_pos : (0 : ℝ) < (2 : ℝ) ^ (-(N : ℤ)) := zpow_pos (by norm_num) _
        have h2N_eq : (2 : ℂ) ^ (-(N : ℤ)) = (((2 : ℝ) ^ (-(N : ℤ)) : ℝ) : ℂ) := by
          rw [Complex.ofReal_zpow, Complex.ofReal_ofNat]
        have hsN : 0 < ((2 : ℂ) ^ (-(N : ℤ)) * s).re := by
          rw [h2N_eq, Complex.re_ofReal_mul]; exact mul_pos h2N_pos hs
        have hsN_shift : 0 < ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * (1 : ℤ)).re := by
          rw [Complex.add_re]
          have h0 : (2 * (Real.pi : ℂ) * I * ((1 : ℤ) : ℂ)).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
          rw [h0, add_zero]; exact hsN
        have h0 := hvan ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * (1 : ℤ)) hsN_shift
        -- Express `u^{(j)}(2^{-N} s + 2πi) = 2^{(j+1) N} (a j + 2^{-(j+1)N} F_1^{(j)}(2^{-N} s))`!
        have h2ne : (2 : ℂ) ≠ 0 := by norm_num
        have hhom_pull : MvPolynomial.eval
              (fun j : Fin (r + 1) => iteratedDeriv j.val masterLacunary ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * (1 : ℤ))) P₀ =
            (2 : ℂ) ^ ((W : ℤ) * (N : ℤ)) * MvPolynomial.eval (fun j => a j + τ N * h N j) P₀ := by
          rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
          refine Finset.sum_congr rfl fun α hα => ?_
          have hprod : ∏ j : Fin (r + 1),
                (iteratedDeriv j.val masterLacunary ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * (1 : ℤ))) ^ (α j) =
              (2 : ℂ) ^ ((W : ℤ) * (N : ℤ)) * ∏ j : Fin (r + 1), (a j + τ N * h N j) ^ (α j) := by
            have hfac : ∀ j : Fin (r + 1),
                (iteratedDeriv j.val masterLacunary ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * (1 : ℤ))) ^ (α j) =
                  ((2 : ℂ) ^ (((j.val + 1 : ℕ) : ℤ) * (N : ℤ) * (α j : ℤ))) * (a j + τ N * h N j) ^ (α j) := by
              intro j
              by_cases hlt : j < j₀
              · have hαj : α j = 0 := coeff_zero_of_pderiv_eq_zero (hpd_lt_zero j hlt) hα
                simp [hαj]
              · have hge : j₀.val ≤ j.val := not_lt.mp hlt
                have hjet : iteratedDeriv j.val masterLacunary ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * (1 : ℤ)) =
                    (2 : ℂ) ^ (((j.val + 1 : ℕ) : ℤ) * (N : ℤ)) * (a j + τ N * h N j) := by
                  rw [iteratedDeriv_masterLacunary_shift 1 j.val hsN,
                    iteratedDeriv_masterLacunary_scaling (N : ℤ) j.val hs]
                  dsimp only [a, τ, h]
                  simp only [hlt, ↓reduceIte, mul_add]
                  congr 1
                  rw [← mul_assoc, ← mul_assoc, ← zpow_add₀ h2ne, ← zpow_add₀ h2ne]
                  have hexp0 : (((j.val + 1 : ℕ) : ℤ) * (N : ℤ)) +
                      (-(((j₀.val + 1 : ℕ) : ℤ) * (N : ℤ))) +
                      (-(((j.val - j₀.val : ℕ) : ℤ) * (N : ℤ))) = 0 := by
                    rw [Nat.cast_sub hge]; push_cast; ring
                  rw [hexp0, zpow_zero, one_mul]
                rw [hjet, mul_pow, ← zpow_natCast, ← zpow_mul]
            simp_rw [hfac, Finset.prod_mul_distrib]
            congr 1
            rw [← zpow_sum_complex h2ne]
            congr 1
            have hW := hhom α hα
            rw [← hW]; unfold jetWeight
            rw [Nat.cast_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => by push_cast; ring
          rw [hprod]; ring
        rw [hhom_pull] at h0
        exact (mul_eq_zero.mp h0).resolve_left (zpow_ne_zero _ h2ne)
      -- Divide the first-order Taylor expansion by `τ N ≠ 0`!
      have hdiv_zero : ∀ N : ℕ,
          (∑ j : Fin (r + 1), MvPolynomial.eval a (MvPolynomial.pderiv j P₀) * h N j) +
            τ N * R a (h N) (τ N) = 0 := by
        intro N
        have h1 := hR_eq a (h N) (τ N)
        rw [hP0_shifted N, hvan s hs, zero_add] at h1
        have hτ_ne : τ N ≠ 0 := zpow_ne_zero _ (by norm_num)
        have h2 : τ N * ((∑ j : Fin (r + 1), MvPolynomial.eval a (MvPolynomial.pderiv j P₀) * h N j) +
            τ N * R a (h N) (τ N)) = 0 := by
          linear_combination -h1
        exact (mul_eq_zero.mp h2).resolve_left hτ_ne
      -- Limits as `N → ∞`: `τ N → 0` and `h N → hLim`!
      have hτ_tend : Filter.Tendsto τ atTop (𝓝 0) :=
        tendsto_two_zpow_neg_mul_zero (j₀.val + 1) (Nat.succ_pos _)
      have hh_tend_coord : ∀ j : Fin (r + 1), Filter.Tendsto (fun N : ℕ => h N j) atTop (𝓝 (hLim j)) := by
        intro j
        by_cases hlt : j < j₀
        · have hne_j : j ≠ j₀ := ne_of_lt hlt
          simp only [h, hLim, hlt, ↓reduceIte, hne_j]
          exact tendsto_const_nhds
        · have hF_cont : Continuous (iteratedDeriv j.val (shiftRemainder 1)) :=
            (((shiftRemainder_differentiable 1).contDiff (n := (⊤ : ℕ∞))).differentiable_iteratedDeriv j.val
              (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top j.val))).continuous
          have harg0 : Filter.Tendsto (fun N : ℕ => (2 : ℂ) ^ (-(N : ℤ)) * s) atTop (𝓝 0) := by
            have h20 : Filter.Tendsto (fun N : ℕ => (2 : ℂ) ^ (-(N : ℤ))) atTop (𝓝 0) := by
              simpa only [Nat.cast_one, one_mul] using tendsto_two_zpow_neg_mul_zero 1 zero_lt_one
            simpa using h20.mul_const s
          have hF_tend : Filter.Tendsto (fun N : ℕ => iteratedDeriv j.val (shiftRemainder 1) ((2 : ℂ) ^ (-(N : ℤ)) * s))
              atTop (𝓝 (iteratedDeriv j.val (shiftRemainder 1) 0)) :=
            hF_cont.continuousAt.tendsto.comp harg0
          by_cases heq_j : j = j₀
          · subst heq_j
            simp only [h, hLim, lt_irrefl, ↓reduceIte, Nat.sub_self, Nat.cast_zero, zero_mul, neg_zero,
              zpow_zero, one_mul]
            exact hF_tend
          · have hgt : 0 < j.val - j₀.val := by
              have hge : j₀.val ≤ j.val := not_lt.mp hlt
              have hnev : j.val ≠ j₀.val := fun hv => heq_j (Fin.ext hv)
              omega
            have hpow0 := tendsto_two_zpow_neg_mul_zero (j.val - j₀.val) hgt
            simp only [h, hLim, hlt, heq_j, ↓reduceIte]
            simpa using hpow0.mul hF_tend
      have hh_tend : Filter.Tendsto h atTop (𝓝 hLim) := tendsto_pi_nhds.mpr hh_tend_coord
      have hR_tend : Filter.Tendsto (fun N : ℕ => R a (h N) (τ N)) atTop (𝓝 (R a hLim 0)) :=
        (hR_cont a).continuousAt.tendsto.comp (hh_tend.prodMk_nhds hτ_tend)
      have hlim : Filter.Tendsto (fun N : ℕ =>
          (∑ j : Fin (r + 1), MvPolynomial.eval a (MvPolynomial.pderiv j P₀) * h N j) +
            τ N * R a (h N) (τ N))
          atTop (𝓝 (MvPolynomial.eval a (MvPolynomial.pderiv j₀ P₀) * iteratedDeriv j₀.val (shiftRemainder 1) 0)) := by
        have hsum_lim : Filter.Tendsto (fun N : ℕ =>
            ∑ j : Fin (r + 1), MvPolynomial.eval a (MvPolynomial.pderiv j P₀) * h N j)
            atTop (𝓝 (∑ j : Fin (r + 1), MvPolynomial.eval a (MvPolynomial.pderiv j P₀) * hLim j)) :=
          tendsto_finset_sum_fr fun j _ => (hh_tend_coord j).const_mul _
        have hsum_val : (∑ j : Fin (r + 1), MvPolynomial.eval a (MvPolynomial.pderiv j P₀) * hLim j) =
            MvPolynomial.eval a (MvPolynomial.pderiv j₀ P₀) * iteratedDeriv j₀.val (shiftRemainder 1) 0 := by
          rw [Finset.sum_eq_single j₀]
          · simp [hLim]
          · intro j _ hne_j; simp [hLim, hne_j]
          · intro hn; exact absurd (Finset.mem_univ j₀) hn
        rw [hsum_val] at hsum_lim
        simpa using hsum_lim.add (hτ_tend.mul hR_tend)
      have h0_tend : Filter.Tendsto (fun N : ℕ =>
          (∑ j : Fin (r + 1), MvPolynomial.eval a (MvPolynomial.pderiv j P₀) * h N j) +
            τ N * R a (h N) (τ N)) atTop (𝓝 0) := by
        simp_rw [hdiv_zero]; exact tendsto_const_nhds
      have hprod0 := tendsto_nhds_unique hlim h0_tend
      exact (mul_eq_zero.mp hprod0).resolve_right (shiftRemainder_one_iteratedDeriv_zero_ne_zero j₀.val)
    exact ih (MvPolynomial.pderiv j₀ P₀) (W - (j₀.val + 1)) hpd_deg hpd_ne hpd_hom hpd_van

/-- **Master Shift-and-Scale Differential Transcendence Theorem (Steps 5–6)**:
`masterLacunary(x) = ∑_{m ∈ ℤ} 2^m e^{-2^m x}` satisfies NO nonzero polynomial ODE over `ℂ[x]`
on the right half-plane `{0 < s.re}`. -/
theorem masterLacunary_no_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ s : ℂ, 0 < s.re →
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val masterLacunary s)
        (P.map (Polynomial.evalRingHom s)) = 0) :
    P = 0 := by
  classical
  by_contra hP_ne
  -- Step 5: Pick maximal weight `W_max = sup_{α ∈ P.support} jetWeight α`, pick `α₀` achieving `W_max`,
  -- and pick `n : ℕ` so `(P.coeff α₀).eval (2πi n) ≠ 0`!
  obtain ⟨α₀, hα₀, hmax⟩ := Finset.exists_mem_eq_sup P.support (MvPolynomial.support_nonempty.mpr hP_ne)
    (fun α => jetWeight α)
  let W : ℕ := P.support.sup jetWeight
  have hα₀_wt : jetWeight α₀ = W := hmax.symm
  have hc₀_ne : P.coeff α₀ ≠ 0 := MvPolynomial.mem_support_iff.mp hα₀
  -- Since `P.coeff α₀` is a nonzero polynomial, it cannot vanish at all `2πi n` (`n : ℕ`):
  have hex_n : ∃ n : ℕ, (P.coeff α₀).eval (2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ)) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hinj : Function.Injective (fun n : ℕ => 2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ)) := by
      intro a b hab
      have hfac : (2 * (Real.pi : ℂ) * I) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) Complex.I_ne_zero
      have heq := mul_left_cancel₀ hfac hab
      exact_mod_cast heq
    let S : Finset ℂ := (Finset.range ((P.coeff α₀).natDegree + 1)).image
      (fun n : ℕ => 2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ))
    have hcard : S.card = (P.coeff α₀).natDegree + 1 := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    have hsub : S.val ⊆ (P.coeff α₀).roots := by
      intro z hz
      rw [Finset.mem_val, Finset.mem_image] at hz
      obtain ⟨n, _, rfl⟩ := hz
      exact (Polynomial.mem_roots hc₀_ne).mpr (hall n)
    have hle : S.card ≤ (P.coeff α₀).roots.card := by
      have hsub_nd : S.val ≤ (P.coeff α₀).roots :=
        (Multiset.le_iff_subset S.nodup).mpr hsub
      exact Multiset.card_le_card hsub_nd
    have hdeg_bd := Polynomial.card_roots' (P.coeff α₀)
    omega
  obtain ⟨n, hn⟩ := hex_n
  -- Define nonzero constant-coefficient weight-homogeneous `P₀` of weight `W`:
  let P₀ : MvPolynomial (Fin (r + 1)) ℂ :=
    ∑ α ∈ P.support.filter (fun α => jetWeight α = W),
      MvPolynomial.monomial α ((P.coeff α).eval (2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ)))
  have hP₀_coeff : ∀ α : Fin (r + 1) →₀ ℕ,
      P₀.coeff α = if α ∈ P.support ∧ jetWeight α = W then
        (P.coeff α).eval (2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ)) else 0 := by
    intro α
    dsimp only [P₀]
    rw [MvPolynomial.coeff_sum]
    simp_rw [MvPolynomial.coeff_monomial]
    by_cases hα : α ∈ P.support ∧ jetWeight α = W
    · have hmem : α ∈ P.support.filter (fun β => jetWeight β = W) := Finset.mem_filter.mpr hα
      rw [Finset.sum_eq_single α]
      · simp [hα]
      · intro β _ hβα; simp [hβα]
      · intro hnot; exact absurd hmem hnot
    · simp only [hα, ↓reduceIte]
      exact Finset.sum_eq_zero fun β hβ => by
        have hne : β ≠ α := fun h => hα (h ▸ Finset.mem_filter.mp hβ)
        simp [hne]
  have hP₀_ne : P₀ ≠ 0 := by
    intro h0
    have hc : P₀.coeff α₀ = 0 := by simp [h0]
    rw [hP₀_coeff α₀] at hc
    simp only [hα₀, hα₀_wt, and_self, ↓reduceIte] at hc
    exact hn hc
  have hP₀_hom : ∀ α ∈ P₀.support, jetWeight α = W := by
    intro α hα
    rw [MvPolynomial.mem_support_iff, hP₀_coeff α] at hα
    by_contra hneW
    have hnot : ¬ (α ∈ P.support ∧ jetWeight α = W) := fun h => hneW h.2
    simp only [hnot, ↓reduceIte] at hα
    exact hα rfl
  -- Show `P₀` vanishes on `(u(s), ..., u^{(r)}(s))` for all `0 < s.re` by plugging `2^{-N} s + 2πi n` into `P`!
  have hP₀_van : ∀ s : ℂ, 0 < s.re →
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val masterLacunary s) P₀ = 0 := by
    intro s hs
    have h2ne : (2 : ℂ) ≠ 0 := by norm_num
    let uJet : ℕ → Fin (r + 1) → ℂ := fun N j =>
      iteratedDeriv j.val masterLacunary s +
        (2 : ℂ) ^ (-(((j.val + 1 : ℕ) : ℤ) * (N : ℤ))) *
          iteratedDeriv j.val (shiftRemainder (n : ℤ)) ((2 : ℂ) ^ (-(N : ℤ)) * s)
    -- Divide `P(2^{-N} s + 2πi n; u(2^{-N} s + 2πi n), ...) = 0` by `2^{W N}`!
    have hzero_seq : ∀ N : ℕ,
        ∑ α ∈ P.support,
          ((P.coeff α).eval ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ)) *
            (2 : ℂ) ^ (-(((W - jetWeight α : ℕ) : ℤ) * (N : ℤ)))) *
            ∏ j : Fin (r + 1), (uJet N j) ^ (α j) = 0 := by
      intro N
      have h2N_pos : (0 : ℝ) < (2 : ℝ) ^ (-(N : ℤ)) := zpow_pos (by norm_num) _
      have h2N_eq : (2 : ℂ) ^ (-(N : ℤ)) = (((2 : ℝ) ^ (-(N : ℤ)) : ℝ) : ℂ) := by
        rw [Complex.ofReal_zpow, Complex.ofReal_ofNat]
      have hsN : 0 < ((2 : ℂ) ^ (-(N : ℤ)) * s).re := by
        rw [h2N_eq, Complex.re_ofReal_mul]; exact mul_pos h2N_pos hs
      have hsN_shift : 0 < ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ)).re := by
        rw [Complex.add_re]
        have h0 : (2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ)).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
        rw [h0, add_zero]; exact hsN
      have h0 := hP ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ)) hsN_shift
      rw [MvPolynomial.eval_map, MvPolynomial.eval₂_eq'] at h0
      have hmul0 : (2 : ℂ) ^ (-((W : ℤ) * (N : ℤ))) *
          (∑ α ∈ P.support, (P.coeff α).eval ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ)) *
            ∏ j : Fin (r + 1),
              (iteratedDeriv j.val masterLacunary ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ))) ^ (α j)) = 0 := by
        have h0' : (∑ α ∈ P.support, (P.coeff α).eval ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ)) *
            ∏ j : Fin (r + 1),
              (iteratedDeriv j.val masterLacunary ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ))) ^ (α j)) = 0 := by
          simpa only [Polynomial.coe_evalRingHom] using h0
        rw [h0', mul_zero]
      rw [Finset.mul_sum] at hmul0
      rw [← hmul0]
      refine Finset.sum_congr rfl fun α hα => ?_
      have hwt_le : jetWeight α ≤ W := Finset.le_sup (f := jetWeight) hα
      have hprod : ∏ j : Fin (r + 1),
            (iteratedDeriv j.val masterLacunary ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ))) ^ (α j) =
          (2 : ℂ) ^ (((jetWeight α : ℕ) : ℤ) * (N : ℤ)) * ∏ j : Fin (r + 1), (uJet N j) ^ (α j) := by
        have hfac : ∀ j : Fin (r + 1),
            (iteratedDeriv j.val masterLacunary ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ))) ^ (α j) =
              (2 : ℂ) ^ (((j.val + 1 : ℕ) : ℤ) * (N : ℤ) * (α j : ℤ)) * (uJet N j) ^ (α j) := fun j => by
          have hjet : iteratedDeriv j.val masterLacunary ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ)) =
              (2 : ℂ) ^ (((j.val + 1 : ℕ) : ℤ) * (N : ℤ)) * uJet N j := by
            rw [iteratedDeriv_masterLacunary_shift (n : ℤ) j.val hsN,
              iteratedDeriv_masterLacunary_scaling (N : ℤ) j.val hs]
            dsimp only [uJet]
            rw [mul_add, ← mul_assoc, ← zpow_add₀ h2ne, add_neg_cancel, zpow_zero, one_mul]
          rw [hjet, mul_pow, ← zpow_natCast, ← zpow_mul]
        simp_rw [hfac, Finset.prod_mul_distrib]
        congr 1
        rw [← zpow_sum_complex h2ne]
        congr 1
        unfold jetWeight
        rw [Nat.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => by push_cast; ring
      rw [hprod]
      have hpow_comb : (2 : ℂ) ^ (-((W : ℤ) * (N : ℤ))) * (2 : ℂ) ^ (((jetWeight α : ℕ) : ℤ) * (N : ℤ)) =
          (2 : ℂ) ^ (-(((W - jetWeight α : ℕ) : ℤ) * (N : ℤ))) := by
        rw [← zpow_add₀ h2ne]; congr 1; rw [Nat.cast_sub hwt_le]; ring
      calc ((P.coeff α).eval ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ)) *
              (2 : ℂ) ^ (-(((W - jetWeight α : ℕ) : ℤ) * (N : ℤ)))) *
              ∏ j : Fin (r + 1), (uJet N j) ^ (α j)
          = (P.coeff α).eval ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ)) *
              ((2 : ℂ) ^ (-((W : ℤ) * (N : ℤ))) * (2 : ℂ) ^ (((jetWeight α : ℕ) : ℤ) * (N : ℤ))) *
              ∏ j : Fin (r + 1), (uJet N j) ^ (α j) := by rw [hpow_comb]
        _ = (2 : ℂ) ^ (-((W : ℤ) * (N : ℤ))) *
              ((P.coeff α).eval ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ)) *
                ((2 : ℂ) ^ (((jetWeight α : ℕ) : ℤ) * (N : ℤ)) * ∏ j : Fin (r + 1), (uJet N j) ^ (α j))) := by ring
    -- Take `N → ∞`:
    have h2N_0 : Filter.Tendsto (fun N : ℕ => (2 : ℂ) ^ (-(N : ℤ)) * s) atTop (𝓝 0) := by
      have h20 : Filter.Tendsto (fun N : ℕ => (2 : ℂ) ^ (-(N : ℤ))) atTop (𝓝 0) := by
        simpa only [Nat.cast_one, one_mul] using tendsto_two_zpow_neg_mul_zero 1 zero_lt_one
      simpa using h20.mul_const s
    have huJet_tend : ∀ j : Fin (r + 1),
        Filter.Tendsto (fun N : ℕ => uJet N j) atTop (𝓝 (iteratedDeriv j.val masterLacunary s)) := by
      intro j
      have hF_cont : Continuous (iteratedDeriv j.val (shiftRemainder (n : ℤ))) :=
        (((shiftRemainder_differentiable (n : ℤ)).contDiff (n := (⊤ : ℕ∞))).differentiable_iteratedDeriv j.val
          (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top j.val))).continuous
      have hF_tend := hF_cont.continuousAt.tendsto.comp h2N_0
      have hpow0 := tendsto_two_zpow_neg_mul_zero (j.val + 1) (Nat.succ_pos _)
      simpa [uJet] using tendsto_const_nhds.add (hpow0.mul hF_tend)
    have htend : Filter.Tendsto (fun N : ℕ =>
        ∑ α ∈ P.support,
          ((P.coeff α).eval ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ)) *
            (2 : ℂ) ^ (-(((W - jetWeight α : ℕ) : ℤ) * (N : ℤ)))) *
            ∏ j : Fin (r + 1), (uJet N j) ^ (α j))
        atTop (𝓝 (MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val masterLacunary s) P₀)) := by
      rw [MvPolynomial.eval_eq']
      have hsub_sup : P₀.support ⊆ P.support := fun α hα => by
        rw [MvPolynomial.mem_support_iff, hP₀_coeff α] at hα
        by_contra hnot
        have : ¬ (α ∈ P.support ∧ jetWeight α = W) := fun h => hnot h.1
        simp only [this, ↓reduceIte] at hα; exact hα rfl
      rw [Finset.sum_subset hsub_sup (fun α _ hnot => by
        rw [MvPolynomial.notMem_support_iff.mp hnot, zero_mul])]
      refine tendsto_finset_sum_fr fun α hα => ?_
      have harg_tend : Filter.Tendsto (fun N : ℕ => (2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ))
          atTop (𝓝 (2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ))) := by
        simpa using h2N_0.add tendsto_const_nhds
      have hc_tend : Filter.Tendsto (fun N : ℕ =>
          (P.coeff α).eval ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ)))
          atTop (𝓝 ((P.coeff α).eval (2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ)))) :=
        (differentiable_poly_eval_complex (P.coeff α)).continuous.continuousAt.tendsto.comp harg_tend
      have hp_tend : Filter.Tendsto (fun N : ℕ => ∏ j : Fin (r + 1), (uJet N j) ^ (α j))
          atTop (𝓝 (∏ j : Fin (r + 1), (iteratedDeriv j.val masterLacunary s) ^ (α j))) :=
        tendsto_finset_prod_fr fun j _ => (huJet_tend j).pow (α j)
      rw [hP₀_coeff α]
      by_cases hwt : jetWeight α = W
      · simp only [hα, hwt, and_self, ↓reduceIte, Nat.sub_self, Nat.cast_zero, zero_mul, neg_zero,
          zpow_zero, mul_one]
        exact hc_tend.mul hp_tend
      · have hpos : 0 < W - jetWeight α := by
          have hle : jetWeight α ≤ W := Finset.le_sup (f := jetWeight) hα
          omega
        have hpow0 := tendsto_two_zpow_neg_mul_zero (W - jetWeight α) hpos
        simp only [hα, hwt, and_false, ↓reduceIte, zero_mul]
        simpa using (hc_tend.mul hpow0).mul hp_tend
    have ht0 : Filter.Tendsto (fun N : ℕ =>
        ∑ α ∈ P.support,
          ((P.coeff α).eval ((2 : ℂ) ^ (-(N : ℤ)) * s + 2 * (Real.pi : ℂ) * I * ((n : ℤ) : ℂ)) *
            (2 : ℂ) ^ (-(((W - jetWeight α : ℕ) : ℤ) * (N : ℤ)))) *
            ∏ j : Fin (r + 1), (uJet N j) ^ (α j)) atTop (𝓝 0) := by
      simp_rw [hzero_seq]; exact tendsto_const_nhds
    exact tendsto_nhds_unique htend ht0
  exact masterLacunary_no_const_homog_ade P₀.totalDegree P₀ W le_rfl hP₀_ne hP₀_hom hP₀_van

/-! ### 5C. Differential Field `FracHolRHP`, `trdeg` Closure Transfer, `frPoisson_no_ade` & `frEGF_no_ade` -/

/-- Open right half-plane `RHP = {z ∈ ℂ | 0 < z.re}`. -/
private def RHP : Set ℂ := {z : ℂ | 0 < z.re}

private lemma isOpen_RHP : IsOpen RHP := isOpen_lt continuous_const Complex.continuous_re

private lemma isPreconnected_RHP : IsPreconnected RHP := (convex_halfSpace_re_gt 0).isPreconnected

private def restrictRHP (g : ℂ → ℂ) (z : RHP) : ℂ := g z.1

private def extendRHP (f : RHP → ℂ) (z : ℂ) : ℂ := by
  classical exact if h : z ∈ RHP then f ⟨z, h⟩ else 0

private lemma extendRHP_restrictRHP_eqOn (g : ℂ → ℂ) : Set.EqOn (extendRHP (restrictRHP g)) g RHP := by
  intro z hz; simp [extendRHP, restrictRHP, hz]

private lemma analyticOnNhd_congr_RHP {f g : ℂ → ℂ} (hfg : Set.EqOn f g RHP) (hf : AnalyticOnNhd ℂ f RHP) :
    AnalyticOnNhd ℂ g RHP := fun z hz =>
  (hf z hz).congr (Filter.eventuallyEq_iff_exists_mem.mpr ⟨RHP, isOpen_RHP.mem_nhds hz, hfg⟩)

/-- The `ℂ`-subalgebra `HolRHP` of holomorphic functions on `RHP = {0 < z.re}`. -/
private def HolRHP : Subalgebra ℂ (RHP → ℂ) where
  carrier := {f | AnalyticOnNhd ℂ (extendRHP f) RHP}
  mul_mem' {f g} hf hg := analyticOnNhd_congr_RHP (f := fun z => extendRHP f z * extendRHP g z)
    (fun z hz => by simp [extendRHP, hz]) (hf.mul hg)
  one_mem' := analyticOnNhd_congr_RHP (f := fun _ => (1 : ℂ))
    (fun z hz => by simp [extendRHP, hz]) analyticOnNhd_const
  add_mem' {f g} hf hg := analyticOnNhd_congr_RHP (f := fun z => extendRHP f z + extendRHP g z)
    (fun z hz => by simp [extendRHP, hz]) (hf.add hg)
  zero_mem' := analyticOnNhd_congr_RHP (f := fun _ => (0 : ℂ))
    (fun z hz => by simp [extendRHP, hz]) analyticOnNhd_const
  algebraMap_mem' c := analyticOnNhd_congr_RHP (f := fun _ => c)
    (fun z hz => by simp [extendRHP, hz]) analyticOnNhd_const

private def holMK {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g RHP) : HolRHP :=
  ⟨restrictRHP g, analyticOnNhd_congr_RHP (extendRHP_restrictRHP_eqOn g).symm hg⟩

private lemma holMK_apply {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g RHP) (z : RHP) :
    (holMK hg : RHP → ℂ) z = g z.1 := rfl

private instance instIsDomainHolRHP : IsDomain HolRHP := by
  have : Nontrivial HolRHP := by
    refine ⟨⟨0, 1, fun h01 => ?_⟩⟩
    have hval := congrArg (fun g : HolRHP => g.1 ⟨1, by simp [RHP]⟩) h01
    simp at hval
  have : NoZeroDivisors HolRHP := by
    constructor
    intro f g hfg
    by_cases hf : f = 0
    · exact Or.inl hf
    · right
      have hex : ∃ z₀ : RHP, f.1 z₀ ≠ 0 := by
        by_contra hall; push Not at hall
        exact hf (Subtype.ext (funext hall))
      obtain ⟨z₀, hz₀⟩ := hex
      have hcont : ContinuousAt (extendRHP f.1) z₀.1 := (f.2 z₀.1 z₀.2).continuousAt
      have hne_ev : ∀ᶠ w in 𝓝 z₀.1, extendRHP f.1 w ≠ 0 :=
        hcont.eventually_ne (by simpa [extendRHP, z₀.2] using hz₀)
      have hmem_ev : ∀ᶠ w in 𝓝 z₀.1, w ∈ RHP := isOpen_RHP.mem_nhds z₀.2
      have hg_ev : extendRHP g.1 =ᶠ[𝓝 z₀.1] 0 := by
        filter_upwards [hne_ev, hmem_ev] with w hwne hwU
        have hmul0 : f.1 ⟨w, hwU⟩ * g.1 ⟨w, hwU⟩ = 0 := congrArg (fun h : HolRHP => h.1 ⟨w, hwU⟩) hfg
        have hfne : f.1 ⟨w, hwU⟩ ≠ 0 := by simpa [extendRHP, hwU] using hwne
        have hg0 : g.1 ⟨w, hwU⟩ = 0 := (mul_eq_zero.mp hmul0).resolve_left hfne
        simpa [extendRHP, hwU] using hg0
      have hzero := g.2.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_RHP z₀.2 hg_ev
      ext z; simpa [extendRHP, z.2] using hzero z.2
  exact NoZeroDivisors.to_isDomain HolRHP

/-- Ordinary complex derivative `d/dz` on `HolRHP`. -/
private def dHol (f : HolRHP) : HolRHP := holMK f.2.deriv

private lemma dHol_mk {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g RHP) :
    dHol (holMK hg) = holMK hg.deriv := by
  ext z
  simp only [dHol, holMK_apply]
  have heq : extendRHP (holMK hg).1 =ᶠ[𝓝 z.1] g :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨RHP, isOpen_RHP.mem_nhds z.2, extendRHP_restrictRHP_eqOn g⟩
  exact heq.deriv_eq

private lemma analyticOnNhd_iteratedDeriv_RHP {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g RHP) (j : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv j g) RHP := by
  induction j with
  | zero => simpa using hg
  | succ j ih => simpa [iteratedDeriv_succ] using ih.deriv

private lemma dHol_iter_mk {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g RHP) (j : ℕ) :
    dHol^[j] (holMK hg) = holMK (analyticOnNhd_iteratedDeriv_RHP hg j) := by
  induction j with
  | zero => ext z; simp [holMK_apply]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, dHol_mk]
    ext z; simp [holMK_apply, iteratedDeriv_succ]

private lemma dHol_add (f g : HolRHP) : dHol (f + g) = dHol f + dHol g := by
  ext z
  have heq : extendRHP (f + g).1 =ᶠ[𝓝 z.1] fun w => extendRHP f.1 w + extendRHP g.1 w :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨RHP, isOpen_RHP.mem_nhds z.2, fun w hw => by simp [extendRHP, hw]⟩
  change deriv (extendRHP (f + g).1) z.1 = deriv (extendRHP f.1) z.1 + deriv (extendRHP g.1) z.1
  rw [heq.deriv_eq, deriv_fun_add (f.2 z.1 z.2).differentiableAt (g.2 z.1 z.2).differentiableAt]

private lemma dHol_mul (f g : HolRHP) : dHol (f * g) = dHol f * g + f * dHol g := by
  ext z
  have heq : extendRHP (f * g).1 =ᶠ[𝓝 z.1] fun w => extendRHP f.1 w * extendRHP g.1 w :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨RHP, isOpen_RHP.mem_nhds z.2, fun w hw => by simp [extendRHP, hw]⟩
  change deriv (extendRHP (f * g).1) z.1 = deriv (extendRHP f.1) z.1 * g.1 z + f.1 z * deriv (extendRHP g.1) z.1
  rw [heq.deriv_eq, deriv_fun_mul (f.2 z.1 z.2).differentiableAt (g.2 z.1 z.2).differentiableAt]
  simp only [extendRHP, z.2, dite_true]

private lemma dHol_sub (f g : HolRHP) : dHol (f - g) = dHol f - dHol g := by
  have h := dHol_add (f - g) g; rw [sub_add_cancel] at h; exact eq_sub_of_add_eq h.symm

private lemma dHol_neg (f : HolRHP) : dHol (-f) = -dHol f := by
  have h0 : dHol 0 = 0 := by have h := dHol_add 0 0; rw [add_zero] at h; linear_combination -h
  have h := dHol_sub 0 f; rw [zero_sub, h0, zero_sub] at h; exact h

private lemma dHol_C (c : ℂ) : dHol (algebraMap ℂ HolRHP c) = 0 := by
  ext z
  have heq : extendRHP (algebraMap ℂ HolRHP c).1 =ᶠ[𝓝 z.1] fun _ => c :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨RHP, isOpen_RHP.mem_nhds z.2, fun w hw => by simp [extendRHP, hw]⟩
  change deriv (extendRHP (algebraMap ℂ HolRHP c).1) z.1 = 0
  rw [heq.deriv_eq, deriv_const]

private def zVarHol : HolRHP := holMK analyticOnNhd_id

private lemma dHol_zVar : dHol zVarHol = 1 := by
  ext z
  rw [zVarHol, dHol_mk]
  change deriv id z.1 = 1
  simp

/-- Embedding `ℂ[X] →+* HolRHP` sending `p` to `z ↦ p.eval z`. -/
private def polyToHol : Polynomial ℂ →+* HolRHP :=
  Polynomial.eval₂RingHom (algebraMap ℂ HolRHP) zVarHol

private lemma polyToHol_apply (p : Polynomial ℂ) (z : RHP) :
    (polyToHol p : RHP → ℂ) z = p.eval z.1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n a => simp [polyToHol, Polynomial.eval₂_monomial, zVarHol, holMK_apply]

private lemma polyToHol_injective : Function.Injective polyToHol := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hpne
  have hroots : ∀ n : ℕ, p.IsRoot (((n + 1 : ℕ) : ℂ)) := fun n => by
    have hz : (((n + 1 : ℕ) : ℂ)) ∈ RHP := by
      show 0 < (((n + 1 : ℕ) : ℂ)).re; rw [Complex.natCast_re]; positivity
    have h0 := congrArg (fun f : HolRHP => f.1 ⟨_, hz⟩) hp
    simpa [polyToHol_apply, Polynomial.IsRoot] using h0
  let S : Finset ℂ := (Finset.range (p.natDegree + 1)).image fun n : ℕ => (((n + 1 : ℕ) : ℂ))
  have hinj : Function.Injective (fun n : ℕ => (((n + 1 : ℕ) : ℂ))) := fun a b hab => by
    dsimp only at hab
    have : a + 1 = b + 1 := by exact_mod_cast hab
    omega
  have hcard : S.card = p.natDegree + 1 := by rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
  have hsub : S.val ⊆ p.roots := fun z hz => by
    rw [Finset.mem_val, Finset.mem_image] at hz
    obtain ⟨n, _, rfl⟩ := hz
    exact (Polynomial.mem_roots hpne).mpr (hroots n)
  have hle : S.card ≤ p.roots.card := Multiset.card_le_card ((Multiset.le_iff_subset S.nodup).mpr hsub)
  have hdeg := Polynomial.card_roots' p
  omega

private lemma dHol_pow (f : HolRHP) (n : ℕ) : dHol (f ^ n) = (n : ℂ) • (f ^ (n - 1) * dHol f) := by
  induction n with
  | zero => rw [pow_zero, show (1 : HolRHP) = algebraMap ℂ HolRHP 1 from rfl, dHol_C]; simp
  | succ n ih =>
    rw [pow_succ, dHol_mul, ih]
    cases n with
    | zero => simp [Algebra.smul_def]
    | succ m =>
      simp only [Nat.add_sub_cancel, Algebra.smul_def, Nat.cast_add, Nat.cast_one, map_add, map_one]
      have hpow : f ^ m * f = f ^ (m + 1) := (pow_succ f m).symm
      linear_combination (algebraMap ℂ HolRHP (m + 1 : ℂ) * dHol f) * hpow

private lemma dHol_polyToHol (p : Polynomial ℂ) : dHol (polyToHol p) = polyToHol p.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, dHol_add, hp, hq, Polynomial.derivative_add, map_add]
  | monomial n a =>
    rw [Polynomial.derivative_monomial]
    simp only [polyToHol, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
    rw [dHol_mul, dHol_C, zero_mul, zero_add, dHol_pow, dHol_zVar, mul_one, Algebra.smul_def]
    rw [← mul_assoc, ← map_mul]

/-- Meromorphic differential field `FracHolRHP = FractionRing HolRHP`. -/
private abbrev FracHolRHP : Type := FractionRing HolRHP

private def algFrac : HolRHP →+* FracHolRHP := algebraMap HolRHP FracHolRHP

private lemma algFrac_injective : Function.Injective algFrac :=
  IsFractionRing.injective HolRHP FracHolRHP

private lemma algFrac_ne_zero_of_mem {s : HolRHP} (hs : s ∈ nonZeroDivisors HolRHP) : algFrac s ≠ 0 :=
  map_ne_zero_of_mem_nonZeroDivisors algFrac algFrac_injective hs

private lemma mk_eq_div (r : HolRHP) (s : nonZeroDivisors HolRHP) :
    Localization.mk r s = algFrac r / algFrac s.1 := by
  have hs : algFrac s.1 ≠ 0 := algFrac_ne_zero_of_mem s.2
  rw [eq_div_iff hs]
  have hr : algFrac r = Localization.mk r 1 := (Localization.mk_one_eq_algebraMap r).symm
  have hs' : algFrac s.1 = Localization.mk s.1 1 := (Localization.mk_one_eq_algebraMap s.1).symm
  rw [hr, hs', Localization.mk_mul]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp [mul_comm]))

/-- Quotient-rule derivation `dFrac` on `FracHolRHP`. -/
private def dFrac (x : FracHolRHP) : FracHolRHP :=
  Localization.liftOn x
    (fun (r : HolRHP) (s : nonZeroDivisors HolRHP) =>
      (algFrac (dHol r) * algFrac s.1 - algFrac r * algFrac (dHol s.1)) / (algFrac s.1 * algFrac s.1))
    (fun {r₁ r₂ s₁ s₂} hrel => by
      have hs1 : algFrac s₁.1 ≠ 0 := algFrac_ne_zero_of_mem s₁.2
      have hs2 : algFrac s₂.1 ≠ 0 := algFrac_ne_zero_of_mem s₂.2
      have hmk : Localization.mk r₁ s₁ = Localization.mk r₂ s₂ := Localization.mk_eq_mk_iff.mpr hrel
      rw [mk_eq_div, mk_eq_div, div_eq_div_iff hs1 hs2] at hmk
      have hce : r₁ * s₂.1 = r₂ * s₁.1 := algFrac_injective (by simpa only [algFrac.map_mul] using hmk)
      have hd := congrArg dHol hce
      rw [dHol_mul, dHol_mul] at hd
      have hda := congrArg algFrac hd
      have hce_a := congrArg algFrac hce
      simp only [algFrac.map_add, algFrac.map_mul] at hda hce_a
      rw [div_eq_div_iff (mul_ne_zero hs1 hs1) (mul_ne_zero hs2 hs2)]
      linear_combination
        (algFrac s₁.1 * algFrac s₂.1) * hda -
        (algFrac (dHol s₁.1) * algFrac s₂.1 + algFrac s₁.1 * algFrac (dHol s₂.1)) * hce_a)

private lemma dFrac_mk (r : HolRHP) (s : nonZeroDivisors HolRHP) :
    dFrac (Localization.mk r s) =
      (algFrac (dHol r) * algFrac s.1 - algFrac r * algFrac (dHol s.1)) / (algFrac s.1 * algFrac s.1) := rfl

private lemma dFrac_algFrac (f : HolRHP) : dFrac (algFrac f) = algFrac (dHol f) := by
  have h1 : algFrac f = Localization.mk f 1 := (Localization.mk_one_eq_algebraMap f).symm
  rw [h1, dFrac_mk]
  have hd1 : dHol 1 = 0 := dHol_C 1
  simp [hd1]

private lemma dFrac_iter_algFrac (f : HolRHP) (j : ℕ) : dFrac^[j] (algFrac f) = algFrac (dHol^[j] f) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, dFrac_algFrac]

private lemma dFrac_add (x y : FracHolRHP) : dFrac (x + y) = dFrac x + dFrac y := by
  induction x using Localization.induction_on with
  | H a =>
    induction y using Localization.induction_on with
    | H b =>
      rcases a with ⟨r₁, s₁⟩; rcases b with ⟨r₂, s₂⟩
      rw [Localization.add_mk, dFrac_mk, dFrac_mk, dFrac_mk]
      have hs1 : algFrac s₁.1 ≠ 0 := algFrac_ne_zero_of_mem s₁.2
      have hs2 : algFrac s₂.1 ≠ 0 := algFrac_ne_zero_of_mem s₂.2
      simp only [Submonoid.coe_mul, dHol_add, dHol_mul, algFrac.map_add, algFrac.map_mul]
      field_simp [hs1, hs2]
      ring

private lemma dFrac_mul (x y : FracHolRHP) : dFrac (x * y) = dFrac x * y + x * dFrac y := by
  induction x using Localization.induction_on with
  | H a =>
    induction y using Localization.induction_on with
    | H b =>
      rcases a with ⟨r₁, s₁⟩; rcases b with ⟨r₂, s₂⟩
      rw [Localization.mk_mul, dFrac_mk, dFrac_mk, dFrac_mk, mk_eq_div, mk_eq_div]
      have hs1 : algFrac s₁.1 ≠ 0 := algFrac_ne_zero_of_mem s₁.2
      have hs2 : algFrac s₂.1 ≠ 0 := algFrac_ne_zero_of_mem s₂.2
      simp only [Submonoid.coe_mul, dHol_mul, algFrac.map_add, algFrac.map_mul]
      field_simp [hs1, hs2]
      ring

private lemma dFrac_zero : dFrac 0 = 0 := by
  have h := dFrac_add 0 0; rw [add_zero] at h; linear_combination -h

private lemma dFrac_one : dFrac 1 = 0 := by
  simpa using dFrac_algFrac 1 |>.trans (by rw [show (1 : HolRHP) = algebraMap ℂ HolRHP 1 from rfl, dHol_C, map_zero])

private lemma dFrac_sub (x y : FracHolRHP) : dFrac (x - y) = dFrac x - dFrac y := by
  have h := dFrac_add (x - y) y; rw [sub_add_cancel] at h; exact eq_sub_of_add_eq h.symm

private lemma dFrac_neg (x : FracHolRHP) : dFrac (-x) = -dFrac x := by
  have h := dFrac_sub 0 x; rw [zero_sub, dFrac_zero, zero_sub] at h; exact h

private lemma dFrac_inv (x : FracHolRHP) : dFrac x⁻¹ = -(dFrac x) / (x * x) := by
  by_cases hx : x = 0
  · subst hx; simp [dFrac_zero]
  · have h := dFrac_mul x x⁻¹
    rw [mul_inv_cancel₀ hx, dFrac_one] at h
    have h1 : x * dFrac x⁻¹ = -(dFrac x * x⁻¹) := by linear_combination -h
    have h2 := congrArg (fun t => t / x) h1
    rw [mul_div_cancel_left₀ _ hx] at h2
    rw [h2]; field_simp [hx]

private lemma dFrac_div (x y : FracHolRHP) (hy : y ≠ 0) :
    dFrac (x / y) = (dFrac x * y - x * dFrac y) / (y * y) := by
  rw [div_eq_mul_inv, dFrac_mul, dFrac_inv]
  field_simp [hy]
  ring

/-- Embedding `RatFunc ℂ →+* FracHolRHP` and its `Algebra` structure. -/
private def ratToFrac : RatFunc ℂ →+* FracHolRHP :=
  RatFunc.liftRingHom (algFrac.comp polyToHol) fun p hp => by
    change algFrac (polyToHol p) ∈ nonZeroDivisors FracHolRHP
    rw [mem_nonZeroDivisors_iff_ne_zero] at hp ⊢
    intro h0
    have h0' : algFrac (polyToHol p) = algFrac (polyToHol 0) := by
      rw [polyToHol.map_zero, algFrac.map_zero]; exact h0
    exact hp (polyToHol_injective (algFrac_injective h0'))

private lemma ratToFrac_algebraMap (p : Polynomial ℂ) :
    ratToFrac (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) = algFrac (polyToHol p) := by
  unfold ratToFrac
  simp [RatFunc.liftRingHom_apply]

private lemma ratToFrac_injective : Function.Injective ratToFrac := RingHom.injective ratToFrac

/-- Quotient-rule derivation on `RatFunc ℂ`. -/
private def dRat (q : RatFunc ℂ) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) (q.num.derivative * q.denom - q.num * q.denom.derivative) /
    (algebraMap (Polynomial ℂ) (RatFunc ℂ) q.denom * algebraMap (Polynomial ℂ) (RatFunc ℂ) q.denom)

private lemma dFrac_ratToFrac (q : RatFunc ℂ) : dFrac (ratToFrac q) = ratToFrac (dRat q) := by
  have hq : q = algebraMap (Polynomial ℂ) (RatFunc ℂ) q.num / algebraMap (Polynomial ℂ) (RatFunc ℂ) q.denom :=
    (RatFunc.num_div_denom q).symm
  have hden_f : algFrac (polyToHol q.denom) ≠ 0 := by
    intro h0
    have h0' : algFrac (polyToHol q.denom) = algFrac (polyToHol 0) := by
      simpa [polyToHol.map_zero, algFrac.map_zero] using h0
    exact RatFunc.denom_ne_zero q (polyToHol_injective (algFrac_injective h0'))
  conv_lhs => rw [hq, map_div₀, ratToFrac_algebraMap, ratToFrac_algebraMap]
  rw [dFrac_div _ _ hden_f, dFrac_algFrac, dFrac_algFrac, dHol_polyToHol, dHol_polyToHol]
  unfold dRat
  rw [map_div₀, ratToFrac.map_mul, ratToFrac_algebraMap, ratToFrac_algebraMap]
  simp only [polyToHol.map_sub, polyToHol.map_mul, algFrac.map_sub, algFrac.map_mul]

private lemma dRat_add (q₁ q₂ : RatFunc ℂ) : dRat (q₁ + q₂) = dRat q₁ + dRat q₂ :=
  ratToFrac_injective (by
    rw [ratToFrac.map_add, ← dFrac_ratToFrac, ← dFrac_ratToFrac, ← dFrac_ratToFrac, ratToFrac.map_add, dFrac_add])

private lemma dRat_mul (q₁ q₂ : RatFunc ℂ) : dRat (q₁ * q₂) = dRat q₁ * q₂ + q₁ * dRat q₂ :=
  ratToFrac_injective (by
    rw [ratToFrac.map_add, ratToFrac.map_mul, ratToFrac.map_mul, ← dFrac_ratToFrac, ← dFrac_ratToFrac,
      ← dFrac_ratToFrac, ratToFrac.map_mul, dFrac_mul])

private lemma dRat_zero : dRat 0 = 0 :=
  ratToFrac_injective (by rw [← dFrac_ratToFrac, ratToFrac.map_zero, dFrac_zero])

private local instance instAlgebraRatFrac : Algebra (RatFunc ℂ) FracHolRHP := ratToFrac.toAlgebra

private lemma algebraMap_ratFrac_apply (q : RatFunc ℂ) :
    algebraMap (RatFunc ℂ) FracHolRHP q = ratToFrac q := rfl

/-- Coefficientwise derivation `P^D` on `MvPolynomial (Fin (r + 1)) (RatFunc ℂ)`. -/
private def coeffDerivRat {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) :
    MvPolynomial (Fin (r + 1)) (RatFunc ℂ) := by
  classical exact ∑ α ∈ P.support, MvPolynomial.monomial α (dRat (P.coeff α))

private lemma coeffDerivRat_coeff {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (α : Fin (r + 1) →₀ ℕ) : (coeffDerivRat P).coeff α = dRat (P.coeff α) := by
  classical
  unfold coeffDerivRat
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · simp
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · rw [MvPolynomial.notMem_support_iff.mp hα, dRat_zero]
    exact Finset.sum_eq_zero fun β hβ => by
      have hne : β ≠ α := fun h => hα (h ▸ hβ)
      simp [hne]

private lemma coeffDerivRat_C {r : ℕ} (q : RatFunc ℂ) :
    coeffDerivRat (r := r) (MvPolynomial.C q) = MvPolynomial.C (dRat q) := by
  ext α
  rw [coeffDerivRat_coeff, MvPolynomial.coeff_C, MvPolynomial.coeff_C]
  split_ifs
  · rfl
  · exact dRat_zero

private lemma coeffDerivRat_add {r : ℕ} (P Q : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) :
    coeffDerivRat (P + Q) = coeffDerivRat P + coeffDerivRat Q := by
  ext α; simp [coeffDerivRat_coeff, dRat_add]

private lemma coeffDerivRat_mul_X {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) (i : Fin (r + 1)) :
    coeffDerivRat (P * MvPolynomial.X i) = coeffDerivRat P * MvPolynomial.X i := by
  classical
  ext α
  rw [coeffDerivRat_coeff, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
  split_ifs
  · exact (coeffDerivRat_coeff P _).symm
  · exact dRat_zero

/-- Differential chain rule in `FracHolRHP` for `MvPolynomial.aeval` along `(f, f', ..., f^{(r)})`. -/
private lemma dFrac_mvPoly_aeval {r : ℕ} (f : FracHolRHP) (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) :
    dFrac (MvPolynomial.aeval (fun j : Fin (r + 1) => dFrac^[j.val] f) P) =
      MvPolynomial.aeval (fun j : Fin (r + 1) => dFrac^[j.val] f) (coeffDerivRat P) +
      ∑ j : Fin (r + 1), MvPolynomial.aeval (fun k : Fin (r + 1) => dFrac^[k.val] f) (MvPolynomial.pderiv j P) *
        dFrac^[j.val + 1] f := by
  induction P using MvPolynomial.induction_on with
  | C q =>
    rw [MvPolynomial.aeval_C, coeffDerivRat_C, MvPolynomial.aeval_C, algebraMap_ratFrac_apply,
      algebraMap_ratFrac_apply, dFrac_ratToFrac]
    simp
  | add P Q ihP ihQ =>
    rw [map_add, dFrac_add, ihP, ihQ, coeffDerivRat_add, map_add]
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    ring
  | mul_X P i ihP =>
    rw [map_mul, MvPolynomial.aeval_X, dFrac_mul, ihP, coeffDerivRat_mul_X, map_mul, MvPolynomial.aeval_X]
    have hstep : dFrac (dFrac^[i.val] f) = dFrac^[i.val + 1] f := (Function.iterate_succ_apply' dFrac i.val f).symm
    rw [hstep]
    have hsum_X : ∑ j : Fin (r + 1),
          MvPolynomial.aeval (fun k : Fin (r + 1) => dFrac^[k.val] f) (MvPolynomial.pderiv j (P * MvPolynomial.X i)) *
            dFrac^[j.val + 1] f =
        (∑ j : Fin (r + 1), MvPolynomial.aeval (fun k : Fin (r + 1) => dFrac^[k.val] f) (MvPolynomial.pderiv j P) *
            dFrac^[j.val + 1] f) * dFrac^[i.val] f +
        MvPolynomial.aeval (fun k : Fin (r + 1) => dFrac^[k.val] f) P * dFrac^[i.val + 1] f := by
      have hterm : ∀ j : Fin (r + 1),
          MvPolynomial.aeval (fun k : Fin (r + 1) => dFrac^[k.val] f) (MvPolynomial.pderiv j (P * MvPolynomial.X i)) *
              dFrac^[j.val + 1] f =
            (MvPolynomial.aeval (fun k : Fin (r + 1) => dFrac^[k.val] f) (MvPolynomial.pderiv j P) *
              dFrac^[j.val + 1] f) * dFrac^[i.val] f +
            (if j = i then MvPolynomial.aeval (fun k : Fin (r + 1) => dFrac^[k.val] f) P * dFrac^[i.val + 1] f else 0) :=
        fun j => by
          rw [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, smul_eq_mul, smul_eq_mul,
            map_add, map_mul, map_mul, MvPolynomial.aeval_X]
          by_cases hji : j = i
          · subst hji; simp; ring
          · simp [hji, Ne.symm hji]; ring
      simp_rw [hterm, Finset.sum_add_distrib, ← Finset.sum_mul]
      simp
    rw [hsum_X]
    ring

/-- Predicate: an intermediate field `E / RatFunc ℂ` inside `FracHolRHP` is closed under `dFrac`. -/
private def IsDiffClosedRHP (E : IntermediateField (RatFunc ℂ) FracHolRHP) : Prop :=
  ∀ x : FracHolRHP, x ∈ E → dFrac x ∈ E

/-- `IntermediateField.adjoin (RatFunc ℂ) S` is `dFrac`-closed iff `dFrac s ∈ adjoin S` for all `s ∈ S`. -/
private lemma isDiffClosedRHP_adjoin_of_gens {S : Set FracHolRHP}
    (hS : ∀ s ∈ S, dFrac s ∈ IntermediateField.adjoin (RatFunc ℂ) S) :
    IsDiffClosedRHP (IntermediateField.adjoin (RatFunc ℂ) S) := by
  let E := IntermediateField.adjoin (RatFunc ℂ) S
  let D : IntermediateField (RatFunc ℂ) FracHolRHP :=
    { carrier := {x : FracHolRHP | x ∈ E ∧ dFrac x ∈ E}
      mul_mem' := fun {a b} ha hb => ⟨E.mul_mem ha.1 hb.1, by rw [dFrac_mul]; exact E.add_mem (E.mul_mem ha.2 hb.1) (E.mul_mem ha.1 hb.2)⟩
      one_mem' := ⟨E.one_mem, by rw [dFrac_one]; exact E.zero_mem⟩
      add_mem' := fun {a b} ha hb => ⟨E.add_mem ha.1 hb.1, by rw [dFrac_add]; exact E.add_mem ha.2 hb.2⟩
      zero_mem' := ⟨E.zero_mem, by rw [dFrac_zero]; exact E.zero_mem⟩
      inv_mem' := fun {a} ha => ⟨E.inv_mem ha.1, by rw [dFrac_inv]; exact E.div_mem (E.neg_mem ha.2) (E.mul_mem ha.1 ha.1)⟩
      algebraMap_mem' := fun q => ⟨E.algebraMap_mem q, by
        rw [algebraMap_ratFrac_apply, dFrac_ratToFrac]
        exact E.algebraMap_mem (dRat q)⟩ }
  have hle : E ≤ D := IntermediateField.adjoin_le_iff.mpr fun s hs =>
    ⟨IntermediateField.subset_adjoin _ _ hs, hS s hs⟩
  exact fun x hx => (hle hx).2

/-- **Finite-Generator Transcendence Degree Bound**:
For any finite `S : Finset FracHolRHP`, `trdeg (RatFunc ℂ) (adjoin S) ≤ S.card`. -/
private lemma trdeg_adjoin_finset_le (S : Finset FracHolRHP) :
    Algebra.trdeg (RatFunc ℂ) (IntermediateField.adjoin (RatFunc ℂ) (S : Set FracHolRHP)) ≤ (S.card : Cardinal) := by
  let E := IntermediateField.adjoin (RatFunc ℂ) (S : Set FracHolRHP)
  let sE : Set E := {y : E | y.1 ∈ S}
  have hsE_card : Cardinal.mk sE ≤ (S.card : Cardinal) := by
    have hinj : Function.Injective (fun y : sE => (⟨y.1.1, y.2⟩ : S)) := fun a b hab => by
      dsimp only at hab
      apply Subtype.ext; apply Subtype.ext; exact congrArg (fun x : S => x.1) hab
    calc Cardinal.mk sE ≤ Cardinal.mk S := Cardinal.mk_le_of_injective hinj
      _ = (S.card : Cardinal) := Cardinal.mk_coe_finset
  -- Every element `y : E` is a fraction `a / b` with `a, b ∈ Algebra.adjoin (RatFunc ℂ) sE`, `b ≠ 0`, hence algebraic!
  let R := Algebra.adjoin (RatFunc ℂ) sE
  let r0 : R := ⟨0, R.zero_mem⟩
  let r1 : R := ⟨1, R.one_mem⟩
  have hr1_ne : r1.1.1 ≠ 0 := one_ne_zero
  have hQ_eq : ∀ x : FracHolRHP, x ∈ E → ∃ a b : R, b.1.1 ≠ 0 ∧ x * b.1.1 = a.1.1 := by
    let Q : IntermediateField (RatFunc ℂ) FracHolRHP :=
      { carrier := {x : FracHolRHP | ∃ a b : R, b.1.1 ≠ 0 ∧ x * b.1.1 = a.1.1}
        zero_mem' := ⟨r0, r1, hr1_ne, by simp [r0, r1]⟩
        one_mem' := ⟨r1, r1, hr1_ne, by simp [r1]⟩
        add_mem' := fun {x y} ⟨ax, bx, hbx, hx⟩ ⟨ay, by_, hby, hy⟩ =>
          ⟨ax * by_ + ay * bx, bx * by_, mul_ne_zero hbx hby, by
            change (x + y) * (bx.1.1 * by_.1.1) = ax.1.1 * by_.1.1 + ay.1.1 * bx.1.1
            linear_combination by_.1.1 * hx + bx.1.1 * hy⟩
        mul_mem' := fun {x y} ⟨ax, bx, hbx, hx⟩ ⟨ay, by_, hby, hy⟩ =>
          ⟨ax * ay, bx * by_, mul_ne_zero hbx hby, by
            change (x * y) * (bx.1.1 * by_.1.1) = ax.1.1 * ay.1.1
            linear_combination (y * by_.1.1) * hx + ax.1.1 * hy⟩
        inv_mem' := fun {x} ⟨a, b, hb, hx⟩ => by
          by_cases hx0 : x = 0
          · subst hx0; exact ⟨r0, r1, hr1_ne, by simp [r0, r1]⟩
          · have ha0 : a.1.1 ≠ 0 := fun ha => mul_ne_zero hx0 hb (hx.trans ha)
            exact ⟨b, a, ha0, by rw [← hx]; field_simp [hx0]⟩
        algebraMap_mem' := fun q => ⟨algebraMap (RatFunc ℂ) R q, r1, hr1_ne, by simp [r1]⟩ }
    have hle : E ≤ Q := IntermediateField.adjoin_le_iff.mpr fun s hs =>
      ⟨⟨⟨s, IntermediateField.subset_adjoin _ _ hs⟩, Algebra.subset_adjoin hs⟩, r1, hr1_ne, by simp [r1]⟩
    exact fun x hx => hle hx
  have hAlg : Algebra.IsAlgebraic R E := by
    constructor
    intro y
    obtain ⟨a, b, hb, hy⟩ := hQ_eq y.1 y.2
    refine ⟨Polynomial.C b * Polynomial.X - Polynomial.C a, ?_, ?_⟩
    · intro h0
      have hc1 := congrArg (fun p : Polynomial R => p.coeff 1) h0
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X, mul_one,
        Polynomial.coeff_C, one_ne_zero, ↓reduceIte, sub_zero, Polynomial.coeff_zero] at hc1
      exact hb (congrArg (fun z : R => z.1.1) hc1)
    · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      apply Subtype.ext
      change b.1.1 * y.1 - a.1.1 = 0
      linear_combination hy
  exact (Algebra.IsAlgebraic.trdeg_le_cardinalMk (RatFunc ℂ) sE).trans hsE_card

/-- Helper: `totalDegree (pderiv i P) < totalDegree P` over any field of characteristic 0. -/
private lemma totalDegree_pderiv_lt_field {K : Type*} [Field K] [CharZero K] {ι : Type*}
    (i : ι) (P : MvPolynomial ι K) (hpos : 0 < P.totalDegree) :
    (MvPolynomial.pderiv i P).totalDegree < P.totalDegree := by
  classical
  conv_lhs => unfold MvPolynomial.totalDegree
  refine lt_of_le_of_lt (Finset.sup_le fun m hm => ?_) (Nat.sub_lt hpos Nat.zero_lt_one)
  have hn := MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hn
  have hmem : m + Finsupp.single i 1 ∈ P.support := MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hn)
  have hle : (m + Finsupp.single i 1).sum (fun _ e => e) ≤ P.totalDegree :=
    Finset.le_sup (f := fun s : ι →₀ ℕ => s.sum fun _ e => e) hmem
  have hsum : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  omega

/-- Helper: if `pderiv j P = 0` in `MvPolynomial (Fin (r + 1)) K` (`CharZero K`), then `α j = 0` for all `α ∈ P.support`. -/
private lemma coeff_zero_of_pderiv_eq_zero_field {K : Type*} [Field K] [CharZero K] {r : ℕ}
    {P : MvPolynomial (Fin (r + 1)) K} {j : Fin (r + 1)}
    (hpd : MvPolynomial.pderiv j P = 0) {α : Fin (r + 1) →₀ ℕ} (hα : α ∈ P.support) :
    α j = 0 := by
  by_contra hpos
  have h1 : 1 ≤ α j := Nat.pos_of_ne_zero hpos
  let β : Fin (r + 1) →₀ ℕ := α - Finsupp.single j 1
  have hβ_add : β + Finsupp.single j 1 = α := by
    ext k
    simp only [β, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
    by_cases hkj : k = j
    · subst hkj; simp; omega
    · simp [Ne.symm hkj]
  have hc : (MvPolynomial.pderiv j P).coeff β = 0 := by simp [hpd]
  rw [MvPolynomial.coeff_pderiv, hβ_add] at hc
  have hne : ((β j : ℕ) + 1 : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (β j)
  exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hα) hne hc

/-- Helper: if every partial derivative of `P : MvPolynomial (Fin (r + 1)) K` is `0`, then `P = C (P.coeff 0)`. -/
private lemma all_partials_zero_field {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) K) (h : ∀ j : Fin (r + 1), MvPolynomial.pderiv j P = 0) :
    P = MvPolynomial.C (P.coeff 0) := by
  ext α
  by_cases hα : α = 0
  · subst hα; simp
  · rw [MvPolynomial.coeff_C]
    simp only [Ne.symm hα, ↓reduceIte]
    by_contra hnz
    have hmem : α ∈ P.support := MvPolynomial.mem_support_iff.mpr hnz
    exact hα (by ext j; simp [coeff_zero_of_pderiv_eq_zero_field (h j) hmem])

/-- **Forward `trdeg` Closure Lemma**:
If `f : FracHolRHP` satisfies a nonzero polynomial ADE over `RatFunc ℂ`, then `f` lies in a
`dFrac`-closed finitely generated intermediate field `IntermediateField.adjoin (RatFunc ℂ) S`. -/
private lemma exists_finset_dClosed_of_ade {f : FracHolRHP} {r₀ : ℕ}
    (P₀ : MvPolynomial (Fin (r₀ + 1)) (RatFunc ℂ)) (hP₀_ne : P₀ ≠ 0)
    (hP₀_val : MvPolynomial.aeval (fun j : Fin (r₀ + 1) => dFrac^[j.val] f) P₀ = 0) :
    ∃ S : Finset FracHolRHP,
      f ∈ IntermediateField.adjoin (RatFunc ℂ) (S : Set FracHolRHP) ∧
      IsDiffClosedRHP (IntermediateField.adjoin (RatFunc ℂ) (S : Set FracHolRHP)) := by
  classical
  -- Pick minimal total degree `D` over all `(r, P)` with `P ≠ 0` vanishing on `f`!
  let HasDeg : ℕ → Prop := fun D =>
    ∃ (r : ℕ) (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      P ≠ 0 ∧ MvPolynomial.aeval (fun j : Fin (r + 1) => dFrac^[j.val] f) P = 0 ∧ P.totalDegree = D
  have hexD : ∃ D, HasDeg D := ⟨P₀.totalDegree, r₀, P₀, hP₀_ne, hP₀_val, rfl⟩
  let D : ℕ := Nat.find hexD
  obtain ⟨r, P, hP_ne, hP_val, hP_deg⟩ := Nat.find_spec hexD
  have hD_min : ∀ {r' : ℕ} (Q : MvPolynomial (Fin (r' + 1)) (RatFunc ℂ)),
      Q ≠ 0 → Q.totalDegree < D → MvPolynomial.aeval (fun j : Fin (r' + 1) => dFrac^[j.val] f) Q ≠ 0 :=
    fun Q hQne hQlt hQ0 => Nat.find_min hexD hQlt ⟨_, Q, hQne, hQ0, rfl⟩
  -- Pick the LARGEST variable index `m : Fin (r + 1)` with `pderiv m P ≠ 0`!
  let I : Finset (Fin (r + 1)) := Finset.univ.filter fun j => MvPolynomial.pderiv j P ≠ 0
  have hI_ne : I.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hall : ∀ j : Fin (r + 1), MvPolynomial.pderiv j P = 0 := fun j => by
      by_contra hnz
      have : j ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hnz⟩
      rw [hempty] at this; exact Finset.notMem_empty j this
    have hconst := all_partials_zero_field P hall
    have hc_ne : P.coeff 0 ≠ 0 := fun hc0 => hP_ne (by rw [hconst, hc0, map_zero])
    rw [hconst, MvPolynomial.aeval_C, algebraMap_ratFrac_apply] at hP_val
    exact hc_ne (ratToFrac_injective (hP_val.trans (map_zero _).symm))
  let m : Fin (r + 1) := I.max' hI_ne
  have hm_mem : m ∈ I := Finset.max'_mem I hI_ne
  have hpd_m_ne : MvPolynomial.pderiv m P ≠ 0 := (Finset.mem_filter.mp hm_mem).2
  have hpd_gt_zero : ∀ j : Fin (r + 1), m < j → MvPolynomial.pderiv j P = 0 := fun j hgt => by
    by_contra hnz
    exact not_le_of_gt hgt (Finset.le_max' I j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hnz⟩))
  have hP_pos : 0 < P.totalDegree := by
    by_contra h0
    have hdeg0 : P.totalDegree = 0 := by omega
    have hconst : P = MvPolynomial.C (P.coeff 0) := by
      ext α
      by_cases hα : α = 0
      · subst hα; simp
      · rw [MvPolynomial.coeff_C]; simp only [Ne.symm hα, ↓reduceIte]
        by_contra hnz
        have hmem : α ∈ P.support := MvPolynomial.mem_support_iff.mpr hnz
        have hsum_le : α.sum (fun _ e => e) ≤ P.totalDegree :=
          Finset.le_sup (f := fun s : Fin (r + 1) →₀ ℕ => s.sum fun _ e => e) hmem
        rw [hdeg0] at hsum_le
        have hzero : α = 0 := by
          ext j
          have hj : α j ≤ α.sum (fun _ e => e) := by
            rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
            exact Finset.single_le_sum (f := fun k => α k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
          simp only [Finsupp.coe_zero, Pi.zero_apply]; omega
        exact hα hzero
    rw [hconst, MvPolynomial.pderiv_C] at hpd_m_ne
    exact hpd_m_ne rfl
  have hpd_m_eval_ne : MvPolynomial.aeval (fun j : Fin (r + 1) => dFrac^[j.val] f) (MvPolynomial.pderiv m P) ≠ 0 :=
    hD_min (MvPolynomial.pderiv m P) hpd_m_ne (by dsimp only [D]; rw [← hP_deg]; exact totalDegree_pderiv_lt_field m P hP_pos)
  -- Let `S = {f, f', ..., f^{(m)}}` and `E = adjoin S`!
  let S : Finset FracHolRHP := (Finset.range (m.val + 1)).image fun k => dFrac^[k] f
  let E := IntermediateField.adjoin (RatFunc ℂ) (S : Set FracHolRHP)
  have hf_mem_E : ∀ k : ℕ, k ≤ m.val → dFrac^[k] f ∈ E := fun k hk =>
    IntermediateField.subset_adjoin _ _ (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩))
  -- Any `Q : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)` using only variables `≤ m` evaluates into `E`!
  have heval_mem_E : ∀ Q : MvPolynomial (Fin (r + 1)) (RatFunc ℂ),
      (∀ α ∈ Q.support, ∀ k : Fin (r + 1), m < k → α k = 0) →
      MvPolynomial.aeval (fun j : Fin (r + 1) => dFrac^[j.val] f) Q ∈ E := by
    intro Q hQ
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    refine E.sum_mem fun α hα => E.mul_mem (E.algebraMap_mem _) ?_
    refine E.prod_mem fun k _ => ?_
    by_cases hkm : k ≤ m
    · exact pow_mem (hf_mem_E k.val hkm) (α k)
    · have h0 : α k = 0 := hQ α hα k (lt_of_not_ge hkm)
      rw [h0, pow_zero]; exact E.one_mem
  have hP_vars : ∀ α ∈ P.support, ∀ k : Fin (r + 1), m < k → α k = 0 := fun α hα k hk =>
    coeff_zero_of_pderiv_eq_zero_field (hpd_gt_zero k hk) hα
  have hcD_mem : MvPolynomial.aeval (fun j : Fin (r + 1) => dFrac^[j.val] f) (coeffDerivRat P) ∈ E := by
    refine heval_mem_E (coeffDerivRat P) fun α hα k hk => ?_
    rw [MvPolynomial.mem_support_iff, coeffDerivRat_coeff] at hα
    have hmem : α ∈ P.support := MvPolynomial.mem_support_iff.mpr fun h0 => hα (by rw [h0, dRat_zero])
    exact hP_vars α hmem k hk
  have hpd_mem : ∀ j : Fin (r + 1),
      MvPolynomial.aeval (fun k : Fin (r + 1) => dFrac^[k.val] f) (MvPolynomial.pderiv j P) ∈ E := by
    intro j
    refine heval_mem_E (MvPolynomial.pderiv j P) fun β hβ k hk => ?_
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hβ
    have hmem : β + Finsupp.single j 1 ∈ P.support := MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hβ)
    have h0 := hP_vars (β + Finsupp.single j 1) hmem k hk
    simp only [Finsupp.coe_add, Pi.add_apply] at h0
    omega
  -- Differentiate `aeval P = 0` once to solve for `dFrac^[m + 1] f ∈ E`!
  have hdiff0 := congrArg dFrac hP_val
  rw [dFrac_zero, dFrac_mvPoly_aeval] at hdiff0
  have hsplit_sum : ∑ j : Fin (r + 1),
        MvPolynomial.aeval (fun k : Fin (r + 1) => dFrac^[k.val] f) (MvPolynomial.pderiv j P) * dFrac^[j.val + 1] f =
      MvPolynomial.aeval (fun k : Fin (r + 1) => dFrac^[k.val] f) (MvPolynomial.pderiv m P) * dFrac^[m.val + 1] f +
      ∑ j ∈ Finset.univ.erase m,
        MvPolynomial.aeval (fun k : Fin (r + 1) => dFrac^[k.val] f) (MvPolynomial.pderiv j P) * dFrac^[j.val + 1] f :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ m)).symm
  rw [hsplit_sum] at hdiff0
  have herase_mem : (∑ j ∈ Finset.univ.erase m,
        MvPolynomial.aeval (fun k : Fin (r + 1) => dFrac^[k.val] f) (MvPolynomial.pderiv j P) * dFrac^[j.val + 1] f) ∈ E := by
    refine E.sum_mem fun j hj => ?_
    by_cases hlt : j < m
    · exact E.mul_mem (hpd_mem j) (hf_mem_E (j.val + 1) hlt)
    · have hgt : m < j := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm (Finset.ne_of_mem_erase hj))
      rw [hpd_gt_zero j hgt, map_zero, zero_mul]; exact E.zero_mem
  have hnext_eq : dFrac^[m.val + 1] f =
      -(MvPolynomial.aeval (fun j : Fin (r + 1) => dFrac^[j.val] f) (coeffDerivRat P) +
        ∑ j ∈ Finset.univ.erase m,
          MvPolynomial.aeval (fun k : Fin (r + 1) => dFrac^[k.val] f) (MvPolynomial.pderiv j P) * dFrac^[j.val + 1] f) /
      MvPolynomial.aeval (fun k : Fin (r + 1) => dFrac^[k.val] f) (MvPolynomial.pderiv m P) := by
    rw [eq_div_iff hpd_m_eval_ne]
    linear_combination hdiff0
  have hnext_mem : dFrac^[m.val + 1] f ∈ E := by
    rw [hnext_eq]
    exact E.div_mem (E.neg_mem (E.add_mem hcD_mem herase_mem)) (hpd_mem m)
  refine ⟨S, hf_mem_E 0 (Nat.zero_le _), isDiffClosedRHP_adjoin_of_gens fun s hs => ?_⟩
  rw [Finset.mem_coe, Finset.mem_image] at hs
  obtain ⟨k, hk, rfl⟩ := hs
  have hk_le : k ≤ m.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [← Function.iterate_succ_apply' dFrac k f]
  rcases lt_or_eq_of_le hk_le with hlt | rfl
  · exact hf_mem_E (k + 1) hlt
  · exact hnext_mem

/-- **Backward `trdeg` Transfer Lemma**:
If `g : FracHolRHP` lies in a `dFrac`-closed finitely generated `IntermediateField.adjoin (RatFunc ℂ) S`,
then `g` satisfies a nonzero polynomial ADE over `Polynomial ℂ` in `FracHolRHP`! -/
private lemma exists_nonzero_poly_ade_of_mem_dClosed {S : Finset FracHolRHP} {g : FracHolRHP}
    (hg : g ∈ IntermediateField.adjoin (RatFunc ℂ) (S : Set FracHolRHP))
    (hclosed : IsDiffClosedRHP (IntermediateField.adjoin (RatFunc ℂ) (S : Set FracHolRHP))) :
    ∃ (m : ℕ) (Q : MvPolynomial (Fin (m + 1)) (Polynomial ℂ)),
      Q ≠ 0 ∧ MvPolynomial.eval₂ (algFrac.comp polyToHol) (fun j : Fin (m + 1) => dFrac^[j.val] g) Q = 0 := by
  classical
  let E := IntermediateField.adjoin (RatFunc ℂ) (S : Set FracHolRHP)
  have hjet_mem : ∀ k : ℕ, dFrac^[k] g ∈ E := by
    intro k
    induction k with
    | zero => simpa using hg
    | succ k ih => rw [Function.iterate_succ_apply']; exact hclosed _ ih
  let m : ℕ := S.card
  let xE : Fin (m + 1) → E := fun j => ⟨dFrac^[j.val] g, hjet_mem j.val⟩
  have htrdeg : Algebra.trdeg (RatFunc ℂ) E ≤ (m : Cardinal) := trdeg_adjoin_finset_le S
  have hnot_indep : ¬ AlgebraicIndependent (RatFunc ℂ) xE := by
    intro hind
    have hcard := hind.cardinalMk_le_trdeg
    have hfin : Cardinal.mk (Fin (m + 1)) = ((m + 1 : ℕ) : Cardinal) := by simp
    rw [hfin] at hcard
    have hle : ((m + 1 : ℕ) : Cardinal) ≤ (m : Cardinal) := hcard.trans htrdeg
    have hnat : m + 1 ≤ m := by exact_mod_cast hle
    omega
  rw [algebraicIndependent_iff] at hnot_indep
  push Not at hnot_indep
  obtain ⟨Q_K, hQ_K_eval, hQ_K_ne⟩ := hnot_indep
  -- Clear denominators of `Q_K : MvPolynomial (Fin (m + 1)) (RatFunc ℂ)` into `Polynomial ℂ`!
  let D_all : Polynomial ℂ := ∏ α ∈ Q_K.support, (Q_K.coeff α).denom
  have hD_ne : D_all ≠ 0 := Finset.prod_ne_zero_iff.mpr fun α _ => RatFunc.denom_ne_zero _
  let Q : MvPolynomial (Fin (m + 1)) (Polynomial ℂ) :=
    ∑ α ∈ Q_K.support, MvPolynomial.monomial α ((Q_K.coeff α).num * ∏ β ∈ Q_K.support.erase α, (Q_K.coeff β).denom)
  have hQ_map : MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) Q =
      MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) D_all) * Q_K := by
    ext α
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul]
    dsimp only [Q]
    rw [MvPolynomial.coeff_sum]
    simp_rw [MvPolynomial.coeff_monomial]
    by_cases hα : α ∈ Q_K.support
    · rw [Finset.sum_eq_single α]
      · simp only [↓reduceIte, map_mul, map_prod]
        have hD_split : D_all = (Q_K.coeff α).denom * ∏ β ∈ Q_K.support.erase α, (Q_K.coeff β).denom :=
          (Finset.mul_prod_erase Q_K.support _ hα).symm
        have hden_ne : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Q_K.coeff α).denom ≠ 0 := by
          intro h0
          exact RatFunc.denom_ne_zero _ ((RatFunc.algebraMap_injective ℂ) (h0.trans (map_zero _).symm))
        have hmul : algebraMap (Polynomial ℂ) (RatFunc ℂ) (Q_K.coeff α).denom * (Q_K.coeff α) =
            algebraMap (Polynomial ℂ) (RatFunc ℂ) (Q_K.coeff α).num := by
          have h := congrArg (algebraMap (Polynomial ℂ) (RatFunc ℂ) (Q_K.coeff α).denom * ·)
            (RatFunc.num_div_denom (Q_K.coeff α))
          rw [mul_div_cancel₀ _ hden_ne] at h
          exact h.symm
        rw [hD_split, map_mul, map_prod]
        linear_combination -(∏ x ∈ Q_K.support.erase α, algebraMap (Polynomial ℂ) (RatFunc ℂ) (Q_K.coeff x).denom) * hmul
      · intro β _ hβα; simp [hβα]
      · intro hnot; exact absurd hα hnot
    · rw [MvPolynomial.notMem_support_iff.mp hα, mul_zero]
      have h0 : ∑ β ∈ Q_K.support,
          (if β = α then (Q_K.coeff β).num * ∏ γ ∈ Q_K.support.erase β, (Q_K.coeff γ).denom else 0) = 0 :=
        Finset.sum_eq_zero fun β hβ => by
          have hne : β ≠ α := fun h => hα (h ▸ hβ)
          simp [hne]
      rw [h0, map_zero]
  have hQ_ne : Q ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hQ_map
    have hD_K : algebraMap (Polynomial ℂ) (RatFunc ℂ) D_all ≠ 0 := fun hd0 =>
      hD_ne ((RatFunc.algebraMap_injective ℂ) (hd0.trans (map_zero _).symm))
    have hC_ne : MvPolynomial.C (σ := Fin (m + 1)) (algebraMap (Polynomial ℂ) (RatFunc ℂ) D_all) ≠ 0 :=
      MvPolynomial.C_ne_zero.mpr hD_K
    exact mul_ne_zero hC_ne hQ_K_ne hQ_map.symm
  have hQ_K_eval_F : MvPolynomial.aeval (fun j : Fin (m + 1) => dFrac^[j.val] g) Q_K = 0 := by
    have hval := congrArg Subtype.val hQ_K_eval
    have hcoe : (MvPolynomial.aeval xE Q_K).1 = MvPolynomial.aeval (fun j : Fin (m + 1) => dFrac^[j.val] g) Q_K := by
      have hgen : ∀ R : MvPolynomial (Fin (m + 1)) (RatFunc ℂ),
          (MvPolynomial.aeval xE R).1 = MvPolynomial.aeval (fun j : Fin (m + 1) => dFrac^[j.val] g) R := by
        intro R
        induction R using MvPolynomial.induction_on with
        | C c => simp only [MvPolynomial.aeval_C]; rfl
        | add R₁ R₂ h₁ h₂ => simp only [map_add]; exact congrArg₂ (· + ·) h₁ h₂
        | mul_X R₁ j h₁ => simp only [map_mul, MvPolynomial.aeval_X]; exact congrArg (· * dFrac^[j.val] g) h₁
      exact hgen Q_K
    rw [← hcoe, hval]; rfl
  refine ⟨m, Q, hQ_ne, ?_⟩
  have hcomp : (algFrac.comp polyToHol) = ratToFrac.comp (algebraMap (Polynomial ℂ) (RatFunc ℂ)) :=
    RingHom.ext fun p => (ratToFrac_algebraMap p).symm
  rw [hcomp, ← MvPolynomial.eval₂_map]
  change MvPolynomial.aeval (fun j : Fin (m + 1) => dFrac^[j.val] g)
      (MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) Q) = 0
  rw [hQ_map, map_mul, hQ_K_eval_F, mul_zero]

/-- Euler operator `θ = z · d/dz` in `FracHolRHP` and its leading-term expansion in ordinary derivatives. -/
private def thetaFrac (f : FracHolRHP) : FracHolRHP := algFrac zVarHol * dFrac f

private lemma thetaFrac_iter_expand (k : ℕ) :
    ∃ c : Fin k → Polynomial ℂ, ∀ f : FracHolRHP,
      thetaFrac^[k] f = (algFrac zVarHol) ^ k * dFrac^[k] f +
        ∑ j : Fin k, algFrac (polyToHol (c j)) * dFrac^[j.val] f := by
  induction k with
  | zero =>
    refine ⟨Fin.elim0, fun f => by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    let cNew : Fin (k + 1) → Polynomial ℂ := fun j =>
      if hlt : j.val < k then
        Polynomial.X * (c ⟨j.val, hlt⟩).derivative +
        (if hpos : 0 < j.val then Polynomial.X * c ⟨j.val - 1, by omega⟩ else 0)
      else
        Polynomial.C (k : ℂ) * Polynomial.X ^ k +
        (if hk : 0 < k then Polynomial.X * c ⟨k - 1, by omega⟩ else 0)
    refine ⟨cNew, fun f => ?_⟩
    rw [Function.iterate_succ_apply', hc f]
    unfold thetaFrac
    have hsum_d : dFrac (∑ j : Fin k, algFrac (polyToHol (c j)) * dFrac^[j.val] f) =
        ∑ j : Fin k, (algFrac (polyToHol (c j).derivative) * dFrac^[j.val] f +
          algFrac (polyToHol (c j)) * dFrac^[j.val + 1] f) := by
      have hgen : ∀ (s : Finset (Fin k)),
          dFrac (∑ j ∈ s, algFrac (polyToHol (c j)) * dFrac^[j.val] f) =
          ∑ j ∈ s, (algFrac (polyToHol (c j).derivative) * dFrac^[j.val] f +
            algFrac (polyToHol (c j)) * dFrac^[j.val + 1] f) := by
        intro s; classical
        induction s using Finset.induction_on with
        | empty => simp [dFrac_zero]
        | insert j s hj ihs =>
          rw [Finset.sum_insert hj, Finset.sum_insert hj, dFrac_add, ihs, dFrac_mul,
            dFrac_algFrac, dHol_polyToHol, Function.iterate_succ_apply']
      exact hgen Finset.univ
    have hpow_d : dFrac ((algFrac zVarHol) ^ k) = algFrac (polyToHol (Polynomial.C (k : ℂ) * Polynomial.X ^ (k - 1))) := by
      rw [← algFrac.map_pow, dFrac_algFrac, dHol_pow, dHol_zVar, mul_one]
      congr 1
      simp only [polyToHol, map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Algebra.smul_def]
    rw [dFrac_add, dFrac_mul, hpow_d, hsum_d, ← Function.iterate_succ_apply' dFrac k f, mul_add, mul_add]
    have htop : algFrac zVarHol * ((algFrac zVarHol) ^ k * dFrac^[k + 1] f) =
        (algFrac zVarHol) ^ (k + 1) * dFrac^[k + 1] f := by rw [pow_succ]; ring
    rw [htop]
    -- Reassemble the lower-order sum on `Fin (k + 1)` cleanly!
    have hlower : algFrac zVarHol * (algFrac (polyToHol (Polynomial.C (k : ℂ) * Polynomial.X ^ (k - 1))) * dFrac^[k] f) +
        algFrac zVarHol * ∑ j : Fin k, (algFrac (polyToHol (c j).derivative) * dFrac^[j.val] f +
          algFrac (polyToHol (c j)) * dFrac^[j.val + 1] f) =
        ∑ j : Fin (k + 1), algFrac (polyToHol (cNew j)) * dFrac^[j.val] f := by
      have hz_eq : algFrac zVarHol = algFrac (polyToHol Polynomial.X) := by simp [polyToHol]
      rw [Fin.sum_univ_castSucc]
      have hlast : algFrac (polyToHol (cNew (Fin.last k))) * dFrac^[k] f =
          algFrac zVarHol * (algFrac (polyToHol (Polynomial.C (k : ℂ) * Polynomial.X ^ (k - 1))) * dFrac^[k] f) +
          (if hk : 0 < k then algFrac zVarHol * (algFrac (polyToHol (c ⟨k - 1, by omega⟩)) * dFrac^[k] f) else 0) := by
        dsimp only [cNew]
        simp only [Fin.val_last, lt_irrefl, ↓reduceDIte, polyToHol.map_add, algFrac.map_add, add_mul]
        congr 1
        · cases k with
          | zero => simp
          | succ m =>
            rw [hz_eq, ← mul_assoc, ← algFrac.map_mul, ← polyToHol.map_mul]
            congr 2; simp only [Nat.add_sub_cancel]; ring
        · split_ifs with hk
          · rw [hz_eq, ← mul_assoc, ← algFrac.map_mul, ← polyToHol.map_mul]
          · simp
      have hcast : ∑ j : Fin k, algFrac (polyToHol (cNew j.castSucc)) * dFrac^[j.val] f =
          ∑ j : Fin k, (algFrac zVarHol * (algFrac (polyToHol (c j).derivative) * dFrac^[j.val] f)) +
          ∑ j : Fin k, (if hpos : 0 < j.val then
            algFrac zVarHol * (algFrac (polyToHol (c ⟨j.val - 1, by omega⟩)) * dFrac^[j.val] f) else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        dsimp only [cNew]
        simp only [Fin.val_castSucc, j.isLt, ↓reduceDIte, polyToHol.map_add, algFrac.map_add, add_mul]
        congr 1
        · rw [hz_eq, ← mul_assoc, ← algFrac.map_mul, ← polyToHol.map_mul]
        · split_ifs with hpos
          · rw [hz_eq, ← mul_assoc, ← algFrac.map_mul, ← polyToHol.map_mul]
          · simp
      have hshift : (∑ j : Fin k, algFrac zVarHol * (algFrac (polyToHol (c j)) * dFrac^[j.val + 1] f)) =
          (∑ j : Fin k, if hpos : 0 < j.val then
            algFrac zVarHol * (algFrac (polyToHol (c ⟨j.val - 1, by omega⟩)) * dFrac^[j.val] f) else 0) +
          (if hk : 0 < k then algFrac zVarHol * (algFrac (polyToHol (c ⟨k - 1, by omega⟩)) * dFrac^[k] f) else 0) := by
        cases k with
        | zero => simp
        | succ m =>
          simp only [Nat.zero_lt_succ, ↓reduceDIte, Nat.add_sub_cancel]
          rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
          simp only [Fin.val_zero, lt_irrefl, ↓reduceDIte, zero_add, Fin.val_succ, Nat.zero_lt_succ,
            Nat.add_sub_cancel, Fin.val_castSucc, Fin.val_last]
          rfl
      have hdist : algFrac zVarHol * ∑ j : Fin k, (algFrac (polyToHol (c j).derivative) * dFrac^[j.val] f +
            algFrac (polyToHol (c j)) * dFrac^[j.val + 1] f) =
          (∑ j : Fin k, algFrac zVarHol * (algFrac (polyToHol (c j).derivative) * dFrac^[j.val] f)) +
          (∑ j : Fin k, algFrac zVarHol * (algFrac (polyToHol (c j)) * dFrac^[j.val + 1] f)) := by
        rw [Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.mul_sum]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [hdist, hlast, hcast, hshift]
      ring
    linear_combination hlower

/-- Connect `eulerOp q g` on `RHP` to `∑ m, q.coeff m * thetaFrac^[m] (algFrac (holMK hg))`. -/
private lemma analyticOnNhd_thetaIter_RHP {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g RHP) (k : ℕ) :
    AnalyticOnNhd ℂ (thetaIter k g) RHP := by
  induction k with
  | zero => exact hg
  | succ k ih =>
    have hstep : thetaIter (k + 1) g = fun z => z * deriv (thetaIter k g) z := by
      funext z; exact congrFun (Function.iterate_succ_apply' thetaOp k g) z
    rw [hstep]
    exact analyticOnNhd_id.mul ih.deriv

private lemma thetaFrac_iter_holMK {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g RHP) (k : ℕ) :
    thetaFrac^[k] (algFrac (holMK hg)) = algFrac (holMK (analyticOnNhd_thetaIter_RHP hg k)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold thetaFrac
    rw [dFrac_algFrac, dHol_mk, ← algFrac.map_mul]
    congr 1; ext z
    change z.1 * deriv (thetaIter k g) z.1 = thetaIter (k + 1) g z.1
    exact (congrFun (Function.iterate_succ_apply' thetaOp k g) z.1).symm

private lemma holRHP_eval₂_apply {r : ℕ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g RHP)
    (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (z : RHP) :
    (MvPolynomial.eval₂ polyToHol (fun j : Fin (r + 1) => dHol^[j.val] (holMK hg)) Q).1 z =
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g z.1)
        (Q.map (Polynomial.evalRingHom z.1)) := by
  let evZ : HolRHP →+* ℂ := (Pi.evalRingHom (fun _ : RHP => ℂ) z).comp HolRHP.val.toRingHom
  change evZ (MvPolynomial.eval₂ polyToHol (fun j : Fin (r + 1) => dHol^[j.val] (holMK hg)) Q) = _
  rw [MvPolynomial.hom_eval₂, MvPolynomial.eval_map]
  congr 1
  · exact RingHom.ext fun p => polyToHol_apply p z
  · funext j; change (dHol^[j.val] (holMK hg)).1 z = iteratedDeriv j.val g z.1
    rw [dHol_iter_mk hg j.val]; rfl

/-- **Unconditional Non-Existence of Any Polynomial ODE for `frPoisson b` (`b ≥ 2`)**:
For EVERY `b ≥ 2`, `frPoisson b` satisfies NO nonzero algebraic differential equation over `ℂ[x]` on `(0, ∞)`. -/
theorem frPoisson_no_ade (b : ℕ) (hb : 2 ≤ b) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ x : ℝ, 0 < x →
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => frPoisson b (t : ℂ)) x)
        (P.map (Polynomial.evalRingHom (x : ℂ))) = 0) :
    P = 0 := by
  classical
  by_contra hP_ne
  -- Step 1: `2^N`-scaling reduction (Section 4B) transfers the ADE from `frPoisson b` to `v_b b` on `RHP`!
  obtain ⟨Q, hQ_ne, hQ_van⟩ := exists_nonzero_ade_v_b_of_frPoisson_ade hb P hP_ne hP
  have hv_an : AnalyticOnNhd ℂ (v_b b) RHP := (v_b_differentiableOn hb).analyticOnNhd isOpen_RHP
  let vF : FracHolRHP := algFrac (holMK hv_an)
  -- Lift `Q` to a nonzero `MvPolynomial (Fin (r + 1)) (RatFunc ℂ)` vanishing on `vF`!
  let Q_K : MvPolynomial (Fin (r + 1)) (RatFunc ℂ) := MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) Q
  have hQ_K_ne : Q_K ≠ 0 := by
    intro h0; apply hQ_ne; apply MvPolynomial.ext; intro α
    have hc := congrArg (fun R => R.coeff α) h0
    rw [MvPolynomial.coeff_map] at hc
    exact (RatFunc.algebraMap_injective ℂ) (by simpa using hc)
  have hQ_K_val : MvPolynomial.aeval (fun j : Fin (r + 1) => dFrac^[j.val] vF) Q_K = 0 := by
    have hcomp : (algFrac.comp polyToHol) = ratToFrac.comp (algebraMap (Polynomial ℂ) (RatFunc ℂ)) :=
      RingHom.ext fun p => (ratToFrac_algebraMap p).symm
    change MvPolynomial.eval₂ ratToFrac (fun j : Fin (r + 1) => dFrac^[j.val] vF)
      (MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) Q) = 0
    rw [MvPolynomial.eval₂_map, ← hcomp]
    have hhol_eq : MvPolynomial.eval₂ (algFrac.comp polyToHol) (fun j : Fin (r + 1) => dFrac^[j.val] vF) Q =
        algFrac (MvPolynomial.eval₂ polyToHol (fun j : Fin (r + 1) => dHol^[j.val] (holMK hv_an)) Q) := by
      simp_rw [vF, dFrac_iter_algFrac]
      exact (MvPolynomial.hom_eval₂ Q polyToHol algFrac (fun j : Fin (r + 1) => dHol^[j.val] (holMK hv_an))).symm
    rw [hhol_eq]
    have hzero_hol : MvPolynomial.eval₂ polyToHol (fun j : Fin (r + 1) => dHol^[j.val] (holMK hv_an)) Q = 0 := by
      ext z
      rw [holRHP_eval₂_apply hv_an Q z]
      exact hQ_van z.1 z.2
    rw [hzero_hol, algFrac.map_zero]
  -- Step 2: Obtain a `dFrac`-closed finitely generated intermediate field `E = adjoin S` containing `vF`!
  obtain ⟨S, hv_mem, hS_closed⟩ := exists_finset_dClosed_of_ade Q_K hQ_K_ne hQ_K_val
  let E := IntermediateField.adjoin (RatFunc ℂ) (S : Set FracHolRHP)
  -- Step 3: `deriv (v_b b) = C_b b + (log 2) * eulerOp (Q_b b) A_func` puts `eulerFrac (Q_b b) A` in `E`!
  have hA_an : AnalyticOnNhd ℂ A_func RHP := A_func_differentiableOn.analyticOnNhd isOpen_RHP
  have hu_an : AnalyticOnNhd ℂ masterLacunary RHP := masterLacunary_differentiableOn.analyticOnNhd isOpen_RHP
  let AF : FracHolRHP := algFrac (holMK hA_an)
  let uF : FracHolRHP := algFrac (holMK hu_an)
  let eulA : FracHolRHP := ∑ k ∈ Finset.range ((Q_b b).natDegree + 1),
    algFrac (polyToHol (Polynomial.C ((Q_b b).coeff k))) * thetaFrac^[k] AF
  have hdv_eq : dFrac vF = algFrac (polyToHol (Polynomial.C (C_b b))) +
      algFrac (polyToHol (Polynomial.C ((Real.log 2 : ℝ) : ℂ))) * eulA := by
    have hsum_hol : eulA = algFrac (∑ k ∈ Finset.range ((Q_b b).natDegree + 1),
        polyToHol (Polynomial.C ((Q_b b).coeff k)) * holMK (analyticOnNhd_thetaIter_RHP hA_an k)) := by
      rw [map_sum algFrac]; refine Finset.sum_congr rfl fun k _ => ?_
      rw [algFrac.map_mul, thetaFrac_iter_holMK hA_an k]
    rw [hsum_hol, show dFrac vF = algFrac (dHol (holMK hv_an)) from dFrac_algFrac _, ← algFrac.map_mul, ← algFrac.map_add]
    congr 1; rw [dHol_mk]; ext z
    let evZ : HolRHP →+* ℂ := (Pi.evalRingHom (fun _ : RHP => ℂ) z).comp HolRHP.val.toRingHom
    change evZ (holMK hv_an.deriv) = evZ (polyToHol (Polynomial.C (C_b b)) +
      polyToHol (Polynomial.C ((Real.log 2 : ℝ) : ℂ)) *
        ∑ k ∈ Finset.range ((Q_b b).natDegree + 1),
          polyToHol (Polynomial.C ((Q_b b).coeff k)) * holMK (analyticOnNhd_thetaIter_RHP hA_an k))
    rw [evZ.map_add, evZ.map_mul, map_sum evZ]
    simp only [evZ.map_mul]
    have hterm : ∀ k : ℕ, evZ (polyToHol (Polynomial.C ((Q_b b).coeff k))) *
        evZ (holMK (analyticOnNhd_thetaIter_RHP hA_an k)) = (Q_b b).coeff k * thetaIter k A_func z.1 := fun k => by
      change (polyToHol (Polynomial.C ((Q_b b).coeff k))).1 z * thetaIter k A_func z.1 = _
      rw [polyToHol_apply, Polynomial.eval_C]
    simp_rw [hterm]
    have hCb : evZ (polyToHol (Polynomial.C (C_b b))) = C_b b := by
      change (polyToHol (Polynomial.C (C_b b))).1 z = _; rw [polyToHol_apply, Polynomial.eval_C]
    have hlog : evZ (polyToHol (Polynomial.C ((Real.log 2 : ℝ) : ℂ))) = ((Real.log 2 : ℝ) : ℂ) := by
      change (polyToHol (Polynomial.C ((Real.log 2 : ℝ) : ℂ))).1 z = _; rw [polyToHol_apply, Polynomial.eval_C]
    rw [hCb, hlog]
    exact deriv_v_b_eq_eulerOp_A_func hb z.2
  have heulA_mem : eulA ∈ E := by
    have hdv_mem : dFrac vF ∈ E := hS_closed vF hv_mem
    have hCb_mem : algFrac (polyToHol (Polynomial.C (C_b b))) ∈ E := by
      rw [← ratToFrac_algebraMap]; exact E.algebraMap_mem _
    have hlog_mem : algFrac (polyToHol (Polynomial.C ((Real.log 2 : ℝ) : ℂ))) ∈ E := by
      rw [← ratToFrac_algebraMap]; exact E.algebraMap_mem _
    have hlog_ne : algFrac (polyToHol (Polynomial.C ((Real.log 2 : ℝ) : ℂ))) ≠ 0 := by
      intro h0
      have h0' : algFrac (polyToHol (Polynomial.C ((Real.log 2 : ℝ) : ℂ))) = algFrac (polyToHol 0) := by
        rw [polyToHol.map_zero, algFrac.map_zero]; exact h0
      have hc0 := polyToHol_injective (algFrac_injective h0')
      have h1 : ((Real.log 2 : ℝ) : ℂ) = 0 := Polynomial.C_eq_zero.mp hc0
      exact (Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne') h1
    have heq : eulA = (dFrac vF - algFrac (polyToHol (Polynomial.C (C_b b)))) /
        algFrac (polyToHol (Polynomial.C ((Real.log 2 : ℝ) : ℂ))) := by
      rw [eq_div_iff hlog_ne]; linear_combination -hdv_eq
    rw [heq]; exact E.div_mem (E.sub_mem hdv_mem hCb_mem) hlog_mem
  -- Step 4: Adjoin `{A, A', ..., A^{(d - 1)}}` (`d = (Q_b b).natDegree`) to `S` → still `dFrac`-closed!
  let d : ℕ := (Q_b b).natDegree
  let S' : Finset FracHolRHP := S ∪ (Finset.range d).image fun j => dFrac^[j] AF
  let E' := IntermediateField.adjoin (RatFunc ℂ) (S' : Set FracHolRHP)
  have hE_le_E' : E ≤ E' := IntermediateField.adjoin_le_iff.mpr fun x hx =>
    IntermediateField.subset_adjoin _ _ (Finset.mem_coe.mpr (Finset.mem_union_left _ hx))
  have hAF_lt_mem : ∀ j : ℕ, j < d → dFrac^[j] AF ∈ E' := fun j hj =>
    IntermediateField.subset_adjoin _ _
      (Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩)))
  -- Solve `eulA` for `dFrac^[d] AF ∈ E'` using `thetaFrac_iter_expand` and `Q_b_ne_zero hb`!
  have hAF_d_mem : dFrac^[d] AF ∈ E' := by
    have hexp : ∀ k : ℕ, ∃ c : Fin k → Polynomial ℂ,
        thetaFrac^[k] AF = (algFrac zVarHol) ^ k * dFrac^[k] AF +
          ∑ j : Fin k, algFrac (polyToHol (c j)) * dFrac^[j.val] AF := fun k => by
      obtain ⟨c, hc⟩ := thetaFrac_iter_expand k; exact ⟨c, hc AF⟩
    choose c hc using hexp
    have hlow_mem : ∀ k : ℕ, k < d → thetaFrac^[k] AF ∈ E' := fun k hk => by
      rw [hc k]
      refine E'.add_mem (E'.mul_mem (E'.pow_mem (by
          rw [show algFrac zVarHol = ratToFrac (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X) from
            (by rw [ratToFrac_algebraMap]; simp [polyToHol])]
          exact E'.algebraMap_mem _) k) (hAF_lt_mem k hk)) ?_
      refine E'.sum_mem fun j _ => E'.mul_mem (by rw [← ratToFrac_algebraMap]; exact E'.algebraMap_mem _)
        (hAF_lt_mem j.val (lt_trans j.isLt hk))
    have hsplit : eulA = algFrac (polyToHol (Polynomial.C ((Q_b b).coeff d))) * thetaFrac^[d] AF +
        ∑ k ∈ Finset.range d, algFrac (polyToHol (Polynomial.C ((Q_b b).coeff k))) * thetaFrac^[k] AF := by
      dsimp only [eulA]; rw [Finset.sum_range_succ, add_comm]
    rw [hc d] at hsplit
    have hlead_ne : algFrac (polyToHol (Polynomial.C ((Q_b b).coeff d))) * (algFrac zVarHol) ^ d ≠ 0 := by
      refine mul_ne_zero ?_ (pow_ne_zero d ?_)
      · intro h0
        have h0' : algFrac (polyToHol (Polynomial.C ((Q_b b).coeff d))) = algFrac (polyToHol 0) := by
          rw [polyToHol.map_zero, algFrac.map_zero]; exact h0
        have hc0 := polyToHol_injective (algFrac_injective h0')
        exact (Polynomial.leadingCoeff_ne_zero.mpr (Q_b_ne_zero hb)) (Polynomial.C_eq_zero.mp hc0)
      · intro h0
        have hz0 := algFrac_injective (h0.trans algFrac.map_zero.symm)
        have h1 := congrArg (fun f : HolRHP => f.1 ⟨1, by simp [RHP]⟩) hz0
        simp [zVarHol, holMK_apply] at h1
    have hsolve : dFrac^[d] AF =
        (eulA - ∑ k ∈ Finset.range d, algFrac (polyToHol (Polynomial.C ((Q_b b).coeff k))) * thetaFrac^[k] AF -
          algFrac (polyToHol (Polynomial.C ((Q_b b).coeff d))) *
            ∑ j : Fin d, algFrac (polyToHol (c d j)) * dFrac^[j.val] AF) /
        (algFrac (polyToHol (Polynomial.C ((Q_b b).coeff d))) * (algFrac zVarHol) ^ d) := by
      rw [eq_div_iff hlead_ne]; linear_combination -hsplit
    rw [hsolve]
    refine E'.div_mem (E'.sub_mem (E'.sub_mem (hE_le_E' heulA_mem) ?_) ?_) ?_
    · refine E'.sum_mem fun k hk => E'.mul_mem (by rw [← ratToFrac_algebraMap]; exact E'.algebraMap_mem _)
        (hlow_mem k (Finset.mem_range.mp hk))
    · refine E'.mul_mem (by rw [← ratToFrac_algebraMap]; exact E'.algebraMap_mem _) ?_
      refine E'.sum_mem fun j _ => E'.mul_mem (by rw [← ratToFrac_algebraMap]; exact E'.algebraMap_mem _)
        (hAF_lt_mem j.val j.isLt)
    · refine E'.mul_mem (by rw [← ratToFrac_algebraMap]; exact E'.algebraMap_mem _)
        (E'.pow_mem (by
          rw [show algFrac zVarHol = ratToFrac (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X) from
            (by rw [ratToFrac_algebraMap]; simp [polyToHol])]
          exact E'.algebraMap_mem _) d)
  have hS'_closed : IsDiffClosedRHP E' := by
    refine isDiffClosedRHP_adjoin_of_gens fun s hs => ?_
    rw [Finset.mem_coe, Finset.mem_union] at hs
    rcases hs with hsS | hsA
    · exact hE_le_E' (hS_closed s (IntermediateField.subset_adjoin _ _ hsS))
    · rw [Finset.mem_image] at hsA
      obtain ⟨j, hj, rfl⟩ := hsA
      have hj_lt : j < d := Finset.mem_range.mp hj
      rw [← Function.iterate_succ_apply' dFrac j AF]
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt hj_lt) with hlt | heq
      · exact hAF_lt_mem (j + 1) hlt
      · rw [heq]; exact hAF_d_mem
  -- Step 5: `uF = (algFrac zVarHol)⁻¹ * AF ∈ E'`!
  have hAF_mem_E' : AF ∈ E' := by
    cases hd : d with
    | zero => rw [hd] at hAF_d_mem; simpa using hAF_d_mem
    | succ d' => exact hAF_lt_mem 0 (by omega)
  have huF_mem_E' : uF ∈ E' := by
    have hAu : AF = algFrac zVarHol * uF := by
      rw [← algFrac.map_mul]; congr 1
    have hz_ne : algFrac zVarHol ≠ 0 := by
      intro h0
      have hz0 := algFrac_injective (h0.trans algFrac.map_zero.symm)
      have h1 := congrArg (fun f : HolRHP => f.1 ⟨1, by simp [RHP]⟩) hz0
      simp [zVarHol, holMK_apply] at h1
    have hu_eq : uF = AF / algFrac zVarHol := by rw [eq_div_iff hz_ne]; linear_combination -hAu
    rw [hu_eq]
    refine E'.div_mem hAF_mem_E' ?_
    rw [show algFrac zVarHol = ratToFrac (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X) from
      (by rw [ratToFrac_algebraMap]; simp [polyToHol])]
    exact E'.algebraMap_mem _
  -- Step 6: Extract nonzero polynomial ADE for `masterLacunary` on `RHP`, contradicting `masterLacunary_no_ade`!
  obtain ⟨m, Q_u, hQ_u_ne, hQ_u_val⟩ := exists_nonzero_poly_ade_of_mem_dClosed huF_mem_E' hS'_closed
  have hQ_u_van : ∀ s : ℂ, 0 < s.re →
      MvPolynomial.eval (fun j : Fin (m + 1) => iteratedDeriv j.val masterLacunary s)
        (Q_u.map (Polynomial.evalRingHom s)) = 0 := by
    have hhol_eq : MvPolynomial.eval₂ (algFrac.comp polyToHol) (fun j : Fin (m + 1) => dFrac^[j.val] uF) Q_u =
        algFrac (MvPolynomial.eval₂ polyToHol (fun j : Fin (m + 1) => dHol^[j.val] (holMK hu_an)) Q_u) := by
      simp_rw [uF, dFrac_iter_algFrac]
      exact (MvPolynomial.hom_eval₂ Q_u polyToHol algFrac (fun j : Fin (m + 1) => dHol^[j.val] (holMK hu_an))).symm
    rw [hhol_eq] at hQ_u_val
    have hzero_hol : MvPolynomial.eval₂ polyToHol (fun j : Fin (m + 1) => dHol^[j.val] (holMK hu_an)) Q_u = 0 :=
      algFrac_injective (hQ_u_val.trans algFrac.map_zero.symm)
    intro s hs
    have hval_s := congrArg (fun f : HolRHP => f.1 ⟨s, hs⟩) hzero_hol
    rw [holRHP_eval₂_apply hu_an Q_u ⟨s, hs⟩] at hval_s
    exact hval_s
  exact hQ_u_ne (masterLacunary_no_ade Q_u hQ_u_van)

/-- **Unconditional Non-Existence of Any Polynomial ODE for the Flajolet–Richmond EGF `frEGF b` (`b ≥ 2`)**:
For EVERY `b ≥ 2`, `frEGF b` satisfies NO nonzero algebraic differential equation over `ℂ[x]` on `(0, ∞)`. -/
theorem frEGF_no_ade (b : ℕ) (hb : 2 ≤ b) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ x : ℝ, 0 < x →
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => frEGF b (t : ℂ)) x)
        (P.map (Polynomial.evalRingHom (x : ℂ))) = 0) :
    P = 0 := by
  classical
  have hb1 : 1 ≤ b := by omega
  by_contra hP_ne
  -- Step 1: Extend the real-axis ADE for entire `frEGF b` to all of `RHP`!
  have hf_ent : Differentiable ℂ (frEGF b) := frEGF_differentiable hb1
  have hf_an : AnalyticOnNhd ℂ (frEGF b) RHP := hf_ent.differentiableOn.analyticOnNhd isOpen_RHP
  have hP_RHP : ∀ z : ℂ, 0 < z.re →
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (frEGF b) z)
        (P.map (Polynomial.evalRingHom z)) = 0 := by
    have hdiff_P : DifferentiableOn ℂ (fun z : ℂ =>
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (frEGF b) z)
          (P.map (Polynomial.evalRingHom z))) RHP := by
      have hrew : (fun z : ℂ =>
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (frEGF b) z)
            (P.map (Polynomial.evalRingHom z))) =
          fun z : ℂ => ∑ α ∈ P.support, (P.coeff α).eval z *
            ∏ j : Fin (r + 1), (iteratedDeriv j.val (frEGF b) z) ^ (α j) := by
        funext z; rw [MvPolynomial.eval_map, MvPolynomial.eval₂_eq']; rfl
      rw [hrew]
      refine DifferentiableOn.fun_sum fun α _ =>
        ((differentiable_poly_eval_complex _).differentiableOn).mul
          (differentiableOn_finset_prod_fr fun j _ =>
            ((analyticOnNhd_iteratedDeriv_RHP hf_an j.val).differentiableOn).pow (α j))
    have hreal : ∀ x : ℝ, 1 < x → x < 2 →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (frEGF b) (x : ℂ))
          (P.map (Polynomial.evalRingHom (x : ℂ))) = 0 := fun x hx1 _ => by
      have hjet : (fun j : Fin (r + 1) => iteratedDeriv j.val (frEGF b) (x : ℂ)) =
          fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => frEGF b (t : ℂ)) x :=
        funext fun j => (iteratedDeriv_comp_ofReal_eq_of_differentiable hf_ent j.val x).symm
      rw [hjet]; exact hP x (by linarith)
    exact fun z hz => eqOn_of_differentiableOn_eq_on_real_interval isOpen_RHP isPreconnected_RHP
      hdiff_P (differentiableOn_const 0) (by norm_num : (1 : ℝ) < 2)
      (fun x hx1 _ => by show 0 < ((x : ℂ)).re; rw [Complex.ofReal_re]; linarith) hreal hz
  -- Step 2: Lift `frEGF b` into `FracHolRHP` and extract a `dFrac`-closed finite-generator `E = adjoin S`!
  let fF : FracHolRHP := algFrac (holMK hf_an)
  let P_K : MvPolynomial (Fin (r + 1)) (RatFunc ℂ) := MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) P
  have hP_K_ne : P_K ≠ 0 := by
    intro h0; apply hP_ne; apply MvPolynomial.ext; intro α
    have hc := congrArg (fun R => R.coeff α) h0
    rw [MvPolynomial.coeff_map] at hc
    exact (RatFunc.algebraMap_injective ℂ) (by simpa using hc)
  have hP_K_val : MvPolynomial.aeval (fun j : Fin (r + 1) => dFrac^[j.val] fF) P_K = 0 := by
    have hcomp : (algFrac.comp polyToHol) = ratToFrac.comp (algebraMap (Polynomial ℂ) (RatFunc ℂ)) :=
      RingHom.ext fun p => (ratToFrac_algebraMap p).symm
    change MvPolynomial.eval₂ ratToFrac (fun j : Fin (r + 1) => dFrac^[j.val] fF)
      (MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) P) = 0
    rw [MvPolynomial.eval₂_map, ← hcomp]
    have hhol_eq : MvPolynomial.eval₂ (algFrac.comp polyToHol) (fun j : Fin (r + 1) => dFrac^[j.val] fF) P =
        algFrac (MvPolynomial.eval₂ polyToHol (fun j : Fin (r + 1) => dHol^[j.val] (holMK hf_an)) P) := by
      simp_rw [fF, dFrac_iter_algFrac]
      exact (MvPolynomial.hom_eval₂ P polyToHol algFrac (fun j : Fin (r + 1) => dHol^[j.val] (holMK hf_an))).symm
    rw [hhol_eq]
    have hzero_hol : MvPolynomial.eval₂ polyToHol (fun j : Fin (r + 1) => dHol^[j.val] (holMK hf_an)) P = 0 := by
      ext z
      rw [holRHP_eval₂_apply hf_an P z]
      exact hP_RHP z.1 z.2
    rw [hzero_hol, algFrac.map_zero]
  obtain ⟨S, hf_mem, hS_closed⟩ := exists_finset_dClosed_of_ade P_K hP_K_ne hP_K_val
  -- Step 3: Adjoin `exp(-z)` (which satisfies `y' = -y`) to `S` → still `dFrac`-closed and contains `frPoisson b`!
  have hexp_an : AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (-z)) RHP :=
    (differentiable_id.neg.cexp).differentiableOn.analyticOnNhd isOpen_RHP
  let eF : FracHolRHP := algFrac (holMK hexp_an)
  have hdeF : dFrac eF = -eF := by
    rw [show dFrac eF = algFrac (dHol (holMK hexp_an)) from dFrac_algFrac _, ← algFrac.map_neg]
    congr 1; rw [dHol_mk]; ext z
    simp only [holMK_apply, Subalgebra.coe_neg, Pi.neg_apply]
    have hd : HasDerivAt (fun w : ℂ => Complex.exp (-w)) (-Complex.exp (-z.1)) z.1 := by
      simpa using (hasDerivAt_id z.1).neg.cexp
    exact hd.deriv
  let S' : Finset FracHolRHP := insert eF S
  let E' := IntermediateField.adjoin (RatFunc ℂ) (S' : Set FracHolRHP)
  have hE_le_E' : IntermediateField.adjoin (RatFunc ℂ) (S : Set FracHolRHP) ≤ E' :=
    IntermediateField.adjoin_le_iff.mpr fun x hx =>
      IntermediateField.subset_adjoin _ _ (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hx))
  have heF_mem : eF ∈ E' := IntermediateField.subset_adjoin _ _ (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
  have hS'_closed : IsDiffClosedRHP E' := by
    refine isDiffClosedRHP_adjoin_of_gens fun s hs => ?_
    rw [Finset.mem_coe, Finset.mem_insert] at hs
    rcases hs with rfl | hsS
    · rw [hdeF]; exact E'.neg_mem heF_mem
    · exact hE_le_E' (hS_closed s (IntermediateField.subset_adjoin _ _ hsS))
  have hh_ent : Differentiable ℂ (frPoisson b) := frPoisson_differentiable hb1
  have hh_an : AnalyticOnNhd ℂ (frPoisson b) RHP := hh_ent.differentiableOn.analyticOnNhd isOpen_RHP
  let hF : FracHolRHP := algFrac (holMK hh_an)
  have hhF_eq : hF = eF * fF := by
    rw [← algFrac.map_mul]; congr 1
  have hhF_mem : hF ∈ E' := by rw [hhF_eq]; exact E'.mul_mem heF_mem (hE_le_E' hf_mem)
  -- Step 4: Extract nonzero polynomial ADE for `frPoisson b` on `(0, ∞)`, contradicting `frPoisson_no_ade`!
  obtain ⟨m, Q_h, hQ_h_ne, hQ_h_val⟩ := exists_nonzero_poly_ade_of_mem_dClosed hhF_mem hS'_closed
  have hQ_h_van : ∀ x : ℝ, 0 < x →
      MvPolynomial.eval (fun j : Fin (m + 1) => iteratedDeriv j.val (fun t : ℝ => frPoisson b (t : ℂ)) x)
        (Q_h.map (Polynomial.evalRingHom (x : ℂ))) = 0 := by
    have hhol_eq : MvPolynomial.eval₂ (algFrac.comp polyToHol) (fun j : Fin (m + 1) => dFrac^[j.val] hF) Q_h =
        algFrac (MvPolynomial.eval₂ polyToHol (fun j : Fin (m + 1) => dHol^[j.val] (holMK hh_an)) Q_h) := by
      simp_rw [hF, dFrac_iter_algFrac]
      exact (MvPolynomial.hom_eval₂ Q_h polyToHol algFrac (fun j : Fin (m + 1) => dHol^[j.val] (holMK hh_an))).symm
    rw [hhol_eq] at hQ_h_val
    have hzero_hol : MvPolynomial.eval₂ polyToHol (fun j : Fin (m + 1) => dHol^[j.val] (holMK hh_an)) Q_h = 0 :=
      algFrac_injective (hQ_h_val.trans algFrac.map_zero.symm)
    intro x hx
    have hx_mem : (x : ℂ) ∈ RHP := by show 0 < ((x : ℂ)).re; rw [Complex.ofReal_re]; exact hx
    have hval_x := congrArg (fun f : HolRHP => f.1 ⟨(x : ℂ), hx_mem⟩) hzero_hol
    rw [holRHP_eval₂_apply hh_an Q_h ⟨(x : ℂ), hx_mem⟩] at hval_x
    have hjet : (fun j : Fin (m + 1) => iteratedDeriv j.val (frPoisson b) (x : ℂ)) =
        fun j : Fin (m + 1) => iteratedDeriv j.val (fun t : ℝ => frPoisson b (t : ℂ)) x :=
      funext fun j => (iteratedDeriv_comp_ofReal_eq_of_differentiable hh_ent j.val x).symm
    rw [hjet] at hval_x
    exact hval_x
  exact hQ_h_ne (frPoisson_no_ade b hb Q_h hQ_h_van)

end Section5

/-! ## Section 6: Formal Power Series Differential Transcendence over `RatFunc ℂ` -/

section Section6

/-- Canonical embedding `ℂ[t] →+* ℂ((t))` via `PowerSeries ℂ →+* LaurentSeries ℂ`. -/
@[expose] def polyToLaurent : Polynomial ℂ →+* LaurentSeries ℂ :=
  (HahnSeries.ofPowerSeries ℤ ℂ).comp Polynomial.coeToPowerSeries.ringHom

private lemma polyToLaurent_injective : Function.Injective polyToLaurent :=
  (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)).comp (Polynomial.coe_injective ℂ)

/-- Canonical embedding `ℂ(t) →+* ℂ((t))` of rational functions into formal Laurent series. -/
@[expose] def ratToLaurent : RatFunc ℂ →+* LaurentSeries ℂ :=
  RatFunc.liftRingHom polyToLaurent fun p hp => by
    change polyToLaurent p ∈ nonZeroDivisors (LaurentSeries ℂ)
    rw [mem_nonZeroDivisors_iff_ne_zero] at hp ⊢
    intro h0
    have h0' : polyToLaurent p = polyToLaurent 0 := by rw [polyToLaurent.map_zero]; exact h0
    exact hp (polyToLaurent_injective h0')

private lemma ratToLaurent_algebraMap (p : Polynomial ℂ) :
    ratToLaurent (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) = polyToLaurent p := by
  unfold ratToLaurent
  simp [RatFunc.liftRingHom_apply]

/-- A formal power series `F ∈ ℂ⟦t⟧` is **differentially transcendental over `ℂ(t)`**
(`DTransOverRatFunc F`) if no nonzero multivariate polynomial `P ∈ ℂ(t)[Y₀, …, Yᵣ]` vanishes on
its derivative jet `(F, F', …, F^{(r)})` inside `ℂ((t))`. -/
@[expose] def DTransOverRatFunc (F : PowerSeries ℂ) : Prop :=
  ∀ {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
    MvPolynomial.eval₂ ratToLaurent
      (fun j : Fin (r + 1) => HahnSeries.ofPowerSeries ℤ ℂ (seriesJet F j.val)) P = 0 →
    P = 0

/-- Differential transcendence over `RatFunc ℂ` is equivalent to the absence of any nonzero
polynomial differential equation over `Polynomial ℂ` in `PowerSeries ℂ`. -/
theorem dTransOverRatFunc_iff_no_poly_ade (F : PowerSeries ℂ) :
    DTransOverRatFunc F ↔
      ∀ {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)),
        MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom
          (fun j : Fin (r + 1) => seriesJet F j.val) P = 0 →
        P = 0 := by
  classical
  constructor
  · intro hD r P hP
    let P_K : MvPolynomial (Fin (r + 1)) (RatFunc ℂ) :=
      MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) P
    have hcomp : polyToLaurent = ratToLaurent.comp (algebraMap (Polynomial ℂ) (RatFunc ℂ)) :=
      RingHom.ext fun p => (ratToLaurent_algebraMap p).symm
    have hP_K : MvPolynomial.eval₂ ratToLaurent
        (fun j : Fin (r + 1) => HahnSeries.ofPowerSeries ℤ ℂ (seriesJet F j.val)) P_K = 0 := by
      dsimp only [P_K]
      rw [MvPolynomial.eval₂_map, ← hcomp]
      change MvPolynomial.eval₂ ((HahnSeries.ofPowerSeries ℤ ℂ).comp Polynomial.coeToPowerSeries.ringHom)
        (fun j : Fin (r + 1) => HahnSeries.ofPowerSeries ℤ ℂ (seriesJet F j.val)) P = 0
      rw [← MvPolynomial.hom_eval₂ P Polynomial.coeToPowerSeries.ringHom (HahnSeries.ofPowerSeries ℤ ℂ)
        (fun j : Fin (r + 1) => seriesJet F j.val), hP, map_zero]
    have hPK0 : P_K = 0 := hD P_K hP_K
    apply MvPolynomial.ext; intro α
    have hc := congrArg (fun R => R.coeff α) hPK0
    rw [MvPolynomial.coeff_map] at hc
    exact (RatFunc.algebraMap_injective ℂ) (by simpa using hc)
  · intro hPoly r P_K hPK
    by_contra hPK_ne
    let D_all : Polynomial ℂ := ∏ α ∈ P_K.support, (P_K.coeff α).denom
    have hD_ne : D_all ≠ 0 := Finset.prod_ne_zero_iff.mpr fun α _ => RatFunc.denom_ne_zero _
    let Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
      ∑ α ∈ P_K.support, MvPolynomial.monomial α ((P_K.coeff α).num * ∏ β ∈ P_K.support.erase α, (P_K.coeff β).denom)
    have hQ_map : MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) Q =
        MvPolynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) D_all) * P_K := by
      apply MvPolynomial.ext; intro α
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul]
      dsimp only [Q]
      rw [MvPolynomial.coeff_sum]
      simp_rw [MvPolynomial.coeff_monomial]
      by_cases hα : α ∈ P_K.support
      · rw [Finset.sum_eq_single α]
        · simp only [↓reduceIte, map_mul, map_prod]
          have hD_split : D_all = (P_K.coeff α).denom * ∏ β ∈ P_K.support.erase α, (P_K.coeff β).denom :=
            (Finset.mul_prod_erase P_K.support _ hα).symm
          have hden_ne : algebraMap (Polynomial ℂ) (RatFunc ℂ) (P_K.coeff α).denom ≠ 0 := by
            intro h0
            exact RatFunc.denom_ne_zero _ ((RatFunc.algebraMap_injective ℂ) (h0.trans (map_zero _).symm))
          have hmul : algebraMap (Polynomial ℂ) (RatFunc ℂ) (P_K.coeff α).denom * (P_K.coeff α) =
              algebraMap (Polynomial ℂ) (RatFunc ℂ) (P_K.coeff α).num := by
            have h := congrArg (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P_K.coeff α).denom * ·)
              (RatFunc.num_div_denom (P_K.coeff α))
            rw [mul_div_cancel₀ _ hden_ne] at h
            exact h.symm
          rw [hD_split, map_mul, map_prod]
          linear_combination -(∏ x ∈ P_K.support.erase α, algebraMap (Polynomial ℂ) (RatFunc ℂ) (P_K.coeff x).denom) * hmul
        · intro β _ hβα; simp [hβα]
        · intro hnot; exact absurd hα hnot
      · rw [MvPolynomial.notMem_support_iff.mp hα, mul_zero]
        have h0 : ∑ β ∈ P_K.support,
            (if β = α then (P_K.coeff β).num * ∏ γ ∈ P_K.support.erase β, (P_K.coeff γ).denom else 0) = 0 :=
          Finset.sum_eq_zero fun β hβ => by
            have hne : β ≠ α := fun h => hα (h ▸ hβ)
            simp [hne]
        rw [h0, map_zero]
    have hQ_ne : Q ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hQ_map
      have hD_K : algebraMap (Polynomial ℂ) (RatFunc ℂ) D_all ≠ 0 := fun hd0 =>
        hD_ne ((RatFunc.algebraMap_injective ℂ) (hd0.trans (map_zero _).symm))
      have hC_ne : MvPolynomial.C (σ := Fin (r + 1)) (algebraMap (Polynomial ℂ) (RatFunc ℂ) D_all) ≠ 0 :=
        MvPolynomial.C_ne_zero.mpr hD_K
      exact mul_ne_zero hC_ne hPK_ne hQ_map.symm
    have hQ_eval : MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom
        (fun j : Fin (r + 1) => seriesJet F j.val) Q = 0 := by
      apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
      rw [map_zero, MvPolynomial.hom_eval₂]
      change MvPolynomial.eval₂ polyToLaurent
        (fun j : Fin (r + 1) => HahnSeries.ofPowerSeries ℤ ℂ (seriesJet F j.val)) Q = 0
      have hcomp : polyToLaurent = ratToLaurent.comp (algebraMap (Polynomial ℂ) (RatFunc ℂ)) :=
        RingHom.ext fun p => (ratToLaurent_algebraMap p).symm
      rw [hcomp, ← MvPolynomial.eval₂_map, hQ_map, MvPolynomial.eval₂_mul, hPK, mul_zero]
    exact hQ_ne (hPoly Q hQ_eval)

/-- Exact equivalence between `DTransOverRatFunc F` (no nonzero rational-function ODE over
`RatFunc ℂ`) and `AlgebraicIndependent ℂ (seriesCoordinates F)` in `PowerSeries ℂ`. -/
theorem dTransOverRatFunc_iff_algebraicIndependent (F : PowerSeries ℂ) :
    DTransOverRatFunc F ↔ AlgebraicIndependent ℂ (seriesCoordinates F) := by
  classical
  rw [dTransOverRatFunc_iff_no_poly_ade, algebraicIndependent_iff]
  constructor
  · intro hPoly Q hQ
    by_contra hQ_ne
    let r : ℕ := Q.support.sup fun α => α.support.sup id
    have hbound : ∀ α ∈ Q.support, ∀ i ∈ α.support, i ≤ r := fun α hα i hi =>
      le_trans (Finset.le_sup (f := id) hi) (Finset.le_sup (f := fun β : ℕ →₀ ℕ => β.support.sup id) hα)
    let collapseMon : (ℕ →₀ ℕ) → (Fin (r + 1) →₀ ℕ) := fun α =>
      Finsupp.equivFunOnFinite.symm (fun j : Fin (r + 1) => α (j.val + 1))
    let P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
      ∑ α ∈ Q.support, MvPolynomial.monomial (collapseMon α) (Polynomial.monomial (α 0) (Q.coeff α))
    have hP_eval : MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom
        (fun j : Fin (r + 1) => seriesJet F j.val) P = 0 := by
      dsimp only [P]
      rw [MvPolynomial.eval₂_sum]
      have hterm : ∀ α ∈ Q.support,
          MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom (fun j : Fin (r + 1) => seriesJet F j.val)
            (MvPolynomial.monomial (collapseMon α) (Polynomial.monomial (α 0) (Q.coeff α))) =
          PowerSeries.C (Q.coeff α) * α.prod (fun i e => seriesCoordinates F i ^ e) := by
        intro α hα
        rw [MvPolynomial.eval₂_monomial]
        have hpoly_mon : Polynomial.coeToPowerSeries.ringHom (Polynomial.monomial (α 0) (Q.coeff α)) =
            PowerSeries.C (Q.coeff α) * PowerSeries.X ^ (α 0) := by
          rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
            Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]
        rw [hpoly_mon, mul_assoc]
        congr 1
        have hprod_fin : (collapseMon α).prod (fun j e => seriesJet F j.val ^ e) =
            ∏ j : Fin (r + 1), seriesCoordinates F (j.val + 1) ^ (α (j.val + 1)) := by
          rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
          refine Finset.prod_congr rfl fun j _ => rfl
        rw [hprod_fin]
        have hsub : α.support ⊆ Finset.range (r + 2) := fun i hi =>
          Finset.mem_range.mpr (by have := hbound α hα i hi; omega)
        have hprod_range : α.prod (fun i e => seriesCoordinates F i ^ e) =
            ∏ i ∈ Finset.range (r + 2), seriesCoordinates F i ^ (α i) := by
          rw [Finsupp.prod]
          exact Finset.prod_subset hsub fun i _ hi => by
            rw [Finsupp.notMem_support_iff.mp hi, pow_zero]
        rw [hprod_range, Finset.prod_range_succ', Fin.prod_univ_eq_prod_range (fun k => seriesCoordinates F (k + 1) ^ α (k + 1)) (r + 1),
          mul_comm]
        rfl
      rw [Finset.sum_congr rfl hterm]
      have hQ_eq : ∑ α ∈ Q.support, PowerSeries.C (Q.coeff α) * α.prod (fun i e => seriesCoordinates F i ^ e) =
          MvPolynomial.aeval (seriesCoordinates F) Q := by
        rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
        rfl
      rw [hQ_eq]; exact hQ
    have hP0 : P = 0 := hPoly P hP_eval
    have hsup_ne : Q.support.Nonempty := MvPolynomial.support_nonempty.mpr hQ_ne
    obtain ⟨α₀, hα₀⟩ := hsup_ne
    have hcoeff0 : ((P.coeff (collapseMon α₀)).coeff (α₀ 0)) = 0 := by rw [hP0]; simp
    have hP_coeff : (P.coeff (collapseMon α₀)).coeff (α₀ 0) = Q.coeff α₀ := by
      dsimp only [P]
      rw [MvPolynomial.coeff_sum]
      have hpoly_sum : (∑ α ∈ Q.support, (MvPolynomial.monomial (collapseMon α)
          (Polynomial.monomial (α 0) (Q.coeff α))).coeff (collapseMon α₀)).coeff (α₀ 0) =
          ∑ α ∈ Q.support, ((MvPolynomial.monomial (collapseMon α)
            (Polynomial.monomial (α 0) (Q.coeff α))).coeff (collapseMon α₀)).coeff (α₀ 0) := by
        simpa only [Polynomial.lcoeff_apply] using map_sum (Polynomial.lcoeff ℂ (α₀ 0)) _ Q.support
      rw [hpoly_sum, Finset.sum_eq_single α₀]
      · simp [MvPolynomial.coeff_monomial, Polynomial.coeff_monomial]
      · intro α hα hne
        rw [MvPolynomial.coeff_monomial]
        by_cases hcm : collapseMon α = collapseMon α₀
        · simp only [hcm, ↓reduceIte, Polynomial.coeff_monomial]
          by_cases h0 : α 0 = α₀ 0
          · exfalso; apply hne
            ext i
            cases i with
            | zero => exact h0
            | succ j =>
              by_cases hj : j < r + 1
              · have hc := congrArg (fun f : Fin (r + 1) →₀ ℕ => f ⟨j, hj⟩) hcm
                simpa [collapseMon] using hc
              · have h1 : α (j + 1) = 0 := by
                  by_contra hnz
                  have := hbound α hα (j + 1) (Finsupp.mem_support_iff.mpr hnz)
                  omega
                have h2 : α₀ (j + 1) = 0 := by
                  by_contra hnz
                  have := hbound α₀ hα₀ (j + 1) (Finsupp.mem_support_iff.mpr hnz)
                  omega
                rw [h1, h2]
          · simp [h0]
        · simp [hcm]
      · intro hnot; exact absurd hα₀ hnot
    rw [hP_coeff] at hcoeff0
    exact (MvPolynomial.mem_support_iff.mp hα₀) hcoeff0
  · intro hind r P hP
    let liftMon : ℕ → (Fin (r + 1) →₀ ℕ) → (ℕ →₀ ℕ) := fun k α =>
      Finsupp.single 0 k + ∑ j : Fin (r + 1), Finsupp.single (j.val + 1) (α j)
    have hsum_apply : ∀ (α : Fin (r + 1) →₀ ℕ) (s : Finset (Fin (r + 1))) (x : ℕ),
        (∑ j ∈ s, Finsupp.single (j.val + 1) (α j)) x = ∑ j ∈ s, (Finsupp.single (j.val + 1) (α j)) x := by
      intro α s x
      induction s using Finset.induction_on with
      | empty => simp
      | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Finsupp.add_apply, ih]
    have hlift_eval0 : ∀ k α, liftMon k α 0 = k := fun k α => by
      dsimp only [liftMon]
      rw [Finsupp.add_apply, Finsupp.single_eq_same, hsum_apply]
      have hzero : ∑ j : Fin (r + 1), (Finsupp.single (j.val + 1) (α j)) 0 = 0 :=
        Finset.sum_eq_zero fun j _ => Finsupp.single_eq_of_ne (show (0 : ℕ) ≠ j.val + 1 by omega)
      rw [hzero, add_zero]
    have hlift_eval_succ : ∀ k α (j : Fin (r + 1)), liftMon k α (j.val + 1) = α j := fun k α j => by
      dsimp only [liftMon]
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (show (0 : ℕ) ≠ j.val + 1 by omega), zero_add,
        hsum_apply, Finset.sum_eq_single j]
      · exact Finsupp.single_eq_same
      · intro i _ hij
        refine Finsupp.single_eq_of_ne ?_
        intro heq; exact hij (Fin.ext (by omega))
      · intro hnot; exact absurd (Finset.mem_univ j) hnot
    have hlift_inj : ∀ k₁ k₂ α₁ α₂, liftMon k₁ α₁ = liftMon k₂ α₂ → k₁ = k₂ ∧ α₁ = α₂ := by
      intro k₁ k₂ α₁ α₂ heq
      constructor
      · have h0 := congrArg (fun f : ℕ →₀ ℕ => f 0) heq
        simpa only [hlift_eval0] using h0
      · ext j
        have hj := congrArg (fun f : ℕ →₀ ℕ => f (j.val + 1)) heq
        simpa only [hlift_eval_succ] using hj
    let Q : MvPolynomial ℕ ℂ :=
      ∑ α ∈ P.support, ∑ k ∈ (P.coeff α).support, MvPolynomial.monomial (liftMon k α) ((P.coeff α).coeff k)
    have hQ_eval : MvPolynomial.aeval (seriesCoordinates F) Q = 0 := by
      dsimp only [Q]
      rw [map_sum]
      have houter : ∀ α ∈ P.support,
          MvPolynomial.aeval (seriesCoordinates F)
            (∑ k ∈ (P.coeff α).support, MvPolynomial.monomial (liftMon k α) ((P.coeff α).coeff k)) =
          Polynomial.coeToPowerSeries.ringHom (P.coeff α) *
            ∏ j : Fin (r + 1), seriesJet F j.val ^ (α j) := by
        intro α _
        rw [map_sum]
        have hinner : ∀ k ∈ (P.coeff α).support,
            MvPolynomial.aeval (seriesCoordinates F) (MvPolynomial.monomial (liftMon k α) ((P.coeff α).coeff k)) =
            (PowerSeries.C ((P.coeff α).coeff k) * PowerSeries.X ^ k) *
              ∏ j : Fin (r + 1), seriesJet F j.val ^ (α j) := by
          intro k _
          rw [MvPolynomial.aeval_monomial]
          have hprod_lift : (liftMon k α).prod (fun i e => seriesCoordinates F i ^ e) =
              PowerSeries.X ^ k * ∏ j : Fin (r + 1), seriesJet F j.val ^ (α j) := by
            dsimp only [liftMon]
            rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
              Finsupp.prod_single_index (by simp)]
            congr 1
            have hgen : ∀ s : Finset (Fin (r + 1)),
                (∑ j ∈ s, Finsupp.single (j.val + 1) (α j)).prod (fun i e => seriesCoordinates F i ^ e) =
                ∏ j ∈ s, seriesJet F j.val ^ (α j) := by
              intro s
              induction s using Finset.induction_on with
              | empty => simp
              | insert j s hj ihs =>
                rw [Finset.sum_insert hj, Finset.prod_insert hj,
                  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
                  Finsupp.prod_single_index (by simp), ihs]
                rfl
            exact hgen Finset.univ
          rw [hprod_lift, ← mul_assoc]
          rfl
        rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul]
        congr 1
        have hpoly_eq : Polynomial.coeToPowerSeries.ringHom (P.coeff α) =
            ∑ k ∈ (P.coeff α).support, PowerSeries.C ((P.coeff α).coeff k) * PowerSeries.X ^ k := by
          conv_lhs => rw [(P.coeff α).as_sum_support_C_mul_X_pow]
          rw [map_sum]
          refine Finset.sum_congr rfl fun k _ => by
            rw [map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
              Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]
        exact hpoly_eq.symm
      rw [Finset.sum_congr rfl houter]
      have hP_eq : ∑ α ∈ P.support, Polynomial.coeToPowerSeries.ringHom (P.coeff α) *
            ∏ j : Fin (r + 1), seriesJet F j.val ^ (α j) =
          MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom (fun j : Fin (r + 1) => seriesJet F j.val) P := by
        rw [MvPolynomial.eval₂_eq']
      rw [hP_eq]; exact hP
    have hQ0 : Q = 0 := hind Q hQ_eval
    apply MvPolynomial.ext; intro α₀
    ext k₀
    have hc0 : Q.coeff (liftMon k₀ α₀) = 0 := by rw [hQ0]; simp
    have hQ_coeff : Q.coeff (liftMon k₀ α₀) = (P.coeff α₀).coeff k₀ := by
      dsimp only [Q]
      rw [MvPolynomial.coeff_sum]
      simp_rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
      by_cases hα₀ : α₀ ∈ P.support
      · rw [Finset.sum_eq_single α₀]
        · by_cases hk₀ : k₀ ∈ (P.coeff α₀).support
          · rw [Finset.sum_eq_single k₀]
            · simp
            · intro k _ hk_ne
              have hne : liftMon k α₀ ≠ liftMon k₀ α₀ := fun h => hk_ne (hlift_inj k k₀ α₀ α₀ h).1
              simp [hne]
            · intro hnot; exact absurd hk₀ hnot
          · rw [Polynomial.notMem_support_iff.mp hk₀]
            refine Finset.sum_eq_zero fun k hk => ?_
            have hne : liftMon k α₀ ≠ liftMon k₀ α₀ := fun h =>
              hk₀ ((hlift_inj k k₀ α₀ α₀ h).1 ▸ hk)
            simp [hne]
        · intro α _ hα_ne
          refine Finset.sum_eq_zero fun k _ => ?_
          have hne : liftMon k α ≠ liftMon k₀ α₀ := fun h => hα_ne (hlift_inj k k₀ α α₀ h).2
          simp [hne]
        · intro hnot; exact absurd hα₀ hnot
      · rw [MvPolynomial.notMem_support_iff.mp hα₀, Polynomial.coeff_zero]
        refine Finset.sum_eq_zero fun α hα => Finset.sum_eq_zero fun k _ => ?_
        have hne : liftMon k α ≠ liftMon k₀ α₀ := fun h => hα₀ ((hlift_inj k k₀ α α₀ h).2 ▸ hα)
        simp [hne]
    rw [hQ_coeff] at hc0
    simpa using hc0

/-- Helper: Cauchy-product summability for nonnegative summable real sequences. -/
private lemma summable_antidiagonal_mul_nonneg {a b : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n)
    (ha : Summable a) (hb : Summable b) :
    Summable (fun n : ℕ => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2) := by
  refine summable_of_sum_le (c := (∑' k, a k) * (∑' l, b l))
    (fun n => Finset.sum_nonneg fun kl _ => mul_nonneg (ha0 kl.1) (hb0 kl.2)) fun s => ?_
  let M : ℕ := s.sup id
  have hs_sub : s ⊆ Finset.range (M + 1) := fun n hn =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))
  have h1 : ∑ n ∈ s, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2 ≤
      ∑ n ∈ Finset.range (M + 1), ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hs_sub fun n _ _ =>
      Finset.sum_nonneg fun kl _ => mul_nonneg (ha0 kl.1) (hb0 kl.2)
  have h2 : ∑ n ∈ Finset.range (M + 1), ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2 ≤
      ∑ p ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1), a p.1 * b p.2 := by
    have hsig : ∑ n ∈ Finset.range (M + 1), ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2 =
        ∑ x ∈ (Finset.range (M + 1)).sigma Finset.HasAntidiagonal.antidiagonal, a x.2.1 * b x.2.2 :=
      Finset.sum_sigma' (Finset.range (M + 1)) Finset.HasAntidiagonal.antidiagonal
        fun _ kl => a kl.1 * b kl.2
    let f : (n : ℕ) × (ℕ × ℕ) → ℕ × ℕ := fun x => x.2
    have hinj : Set.InjOn f ((Finset.range (M + 1)).sigma Finset.HasAntidiagonal.antidiagonal) := by
      intro x hx y hy hxy
      have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_sigma.mp hx).2
      have hy' := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_sigma.mp hy).2
      have h1st : x.1 = y.1 := by rw [← hx', ← hy']; exact congrArg (fun p : ℕ × ℕ => p.1 + p.2) hxy
      exact Sigma.ext h1st (heq_of_eq hxy)
    let T : Finset (ℕ × ℕ) := ((Finset.range (M + 1)).sigma Finset.HasAntidiagonal.antidiagonal).image f
    have himg : ∑ x ∈ (Finset.range (M + 1)).sigma Finset.HasAntidiagonal.antidiagonal, a x.2.1 * b x.2.2 =
        ∑ p ∈ T, a p.1 * b p.2 :=
      (Finset.sum_image (f := fun p : ℕ × ℕ => a p.1 * b p.2) (g := f) hinj).symm
    have hsub : T ⊆ Finset.range (M + 1) ×ˢ Finset.range (M + 1) := by
      intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨x, hx, rfl⟩ := hp
      have hxn : x.1 < M + 1 := Finset.mem_range.mp (Finset.mem_sigma.mp hx).1
      have hadd : x.2.1 + x.2.2 = x.1 := Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_sigma.mp hx).2
      dsimp only [f]
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
    rw [hsig, himg]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => mul_nonneg (ha0 p.1) (hb0 p.2)
  have h3 : ∑ p ∈ Finset.range (M + 1) ×ˢ Finset.range (M + 1), a p.1 * b p.2 =
      (∑ k ∈ Finset.range (M + 1), a k) * (∑ l ∈ Finset.range (M + 1), b l) := by
    rw [Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only
    exact (Finset.mul_sum _ _ _).symm
  have h4 : (∑ k ∈ Finset.range (M + 1), a k) * (∑ l ∈ Finset.range (M + 1), b l) ≤
      (∑' k, a k) * (∑' l, b l) :=
    mul_le_mul (ha.sum_le_tsum _ fun k _ => ha0 k) (hb.sum_le_tsum _ fun l _ => hb0 l)
      (Finset.sum_nonneg fun l _ => hb0 l) (tsum_nonneg ha0)
  exact le_trans h1 (le_trans h2 (h3.le.trans h4))

/-- Subalgebra of entire formal power series `S ∈ ℂ⟦t⟧` (convergent everywhere on `ℂ`). -/
private def EntirePS : Subalgebra ℂ (PowerSeries ℂ) where
  carrier := {S | ∀ z : ℂ, Summable (fun n : ℕ => ‖PowerSeries.coeff n S * z ^ n‖)}
  mul_mem' {f g} hf hg z := by
    have hsum_anti := summable_antidiagonal_mul_nonneg
      (fun n => norm_nonneg _) (fun n => norm_nonneg _) (hf z) (hg z)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hsum_anti
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    calc ‖∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff kl.1 f * PowerSeries.coeff kl.2 g * z ^ n‖
        ≤ ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, ‖PowerSeries.coeff kl.1 f * PowerSeries.coeff kl.2 g * z ^ n‖ :=
          norm_sum_le _ _
      _ = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, ‖PowerSeries.coeff kl.1 f * z ^ kl.1‖ * ‖PowerSeries.coeff kl.2 g * z ^ kl.2‖ := by
          refine Finset.sum_congr rfl fun kl hkl => ?_
          have hadd : kl.1 + kl.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
          rw [← hadd, pow_add, ← norm_mul]; congr 1; ring
  one_mem' z := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    have hne : n ≠ 0 := by simpa using hn
    simp [PowerSeries.coeff_one, hne]
  add_mem' {f g} hf hg z := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) ((hf z).add (hg z))
    rw [map_add, add_mul]; exact norm_add_le _ _
  zero_mem' z := by simp [summable_zero]
  algebraMap_mem' c z := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    have hne : n ≠ 0 := by simpa using hn
    simp [PowerSeries.algebraMap_eq, PowerSeries.coeff_C, hne]

/-- Pointwise evaluation ring homomorphism `evalPS z : EntirePS →+* ℂ`. -/
private def evalPS (z : ℂ) : EntirePS →+* ℂ where
  toFun S := ∑' n : ℕ, PowerSeries.coeff n S.1 * z ^ n
  map_one' := by
    rw [tsum_eq_single 0]
    · simp [PowerSeries.coeff_one]
    · intro n hn; simp [PowerSeries.coeff_one, hn]
  map_mul' f g := by
    have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (f.2 z) (g.2 z)
    rw [hprod]
    refine tsum_congr fun n => ?_
    change PowerSeries.coeff n (f.1 * g.1) * z ^ n = _
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    have hadd : kl.1 + kl.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
    rw [← hadd, pow_add]; ring
  map_zero' := by simp
  map_add' f g := by
    have hadd := (Summable.of_norm (f.2 z)).tsum_add (Summable.of_norm (g.2 z))
    rw [← hadd]
    refine tsum_congr fun n => ?_
    change PowerSeries.coeff n (f.1 + g.1) * z ^ n = _
    rw [map_add, add_mul]

/-- Lift `Polynomial ℂ →+* EntirePS` compatible with `Polynomial.coeToPowerSeries.ringHom`. -/
private def polyToEntirePS : Polynomial ℂ →+* EntirePS where
  toFun p := ⟨Polynomial.coeToPowerSeries.ringHom p, fun z => by
    refine summable_of_ne_finset_zero (s := Finset.range (p.natDegree + 1)) fun n hn => ?_
    have hgt : p.natDegree < n := by
      rw [Finset.mem_range, not_lt] at hn; omega
    rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe,
      Polynomial.coeff_eq_zero_of_natDegree_lt hgt, zero_mul, norm_zero]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' p q := Subtype.ext (map_mul _ p q)
  map_zero' := Subtype.ext (map_zero _)
  map_add' p q := Subtype.ext (map_add _ p q)

private lemma evalPS_polyToEntirePS (z : ℂ) (p : Polynomial ℂ) :
    evalPS z (polyToEntirePS p) = p.eval z := by
  change ∑' n : ℕ, PowerSeries.coeff n (Polynomial.coeToPowerSeries.ringHom p) * z ^ n = p.eval z
  rw [tsum_eq_sum (s := Finset.range (p.natDegree + 1)) (fun n hn => by
    have hgt : p.natDegree < n := by rw [Finset.mem_range, not_lt] at hn; omega
    rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe,
      Polynomial.coeff_eq_zero_of_natDegree_lt hgt, zero_mul])]
  rw [Polynomial.eval_eq_sum_range]
  refine Finset.sum_congr rfl fun n _ => by
    rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe]

/-- Exact Taylor coefficients of `seriesJet` for any formal EGF `∑ a_n t^n / n!`. -/
private lemma coeff_seriesJet_egf (a : ℕ → ℂ) (j n : ℕ) :
    PowerSeries.coeff n (seriesJet (PowerSeries.mk fun m => a m / (m.factorial : ℂ)) j) =
      a (n + j) / (n.factorial : ℂ) := by
  induction j generalizing n with
  | zero => simp [seriesJet]
  | succ j ih =>
    rw [seriesJet, Function.iterate_succ_apply', ← seriesJet, PowerSeries.coeff_derivative, ih (n + 1)]
    rw [show n + 1 + j = n + (j + 1) by omega, Nat.factorial_succ, Nat.cast_mul]
    have hn1 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have hnf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    field_simp [hn1, hnf]
    push_cast; ring

private lemma seriesJet_egf_mem_entirePS {a : ℕ → ℂ} {R : ℝ}
    (ha : ∀ n, ‖a n‖ ≤ R ^ n) (j : ℕ) :
    seriesJet (PowerSeries.mk fun m => a m / (m.factorial : ℂ)) j ∈ EntirePS := fun z => by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((Real.summable_pow_div_factorial (R * ‖z‖)).mul_left (R ^ j))
  rw [coeff_seriesJet_egf, norm_mul, norm_div, norm_pow, Complex.norm_natCast, mul_pow]
  have hle := ha (n + j)
  rw [pow_add] at hle
  calc ‖a (n + j)‖ / (n.factorial : ℝ) * ‖z‖ ^ n
      ≤ R ^ n * R ^ j / (n.factorial : ℝ) * ‖z‖ ^ n := by gcongr
    _ = R ^ j * (R ^ n * ‖z‖ ^ n / (n.factorial : ℝ)) := by ring

/-- **Unconditional Formal Power Series Differential Transcendence of `frPoissonSeries b` (`b ≥ 2`)**:
For EVERY integer `b ≥ 2`, the formal Poisson generating series `frPoissonSeries b ∈ ℂ⟦t⟧` is
differentially transcendental over `ℂ(t)` (`RatFunc ℂ`). -/
theorem frPoissonSeries_dTrans_over_ratFunc (b : ℕ) (hb : 2 ≤ b) :
    DTransOverRatFunc (frPoissonSeries b) := by
  have hb1 : 1 ≤ b := by omega
  rw [dTransOverRatFunc_iff_no_poly_ade]
  intro r P hP
  have hmem : ∀ j : Fin (r + 1), seriesJet (frPoissonSeries b) j.val ∈ EntirePS := fun j =>
    seriesJet_egf_mem_entirePS (norm_frPoissonCoeff_le hb1) j.val
  let jetE : Fin (r + 1) → EntirePS := fun j => ⟨seriesJet (frPoissonSeries b) j.val, hmem j⟩
  have hP_ent : MvPolynomial.eval₂ polyToEntirePS jetE P = 0 := by
    apply Subtype.ext
    change EntirePS.val.toRingHom (MvPolynomial.eval₂ polyToEntirePS jetE P) = 0
    rw [MvPolynomial.hom_eval₂]
    exact hP
  refine frPoisson_no_ade b hb P fun x hx => ?_
  have hval := congrArg (evalPS (x : ℂ)) hP_ent
  rw [map_zero, MvPolynomial.hom_eval₂] at hval
  have hcomp : (evalPS (x : ℂ)).comp polyToEntirePS = Polynomial.evalRingHom (x : ℂ) :=
    RingHom.ext fun p => evalPS_polyToEntirePS (x : ℂ) p
  have hjet : (fun j : Fin (r + 1) => evalPS (x : ℂ) (jetE j)) =
      fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => frPoisson b (t : ℂ)) x := by
    funext j
    rw [iteratedDeriv_comp_ofReal_eq_of_differentiable (frPoisson_differentiable hb1) j.val x,
      iteratedDeriv_frPoisson hb1 j.val (x : ℂ)]
    change ∑' n : ℕ, PowerSeries.coeff n (seriesJet (frPoissonSeries b) j.val) * (x : ℂ) ^ n = _
    refine tsum_congr fun n => ?_
    rw [frPoissonSeries, coeff_seriesJet_egf]; ring
  rw [hcomp, hjet, ← MvPolynomial.eval_map] at hval
  exact hval

/-- **Algebraic Independence of Derivative Coordinates of `frPoissonSeries b` (`b ≥ 2`)**. -/
theorem frPoissonSeries_algebraicIndependent (b : ℕ) (hb : 2 ≤ b) :
    AlgebraicIndependent ℂ (seriesCoordinates (frPoissonSeries b)) :=
  (dTransOverRatFunc_iff_algebraicIndependent (frPoissonSeries b)).mp
    (frPoissonSeries_dTrans_over_ratFunc b hb)

/-- **Unconditional Resolution of Bostan–Di Vizio–Raschel (AJM 2024, §2.2.6, Example #3)**:
For EVERY integer `b ≥ 2`, the Flajolet–Richmond generalized digital tree exponential generating
series `frEGFSeries b ∈ ℂ⟦t⟧` is **differentially transcendental over `ℂ(t)`** (`RatFunc ℂ`). -/
theorem frEGFSeries_dTrans_over_ratFunc (b : ℕ) (hb : 2 ≤ b) :
    DTransOverRatFunc (frEGFSeries b) := by
  have hb1 : 1 ≤ b := by omega
  rw [dTransOverRatFunc_iff_no_poly_ade]
  intro r P hP
  have hmem : ∀ j : Fin (r + 1), seriesJet (frEGFSeries b) j.val ∈ EntirePS := fun j =>
    seriesJet_egf_mem_entirePS (norm_frCoeff_le hb1) j.val
  let jetE : Fin (r + 1) → EntirePS := fun j => ⟨seriesJet (frEGFSeries b) j.val, hmem j⟩
  have hP_ent : MvPolynomial.eval₂ polyToEntirePS jetE P = 0 := by
    apply Subtype.ext
    change EntirePS.val.toRingHom (MvPolynomial.eval₂ polyToEntirePS jetE P) = 0
    rw [MvPolynomial.hom_eval₂]
    exact hP
  refine frEGF_no_ade b hb P fun x hx => ?_
  have hval := congrArg (evalPS (x : ℂ)) hP_ent
  rw [map_zero, MvPolynomial.hom_eval₂] at hval
  have hcomp : (evalPS (x : ℂ)).comp polyToEntirePS = Polynomial.evalRingHom (x : ℂ) :=
    RingHom.ext fun p => evalPS_polyToEntirePS (x : ℂ) p
  have hjet : (fun j : Fin (r + 1) => evalPS (x : ℂ) (jetE j)) =
      fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => frEGF b (t : ℂ)) x := by
    funext j
    rw [iteratedDeriv_comp_ofReal_eq_of_differentiable (frEGF_differentiable hb1) j.val x,
      iteratedDeriv_frEGF hb1 j.val (x : ℂ)]
    change ∑' n : ℕ, PowerSeries.coeff n (seriesJet (frEGFSeries b) j.val) * (x : ℂ) ^ n = _
    refine tsum_congr fun n => ?_
    rw [frEGFSeries, coeff_seriesJet_egf]; ring
  rw [hcomp, hjet, ← MvPolynomial.eval_map] at hval
  exact hval

/-- **Algebraic Independence of Derivative Coordinates of `frEGFSeries b` (`b ≥ 2`)**. -/
theorem frEGFSeries_algebraicIndependent (b : ℕ) (hb : 2 ≤ b) :
    AlgebraicIndependent ℂ (seriesCoordinates (frEGFSeries b)) :=
  (dTransOverRatFunc_iff_algebraicIndependent (frEGFSeries b)).mp
    (frEGFSeries_dTrans_over_ratFunc b hb)

/-- **Exact `b = 1` Counterexample to Unqualified BDR p. 12**:
At `b = 1`, `frEGFSeries 1` is NOT differentially transcendental over `ℂ(t)` (since `f_1(t) = t e^t`). -/
theorem frEGF_one_not_dTrans : ¬ DTransOverRatFunc (frEGFSeries 1) := by
  rw [dTransOverRatFunc_iff_algebraicIndependent]
  exact frEGF_one_isDAlgebraic

end Section6

end
end PakPrimes.FlajoletRichmondDTrans
end
