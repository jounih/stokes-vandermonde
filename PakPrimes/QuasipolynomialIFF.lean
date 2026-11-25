module

public import PakPrimes.QuasipolynomialEulerParity
public import PakPrimes.ThermalGasEOS
public import PakPrimes.FalseThetaDichotomy
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-! # Complete `IFF` Parity Converse & Nesterenko-Style Joint Differential Independence

This module completes the **Quasipolynomial Euler-Product Parity Theorem** with two major results
in Lean 4 (fully proved, strictly `[propext, Classical.choice, Quot.sound]`):

1. **Complete `IFF` Converse (Even-Parity D-Algebraicity via Ramanujan's Quasi-Modular Ring):**
   - Formalizes Ramanujan's 3-variable ODE system for `(E₂, E₄, E₆)` directly in `PowerSeries ℂ`:
     `12 θ E₂ = E₂² - E₄`, `3 θ E₄ = E₂ E₄ - E₆`, `2 θ E₆ = E₂ E₆ - E₄²`,
     and its `PowerSeries.expand m` scaling for every `m ≥ 1`.
   - Combines Mathlib's `ModularForm.evalE₄E₆_surjective` (`M_*(SL₂(ℤ)) = ℂ[E₄, E₆]`) with
     `EisensteinSeries.E_qExpansion_coeff` to prove that EVERY odd-index divisor sum
     `L_{2k+1}(q) = ∑ σ_{2k+1}(n) q^n` lies in `ℂ[E₂, E₄, E₆]`.
   - Proves via finite transcendence degree in `FractionRing (PowerSeries ℂ)` that every finite
     `ℂ`-linear combination of `expand m (sigmaSeries (2k+1))` and its Euler product are
     unconditionally **D-algebraic** (`¬ AlgebraicIndependent ℂ (seriesCoordinates ...)`).
   - Establishes the **100% unconditional `IFF` Parity Theorem** for all `M = 1` (polynomial) and
     `M = 2` (parity-periodic) quasipolynomials, plus concrete D-algebraic controls for ordinary
     partitions `∏ (1 - q^n)^{-1}`, odd-parts partitions `∏_{2 ∤ n} (1 - q^n)^{-1}`,
     non-5-divisible partitions `∏_{5 ∤ n} (1 - q^n)^{-1}`, the centered 3D harmonic trap,
     the `S³` conformal scalar, and the Ehrhart quotient.

2. **Nesterenko-Style Joint Differential Independence over `ℂ(q)`:**
   - Pure-algebra `K`-tuple Kolchin–Ostrowski log-derivative transfer (`joint_algIndep_of_log_deriv`)
     and `q`-elimination (`joint_autonomous_theta_of_dep`).
   - Shared-lattice multi-function simple-pole Stokes–Vandermonde engine (`SharedLatticeSimplePoleFamily`).
   - Unconditional **3-tuple joint differential independence over `ℂ(q)`** of:
     1. MacMahon plane partitions `M(q) = ∏_{n ≥ 1} (1 - q^n)^{-n}`,
     2. Parts `≡ 1 mod 5` `∏_{n ≡ 1 (5)} (1 - q^n)^{-1}`,
     3. Parts `≡ 2 mod 5` `∏_{n ≡ 2 (5)} (1 - q^n)^{-1}`,
     for BOTH their Lambert logarithmic derivatives and their literal infinite Euler products!
-/

set_option maxHeartbeats 1600000

public section
namespace PakPrimes.QuasipolynomialIFF

open Complex Real Filter MeasureTheory Set MvPolynomial UpperHalfPlane
open EisensteinSeries ModularForm Derivative
open PakPrimes.BorelStokesVandermonde PakPrimes.GeneralTheorem2 PakPrimes.HigherOrderStokes
  PakPrimes.PrimeNome PakPrimes.DivisorAndMacMahon PakPrimes.QuasipolynomialEulerParity
  PakPrimes.ThermalGasEOS PakPrimes.FalseThetaDichotomy
open scoped Topology Interval BigOperators MatrixGroups DirectSum Manifold

noncomputable section

/-! ### Part 1: Formal Ramanujan ODE System, Quasi-Modular Ring, and Complete `IFF` Converse -/

/-- Formal `q`-series of the weight-2 quasi-modular Eisenstein series `E₂ = 1 - 24 ∑ σ₁(n) q^n`. -/
@[expose] def E2Series : PowerSeries ℂ :=
  1 - PowerSeries.C (24 : ℂ) * sigmaSeries 1

/-- Formal `q`-series of the weight-6 Eisenstein series `E₆ = 1 - 504 ∑ σ₅(n) q^n`. -/
@[expose] def E6Series : PowerSeries ℂ :=
  1 - PowerSeries.C (504 : ℂ) * sigmaSeries 5

/-- Pure arithmetic computation `bernoulli 4 = -1 / 30` (matching `ThermalGasEOS`). -/
private lemma bernoulli_four_eq' : bernoulli 4 = -(1 / 30 : ℚ) := by
  have h5 := sum_bernoulli 5
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at h5
  have hb0 : bernoulli 0 = 1 := bernoulli_zero
  have hb1 : bernoulli 1 = -(1 / 2 : ℚ) := by rw [bernoulli_one]; norm_num
  have hb2 : bernoulli 2 = 1 / 6 := by rw [bernoulli_two]; norm_num
  have hb3 : bernoulli 3 = 0 := bernoulli_eq_zero_of_odd ⟨1, rfl⟩ (by omega)
  rw [hb0, hb1, hb2, hb3] at h5
  norm_num [Nat.choose] at h5
  linarith

/-- Pure arithmetic computation `bernoulli 6 = 1 / 42`. -/
private lemma bernoulli_six_eq' : bernoulli 6 = (1 / 42 : ℚ) := by
  have h7 := sum_bernoulli 7
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at h7
  have hb0 : bernoulli 0 = 1 := bernoulli_zero
  have hb1 : bernoulli 1 = -(1 / 2 : ℚ) := by rw [bernoulli_one]; norm_num
  have hb2 : bernoulli 2 = 1 / 6 := by rw [bernoulli_two]; norm_num
  have hb3 : bernoulli 3 = 0 := bernoulli_eq_zero_of_odd ⟨1, rfl⟩ (by omega)
  have hb4 : bernoulli 4 = -(1 / 30 : ℚ) := bernoulli_four_eq'
  have hb5 : bernoulli 5 = 0 := bernoulli_eq_zero_of_odd ⟨2, rfl⟩ (by omega)
  rw [hb0, hb1, hb2, hb3, hb4, hb5] at h7
  norm_num [Nat.choose] at h7
  linarith

/-- Formal Euler operator `θ S = X * derivative S` on `PowerSeries ℂ`. -/
@[expose] def thetaD : Derivation ℂ (PowerSeries ℂ) (PowerSeries ℂ) where
  toFun S := PowerSeries.X * PowerSeries.derivative S
  map_add' A B := by simp [mul_add]
  map_smul' c A := by simp [Algebra.mul_smul_comm]
  map_one_eq_zero' := by simp
  leibniz' A B := by simp [Derivation.leibniz, smul_eq_mul]; ring

lemma thetaD_apply (S : PowerSeries ℂ) :
    thetaD S = PowerSeries.X * PowerSeries.derivative S := rfl

lemma coeff_thetaD (S : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (thetaD S) = (n : ℂ) * PowerSeries.coeff n S := by
  cases n with
  | zero =>
    rw [thetaD_apply, PowerSeries.coeff_zero_X_mul]; simp
  | succ m =>
    rw [thetaD_apply, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    push_cast; ring

lemma thetaD_expand {k : ℕ} (hk : 0 < k) (S : PowerSeries ℂ) :
    thetaD (PowerSeries.expand k hk.ne' S) =
      PowerSeries.C (k : ℂ) * PowerSeries.expand k hk.ne' (thetaD S) := by
  ext n
  rw [coeff_thetaD, PowerSeries.coeff_C_mul, PowerSeries.coeff_expand, PowerSeries.coeff_expand]
  split_ifs with hd
  · rw [coeff_thetaD]
    obtain ⟨m, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left m hk]
    push_cast; ring
  · simp

private lemma polyBound_const' (c : ℂ) : PolyCoeffBound (PowerSeries.C c) := by
  refine ⟨‖c‖, 0, norm_nonneg c, fun n => ?_⟩
  cases n with
  | zero => simp
  | succ m => simp

private lemma polyBound_add' {F G : PowerSeries ℂ} (hF : PolyCoeffBound F) (hG : PolyCoeffBound G) :
    PolyCoeffBound (F + G) := by
  obtain ⟨CF, dF, hCF, hFbd⟩ := hF
  obtain ⟨CG, dG, hCG, hGbd⟩ := hG
  refine ⟨CF + CG, max dF dG, by linarith, fun n => ?_⟩
  rw [map_add]
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hpF : ((n : ℝ) + 1) ^ dF ≤ ((n : ℝ) + 1) ^ max dF dG := pow_le_pow_right₀ h1 (le_max_left _ _)
  have hpG : ((n : ℝ) + 1) ^ dG ≤ ((n : ℝ) + 1) ^ max dF dG := pow_le_pow_right₀ h1 (le_max_right _ _)
  calc ‖PowerSeries.coeff n F + PowerSeries.coeff n G‖
      ≤ ‖PowerSeries.coeff n F‖ + ‖PowerSeries.coeff n G‖ := norm_add_le _ _
    _ ≤ CF * ((n : ℝ) + 1) ^ dF + CG * ((n : ℝ) + 1) ^ dG := add_le_add (hFbd n) (hGbd n)
    _ ≤ CF * ((n : ℝ) + 1) ^ max dF dG + CG * ((n : ℝ) + 1) ^ max dF dG :=
        add_le_add (mul_le_mul_of_nonneg_left hpF hCF) (mul_le_mul_of_nonneg_left hpG hCG)
    _ = (CF + CG) * ((n : ℝ) + 1) ^ max dF dG := by ring

private lemma polyBound_const_mul' (c : ℂ) {F : PowerSeries ℂ} (hF : PolyCoeffBound F) :
    PolyCoeffBound (PowerSeries.C c * F) := by
  obtain ⟨C, d, hC, hbd⟩ := hF
  refine ⟨‖c‖ * C, d, by positivity, fun n => ?_⟩
  rw [PowerSeries.coeff_C_mul, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hbd n) (norm_nonneg c)

private lemma polyBound_sub' {F G : PowerSeries ℂ} (hF : PolyCoeffBound F) (hG : PolyCoeffBound G) :
    PolyCoeffBound (F - G) := by
  rw [sub_eq_add_neg, show -G = PowerSeries.C (-1 : ℂ) * G by simp]
  exact polyBound_add' hF (polyBound_const_mul' (-1) hG)

private lemma polyBound_mul' {F G : PowerSeries ℂ} (hF : PolyCoeffBound F) (hG : PolyCoeffBound G) :
    PolyCoeffBound (F * G) := by
  obtain ⟨CF, dF, hCF, hFbd⟩ := hF
  obtain ⟨CG, dG, hCG, hGbd⟩ := hG
  refine ⟨CF * CG, dF + dG + 1, by positivity, fun n => ?_⟩
  rw [PowerSeries.coeff_mul]
  have h1 : ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal n,
      ‖PowerSeries.coeff ab.1 F * PowerSeries.coeff ab.2 G‖ ≤
        CF * CG * ((n : ℝ) + 1) ^ (dF + dG) := by
    intro ab hab
    have hab' : ab.1 + ab.2 = n := by simpa using hab
    have ha : ((ab.1 : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (by omega : ab.1 ≤ n)
    have hb : ((ab.2 : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (by omega : ab.2 ≤ n)
    rw [norm_mul]
    calc ‖PowerSeries.coeff ab.1 F‖ * ‖PowerSeries.coeff ab.2 G‖
        ≤ (CF * ((ab.1 : ℝ) + 1) ^ dF) * (CG * ((ab.2 : ℝ) + 1) ^ dG) :=
          mul_le_mul (hFbd ab.1) (hGbd ab.2) (norm_nonneg _) (by positivity)
      _ ≤ (CF * ((n : ℝ) + 1) ^ dF) * (CG * ((n : ℝ) + 1) ^ dG) := by
          gcongr
      _ = CF * CG * ((n : ℝ) + 1) ^ (dF + dG) := by rw [pow_add]; ring
  calc ‖∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff ab.1 F * PowerSeries.coeff ab.2 G‖
      ≤ ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, ‖PowerSeries.coeff ab.1 F * PowerSeries.coeff ab.2 G‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _ab ∈ Finset.HasAntidiagonal.antidiagonal n, (CF * CG * ((n : ℝ) + 1) ^ (dF + dG)) :=
        Finset.sum_le_sum h1
    _ = ((Finset.HasAntidiagonal.antidiagonal n).card : ℝ) * (CF * CG * ((n : ℝ) + 1) ^ (dF + dG)) := by simp
    _ = ((n : ℝ) + 1) * (CF * CG * ((n : ℝ) + 1) ^ (dF + dG)) := by
        rw [Finset.Nat.card_antidiagonal]; push_cast; rfl
    _ = CF * CG * ((n : ℝ) + 1) ^ (dF + dG + 1) := by rw [pow_succ]; ring

private lemma polyBound_thetaD {S : PowerSeries ℂ} (hS : PolyCoeffBound S) :
    PolyCoeffBound (thetaD S) := by
  obtain ⟨C, d, hC, hbd⟩ := hS
  refine ⟨C, d + 1, hC, fun n => ?_⟩
  rw [coeff_thetaD, norm_mul, Complex.norm_natCast]
  have hn : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  calc (n : ℝ) * ‖PowerSeries.coeff n S‖
      ≤ ((n : ℝ) + 1) * (C * ((n : ℝ) + 1) ^ d) :=
        mul_le_mul hn (hbd n) (norm_nonneg _) (by positivity)
    _ = C * ((n : ℝ) + 1) ^ (d + 1) := by rw [pow_succ]; ring

private lemma E2Series_polyBound : PolyCoeffBound E2Series :=
  polyBound_sub' (by simpa using polyBound_const' (1 : ℂ))
    (polyBound_const_mul' 24 (sigmaSeries_polyBound 1))

private lemma E4Series_polyBound' : PolyCoeffBound E4Series :=
  polyBound_add' (by simpa using polyBound_const' (1 : ℂ))
    (polyBound_const_mul' 240 (sigmaSeries_polyBound 3))

private lemma E6Series_polyBound : PolyCoeffBound E6Series :=
  polyBound_sub' (by simpa using polyBound_const' (1 : ℂ))
    (polyBound_const_mul' 504 (sigmaSeries_polyBound 5))

private lemma value_eq_zero_of_exp_neg_ray' {S : PowerSeries ℂ} (hS : DiskCoeffBound S)
    (hray : ∀ t : ℝ, 0 < t → value S (Complex.exp (-(t : ℂ))) = 0) : S = 0 := by
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    have hcoeff_bd : ∀ t : ℝ, 1 ≤ t →
        ‖PowerSeries.coeff n S‖ ≤
          (∑' k : ℕ, ‖PowerSeries.coeff (k + (n + 1)) S‖ * (Real.exp (-1)) ^ k) * Real.exp (-t) := by
      intro t ht
      have ht_pos : 0 < t := by linarith
      have hq_norm : ‖Complex.exp (-(t : ℂ))‖ = Real.exp (-t) := by
        rw [show -(t : ℂ) = ((-t : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
      have hq_lt : ‖Complex.exp (-(t : ℂ))‖ < 1 := by
        rw [hq_norm]; exact Real.exp_lt_one_iff.mpr (by linarith)
      have habs : AbsAt S (Complex.exp (-(t : ℂ))) := by
        simpa [seriesJet] using seriesJet_abs hS 0 hq_lt
      have habs1 : AbsAt S (Complex.exp (-(1 : ℂ))) := by
        have h1 : ‖Complex.exp (-(1 : ℂ))‖ < 1 := by
          rw [show -(1 : ℂ) = ((-1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
          exact Real.exp_lt_one_iff.mpr (by norm_num)
        simpa [seriesJet] using seriesJet_abs hS 0 h1
      have h0 : value S (Complex.exp (-(t : ℂ))) = 0 := hray t ht_pos
      have hsplit := habs.of_norm.sum_add_tsum_nat_add (n + 1)
      change (∑ i ∈ Finset.range (n + 1), term S (Complex.exp (-(t : ℂ))) i) +
          ∑' k : ℕ, term S (Complex.exp (-(t : ℂ))) (k + (n + 1)) =
          value S (Complex.exp (-(t : ℂ))) at hsplit
      rw [h0, Finset.sum_range_succ] at hsplit
      have hpref : ∑ i ∈ Finset.range n, term S (Complex.exp (-(t : ℂ))) i = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        simp [term, ih i (Finset.mem_range.mp hi)]
      rw [hpref, zero_add] at hsplit
      have hterm_eq : term S (Complex.exp (-(t : ℂ))) n =
          -(∑' k : ℕ, term S (Complex.exp (-(t : ℂ))) (k + (n + 1))) :=
        eq_neg_of_add_eq_zero_left hsplit
      have hnorm_eq : ‖PowerSeries.coeff n S‖ * (Real.exp (-t)) ^ n =
          ‖∑' k : ℕ, term S (Complex.exp (-(t : ℂ))) (k + (n + 1))‖ := by
        have h1 := congrArg norm hterm_eq
        rw [norm_neg, term, norm_mul, norm_pow, hq_norm] at h1
        exact h1
      have hsum_norm_shift : Summable (fun k : ℕ => ‖term S (Complex.exp (-(t : ℂ))) (k + (n + 1))‖) :=
        habs.comp_injective (add_left_injective (n + 1))
      have hsum_bd1 : Summable (fun k : ℕ => ‖PowerSeries.coeff (k + (n + 1)) S‖ * (Real.exp (-1)) ^ k) := by
        have hs1 : Summable (fun k : ℕ => ‖term S (Complex.exp (-(1 : ℂ))) (k + (n + 1))‖) :=
          habs1.comp_injective (add_left_injective (n + 1))
        have hq1 : ‖Complex.exp (-(1 : ℂ))‖ = Real.exp (-1) := by
          rw [show -(1 : ℂ) = ((-1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
        refine (hs1.mul_right ((Real.exp (-1)) ^ (n + 1))⁻¹).congr fun k => ?_
        rw [term, norm_mul, norm_pow, hq1, pow_add, mul_assoc, mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero _ (Real.exp_pos _).ne'), mul_one]
      have hle_tail : ‖∑' k : ℕ, term S (Complex.exp (-(t : ℂ))) (k + (n + 1))‖ ≤
          (∑' k : ℕ, ‖PowerSeries.coeff (k + (n + 1)) S‖ * (Real.exp (-1)) ^ k) *
            ((Real.exp (-t)) ^ n * Real.exp (-t)) := by
        rw [← tsum_mul_right]
        calc ‖∑' k : ℕ, term S (Complex.exp (-(t : ℂ))) (k + (n + 1))‖
            ≤ ∑' k : ℕ, ‖term S (Complex.exp (-(t : ℂ))) (k + (n + 1))‖ :=
              norm_tsum_le_tsum_norm hsum_norm_shift
          _ ≤ ∑' k : ℕ, ‖PowerSeries.coeff (k + (n + 1)) S‖ * (Real.exp (-1)) ^ k *
                ((Real.exp (-t)) ^ n * Real.exp (-t)) := by
              refine hsum_norm_shift.tsum_le_tsum (fun k => ?_) (hsum_bd1.mul_right _)
              rw [term, norm_mul, norm_pow, hq_norm, pow_add, pow_succ]
              have hexp_le : (Real.exp (-t)) ^ k ≤ (Real.exp (-1)) ^ k :=
                pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (by linarith)) k
              have hnn : 0 ≤ ‖PowerSeries.coeff (k + (n + 1)) S‖ * ((Real.exp (-t)) ^ n * Real.exp (-t)) :=
                by positivity
              have h1 := mul_le_mul_of_nonneg_right hexp_le hnn
              linarith
      rw [← hnorm_eq] at hle_tail
      have hpos : 0 < (Real.exp (-t)) ^ n := pow_pos (Real.exp_pos _) n
      exact le_of_mul_le_mul_right (by linarith) hpos
    set C := ∑' k : ℕ, ‖PowerSeries.coeff (k + (n + 1)) S‖ * (Real.exp (-1)) ^ k
    have htend : Tendsto (fun t : ℝ => C * Real.exp (-t)) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C)
    have hnorm0 : ‖PowerSeries.coeff n S‖ ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds htend (Filter.eventually_atTop.mpr ⟨(1 : ℝ), hcoeff_bd⟩)
    exact norm_le_zero_iff.mp hnorm0

/-- Helper: imaginary ray `τ(s) = i s / (2π) ∈ ℍ` for `s > 0`. -/
private def tauRay (s : ℝ) : ℍ :=
  if hs : 0 < s then
    ⟨(Complex.I / (2 * (Real.pi : ℂ))) * (s : ℂ), by
      have hre : ((Complex.I / (2 * (Real.pi : ℂ))) * (s : ℂ)).im = s / (2 * Real.pi) := by
        rw [div_eq_mul_inv, mul_assoc, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
        have h1 : (((2 * (Real.pi : ℂ))⁻¹ * (s : ℂ))).re = (2 * Real.pi)⁻¹ * s := by
          have : (2 * (Real.pi : ℂ))⁻¹ * (s : ℂ) = (((2 * Real.pi)⁻¹ * s : ℝ) : ℂ) := by push_cast; ring
          rw [this, Complex.ofReal_re]
        rw [h1]; ring
      rw [hre]; positivity⟩
  else ⟨Complex.I, by simp⟩

private lemma tauRay_coe {s : ℝ} (hs : 0 < s) :
    (tauRay s : ℂ) = (Complex.I / (2 * (Real.pi : ℂ))) * (s : ℂ) := by
  simp [tauRay, hs]

private lemma cexp_tauRay {s : ℝ} (hs : 0 < s) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (tauRay s : ℂ)) = Complex.exp (-(s : ℂ)) := by
  rw [tauRay_coe hs]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi]
  rw [Complex.I_sq]; ring

/-- General ray differentiation transfer: if `F : ℍ → ℂ` is holomorphic (`MDiff F`) and matches a
polynomially bounded power series `S` along `tauRay`, then `D F` matches `thetaD S` along `tauRay`. -/
private lemma deriv_ray_match {F : ℍ → ℂ} {S : PowerSeries ℂ}
    (hF : MDiff F) (hS : PolyCoeffBound S)
    (heq : ∀ s : ℝ, 0 < s → F (tauRay s) = value S (Complex.exp (-(s : ℂ))))
    {s : ℝ} (hs : 0 < s) :
    D F (tauRay s) = value (thetaD S) (Complex.exp (-(s : ℂ))) := by
  have hLHS : HasDerivAt (fun u : ℝ => F (tauRay u)) (-(D F (tauRay s))) s := by
    have hτs := tauRay_coe hs
    have hF_diff : DifferentiableAt ℂ (F ∘ UpperHalfPlane.ofComplex)
        ((Complex.I / (2 * (Real.pi : ℂ))) * (s : ℂ)) := by
      rw [← hτs]; exact UpperHalfPlane.mdifferentiableAt_iff.mp (hF (tauRay s))
    have hlin : HasDerivAt (fun u : ℝ => (Complex.I / (2 * (Real.pi : ℂ))) * (u : ℂ))
        (Complex.I / (2 * (Real.pi : ℂ))) s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (Complex.I / (2 * (Real.pi : ℂ)))
    have hcomp := hF_diff.hasDerivAt.comp s hlin
    have hev : (fun u : ℝ => F (tauRay u)) =ᶠ[𝓝 s]
        fun u : ℝ => (F ∘ UpperHalfPlane.ofComplex) ((Complex.I / (2 * (Real.pi : ℂ))) * (u : ℂ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hs] with u hu
      rw [Function.comp_apply, ← tauRay_coe hu, UpperHalfPlane.ofComplex_apply]
    refine (hcomp.congr_of_eventuallyEq hev).congr_deriv ?_
    rw [normalizedDerivOfComplex, ← hτs]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hpi, Complex.I_ne_zero]
    rw [Complex.I_sq]; ring
  have hRHS : HasDerivAt (fun u : ℝ => value S (Complex.exp (-(u : ℂ))))
      (-value (thetaD S) (Complex.exp (-(s : ℂ)))) s := by
    have hq_lt : ‖Complex.exp (-(s : ℂ))‖ < 1 := by
      rw [show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
      exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs)
    have hval_deriv := seriesJet_deriv hS.to_diskCoeffBound 0 hq_lt
    have hexp : HasDerivAt (fun u : ℝ => Complex.exp (-(u : ℂ))) (-Complex.exp (-(s : ℂ))) s := by
      have hlin : HasDerivAt (fun u : ℝ => -(u : ℂ)) (-1 : ℂ) s := by
        have h := (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (-1 : ℂ)
        refine h.congr_of_eventuallyEq (Eventually.of_forall fun u => by simp) |>.congr_deriv ?_
        simp
      simpa using hlin.cexp
    have hcomp := hval_deriv.comp s hexp
    refine hcomp.congr_deriv ?_
    have hmul_val : value (thetaD S) (Complex.exp (-(s : ℂ))) =
        Complex.exp (-(s : ℂ)) * value (PowerSeries.derivative S) (Complex.exp (-(s : ℂ))) := by
      rw [thetaD_apply]
      let P : MvPolynomial (Fin 2) ℂ := MvPolynomial.X 0 * MvPolynomial.X 1
      have h1 := (polynomial_value P (S := ![PowerSeries.X, PowerSeries.derivative S])
        (q := Complex.exp (-(s : ℂ))) (fun i => by
          fin_cases i
          · exact (nome_abs _).1
          · simpa [seriesJet] using seriesJet_abs hS.to_diskCoeffBound 1 hq_lt)).2
      simpa [P, (nome_abs _).2] using h1
    rw [hmul_val]; simp [seriesJet]; ring
  have hev : (fun u : ℝ => F (tauRay u)) =ᶠ[𝓝 s] fun u : ℝ => value S (Complex.exp (-(u : ℂ))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hs] with u hu; exact heq u hu
  exact neg_inj.mp ((hLHS.congr_of_eventuallyEq hev.symm).unique hRHS)

private lemma sigmaSeries_tsum_pnat (k : ℕ) {s : ℝ} (hs : 0 < s) :
    (∑' n : ℕ+, (ArithmeticFunction.sigma k n : ℂ) * Complex.exp (-(s : ℂ)) ^ (n : ℕ)) =
      value (sigmaSeries k) (Complex.exp (-(s : ℂ))) := by
  have hq_lt : ‖Complex.exp (-(s : ℂ))‖ < 1 := by
    rw [show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs)
  unfold value
  rw [← tsum_zero_pnat_eq_tsum_nat
    ((by simpa [seriesJet] using seriesJet_abs (sigmaSeries_polyBound k).to_diskCoeffBound 0 hq_lt :
      AbsAt (sigmaSeries k) (Complex.exp (-(s : ℂ)))).of_norm)]
  simp only [term, sigmaSeries, PowerSeries.coeff_mk, ↓reduceIte, zero_mul, zero_add]
  refine tsum_congr fun n => ?_
  simp only [show (n : ℕ) ≠ 0 from n.ne_zero, ↓reduceIte, ArithmeticFunction.sigma_apply]
  push_cast; rfl

private lemma E2_ray_eq {s : ℝ} (hs : 0 < s) :
    E2 (tauRay s) = value E2Series (Complex.exp (-(s : ℂ))) := by
  have hq_lt : ‖Complex.exp (-(s : ℂ))‖ < 1 := by
    rw [show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs)
  rw [E2_eq_tsum_cexp, cexp_tauRay hs, sigmaSeries_tsum_pnat 1 hs]
  let P : MvPolynomial (Fin 1) ℂ := 1 - 24 * MvPolynomial.X 0
  have hP_eq : MvPolynomial.aeval (fun _ : Fin 1 => sigmaSeries 1) P = E2Series := by
    simp [P, E2Series, map_ofNat]
  have h := (polynomial_value P (S := fun _ : Fin 1 => sigmaSeries 1) (q := Complex.exp (-(s : ℂ)))
    (fun _ => by simpa [seriesJet] using seriesJet_abs (sigmaSeries_polyBound 1).to_diskCoeffBound 0 hq_lt)).2
  rw [hP_eq] at h
  simpa [P] using h.symm

private lemma E4_ray_eq {s : ℝ} (hs : 0 < s) :
    E₄ (tauRay s) = value E4Series (Complex.exp (-(s : ℂ))) := by
  have hq_lt : ‖Complex.exp (-(s : ℂ))‖ < 1 := by
    rw [show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs)
  have hq_exp := EisensteinSeries.q_expansion_bernoulli (k := 4) (by norm_num) (by decide) (tauRay s)
  change (E (by simp : 3 ≤ 4) (tauRay s) : ℂ) = _
  rw [hq_exp, bernoulli_four_eq', cexp_tauRay hs]
  simp_rw [zpow_natCast]
  rw [show (4 - 1 : ℕ) = 3 by rfl, sigmaSeries_tsum_pnat 3 hs]
  let P : MvPolynomial (Fin 1) ℂ := 1 + 240 * MvPolynomial.X 0
  have hP_eq : MvPolynomial.aeval (fun _ : Fin 1 => sigmaSeries 3) P = E4Series := by
    simp [P, E4Series, map_ofNat]
  have h := (polynomial_value P (S := fun _ : Fin 1 => sigmaSeries 3) (q := Complex.exp (-(s : ℂ)))
    (fun _ => by simpa [seriesJet] using seriesJet_abs (sigmaSeries_polyBound 3).to_diskCoeffBound 0 hq_lt)).2
  rw [hP_eq] at h
  have hval : value E4Series (Complex.exp (-(s : ℂ))) = 1 + 240 * value (sigmaSeries 3) (Complex.exp (-(s : ℂ))) := by
    simpa [P] using h
  rw [hval]; push_cast; ring

private lemma E6_ray_eq {s : ℝ} (hs : 0 < s) :
    E₆ (tauRay s) = value E6Series (Complex.exp (-(s : ℂ))) := by
  have hq_lt : ‖Complex.exp (-(s : ℂ))‖ < 1 := by
    rw [show -(s : ℂ) = ((-s : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hs)
  have hq_exp := EisensteinSeries.q_expansion_bernoulli (k := 6) (by norm_num) (by decide) (tauRay s)
  change (E (by simp : 3 ≤ 6) (tauRay s) : ℂ) = _
  rw [hq_exp, bernoulli_six_eq', cexp_tauRay hs]
  simp_rw [zpow_natCast]
  rw [show (6 - 1 : ℕ) = 5 by rfl, sigmaSeries_tsum_pnat 5 hs]
  let P : MvPolynomial (Fin 1) ℂ := 1 - 504 * MvPolynomial.X 0
  have hP_eq : MvPolynomial.aeval (fun _ : Fin 1 => sigmaSeries 5) P = E6Series := by
    simp [P, E6Series, map_ofNat]
  have h := (polynomial_value P (S := fun _ : Fin 1 => sigmaSeries 5) (q := Complex.exp (-(s : ℂ)))
    (fun _ => by simpa [seriesJet] using seriesJet_abs (sigmaSeries_polyBound 5).to_diskCoeffBound 0 hq_lt)).2
  rw [hP_eq] at h
  have hval : value E6Series (Complex.exp (-(s : ℂ))) = 1 - 504 * value (sigmaSeries 5) (Complex.exp (-(s : ℂ))) := by
    simpa [P] using h
  rw [hval]; push_cast; ring

/-- **Formal Ramanujan ODE #1 in `PowerSeries ℂ`**: `12 θ E₂ = E₂² - E₄`. -/
theorem ramanujan_ode_E2 :
    (12 : PowerSeries ℂ) * thetaD E2Series = E2Series ^ 2 - E4Series := by
  apply sub_eq_zero.mp
  let S : PowerSeries ℂ := (12 : PowerSeries ℂ) * thetaD E2Series - (E2Series ^ 2 - E4Series)
  have hS_poly : PolyCoeffBound S :=
    polyBound_sub'
      (by
        have h12 : (12 : PowerSeries ℂ) = PowerSeries.C (12 : ℂ) := (map_ofNat PowerSeries.C 12).symm
        rw [h12]; exact polyBound_const_mul' 12 (polyBound_thetaD E2Series_polyBound))
      (polyBound_sub' (by simpa [sq] using polyBound_mul' E2Series_polyBound E2Series_polyBound) E4Series_polyBound')
  refine value_eq_zero_of_exp_neg_ray' hS_poly.to_diskCoeffBound fun t ht => ?_
  have hq_lt : ‖Complex.exp (-(t : ℂ))‖ < 1 := by
    rw [show -(t : ℂ) = ((-t : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  let P : MvPolynomial (Fin 3) ℂ := 12 * MvPolynomial.X 0 - (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2)
  have hP : MvPolynomial.aeval ![thetaD E2Series, E2Series, E4Series] P = S := by
    simp [P, S, map_ofNat]
  have hv := (polynomial_value P (S := ![thetaD E2Series, E2Series, E4Series]) (q := Complex.exp (-(t : ℂ)))
    (fun i => by
      fin_cases i
      · simpa [seriesJet] using seriesJet_abs (polyBound_thetaD E2Series_polyBound).to_diskCoeffBound 0 hq_lt
      · simpa [seriesJet] using seriesJet_abs E2Series_polyBound.to_diskCoeffBound 0 hq_lt
      · simpa [seriesJet] using seriesJet_abs E4Series_polyBound'.to_diskCoeffBound 0 hq_lt)).2
  rw [hP] at hv
  rw [hv]
  have hD := deriv_ray_match E2_mdifferentiable E2Series_polyBound (fun s hs => E2_ray_eq hs) ht
  have hram := congrFun normalizedDerivOfComplex_E₂ (tauRay t)
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.pow_apply, smul_eq_mul] at hram
  simp only [P, map_sub, map_mul, map_pow, map_ofNat, MvPolynomial.eval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  rw [← hD, ← E2_ray_eq ht, ← E4_ray_eq ht, hram]
  ring

/-- **Formal Ramanujan ODE #2 in `PowerSeries ℂ`**: `3 θ E₄ = E₂ E₄ - E₆`. -/
theorem ramanujan_ode_E4 :
    (3 : PowerSeries ℂ) * thetaD E4Series = E2Series * E4Series - E6Series := by
  apply sub_eq_zero.mp
  let S : PowerSeries ℂ := (3 : PowerSeries ℂ) * thetaD E4Series - (E2Series * E4Series - E6Series)
  have hS_poly : PolyCoeffBound S :=
    polyBound_sub'
      (by
        have h3 : (3 : PowerSeries ℂ) = PowerSeries.C (3 : ℂ) := (map_ofNat PowerSeries.C 3).symm
        rw [h3]; exact polyBound_const_mul' 3 (polyBound_thetaD E4Series_polyBound'))
      (polyBound_sub' (polyBound_mul' E2Series_polyBound E4Series_polyBound') E6Series_polyBound)
  refine value_eq_zero_of_exp_neg_ray' hS_poly.to_diskCoeffBound fun t ht => ?_
  have hq_lt : ‖Complex.exp (-(t : ℂ))‖ < 1 := by
    rw [show -(t : ℂ) = ((-t : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  let P : MvPolynomial (Fin 4) ℂ :=
    3 * MvPolynomial.X 0 - (MvPolynomial.X 1 * MvPolynomial.X 2 - MvPolynomial.X 3)
  have hP : MvPolynomial.aeval ![thetaD E4Series, E2Series, E4Series, E6Series] P = S := by
    simp [P, S, map_ofNat]
  have hv := (polynomial_value P (S := ![thetaD E4Series, E2Series, E4Series, E6Series])
    (q := Complex.exp (-(t : ℂ))) (fun i => by
      fin_cases i
      · simpa [seriesJet] using seriesJet_abs (polyBound_thetaD E4Series_polyBound').to_diskCoeffBound 0 hq_lt
      · simpa [seriesJet] using seriesJet_abs E2Series_polyBound.to_diskCoeffBound 0 hq_lt
      · simpa [seriesJet] using seriesJet_abs E4Series_polyBound'.to_diskCoeffBound 0 hq_lt
      · simpa [seriesJet] using seriesJet_abs E6Series_polyBound.to_diskCoeffBound 0 hq_lt)).2
  rw [hP] at hv
  rw [hv]
  have hD : D (E₄ : ℍ → ℂ) (tauRay t) = value (thetaD E4Series) (Complex.exp (-(t : ℂ))) :=
    deriv_ray_match (F := (E₄ : ℍ → ℂ)) E₄.holo' E4Series_polyBound' (fun s hs => E4_ray_eq hs) ht
  have hram := congrFun normalizedDerivOfComplex_E₄ (tauRay t)
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul] at hram
  simp only [P, map_sub, map_mul, map_ofNat, MvPolynomial.eval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  rw [← hD, ← E2_ray_eq ht, ← E4_ray_eq ht, ← E6_ray_eq ht, hram]
  ring

/-- **Formal Ramanujan ODE #3 in `PowerSeries ℂ`**: `2 θ E₆ = E₂ E₆ - E₄²`. -/
theorem ramanujan_ode_E6 :
    (2 : PowerSeries ℂ) * thetaD E6Series = E2Series * E6Series - E4Series ^ 2 := by
  apply sub_eq_zero.mp
  let S : PowerSeries ℂ := (2 : PowerSeries ℂ) * thetaD E6Series - (E2Series * E6Series - E4Series ^ 2)
  have hS_poly : PolyCoeffBound S :=
    polyBound_sub'
      (by
        have h2 : (2 : PowerSeries ℂ) = PowerSeries.C (2 : ℂ) := (map_ofNat PowerSeries.C 2).symm
        rw [h2]; exact polyBound_const_mul' 2 (polyBound_thetaD E6Series_polyBound))
      (polyBound_sub' (polyBound_mul' E2Series_polyBound E6Series_polyBound)
        (by simpa [sq] using polyBound_mul' E4Series_polyBound' E4Series_polyBound'))
  refine value_eq_zero_of_exp_neg_ray' hS_poly.to_diskCoeffBound fun t ht => ?_
  have hq_lt : ‖Complex.exp (-(t : ℂ))‖ < 1 := by
    rw [show -(t : ℂ) = ((-t : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
    exact Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  let P : MvPolynomial (Fin 4) ℂ :=
    2 * MvPolynomial.X 0 - (MvPolynomial.X 1 * MvPolynomial.X 2 - MvPolynomial.X 3 ^ 2)
  have hP : MvPolynomial.aeval ![thetaD E6Series, E2Series, E6Series, E4Series] P = S := by
    simp [P, S, map_ofNat]
  have hv := (polynomial_value P (S := ![thetaD E6Series, E2Series, E6Series, E4Series])
    (q := Complex.exp (-(t : ℂ))) (fun i => by
      fin_cases i
      · simpa [seriesJet] using seriesJet_abs (polyBound_thetaD E6Series_polyBound).to_diskCoeffBound 0 hq_lt
      · simpa [seriesJet] using seriesJet_abs E2Series_polyBound.to_diskCoeffBound 0 hq_lt
      · simpa [seriesJet] using seriesJet_abs E6Series_polyBound.to_diskCoeffBound 0 hq_lt
      · simpa [seriesJet] using seriesJet_abs E4Series_polyBound'.to_diskCoeffBound 0 hq_lt)).2
  rw [hP] at hv
  rw [hv]
  have hD : D (E₆ : ℍ → ℂ) (tauRay t) = value (thetaD E6Series) (Complex.exp (-(t : ℂ))) :=
    deriv_ray_match (F := (E₆ : ℍ → ℂ)) E₆.holo' E6Series_polyBound (fun s hs => E6_ray_eq hs) ht
  have hram := congrFun normalizedDerivOfComplex_E₆ (tauRay t)
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul] at hram
  simp only [P, map_sub, map_mul, map_pow, map_ofNat, MvPolynomial.eval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  rw [← hD, ← E2_ray_eq ht, ← E4_ray_eq ht, ← E6_ray_eq ht, hram]
  ring

/-- Immediate corollary via `FalseThetaDichotomy.ramanujan_chazy_ode`:
`E2Series` satisfies Chazy's exact order-3 autonomous ODE in `PowerSeries ℂ`. -/
theorem E2Series_chazy_formal_ode :
    (2 : PowerSeries ℂ) * thetaD (thetaD (thetaD E2Series)) -
      2 * E2Series * thetaD (thetaD E2Series) + 3 * (thetaD E2Series) ^ 2 = 0 :=
  ramanujan_chazy_ode thetaD ramanujan_ode_E2 ramanujan_ode_E4 ramanujan_ode_E6

/-! #### 1B. Every Odd-Index Divisor Sum `L_{2k+1}` Lies in `ℂ[E₂, E₄, E₆]` -/

private lemma qExpansion_E4_eq : qExpansion 1 E₄ = E4Series := by
  ext m
  have h := EisensteinSeries.E_qExpansion_coeff (k := 4) (by norm_num) (by decide) m
  change (qExpansion 1 E₄).coeff m = _ at h
  rw [h, bernoulli_four_eq']
  cases m with
  | zero =>
    simp [E4Series, sigmaSeries]
  | succ n =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, E4Series, map_add, PowerSeries.coeff_one,
      PowerSeries.coeff_C_mul, sigmaSeries, PowerSeries.coeff_mk, zero_add,
      ArithmeticFunction.sigma_apply]
    push_cast; ring

private lemma qExpansion_E6_eq : qExpansion 1 E₆ = E6Series := by
  ext m
  have h := EisensteinSeries.E_qExpansion_coeff (k := 6) (by norm_num) (by decide) m
  change (qExpansion 1 E₆).coeff m = _ at h
  rw [h, bernoulli_six_eq']
  cases m with
  | zero =>
    simp [E6Series, sigmaSeries]
  | succ n =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, E6Series, map_sub, PowerSeries.coeff_one,
      PowerSeries.coeff_C_mul, sigmaSeries, PowerSeries.coeff_mk, zero_sub,
      ArithmeticFunction.sigma_apply]
    push_cast; ring

private lemma bernoulli_two_mul_ne_zero {k : ℕ} (hk : 1 ≤ k) : (bernoulli (2 * k) : ℂ) ≠ 0 := by
  intro h0
  have hz := riemannZeta_two_mul_nat (k := k) (by omega)
  rw [h0] at hz
  simp only [zero_div, mul_zero] at hz
  have hne : riemannZeta (2 * (k : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      simp only [Complex.mul_re, Complex.re_ofNat, Complex.natCast_re, Complex.im_ofNat,
        Complex.natCast_im, mul_zero, sub_zero]
      linarith)
  exact hne hz

/-- **Every odd-index divisor-sum Lambert series `sigmaSeries (2k + 1)` lies in `ℂ[E₂, E₄, E₆]`**:
for `k = 0`, `L₁ = (1 - E₂)/24`; for `k ≥ 1`, `L_{2k+1}` is a scalar multiple of `E_{2k+2} - 1`,
and `E_{2k+2} ∈ ℂ[E₄, E₆]` by Mathlib's `ModularForm.evalE₄E₆_surjective`. -/
theorem sigmaSeries_odd_mem_adjoin (k : ℕ) :
    sigmaSeries (2 * k + 1) ∈ Algebra.adjoin ℂ ({E2Series, E4Series, E6Series} : Set (PowerSeries ℂ)) := by
  let A := Algebra.adjoin ℂ ({E2Series, E4Series, E6Series} : Set (PowerSeries ℂ))
  have hE2 : E2Series ∈ A := Algebra.subset_adjoin (by simp)
  have hE4 : E4Series ∈ A := Algebra.subset_adjoin (by simp)
  have hE6 : E6Series ∈ A := Algebra.subset_adjoin (by simp)
  cases k with
  | zero =>
    have heq : sigmaSeries 1 = ((1 / 24 : ℂ) • (1 - E2Series)) := by
      ext n
      simp only [E2Series, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_smul, smul_eq_mul]
      ring
    rw [heq]
    exact A.smul_mem (A.sub_mem A.one_mem hE2) _
  | succ m =>
    let w : ℕ := 2 * (m + 2)
    have hw3 : 3 ≤ w := by dsimp only [w]; omega
    have hwev : Even w := ⟨m + 2, by dsimp only [w]; omega⟩
    let f : ModularForm 𝒮ℒ (w : ℤ) := E hw3
    obtain ⟨P, hP⟩ := ModularForm.evalE₄E₆_surjective (DirectSum.of (ModularForm 𝒮ℒ) (w : ℤ) f)
    have hq_poly : qExpansion 1 f = MvPolynomial.aeval ![E4Series, E6Series] P := by
      have hmap := congrArg (ModularForm.qExpansionAlgHom 1 one_pos one_mem_strictPeriods_SL) hP
      rw [ModularForm.qExpansionAlgHom_apply] at hmap
      rw [← hmap]
      clear hmap hP
      induction P using MvPolynomial.induction_on with
      | C c => simp
      | add Q R hQ hR => simp only [map_add, hQ, hR]
      | mul_X Q i hQ =>
        simp only [map_mul, MvPolynomial.aeval_X, hQ]
        congr 1
        fin_cases i
        · simp [ModularForm.evalE₄E₆_X_zero, qExpansion_E4_eq]
        · simp [ModularForm.evalE₄E₆_X_one, qExpansion_E6_eq]
    have hq_mem : qExpansion 1 f ∈ A := by
      rw [hq_poly]
      clear hP hq_poly
      induction P using MvPolynomial.induction_on with
      | C c => simp only [MvPolynomial.aeval_C]; exact Subalgebra.algebraMap_mem A c
      | add Q R hQ hR => rw [map_add]; exact Subalgebra.add_mem A hQ hR
      | mul_X Q i hQ =>
        rw [map_mul, MvPolynomial.aeval_X]
        refine Subalgebra.mul_mem A hQ ?_
        fin_cases i
        · simpa using hE4
        · simpa using hE6
    let β : ℂ := -(2 * (w : ℂ) / (bernoulli w : ℂ))
    have hβ_ne : β ≠ 0 := by
      dsimp only [β]
      have hw_ne : (w : ℂ) ≠ 0 := by exact_mod_cast (by omega : w ≠ 0)
      have hb_ne : (bernoulli w : ℂ) ≠ 0 := bernoulli_two_mul_ne_zero (by omega)
      exact neg_ne_zero.mpr (div_ne_zero (mul_ne_zero two_ne_zero hw_ne) hb_ne)
    have hq_eq : qExpansion 1 f = 1 + PowerSeries.C β * sigmaSeries (2 * (m + 1) + 1) := by
      ext n
      have hc := EisensteinSeries.E_qExpansion_coeff hw3 hwev n
      change (qExpansion 1 f).coeff n = _ at hc
      rw [hc]
      cases n with
      | zero => simp [sigmaSeries]
      | succ r =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, map_add, PowerSeries.coeff_one,
          PowerSeries.coeff_C_mul, sigmaSeries, PowerSeries.coeff_mk, zero_add,
          ArithmeticFunction.sigma_apply]
        have hwm : w - 1 = 2 * (m + 1) + 1 := by dsimp only [w]; omega
        rw [hwm]
        dsimp only [β]
        push_cast; rfl
    have hsig_eq : sigmaSeries (2 * (m + 1) + 1) = β⁻¹ • (qExpansion 1 f - 1) := by
      rw [hq_eq]
      ext n
      simp only [map_sub, map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_smul, smul_eq_mul]
      field_simp [hβ_ne]
      ring
    rw [hsig_eq]
    exact A.smul_mem (A.sub_mem hq_mem A.one_mem) _

/-! #### 1C. Differential-Field Closure in `FractionRing (PowerSeries ℂ)` & General D-Algebraicity -/

abbrev PS := PowerSeries ℂ
abbrev FracPS := FractionRing PS
abbrev embPS : PS →ₐ[ℂ] FracPS := IsScalarTower.toAlgHom ℂ PS FracPS
abbrev genPS {ι : Type} (v : ι → PS) : IntermediateField ℂ FracPS :=
  IntermediateField.adjoin ℂ (Set.range fun i => embPS (v i))

private lemma embPS_C_mem {ι : Type} (v : ι → PS) (c : ℂ) : embPS (PowerSeries.C c) ∈ genPS v := by
  have h : embPS (PowerSeries.C c) = algebraMap ℂ FracPS c := by
    rw [← PowerSeries.algebraMap_eq, AlgHom.commutes]
  rw [h]
  exact (genPS v).algebraMap_mem c

private lemma mem_eval_ps' {ι : Type} (v : ι → PS) (P : MvPolynomial ι ℂ) :
    embPS (MvPolynomial.aeval v P) ∈ genPS v := by
  rw [MvPolynomial.comp_aeval_apply]
  induction P using MvPolynomial.induction_on with
  | C r => simp only [MvPolynomial.aeval_C]; exact (genPS v).algebraMap_mem r
  | add P Q hP hQ => simpa only [map_add] using (genPS v).add_mem hP hQ
  | mul_X P i hP =>
    simpa only [map_mul, MvPolynomial.aeval_X] using
      (genPS v).mul_mem hP (IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self i))

private lemma poly_deriv_mem_ps' {ι : Type} (v : ι → PS)
    (h : ∀ i, embPS (PowerSeries.derivative (v i)) ∈ genPS v) (P : MvPolynomial ι ℂ) :
    embPS (PowerSeries.derivative (MvPolynomial.aeval v P)) ∈ genPS v := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ => simpa only [map_add] using (genPS v).add_mem hP hQ
  | mul_X P i hP =>
    simp only [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, smul_eq_mul, map_add]
    exact (genPS v).add_mem ((genPS v).mul_mem (mem_eval_ps' v P) (h i))
      ((genPS v).mul_mem (IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self i)) hP)

private lemma deriv_mem_ps' {ι : Type} (v : ι → PS)
    (h : ∀ i, embPS (PowerSeries.derivative (v i)) ∈ genPS v)
    {f : PS} (hf : embPS f ∈ genPS v) : embPS (PowerSeries.derivative f) ∈ genPS v := by
  rcases (IntermediateField.mem_adjoin_range_iff ℂ (fun i => embPS (v i)) _).mp hf with ⟨P, Q, he⟩
  have hinj : Function.Injective embPS := IsFractionRing.injective PS FracPS
  rw [← MvPolynomial.comp_aeval_apply, ← MvPolynomial.comp_aeval_apply] at he
  by_cases hn : embPS (MvPolynomial.aeval v Q) = 0
  · rw [hn, div_zero] at he
    have hzero : f = 0 := hinj (he.trans embPS.map_zero.symm)
    simp [hzero]
  have hj : f * MvPolynomial.aeval v Q = MvPolynomial.aeval v P :=
    hinj (by rw [map_mul]; exact (eq_div_iff hn).mp he)
  have hd := congrArg (fun a : PS => embPS (PowerSeries.derivative a)) hj
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul] at hd
  have hdf : embPS (PowerSeries.derivative f) =
      (embPS (PowerSeries.derivative (MvPolynomial.aeval v P)) -
        embPS f * embPS (PowerSeries.derivative (MvPolynomial.aeval v Q))) /
      embPS (MvPolynomial.aeval v Q) := by
    apply (eq_div_iff hn).mpr
    linear_combination hd
  rw [hdf]
  exact (genPS v).div_mem ((genPS v).sub_mem (poly_deriv_mem_ps' v h P)
    ((genPS v).mul_mem hf (poly_deriv_mem_ps' v h Q))) (mem_eval_ps' v Q)

/-- **Finite Differential Subfield ⇒ D-Algebraicity**:
If `v : ι → PowerSeries ℂ` (`Fintype ι`) generates a derivative-closed subfield of
`FractionRing (PowerSeries ℂ)` containing `X` and `F`, then `F` is D-algebraic over `ℂ(X)`. -/
theorem dAlgebraic_of_mem_diff_gen {ι : Type} [Fintype ι] (v : ι → PowerSeries ℂ)
    (hX : embPS PowerSeries.X ∈ genPS v)
    (hclosed : ∀ i, embPS (PowerSeries.derivative (v i)) ∈ genPS v)
    {F : PowerSeries ℂ} (hF : embPS F ∈ genPS v) :
    ¬ AlgebraicIndependent ℂ (seriesCoordinates F) := by
  have hall : ∀ n : ℕ, embPS (seriesCoordinates F n) ∈ genPS v := by
    intro n
    cases n with
    | zero => exact hX
    | succ k =>
      change embPS (PowerSeries.derivative^[k] F) ∈ genPS v
      induction k with
      | zero => simpa using hF
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        exact deriv_mem_ps' v hclosed ih
  intro hi
  have hfg : (genPS v).FG := IntermediateField.fg_adjoin_of_finite (Set.finite_range _)
  let : Algebra.EssFiniteType ℂ (genPS v) := IntermediateField.essFiniteType_iff.mpr hfg
  have hE : AlgebraicIndependent ℂ (embPS ∘ seriesCoordinates F) :=
    (embPS.algebraicIndependent_iff (IsFractionRing.injective PS FracPS)).mpr hi
  have hS : AlgebraicIndependent ℂ (fun i => (⟨embPS (seriesCoordinates F i), hall i⟩ : genPS v)) :=
    hE.of_comp (genPS v).val
  let : Finite ℕ := finite_of_algebraicIndependent hS
  exact not_finite ℕ

/-- **Log-Derivative D-Algebraicity Transfer**:
If `H` lies in a finite derivative-closed subfield `genPS v` containing `X`, and `G` satisfies
`X * derivative G = H * G`, then `G` is also D-algebraic over `ℂ(X)`. -/
theorem dAlgebraic_of_log_deriv_mem_diff_gen {ι : Type} [Fintype ι] (v : ι → PowerSeries ℂ)
    (hX : embPS PowerSeries.X ∈ genPS v)
    (hclosed : ∀ i, embPS (PowerSeries.derivative (v i)) ∈ genPS v)
    {H G : PowerSeries ℂ} (hH : embPS H ∈ genPS v)
    (hode : PowerSeries.X * PowerSeries.derivative G = H * G) :
    ¬ AlgebraicIndependent ℂ (seriesCoordinates G) := by
  let v' : Option ι → PowerSeries ℂ := Option.elim' G v
  have hle : genPS v ≤ genPS v' := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact IntermediateField.subset_adjoin ℂ _ ⟨some i, rfl⟩
  have hX' : embPS PowerSeries.X ∈ genPS v' := hle hX
  have hG' : embPS G ∈ genPS v' := IntermediateField.subset_adjoin ℂ _ ⟨none, rfl⟩
  have hH' : embPS H ∈ genPS v' := hle hH
  have hXne : embPS PowerSeries.X ≠ 0 := by
    intro h0
    have hX0 : (PowerSeries.X : PowerSeries ℂ) = 0 :=
      IsFractionRing.injective PS FracPS (h0.trans embPS.map_zero.symm)
    have h1 := congrArg (PowerSeries.coeff 1) hX0
    simp at h1
  refine dAlgebraic_of_mem_diff_gen v' hX' (fun o => ?_) hG'
  cases o with
  | some i => exact hle (hclosed i)
  | none =>
    change embPS (PowerSeries.derivative G) ∈ genPS v'
    have hm := congrArg embPS hode
    simp only [map_mul] at hm
    have heq : embPS (PowerSeries.derivative G) = embPS H * embPS G / embPS PowerSeries.X := by
      apply (eq_div_iff hXne).mpr
      linear_combination hm
    rw [heq]
    exact (genPS v').div_mem ((genPS v').mul_mem hH' hG') hX'

/-- Generators of the level-`S` quasi-modular differential subfield:
`X` together with `(expand m E₂, expand m E₄, expand m E₆)` for `m ∈ S`. -/
private def qmGen (S : Finset ℕ+) : Option (S × Fin 3) → PowerSeries ℂ
  | none => PowerSeries.X
  | some (m, j) =>
    match j with
    | 0 => PowerSeries.expand m.1.1 m.1.2.ne' E2Series
    | 1 => PowerSeries.expand m.1.1 m.1.2.ne' E4Series
    | 2 => PowerSeries.expand m.1.1 m.1.2.ne' E6Series

private lemma qmGen_X_mem (S : Finset ℕ+) : embPS PowerSeries.X ∈ genPS (qmGen S) :=
  IntermediateField.subset_adjoin ℂ _ ⟨none, rfl⟩

private lemma qmGen_closed (S : Finset ℕ+) :
    ∀ i, embPS (PowerSeries.derivative (qmGen S i)) ∈ genPS (qmGen S) := by
  have hX : embPS PowerSeries.X ∈ genPS (qmGen S) := qmGen_X_mem S
  have hXne : embPS PowerSeries.X ≠ 0 := by
    intro h0
    have hX0 : (PowerSeries.X : PowerSeries ℂ) = 0 :=
      IsFractionRing.injective PS FracPS (h0.trans embPS.map_zero.symm)
    have h1 := congrArg (PowerSeries.coeff 1) hX0
    simp at h1
  have hnat_ne : ∀ n : ℕ, n ≠ 0 → (n : FracPS) ≠ 0 := fun n hn h0 => by
    have hC : algebraMap ℂ FracPS (n : ℂ) = 0 := by simpa using h0
    have hnC : (n : ℂ) = 0 := (algebraMap ℂ FracPS).injective (hC.trans (map_zero _).symm)
    exact hn (Nat.cast_eq_zero.mp hnC)
  intro i
  cases i with
  | none =>
    change embPS (PowerSeries.derivative PowerSeries.X) ∈ genPS (qmGen S)
    simp
  | some mj =>
    rcases mj with ⟨m, j⟩
    have hm2 : embPS (PowerSeries.expand m.1.1 m.1.2.ne' E2Series) ∈ genPS (qmGen S) :=
      IntermediateField.subset_adjoin ℂ _ ⟨some (m, 0), rfl⟩
    have hm4 : embPS (PowerSeries.expand m.1.1 m.1.2.ne' E4Series) ∈ genPS (qmGen S) :=
      IntermediateField.subset_adjoin ℂ _ ⟨some (m, 1), rfl⟩
    have hm6 : embPS (PowerSeries.expand m.1.1 m.1.2.ne' E6Series) ∈ genPS (qmGen S) :=
      IntermediateField.subset_adjoin ℂ _ ⟨some (m, 2), rfl⟩
    have hC : ∀ c : ℂ, embPS (PowerSeries.C c) ∈ genPS (qmGen S) := embPS_C_mem (qmGen S)
    fin_cases j
    · change embPS (PowerSeries.derivative (PowerSeries.expand m.1.1 m.1.2.ne' E2Series)) ∈ genPS (qmGen S)
      have hode : (12 : PS) * (PowerSeries.X * PowerSeries.derivative (PowerSeries.expand m.1.1 m.1.2.ne' E2Series)) =
          PowerSeries.C (m.1.1 : ℂ) * ((PowerSeries.expand m.1.1 m.1.2.ne' E2Series) ^ 2 -
            PowerSeries.expand m.1.1 m.1.2.ne' E4Series) := by
        rw [← thetaD_apply, thetaD_expand m.1.2 E2Series]
        have h1 := congrArg (PowerSeries.expand m.1.1 m.1.2.ne') ramanujan_ode_E2
        simp only [map_mul, map_ofNat, map_sub, map_pow] at h1
        linear_combination PowerSeries.C (m.1.1 : ℂ) * h1
      have hm := congrArg embPS hode
      simp only [map_mul, map_ofNat, map_sub, map_pow] at hm
      have heq : embPS (PowerSeries.derivative (PowerSeries.expand m.1.1 m.1.2.ne' E2Series)) =
          embPS (PowerSeries.C (m.1.1 : ℂ)) *
            (embPS (PowerSeries.expand m.1.1 m.1.2.ne' E2Series) ^ 2 -
              embPS (PowerSeries.expand m.1.1 m.1.2.ne' E4Series)) /
            ((12 : FracPS) * embPS PowerSeries.X) := by
        apply (eq_div_iff (mul_ne_zero (hnat_ne 12 (by decide)) hXne)).mpr
        linear_combination hm
      rw [heq]
      exact (genPS (qmGen S)).div_mem
        ((genPS (qmGen S)).mul_mem (hC _) ((genPS (qmGen S)).sub_mem ((genPS (qmGen S)).pow_mem hm2 2) hm4))
        ((genPS (qmGen S)).mul_mem (by simp) hX)
    · change embPS (PowerSeries.derivative (PowerSeries.expand m.1.1 m.1.2.ne' E4Series)) ∈ genPS (qmGen S)
      have hode : (3 : PS) * (PowerSeries.X * PowerSeries.derivative (PowerSeries.expand m.1.1 m.1.2.ne' E4Series)) =
          PowerSeries.C (m.1.1 : ℂ) * (PowerSeries.expand m.1.1 m.1.2.ne' E2Series *
            PowerSeries.expand m.1.1 m.1.2.ne' E4Series - PowerSeries.expand m.1.1 m.1.2.ne' E6Series) := by
        rw [← thetaD_apply, thetaD_expand m.1.2 E4Series]
        have h1 := congrArg (PowerSeries.expand m.1.1 m.1.2.ne') ramanujan_ode_E4
        simp only [map_mul, map_ofNat, map_sub] at h1
        linear_combination PowerSeries.C (m.1.1 : ℂ) * h1
      have hm := congrArg embPS hode
      simp only [map_mul, map_ofNat, map_sub] at hm
      have heq : embPS (PowerSeries.derivative (PowerSeries.expand m.1.1 m.1.2.ne' E4Series)) =
          embPS (PowerSeries.C (m.1.1 : ℂ)) *
            (embPS (PowerSeries.expand m.1.1 m.1.2.ne' E2Series) *
              embPS (PowerSeries.expand m.1.1 m.1.2.ne' E4Series) -
              embPS (PowerSeries.expand m.1.1 m.1.2.ne' E6Series)) /
            ((3 : FracPS) * embPS PowerSeries.X) := by
        apply (eq_div_iff (mul_ne_zero (hnat_ne 3 (by decide)) hXne)).mpr
        linear_combination hm
      rw [heq]
      exact (genPS (qmGen S)).div_mem
        ((genPS (qmGen S)).mul_mem (hC _) ((genPS (qmGen S)).sub_mem ((genPS (qmGen S)).mul_mem hm2 hm4) hm6))
        ((genPS (qmGen S)).mul_mem (by simp) hX)
    · change embPS (PowerSeries.derivative (PowerSeries.expand m.1.1 m.1.2.ne' E6Series)) ∈ genPS (qmGen S)
      have hode : (2 : PS) * (PowerSeries.X * PowerSeries.derivative (PowerSeries.expand m.1.1 m.1.2.ne' E6Series)) =
          PowerSeries.C (m.1.1 : ℂ) * (PowerSeries.expand m.1.1 m.1.2.ne' E2Series *
            PowerSeries.expand m.1.1 m.1.2.ne' E6Series - (PowerSeries.expand m.1.1 m.1.2.ne' E4Series) ^ 2) := by
        rw [← thetaD_apply, thetaD_expand m.1.2 E6Series]
        have h1 := congrArg (PowerSeries.expand m.1.1 m.1.2.ne') ramanujan_ode_E6
        simp only [map_mul, map_ofNat, map_sub, map_pow] at h1
        linear_combination PowerSeries.C (m.1.1 : ℂ) * h1
      have hm := congrArg embPS hode
      simp only [map_mul, map_ofNat, map_sub, map_pow] at hm
      have heq : embPS (PowerSeries.derivative (PowerSeries.expand m.1.1 m.1.2.ne' E6Series)) =
          embPS (PowerSeries.C (m.1.1 : ℂ)) *
            (embPS (PowerSeries.expand m.1.1 m.1.2.ne' E2Series) *
              embPS (PowerSeries.expand m.1.1 m.1.2.ne' E6Series) -
              embPS (PowerSeries.expand m.1.1 m.1.2.ne' E4Series) ^ 2) /
            ((2 : FracPS) * embPS PowerSeries.X) := by
        apply (eq_div_iff (mul_ne_zero (hnat_ne 2 (by decide)) hXne)).mpr
        linear_combination hm
      rw [heq]
      exact (genPS (qmGen S)).div_mem
        ((genPS (qmGen S)).mul_mem (hC _) ((genPS (qmGen S)).sub_mem ((genPS (qmGen S)).mul_mem hm2 hm6)
          ((genPS (qmGen S)).pow_mem hm4 2)))
        ((genPS (qmGen S)).mul_mem (by simp) hX)

private lemma expand_sigmaSeries_odd_mem_qmGen {S : Finset ℕ+} {m : ℕ+} (hm : m ∈ S) (k : ℕ) :
    embPS (PowerSeries.expand m.1 m.2.ne' (sigmaSeries (2 * k + 1))) ∈ genPS (qmGen S) := by
  have hmem := sigmaSeries_odd_mem_adjoin k
  let f : PS →ₐ[ℂ] FracPS := embPS.comp (PowerSeries.expand m.1 m.2.ne')
  have hsub : Algebra.adjoin ℂ ({E2Series, E4Series, E6Series} : Set PS) ≤
      (genPS (qmGen S)).toSubalgebra.comap f := by
    refine Algebra.adjoin_le ?_
    rintro x (rfl | rfl | rfl)
    · exact IntermediateField.subset_adjoin ℂ _ ⟨some (⟨m, hm⟩, 0), rfl⟩
    · exact IntermediateField.subset_adjoin ℂ _ ⟨some (⟨m, hm⟩, 1), rfl⟩
    · exact IntermediateField.subset_adjoin ℂ _ ⟨some (⟨m, hm⟩, 2), rfl⟩
  exact hsub hmem

private lemma sigmaSeries_odd_mem_qmGen_one {S : Finset ℕ+} (h1 : (1 : ℕ+) ∈ S) (k : ℕ) :
    embPS (sigmaSeries (2 * k + 1)) ∈ genPS (qmGen S) := by
  have heq : PowerSeries.expand (1 : ℕ+).1 (1 : ℕ+).2.ne' (sigmaSeries (2 * k + 1)) =
      sigmaSeries (2 * k + 1) := by
    ext n
    rw [PowerSeries.coeff_expand]
    change (if 1 ∣ n then PowerSeries.coeff (n / 1) (sigmaSeries (2 * k + 1)) else 0) = _
    simp
  rw [← heq]
  exact expand_sigmaSeries_odd_mem_qmGen h1 k

/-- **Master Even-Divisor-Sum D-Algebraicity Theorem**:
For any finite set `S : Finset ℕ+` of scaling periods and any `H` in the `ℂ`-linear span of
`{expand m (sigmaSeries (2k + 1)) | m ∈ S, k ∈ ℕ}` (in fact, any element of `genPS (qmGen S)`),
both `H` and any Euler product `G` satisfying `X * G' = H * G` are **D-algebraic** over `ℂ(q)`. -/
theorem evenDivisorSpan_dAlgebraic {S : Finset ℕ+} {ι : Type*} (t : Finset ι)
    (c : ι → ℂ) (m : ι → ℕ+) (hm : ∀ i ∈ t, m i ∈ S) (k : ι → ℕ) :
    let H : PowerSeries ℂ := ∑ i ∈ t, PowerSeries.C (c i) * PowerSeries.expand (m i).1 (m i).2.ne' (sigmaSeries (2 * k i + 1))
    (¬ AlgebraicIndependent ℂ (seriesCoordinates H)) ∧
    (∀ G : PowerSeries ℂ, PowerSeries.X * PowerSeries.derivative G = H * G →
      ¬ AlgebraicIndependent ℂ (seriesCoordinates G)) := by
  intro H
  have hH_mem : embPS H ∈ genPS (qmGen S) := by
    dsimp only [H]
    rw [map_sum]
    refine (genPS (qmGen S)).sum_mem fun i hi => ?_
    rw [map_mul]
    exact (genPS (qmGen S)).mul_mem (embPS_C_mem _ (c i))
      (expand_sigmaSeries_odd_mem_qmGen (hm i hi) (k i))
  exact ⟨dAlgebraic_of_mem_diff_gen (qmGen S) (qmGen_X_mem S) (qmGen_closed S) hH_mem,
    fun G hode => dAlgebraic_of_log_deriv_mem_diff_gen (qmGen S) (qmGen_X_mem S) (qmGen_closed S) hH_mem hode⟩

/-! #### 1D. Complete Unconditional `IFF` Theorems for Period `M = 1` and Period `M = 2` -/

private lemma lambertSeries_pow (d : ℕ) :
    lambertSeries (fun n => (n : ℂ) ^ d) = sigmaSeries (d + 1) := by
  ext n
  rw [coeff_lambertSeries]
  by_cases hn : n = 0
  · subst hn; simp [sigmaSeries]
  · simp only [hn, ↓reduceIte, sigmaSeries, PowerSeries.coeff_mk]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [pow_succ']

private lemma lambertSeries_mul_dvd {m : ℕ} (hm : 0 < m) (d : ℕ) :
    lambertSeries (fun n => if m ∣ n then (n : ℂ) ^ d else 0) =
      PowerSeries.C ((m : ℂ) ^ (d + 1)) * PowerSeries.expand m hm.ne' (sigmaSeries (d + 1)) := by
  ext n
  rw [coeff_lambertSeries, PowerSeries.coeff_C_mul, PowerSeries.coeff_expand]
  by_cases hn : n = 0
  · subst hn
    simp only [↓reduceIte, dvd_zero, Nat.zero_div, sigmaSeries, PowerSeries.coeff_mk, mul_zero]
  · simp only [hn, ↓reduceIte]
    split_ifs with hmn
    · obtain ⟨q, rfl⟩ := hmn
      have hq0 : q ≠ 0 := by intro h; subst h; simp at hn
      rw [Nat.mul_div_cancel_left q hm]
      simp only [sigmaSeries, PowerSeries.coeff_mk, hq0, ↓reduceIte, Finset.mul_sum]
      have hfilt : (∑ e ∈ (m * q).divisors, (e : ℂ) * (if m ∣ e then (e : ℂ) ^ d else 0)) =
          ∑ e ∈ (m * q).divisors.filter (m ∣ ·), (e : ℂ) ^ (d + 1) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun e _ => ?_
        split_ifs <;> simp [pow_succ']
      rw [hfilt]
      refine (Finset.sum_bij (fun a _ => m * a) ?_ ?_ ?_ ?_).symm
      · intro a ha
        simp only [Finset.mem_filter, Nat.mem_divisors] at ha ⊢
        exact ⟨⟨Nat.mul_dvd_mul_left m ha.1, hn⟩, dvd_mul_right m a⟩
      · intro a₁ _ a₂ _ h; exact Nat.eq_of_mul_eq_mul_left hm h
      · intro e he
        simp only [Finset.mem_filter, Nat.mem_divisors] at he
        obtain ⟨⟨he_dvd, _⟩, ⟨a, rfl⟩⟩ := he
        exact ⟨a, Nat.mem_divisors.mpr ⟨(Nat.mul_dvd_mul_iff_left hm).mp he_dvd, hq0⟩, rfl⟩
      · intro a _
        push_cast; rw [mul_pow]
    · rw [mul_zero]
      refine Finset.sum_eq_zero fun e he => ?_
      have hndvd : ¬ m ∣ e := fun hme => hmn (dvd_trans hme (Nat.dvd_of_mem_divisors he))
      simp only [hndvd, ↓reduceIte, mul_zero]

private lemma lambertSeries_const_mul (c : ℂ) (w : ℕ → ℂ) :
    lambertSeries (fun n => c * w n) = PowerSeries.C c * lambertSeries w := by
  ext n
  rw [coeff_lambertSeries, PowerSeries.coeff_C_mul, coeff_lambertSeries]
  split_ifs with hn
  · simp
  · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d _ => by ring

private lemma lambertSeries_finset_sum {ι : Type*} (s : Finset ι) (w : ι → ℕ → ℂ) :
    lambertSeries (fun n => ∑ i ∈ s, w i n) = ∑ i ∈ s, lambertSeries (w i) := by
  ext n
  rw [coeff_lambertSeries, map_sum]
  simp_rw [coeff_lambertSeries]
  split_ifs with hn
  · simp
  · simp_rw [Finset.mul_sum]; exact Finset.sum_comm

private lemma period1_oddPart_eq_zero_iff (P : Quasipoly) (hM : P.M = 1) :
    (∀ n : ℤ, P.oddPart n = 0) ↔ ∀ d : Fin (P.D + 1), Odd d.1 → P.c d 0 = 0 := by
  constructor
  · intro hall d hodd
    -- Evaluate `P.oddPart` as a polynomial in `n`!
    let Q : Polynomial ℂ := ∑ e : Fin (P.D + 1), Polynomial.C (P.cOdd e 0) * Polynomial.X ^ e.1
    have hQ_eval : ∀ n : ℤ, Q.eval (n : ℂ) = 0 := by
      intro n
      have h1 := hall n
      rw [P.oddPart_eq_sum_cOdd n] at h1
      have hmod : (n % (P.M : ℤ)).toNat = 0 := by rw [hM]; simp
      simp_rw [hmod] at h1
      change Polynomial.evalRingHom (n : ℂ) Q = 0
      dsimp only [Q]
      rw [map_sum]
      simpa [Polynomial.eval_C, Polynomial.eval_X] using h1
    have hQ0 : Q = 0 := by
      by_contra hne
      have hfin : (Q.roots.toFinset : Set ℂ).Finite := Finset.finite_toSet _
      have hinf : (Set.range (fun n : ℕ => (n : ℂ))).Infinite :=
        Set.infinite_range_of_injective Nat.cast_injective
      obtain ⟨z, ⟨n, rfl⟩, hnot⟩ := (hinf.sdiff hfin).nonempty
      have hroot : (n : ℂ) ∈ Q.roots.toFinset := by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
        simpa [Polynomial.IsRoot] using hQ_eval (n : ℤ)
      exact hnot hroot
    have hc0 := congrArg (fun R : Polynomial ℂ => Polynomial.lcoeff ℂ d.1 R) hQ0
    rw [map_zero] at hc0
    dsimp only [Q] at hc0
    rw [map_sum] at hc0
    simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero] at hc0
    have hsum : (∑ e : Fin (P.D + 1), if d.1 = e.1 then P.cOdd e 0 else 0) = P.cOdd d 0 := by
      rw [Finset.sum_eq_single d]
      · simp
      · intro e _ hne; exact ite_eq_right_iff.mpr fun h => (hne (Fin.ext h.symm)).elim
      · intro h; exact absurd (Finset.mem_univ d) h
    rw [hsum] at hc0
    have hcOdd_eq : P.cOdd d 0 = P.c d 0 := by
      unfold Quasipoly.cOdd
      rw [Nat.zero_mod, Nat.sub_zero, P.periodic_M, hodd.neg_one_pow]
      ring
    rwa [hcOdd_eq] at hc0
  · intro hzero n
    rw [P.oddPart_eq_sum_cOdd]
    have hmod : (n % (P.M : ℤ)).toNat = 0 := by rw [hM]; simp
    simp_rw [hmod]
    refine Finset.sum_eq_zero fun d _ => ?_
    rcases Nat.even_or_odd d.1 with he | ho
    · have h0 : P.cOdd d 0 = 0 := by
        unfold Quasipoly.cOdd
        rw [Nat.zero_mod, Nat.sub_zero, P.periodic_M, he.neg_one_pow]; ring
      rw [h0, zero_mul]
    · have h0 : P.cOdd d 0 = 0 := by
        unfold Quasipoly.cOdd
        rw [Nat.zero_mod, Nat.sub_zero, P.periodic_M, ho.neg_one_pow, hzero d ho]; ring
      rw [h0, zero_mul]

/-- **Complete Unconditional `IFF` Theorem for ALL Polynomial Weights (`M = 1`) — Lambert Series**:
For any polynomial quasipolynomial `P` (`P.M = 1`), its Lambert series `H_P(q)` is D-algebraic
if and only if `P` is even (`∀ n : ℤ, P.oddPart n = 0`). -/
theorem quasipoly_period1_lambert_iff (P : Quasipoly) (hM : P.M = 1) :
    ¬ AlgebraicIndependent ℂ (seriesCoordinates (lambertSeries (fun n => P.eval (n : ℤ)))) ↔
      ∀ n : ℤ, P.oddPart n = 0 := by
  constructor
  · intro hdep n
    by_contra hne
    exact hdep (quasipoly_lambert_pure_algebraicIndependent P ⟨n, hne⟩)
  · intro heven
    have hodd0 := (period1_oddPart_eq_zero_iff P hM).mp heven
    let S : Finset ℕ+ := {1}
    have hH_mem : embPS (lambertSeries (fun n => P.eval (n : ℤ))) ∈ genPS (qmGen S) := by
      have hrew : lambertSeries (fun n => P.eval (n : ℤ)) =
          ∑ d : Fin (P.D + 1), PowerSeries.C (P.c d 0) * sigmaSeries (d.1 + 1) := by
        have hfun : (fun n : ℕ => P.eval (n : ℤ)) =
            fun n : ℕ => ∑ d : Fin (P.D + 1), P.c d 0 * (n : ℂ) ^ d.1 := by
          funext n
          rw [P.eval_nat n]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [← P.periodic_mod d n, hM, Nat.mod_one]
        rw [hfun, lambertSeries_finset_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [lambertSeries_const_mul, lambertSeries_pow]
      rw [hrew, map_sum]
      refine (genPS (qmGen S)).sum_mem fun d _ => ?_
      rcases Nat.even_or_odd d.1 with ⟨k, hk⟩ | hodd
      · rw [map_mul]
        refine (genPS (qmGen S)).mul_mem (embPS_C_mem _ (P.c d 0)) ?_
        have h2k : d.1 + 1 = 2 * k + 1 := by omega
        rw [h2k]
        exact sigmaSeries_odd_mem_qmGen_one (Finset.mem_singleton_self 1) k
      · rw [hodd0 d hodd, map_zero, zero_mul, map_zero]
        exact (genPS (qmGen S)).zero_mem
    exact dAlgebraic_of_mem_diff_gen (qmGen S) (qmGen_X_mem S) (qmGen_closed S) hH_mem

/-- **Complete Unconditional `IFF` Theorem for ALL Polynomial Weights (`M = 1`) — Euler Products**:
For any polynomial quasipolynomial `P` (`P.M = 1`), the weighted Euler product
`G_P(q) = ∏_{n ≥ 1} (1 - q^n)^{-P(n)}` is D-algebraic if and only if `P` is even
(`∀ n : ℤ, P.oddPart n = 0`). -/
theorem quasipoly_period1_eulerProduct_iff (P : Quasipoly) (hM : P.M = 1) :
    ¬ AlgebraicIndependent ℂ (seriesCoordinates (eulerProduct (fun n => P.eval (n : ℤ)))) ↔
      ∀ n : ℤ, P.oddPart n = 0 := by
  constructor
  · intro hdep n
    by_contra hne
    exact hdep (quasipoly_eulerProduct_algebraicIndependent P ⟨n, hne⟩ (Eventually.of_forall fun _ => rfl))
  · intro heven
    have hodd0 := (period1_oddPart_eq_zero_iff P hM).mp heven
    let S : Finset ℕ+ := {1}
    have hH_mem : embPS (lambertSeries (fun n => P.eval (n : ℤ))) ∈ genPS (qmGen S) := by
      have hrew : lambertSeries (fun n => P.eval (n : ℤ)) =
          ∑ d : Fin (P.D + 1), PowerSeries.C (P.c d 0) * sigmaSeries (d.1 + 1) := by
        have hfun : (fun n : ℕ => P.eval (n : ℤ)) =
            fun n : ℕ => ∑ d : Fin (P.D + 1), P.c d 0 * (n : ℂ) ^ d.1 := by
          funext n
          rw [P.eval_nat n]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [← P.periodic_mod d n, hM, Nat.mod_one]
        rw [hfun, lambertSeries_finset_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [lambertSeries_const_mul, lambertSeries_pow]
      rw [hrew, map_sum]
      refine (genPS (qmGen S)).sum_mem fun d _ => ?_
      rcases Nat.even_or_odd d.1 with ⟨k, hk⟩ | hodd
      · rw [map_mul]
        refine (genPS (qmGen S)).mul_mem (embPS_C_mem _ (P.c d 0)) ?_
        have h2k : d.1 + 1 = 2 * k + 1 := by omega
        rw [h2k]
        exact sigmaSeries_odd_mem_qmGen_one (Finset.mem_singleton_self 1) k
      · rw [hodd0 d hodd, map_zero, zero_mul, map_zero]
        exact (genPS (qmGen S)).zero_mem
    exact dAlgebraic_of_log_deriv_mem_diff_gen (qmGen S) (qmGen_X_mem S) (qmGen_closed S) hH_mem
      (eulerProduct_ode _)

private lemma period2_oddPart_eq_zero_iff (P : Quasipoly) (hM : P.M = 2) :
    (∀ n : ℤ, P.oddPart n = 0) ↔ ∀ d : Fin (P.D + 1), Odd d.1 → P.c d 0 = 0 ∧ P.c d 1 = 0 := by
  constructor
  · intro hall d hodd
    have hpoly_zero : ∀ r : ℕ, r < 2 → P.cOdd d r = 0 := by
      intro r hr
      let Q : Polynomial ℂ := ∑ e : Fin (P.D + 1), Polynomial.C (P.cOdd e r) * Polynomial.X ^ e.1
      have hQ_eval : ∀ k : ℕ, Q.eval (((2 * k + r : ℕ) : ℂ)) = 0 := by
        intro k
        have h1 := hall ((2 * k + r : ℕ) : ℤ)
        rw [P.oddPart_eq_sum_cOdd] at h1
        have hmod : ((((2 * k + r : ℕ) : ℤ) % (P.M : ℤ)).toNat) = r := by
          rw [hM]; omega
        simp_rw [hmod] at h1
        change Polynomial.evalRingHom (((2 * k + r : ℕ) : ℂ)) Q = 0
        dsimp only [Q]
        rw [map_sum]
        simpa [Polynomial.eval_C, Polynomial.eval_X] using h1
      have hQ0 : Q = 0 := by
        by_contra hne
        have hfin : (Q.roots.toFinset : Set ℂ).Finite := Finset.finite_toSet _
        have hinj : Function.Injective (fun k : ℕ => ((2 * k + r : ℕ) : ℂ)) := fun a b hab => by
          have : 2 * a + r = 2 * b + r := Nat.cast_injective hab; omega
        have hinf : (Set.range (fun k : ℕ => ((2 * k + r : ℕ) : ℂ))).Infinite :=
          Set.infinite_range_of_injective hinj
        obtain ⟨z, ⟨k, rfl⟩, hnot⟩ := (hinf.sdiff hfin).nonempty
        have hroot : ((2 * k + r : ℕ) : ℂ) ∈ Q.roots.toFinset := by
          rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
          exact hQ_eval k
        exact hnot hroot
      have hc0 := congrArg (fun R : Polynomial ℂ => Polynomial.lcoeff ℂ d.1 R) hQ0
      rw [map_zero] at hc0
      dsimp only [Q] at hc0
      rw [map_sum] at hc0
      simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        mul_ite, mul_one, mul_zero] at hc0
      have hsum : (∑ e : Fin (P.D + 1), if d.1 = e.1 then P.cOdd e r else 0) = P.cOdd d r := by
        rw [Finset.sum_eq_single d]
        · simp
        · intro e _ hne; exact ite_eq_right_iff.mpr fun h => (hne (Fin.ext h.symm)).elim
        · intro h; exact absurd (Finset.mem_univ d) h
      rwa [hsum] at hc0
    constructor
    · have h0 := hpoly_zero 0 (by omega)
      unfold Quasipoly.cOdd at h0
      rw [Nat.zero_mod, Nat.sub_zero, P.periodic_M, hodd.neg_one_pow] at h0
      linear_combination h0
    · have h1 := hpoly_zero 1 (by omega)
      unfold Quasipoly.cOdd at h1
      rw [hM, Nat.mod_eq_of_lt (by omega : 1 < 2), show 2 - 1 = 1 by rfl, hodd.neg_one_pow] at h1
      linear_combination h1
  · intro hzero n
    rw [P.oddPart_eq_sum_cOdd]
    refine Finset.sum_eq_zero fun d _ => ?_
    have hr : (n % (P.M : ℤ)).toNat = 0 ∨ (n % (P.M : ℤ)).toNat = 1 := by rw [hM]; omega
    rcases hr with hr0 | hr1
    · rw [hr0]
      rcases Nat.even_or_odd d.1 with he | ho
      · have h0 : P.cOdd d 0 = 0 := by
          unfold Quasipoly.cOdd; rw [Nat.zero_mod, Nat.sub_zero, P.periodic_M, he.neg_one_pow]; ring
        rw [h0, zero_mul]
      · have h0 : P.cOdd d 0 = 0 := by
          unfold Quasipoly.cOdd; rw [Nat.zero_mod, Nat.sub_zero, P.periodic_M, ho.neg_one_pow, (hzero d ho).1]; ring
        rw [h0, zero_mul]
    · rw [hr1]
      rcases Nat.even_or_odd d.1 with he | ho
      · have h0 : P.cOdd d 1 = 0 := by
          unfold Quasipoly.cOdd; rw [hM, Nat.mod_eq_of_lt (by omega : 1 < 2), show 2 - 1 = 1 by rfl, he.neg_one_pow]; ring
        rw [h0, zero_mul]
      · have h0 : P.cOdd d 1 = 0 := by
          unfold Quasipoly.cOdd; rw [hM, Nat.mod_eq_of_lt (by omega : 1 < 2), show 2 - 1 = 1 by rfl, ho.neg_one_pow, (hzero d ho).2]; ring
        rw [h0, zero_mul]

private lemma period2_lambert_mem_qmGen (P : Quasipoly) (hM : P.M = 2)
    (heven : ∀ n : ℤ, P.oddPart n = 0) :
    embPS (lambertSeries (fun n => P.eval (n : ℤ))) ∈ genPS (qmGen ({1, 2} : Finset ℕ+)) := by
  have hodd0 := (period2_oddPart_eq_zero_iff P hM).mp heven
  let S : Finset ℕ+ := {1, 2}
  have h1S : (1 : ℕ+) ∈ S := by simp [S]
  have h2S : (2 : ℕ+) ∈ S := by simp [S]
  have hrew : lambertSeries (fun n => P.eval (n : ℤ)) =
      ∑ d : Fin (P.D + 1),
        (PowerSeries.C (P.c d 1) * sigmaSeries (d.1 + 1) +
          PowerSeries.C ((P.c d 0 - P.c d 1) * (2 : ℂ) ^ (d.1 + 1)) *
            PowerSeries.expand 2 (by norm_num) (sigmaSeries (d.1 + 1))) := by
    have hfun : (fun n : ℕ => P.eval (n : ℤ)) =
        fun n : ℕ => ∑ d : Fin (P.D + 1),
          (P.c d 1 * (n : ℂ) ^ d.1 + (P.c d 0 - P.c d 1) * (if 2 ∣ n then (n : ℂ) ^ d.1 else 0)) := by
      funext n
      rw [P.eval_nat n]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [← P.periodic_mod d n, hM]
      by_cases h2 : 2 ∣ n
      · have hmod : n % 2 = 0 := Nat.mod_eq_zero_of_dvd h2
        rw [hmod, ite_eq_left_iff.mpr fun h => (h h2).elim]; ring
      · have hmod : n % 2 = 1 := by omega
        rw [hmod, ite_eq_right_iff.mpr fun h => (h2 h).elim]; ring
    rw [hfun, lambertSeries_finset_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hadd : lambertSeries (fun n => P.c d 1 * (n : ℂ) ^ d.1 +
        (P.c d 0 - P.c d 1) * (if 2 ∣ n then (n : ℂ) ^ d.1 else 0)) =
        lambertSeries (fun n => P.c d 1 * (n : ℂ) ^ d.1) +
        lambertSeries (fun n => (P.c d 0 - P.c d 1) * (if 2 ∣ n then (n : ℂ) ^ d.1 else 0)) := by
      ext n; simp only [coeff_lambertSeries, map_add]; split_ifs with hn
      · simp
      · simp_rw [mul_add, Finset.sum_add_distrib]
    rw [hadd, lambertSeries_const_mul, lambertSeries_pow, lambertSeries_const_mul,
      lambertSeries_mul_dvd (by norm_num : 0 < 2) d.1, ← mul_assoc, ← map_mul]
    simp
  rw [hrew, map_sum]
  refine (genPS (qmGen S)).sum_mem fun d _ => ?_
  rcases Nat.even_or_odd d.1 with ⟨k, hk⟩ | hodd
  · have h2k : d.1 + 1 = 2 * k + 1 := by omega
    rw [h2k, map_add, map_mul, map_mul]
    refine (genPS (qmGen S)).add_mem
      ((genPS (qmGen S)).mul_mem (embPS_C_mem _ (P.c d 1)) (sigmaSeries_odd_mem_qmGen_one h1S k))
      ((genPS (qmGen S)).mul_mem (embPS_C_mem _ ((P.c d 0 - P.c d 1) * (2 : ℂ) ^ (2 * k + 1)))
        (expand_sigmaSeries_odd_mem_qmGen h2S k))
  · rw [(hodd0 d hodd).1, (hodd0 d hodd).2, sub_self, zero_mul, map_zero, zero_mul, zero_mul,
      add_zero, map_zero]
    exact (genPS (qmGen S)).zero_mem

/-- **Complete Unconditional `IFF` Theorem for ALL Period-2 Quasipolynomials (`M = 2`) — Lambert Series**:
For any period-2 quasipolynomial `P` (`P.M = 2`), its Lambert series `H_P(q)` is D-algebraic
if and only if `P` is even (`∀ n : ℤ, P.oddPart n = 0`). -/
theorem quasipoly_period2_lambert_iff (P : Quasipoly) (hM : P.M = 2) :
    ¬ AlgebraicIndependent ℂ (seriesCoordinates (lambertSeries (fun n => P.eval (n : ℤ)))) ↔
      ∀ n : ℤ, P.oddPart n = 0 := by
  constructor
  · intro hdep n
    by_contra hne
    exact hdep (quasipoly_lambert_pure_algebraicIndependent P ⟨n, hne⟩)
  · intro heven
    exact dAlgebraic_of_mem_diff_gen (qmGen ({1, 2} : Finset ℕ+))
      (qmGen_X_mem _) (qmGen_closed _) (period2_lambert_mem_qmGen P hM heven)

/-- **Complete Unconditional `IFF` Theorem for ALL Period-2 Quasipolynomials (`M = 2`) — Euler Products**:
For any period-2 quasipolynomial `P` (`P.M = 2`), its Euler product `G_P(q)` is D-algebraic
if and only if `P` is even (`∀ n : ℤ, P.oddPart n = 0`). -/
theorem quasipoly_period2_eulerProduct_iff (P : Quasipoly) (hM : P.M = 2) :
    ¬ AlgebraicIndependent ℂ (seriesCoordinates (eulerProduct (fun n => P.eval (n : ℤ)))) ↔
      ∀ n : ℤ, P.oddPart n = 0 := by
  constructor
  · intro hdep n
    by_contra hne
    exact hdep (quasipoly_eulerProduct_algebraicIndependent P ⟨n, hne⟩ (Eventually.of_forall fun _ => rfl))
  · intro heven
    exact dAlgebraic_of_log_deriv_mem_diff_gen (qmGen ({1, 2} : Finset ℕ+))
      (qmGen_X_mem _) (qmGen_closed _) (period2_lambert_mem_qmGen P hM heven) (eulerProduct_ode _)

/-! #### 1E. Concrete D-Algebraic Showcases & Complete Dichotomy Contrasts -/

/-- **Ordinary Partitions `p(q) = ∏_{n ≥ 1} (1 - q^n)^{-1}` are D-Algebraic**:
Directly witnessed by `M = 1`, `P(n) = 1` (`L₁ = (1 - E₂)/24`). -/
theorem ordinaryPartitions_dAlgebraic :
    ¬ AlgebraicIndependent ℂ (seriesCoordinates (PakPrimes.HarmonicTrap.bose (fun _ => 1))) := by
  rw [← eulerProduct_eq_bose]
  let P : Quasipoly := ⟨1, by norm_num, 0, fun _ _ => 1, fun _ _ => rfl⟩
  have hfun : (fun n : ℕ => ((1 : ℕ) : ℂ)) = fun n : ℕ => P.eval (n : ℤ) := by
    funext n; rw [P.eval_nat n]; simp [P]
  rw [hfun]
  refine (quasipoly_period1_eulerProduct_iff P rfl).mpr fun n => ?_
  unfold Quasipoly.oddPart Quasipoly.eval P; simp

/-- **Odd-Parts / Distinct-Parts Partitions `∏_{2 ∤ n} (1 - q^n)^{-1}` are D-Algebraic**:
Directly witnessed by `M = 2`, `P(n) = 1_{2 ∤ n}` (`H = L₁(q) - 2 L₁(q²)`). -/
theorem oddPartsPartitions_dAlgebraic :
    ¬ AlgebraicIndependent ℂ
      (seriesCoordinates (PakPrimes.HarmonicTrap.bose (fun n => if n % 2 = 1 then 1 else 0))) := by
  rw [← eulerProduct_eq_bose]
  let P : Quasipoly := ⟨2, by norm_num, 0, fun _ n => if n % 2 = 1 then 1 else 0, fun _ n => by simp⟩
  have hfun : (fun n : ℕ => ((if n % 2 = 1 then (1 : ℕ) else 0 : ℕ) : ℂ)) = fun n : ℕ => P.eval (n : ℤ) := by
    funext n; rw [P.eval_nat n]; simp only [P]
    rw [Fin.sum_univ_one]; simp only [Fin.val_zero, pow_zero, mul_one]
    split_ifs <;> simp
  rw [hfun]
  refine (quasipoly_period2_eulerProduct_iff P rfl).mpr fun n => ?_
  unfold Quasipoly.oddPart Quasipoly.eval P
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  have hmod : ((-n) % (2 : ℤ)).toNat = (n % (2 : ℤ)).toNat := by congr 1; omega
  simp only [Fin.val_zero, pow_zero, mul_one, Nat.cast_ofNat, hmod, sub_self, zero_div]

/-- **Non-5-Divisible Partitions `∏_{5 ∤ n} (1 - q^n)^{-1}` (Product of Rogers–Ramanujan `±1` & `±2 mod 5`)
are D-Algebraic**: `H(q) = L₁(q) - 5 L₁(q⁵)` lies in `genPS (qmGen {1, 5})`. -/
theorem nonMultipleOf5Partitions_dAlgebraic :
    ¬ AlgebraicIndependent ℂ
      (seriesCoordinates (PakPrimes.HarmonicTrap.bose (fun n => if n % 5 ≠ 0 then 1 else 0))) := by
  rw [← eulerProduct_eq_bose]
  let S : Finset ℕ+ := {1, 5}
  have h1S : (1 : ℕ+) ∈ S := by simp [S]
  have h5S : (5 : ℕ+) ∈ S := by simp [S]
  have hH_eq : lambertSeries (fun n => ((if n % 5 ≠ 0 then (1 : ℕ) else 0 : ℕ) : ℂ)) =
      sigmaSeries 1 - PowerSeries.C (5 : ℂ) * PowerSeries.expand 5 (by norm_num) (sigmaSeries 1) := by
    have hfun : (fun n : ℕ => ((if n % 5 ≠ 0 then (1 : ℕ) else 0 : ℕ) : ℂ)) =
        fun n : ℕ => (n : ℂ) ^ 0 + (-1 : ℂ) * (if 5 ∣ n then (n : ℂ) ^ 0 else 0) := by
      funext n
      by_cases h5 : 5 ∣ n
      · have hmod : n % 5 = 0 := Nat.mod_eq_zero_of_dvd h5
        simp [h5, hmod]
      · have hmod : n % 5 ≠ 0 := fun h => h5 (Nat.dvd_of_mod_eq_zero h)
        simp [h5, hmod]
    rw [hfun]
    have hadd : lambertSeries (fun n => (n : ℂ) ^ 0 + (-1 : ℂ) * (if 5 ∣ n then (n : ℂ) ^ 0 else 0)) =
        lambertSeries (fun n => (n : ℂ) ^ 0) +
        lambertSeries (fun n => (-1 : ℂ) * (if 5 ∣ n then (n : ℂ) ^ 0 else 0)) := by
      ext n; simp only [coeff_lambertSeries, map_add]; split_ifs with hn
      · simp
      · simp_rw [mul_add, Finset.sum_add_distrib]
    rw [hadd, lambertSeries_pow, lambertSeries_const_mul, lambertSeries_mul_dvd (by norm_num : 0 < 5) 0]
    simp only [← mul_assoc, ← map_mul, neg_one_mul]
    ext n; simp [sub_eq_add_neg]
  have hH_mem : embPS (lambertSeries (fun n => ((if n % 5 ≠ 0 then (1 : ℕ) else 0 : ℕ) : ℂ))) ∈
      genPS (qmGen S) := by
    rw [hH_eq, map_sub, map_mul]
    exact (genPS (qmGen S)).sub_mem (sigmaSeries_odd_mem_qmGen_one h1S 0)
      ((genPS (qmGen S)).mul_mem (embPS_C_mem _ (5 : ℂ)) (expand_sigmaSeries_odd_mem_qmGen h5S 0))
  exact dAlgebraic_of_log_deriv_mem_diff_gen (qmGen S) (qmGen_X_mem S) (qmGen_closed S) hH_mem
    (eulerProduct_ode _)

/-- **Centered 3D Harmonic Trap (`3/2` Zero-Point) is D-Algebraic**:
Both `eulerProduct centeredTrap3DQP.eval` and the literal infinite Bose product
`PakPrimes.HarmonicTrap.bose PakPrimes.HarmonicTrap.centeredDeg` are unconditionally D-algebraic! -/
theorem centeredTrap3D_dAlgebraic :
    ¬ AlgebraicIndependent ℂ (seriesCoordinates (eulerProduct (fun n => centeredTrap3DQP.eval (n : ℤ)))) :=
  (quasipoly_period2_eulerProduct_iff centeredTrap3DQP rfl).mpr centeredTrap3D_oddPart_eq_zero

theorem centeredTrap3D_bose_dAlgebraic :
    ¬ AlgebraicIndependent ℂ
      (seriesCoordinates (PakPrimes.HarmonicTrap.bose PakPrimes.HarmonicTrap.centeredDeg)) := by
  rw [← eulerProduct_eq_bose]
  have hfun : (fun n : ℕ => (PakPrimes.HarmonicTrap.centeredDeg n : ℂ)) =
      fun n : ℕ => centeredTrap3DQP.eval (n : ℤ) := by
    funext n
    rw [centeredTrap3DQP.eval_nat n]
    unfold PakPrimes.HarmonicTrap.centeredDeg centeredTrap3DQP
    rw [Fin.sum_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, mul_one]
    by_cases hodd : n % 2 = 1
    · have hndvd : ¬ (2 ∣ n) := by omega
      simp only [hodd, hndvd, ↓reduceIte]
      have hch2 : 2 * (n / 2 + 1).choose 2 = (n / 2 + 1) * (n / 2) := by
        have hd := Nat.descFactorial_eq_factorial_mul_choose (n / 2 + 1) 2
        simp [Nat.descFactorial, Nat.factorial] at hd
        linarith
      have hq : n = 2 * (n / 2) + 1 := by omega
      have h8 : 8 * (n / 2 + 1).choose 2 + 1 = n ^ 2 := by nlinarith
      have h8c : (8 : ℂ) * (((n / 2 + 1).choose 2 : ℕ) : ℂ) + 1 = (n : ℂ) ^ 2 := by
        exact_mod_cast h8
      norm_num
      linear_combination (1 / 8 : ℂ) * h8c
    · have hdvd : 2 ∣ n := by omega
      simp [hodd, hdvd]
  rw [hfun]
  exact centeredTrap3D_dAlgebraic

/-- **`S³` Conformal Scalar (`Z_{S³}(q) = ∏ (1 - q^n)^{-n²}`) is D-Algebraic** via `M = 1` `IFF`. -/
theorem conformalScalarS3_dAlgebraic :
    ¬ AlgebraicIndependent ℂ (seriesCoordinates (eulerProduct (fun n => conformalScalarS3QP.eval (n : ℤ)))) :=
  (quasipoly_period1_eulerProduct_iff conformalScalarS3QP rfl).mpr conformalScalarS3_oddPart_eq_zero

/-- **Ehrhart Quotient (`∏ (1 - q^n)^{-2}`) is D-Algebraic** via `M = 1` `IFF`. -/
theorem ehrhartSegmentQuotient_dAlgebraic :
    ¬ AlgebraicIndependent ℂ
      (seriesCoordinates (eulerProduct (fun n => ehrhartSegmentQuotientQP.eval (n : ℤ)))) :=
  (quasipoly_period1_eulerProduct_iff ehrhartSegmentQuotientQP rfl).mpr ehrhartSegment_quotient_oddPart_eq_zero

/-- **Unified Parity-Dichotomy `IFF` Showcase**:
Contrasts D-algebraic even-parity products against D-transcendental odd-parity counterparts across
number theory, ultracold harmonic traps, conformal field theory on spheres, and Ehrhart theory. -/
theorem quasipoly_parity_dichotomy_showcase :
    -- 1. Partitions: ordinary & non-5-divisible (D-alg) vs parts ≡ 1 mod 5 (D-trans)
    (¬ AlgebraicIndependent ℂ (seriesCoordinates (PakPrimes.HarmonicTrap.bose (fun _ => 1)))) ∧
    (¬ AlgebraicIndependent ℂ (seriesCoordinates (PakPrimes.HarmonicTrap.bose (fun n => if n % 5 ≠ 0 then 1 else 0)))) ∧
    AlgebraicIndependent ℂ (seriesCoordinates (PakPrimes.HarmonicTrap.bose (fun n => if n % 5 = 1 then 1 else 0))) ∧
    -- 2. 3D Harmonic Trap: centered 3/2 zero-point (D-alg) vs shifted by ±1/2 (D-trans)
    (¬ AlgebraicIndependent ℂ (seriesCoordinates (PakPrimes.HarmonicTrap.bose PakPrimes.HarmonicTrap.centeredDeg))) ∧
    AlgebraicIndependent ℂ (seriesCoordinates (PakPrimes.HarmonicTrap.bose (fun n => (n + 1).choose 2))) ∧
    AlgebraicIndependent ℂ (seriesCoordinates (PakPrimes.HarmonicTrap.bose (fun n => n.choose 2))) ∧
    -- 3. Sphere Conformal Scalar: S³ (D-alg) vs S² (D-trans)
    (¬ AlgebraicIndependent ℂ (seriesCoordinates (eulerProduct (fun n => conformalScalarS3QP.eval (n : ℤ))))) ∧
    AlgebraicIndependent ℂ (seriesCoordinates (PakPrimes.HarmonicTrap.bose (fun n => if n % 2 = 1 then n else 0))) ∧
    -- 4. Ehrhart [0, 1]: quotient (D-alg) vs boundary & interior (D-trans)
    (¬ AlgebraicIndependent ℂ (seriesCoordinates (eulerProduct (fun n => ehrhartSegmentQuotientQP.eval (n : ℤ))))) ∧
    AlgebraicIndependent ℂ (seriesCoordinates (PakPrimes.HarmonicTrap.bose (fun n => n + 1))) :=
  ⟨ordinaryPartitions_dAlgebraic, nonMultipleOf5Partitions_dAlgebraic, partsMod5One_algebraicIndependent,
   centeredTrap3D_bose_dAlgebraic, shiftedTrap3D_plus_algebraicIndependent, shiftedTrap3D_minus_algebraicIndependent,
   conformalScalarS3_dAlgebraic, conformalScalarS2_algebraicIndependent,
   ehrhartSegmentQuotient_dAlgebraic, ehrhartSegment_algebraicIndependent⟩

/-! ### Part 2: Nesterenko-Style Joint Differential Independence over `ℂ(q)` -/

/-! #### 2A. Joint Differential Coordinates, Quotient Partial Derivatives, `q`-Elimination, and Kolchin–Ostrowski Transfer -/

/-- Joint differential jet coordinates of a `K`-tuple of formal power series `H : Fin K → PowerSeries ℂ`:
`none ↦ X`, `some (i, j) ↦ derivative^[j] (H i)`.
`AlgebraicIndependent ℂ (jointCoords H)` expresses that `(H 0, ..., H (K-1))` satisfy no nonzero
joint algebraic differential equation over `ℂ(X)`. -/
@[expose] def jointCoords {K : ℕ} (H : Fin K → PowerSeries ℂ) : Option (Fin K × ℕ) → PowerSeries ℂ
  | none => PowerSeries.X
  | some (i, j) => PowerSeries.derivative^[j] (H i)

/-- Restricting a jointly differentially independent tuple along any injection `e : Fin L → Fin K`
preserves joint differential independence. -/
theorem jointCoords_algIndep_comp {K L : ℕ} {H : Fin K → PowerSeries ℂ}
    (hH : AlgebraicIndependent ℂ (jointCoords H)) (e : Fin L → Fin K) (he : Function.Injective e) :
    AlgebraicIndependent ℂ (jointCoords (H ∘ e)) := by
  let f : Option (Fin L × ℕ) → Option (Fin K × ℕ) := Option.map (Prod.map e id)
  have hf : Function.Injective f := Option.map_injective fun a b hab => by
    rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
    simp only [Prod.map_apply, id_eq, Prod.mk.injEq] at hab
    exact Prod.ext (he hab.1) hab.2
  have hcomp : jointCoords (H ∘ e) = (jointCoords H) ∘ f := by
    funext x; cases x <;> rfl
  rw [hcomp]
  exact hH.comp f hf

section PderivFrac

variable {σ : Type}

private lemma mvpoly_pderiv_comm (u v : σ) (P : MvPolynomial σ ℂ) :
    MvPolynomial.pderiv u (MvPolynomial.pderiv v P) = MvPolynomial.pderiv v (MvPolynomial.pderiv u P) := by
  classical
  ext m
  simp only [MvPolynomial.coeff_pderiv]
  have hadd : m + Finsupp.single u 1 + Finsupp.single v 1 = m + Finsupp.single v 1 + Finsupp.single u 1 := by
    abel
  rw [hadd]
  by_cases huv : u = v
  · subst huv; ring
  · have h1 : (m + Finsupp.single u 1 : σ →₀ ℕ) v = m v := by
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm huv), add_zero]
    have h2 : (m + Finsupp.single v 1 : σ →₀ ℕ) u = m u := by
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne huv, add_zero]
    rw [h1, h2]; ring

private lemma mvpoly_pderiv_eq_zero_of_notMem_vars {v : σ} {P : MvPolynomial σ ℂ} (hv : v ∉ P.vars) :
    MvPolynomial.pderiv v P = 0 := by
  classical
  ext m
  simp only [MvPolynomial.coeff_pderiv, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  have h0 : P.coeff (m + Finsupp.single v 1) = 0 := by
    by_contra hne
    apply hv
    rw [MvPolynomial.mem_vars_iff_mem_support]
    refine ⟨m + Finsupp.single v 1, MvPolynomial.mem_support_iff.mpr hne, ?_⟩
    rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  rw [h0, zero_mul]

private lemma mvpoly_vars_pderiv_subset (v : σ) (P : MvPolynomial σ ℂ) :
    (MvPolynomial.pderiv v P).vars ⊆ P.vars := by
  classical
  intro u hu
  rw [MvPolynomial.mem_vars_iff_mem_support] at hu ⊢
  obtain ⟨m, hm, hmu⟩ := hu
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hm
  have hne : P.coeff (m + Finsupp.single v 1) ≠ 0 := left_ne_zero_of_mul hm
  refine ⟨m + Finsupp.single v 1, MvPolynomial.mem_support_iff.mpr hne, ?_⟩
  rw [Finsupp.mem_support_iff] at hmu ⊢
  rw [Finsupp.add_apply]
  omega

private lemma mvpoly_aeval_eq_of_eq_on_vars {R : Type*} [CommSemiring R] [Algebra ℂ R]
    {f g : σ → R} {P : MvPolynomial σ ℂ} (h : ∀ v ∈ P.vars, f v = g v) :
    MvPolynomial.aeval f P = MvPolynomial.aeval g P := by
  classical
  rw [P.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [MvPolynomial.aeval_monomial, Finsupp.prod]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  have hvP : v ∈ P.vars := by
    rw [MvPolynomial.mem_vars_iff_mem_support]
    exact ⟨m, hm, hv⟩
  rw [h v hvP]

private lemma localization_mk_eq_div (a : MvPolynomial σ ℂ) (b : nonZeroDivisors (MvPolynomial σ ℂ)) :
    (Localization.mk a b : FractionRing (MvPolynomial σ ℂ)) =
      algebraMap (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ)) a /
        algebraMap (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ)) (b : MvPolynomial σ ℂ) := by
  set ι := algebraMap (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ))
  have hb : ι b ≠ 0 := (map_ne_zero_iff ι (IsFractionRing.injective _ _)).mpr (nonZeroDivisors.ne_zero b.2)
  refine (eq_div_iff hb).mpr ?_
  have h1 : ι (b : MvPolynomial σ ℂ) = Localization.mk (b : MvPolynomial σ ℂ) 1 :=
    (Localization.mk_one_eq_algebraMap _).symm
  have h2 : ι a = Localization.mk a 1 := (Localization.mk_one_eq_algebraMap _).symm
  rw [h1, h2, Localization.mk_mul, mul_one]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_iff_exists.mpr ⟨1, by simp; ring⟩)

/-- Partial derivative extended to `FractionRing (MvPolynomial σ ℂ)` by the quotient rule. -/
private def pderivFrac (v : σ) :
    FractionRing (MvPolynomial σ ℂ) → FractionRing (MvPolynomial σ ℂ) :=
  let ι := algebraMap (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ))
  fun x => Localization.liftOn x
    (fun a b => (ι (MvPolynomial.pderiv v a) * ι b - ι a * ι (MvPolynomial.pderiv v b)) / (ι b) ^ 2)
    (by
      intro a₁ a₂ b₁ b₂ h
      have hrel : a₁ * (b₂ : MvPolynomial σ ℂ) = a₂ * (b₁ : MvPolynomial σ ℂ) := by
        obtain ⟨c, hc⟩ := Localization.r_iff_exists.mp h
        have hc0 : (c : MvPolynomial σ ℂ) ≠ 0 := nonZeroDivisors.ne_zero c.2
        exact mul_left_cancel₀ hc0 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hc)
      have hb₁ : ι b₁ ≠ 0 := (map_ne_zero_iff ι (IsFractionRing.injective _ _)).mpr (nonZeroDivisors.ne_zero b₁.2)
      have hb₂ : ι b₂ ≠ 0 := (map_ne_zero_iff ι (IsFractionRing.injective _ _)).mpr (nonZeroDivisors.ne_zero b₂.2)
      have hder := congrArg (MvPolynomial.pderiv v) hrel
      simp only [Derivation.leibniz, smul_eq_mul] at hder
      have hrel' := congrArg ι hrel
      have hder' := congrArg ι hder
      simp only [map_add, map_mul] at hrel' hder'
      rw [div_eq_div_iff (pow_ne_zero 2 hb₁) (pow_ne_zero 2 hb₂)]
      linear_combination (ι b₁ * ι b₂) * hder' - (ι b₂ * ι (MvPolynomial.pderiv v b₁) + ι b₁ * ι (MvPolynomial.pderiv v b₂)) * hrel')

private lemma pderivFrac_mk (v : σ) (a : MvPolynomial σ ℂ) (b : nonZeroDivisors (MvPolynomial σ ℂ)) :
    pderivFrac v (Localization.mk a b) =
      (algebraMap _ _ (MvPolynomial.pderiv v a) * algebraMap _ _ (b : MvPolynomial σ ℂ) -
        algebraMap _ _ a * algebraMap _ _ (MvPolynomial.pderiv v (b : MvPolynomial σ ℂ))) /
        (algebraMap _ _ (b : MvPolynomial σ ℂ)) ^ 2 := by
  unfold pderivFrac
  rw [Localization.liftOn_mk]

private lemma pderivFrac_algebraMap (v : σ) (a : MvPolynomial σ ℂ) :
    pderivFrac v (algebraMap (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ)) a) =
      algebraMap _ _ (MvPolynomial.pderiv v a) := by
  have h1 : algebraMap (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ)) a = Localization.mk a 1 :=
    (Localization.mk_one_eq_algebraMap a).symm
  rw [h1, pderivFrac_mk]
  simp

private lemma pderivFrac_C (v : σ) (c : ℂ) :
    pderivFrac v (algebraMap ℂ (FractionRing (MvPolynomial σ ℂ)) c) = 0 := by
  have h : algebraMap ℂ (FractionRing (MvPolynomial σ ℂ)) c =
      algebraMap (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ)) (MvPolynomial.C c) := by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  rw [h, pderivFrac_algebraMap, MvPolynomial.pderiv_C, map_zero]

private lemma pderivFrac_zero (v : σ) :
    pderivFrac v (0 : FractionRing (MvPolynomial σ ℂ)) = 0 := by
  simpa using pderivFrac_C (σ := σ) v 0

private lemma pderivFrac_add (v : σ) (x y : FractionRing (MvPolynomial σ ℂ)) :
    pderivFrac v (x + y) = pderivFrac v x + pderivFrac v y := by
  induction x, y using Localization.induction_on₂ with
  | H ab₁ ab₂ =>
    rcases ab₁ with ⟨a₁, b₁⟩
    rcases ab₂ with ⟨a₂, b₂⟩
    rw [Localization.add_mk, pderivFrac_mk, pderivFrac_mk, pderivFrac_mk]
    set ι := algebraMap (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ))
    have hb₁ : ι b₁ ≠ 0 := (map_ne_zero_iff ι (IsFractionRing.injective _ _)).mpr (nonZeroDivisors.ne_zero b₁.2)
    have hb₂ : ι b₂ ≠ 0 := (map_ne_zero_iff ι (IsFractionRing.injective _ _)).mpr (nonZeroDivisors.ne_zero b₂.2)
    simp only [Submonoid.coe_mul, map_add, map_mul, Derivation.leibniz, smul_eq_mul]
    field_simp [hb₁, hb₂]
    ring

private lemma pderivFrac_mul (v : σ) (x y : FractionRing (MvPolynomial σ ℂ)) :
    pderivFrac v (x * y) = pderivFrac v x * y + x * pderivFrac v y := by
  induction x, y using Localization.induction_on₂ with
  | H ab₁ ab₂ =>
    rcases ab₁ with ⟨a₁, b₁⟩
    rcases ab₂ with ⟨a₂, b₂⟩
    rw [Localization.mk_mul, pderivFrac_mk, pderivFrac_mk, pderivFrac_mk]
    set ι := algebraMap (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ))
    have hb₁ : ι b₁ ≠ 0 := (map_ne_zero_iff ι (IsFractionRing.injective _ _)).mpr (nonZeroDivisors.ne_zero b₁.2)
    have hb₂ : ι b₂ ≠ 0 := (map_ne_zero_iff ι (IsFractionRing.injective _ _)).mpr (nonZeroDivisors.ne_zero b₂.2)
    rw [localization_mk_eq_div a₁ b₁, localization_mk_eq_div a₂ b₂]
    simp only [Submonoid.coe_mul, map_add, map_mul, Derivation.leibniz, smul_eq_mul]
    field_simp [hb₁, hb₂]
    ring

private lemma pderivFrac_sum {ι' : Type*} (v : σ) (s : Finset ι')
    (f : ι' → FractionRing (MvPolynomial σ ℂ)) :
    pderivFrac v (∑ i ∈ s, f i) = ∑ i ∈ s, pderivFrac v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact pderivFrac_zero v
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, pderivFrac_add, ih]

private lemma pderivFrac_neg (v : σ) (x : FractionRing (MvPolynomial σ ℂ)) :
    pderivFrac v (-x) = -pderivFrac v x := by
  have h := pderivFrac_mul v (algebraMap ℂ _ (-1 : ℂ)) x
  rw [pderivFrac_C, zero_mul, zero_add, map_neg, map_one, neg_one_mul, neg_one_mul] at h
  exact h

private lemma pderivFrac_sub (v : σ) (x y : FractionRing (MvPolynomial σ ℂ)) :
    pderivFrac v (x - y) = pderivFrac v x - pderivFrac v y := by
  rw [sub_eq_add_neg, pderivFrac_add, pderivFrac_neg, ← sub_eq_add_neg]

private lemma pderivFrac_comm (u v : σ) (x : FractionRing (MvPolynomial σ ℂ)) :
    pderivFrac u (pderivFrac v x) = pderivFrac v (pderivFrac u x) := by
  induction x using Localization.induction_on with
  | H ab =>
    rcases ab with ⟨a, b⟩
    set ι := algebraMap (MvPolynomial σ ℂ) (FractionRing (MvPolynomial σ ℂ))
    have hb : ι b ≠ 0 := (map_ne_zero_iff ι (IsFractionRing.injective _ _)).mpr (nonZeroDivisors.ne_zero b.2)
    have hdiv : ∀ (p q : MvPolynomial σ ℂ) (hq : ι q ≠ 0) (w : σ),
        pderivFrac w (ι p / ι q) =
          (ι (MvPolynomial.pderiv w p) * ι q - ι p * ι (MvPolynomial.pderiv w q)) / (ι q) ^ 2 := by
      intro p q hq w
      have hq0 : q ∈ nonZeroDivisors (MvPolynomial σ ℂ) := by
        rw [mem_nonZeroDivisors_iff_ne_zero]
        intro h0; exact hq (by rw [h0, map_zero])
      have heq : ι p / ι q = Localization.mk p ⟨q, hq0⟩ := (localization_mk_eq_div p ⟨q, hq0⟩).symm
      rw [heq, pderivFrac_mk]
    rw [pderivFrac_mk, pderivFrac_mk]
    have hnum_v : ι (MvPolynomial.pderiv v a) * ι b - ι a * ι (MvPolynomial.pderiv v b) =
        ι (MvPolynomial.pderiv v a * (b : MvPolynomial σ ℂ) - a * MvPolynomial.pderiv v b) := by
      simp only [map_sub, map_mul]
    have hnum_u : ι (MvPolynomial.pderiv u a) * ι b - ι a * ι (MvPolynomial.pderiv u b) =
        ι (MvPolynomial.pderiv u a * (b : MvPolynomial σ ℂ) - a * MvPolynomial.pderiv u b) := by
      simp only [map_sub, map_mul]
    have hden : (ι b) ^ 2 = ι ((b : MvPolynomial σ ℂ) ^ 2) := (map_pow ι _ 2).symm
    rw [hnum_v, hnum_u, hden, hdiv _ _ (by rw [← hden]; exact pow_ne_zero 2 hb) u,
      hdiv _ _ (by rw [← hden]; exact pow_ne_zero 2 hb) v]
    have h2b : ∀ w : σ, MvPolynomial.pderiv w ((b : MvPolynomial σ ℂ) ^ 2) =
        2 * (b : MvPolynomial σ ℂ) * MvPolynomial.pderiv w b := fun w => by
      rw [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, pow_one]; ring
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, Derivation.leibniz, h2b, smul_eq_mul,
      mvpoly_pderiv_comm u v a, mvpoly_pderiv_comm u v b]
    field_simp [hb]
    ring

private lemma pderivFrac_mk_eq_zero_of_notMem {v : σ} {a : MvPolynomial σ ℂ}
    {b : nonZeroDivisors (MvPolynomial σ ℂ)} (ha : v ∉ a.vars) (hb : v ∉ (b : MvPolynomial σ ℂ).vars) :
    pderivFrac v (Localization.mk a b) = 0 := by
  rw [pderivFrac_mk, mvpoly_pderiv_eq_zero_of_notMem_vars ha, mvpoly_pderiv_eq_zero_of_notMem_vars hb]
  simp

end PderivFrac

/-! #### 2A.1. Pure-Algebra `q`-Elimination (`joint_autonomous_theta_of_dep`) -/

/-- Formal Euler derivation `θ_poly` on `MvPolynomial (Fin K × ℕ) ℂ` sending `X (i, j) ↦ X (i, j + 1)`. -/
private def thetaPoly {K : ℕ} (P : MvPolynomial (Fin K × ℕ) ℂ) : MvPolynomial (Fin K × ℕ) ℂ :=
  ∑ v ∈ P.vars, MvPolynomial.X (v.1, v.2 + 1) * MvPolynomial.pderiv v P

private lemma thetaPoly_eq_sum_superset {K : ℕ} {P : MvPolynomial (Fin K × ℕ) ℂ}
    {s : Finset (Fin K × ℕ)} (hs : P.vars ⊆ s) :
    thetaPoly P = ∑ v ∈ s, MvPolynomial.X (v.1, v.2 + 1) * MvPolynomial.pderiv v P := by
  unfold thetaPoly
  refine Finset.sum_subset hs fun v _ hv => ?_
  rw [mvpoly_pderiv_eq_zero_of_notMem_vars hv, mul_zero]

private lemma thetaPoly_add {K : ℕ} (A B : MvPolynomial (Fin K × ℕ) ℂ) :
    thetaPoly (A + B) = thetaPoly A + thetaPoly B := by
  classical
  let s := A.vars ∪ B.vars
  rw [thetaPoly_eq_sum_superset ((MvPolynomial.vars_add_subset A B).trans Finset.Subset.rfl),
    thetaPoly_eq_sum_superset Finset.subset_union_left,
    thetaPoly_eq_sum_superset Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => by rw [map_add, mul_add]

private lemma thetaPoly_mul {K : ℕ} (A B : MvPolynomial (Fin K × ℕ) ℂ) :
    thetaPoly (A * B) = thetaPoly A * B + A * thetaPoly B := by
  classical
  let s := A.vars ∪ B.vars
  rw [thetaPoly_eq_sum_superset (MvPolynomial.vars_mul A B),
    thetaPoly_eq_sum_superset Finset.subset_union_left,
    thetaPoly_eq_sum_superset Finset.subset_union_right,
    Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring

private lemma thetaPoly_C {K : ℕ} (c : ℂ) : thetaPoly (MvPolynomial.C c : MvPolynomial (Fin K × ℕ) ℂ) = 0 := by
  simp [thetaPoly]

private lemma thetaPoly_X {K : ℕ} (v : Fin K × ℕ) :
    thetaPoly (MvPolynomial.X v : MvPolynomial (Fin K × ℕ) ℂ) = MvPolynomial.X (v.1, v.2 + 1) := by
  classical
  simp [thetaPoly]

private lemma aeval_thetaPoly {K : ℕ} (H : Fin K → PowerSeries ℂ) (P : MvPolynomial (Fin K × ℕ) ℂ) :
    thetaD (MvPolynomial.aeval (fun ij : Fin K × ℕ => thetaD^[ij.2] (H ij.1)) P) =
      MvPolynomial.aeval (fun ij : Fin K × ℕ => thetaD^[ij.2] (H ij.1)) (thetaPoly P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [thetaPoly_C, map_zero, MvPolynomial.aeval_C, Derivation.map_algebraMap]
  | add A B hA hB =>
    rw [thetaPoly_add, map_add, map_add, map_add, hA, hB]
  | mul_X A v hA =>
    rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hA, thetaPoly_mul, thetaPoly_X,
      map_add, map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
      Function.iterate_succ_apply' thetaD v.2 (H v.1)]
    ring

/-- **Key No-Exponential-Log-Derivative Lemma**: No nonzero rational function
`R = B / A ∈ Frac(ℂ[Y_{i, j}])` satisfies `θ(R) / R = c` for a nonzero constant `c ∈ ℂ`. -/
private lemma no_const_logDeriv_thetaPoly {K : ℕ} {A B : MvPolynomial (Fin K × ℕ) ℂ}
    (hA : A ≠ 0) (hB : B ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    A * thetaPoly B - B * thetaPoly A + MvPolynomial.C c * A * B ≠ 0 := by
  classical
  intro h0
  let R := MvPolynomial (Fin K × ℕ) ℂ
  let F := FractionRing R
  set ι : R →+* F := algebraMap R F
  have hA_nz : A ∈ nonZeroDivisors R := mem_nonZeroDivisors_iff_ne_zero.mpr hA
  let x : F := Localization.mk B ⟨A, hA_nz⟩
  have hAι : ι A ≠ 0 := (map_ne_zero_iff ι (IsFractionRing.injective R F)).mpr hA
  have hBι : ι B ≠ 0 := (map_ne_zero_iff ι (IsFractionRing.injective R F)).mpr hB
  have hx_div : x = ι B / ι A := localization_mk_eq_div B ⟨A, hA_nz⟩
  have hx_ne : x ≠ 0 := by
    intro hx0
    rw [hx_div, div_eq_zero_iff] at hx0
    exact hx0.elim hBι hAι
  let S : Finset (Fin K × ℕ) := A.vars ∪ B.vars
  have hsum_eq : ∑ v ∈ S, ι (MvPolynomial.X (v.1, v.2 + 1)) * pderivFrac v x =
      -(algebraMap ℂ F c) * x := by
    have hA_th := thetaPoly_eq_sum_superset (P := A) (s := S) Finset.subset_union_left
    have hB_th := thetaPoly_eq_sum_superset (P := B) (s := S) Finset.subset_union_right
    have hsum_lhs : ∑ v ∈ S, ι (MvPolynomial.X (v.1, v.2 + 1)) * pderivFrac v x =
        (ι A * ι (thetaPoly B) - ι B * ι (thetaPoly A)) / (ι A) ^ 2 := by
      rw [hA_th, hB_th, map_sum, map_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        Finset.sum_div]
      refine Finset.sum_congr rfl fun v _ => ?_
      change ι (MvPolynomial.X (v.1, v.2 + 1)) * pderivFrac v (Localization.mk B ⟨A, hA_nz⟩) = _
      rw [pderivFrac_mk]
      change ι (MvPolynomial.X (v.1, v.2 + 1)) * ((ι (MvPolynomial.pderiv v B) * ι A - ι B * ι (MvPolynomial.pderiv v A)) / ι A ^ 2) = _
      simp only [map_mul]
      field_simp [hAι]
    rw [hsum_lhs, hx_div]
    have h0' := congrArg ι h0
    simp only [map_add, map_sub, map_mul, map_zero] at h0'
    have hC : ι (MvPolynomial.C c) = algebraMap ℂ F c := by
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    rw [hC] at h0'
    field_simp [hAι]
    linear_combination h0'
  -- Check whether any `v ∈ S` has `pderivFrac v x ≠ 0`.
  let active : Finset (Fin K × ℕ) := S.filter fun v => pderivFrac v x ≠ 0
  by_cases hact : active.Nonempty
  · -- Pick `v₀ ∈ active` maximizing `v₀.2`!
    obtain ⟨v₀, hv₀_mem, hv₀_max⟩ := active.exists_max_image Prod.snd hact
    have hv₀_S : v₀ ∈ S := (Finset.mem_filter.mp hv₀_mem).1
    have hv₀_ne : pderivFrac v₀ x ≠ 0 := (Finset.mem_filter.mp hv₀_mem).2
    let w : Fin K × ℕ := (v₀.1, v₀.2 + 1)
    have hw_zero : pderivFrac w x = 0 := by
      by_cases hwS : w ∈ S
      · by_contra hne
        have hw_act : w ∈ active := Finset.mem_filter.mpr ⟨hwS, hne⟩
        have hle := hv₀_max w hw_act
        dsimp only [w] at hle; omega
      · exact pderivFrac_mk_eq_zero_of_notMem (fun h => hwS (Finset.mem_union_right _ h))
          (fun h => hwS (Finset.mem_union_left _ h))
    -- Apply `pderivFrac w` to `hsum_eq`!
    have hdiff := congrArg (pderivFrac w) hsum_eq
    rw [pderivFrac_sum, pderivFrac_mul, pderivFrac_neg, pderivFrac_C, neg_zero, zero_mul, zero_add,
      hw_zero, mul_zero] at hdiff
    have hterm : ∀ v ∈ S, pderivFrac w (ι (MvPolynomial.X (v.1, v.2 + 1)) * pderivFrac v x) =
        if v = v₀ then pderivFrac v₀ x else 0 := by
      intro v _
      rw [pderivFrac_mul, pderivFrac_algebraMap, MvPolynomial.pderiv_X, pderivFrac_comm w v x,
        hw_zero, pderivFrac_zero, mul_zero, add_zero]
      have hiff : (v.1, v.2 + 1) = w ↔ v = v₀ := by
        dsimp only [w]
        constructor
        · intro h
          simp only [Prod.mk.injEq] at h
          exact Prod.ext h.1 (Nat.succ.inj h.2)
        · intro h; subst h; rfl
      by_cases heq : v = v₀
      · subst heq; simp [w]
      · have hne : (v.1, v.2 + 1) ≠ w := mt hiff.mp heq
        simp [hne, heq]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' S v₀, ite_eq_left_iff.mpr (fun h => (h hv₀_S).elim)] at hdiff
    exact hv₀_ne hdiff
  · rw [Finset.not_nonempty_iff_eq_empty] at hact
    have hall0 : ∀ v ∈ S, pderivFrac v x = 0 := by
      intro v hv
      by_contra hne
      have : v ∈ active := Finset.mem_filter.mpr ⟨hv, hne⟩
      rw [hact] at this
      exact Finset.notMem_empty v this
    have hlhs0 : ∑ v ∈ S, ι (MvPolynomial.X (v.1, v.2 + 1)) * pderivFrac v x = 0 :=
      Finset.sum_eq_zero fun v hv => by rw [hall0 v hv, mul_zero]
    rw [hlhs0] at hsum_eq
    have hcF : -(algebraMap ℂ F c) ≠ 0 :=
      neg_ne_zero.mpr ((map_ne_zero_iff (algebraMap ℂ F) (algebraMap ℂ F).injective).mpr hc)
    exact mul_ne_zero hcF hx_ne hsum_eq.symm

/-- Signed Stirling numbers of the first kind `s(j, m)` satisfying
`X^j * D^j F = ∑_{m=0}^j s(j, m) * θ^m F`. -/
private def stirlingCoeff : ℕ → ℕ → ℂ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | j + 1, 0 => -(j : ℂ) * stirlingCoeff j 0
  | j + 1, m + 1 => stirlingCoeff j m - (j : ℂ) * stirlingCoeff j (m + 1)

private lemma stirlingCoeff_self (j : ℕ) : stirlingCoeff j j = 1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hgt : ∀ k m : ℕ, k < m → stirlingCoeff k m = 0 := by
      intro k
      induction k with
      | zero => intro m hm; cases m with | zero => omega | succ r => rfl
      | succ k ihk =>
        intro m hm
        cases m with
        | zero => omega
        | succ r => simp only [stirlingCoeff, ihk r (by omega), ihk (r + 1) (by omega), mul_zero, sub_zero]
    simp only [stirlingCoeff, ih, hgt j (j + 1) (by omega), mul_zero, sub_zero]

private lemma stirlingCoeff_eq_zero_of_lt {j m : ℕ} (h : j < m) : stirlingCoeff j m = 0 := by
  induction j generalizing m with
  | zero => cases m with | zero => omega | succ r => rfl
  | succ j ih =>
    cases m with
    | zero => omega
    | succ r => simp only [stirlingCoeff, ih (by omega : j < r), ih (by omega : j < r + 1), mul_zero, sub_zero]

private lemma X_pow_mul_iteratedDeriv_eq_sum_thetaD (F : PowerSeries ℂ) (j : ℕ) :
    PowerSeries.X ^ j * PowerSeries.derivative^[j] F =
      ∑ m ∈ Finset.range (j + 1), PowerSeries.C (stirlingCoeff j m) * thetaD^[m] F := by
  induction j with
  | zero => simp [stirlingCoeff]
  | succ j ih =>
    have hstep : PowerSeries.X ^ (j + 1) * PowerSeries.derivative^[j + 1] F =
        thetaD (PowerSeries.X ^ j * PowerSeries.derivative^[j] F) -
          PowerSeries.C (j : ℂ) * (PowerSeries.X ^ j * PowerSeries.derivative^[j] F) := by
      rw [thetaD_apply, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
        Function.iterate_succ_apply' PowerSeries.derivative j F]
      have hdX : PowerSeries.derivative (PowerSeries.X ^ j : PowerSeries ℂ) =
          PowerSeries.C (j : ℂ) * PowerSeries.X ^ (j - 1) := by
        cases j with
        | zero => simp
        | succ m =>
          rw [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, PowerSeries.derivative_X, mul_one,
            PowerSeries.C_eq_algebraMap, map_natCast]
      rw [hdX]
      cases j with
      | zero => simp [pow_one]
      | succ m =>
        rw [Nat.succ_sub_one, pow_succ (PowerSeries.X : PowerSeries ℂ) (m + 1),
          pow_succ (PowerSeries.X : PowerSeries ℂ) m]
        ring
    rw [hstep, ih, map_sum, Finset.mul_sum]
    have htheta_term : ∀ m : ℕ,
        thetaD (PowerSeries.C (stirlingCoeff j m) * thetaD^[m] F) =
          PowerSeries.C (stirlingCoeff j m) * thetaD^[m + 1] F := fun m => by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul,
        show thetaD (PowerSeries.C (stirlingCoeff j m)) = 0 from by
          rw [PowerSeries.C_eq_algebraMap]; exact Derivation.map_algebraMap thetaD _,
        mul_zero, add_zero, Function.iterate_succ_apply' thetaD m F]
    simp_rw [htheta_term]
    rw [Finset.sum_range_succ' (fun m => PowerSeries.C (stirlingCoeff (j + 1) m) * thetaD^[m] F) (j + 1)]
    have hsum_shift : ∑ m ∈ Finset.range (j + 1), PowerSeries.C (stirlingCoeff (j + 1) (m + 1)) * thetaD^[m + 1] F =
        (∑ m ∈ Finset.range (j + 1), PowerSeries.C (stirlingCoeff j m) * thetaD^[m + 1] F) -
          ∑ m ∈ Finset.range (j + 1), PowerSeries.C (j : ℂ) * (PowerSeries.C (stirlingCoeff j (m + 1)) * thetaD^[m + 1] F) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [stirlingCoeff, map_sub, map_mul, sub_mul, mul_assoc]
    rw [hsum_shift]
    have hsum_j : ∑ m ∈ Finset.range (j + 1), PowerSeries.C (j : ℂ) * (PowerSeries.C (stirlingCoeff j m) * thetaD^[m] F) =
        PowerSeries.C (j : ℂ) * (PowerSeries.C (stirlingCoeff j 0) * thetaD^[0] F) +
          ∑ m ∈ Finset.range j, PowerSeries.C (j : ℂ) * (PowerSeries.C (stirlingCoeff j (m + 1)) * thetaD^[m + 1] F) := by
      rw [Finset.sum_range_succ', add_comm]
    have hsum_j1 : ∑ m ∈ Finset.range (j + 1), PowerSeries.C (j : ℂ) * (PowerSeries.C (stirlingCoeff j (m + 1)) * thetaD^[m + 1] F) =
        ∑ m ∈ Finset.range j, PowerSeries.C (j : ℂ) * (PowerSeries.C (stirlingCoeff j (m + 1)) * thetaD^[m + 1] F) := by
      rw [Finset.sum_range_succ, stirlingCoeff_eq_zero_of_lt (by omega : j < j + 1), map_zero, zero_mul, mul_zero, add_zero]
    rw [hsum_j, hsum_j1]
    simp only [stirlingCoeff, map_mul, map_neg]
    ring

/-- Recursive polynomial inversion of the Stirling substitution `∑_{m ≤ j} s(j, m) Z_{i, m} = X^j W_{i, j}`:
satisfies `∑_{m ≤ j} s(j, m) * stirlingInvPoly i m = X none ^ j * X (some (i, j))`. -/
private def stirlingInvPoly {K : ℕ} (i : Fin K) : ℕ → MvPolynomial (Option (Fin K × ℕ)) ℂ
  | 0 => MvPolynomial.X (some (i, 0))
  | j + 1 =>
    MvPolynomial.X none ^ (j + 1) * MvPolynomial.X (some (i, j + 1)) -
      ∑ m : Fin (j + 1), MvPolynomial.C (stirlingCoeff (j + 1) m.val) * stirlingInvPoly i m.val

private lemma sum_stirlingCoeff_mul_stirlingInvPoly {K : ℕ} (i : Fin K) (j : ℕ) :
    ∑ m ∈ Finset.range (j + 1), MvPolynomial.C (stirlingCoeff j m) * stirlingInvPoly i m =
      MvPolynomial.X none ^ j * MvPolynomial.X (some (i, j)) := by
  cases j with
  | zero => simp [stirlingCoeff, stirlingInvPoly]
  | succ k =>
    rw [Finset.sum_range_succ, stirlingCoeff_self, map_one, one_mul, stirlingInvPoly,
      Fin.sum_univ_eq_sum_range (fun m => MvPolynomial.C (stirlingCoeff (k + 1) m) * stirlingInvPoly i m)]
    ring

/-- **Pure-Algebra `q`-Elimination (`joint_autonomous_theta_of_dep`)**:
If `H : Fin K → PowerSeries ℂ` is jointly differentially dependent over `ℂ(X)`, then there exist
`r : ℕ` and a nonzero autonomous polynomial `P : MvPolynomial (Fin K × Fin (r + 1)) ℂ` (free of `X`)
such that `MvPolynomial.aeval (fun ij => thetaD^[ij.2.val] (H ij.1)) P = 0`. -/
theorem joint_autonomous_theta_of_dep {K : ℕ} {H : Fin K → PowerSeries ℂ}
    (hdep : ¬ AlgebraicIndependent ℂ (jointCoords H)) :
    ∃ (r : ℕ) (P : MvPolynomial (Fin K × Fin (r + 1)) ℂ),
      P ≠ 0 ∧ MvPolynomial.aeval (fun ij : Fin K × Fin (r + 1) => thetaD^[ij.2.val] (H ij.1)) P = 0 := by
  classical
  rw [algebraicIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨P₀, hP₀_zero, hP₀_ne⟩ := hdep
  -- Step 1: Convert `P₀(X, D^j H_i) = 0` into a nonzero polynomial `Q₀ ∈ ℂ[X, Y_{i, j}]` vanishing at `(X, θ^j H_i)`.
  let S_alg := MvPolynomial (Option (Fin K × ℕ)) ℂ
  let wt (α : Option (Fin K × ℕ) →₀ ℕ) : ℕ :=
    ∑ v ∈ α.support, match v with | none => 0 | some (_, j) => α v * j
  let N : ℕ := P₀.support.sup wt
  have hwt_le : ∀ α ∈ P₀.support, wt α ≤ N := fun α hα => Finset.le_sup hα
  let stirlingSum (i : Fin K) (j : ℕ) : S_alg :=
    ∑ m ∈ Finset.range (j + 1), MvPolynomial.C (stirlingCoeff j m) * MvPolynomial.X (some (i, m))
  let Q₀ : S_alg :=
    ∑ α ∈ P₀.support,
      MvPolynomial.C (P₀.coeff α) * MvPolynomial.X none ^ (N - wt α) *
        ∏ v ∈ α.support, (match v with
          | none => MvPolynomial.X none
          | some (i, j) => stirlingSum i j) ^ (α v)
  -- Show `Q₀ ≠ 0` by applying the left-inverse `ψ : S_alg →ₐ[ℂ] S_alg`!
  let ψ : S_alg →ₐ[ℂ] S_alg :=
    MvPolynomial.aeval fun v : Option (Fin K × ℕ) => match v with
      | none => MvPolynomial.X none
      | some (i, m) => stirlingInvPoly i m
  have hψ_Q₀ : ψ Q₀ = MvPolynomial.X none ^ N * P₀ := by
    dsimp only [Q₀]
    rw [map_sum]
    conv_rhs => rw [P₀.as_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [map_mul, map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, map_pow, MvPolynomial.aeval_X,
      map_prod]
    have hprod : ∏ v ∈ α.support, ψ ((match v with | none => MvPolynomial.X none | some (i, j) => stirlingSum i j) ^ α v) =
        MvPolynomial.X none ^ wt α * ∏ v ∈ α.support, (MvPolynomial.X v : S_alg) ^ α v := by
      have hterm : ∀ v ∈ α.support,
          ψ ((match v with | none => MvPolynomial.X none | some (i, j) => stirlingSum i j) ^ α v) =
            MvPolynomial.X none ^ (match v with | none => 0 | some (_, j) => α v * j) *
              (MvPolynomial.X v : S_alg) ^ α v := by
        intro v _
        rw [map_pow]
        cases v with
        | none => dsimp only [ψ]; rw [MvPolynomial.aeval_X]; simp
        | some ij =>
          rcases ij with ⟨i, j⟩
          dsimp only [stirlingSum]
          rw [map_sum]
          have hsum_eq : ∑ m ∈ Finset.range (j + 1),
              ψ (MvPolynomial.C (stirlingCoeff j m) * MvPolynomial.X (some (i, m))) =
              MvPolynomial.X none ^ j * MvPolynomial.X (some (i, j)) := by
            rw [← sum_stirlingCoeff_mul_stirlingInvPoly i j]
            refine Finset.sum_congr rfl fun m _ => by
              dsimp only [ψ]
              rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq]
          rw [hsum_eq, mul_pow, ← pow_mul, mul_comm j (α (some (i, j)))]
      rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [hprod, MvPolynomial.monomial_eq, Finsupp.prod]
    have hadd : (N - wt α) + wt α = N := Nat.sub_add_cancel (hwt_le α hα)
    calc MvPolynomial.C (P₀.coeff α) * MvPolynomial.X none ^ (N - wt α) *
          (MvPolynomial.X none ^ wt α * ∏ v ∈ α.support, (MvPolynomial.X v : S_alg) ^ α v)
        = MvPolynomial.X none ^ ((N - wt α) + wt α) *
            (MvPolynomial.C (P₀.coeff α) * ∏ v ∈ α.support, (MvPolynomial.X v : S_alg) ^ α v) := by
          rw [pow_add]; ring
      _ = MvPolynomial.X none ^ N *
            (MvPolynomial.C (P₀.coeff α) * ∏ v ∈ α.support, (MvPolynomial.X v : S_alg) ^ α v) := by
          rw [hadd]
  have hQ₀_ne : Q₀ ≠ 0 := by
    intro h0
    have h1 := congrArg ψ h0
    rw [hψ_Q₀, map_zero] at h1
    exact mul_ne_zero (pow_ne_zero N (MvPolynomial.X_ne_zero none)) hP₀_ne h1
  -- Show `aeval (X, θ^j H_i) Q₀ = X^N * aeval (jointCoords H) P₀ = 0`!
  let θCoords : Option (Fin K × ℕ) → PowerSeries ℂ
    | none => PowerSeries.X
    | some (i, j) => thetaD^[j] (H i)
  have hQ₀_zero : MvPolynomial.aeval θCoords Q₀ = 0 := by
    have hval : MvPolynomial.aeval θCoords Q₀ = PowerSeries.X ^ N * MvPolynomial.aeval (jointCoords H) P₀ := by
      dsimp only [Q₀]
      rw [map_sum]
      conv_rhs => rw [P₀.as_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [map_mul, map_mul, MvPolynomial.aeval_C, PowerSeries.algebraMap_eq, map_pow, MvPolynomial.aeval_X,
        map_prod]
      have hprod : ∏ v ∈ α.support,
          MvPolynomial.aeval θCoords ((match v with | none => MvPolynomial.X none | some (i, j) => stirlingSum i j) ^ α v) =
          PowerSeries.X ^ wt α * ∏ v ∈ α.support, (jointCoords H v) ^ α v := by
        have hterm : ∀ v ∈ α.support,
            MvPolynomial.aeval θCoords ((match v with | none => MvPolynomial.X none | some (i, j) => stirlingSum i j) ^ α v) =
              PowerSeries.X ^ (match v with | none => 0 | some (_, j) => α v * j) *
                (jointCoords H v) ^ α v := by
          intro v _
          rw [map_pow]
          cases v with
          | none => simp [θCoords, jointCoords]
          | some ij =>
            rcases ij with ⟨i, j⟩
            dsimp only [stirlingSum]
            rw [map_sum]
            have hst : ∑ m ∈ Finset.range (j + 1),
                MvPolynomial.aeval θCoords (MvPolynomial.C (stirlingCoeff j m) * MvPolynomial.X (some (i, m))) =
                PowerSeries.X ^ j * PowerSeries.derivative^[j] (H i) := by
              rw [X_pow_mul_iteratedDeriv_eq_sum_thetaD]
              refine Finset.sum_congr rfl fun m _ => by simp [θCoords, PowerSeries.algebraMap_eq]
            rw [hst, mul_pow, ← pow_mul, mul_comm j (α (some (i, j)))]
            rfl
        rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      rw [hprod, MvPolynomial.aeval_monomial, PowerSeries.algebraMap_eq, Finsupp.prod]
      have hadd : (N - wt α) + wt α = N := Nat.sub_add_cancel (hwt_le α hα)
      dsimp only [θCoords]
      calc PowerSeries.C (P₀.coeff α) * PowerSeries.X ^ (N - wt α) *
            (PowerSeries.X ^ wt α * ∏ v ∈ α.support, jointCoords H v ^ α v)
          = PowerSeries.X ^ ((N - wt α) + wt α) *
              (PowerSeries.C (P₀.coeff α) * ∏ v ∈ α.support, jointCoords H v ^ α v) := by
            rw [pow_add]; ring
        _ = PowerSeries.X ^ N *
              (PowerSeries.C (P₀.coeff α) * ∏ v ∈ α.support, jointCoords H v ^ α v) := by
            rw [hadd]
    rw [hval, hP₀_zero, mul_zero]
  -- Step 2: View `S_alg ≃ₐ[ℂ] Polynomial (MvPolynomial (Fin K × ℕ) ℂ)` and descend on `X`-support size!
  let R := MvPolynomial (Fin K × ℕ) ℂ
  let eOpt : S_alg ≃ₐ[ℂ] Polynomial R := MvPolynomial.optionEquivLeft ℂ (Fin K × ℕ)
  let evalRX : Polynomial R →+* PowerSeries ℂ :=
    Polynomial.eval₂RingHom (MvPolynomial.aeval (fun ij : Fin K × ℕ => thetaD^[ij.2] (H ij.1))).toRingHom PowerSeries.X
  have heval_eOpt : ∀ Q : S_alg, evalRX (eOpt Q) = MvPolynomial.aeval θCoords Q := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C c =>
      dsimp only [eOpt, evalRX]
      rw [MvPolynomial.optionEquivLeft_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]
    | add A B hA hB => simp only [map_add, hA, hB]
    | mul_X A v hA =>
      rw [map_mul, map_mul, map_mul, hA]
      congr 1
      cases v with
      | none =>
        dsimp only [eOpt, evalRX]
        rw [MvPolynomial.optionEquivLeft_X_none, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
          MvPolynomial.aeval_X]
      | some ij =>
        dsimp only [eOpt, evalRX]
        rw [MvPolynomial.optionEquivLeft_X_some, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  let Q₁ : Polynomial R := eOpt Q₀
  have hQ₁_ne : Q₁ ≠ 0 := fun h0 => hQ₀_ne (eOpt.injective (h0.trans (map_zero eOpt).symm))
  have hQ₁_zero : evalRX Q₁ = 0 := (heval_eOpt Q₀).trans hQ₀_zero
  -- Pick a nonzero `Q : Polynomial R` with `evalRX Q = 0` minimizing `Q.support.card`!
  have hex : ∃ n : ℕ, ∃ Q : Polynomial R, Q.support.card = n ∧ Q ≠ 0 ∧ evalRX Q = 0 :=
    ⟨Q₁.support.card, Q₁, rfl, hQ₁_ne, hQ₁_zero⟩
  obtain ⟨Q, hQ_card, hQ_ne, hQ_zero⟩ := Nat.find_spec hex
  have hQ_min : ∀ Q' : Polynomial R, Q' ≠ 0 → evalRX Q' = 0 → Q.support.card ≤ Q'.support.card := by
    intro Q' hne hz
    rw [hQ_card]
    exact Nat.find_min' hex ⟨Q', rfl, hne, hz⟩
  have hsupp_ne : Q.support.Nonempty := Polynomial.support_nonempty.mpr hQ_ne
  obtain ⟨k₀, hk₀⟩ := hsupp_ne
  have hcard1 : Q.support.card = 1 := by
    by_contra hne1
    have hge2 : 2 ≤ Q.support.card := by
      have hpos : 0 < Q.support.card := Finset.card_pos.mpr ⟨k₀, hk₀⟩
      omega
    obtain ⟨k₁, hk₁, hk₁₀⟩ : ∃ k₁ ∈ Q.support, k₁ ≠ k₀ :=
      Finset.exists_mem_ne (by omega : 1 < Q.support.card) k₀
    -- Define `θ_RX (∑ C_k X^k) = ∑ (thetaPoly C_k + k * C_k) X^k`!
    let θRX (F : Polynomial R) : Polynomial R :=
      ∑ k ∈ F.support, Polynomial.monomial k (thetaPoly (F.coeff k) + MvPolynomial.C (k : ℂ) * F.coeff k)
    have hθRX_eval : ∀ F : Polynomial R, evalRX (θRX F) = thetaD (evalRX F) := by
      intro F
      dsimp only [θRX]
      conv_rhs => rw [F.as_sum_support]
      rw [map_sum, map_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [evalRX, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_mul]
      rw [MvPolynomial.aeval_C, PowerSeries.algebraMap_eq, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
        aeval_thetaPoly]
      have hθXk : thetaD (PowerSeries.X ^ k : PowerSeries ℂ) = PowerSeries.C (k : ℂ) * PowerSeries.X ^ k := by
        cases k with
        | zero => simp
        | succ m =>
          rw [thetaD_apply, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, PowerSeries.derivative_X,
            mul_one, Nat.succ_sub_one, pow_succ, PowerSeries.C_eq_algebraMap, map_natCast]
          ring
      rw [hθXk]; ring
    let C₀ : R := Q.coeff k₀
    let Q' : Polynomial R :=
      Polynomial.C C₀ * θRX Q - Polynomial.C (thetaPoly C₀ + MvPolynomial.C (k₀ : ℂ) * C₀) * Q
    have hQ'_zero : evalRX Q' = 0 := by
      dsimp only [Q']
      rw [map_sub, map_mul, map_mul, hθRX_eval, hQ_zero, map_zero, mul_zero, mul_zero, sub_self]
    have hQ'_coeff : ∀ k : ℕ, Q'.coeff k =
        C₀ * thetaPoly (Q.coeff k) - Q.coeff k * thetaPoly C₀ +
          MvPolynomial.C ((k : ℂ) - (k₀ : ℂ)) * C₀ * Q.coeff k := by
      intro k
      dsimp only [Q', θRX]
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
      have hθk : (∑ j ∈ Q.support, Polynomial.monomial j (thetaPoly (Q.coeff j) + MvPolynomial.C (j : ℂ) * Q.coeff j)).coeff k =
          thetaPoly (Q.coeff k) + MvPolynomial.C (k : ℂ) * Q.coeff k := by
        change (Polynomial.lcoeff R k) (∑ j ∈ Q.support, Polynomial.monomial j _) = _
        rw [map_sum]
        simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial, Finsupp.single_apply]
        by_cases hk : k ∈ Q.support
        · rw [Finset.sum_ite_eq' Q.support k, ite_eq_left_iff.mpr fun h => (h hk).elim]
        · rw [Finset.sum_ite_eq' Q.support k, ite_eq_right_iff.mpr fun h => (hk h).elim]
          have hqk0 : Q.coeff k = 0 := Polynomial.notMem_support_iff.mp hk
          rw [hqk0, mul_zero, add_zero]
          exact (show thetaPoly (0 : R) = 0 by simpa using thetaPoly_C (K := K) 0).symm
      rw [hθk, map_sub]
      ring
    have hQ'_supp : Q'.support ⊆ Q.support.erase k₀ := by
      intro k hk
      rw [Polynomial.mem_support_iff] at hk
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro hkk0; subst hkk0
        rw [hQ'_coeff k] at hk
        dsimp only [C₀] at hk
        simp at hk
      · by_contra hnot
        have hqk0 : Q.coeff k = 0 := Polynomial.notMem_support_iff.mp hnot
        rw [hQ'_coeff k, hqk0, show thetaPoly (0 : R) = 0 from by simpa using thetaPoly_C (K := K) 0] at hk
        simp at hk
    have hQ'_card_lt : Q'.support.card < Q.support.card := by
      calc Q'.support.card ≤ (Q.support.erase k₀).card := Finset.card_le_card hQ'_supp
        _ < Q.support.card := Finset.card_erase_lt_of_mem hk₀
    have hQ'_eq0 : Q' = 0 := by
      by_contra hne
      exact not_lt.mpr (hQ_min Q' hne hQ'_zero) hQ'_card_lt
    have hk₁_zero : Q'.coeff k₁ = 0 := by rw [hQ'_eq0, Polynomial.coeff_zero]
    rw [hQ'_coeff k₁] at hk₁_zero
    have hC₀_ne : C₀ ≠ 0 := Polynomial.mem_support_iff.mp hk₀
    have hC₁_ne : Q.coeff k₁ ≠ 0 := Polynomial.mem_support_iff.mp hk₁
    have hdiff_ne : (k₁ : ℂ) - (k₀ : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (fun h => hk₁₀ (Nat.cast_injective h))
    exact no_const_logDeriv_thetaPoly hC₀_ne hC₁_ne hdiff_ne hk₁_zero
  -- Now `Q.support = {k₀}`, so `Q = monomial k₀ C₀` with `C₀ ≠ 0` and `C₀(θ^j H_i) * X^{k₀} = 0`!
  have hsupp_eq : Q.support = {k₀} := Finset.card_eq_one.mp hcard1 |> fun ⟨a, ha⟩ => by
    have : k₀ = a := Finset.mem_singleton.mp (ha ▸ hk₀)
    subst this; exact ha
  have hQ_mono : Q = Polynomial.monomial k₀ (Q.coeff k₀) := by
    conv_lhs => rw [Q.as_sum_support, hsupp_eq, Finset.sum_singleton]
  have hC₀_ne : Q.coeff k₀ ≠ 0 := Polynomial.mem_support_iff.mp hk₀
  have hC₀_zero : MvPolynomial.aeval (fun ij : Fin K × ℕ => thetaD^[ij.2] (H ij.1)) (Q.coeff k₀) = 0 := by
    rw [hQ_mono] at hQ_zero
    simp only [evalRX, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hQ_zero
    have hXk_ne : (PowerSeries.X : PowerSeries ℂ) ^ k₀ ≠ 0 := by
      refine pow_ne_zero k₀ ?_
      intro h0
      have h1 := congrArg (PowerSeries.coeff 1) h0
      simp at h1
    exact (mul_eq_zero.mp hQ_zero).resolve_right hXk_ne
  -- Step 3: Restrict `Q.coeff k₀` to `Fin K × Fin (r + 1)`!
  let r : ℕ := (Q.coeff k₀).vars.sup Prod.snd
  let emb : Fin K × Fin (r + 1) → Fin K × ℕ := fun ij => (ij.1, ij.2.val)
  have hemb_inj : Function.Injective emb := fun a b h => by
    simp only [emb, Prod.mk.injEq] at h
    exact Prod.ext h.1 (Fin.ext h.2)
  obtain ⟨P, hP_ren⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range (Q.coeff k₀) emb hemb_inj
    (fun v hv => ⟨(v.1, ⟨v.2, Nat.lt_succ_of_le (Finset.le_sup (f := Prod.snd) hv)⟩), rfl⟩)
  refine ⟨r, P, ?_, ?_⟩
  · intro h0; apply hC₀_ne; rw [← hP_ren, h0, map_zero]
  · rw [← hP_ren, MvPolynomial.aeval_rename] at hC₀_zero
    exact hC₀_zero

/-! #### 2A.2. Exact `K`-Tuple Kolchin–Ostrowski Log-Derivative Transfer (`joint_algIndep_of_log_deriv`) -/

/-- Formal `X`-derivative on `MvPolynomial (Option (Fin K × ℕ)) ℂ` sending
`none ↦ 1` and `some (i, j) ↦ X (some (i, j + 1))`. -/
private def derivPolyOpt {K : ℕ} (P : MvPolynomial (Option (Fin K × ℕ)) ℂ) :
    MvPolynomial (Option (Fin K × ℕ)) ℂ :=
  MvPolynomial.pderiv none P +
    ∑ v ∈ P.vars, match v with
      | none => 0
      | some (i, j) => MvPolynomial.X (some (i, j + 1)) * MvPolynomial.pderiv (some (i, j)) P

private lemma derivPolyOpt_eq_sum_superset {K : ℕ} {P : MvPolynomial (Option (Fin K × ℕ)) ℂ}
    {s : Finset (Option (Fin K × ℕ))} (hs : P.vars ⊆ s) :
    derivPolyOpt P = MvPolynomial.pderiv none P +
      ∑ v ∈ s, match v with
        | none => 0
        | some (i, j) => MvPolynomial.X (some (i, j + 1)) * MvPolynomial.pderiv (some (i, j)) P := by
  unfold derivPolyOpt
  congr 1
  refine Finset.sum_subset hs fun v _ hv => ?_
  cases v with
  | none => rfl
  | some ij => rcases ij with ⟨i, j⟩; dsimp only; rw [mvpoly_pderiv_eq_zero_of_notMem_vars hv, mul_zero]

private lemma derivPolyOpt_add {K : ℕ} (A B : MvPolynomial (Option (Fin K × ℕ)) ℂ) :
    derivPolyOpt (A + B) = derivPolyOpt A + derivPolyOpt B := by
  classical
  let s := A.vars ∪ B.vars
  rw [derivPolyOpt_eq_sum_superset (MvPolynomial.vars_add_subset A B),
    derivPolyOpt_eq_sum_superset Finset.subset_union_left,
    derivPolyOpt_eq_sum_superset Finset.subset_union_right, map_add]
  have hsum : (∑ v ∈ s, match v with
      | none => (0 : MvPolynomial (Option (Fin K × ℕ)) ℂ)
      | some (i, j) => MvPolynomial.X (some (i, j + 1)) * MvPolynomial.pderiv (some (i, j)) (A + B)) =
      (∑ v ∈ s, match v with | none => 0 | some (i, j) => MvPolynomial.X (some (i, j + 1)) * MvPolynomial.pderiv (some (i, j)) A) +
      (∑ v ∈ s, match v with | none => 0 | some (i, j) => MvPolynomial.X (some (i, j + 1)) * MvPolynomial.pderiv (some (i, j)) B) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    cases v with
    | none => simp
    | some ij => rcases ij with ⟨i, j⟩; dsimp only; rw [map_add, mul_add]
  rw [hsum]; ring

private lemma derivPolyOpt_mul {K : ℕ} (A B : MvPolynomial (Option (Fin K × ℕ)) ℂ) :
    derivPolyOpt (A * B) = derivPolyOpt A * B + A * derivPolyOpt B := by
  classical
  let s := A.vars ∪ B.vars
  rw [derivPolyOpt_eq_sum_superset (MvPolynomial.vars_mul A B),
    derivPolyOpt_eq_sum_superset Finset.subset_union_left,
    derivPolyOpt_eq_sum_superset Finset.subset_union_right,
    Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hsum : (∑ v ∈ s, match v with
      | none => (0 : MvPolynomial (Option (Fin K × ℕ)) ℂ)
      | some (i, j) => MvPolynomial.X (some (i, j + 1)) * MvPolynomial.pderiv (some (i, j)) (A * B)) =
      (∑ v ∈ s, match v with | none => 0 | some (i, j) => MvPolynomial.X (some (i, j + 1)) * MvPolynomial.pderiv (some (i, j)) A) * B +
      A * (∑ v ∈ s, match v with | none => 0 | some (i, j) => MvPolynomial.X (some (i, j + 1)) * MvPolynomial.pderiv (some (i, j)) B) := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    cases v with
    | none => simp
    | some ij => rcases ij with ⟨i, j⟩; dsimp only; rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
  rw [hsum]; ring

private lemma derivPolyOpt_C {K : ℕ} (c : ℂ) :
    derivPolyOpt (MvPolynomial.C c : MvPolynomial (Option (Fin K × ℕ)) ℂ) = 0 := by
  simp [derivPolyOpt]

private lemma derivPolyOpt_X_none {K : ℕ} :
    derivPolyOpt (MvPolynomial.X none : MvPolynomial (Option (Fin K × ℕ)) ℂ) = 1 := by
  classical
  simp [derivPolyOpt]

private lemma derivPolyOpt_X_some {K : ℕ} (i : Fin K) (j : ℕ) :
    derivPolyOpt (MvPolynomial.X (some (i, j)) : MvPolynomial (Option (Fin K × ℕ)) ℂ) =
      MvPolynomial.X (some (i, j + 1)) := by
  classical
  simp [derivPolyOpt]

private lemma derivPolyOpt_X_none_pow {K : ℕ} (k : ℕ) :
    derivPolyOpt (MvPolynomial.X none ^ k : MvPolynomial (Option (Fin K × ℕ)) ℂ) =
      MvPolynomial.C (k : ℂ) * MvPolynomial.X none ^ (k - 1) := by
  induction k with
  | zero => simpa using derivPolyOpt_C (K := K) 1
  | succ m ih =>
    cases m with
    | zero => simp [derivPolyOpt_X_none]
    | succ r =>
      rw [pow_succ, derivPolyOpt_mul, derivPolyOpt_X_none, mul_one, ih, Nat.succ_sub_one,
        Nat.succ_sub_one, pow_succ]
      push_cast
      simp only [map_add, map_one]
      ring

private lemma aeval_derivPolyOpt {K : ℕ} (H : Fin K → PowerSeries ℂ)
    (P : MvPolynomial (Option (Fin K × ℕ)) ℂ) :
    PowerSeries.derivative (MvPolynomial.aeval (jointCoords H) P) =
      MvPolynomial.aeval (jointCoords H) (derivPolyOpt P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [derivPolyOpt_C, map_zero, MvPolynomial.aeval_C, PowerSeries.algebraMap_eq, PowerSeries.derivative_C]
  | add A B hA hB =>
    rw [derivPolyOpt_add, map_add, map_add, map_add, hA, hB]
  | mul_X A v hA =>
    rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hA, derivPolyOpt_mul, map_add,
      map_mul, map_mul, MvPolynomial.aeval_X]
    cases v with
    | none =>
      rw [derivPolyOpt_X_none, map_one]; simp [jointCoords]; ring
    | some ij =>
      rw [derivPolyOpt_X_some, MvPolynomial.aeval_X]
      dsimp only [jointCoords]
      rw [Function.iterate_succ_apply' PowerSeries.derivative ij.2 (H ij.1)]
      ring

/-- **Key Kolchin–Ostrowski Obstruction Lemma**:
For any nonzero `A, B ∈ ℂ[X, Y_{i, j}]` and any nonzero integer vector `β : Fin K → ℤ`,
`X * (A * D B - B * D A) + (∑ i, β_i Y_{i, 0}) * A * B ≠ 0`. -/
private lemma no_linear_logDeriv_opt {K : ℕ} {A B : MvPolynomial (Option (Fin K × ℕ)) ℂ}
    (hA : A ≠ 0) (hB : B ≠ 0) {β : Fin K → ℤ} (hβ : ∃ i : Fin K, β i ≠ 0) :
    MvPolynomial.X none * (A * derivPolyOpt B - B * derivPolyOpt A) +
      (∑ i : Fin K, MvPolynomial.C (β i : ℂ) * MvPolynomial.X (some (i, 0))) * A * B ≠ 0 := by
  classical
  intro h0
  let R := MvPolynomial (Option (Fin K × ℕ)) ℂ
  let F := FractionRing R
  set ι : R →+* F := algebraMap R F
  have hA_nz : A ∈ nonZeroDivisors R := mem_nonZeroDivisors_iff_ne_zero.mpr hA
  let x : F := Localization.mk B ⟨A, hA_nz⟩
  have hAι : ι A ≠ 0 := (map_ne_zero_iff ι (IsFractionRing.injective R F)).mpr hA
  have hBι : ι B ≠ 0 := (map_ne_zero_iff ι (IsFractionRing.injective R F)).mpr hB
  have hXι : ι (MvPolynomial.X none) ≠ 0 :=
    (map_ne_zero_iff ι (IsFractionRing.injective R F)).mpr (MvPolynomial.X_ne_zero none)
  have hx_div : x = ι B / ι A := localization_mk_eq_div B ⟨A, hA_nz⟩
  have hx_ne : x ≠ 0 := by
    intro hx0
    rw [hx_div, div_eq_zero_iff] at hx0
    exact hx0.elim hBι hAι
  let S : Finset (Option (Fin K × ℕ)) := A.vars ∪ B.vars
  let linSum : F := ∑ i : Fin K, algebraMap ℂ F (β i : ℂ) * ι (MvPolynomial.X (some (i, 0)))
  have hsum_eq : ι (MvPolynomial.X none) * (pderivFrac none x +
      (∑ v ∈ S, match v with
        | none => (0 : F)
        | some (i, j) => ι (MvPolynomial.X (some (i, j + 1))) * pderivFrac (some (i, j)) x)) =
      -linSum * x := by
    have hA_d := derivPolyOpt_eq_sum_superset (P := A) (s := S) Finset.subset_union_left
    have hB_d := derivPolyOpt_eq_sum_superset (P := B) (s := S) Finset.subset_union_right
    have hsum_lhs : pderivFrac none x +
        (∑ v ∈ S, match v with
          | none => (0 : F)
          | some (i, j) => ι (MvPolynomial.X (some (i, j + 1))) * pderivFrac (some (i, j)) x) =
        (ι A * ι (derivPolyOpt B) - ι B * ι (derivPolyOpt A)) / (ι A) ^ 2 := by
      rw [hA_d, hB_d, map_add, map_add, map_sum, map_sum, mul_add, mul_add,
        Finset.mul_sum, Finset.mul_sum, add_sub_add_comm,
        add_div, ← Finset.sum_sub_distrib, Finset.sum_div]
      congr 1
      · change pderivFrac none (Localization.mk B ⟨A, hA_nz⟩) = _
        rw [pderivFrac_mk]
        change (ι (MvPolynomial.pderiv none B) * ι A - ι B * ι (MvPolynomial.pderiv none A)) / ι A ^ 2 = _
        field_simp [hAι]
      · refine Finset.sum_congr rfl fun v _ => ?_
        cases v with
        | none => simp
        | some ij =>
          rcases ij with ⟨i, j⟩
          dsimp only
          change ι (MvPolynomial.X (some (i, j + 1))) * pderivFrac (some (i, j)) (Localization.mk B ⟨A, hA_nz⟩) = _
          rw [pderivFrac_mk]
          change ι (MvPolynomial.X (some (i, j + 1))) *
            ((ι (MvPolynomial.pderiv (some (i, j)) B) * ι A - ι B * ι (MvPolynomial.pderiv (some (i, j)) A)) / ι A ^ 2) = _
          simp only [map_mul]
          field_simp [hAι]
    rw [hsum_lhs, hx_div]
    have h0' := congrArg ι h0
    simp only [map_add, map_sub, map_mul, map_sum, map_zero] at h0'
    have hlin : (∑ i : Fin K, ι (MvPolynomial.C (β i : ℂ)) * ι (MvPolynomial.X (some (i, 0)))) = linSum := by
      refine Finset.sum_congr rfl fun i _ => rfl
    rw [hlin] at h0'
    field_simp [hAι]
    linear_combination h0'
  -- Check whether any `some (i, j) ∈ S` has `pderivFrac (some (i, j)) x ≠ 0`.
  let active : Finset (Fin K × ℕ) :=
    (S.filterMap id (by
      intro a b c ha hb
      simp only [Option.mem_def, id_eq] at ha hb
      rw [ha, hb])).filter fun ij => pderivFrac (some ij) x ≠ 0
  have hmem_act : ∀ ij : Fin K × ℕ, ij ∈ active ↔ some ij ∈ S ∧ pderivFrac (some ij) x ≠ 0 := by
    intro ij
    simp only [active, Finset.mem_filter, Finset.mem_filterMap, id_eq]
    constructor
    · rintro ⟨⟨v, hvS, hv_eq⟩, hne⟩; subst hv_eq; exact ⟨hvS, hne⟩
    · rintro ⟨hvS, hne⟩; exact ⟨⟨some ij, hvS, rfl⟩, hne⟩
  by_cases hact : active.Nonempty
  · obtain ⟨ij₀, hij₀_mem, hij₀_max⟩ := active.exists_max_image Prod.snd hact
    have hij₀_S : some ij₀ ∈ S := ((hmem_act ij₀).mp hij₀_mem).1
    have hij₀_ne : pderivFrac (some ij₀) x ≠ 0 := ((hmem_act ij₀).mp hij₀_mem).2
    let w : Option (Fin K × ℕ) := some (ij₀.1, ij₀.2 + 1)
    have hw_zero : pderivFrac w x = 0 := by
      by_cases hwS : w ∈ S
      · by_contra hne
        have hw_act : (ij₀.1, ij₀.2 + 1) ∈ active := (hmem_act _).mpr ⟨hwS, hne⟩
        have hle := hij₀_max (ij₀.1, ij₀.2 + 1) hw_act
        dsimp only at hle; omega
      · exact pderivFrac_mk_eq_zero_of_notMem (fun h => hwS (Finset.mem_union_right _ h))
          (fun h => hwS (Finset.mem_union_left _ h))
    have hdiff := congrArg (pderivFrac w) hsum_eq
    have hlin_w : pderivFrac w linSum = 0 := by
      dsimp only [linSum]
      rw [pderivFrac_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [pderivFrac_mul, pderivFrac_C, zero_mul, zero_add, pderivFrac_algebraMap, MvPolynomial.pderiv_X]
      have hne : (some (i, 0) : Option (Fin K × ℕ)) ≠ w := by
        intro h; have := congrArg Prod.snd (Option.some.inj h); omega
      simp [hne]
    have hX_w : pderivFrac w (ι (MvPolynomial.X none)) = 0 := by
      rw [pderivFrac_algebraMap, MvPolynomial.pderiv_X]
      simp [w]
    have hrhs0 : pderivFrac w (-linSum * x) = 0 := by
      rw [pderivFrac_mul, pderivFrac_neg, hlin_w, neg_zero, zero_mul, zero_add, hw_zero, mul_zero]
    rw [hrhs0, pderivFrac_mul, hX_w, zero_mul, zero_add, pderivFrac_add, pderivFrac_comm w none x,
      hw_zero, pderivFrac_zero, zero_add, pderivFrac_sum] at hdiff
    have hterm : ∀ v ∈ S, pderivFrac w (match v with
        | none => (0 : F)
        | some (i, j) => ι (MvPolynomial.X (some (i, j + 1))) * pderivFrac (some (i, j)) x) =
        if v = some ij₀ then pderivFrac (some ij₀) x else 0 := by
      intro v _
      cases v with
      | none => simp [pderivFrac_zero]
      | some ij =>
        rcases ij with ⟨i, j⟩
        dsimp only
        rw [pderivFrac_mul, pderivFrac_algebraMap, MvPolynomial.pderiv_X, pderivFrac_comm w (some (i, j)) x,
          hw_zero, pderivFrac_zero, mul_zero, add_zero]
        have hiff : (some (i, j + 1) : Option (Fin K × ℕ)) = w ↔ (some (i, j) : Option (Fin K × ℕ)) = some ij₀ := by
          dsimp only [w]
          constructor
          · intro h
            have hp := Option.some.inj h
            simp only [Prod.mk.injEq] at hp
            exact congrArg some (Prod.ext hp.1 (Nat.succ.inj hp.2))
          · intro h
            have hp := Option.some.inj h
            rcases ij₀ with ⟨i₀, j₀⟩
            simp only [Prod.mk.injEq] at hp
            rw [hp.1, hp.2]
        by_cases heq : (some (i, j) : Option (Fin K × ℕ)) = some ij₀
        · have hp := Option.some.inj heq
          rcases ij₀ with ⟨i₀, j₀⟩
          simp only [Prod.mk.injEq] at hp
          rcases hp with ⟨rfl, rfl⟩
          simp [w]
        · have hne : (some (i, j + 1) : Option (Fin K × ℕ)) ≠ w := mt hiff.mp heq
          simp [hne, heq]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' S (some ij₀),
      ite_eq_left_iff.mpr fun h => (h hij₀_S).elim] at hdiff
    exact mul_ne_zero hXι hij₀_ne hdiff
  · rw [Finset.not_nonempty_iff_eq_empty] at hact
    have hall_some0 : ∀ ij : Fin K × ℕ, pderivFrac (some ij) x = 0 := by
      intro ij
      by_cases hS : some ij ∈ S
      · by_contra hne
        have : ij ∈ active := (hmem_act ij).mpr ⟨hS, hne⟩
        rw [hact] at this; exact Finset.notMem_empty ij this
      · exact pderivFrac_mk_eq_zero_of_notMem (fun h => hS (Finset.mem_union_right _ h))
          (fun h => hS (Finset.mem_union_left _ h))
    have hsum0 : (∑ v ∈ S, match v with
        | none => (0 : F)
        | some (i, j) => ι (MvPolynomial.X (some (i, j + 1))) * pderivFrac (some (i, j)) x) = 0 := by
      refine Finset.sum_eq_zero fun v _ => ?_
      cases v with
      | none => rfl
      | some ij => rcases ij with ⟨i, j⟩; dsimp only; rw [hall_some0 (i, j), mul_zero]
    rw [hsum0, add_zero] at hsum_eq
    obtain ⟨i₁, hi₁⟩ := hβ
    let w : Option (Fin K × ℕ) := some (i₁, 0)
    have hdiff := congrArg (pderivFrac w) hsum_eq
    have hX_w : pderivFrac w (ι (MvPolynomial.X none)) = 0 := by
      rw [pderivFrac_algebraMap, MvPolynomial.pderiv_X]; simp [w]
    rw [pderivFrac_mul, hX_w, zero_mul, zero_add, pderivFrac_comm w none x, hall_some0 (i₁, 0),
      pderivFrac_zero, mul_zero, pderivFrac_mul, pderivFrac_neg, hall_some0 (i₁, 0), mul_zero, add_zero] at hdiff
    have hlin_w : pderivFrac w linSum = algebraMap ℂ F (β i₁ : ℂ) := by
      dsimp only [linSum]
      rw [pderivFrac_sum]
      have ht : ∀ i : Fin K, pderivFrac w (algebraMap ℂ F (β i : ℂ) * ι (MvPolynomial.X (some (i, 0)))) =
          if i = i₁ then algebraMap ℂ F (β i₁ : ℂ) else 0 := fun i => by
        rw [pderivFrac_mul, pderivFrac_C, zero_mul, zero_add, pderivFrac_algebraMap, MvPolynomial.pderiv_X]
        by_cases hi : i = i₁
        · subst hi; simp [w]
        · have hne : (some (i, 0) : Option (Fin K × ℕ)) ≠ w := by
            intro h; exact hi (congrArg Prod.fst (Option.some.inj h))
          simp [hne, hi]
      simp_rw [ht, Finset.sum_ite_eq']
      simp
    rw [hlin_w] at hdiff
    have hβ_ne : -(algebraMap ℂ F (β i₁ : ℂ)) ≠ 0 := by
      refine neg_ne_zero.mpr ((map_ne_zero_iff (algebraMap ℂ F) (algebraMap ℂ F).injective).mpr ?_)
      exact_mod_cast hi₁
    exact mul_ne_zero hβ_ne hx_ne hdiff.symm

/-- Recursive polynomial `c_{i, j} ∈ ℂ[X, Y_{i, k}]` such that `X^j * D^j G_i = c_{i, j}(X, D^k H_i) * G_i`. -/
private def logDerivPoly {K : ℕ} (i : Fin K) : ℕ → MvPolynomial (Option (Fin K × ℕ)) ℂ
  | 0 => 1
  | j + 1 =>
    MvPolynomial.X none * derivPolyOpt (logDerivPoly i j) +
      (MvPolynomial.X (some (i, 0)) - MvPolynomial.C (j : ℂ)) * logDerivPoly i j

private lemma logDerivPoly_eval {K : ℕ} {G H : Fin K → PowerSeries ℂ}
    (hode : ∀ i, PowerSeries.X * PowerSeries.derivative (G i) = H i * G i) (i : Fin K) (j : ℕ) :
    PowerSeries.X ^ j * PowerSeries.derivative^[j] (G i) =
      MvPolynomial.aeval (jointCoords H) (logDerivPoly i j) * G i := by
  induction j with
  | zero => simp [logDerivPoly]
  | succ j ih =>
    have hstep : PowerSeries.X ^ (j + 1) * PowerSeries.derivative^[j + 1] (G i) =
        PowerSeries.X * PowerSeries.derivative (PowerSeries.X ^ j * PowerSeries.derivative^[j] (G i)) -
          PowerSeries.C (j : ℂ) * (PowerSeries.X ^ j * PowerSeries.derivative^[j] (G i)) := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul,
        Function.iterate_succ_apply' PowerSeries.derivative j (G i)]
      have hdX : PowerSeries.derivative (PowerSeries.X ^ j : PowerSeries ℂ) =
          PowerSeries.C (j : ℂ) * PowerSeries.X ^ (j - 1) := by
        cases j with
        | zero => simp
        | succ m =>
          rw [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, PowerSeries.derivative_X, mul_one,
            PowerSeries.C_eq_algebraMap, map_natCast]
      rw [hdX]
      cases j with
      | zero => simp [pow_one]
      | succ m =>
        rw [Nat.succ_sub_one, pow_succ (PowerSeries.X : PowerSeries ℂ) (m + 1),
          pow_succ (PowerSeries.X : PowerSeries ℂ) m]
        ring
    rw [hstep, ih, Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_add,
      ← mul_assoc PowerSeries.X, mul_comm PowerSeries.X (MvPolynomial.aeval (jointCoords H) (logDerivPoly i j)),
      mul_assoc, hode i, aeval_derivPolyOpt]
    simp only [logDerivPoly, map_add, map_mul, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      PowerSeries.algebraMap_eq, jointCoords, Function.iterate_zero, id_eq]
    ring

private lemma logDerivPoly_lead {K : ℕ} (i : Fin K) (j : ℕ) :
    ∃ R : MvPolynomial (Option (Fin K × ℕ)) ℂ,
      (∀ v ∈ R.vars, v = none ∨ ∃ m < j, v = some (i, m)) ∧
      logDerivPoly i (j + 1) = MvPolynomial.X none ^ j * MvPolynomial.X (some (i, j)) + R := by
  induction j with
  | zero =>
    refine ⟨0, by simp, ?_⟩
    simp [logDerivPoly, derivPolyOpt]
  | succ k ih =>
    obtain ⟨R, hRvars, hReq⟩ := ih
    let R' : MvPolynomial (Option (Fin K × ℕ)) ℂ :=
      MvPolynomial.X none * (MvPolynomial.C (k : ℂ) * MvPolynomial.X none ^ (k - 1) * MvPolynomial.X (some (i, k)) +
        derivPolyOpt R) +
      (MvPolynomial.X (some (i, 0)) - MvPolynomial.C ((k + 1 : ℕ) : ℂ)) * logDerivPoly i (k + 1)
    have hvars_deriv : ∀ P : MvPolynomial (Option (Fin K × ℕ)) ℂ,
        (∀ v ∈ P.vars, v = none ∨ ∃ m < k, v = some (i, m)) →
        ∀ v ∈ (derivPolyOpt P).vars, v = none ∨ ∃ m < k + 1, v = some (i, m) := by
      intro P hP v hv
      unfold derivPolyOpt at hv
      rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hv) with h1 | h2
      · rcases hP v (mvpoly_vars_pderiv_subset none P h1) with rfl | ⟨m, hm, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨m, by omega, rfl⟩
      · obtain ⟨u, huP, hvu⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ h2)
        cases u with
        | none => simp at hvu
        | some pq =>
          rcases hP (some pq) huP with h0 | ⟨m, hm, heq⟩
          · exact False.elim (Option.some_ne_none pq h0)
          · have hpq := Option.some.inj heq
            rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hvu) with hx | hd
            · rw [MvPolynomial.vars_X, Finset.mem_singleton] at hx
              rw [hx, hpq]
              exact Or.inr ⟨m + 1, by omega, rfl⟩
            · rcases hP v (mvpoly_vars_pderiv_subset _ P hd) with rfl | ⟨m', hm', rfl⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨m', by omega, rfl⟩
    refine ⟨R', ?_, ?_⟩
    · intro v hv
      dsimp only [R'] at hv
      rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ hv) with h1 | h2
      · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ h1) with hx | h1b
        · rw [MvPolynomial.vars_X, Finset.mem_singleton] at hx; exact Or.inl hx
        · rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ h1b) with h1c | h1d
          · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ h1c) with h1e | h1f
            · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ h1e) with hC | hpow
              · simp only [MvPolynomial.vars_C, Finset.notMem_empty] at hC
              · have := MvPolynomial.vars_pow _ _ hpow; rw [MvPolynomial.vars_X, Finset.mem_singleton] at this; exact Or.inl this
            · rw [MvPolynomial.vars_X, Finset.mem_singleton] at h1f; exact Or.inr ⟨k, by omega, h1f⟩
          · exact hvars_deriv R hRvars v h1d
      · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ h2) with h2a | h2b
        · rw [sub_eq_add_neg] at h2a
          rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ h2a) with hx | hC
          · rw [MvPolynomial.vars_X, Finset.mem_singleton] at hx; exact Or.inr ⟨0, by omega, hx⟩
          · rw [MvPolynomial.vars_neg] at hC; simp only [MvPolynomial.vars_C, Finset.notMem_empty] at hC
        · rw [hReq] at h2b
          rcases Finset.mem_union.mp (MvPolynomial.vars_add_subset _ _ h2b) with h2c | h2d
          · rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ h2c) with hpow | hx
            · have := MvPolynomial.vars_pow _ _ hpow; rw [MvPolynomial.vars_X, Finset.mem_singleton] at this; exact Or.inl this
            · rw [MvPolynomial.vars_X, Finset.mem_singleton] at hx; exact Or.inr ⟨k, by omega, hx⟩
          · rcases hRvars v h2d with rfl | ⟨m, hm, rfl⟩
            · exact Or.inl rfl
            · exact Or.inr ⟨m, by omega, rfl⟩
    · dsimp only [R']
      conv_lhs => rw [logDerivPoly, hReq, derivPolyOpt_add, derivPolyOpt_mul, derivPolyOpt_X_some]
      rw [derivPolyOpt_X_none_pow k, hReq, pow_succ]
      ring

/-- **Exact `K`-Tuple Kolchin–Ostrowski Log-Derivative Transfer (`joint_algIndep_of_log_deriv`)**:
If `G, H : Fin K → PowerSeries ℂ` satisfy `G i ≠ 0` and `X * derivative (G i) = H i * G i` for all
`i : Fin K`, and `H` is jointly differentially independent over `ℂ(X)`, then `G` is ALSO jointly
differentially independent over `ℂ(X)`. -/
theorem joint_algIndep_of_log_deriv {K : ℕ} {G H : Fin K → PowerSeries ℂ}
    (hG : ∀ i, G i ≠ 0)
    (hode : ∀ i, PowerSeries.X * PowerSeries.derivative (G i) = H i * G i)
    (hH : AlgebraicIndependent ℂ (jointCoords H)) :
    AlgebraicIndependent ℂ (jointCoords G) := by
  classical
  by_contra hdep
  rw [algebraicIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨P₀, hP₀_zero, hP₀_ne⟩ := hdep
  -- Step 1: Express `X^N * P₀(X, D^j G_i)` as a nonzero polynomial `Q₀ ∈ S_alg[Z_0, ..., Z_{K-1}]`!
  let S_alg := MvPolynomial (Option (Fin K × ℕ)) ℂ
  let F_alg := FractionRing S_alg
  let ιS : S_alg →ₐ[ℂ] F_alg := IsScalarTower.toAlgHom ℂ S_alg F_alg
  let wt (α : Option (Fin K × ℕ) →₀ ℕ) : ℕ :=
    ∑ v ∈ α.support, match v with | none => 0 | some (_, j) => α v * j
  let N : ℕ := P₀.support.sup wt
  have hwt_le : ∀ α ∈ P₀.support, wt α ≤ N := fun α hα => Finset.le_sup hα
  let Q₀ : MvPolynomial (Fin K) S_alg :=
    ∑ α ∈ P₀.support,
      MvPolynomial.C (MvPolynomial.C (P₀.coeff α) * MvPolynomial.X none ^ (N - wt α)) *
        ∏ v ∈ α.support, (match v with
          | none => MvPolynomial.C (MvPolynomial.X none)
          | some (i, j) => MvPolynomial.C (logDerivPoly i j) * MvPolynomial.X i) ^ (α v)
  -- Step 1a: Prove `Q₀ ≠ 0` by constructing an explicit left-inverse `S_alg[Z] →ₐ[ℂ] F_alg`!
  have hX_ne : ιS (MvPolynomial.X none) ≠ 0 :=
    (map_ne_zero_iff ιS (IsFractionRing.injective S_alg F_alg)).mpr (MvPolynomial.X_ne_zero none)
  have hG0_ne : ∀ i : Fin K, ιS (MvPolynomial.X (some (i, 0))) ≠ 0 := fun i =>
    (map_ne_zero_iff ιS (IsFractionRing.injective S_alg F_alg)).mpr (MvPolynomial.X_ne_zero _)
  -- Recursive inversion `invLD i j ∈ F_alg` such that `aeval invLD (logDerivPoly i (j + 1)) = X^{j+1} W_{i, j+1} / W_{i, 0}`!
  let invLD_aux : Fin K → ℕ → F_alg := fun i =>
    WellFounded.fix Nat.lt_wfRel.wf fun j rec =>
      let R := Classical.choose (logDerivPoly_lead i j)
      let evalR : F_alg := MvPolynomial.aeval (fun v : Option (Fin K × ℕ) =>
        match v with
        | none => ιS (MvPolynomial.X none)
        | some (i', m) => if h : i' = i ∧ m < j then rec m h.2 else 0) R
      ((ιS (MvPolynomial.X none)) ^ (j + 1) * ιS (MvPolynomial.X (some (i, j + 1))) /
        ιS (MvPolynomial.X (some (i, 0))) - evalR) / (ιS (MvPolynomial.X none)) ^ j
  let invSub : Option (Fin K × ℕ) → F_alg
    | none => ιS (MvPolynomial.X none)
    | some (i, j) => invLD_aux i j
  have hinv_ld : ∀ (i : Fin K) (j : ℕ),
      MvPolynomial.aeval invSub (logDerivPoly i j) * ιS (MvPolynomial.X (some (i, 0))) =
        (ιS (MvPolynomial.X none)) ^ j * ιS (MvPolynomial.X (some (i, j))) := by
    intro i j
    cases j with
    | zero => simp [logDerivPoly]
    | succ k =>
      have hspec := Classical.choose_spec (logDerivPoly_lead i k)
      set R := Classical.choose (logDerivPoly_lead i k)
      rw [hspec.2, map_add, map_mul, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
      dsimp only [invSub]
      have hrec_eq : invLD_aux i k =
          ((ιS (MvPolynomial.X none)) ^ (k + 1) * ιS (MvPolynomial.X (some (i, k + 1))) /
            ιS (MvPolynomial.X (some (i, 0))) -
            MvPolynomial.aeval (fun v : Option (Fin K × ℕ) =>
              match v with
              | none => ιS (MvPolynomial.X none)
              | some (i', m) => if h : i' = i ∧ m < k then invLD_aux i m else 0) R) /
            (ιS (MvPolynomial.X none)) ^ k := by
        dsimp only [invLD_aux]
        rw [WellFounded.fix_eq]
      have hR_eq : MvPolynomial.aeval invSub R =
          MvPolynomial.aeval (fun v : Option (Fin K × ℕ) =>
            match v with
            | none => ιS (MvPolynomial.X none)
            | some (i', m) => if h : i' = i ∧ m < k then invLD_aux i m else 0) R := by
        refine mvpoly_aeval_eq_of_eq_on_vars fun v hv => ?_
        rcases hspec.1 v hv with rfl | ⟨m, hm, rfl⟩
        · rfl
        · simp [invSub, hm]
      rw [hrec_eq, hR_eq]
      have hXk : (ιS (MvPolynomial.X none)) ^ k ≠ 0 := pow_ne_zero k hX_ne
      have hG0 := hG0_ne i
      field_simp [hXk, hG0]
      ring
  let ψZ : MvPolynomial (Fin K) S_alg →+* F_alg :=
    MvPolynomial.eval₂Hom (MvPolynomial.aeval invSub).toRingHom (fun i => ιS (MvPolynomial.X (some (i, 0))))
  have hψZ_Q₀ : ψZ Q₀ = ιS (MvPolynomial.X none ^ N * P₀) := by
    dsimp only [Q₀]
    rw [map_sum]
    conv_rhs => rw [P₀.as_sum, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [map_mul, MvPolynomial.eval₂Hom_C, map_prod]
    have hprod : ∏ v ∈ α.support, ψZ ((match v with
        | none => MvPolynomial.C (MvPolynomial.X none)
        | some (i, j) => MvPolynomial.C (logDerivPoly i j) * MvPolynomial.X i) ^ α v) =
        (ιS (MvPolynomial.X none)) ^ wt α * ∏ v ∈ α.support, (ιS (MvPolynomial.X v)) ^ α v := by
      have hterm : ∀ v ∈ α.support,
          ψZ ((match v with
            | none => MvPolynomial.C (MvPolynomial.X none)
            | some (i, j) => MvPolynomial.C (logDerivPoly i j) * MvPolynomial.X i) ^ α v) =
            (ιS (MvPolynomial.X none)) ^ (match v with | none => 0 | some (_, j) => α v * j) *
              (ιS (MvPolynomial.X v)) ^ α v := by
        intro v _
        rw [map_pow]
        cases v with
        | none =>
          dsimp only [ψZ]
          rw [MvPolynomial.eval₂Hom_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
          simp [invSub]
        | some ij =>
          rcases ij with ⟨i, j⟩
          simp only [ψZ, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
            AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
          rw [hinv_ld i j, mul_pow, ← pow_mul, mul_comm j (α (some (i, j)))]
      rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rw [hprod]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_pow]
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    simp only [invSub, MvPolynomial.monomial_eq, Finsupp.prod, map_mul, map_prod, map_pow]
    have hadd : (N - wt α) + wt α = N := Nat.sub_add_cancel (hwt_le α hα)
    have hC : algebraMap ℂ F_alg (P₀.coeff α) = ιS (MvPolynomial.C (P₀.coeff α)) := by
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    rw [hC]
    calc ιS (MvPolynomial.C (P₀.coeff α)) * ιS (MvPolynomial.X none) ^ (N - wt α) *
          (ιS (MvPolynomial.X none) ^ wt α * ∏ v ∈ α.support, ιS (MvPolynomial.X v) ^ α v)
        = ιS (MvPolynomial.X none) ^ ((N - wt α) + wt α) *
            (ιS (MvPolynomial.C (P₀.coeff α)) * ∏ v ∈ α.support, ιS (MvPolynomial.X v) ^ α v) := by
          rw [pow_add]; ring
      _ = ιS (MvPolynomial.X none) ^ N *
            (ιS (MvPolynomial.C (P₀.coeff α)) * ∏ v ∈ α.support, ιS (MvPolynomial.X v) ^ α v) := by
          rw [hadd]
  have hQ₀_ne : Q₀ ≠ 0 := by
    intro h0
    have h1 := congrArg ψZ h0
    rw [hψZ_Q₀, map_zero] at h1
    have h2 : (MvPolynomial.X none : S_alg) ^ N * P₀ = 0 :=
      IsFractionRing.injective S_alg F_alg (h1.trans (map_zero ιS).symm)
    exact mul_ne_zero (pow_ne_zero N (MvPolynomial.X_ne_zero none)) hP₀_ne h2
  -- Step 2: Evaluate `Q₀` at `(H, G)`!
  let evalH : S_alg →+* PowerSeries ℂ := (MvPolynomial.aeval (jointCoords H)).toRingHom
  have hevalH_inj : Function.Injective evalH := (algebraicIndependent_iff_injective_aeval.mp hH)
  let evalHG : MvPolynomial (Fin K) S_alg →+* PowerSeries ℂ := MvPolynomial.eval₂Hom evalH G
  have hQ₀_eval0 : evalHG Q₀ = 0 := by
    have hval : evalHG Q₀ = PowerSeries.X ^ N * MvPolynomial.aeval (jointCoords G) P₀ := by
      dsimp only [Q₀]
      rw [map_sum]
      conv_rhs => rw [P₀.as_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [map_mul, MvPolynomial.eval₂Hom_C, map_prod]
      have hprod : ∏ v ∈ α.support, evalHG ((match v with
          | none => MvPolynomial.C (MvPolynomial.X none)
          | some (i, j) => MvPolynomial.C (logDerivPoly i j) * MvPolynomial.X i) ^ α v) =
          PowerSeries.X ^ wt α * ∏ v ∈ α.support, (jointCoords G v) ^ α v := by
        have hterm : ∀ v ∈ α.support,
            evalHG ((match v with
              | none => MvPolynomial.C (MvPolynomial.X none)
              | some (i, j) => MvPolynomial.C (logDerivPoly i j) * MvPolynomial.X i) ^ α v) =
              PowerSeries.X ^ (match v with | none => 0 | some (_, j) => α v * j) *
                (jointCoords G v) ^ α v := by
          intro v _
          rw [map_pow]
          cases v with
          | none =>
            dsimp only [evalHG, evalH]
            rw [MvPolynomial.eval₂Hom_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
            simp [jointCoords]
          | some ij =>
            rcases ij with ⟨i, j⟩
            simp only [evalHG, evalH, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
              AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
            rw [← logDerivPoly_eval hode i j, mul_pow, ← pow_mul, mul_comm j (α (some (i, j)))]
            rfl
        rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      rw [hprod]
      simp only [evalH, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_pow]
      rw [MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.aeval_monomial]
      simp only [PowerSeries.algebraMap_eq, Finsupp.prod]
      change PowerSeries.C (P₀.coeff α) * PowerSeries.X ^ (N - wt α) *
          (PowerSeries.X ^ wt α * ∏ v ∈ α.support, jointCoords G v ^ α v) =
        PowerSeries.X ^ N *
          (PowerSeries.C (P₀.coeff α) * ∏ v ∈ α.support, jointCoords G v ^ α v)
      have hadd : (N - wt α) + wt α = N := Nat.sub_add_cancel (hwt_le α hα)
      calc PowerSeries.C (P₀.coeff α) * PowerSeries.X ^ (N - wt α) *
            (PowerSeries.X ^ wt α * ∏ v ∈ α.support, jointCoords G v ^ α v)
          = PowerSeries.X ^ ((N - wt α) + wt α) *
              (PowerSeries.C (P₀.coeff α) * ∏ v ∈ α.support, jointCoords G v ^ α v) := by
            rw [pow_add]; ring
        _ = PowerSeries.X ^ N *
              (PowerSeries.C (P₀.coeff α) * ∏ v ∈ α.support, jointCoords G v ^ α v) := by
            rw [hadd]
    rw [hval, hP₀_zero, mul_zero]
  -- Step 3: Minimal-support descent in `MvPolynomial (Fin K) S_alg`!
  have hex : ∃ n : ℕ, ∃ Q : MvPolynomial (Fin K) S_alg, Q.support.card = n ∧ Q ≠ 0 ∧ evalHG Q = 0 :=
    ⟨Q₀.support.card, Q₀, rfl, hQ₀_ne, hQ₀_eval0⟩
  obtain ⟨Q, hQ_card, hQ_ne, hQ_zero⟩ := Nat.find_spec hex
  have hQ_min : ∀ Q' : MvPolynomial (Fin K) S_alg, Q' ≠ 0 → evalHG Q' = 0 → Q.support.card ≤ Q'.support.card := by
    intro Q' hne hz
    rw [hQ_card]
    exact Nat.find_min' hex ⟨Q', rfl, hne, hz⟩
  have hsupp_ne : Q.support.Nonempty := MvPolynomial.support_nonempty.mpr hQ_ne
  obtain ⟨α₀, hα₀⟩ := hsupp_ne
  have hge2 : 2 ≤ Q.support.card := by
    by_contra hlt
    have hcard1 : Q.support.card = 1 := by
      have hpos : 0 < Q.support.card := Finset.card_pos.mpr ⟨α₀, hα₀⟩
      omega
    have hsupp_eq : Q.support = {α₀} := Finset.card_eq_one.mp hcard1 |> fun ⟨a, ha⟩ => by
      have : α₀ = a := Finset.mem_singleton.mp (ha ▸ hα₀)
      subst this; exact ha
    have hQ_mono : Q = MvPolynomial.monomial α₀ (Q.coeff α₀) := by
      conv_lhs => rw [Q.as_sum, hsupp_eq, Finset.sum_singleton]
    rw [hQ_mono] at hQ_zero
    simp only [evalHG, MvPolynomial.eval₂Hom_monomial] at hQ_zero
    have hprod_ne : (α₀.prod fun i k => G i ^ k) ≠ 0 := by
      rw [Finsupp.prod]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hG i)
    have hc0 : evalH (Q.coeff α₀) = 0 := (mul_eq_zero.mp hQ_zero).resolve_right hprod_ne
    exact (MvPolynomial.mem_support_iff.mp hα₀) (hevalH_inj (hc0.trans (map_zero evalH).symm))
  obtain ⟨α₁, hα₁, hα₁₀⟩ : ∃ α₁ ∈ Q.support, α₁ ≠ α₀ := Finset.exists_mem_ne (by omega : 1 < Q.support.card) α₀
  -- Define `θ_G (∑ C_α Z^α) = ∑ (X * derivPolyOpt C_α + (∑ i, α i * X_{i, 0}) * C_α) Z^α`!
  let linAlpha (α : Fin K →₀ ℕ) : S_alg :=
    ∑ i : Fin K, MvPolynomial.C ((α i : ℕ) : ℂ) * MvPolynomial.X (some (i, 0))
  let θZ (F : MvPolynomial (Fin K) S_alg) : MvPolynomial (Fin K) S_alg :=
    ∑ α ∈ F.support, MvPolynomial.monomial α (MvPolynomial.X none * derivPolyOpt (F.coeff α) + linAlpha α * F.coeff α)
  have hθZ_eval : ∀ F : MvPolynomial (Fin K) S_alg, evalHG (θZ F) = thetaD (evalHG F) := by
    intro F
    dsimp only [θZ]
    conv_rhs => rw [F.as_sum]
    rw [map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [evalHG, MvPolynomial.eval₂Hom_monomial, evalH, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      map_add, map_mul]
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, MvPolynomial.aeval_X]
    dsimp only [jointCoords]
    have hθ_prod : thetaD (α.prod fun i k => G i ^ k) =
        MvPolynomial.aeval (jointCoords H) (linAlpha α) * (α.prod fun i k => G i ^ k) := by
      have hprod_fin : (α.prod fun i k => G i ^ k) = ∏ i : Fin K, G i ^ α i := by
        rw [Finsupp.prod]
        exact Finset.prod_subset (Finset.subset_univ _) fun i _ hi => by
          rw [Finsupp.notMem_support_iff.mp hi, pow_zero]
      rw [hprod_fin]
      -- Prove `thetaD (∏ i ∈ s, G i ^ α i) = (∑ i ∈ s, α i * H i) * ∏ i ∈ s, G i ^ α i` by Finset induction!
      have hfin : ∀ s : Finset (Fin K),
          thetaD (∏ i ∈ s, G i ^ α i) =
            (∑ i ∈ s, PowerSeries.C ((α i : ℕ) : ℂ) * H i) * ∏ i ∈ s, G i ^ α i := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp
        | @insert i s hi ih =>
          rw [Finset.prod_insert hi, Finset.sum_insert hi, Derivation.leibniz, smul_eq_mul, smul_eq_mul, ih]
          have hpow_th : thetaD (G i ^ α i) = PowerSeries.C ((α i : ℕ) : ℂ) * H i * G i ^ α i := by
            cases hαi : α i with
            | zero => simp
            | succ m =>
              rw [thetaD_apply, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, Nat.succ_sub_one,
                show (PowerSeries.X : PowerSeries ℂ) * (((m + 1 : ℕ) : PowerSeries ℂ) * (G i ^ m * PowerSeries.derivative (G i))) =
                  PowerSeries.C ((m + 1 : ℕ) : ℂ) * G i ^ m * (PowerSeries.X * PowerSeries.derivative (G i)) by
                  rw [PowerSeries.C_eq_algebraMap, map_natCast]; ring,
                hode i, pow_succ]
              ring
          rw [hpow_th]; ring
      rw [hfin Finset.univ]
      congr 1
      dsimp only [linAlpha]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => by
        simp [jointCoords]
    rw [hθ_prod, thetaD_apply, aeval_derivPolyOpt]; ring
  let C₀ : S_alg := Q.coeff α₀
  let Q' : MvPolynomial (Fin K) S_alg :=
    MvPolynomial.C C₀ * θZ Q - MvPolynomial.C (MvPolynomial.X none * derivPolyOpt C₀ + linAlpha α₀ * C₀) * Q
  have hQ'_zero : evalHG Q' = 0 := by
    dsimp only [Q']
    rw [map_sub, map_mul, map_mul, hθZ_eval, hQ_zero, map_zero, mul_zero, mul_zero, sub_self]
  have hQ'_coeff : ∀ α : Fin K →₀ ℕ, Q'.coeff α =
      MvPolynomial.X none * (C₀ * derivPolyOpt (Q.coeff α) - Q.coeff α * derivPolyOpt C₀) +
        (∑ i : Fin K, MvPolynomial.C (((α i : ℤ) - (α₀ i : ℤ) : ℤ) : ℂ) * MvPolynomial.X (some (i, 0))) *
          C₀ * Q.coeff α := by
    intro α
    dsimp only [Q', θZ]
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul]
    have hθa : (∑ β ∈ Q.support, MvPolynomial.monomial β
        (MvPolynomial.X none * derivPolyOpt (Q.coeff β) + linAlpha β * Q.coeff β)).coeff α =
        MvPolynomial.X none * derivPolyOpt (Q.coeff α) + linAlpha α * Q.coeff α := by
      rw [MvPolynomial.coeff_sum]
      simp_rw [MvPolynomial.coeff_monomial]
      by_cases hα : α ∈ Q.support
      · rw [Finset.sum_ite_eq' Q.support α, ite_eq_left_iff.mpr fun h => (h hα).elim]
      · rw [Finset.sum_ite_eq' Q.support α, ite_eq_right_iff.mpr fun h => (hα h).elim]
        have hqa0 : Q.coeff α = 0 := MvPolynomial.notMem_support_iff.mp hα
        rw [hqa0, mul_zero, add_zero, show derivPolyOpt (0 : S_alg) = 0 from by simpa using derivPolyOpt_C (K := K) 0,
          mul_zero]
    rw [hθa]
    have hlin_sub : linAlpha α - linAlpha α₀ =
        ∑ i : Fin K, MvPolynomial.C (((α i : ℤ) - (α₀ i : ℤ) : ℤ) : ℂ) * MvPolynomial.X (some (i, 0)) := by
      dsimp only [linAlpha]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← sub_mul, ← map_sub]
      congr 2; push_cast; ring
    linear_combination (C₀ * Q.coeff α) * hlin_sub
  have hQ'_supp : Q'.support ⊆ Q.support.erase α₀ := by
    intro α hα
    rw [MvPolynomial.mem_support_iff] at hα
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro hEq; subst hEq
      rw [hQ'_coeff α] at hα
      dsimp only [C₀] at hα
      simp at hα
    · by_contra hnot
      have hqa0 : Q.coeff α = 0 := MvPolynomial.notMem_support_iff.mp hnot
      rw [hQ'_coeff α, hqa0, show derivPolyOpt (0 : S_alg) = 0 from by simpa using derivPolyOpt_C (K := K) 0] at hα
      simp at hα
  have hQ'_card_lt : Q'.support.card < Q.support.card :=
    (Finset.card_le_card hQ'_supp).trans_lt (Finset.card_erase_lt_of_mem hα₀)
  have hQ'_eq0 : Q' = 0 := by
    by_contra hne
    exact not_lt.mpr (hQ_min Q' hne hQ'_zero) hQ'_card_lt
  have hα₁_zero : Q'.coeff α₁ = 0 := by rw [hQ'_eq0]; simp
  rw [hQ'_coeff α₁] at hα₁_zero
  have hβ_ne : ∃ i : Fin K, (α₁ i : ℤ) - (α₀ i : ℤ) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hα₁₀
    ext i
    have := hall i
    omega
  exact no_linear_logDeriv_opt (MvPolynomial.mem_support_iff.mp hα₀)
    (MvPolynomial.mem_support_iff.mp hα₁) hβ_ne hα₁_zero

/-! #### 2B. Analytic Evaluation Along `q = e^{-1/u}` and Remainder ODE Transfer -/

/-- Polynomial coefficients `a_{j, k}(u) ∈ ℂ[u]` such that `(u² d/du)^j g(u) = ∑_{k ≤ j} a_{j, k}(u) g^{(k)}(u)`. -/
private def thetaToDerivPoly : ℕ → ℕ → Polynomial ℂ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | j + 1, 0 => Polynomial.X ^ 2 * Polynomial.derivative (thetaToDerivPoly j 0)
  | j + 1, k + 1 => Polynomial.X ^ 2 * (Polynomial.derivative (thetaToDerivPoly j (k + 1)) + thetaToDerivPoly j k)

private lemma thetaToDerivPoly_eq_zero_of_lt {j k : ℕ} (h : j < k) : thetaToDerivPoly j k = 0 := by
  induction j generalizing k with
  | zero => cases k with | zero => omega | succ r => rfl
  | succ j ih =>
    cases k with
    | zero => omega
    | succ r =>
      simp only [thetaToDerivPoly, ih (by omega : j < r + 1), ih (by omega : j < r),
        map_zero, add_zero, mul_zero]

private lemma thetaToDerivPoly_self (j : ℕ) : thetaToDerivPoly j j = Polynomial.X ^ (2 * j) := by
  induction j with
  | zero => simp [thetaToDerivPoly]
  | succ j ih =>
    rw [thetaToDerivPoly, thetaToDerivPoly_eq_zero_of_lt (by omega : j < j + 1), map_zero,
      zero_add, ih, ← pow_add]
    congr 1; omega

private lemma hasDerivAt_poly_eval_real (p : Polynomial ℂ) (u : ℝ) :
    HasDerivAt (fun t : ℝ => Polynomial.eval (t : ℂ) p) (Polynomial.eval (u : ℂ) (Polynomial.derivative p)) u := by
  have hC : HasDerivAt (fun z : ℂ => Polynomial.eval z p) (Polynomial.eval (u : ℂ) (Polynomial.derivative p)) (u : ℂ) :=
    Polynomial.hasDerivAt p (u : ℂ)
  simpa using hC.comp_ofReal

private lemma iteratedDeriv_poly_eval_real (p : Polynomial ℂ) (k : ℕ) (u : ℝ) :
    iteratedDeriv k (fun t : ℝ => Polynomial.eval (t : ℂ) p) u =
      Polynomial.eval (u : ℂ) (Polynomial.derivative^[k] p) := by
  induction k generalizing p u with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ', Function.iterate_succ_apply]
    have hder : deriv (fun t : ℝ => Polynomial.eval (t : ℂ) p) =
        fun t : ℝ => Polynomial.eval (t : ℂ) (Polynomial.derivative p) := by
      funext t; exact (hasDerivAt_poly_eval_real p t).deriv
    rw [hder]
    exact ih (Polynomial.derivative p) u

private lemma contDiffAt_poly_eval_real (p : Polynomial ℂ) (m : ℕ) (u : ℝ) :
    ContDiffAt ℝ m (fun t : ℝ => Polynomial.eval (t : ℂ) p) u := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hEq : (fun t : ℝ => Polynomial.eval (t : ℂ) (p + q)) =
        (fun t : ℝ => Polynomial.eval (t : ℂ) p) + (fun t : ℝ => Polynomial.eval (t : ℂ) q) := by
      funext t; simp
    rw [hEq]; exact hp.add hq
  | monomial n c =>
    have hEq : (fun t : ℝ => Polynomial.eval (t : ℂ) (Polynomial.monomial n c)) =
        fun t : ℝ => c * (t : ℂ) ^ n := by
      funext t; simp [Polynomial.eval_monomial]
    rw [hEq]
    exact (contDiffAt_const (c := c)).mul ((Complex.ofRealCLM.contDiff.contDiffAt.pow n).of_le le_top)

private lemma contDiffOn_Ioi_iteratedDeriv_diffAt {g : ℝ → ℂ}
    (hg : ∀ m : ℕ, ContDiffOn ℝ m g (Ioi (0 : ℝ))) (k : ℕ) {u : ℝ} (hu : 0 < u) :
    DifferentiableAt ℝ (iteratedDeriv k g) u := by
  have hcd : ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) g (Ioi (0 : ℝ)) := hg (k + 1)
  have hd_on : DifferentiableOn ℝ (iteratedDerivWithin k g (Ioi (0 : ℝ))) (Ioi (0 : ℝ)) :=
    hcd.differentiableOn_iteratedDerivWithin (by exact_mod_cast (by omega : k < k + 1))
      isOpen_Ioi.uniqueDiffOn
  have hev : iteratedDeriv k g =ᶠ[𝓝 u] iteratedDerivWithin k g (Ioi (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
    exact (iteratedDerivWithin_of_isOpen isOpen_Ioi hv).symm
  exact (hd_on.differentiableAt (isOpen_Ioi.mem_nhds hu)).congr_of_eventuallyEq hev

private lemma deriv_u2_of_poly_sum {g : ℝ → ℂ} {u : ℝ} (hu : 0 < u)
    (hdiff : ∀ m : ℕ, ContDiffOn ℝ m g (Ioi (0 : ℝ))) (j : ℕ) :
    (u : ℂ) ^ 2 * deriv (fun t : ℝ => ∑ k ∈ Finset.range (j + 1),
      Polynomial.eval (t : ℂ) (thetaToDerivPoly j k) * iteratedDeriv k g t) u =
      ∑ k ∈ Finset.range (j + 2),
        Polynomial.eval (u : ℂ) (thetaToDerivPoly (j + 1) k) * iteratedDeriv k g u := by
  have hterm : ∀ k ∈ Finset.range (j + 1),
      HasDerivAt (fun t : ℝ => Polynomial.eval (t : ℂ) (thetaToDerivPoly j k) * iteratedDeriv k g t)
        (Polynomial.eval (u : ℂ) (Polynomial.derivative (thetaToDerivPoly j k)) * iteratedDeriv k g u +
          Polynomial.eval (u : ℂ) (thetaToDerivPoly j k) * iteratedDeriv (k + 1) g u) u := fun k _ => by
    have h1 := hasDerivAt_poly_eval_real (thetaToDerivPoly j k) u
    have h2 : HasDerivAt (iteratedDeriv k g) (iteratedDeriv (k + 1) g u) u := by
      rw [iteratedDeriv_succ]
      exact (contDiffOn_Ioi_iteratedDeriv_diffAt hdiff k hu).hasDerivAt
    exact h1.mul h2
  have hsum_hd : HasDerivAt (fun t : ℝ => ∑ k ∈ Finset.range (j + 1),
      Polynomial.eval (t : ℂ) (thetaToDerivPoly j k) * iteratedDeriv k g t)
      (∑ k ∈ Finset.range (j + 1),
        (Polynomial.eval (u : ℂ) (Polynomial.derivative (thetaToDerivPoly j k)) * iteratedDeriv k g u +
          Polynomial.eval (u : ℂ) (thetaToDerivPoly j k) * iteratedDeriv (k + 1) g u)) u :=
    HasDerivAt.fun_sum hterm
  rw [hsum_hd.deriv, Finset.sum_add_distrib, mul_add, Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_range_succ' (fun k => Polynomial.eval (u : ℂ) (thetaToDerivPoly (j + 1) k) * iteratedDeriv k g u) (j + 1)]
  have hsplit : ∑ k ∈ Finset.range (j + 1),
      Polynomial.eval (u : ℂ) (thetaToDerivPoly (j + 1) (k + 1)) * iteratedDeriv (k + 1) g u =
      (∑ k ∈ Finset.range (j + 1), (u : ℂ) ^ 2 * (Polynomial.eval (u : ℂ) (Polynomial.derivative (thetaToDerivPoly j (k + 1))) * iteratedDeriv (k + 1) g u)) +
      (∑ k ∈ Finset.range (j + 1), (u : ℂ) ^ 2 * (Polynomial.eval (u : ℂ) (thetaToDerivPoly j k) * iteratedDeriv (k + 1) g u)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [thetaToDerivPoly, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_add]
    ring
  rw [hsplit]
  have hzero_tail : ∑ k ∈ Finset.range (j + 1),
      (u : ℂ) ^ 2 * (Polynomial.eval (u : ℂ) (Polynomial.derivative (thetaToDerivPoly j (k + 1))) * iteratedDeriv (k + 1) g u) =
      ∑ k ∈ Finset.range j,
        (u : ℂ) ^ 2 * (Polynomial.eval (u : ℂ) (Polynomial.derivative (thetaToDerivPoly j (k + 1))) * iteratedDeriv (k + 1) g u) := by
    rw [Finset.sum_range_succ, thetaToDerivPoly_eq_zero_of_lt (by omega : j < j + 1),
      map_zero, Polynomial.eval_zero, zero_mul, mul_zero, add_zero]
  have hfirst_shift : ∑ k ∈ Finset.range (j + 1),
      (u : ℂ) ^ 2 * (Polynomial.eval (u : ℂ) (Polynomial.derivative (thetaToDerivPoly j k)) * iteratedDeriv k g u) =
      (∑ k ∈ Finset.range j,
        (u : ℂ) ^ 2 * (Polynomial.eval (u : ℂ) (Polynomial.derivative (thetaToDerivPoly j (k + 1))) * iteratedDeriv (k + 1) g u)) +
      (u : ℂ) ^ 2 * (Polynomial.eval (u : ℂ) (Polynomial.derivative (thetaToDerivPoly j 0)) * iteratedDeriv 0 g u) :=
    Finset.sum_range_succ' _ j
  rw [hzero_tail, hfirst_shift]
  simp only [thetaToDerivPoly, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  have _ := hu
  ring

private lemma value_exp_inv_contDiffAt {F : PowerSeries ℂ} (hF : PolyCoeffBound F) {u : ℝ} (hu : 0 < u) (m : ℕ) :
    ContDiffAt ℝ m (fun t : ℝ => value F (Complex.exp (-((t⁻¹ : ℝ) : ℂ)))) u := by
  have hq : ‖Complex.exp (-((u⁻¹ : ℝ) : ℂ))‖ < 1 := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    exact neg_lt_zero.mpr (inv_pos.mpr hu)
  have hanF : AnalyticAt ℂ (value F) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) := by
    simpa [seriesJet] using seriesJet_analytic hF.to_diskCoeffBound 0 _ (by simpa using hq)
  have hcdF : ContDiffAt ℝ m (value F) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) :=
    (hanF.contDiffAt (n := (m : WithTop ℕ∞))).restrict_scalars ℝ
  have hcdExp : ContDiffAt ℝ m (fun t : ℝ => Complex.exp (-((t⁻¹ : ℝ) : ℂ))) u := by
    have h1 : ContDiffAt ℝ m (fun t : ℝ => -(t⁻¹)) u := (contDiffAt_id.inv hu.ne').neg
    have h2 : ContDiffAt ℝ m (fun t : ℝ => ((-(t⁻¹) : ℝ) : ℂ)) u :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp u h1
    have hcexp : ContDiffAt ℝ m Complex.exp ((-(u⁻¹) : ℝ) : ℂ) :=
      (Complex.contDiff_exp (𝕜 := ℂ) (n := (m : WithTop ℕ∞))).contDiffAt.restrict_scalars ℝ
    simpa [Function.comp_def, Complex.ofReal_neg] using hcexp.comp u h2
  exact hcdF.comp u hcdExp

private lemma value_thetaD_iter_exp_inv {F : PowerSeries ℂ} (hF : PolyCoeffBound F) (j : ℕ) :
    ∀ {u : ℝ}, 0 < u →
      value (thetaD^[j] F) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) =
        ∑ k ∈ Finset.range (j + 1),
          Polynomial.eval (u : ℂ) (thetaToDerivPoly j k) *
            iteratedDeriv k (fun t : ℝ => value F (Complex.exp (-((t⁻¹ : ℝ) : ℂ)))) u := by
  have hpoly_iter : ∀ n : ℕ, PolyCoeffBound (thetaD^[n] F) := by
    intro n
    induction n with
    | zero => exact hF
    | succ n ih => rw [Function.iterate_succ_apply']; exact polyBound_thetaD ih
  induction j with
  | zero =>
    intro u _; simp [thetaToDerivPoly]
  | succ j ih =>
    intro u hu
    have hFj : PolyCoeffBound (thetaD^[j] F) := hpoly_iter j
    have hq : ‖Complex.exp (-((u⁻¹ : ℝ) : ℂ))‖ < 1 := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
      exact neg_lt_zero.mpr (inv_pos.mpr hu)
    -- Derivative of `t ↦ value (thetaD^[j] F) (exp (-t⁻¹))` at `u` equals `u⁻² * value (thetaD^[j+1] F) (exp (-u⁻¹))`.
    have hderiv_val : HasDerivAt (fun t : ℝ => value (thetaD^[j] F) (Complex.exp (-((t⁻¹ : ℝ) : ℂ))))
        (value (PowerSeries.derivative (thetaD^[j] F)) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) *
          (((u : ℂ) ^ 2)⁻¹ * Complex.exp (-((u⁻¹ : ℝ) : ℂ)))) u := by
      have h1 : HasDerivAt (value (thetaD^[j] F))
          (value (PowerSeries.derivative (thetaD^[j] F)) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))))
          (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) := by
        simpa [seriesJet] using seriesJet_deriv hFj.to_diskCoeffBound 0 hq
      have hinv : HasDerivAt (fun t : ℝ => -(t⁻¹)) (u ^ 2)⁻¹ u := by
        simpa using (hasDerivAt_inv hu.ne').fun_neg
      have hinvC : HasDerivAt (fun t : ℝ => -((t⁻¹ : ℝ) : ℂ)) (((u : ℂ) ^ 2)⁻¹) u := by
        have := hinv.ofReal_comp
        simpa [Complex.ofReal_neg, Complex.ofReal_inv, Complex.ofReal_pow] using this
      have hexp : HasDerivAt (fun t : ℝ => Complex.exp (-((t⁻¹ : ℝ) : ℂ)))
          (Complex.exp (-((u⁻¹ : ℝ) : ℂ)) * ((u : ℂ) ^ 2)⁻¹) u :=
        hinvC.cexp
      have hcomp := (h1.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt u hexp
      simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using hcomp
    have hval_theta : value (thetaD^[j + 1] F) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) =
        Complex.exp (-((u⁻¹ : ℝ) : ℂ)) *
          value (PowerSeries.derivative (thetaD^[j] F)) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) := by
      rw [Function.iterate_succ_apply', thetaD_apply]
      have habsX := nome_abs (Complex.exp (-((u⁻¹ : ℝ) : ℂ)))
      have habsD : AbsAt (PowerSeries.derivative (thetaD^[j] F)) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) := by
        simpa [seriesJet] using seriesJet_abs hFj.to_diskCoeffBound 1 hq
      have hmul := (polynomial_value (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1)
        (S := ![PowerSeries.X, PowerSeries.derivative (thetaD^[j] F)])
        (q := Complex.exp (-((u⁻¹ : ℝ) : ℂ)))
        (fun i => by fin_cases i; exact habsX.1; exact habsD)).2
      simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] at hmul
      rw [habsX.2] at hmul
      exact hmul
    have heq_nhds : (fun t : ℝ => value (thetaD^[j] F) (Complex.exp (-((t⁻¹ : ℝ) : ℂ)))) =ᶠ[𝓝 u]
        (fun t : ℝ => ∑ k ∈ Finset.range (j + 1),
          Polynomial.eval (t : ℂ) (thetaToDerivPoly j k) *
            iteratedDeriv k (fun s : ℝ => value F (Complex.exp (-((s⁻¹ : ℝ) : ℂ)))) t) := by
      filter_upwards [Ioi_mem_nhds hu] with t ht
      exact ih ht
    have hderiv_eq : deriv (fun t : ℝ => value (thetaD^[j] F) (Complex.exp (-((t⁻¹ : ℝ) : ℂ)))) u =
        deriv (fun t : ℝ => ∑ k ∈ Finset.range (j + 1),
          Polynomial.eval (t : ℂ) (thetaToDerivPoly j k) *
            iteratedDeriv k (fun s : ℝ => value F (Complex.exp (-((s⁻¹ : ℝ) : ℂ)))) t) u :=
      heq_nhds.deriv_eq
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    have hstep_u2 : value (thetaD^[j + 1] F) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) =
        (u : ℂ) ^ 2 * deriv (fun t : ℝ => value (thetaD^[j] F) (Complex.exp (-((t⁻¹ : ℝ) : ℂ)))) u := by
      rw [hderiv_val.deriv, hval_theta]
      field_simp [hu_ne]
    rw [hstep_u2, hderiv_eq]
    exact deriv_u2_of_poly_sum hu (fun m v hv => (value_exp_inv_contDiffAt hF hv m).contDiffWithinAt) j

/-- Leibniz polynomial coefficient `C(k, m) * D^{k - m}(X^N)` for `(u^N * f(u))^{(k)}`. -/
private def leibnizPowPoly (N k m : ℕ) : Polynomial ℂ :=
  Polynomial.C ((k.choose m : ℕ) : ℂ) * (Polynomial.derivative^[k - m] (Polynomial.X ^ N))

private lemma leibnizPowPoly_self (N k : ℕ) : leibnizPowPoly N k k = Polynomial.X ^ N := by
  simp [leibnizPowPoly]

private lemma iteratedDeriv_pow_mul_add_poly {N : ℕ} {f : ℝ → ℂ} {a : Polynomial ℂ} {u : ℝ} (hu : 0 < u)
    (hf : ∀ m : ℕ, ContDiffAt ℝ m f u) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => (t : ℂ) ^ N * f t + Polynomial.eval (t : ℂ) a) u =
      (∑ m ∈ Finset.range (k + 1),
        Polynomial.eval (u : ℂ) (leibnizPowPoly N k m) * iteratedDeriv m f u) +
        Polynomial.eval (u : ℂ) (Polynomial.derivative^[k] a) := by
  have hcd_pow : ContDiffAt ℝ k (fun t : ℝ => (t : ℂ) ^ N) u :=
    (Complex.ofRealCLM.contDiff.contDiffAt.pow N).of_le le_top
  have hcd_poly : ContDiffAt ℝ k (fun t : ℝ => Polynomial.eval (t : ℂ) a) u :=
    contDiffAt_poly_eval_real a k u
  have hcd_mul : ContDiffAt ℝ k (fun t : ℝ => f t * (t : ℂ) ^ N) u :=
    (hf k).mul hcd_pow
  have hcomm : (fun t : ℝ => (t : ℂ) ^ N * f t + Polynomial.eval (t : ℂ) a) =
      (fun t : ℝ => f t * (t : ℂ) ^ N + Polynomial.eval (t : ℂ) a) := by
    funext t; ring
  rw [hcomm, iteratedDeriv_fun_add hcd_mul hcd_poly, iteratedDeriv_fun_mul (hf k) hcd_pow,
    iteratedDeriv_poly_eval_real a k u]
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  have hpow_eq : (fun t : ℝ => (t : ℂ) ^ N) = fun t : ℝ => Polynomial.eval (t : ℂ) (Polynomial.X ^ N) := by
    funext t; simp
  rw [hpow_eq, iteratedDeriv_poly_eval_real (Polynomial.X ^ N) (k - m) u]
  simp only [leibnizPowPoly, Polynomial.eval_mul, Polynomial.eval_C, mul_assoc]
  have _ := hu
  ring

/-- Combined triangular coefficient `combPoly N j m = ∑_{k=m}^j thetaToDerivPoly j k * leibnizPowPoly N k m`. -/
private def combPoly (N j m : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (j + 1), thetaToDerivPoly j k * (if m ≤ k then leibnizPowPoly N k m else 0)

private lemma combPoly_self (N j : ℕ) : combPoly N j j = Polynomial.X ^ (2 * j + N) := by
  unfold combPoly
  rw [Finset.sum_range_succ, Finset.sum_eq_zero]
  · simp [thetaToDerivPoly_self, leibnizPowPoly_self, pow_add]
  · intro k hk
    have hlt : k < j := Finset.mem_range.mp hk
    rw [ite_eq_right_iff.mpr (by omega), mul_zero]

/-- Combined affine polynomial shift `shiftPoly a j = ∑_{k=0}^j thetaToDerivPoly j k * D^k a`. -/
private def shiftPoly (a : Polynomial ℂ) (j : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (j + 1), thetaToDerivPoly j k * (Polynomial.derivative^[k] a)

/-- **Section 2B Master Transfer (`joint_poly_ode_of_dep`)**:
If `H : Fin K → PowerSeries ℂ` with `PolyCoeffBound (H i)` is jointly differentially dependent over
`ℂ(X)`, and for each `i` we have `value (H i) (exp (-u⁻¹)) = u^{N i} * f i u + eval u (a i)` on `u > 0`,
then there exist `r : ℕ` and a **nonzero** `Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)`
annihilating `(iteratedDeriv j (f i) u)` for all `u > 0`. -/
theorem joint_poly_ode_of_dep {K : ℕ} {H : Fin K → PowerSeries ℂ}
    (hH_bd : ∀ i : Fin K, PolyCoeffBound (H i))
    {N : Fin K → ℕ} {a : Fin K → Polynomial ℂ} {f : Fin K → ℝ → ℂ}
    (hf_rel : ∀ (i : Fin K) {u : ℝ}, 0 < u →
      value (H i) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) =
        (u : ℂ) ^ (N i) * f i u + Polynomial.eval (u : ℂ) (a i))
    (hdep : ¬ AlgebraicIndependent ℂ (jointCoords H)) :
    ∃ (r : ℕ) (Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)),
      Q ≠ 0 ∧ ∀ u : ℝ, 0 < u →
        MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) => iteratedDeriv ij.2.val (f ij.1) u)
          (jointEvalU Q (u : ℂ)) = 0 := by
  classical
  obtain ⟨r, P, hP_ne, hP_zero⟩ := joint_autonomous_theta_of_dep hdep
  -- Smoothness of `f i` on `(0, ∞)` from `f i u = u^{-N i} * (value (H i) (exp (-u⁻¹)) - eval u (a i))`.
  have hf_cd : ∀ (i : Fin K) {u : ℝ}, 0 < u → ∀ m : ℕ, ContDiffAt ℝ m (f i) u := by
    intro i u hu m
    have heq : f i =ᶠ[𝓝 u] fun t : ℝ =>
        ((t : ℂ) ^ (N i))⁻¹ * (value (H i) (Complex.exp (-((t⁻¹ : ℝ) : ℂ))) - Polynomial.eval (t : ℂ) (a i)) := by
      filter_upwards [Ioi_mem_nhds hu] with t ht
      have ht_ne : (t : ℂ) ^ (N i) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ht.ne')
      rw [hf_rel i ht, add_sub_cancel_right, inv_mul_cancel_left₀ ht_ne]
    have hcd1 : ContDiffAt ℝ m (fun t : ℝ => ((t : ℂ) ^ (N i))⁻¹) u :=
      ((Complex.ofRealCLM.contDiff.contDiffAt.pow (N i)).inv
        (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hu.ne'))).of_le le_top
    have hcd2 : ContDiffAt ℝ m (fun t : ℝ => value (H i) (Complex.exp (-((t⁻¹ : ℝ) : ℂ)))) u :=
      value_exp_inv_contDiffAt (hH_bd i) hu m
    have hcd3 : ContDiffAt ℝ m (fun t : ℝ => Polynomial.eval (t : ℂ) (a i)) u :=
      contDiffAt_poly_eval_real (a i) m u
    exact (hcd1.mul (hcd2.sub hcd3)).congr_of_eventuallyEq heq
  -- Express `value (thetaD^[j] (H i)) (exp (-u⁻¹))` in terms of `iteratedDeriv m (f i) u`.
  have hθ_to_f : ∀ (i : Fin K) (j : ℕ) {u : ℝ}, 0 < u →
      value (thetaD^[j] (H i)) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) =
        (∑ m ∈ Finset.range (j + 1),
          Polynomial.eval (u : ℂ) (combPoly (N i) j m) * iteratedDeriv m (f i) u) +
          Polynomial.eval (u : ℂ) (shiftPoly (a i) j) := by
    intro i j u hu
    rw [value_thetaD_iter_exp_inv (hH_bd i) j hu]
    have hcongr_k : ∀ k ∈ Finset.range (j + 1),
        iteratedDeriv k (fun t : ℝ => value (H i) (Complex.exp (-((t⁻¹ : ℝ) : ℂ)))) u =
          (∑ m ∈ Finset.range (k + 1),
            Polynomial.eval (u : ℂ) (leibnizPowPoly (N i) k m) * iteratedDeriv m (f i) u) +
            Polynomial.eval (u : ℂ) (Polynomial.derivative^[k] (a i)) := fun k _ => by
      have heq_nhds : (fun t : ℝ => value (H i) (Complex.exp (-((t⁻¹ : ℝ) : ℂ)))) =ᶠ[𝓝 u]
          (fun t : ℝ => (t : ℂ) ^ (N i) * f i t + Polynomial.eval (t : ℂ) (a i)) := by
        filter_upwards [Ioi_mem_nhds hu] with t ht
        exact hf_rel i ht
      rw [heq_nhds.iteratedDeriv_eq k]
      exact iteratedDeriv_pow_mul_add_poly hu (hf_cd i hu) k
    calc ∑ k ∈ Finset.range (j + 1),
          Polynomial.eval (u : ℂ) (thetaToDerivPoly j k) *
            iteratedDeriv k (fun t : ℝ => value (H i) (Complex.exp (-((t⁻¹ : ℝ) : ℂ)))) u
        = ∑ k ∈ Finset.range (j + 1),
            Polynomial.eval (u : ℂ) (thetaToDerivPoly j k) *
              ((∑ m ∈ Finset.range (k + 1),
                Polynomial.eval (u : ℂ) (leibnizPowPoly (N i) k m) * iteratedDeriv m (f i) u) +
                Polynomial.eval (u : ℂ) (Polynomial.derivative^[k] (a i))) :=
          Finset.sum_congr rfl fun k hk => by rw [hcongr_k k hk]
      _ = (∑ k ∈ Finset.range (j + 1), ∑ m ∈ Finset.range (j + 1),
            Polynomial.eval (u : ℂ) (thetaToDerivPoly j k) *
              (if m ≤ k then Polynomial.eval (u : ℂ) (leibnizPowPoly (N i) k m) * iteratedDeriv m (f i) u else 0)) +
          Polynomial.eval (u : ℂ) (shiftPoly (a i) j) := by
          simp_rw [mul_add, Finset.sum_add_distrib]
          congr 1
          · refine Finset.sum_congr rfl fun k hk => ?_
            have hk_le : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            rw [Finset.mul_sum]
            symm
            rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hk_le))]
            · refine Finset.sum_congr rfl fun m hm => ?_
              have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
              simp [hmk]
            · intro m _ hm
              have hgt : ¬ m ≤ k := by
                intro hle; exact hm (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
              simp [hgt]
          · dsimp only [shiftPoly]
            change _ = Polynomial.evalRingHom (u : ℂ) (∑ k ∈ Finset.range (j + 1), _)
            rw [map_sum]
            refine Finset.sum_congr rfl fun k _ => by simp
      _ = (∑ m ∈ Finset.range (j + 1),
            Polynomial.eval (u : ℂ) (combPoly (N i) j m) * iteratedDeriv m (f i) u) +
          Polynomial.eval (u : ℂ) (shiftPoly (a i) j) := by
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun m _ => ?_
          dsimp only [combPoly]
          change _ = Polynomial.evalRingHom (u : ℂ) (∑ k ∈ Finset.range (j + 1), _) * _
          rw [map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          by_cases hmk : m ≤ k <;> simp [hmk, mul_assoc]
  -- Define the triangular affine substitution `subPoly : Fin K × Fin (r + 1) → MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)`.
  let subPoly (ij : Fin K × Fin (r + 1)) : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ) :=
    (∑ m : Fin (r + 1),
      if m.1 ≤ ij.2.1 then MvPolynomial.C (combPoly (N ij.1) ij.2.1 m.1) * MvPolynomial.X (ij.1, m) else 0) +
      MvPolynomial.C (shiftPoly (a ij.1) ij.2.1)
  let cToP : ℂ →+* MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ) :=
    MvPolynomial.C.comp Polynomial.C
  let Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ) :=
    MvPolynomial.eval₂ cToP subPoly P
  refine ⟨r, Q, ?_, ?_⟩
  · -- Prove `Q ≠ 0` by constructing the exact triangular left-inverse over `RatFunc ℂ`!
    let K_rf := RatFunc ℂ
    let ιP : Polynomial ℂ →+* K_rf := algebraMap (Polynomial ℂ) K_rf
    let target := MvPolynomial (Fin K × Fin (r + 1)) K_rf
    have hdiag_ne : ∀ (i : Fin K) (m : ℕ), ιP (combPoly (N i) m m) ≠ 0 := fun i m => by
      rw [combPoly_self]
      have hX_ne : (Polynomial.X : Polynomial ℂ) ^ (2 * m + N i) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
      exact (map_ne_zero_iff ιP (IsFractionRing.injective (Polynomial ℂ) K_rf)).mpr hX_ne
    let invRow : Fin K → (j : ℕ) → target := fun i =>
      WellFounded.fix Nat.lt_wfRel.wf fun j rec =>
        if hj : j < r + 1 then
          MvPolynomial.C (ιP (combPoly (N i) j j))⁻¹ *
            (MvPolynomial.X (i, ⟨j, hj⟩) - MvPolynomial.C (ιP (shiftPoly (a i) j)) -
              ∑ m : Fin (r + 1), if hm : m.1 < j then
                MvPolynomial.C (ιP (combPoly (N i) j m.1)) * rec m.1 hm else 0)
        else 0
    let ψ : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ) →+* target :=
      MvPolynomial.eval₂Hom (MvPolynomial.C.comp ιP) (fun ij => invRow ij.1 ij.2.1)
    have hψ_sub : ∀ ij : Fin K × Fin (r + 1), ψ (subPoly ij) = MvPolynomial.X ij := by
      rintro ⟨i, j⟩
      dsimp only [subPoly]
      rw [map_add, map_sum, MvPolynomial.eval₂Hom_C]
      have hsplit : (∑ m : Fin (r + 1), ψ (if m.1 ≤ j.1 then
          MvPolynomial.C (combPoly (N i) j.1 m.1) * MvPolynomial.X (i, m) else 0)) =
          MvPolynomial.C (ιP (combPoly (N i) j.1 j.1)) * invRow i j.1 +
            ∑ m : Fin (r + 1), if m.1 < j.1 then
              MvPolynomial.C (ιP (combPoly (N i) j.1 m.1)) * invRow i m.1 else 0 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        have hdiag : ψ (if j.1 ≤ j.1 then MvPolynomial.C (combPoly (N i) j.1 j.1) * MvPolynomial.X (i, j) else 0) =
            MvPolynomial.C (ιP (combPoly (N i) j.1 j.1)) * invRow i j.1 := by
          simp [ψ]
        rw [hdiag]
        congr 1
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        simp only [lt_self_iff_false, ↓reduceIte, zero_add]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hne : m ≠ j := (Finset.mem_erase.mp hm).1
        have hiff : m.1 ≤ j.1 ↔ m.1 < j.1 :=
          ⟨fun hle => lt_of_le_of_ne hle (fun heq => hne (Fin.ext heq)), le_of_lt⟩
        by_cases hlt : m.1 < j.1
        · rw [ite_eq_left_iff.mpr (fun h => (h (hiff.mpr hlt)).elim),
            ite_eq_left_iff.mpr (fun h => (h hlt).elim)]; simp [ψ]
        · rw [ite_eq_right_iff.mpr (fun h => (hlt (hiff.mp h)).elim),
            ite_eq_right_iff.mpr (fun h => (hlt h).elim), map_zero]
      rw [hsplit]
      have hinv_eq : invRow i j.1 = MvPolynomial.C (ιP (combPoly (N i) j.1 j.1))⁻¹ *
          (MvPolynomial.X (i, j) - MvPolynomial.C (ιP (shiftPoly (a i) j.1)) -
            ∑ m : Fin (r + 1), if m.1 < j.1 then
              MvPolynomial.C (ιP (combPoly (N i) j.1 m.1)) * invRow i m.1 else 0) := by
        dsimp only [invRow]
        rw [WellFounded.fix_eq]
        simp only [j.isLt, ↓reduceDIte, dite_eq_ite, Fin.eta]
      rw [hinv_eq, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (hdiag_ne i j.1), map_one, one_mul]
      simp only [RingHom.comp_apply]
      ring
    have hψ_eval : ∀ P' : MvPolynomial (Fin K × Fin (r + 1)) ℂ,
        ψ (MvPolynomial.eval₂ cToP subPoly P') = MvPolynomial.map (algebraMap ℂ K_rf) P' := by
      intro P'
      induction P' using MvPolynomial.induction_on with
      | C c =>
        simp only [MvPolynomial.eval₂_C, cToP, RingHom.comp_apply, ψ, MvPolynomial.eval₂Hom_C,
          MvPolynomial.map_C]
        rfl
      | add A B hA hB => simp only [map_add, MvPolynomial.eval₂_add, hA, hB]
      | mul_X A v hA =>
        rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul, hA, hψ_sub v, map_mul, MvPolynomial.map_X]
    intro hQ0
    have h1 := congrArg ψ hQ0
    rw [show Q = MvPolynomial.eval₂ cToP subPoly P from rfl, hψ_eval P, map_zero] at h1
    exact hP_ne (MvPolynomial.map_injective (algebraMap ℂ K_rf) (algebraMap ℂ K_rf).injective
      (h1.trans (map_zero _).symm))
  · -- Prove `jointEvalU Q u` vanishes at `(iteratedDeriv j (f i) u)` for all `u > 0`!
    intro u hu
    have hval_sub : ∀ ij : Fin K × Fin (r + 1),
        MvPolynomial.eval (fun kl : Fin K × Fin (r + 1) => iteratedDeriv kl.2.val (f kl.1) u)
          (jointEvalU (subPoly ij) (u : ℂ)) =
        value (thetaD^[ij.2.val] (H ij.1)) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) := by
      rintro ⟨i, j⟩
      rw [hθ_to_f i j.1 hu]
      dsimp only [subPoly, jointEvalU]
      simp only [map_add, map_sum, MvPolynomial.map_C, Polynomial.coe_evalRingHom,
        MvPolynomial.eval_C]
      congr 1
      have hsum_fin : (∑ m : Fin (r + 1), MvPolynomial.eval (fun kl => iteratedDeriv kl.2.val (f kl.1) u)
          (MvPolynomial.map (Polynomial.evalRingHom (u : ℂ))
            (if m.1 ≤ j.1 then MvPolynomial.C (combPoly (N i) j.1 m.1) * MvPolynomial.X (i, m) else 0))) =
          ∑ m ∈ Finset.range (r + 1),
            if m ≤ j.1 then Polynomial.eval (u : ℂ) (combPoly (N i) j.1 m) * iteratedDeriv m (f i) u else 0 := by
        rw [← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun m _ => ?_
        by_cases hm : m.1 ≤ j.1 <;> simp [hm]
      rw [hsum_fin]
      symm
      rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt j.isLt))]
      · refine Finset.sum_congr rfl fun m hm => ?_
        have hle : m ≤ j.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
        simp [hle]
      · intro m _ hm
        have hgt : ¬ m ≤ j.1 := fun hle => hm (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
        simp [hgt]
    have hcomp_eval : ∀ P' : MvPolynomial (Fin K × Fin (r + 1)) ℂ,
        MvPolynomial.eval (fun kl : Fin K × Fin (r + 1) => iteratedDeriv kl.2.val (f kl.1) u)
          (jointEvalU (MvPolynomial.eval₂ cToP subPoly P') (u : ℂ)) =
        MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) =>
          value (thetaD^[ij.2.val] (H ij.1)) (Complex.exp (-((u⁻¹ : ℝ) : ℂ)))) P' := by
      intro P'
      induction P' using MvPolynomial.induction_on with
      | C c => simp [cToP, jointEvalU]
      | add A B hA hB =>
        rw [MvPolynomial.eval₂_add, jointEvalU, map_add, map_add, map_add]
        exact congrArg₂ (· + ·) hA hB
      | mul_X A v hA =>
        rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, jointEvalU, map_mul, map_mul]
        change MvPolynomial.eval _ (jointEvalU (MvPolynomial.eval₂ cToP subPoly A) (u : ℂ)) *
          MvPolynomial.eval _ (jointEvalU (subPoly v) (u : ℂ)) = _
        rw [hA, hval_sub v, map_mul, MvPolynomial.eval_X]
    rw [show Q = MvPolynomial.eval₂ cToP subPoly P from rfl, hcomp_eval P]
    have hq : ‖Complex.exp (-((u⁻¹ : ℝ) : ℂ))‖ < 1 := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
      exact neg_lt_zero.mpr (inv_pos.mpr hu)
    have habs : ∀ ij : Fin K × Fin (r + 1),
        AbsAt (thetaD^[ij.2.val] (H ij.1)) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) := by
      intro ij
      have hpb : PolyCoeffBound (thetaD^[ij.2.val] (H ij.1)) := by
        induction ij.2.val with
        | zero => exact hH_bd ij.1
        | succ n ih => rw [Function.iterate_succ_apply']; exact polyBound_thetaD ih
      simpa [seriesJet] using seriesJet_abs hpb.to_diskCoeffBound 0 hq
    have hvalP := (polynomial_value P habs).2
    rw [← hvalP, hP_zero]
    simp [value, term]




/-! #### 2C. Shared-Lattice Multi-Function Simple-Pole Stokes–Vandermonde Engine -/

section SharedLatticeStokes

private lemma uLaurent_pow' (k : ℕ) :
    uLaurent ^ k = HahnSeries.single (-(k : ℤ)) (1 : ℂ) := by
  induction k with
  | zero => simp [uLaurent]
  | succ k ih =>
    rw [pow_succ, ih, uLaurent, HahnSeries.single_mul_single, one_mul]
    have hidx : -(k : ℤ) + (-1 : ℤ) = -((k + 1 : ℕ) : ℤ) := by omega
    rw [hidx]

private def revPolyJ (N : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ (N - k)

private lemma poly_finset_sum_coeffJ {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) (m : ℕ) :
    (∑ i ∈ s, f i).coeff m = ∑ i ∈ s, (f i).coeff m := by
  simpa only [Polynomial.lcoeff_apply] using map_sum (Polynomial.lcoeff ℂ m) f s

private lemma revPolyJ_eval_inv {N : ℕ} (p : Polynomial ℂ) (hp : p.natDegree ≤ N)
    {u : ℂ} (hu : u ≠ 0) :
    (revPolyJ N p).eval u⁻¹ = u⁻¹ ^ N * p.eval u := by
  have hsum : p = ∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ k :=
    Polynomial.as_sum_range_C_mul_X_pow' p (Nat.lt_succ_of_le hp)
  conv_rhs => rw [hsum]
  change Polynomial.evalRingHom u⁻¹ (revPolyJ N p) = u⁻¹ ^ N * Polynomial.evalRingHom u _
  simp only [revPolyJ, map_sum, map_mul, Polynomial.coe_evalRingHom, Polynomial.eval_C,
    map_pow, Polynomial.eval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have heq : u⁻¹ ^ (N - k) = u⁻¹ ^ N * u ^ k := by
    calc u⁻¹ ^ (N - k) = u⁻¹ ^ (N - k) * (u⁻¹ ^ k * u ^ k) := by
          rw [← mul_pow, inv_mul_cancel₀ hu, one_pow, mul_one]
      _ = (u⁻¹ ^ (N - k) * u⁻¹ ^ k) * u ^ k := by ring
      _ = u⁻¹ ^ N * u ^ k := by rw [← pow_add, Nat.sub_add_cancel hk_le]
  rw [heq]; ring

private lemma single_mul_polyToLaurentJ {N : ℕ} (p : Polynomial ℂ) (hp : p.natDegree ≤ N) :
    HahnSeries.single (N : ℤ) (1 : ℂ) * polyToLaurent p =
      (((revPolyJ N p : Polynomial ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
  have hsum : p = ∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ k :=
    Polynomial.as_sum_range_C_mul_X_pow' p (Nat.lt_succ_of_le hp)
  conv_lhs => rw [hsum]
  have halg : ∀ c : ℂ, algebraMap ℂ (LaurentSeries ℂ) c = HahnSeries.C c := fun c =>
    HahnSeries.ofPowerSeries_C c
  have hL : HahnSeries.single (N : ℤ) (1 : ℂ) *
      polyToLaurent (∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ k) =
      ∑ k ∈ Finset.range (N + 1), HahnSeries.single (N : ℤ) (1 : ℂ) *
        (HahnSeries.C (p.coeff k) * uLaurent ^ k) := by
    simp only [polyToLaurent, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul,
      map_pow, Polynomial.aeval_C, Polynomial.aeval_X, halg, Finset.mul_sum]
  have hR : (((revPolyJ N p : Polynomial ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ∑ k ∈ Finset.range (N + 1),
        HahnSeries.C (p.coeff k) *
          ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) ^ (N - k) := by
    unfold revPolyJ
    change HahnSeries.ofPowerSeries ℤ ℂ
      (Polynomial.coeToPowerSeries.ringHom
        (∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ (N - k))) = _
    simp only [map_sum, map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, HahnSeries.ofPowerSeries_C, Polynomial.coe_X]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [uLaurent_pow' k]
  have hX : ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) ^ (N - k) =
      HahnSeries.single ((N - k : ℕ) : ℤ) (1 : ℂ) := by
    rw [← PowerSeries.coe_pow, HahnSeries.ofPowerSeries_X_pow]
  rw [hX, ← mul_assoc, mul_comm (HahnSeries.single (N : ℤ) 1) (HahnSeries.C (p.coeff k)),
    mul_assoc, HahnSeries.single_mul_single, one_mul]
  have hidx : (N : ℤ) + -(k : ℤ) = ((N - k : ℕ) : ℤ) := by omega
  rw [hidx, HahnSeries.C_apply, HahnSeries.single_mul_single]

private lemma polyToLaurent_injectiveJ : Function.Injective polyToLaurent := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hp0
  have hsingle := single_mul_polyToLaurentJ p le_rfl
  rw [hp, mul_zero] at hsingle
  have hps : ((revPolyJ p.natDegree p : Polynomial ℂ) : PowerSeries ℂ) = 0 :=
    HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ) (hsingle.symm.trans (map_zero _).symm)
  have hpoly : revPolyJ p.natDegree p = 0 := Polynomial.coe_inj.mp hps
  have hcoeff0 : (revPolyJ p.natDegree p).coeff 0 = 0 := by rw [hpoly]; simp
  rw [revPolyJ, poly_finset_sum_coeffJ] at hcoeff0
  have hterm : ∀ k ∈ Finset.range (p.natDegree + 1),
      (Polynomial.C (p.coeff k) * Polynomial.X ^ (p.natDegree - k)).coeff 0 =
        if k = p.natDegree then p.coeff p.natDegree else 0 := by
    intro k hk
    have hk_le : k ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hkp : k = p.natDegree
    · subst hkp; simp
    · have hne : p.natDegree - k ≠ 0 := by omega
      simp [hkp, Ne.symm hne]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq'] at hcoeff0
  simp only [Finset.mem_range, Nat.lt_succ_self, ↓reduceIte] at hcoeff0
  exact hp0 (Polynomial.leadingCoeff_eq_zero.mp hcoeff0)

private def maxUDegJ {ι : Type*} (P : MvPolynomial ι (Polynomial ℂ)) : ℕ :=
  P.support.sup fun α => (P.coeff α).natDegree

private lemma natDegree_le_maxUDegJ {ι : Type*} (P : MvPolynomial ι (Polynomial ℂ))
    (α : ι →₀ ℕ) : (P.coeff α).natDegree ≤ maxUDegJ P := by
  by_cases hα : α ∈ P.support
  · exact Finset.le_sup (f := fun α => (P.coeff α).natDegree) hα
  · rw [MvPolynomial.notMem_support_iff.mp hα, Polynomial.natDegree_zero]
    exact Nat.zero_le _

private def revMvPolyJ {ι : Type*} (N : ℕ) (P : MvPolynomial ι (Polynomial ℂ)) :
    MvPolynomial ι (Polynomial ℂ) :=
  ∑ α ∈ P.support, MvPolynomial.monomial α (revPolyJ N (P.coeff α))

private lemma revMvPolyJ_coeff {ι : Type*} (N : ℕ) (P : MvPolynomial ι (Polynomial ℂ))
    (α : ι →₀ ℕ) :
    (revMvPolyJ N P).coeff α = revPolyJ N (P.coeff α) := by
  classical
  unfold revMvPolyJ
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · simp
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · rw [MvPolynomial.notMem_support_iff.mp hα, Finset.sum_eq_zero]
    · simp [revPolyJ]
    · intro β hβ
      have hne : β ≠ α := fun h => hα (h ▸ hβ)
      simp [hne]

private lemma jointEvalU_revMvPolyJ {K r N : ℕ}
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ))
    (hN : ∀ α, (P.coeff α).natDegree ≤ N) {u : ℂ} (hu : u ≠ 0) :
    jointEvalU (revMvPolyJ N P) u⁻¹ = (u⁻¹ ^ N) • jointEvalU P u := by
  classical
  ext α
  simp only [jointEvalU, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom, revMvPolyJ_coeff,
    MvPolynomial.coeff_smul, smul_eq_mul]
  exact revPolyJ_eval_inv (P.coeff α) (hN α) hu

private def jointFormalEvalW {K r : ℕ} (S : Fin K → PowerSeries ℂ)
    (Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) : PowerSeries ℂ :=
  MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom
    (fun ij : Fin K × Fin (r + 1) => d_u^[ij.2.val] (S ij.1)) Q

private lemma jointFormalEvalW_eq_zero_iff_poly {K r : ℕ} (S : Fin K → PowerSeries ℂ)
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) {N : ℕ}
    (hN : ∀ α, (P.coeff α).natDegree ≤ N) :
    jointFormalEvalW S (revMvPolyJ N P) = 0 ↔ jointFormalEvalPoly S P = 0 := by
  have hlink : HahnSeries.single (N : ℤ) (1 : ℂ) * jointFormalEvalPoly S P =
      ((jointFormalEvalW S (revMvPolyJ N P) : PowerSeries ℂ) : LaurentSeries ℂ) := by
    have hP_sum : P = ∑ α ∈ P.support, MvPolynomial.monomial α (P.coeff α) := MvPolynomial.as_sum P
    conv_lhs => arg 2; rw [hP_sum]
    unfold jointFormalEvalPoly jointFormalEvalW revMvPolyJ
    rw [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_sum, Finset.mul_sum]
    simp_rw [MvPolynomial.eval₂_monomial]
    change ∑ α ∈ P.support, HahnSeries.single (N : ℤ) 1 *
        (polyToLaurent (P.coeff α) * α.prod fun ij e =>
          ((d_u^[ij.2.val] (S ij.1) : PowerSeries ℂ) : LaurentSeries ℂ) ^ e) =
      HahnSeries.ofPowerSeries ℤ ℂ
        (∑ α ∈ P.support, Polynomial.coeToPowerSeries.ringHom (revPolyJ N (P.coeff α)) *
          α.prod fun ij e => (d_u^[ij.2.val] (S ij.1)) ^ e)
    rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    have hpow_eq : (α.prod fun ij e => ((d_u^[ij.2.val] (S ij.1) : PowerSeries ℂ) : LaurentSeries ℂ) ^ e) =
        ((α.prod fun ij e => (d_u^[ij.2.val] (S ij.1)) ^ e : PowerSeries ℂ) : LaurentSeries ℂ) := by
      simp only [Finsupp.prod, map_prod, map_pow]
    rw [hpow_eq, ← mul_assoc, single_mul_polyToLaurentJ (P.coeff α) (hN α),
      map_mul, Polynomial.coeToPowerSeries.ringHom_apply]
  have hsingle_ne : (HahnSeries.single (N : ℤ) (1 : ℂ)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : LaurentSeries ℂ => x.coeff (N : ℤ)) h0
    simp at this
  constructor
  · intro hw
    rw [hw, PowerSeries.coe_zero] at hlink
    exact (mul_eq_zero.mp hlink).resolve_left hsingle_ne
  · intro hp
    rw [hp, mul_zero] at hlink
    exact HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ) (hlink.symm.trans (map_zero _).symm)

/-! #### 1B. Scaling & Rotation Reduction (`θ₀` → `0`) -/

private def D_joint (K r : ℕ) (i : Fin K) (ω : ℂ) :
    MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ) →ₗ[Polynomial ℂ]
      MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ) where
  toFun P := ∑ j : Fin (r + 1), (Polynomial.C ((-ω) ^ j.val)) • MvPolynomial.pderiv (i, j) P
  map_add' P Q := by simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => by rw [(MvPolynomial.pderiv (i, j)).map_smul, smul_comm]

private lemma degree_pderiv_poly_ltJ {ι : Type*} (i : ι) (P : MvPolynomial ι (Polynomial ℂ))
    (h : 0 < P.totalDegree) : (MvPolynomial.pderiv i P).totalDegree < P.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree_eq]
  apply lt_of_le_of_lt (Finset.sup_le fun m hm => ?_) (Nat.pred_lt h.ne')
  have hn := MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hn
  have hs := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hn))
  change ((m + Finsupp.single i 1).sum fun _ => id) ≤ _ at hs
  rw [← Finsupp.card_toMultiset, Finsupp.toMultiset_add, Finsupp.toMultiset_single] at hs
  simp at hs
  rw [Finsupp.card_toMultiset, Nat.pred_eq_sub_one]
  omega

private lemma totalDegree_poly_sum_ltJ {ι σ : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → MvPolynomial σ (Polynomial ℂ)) {d : ℕ} (hd : 0 < d)
    (hf : ∀ i ∈ s, (f i).totalDegree < d) :
    (∑ i ∈ s, f i).totalDegree < d := by
  induction s using Finset.induction_on with
  | empty => simpa using hd
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (MvPolynomial.totalDegree_add _ _).trans_lt
      (max_lt (hf i (Finset.mem_insert_self i s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))))

private lemma degree_D_joint_lt {K r : ℕ} (i : Fin K) (ω : ℂ)
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) (h : 0 < P.totalDegree) :
    (D_joint K r i ω P).totalDegree < P.totalDegree := by
  unfold D_joint
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  refine totalDegree_poly_sum_ltJ Finset.univ _ h fun j _ => ?_
  exact (MvPolynomial.totalDegree_smul_le _ _).trans_lt (degree_pderiv_poly_ltJ (i, j) P h)

private lemma jointEvalU_D_joint {K r : ℕ} (i : Fin K) (ω u : ℂ)
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) :
    jointEvalU (D_joint K r i ω P) u =
      ∑ j : Fin (r + 1), ((-ω) ^ j.val) • MvPolynomial.pderiv (i, j) (jointEvalU P u) := by
  unfold D_joint jointEvalU
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, MvPolynomial.pderiv_map, MvPolynomial.smul_eq_C_mul]

private def lineSliceAny {ι : Type*} (x v : ι → ℂ) :
    MvPolynomial ι ℂ →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval fun j => Polynomial.C (x j) + Polynomial.C (v j) * Polynomial.X

private lemma lineSliceAny_eval {ι : Type*} (x v : ι → ℂ) (P : MvPolynomial ι ℂ) (a : ℂ) :
    (lineSliceAny x v P).eval a = MvPolynomial.eval (fun j => x j + a * v j) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [lineSliceAny]
  | add A B hA hB => simp only [map_add, Polynomial.eval_add, hA, hB]
  | mul_X A k hA =>
    rw [map_mul, Polynomial.eval_mul, hA]
    simp only [lineSliceAny, MvPolynomial.aeval_X, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, map_mul, MvPolynomial.eval_X]
    ring

private lemma derivative_lineSliceAny {ι : Type*} [Fintype ι] [DecidableEq ι] (x v : ι → ℂ)
    (P : MvPolynomial ι ℂ) :
    Polynomial.derivative (lineSliceAny x v P) =
      ∑ j : ι, Polynomial.C (v j) * lineSliceAny x v (MvPolynomial.pderiv j P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [lineSliceAny]
  | add A B hA hB =>
    simp only [map_add, hA, hB, mul_add, Finset.sum_add_distrib]
  | mul_X A k hA =>
    simp only [map_mul, Polynomial.derivative_mul, hA, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_X, Pi.single_apply, map_add, mul_add, Finset.sum_add_distrib]
    have hdk : Polynomial.derivative (lineSliceAny x v (MvPolynomial.X k)) = Polynomial.C (v k) := by
      simp [lineSliceAny]
    rw [hdk]
    have h1 : (∑ j : ι, Polynomial.C (v j) * lineSliceAny x v (MvPolynomial.pderiv j A)) *
          lineSliceAny x v (MvPolynomial.X k) =
        ∑ j : ι, Polynomial.C (v j) *
          (lineSliceAny x v (MvPolynomial.pderiv j A) * lineSliceAny x v (MvPolynomial.X k)) := by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => by ring
    have h2 : ∑ j : ι, Polynomial.C (v j) *
          (lineSliceAny x v A * lineSliceAny x v (if k = j then 1 else 0)) =
        lineSliceAny x v A * Polynomial.C (v k) := by
      trans ∑ j : ι, if k = j then lineSliceAny x v A * Polynomial.C (v k) else 0
      · refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs with hkj
        · subst hkj; simp [mul_comm]
        · simp
      · simp
    rw [h1, h2]

private lemma shift_invariant_any {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℂ) (P : MvPolynomial ι ℂ)
    (hP : ∑ j : ι, v j • MvPolynomial.pderiv j P = 0) (x : ι → ℂ) (a : ℂ) :
    MvPolynomial.eval (fun j => x j + a * v j) P = MvPolynomial.eval x P := by
  have hd : Polynomial.derivative (lineSliceAny x v P) = 0 := by
    rw [derivative_lineSliceAny]
    have h0 : lineSliceAny x v (∑ j : ι, v j • MvPolynomial.pderiv j P) = 0 := by
      rw [hP, map_zero]
    rw [map_sum] at h0
    refine (Eq.trans ?_ h0)
    refine Finset.sum_congr rfl fun j _ => by
      rw [MvPolynomial.smul_eq_C_mul, map_mul]; simp [lineSliceAny]
  have hc := Polynomial.eq_C_of_derivative_eq_zero hd
  have he : (lineSliceAny x v P).eval a = (lineSliceAny x v P).eval 0 := by
    rw [hc, Polynomial.eval_C, Polynomial.eval_C]
  rw [lineSliceAny_eval, lineSliceAny_eval] at he
  simpa using he

private lemma eval_shift_taylor_bound_any {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial ι ℂ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x v : ι → ℂ) (a : ℂ),
      (∀ j, ‖x j‖ ≤ M) → (∀ j, ‖v j‖ ≤ M) → ‖a‖ ≤ 1 →
      ‖MvPolynomial.eval (fun j => x j + a * v j) P - MvPolynomial.eval x P -
        a * ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j P) * v j‖ ≤
        C * ‖a‖ ^ 2 := by
  have eval_bdd : ∀ Q : MvPolynomial ι ℂ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ι → ℂ, (∀ j, ‖y j‖ ≤ M) → ‖MvPolynomial.eval y Q‖ ≤ B := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C c => exact ⟨‖c‖, norm_nonneg _, fun _ _ => by simp⟩
    | add A B hA hB =>
      obtain ⟨BA, hBA, hbA⟩ := hA
      obtain ⟨BB, hBB, hbB⟩ := hB
      refine ⟨BA + BB, add_nonneg hBA hBB, fun y hy => ?_⟩
      simpa only [map_add] using (norm_add_le _ _).trans (add_le_add (hbA y hy) (hbB y hy))
    | mul_X A k hA =>
      obtain ⟨BA, hBA, hbA⟩ := hA
      refine ⟨BA * M, mul_nonneg hBA hM, fun y hy => ?_⟩
      simp only [map_mul, MvPolynomial.eval_X, norm_mul]
      exact mul_le_mul (hbA y hy) (hy k) (norm_nonneg _) hBA
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨0, le_rfl, fun x v a _ _ _ => by simp⟩
  | add A B hA hB =>
    obtain ⟨CA, hCA, hbA⟩ := hA
    obtain ⟨CB, hCB, hbB⟩ := hB
    refine ⟨CA + CB, add_nonneg hCA hCB, fun x v a hx hv ha => ?_⟩
    have hsplit : MvPolynomial.eval (fun j => x j + a * v j) (A + B) - MvPolynomial.eval x (A + B) -
        a * ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j (A + B)) * v j =
        (MvPolynomial.eval (fun j => x j + a * v j) A - MvPolynomial.eval x A -
          a * ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j A) * v j) +
        (MvPolynomial.eval (fun j => x j + a * v j) B - MvPolynomial.eval x B -
          a * ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j B) * v j) := by
      simp only [map_add, add_mul, Finset.sum_add_distrib]; ring
    rw [hsplit, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hbA x v a hx hv ha) (hbB x v a hx hv ha))
  | mul_X A k hA =>
    obtain ⟨CA, hCA, hbA⟩ := hA
    obtain ⟨BA, hBA, hAbdd⟩ := eval_bdd A
    have hderivBdd : ∃ BD : ℝ, 0 ≤ BD ∧ ∀ x v : ι → ℂ,
        (∀ j, ‖x j‖ ≤ M) → (∀ j, ‖v j‖ ≤ M) →
        ‖∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j A) * v j‖ ≤ BD := by
      choose B hB hBbdd using fun j => eval_bdd (MvPolynomial.pderiv j A)
      refine ⟨∑ j : ι, B j * M, Finset.sum_nonneg fun j _ => mul_nonneg (hB j) hM,
        fun x v hx hv => ?_⟩
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact mul_le_mul (hBbdd j x hx) (hv j) (norm_nonneg _) (hB j)
    obtain ⟨BD, hBD, hDbdd⟩ := hderivBdd
    refine ⟨CA * (2 * M) + BD * M, by positivity, fun x v a hx hv ha => ?_⟩
    let S := ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j A) * v j
    let RA := MvPolynomial.eval (fun j => x j + a * v j) A - MvPolynomial.eval x A - a * S
    have hsum : ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j (A * MvPolynomial.X k)) * v j =
        S * x k + MvPolynomial.eval x A * v k := by
      simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single_apply, map_add, map_mul,
        MvPolynomial.eval_X, add_mul, Finset.sum_add_distrib]
      have h1 : ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j A) * x k * v j = S * x k := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => by ring
      have h2 : ∑ j : ι, MvPolynomial.eval x A *
          MvPolynomial.eval x (if k = j then 1 else 0) * v j =
          MvPolynomial.eval x A * v k := by
        trans ∑ j : ι, if k = j then MvPolynomial.eval x A * v k else 0
        · refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs with hkj
          · subst hkj; simp
          · simp
        · simp
      rw [h1, h2]
    have hid : MvPolynomial.eval (fun j => x j + a * v j) (A * MvPolynomial.X k) -
        MvPolynomial.eval x (A * MvPolynomial.X k) - a * (S * x k + MvPolynomial.eval x A * v k) =
        RA * (x k + a * v k) + a ^ 2 * (S * v k) := by
      simp only [map_mul, MvPolynomial.eval_X, RA]; ring
    rw [hsum, hid]
    have hxk : ‖x k + a * v k‖ ≤ 2 * M := by
      calc ‖x k + a * v k‖ ≤ ‖x k‖ + ‖a‖ * ‖v k‖ := (norm_add_le _ _).trans (by rw [norm_mul])
        _ ≤ M + 1 * M := add_le_add (hx k) (mul_le_mul ha (hv k) (norm_nonneg _) zero_le_one)
        _ = 2 * M := by ring
    have hRA := hbA x v a hx hv ha
    have hSv : ‖S * v k‖ ≤ BD * M := by
      rw [norm_mul]
      exact mul_le_mul (hDbdd x v hx hv) (hv k) (norm_nonneg _) hBD
    calc ‖RA * (x k + a * v k) + a ^ 2 * (S * v k)‖
        ≤ ‖RA‖ * ‖x k + a * v k‖ + ‖a ^ 2‖ * ‖S * v k‖ :=
          (norm_add_le _ _).trans (by rw [norm_mul, norm_mul])
      _ ≤ (CA * ‖a‖ ^ 2) * (2 * M) + ‖a‖ ^ 2 * (BD * M) := by
          rw [norm_pow]
          exact add_le_add
            (mul_le_mul hRA hxk (norm_nonneg _) (mul_nonneg hCA (sq_nonneg _)))
            (mul_le_mul_of_nonneg_left hSv (sq_nonneg _))
      _ = (CA * (2 * M) + BD * M) * ‖a‖ ^ 2 := by ring

private def coeffUJ {ι : Type*} (k : ℕ) (P : MvPolynomial ι (Polynomial ℂ)) :
    MvPolynomial ι ℂ :=
  ∑ α ∈ P.support, MvPolynomial.monomial α ((P.coeff α).coeff k)

private lemma coeffUJ_coeff {ι : Type*} (k : ℕ) (P : MvPolynomial ι (Polynomial ℂ))
    (α : ι →₀ ℕ) : (coeffUJ k P).coeff α = (P.coeff α).coeff k := by
  classical
  dsimp only [coeffUJ]
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · simp
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · rw [MvPolynomial.notMem_support_iff.mp hα, Polynomial.coeff_zero, Finset.sum_eq_zero]
    intro β hβ
    have hne : β ≠ α := fun h => hα (h ▸ hβ)
    simp [hne]

private lemma coeffUJ_pderiv {ι : Type*} (k : ℕ) (j : ι)
    (P : MvPolynomial ι (Polynomial ℂ)) :
    coeffUJ k (MvPolynomial.pderiv j P) = MvPolynomial.pderiv j (coeffUJ k P) := by
  ext α
  rw [coeffUJ_coeff, MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv, coeffUJ_coeff]
  have hcast : (((α j : ℕ) : Polynomial ℂ) + 1) = Polynomial.C (((α j : ℕ) : ℂ) + 1) := by
    simp [map_natCast]
  rw [hcast, mul_comm, Polynomial.coeff_C_mul, mul_comm]

private lemma coeffUJ_add {ι : Type*} (k : ℕ) (A B : MvPolynomial ι (Polynomial ℂ)) :
    coeffUJ k (A + B) = coeffUJ k A + coeffUJ k B := by
  ext α; simp [coeffUJ_coeff]

private lemma coeffUJ_C_smul {ι : Type*} (k : ℕ) (c : ℂ) (P : MvPolynomial ι (Polynomial ℂ)) :
    coeffUJ k (Polynomial.C c • P) = c • coeffUJ k P := by
  ext α
  rw [coeffUJ_coeff, MvPolynomial.coeff_smul, smul_eq_mul, Polynomial.coeff_C_mul,
    MvPolynomial.coeff_smul, smul_eq_mul, coeffUJ_coeff]

private lemma coeffUJ_sum {ι σ : Type*} (s : Finset σ) (k : ℕ)
    (f : σ → MvPolynomial ι (Polynomial ℂ)) :
    coeffUJ k (∑ i ∈ s, f i) = ∑ i ∈ s, coeffUJ k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext α; simp [coeffUJ_coeff]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, coeffUJ_add, ih, Finset.sum_insert hi]

private lemma jointEvalU_eq_sum_coeffUJ {K r : ℕ}
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) (u : ℂ) :
    jointEvalU P u = ∑ k ∈ Finset.range (maxUDegJ P + 1), u ^ k • coeffUJ k P := by
  ext α
  rw [jointEvalU, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_smul, coeffUJ_coeff, smul_eq_mul]
  have hdeg : (P.coeff α).natDegree < maxUDegJ P + 1 := Nat.lt_succ_of_le (natDegree_le_maxUDegJ P α)
  have hsum := Polynomial.as_sum_range_C_mul_X_pow' (P.coeff α) hdeg
  conv_lhs => rw [hsum]
  change Polynomial.evalRingHom u _ = _
  simp only [map_sum, map_mul, map_pow, Polynomial.coe_evalRingHom, Polynomial.eval_C,
    Polynomial.eval_X]
  refine Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **Componentwise Vandermonde Contradiction**:
If `Pmin : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)` has `0 < Pmin.totalDegree` and for
every component `i : Fin K` there are `r + 1` distinct frequencies `ω i 0, ..., ω i r` annihilating
`D_joint K r i (ω i m) Pmin = 0`, then `False`. -/

private def aPhiJ (φ : ℂ → ℂ) : Minor := ⟨0, φ⟩

private lemma aPhiJ_toSeries (φ : ℂ → ℂ) : (aPhiJ φ).toSeries = formalSeries φ := by
  ext n; cases n <;> simp [aPhiJ, Minor.toSeries, formalSeries]

private def polyMinorJ (q : Polynomial ℂ) : Minor :=
  ⟨q.coeff 0, fun z : ℂ =>
    ∑ m ∈ Finset.range q.natDegree, (q.coeff (m + 1) / (m.factorial : ℂ)) * z ^ m⟩

private lemma polyMinorJ_toSeries (q : Polynomial ℂ) :
    (polyMinorJ q).toSeries = (q : PowerSeries ℂ) := by
  ext n
  cases n with
  | zero => simp [polyMinorJ, Minor.toSeries]
  | succ k =>
    simp only [polyMinorJ, Minor.toSeries, PowerSeries.coeff_mk, Polynomial.coeff_coe]
    have hcd : ∀ m ∈ Finset.range q.natDegree,
        ContDiffAt ℂ k (fun z : ℂ => (q.coeff (m + 1) / (m.factorial : ℂ)) * z ^ m) 0 :=
      fun _ _ => (analyticAt_const.mul (analyticAt_id.pow _)).contDiffAt
    rw [iteratedDeriv_fun_sum hcd]
    have hterm : ∀ m ∈ Finset.range q.natDegree,
        iteratedDeriv k (fun z : ℂ => (q.coeff (m + 1) / (m.factorial : ℂ)) * z ^ m) 0 =
          if m = k then q.coeff (k + 1) else 0 := by
      intro m _
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
      by_cases hkm : m = k
      · subst hkm; simp only [↓reduceIte]
        have hfac : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
        field_simp [hfac]
      · simp [hkm, Ne.symm hkm]
    rw [Finset.sum_congr rfl hterm]
    by_cases hk : k < q.natDegree
    · rw [Finset.sum_ite_eq']; simp [Finset.mem_range.mpr hk]
    · have hnot : k ∉ Finset.range q.natDegree := by simpa [Finset.mem_range] using hk
      rw [Finset.sum_ite_eq', ite_eq_right_iff.mpr fun hmem => absurd hmem hnot]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

private lemma polyMinorJ_good (q : Polynomial ℂ) (U : Set ℂ) (d : ℂ) :
    (polyMinorJ q).Good U d := by
  refine ⟨?_, ?_⟩
  · intro z _; dsimp only [polyMinorJ]
    exact Finset.analyticAt_fun_sum _ fun m _ => by fun_prop
  · refine ⟨∑ m ∈ Finset.range q.natDegree, ‖d‖ ^ (m + 1) * ‖q.coeff (m + 1)‖, 1,
      Finset.sum_nonneg (fun _ _ => by positivity), zero_le_one, fun v hv => ?_⟩
    rw [Minor.pull]; dsimp only [polyMinorJ]
    rw [Finset.mul_sum, one_mul, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [mul_pow, norm_mul, norm_mul, norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
    have hpow : v ^ m / (m.factorial : ℝ) ≤ Real.exp v := Real.pow_div_factorial_le_exp v hv m
    calc ‖d‖ * (‖q.coeff (m + 1)‖ / (m.factorial : ℝ) * (‖d‖ ^ m * v ^ m))
        = (‖d‖ ^ (m + 1) * ‖q.coeff (m + 1)‖) * (v ^ m / (m.factorial : ℝ)) := by
          rw [pow_succ']; ring
      _ ≤ (‖d‖ ^ (m + 1) * ‖q.coeff (m + 1)‖) * Real.exp v :=
          mul_le_mul_of_nonneg_left hpow (by positivity)

private lemma polyMinorJ_value (q : Polynomial ℂ) {d p : ℂ} (hp : 0 < (p * d).re) :
    (polyMinorJ q).value d p = q.eval p⁻¹ := by
  have hpd0 : p * d ≠ 0 := fun h0 => by simp [h0] at hp
  have hp0 : p ≠ 0 := left_ne_zero_of_mul hpd0
  have hd0 : d ≠ 0 := right_ne_zero_of_mul hpd0
  unfold Minor.value polyMinorJ complexLaplace; dsimp only
  have heq : (fun v : ℝ => damped (p * d)
      (Minor.pull d fun z => ∑ m ∈ Finset.range q.natDegree,
        (q.coeff (m + 1) / (m.factorial : ℂ)) * z ^ m) v) =
      fun v : ℝ => ∑ m ∈ Finset.range q.natDegree,
        (d ^ (m + 1) * (q.coeff (m + 1) / (m.factorial : ℂ))) *
          (Complex.exp (-(p * d) * (v : ℂ)) * (v : ℂ) ^ m) := by
    funext v; simp only [damped, Minor.pull, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => by rw [mul_pow, pow_succ']; ring
  rw [heq]
  have hi_term : ∀ m ∈ Finset.range q.natDegree,
      IntegrableOn (fun v : ℝ => (d ^ (m + 1) * (q.coeff (m + 1) / (m.factorial : ℂ))) *
        (Complex.exp (-(p * d) * (v : ℂ)) * (v : ℂ) ^ m)) (Ioi 0) := by
    intro m _
    refine Integrable.const_mul ?_ _
    refine ((integrableOn_exp_mul_Ioi (show -((p * d).re / 2) < 0 by linarith) 0).const_mul
      ((m.factorial : ℝ) / ((p * d).re / 2) ^ m)).mono'
      ((by fun_prop : Continuous (fun v : ℝ =>
        Complex.exp (-(p * d) * (v : ℂ)) * (v : ℂ) ^ m)).aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv
    change 0 < v at hv
    rw [norm_mul, Complex.norm_exp, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv.le]
    have hre2 : (-(p * d) * (v : ℂ)).re = -(p * d).re * v := by simp [Complex.mul_re]; ring
    rw [hre2]
    have hpow := Real.pow_div_factorial_le_exp ((p * d).re / 2 * v) (by positivity) m
    have h1 : 0 < ((p * d).re / 2) ^ m := pow_pos (by positivity) m
    have h2 : 0 < (m.factorial : ℝ) := by positivity
    rw [mul_pow, div_le_iff₀ h2] at hpow
    have hvm : v ^ m ≤ ((m.factorial : ℝ) / ((p * d).re / 2) ^ m) * Real.exp ((p * d).re / 2 * v) := by
      calc v ^ m ≤ (Real.exp ((p * d).re / 2 * v) * m.factorial) / ((p * d).re / 2) ^ m :=
            (le_div_iff₀ h1).mpr (by linarith)
        _ = _ := by ring
    calc Real.exp (-(p * d).re * v) * v ^ m
        ≤ Real.exp (-(p * d).re * v) *
            (((m.factorial : ℝ) / ((p * d).re / 2) ^ m) * Real.exp ((p * d).re / 2 * v)) :=
          mul_le_mul_of_nonneg_left hvm (Real.exp_pos _).le
      _ = ((m.factorial : ℝ) / ((p * d).re / 2) ^ m) * Real.exp (-((p * d).re / 2) * v) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  rw [MeasureTheory.integral_finsetSum _ hi_term]
  have hsum_eq : ∑ m ∈ Finset.range q.natDegree,
      ∫ v in Ioi (0 : ℝ), (d ^ (m + 1) * (q.coeff (m + 1) / (m.factorial : ℂ))) *
        (Complex.exp (-(p * d) * (v : ℂ)) * (v : ℂ) ^ m) =
      ∑ m ∈ Finset.range q.natDegree, q.coeff (m + 1) * p⁻¹ ^ (m + 1) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_const_mul, Minor.complexLaplace_monomial m hp, mul_pow, inv_pow]
    have hm_ne : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    field_simp [hm_ne, hd0, hp0]
  rw [hsum_eq, Polynomial.eval_eq_sum_range, Finset.sum_range_succ']
  simp only [pow_zero, mul_one]; ring

private inductive JointBorelExpr (K : ℕ) where
  | poly (q : Polynomial ℂ)
  | leaf (i : Fin K)
  | add (e f : JointBorelExpr K)
  | mul (e f : JointBorelExpr K)
  | jet (e : JointBorelExpr K)

namespace JointBorelExpr

private def residual {K : ℕ} (a : Fin K → Minor) : JointBorelExpr K → Minor
  | poly q => polyMinorJ q
  | leaf i => a i
  | add e f => (e.residual a).plus (f.residual a)
  | mul e f => (e.residual a).times (f.residual a)
  | jet e => (e.residual a).jet

private def eval {K : ℕ} (a : Fin K → Minor) (d : ℂ) : JointBorelExpr K → ℂ → ℂ
  | poly q => fun p => q.eval p⁻¹
  | leaf i => (a i).value d
  | add e f => fun p => e.eval a d p + f.eval a d p
  | mul e f => fun p => e.eval a d p * f.eval a d p
  | jet e => fun p => deriv (e.eval a d) p

private lemma represents {K : ℕ} (e : JointBorelExpr K) {U : Set ℂ} {d : ℂ} (hU : Domain U)
    (ray : ContainsRay U d) {a : Fin K → Minor} (ha : ∀ i, (a i).Good U d) :
    (e.residual a).Good U d ∧ e.eval a d =ᶠ[BorelStokesVandermonde.far d] (e.residual a).value d := by
  induction e with
  | poly q =>
    refine ⟨polyMinorJ_good q U d, ?_⟩
    filter_upwards [eventually_bound_far d 0] with p hp
    exact (polyMinorJ_value q hp).symm
  | leaf i => exact ⟨ha i, .rfl⟩
  | add e f he hf =>
    refine ⟨he.1.plus hf.1, ?_⟩
    filter_upwards [he.2, hf.2, Minor.good_plus_value ray he.1 hf.1] with p hp hq h
    simp only [residual, eval, h, hp, hq]
  | mul e f he hf =>
    refine ⟨he.1.times hU hf.1, ?_⟩
    filter_upwards [he.2, hf.2, Minor.good_times_value ray hU he.1 hf.1] with p hp hq h
    simp only [residual, eval, h, hp, hq]
  | jet e he =>
    refine ⟨he.1.jet, ?_⟩
    obtain ⟨R, hR⟩ := eventually_atTop.mp (eventually_comap.mp he.2)
    filter_upwards [eventually_bound_far d R, Minor.good_jet_derivative ray he.1] with p hp h
    have loc : e.eval a d =ᶠ[𝓝 p] (e.residual a).value d := by
      filter_upwards [(isOpen_lt continuous_const (Complex.continuous_re.comp
        (continuous_id.mul_const d))).mem_nhds hp] with q hq
      exact hR _ (le_of_lt hq) q rfl
    simp only [eval, residual, loc.deriv_eq, h.deriv]

private lemma jetIter_eval_eq {K : ℕ} (a : Fin K → Minor) (d : ℂ) (i : Fin K) (j : ℕ) :
    (Nat.iterate jet j (leaf i)).eval a d =
      (Nat.iterate BorelExpr.jet j BorelExpr.leaf).eval (a i) d := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (fun p => deriv ((Nat.iterate jet j (leaf i)).eval a d) p) =
      (fun p => deriv ((Nat.iterate BorelExpr.jet j BorelExpr.leaf).eval (a i) d) p)
    rw [ih]

private lemma exists_of_mvPolynomial {K r : ℕ}
    (Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) :
    ∃ e : JointBorelExpr K,
      (∀ (U : Set ℂ) (d : ℂ) (a : Fin K → Minor), Domain U → ContainsRay U d →
        (∀ i, (a i).Good U d) →
        (e.residual a).toSeries = jointFormalEvalW (fun i => (a i).toSeries) Q) ∧
      (∀ (U : Set ℂ) (d : ℂ) (a : Fin K → Minor) (_hU : Domain U) (_ray : ContainsRay U d)
        (_ha : ∀ i, (a i).Good U d) (_hd : 0 < d.re),
        ∀ᶠ u : ℝ in atTop,
          e.eval a d (u : ℂ) =
            MvPolynomial.eval
              (fun ij : Fin K × Fin (r + 1) =>
                iteratedDeriv ij.2.val (fun t : ℝ => (a ij.1).value d (t : ℂ)) u)
              (jointEvalU Q (u : ℂ)⁻¹)) := by
  induction Q using MvPolynomial.induction_on with
  | C q =>
    refine ⟨poly q, ?_, ?_⟩
    · intro U d a _ _ _
      simp [residual, polyMinorJ_toSeries, jointFormalEvalW]
    · intro U d a _ _ _ _
      exact .of_forall fun u => by simp [eval, jointEvalU]
  | add Q₁ Q₂ h₁ h₂ =>
    obtain ⟨e₁, hs₁, he₁⟩ := h₁
    obtain ⟨e₂, hs₂, he₂⟩ := h₂
    refine ⟨add e₁ e₂, ?_, ?_⟩
    · intro U d a hU ray ha
      have hg₁ := (e₁.represents hU ray ha).1.1 0 (by simpa using ray 0 le_rfl)
      have hg₂ := (e₂.represents hU ray ha).1.1 0 (by simpa using ray 0 le_rfl)
      rw [residual, Minor.toSeries_plus hg₁ hg₂, hs₁ U d a hU ray ha, hs₂ U d a hU ray ha]
      simp [jointFormalEvalW]
    · intro U d a hU ray ha hd
      filter_upwards [he₁ U d a hU ray ha hd, he₂ U d a hU ray ha hd] with u hu₁ hu₂
      simp [eval, jointEvalU, hu₁, hu₂]
  | mul_X Q₁ ij h₁ =>
    obtain ⟨e₁, hs₁, he₁⟩ := h₁
    let ej : JointBorelExpr K := Nat.iterate jet ij.2.val (leaf ij.1)
    refine ⟨mul e₁ ej, ?_, ?_⟩
    · intro U d a hU ray ha
      have h0 : (0 : ℂ) ∈ U := by simpa using ray 0 le_rfl
      have hg₁ := (e₁.represents hU ray ha).1.1 0 h0
      have hgj := (ej.represents hU ray ha).1.1 0 h0
      rw [residual, Minor.toSeries_times hg₁ hgj, hs₁ U d a hU ray ha]
      have hj_series : ∀ k : ℕ, ((Nat.iterate jet k (leaf ij.1)).residual a).toSeries =
          d_u^[k] (a ij.1).toSeries := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
          have hgk := ((Nat.iterate jet k (leaf ij.1)).represents hU ray ha).1.1 0 h0
          rw [Function.iterate_succ_apply' jet k (leaf ij.1),
            Function.iterate_succ_apply' d_u k (a ij.1).toSeries]
          exact (Minor.toSeries_jet hgk).trans (congrArg d_u ih)
      rw [hj_series ij.2.val]
      simp [jointFormalEvalW]
    · intro U d a hU ray ha hd
      have hjet_eq := (BorelExpr.jetIter_eval_eq_iteratedDeriv (a ij.1) hU ray (ha ij.1) hd ij.2.val).1
      filter_upwards [he₁ U d a hU ray ha hd, hjet_eq] with u hu₁ huj
      have heval_eq : ej.eval a d (u : ℂ) =
          (Nat.iterate BorelExpr.jet ij.2.val BorelExpr.leaf).eval (a ij.1) d (u : ℂ) :=
        congrFun (jetIter_eval_eq a d ij.1 ij.2.val) (u : ℂ)
      simp only [eval, jointEvalU, map_mul, MvPolynomial.map_X, MvPolynomial.eval_X] at hu₁ ⊢
      rw [heval_eq, hu₁, huj]

end JointBorelExpr

/-! #### 1E. Wedge Geometry, Single-Component Simple-Pole Stokes Jump at Arbitrary Cut `R`, & Joint Descent -/

private def dPlusJ (θ : ℝ) : ℂ := Complex.exp (Complex.I * (θ : ℂ))
private def dMinusJ (θ : ℝ) : ℂ := Complex.exp (-Complex.I * (θ : ℂ))

private lemma dPlusJ_eq (θ : ℝ) : dPlusJ θ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  unfold dPlusJ; rw [mul_comm Complex.I, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]

private lemma dMinusJ_eq (θ : ℝ) : dMinusJ θ = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
  unfold dMinusJ
  rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast; ring

private lemma norm_dPlusJ (θ : ℝ) : ‖dPlusJ θ‖ = 1 := by
  unfold dPlusJ; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I θ

private lemma norm_dMinusJ (θ : ℝ) : ‖dMinusJ θ‖ = 1 := by
  unfold dMinusJ; rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I (-θ)

private lemma dPlusJ_re (θ : ℝ) : (dPlusJ θ).re = Real.cos θ := by
  unfold dPlusJ; rw [mul_comm]; exact Complex.exp_ofReal_mul_I_re θ

private lemma dPlusJ_im (θ : ℝ) : (dPlusJ θ).im = Real.sin θ := by
  unfold dPlusJ; rw [mul_comm]; exact Complex.exp_ofReal_mul_I_im θ

private lemma dMinusJ_re (θ : ℝ) : (dMinusJ θ).re = Real.cos θ := by
  unfold dMinusJ
  rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

private lemma dMinusJ_im (θ : ℝ) : (dMinusJ θ).im = -Real.sin θ := by
  unfold dMinusJ
  rw [show -Complex.I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_ofReal_mul_I_im, Real.sin_neg]

private def wedgePlusJ (α₀ ε : ℝ) : Set ℂ :=
  {z : ℂ | ‖z‖ < ε ∨ (0 < z.im ∧ z.im < Real.tan α₀ * z.re)}

private def wedgeMinusJ (α₀ ε : ℝ) : Set ℂ :=
  {z : ℂ | ‖z‖ < ε ∨ (z.im < 0 ∧ -z.im < Real.tan α₀ * z.re)}

private lemma wedgePlusJ_domain {α₀ ε : ℝ} (hε : 0 < ε) : Domain (wedgePlusJ α₀ ε) := by
  refine ⟨?_, ?_⟩
  · exact (isOpen_lt continuous_norm continuous_const).union
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im (continuous_const.mul Complex.continuous_re)))
  · intro z hz t ht
    rcases hz with hball | ⟨him, htan⟩
    · left
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hball
    · rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
      · left; simpa using hε
      · right
        have hre_eq : ((t : ℂ) * z).re = t * z.re := by simp [Complex.mul_re]
        have him_eq : ((t : ℂ) * z).im = t * z.im := by simp [Complex.mul_im]
        rw [hre_eq, him_eq]
        refine ⟨mul_pos ht_pos him, ?_⟩
        calc t * z.im < t * (Real.tan α₀ * z.re) := mul_lt_mul_of_pos_left htan ht_pos
          _ = Real.tan α₀ * (t * z.re) := by ring

private lemma wedgeMinusJ_domain {α₀ ε : ℝ} (hε : 0 < ε) : Domain (wedgeMinusJ α₀ ε) := by
  refine ⟨?_, ?_⟩
  · exact (isOpen_lt continuous_norm continuous_const).union
      ((isOpen_lt Complex.continuous_im continuous_const).inter
        (isOpen_lt (continuous_neg.comp Complex.continuous_im) (continuous_const.mul Complex.continuous_re)))
  · intro z hz t ht
    rcases hz with hball | ⟨him, htan⟩
    · left
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hball
    · rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
      · left; simpa using hε
      · right
        have hre_eq : ((t : ℂ) * z).re = t * z.re := by simp [Complex.mul_re]
        have him_eq : ((t : ℂ) * z).im = t * z.im := by simp [Complex.mul_im]
        rw [hre_eq, him_eq]
        refine ⟨mul_neg_of_pos_of_neg ht_pos him, ?_⟩
        have h1 : -(t * z.im) = t * (-z.im) := by ring
        rw [h1]
        calc t * (-z.im) < t * (Real.tan α₀ * z.re) := mul_lt_mul_of_pos_left htan ht_pos
          _ = Real.tan α₀ * (t * z.re) := by ring

private lemma isPreconnected_of_starJ {U : Set ℂ} (h0 : (0 : ℂ) ∈ U)
    (hstar : ∀ z ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * z ∈ U) : IsPreconnected U := by
  refine isPreconnected_iff_subset_of_disjoint_closed.mpr fun s t hs ht hsub hdisj => ?_
  have h0_mem : (0 : ℂ) ∈ s ∪ t := hsub h0
  rcases h0_mem with h0s | h0t
  · left
    intro z hz
    let γ : ℝ → ℂ := fun τ => (τ : ℂ) * z
    have hγ_cont : Continuous γ := Complex.continuous_ofReal.mul continuous_const
    have hconn : IsPreconnected (Icc (0 : ℝ) 1) := isPreconnected_Icc
    have hsub' : Icc (0 : ℝ) 1 ⊆ γ ⁻¹' s ∪ γ ⁻¹' t := fun τ hτ => hsub (hstar z hz τ hτ)
    have hdisj' : Icc (0 : ℝ) 1 ∩ (γ ⁻¹' s ∩ γ ⁻¹' t) = ∅ := by
      ext τ; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hτ, hτs, hτt⟩
      have hmem : γ τ ∈ U ∩ (s ∩ t) := ⟨hstar z hz τ hτ, hτs, hτt⟩
      rw [hdisj] at hmem; exact hmem
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn (γ ⁻¹' s) (γ ⁻¹' t)
        (hs.preimage hγ_cont) (ht.preimage hγ_cont) hsub' hdisj' with hL | hR
    · have := hL ⟨zero_le_one, le_rfl⟩; simpa [γ] using this
    · have h0t' : (0 : ℂ) ∈ t := by simpa [γ] using hR ⟨le_rfl, zero_le_one⟩
      have hmem : (0 : ℂ) ∈ U ∩ (s ∩ t) := ⟨h0, h0s, h0t'⟩
      rw [hdisj] at hmem; exact hmem.elim
  · right
    intro z hz
    let γ : ℝ → ℂ := fun τ => (τ : ℂ) * z
    have hγ_cont : Continuous γ := Complex.continuous_ofReal.mul continuous_const
    have hconn : IsPreconnected (Icc (0 : ℝ) 1) := isPreconnected_Icc
    have hsub' : Icc (0 : ℝ) 1 ⊆ γ ⁻¹' s ∪ γ ⁻¹' t := fun τ hτ => hsub (hstar z hz τ hτ)
    have hdisj' : Icc (0 : ℝ) 1 ∩ (γ ⁻¹' s ∩ γ ⁻¹' t) = ∅ := by
      ext τ; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hτ, hτs, hτt⟩
      have hmem : γ τ ∈ U ∩ (s ∩ t) := ⟨hstar z hz τ hτ, hτs, hτt⟩
      rw [hdisj] at hmem; exact hmem
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn (γ ⁻¹' s) (γ ⁻¹' t)
        (hs.preimage hγ_cont) (ht.preimage hγ_cont) hsub' hdisj' with hL | hR
    · have h0s' : (0 : ℂ) ∈ s := by simpa [γ] using hL ⟨le_rfl, zero_le_one⟩
      have hmem : (0 : ℂ) ∈ U ∩ (s ∩ t) := ⟨h0, h0s', h0t⟩
      rw [hdisj] at hmem; exact hmem.elim
    · have := hR ⟨zero_le_one, le_rfl⟩; simpa [γ] using this

private lemma analyticAt_eqOn_zero_of_iteratedDeriv_zeroJ {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsPreconnected U) (h0 : (0 : ℂ) ∈ U) (hf : AnalyticOnNhd ℂ f U)
    (hderiv : ∀ k : ℕ, iteratedDeriv k f 0 = 0) : EqOn f 0 U := by
  refine hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU h0 ?_
  by_contra hne
  obtain ⟨n, g, hg, hg0, hfac⟩ := (hf 0 h0).exists_eventuallyEq_pow_smul_ne_zero_iff.mpr hne
  have hloc : f =ᶠ[𝓝 (0 : ℂ)] fun z => z ^ n * g z := by
    filter_upwards [hfac] with z hz; simpa [smul_eq_mul] using hz
  have hdn : iteratedDeriv n f 0 = (n.factorial : ℂ) * g 0 := by
    rw [hloc.iteratedDeriv_eq n]
    rw [iteratedDeriv_fun_mul (n := n) (x := (0 : ℂ))
      (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z ^ n) 0).contDiffAt hg.contDiffAt]
    have hterm : ∀ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * iteratedDeriv i (fun z : ℂ => z ^ n) (0 : ℂ) * iteratedDeriv (n - i) g 0 =
          if i = n then (n.factorial : ℂ) * g 0 else 0 := by
      intro i _; rw [iteratedDeriv_fun_pow_zero]
      split_ifs with hin
      · subst hin; simp [Nat.choose_self]
      · simp
    rw [Finset.sum_congr rfl hterm]; simp
  exact (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n) hg0) (hdn ▸ hderiv n)

private lemma tan_lt_tanJ {θ α₀ : ℝ} (hθ : 0 < θ) (hθα : θ < α₀) (hα : α₀ < Real.pi / 2) :
    Real.tan θ < Real.tan α₀ :=
  Real.strictMonoOn_tan ⟨by linarith, by linarith⟩ ⟨by linarith, hα⟩ hθα

private lemma cos_pos_J {θ α₀ : ℝ} (hθ : 0 < θ) (hθα : θ < α₀) (hα : α₀ < Real.pi / 2) :
    0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

private lemma sin_pos_J {θ α₀ : ℝ} (hθ : 0 < θ) (hθα : θ < α₀) (hα : α₀ < Real.pi / 2) :
    0 < Real.sin θ :=
  Real.sin_pos_of_pos_of_lt_pi hθ (by linarith)

private lemma tan_pos_J {θ α₀ : ℝ} (hθ : 0 < θ) (hθα : θ < α₀) (hα : α₀ < Real.pi / 2) :
    0 < Real.tan θ := by
  rw [Real.tan_eq_sin_div_cos]
  exact div_pos (sin_pos_J hθ hθα hα) (cos_pos_J hθ hθα hα)

private lemma wedgePlusJ_containsRay {θ α₀ ε : ℝ} (hθ : 0 < θ) (hθα : θ < α₀)
    (hα : α₀ < Real.pi / 2) (hε : 0 < ε) :
    ContainsRay (wedgePlusJ α₀ ε) (dPlusJ θ) := by
  intro v hv
  rcases eq_or_lt_of_le hv with rfl | hv_pos
  · left; simpa using hε
  · right
    have hre : (dPlusJ θ * (v : ℂ)).re = Real.cos θ * v := by
      simp [Complex.mul_re, dPlusJ_re]
    have him : (dPlusJ θ * (v : ℂ)).im = Real.sin θ * v := by
      simp [Complex.mul_im, dPlusJ_im]
    rw [hre, him]
    have hcos := cos_pos_J hθ hθα hα
    have hsin := sin_pos_J hθ hθα hα
    refine ⟨mul_pos hsin hv_pos, ?_⟩
    have htan := tan_lt_tanJ hθ hθα hα
    rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hcos] at htan
    nlinarith

private lemma wedgeMinusJ_containsRay {θ α₀ ε : ℝ} (hθ : 0 < θ) (hθα : θ < α₀)
    (hα : α₀ < Real.pi / 2) (hε : 0 < ε) :
    ContainsRay (wedgeMinusJ α₀ ε) (dMinusJ θ) := by
  intro v hv
  rcases eq_or_lt_of_le hv with rfl | hv_pos
  · left; simpa using hε
  · right
    have hre : (dMinusJ θ * (v : ℂ)).re = Real.cos θ * v := by
      simp [Complex.mul_re, dMinusJ_re]
    have him : (dMinusJ θ * (v : ℂ)).im = -(Real.sin θ * v) := by
      simp [Complex.mul_im, dMinusJ_im]
    rw [hre, him]
    have hcos := cos_pos_J hθ hθα hα
    have hsin := sin_pos_J hθ hθα hα
    refine ⟨by nlinarith, ?_⟩
    have htan := tan_lt_tanJ hθ hθα hα
    rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hcos] at htan
    nlinarith

private lemma rotatedPuncturedWedge_zero_eqJ (α₀ ε : ℝ) (ω : ℕ → ℝ) :
    rotatedPuncturedWedge 0 α₀ ε ω = puncturedWedge α₀ ε ω := by
  ext z; simp [rotatedPuncturedWedge]

private lemma wedgePlusJ_subset_punctured {α₀ ε ε₀ : ℝ} {ω : ℕ → ℝ}
    (hα : 0 < α₀) (hα2 : α₀ < Real.pi / 2) (hε₀_le : ε₀ ≤ ε) (hε₀_lt : ε₀ ≤ ω 0 / 2)
    (hω_pos : 0 < ω 0) (hω_mono : StrictMono ω) :
    wedgePlusJ α₀ ε₀ ⊆ rotatedPuncturedWedge 0 α₀ ε ω := by
  rw [rotatedPuncturedWedge_zero_eqJ]
  intro z hz
  refine ⟨?_, ?_⟩
  · rcases hz with hball | ⟨him, htan⟩
    · left; simpa [Metric.mem_ball, dist_zero_right] using hball.trans_le hε₀_le
    · right
      have htan_pos : 0 < Real.tan α₀ := by
        rw [Real.tan_eq_sin_div_cos]
        exact div_pos (Real.sin_pos_of_pos_of_lt_pi hα (by linarith))
          (Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩)
      have hre_pos : 0 < z.re := by nlinarith
      refine ⟨hre_pos, ?_⟩
      rwa [abs_of_pos him]
  · rintro ⟨m, rfl⟩
    rcases hz with hball | ⟨him, _⟩
    · rw [Complex.norm_real, Real.norm_of_nonneg (lt_of_lt_of_le hω_pos (hω_mono.monotone (Nat.zero_le m))).le] at hball
      have hle : ω 0 ≤ ω m := hω_mono.monotone (Nat.zero_le m)
      linarith
    · simp at him

private lemma wedgeMinusJ_subset_punctured {α₀ ε ε₀ : ℝ} {ω : ℕ → ℝ}
    (hα : 0 < α₀) (hα2 : α₀ < Real.pi / 2) (hε₀_le : ε₀ ≤ ε) (hε₀_lt : ε₀ ≤ ω 0 / 2)
    (hω_pos : 0 < ω 0) (hω_mono : StrictMono ω) :
    wedgeMinusJ α₀ ε₀ ⊆ rotatedPuncturedWedge 0 α₀ ε ω := by
  rw [rotatedPuncturedWedge_zero_eqJ]
  intro z hz
  refine ⟨?_, ?_⟩
  · rcases hz with hball | ⟨him, htan⟩
    · left; simpa [Metric.mem_ball, dist_zero_right] using hball.trans_le hε₀_le
    · right
      have htan_pos : 0 < Real.tan α₀ := by
        rw [Real.tan_eq_sin_div_cos]
        exact div_pos (Real.sin_pos_of_pos_of_lt_pi hα (by linarith))
          (Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩)
      have hre_pos : 0 < z.re := by nlinarith
      refine ⟨hre_pos, ?_⟩
      rwa [abs_of_neg him]
  · rintro ⟨m, rfl⟩
    rcases hz with hball | ⟨him, _⟩
    · rw [Complex.norm_real, Real.norm_of_nonneg (lt_of_lt_of_le hω_pos (hω_mono.monotone (Nat.zero_le m))).le] at hball
      have hle : ω 0 ≤ ω m := hω_mono.monotone (Nat.zero_le m)
      linarith
    · simp at him

private lemma tendsto_coe_farJ {d : ℂ} (hd : 0 < d.re) :
    Tendsto (fun u : ℝ => (u : ℂ)) atTop (BorelStokesVandermonde.far d) := by
  rw [BorelStokesVandermonde.far, Filter.tendsto_comap_iff]
  have hfun : (fun u : ℝ => ((u : ℂ) * d).re) = fun u : ℝ => d.re * u := by
    funext u; simp [Complex.mul_re]; ring
  rw [show (fun x : ℂ => (x * d).re) ∘ (fun u : ℝ => (u : ℂ)) = fun u : ℝ => d.re * u from hfun]
  exact Filter.Tendsto.const_mul_atTop hd tendsto_id

private lemma jet_residual_densityJ (φ : ℂ → ℂ) (j : ℕ) :
    ((Nat.iterate BorelExpr.jet j BorelExpr.leaf).residual (aPhiJ φ)).density =
      fun z : ℂ => (-z) ^ j * φ z := by
  induction j with
  | zero => funext z; simp [aPhiJ, BorelExpr.residual]
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    change (fun z : ℂ => -z * ((Nat.iterate BorelExpr.jet j BorelExpr.leaf).residual (aPhiJ φ)).density z) = _
    rw [ih]; funext z; rw [pow_succ']; ring

private lemma jet_residual_atomJ (φ : ℂ → ℂ) (j : ℕ) :
    ((Nat.iterate BorelExpr.jet j BorelExpr.leaf).residual (aPhiJ φ)).atom = 0 := by
  cases j with
  | zero => rfl
  | succ j =>
    rw [Function.iterate_succ_apply']
    rfl

private lemma iteratedDeriv_lateral_eq_laplaceJ {φ : ℂ → ℂ} {U : Set ℂ} {d : ℂ}
    (hU : Domain U) (hray : ContainsRay U d) (hgood : (aPhiJ φ).Good U d) (hd : 0 < d.re) (j : ℕ) :
    ∀ᶠ u : ℝ in atTop,
      iteratedDeriv j (fun t : ℝ => (aPhiJ φ).value d (t : ℂ)) u =
        ∫ v in Ioi (0 : ℝ), d * ((-(d * (v : ℂ))) ^ j * Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) *
          φ (d * (v : ℂ))) := by
  let ej := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  have hrep := (tendsto_coe_farJ hd).eventually (ej.represents hU hray hgood).2
  have hjet := (BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhiJ φ) hU hray hgood hd j).1
  filter_upwards [hrep, hjet] with u hurep hujet
  rw [← hujet, hurep, Minor.value, jet_residual_atomJ φ j, zero_add, complexLaplace]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [damped, Minor.pull, jet_residual_densityJ φ j]
  have hexp : -((u : ℂ) * d) * (v : ℂ) = -(d * (v : ℂ)) * (u : ℂ) := by ring
  rw [hexp]; ring

/-- Tail bound along a flanking ray `d` (`‖d‖ = 1`, `d.re = cos θ > 0`) for any cut `R > 0`. -/
private lemma exp_tail_boundJ {φ : ℂ → ℂ} {U : Set ℂ} {d : ℂ} {θ R : ℝ}
    (hR : 0 < R) (hcos : 0 < Real.cos θ)
    (hd_norm : ‖d‖ = 1) (hd_re : d.re = Real.cos θ)
    (hexp : ExpType (Minor.pull d φ))
    (hgood : (aPhiJ φ).Good U d) (hray : ContainsRay U d) (hU : Domain U) (j : ℕ) :
    ∃ K : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖∫ v in Ioi (R / Real.cos θ),
        d * ((-(d * (v : ℂ))) ^ j * Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) * φ (d * (v : ℂ)))‖ ≤
        K * Real.exp (-R * u) := by
  obtain ⟨Cexp, Dexp, hCexp, _, hexp_bd⟩ := hexp
  let v₀ : ℝ := R / Real.cos θ
  have hv₀_pos : 0 < v₀ := div_pos hR hcos
  have h_base_int : IntegrableOn (fun v : ℝ => v ^ j * Real.exp (-(1 / 2 : ℝ) * v)) (Ioi 0) := by
    refine ((integrableOn_exp_mul_Ioi (show -(1 / 4 : ℝ) < 0 by norm_num) 0).const_mul
      ((j.factorial : ℝ) / (1 / 4 : ℝ) ^ j)).mono'
      ((by fun_prop : Continuous fun v : ℝ => v ^ j * Real.exp (-(1 / 2 : ℝ) * v)).aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv
    change 0 < v at hv
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hv.le _) (Real.exp_pos _).le)]
    have hpow := Real.pow_div_factorial_le_exp ((1 / 4 : ℝ) * v) (by positivity) j
    have h1 : 0 < (1 / 4 : ℝ) ^ j := by positivity
    have h2 : 0 < (j.factorial : ℝ) := by positivity
    rw [mul_pow, div_le_iff₀ h2] at hpow
    have hvj : v ^ j ≤ ((j.factorial : ℝ) / (1 / 4 : ℝ) ^ j) * Real.exp ((1 / 4 : ℝ) * v) := by
      calc v ^ j ≤ (Real.exp ((1 / 4 : ℝ) * v) * j.factorial) / (1 / 4 : ℝ) ^ j :=
            (le_div_iff₀ h1).mpr (by linarith)
        _ = _ := by ring
    calc v ^ j * Real.exp (-(1 / 2 : ℝ) * v)
        ≤ (((j.factorial : ℝ) / (1 / 4 : ℝ) ^ j) * Real.exp ((1 / 4 : ℝ) * v)) *
            Real.exp (-(1 / 2 : ℝ) * v) := mul_le_mul_of_nonneg_right hvj (Real.exp_pos _).le
      _ = ((j.factorial : ℝ) / (1 / 4 : ℝ) ^ j) * Real.exp (-(1 / 4 : ℝ) * v) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  let Ij : ℝ := ∫ v in Ioi (0 : ℝ), v ^ j * Real.exp (-(1 / 2 : ℝ) * v)
  let K : ℝ := Cexp * Real.exp ((Dexp + 1 / 2) * v₀) * Ij
  let ej := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  have hej_good : (ej.residual (aPhiJ φ)).Good U d := (ej.represents hU hray hgood).1
  have hej_int := (tendsto_coe_farJ (by rw [hd_re]; exact hcos)).eventually (hej_good.integrable hray)
  refine ⟨K, ?_⟩
  filter_upwards [hej_int, eventually_ge_atTop ((Dexp + 1) / Real.cos θ)] with u hu_int hu_ge
  have hu_re : Dexp + 1 ≤ u * Real.cos θ := (div_le_iff₀ hcos).mp hu_ge
  let Ftail (v : ℝ) : ℂ := d * ((-(d * (v : ℂ))) ^ j *
    Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) * φ (d * (v : ℂ)))
  have hF_int_Ioi0 : IntegrableOn Ftail (Ioi 0) :=
    hu_int.congr_fun (fun v _ => by
      rw [damped, Minor.pull, jet_residual_densityJ φ j]
      have hexp' : -((u : ℂ) * d) * (v : ℂ) = -(d * (v : ℂ)) * (u : ℂ) := by ring
      rw [hexp']; dsimp only [Ftail]; ring) measurableSet_Ioi
  have hF_int_tail : IntegrableOn Ftail (Ioi v₀) :=
    hF_int_Ioi0.mono_set (Ioi_subset_Ioi hv₀_pos.le)
  let bnd (v : ℝ) : ℝ :=
    (Cexp * Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-R * u)) *
      (v ^ j * Real.exp (-(1 / 2 : ℝ) * v))
  have hbnd_int : IntegrableOn bnd (Ioi 0) :=
    h_base_int.const_mul (Cexp * Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-R * u))
  have h_pt_le : ∀ v ∈ Ioi v₀, ‖Ftail v‖ ≤ bnd v := by
    intro v hv; change v₀ < v at hv
    have hv0 : 0 ≤ v := le_trans hv₀_pos.le hv.le
    have hF_rew : Ftail v = (-(d * (v : ℂ))) ^ j * Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) *
        Minor.pull d φ v := by dsimp only [Ftail, Minor.pull]; ring
    rw [hF_rew, norm_mul, norm_mul, norm_pow, norm_neg, norm_mul, hd_norm, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0]
    have hexp_re : (-(d * (v : ℂ)) * (u : ℂ)).re = -(u * Real.cos θ) * v := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, hd_re]; ring
    rw [Complex.norm_exp, hexp_re]
    have hpull := hexp_bd v hv0
    have h_exp_split : Real.exp (-(u * Real.cos θ) * v) * (Cexp * Real.exp (Dexp * v)) =
        Cexp * Real.exp (-(u * Real.cos θ - Dexp) * v) := by
      rw [mul_left_comm _ Cexp, ← Real.exp_add]; congr 2; ring
    have h_exp_le : Real.exp (-(u * Real.cos θ - Dexp) * v) ≤
        Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-R * u) * Real.exp (-(1 / 2 : ℝ) * v) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      have h_rem_pos : 0 ≤ u * Real.cos θ - Dexp - 1 / 2 := by linarith
      have h_v0_mul : (u * Real.cos θ - Dexp - 1 / 2) * v₀ ≤
          (u * Real.cos θ - Dexp - 1 / 2) * v :=
        mul_le_mul_of_nonneg_left hv.le h_rem_pos
      have hv₀_eq : Real.cos θ * v₀ = R := by dsimp only [v₀]; field_simp [hcos.ne']
      nlinarith [hv₀_eq]
    calc v ^ j * Real.exp (-(u * Real.cos θ) * v) * ‖Minor.pull d φ v‖
        ≤ v ^ j * Real.exp (-(u * Real.cos θ) * v) * (Cexp * Real.exp (Dexp * v)) :=
          mul_le_mul_of_nonneg_left hpull (by positivity)
      _ = Cexp * (v ^ j * Real.exp (-(u * Real.cos θ - Dexp) * v)) := by
          rw [mul_assoc, h_exp_split]; ring
      _ ≤ Cexp * (v ^ j * (Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-R * u) *
            Real.exp (-(1 / 2 : ℝ) * v))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h_exp_le (pow_nonneg hv0 _)) hCexp
      _ = bnd v := by dsimp only [bnd]; ring
  calc ‖∫ v in Ioi v₀, Ftail v‖
      ≤ ∫ v in Ioi v₀, ‖Ftail v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v in Ioi v₀, bnd v :=
        setIntegral_mono_on hF_int_tail.norm (hbnd_int.mono_set (Ioi_subset_Ioi hv₀_pos.le))
          measurableSet_Ioi h_pt_le
    _ ≤ ∫ v in Ioi 0, bnd v :=
        setIntegral_mono_set hbnd_int
          ((ae_restrict_mem measurableSet_Ioi).mono fun v (hv : 0 < v) => by
            dsimp only [bnd]
            exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hv.le _) (Real.exp_pos _).le))
          (Eventually.of_forall fun _ hx => Ioi_subset_Ioi hv₀_pos.le hx)
    _ = K * Real.exp (-R * u) := by
        dsimp only [bnd, K, Ij]; rw [integral_const_mul]; ring

private def TriBdIntJ (F : ℂ → ℂ) (R m : ℝ) : Prop :=
  IntervalIntegrable (fun x : ℝ => (1 - Complex.I * (m : ℂ)) * F ((x : ℂ) * (1 - Complex.I * (m : ℂ)))) volume 0 R ∧
  IntervalIntegrable (fun y : ℝ => F ((R : ℂ) + (y : ℂ) * Complex.I)) volume (-m * R) (m * R) ∧
  IntervalIntegrable (fun x : ℝ => (1 + Complex.I * (m : ℂ)) * F ((x : ℂ) * (1 + Complex.I * (m : ℂ)))) volume 0 R

private lemma triIntegral_addJ {F G : ℂ → ℂ} {R m : ℝ}
    (hF : TriBdIntJ F R m) (hG : TriBdIntJ G R m) :
    triIntegral (fun z => F z + G z) R m = triIntegral F R m + triIntegral G R m := by
  unfold triIntegral
  have h1 : (fun x : ℝ => (1 - Complex.I * (m : ℂ)) * (F ((x : ℂ) * (1 - Complex.I * (m : ℂ))) +
      G ((x : ℂ) * (1 - Complex.I * (m : ℂ))))) = fun x : ℝ =>
      (1 - Complex.I * (m : ℂ)) * F ((x : ℂ) * (1 - Complex.I * (m : ℂ))) +
      (1 - Complex.I * (m : ℂ)) * G ((x : ℂ) * (1 - Complex.I * (m : ℂ))) := by funext x; ring
  have h2 : (fun x : ℝ => (1 + Complex.I * (m : ℂ)) * (F ((x : ℂ) * (1 + Complex.I * (m : ℂ))) +
      G ((x : ℂ) * (1 + Complex.I * (m : ℂ))))) = fun x : ℝ =>
      (1 + Complex.I * (m : ℂ)) * F ((x : ℂ) * (1 + Complex.I * (m : ℂ))) +
      (1 + Complex.I * (m : ℂ)) * G ((x : ℂ) * (1 + Complex.I * (m : ℂ))) := by funext x; ring
  rw [h1, h2, intervalIntegral.integral_add hF.1 hG.1,
    intervalIntegral.integral_add hF.2.1 hG.2.1,
    intervalIntegral.integral_add hF.2.2 hG.2.2]; ring

private lemma triIntegral_const_mulJ (c : ℂ) (F : ℂ → ℂ) (R m : ℝ) :
    triIntegral (fun z => c * F z) R m = c * triIntegral F R m := by
  unfold triIntegral
  have h1 : (fun x : ℝ => (1 - Complex.I * (m : ℂ)) * (c * F ((x : ℂ) * (1 - Complex.I * (m : ℂ))))) =
      fun x : ℝ => c * ((1 - Complex.I * (m : ℂ)) * F ((x : ℂ) * (1 - Complex.I * (m : ℂ)))) := by funext x; ring
  have h2 : (fun x : ℝ => (1 + Complex.I * (m : ℂ)) * (c * F ((x : ℂ) * (1 + Complex.I * (m : ℂ))))) =
      fun x : ℝ => c * ((1 + Complex.I * (m : ℂ)) * F ((x : ℂ) * (1 + Complex.I * (m : ℂ)))) := by funext x; ring
  rw [h1, h2, intervalIntegral.integral_const_mul c, intervalIntegral.integral_const_mul c,
    intervalIntegral.integral_const_mul c]; ring

private lemma triIntegral_sumJ {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (R m : ℝ)
    (hF : ∀ i ∈ s, TriBdIntJ (F i) R m) :
    triIntegral (fun z => ∑ i ∈ s, F i z) R m = ∑ i ∈ s, triIntegral (F i) R m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [triIntegral]
  | @insert i s hi ih =>
    have hFi := hF i (Finset.mem_insert_self i s)
    have hFs : ∀ j ∈ s, TriBdIntJ (F j) R m := fun j hj => hF j (Finset.mem_insert_of_mem hj)
    have hsum_int : TriBdIntJ (fun z => ∑ j ∈ s, F j z) R m := by
      refine ⟨?_, ?_, ?_⟩
      · have heq : (fun x : ℝ => (1 - Complex.I * (m : ℂ)) * ∑ j ∈ s, F j ((x : ℂ) * (1 - Complex.I * (m : ℂ)))) =
            ∑ j ∈ s, fun x : ℝ => (1 - Complex.I * (m : ℂ)) * F j ((x : ℂ) * (1 - Complex.I * (m : ℂ))) := by
          funext x; rw [Finset.mul_sum, Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum s fun j hj => (hFs j hj).1
      · have heq : (fun y : ℝ => ∑ j ∈ s, F j ((R : ℂ) + (y : ℂ) * Complex.I)) =
            ∑ j ∈ s, fun y : ℝ => F j ((R : ℂ) + (y : ℂ) * Complex.I) := by
          funext y; rw [Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum s fun j hj => (hFs j hj).2.1
      · have heq : (fun x : ℝ => (1 + Complex.I * (m : ℂ)) * ∑ j ∈ s, F j ((x : ℂ) * (1 + Complex.I * (m : ℂ)))) =
            ∑ j ∈ s, fun x : ℝ => (1 + Complex.I * (m : ℂ)) * F j ((x : ℂ) * (1 + Complex.I * (m : ℂ))) := by
          funext x; rw [Finset.mul_sum, Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum s fun j hj => (hFs j hj).2.2
    have hfn : (fun z => ∑ j ∈ insert i s, F j z) = fun z => F i z + ∑ j ∈ s, F j z := by
      funext z; rw [Finset.sum_insert hi]
    rw [hfn, triIntegral_addJ hFi hsum_int, ih hFs, Finset.sum_insert hi]

private lemma triIntegral_congrJ {F G : ℂ → ℂ} {R m : ℝ} (hR : 0 ≤ R) (hm : 0 ≤ m)
    (h1 : ∀ x ∈ Icc (0 : ℝ) R, F ((x : ℂ) * (1 - Complex.I * (m : ℂ))) = G ((x : ℂ) * (1 - Complex.I * (m : ℂ))))
    (h2 : ∀ y ∈ Icc (-m * R) (m * R), F ((R : ℂ) + (y : ℂ) * Complex.I) = G ((R : ℂ) + (y : ℂ) * Complex.I))
    (h3 : ∀ x ∈ Icc (0 : ℝ) R, F ((x : ℂ) * (1 + Complex.I * (m : ℂ))) = G ((x : ℂ) * (1 + Complex.I * (m : ℂ)))) :
    triIntegral F R m = triIntegral G R m := by
  unfold triIntegral
  have hmR : -m * R ≤ m * R := by nlinarith
  have i1 : (∫ x : ℝ in (0 : ℝ)..R, (1 - Complex.I * (m : ℂ)) * F ((x : ℂ) * (1 - Complex.I * (m : ℂ)))) =
      ∫ x : ℝ in (0 : ℝ)..R, (1 - Complex.I * (m : ℂ)) * G ((x : ℂ) * (1 - Complex.I * (m : ℂ))) :=
    intervalIntegral.integral_congr fun x hx => by rw [uIcc_of_le hR] at hx; rw [h1 x hx]
  have i2 : (∫ y : ℝ in (-m * R)..(m * R), F ((R : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ y : ℝ in (-m * R)..(m * R), G ((R : ℂ) + (y : ℂ) * Complex.I) :=
    intervalIntegral.integral_congr fun y hy => by rw [uIcc_of_le hmR] at hy; rw [h2 y hy]
  have i3 : (∫ x : ℝ in (0 : ℝ)..R, (1 + Complex.I * (m : ℂ)) * F ((x : ℂ) * (1 + Complex.I * (m : ℂ)))) =
      ∫ x : ℝ in (0 : ℝ)..R, (1 + Complex.I * (m : ℂ)) * G ((x : ℂ) * (1 + Complex.I * (m : ℂ))) :=
    intervalIntegral.integral_congr fun x hx => by rw [uIcc_of_le hR] at hx; rw [h3 x hx]
  rw [i1, i2, i3]

private lemma triBdIntJ_of_cont {F : ℂ → ℂ} {R m : ℝ} (hR : 0 ≤ R) (hm : 0 ≤ m)
    (h1 : ContinuousOn (fun x : ℝ => F ((x : ℂ) * (1 - Complex.I * (m : ℂ)))) (Icc 0 R))
    (h2 : ContinuousOn (fun y : ℝ => F ((R : ℂ) + (y : ℂ) * Complex.I)) (Icc (-m * R) (m * R)))
    (h3 : ContinuousOn (fun x : ℝ => F ((x : ℂ) * (1 + Complex.I * (m : ℂ)))) (Icc 0 R)) :
    TriBdIntJ F R m :=
  ⟨(continuousOn_const.mul h1).intervalIntegrable_of_Icc hR,
   h2.intervalIntegrable_of_Icc (by nlinarith),
   (continuousOn_const.mul h3).intervalIntegrable_of_Icc hR⟩

private lemma triIntegral_mul_inv_sub_simple {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F univ)
    {c R m : ℝ} (hc : 0 < c) (hR : c < R) (hm : 0 < m) :
    triIntegral (fun z : ℂ => F z / (z - (c : ℂ))) R m =
      2 * (Real.pi : ℂ) * Complex.I * F (c : ℂ) := by
  have hR_pos : 0 < R := lt_trans hc hR
  have hav : (∀ x : ℝ, (x : ℂ) * (1 - Complex.I * (m : ℂ)) ≠ (c : ℂ)) ∧
      (∀ x : ℝ, (x : ℂ) * (1 + Complex.I * (m : ℂ)) ≠ (c : ℂ)) ∧
      (∀ y : ℝ, (R : ℂ) + (y : ℂ) * Complex.I ≠ (c : ℂ)) := by
    refine ⟨fun x h0 => ?_, fun x h0 => ?_, fun y h0 => ?_⟩
    · have him := congrArg Complex.im h0
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
        Complex.one_im, Complex.I_im, mul_zero, zero_mul, zero_sub, add_zero] at him
      have hx0 : x = 0 := (mul_eq_zero.mp (by linarith : x * (-m) = 0)).resolve_right (neg_ne_zero.mpr hm.ne')
      subst hx0; have hre := congrArg Complex.re h0; simp at hre; linarith
    · have him := congrArg Complex.im h0
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
        Complex.one_im, Complex.I_im, mul_zero, zero_mul, add_zero, zero_add] at him
      have hx0 : x = 0 := (mul_eq_zero.mp (by linarith : x * m = 0)).resolve_right hm.ne'
      subst hx0; have hre := congrArg Complex.re h0; simp at hre; linarith
    · have hre := congrArg Complex.re h0; simp [Complex.mul_re] at hre; linarith
  let G : ℂ → ℂ := dslope F (c : ℂ)
  have hG_an : AnalyticOnNhd ℂ G univ :=
    ((Complex.differentiableOn_dslope (Filter.univ_mem : univ ∈ 𝓝 (c : ℂ))).mpr
      hF.differentiableOn).analyticOnNhd isOpen_univ
  have htri_G : triIntegral G R m = 0 :=
    triIntegral_eq_zero_of_analyticOn hR_pos.le hm.le isOpen_univ (subset_univ _) hG_an
  have hG_int : TriBdIntJ G R m :=
    triBdIntJ_of_cont hR_pos.le hm.le
      (hG_an.continuousOn.comp (by fun_prop) fun _ _ => mem_univ _)
      (hG_an.continuousOn.comp (by fun_prop) fun _ _ => mem_univ _)
      (hG_an.continuousOn.comp (by fun_prop) fun _ _ => mem_univ _)
  have hP_int : TriBdIntJ (fun z => F (c : ℂ) * (z - (c : ℂ))⁻¹) R m :=
    triBdIntJ_of_cont hR_pos.le hm.le
      (Continuous.continuousOn (continuous_const.mul (Continuous.inv₀ (by fun_prop) fun x h0 =>
        hav.1 x (sub_eq_zero.mp h0))))
      (Continuous.continuousOn (continuous_const.mul (Continuous.inv₀ (by fun_prop) fun y h0 =>
        hav.2.2 y (sub_eq_zero.mp h0))))
      (Continuous.continuousOn (continuous_const.mul (Continuous.inv₀ (by fun_prop) fun x h0 =>
        hav.2.1 x (sub_eq_zero.mp h0))))
  have hsplit : ∀ z : ℂ, z ≠ (c : ℂ) → F z / (z - (c : ℂ)) = G z + F (c : ℂ) * (z - (c : ℂ))⁻¹ := by
    intro z hzc
    have hsub : z - (c : ℂ) ≠ 0 := sub_ne_zero.mpr hzc
    have hsl := sub_smul_dslope F (c : ℂ) z
    rw [smul_eq_mul] at hsl
    dsimp only [G]
    rw [← sub_add_cancel (F z) (F (c : ℂ)), ← hsl, add_div, mul_div_cancel_left₀ _ hsub, div_eq_mul_inv]
  have hcongr := triIntegral_congrJ
    (F := fun z : ℂ => F z / (z - (c : ℂ)))
    (G := fun z : ℂ => G z + F (c : ℂ) * (z - (c : ℂ))⁻¹)
    hR_pos.le hm.le
    (fun x _ => hsplit _ (hav.1 x)) (fun y _ => hsplit _ (hav.2.2 y)) (fun x _ => hsplit _ (hav.2.1 x))
  rw [hcongr, triIntegral_addJ hG_int hP_int, htri_G, zero_add, triIntegral_const_mulJ,
    triIntegral_inv_sub hc hR hm]
  ring

/-- **Single-Component Simple-Pole Stokes Jump at Any Pole-Avoiding Cut `R > 0`**:
For a simple-pole kernel `φ` along `θ₀ = 0` with poles `ω m`, if `M : ℕ` satisfies
`∀ m < M, ω m < R` and `R < ω M` (hence `R` avoids every pole `ω m`), then for every `j`,
`iteratedDeriv j (g_neg - g_pos) u - ∑_{m < M} (2π i res m (-ω m)^j) e^{-ω m u} = O(e^{-R u})`. -/
private lemma simplePole_stokes_jump_at_cut
    {φ : ℂ → ℂ} {ω : ℕ → ℝ} {res : ℕ → ℂ} {α₀ θ ε ε₀ R : ℝ} {M : ℕ}
    (hθ_pos : 0 < θ) (hθ_lt : θ < α₀) (hα₀_lt : α₀ < Real.pi / 2)
    (hε₀_pos : 0 < ε₀) (hε₀_le : ε₀ ≤ ε) (hε₀_lt : ε₀ ≤ ω 0 / 2)
    (hω_pos : 0 < ω 0) (hω_mono : StrictMono ω)
    (hana : AnalyticOnNhd ℂ φ (rotatedPuncturedWedge 0 α₀ ε ω))
    (hpole : ∀ m, ∃ L : ℂ, Tendsto (fun z => φ z - res m / (z - (ω m : ℂ))) (𝓝[≠] (ω m : ℂ)) (𝓝 L))
    (hexpP : ExpType (Minor.pull (dPlusJ θ) φ))
    (hexpM : ExpType (Minor.pull (dMinusJ θ) φ))
    (hR_pos : 0 < R) (hM_below : ∀ m < M, ω m < R) (hM_above : R < ω M) (j : ℕ) :
    ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖iteratedDeriv j (fun t : ℝ => (aPhiJ φ).value (dMinusJ θ) (t : ℂ) -
          (aPhiJ φ).value (dPlusJ θ) (t : ℂ)) u -
        ∑ m ∈ Finset.range M,
          (2 * (Real.pi : ℂ) * Complex.I * res m * (-(ω m : ℂ)) ^ j) *
            Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ ≤
        C * Real.exp (-R * u) := by
  classical
  let mθ : ℝ := Real.tan θ
  let v₀ : ℝ := R / Real.cos θ
  have hα_pos : 0 < α₀ := hθ_pos.trans hθ_lt
  have hcos : 0 < Real.cos θ := cos_pos_J hθ_pos hθ_lt hα₀_lt
  have hm_pos : 0 < mθ := tan_pos_J hθ_pos hθ_lt hα₀_lt
  have hv₀_pos : 0 < v₀ := div_pos hR_pos hcos
  have hreP : 0 < (dPlusJ θ).re := by rw [dPlusJ_re]; exact hcos
  have hreM : 0 < (dMinusJ θ).re := by rw [dMinusJ_re]; exact hcos
  let Up := wedgePlusJ α₀ ε₀
  let Um := wedgeMinusJ α₀ ε₀
  have hUp_dom : Domain Up := wedgePlusJ_domain hε₀_pos
  have hUm_dom : Domain Um := wedgeMinusJ_domain hε₀_pos
  have hrayP : ContainsRay Up (dPlusJ θ) := wedgePlusJ_containsRay hθ_pos hθ_lt hα₀_lt hε₀_pos
  have hrayM : ContainsRay Um (dMinusJ θ) := wedgeMinusJ_containsRay hθ_pos hθ_lt hα₀_lt hε₀_pos
  have hgoodP : (aPhiJ φ).Good Up (dPlusJ θ) :=
    ⟨hana.mono (wedgePlusJ_subset_punctured hα_pos hα₀_lt hε₀_le hε₀_lt hω_pos hω_mono), hexpP⟩
  have hgoodM : (aPhiJ φ).Good Um (dMinusJ θ) :=
    ⟨hana.mono (wedgeMinusJ_subset_punctured hα_pos hα₀_lt hε₀_le hε₀_lt hω_pos hω_mono), hexpM⟩
  have h_sub_deriv : ∀ᶠ u : ℝ in atTop,
      iteratedDeriv j (fun t : ℝ => (aPhiJ φ).value (dMinusJ θ) (t : ℂ) -
          (aPhiJ φ).value (dPlusJ θ) (t : ℂ)) u =
        iteratedDeriv j (fun t : ℝ => (aPhiJ φ).value (dMinusJ θ) (t : ℂ)) u -
          iteratedDeriv j (fun t : ℝ => (aPhiJ φ).value (dPlusJ θ) (t : ℂ)) u :=
    eventually_iteratedDeriv_sub
      (fun i _ => (BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhiJ φ) hUm_dom hrayM hgoodM hreM i).2)
      (fun i _ => (BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhiJ φ) hUp_dom hrayP hgoodP hreP i).2)
  have h_lapP := iteratedDeriv_lateral_eq_laplaceJ hUp_dom hrayP hgoodP hreP j
  have h_lapM := iteratedDeriv_lateral_eq_laplaceJ hUm_dom hrayM hgoodM hreM j
  let ej := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  have h_intP := (tendsto_coe_farJ hreP).eventually ((ej.represents hUp_dom hrayP hgoodP).1.integrable hrayP)
  have h_intM := (tendsto_coe_farJ hreM).eventually ((ej.represents hUm_dom hrayM hgoodM).1.integrable hrayM)
  obtain ⟨Km, hKm⟩ := exp_tail_boundJ hR_pos hcos (norm_dMinusJ θ) (dMinusJ_re θ) hexpM hgoodM hrayM hUm_dom j
  obtain ⟨Kp, hKp⟩ := exp_tail_boundJ hR_pos hcos (norm_dPlusJ θ) (dPlusJ_re θ) hexpP hgoodP hrayP hUp_dom j
  -- Avoidance of poles on triangle boundary
  have h_avoid : (∀ x : ℝ, ∀ m : ℕ, (x : ℂ) * (1 - Complex.I * (mθ : ℂ)) ≠ (ω m : ℂ)) ∧
      (∀ x : ℝ, ∀ m : ℕ, (x : ℂ) * (1 + Complex.I * (mθ : ℂ)) ≠ (ω m : ℂ)) ∧
      (∀ y : ℝ, ∀ m : ℕ, (R : ℂ) + (y : ℂ) * Complex.I ≠ (ω m : ℂ)) := by
    refine ⟨fun x m h0 => ?_, fun x m h0 => ?_, fun y m h0 => ?_⟩
    · have him := congrArg Complex.im h0
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
        Complex.one_im, Complex.I_im, mul_zero, zero_mul, zero_sub, add_zero] at him
      have hx0 : x = 0 := (mul_eq_zero.mp (by linarith : x * (-mθ) = 0)).resolve_right (neg_ne_zero.mpr hm_pos.ne')
      subst hx0; have hre := congrArg Complex.re h0; simp at hre
      have hωm : 0 < ω m := lt_of_lt_of_le hω_pos (hω_mono.monotone (Nat.zero_le m))
      linarith
    · have him := congrArg Complex.im h0
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
        Complex.one_im, Complex.I_im, mul_zero, zero_mul, add_zero, zero_add] at him
      have hx0 : x = 0 := (mul_eq_zero.mp (by linarith : x * mθ = 0)).resolve_right hm_pos.ne'
      subst hx0; have hre := congrArg Complex.re h0; simp at hre
      have hωm : 0 < ω m := lt_of_lt_of_le hω_pos (hω_mono.monotone (Nat.zero_le m))
      linarith
    · have hre := congrArg Complex.re h0; simp [Complex.mul_re] at hre
      rcases lt_or_ge m M with hm | hm
      · exact (hM_below m hm).ne hre.symm
      · exact (lt_of_lt_of_le hM_above (hω_mono.monotone hm)).ne hre
  -- Triangle residue formula for Fkern(z) = (-z)^j e^{-z u} φ(z)
  have htri_eq : ∀ u : ℝ,
      triIntegral (fun z => (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z) R mθ =
        ∑ m ∈ Finset.range M,
          (2 * (Real.pi : ℂ) * Complex.I * res m * (-(ω m : ℂ)) ^ j) *
            Complex.exp (-(ω m : ℂ) * (u : ℂ)) := by
    intro u
    let Un : Set ℂ := borelWedge α₀ ε₀ ∩ {z : ℂ | z.re < ω M}
    have hUn_open : IsOpen Un :=
      (Metric.isOpen_ball.union ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt (continuous_abs.comp Complex.continuous_im)
          (continuous_const.mul Complex.continuous_re)))).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have htri_sub : closedTri R mθ ⊆ Un := by
      intro z hz
      refine ⟨?_, lt_of_le_of_lt hz.2.1 hM_above⟩
      rcases eq_or_lt_of_le hz.1 with hz0 | hzpos
      · left
        have him0 : z.im = 0 := abs_nonpos_iff.mp (by simpa [← hz0] using hz.2.2)
        have hz_eq : z = 0 := Complex.ext hz0.symm him0
        simpa [hz_eq, Metric.mem_ball, dist_zero_right] using hε₀_pos
      · right
        exact ⟨hzpos, lt_of_le_of_lt hz.2.2 (mul_lt_mul_of_pos_right (tan_lt_tanJ hθ_pos hθ_lt hα₀_lt) hzpos)⟩
    let Sn (z : ℂ) : ℂ := ∑ m ∈ Finset.range M, res m / (z - (ω m : ℂ))
    let Pset : Set ℂ := (fun m : ℕ => (ω m : ℂ)) '' (Finset.range M : Set ℕ)
    let ψn (z : ℂ) : ℂ :=
      if z ∈ Pset then Filter.limUnder (𝓝[≠] z) (fun w => φ w - Sn w) else φ z - Sn z
    have hP_fin : Pset.Finite := (Finset.finite_toSet (Finset.range M)).image _
    have hP_closed : IsClosed Pset := hP_fin.isClosed
    have hUn_sub : Un \ Pset ⊆ rotatedPuncturedWedge 0 α₀ ε ω := by
      rw [rotatedPuncturedWedge_zero_eqJ]
      intro w ⟨hwU, hwP⟩
      refine ⟨?_, ?_⟩
      · rcases hwU.1 with hw_ball | hw_sec
        · left; exact Metric.ball_subset_ball hε₀_le hw_ball
        · right; exact hw_sec
      · rintro ⟨m, rfl⟩
        have hm_lt : ω m < ω M := by simpa using hwU.2
        have hm_idx : m < M := hω_mono.lt_iff_lt.mp hm_lt
        exact hwP ⟨m, Finset.mem_coe.mpr (Finset.mem_range.mpr hm_idx), rfl⟩
    have hSn_an : ∀ z ∈ Un \ Pset, AnalyticAt ℂ Sn z := by
      intro z hz
      refine Finset.analyticAt_fun_sum _ fun m hm => analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_
      intro h0; exact hz.2 ⟨m, Finset.mem_coe.mpr hm, (sub_eq_zero.mp h0).symm⟩
    have hψ_an : AnalyticOnNhd ℂ ψn Un := by
      intro z hzU
      by_cases hzP : z ∈ Pset
      · obtain ⟨k, hk_mem, rfl⟩ := hzP
        let Qk : Set ℂ := Pset \ {(ω k : ℂ)}
        have hQk_closed : IsClosed Qk := (hP_fin.subset Set.sdiff_subset).isClosed
        let Vk : Set ℂ := Un \ Qk
        have hVk_open : IsOpen Vk := hUn_open.sdiff hQk_closed
        have hwk_Vk : (ω k : ℂ) ∈ Vk := ⟨hzU, fun hmem => hmem.2 rfl⟩
        have hmem_punc : Vk \ {(ω k : ℂ)} ∈ 𝓝[≠] (ω k : ℂ) := by
          rw [Set.sdiff_eq, inter_comm]; exact inter_mem_nhdsWithin _ (hVk_open.mem_nhds hwk_Vk)
        have hsub_open : Vk \ {(ω k : ℂ)} ⊆ Un \ Pset := fun ζ hζ =>
          ⟨hζ.1.1, fun hP => hζ.2 (by by_contra hne; exact hζ.1.2 ⟨hP, hne⟩)⟩
        have hψ_diff_punc : ∀ᶠ w in 𝓝[≠] (ω k : ℂ), DifferentiableAt ℂ ψn w := by
          filter_upwards [hmem_punc] with w hw
          have hdiff := ((hana w (hUn_sub (hsub_open hw))).sub (hSn_an w (hsub_open hw))).differentiableAt
          refine hdiff.congr_of_eventuallyEq ?_
          filter_upwards [(hUn_open.sdiff hP_closed).mem_nhds (hsub_open hw)] with ζ hζ
          exact ite_eq_right_iff.mpr fun hmem => absurd hmem hζ.2
        let Sn_rest (w : ℂ) : ℂ := ∑ m ∈ (Finset.range M).erase k, res m / (w - (ω m : ℂ))
        have hSn_split : ∀ w : ℂ, φ w - Sn w = (φ w - res k / (w - (ω k : ℂ))) - Sn_rest w := by
          intro w; dsimp only [Sn, Sn_rest]
          rw [← Finset.add_sum_erase (Finset.range M) (fun m => res m / (w - (ω m : ℂ))) hk_mem]; ring
        have hrest_an : AnalyticAt ℂ Sn_rest (ω k : ℂ) := by
          refine Finset.analyticAt_fun_sum _ fun m hm => analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_
          intro h0; exact hω_mono.injective.ne (Finset.mem_erase.mp hm).1.symm
            (by exact_mod_cast sub_eq_zero.mp h0)
        obtain ⟨L, hL⟩ := hpole k
        have h_tend : Tendsto (fun w => φ w - Sn w) (𝓝[≠] (ω k : ℂ)) (𝓝 (L - Sn_rest (ω k : ℂ))) := by
          simp_rw [hSn_split]; exact hL.sub hrest_an.continuousAt.continuousWithinAt.tendsto
        have hψ_tend : Tendsto ψn (𝓝[≠] (ω k : ℂ)) (𝓝 (L - Sn_rest (ω k : ℂ))) := by
          refine h_tend.congr' ?_
          filter_upwards [hmem_punc] with w hw
          exact (ite_eq_right_iff.mpr fun hmem => absurd hmem (hsub_open hw).2).symm
        have hψ_at : ψn (ω k : ℂ) = L - Sn_rest (ω k : ℂ) := by
          have hmemP : (ω k : ℂ) ∈ Pset := ⟨k, Finset.mem_coe.mpr hk_mem, rfl⟩
          dsimp only [ψn]; rw [ite_eq_left_iff.mpr fun hnot => absurd hmemP hnot, h_tend.limUnder_eq]
        exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hψ_diff_punc
          (continuousAt_iff_punctured_nhds.mpr (by simpa [hψ_at] using hψ_tend))
      · have hdiff := (hana z (hUn_sub ⟨hzU, hzP⟩)).sub (hSn_an z ⟨hzU, hzP⟩)
        refine hdiff.congr ?_
        filter_upwards [(hUn_open.sdiff hP_closed).mem_nhds ⟨hzU, hzP⟩] with w hw
        exact (ite_eq_right_iff.mpr fun hmem => absurd hmem hw.2).symm
    let Fψ (z : ℂ) : ℂ := (-z) ^ j * Complex.exp (-z * (u : ℂ)) * ψn z
    have hFψ_an : AnalyticOnNhd ℂ Fψ Un :=
      ((analyticOnNhd_id.neg.pow j).mul ((analyticOnNhd_id.neg.mul analyticOnNhd_const).cexp)).mul hψ_an
    have htri_ψ : triIntegral Fψ R mθ = 0 :=
      triIntegral_eq_zero_of_analyticOn hR_pos.le hm_pos.le hUn_open htri_sub hFψ_an
    let termM (m : ℕ) (z : ℂ) : ℂ :=
      (-z) ^ j * Complex.exp (-z * (u : ℂ)) * (res m / (z - (ω m : ℂ)))
    have htermM_int : ∀ m ∈ Finset.range M, TriBdIntJ (termM m) R mθ := by
      intro m _
      refine triBdIntJ_of_cont hR_pos.le hm_pos.le
        ((Continuous.continuousOn (by fun_prop)).mul (Continuous.continuousOn
          (continuous_const.div (by fun_prop) fun x h0 => h_avoid.1 x m (sub_eq_zero.mp h0))))
        ((Continuous.continuousOn (by fun_prop)).mul (Continuous.continuousOn
          (continuous_const.div (by fun_prop) fun y h0 => h_avoid.2.2 y m (sub_eq_zero.mp h0))))
        ((Continuous.continuousOn (by fun_prop)).mul (Continuous.continuousOn
          (continuous_const.div (by fun_prop) fun x h0 => h_avoid.2.1 x m (sub_eq_zero.mp h0))))
    have hFψ_int : TriBdIntJ Fψ R mθ := by
      refine triBdIntJ_of_cont hR_pos.le hm_pos.le
        (hFψ_an.continuousOn.comp (by fun_prop) fun x hx => htri_sub ?_)
        (hFψ_an.continuousOn.comp (by fun_prop) fun y hy => htri_sub ?_)
        (hFψ_an.continuousOn.comp (by fun_prop) fun x hx => htri_sub ?_)
      · refine ⟨by simp [Complex.mul_re]; exact hx.1, by simp [Complex.mul_re]; exact hx.2, ?_⟩
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
          mul_zero, zero_mul, sub_zero, add_zero, zero_sub, zero_add, neg_zero, mul_one, mul_neg, one_mul]
        rw [abs_neg, abs_mul, abs_of_nonneg hx.1, abs_of_pos hm_pos, mul_comm]
      · refine ⟨by simp [Complex.mul_re]; exact hR_pos.le, by simp [Complex.mul_re], ?_⟩
        simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
          add_zero, zero_add]
        have hy' : y ∈ Icc (-(mθ * R)) (mθ * R) := by simpa [neg_mul] using hy
        exact abs_le.mpr hy'
      · refine ⟨by simp [Complex.mul_re]; exact hx.1, by simp [Complex.mul_re]; exact hx.2, ?_⟩
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
          mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one, one_mul]
        rw [abs_mul, abs_of_nonneg hx.1, abs_of_pos hm_pos, mul_comm]
    have hsum_int : TriBdIntJ (fun z => ∑ m ∈ Finset.range M, termM m z) R mθ := by
      refine ⟨?_, ?_, ?_⟩
      · have heq : (fun x : ℝ => (1 - Complex.I * (mθ : ℂ)) *
            ∑ m ∈ Finset.range M, termM m ((x : ℂ) * (1 - Complex.I * (mθ : ℂ)))) =
            ∑ m ∈ Finset.range M, fun x : ℝ => (1 - Complex.I * (mθ : ℂ)) * termM m ((x : ℂ) * (1 - Complex.I * (mθ : ℂ))) := by
          funext x; rw [Finset.mul_sum, Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum _ fun m hm => (htermM_int m hm).1
      · have heq : (fun y : ℝ => ∑ m ∈ Finset.range M, termM m ((R : ℂ) + (y : ℂ) * Complex.I)) =
            ∑ m ∈ Finset.range M, fun y : ℝ => termM m ((R : ℂ) + (y : ℂ) * Complex.I) := by
          funext y; rw [Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum _ fun m hm => (htermM_int m hm).2.1
      · have heq : (fun x : ℝ => (1 + Complex.I * (mθ : ℂ)) *
            ∑ m ∈ Finset.range M, termM m ((x : ℂ) * (1 + Complex.I * (mθ : ℂ)))) =
            ∑ m ∈ Finset.range M, fun x : ℝ => (1 + Complex.I * (mθ : ℂ)) * termM m ((x : ℂ) * (1 + Complex.I * (mθ : ℂ))) := by
          funext x; rw [Finset.mul_sum, Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum _ fun m hm => (htermM_int m hm).2.2
    have hpt_eq : ∀ z : ℂ, z ∉ Pset →
        (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z = Fψ z + ∑ m ∈ Finset.range M, termM m z := by
      intro z hz
      dsimp only [Fψ, ψn, termM, Sn]
      rw [ite_eq_right_iff.mpr (fun h => absurd h hz), mul_sub, Finset.mul_sum]; ring
    have hcongr := triIntegral_congrJ
      (F := fun z : ℂ => (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z)
      (G := fun z : ℂ => Fψ z + ∑ m ∈ Finset.range M, termM m z)
      hR_pos.le hm_pos.le
      (fun x _ => hpt_eq _ fun ⟨m, _, hm⟩ => h_avoid.1 x m hm.symm)
      (fun y _ => hpt_eq _ fun ⟨m, _, hm⟩ => h_avoid.2.2 y m hm.symm)
      (fun x _ => hpt_eq _ fun ⟨m, _, hm⟩ => h_avoid.2.1 x m hm.symm)
    rw [hcongr, triIntegral_addJ hFψ_int hsum_int, htri_ψ, zero_add,
      triIntegral_sumJ _ _ R mθ htermM_int]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hterm_rew : termM m = fun z => res m * (((-z) ^ j * Complex.exp (-z * (u : ℂ))) / (z - (ω m : ℂ))) := by
      funext z; dsimp only [termM]; ring
    rw [hterm_rew, triIntegral_const_mulJ]
    have hFn : AnalyticOnNhd ℂ (fun z : ℂ => (-z) ^ j * Complex.exp (-z * (u : ℂ))) univ :=
      (analyticOnNhd_id.neg.pow j).mul ((analyticOnNhd_id.neg.mul analyticOnNhd_const).cexp)
    rw [triIntegral_mul_inv_sub_simple hFn
      (lt_of_lt_of_le hω_pos (hω_mono.monotone (Nat.zero_le m)))
      (hM_below m (Finset.mem_range.mp hm)) hm_pos]
    ring
  -- Vertical edge bound on x = R
  have h_vert_sub : ∀ y ∈ Icc (-mθ * R) (mθ * R),
      (R : ℂ) + (y : ℂ) * Complex.I ∈ rotatedPuncturedWedge 0 α₀ ε ω := by
    rw [rotatedPuncturedWedge_zero_eqJ]
    intro y hy
    refine ⟨Or.inr ?_, fun ⟨m, hm⟩ => h_avoid.2.2 y m hm.symm⟩
    simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      mul_one, zero_add]
    rw [show -mθ * R = -(mθ * R) by ring] at hy
    exact ⟨hR_pos, lt_of_le_of_lt (abs_le.mpr hy)
      (mul_lt_mul_of_pos_right (tan_lt_tanJ hθ_pos hθ_lt hα₀_lt) hR_pos)⟩
  have hφ_vert_cont : ContinuousOn (fun y : ℝ => φ ((R : ℂ) + (y : ℂ) * Complex.I)) (Icc (-mθ * R) (mθ * R)) :=
    hana.continuousOn.comp (by fun_prop) h_vert_sub
  obtain ⟨Mφ, hMφ⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ_vert_cont
  let Kv : ℝ := (2 * mθ * R) * ((R / Real.cos θ) ^ j * max Mφ 0)
  have h_vert_bd : ∀ u : ℝ,
      ‖Complex.I * (∫ y : ℝ in (-mθ * R)..(mθ * R),
        (-((R : ℂ) + (y : ℂ) * Complex.I)) ^ j * Complex.exp (-((R : ℂ) + (y : ℂ) * Complex.I) * (u : ℂ)) *
          φ ((R : ℂ) + (y : ℂ) * Complex.I))‖ ≤ Kv * Real.exp (-R * u) := by
    intro u
    rw [norm_mul, Complex.norm_I, one_mul]
    have hpt : ∀ y ∈ uIoc (-mθ * R) (mθ * R),
        ‖(-((R : ℂ) + (y : ℂ) * Complex.I)) ^ j * Complex.exp (-((R : ℂ) + (y : ℂ) * Complex.I) * (u : ℂ)) *
          φ ((R : ℂ) + (y : ℂ) * Complex.I)‖ ≤
          ((R / Real.cos θ) ^ j * max Mφ 0) * Real.exp (-R * u) := by
      intro y hy
      rw [uIoc_of_le (by nlinarith : -mθ * R ≤ mθ * R)] at hy
      have hy_cc : y ∈ Icc (-mθ * R) (mθ * R) := ⟨hy.1.le, hy.2⟩
      have hnorm_z : ‖-((R : ℂ) + (y : ℂ) * Complex.I)‖ ≤ R / Real.cos θ := by
        rw [norm_neg, Complex.norm_def]
        have hy_sq : y ^ 2 ≤ mθ ^ 2 * R ^ 2 := by
          have : |y| ≤ mθ * R := abs_le.mpr (by simpa [neg_mul] using hy_cc)
          rw [← sq_abs y]
          calc |y| ^ 2 ≤ (mθ * R) ^ 2 := sq_le_sq' (by linarith [abs_nonneg y]) this
            _ = mθ ^ 2 * R ^ 2 := by ring
        have hnsq : Complex.normSq ((R : ℂ) + (y : ℂ) * Complex.I) ≤ (R / Real.cos θ) ^ 2 := by
          rw [Complex.normSq_apply]
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
            mul_one, zero_add]
          have hsec : 1 + mθ ^ 2 = (Real.cos θ) ^ (-2 : ℤ) := by
            dsimp only [mθ]; rw [Real.tan_eq_sin_div_cos, _root_.zpow_neg, zpow_two]
            have hc := hcos.ne'; have hid := Real.sin_sq_add_cos_sq θ
            field_simp [hc]; linarith
          calc R * R + y * y = R ^ 2 + y ^ 2 := by ring
            _ ≤ R ^ 2 + mθ ^ 2 * R ^ 2 := by linarith
            _ = R ^ 2 * (1 + mθ ^ 2) := by ring
            _ = R ^ 2 * (Real.cos θ) ^ (-2 : ℤ) := by rw [hsec]
            _ = (R / Real.cos θ) ^ 2 := by rw [_root_.zpow_neg, zpow_two, div_pow]; ring
        exact Real.sqrt_le_iff.mpr ⟨div_nonneg hR_pos.le hcos.le, hnsq⟩
      have hexp_norm : ‖Complex.exp (-((R : ℂ) + (y : ℂ) * Complex.I) * (u : ℂ))‖ = Real.exp (-R * u) := by
        rw [Complex.norm_exp]; simp [Complex.mul_re]
      have hφ_le : ‖φ ((R : ℂ) + (y : ℂ) * Complex.I)‖ ≤ max Mφ 0 := (hMφ y hy_cc).trans (le_max_left _ _)
      rw [norm_mul, norm_mul, norm_pow, hexp_norm]
      calc ‖-((R : ℂ) + (y : ℂ) * Complex.I)‖ ^ j * Real.exp (-R * u) * ‖φ ((R : ℂ) + (y : ℂ) * Complex.I)‖
          ≤ (R / Real.cos θ) ^ j * Real.exp (-R * u) * max Mφ 0 := by gcongr
        _ = ((R / Real.cos θ) ^ j * max Mφ 0) * Real.exp (-R * u) := by ring
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    calc ‖∫ y : ℝ in (-mθ * R)..(mθ * R), _‖
        ≤ ((R / Real.cos θ) ^ j * max Mφ 0) * Real.exp (-R * u) * |mθ * R - -mθ * R| := hle
      _ = Kv * Real.exp (-R * u) := by
          rw [show mθ * R - -mθ * R = 2 * mθ * R by ring, abs_of_pos (by positivity)]
          dsimp only [Kv]; ring
  refine ⟨Kv + Km + Kp, ?_⟩
  filter_upwards [h_sub_deriv, h_lapP, h_lapM, h_intP, h_intM, hKp, hKm] with
    u hsub hlp hlm hip him hkp_bd hkm_bd
  let Fkern (z : ℂ) : ℂ := (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z
  have hintP_Ioi : IntegrableOn (fun v : ℝ => dPlusJ θ * Fkern (dPlusJ θ * (v : ℂ))) (Ioi 0) :=
    hip.congr_fun (fun v _ => by
      rw [damped, Minor.pull, jet_residual_densityJ φ j]
      have hexp : -((u : ℂ) * dPlusJ θ) * (v : ℂ) = -(dPlusJ θ * (v : ℂ)) * (u : ℂ) := by ring
      rw [hexp]; dsimp only [Fkern]; ring) measurableSet_Ioi
  have hintM_Ioi : IntegrableOn (fun v : ℝ => dMinusJ θ * Fkern (dMinusJ θ * (v : ℂ))) (Ioi 0) :=
    him.congr_fun (fun v _ => by
      rw [damped, Minor.pull, jet_residual_densityJ φ j]
      have hexp : -((u : ℂ) * dMinusJ θ) * (v : ℂ) = -(dMinusJ θ * (v : ℂ)) * (u : ℂ) := by ring
      rw [hexp]; dsimp only [Fkern]; ring) measurableSet_Ioi
  have hsplitP := intervalIntegral.integral_interval_add_Ioi hintP_Ioi
    (hintP_Ioi.mono_set (Ioi_subset_Ioi hv₀_pos.le))
  have hsplitM := intervalIntegral.integral_interval_add_Ioi hintM_Ioi
    (hintM_Ioi.mono_set (Ioi_subset_Ioi hv₀_pos.le))
  have hcovP : ∫ v in (0 : ℝ)..v₀, dPlusJ θ * Fkern (dPlusJ θ * (v : ℂ)) =
      ∫ x in (0 : ℝ)..R, (1 + Complex.I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 + Complex.I * (mθ : ℂ))) := by
    have hcomp := intervalIntegral.integral_comp_div
      (fun v : ℝ => dPlusJ θ * Fkern (dPlusJ θ * (v : ℂ))) hcos.ne' (a := 0) (b := R)
    have hmul_eq : (1 + Complex.I * (mθ : ℂ)) = ((Real.cos θ)⁻¹ : ℂ) * dPlusJ θ := by
      rw [dPlusJ_eq]; dsimp only [mθ]; rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
      have hc : (Real.cos θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos.ne'
      field_simp [hc]
    have heq_int : (fun x : ℝ => (1 + Complex.I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 + Complex.I * (mθ : ℂ)))) =
        fun x : ℝ => (Real.cos θ)⁻¹ • (dPlusJ θ * Fkern (dPlusJ θ * ((x / Real.cos θ : ℝ) : ℂ))) := by
      funext x
      have harg : (x : ℂ) * (1 + Complex.I * (mθ : ℂ)) = dPlusJ θ * ((x / Real.cos θ : ℝ) : ℂ) := by
        rw [hmul_eq]; push_cast; ring
      rw [harg, Complex.real_smul, hmul_eq]; push_cast; ring
    rw [heq_int, intervalIntegral.integral_smul, hcomp, smul_smul, inv_mul_cancel₀ hcos.ne',
      one_smul, zero_div]
  have hcovM : ∫ v in (0 : ℝ)..v₀, dMinusJ θ * Fkern (dMinusJ θ * (v : ℂ)) =
      ∫ x in (0 : ℝ)..R, (1 - Complex.I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 - Complex.I * (mθ : ℂ))) := by
    have hcomp := intervalIntegral.integral_comp_div
      (fun v : ℝ => dMinusJ θ * Fkern (dMinusJ θ * (v : ℂ))) hcos.ne' (a := 0) (b := R)
    have hmul_eq : (1 - Complex.I * (mθ : ℂ)) = ((Real.cos θ)⁻¹ : ℂ) * dMinusJ θ := by
      rw [dMinusJ_eq]; dsimp only [mθ]; rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
      have hc : (Real.cos θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos.ne'
      field_simp [hc]
    have heq_int : (fun x : ℝ => (1 - Complex.I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 - Complex.I * (mθ : ℂ)))) =
        fun x : ℝ => (Real.cos θ)⁻¹ • (dMinusJ θ * Fkern (dMinusJ θ * ((x / Real.cos θ : ℝ) : ℂ))) := by
      funext x
      have harg : (x : ℂ) * (1 - Complex.I * (mθ : ℂ)) = dMinusJ θ * ((x / Real.cos θ : ℝ) : ℂ) := by
        rw [hmul_eq]; push_cast; ring
      rw [harg, Complex.real_smul, hmul_eq]; push_cast; ring
    rw [heq_int, intervalIntegral.integral_smul, hcomp, smul_smul, inv_mul_cancel₀ hcos.ne',
      one_smul, zero_div]
  have h_id : iteratedDeriv j (fun t : ℝ => (aPhiJ φ).value (dMinusJ θ) (t : ℂ) -
        (aPhiJ φ).value (dPlusJ θ) (t : ℂ)) u -
      ∑ m ∈ Finset.range M,
        (2 * (Real.pi : ℂ) * Complex.I * res m * (-(ω m : ℂ)) ^ j) *
          Complex.exp (-(ω m : ℂ) * (u : ℂ)) =
      -(Complex.I * (∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * Complex.I))) +
        (∫ v in Ioi v₀, dMinusJ θ * Fkern (dMinusJ θ * (v : ℂ))) -
        (∫ v in Ioi v₀, dPlusJ θ * Fkern (dPlusJ θ * (v : ℂ))) := by
    rw [hsub, hlm, hlp, ← htri_eq u]
    change (∫ v in Ioi (0 : ℝ), dMinusJ θ * Fkern (dMinusJ θ * (v : ℂ))) -
        (∫ v in Ioi (0 : ℝ), dPlusJ θ * Fkern (dPlusJ θ * (v : ℂ))) -
        triIntegral Fkern R mθ = _
    rw [← hsplitM, ← hsplitP, hcovM, hcovP]; unfold triIntegral; ring
  rw [h_id]
  calc ‖-(Complex.I * ∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * Complex.I)) +
          (∫ v in Ioi v₀, dMinusJ θ * Fkern (dMinusJ θ * (v : ℂ))) -
          (∫ v in Ioi v₀, dPlusJ θ * Fkern (dPlusJ θ * (v : ℂ)))‖
      ≤ ‖-(Complex.I * ∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * Complex.I))‖ +
          ‖∫ v in Ioi v₀, dMinusJ θ * Fkern (dMinusJ θ * (v : ℂ))‖ +
          ‖∫ v in Ioi v₀, dPlusJ θ * Fkern (dPlusJ θ * (v : ℂ))‖ := by
        linarith [norm_sub_le (-(Complex.I * ∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * Complex.I)) +
            (∫ v in Ioi v₀, dMinusJ θ * Fkern (dMinusJ θ * (v : ℂ))))
            (∫ v in Ioi v₀, dPlusJ θ * Fkern (dPlusJ θ * (v : ℂ))),
          norm_add_le (-(Complex.I * ∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * Complex.I)))
            (∫ v in Ioi v₀, dMinusJ θ * Fkern (dMinusJ θ * (v : ℂ)))]
    _ ≤ Kv * Real.exp (-R * u) + Km * Real.exp (-R * u) + Kp * Real.exp (-R * u) := by
        rw [norm_neg]; exact add_le_add (add_le_add (h_vert_bd u) hkm_bd) hkp_bd
    _ = (Kv + Km + Kp) * Real.exp (-R * u) := by ring

private lemma pow_mul_exp_neg_le_oneJ (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ u : ℝ in atTop, u ^ K * Real.exp (-δ * u) ≤ 1 := by
  let U₀ : ℝ := max 1 (((K + 1).factorial : ℝ) / δ ^ (K + 1))
  filter_upwards [eventually_ge_atTop U₀] with u hu
  have hu1 : 1 ≤ u := le_trans (le_max_left _ _) hu
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hU_ge : ((K + 1).factorial : ℝ) / δ ^ (K + 1) ≤ u := le_trans (le_max_right _ _) hu
  have harg := Real.pow_div_factorial_le_exp (δ * u) (by positivity) (K + 1)
  have hfac : 0 < ((K + 1).factorial : ℝ) := by positivity
  have hpow : 0 < (δ * u) ^ (K + 1) := pow_pos (by positivity) (K + 1)
  have hexp : Real.exp (-δ * u) ≤ ((K + 1).factorial : ℝ) / (δ ^ (K + 1) * u ^ (K + 1)) := by
    calc Real.exp (-δ * u) = (Real.exp (δ * u))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
      _ ≤ ((δ * u) ^ (K + 1) / ((K + 1).factorial : ℝ))⁻¹ := inv_anti₀ (div_pos hpow hfac) harg
      _ = ((K + 1).factorial : ℝ) / (δ ^ (K + 1) * u ^ (K + 1)) := by rw [inv_div, mul_pow]
  have hδ_pos : 0 < δ ^ (K + 1) := pow_pos hδ (K + 1)
  calc u ^ K * Real.exp (-δ * u)
      ≤ u ^ K * (((K + 1).factorial : ℝ) / (δ ^ (K + 1) * u ^ (K + 1))) :=
        mul_le_mul_of_nonneg_left hexp (pow_nonneg hu_pos.le K)
    _ = (((K + 1).factorial : ℝ) / δ ^ (K + 1)) / u := by
        rw [pow_succ u K]; field_simp [hu_pos.ne', hδ_pos.ne']
    _ ≤ u / u := div_le_div_of_nonneg_right hU_ge hu_pos.le
    _ = 1 := div_self hu_pos.ne'

private lemma const_mul_exp_neg_le_oneJ {δ C : ℝ} (hδ : 0 < δ) (_hC : 0 ≤ C) :
    ∀ᶠ u : ℝ in atTop, C * Real.exp (-δ * u) ≤ 1 := by
  filter_upwards [eventually_ge_atTop (max 1 (C / δ))] with u hu
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hu)
  have hpow1 := Real.pow_div_factorial_le_exp (δ * u) (by positivity) 1
  rw [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at hpow1
  have hexp : Real.exp (-δ * u) = (Real.exp (δ * u))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
  have hge : C ≤ δ * u := by
    have : C / δ ≤ u := le_trans (le_max_right _ _) hu
    calc C = δ * (C / δ) := by field_simp [hδ.ne']
      _ ≤ δ * u := mul_le_mul_of_nonneg_left this hδ.le
  calc C * Real.exp (-δ * u)
      ≤ (δ * u) * (δ * u)⁻¹ := by
        rw [hexp]; exact mul_le_mul hge (inv_anti₀ (by positivity) hpow1)
          (inv_nonneg.mpr (Real.exp_pos _).le) (by positivity)
    _ = 1 := mul_inv_cancel₀ (by positivity)

private lemma joint_formal_to_lateral_zero {K r : ℕ}
    {φ : Fin K → ℂ → ℂ} {Up Um : Set ℂ} {θ : ℝ}
    (hUp_dom : Domain Up) (hUm_dom : Domain Um)
    (hrayP : ContainsRay Up (dPlusJ θ)) (hrayM : ContainsRay Um (dMinusJ θ))
    (hgoodP : ∀ i : Fin K, (aPhiJ (φ i)).Good Up (dPlusJ θ))
    (hgoodM : ∀ i : Fin K, (aPhiJ (φ i)).Good Um (dMinusJ θ))
    (hreP : 0 < (dPlusJ θ).re) (hreM : 0 < (dMinusJ θ).re)
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ))
    (hP : jointFormalEvalPoly (fun i => formalSeries (φ i)) P = 0) :
    (∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) =>
        iteratedDeriv ij.2.val (fun t : ℝ => (aPhiJ (φ ij.1)).value (dPlusJ θ) (t : ℂ)) u)
        (jointEvalU P (u : ℂ)) = 0) ∧
    (∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) =>
        iteratedDeriv ij.2.val (fun t : ℝ => (aPhiJ (φ ij.1)).value (dMinusJ θ) (t : ℂ)) u)
        (jointEvalU P (u : ℂ)) = 0) := by
  let N := maxUDegJ P
  let Q := revMvPolyJ N P
  have hNP : ∀ α, (P.coeff α).natDegree ≤ N := natDegree_le_maxUDegJ P
  have hQ0 : jointFormalEvalW (fun i => formalSeries (φ i)) Q = 0 :=
    (jointFormalEvalW_eq_zero_iff_poly _ _ hNP).mpr hP
  obtain ⟨e, hs, he⟩ := JointBorelExpr.exists_of_mvPolynomial Q
  have hres_series : (e.residual (fun i => aPhiJ (φ i))).toSeries = 0 := by
    rw [hs Up (dPlusJ θ) (fun i => aPhiJ (φ i)) hUp_dom hrayP hgoodP]
    simpa only [aPhiJ_toSeries] using hQ0
  have hatom : (e.residual (fun i => aPhiJ (φ i))).atom = 0 := by
    have := congrArg (PowerSeries.coeff 0) hres_series
    simpa [Minor.toSeries] using this
  have hderiv_zero : ∀ k : ℕ, iteratedDeriv k (e.residual (fun i => aPhiJ (φ i))).density 0 = 0 := by
    intro k
    have := congrArg (PowerSeries.coeff (k + 1)) hres_series
    simpa [Minor.toSeries] using this
  have h0Up : (0 : ℂ) ∈ Up := by simpa using hrayP 0 le_rfl
  have h0Um : (0 : ℂ) ∈ Um := by simpa using hrayM 0 le_rfl
  have hplus_dens : EqOn (e.residual (fun i => aPhiJ (φ i))).density 0 Up :=
    analyticAt_eqOn_zero_of_iteratedDeriv_zeroJ
      (isPreconnected_of_starJ h0Up hUp_dom.star) h0Up
      (e.represents hUp_dom hrayP hgoodP).1.1 hderiv_zero
  have hminus_dens : EqOn (e.residual (fun i => aPhiJ (φ i))).density 0 Um :=
    analyticAt_eqOn_zero_of_iteratedDeriv_zeroJ
      (isPreconnected_of_starJ h0Um hUm_dom.star) h0Um
      (e.represents hUm_dom hrayM hgoodM).1.1 hderiv_zero
  constructor
  · have hrep := (tendsto_coe_farJ hreP).eventually (e.represents hUp_dom hrayP hgoodP).2
    filter_upwards [hrep, he Up (dPlusJ θ) (fun i => aPhiJ (φ i)) hUp_dom hrayP hgoodP hreP,
      eventually_gt_atTop (0 : ℝ)] with u hu_rep hu_ev hu_pos
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    have hevalQ : MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) =>
        iteratedDeriv ij.2.val (fun t : ℝ => (aPhiJ (φ ij.1)).value (dPlusJ θ) (t : ℂ)) u)
        (jointEvalU Q (u : ℂ)⁻¹) = 0 := by
      rw [← hu_ev, hu_rep, Minor.value, hatom, zero_add]
      refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
      have hd0 : (e.residual (fun i => aPhiJ (φ i))).density (dPlusJ θ * (v : ℂ)) = 0 :=
        hplus_dens (hrayP v hv.le)
      rw [damped, Minor.pull, hd0, mul_zero, mul_zero]
    rw [show Q = revMvPolyJ N P from rfl, jointEvalU_revMvPolyJ P hNP hu_ne,
      MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C] at hevalQ
    exact (mul_eq_zero.mp hevalQ).resolve_left (pow_ne_zero N (inv_ne_zero hu_ne))
  · have hrep := (tendsto_coe_farJ hreM).eventually (e.represents hUm_dom hrayM hgoodM).2
    filter_upwards [hrep, he Um (dMinusJ θ) (fun i => aPhiJ (φ i)) hUm_dom hrayM hgoodM hreM,
      eventually_gt_atTop (0 : ℝ)] with u hu_rep hu_ev hu_pos
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    have hevalQ : MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) =>
        iteratedDeriv ij.2.val (fun t : ℝ => (aPhiJ (φ ij.1)).value (dMinusJ θ) (t : ℂ)) u)
        (jointEvalU Q (u : ℂ)⁻¹) = 0 := by
      rw [← hu_ev, hu_rep, Minor.value, hatom, zero_add]
      refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
      have hd0 : (e.residual (fun i => aPhiJ (φ i))).density (dMinusJ θ * (v : ℂ)) = 0 :=
        hminus_dens (hrayM v hv.le)
      rw [damped, Minor.pull, hd0, mul_zero, mul_zero]
    rw [show Q = revMvPolyJ N P from rfl, jointEvalU_revMvPolyJ P hNP hu_ne,
      MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C] at hevalQ
    exact (mul_eq_zero.mp hevalQ).resolve_left (pow_ne_zero N (inv_ne_zero hu_ne))

private lemma joint_flat_to_formal_zero {K r : ℕ}
    {φ : Fin K → ℂ → ℂ} {Up : Set ℂ} {θ δ : ℝ}
    (hUp_dom : Domain Up) (hrayP : ContainsRay Up (dPlusJ θ))
    (hgoodP : ∀ i : Fin K, (aPhiJ (φ i)).Good Up (dPlusJ θ))
    (hreP : 0 < (dPlusJ θ).re) (hδ : 0 < δ)
    (Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ))
    (hQ : ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) =>
        iteratedDeriv ij.2.val (fun t : ℝ => (aPhiJ (φ ij.1)).value (dPlusJ θ) (t : ℂ)) u)
        (jointEvalU Q (u : ℂ))‖ ≤ C * Real.exp (-δ * u)) :
    jointFormalEvalPoly (fun i => formalSeries (φ i)) Q = 0 := by
  obtain ⟨C, hC⟩ := hQ
  let N := maxUDegJ Q
  let Qrev := revMvPolyJ N Q
  have hNQ : ∀ α, (Q.coeff α).natDegree ≤ N := natDegree_le_maxUDegJ Q
  obtain ⟨e, hs, he⟩ := JointBorelExpr.exists_of_mvPolynomial Qrev
  have hrep := (tendsto_coe_farJ hreP).eventually (e.represents hUp_dom hrayP hgoodP).2
  have hflat : ∀ M : ℕ, ∃ C_M : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖(e.residual (fun i => aPhiJ (φ i))).value (dPlusJ θ) (u : ℂ)‖ ≤ C_M / u ^ (M + 1) := by
    intro M
    refine ⟨max C 0 * (((M + 1).factorial : ℝ) / δ ^ (M + 1)), ?_⟩
    filter_upwards [hC, hrep, he Up (dPlusJ θ) (fun i => aPhiJ (φ i)) hUp_dom hrayP hgoodP hreP,
      eventually_ge_atTop (1 : ℝ)] with u huC hurep huev hu1
    have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    have hinv_le1 : ‖(u : ℂ)⁻¹ ^ N‖ ≤ 1 := by
      rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos]
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hu1)
    rw [← hurep, huev, show Qrev = revMvPolyJ N Q from rfl, jointEvalU_revMvPolyJ Q hNQ hu_ne,
      MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, norm_mul]
    have hexp : Real.exp (-δ * u) ≤ ((M + 1).factorial : ℝ) / (δ ^ (M + 1) * u ^ (M + 1)) := by
      have harg := Real.pow_div_factorial_le_exp (δ * u) (by positivity) (M + 1)
      have hfac : 0 < ((M + 1).factorial : ℝ) := by positivity
      have hpow : 0 < (δ * u) ^ (M + 1) := pow_pos (by positivity) (M + 1)
      calc Real.exp (-δ * u) = (Real.exp (δ * u))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
        _ ≤ ((δ * u) ^ (M + 1) / ((M + 1).factorial : ℝ))⁻¹ := inv_anti₀ (div_pos hpow hfac) harg
        _ = ((M + 1).factorial : ℝ) / (δ ^ (M + 1) * u ^ (M + 1)) := by rw [inv_div, mul_pow]
    calc ‖(u : ℂ)⁻¹ ^ N‖ * ‖MvPolynomial.eval _ (jointEvalU Q (u : ℂ))‖
        ≤ 1 * (C * Real.exp (-δ * u)) := mul_le_mul hinv_le1 huC (norm_nonneg _) zero_le_one
      _ ≤ max C 0 * Real.exp (-δ * u) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le
      _ ≤ max C 0 * (((M + 1).factorial : ℝ) / (δ ^ (M + 1) * u ^ (M + 1))) :=
          mul_le_mul_of_nonneg_left hexp (le_max_right C 0)
      _ = (max C 0 * (((M + 1).factorial : ℝ) / δ ^ (M + 1))) / u ^ (M + 1) := by ring
  have hzero := Minor.toSeries_eq_zero_of_flat (e.residual (fun i => aPhiJ (φ i))) hUp_dom hrayP
    (e.represents hUp_dom hrayP hgoodP).1 hreP hflat
  rw [hs Up (dPlusJ θ) (fun i => aPhiJ (φ i)) hUp_dom hrayP hgoodP] at hzero
  have hzero' : jointFormalEvalW (fun i => formalSeries (φ i)) Qrev = 0 := by
    simpa only [aPhiJ_toSeries] using hzero
  exact (jointFormalEvalW_eq_zero_iff_poly _ _ hNQ).mp hzero'

private lemma joint_lateral_bounded_deriv {φ : ℂ → ℂ} {Up : Set ℂ} {θ : ℝ}
    (hUp_dom : Domain Up) (hrayP : ContainsRay Up (dPlusJ θ))
    (hgoodP : (aPhiJ φ).Good Up (dPlusJ θ)) (hreP : 0 < (dPlusJ θ).re) (j : ℕ) :
    ∃ B : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖iteratedDeriv j (fun t : ℝ => (aPhiJ φ).value (dPlusJ θ) (t : ℂ)) u‖ ≤ B := by
  let e := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  have ha := (e.represents hUp_dom hrayP hgoodP).1
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := Minor.value_asymptotic (e.residual (aPhiJ φ)) hUp_dom hrayP ha hreP 0
  have hrep := (tendsto_coe_farJ hreP).eventually (e.represents hUp_dom hrayP hgoodP).2
  have heq := (BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhiJ φ) hUp_dom hrayP hgoodP hreP j).1
  refine ⟨‖(e.residual (aPhiJ φ)).atom‖ + C₀, ?_⟩
  filter_upwards [hC₀, hrep, heq, eventually_ge_atTop (1 : ℝ)] with u hu0 hurep hueq hu1
  have heq' : iteratedDeriv j (fun t : ℝ => (aPhiJ φ).value (dPlusJ θ) (t : ℂ)) u =
      (e.residual (aPhiJ φ)).value (dPlusJ θ) (u : ℂ) := hueq.symm.trans hurep
  rw [heq']
  have hu0' : ‖(e.residual (aPhiJ φ)).value (dPlusJ θ) (u : ℂ) -
      (e.residual (aPhiJ φ)).atom‖ ≤ C₀ := by
    simpa using hu0.trans (div_le_self hC₀_nn (one_le_pow₀ hu1))
  calc ‖(e.residual (aPhiJ φ)).value (dPlusJ θ) (u : ℂ)‖
      = ‖((e.residual (aPhiJ φ)).value (dPlusJ θ) (u : ℂ) -
          (e.residual (aPhiJ φ)).atom) + (e.residual (aPhiJ φ)).atom‖ := by congr 1; ring
    _ ≤ ‖(e.residual (aPhiJ φ)).value (dPlusJ θ) (u : ℂ) -
          (e.residual (aPhiJ φ)).atom‖ + ‖(e.residual (aPhiJ φ)).atom‖ := norm_add_le _ _
    _ ≤ ‖(e.residual (aPhiJ φ)).atom‖ + C₀ := by linarith

private lemma exp_comb_rhs_le {CL Cr CT A u R lam δ : ℝ} {Du : ℕ}
    (hCL : 0 ≤ CL) (hCr : 0 ≤ Cr) (hCT : 0 ≤ CT) (hA : 0 < A)
    (h1 : u ^ Du * Real.exp (-R * u) ≤ Real.exp (-lam * u) * Real.exp (-(δ / 2) * u))
    (h2 : u ^ Du * Real.exp (-lam * u) ^ 2 ≤ Real.exp (-lam * u) * Real.exp (-(δ / 2) * u)) :
    (CL * Cr) * u ^ Du * Real.exp (-R * u) + CT * u ^ Du * (A ^ 2 * Real.exp (-lam * u) ^ 2) ≤
      (A * Real.exp (-lam * u)) * (((CL * Cr + CT * A ^ 2) / A) * Real.exp (-(δ / 2) * u)) := by
  have hcomb : (CL * Cr) * (u ^ Du * Real.exp (-R * u)) +
        (CT * A ^ 2) * (u ^ Du * Real.exp (-lam * u) ^ 2) ≤
      (CL * Cr + CT * A ^ 2) * (Real.exp (-lam * u) * Real.exp (-(δ / 2) * u)) := by
    calc (CL * Cr) * (u ^ Du * Real.exp (-R * u)) +
          (CT * A ^ 2) * (u ^ Du * Real.exp (-lam * u) ^ 2)
        ≤ (CL * Cr) * (Real.exp (-lam * u) * Real.exp (-(δ / 2) * u)) +
            (CT * A ^ 2) * (Real.exp (-lam * u) * Real.exp (-(δ / 2) * u)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (mul_nonneg hCL hCr))
            (mul_le_mul_of_nonneg_left h2 (mul_nonneg hCT (sq_nonneg A)))
      _ = (CL * Cr + CT * A ^ 2) * (Real.exp (-lam * u) * Real.exp (-(δ / 2) * u)) := by ring
  have hL : (CL * Cr) * u ^ Du * Real.exp (-R * u) + CT * u ^ Du * (A ^ 2 * Real.exp (-lam * u) ^ 2) =
      (CL * Cr) * (u ^ Du * Real.exp (-R * u)) + (CT * A ^ 2) * (u ^ Du * Real.exp (-lam * u) ^ 2) := by ring
  have hR : (A * Real.exp (-lam * u)) * (((CL * Cr + CT * A ^ 2) / A) * Real.exp (-(δ / 2) * u)) =
      (CL * Cr + CT * A ^ 2) * (Real.exp (-lam * u) * Real.exp (-(δ / 2) * u)) := by
    calc (A * Real.exp (-lam * u)) * (((CL * Cr + CT * A ^ 2) / A) * Real.exp (-(δ / 2) * u))
        = (A * ((CL * Cr + CT * A ^ 2) / A)) * (Real.exp (-lam * u) * Real.exp (-(δ / 2) * u)) := by ring
      _ = (CL * Cr + CT * A ^ 2) * (Real.exp (-lam * u) * Real.exp (-(δ / 2) * u)) := by
            rw [mul_div_cancel₀ _ hA.ne']
  rw [hL, hR]; exact hcomb

set_option maxHeartbeats 3200000 in
/-- **Unrotated Multi-Function Simple-Pole Joint Differential Independence (`θ₀ = 0`, `ℂ[u]`)**:
Given `JointSimplePoleFamily K φ 0 ω res`, any joint polynomial ODE `P ∈ ℂ[u][Y_{i, j}]`
annihilating `(formalSeries (φ 0), ..., formalSeries (φ (K-1)))` must vanish identically. -/

private lemma hasAsympExp_jointEvalW {K r : ℕ}
    {f : Fin K × Fin (r + 1) → ℝ → ℂ} {S : Fin K × Fin (r + 1) → PowerSeries ℂ}
    (hf : ∀ ij, HasAsympExp (f ij) (S ij))
    (Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) :
    HasAsympExp
      (fun u : ℝ => MvPolynomial.eval (fun ij => f ij u) (jointEvalU Q (u : ℂ)⁻¹))
      (MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom S Q) := by
  induction Q using MvPolynomial.induction_on with
  | C q =>
    have hq : HasAsympExp (fun u : ℝ => q.eval (u : ℂ)⁻¹) (q : PowerSeries ℂ) := by
      intro N
      refine ⟨∑ k ∈ Finset.range (q.natDegree + 1), ‖q.coeff k‖, ?_⟩
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
      have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
      have hq_sum : q.eval (u : ℂ)⁻¹ =
          ∑ k ∈ Finset.range (max N (q.natDegree + 1)), q.coeff k * (u : ℂ)⁻¹ ^ k := by
        rw [Polynomial.eval_eq_sum_range' (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right N _))]
      have hps_sum : ∑ k ∈ Finset.range N, PowerSeries.coeff k (q : PowerSeries ℂ) * (u : ℂ)⁻¹ ^ k =
          ∑ k ∈ Finset.range N, q.coeff k * (u : ℂ)⁻¹ ^ k := by
        refine Finset.sum_congr rfl fun k _ => by rw [Polynomial.coeff_coe]
      rw [hq_sum, hps_sum]
      have hsub : (∑ k ∈ Finset.range (max N (q.natDegree + 1)), q.coeff k * (u : ℂ)⁻¹ ^ k) -
          (∑ k ∈ Finset.range N, q.coeff k * (u : ℂ)⁻¹ ^ k) =
          ∑ k ∈ (Finset.range (max N (q.natDegree + 1))) \ (Finset.range N),
            q.coeff k * (u : ℂ)⁻¹ ^ k := by
        rw [Finset.sum_sdiff_eq_sub (Finset.range_mono (le_max_left N _))]
      rw [hsub]
      calc ‖∑ k ∈ (Finset.range (max N (q.natDegree + 1))) \ (Finset.range N),
              q.coeff k * (u : ℂ)⁻¹ ^ k‖
          ≤ ∑ k ∈ (Finset.range (max N (q.natDegree + 1))) \ (Finset.range N),
              ‖q.coeff k * (u : ℂ)⁻¹ ^ k‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ (Finset.range (max N (q.natDegree + 1))) \ (Finset.range N),
              ‖q.coeff k‖ / u ^ N := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hkN : N ≤ k := not_lt.mp (Finset.mem_range.not.mp (Finset.mem_sdiff.mp hk).2)
            rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu_pos.le,
              inv_pow, ← div_eq_mul_inv]
            exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hu_pos N) (pow_le_pow_right₀ hu hkN)
        _ = (∑ k ∈ (Finset.range (max N (q.natDegree + 1))) \ (Finset.range N), ‖q.coeff k‖) / u ^ N := by
            rw [Finset.sum_div]
        _ ≤ (∑ k ∈ Finset.range (q.natDegree + 1), ‖q.coeff k‖) / u ^ N := by
            refine div_le_div_of_nonneg_right ?_ (pow_nonneg hu_pos.le N)
            have hle : ∑ k ∈ (Finset.range (max N (q.natDegree + 1))) \ (Finset.range N), ‖q.coeff k‖ ≤
                ∑ k ∈ Finset.range (max N (q.natDegree + 1)), ‖q.coeff k‖ :=
              Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => norm_nonneg _
            refine hle.trans_eq ?_
            refine (Finset.sum_subset (Finset.range_mono (le_max_right N _)) fun k _ hnot => ?_).symm
            rw [Finset.mem_range, not_lt] at hnot
            rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]
    simpa [jointEvalU] using hq
  | add A B hA hB =>
    have h1 : (fun u : ℝ => MvPolynomial.eval (fun ij => f ij u) (jointEvalU (A + B) (u : ℂ)⁻¹)) =
        fun u => MvPolynomial.eval (fun ij => f ij u) (jointEvalU A (u : ℂ)⁻¹) +
          MvPolynomial.eval (fun ij => f ij u) (jointEvalU B (u : ℂ)⁻¹) := by
      funext u; simp only [jointEvalU, map_add]
    rw [h1, MvPolynomial.eval₂_add]
    exact hA.add hB
  | mul_X A ij hA =>
    have h1 : (fun u : ℝ => MvPolynomial.eval (fun ij' => f ij' u)
        (jointEvalU (A * MvPolynomial.X ij) (u : ℂ)⁻¹)) = fun u =>
        MvPolynomial.eval (fun ij' => f ij' u) (jointEvalU A (u : ℂ)⁻¹) * f ij u := by
      funext u; simp only [jointEvalU, map_mul, MvPolynomial.map_X, MvPolynomial.eval_X]
    rw [h1, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact hA.mul (hf ij)


/-- Complex-analytic hypotheses for a `K`-tuple of simple-pole Borel transforms `φ : Fin K → ℂ → ℂ`
sharing a common strictly increasing real pole lattice `ω : ℕ → ℝ` (`ω 0 > 0`) with residues
`res : Fin K → ℕ → ℂ` (allowing `res i m = 0` when `φ i` is analytic at `ω m`), flanking-ray
`ExpType` bounds, and a residue-matrix rank hypothesis `hRank` killing all partial derivatives. -/
structure SharedLatticeSimplePoleFamily
    (K : ℕ) (φ : Fin K → ℂ → ℂ) (ω : ℕ → ℝ) (res : Fin K → ℕ → ℂ) where
  α₀ : ℝ
  θ : ℝ
  ε : ℝ
  hθ_pos : 0 < θ
  hθ_lt : θ < α₀
  hα₀_lt : α₀ < Real.pi / 2
  hε_pos : 0 < ε
  ω_pos : 0 < ω 0
  ω_mono : StrictMono ω
  analyticOn : ∀ i : Fin K, AnalyticOnNhd ℂ (φ i) (puncturedWedge α₀ ε ω)
  pole_res : ∀ i : Fin K, ∀ m : ℕ, ∃ L : ℂ,
    Filter.Tendsto
      (fun z : ℂ => φ i z - res i m / (z - (ω m : ℂ)))
      (𝓝[≠] (ω m : ℂ)) (𝓝 L)
  expType_plus : ∀ i : Fin K, ExpType (Minor.pull (Complex.exp (Complex.I * (θ : ℂ))) (φ i))
  expType_minus : ∀ i : Fin K, ExpType (Minor.pull (Complex.exp (-Complex.I * (θ : ℂ))) (φ i))
  hRank : ∀ {r : ℕ} (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)),
    (∀ m : ℕ, ∑ i : Fin K, ∑ j : Fin (r + 1),
      MvPolynomial.C (Polynomial.C (res i m * (-(ω m : ℂ)) ^ j.val)) * MvPolynomial.pderiv (i, j) P = 0) →
    ∀ ij : Fin K × Fin (r + 1), MvPolynomial.pderiv ij P = 0

/-- Shared-lattice Stokes directional derivative at lattice point `m`:
`D_shared m P = ∑ i, res i m • D_joint K r i (ω m) P`. -/
private def D_shared (K r : ℕ) (ω : ℕ → ℝ) (res : Fin K → ℕ → ℂ) (m : ℕ)
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) :
    MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ) :=
  ∑ i : Fin K, ∑ j : Fin (r + 1),
    MvPolynomial.C (Polynomial.C (res i m * (-(ω m : ℂ)) ^ j.val)) * MvPolynomial.pderiv (i, j) P

private lemma degree_D_shared_lt {K r : ℕ} (ω : ℕ → ℝ) (res : Fin K → ℕ → ℂ) (m : ℕ)
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) (hpos : 0 < P.totalDegree) :
    (D_shared K r ω res m P).totalDegree < P.totalDegree := by
  unfold D_shared
  refine totalDegree_poly_sum_ltJ Finset.univ _ hpos fun i _ => ?_
  refine totalDegree_poly_sum_ltJ Finset.univ _ hpos fun j _ => ?_
  calc (MvPolynomial.C (Polynomial.C (res i m * (-(ω m : ℂ)) ^ j.val)) * MvPolynomial.pderiv (i, j) P).totalDegree
      ≤ (MvPolynomial.C (Polynomial.C (res i m * (-(ω m : ℂ)) ^ j.val))).totalDegree +
          (MvPolynomial.pderiv (i, j) P).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = (MvPolynomial.pderiv (i, j) P).totalDegree := by rw [MvPolynomial.totalDegree_C, zero_add]
    _ < P.totalDegree := degree_pderiv_poly_ltJ (i, j) P hpos

private lemma jointEvalU_D_shared {K r : ℕ} (ω : ℕ → ℝ) (res : Fin K → ℕ → ℂ) (m : ℕ) (u : ℂ)
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) :
    jointEvalU (D_shared K r ω res m P) u =
      ∑ ij : Fin K × Fin (r + 1),
        (res ij.1 m * (-(ω m : ℂ)) ^ ij.2.val) • MvPolynomial.pderiv ij (jointEvalU P u) := by
  unfold D_shared jointEvalU
  rw [Fintype.sum_prod_type, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, MvPolynomial.map_C, Polynomial.coe_evalRingHom, Polynomial.eval_C,
    MvPolynomial.pderiv_map, MvPolynomial.smul_eq_C_mul]

/-- **Shared-Lattice Simple-Pole Joint Stokes–Vandermonde Engine**:
For any `SharedLatticeSimplePoleFamily`, no nonzero `P ∈ ℂ[u][Y_{i, j}]` annihilates the formal
Borel–Laplace series `(formalSeries (φ 0), ..., formalSeries (φ (K-1)))`. -/
theorem shared_lattice_joint_stokes_no_ade {K : ℕ}
    {φ : Fin K → ℂ → ℂ} {ω : ℕ → ℝ} {res : Fin K → ℕ → ℂ}
    (h : SharedLatticeSimplePoleFamily K φ ω res)
    {r : ℕ} (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ))
    (hP : jointFormalEvalPoly (fun i => formalSeries (φ i)) P = 0) : P = 0 := by
  classical
  by_contra hP_ne
  have hex : ∃ d : ℕ, ∃ Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ),
      Q.totalDegree = d ∧ Q ≠ 0 ∧ jointFormalEvalPoly (fun i => formalSeries (φ i)) Q = 0 :=
    ⟨P.totalDegree, P, rfl, hP_ne, hP⟩
  let Pmin := Classical.choose (Nat.find_spec hex)
  have hPmin_spec := Classical.choose_spec (Nat.find_spec hex)
  have hPmin_deg : Pmin.totalDegree = Nat.find hex := hPmin_spec.1
  have hPmin_ne : Pmin ≠ 0 := hPmin_spec.2.1
  have hPmin_zero : jointFormalEvalPoly (fun i => formalSeries (φ i)) Pmin = 0 := hPmin_spec.2.2
  have hPmin_min : ∀ Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ),
      Q ≠ 0 → Q.totalDegree < Pmin.totalDegree →
        ¬ jointFormalEvalPoly (fun i => formalSeries (φ i)) Q = 0 := by
    intro Q hQ_ne hQ_deg hQ_zero
    rw [hPmin_deg] at hQ_deg
    exact Nat.find_min hex hQ_deg ⟨Q, rfl, hQ_ne, hQ_zero⟩
  have hPmin_pos_deg : 0 < Pmin.totalDegree := by
    by_contra! hle
    have h0 : Pmin.totalDegree = 0 := Nat.eq_zero_of_le_zero hle
    have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
    have hev0 : jointFormalEvalPoly (fun i => formalSeries (φ i))
        (MvPolynomial.C (Pmin.coeff 0) : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) = 0 := by
      rw [← hC]; exact hPmin_zero
    have hp0 : polyToLaurent (Pmin.coeff 0) = 0 := by simpa [jointFormalEvalPoly] using hev0
    have hc0 : Pmin.coeff 0 = 0 := polyToLaurent_injectiveJ (hp0.trans (map_zero _).symm)
    exact hPmin_ne (hC.trans (by rw [hc0, map_zero]))
  -- Shared wedge setup
  have hα_pos : 0 < h.α₀ := h.hθ_pos.trans h.hθ_lt
  let ε₀ : ℝ := min h.ε (ω 0 / 2)
  have hε₀_pos : 0 < ε₀ := lt_min h.hε_pos (half_pos h.ω_pos)
  have hε₀_le : ε₀ ≤ h.ε := min_le_left _ _
  have hε₀_lt : ε₀ ≤ ω 0 / 2 := min_le_right _ _
  let Up := wedgePlusJ h.α₀ ε₀
  let Um := wedgeMinusJ h.α₀ ε₀
  have hUp_dom : Domain Up := wedgePlusJ_domain hε₀_pos
  have hUm_dom : Domain Um := wedgeMinusJ_domain hε₀_pos
  have hrayP : ContainsRay Up (dPlusJ h.θ) := wedgePlusJ_containsRay h.hθ_pos h.hθ_lt h.hα₀_lt hε₀_pos
  have hrayM : ContainsRay Um (dMinusJ h.θ) := wedgeMinusJ_containsRay h.hθ_pos h.hθ_lt h.hα₀_lt hε₀_pos
  have hcos : 0 < Real.cos h.θ := cos_pos_J h.hθ_pos h.hθ_lt h.hα₀_lt
  have hreP : 0 < (dPlusJ h.θ).re := by rw [dPlusJ_re]; exact hcos
  have hreM : 0 < (dMinusJ h.θ).re := by rw [dMinusJ_re]; exact hcos
  have hexpP : ∀ i : Fin K, ExpType (Minor.pull (dPlusJ h.θ) (φ i)) := fun i => h.expType_plus i
  have hexpM : ∀ i : Fin K, ExpType (Minor.pull (dMinusJ h.θ) (φ i)) := fun i => h.expType_minus i
  have hAn0 : ∀ i : Fin K, AnalyticOnNhd ℂ (φ i) (rotatedPuncturedWedge 0 h.α₀ h.ε ω) := fun i => by
    rw [rotatedPuncturedWedge_zero_eqJ]; exact h.analyticOn i
  have hgoodP : ∀ i : Fin K, (aPhiJ (φ i)).Good Up (dPlusJ h.θ) := fun i =>
    ⟨(hAn0 i).mono (wedgePlusJ_subset_punctured hα_pos h.hα₀_lt hε₀_le hε₀_lt h.ω_pos h.ω_mono), hexpP i⟩
  have hgoodM : ∀ i : Fin K, (aPhiJ (φ i)).Good Um (dMinusJ h.θ) := fun i =>
    ⟨(hAn0 i).mono (wedgeMinusJ_subset_punctured hα_pos h.hα₀_lt hε₀_le hε₀_lt h.ω_pos h.ω_mono), hexpM i⟩
  let g_pos (i : Fin K) (t : ℝ) : ℂ := (aPhiJ (φ i)).value (dPlusJ h.θ) (t : ℂ)
  let g_neg (i : Fin K) (t : ℝ) : ℂ := (aPhiJ (φ i)).value (dMinusJ h.θ) (t : ℂ)
  have hPmin_lateral :=
    joint_formal_to_lateral_zero hUp_dom hUm_dom hrayP hrayM hgoodP hgoodM hreP hreM Pmin hPmin_zero
  have hflat_to_formal : ∀ {δ : ℝ}, 0 < δ →
      ∀ Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ),
      (∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
        ‖MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) =>
          iteratedDeriv ij.2.val (g_pos ij.1) u) (jointEvalU Q (u : ℂ))‖ ≤ C * Real.exp (-δ * u)) →
      jointFormalEvalPoly (fun i => formalSeries (φ i)) Q = 0 :=
    fun hδ Q hQ => joint_flat_to_formal_zero hUp_dom hrayP hgoodP hreP hδ Q hQ
  have h_bg_each : ∀ ij : Fin K × Fin (r + 1), ∃ B : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖iteratedDeriv ij.2.val (g_pos ij.1) u‖ ≤ B :=
    fun ij => joint_lateral_bounded_deriv hUp_dom hrayP (hgoodP ij.1) hreP ij.2.val
  -- Strong induction peeling off every lattice point `m = 0, 1, 2, ...`!
  have hD_peel : ∀ m₀ : ℕ, D_shared K r ω res m₀ Pmin = 0 := by
    intro m₀
    induction m₀ using Nat.strong_induction_on with
    | ind m₀ ih =>
      let lam₀ : ℝ := ω m₀
      have hlam₀_pos : 0 < lam₀ := lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m₀))
      have hlam₀_lt_next : lam₀ < ω (m₀ + 1) := h.ω_mono (Nat.lt_succ_self m₀)
      let R_cut : ℝ := (lam₀ + ω (m₀ + 1)) / 2
      have hlam₀_lt_R : lam₀ < R_cut := by dsimp only [R_cut]; linarith
      have hR_lt_next : R_cut < ω (m₀ + 1) := by dsimp only [R_cut]; linarith
      have hR_pos : 0 < R_cut := lt_trans hlam₀_pos hlam₀_lt_R
      have hM_lt_R : ∀ m : ℕ, m < m₀ + 1 → ω m < R_cut := fun m hm =>
        lt_of_le_of_lt (h.ω_mono.monotone (Nat.lt_succ_iff.mp hm)) hlam₀_lt_R
      -- Shift invariance of `jointEvalU Pmin u` along any earlier lattice vector `v_m` (`m < m₀`).
      let v_lat (m : ℕ) (ij : Fin K × Fin (r + 1)) : ℂ := res ij.1 m * (-(ω m : ℂ)) ^ ij.2.val
      have h_shift_one : ∀ (u : ℝ) (m : ℕ), m < m₀ →
          ∀ (x : Fin K × Fin (r + 1) → ℂ) (a : ℂ),
          MvPolynomial.eval (fun ij => x ij + a * v_lat m ij) (jointEvalU Pmin (u : ℂ)) =
            MvPolynomial.eval x (jointEvalU Pmin (u : ℂ)) := by
        intro u m hm x a
        have hv_zero : ∑ ij : Fin K × Fin (r + 1),
            v_lat m ij • MvPolynomial.pderiv ij (jointEvalU Pmin (u : ℂ)) = 0 := by
          rw [← jointEvalU_D_shared ω res m (u : ℂ) Pmin, ih m hm, jointEvalU, map_zero]
        exact shift_invariant_any (v_lat m) (jointEvalU Pmin (u : ℂ)) hv_zero x a
      have h_shift_range : ∀ (n : ℕ), n ≤ m₀ →
          ∀ (u : ℝ) (x : Fin K × Fin (r + 1) → ℂ) (c : ℕ → ℂ),
          MvPolynomial.eval (fun ij => x ij + ∑ m ∈ Finset.range n, c m * v_lat m ij)
              (jointEvalU Pmin (u : ℂ)) =
            MvPolynomial.eval x (jointEvalU Pmin (u : ℂ)) := by
        intro n hn u x c
        induction n generalizing x with
        | zero => simp
        | succ n ihn =>
          have hrew : (fun ij : Fin K × Fin (r + 1) => x ij + ∑ m ∈ Finset.range (n + 1), c m * v_lat m ij) =
              fun ij => (x ij + ∑ m ∈ Finset.range n, c m * v_lat m ij) + c n * v_lat n ij := by
            funext ij; rw [Finset.sum_range_succ]; ring
          rw [hrew, h_shift_one u n (by omega) _ (c n), ihn (by omega)]
      -- Assemble Stokes jump expansions at cut `R_cut` (`M = m₀ + 1`) for every `(i, j)`.
      choose Cexp h_exp_ev using fun ij : Fin K × Fin (r + 1) =>
        simplePole_stokes_jump_at_cut (φ := φ ij.1) (ω := ω) (res := res ij.1)
          (α₀ := h.α₀) (θ := h.θ) (ε := h.ε) (ε₀ := ε₀) (R := R_cut) (M := m₀ + 1)
          h.hθ_pos h.hθ_lt h.hα₀_lt hε₀_pos hε₀_le hε₀_lt h.ω_pos h.ω_mono
          (hAn0 ij.1) (h.pole_res ij.1) (hexpP ij.1) (hexpM ij.1)
          hR_pos hM_lt_R hR_lt_next ij.2.val
      have h_all_exp : ∀ᶠ u : ℝ in atTop, ∀ ij : Fin K × Fin (r + 1),
          ‖iteratedDeriv ij.2.val (fun t : ℝ => g_neg ij.1 t - g_pos ij.1 t) u -
            ∑ m ∈ Finset.range (m₀ + 1),
              (2 * (Real.pi : ℂ) * Complex.I * res ij.1 m * (-(ω m : ℂ)) ^ ij.2.val) *
                Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ ≤
            Cexp ij * Real.exp (-R_cut * u) :=
        Filter.eventually_all.mpr h_exp_ev
      have h_all_sub : ∀ᶠ u : ℝ in atTop, ∀ ij : Fin K × Fin (r + 1),
          iteratedDeriv ij.2.val (fun t : ℝ => g_neg ij.1 t - g_pos ij.1 t) u =
            iteratedDeriv ij.2.val (g_neg ij.1) u - iteratedDeriv ij.2.val (g_pos ij.1) u :=
        Filter.eventually_all.mpr fun ij =>
          eventually_iteratedDeriv_sub
            (fun k _ => (BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhiJ (φ ij.1)) hUm_dom hrayM (hgoodM ij.1) hreM k).2)
            (fun k _ => (BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhiJ (φ ij.1)) hUp_dom hrayP (hgoodP ij.1) hreP k).2)
      choose Bg hBg using h_bg_each
      have h_all_bg : ∀ᶠ u : ℝ in atTop, ∀ ij : Fin K × Fin (r + 1),
          ‖iteratedDeriv ij.2.val (g_pos ij.1) u‖ ≤ Bg ij :=
        Filter.eventually_all.mpr hBg
      let amp₀ : ℂ := 2 * (Real.pi : ℂ) * Complex.I
      have hamp₀_ne : amp₀ ≠ 0 := by
        have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
      let v_dir : Fin K × Fin (r + 1) → ℂ := v_lat m₀
      let M_v : ℝ := ∑ ij : Fin K × Fin (r + 1), ‖v_dir ij‖
      let M_box : ℝ := 2 + (∑ ij : Fin K × Fin (r + 1), |Bg ij|) + M_v
      have hM_nn : 0 ≤ M_box := by
        have h1 : 0 ≤ ∑ ij : Fin K × Fin (r + 1), |Bg ij| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        have h2 : 0 ≤ M_v := Finset.sum_nonneg fun _ _ => norm_nonneg _
        dsimp only [M_box]; linarith
      have hBg_le : ∀ ij, |Bg ij| + 2 ≤ M_box := fun ij => by
        have h1 : |Bg ij| ≤ ∑ p : Fin K × Fin (r + 1), |Bg p| :=
          Finset.single_le_sum (f := fun p => |Bg p|) (fun _ _ => abs_nonneg _) (Finset.mem_univ ij)
        have h2 : 0 ≤ M_v := Finset.sum_nonneg fun _ _ => norm_nonneg _
        dsimp only [M_box]; linarith
      have hv_le : ∀ ij, ‖v_dir ij‖ ≤ M_box := fun ij => by
        have h1 : 0 ≤ ∑ p : Fin K × Fin (r + 1), |Bg p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        have h2 : ‖v_dir ij‖ ≤ M_v :=
          Finset.single_le_sum (f := fun p => ‖v_dir p‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ ij)
        dsimp only [M_box]; linarith
      let C_rem : ℝ := ∑ ij : Fin K × Fin (r + 1), max (Cexp ij) 0
      have hC_rem_nn : 0 ≤ C_rem := Finset.sum_nonneg fun _ _ => le_max_right _ _
      let Du : ℕ := maxUDegJ Pmin
      choose C_lip_k hC_lip_k h_lip_k using fun k : ℕ => eval_lipschitz_of_bounded (coeffUJ k Pmin) hM_nn
      choose C_tay_k hC_tay_k h_tay_k using fun k : ℕ => eval_shift_taylor_bound_any (coeffUJ k Pmin) hM_nn
      let C_L : ℝ := ∑ k ∈ Finset.range (Du + 1), C_lip_k k
      let C_T : ℝ := ∑ k ∈ Finset.range (Du + 1), C_tay_k k
      have hC_L_nn : 0 ≤ C_L := Finset.sum_nonneg fun k _ => hC_lip_k k
      have hC_T_nn : 0 ≤ C_T := Finset.sum_nonneg fun k _ => hC_tay_k k
      let δ_gap : ℝ := min lam₀ (R_cut - lam₀)
      have hδ_pos : 0 < δ_gap := lt_min hlam₀_pos (by linarith)
      have hS_small : ∀ᶠ u : ℝ in atTop, ∀ ij : Fin K × Fin (r + 1),
          ‖∑ m ∈ Finset.range (m₀ + 1),
            (2 * (Real.pi : ℂ) * Complex.I * res ij.1 m * (-(ω m : ℂ)) ^ ij.2.val) *
              Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ ≤ 1 := by
        refine Filter.eventually_all.mpr fun ij => ?_
        have hM_pos : (0 : ℝ) < ((m₀ + 1 : ℕ) : ℝ) := by positivity
        have hterm : ∀ m ∈ Finset.range (m₀ + 1), ∀ᶠ u : ℝ in atTop,
            ‖(2 * (Real.pi : ℂ) * Complex.I * res ij.1 m * (-(ω m : ℂ)) ^ ij.2.val) *
              Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ ≤ 1 / ((m₀ + 1 : ℕ) : ℝ) := by
          intro m _
          have hωm : 0 < ω m := lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))
          let C_m : ℝ := ((m₀ + 1 : ℕ) : ℝ) * ‖2 * (Real.pi : ℂ) * Complex.I * res ij.1 m * (-(ω m : ℂ)) ^ ij.2.val‖
          filter_upwards [const_mul_exp_neg_le_oneJ hωm (by positivity : 0 ≤ C_m)] with u hu
          rw [norm_mul, Complex.norm_exp,
            show (-(ω m : ℂ) * (u : ℂ)).re = -ω m * u from by simp [Complex.mul_re] ]
          rw [le_div_iff₀' hM_pos]
          dsimp only [C_m] at hu; linarith
        filter_upwards [(Filter.eventually_all_finset (Finset.range (m₀ + 1))).mpr hterm] with u hu
        calc ‖∑ m ∈ Finset.range (m₀ + 1), _‖
            ≤ ∑ m ∈ Finset.range (m₀ + 1), ‖_‖ := norm_sum_le _ _
          _ ≤ ∑ _m ∈ Finset.range (m₀ + 1), (1 / ((m₀ + 1 : ℕ) : ℝ)) := Finset.sum_le_sum hu
          _ = 1 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, one_div, mul_inv_cancel₀ hM_pos.ne']
      have ha_small : ∀ᶠ u : ℝ in atTop, ‖amp₀‖ * Real.exp (-lam₀ * u) ≤ 1 :=
        const_mul_exp_neg_le_oneJ hlam₀_pos (norm_nonneg amp₀)
      have hrem_small : ∀ᶠ u : ℝ in atTop, C_rem * Real.exp (-R_cut * u) ≤ 1 :=
        const_mul_exp_neg_le_oneJ hR_pos hC_rem_nn
      have hu_poly_exp : ∀ᶠ u : ℝ in atTop, u ^ Du * Real.exp (-(δ_gap / 2) * u) ≤ 1 :=
        pow_mul_exp_neg_le_oneJ Du (half_pos hδ_pos)
      have h_bridge : ∀ᶠ u : ℝ in atTop,
          ‖MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) => iteratedDeriv ij.2.val (g_pos ij.1) u)
            (jointEvalU (D_shared K r ω res m₀ Pmin) (u : ℂ))‖ ≤
            ((C_L * C_rem + C_T * ‖amp₀‖ ^ 2) / ‖amp₀‖) * Real.exp (-(δ_gap / 2) * u) := by
        filter_upwards [h_all_bg, h_all_exp, h_all_sub, hPmin_lateral.1, hPmin_lateral.2,
          hS_small, ha_small, hrem_small, hu_poly_exp, eventually_ge_atTop (1 : ℝ)] with
          u hbg hexp hsub hpos hneg hS1 ha1 hrem1 hpoly_u hu1
        have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
        let x : Fin K × Fin (r + 1) → ℂ := fun ij => iteratedDeriv ij.2.val (g_pos ij.1) u
        let S : Fin K × Fin (r + 1) → ℂ := fun ij =>
          ∑ m ∈ Finset.range (m₀ + 1),
            (2 * (Real.pi : ℂ) * Complex.I * res ij.1 m * (-(ω m : ℂ)) ^ ij.2.val) *
              Complex.exp (-(ω m : ℂ) * (u : ℂ))
        let y : Fin K × Fin (r + 1) → ℂ := fun ij => x ij + S ij
        let z : Fin K × Fin (r + 1) → ℂ := fun ij => iteratedDeriv ij.2.val (g_neg ij.1) u
        let a : ℂ := amp₀ * Complex.exp (-(lam₀ : ℂ) * (u : ℂ))
        have ha_norm : ‖a‖ = ‖amp₀‖ * Real.exp (-lam₀ * u) := by
          simp only [a, norm_mul, Complex.norm_exp,
            show (-(lam₀ : ℂ) * (u : ℂ)).re = -lam₀ * u from by simp [Complex.mul_re] ]
        have ha_le1 : ‖a‖ ≤ 1 := ha_norm ▸ ha1
        have hx_le : ∀ ij, ‖x ij‖ ≤ M_box := fun ij =>
          (hbg ij).trans ((le_abs_self _).trans (by linarith [hBg_le ij]))
        have hy_le : ∀ ij, ‖y ij‖ ≤ M_box := fun ij =>
          (norm_add_le _ _).trans ((add_le_add ((hbg ij).trans (le_abs_self _)) (hS1 ij)).trans (by linarith [hBg_le ij]))
        have hzy_le : ∀ ij, ‖z ij - y ij‖ ≤ C_rem * Real.exp (-R_cut * u) := fun ij => by
          have hsub_eq : z ij - y ij = iteratedDeriv ij.2.val (fun t => g_neg ij.1 t - g_pos ij.1 t) u - S ij := by
            rw [hsub ij]; simp only [y, x, z]; ring
          rw [hsub_eq]
          refine (hexp ij).trans ?_
          exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans
            (Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ ij))) (Real.exp_pos _).le
        have hz_le : ∀ ij, ‖z ij‖ ≤ M_box := fun ij => by
          rw [show z ij = y ij + (z ij - y ij) by ring]
          exact (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans
            (add_le_add ((hbg ij).trans (le_abs_self _)) (hS1 ij))) ((hzy_le ij).trans hrem1)).trans
            (by linarith [hBg_le ij]))
        have hu_pow_le : ∀ k ∈ Finset.range (Du + 1), ‖(u : ℂ) ^ k‖ ≤ u ^ Du := fun k hk => by
          rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos]
          exact pow_le_pow_right₀ hu1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
        have hy_eq : MvPolynomial.eval y (jointEvalU Pmin (u : ℂ)) =
            MvPolynomial.eval (fun ij => x ij + a * v_dir ij) (jointEvalU Pmin (u : ℂ)) := by
          let c_lat : ℕ → ℂ := fun m => 2 * (Real.pi : ℂ) * Complex.I * Complex.exp (-(ω m : ℂ) * (u : ℂ))
          have hy_split : y = fun ij => (x ij + a * v_dir ij) + ∑ m ∈ Finset.range m₀, c_lat m * v_lat m ij := by
            funext ij
            dsimp only [y, S, a, amp₀, v_dir, v_lat, c_lat, lam₀]
            rw [Finset.sum_range_succ]
            have hsum_eq : (∑ m ∈ Finset.range m₀,
                (2 * (Real.pi : ℂ) * Complex.I * res ij.1 m * (-(ω m : ℂ)) ^ ij.2.val) *
                  Complex.exp (-(ω m : ℂ) * (u : ℂ))) =
                ∑ m ∈ Finset.range m₀,
                  (2 * (Real.pi : ℂ) * Complex.I * Complex.exp (-(ω m : ℂ) * (u : ℂ))) *
                    (res ij.1 m * (-(ω m : ℂ)) ^ ij.2.val) :=
              Finset.sum_congr rfl fun m _ => by ring
            rw [hsum_eq]; ring
          rw [hy_split]
          exact h_shift_range m₀ le_rfl u (fun ij => x ij + a * v_dir ij) c_lat
        have h_lip_y : ‖MvPolynomial.eval y (jointEvalU Pmin (u : ℂ))‖ ≤
            (C_L * C_rem) * u ^ Du * Real.exp (-R_cut * u) := by
          have hyz : MvPolynomial.eval y (jointEvalU Pmin (u : ℂ)) =
              ∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k *
                (MvPolynomial.eval y (coeffUJ k Pmin) - MvPolynomial.eval z (coeffUJ k Pmin)) := by
            rw [← sub_zero (MvPolynomial.eval y (jointEvalU Pmin (u : ℂ))), ← hneg]
            dsimp only [Du]
            simp only [jointEvalU_eq_sum_coeffUJ Pmin (u : ℂ), map_sum, MvPolynomial.smul_eq_C_mul,
              map_mul, MvPolynomial.eval_C, ← Finset.sum_sub_distrib, ← mul_sub]
            rfl
          rw [hyz]
          calc ‖∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k * _‖
              ≤ ∑ k ∈ Finset.range (Du + 1), ‖(u : ℂ) ^ k * _‖ := norm_sum_le _ _
            _ ≤ ∑ k ∈ Finset.range (Du + 1), u ^ Du * (C_lip_k k * (C_rem * Real.exp (-R_cut * u))) := by
                refine Finset.sum_le_sum fun k hk => ?_
                rw [norm_mul]
                have hlk := h_lip_k k z y (C_rem * Real.exp (-R_cut * u))
                  (mul_nonneg hC_rem_nn (Real.exp_pos _).le) hz_le hy_le hzy_le
                rw [norm_sub_rev] at hlk
                exact mul_le_mul (hu_pow_le k hk) hlk (norm_nonneg _) (pow_nonneg hu_pos.le Du)
            _ = (C_L * C_rem) * u ^ Du * Real.exp (-R_cut * u) := by
                dsimp only [C_L]; rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
        have h_tay_y :
            ‖MvPolynomial.eval y (jointEvalU Pmin (u : ℂ)) -
                a * ∑ ij : Fin K × Fin (r + 1),
                  MvPolynomial.eval x (MvPolynomial.pderiv ij (jointEvalU Pmin (u : ℂ))) * v_dir ij‖ ≤
              C_T * u ^ Du * ‖a‖ ^ 2 := by
          have hsum_id : MvPolynomial.eval y (jointEvalU Pmin (u : ℂ)) -
                a * ∑ ij : Fin K × Fin (r + 1),
                  MvPolynomial.eval x (MvPolynomial.pderiv ij (jointEvalU Pmin (u : ℂ))) * v_dir ij =
              ∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k *
                (MvPolynomial.eval (fun ij => x ij + a * v_dir ij) (coeffUJ k Pmin) -
                  MvPolynomial.eval x (coeffUJ k Pmin) -
                  a * ∑ ij : Fin K × Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv ij (coeffUJ k Pmin)) * v_dir ij) := by
            rw [hy_eq, ← sub_zero (MvPolynomial.eval (fun ij => x ij + a * v_dir ij) (jointEvalU Pmin (u : ℂ))), ← hpos]
            have hpd_u : ∑ ij : Fin K × Fin (r + 1),
                  MvPolynomial.eval x (MvPolynomial.pderiv ij (jointEvalU Pmin (u : ℂ))) * v_dir ij =
                ∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k *
                  ∑ ij : Fin K × Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv ij (coeffUJ k Pmin)) * v_dir ij := by
              have hexp_ij : ∀ ij : Fin K × Fin (r + 1),
                  MvPolynomial.eval x (MvPolynomial.pderiv ij (jointEvalU Pmin (u : ℂ))) * v_dir ij =
                    ∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k *
                      (MvPolynomial.eval x (MvPolynomial.pderiv ij (coeffUJ k Pmin)) * v_dir ij) := by
                intro ij
                rw [jointEvalU_eq_sum_coeffUJ Pmin (u : ℂ), map_sum, map_sum, Finset.sum_mul]
                refine Finset.sum_congr rfl fun k _ => by
                  rw [(MvPolynomial.pderiv ij).map_smul_of_tower, MvPolynomial.smul_eq_C_mul,
                    map_mul, MvPolynomial.eval_C, mul_assoc]
              simp_rw [hexp_ij]; rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
            rw [hpd_u, Finset.mul_sum]
            dsimp only [Du]
            simp only [jointEvalU_eq_sum_coeffUJ Pmin (u : ℂ), map_sum, MvPolynomial.smul_eq_C_mul,
              map_mul, MvPolynomial.eval_C, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun k _ => by ring
          rw [hsum_id]
          calc ‖∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k * _‖
              ≤ ∑ k ∈ Finset.range (Du + 1), ‖(u : ℂ) ^ k * _‖ := norm_sum_le _ _
            _ ≤ ∑ k ∈ Finset.range (Du + 1), u ^ Du * (C_tay_k k * ‖a‖ ^ 2) := by
                refine Finset.sum_le_sum fun k hk => ?_
                rw [norm_mul]
                exact mul_le_mul (hu_pow_le k hk) (h_tay_k k x v_dir a hx_le hv_le ha_le1)
                  (norm_nonneg _) (pow_nonneg hu_pos.le Du)
            _ = C_T * u ^ Du * ‖a‖ ^ 2 := by dsimp only [C_T]; rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
        have hD_rew : ∑ ij : Fin K × Fin (r + 1),
              MvPolynomial.eval x (MvPolynomial.pderiv ij (jointEvalU Pmin (u : ℂ))) * v_dir ij =
            MvPolynomial.eval x (jointEvalU (D_shared K r ω res m₀ Pmin) (u : ℂ)) := by
          rw [jointEvalU_D_shared ω res m₀ (u : ℂ) Pmin, map_sum]
          refine Finset.sum_congr rfl fun ij _ => ?_
          rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, mul_comm]
        rw [hD_rew] at h_tay_y
        have h_main : ‖a‖ * ‖MvPolynomial.eval x (jointEvalU (D_shared K r ω res m₀ Pmin) (u : ℂ))‖ ≤
            (C_L * C_rem) * u ^ Du * Real.exp (-R_cut * u) + C_T * u ^ Du * ‖a‖ ^ 2 := by
          have htri := norm_sub_le (MvPolynomial.eval y (jointEvalU Pmin (u : ℂ)))
            (MvPolynomial.eval y (jointEvalU Pmin (u : ℂ)) -
              a * MvPolynomial.eval x (jointEvalU (D_shared K r ω res m₀ Pmin) (u : ℂ)))
          have hsimp : MvPolynomial.eval y (jointEvalU Pmin (u : ℂ)) -
              (MvPolynomial.eval y (jointEvalU Pmin (u : ℂ)) -
                a * MvPolynomial.eval x (jointEvalU (D_shared K r ω res m₀ Pmin) (u : ℂ))) =
              a * MvPolynomial.eval x (jointEvalU (D_shared K r ω res m₀ Pmin) (u : ℂ)) := by ring
          rw [hsimp, norm_mul] at htri
          exact htri.trans (add_le_add h_lip_y h_tay_y)
        have h1_bd : u ^ Du * Real.exp (-R_cut * u) ≤ Real.exp (-lam₀ * u) * Real.exp (-(δ_gap / 2) * u) := by
          have hle : lam₀ + δ_gap ≤ R_cut := by have := min_le_right lam₀ (R_cut - lam₀); linarith
          have hexp_cut : Real.exp (-R_cut * u) ≤ Real.exp (-(lam₀ + δ_gap) * u) :=
            Real.exp_le_exp.mpr (by nlinarith [hu_pos.le])
          have hexp_eq : Real.exp (-(lam₀ + δ_gap) * u) =
              Real.exp (-lam₀ * u) * (Real.exp (-(δ_gap / 2) * u) * Real.exp (-(δ_gap / 2) * u)) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          calc u ^ Du * Real.exp (-R_cut * u)
              ≤ u ^ Du * Real.exp (-(lam₀ + δ_gap) * u) := mul_le_mul_of_nonneg_left hexp_cut (pow_nonneg hu_pos.le _)
            _ = Real.exp (-lam₀ * u) * ((u ^ Du * Real.exp (-(δ_gap / 2) * u)) * Real.exp (-(δ_gap / 2) * u)) := by
                rw [hexp_eq]; ring
            _ ≤ Real.exp (-lam₀ * u) * (1 * Real.exp (-(δ_gap / 2) * u)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpoly_u (Real.exp_pos _).le) (Real.exp_pos _).le
            _ = Real.exp (-lam₀ * u) * Real.exp (-(δ_gap / 2) * u) := by rw [one_mul]
        have h2_bd : u ^ Du * Real.exp (-lam₀ * u) ^ 2 ≤ Real.exp (-lam₀ * u) * Real.exp (-(δ_gap / 2) * u) := by
          have hle : δ_gap ≤ lam₀ := min_le_left _ _
          have hexp_om : Real.exp (-lam₀ * u) ≤ Real.exp (-δ_gap * u) :=
            Real.exp_le_exp.mpr (by nlinarith [hu_pos.le])
          have hexp_eq : Real.exp (-δ_gap * u) =
              Real.exp (-(δ_gap / 2) * u) * Real.exp (-(δ_gap / 2) * u) := by
            rw [← Real.exp_add]; congr 1; ring
          calc u ^ Du * Real.exp (-lam₀ * u) ^ 2
              = Real.exp (-lam₀ * u) * (u ^ Du * Real.exp (-lam₀ * u)) := by ring
            _ ≤ Real.exp (-lam₀ * u) * (u ^ Du * Real.exp (-δ_gap * u)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp_om (pow_nonneg hu_pos.le _)) (Real.exp_pos _).le
            _ = Real.exp (-lam₀ * u) * ((u ^ Du * Real.exp (-(δ_gap / 2) * u)) * Real.exp (-(δ_gap / 2) * u)) := by
                rw [hexp_eq]; ring
            _ ≤ Real.exp (-lam₀ * u) * (1 * Real.exp (-(δ_gap / 2) * u)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpoly_u (Real.exp_pos _).le) (Real.exp_pos _).le
            _ = Real.exp (-lam₀ * u) * Real.exp (-(δ_gap / 2) * u) := by rw [one_mul]
        rw [ha_norm, mul_pow] at h_main
        have hamp_pos : 0 < ‖amp₀‖ := norm_pos_iff.mpr hamp₀_ne
        have h_rhs := exp_comb_rhs_le hC_L_nn hC_rem_nn hC_T_nn hamp_pos h1_bd h2_bd
        exact le_of_mul_le_mul_left (h_main.trans h_rhs) (mul_pos hamp_pos (Real.exp_pos _))
      have hD_formal : jointFormalEvalPoly (fun i => formalSeries (φ i)) (D_shared K r ω res m₀ Pmin) = 0 :=
        hflat_to_formal (half_pos hδ_pos) (D_shared K r ω res m₀ Pmin) ⟨_, h_bridge⟩
      by_contra hD_ne
      exact hPmin_min (D_shared K r ω res m₀ Pmin) hD_ne
        (degree_D_shared_lt ω res m₀ Pmin hPmin_pos_deg) hD_formal
  -- Apply `h.hRank` to kill every partial derivative of `Pmin`, contradicting `0 < Pmin.totalDegree`!
  have hall_pd : ∀ ij : Fin K × Fin (r + 1), MvPolynomial.pderiv ij Pmin = 0 :=
    h.hRank Pmin hD_peel
  have hPmin_zero_deg : Pmin.totalDegree = 0 := by
    have hcoeff0 : ∀ k : ℕ, (coeffUJ k Pmin).totalDegree = 0 := fun k => by
      have hall_k : ∀ ij : Fin K × Fin (r + 1), MvPolynomial.pderiv ij (coeffUJ k Pmin) = 0 := fun ij => by
        rw [← coeffUJ_pderiv, hall_pd ij]
        ext α; simp [coeffUJ_coeff]
      have hC := all_partials_zero (coeffUJ k Pmin) hall_k
      rw [hC]; exact MvPolynomial.totalDegree_C _
    rw [MvPolynomial.totalDegree_eq]
    refine Nat.eq_zero_of_le_zero (Finset.sup_le fun α hα => ?_)
    have hp_ne : Pmin.coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (Pmin.coeff α).coeff k ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hp_ne (by ext k; simpa using hall k)
    have hα_k : α ∈ (coeffUJ k Pmin).support := by
      rw [MvPolynomial.mem_support_iff, coeffUJ_coeff]; exact hk
    have hle : (Finsupp.toMultiset α).card ≤ (coeffUJ k Pmin).totalDegree := by
      rw [MvPolynomial.totalDegree_eq]
      exact Finset.le_sup (f := fun m => (Finsupp.toMultiset m).card) hα_k
    have h0k := hcoeff0 k
    omega
  omega

/-- **Shared-Lattice Asymptotic-Transfer Joint Differential Independence (`ℂ[u]`)**. -/
theorem shared_lattice_joint_no_nonautonomous_ade_of_asymp {K : ℕ}
    {φ : Fin K → ℂ → ℂ} {ω : ℕ → ℝ} {res : Fin K → ℕ → ℂ}
    (h : SharedLatticeSimplePoleFamily K φ ω res)
    {f : Fin K → ℝ → ℂ}
    (hf_asymp : ∀ (i : Fin K) (j : ℕ), HasAsympExp (iteratedDeriv j (f i)) (d_u^[j] (formalSeries (φ i))))
    {r : ℕ} (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) => iteratedDeriv ij.2.val (f ij.1) u)
        (jointEvalU P (u : ℂ)) = 0) : P = 0 := by
  let N := maxUDegJ P
  let Q := revMvPolyJ N P
  have hNP : ∀ α, (P.coeff α).natDegree ≤ N := natDegree_le_maxUDegJ P
  have hexp : HasAsympExp
      (fun u : ℝ => MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) => iteratedDeriv ij.2.val (f ij.1) u)
        (jointEvalU Q (u : ℂ)⁻¹))
      (jointFormalEvalW (fun i => formalSeries (φ i)) Q) :=
    hasAsympExp_jointEvalW (fun ij => hf_asymp ij.1 ij.2.val) Q
  have hflat : ∀ M : ℕ, ∃ C : ℝ, ∀ᶠ u : ℝ in Filter.atTop,
      ‖MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) => iteratedDeriv ij.2.val (f ij.1) u)
        (jointEvalU Q (u : ℂ)⁻¹)‖ ≤ C / u ^ M := by
    intro M
    refine ⟨0, ?_⟩
    filter_upwards [hP, eventually_gt_atTop (0 : ℝ)] with u hu hu_pos
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    rw [show Q = revMvPolyJ N P from rfl, jointEvalU_revMvPolyJ P hNP hu_ne,
      MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, hu, mul_zero, norm_zero, zero_div]
  have hW0 : jointFormalEvalW (fun i => formalSeries (φ i)) Q = 0 := hexp.eq_zero_of_flat hflat
  exact shared_lattice_joint_stokes_no_ade h P
    ((jointFormalEvalW_eq_zero_iff_poly (fun i => formalSeries (φ i)) P hNP).mp hW0)

end SharedLatticeStokes

/-! #### 2D. Simple-Pole Borel Transforms & Rank-3 Residue Independence for `(MacMahon, Parts ≡ 1 mod 5, Parts ≡ 2 mod 5)` -/

/-- Quasipolynomial weight `1_{n ≡ 2 (5)}` (`M = 5, D = 0`). -/
@[expose] def partsMod5TwoQP : Quasipoly where
  M := 5
  hM := by norm_num
  «D» := 0
  c _ n := if n % 5 = 2 then 1 else 0
  periodic _ n := by simp

lemma partsMod5TwoQP_eval_nat (n : ℕ) :
    partsMod5TwoQP.eval (n : ℤ) = if n % 5 = 2 then 1 else 0 := by
  rw [partsMod5TwoQP.eval_nat n]
  unfold partsMod5TwoQP
  rw [Fin.sum_univ_one]
  simp

/-- Quasipolynomial weight `P(n) = n` (`M = 1, D = 1`) whose Lambert series is `sigmaSeries 2` and
whose Euler product is MacMahon's plane-partition generating function `macmahonSeries`. -/
@[expose] def macMahonQP : Quasipoly where
  M := 1
  hM := by norm_num
  «D» := 1
  c d _ := if d.1 = 1 then 1 else 0
  periodic _ _ := rfl

lemma macMahonQP_eval_int (n : ℤ) : macMahonQP.eval n = (n : ℂ) := by
  unfold Quasipoly.eval macMahonQP
  simp [Fin.sum_univ_two]

lemma lambertSeries_macMahonQP_eq :
    lambertSeries (fun n => macMahonQP.eval (n : ℤ)) = sigmaSeries 2 := by
  ext n
  cases n with
  | zero => simp [coeff_lambertSeries, sigmaSeries]
  | succ m =>
    rw [coeff_lambertSeries, sigmaSeries, PowerSeries.coeff_mk]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [macMahonQP_eval_int, Int.cast_natCast, sq]

lemma eulerProduct_macMahonQP_eq :
    eulerProduct (fun n => macMahonQP.eval (n : ℤ)) = macmahonSeries := by
  refine PowerSeries.ext fun n => ?_
  have hode1 : PowerSeries.X * PowerSeries.derivative (eulerProduct (fun n => macMahonQP.eval (n : ℤ))) =
      sigmaSeries 2 * eulerProduct (fun n => macMahonQP.eval (n : ℤ)) := by
    rw [← lambertSeries_macMahonQP_eq]; exact eulerProduct_ode _
  have hode2 : PowerSeries.X * PowerSeries.derivative macmahonSeries = sigmaSeries 2 * macmahonSeries :=
    macmahonSeries_ode
  have hc1 : PowerSeries.constantCoeff (eulerProduct (fun n => macMahonQP.eval (n : ℤ))) = 1 :=
    eulerProduct_constantCoeff _
  have hc2 : PowerSeries.constantCoeff macmahonSeries = 1 := macmahonSeries_constantCoeff
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero =>
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hc1.trans hc2.symm
    | succ m =>
      have h1 := congrArg (PowerSeries.coeff (m + 1)) hode1
      have h2 := congrArg (PowerSeries.coeff (m + 1)) hode2
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at h1 h2
      have hEq : PowerSeries.coeff (m + 1) (eulerProduct (fun n => macMahonQP.eval (n : ℤ))) * ((m : ℂ) + 1) =
          PowerSeries.coeff (m + 1) macmahonSeries * ((m : ℂ) + 1) := by
        rw [h1, h2]
        refine Finset.sum_congr rfl fun p hp => ?_
        have hsum_eq : p.1 + p.2 = m + 1 := by simpa using hp
        by_cases hp1 : p.1 = 0
        · simp [hp1, sigmaSeries]
        · have hp2 : p.2 < m + 1 := by omega
          rw [ih p.2 hp2]
      exact mul_right_cancel₀ (by exact_mod_cast Nat.succ_ne_zero m) hEq

/-- Shared Borel pole lattice `ω5 m = 4π² (m + 1) / 5`. -/
private def ω5 (m : ℕ) : ℝ := 4 * Real.pi ^ 2 * ((m + 1 : ℕ) : ℝ) / 5

private lemma ω5_pos (m : ℕ) : 0 < ω5 m := by unfold ω5; positivity

private lemma ω5_strictMono : StrictMono ω5 := by
  intro a b hab
  unfold ω5
  have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
  gcongr

private lemma ωBase_partsMod5One (m : ℕ) : ωBase partsMod5OneQP m = ω5 m := by
  unfold ωBase ω5 partsMod5OneQP; norm_num

private lemma ωBase_partsMod5Two (m : ℕ) : ωBase partsMod5TwoQP m = ω5 m := by
  unfold ωBase ω5 partsMod5TwoQP; norm_num

private lemma ωBase_macMahon (k : ℕ) : ωBase macMahonQP k = ω5 (5 * k + 4) := by
  unfold ωBase ω5 macMahonQP
  push_cast; ring

private lemma ωBase_pos' (P : Quasipoly) (m : ℕ) : 0 < ωBase P m := by
  unfold ωBase
  have : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  positivity

private lemma div_sigma_ext {n₁ n₂ : ℕ} {d₁ : Nat.divisors (n₁ + 1)} {d₂ : Nat.divisors (n₂ + 1)}
    (hn : n₁ = n₂) (hd : d₁.1 = d₂.1) : (⟨n₁, d₁⟩ : Σ k, Nat.divisors (k + 1)) = ⟨n₂, d₂⟩ := by
  subst hn
  congr 1
  exact Subtype.ext hd

private def divPairEquiv : ℕ × ℕ ≃ Σ n : ℕ, Nat.divisors (n + 1) where
  toFun p := ⟨(p.1 + 1) * (p.2 + 1) - 1,
    ⟨p.2 + 1, Nat.mem_divisors.mpr ⟨by
      have h1 : 1 ≤ (p.1 + 1) * (p.2 + 1) := Nat.succ_le_of_lt (by positivity)
      rw [Nat.sub_add_cancel h1]
      exact dvd_mul_left _ _, by omega⟩⟩⟩
  invFun s := ((s.1 + 1) / s.2.1 - 1, s.2.1 - 1)
  left_inv p := by
    ext <;> dsimp only
    · have h1 : 1 ≤ (p.1 + 1) * (p.2 + 1) := Nat.succ_le_of_lt (by positivity)
      rw [Nat.sub_add_cancel h1, Nat.mul_div_cancel _ (Nat.succ_pos p.2)]
      omega
    · omega
  right_inv s := by
    rcases s with ⟨n, ⟨k, hk⟩⟩
    have hk_pos : 0 < k := Nat.pos_of_mem_divisors hk
    have hk_dvd : k ∣ n + 1 := Nat.dvd_of_mem_divisors hk
    have hq_pos : 0 < (n + 1) / k := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos n) hk_dvd) hk_pos
    have hmul : ((n + 1) / k - 1 + 1) * (k - 1 + 1) = n + 1 := by
      rw [Nat.sub_add_cancel hq_pos, Nat.sub_add_cancel hk_pos, Nat.div_mul_cancel hk_dvd]
    exact div_sigma_ext (by dsimp only; rw [hmul]; omega) (by dsimp only; exact Nat.sub_add_cancel hk_pos)

private lemma tsum_divisor_fubini {F : ℕ → ℕ → ℂ}
    (hF : Summable (fun p : ℕ × ℕ => ‖F (p.1 + 1) (p.2 + 1)‖)) :
    Summable (fun m : ℕ => ∑ k ∈ Nat.divisors (m + 1), F ((m + 1) / k) k) ∧
    (∑' m : ℕ, ∑ k ∈ Nat.divisors (m + 1), F ((m + 1) / k) k) =
      ∑' n : ℕ, ∑' k : ℕ, F (n + 1) (k + 1) := by
  have hF_sum : Summable (fun p : ℕ × ℕ => F (p.1 + 1) (p.2 + 1)) := hF.of_norm
  let G : (Σ m : ℕ, Nat.divisors (m + 1)) → ℂ := fun s => F ((s.1 + 1) / s.2.1) s.2.1
  have hG_comp : G ∘ divPairEquiv = fun p : ℕ × ℕ => F (p.1 + 1) (p.2 + 1) := by
    funext p
    change F (((p.1 + 1) * (p.2 + 1) - 1 + 1) / (p.2 + 1)) (p.2 + 1) = F (p.1 + 1) (p.2 + 1)
    have h1 : 1 ≤ (p.1 + 1) * (p.2 + 1) := Nat.succ_le_of_lt (by positivity)
    rw [Nat.sub_add_cancel h1, Nat.mul_div_cancel _ (Nat.succ_pos p.2)]
  have hG_sum : Summable G := (divPairEquiv.summable_iff).mp (by simpa only [hG_comp] using hF_sum)
  have hG_norm : Summable (fun s => ‖G s‖) :=
    (divPairEquiv.summable_iff).mp (hF.congr fun p => by
      change ‖F (p.1 + 1) (p.2 + 1)‖ = ‖G (divPairEquiv p)‖
      rw [← congrFun hG_comp p]; rfl)
  have h_fin_eq : ∀ m : ℕ, (∑' k : Nat.divisors (m + 1), G ⟨m, k⟩) =
      ∑ k ∈ Nat.divisors (m + 1), F ((m + 1) / k) k := fun m => by
    rw [tsum_fintype]
    exact Finset.sum_attach (Nat.divisors (m + 1)) (fun k => F ((m + 1) / k) k)
  have h_sigma_sum : Summable (fun m : ℕ => ∑' k : Nat.divisors (m + 1), G ⟨m, k⟩) := by
    have h_norm_m : Summable (fun m : ℕ => ∑' k : Nat.divisors (m + 1), ‖G ⟨m, k⟩‖) :=
      ((summable_sigma_of_nonneg (fun _ => norm_nonneg _)).mp hG_norm).2
    refine h_norm_m.of_norm_bounded fun m => ?_
    rw [tsum_fintype, tsum_fintype]
    exact norm_sum_le _ _
  refine ⟨h_sigma_sum.congr h_fin_eq, ?_⟩
  calc ∑' m : ℕ, ∑ k ∈ Nat.divisors (m + 1), F ((m + 1) / k) k
      = ∑' m : ℕ, ∑' k : Nat.divisors (m + 1), G ⟨m, k⟩ := tsum_congr fun m => (h_fin_eq m).symm
    _ = ∑' s : (Σ m : ℕ, Nat.divisors (m + 1)), G s := (hG_sum.tsum_sigma' (fun _ => Summable.of_finite)).symm
    _ = ∑' p : ℕ × ℕ, G (divPairEquiv p) := (divPairEquiv.tsum_eq G).symm
    _ = ∑' p : ℕ × ℕ, F (p.1 + 1) (p.2 + 1) := tsum_congr fun p => congrFun hG_comp p
    _ = ∑' n : ℕ, ∑' k : ℕ, F (n + 1) (k + 1) := hF_sum.tsum_prod' (fun n => hF_sum.prod_factor n)

private lemma summable_one_div_nat_pow_succ {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ p)⁻¹) := by
  have h1 : Summable (fun n : ℕ => ((n : ℝ) ^ p)⁻¹) := by
    simpa [one_div] using Real.summable_one_div_nat_pow.mpr (by omega : 1 < p)
  exact (summable_nat_add_iff 1).mpr h1

/-- Summability of `σ_{a+1}(m+1) / (m+1)^{a+3}` (`= ζ(2) ζ(a+3) < ∞`). -/
private lemma summable_sigmaNat_div_pow_two_more (a : ℕ) :
    Summable (fun m : ℕ => (sigmaNat (a + 1) (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ (a + 3)) := by
  let F : ℕ → ℕ → ℂ := fun q k => (((q : ℝ) ^ 2)⁻¹ * ((k : ℝ) ^ (a + 3))⁻¹ : ℂ)
  have hF_norm : Summable (fun p : ℕ × ℕ => ‖F (p.1 + 1) (p.2 + 1)‖) := by
    have hprod := (summable_one_div_nat_pow_succ (p := 2) le_rfl).mul_of_nonneg
      (summable_one_div_nat_pow_succ (p := a + 3) (by omega))
      (fun _ => by positivity) (fun _ => by positivity)
    refine hprod.congr fun p => ?_
    dsimp only [F]
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  have hsumC := (tsum_divisor_fubini hF_norm).1
  have hsumR : Summable (fun m : ℕ => (∑ k ∈ Nat.divisors (m + 1), F ((m + 1) / k) k).re) :=
    Complex.reCLM.summable hsumC
  refine hsumR.congr fun m => ?_
  have hre : (∑ k ∈ Nat.divisors (m + 1), F ((m + 1) / k) k).re =
      ∑ k ∈ Nat.divisors (m + 1), ((((m + 1) / k : ℕ) : ℝ) ^ 2)⁻¹ * ((k : ℝ) ^ (a + 3))⁻¹ := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only [F]; norm_cast
  rw [hre]
  have hm0 : m + 1 ≠ 0 := Nat.succ_ne_zero m
  have hsig : (sigmaNat (a + 1) (m + 1) : ℝ) =
      ∑ k ∈ Nat.divisors (m + 1), (((m + 1) / k : ℕ) : ℝ) ^ (a + 1) := by
    simp only [sigmaNat, hm0, ↓reduceIte, Nat.cast_sum, Nat.cast_pow]
    exact (Nat.sum_div_divisors (m + 1) (fun x : ℕ => (x : ℝ) ^ (a + 1))).symm
  rw [hsig, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_dvd : k ∣ m + 1 := Nat.dvd_of_mem_divisors hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hk
  have hm_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hmul : (((m + 1) / k : ℕ) : ℝ) * (k : ℝ) = ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel hk_dvd
  have hq_pos : (0 : ℝ) < (((m + 1) / k : ℕ) : ℝ) := by
    have : 0 < (m + 1) / k := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos m) hk_dvd) (Nat.pos_of_mem_divisors hk)
    exact_mod_cast this
  have hpow : ((m + 1 : ℕ) : ℝ) ^ (a + 3) =
      (((m + 1) / k : ℕ) : ℝ) ^ (a + 3) * (k : ℝ) ^ (a + 3) := by
    rw [← mul_pow, hmul]
  rw [hpow, show a + 3 = (a + 1) + 2 by omega, pow_add]
  field_simp [hq_pos.ne', hk_pos.ne']
  ring

/-- Simple-pole Borel kernel `ΦSimple0 P` for degree-0 quasipolynomials (`P.D = 0`):
`ΦSimple0 P ξ = (1/2) * borelPref 0 * ∑' m, P.borelAmp 0 (m + 1) * (2 ξ² / (ω_m (ξ² - ω_m²)))`. -/
private def ΦSimple0 (P : Quasipoly) (ξ : ℂ) : ℂ :=
  (1 / 2 : ℂ) * borelPref 0 *
    ∑' m : ℕ, P.borelAmp 0 (m + 1) *
      (2 * ξ ^ 2 / ((ωBase P m : ℂ) * (ξ ^ 2 - (ωBase P m : ℂ) ^ 2)))

/-- Simple-pole Borel kernel `ΦSimple1 P` for pure degree-1 quasipolynomials (`P.D = 1, P.c 0 = 0`):
`ΦSimple1 P ξ = (-1/6) * borelPref 1 * ∑' m, P.borelAmp 1 (m + 1) * (2 ξ³ / (ω_m² (ξ² - ω_m²)))`. -/
private def ΦSimple1 (P : Quasipoly) (hD : P.D = 1) (ξ : ℂ) : ℂ :=
  (-(1 / 6) : ℂ) * borelPref 1 *
    ∑' m : ℕ, P.borelAmp ⟨1, by omega⟩ (m + 1) *
      (2 * ξ ^ 3 / ((ωBase P m : ℂ) ^ 2 * (ξ ^ 2 - (ωBase P m : ℂ) ^ 2)))

private lemma ker0_decomp {ω z : ℂ} (hω : ω ≠ 0) (hz1 : z ≠ ω) (hz2 : z ≠ -ω) :
    2 * z ^ 2 / (ω * (z ^ 2 - ω ^ 2)) = (z - ω)⁻¹ - (z + ω)⁻¹ + 2 / ω := by
  have h1 : z - ω ≠ 0 := sub_ne_zero.mpr hz1
  have h2 : z + ω ≠ 0 := by intro h0; apply hz2; linear_combination h0
  have hsq : z ^ 2 - ω ^ 2 = (z - ω) * (z + ω) := by ring
  rw [hsq]
  field_simp [hω, h1, h2]
  ring

private lemma ker1_decomp {ω z : ℂ} (hω : ω ≠ 0) (hz1 : z ≠ ω) (hz2 : z ≠ -ω) :
    2 * z ^ 3 / (ω ^ 2 * (z ^ 2 - ω ^ 2)) = (z - ω)⁻¹ + (z + ω)⁻¹ + 2 * z / ω ^ 2 := by
  have h1 : z - ω ≠ 0 := sub_ne_zero.mpr hz1
  have h2 : z + ω ≠ 0 := by intro h0; apply hz2; linear_combination h0
  have hsq : z ^ 2 - ω ^ 2 = (z - ω) * (z + ω) := by ring
  rw [hsq]
  field_simp [hω, h1, h2]
  ring

private lemma hasDerivAt_ker0 {ω z : ℂ} (hω : ω ≠ 0) (hz1 : z ≠ ω) (hz2 : z ≠ -ω) :
    HasDerivAt (fun w : ℂ => 2 * w ^ 2 / (ω * (w ^ 2 - ω ^ 2)))
      (-4 * z * ω / (z ^ 2 - ω ^ 2) ^ 2) z := by
  have h1 : z - ω ≠ 0 := sub_ne_zero.mpr hz1
  have h2 : z + ω ≠ 0 := by intro h0; apply hz2; linear_combination h0
  have hsq : z ^ 2 - ω ^ 2 ≠ 0 := by rw [show z ^ 2 - ω ^ 2 = (z - ω) * (z + ω) by ring]; exact mul_ne_zero h1 h2
  have hnum : HasDerivAt (fun w : ℂ => 2 * w ^ 2) (4 * z) z := by
    have := ((hasDerivAt_pow 2 z).const_mul (2 : ℂ))
    simpa [pow_one, mul_assoc] using (show HasDerivAt (fun w : ℂ => 2 * w ^ 2) (2 * (2 * z ^ 1)) z from this).congr_deriv (by ring)
  have hden : HasDerivAt (fun w : ℂ => ω * (w ^ 2 - ω ^ 2)) (ω * (2 * z)) z := by
    have := ((hasDerivAt_pow 2 z).sub_const (ω ^ 2)).const_mul ω
    simpa [pow_one] using this
  have hdiv := hnum.div hden (mul_ne_zero hω hsq)
  refine hdiv.congr_deriv ?_
  field_simp [hω, hsq]
  ring

private lemma hasDerivAt_ker0_deriv {ω z : ℂ} (hz1 : z ≠ ω) (hz2 : z ≠ -ω) :
    HasDerivAt (fun w : ℂ => -4 * w * ω / (w ^ 2 - ω ^ 2) ^ 2)
      (2 * (((z - ω) ^ 3)⁻¹ - ((z + ω) ^ 3)⁻¹)) z := by
  have h1 : z - ω ≠ 0 := sub_ne_zero.mpr hz1
  have h2 : z + ω ≠ 0 := by intro h0; apply hz2; linear_combination h0
  have hsq : z ^ 2 - ω ^ 2 ≠ 0 := by rw [show z ^ 2 - ω ^ 2 = (z - ω) * (z + ω) by ring]; exact mul_ne_zero h1 h2
  have hnum : HasDerivAt (fun w : ℂ => -4 * w * ω) (-4 * ω) z := by
    have := ((hasDerivAt_id z).const_mul (-4 : ℂ)).mul_const ω
    simpa using this
  have hden : HasDerivAt (fun w : ℂ => (w ^ 2 - ω ^ 2) ^ 2) (2 * (z ^ 2 - ω ^ 2) * (2 * z)) z := by
    have h0 : HasDerivAt (fun w : ℂ => w ^ 2 - ω ^ 2) (2 * z) z := by
      simpa [pow_one] using (hasDerivAt_pow 2 z).sub_const (ω ^ 2)
    simpa [pow_one] using h0.fun_pow 2
  have hdiv := hnum.div hden (pow_ne_zero 2 hsq)
  refine hdiv.congr_deriv ?_
  have hfac : z ^ 2 - ω ^ 2 = (z - ω) * (z + ω) := by ring
  rw [hfac]
  field_simp [h1, h2]
  ring

private lemma hasDerivAt_ker1 {ω z : ℂ} (hω : ω ≠ 0) (hz1 : z ≠ ω) (hz2 : z ≠ -ω) :
    HasDerivAt (fun w : ℂ => 2 * w ^ 3 / (ω ^ 2 * (w ^ 2 - ω ^ 2)))
      (2 * z ^ 2 * (z ^ 2 - 3 * ω ^ 2) / (ω ^ 2 * (z ^ 2 - ω ^ 2) ^ 2)) z := by
  have h1 : z - ω ≠ 0 := sub_ne_zero.mpr hz1
  have h2 : z + ω ≠ 0 := by intro h0; apply hz2; linear_combination h0
  have hsq : z ^ 2 - ω ^ 2 ≠ 0 := by rw [show z ^ 2 - ω ^ 2 = (z - ω) * (z + ω) by ring]; exact mul_ne_zero h1 h2
  have hnum : HasDerivAt (fun w : ℂ => 2 * w ^ 3) (6 * z ^ 2) z := by
    have := ((hasDerivAt_pow 3 z).const_mul (2 : ℂ))
    exact this.congr_deriv (by ring)
  have hden : HasDerivAt (fun w : ℂ => ω ^ 2 * (w ^ 2 - ω ^ 2)) (ω ^ 2 * (2 * z)) z := by
    have := ((hasDerivAt_pow 2 z).sub_const (ω ^ 2)).const_mul (ω ^ 2)
    simpa [pow_one] using this
  have hdiv := hnum.div hden (mul_ne_zero (pow_ne_zero 2 hω) hsq)
  refine hdiv.congr_deriv ?_
  field_simp [hω, hsq]
  ring

private lemma hasDerivAt_ker1_deriv1 {ω z : ℂ} (hω : ω ≠ 0) (hz1 : z ≠ ω) (hz2 : z ≠ -ω) :
    HasDerivAt (fun w : ℂ => 2 * w ^ 2 * (w ^ 2 - 3 * ω ^ 2) / (ω ^ 2 * (w ^ 2 - ω ^ 2) ^ 2))
      (4 * z * (z ^ 2 + 3 * ω ^ 2) / (z ^ 2 - ω ^ 2) ^ 3) z := by
  have h1 : z - ω ≠ 0 := sub_ne_zero.mpr hz1
  have h2 : z + ω ≠ 0 := by intro h0; apply hz2; linear_combination h0
  have hsq : z ^ 2 - ω ^ 2 ≠ 0 := by rw [show z ^ 2 - ω ^ 2 = (z - ω) * (z + ω) by ring]; exact mul_ne_zero h1 h2
  have hnum : HasDerivAt (fun w : ℂ => 2 * w ^ 2 * (w ^ 2 - 3 * ω ^ 2))
      (4 * z * (z ^ 2 - 3 * ω ^ 2) + 2 * z ^ 2 * (2 * z)) z := by
    have ha : HasDerivAt (fun w : ℂ => 2 * w ^ 2) (4 * z) z :=
      ((hasDerivAt_pow 2 z).const_mul (2 : ℂ)).congr_deriv (by ring)
    have hb : HasDerivAt (fun w : ℂ => w ^ 2 - 3 * ω ^ 2) (2 * z) z := by
      simpa [pow_one] using (hasDerivAt_pow 2 z).sub_const (3 * ω ^ 2)
    exact ha.mul hb
  have hden : HasDerivAt (fun w : ℂ => ω ^ 2 * (w ^ 2 - ω ^ 2) ^ 2)
      (ω ^ 2 * (2 * (z ^ 2 - ω ^ 2) * (2 * z))) z := by
    have h0 : HasDerivAt (fun w : ℂ => w ^ 2 - ω ^ 2) (2 * z) z := by
      simpa [pow_one] using (hasDerivAt_pow 2 z).sub_const (ω ^ 2)
    simpa [pow_one] using (h0.fun_pow 2).const_mul (ω ^ 2)
  have hdiv := hnum.div hden (mul_ne_zero (pow_ne_zero 2 hω) (pow_ne_zero 2 hsq))
  refine hdiv.congr_deriv ?_
  field_simp [hω, hsq]
  ring

private lemma hasDerivAt_ker1_deriv2 {ω z : ℂ} (hz1 : z ≠ ω) (hz2 : z ≠ -ω) :
    HasDerivAt (fun w : ℂ => 4 * w * (w ^ 2 + 3 * ω ^ 2) / (w ^ 2 - ω ^ 2) ^ 3)
      (-6 * (((z - ω) ^ 4)⁻¹ + ((z + ω) ^ 4)⁻¹)) z := by
  have h1 : z - ω ≠ 0 := sub_ne_zero.mpr hz1
  have h2 : z + ω ≠ 0 := by intro h0; apply hz2; linear_combination h0
  have hsq : z ^ 2 - ω ^ 2 ≠ 0 := by rw [show z ^ 2 - ω ^ 2 = (z - ω) * (z + ω) by ring]; exact mul_ne_zero h1 h2
  have hnum : HasDerivAt (fun w : ℂ => 4 * w * (w ^ 2 + 3 * ω ^ 2))
      (4 * (z ^ 2 + 3 * ω ^ 2) + 4 * z * (2 * z)) z := by
    have ha : HasDerivAt (fun w : ℂ => 4 * w) 4 z := by simpa using (hasDerivAt_id z).const_mul (4 : ℂ)
    have hb : HasDerivAt (fun w : ℂ => w ^ 2 + 3 * ω ^ 2) (2 * z) z := by
      simpa [pow_one] using (hasDerivAt_pow 2 z).add_const (3 * ω ^ 2)
    exact ha.mul hb
  have hden : HasDerivAt (fun w : ℂ => (w ^ 2 - ω ^ 2) ^ 3) (3 * (z ^ 2 - ω ^ 2) ^ 2 * (2 * z)) z := by
    have h0 : HasDerivAt (fun w : ℂ => w ^ 2 - ω ^ 2) (2 * z) z := by
      simpa [pow_one] using (hasDerivAt_pow 2 z).sub_const (ω ^ 2)
    exact h0.fun_pow 3
  have hdiv := hnum.div hden (pow_ne_zero 3 hsq)
  refine hdiv.congr_deriv ?_
  have hfac : z ^ 2 - ω ^ 2 = (z - ω) * (z + ω) := by ring
  rw [hfac]
  field_simp [h1, h2]
  ring

/-- Distance lower bound on any ball `Metric.ball w r` for large `m`: `‖z ± ωBase P m‖ ≥ ωBase P m / 2`. -/
private lemma ωBase_tail_ge_half (P : Quasipoly) (w : ℂ) (r : ℝ) :
    ∃ N : ℕ, ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball w r →
      ωBase P (k + N) / 2 ≤ ‖z - (ωBase P (k + N) : ℂ)‖ ∧
      ωBase P (k + N) / 2 ≤ ‖z + (ωBase P (k + N) : ℂ)‖ := by
  have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  have hc : 0 < 4 * Real.pi ^ 2 / (P.M : ℝ) := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (‖w‖ + |r|) / (4 * Real.pi ^ 2 / (P.M : ℝ)))
  refine ⟨N, fun k z hz => ?_⟩
  have hz_le : ‖z‖ ≤ ‖w‖ + |r| := by
    have hdist : ‖z - w‖ < r := by simpa [dist_eq_norm] using Metric.mem_ball.mp hz
    calc ‖z‖ = ‖(z - w) + w‖ := by ring_nf
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ |r| + ‖w‖ := add_le_add (hdist.le.trans (le_abs_self r)) le_rfl
      _ = ‖w‖ + |r| := add_comm _ _
  have hω_ge : 2 * (‖w‖ + |r|) ≤ ωBase P (k + N) := by
    unfold ωBase
    have h1 : (N : ℝ) ≤ ((k + N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : N ≤ k + N + 1)
    have h2 : 2 * (‖w‖ + |r|) < (N : ℝ) * (4 * Real.pi ^ 2 / (P.M : ℝ)) := (div_lt_iff₀ hc).mp hN
    calc 2 * (‖w‖ + |r|) ≤ (N : ℝ) * (4 * Real.pi ^ 2 / (P.M : ℝ)) := h2.le
      _ ≤ ((k + N + 1 : ℕ) : ℝ) * (4 * Real.pi ^ 2 / (P.M : ℝ)) := mul_le_mul_of_nonneg_right h1 hc.le
      _ = 4 * Real.pi ^ 2 * ((k + N + 1 : ℕ) : ℝ) / (P.M : ℝ) := by ring
  have hω_pos : 0 < ωBase P (k + N) := by unfold ωBase; positivity
  constructor
  · have htri := norm_sub_norm_le (ωBase P (k + N) : ℂ) z
    rw [norm_sub_rev, Complex.norm_real, Real.norm_of_nonneg hω_pos.le] at htri
    linarith
  · have htri := norm_sub_norm_le (ωBase P (k + N) : ℂ) (-z)
    rw [sub_neg_eq_add, add_comm (ωBase P (k + N) : ℂ) z, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg hω_pos.le] at htri
    linarith

/-- On `t • e^{±iθ}` (`t ≥ 0`, `0 < θ < π/2`), `‖z² - ω²‖ ≥ ω² * sin(2θ)`? Better:
`‖z - ω‖ ≥ ω * sin θ` and `‖z + ω‖ ≥ ω` since `z.re ≥ 0` and `ω > 0`! -/
private lemma ray_dist_to_pos_real {θ t ω : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (ht : 0 ≤ t) (_hω : 0 < ω) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ω * Real.sin θ ≤ ‖(t : ℂ) * Complex.exp (Complex.I * ((s * θ : ℝ) : ℂ)) - (ω : ℂ)‖ ∧
    ω ≤ ‖(t : ℂ) * Complex.exp (Complex.I * ((s * θ : ℝ) : ℂ)) + (ω : ℂ)‖ := by
  set z : ℂ := (t : ℂ) * Complex.exp (Complex.I * ((s * θ : ℝ) : ℂ))
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ1⟩
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hz_re : z.re = t * Real.cos θ := by
    dsimp only [z]
    rw [mul_comm Complex.I, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.exp_ofReal_mul_I_re]
    rcases hs with rfl | rfl <;> simp [Real.cos_neg]
  have hz_im : |z.im| = t * Real.sin θ := by
    dsimp only [z]
    rw [mul_comm Complex.I, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.exp_ofReal_mul_I_im]
    rcases hs with rfl | rfl
    · simp only [one_mul, abs_mul, abs_of_nonneg ht, abs_of_pos hsin]
    · simp only [neg_one_mul, Real.sin_neg, mul_neg, abs_neg, abs_mul, abs_of_nonneg ht, abs_of_pos hsin]
  constructor
  · -- `‖z - ω‖² = (t cos θ - ω)² + (t sin θ)² = (t - ω cos θ)² + (ω sin θ)² ≥ (ω sin θ)²`!
    have hsq : (ω * Real.sin θ) ^ 2 ≤ ‖z - (ω : ℂ)‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have hre : (z - (ω : ℂ)).re = t * Real.cos θ - ω := by simp [hz_re]
      have him : |(z - (ω : ℂ)).im| = t * Real.sin θ := by simpa using hz_im
      have him2 : (z - (ω : ℂ)).im * (z - (ω : ℂ)).im = (t * Real.sin θ) ^ 2 := by
        rw [← sq, ← sq_abs, him]
      rw [hre, him2]
      have hsc : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
      have halg : (t * Real.cos θ - ω) * (t * Real.cos θ - ω) + (t * Real.sin θ) ^ 2 - (ω * Real.sin θ) ^ 2 =
          (t - ω * Real.cos θ) ^ 2 + (t ^ 2 - ω ^ 2) * (Real.cos θ ^ 2 + Real.sin θ ^ 2 - 1) := by ring
      rw [hsc, sub_self, mul_zero, add_zero] at halg
      linarith [sq_nonneg (t - ω * Real.cos θ)]
    nlinarith [norm_nonneg (z - (ω : ℂ)), hsq]
  · -- `‖z + ω‖ ≥ (z + ω).re = t cos θ + ω ≥ ω`!
    calc ω ≤ t * Real.cos θ + ω := by nlinarith
      _ = (z + (ω : ℂ)).re := by simp [hz_re]
      _ ≤ ‖z + (ω : ℂ)‖ := Complex.re_le_norm _

/-- Analyticity of `ΦSimple0 P` at any `w` not equal to `± ωBase P m`. -/
private lemma ΦSimple0_analyticAt (P : Quasipoly) {w : ℂ}
    (hw : ∀ m : ℕ, w ≠ (ωBase P m : ℂ) ∧ w ≠ -(ωBase P m : ℂ)) :
    AnalyticAt ℂ (ΦSimple0 P) w := by
  obtain ⟨N, hN⟩ := ωBase_tail_ge_half P w 1
  let term (m : ℕ) (z : ℂ) : ℂ :=
    P.borelAmp 0 (m + 1) * (2 * z ^ 2 / ((ωBase P m : ℂ) * (z ^ 2 - (ωBase P m : ℂ) ^ 2)))
  have hhead_an : AnalyticAt ℂ (fun z => ∑ m ∈ Finset.range N, term m z) w := by
    refine Finset.analyticAt_fun_sum (Finset.range N) fun m _ => ?_
    have hω_ne : (ωBase P m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ωBase_pos' P m).ne'
    have hsq_ne : w ^ 2 - (ωBase P m : ℂ) ^ 2 ≠ 0 := by
      rw [show w ^ 2 - (ωBase P m : ℂ) ^ 2 = (w - (ωBase P m : ℂ)) * (w + (ωBase P m : ℂ)) by ring]
      exact mul_ne_zero (sub_ne_zero.mpr (hw m).1) (fun h0 => (hw m).2 (by linear_combination h0))
    refine analyticAt_const.mul ((analyticAt_const.mul (analyticAt_id.pow 2)).div
      (analyticAt_const.mul ((analyticAt_id.pow 2).sub analyticAt_const)) (mul_ne_zero hω_ne hsq_ne))
  obtain ⟨C0, hC0_nn, hC0_bd⟩ := P.borelAmp_norm_le 0
  have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  have hpi : (0 : ℝ) < 4 * Real.pi ^ 2 / (P.M : ℝ) := by positivity
  let Rw : ℝ := ‖w‖ + 1
  have htail_bd : ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball w 1 →
      ‖term (k + N) z‖ ≤
        (C0 * (8 * Rw ^ 2 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) *
          ((sigmaNat 1 (k + N + 1) : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 3) := by
    intro k z hz
    obtain ⟨hsub, hadd⟩ := hN k z hz
    have hω_pos : 0 < ωBase P (k + N) := by unfold ωBase; positivity
    have hz_le : ‖z‖ ≤ Rw := by
      have hdist : ‖z - w‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hz
      calc ‖z‖ = ‖(z - w) + w‖ := by ring_nf
        _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
        _ ≤ Rw := by dsimp only [Rw]; linarith
    have hden_ge : ωBase P (k + N) ^ 3 / 4 ≤ ‖(ωBase P (k + N) : ℂ) * (z ^ 2 - (ωBase P (k + N) : ℂ) ^ 2)‖ := by
      rw [show z ^ 2 - (ωBase P (k + N) : ℂ) ^ 2 = (z - (ωBase P (k + N) : ℂ)) * (z + (ωBase P (k + N) : ℂ)) by ring,
        norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hω_pos.le]
      have hmul : (ωBase P (k + N) / 2) * (ωBase P (k + N) / 2) ≤
          ‖z - (ωBase P (k + N) : ℂ)‖ * ‖z + (ωBase P (k + N) : ℂ)‖ :=
        mul_le_mul hsub hadd (by positivity) (norm_nonneg _)
      calc ωBase P (k + N) ^ 3 / 4
          = ωBase P (k + N) * ((ωBase P (k + N) / 2) * (ωBase P (k + N) / 2)) := by ring
        _ ≤ ωBase P (k + N) * (‖z - (ωBase P (k + N) : ℂ)‖ * ‖z + (ωBase P (k + N) : ℂ)‖) :=
            mul_le_mul_of_nonneg_left hmul hω_pos.le
    dsimp only [term]
    rw [norm_mul, norm_div, norm_mul, norm_pow, Complex.norm_ofNat]
    have h1 : ‖P.borelAmp 0 (k + N + 1)‖ ≤ C0 * (sigmaNat 1 (k + N + 1) : ℝ) :=
      hC0_bd (k + N + 1) (Nat.succ_pos _)
    have h2 : 2 * ‖z‖ ^ 2 / ‖(ωBase P (k + N) : ℂ) * (z ^ 2 - (ωBase P (k + N) : ℂ) ^ 2)‖ ≤
        2 * Rw ^ 2 / (ωBase P (k + N) ^ 3 / 4) :=
      div_le_div₀ (by positivity) (by gcongr) (by positivity) hden_ge
    calc ‖P.borelAmp 0 (k + N + 1)‖ * (2 * ‖z‖ ^ 2 / ‖(ωBase P (k + N) : ℂ) * (z ^ 2 - (ωBase P (k + N) : ℂ) ^ 2)‖)
        ≤ (C0 * (sigmaNat 1 (k + N + 1) : ℝ)) * (2 * Rw ^ 2 / (ωBase P (k + N) ^ 3 / 4)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (C0 * (8 * Rw ^ 2 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) *
            ((sigmaNat 1 (k + N + 1) : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 3) := by
          unfold ωBase
          have hn0 : ((k + N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
          field_simp [hM.ne', hn0, hpi0]; ring
  have hsumm_u : Summable (fun k : ℕ =>
      (C0 * (8 * Rw ^ 2 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) *
        ((sigmaNat 1 (k + N + 1) : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 3)) :=
    ((summable_sigmaNat_div_pow_two_more 0).comp_injective
      (fun a b (hab : a + N = b + N) => by omega)).mul_left _
  have htail_an : AnalyticAt ℂ (fun z => ∑' k : ℕ, term (k + N) z) w := by
    let term' (m : ℕ) (z : ℂ) : ℂ :=
      P.borelAmp 0 (m + 1) * (-4 * z * (ωBase P m : ℂ) / (z ^ 2 - (ωBase P m : ℂ) ^ 2) ^ 2)
    have hdiff : DifferentiableOn ℂ (fun z => ∑' k : ℕ, term (k + N) z) (Metric.ball w 1) := by
      intro z hz
      have hbound' : ∀ (k : ℕ) (y : ℂ), y ∈ Metric.ball w 1 →
          ‖term' (k + N) y‖ ≤ (C0 * (64 * Rw / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) *
            ((sigmaNat 1 (k + N + 1) : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 3) := by
        intro k y hy
        obtain ⟨hsub, hadd⟩ := hN k y hy
        have hω_pos : 0 < ωBase P (k + N) := ωBase_pos' P (k + N)
        have hy_le : ‖y‖ ≤ Rw := by
          have hdist : ‖y - w‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hy
          calc ‖y‖ = ‖(y - w) + w‖ := by ring_nf
            _ ≤ ‖y - w‖ + ‖w‖ := norm_add_le _ _
            _ ≤ Rw := by dsimp only [Rw]; linarith
        have hden : (ωBase P (k + N) ^ 2 / 4) ^ 2 ≤ ‖(y ^ 2 - (ωBase P (k + N) : ℂ) ^ 2) ^ 2‖ := by
          rw [norm_pow, show y ^ 2 - (ωBase P (k + N) : ℂ) ^ 2 =
            (y - (ωBase P (k + N) : ℂ)) * (y + (ωBase P (k + N) : ℂ)) by ring, norm_mul]
          have hmul := mul_le_mul hsub hadd (by positivity) (norm_nonneg _)
          exact pow_le_pow_left₀ (by positivity) (by linarith : ωBase P (k + N) ^ 2 / 4 ≤ _) 2
        dsimp only [term']
        rw [norm_mul, norm_div, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_of_nonneg hω_pos.le]
        have h1 := hC0_bd (k + N + 1) (Nat.succ_pos _)
        have h2 : 4 * ‖y‖ * ωBase P (k + N) / ‖(y ^ 2 - (ωBase P (k + N) : ℂ) ^ 2) ^ 2‖ ≤
            4 * Rw * ωBase P (k + N) / (ωBase P (k + N) ^ 2 / 4) ^ 2 :=
          div_le_div₀ (by positivity) (by gcongr) (by positivity) hden
        calc ‖P.borelAmp 0 (k + N + 1)‖ * _
            ≤ (C0 * (sigmaNat 1 (k + N + 1) : ℝ)) * (4 * Rw * ωBase P (k + N) / (ωBase P (k + N) ^ 2 / 4) ^ 2) :=
              mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = (C0 * (64 * Rw / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) *
                ((sigmaNat 1 (k + N + 1) : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 3) := by
              unfold ωBase
              have hn0 : ((k + N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
              have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
              field_simp [hM.ne', hn0, hpi0]; ring
      have hsumm' : Summable (fun k : ℕ => (C0 * (64 * Rw / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) *
          ((sigmaNat 1 (k + N + 1) : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 3)) :=
        ((summable_sigmaNat_div_pow_two_more 0).comp_injective
          (fun a b (hab : a + N = b + N) => by omega)).mul_left _
      have hderiv := hasDerivAt_tsum_of_isPreconnected hsumm' Metric.isOpen_ball
        (convex_ball w 1).isPreconnected
        (fun k y hy => by
          obtain ⟨hsub, hadd⟩ := hN k y hy
          have hω_pos : 0 < ωBase P (k + N) := ωBase_pos' P (k + N)
          have hz1 : y ≠ (ωBase P (k + N) : ℂ) := fun h0 => by rw [h0, sub_self, norm_zero] at hsub; linarith
          have hz2 : y ≠ -(ωBase P (k + N) : ℂ) := fun h0 => by rw [h0, neg_add_cancel, norm_zero] at hadd; linarith
          exact (hasDerivAt_ker0 (Complex.ofReal_ne_zero.mpr hω_pos.ne') hz1 hz2).const_mul _)
        hbound' (y₀ := w) (Metric.mem_ball_self one_pos)
        (hsumm_u.of_norm_bounded fun k => htail_bd k w (Metric.mem_ball_self one_pos)) hz
      exact hderiv.differentiableAt.differentiableWithinAt
    exact (hdiff.analyticOnNhd Metric.isOpen_ball) w (Metric.mem_ball_self one_pos)
  have heq_nhds : ΦSimple0 P =ᶠ[𝓝 w] fun z =>
      (1 / 2 : ℂ) * borelPref 0 * ((∑ m ∈ Finset.range N, term m z) + ∑' k : ℕ, term (k + N) z) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos)] with z hz
    unfold ΦSimple0
    congr 1
    have hsumm_tail : Summable (fun k : ℕ => term (k + N) z) :=
      (hsumm_u.of_norm_bounded fun k => htail_bd k z hz)
    have hsumm_all : Summable (fun m : ℕ => term m z) := (summable_nat_add_iff N).mp hsumm_tail
    exact (hsumm_all.sum_add_tsum_nat_add N).symm
  exact ((analyticAt_const.mul (hhead_an.add htail_an)).congr heq_nhds.symm)

/-- Analyticity of `ΦSimple1 P hD` at any `w` not equal to `± ωBase P m`. -/
private lemma ΦSimple1_analyticAt (P : Quasipoly) (hD : P.D = 1) {w : ℂ}
    (hw : ∀ m : ℕ, w ≠ (ωBase P m : ℂ) ∧ w ≠ -(ωBase P m : ℂ)) :
    AnalyticAt ℂ (ΦSimple1 P hD) w := by
  obtain ⟨N, hN⟩ := ωBase_tail_ge_half P w 1
  let d1 : Fin (P.D + 1) := ⟨1, by omega⟩
  let term (m : ℕ) (z : ℂ) : ℂ :=
    P.borelAmp d1 (m + 1) * (2 * z ^ 3 / ((ωBase P m : ℂ) ^ 2 * (z ^ 2 - (ωBase P m : ℂ) ^ 2)))
  have hhead_an : AnalyticAt ℂ (fun z => ∑ m ∈ Finset.range N, term m z) w := by
    refine Finset.analyticAt_fun_sum (Finset.range N) fun m _ => ?_
    have hω_ne : (ωBase P m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ωBase_pos' P m).ne'
    have hsq_ne : w ^ 2 - (ωBase P m : ℂ) ^ 2 ≠ 0 := by
      rw [show w ^ 2 - (ωBase P m : ℂ) ^ 2 = (w - (ωBase P m : ℂ)) * (w + (ωBase P m : ℂ)) by ring]
      exact mul_ne_zero (sub_ne_zero.mpr (hw m).1) (fun h0 => (hw m).2 (by linear_combination h0))
    refine analyticAt_const.mul ((analyticAt_const.mul (analyticAt_id.pow 3)).div
      (analyticAt_const.mul ((analyticAt_id.pow 2).sub analyticAt_const))
      (mul_ne_zero (pow_ne_zero 2 hω_ne) hsq_ne))
  obtain ⟨C1, hC1_nn, hC1_bd⟩ := P.borelAmp_norm_le d1
  have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  let Rw : ℝ := ‖w‖ + 1
  have htail_bd : ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball w 1 →
      ‖term (k + N) z‖ ≤
        (C1 * (8 * Rw ^ 3 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 4)) *
          ((sigmaNat 2 (k + N + 1) : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 4) := by
    intro k z hz
    obtain ⟨hsub, hadd⟩ := hN k z hz
    have hω_pos : 0 < ωBase P (k + N) := by unfold ωBase; positivity
    have hz_le : ‖z‖ ≤ Rw := by
      have hdist : ‖z - w‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hz
      calc ‖z‖ = ‖(z - w) + w‖ := by ring_nf
        _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
        _ ≤ Rw := by dsimp only [Rw]; linarith
    have hden_ge : ωBase P (k + N) ^ 4 / 4 ≤ ‖(ωBase P (k + N) : ℂ) ^ 2 * (z ^ 2 - (ωBase P (k + N) : ℂ) ^ 2)‖ := by
      rw [show z ^ 2 - (ωBase P (k + N) : ℂ) ^ 2 = (z - (ωBase P (k + N) : ℂ)) * (z + (ωBase P (k + N) : ℂ)) by ring,
        norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hω_pos.le]
      have hmul : (ωBase P (k + N) / 2) * (ωBase P (k + N) / 2) ≤
          ‖z - (ωBase P (k + N) : ℂ)‖ * ‖z + (ωBase P (k + N) : ℂ)‖ :=
        mul_le_mul hsub hadd (by positivity) (norm_nonneg _)
      calc ωBase P (k + N) ^ 4 / 4
          = ωBase P (k + N) ^ 2 * ((ωBase P (k + N) / 2) * (ωBase P (k + N) / 2)) := by ring
        _ ≤ ωBase P (k + N) ^ 2 * (‖z - (ωBase P (k + N) : ℂ)‖ * ‖z + (ωBase P (k + N) : ℂ)‖) :=
            mul_le_mul_of_nonneg_left hmul (pow_nonneg hω_pos.le 2)
    dsimp only [term]
    rw [norm_mul, norm_div, norm_mul, norm_pow, Complex.norm_ofNat]
    have h1 : ‖P.borelAmp d1 (k + N + 1)‖ ≤ C1 * (sigmaNat 2 (k + N + 1) : ℝ) :=
      hC1_bd (k + N + 1) (Nat.succ_pos _)
    have h2 : 2 * ‖z‖ ^ 3 / ‖(ωBase P (k + N) : ℂ) ^ 2 * (z ^ 2 - (ωBase P (k + N) : ℂ) ^ 2)‖ ≤
        2 * Rw ^ 3 / (ωBase P (k + N) ^ 4 / 4) :=
      div_le_div₀ (by positivity) (by gcongr) (by positivity) hden_ge
    calc ‖P.borelAmp d1 (k + N + 1)‖ * (2 * ‖z‖ ^ 3 / ‖(ωBase P (k + N) : ℂ) ^ 2 * (z ^ 2 - (ωBase P (k + N) : ℂ) ^ 2)‖)
        ≤ (C1 * (sigmaNat 2 (k + N + 1) : ℝ)) * (2 * Rw ^ 3 / (ωBase P (k + N) ^ 4 / 4)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (C1 * (8 * Rw ^ 3 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 4)) *
            ((sigmaNat 2 (k + N + 1) : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 4) := by
          unfold ωBase
          have hn0 : ((k + N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
          field_simp [hM.ne', hn0, hpi0]; ring
  have hsumm_u : Summable (fun k : ℕ =>
      (C1 * (8 * Rw ^ 3 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 4)) *
        ((sigmaNat 2 (k + N + 1) : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 4)) :=
    ((summable_sigmaNat_div_pow_two_more 1).comp_injective
      (fun a b (hab : a + N = b + N) => by omega)).mul_left _
  have htail_an : AnalyticAt ℂ (fun z => ∑' k : ℕ, term (k + N) z) w := by
    let term' (m : ℕ) (z : ℂ) : ℂ :=
      P.borelAmp d1 (m + 1) * (2 * z ^ 2 * (z ^ 2 - 3 * (ωBase P m : ℂ) ^ 2) /
        ((ωBase P m : ℂ) ^ 2 * (z ^ 2 - (ωBase P m : ℂ) ^ 2) ^ 2))
    let c0 : ℝ := 4 * Real.pi ^ 2 / (P.M : ℝ)
    have hc0_pos : 0 < c0 := by dsimp only [c0]; positivity
    let Mnum : ℝ := Rw ^ 2 / c0 ^ 2 + 3
    have hdiff : DifferentiableOn ℂ (fun z => ∑' k : ℕ, term (k + N) z) (Metric.ball w 1) := by
      intro z hz
      have hbound' : ∀ (k : ℕ) (y : ℂ), y ∈ Metric.ball w 1 →
          ‖term' (k + N) y‖ ≤ (C1 * (32 * Rw ^ 2 * Mnum / c0 ^ 4)) *
            ((sigmaNat 2 (k + N + 1) : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 4) := by
        intro k y hy
        obtain ⟨hsub, hadd⟩ := hN k y hy
        have hω_pos : 0 < ωBase P (k + N) := ωBase_pos' P (k + N)
        have hc0_le : c0 ≤ ωBase P (k + N) := by
          dsimp only [c0]; unfold ωBase
          have h1 : (1 : ℝ) ≤ ((k + N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
          calc 4 * Real.pi ^ 2 / (P.M : ℝ) = 4 * Real.pi ^ 2 * 1 / (P.M : ℝ) := by ring
            _ ≤ 4 * Real.pi ^ 2 * ((k + N + 1 : ℕ) : ℝ) / (P.M : ℝ) := by gcongr
        have hy_le : ‖y‖ ≤ Rw := by
          have hdist : ‖y - w‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hy
          calc ‖y‖ = ‖(y - w) + w‖ := by ring_nf
            _ ≤ ‖y - w‖ + ‖w‖ := norm_add_le _ _
            _ ≤ Rw := by dsimp only [Rw]; linarith
        have hnum : ‖2 * y ^ 2 * (y ^ 2 - 3 * (ωBase P (k + N) : ℂ) ^ 2)‖ ≤
            2 * Rw ^ 2 * (Mnum * ωBase P (k + N) ^ 2) := by
          rw [norm_mul, norm_mul, Complex.norm_ofNat, norm_pow]
          have htri : ‖y ^ 2 - 3 * (ωBase P (k + N) : ℂ) ^ 2‖ ≤ Mnum * ωBase P (k + N) ^ 2 := by
            have h1 : Rw ^ 2 ≤ (Rw ^ 2 / c0 ^ 2) * ωBase P (k + N) ^ 2 := by
              have hsq : c0 ^ 2 ≤ ωBase P (k + N) ^ 2 := pow_le_pow_left₀ hc0_pos.le hc0_le 2
              calc Rw ^ 2 = (Rw ^ 2 / c0 ^ 2) * c0 ^ 2 := by field_simp [hc0_pos.ne']
                _ ≤ (Rw ^ 2 / c0 ^ 2) * ωBase P (k + N) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
            calc _ ≤ ‖y ^ 2‖ + ‖3 * (ωBase P (k + N) : ℂ) ^ 2‖ := norm_sub_le _ _
              _ = ‖y‖ ^ 2 + 3 * ωBase P (k + N) ^ 2 := by
                  rw [norm_pow, norm_mul, Complex.norm_ofNat, norm_pow, Complex.norm_real, Real.norm_of_nonneg hω_pos.le]
              _ ≤ Rw ^ 2 + 3 * ωBase P (k + N) ^ 2 := by gcongr
              _ ≤ (Rw ^ 2 / c0 ^ 2) * ωBase P (k + N) ^ 2 + 3 * ωBase P (k + N) ^ 2 := add_le_add h1 le_rfl
              _ = Mnum * ωBase P (k + N) ^ 2 := by dsimp only [Mnum]; ring
          exact mul_le_mul (by gcongr) htri (norm_nonneg _) (by positivity)
        have hden : ωBase P (k + N) ^ 6 / 16 ≤
            ‖(ωBase P (k + N) : ℂ) ^ 2 * (y ^ 2 - (ωBase P (k + N) : ℂ) ^ 2) ^ 2‖ := by
          rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hω_pos.le,
            show y ^ 2 - (ωBase P (k + N) : ℂ) ^ 2 =
              (y - (ωBase P (k + N) : ℂ)) * (y + (ωBase P (k + N) : ℂ)) by ring, norm_mul]
          have hmul := mul_le_mul hsub hadd (by positivity) (norm_nonneg _)
          have hsq : (ωBase P (k + N) ^ 2 / 4) ^ 2 ≤
              (‖y - (ωBase P (k + N) : ℂ)‖ * ‖y + (ωBase P (k + N) : ℂ)‖) ^ 2 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 2
          calc ωBase P (k + N) ^ 6 / 16 = ωBase P (k + N) ^ 2 * (ωBase P (k + N) ^ 2 / 4) ^ 2 := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hsq (by positivity)
        dsimp only [term']
        rw [norm_mul, norm_div]
        calc ‖P.borelAmp d1 (k + N + 1)‖ * _
            ≤ (C1 * (sigmaNat 2 (k + N + 1) : ℝ)) *
                (2 * Rw ^ 2 * (Mnum * ωBase P (k + N) ^ 2) / (ωBase P (k + N) ^ 6 / 16)) :=
              mul_le_mul (hC1_bd (k + N + 1) (Nat.succ_pos _))
                (div_le_div₀ (by positivity) hnum (by positivity) hden) (by positivity) (by positivity)
          _ = (C1 * (32 * Rw ^ 2 * Mnum / c0 ^ 4)) *
                ((sigmaNat 2 (k + N + 1) : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 4) := by
              dsimp only [c0]; unfold ωBase
              have hn0 : ((k + N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
              have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
              field_simp [hM.ne', hn0, hpi0]; ring
      have hsumm' : Summable (fun k : ℕ => (C1 * (32 * Rw ^ 2 * Mnum / c0 ^ 4)) *
          ((sigmaNat 2 (k + N + 1) : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 4)) :=
        ((summable_sigmaNat_div_pow_two_more 1).comp_injective
          (fun a b (hab : a + N = b + N) => by omega)).mul_left _
      have hderiv := hasDerivAt_tsum_of_isPreconnected hsumm' Metric.isOpen_ball
        (convex_ball w 1).isPreconnected
        (fun k y hy => by
          obtain ⟨hsub, hadd⟩ := hN k y hy
          have hω_pos : 0 < ωBase P (k + N) := ωBase_pos' P (k + N)
          have hz1 : y ≠ (ωBase P (k + N) : ℂ) := fun h0 => by rw [h0, sub_self, norm_zero] at hsub; linarith
          have hz2 : y ≠ -(ωBase P (k + N) : ℂ) := fun h0 => by rw [h0, neg_add_cancel, norm_zero] at hadd; linarith
          exact (hasDerivAt_ker1 (Complex.ofReal_ne_zero.mpr hω_pos.ne') hz1 hz2).const_mul _)
        hbound' (y₀ := w) (Metric.mem_ball_self one_pos)
        (hsumm_u.of_norm_bounded fun k => htail_bd k w (Metric.mem_ball_self one_pos)) hz
      exact hderiv.differentiableAt.differentiableWithinAt
    exact (hdiff.analyticOnNhd Metric.isOpen_ball) w (Metric.mem_ball_self one_pos)
  have heq_nhds : ΦSimple1 P hD =ᶠ[𝓝 w] fun z =>
      (-(1 / 6) : ℂ) * borelPref 1 * ((∑ m ∈ Finset.range N, term m z) + ∑' k : ℕ, term (k + N) z) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos)] with z hz
    unfold ΦSimple1
    congr 1
    have hsumm_tail : Summable (fun k : ℕ => term (k + N) z) :=
      hsumm_u.of_norm_bounded fun k => htail_bd k z hz
    have hsumm_all : Summable (fun m : ℕ => term m z) := (summable_nat_add_iff N).mp hsumm_tail
    exact (hsumm_all.sum_add_tsum_nat_add N).symm
  exact (analyticAt_const.mul (hhead_an.add htail_an)).congr heq_nhds.symm

private lemma continuousOn_sum' {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → ℂ → ℂ} {t : Set ℂ}
    (hf : ∀ i ∈ s, ContinuousOn (f i) t) :
    ContinuousOn (fun z => ∑ i ∈ s, f i z) t := by
  induction s using Finset.induction_on with
  | empty => simpa using continuousOn_const
  | insert a s ha ih =>
    have heq : (fun z => ∑ i ∈ insert a s, f i z) = fun z => f a z + ∑ i ∈ s, f i z := by
      funext z; exact Finset.sum_insert ha
    rw [heq]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma continuousAt_sum' {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → ℂ → ℂ} {w : ℂ}
    (hf : ∀ i ∈ s, ContinuousAt (f i) w) :
    ContinuousAt (fun z => ∑ i ∈ s, f i z) w := by
  induction s using Finset.induction_on with
  | empty => simpa using continuousAt_const
  | insert a s ha ih =>
    have heq : (fun z => ∑ i ∈ insert a s, f i z) = fun z => f a z + ∑ i ∈ s, f i z := by
      funext z; exact Finset.sum_insert ha
    rw [heq]
    exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- Simple-pole residue of `ΦSimple0 P` at `ωBase P m₀`. -/
private lemma ΦSimple0_pole_res (P : Quasipoly) (m₀ : ℕ) :
    ∃ L : ℂ, Filter.Tendsto
      (fun z : ℂ => ΦSimple0 P z - ((1 / 2 : ℂ) * borelPref 0 * P.borelAmp 0 (m₀ + 1)) / (z - (ωBase P m₀ : ℂ)))
      (𝓝[≠] (ωBase P m₀ : ℂ)) (𝓝 L) := by
  let ω₀ : ℝ := ωBase P m₀
  have hω₀_pos : 0 < ω₀ := ωBase_pos' P m₀
  have hω₀_ne : (ω₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω₀_pos.ne'
  obtain ⟨N, hN⟩ := ωBase_tail_ge_half P (ω₀ : ℂ) 1
  let N' : ℕ := max N (m₀ + 1)
  have hm₀_lt : m₀ < N' := lt_of_lt_of_le (Nat.lt_succ_self m₀) (le_max_right _ _)
  let term (m : ℕ) (z : ℂ) : ℂ :=
    P.borelAmp 0 (m + 1) * (2 * z ^ 2 / ((ωBase P m : ℂ) * (z ^ 2 - (ωBase P m : ℂ) ^ 2)))
  let rest (z : ℂ) : ℂ :=
    (1 / 2 : ℂ) * borelPref 0 *
      (P.borelAmp 0 (m₀ + 1) * (-(z + (ω₀ : ℂ))⁻¹ + 2 / (ω₀ : ℂ)) +
        (∑ m ∈ (Finset.range N').erase m₀, term m z) +
        ∑' k : ℕ, term (k + N') z)
  have hrest_cont : ContinuousAt rest (ω₀ : ℂ) := by
    -- Same tail analyticity as in `ΦSimple0_analyticAt`, plus each `m ≠ m₀` avoids `ω₀`!
    obtain ⟨C0, hC0_nn, hC0_bd⟩ := P.borelAmp_norm_le 0
    have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
    let Rw : ℝ := ‖(ω₀ : ℂ)‖ + 1
    have htail_bd : ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball (ω₀ : ℂ) 1 →
        ‖term (k + N') z‖ ≤
          (C0 * (8 * Rw ^ 2 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) *
            ((sigmaNat 1 (k + N' + 1) : ℝ) / ((k + N' + 1 : ℕ) : ℝ) ^ 3) := by
      intro k z hz
      have hNk := hN (k + (N' - N)) z hz
      have heq_idx : k + (N' - N) + N = k + N' := by omega
      rw [heq_idx] at hNk
      obtain ⟨hsub, hadd⟩ := hNk
      have hω_pos : 0 < ωBase P (k + N') := by unfold ωBase; positivity
      have hz_le : ‖z‖ ≤ Rw := by
        have hdist : ‖z - (ω₀ : ℂ)‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hz
        calc ‖z‖ = ‖(z - (ω₀ : ℂ)) + (ω₀ : ℂ)‖ := by ring_nf
          _ ≤ ‖z - (ω₀ : ℂ)‖ + ‖(ω₀ : ℂ)‖ := norm_add_le _ _
          _ ≤ Rw := by dsimp only [Rw]; linarith
      have hden_ge : ωBase P (k + N') ^ 3 / 4 ≤ ‖(ωBase P (k + N') : ℂ) * (z ^ 2 - (ωBase P (k + N') : ℂ) ^ 2)‖ := by
        rw [show z ^ 2 - (ωBase P (k + N') : ℂ) ^ 2 = (z - (ωBase P (k + N') : ℂ)) * (z + (ωBase P (k + N') : ℂ)) by ring,
          norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hω_pos.le]
        have hmul := mul_le_mul hsub hadd (by positivity) (norm_nonneg _)
        calc ωBase P (k + N') ^ 3 / 4
            = ωBase P (k + N') * ((ωBase P (k + N') / 2) * (ωBase P (k + N') / 2)) := by ring
          _ ≤ ωBase P (k + N') * (‖z - (ωBase P (k + N') : ℂ)‖ * ‖z + (ωBase P (k + N') : ℂ)‖) :=
              mul_le_mul_of_nonneg_left hmul hω_pos.le
      dsimp only [term]
      rw [norm_mul, norm_div, norm_mul, norm_pow, Complex.norm_ofNat]
      have h1 := hC0_bd (k + N' + 1) (Nat.succ_pos _)
      have h2 : 2 * ‖z‖ ^ 2 / ‖(ωBase P (k + N') : ℂ) * (z ^ 2 - (ωBase P (k + N') : ℂ) ^ 2)‖ ≤
          2 * Rw ^ 2 / (ωBase P (k + N') ^ 3 / 4) :=
        div_le_div₀ (by positivity) (by gcongr) (by positivity) hden_ge
      calc ‖P.borelAmp 0 (k + N' + 1)‖ * _
          ≤ (C0 * (sigmaNat 1 (k + N' + 1) : ℝ)) * (2 * Rw ^ 2 / (ωBase P (k + N') ^ 3 / 4)) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (C0 * (8 * Rw ^ 2 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) *
              ((sigmaNat 1 (k + N' + 1) : ℝ) / ((k + N' + 1 : ℕ) : ℝ) ^ 3) := by
            unfold ωBase
            have hn0 : ((k + N' + 1 : ℕ) : ℝ) ≠ 0 := by positivity
            have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
            field_simp [hM.ne', hn0, hpi0]; ring
    have hsumm_u : Summable (fun k : ℕ =>
        (C0 * (8 * Rw ^ 2 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) *
          ((sigmaNat 1 (k + N' + 1) : ℝ) / ((k + N' + 1 : ℕ) : ℝ) ^ 3)) :=
      ((summable_sigmaNat_div_pow_two_more 0).comp_injective
        (fun a b (hab : a + N' = b + N') => by omega)).mul_left _
    have htail_cont : ContinuousAt (fun z => ∑' k : ℕ, term (k + N') z) (ω₀ : ℂ) := by
      have hunif : TendstoUniformlyOn (fun (s : Finset ℕ) z => ∑ k ∈ s, term (k + N') z)
          (fun z => ∑' k : ℕ, term (k + N') z) atTop (Metric.ball (ω₀ : ℂ) 1) :=
        tendstoUniformlyOn_tsum hsumm_u fun k z hz => htail_bd k z hz
      have hcontOn := hunif.continuousOn (Filter.Eventually.of_forall fun s =>
        continuousOn_sum' s (f := fun k z => term (k + N') z) fun k _ => fun z hz => by
          have hNk := hN (k + (N' - N)) z hz
          rw [show k + (N' - N) + N = k + N' by omega] at hNk
          have hω_pos : 0 < ωBase P (k + N') := ωBase_pos' P (k + N')
          have hz1 : z ≠ (ωBase P (k + N') : ℂ) := fun h0 => by rw [h0, sub_self, norm_zero] at hNk; linarith [hNk.1]
          have hz2 : z ≠ -(ωBase P (k + N') : ℂ) := fun h0 => by rw [h0, neg_add_cancel, norm_zero] at hNk; linarith [hNk.2]
          exact ((hasDerivAt_ker0 (Complex.ofReal_ne_zero.mpr hω_pos.ne') hz1 hz2).const_mul _).continuousAt.continuousWithinAt).frequently
      exact hcontOn.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))
    have hfin_cont : ContinuousAt (fun z => ∑ m ∈ (Finset.range N').erase m₀, term m z) (ω₀ : ℂ) := by
      refine continuousAt_sum' _ fun m hm => ?_
      have hne : m ≠ m₀ := (Finset.mem_erase.mp hm).1
      have hωm_pos : 0 < ωBase P m := by unfold ωBase; positivity
      have hω_ne_ω₀ : ωBase P m ≠ ω₀ := by
        intro heq
        unfold ω₀ ωBase at heq
        have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
        have hnat : ((m + 1 : ℕ) : ℝ) = ((m₀ + 1 : ℕ) : ℝ) := by
          have := congrArg (· * (P.M : ℝ) / (4 * Real.pi ^ 2)) heq
          field_simp [hM.ne', hpi0] at this; linarith
        exact hne (by exact_mod_cast Nat.succ.inj (Nat.cast_injective hnat))
      have hz1 : (ω₀ : ℂ) ≠ (ωBase P m : ℂ) := fun h => hω_ne_ω₀ (Complex.ofReal_injective h).symm
      have hz2 : (ω₀ : ℂ) ≠ -(ωBase P m : ℂ) := fun h => by
        have : ω₀ = -ωBase P m := Complex.ofReal_injective (by simpa using h); linarith
      exact ((hasDerivAt_ker0 (Complex.ofReal_ne_zero.mpr hωm_pos.ne') hz1 hz2).const_mul _).continuousAt
    have hpart_cont : ContinuousAt (fun z : ℂ => -(z + (ω₀ : ℂ))⁻¹ + 2 / (ω₀ : ℂ)) (ω₀ : ℂ) := by
      have h2ω : (ω₀ : ℂ) + (ω₀ : ℂ) ≠ 0 := by
        rw [show (ω₀ : ℂ) + (ω₀ : ℂ) = 2 * (ω₀ : ℂ) by ring]; exact mul_ne_zero two_ne_zero hω₀_ne
      exact ((continuousAt_id.add continuousAt_const).inv₀ h2ω).neg.add continuousAt_const
    exact continuousAt_const.mul (((continuousAt_const.mul hpart_cont).add hfin_cont).add htail_cont)
  refine ⟨rest (ω₀ : ℂ), (hrest_cont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_⟩
  have hball : Metric.ball (ω₀ : ℂ) (min 1 ω₀) ∈ 𝓝 (ω₀ : ℂ) :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (lt_min one_pos hω₀_pos))
  filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with z hz hzne
  have hz1 : z ≠ (ω₀ : ℂ) := hzne
  have hz2 : z ≠ -(ω₀ : ℂ) := by
    intro h0
    have hdist : ‖z - (ω₀ : ℂ)‖ < ω₀ :=
      (by simpa [dist_eq_norm] using Metric.mem_ball.mp hz : ‖z - (ω₀ : ℂ)‖ < min 1 ω₀).trans_le (min_le_right _ _)
    rw [h0, show -(ω₀ : ℂ) - (ω₀ : ℂ) = -(2 * (ω₀ : ℂ)) by ring, norm_neg, norm_mul,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg hω₀_pos.le] at hdist
    linarith
  have hz_b1 : z ∈ Metric.ball (ω₀ : ℂ) 1 := Metric.ball_subset_ball (min_le_left _ _) hz
  obtain ⟨C0, hC0_nn, hC0_bd⟩ := P.borelAmp_norm_le 0
  have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  have hsumm_tail : Summable (fun k : ℕ => term (k + N') z) := by
    let Rw : ℝ := ‖(ω₀ : ℂ)‖ + 1
    have hsumm_u : Summable (fun k : ℕ =>
        (C0 * (8 * Rw ^ 2 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) *
          ((sigmaNat 1 (k + N' + 1) : ℝ) / ((k + N' + 1 : ℕ) : ℝ) ^ 3)) :=
      ((summable_sigmaNat_div_pow_two_more 0).comp_injective
        (fun a b (hab : a + N' = b + N') => by omega)).mul_left _
    refine hsumm_u.of_norm_bounded fun k => ?_
    have hNk := hN (k + (N' - N)) z hz_b1
    rw [show k + (N' - N) + N = k + N' by omega] at hNk
    obtain ⟨hsub, hadd⟩ := hNk
    have hω_pos : 0 < ωBase P (k + N') := ωBase_pos' P (k + N')
    have hz_le : ‖z‖ ≤ Rw := by
      have hdist : ‖z - (ω₀ : ℂ)‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hz_b1
      calc ‖z‖ = ‖(z - (ω₀ : ℂ)) + (ω₀ : ℂ)‖ := by ring_nf
        _ ≤ ‖z - (ω₀ : ℂ)‖ + ‖(ω₀ : ℂ)‖ := norm_add_le _ _
        _ ≤ Rw := by dsimp only [Rw]; linarith
    have hden_ge : ωBase P (k + N') ^ 3 / 4 ≤ ‖(ωBase P (k + N') : ℂ) * (z ^ 2 - (ωBase P (k + N') : ℂ) ^ 2)‖ := by
      rw [show z ^ 2 - (ωBase P (k + N') : ℂ) ^ 2 = (z - (ωBase P (k + N') : ℂ)) * (z + (ωBase P (k + N') : ℂ)) by ring,
        norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hω_pos.le]
      have hmul := mul_le_mul hsub hadd (by positivity) (norm_nonneg _)
      calc ωBase P (k + N') ^ 3 / 4
          = ωBase P (k + N') * ((ωBase P (k + N') / 2) * (ωBase P (k + N') / 2)) := by ring
        _ ≤ ωBase P (k + N') * (‖z - (ωBase P (k + N') : ℂ)‖ * ‖z + (ωBase P (k + N') : ℂ)‖) :=
            mul_le_mul_of_nonneg_left hmul hω_pos.le
    dsimp only [term]
    rw [norm_mul, norm_div, norm_mul, norm_pow, Complex.norm_ofNat]
    have h1 := hC0_bd (k + N' + 1) (Nat.succ_pos _)
    have h2 : 2 * ‖z‖ ^ 2 / ‖(ωBase P (k + N') : ℂ) * (z ^ 2 - (ωBase P (k + N') : ℂ) ^ 2)‖ ≤
        2 * Rw ^ 2 / (ωBase P (k + N') ^ 3 / 4) :=
      div_le_div₀ (by positivity) (by gcongr) (by positivity) hden_ge
    calc ‖P.borelAmp 0 (k + N' + 1)‖ * _
        ≤ (C0 * (sigmaNat 1 (k + N' + 1) : ℝ)) * (2 * Rw ^ 2 / (ωBase P (k + N') ^ 3 / 4)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (C0 * (8 * Rw ^ 2 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) *
            ((sigmaNat 1 (k + N' + 1) : ℝ) / ((k + N' + 1 : ℕ) : ℝ) ^ 3) := by
          unfold ωBase
          have hn0 : ((k + N' + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
          field_simp [hM.ne', hn0, hpi0]; ring
  have hsumm_all : Summable (fun m : ℕ => term m z) := (summable_nat_add_iff N').mp hsumm_tail
  symm
  unfold ΦSimple0
  rw [← hsumm_all.sum_add_tsum_nat_add N', ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hm₀_lt)]
  dsimp only [rest, term]
  rw [show ωBase P m₀ = ω₀ from rfl, ker0_decomp hω₀_ne hz1 hz2]
  ring

/-- Simple-pole residue of `ΦSimple1 P hD` at `ωBase P m₀`. -/
private lemma ΦSimple1_pole_res (P : Quasipoly) (hD : P.D = 1) (m₀ : ℕ) :
    ∃ L : ℂ, Filter.Tendsto
      (fun z : ℂ => ΦSimple1 P hD z -
        ((-(1 / 6) : ℂ) * borelPref 1 * P.borelAmp ⟨1, by omega⟩ (m₀ + 1)) / (z - (ωBase P m₀ : ℂ)))
      (𝓝[≠] (ωBase P m₀ : ℂ)) (𝓝 L) := by
  let d1 : Fin (P.D + 1) := ⟨1, by omega⟩
  let ω₀ : ℝ := ωBase P m₀
  have hω₀_pos : 0 < ω₀ := ωBase_pos' P m₀
  have hω₀_ne : (ω₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω₀_pos.ne'
  obtain ⟨N, hN⟩ := ωBase_tail_ge_half P (ω₀ : ℂ) 1
  let N' : ℕ := max N (m₀ + 1)
  have hm₀_lt : m₀ < N' := lt_of_lt_of_le (Nat.lt_succ_self m₀) (le_max_right _ _)
  let term (m : ℕ) (z : ℂ) : ℂ :=
    P.borelAmp d1 (m + 1) * (2 * z ^ 3 / ((ωBase P m : ℂ) ^ 2 * (z ^ 2 - (ωBase P m : ℂ) ^ 2)))
  let rest (z : ℂ) : ℂ :=
    (-(1 / 6) : ℂ) * borelPref 1 *
      (P.borelAmp d1 (m₀ + 1) * ((z + (ω₀ : ℂ))⁻¹ + 2 * z / (ω₀ : ℂ) ^ 2) +
        (∑ m ∈ (Finset.range N').erase m₀, term m z) +
        ∑' k : ℕ, term (k + N') z)
  obtain ⟨C1, hC1_nn, hC1_bd⟩ := P.borelAmp_norm_le d1
  have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  let Rw : ℝ := ‖(ω₀ : ℂ)‖ + 1
  have htail_bd : ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball (ω₀ : ℂ) 1 →
      ‖term (k + N') z‖ ≤
        (C1 * (8 * Rw ^ 3 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 4)) *
          ((sigmaNat 2 (k + N' + 1) : ℝ) / ((k + N' + 1 : ℕ) : ℝ) ^ 4) := by
    intro k z hz
    have hNk := hN (k + (N' - N)) z hz
    rw [show k + (N' - N) + N = k + N' by omega] at hNk
    obtain ⟨hsub, hadd⟩ := hNk
    have hω_pos : 0 < ωBase P (k + N') := by unfold ωBase; positivity
    have hz_le : ‖z‖ ≤ Rw := by
      have hdist : ‖z - (ω₀ : ℂ)‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hz
      calc ‖z‖ = ‖(z - (ω₀ : ℂ)) + (ω₀ : ℂ)‖ := by ring_nf
        _ ≤ ‖z - (ω₀ : ℂ)‖ + ‖(ω₀ : ℂ)‖ := norm_add_le _ _
        _ ≤ Rw := by dsimp only [Rw]; linarith
    have hden_ge : ωBase P (k + N') ^ 4 / 4 ≤ ‖(ωBase P (k + N') : ℂ) ^ 2 * (z ^ 2 - (ωBase P (k + N') : ℂ) ^ 2)‖ := by
      rw [show z ^ 2 - (ωBase P (k + N') : ℂ) ^ 2 = (z - (ωBase P (k + N') : ℂ)) * (z + (ωBase P (k + N') : ℂ)) by ring,
        norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hω_pos.le]
      have hmul := mul_le_mul hsub hadd (by positivity) (norm_nonneg _)
      calc ωBase P (k + N') ^ 4 / 4
          = ωBase P (k + N') ^ 2 * ((ωBase P (k + N') / 2) * (ωBase P (k + N') / 2)) := by ring
        _ ≤ ωBase P (k + N') ^ 2 * (‖z - (ωBase P (k + N') : ℂ)‖ * ‖z + (ωBase P (k + N') : ℂ)‖) :=
            mul_le_mul_of_nonneg_left hmul (pow_nonneg hω_pos.le 2)
    dsimp only [term]
    rw [norm_mul, norm_div, norm_mul, norm_pow, Complex.norm_ofNat]
    have h1 := hC1_bd (k + N' + 1) (Nat.succ_pos _)
    have h2 : 2 * ‖z‖ ^ 3 / ‖(ωBase P (k + N') : ℂ) ^ 2 * (z ^ 2 - (ωBase P (k + N') : ℂ) ^ 2)‖ ≤
        2 * Rw ^ 3 / (ωBase P (k + N') ^ 4 / 4) :=
      div_le_div₀ (by positivity) (by gcongr) (by positivity) hden_ge
    calc ‖P.borelAmp d1 (k + N' + 1)‖ * _
        ≤ (C1 * (sigmaNat 2 (k + N' + 1) : ℝ)) * (2 * Rw ^ 3 / (ωBase P (k + N') ^ 4 / 4)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (C1 * (8 * Rw ^ 3 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 4)) *
            ((sigmaNat 2 (k + N' + 1) : ℝ) / ((k + N' + 1 : ℕ) : ℝ) ^ 4) := by
          unfold ωBase
          have hn0 : ((k + N' + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
          field_simp [hM.ne', hn0, hpi0]; ring
  have hsumm_u : Summable (fun k : ℕ =>
      (C1 * (8 * Rw ^ 3 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 4)) *
        ((sigmaNat 2 (k + N' + 1) : ℝ) / ((k + N' + 1 : ℕ) : ℝ) ^ 4)) :=
    ((summable_sigmaNat_div_pow_two_more 1).comp_injective
      (fun a b (hab : a + N' = b + N') => by omega)).mul_left _
  have hrest_cont : ContinuousAt rest (ω₀ : ℂ) := by
    have htail_cont : ContinuousAt (fun z => ∑' k : ℕ, term (k + N') z) (ω₀ : ℂ) := by
      have hunif : TendstoUniformlyOn (fun (s : Finset ℕ) z => ∑ k ∈ s, term (k + N') z)
          (fun z => ∑' k : ℕ, term (k + N') z) atTop (Metric.ball (ω₀ : ℂ) 1) :=
        tendstoUniformlyOn_tsum hsumm_u fun k z hz => htail_bd k z hz
      have hcontOn := hunif.continuousOn (Filter.Eventually.of_forall fun s =>
        continuousOn_sum' s (f := fun k z => term (k + N') z) fun k _ => fun z hz => by
          have hNk := hN (k + (N' - N)) z hz
          rw [show k + (N' - N) + N = k + N' by omega] at hNk
          have hω_pos : 0 < ωBase P (k + N') := ωBase_pos' P (k + N')
          have hz1 : z ≠ (ωBase P (k + N') : ℂ) := fun h0 => by rw [h0, sub_self, norm_zero] at hNk; linarith [hNk.1]
          have hz2 : z ≠ -(ωBase P (k + N') : ℂ) := fun h0 => by rw [h0, neg_add_cancel, norm_zero] at hNk; linarith [hNk.2]
          exact ((hasDerivAt_ker1 (Complex.ofReal_ne_zero.mpr hω_pos.ne') hz1 hz2).const_mul _).continuousAt.continuousWithinAt).frequently
      exact hcontOn.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))
    have hfin_cont : ContinuousAt (fun z => ∑ m ∈ (Finset.range N').erase m₀, term m z) (ω₀ : ℂ) := by
      refine continuousAt_sum' _ fun m hm => ?_
      have hne : m ≠ m₀ := (Finset.mem_erase.mp hm).1
      have hωm_pos : 0 < ωBase P m := by unfold ωBase; positivity
      have hω_ne_ω₀ : ωBase P m ≠ ω₀ := by
        intro heq
        unfold ω₀ ωBase at heq
        have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
        have hnat : ((m + 1 : ℕ) : ℝ) = ((m₀ + 1 : ℕ) : ℝ) := by
          have := congrArg (· * (P.M : ℝ) / (4 * Real.pi ^ 2)) heq
          field_simp [hM.ne', hpi0] at this; linarith
        exact hne (by exact_mod_cast Nat.succ.inj (Nat.cast_injective hnat))
      have hz1 : (ω₀ : ℂ) ≠ (ωBase P m : ℂ) := fun h => hω_ne_ω₀ (Complex.ofReal_injective h).symm
      have hz2 : (ω₀ : ℂ) ≠ -(ωBase P m : ℂ) := fun h => by
        have : ω₀ = -ωBase P m := Complex.ofReal_injective (by simpa using h); linarith
      exact ((hasDerivAt_ker1 (Complex.ofReal_ne_zero.mpr hωm_pos.ne') hz1 hz2).const_mul _).continuousAt
    have hpart_cont : ContinuousAt (fun z : ℂ => (z + (ω₀ : ℂ))⁻¹ + 2 * z / (ω₀ : ℂ) ^ 2) (ω₀ : ℂ) := by
      have h2ω : (ω₀ : ℂ) + (ω₀ : ℂ) ≠ 0 := by
        rw [show (ω₀ : ℂ) + (ω₀ : ℂ) = 2 * (ω₀ : ℂ) by ring]; exact mul_ne_zero two_ne_zero hω₀_ne
      exact ((continuousAt_id.add continuousAt_const).inv₀ h2ω).add
        ((continuousAt_const.mul continuousAt_id).div_const _)
    exact continuousAt_const.mul (((continuousAt_const.mul hpart_cont).add hfin_cont).add htail_cont)
  refine ⟨rest (ω₀ : ℂ), (hrest_cont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_⟩
  have hball : Metric.ball (ω₀ : ℂ) (min 1 ω₀) ∈ 𝓝 (ω₀ : ℂ) :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (lt_min one_pos hω₀_pos))
  filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with z hz hzne
  have hz1 : z ≠ (ω₀ : ℂ) := hzne
  have hz2 : z ≠ -(ω₀ : ℂ) := by
    intro h0
    have hdist : ‖z - (ω₀ : ℂ)‖ < ω₀ :=
      (by simpa [dist_eq_norm] using Metric.mem_ball.mp hz : ‖z - (ω₀ : ℂ)‖ < min 1 ω₀).trans_le (min_le_right _ _)
    rw [h0, show -(ω₀ : ℂ) - (ω₀ : ℂ) = -(2 * (ω₀ : ℂ)) by ring, norm_neg, norm_mul,
      Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg hω₀_pos.le] at hdist
    linarith
  have hz_b1 : z ∈ Metric.ball (ω₀ : ℂ) 1 := Metric.ball_subset_ball (min_le_left _ _) hz
  have hsumm_tail : Summable (fun k : ℕ => term (k + N') z) :=
    hsumm_u.of_norm_bounded fun k => htail_bd k z hz_b1
  have hsumm_all : Summable (fun m : ℕ => term m z) := (summable_nat_add_iff N').mp hsumm_tail
  symm
  unfold ΦSimple1
  rw [← hsumm_all.sum_add_tsum_nat_add N', ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hm₀_lt)]
  dsimp only [rest, term, d1]
  rw [show ωBase P m₀ = ω₀ from rfl, ker1_decomp hω₀_ne hz1 hz2]
  ring

/-- Polynomial-growth `ExpType` bound along `e^{±iθ}` for `ΦSimple0 P`. -/
private lemma ΦSimple0_expType (P : Quasipoly) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ExpType (Minor.pull (Complex.exp (Complex.I * ((s * θ : ℝ) : ℂ))) (ΦSimple0 P)) := by
  obtain ⟨C0, hC0_nn, hC0_bd⟩ := P.borelAmp_norm_le 0
  have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  let K : ℝ := ‖(1 / 2 : ℂ) * borelPref 0‖ * C0 * (2 / (Real.sin θ * (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) *
    ∑' m : ℕ, (sigmaNat 1 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 3
  refine ⟨2 * K + 1, 1, by positivity, by norm_num, fun t ht => ?_⟩
  set d : ℂ := Complex.exp (Complex.I * ((s * θ : ℝ) : ℂ))
  have hd_norm : ‖d‖ = 1 := by
    dsimp only [d]; rw [mul_comm Complex.I]; exact Complex.norm_exp_ofReal_mul_I (s * θ)
  have ht2_exp : t ^ 2 ≤ 2 * Real.exp t := by
    have h := Real.sum_le_exp_of_nonneg ht 3
    simp [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  dsimp only [Minor.pull, ΦSimple0]
  rw [norm_mul, hd_norm, one_mul, norm_mul, one_mul]
  simp_rw [mul_comm d (t : ℂ)]
  have hterm_le : ∀ m : ℕ,
      ‖P.borelAmp 0 (m + 1) * (2 * ((t : ℂ) * d) ^ 2 / ((ωBase P m : ℂ) * (((t : ℂ) * d) ^ 2 - (ωBase P m : ℂ) ^ 2)))‖ ≤
        (C0 * (2 / (Real.sin θ * (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) * t ^ 2) *
          ((sigmaNat 1 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 3) := by
    intro m
    have hω_pos : 0 < ωBase P m := by unfold ωBase; positivity
    obtain ⟨hsub, hadd⟩ := ray_dist_to_pos_real hθ0 hθ1 ht hω_pos s hs
    have hden_ge : Real.sin θ * ωBase P m ^ 3 ≤
        ‖(ωBase P m : ℂ) * (((t : ℂ) * d) ^ 2 - (ωBase P m : ℂ) ^ 2)‖ := by
      rw [show ((t : ℂ) * d) ^ 2 - (ωBase P m : ℂ) ^ 2 =
          ((t : ℂ) * d - (ωBase P m : ℂ)) * ((t : ℂ) * d + (ωBase P m : ℂ)) by ring,
        norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hω_pos.le]
      have hmul := mul_le_mul hsub hadd hω_pos.le (norm_nonneg _)
      calc Real.sin θ * ωBase P m ^ 3
          = ωBase P m * (ωBase P m * Real.sin θ * ωBase P m) := by ring
        _ ≤ ωBase P m * (‖(t : ℂ) * d - (ωBase P m : ℂ)‖ * ‖(t : ℂ) * d + (ωBase P m : ℂ)‖) :=
            mul_le_mul_of_nonneg_left hmul hω_pos.le
    rw [norm_mul, norm_div, norm_mul, norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg ht, hd_norm, mul_one]
    have h1 := hC0_bd (m + 1) (Nat.succ_pos _)
    have h2 : 2 * t ^ 2 / ‖(ωBase P m : ℂ) * (((t : ℂ) * d) ^ 2 - (ωBase P m : ℂ) ^ 2)‖ ≤
        2 * t ^ 2 / (Real.sin θ * ωBase P m ^ 3) :=
      div_le_div₀ (by positivity) le_rfl (by positivity) hden_ge
    calc ‖P.borelAmp 0 (m + 1)‖ * _
        ≤ (C0 * (sigmaNat 1 (m + 1) : ℝ)) * (2 * t ^ 2 / (Real.sin θ * ωBase P m ^ 3)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (C0 * (2 / (Real.sin θ * (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) * t ^ 2) *
            ((sigmaNat 1 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 3) := by
          unfold ωBase
          have hn0 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
          field_simp [hM.ne', hn0, hpi0, hsin.ne']
  let F (m : ℕ) : ℂ := P.borelAmp 0 (m + 1) *
    (2 * ((t : ℂ) * d) ^ 2 / ((ωBase P m : ℂ) * (((t : ℂ) * d) ^ 2 - (ωBase P m : ℂ) ^ 2)))
  have hsum_bd : ‖∑' m : ℕ, F m‖ ≤
      (C0 * (2 / (Real.sin θ * (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) * t ^ 2) *
        ∑' m : ℕ, (sigmaNat 1 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 3 := by
    have hsm := (summable_sigmaNat_div_pow_two_more 0).mul_left
      (C0 * (2 / (Real.sin θ * (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) * t ^ 2)
    have hFn : Summable (fun m => ‖F m‖) := hsm.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le
    calc ‖∑' m : ℕ, F m‖ ≤ ∑' m : ℕ, ‖F m‖ := norm_tsum_le_tsum_norm hFn
      _ ≤ ∑' m : ℕ, (C0 * (2 / (Real.sin θ * (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) * t ^ 2) *
            ((sigmaNat 1 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 3) := Summable.tsum_le_tsum hterm_le hFn hsm
      _ = _ := tsum_mul_left
  have hK_nn : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (by positivity) (tsum_nonneg fun _ => by positivity)
  have hle : ‖(1 / 2 : ℂ) * borelPref 0‖ * ‖∑' m : ℕ, F m‖ ≤ K * t ^ 2 := by
    calc ‖(1 / 2 : ℂ) * borelPref 0‖ * ‖∑' m : ℕ, F m‖
        ≤ ‖(1 / 2 : ℂ) * borelPref 0‖ * ((C0 * (2 / (Real.sin θ * (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) * t ^ 2) *
            ∑' m : ℕ, (sigmaNat 1 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left hsum_bd (norm_nonneg _)
      _ = K * t ^ 2 := by dsimp only [K]; ring
  calc ‖(1 / 2 : ℂ) * borelPref 0‖ * ‖∑' m : ℕ, F m‖
      ≤ K * t ^ 2 := hle
    _ ≤ K * (2 * Real.exp t) := mul_le_mul_of_nonneg_left ht2_exp hK_nn
    _ ≤ (2 * K + 1) * Real.exp t := by nlinarith [Real.exp_pos t]

/-- Polynomial-growth `ExpType` bound along `e^{±iθ}` for `ΦSimple1 P hD`. -/
private lemma ΦSimple1_expType (P : Quasipoly) (hD : P.D = 1) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ExpType (Minor.pull (Complex.exp (Complex.I * ((s * θ : ℝ) : ℂ))) (ΦSimple1 P hD)) := by
  let d1 : Fin (P.D + 1) := ⟨1, by omega⟩
  obtain ⟨C1, hC1_nn, hC1_bd⟩ := P.borelAmp_norm_le d1
  have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  let K : ℝ := ‖(-(1 / 6) : ℂ) * borelPref 1‖ * C1 * (2 / (Real.sin θ * (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 4)) *
    ∑' m : ℕ, (sigmaNat 2 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 4
  refine ⟨6 * K + 1, 1, by positivity, by norm_num, fun t ht => ?_⟩
  set d : ℂ := Complex.exp (Complex.I * ((s * θ : ℝ) : ℂ))
  have hd_norm : ‖d‖ = 1 := by
    dsimp only [d]; rw [mul_comm Complex.I]; exact Complex.norm_exp_ofReal_mul_I (s * θ)
  have ht3_exp : t ^ 3 ≤ 6 * Real.exp t := by
    have h := Real.sum_le_exp_of_nonneg ht 4
    simp [Finset.sum_range_succ, Nat.factorial] at h
    linarith [sq_nonneg t, ht]
  dsimp only [Minor.pull, ΦSimple1]
  rw [norm_mul, hd_norm, one_mul, norm_mul, one_mul]
  simp_rw [mul_comm d (t : ℂ)]
  have hterm_le : ∀ m : ℕ,
      ‖P.borelAmp d1 (m + 1) * (2 * ((t : ℂ) * d) ^ 3 / ((ωBase P m : ℂ) ^ 2 * (((t : ℂ) * d) ^ 2 - (ωBase P m : ℂ) ^ 2)))‖ ≤
        (C1 * (2 / (Real.sin θ * (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 4)) * t ^ 3) *
          ((sigmaNat 2 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 4) := by
    intro m
    have hω_pos : 0 < ωBase P m := by unfold ωBase; positivity
    obtain ⟨hsub, hadd⟩ := ray_dist_to_pos_real hθ0 hθ1 ht hω_pos s hs
    have hden_ge : Real.sin θ * ωBase P m ^ 4 ≤
        ‖(ωBase P m : ℂ) ^ 2 * (((t : ℂ) * d) ^ 2 - (ωBase P m : ℂ) ^ 2)‖ := by
      rw [show ((t : ℂ) * d) ^ 2 - (ωBase P m : ℂ) ^ 2 =
          ((t : ℂ) * d - (ωBase P m : ℂ)) * ((t : ℂ) * d + (ωBase P m : ℂ)) by ring,
        norm_mul, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hω_pos.le]
      have hmul := mul_le_mul hsub hadd hω_pos.le (norm_nonneg _)
      calc Real.sin θ * ωBase P m ^ 4
          = ωBase P m ^ 2 * (ωBase P m * Real.sin θ * ωBase P m) := by ring
        _ ≤ ωBase P m ^ 2 * (‖(t : ℂ) * d - (ωBase P m : ℂ)‖ * ‖(t : ℂ) * d + (ωBase P m : ℂ)‖) :=
            mul_le_mul_of_nonneg_left hmul (pow_nonneg hω_pos.le 2)
    rw [norm_mul, norm_div, norm_mul, norm_pow, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg ht, hd_norm, mul_one]
    have h1 := hC1_bd (m + 1) (Nat.succ_pos _)
    have h2 : 2 * t ^ 3 / ‖(ωBase P m : ℂ) ^ 2 * (((t : ℂ) * d) ^ 2 - (ωBase P m : ℂ) ^ 2)‖ ≤
        2 * t ^ 3 / (Real.sin θ * ωBase P m ^ 4) :=
      div_le_div₀ (by positivity) le_rfl (by positivity) hden_ge
    calc ‖P.borelAmp d1 (m + 1)‖ * _
        ≤ (C1 * (sigmaNat 2 (m + 1) : ℝ)) * (2 * t ^ 3 / (Real.sin θ * ωBase P m ^ 4)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (C1 * (2 / (Real.sin θ * (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 4)) * t ^ 3) *
            ((sigmaNat 2 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 4) := by
          unfold ωBase
          have hn0 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
          field_simp [hM.ne', hn0, hpi0, hsin.ne']
  let F (m : ℕ) : ℂ := P.borelAmp d1 (m + 1) *
    (2 * ((t : ℂ) * d) ^ 3 / ((ωBase P m : ℂ) ^ 2 * (((t : ℂ) * d) ^ 2 - (ωBase P m : ℂ) ^ 2)))
  have hsum_bd : ‖∑' m : ℕ, F m‖ ≤
      (C1 * (2 / (Real.sin θ * (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 4)) * t ^ 3) *
        ∑' m : ℕ, (sigmaNat 2 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 4 := by
    have hsm := (summable_sigmaNat_div_pow_two_more 1).mul_left
      (C1 * (2 / (Real.sin θ * (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 4)) * t ^ 3)
    have hFn : Summable (fun m => ‖F m‖) := hsm.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le
    calc ‖∑' m : ℕ, F m‖ ≤ ∑' m : ℕ, ‖F m‖ := norm_tsum_le_tsum_norm hFn
      _ ≤ ∑' m : ℕ, (C1 * (2 / (Real.sin θ * (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 4)) * t ^ 3) *
            ((sigmaNat 2 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 4) := Summable.tsum_le_tsum hterm_le hFn hsm
      _ = _ := tsum_mul_left
  have hK_nn : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (by positivity) (tsum_nonneg fun _ => by positivity)
  have hle : ‖(-(1 / 6) : ℂ) * borelPref 1‖ * ‖∑' m : ℕ, F m‖ ≤ K * t ^ 3 := by
    calc ‖(-(1 / 6) : ℂ) * borelPref 1‖ * ‖∑' m : ℕ, F m‖
        ≤ ‖(-(1 / 6) : ℂ) * borelPref 1‖ * ((C1 * (2 / (Real.sin θ * (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 4)) * t ^ 3) *
            ∑' m : ℕ, (sigmaNat 2 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_left hsum_bd (norm_nonneg _)
      _ = K * t ^ 3 := by dsimp only [K]; ring
  calc ‖(-(1 / 6) : ℂ) * borelPref 1‖ * ‖∑' m : ℕ, F m‖
      ≤ K * t ^ 3 := hle
    _ ≤ K * (6 * Real.exp t) := mul_le_mul_of_nonneg_left ht3_exp hK_nn
    _ ≤ (6 * K + 1) * Real.exp t := by nlinarith [Real.exp_pos t]

private lemma iteratedDeriv_add_nat' (k n : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv (k + n) f = iteratedDeriv k (iteratedDeriv n f) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.succ_add, iteratedDeriv_succ, iteratedDeriv_succ, ih]

/-- **Exact Formal-Series Identity for `ΦSimple0 P`** (`P.D = 0`):
`formalSeries (ΦSimple0 P) = PowerSeries.X ^ 2 * formalSeries (borelPhi P)`. -/
private lemma formalSeries_ΦSimple0 (P : Quasipoly) (hD : P.D = 0) :
    formalSeries (ΦSimple0 P) = PowerSeries.X ^ 2 * formalSeries (borelPhi P) := by
  let r₀ : ℝ := ωBase P 0 / 2
  have hr₀_pos : 0 < r₀ := half_pos (ωBase_pos' P 0)
  have hdist_ball : ∀ (m : ℕ) (z : ℂ), z ∈ Metric.ball (0 : ℂ) r₀ →
      ωBase P m / 2 ≤ ‖z - (ωBase P m : ℂ)‖ ∧ ωBase P m / 2 ≤ ‖z + (ωBase P m : ℂ)‖ := by
    intro m z hz
    have hzm : ‖z‖ < r₀ := by simpa [Metric.mem_ball, dist_zero_right] using hz
    have hω_ge : ωBase P 0 ≤ ωBase P m := by
      unfold ωBase; have : (0 : ℝ) < P.M := by exact_mod_cast P.hM
      have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
      gcongr; simp
    have hω_pos : 0 < ωBase P m := ωBase_pos' P m
    constructor
    · have htri := norm_sub_norm_le (ωBase P m : ℂ) z
      rw [norm_sub_rev, Complex.norm_real, Real.norm_of_nonneg hω_pos.le] at htri
      dsimp only [r₀] at hzm; linarith
    · have htri := norm_sub_norm_le (ωBase P m : ℂ) (-z)
      rw [sub_neg_eq_add, add_comm, norm_neg, Complex.norm_real, Real.norm_of_nonneg hω_pos.le] at htri
      dsimp only [r₀] at hzm; linarith
  obtain ⟨C0, hC0_nn, hC0_bd⟩ := P.borelAmp_norm_le 0
  have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  let f0 (m : ℕ) (z : ℂ) : ℂ := P.borelAmp 0 (m + 1) * (2 * z ^ 2 / ((ωBase P m : ℂ) * (z ^ 2 - (ωBase P m : ℂ) ^ 2)))
  let f1 (m : ℕ) (z : ℂ) : ℂ := P.borelAmp 0 (m + 1) * (-4 * z * (ωBase P m : ℂ) / (z ^ 2 - (ωBase P m : ℂ) ^ 2) ^ 2)
  let f2 (m : ℕ) (z : ℂ) : ℂ := P.borelAmp 0 (m + 1) * (2 * (((z - (ωBase P m : ℂ)) ^ 3)⁻¹ - ((z + (ωBase P m : ℂ)) ^ 3)⁻¹))
  -- Step 1: `deriv (∑' m, f0 m) = ∑' m, f1 m` on `ball 0 r₀`.
  have hd1 : ∀ z ∈ Metric.ball (0 : ℂ) r₀, HasDerivAt (fun w => ∑' m : ℕ, f0 m w) (∑' m : ℕ, f1 m z) z := by
    intro z hz
    have hbound1 : ∀ (m : ℕ) (w : ℂ), w ∈ Metric.ball (0 : ℂ) r₀ →
        ‖f1 m w‖ ≤ (C0 * (64 * r₀ / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) *
          ((sigmaNat 1 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 3) := by
      intro m w hw
      obtain ⟨hsub, hadd⟩ := hdist_ball m w hw
      have hω_pos : 0 < ωBase P m := by unfold ωBase; positivity
      have hw_le : ‖w‖ ≤ r₀ := (by simpa [Metric.mem_ball, dist_zero_right] using hw : ‖w‖ < r₀).le
      have hden : (ωBase P m ^ 2 / 4) ^ 2 ≤ ‖(w ^ 2 - (ωBase P m : ℂ) ^ 2) ^ 2‖ := by
        rw [norm_pow, show w ^ 2 - (ωBase P m : ℂ) ^ 2 = (w - (ωBase P m : ℂ)) * (w + (ωBase P m : ℂ)) by ring,
          norm_mul]
        have hmul := mul_le_mul hsub hadd (by positivity) (norm_nonneg _)
        exact pow_le_pow_left₀ (by positivity) (by linarith : ωBase P m ^ 2 / 4 ≤ _) 2
      dsimp only [f1]
      rw [norm_mul, norm_div, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg hω_pos.le]
      have h1 := hC0_bd (m + 1) (Nat.succ_pos _)
      have h2 : 4 * ‖w‖ * ωBase P m / ‖(w ^ 2 - (ωBase P m : ℂ) ^ 2) ^ 2‖ ≤
          4 * r₀ * ωBase P m / (ωBase P m ^ 2 / 4) ^ 2 :=
        div_le_div₀ (by positivity) (by gcongr) (by positivity) hden
      calc ‖P.borelAmp 0 (m + 1)‖ * _
          ≤ (C0 * (sigmaNat 1 (m + 1) : ℝ)) * (4 * r₀ * ωBase P m / (ωBase P m ^ 2 / 4) ^ 2) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (C0 * (64 * r₀ / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) *
              ((sigmaNat 1 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 3) := by
            unfold ωBase
            have hn0 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
            have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
            field_simp [hM.ne', hn0, hpi0]; ring
    refine hasDerivAt_tsum_of_isPreconnected ((summable_sigmaNat_div_pow_two_more 0).mul_left _)
      Metric.isOpen_ball (convex_ball (0 : ℂ) r₀).isPreconnected
      (fun m w hw => by
        obtain ⟨hsub, hadd⟩ := hdist_ball m w hw
        have hω_pos : 0 < ωBase P m := by unfold ωBase; positivity
        have hz1 : w ≠ (ωBase P m : ℂ) := fun h0 => by rw [h0, sub_self, norm_zero] at hsub; linarith
        have hz2 : w ≠ -(ωBase P m : ℂ) := fun h0 => by rw [h0, neg_add_cancel, norm_zero] at hadd; linarith
        exact (hasDerivAt_ker0 (Complex.ofReal_ne_zero.mpr hω_pos.ne') hz1 hz2).const_mul _)
      hbound1 (y₀ := (0 : ℂ)) (Metric.mem_ball_self hr₀_pos)
      (by simp [f0]) hz
  -- Step 2: `deriv (∑' m, f1 m) = ∑' m, f2 m` on `ball 0 r₀`.
  have hd2 : ∀ z ∈ Metric.ball (0 : ℂ) r₀, HasDerivAt (fun w => ∑' m : ℕ, f1 m w) (∑' m : ℕ, f2 m z) z := by
    intro z hz
    have hbound2 : ∀ (m : ℕ) (w : ℂ), w ∈ Metric.ball (0 : ℂ) r₀ →
        ‖f2 m w‖ ≤ (C0 * (32 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) *
          ((sigmaNat 1 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 3) := by
      intro m w hw
      obtain ⟨hsub, hadd⟩ := hdist_ball m w hw
      have hω_pos : 0 < ωBase P m := by unfold ωBase; positivity
      have hinv1 : ‖((w - (ωBase P m : ℂ)) ^ 3)⁻¹‖ ≤ (ωBase P m / 2)⁻¹ ^ 3 := by
        rw [norm_inv, norm_pow, inv_pow]
        exact inv_anti₀ (pow_pos (by positivity) 3) (pow_le_pow_left₀ (by positivity) hsub 3)
      have hinv2 : ‖((w + (ωBase P m : ℂ)) ^ 3)⁻¹‖ ≤ (ωBase P m / 2)⁻¹ ^ 3 := by
        rw [norm_inv, norm_pow, inv_pow]
        exact inv_anti₀ (pow_pos (by positivity) 3) (pow_le_pow_left₀ (by positivity) hadd 3)
      dsimp only [f2]
      rw [norm_mul, norm_mul, Complex.norm_ofNat]
      have htri : ‖((w - (ωBase P m : ℂ)) ^ 3)⁻¹ - ((w + (ωBase P m : ℂ)) ^ 3)⁻¹‖ ≤
          2 * (ωBase P m / 2)⁻¹ ^ 3 := by
        calc _ ≤ ‖((w - (ωBase P m : ℂ)) ^ 3)⁻¹‖ + ‖((w + (ωBase P m : ℂ)) ^ 3)⁻¹‖ := norm_sub_le _ _
          _ ≤ (ωBase P m / 2)⁻¹ ^ 3 + (ωBase P m / 2)⁻¹ ^ 3 := add_le_add hinv1 hinv2
          _ = 2 * (ωBase P m / 2)⁻¹ ^ 3 := by ring
      calc ‖P.borelAmp 0 (m + 1)‖ * (2 * ‖_‖)
          ≤ (C0 * (sigmaNat 1 (m + 1) : ℝ)) * (2 * (2 * (ωBase P m / 2)⁻¹ ^ 3)) :=
            mul_le_mul (hC0_bd (m + 1) (Nat.succ_pos _)) (mul_le_mul_of_nonneg_left htri (by positivity))
              (by positivity) (by positivity)
        _ = (C0 * (32 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 3)) *
              ((sigmaNat 1 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 3) := by
            unfold ωBase
            have hn0 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
            have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
            field_simp [hM.ne', hn0, hpi0]; ring
    refine hasDerivAt_tsum_of_isPreconnected ((summable_sigmaNat_div_pow_two_more 0).mul_left _)
      Metric.isOpen_ball (convex_ball (0 : ℂ) r₀).isPreconnected
      (fun m w hw => by
        obtain ⟨hsub, hadd⟩ := hdist_ball m w hw
        have hω_pos : 0 < ωBase P m := by unfold ωBase; positivity
        have hz1 : w ≠ (ωBase P m : ℂ) := fun h0 => by rw [h0, sub_self, norm_zero] at hsub; linarith
        have hz2 : w ≠ -(ωBase P m : ℂ) := fun h0 => by rw [h0, neg_add_cancel, norm_zero] at hadd; linarith
        exact (hasDerivAt_ker0_deriv hz1 hz2).const_mul _)
      hbound2 (y₀ := (0 : ℂ)) (Metric.mem_ball_self hr₀_pos)
      (by simp [f1]) hz
  -- Therefore `deriv (ΦSimple0 P) =ᶠ[𝓝 0] (1/2) * borelPref 0 * ∑' m, f1 m` and `deriv^[2] (ΦSimple0 P) =ᶠ[𝓝 0] borelPhi P`!
  have hPhi_d1 : deriv (ΦSimple0 P) =ᶠ[𝓝 (0 : ℂ)] fun z => (1 / 2 : ℂ) * borelPref 0 * ∑' m : ℕ, f1 m z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₀_pos)] with z hz
    exact ((hd1 z hz).const_mul ((1 / 2 : ℂ) * borelPref 0)).deriv
  have hPhi_d2 : iteratedDeriv 2 (ΦSimple0 P) =ᶠ[𝓝 (0 : ℂ)] borelPhi P := by
    have h1 : deriv (deriv (ΦSimple0 P)) =ᶠ[𝓝 (0 : ℂ)] deriv (fun z => (1 / 2 : ℂ) * borelPref 0 * ∑' m : ℕ, f1 m z) :=
      hPhi_d1.deriv
    filter_upwards [h1, Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₀_pos)] with z hz1 hz2
    rw [iteratedDeriv_succ, iteratedDeriv_one, hz1, ((hd2 z hz2).const_mul ((1 / 2 : ℂ) * borelPref 0)).deriv]
    unfold borelPhi
    rw [← tsum_mul_left]
    refine tsum_congr fun m => ?_
    unfold borelTerm
    have hsum_d : (∑ d : Fin (P.D + 1), borelPref d.1 * P.borelAmp d (m + 1) *
        (((z - (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹ + (-1 : ℂ) ^ (d.1 + 1) * ((z + (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹)) =
        borelPref 0 * P.borelAmp 0 (m + 1) *
          (((z - (ωBase P m : ℂ)) ^ 3)⁻¹ - ((z + (ωBase P m : ℂ)) ^ 3)⁻¹) := by
      have huniv : (Finset.univ : Finset (Fin (P.D + 1))) = {0} := by
        ext ⟨k, hk⟩
        simp only [Finset.mem_univ, Finset.mem_singleton, Fin.ext_iff, Fin.val_zero, true_iff]
        rw [hD] at hk
        omega
      rw [huniv, Finset.sum_singleton]
      simp [sub_eq_add_neg]
    rw [hsum_d]; dsimp only [f2]; ring
  have h0_zero : ΦSimple0 P 0 = 0 := by simp [ΦSimple0]
  have h1_zero : deriv (ΦSimple0 P) 0 = 0 := by
    rw [hPhi_d1.self_of_nhds]; simp [f1]
  ext n
  rcases n with _ | _ | _ | k
  · simp [formalSeries, PowerSeries.coeff_X_pow_mul']
  · simp [formalSeries, h0_zero, PowerSeries.coeff_X_pow_mul']
  · simp [formalSeries, iteratedDeriv_one, h1_zero, PowerSeries.coeff_X_pow_mul']
  · simp only [formalSeries, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul']
    split_ifs with hle
    · rw [show k + 3 - 2 = k + 1 by omega]
      rw [iteratedDeriv_add_nat' k 2 (ΦSimple0 P)]
      exact hPhi_d2.iteratedDeriv_eq k
    · omega

/-- **Exact Formal-Series Identity for `ΦSimple1 P hD`** (`P.D = 1`, `P.c 0 = 0`):
`formalSeries (ΦSimple1 P hD) = PowerSeries.X ^ 3 * formalSeries (borelPhi P)`. -/
private lemma formalSeries_ΦSimple1 (P : Quasipoly) (hD : P.D = 1) (hc0 : ∀ r, P.c 0 r = 0) :
    formalSeries (ΦSimple1 P hD) = PowerSeries.X ^ 3 * formalSeries (borelPhi P) := by
  let d1 : Fin (P.D + 1) := ⟨1, by omega⟩
  let r₀ : ℝ := ωBase P 0 / 2
  have hr₀_pos : 0 < r₀ := half_pos (ωBase_pos' P 0)
  have hdist_ball : ∀ (m : ℕ) (z : ℂ), z ∈ Metric.ball (0 : ℂ) r₀ →
      ωBase P m / 2 ≤ ‖z - (ωBase P m : ℂ)‖ ∧ ωBase P m / 2 ≤ ‖z + (ωBase P m : ℂ)‖ := by
    intro m z hz
    have hzm : ‖z‖ < r₀ := by simpa [Metric.mem_ball, dist_zero_right] using hz
    have hω_ge : ωBase P 0 ≤ ωBase P m := by
      unfold ωBase; have : (0 : ℝ) < P.M := by exact_mod_cast P.hM
      have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
      gcongr; simp
    have hω_pos : 0 < ωBase P m := ωBase_pos' P m
    constructor
    · have htri := norm_sub_norm_le (ωBase P m : ℂ) z
      rw [norm_sub_rev, Complex.norm_real, Real.norm_of_nonneg hω_pos.le] at htri
      dsimp only [r₀] at hzm; linarith
    · have htri := norm_sub_norm_le (ωBase P m : ℂ) (-z)
      rw [sub_neg_eq_add, add_comm, norm_neg, Complex.norm_real, Real.norm_of_nonneg hω_pos.le] at htri
      dsimp only [r₀] at hzm; linarith
  obtain ⟨C1, hC1_nn, hC1_bd⟩ := P.borelAmp_norm_le d1
  have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  let f0 (m : ℕ) (z : ℂ) : ℂ := P.borelAmp d1 (m + 1) * (2 * z ^ 3 / ((ωBase P m : ℂ) ^ 2 * (z ^ 2 - (ωBase P m : ℂ) ^ 2)))
  let f1 (m : ℕ) (z : ℂ) : ℂ := P.borelAmp d1 (m + 1) * (2 * z ^ 2 * (z ^ 2 - 3 * (ωBase P m : ℂ) ^ 2) / ((ωBase P m : ℂ) ^ 2 * (z ^ 2 - (ωBase P m : ℂ) ^ 2) ^ 2))
  let f2 (m : ℕ) (z : ℂ) : ℂ := P.borelAmp d1 (m + 1) * (4 * z * (z ^ 2 + 3 * (ωBase P m : ℂ) ^ 2) / (z ^ 2 - (ωBase P m : ℂ) ^ 2) ^ 3)
  let f3 (m : ℕ) (z : ℂ) : ℂ := P.borelAmp d1 (m + 1) * (-6 * (((z - (ωBase P m : ℂ)) ^ 4)⁻¹ + ((z + (ωBase P m : ℂ)) ^ 4)⁻¹))
  have hr₀_le_ω : ∀ m : ℕ, r₀ ≤ ωBase P m := fun m => by
    have hω_ge : ωBase P 0 ≤ ωBase P m := by
      unfold ωBase
      have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
      have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
      gcongr; simp
    dsimp only [r₀]; linarith [hω_ge, ωBase_pos' P 0]
  -- Step 1: `deriv (∑' m, f0 m) = ∑' m, f1 m` on `ball 0 r₀`.
  have hd1 : ∀ z ∈ Metric.ball (0 : ℂ) r₀, HasDerivAt (fun w => ∑' m : ℕ, f0 m w) (∑' m : ℕ, f1 m z) z := by
    intro z hz
    have hbound1 : ∀ (m : ℕ) (w : ℂ), w ∈ Metric.ball (0 : ℂ) r₀ →
        ‖f1 m w‖ ≤ (C1 * (128 * r₀ ^ 2 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 4)) *
          ((sigmaNat 2 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 4) := by
      intro m w hw
      obtain ⟨hsub, hadd⟩ := hdist_ball m w hw
      have hω_pos : 0 < ωBase P m := by unfold ωBase; positivity
      have hw_le : ‖w‖ ≤ r₀ := (by simpa [Metric.mem_ball, dist_zero_right] using hw : ‖w‖ < r₀).le
      have hw_le_ω : ‖w‖ ≤ ωBase P m := hw_le.trans (hr₀_le_ω m)
      have hnum : ‖2 * w ^ 2 * (w ^ 2 - 3 * (ωBase P m : ℂ) ^ 2)‖ ≤ 8 * r₀ ^ 2 * ωBase P m ^ 2 := by
        rw [norm_mul, norm_mul, Complex.norm_ofNat, norm_pow]
        have htri : ‖w ^ 2 - 3 * (ωBase P m : ℂ) ^ 2‖ ≤ 4 * ωBase P m ^ 2 := by
          calc _ ≤ ‖w ^ 2‖ + ‖3 * (ωBase P m : ℂ) ^ 2‖ := norm_sub_le _ _
            _ = ‖w‖ ^ 2 + 3 * ωBase P m ^ 2 := by
                rw [norm_pow, norm_mul, Complex.norm_ofNat, norm_pow, Complex.norm_real, Real.norm_of_nonneg hω_pos.le]
            _ ≤ ωBase P m ^ 2 + 3 * ωBase P m ^ 2 := by nlinarith [hw_le_ω, norm_nonneg w, hω_pos]
            _ = 4 * ωBase P m ^ 2 := by ring
        calc 2 * ‖w‖ ^ 2 * ‖w ^ 2 - 3 * (ωBase P m : ℂ) ^ 2‖
            ≤ 2 * r₀ ^ 2 * (4 * ωBase P m ^ 2) :=
              mul_le_mul (by gcongr) htri (norm_nonneg _) (by positivity)
          _ = 8 * r₀ ^ 2 * ωBase P m ^ 2 := by ring
      have hden : ωBase P m ^ 6 / 16 ≤ ‖(ωBase P m : ℂ) ^ 2 * (w ^ 2 - (ωBase P m : ℂ) ^ 2) ^ 2‖ := by
        rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_of_nonneg hω_pos.le,
          show w ^ 2 - (ωBase P m : ℂ) ^ 2 = (w - (ωBase P m : ℂ)) * (w + (ωBase P m : ℂ)) by ring, norm_mul]
        have hmul := mul_le_mul hsub hadd (by positivity) (norm_nonneg _)
        have hsq : (ωBase P m ^ 2 / 4) ^ 2 ≤ (‖w - (ωBase P m : ℂ)‖ * ‖w + (ωBase P m : ℂ)‖) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 2
        calc ωBase P m ^ 6 / 16 = ωBase P m ^ 2 * (ωBase P m ^ 2 / 4) ^ 2 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hsq (by positivity)
      dsimp only [f1]
      rw [norm_mul, norm_div]
      calc ‖P.borelAmp d1 (m + 1)‖ * _
          ≤ (C1 * (sigmaNat 2 (m + 1) : ℝ)) * (8 * r₀ ^ 2 * ωBase P m ^ 2 / (ωBase P m ^ 6 / 16)) :=
            mul_le_mul (hC1_bd (m + 1) (Nat.succ_pos _))
              (div_le_div₀ (by positivity) hnum (by positivity) hden) (by positivity) (by positivity)
        _ = (C1 * (128 * r₀ ^ 2 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 4)) *
              ((sigmaNat 2 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 4) := by
            unfold ωBase
            have hn0 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
            have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
            field_simp [hM.ne', hn0, hpi0]; ring
    refine hasDerivAt_tsum_of_isPreconnected ((summable_sigmaNat_div_pow_two_more 1).mul_left _)
      Metric.isOpen_ball (convex_ball (0 : ℂ) r₀).isPreconnected
      (fun m w hw => by
        obtain ⟨hsub, hadd⟩ := hdist_ball m w hw
        have hω_pos : 0 < ωBase P m := by unfold ωBase; positivity
        have hz1 : w ≠ (ωBase P m : ℂ) := fun h0 => by rw [h0, sub_self, norm_zero] at hsub; linarith
        have hz2 : w ≠ -(ωBase P m : ℂ) := fun h0 => by rw [h0, neg_add_cancel, norm_zero] at hadd; linarith
        exact (hasDerivAt_ker1 (Complex.ofReal_ne_zero.mpr hω_pos.ne') hz1 hz2).const_mul _)
      hbound1 (y₀ := (0 : ℂ)) (Metric.mem_ball_self hr₀_pos)
      (by simp [f0]) hz
  -- Step 2: `deriv (∑' m, f1 m) = ∑' m, f2 m` on `ball 0 r₀`.
  have hd2 : ∀ z ∈ Metric.ball (0 : ℂ) r₀, HasDerivAt (fun w => ∑' m : ℕ, f1 m w) (∑' m : ℕ, f2 m z) z := by
    intro z hz
    have hbound2 : ∀ (m : ℕ) (w : ℂ), w ∈ Metric.ball (0 : ℂ) r₀ →
        ‖f2 m w‖ ≤ (C1 * (1024 * r₀ / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 4)) *
          ((sigmaNat 2 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 4) := by
      intro m w hw
      obtain ⟨hsub, hadd⟩ := hdist_ball m w hw
      have hω_pos : 0 < ωBase P m := by unfold ωBase; positivity
      have hw_le : ‖w‖ ≤ r₀ := (by simpa [Metric.mem_ball, dist_zero_right] using hw : ‖w‖ < r₀).le
      have hw_le_ω : ‖w‖ ≤ ωBase P m := hw_le.trans (hr₀_le_ω m)
      have hnum : ‖4 * w * (w ^ 2 + 3 * (ωBase P m : ℂ) ^ 2)‖ ≤ 16 * r₀ * ωBase P m ^ 2 := by
        rw [norm_mul, norm_mul, Complex.norm_ofNat]
        have htri : ‖w ^ 2 + 3 * (ωBase P m : ℂ) ^ 2‖ ≤ 4 * ωBase P m ^ 2 := by
          calc _ ≤ ‖w ^ 2‖ + ‖3 * (ωBase P m : ℂ) ^ 2‖ := norm_add_le _ _
            _ = ‖w‖ ^ 2 + 3 * ωBase P m ^ 2 := by
                rw [norm_pow, norm_mul, Complex.norm_ofNat, norm_pow, Complex.norm_real, Real.norm_of_nonneg hω_pos.le]
            _ ≤ ωBase P m ^ 2 + 3 * ωBase P m ^ 2 := by nlinarith [hw_le_ω, norm_nonneg w, hω_pos]
            _ = 4 * ωBase P m ^ 2 := by ring
        calc 4 * ‖w‖ * ‖w ^ 2 + 3 * (ωBase P m : ℂ) ^ 2‖
            ≤ 4 * r₀ * (4 * ωBase P m ^ 2) :=
              mul_le_mul (by linarith) htri (norm_nonneg _) (by positivity)
          _ = 16 * r₀ * ωBase P m ^ 2 := by ring
      have hden : ωBase P m ^ 6 / 64 ≤ ‖(w ^ 2 - (ωBase P m : ℂ) ^ 2) ^ 3‖ := by
        rw [norm_pow, show w ^ 2 - (ωBase P m : ℂ) ^ 2 = (w - (ωBase P m : ℂ)) * (w + (ωBase P m : ℂ)) by ring, norm_mul]
        have hmul := mul_le_mul hsub hadd (by positivity) (norm_nonneg _)
        have hcu : (ωBase P m ^ 2 / 4) ^ 3 ≤ (‖w - (ωBase P m : ℂ)‖ * ‖w + (ωBase P m : ℂ)‖) ^ 3 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 3
        linarith [show (ωBase P m ^ 2 / 4) ^ 3 = ωBase P m ^ 6 / 64 by ring]
      dsimp only [f2]
      rw [norm_mul, norm_div]
      calc ‖P.borelAmp d1 (m + 1)‖ * _
          ≤ (C1 * (sigmaNat 2 (m + 1) : ℝ)) * (16 * r₀ * ωBase P m ^ 2 / (ωBase P m ^ 6 / 64)) :=
            mul_le_mul (hC1_bd (m + 1) (Nat.succ_pos _))
              (div_le_div₀ (by positivity) hnum (by positivity) hden) (by positivity) (by positivity)
        _ = (C1 * (1024 * r₀ / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 4)) *
              ((sigmaNat 2 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 4) := by
            unfold ωBase
            have hn0 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
            have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
            field_simp [hM.ne', hn0, hpi0]; ring
    refine hasDerivAt_tsum_of_isPreconnected ((summable_sigmaNat_div_pow_two_more 1).mul_left _)
      Metric.isOpen_ball (convex_ball (0 : ℂ) r₀).isPreconnected
      (fun m w hw => by
        obtain ⟨hsub, hadd⟩ := hdist_ball m w hw
        have hω_pos : 0 < ωBase P m := by unfold ωBase; positivity
        have hz1 : w ≠ (ωBase P m : ℂ) := fun h0 => by rw [h0, sub_self, norm_zero] at hsub; linarith
        have hz2 : w ≠ -(ωBase P m : ℂ) := fun h0 => by rw [h0, neg_add_cancel, norm_zero] at hadd; linarith
        exact (hasDerivAt_ker1_deriv1 (Complex.ofReal_ne_zero.mpr hω_pos.ne') hz1 hz2).const_mul _)
      hbound2 (y₀ := (0 : ℂ)) (Metric.mem_ball_self hr₀_pos)
      (by simp [f1]) hz
  -- Step 3: `deriv (∑' m, f2 m) = ∑' m, f3 m` on `ball 0 r₀`.
  have hd3 : ∀ z ∈ Metric.ball (0 : ℂ) r₀, HasDerivAt (fun w => ∑' m : ℕ, f2 m w) (∑' m : ℕ, f3 m z) z := by
    intro z hz
    have hbound3 : ∀ (m : ℕ) (w : ℂ), w ∈ Metric.ball (0 : ℂ) r₀ →
        ‖f3 m w‖ ≤ (C1 * (192 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 4)) *
          ((sigmaNat 2 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 4) := by
      intro m w hw
      obtain ⟨hsub, hadd⟩ := hdist_ball m w hw
      have hω_pos : 0 < ωBase P m := by unfold ωBase; positivity
      have hinv1 : ‖((w - (ωBase P m : ℂ)) ^ 4)⁻¹‖ ≤ (ωBase P m / 2)⁻¹ ^ 4 := by
        rw [norm_inv, norm_pow, inv_pow]
        exact inv_anti₀ (pow_pos (by positivity) 4) (pow_le_pow_left₀ (by positivity) hsub 4)
      have hinv2 : ‖((w + (ωBase P m : ℂ)) ^ 4)⁻¹‖ ≤ (ωBase P m / 2)⁻¹ ^ 4 := by
        rw [norm_inv, norm_pow, inv_pow]
        exact inv_anti₀ (pow_pos (by positivity) 4) (pow_le_pow_left₀ (by positivity) hadd 4)
      dsimp only [f3]
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_ofNat]
      have htri : ‖((w - (ωBase P m : ℂ)) ^ 4)⁻¹ + ((w + (ωBase P m : ℂ)) ^ 4)⁻¹‖ ≤
          2 * (ωBase P m / 2)⁻¹ ^ 4 := by
        calc _ ≤ ‖((w - (ωBase P m : ℂ)) ^ 4)⁻¹‖ + ‖((w + (ωBase P m : ℂ)) ^ 4)⁻¹‖ := norm_add_le _ _
          _ ≤ (ωBase P m / 2)⁻¹ ^ 4 + (ωBase P m / 2)⁻¹ ^ 4 := add_le_add hinv1 hinv2
          _ = 2 * (ωBase P m / 2)⁻¹ ^ 4 := by ring
      calc ‖P.borelAmp d1 (m + 1)‖ * (6 * ‖_‖)
          ≤ (C1 * (sigmaNat 2 (m + 1) : ℝ)) * (6 * (2 * (ωBase P m / 2)⁻¹ ^ 4)) :=
            mul_le_mul (hC1_bd (m + 1) (Nat.succ_pos _)) (mul_le_mul_of_nonneg_left htri (by positivity))
              (by positivity) (by positivity)
        _ = (C1 * (192 / (4 * Real.pi ^ 2 / (P.M : ℝ)) ^ 4)) *
              ((sigmaNat 2 (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 4) := by
            unfold ωBase
            have hn0 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
            have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
            field_simp [hM.ne', hn0, hpi0]; ring
    refine hasDerivAt_tsum_of_isPreconnected ((summable_sigmaNat_div_pow_two_more 1).mul_left _)
      Metric.isOpen_ball (convex_ball (0 : ℂ) r₀).isPreconnected
      (fun m w hw => by
        obtain ⟨hsub, hadd⟩ := hdist_ball m w hw
        have hω_pos : 0 < ωBase P m := by unfold ωBase; positivity
        have hz1 : w ≠ (ωBase P m : ℂ) := fun h0 => by rw [h0, sub_self, norm_zero] at hsub; linarith
        have hz2 : w ≠ -(ωBase P m : ℂ) := fun h0 => by rw [h0, neg_add_cancel, norm_zero] at hadd; linarith
        exact (hasDerivAt_ker1_deriv2 hz1 hz2).const_mul _)
      hbound3 (y₀ := (0 : ℂ)) (Metric.mem_ball_self hr₀_pos)
      (by simp [f2]) hz
  have hPhi_d1 : deriv (ΦSimple1 P hD) =ᶠ[𝓝 (0 : ℂ)] fun z => (-(1 / 6) : ℂ) * borelPref 1 * ∑' m : ℕ, f1 m z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₀_pos)] with z hz
    exact ((hd1 z hz).const_mul ((-(1 / 6) : ℂ) * borelPref 1)).deriv
  have hPhi_d2 : iteratedDeriv 2 (ΦSimple1 P hD) =ᶠ[𝓝 (0 : ℂ)] fun z => (-(1 / 6) : ℂ) * borelPref 1 * ∑' m : ℕ, f2 m z := by
    have h1 := hPhi_d1.deriv
    filter_upwards [h1, Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₀_pos)] with z hz1 hz2
    rw [iteratedDeriv_succ, iteratedDeriv_one, hz1]
    exact ((hd2 z hz2).const_mul ((-(1 / 6) : ℂ) * borelPref 1)).deriv
  have hPhi_d3 : iteratedDeriv 3 (ΦSimple1 P hD) =ᶠ[𝓝 (0 : ℂ)] borelPhi P := by
    have h2 := hPhi_d2.deriv
    filter_upwards [h2, Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr₀_pos)] with z hz1 hz2
    rw [iteratedDeriv_succ, hz1, ((hd3 z hz2).const_mul ((-(1 / 6) : ℂ) * borelPref 1)).deriv]
    unfold borelPhi
    rw [← tsum_mul_left]
    refine tsum_congr fun m => ?_
    unfold borelTerm
    have hamp0 : P.borelAmp 0 (m + 1) = 0 := by
      unfold Quasipoly.borelAmp
      refine Finset.sum_eq_zero fun k _ => ?_
      have hc0_dft : P.cDft 0 k = 0 := by
        unfold Quasipoly.cDft
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun r _ => ?_)
        have hodd0 : P.cOdd 0 r = 0 := by
          unfold Quasipoly.cOdd; simp [hc0]
        rw [hodd0, zero_mul]
      rw [hc0_dft, mul_zero]
    have hsum_d : (∑ d : Fin (P.D + 1), borelPref d.1 * P.borelAmp d (m + 1) *
        (((z - (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹ + (-1 : ℂ) ^ (d.1 + 1) * ((z + (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹)) =
        borelPref 1 * P.borelAmp d1 (m + 1) *
          (((z - (ωBase P m : ℂ)) ^ 4)⁻¹ + ((z + (ωBase P m : ℂ)) ^ 4)⁻¹) := by
      have huniv : (Finset.univ : Finset (Fin (P.D + 1))) = {0, d1} := by
        ext ⟨k, hk⟩
        simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.val_zero, d1, true_iff]
        rw [hD] at hk
        omega
      have h0ne : (0 : Fin (P.D + 1)) ≠ d1 := by intro h; have := congrArg Fin.val h; simp [d1] at this
      rw [huniv, Finset.sum_pair h0ne, hamp0, mul_zero, zero_mul, zero_add]
      simp [d1]
    rw [hsum_d]; dsimp only [f3]; ring
  have h0_zero : ΦSimple1 P hD 0 = 0 := by simp [ΦSimple1]
  have h1_zero : deriv (ΦSimple1 P hD) 0 = 0 := by rw [hPhi_d1.self_of_nhds]; simp [f1]
  have h2_zero : iteratedDeriv 2 (ΦSimple1 P hD) 0 = 0 := by rw [hPhi_d2.self_of_nhds]; simp [f2]
  ext n
  rcases n with _ | _ | _ | _ | k
  · simp [formalSeries, PowerSeries.coeff_X_pow_mul']
  · simp [formalSeries, h0_zero, PowerSeries.coeff_X_pow_mul']
  · simp [formalSeries, iteratedDeriv_one, h1_zero, PowerSeries.coeff_X_pow_mul']
  · simp [formalSeries, h2_zero, PowerSeries.coeff_X_pow_mul']
  · simp only [formalSeries, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul']
    split_ifs with hle
    · rw [show k + 4 - 3 = k + 1 by omega]
      rw [iteratedDeriv_add_nat' k 3 (ΦSimple1 P hD)]
      exact hPhi_d3.iteratedDeriv_eq k
    · omega

/-! ##### Asymptotic Remainder Helper for `u^{-N} * g(u)` and Concrete Remainders for the 3-Tuple -/

private lemma hasAsympExp_inv_pow' (k : ℕ) :
    HasAsympExp (fun u : ℝ => (u : ℂ)⁻¹ ^ k) (PowerSeries.X ^ k) := by
  intro M
  refine ⟨1, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu1
  have hu : 0 < u := by linarith
  have hsum : ∑ n ∈ Finset.range M, PowerSeries.coeff n (PowerSeries.X ^ k : PowerSeries ℂ) *
      (u : ℂ)⁻¹ ^ n = if k < M then (u : ℂ)⁻¹ ^ k else 0 := by
    simp_rw [PowerSeries.coeff_X_pow]
    split_ifs with hkM
    · rw [Finset.sum_eq_single k]
      · simp
      · intro b _ hbk; simp [hbk]
      · intro hnot; exact absurd (Finset.mem_range.mpr hkM) hnot
    · refine Finset.sum_eq_zero fun b hb => ?_
      have hne : b ≠ k := by have := Finset.mem_range.mp hb; omega
      simp [hne]
  rw [hsum]
  split_ifs with hkM
  · simp [sub_self, pow_nonneg hu.le M]
  · have hle : M ≤ k := by omega
    rw [sub_zero, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu,
      _root_.inv_pow, one_div]
    exact inv_anti₀ (pow_pos hu M) (pow_le_pow_right₀ hu1 hle)

private lemma hasDerivAt_inv_pow_complex' {j : ℕ} {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun v : ℝ => (v : ℂ)⁻¹ ^ j) (-(j : ℂ) * (y : ℂ)⁻¹ ^ (j + 1)) y := by
  have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy
  have hinv : HasDerivAt (fun v : ℝ => (v : ℂ)⁻¹) (-(y : ℂ)⁻¹ ^ 2) y := by
    have h := ((hasDerivAt_id y).ofReal_comp).inv hyc
    refine h.congr_deriv ?_; simp [div_eq_mul_inv, inv_pow]
  have hpow := hinv.pow j
  refine hpow.congr_deriv ?_
  cases j with
  | zero => simp
  | succ k => rw [pow_succ (y : ℂ)⁻¹ (k + 1), pow_succ (y : ℂ)⁻¹ k]; push_cast; ring

private lemma d_u_X_pow_mul (N : ℕ) (S : PowerSeries ℂ) :
    d_u (PowerSeries.X ^ N * S) =
      PowerSeries.C (-(N : ℂ)) * (PowerSeries.X ^ (N + 1) * S) + PowerSeries.X ^ N * d_u S := by
  unfold d_u
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have hdX : PowerSeries.derivative (PowerSeries.X ^ N : PowerSeries ℂ) =
      PowerSeries.C (N : ℂ) * PowerSeries.X ^ (N - 1) := by
    cases N with
    | zero => simp
    | succ m =>
      rw [Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul, PowerSeries.derivative_X, mul_one,
        PowerSeries.C_eq_algebraMap, map_natCast]
  rw [hdX]
  cases N with
  | zero => simp
  | succ m =>
    rw [Nat.succ_sub_one, pow_succ (PowerSeries.X : PowerSeries ℂ) (m + 1),
      pow_succ (PowerSeries.X : PowerSeries ℂ) m, map_neg]
    ring

private lemma hasAsympExp_inv_pow_mul_iteratedDeriv (j : ℕ) :
    ∀ (N : ℕ) {g : ℝ → ℂ} {S : PowerSeries ℂ},
      (∀ k : ℕ, ContDiffOn ℝ k g (Ioi (0 : ℝ))) →
      (∀ k : ℕ, HasAsympExp (iteratedDeriv k g) (d_u^[k] S)) →
      HasAsympExp (iteratedDeriv j (fun u : ℝ => (u : ℂ)⁻¹ ^ N * g u))
        (d_u^[j] (PowerSeries.X ^ N * S)) := by
  induction j with
  | zero =>
    intro N g S _ hg
    simpa using (hasAsympExp_inv_pow' N).mul (hg 0)
  | succ j ih =>
    intro N g S hcd hg
    have hderiv_eq : ∀ u : ℝ, 0 < u →
        deriv (fun t : ℝ => (t : ℂ)⁻¹ ^ N * g t) u =
          (-(N : ℂ)) * ((u : ℂ)⁻¹ ^ (N + 1) * g u) + (u : ℂ)⁻¹ ^ N * deriv g u := by
      intro u hu
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)⁻¹ ^ N) (-(N : ℂ) * (u : ℂ)⁻¹ ^ (N + 1)) u :=
        hasDerivAt_inv_pow_complex' hu.ne'
      have h2 : HasDerivAt g (deriv g u) u :=
        ((contDiffOn_Ioi_iteratedDeriv_diffAt hcd 0 hu)).hasDerivAt
      simpa [mul_assoc] using (h1.fun_mul h2).deriv
    have hev : iteratedDeriv (j + 1) (fun u : ℝ => (u : ℂ)⁻¹ ^ N * g u) =ᶠ[atTop]
        fun u : ℝ => (-(N : ℂ)) * iteratedDeriv j (fun t : ℝ => (t : ℂ)⁻¹ ^ (N + 1) * g t) u +
          iteratedDeriv j (fun t : ℝ => (t : ℂ)⁻¹ ^ N * deriv g t) u := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      have hnhds : deriv (fun t : ℝ => (t : ℂ)⁻¹ ^ N * g t) =ᶠ[𝓝 u]
          fun t : ℝ => (-(N : ℂ)) * ((t : ℂ)⁻¹ ^ (N + 1) * g t) + (t : ℂ)⁻¹ ^ N * deriv g t := by
        filter_upwards [Ioi_mem_nhds hu] with t ht
        exact hderiv_eq t ht
      rw [iteratedDeriv_succ', hnhds.iteratedDeriv_eq j]
      have hcd_inv : ∀ m : ℕ, ContDiffAt ℝ j (fun t : ℝ => (t : ℂ)⁻¹ ^ m) u := fun m =>
        (((Complex.ofRealCLM.contDiff.contDiffAt.inv (Complex.ofReal_ne_zero.mpr hu.ne')).pow m).of_le le_top)
      have hcd_g : ContDiffAt ℝ j g u := (hcd j).contDiffAt (isOpen_Ioi.mem_nhds hu)
      have hcd_dg : ContDiffAt ℝ j (deriv g) u := by
        have h1 : ContDiffOn ℝ ((j + 1 : ℕ) : WithTop ℕ∞) g (Ioi (0 : ℝ)) := hcd (j + 1)
        have h2 : ContDiffOn ℝ j (deriv g) (Ioi (0 : ℝ)) :=
          ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).mp (by simpa [Nat.cast_add] using h1)).2.2
        exact h2.contDiffAt (isOpen_Ioi.mem_nhds hu)
      rw [iteratedDeriv_fun_add ((contDiffAt_const.mul ((hcd_inv (N + 1)).mul hcd_g))) ((hcd_inv N).mul hcd_dg),
        iteratedDeriv_const_mul _ ((hcd_inv (N + 1)).mul hcd_g)]
    have hcd_dg_on : ∀ k : ℕ, ContDiffOn ℝ k (deriv g) (Ioi (0 : ℝ)) := fun k => by
      have h1 : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) g (Ioi (0 : ℝ)) := hcd (k + 1)
      exact ((contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).mp (by simpa [Nat.cast_add] using h1)).2.2
    have hdg_asymp : ∀ k : ℕ, HasAsympExp (iteratedDeriv k (deriv g)) (d_u^[k] (d_u S)) := fun k => by
      have hEq : iteratedDeriv k (deriv g) = iteratedDeriv (k + 1) g := (iteratedDeriv_succ' (f := g)).symm
      rw [hEq, ← Function.iterate_succ_apply d_u k S]
      exact hg (k + 1)
    have hA := (HasAsympExp.const (-(N : ℂ))).mul (ih (N + 1) hcd hg)
    have hB := ih N hcd_dg_on hdg_asymp
    have hS_eq : d_u^[j + 1] (PowerSeries.X ^ N * S) =
        PowerSeries.C (-(N : ℂ)) * d_u^[j] (PowerSeries.X ^ (N + 1) * S) +
          d_u^[j] (PowerSeries.X ^ N * d_u S) := by
      rw [Function.iterate_succ_apply, d_u_X_pow_mul]
      have hd_add : ∀ n (A B : PowerSeries ℂ), d_u^[n] (A + B) = d_u^[n] A + d_u^[n] B := fun n => by
        induction n with
        | zero => intro A B; rfl
        | succ n ihn =>
          intro A B
          simp only [Function.iterate_succ_apply', ihn]
          unfold d_u; rw [map_add]; ring
      have hd_C : ∀ n (c : ℂ) (A : PowerSeries ℂ), d_u^[n] (PowerSeries.C c * A) = PowerSeries.C c * d_u^[n] A := fun n c => by
        induction n with
        | zero => intro A; rfl
        | succ n ihn =>
          intro A
          rw [Function.iterate_succ_apply', ihn, Function.iterate_succ_apply']
          unfold d_u
          rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, PowerSeries.derivative_C, mul_zero, add_zero]
          ring
      rw [hd_add, hd_C]
    rw [hS_eq]
    intro M
    obtain ⟨C, hC⟩ := (hA.add hB) M
    refine ⟨C, ?_⟩
    filter_upwards [hC, hev] with u hu hequ
    simpa only [hequ] using hu

section RemFunAsymp

private lemma expAux_hasFPowerSeriesOnBall' :
    HasFPowerSeriesOnBall expAux
      (.ofScalars ℂ (fun n : ℕ => ((n + 1).factorial : ℂ)⁻¹)) 0 ⊤ := by
  let c : ℕ → ℂ := fun n => ((n + 1).factorial : ℂ)⁻¹
  have hc_ne : ∀ᶠ n : ℕ in atTop, c n ≠ 0 := Eventually.of_forall fun n => by
    dsimp [c]; exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hc_lim : Tendsto (fun n : ℕ => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 0) := by
    have heq : (fun n : ℕ => ‖c n.succ‖ / ‖c n‖) = fun n : ℕ => ((n : ℝ) + 2)⁻¹ := by
      funext n; dsimp [c]
      rw [norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast, Nat.factorial_succ,
        Nat.cast_mul]
      have h1 : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
      have h2 : ((n + 1 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [h1, h2]; push_cast; ring
    rw [heq]
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hrad : (FormalMultilinearSeries.ofScalars ℂ c).radius = ⊤ :=
    FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto ℂ c hc_ne hc_lim
  have hball : HasFPowerSeriesOnBall (FormalMultilinearSeries.ofScalarsSum c)
      (FormalMultilinearSeries.ofScalars ℂ c) 0 ⊤ := by
    rw [← hrad]
    exact (FormalMultilinearSeries.ofScalars ℂ c).hasFPowerSeriesOnBall
      (hrad ▸ (by simp : (0 : ENNReal) < ⊤))
  refine hball.congr fun z _ => ?_
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  refine tsum_congr fun n => by dsimp [c]; simp [div_eq_mul_inv, mul_comm]

private lemma expAux_analytic' (z : ℂ) : AnalyticAt ℂ expAux z :=
  expAux_hasFPowerSeriesOnBall'.analyticOnNhd z (by simp)

private lemma expAux_zero' : expAux 0 = 1 := by
  rw [expAux, tsum_eq_single 0]
  · simp
  · intro n hn; simp [hn]

private lemma expAux_mul_sub' (z : ℂ) : z * expAux z = Complex.exp z - 1 := by
  by_cases hz : z = 0
  · subst hz; simp
  have hsum : HasSum (fun n : ℕ => z ^ n / (n.factorial : ℂ)) (Complex.exp z) := by
    rw [Complex.exp_eq_exp_ℂ]; exact NormedSpace.expSeries_div_hasSum_exp z
  have hsum_tail : HasSum (fun n : ℕ => z ^ (n + 1) / ((n + 1).factorial : ℂ)) (Complex.exp z - 1) := by
    simpa [Finset.sum_range_one] using
      (hasSum_nat_add_iff' (f := fun n : ℕ => z ^ n / (n.factorial : ℂ)) 1).mpr hsum
  have hsum_aux : HasSum (fun n : ℕ => z ^ n / ((n + 1).factorial : ℂ)) (z⁻¹ * (Complex.exp z - 1)) := by
    refine (hsum_tail.mul_left z⁻¹).congr_fun fun n => ?_
    rw [pow_succ']; field_simp [hz]
  rw [expAux, hsum_aux.tsum_eq]; field_simp [hz]

private lemma expAux_ofReal_ne_zero' (x : ℝ) : expAux (x : ℂ) ≠ 0 := by
  by_cases hx0 : x = 0
  · subst hx0; simp [expAux_zero']
  intro h0
  have hmul := expAux_mul_sub' (x : ℂ)
  rw [h0, mul_zero] at hmul
  have hexpR : Real.exp x = 1 := by
    exact_mod_cast (by simpa [← Complex.ofReal_exp] using sub_eq_zero.mp hmul.symm :
      ((Real.exp x : ℝ) : ℂ) = (1 : ℂ))
  rcases lt_or_gt_of_ne hx0 with hlt | hgt
  · exact (Real.exp_lt_one_iff.mpr hlt).ne hexpR
  · exact (Real.one_lt_exp_iff.mpr hgt).ne' hexpR

private lemma qComplex_analytic_ofReal' (x : ℝ) : AnalyticAt ℂ qComplex (x : ℂ) :=
  (expAux_analytic' (x : ℂ)).inv (expAux_ofReal_ne_zero' x)

private lemma qComplex_mul_exp_sub_one' (z : ℂ) (hz : expAux z ≠ 0) :
    qComplex z * (Complex.exp z - 1) = z := by
  rw [qComplex, ← expAux_mul_sub' z]; field_simp [hz]

private lemma qFun_eq_div_exp_sub_one' {x : ℝ} (hx : x ≠ 0) :
    qFun x = (x : ℂ) / (Complex.exp (x : ℂ) - 1) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have h := qComplex_mul_exp_sub_one' (x : ℂ) (expAux_ofReal_ne_zero' x)
  have hden : Complex.exp (x : ℂ) - 1 ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at h; exact hx0 h.symm
  exact eq_div_of_mul_eq hden h


private lemma iteratedDeriv_ofReal_comp' {F : ℂ → ℂ} (hF : ∀ x : ℝ, AnalyticAt ℂ F (x : ℂ)) :
    ∀ (n : ℕ) (x : ℝ), iteratedDeriv n (fun t : ℝ => F (t : ℂ)) x = iteratedDeriv n F (x : ℂ) := by
  intro n
  induction n generalizing F with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    have hderiv : (deriv fun t : ℝ => F (t : ℂ)) = fun t : ℝ => deriv F (t : ℂ) := by
      funext t
      simpa [Function.comp_def] using
        ((hF t).differentiableAt.hasDerivAt.scomp t (hasDerivAt_id t).ofReal_comp).deriv
    rw [hderiv]; exact ih (fun t => (hF t).deriv) x

private lemma eds_deriv {h : ℝ → ℂ} (hh : ExpDecaySmooth h) : ExpDecaySmooth (deriv h) := by
  refine ⟨(contDiff_infty_iff_deriv.mp hh.1).2, fun r => ?_⟩
  obtain ⟨C, c, hC, hc, hbd⟩ := hh.2 (r + 1)
  exact ⟨C, c, hC, hc, fun x hx => by rw [← iteratedDeriv_succ']; exact hbd x hx⟩

private lemma qFun_contDiff' : ContDiff ℝ (⊤ : ℕ∞) qFun :=
  contDiff_iff_contDiffAt.mpr fun x =>
    ((qComplex_analytic_ofReal' x).restrictScalars.contDiffAt.comp x
      (Complex.ofRealCLM.contDiff.contDiffAt)).of_le le_top


private lemma eds_continuous {h : ℝ → ℂ} (hh : ExpDecaySmooth h) : Continuous h :=
  hh.1.continuous

private lemma eds_differentiable {h : ℝ → ℂ} (hh : ExpDecaySmooth h) : Differentiable ℝ h :=
  hh.1.differentiable (by simp)

private lemma eds_iteratedDeriv_smooth {h : ℝ → ℂ} (hh : ExpDecaySmooth h) (r : ℕ) :
    ExpDecaySmooth (iteratedDeriv r h) := by
  induction r with
  | zero => simpa using hh
  | succ r ih => rw [iteratedDeriv_succ]; exact eds_deriv ih

private lemma eds_integrableOn {h : ℝ → ℂ} (hh : ExpDecaySmooth h) (r : ℕ) :
    IntegrableOn (iteratedDeriv r h) (Ioi (0 : ℝ)) := by
  obtain ⟨C, c, hC, hc, hbd⟩ := hh.2 r
  have hdom : IntegrableOn (fun x : ℝ => C * Real.exp (-c * x)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (by linarith : -c < 0) 0).const_mul C
  refine hdom.mono' ((eds_iteratedDeriv_smooth hh r).1.continuous.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact hbd x (le_of_lt hx)

private lemma eds_tendsto_atTop {h : ℝ → ℂ} (hh : ExpDecaySmooth h) (r : ℕ) :
    Tendsto (iteratedDeriv r h) atTop (𝓝 0) := by
  obtain ⟨C, c, hC, hc, hbd⟩ := hh.2 r
  have hlim : Tendsto (fun x : ℝ => C * Real.exp (-c * x)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => -c * x) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul C
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact hbd x hx

private lemma real_mul_exp_neg_le_one' {y : ℝ} : y * Real.exp (-y) ≤ 1 := by
  have h2 : y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (div_le_one (Real.exp_pos y)).mpr h2

private lemma iteratedDeriv_ofReal_ge_two' (k : ℕ) (hk : 2 ≤ k) (x : ℝ) :
    iteratedDeriv k (fun t : ℝ => (t : ℂ)) x = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 2 := ⟨k - 2, by omega⟩
  change iteratedDeriv (m + 2) (fun t : ℝ => (id : ℂ → ℂ) (t : ℂ)) x = 0
  rw [iteratedDeriv_ofReal_comp' (fun _ => analyticAt_id), show m + 2 = (m + 1) + 1 by omega,
    iteratedDeriv_succ', show deriv (id : ℂ → ℂ) = fun _ => 1 from by ext z; simp]
  cases m with
  | zero => simp
  | succ j => simp [iteratedDeriv_const]

private lemma eds_mul_ofReal {h : ℝ → ℂ} (hh : ExpDecaySmooth h) :
    ExpDecaySmooth (fun x => (x : ℂ) * h x) := by
  refine ⟨(Complex.ofRealCLM.contDiff).mul hh.1, fun r => ?_⟩
  have hxe : ∀ (c x : ℝ), 0 < c → 0 ≤ x → x * Real.exp (-c * x) ≤ (2 / c) * Real.exp (-(c / 2) * x) := by
    intro c x hc hx
    have hexp : Real.exp (-c * x) = Real.exp (-((c / 2) * x)) * Real.exp (-(c / 2) * x) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp, ← mul_assoc]
    calc (x * Real.exp (-((c / 2) * x))) * Real.exp (-(c / 2) * x)
        = ((2 / c) * (((c / 2) * x) * Real.exp (-((c / 2) * x)))) * Real.exp (-(c / 2) * x) := by
          field_simp [hc.ne']
      _ ≤ ((2 / c) * 1) * Real.exp (-(c / 2) * x) := by
          gcongr; exact real_mul_exp_neg_le_one'
      _ = (2 / c) * Real.exp (-(c / 2) * x) := by ring
  cases r with
  | zero =>
    obtain ⟨C0, c0, hC0, hc0, hb0⟩ := hh.2 0
    refine ⟨C0 * (2 / c0), c0 / 2, by positivity, by positivity, fun x hx => ?_⟩
    simp only [iteratedDeriv_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
    have h0 : ‖h x‖ ≤ C0 * Real.exp (-c0 * x) := by simpa [iteratedDeriv_zero] using hb0 x hx
    calc x * ‖h x‖ ≤ C0 * (x * Real.exp (-c0 * x)) := by nlinarith
      _ ≤ C0 * ((2 / c0) * Real.exp (-(c0 / 2) * x)) := mul_le_mul_of_nonneg_left (hxe c0 x hc0 hx) hC0
      _ = C0 * (2 / c0) * Real.exp (-(c0 / 2) * x) := by ring
  | succ m =>
    obtain ⟨C0, c0, hC0, hc0, hb0⟩ := hh.2 m
    obtain ⟨C1, c1, hC1, hc1, hb1⟩ := hh.2 (m + 1)
    let c := min c0 (c1 / 2)
    refine ⟨C1 * (2 / c1) + (m + 1 : ℝ) * C0, c, by positivity, lt_min hc0 (by positivity), fun x hx => ?_⟩
    have hleib := iteratedDeriv_fun_mul (f := fun t : ℝ => (t : ℂ)) (g := h) (n := m + 1) (x := x)
      ((Complex.ofRealCLM.contDiff.contDiffAt).of_le le_top)
      (hh.1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
    have hsplit : ∑ i ∈ Finset.range (m + 2),
        ((m + 1).choose i : ℂ) * iteratedDeriv i (fun t : ℝ => (t : ℂ)) x *
          iteratedDeriv (m + 1 - i) h x =
        (x : ℂ) * iteratedDeriv (m + 1) h x + ((m + 1 : ℕ) : ℂ) * iteratedDeriv m h x := by
      rw [Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.sub_zero]
      rw [Finset.sum_range_succ']
      have hd1 : iteratedDeriv 1 (fun t : ℝ => (t : ℂ)) x = 1 := by
        rw [iteratedDeriv_one]; exact (hasDerivAt_id x).ofReal_comp.deriv
      have hzero : ∀ i ∈ Finset.range m,
          ((m + 1).choose (i + 1 + 1) : ℂ) * iteratedDeriv (i + 1 + 1) (fun t : ℝ => (t : ℂ)) x *
            iteratedDeriv (m + 1 - (i + 1 + 1)) h x = 0 := fun i _ => by
        rw [iteratedDeriv_ofReal_ge_two' (i + 1 + 1) (by omega) x, mul_zero, zero_mul]
      rw [Finset.sum_eq_zero hzero, zero_add, Nat.choose_one_right, hd1, mul_one,
        show m + 1 - 1 = m by omega]
      push_cast; ring
    rw [hleib, hsplit]
    have he1 : Real.exp (-(c1 / 2) * x) ≤ Real.exp (-c * x) :=
      Real.exp_le_exp.mpr (by nlinarith [min_le_right c0 (c1 / 2)])
    have he0 : Real.exp (-c0 * x) ≤ Real.exp (-c * x) :=
      Real.exp_le_exp.mpr (by nlinarith [min_le_left c0 (c1 / 2)])
    calc ‖(x : ℂ) * iteratedDeriv (m + 1) h x + ((m + 1 : ℕ) : ℂ) * iteratedDeriv m h x‖
        ≤ ‖(x : ℂ) * iteratedDeriv (m + 1) h x‖ + ‖((m + 1 : ℕ) : ℂ) * iteratedDeriv m h x‖ :=
          norm_add_le _ _
      _ = x * ‖iteratedDeriv (m + 1) h x‖ + (m + 1 : ℝ) * ‖iteratedDeriv m h x‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx,
            Complex.norm_natCast]; push_cast; rfl
      _ ≤ x * (C1 * Real.exp (-c1 * x)) + (m + 1 : ℝ) * (C0 * Real.exp (-c0 * x)) := by
          gcongr; exact hb1 x hx; exact hb0 x hx
      _ = C1 * (x * Real.exp (-c1 * x)) + (m + 1 : ℝ) * C0 * Real.exp (-c0 * x) := by ring
      _ ≤ C1 * ((2 / c1) * Real.exp (-(c1 / 2) * x)) + (m + 1 : ℝ) * C0 * Real.exp (-c0 * x) :=
          add_le_add (mul_le_mul_of_nonneg_left (hxe c1 x hc1 hx) hC1) le_rfl
      _ ≤ C1 * ((2 / c1) * Real.exp (-c * x)) + (m + 1 : ℝ) * C0 * Real.exp (-c * x) := by gcongr
      _ = (C1 * (2 / c1) + (m + 1 : ℝ) * C0) * Real.exp (-c * x) := by ring

private lemma eds_pow_ofReal_mul {h : ℝ → ℂ} (k : ℕ) (hh : ExpDecaySmooth h) :
    ExpDecaySmooth (fun x => (x : ℂ) ^ k * h x) := by
  induction k with
  | zero => simpa using hh
  | succ k ih =>
    rw [show (fun x : ℝ => (x : ℂ) ^ (k + 1) * h x) = fun x : ℝ => (x : ℂ) * ((x : ℂ) ^ k * h x) by
      funext x; rw [pow_succ']; ring]
    exact eds_mul_ofReal ih


private lemma qFun_expDecaySmooth' : ExpDecaySmooth qFun := by
  have hv_poly : ∀ r : ℕ, ∃ P : Polynomial ℝ, ∀ x : ℝ, 0 < x →
      iteratedDeriv r (fun y : ℝ => (Real.exp y - 1)⁻¹) x =
        (Real.exp x - 1)⁻¹ * P.eval ((Real.exp x - 1)⁻¹) := fun r => by
    let v : ℝ → ℝ := fun y => (Real.exp y - 1)⁻¹
    have hv_deriv : ∀ x : ℝ, 0 < x → HasDerivAt v (-(v x + v x ^ 2)) x := fun x hx => by
      have hexp : Real.exp x - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)).ne'
      have h2 : HasDerivAt v (-Real.exp x / (Real.exp x - 1) ^ 2) x :=
        ((Real.hasDerivAt_exp x).sub_const 1).inv hexp
      convert h2 using 1; dsimp [v]; field_simp [hexp]; ring
    induction r with
    | zero => exact ⟨1, fun x _ => by simp⟩
    | succ r ih =>
      obtain ⟨P, hP⟩ := ih
      refine ⟨-(1 + Polynomial.X) * (P + Polynomial.X * P.derivative), fun x hx => ?_⟩
      have heq_nhds : iteratedDeriv r v =ᶠ[𝓝 x] fun y => v y * P.eval (v y) :=
        Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hx) hP
      rw [iteratedDeriv_succ, heq_nhds.deriv_eq]
      have hvd := hv_deriv x hx
      have hPd : HasDerivAt (fun y => P.eval (v y)) (P.derivative.eval (v x) * -(v x + v x ^ 2)) x :=
        (Polynomial.hasDerivAt P (v x)).comp x hvd
      have hmul : deriv (fun y => v y * P.eval (v y)) x =
          -(v x + v x ^ 2) * P.eval (v x) + v x * (P.derivative.eval (v x) * -(v x + v x ^ 2)) :=
        (hvd.mul hPd).deriv
      rw [hmul]
      simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_add, Polynomial.eval_one,
        Polynomial.eval_X]
      ring
  have hpoly_unit : ∀ (P : Polynomial ℝ) {t : ℝ}, 0 ≤ t → t ≤ 1 →
      |P.eval t| ≤ ∑ i ∈ P.support, |P.coeff i| := fun P {t} ht0 ht1 => by
    rw [Polynomial.eval_eq_sum]; dsimp only [Polynomial.sum, Finsupp.sum]
    calc |∑ i ∈ P.support, P.coeff i * t ^ i|
        ≤ ∑ i ∈ P.support, |P.coeff i * t ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ P.support, |P.coeff i| := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_pow, abs_of_nonneg ht0]
          exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ ht0 ht1)
  have hofReal_v : ∀ (k : ℕ) {v : ℝ → ℝ} {x : ℝ}, ContDiffOn ℝ (⊤ : ℕ∞) v (Ioi 0) → 0 < x →
      iteratedDeriv k (fun y : ℝ => (v y : ℂ)) x = ((iteratedDeriv k v x : ℝ) : ℂ) := fun k => by
    induction k with
    | zero => intro _ _ _ _; simp
    | succ k ih =>
      intro v x hv hx
      have hdv : ContDiffOn ℝ (⊤ : ℕ∞) (deriv v) (Ioi 0) :=
        ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp hv).2
      have heq : (deriv fun y : ℝ => (v y : ℂ)) =ᶠ[𝓝 x] fun y : ℝ => ((deriv v y : ℝ) : ℂ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        exact (((hv.differentiableOn (by simp)) y hy).differentiableAt
          (isOpen_Ioi.mem_nhds hy)).hasDerivAt.ofReal_comp.deriv
      rw [iteratedDeriv_succ', heq.iteratedDeriv_eq k, iteratedDeriv_succ']
      exact ih hdv hx
  refine ⟨qFun_contDiff', fun r => ?_⟩
  obtain ⟨P, hP⟩ := hv_poly r
  obtain ⟨P1, hP1⟩ := hv_poly (r - 1)
  let B0 : ℝ := ∑ i ∈ P.support, |P.coeff i|
  let B1 : ℝ := ∑ i ∈ P1.support, |P1.coeff i|
  have hcont_r : ContinuousOn (fun x : ℝ => ‖iteratedDeriv r qFun x‖) (Icc 0 1) :=
    ((qFun_contDiff'.continuous_iteratedDeriv r (WithTop.coe_le_coe.mpr le_top)).norm).continuousOn
  obtain ⟨xm, _, hxm⟩ := isCompact_Icc.exists_isMaxOn ⟨0, left_mem_Icc.mpr zero_le_one⟩ hcont_r
  let M0 : ℝ := ‖iteratedDeriv r qFun xm‖
  let C_tail : ℝ := 2 * B0 * 2 + (r : ℝ) * (2 * B1)
  refine ⟨max (M0 * Real.exp (1 / 2)) C_tail, 1 / 2, by positivity, by norm_num, fun x hx => ?_⟩
  by_cases hx1 : x ≤ 1
  · have hexp : 1 ≤ Real.exp (1 / 2) * Real.exp (-(1 / 2) * x) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    calc ‖iteratedDeriv r qFun x‖ ≤ M0 := hxm ⟨hx, hx1⟩
      _ ≤ M0 * (Real.exp (1 / 2) * Real.exp (-(1 / 2) * x)) := by nlinarith [norm_nonneg (iteratedDeriv r qFun xm)]
      _ = (M0 * Real.exp (1 / 2)) * Real.exp (-(1 / 2) * x) := by ring
      _ ≤ max (M0 * Real.exp (1 / 2)) C_tail * Real.exp (-(1 / 2) * x) := by gcongr; exact le_max_left _ _
  · have hx_gt1 : 1 ≤ x := by linarith
    have hx_pos : 0 < x := by linarith
    let v : ℝ → ℝ := fun y => (Real.exp y - 1)⁻¹
    have hv_le1 : v x ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.add_one_le_exp x])
    have hv_pos : 0 ≤ v x := inv_nonneg.mpr (sub_nonneg.mpr (Real.one_le_exp hx))
    have hv_exp : v x ≤ 2 * Real.exp (-x) := by
      have hge : Real.exp x / 2 ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
      calc (Real.exp x - 1)⁻¹ ≤ (Real.exp x / 2)⁻¹ := inv_anti₀ (by positivity) hge
        _ = 2 * Real.exp (-x) := by rw [Real.exp_neg]; field_simp [(Real.exp_pos x).ne']
    have heq_on : qFun =ᶠ[𝓝 x] fun y : ℝ => (y : ℂ) * ((v y : ℝ) : ℂ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx_pos] with y hy
      rw [qFun_eq_div_exp_sub_one' hy.ne']; simp [v, div_eq_mul_inv, Complex.ofReal_exp]
    have hv_smooth_on : ContDiffOn ℝ (⊤ : ℕ∞) v (Ioi 0) :=
      ContDiffOn.inv ((Real.contDiff_exp.sub contDiff_const).contDiffOn.of_le le_top)
        fun y hy => (sub_pos.mpr (Real.one_lt_exp_iff.mpr hy)).ne'
    have hmul_deriv : iteratedDeriv r qFun x =
        ∑ i ∈ Finset.range (r + 1),
          ((r.choose i : ℂ) * iteratedDeriv i (fun t : ℝ => (t : ℂ)) x *
            iteratedDeriv (r - i) (fun y : ℝ => (v y : ℂ)) x) := by
      rw [heq_on.iteratedDeriv_eq r]
      have h1 : ContDiffAt ℝ r (fun y : ℝ => (v y : ℂ)) x :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp x
          ((hv_smooth_on.contDiffAt (isOpen_Ioi.mem_nhds hx_pos)).of_le (WithTop.coe_le_coe.mpr le_top))
      have hid_cd : ContDiffAt ℝ r (fun t : ℝ => (t : ℂ)) x :=
        Complex.ofRealCLM.contDiff.contDiffAt.of_le le_top
      simpa using iteratedDeriv_fun_mul hid_cd h1
    have hval_r : |iteratedDeriv r v x| ≤ 2 * B0 * Real.exp (-x) := by
      rw [hP x hx_pos, abs_mul, abs_of_nonneg hv_pos]
      calc v x * |P.eval (v x)| ≤ (2 * Real.exp (-x)) * B0 :=
            mul_le_mul hv_exp (hpoly_unit P hv_pos hv_le1) (abs_nonneg _) (by positivity)
        _ = 2 * B0 * Real.exp (-x) := by ring
    have hbd_sum : ‖iteratedDeriv r qFun x‖ ≤
        x * (2 * B0 * Real.exp (-x)) + (r : ℝ) * (2 * B1 * Real.exp (-x)) := by
      rw [hmul_deriv]
      cases r with
      | zero =>
        simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, Nat.choose_self,
          Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.sub_zero, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hx, Nat.cast_zero, zero_mul, add_zero]
        have h0 : |v x| ≤ 2 * B0 * Real.exp (-x) := by simpa [iteratedDeriv_zero] using hval_r
        exact mul_le_mul_of_nonneg_left h0 hx
      | succ m =>
        have hsplit : ∑ i ∈ Finset.range (m + 2),
            ((m + 1).choose i : ℂ) * iteratedDeriv i (fun t : ℝ => (t : ℂ)) x *
              iteratedDeriv (m + 1 - i) (fun y : ℝ => (v y : ℂ)) x =
            (x : ℂ) * ((iteratedDeriv (m + 1) v x : ℝ) : ℂ) +
              ((m + 1 : ℕ) : ℂ) * ((iteratedDeriv m v x : ℝ) : ℂ) := by
          rw [Finset.sum_range_succ']
          simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.sub_zero]
          rw [Finset.sum_range_succ']
          have hd1 : iteratedDeriv 1 (fun t : ℝ => (t : ℂ)) x = 1 := by
            rw [iteratedDeriv_one]; exact (hasDerivAt_id x).ofReal_comp.deriv
          have hzero : ∀ i ∈ Finset.range m,
              ((m + 1).choose (i + 1 + 1) : ℂ) * iteratedDeriv (i + 1 + 1) (fun t : ℝ => (t : ℂ)) x *
                iteratedDeriv (m + 1 - (i + 1 + 1)) (fun y : ℝ => (v y : ℂ)) x = 0 := fun i _ => by
            rw [iteratedDeriv_ofReal_ge_two' (i + 1 + 1) (by omega) x, mul_zero, zero_mul]
          rw [Finset.sum_eq_zero hzero, zero_add, Nat.choose_one_right, hd1, mul_one,
            show m + 1 - 1 = m by omega, hofReal_v (m + 1) hv_smooth_on hx_pos,
            hofReal_v m hv_smooth_on hx_pos]
          push_cast; ring
        rw [hsplit]
        have hval_m : |iteratedDeriv m v x| ≤ 2 * B1 * Real.exp (-x) := by
          have hPm := hP1 x hx_pos; simp only [Nat.add_one_sub_one] at hPm
          rw [hPm, abs_mul, abs_of_nonneg hv_pos]
          calc v x * |P1.eval (v x)| ≤ (2 * Real.exp (-x)) * B1 :=
                mul_le_mul hv_exp (hpoly_unit P1 hv_pos hv_le1) (abs_nonneg _) (by positivity)
            _ = 2 * B1 * Real.exp (-x) := by ring
        calc ‖(x : ℂ) * ((iteratedDeriv (m + 1) v x : ℝ) : ℂ) +
              ((m + 1 : ℕ) : ℂ) * ((iteratedDeriv m v x : ℝ) : ℂ)‖
            ≤ ‖(x : ℂ) * ((iteratedDeriv (m + 1) v x : ℝ) : ℂ)‖ +
              ‖((m + 1 : ℕ) : ℂ) * ((iteratedDeriv m v x : ℝ) : ℂ)‖ := norm_add_le _ _
          _ = x * |iteratedDeriv (m + 1) v x| + ((m + 1 : ℕ) : ℝ) * |iteratedDeriv m v x| := by
              simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast,
                abs_of_nonneg hx]
          _ ≤ x * (2 * B0 * Real.exp (-x)) + ((m + 1 : ℕ) : ℝ) * (2 * B1 * Real.exp (-x)) := by
              gcongr
    have hx_half : x * Real.exp (-x) ≤ 2 * Real.exp (-(1 / 2) * x) := by
      have hexp : Real.exp (-x) = Real.exp (-((1 / 2) * x)) * Real.exp (-(1 / 2) * x) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp, ← mul_assoc]
      calc (x * Real.exp (-((1 / 2) * x))) * Real.exp (-(1 / 2) * x)
          = (2 * (((1 / 2) * x) * Real.exp (-((1 / 2) * x)))) * Real.exp (-(1 / 2) * x) := by ring
        _ ≤ (2 * 1) * Real.exp (-(1 / 2) * x) := by gcongr; exact real_mul_exp_neg_le_one'
        _ = 2 * Real.exp (-(1 / 2) * x) := by ring
    have hexp_half : Real.exp (-x) ≤ Real.exp (-(1 / 2) * x) := Real.exp_le_exp.mpr (by linarith)
    calc ‖iteratedDeriv r qFun x‖
        ≤ 2 * B0 * (x * Real.exp (-x)) + (r : ℝ) * (2 * B1) * Real.exp (-x) := by linarith
      _ ≤ 2 * B0 * (2 * Real.exp (-(1 / 2) * x)) + (r : ℝ) * (2 * B1) * Real.exp (-(1 / 2) * x) := by
          gcongr
      _ = C_tail * Real.exp (-(1 / 2) * x) := by dsimp [C_tail]; ring
      _ ≤ max (M0 * Real.exp (1 / 2)) C_tail * Real.exp (-(1 / 2) * x) := by gcongr; exact le_max_right _ _

private lemma hPow_expDecaySmooth (d : ℕ) : ExpDecaySmooth (hPow d) :=
  eds_pow_ofReal_mul d qFun_expDecaySmooth'

private lemma hPow_eq_div_exp_sub_one (d : ℕ) {x : ℝ} (hx : x ≠ 0) :
    hPow d x = (x : ℂ) ^ (d + 1) / (Complex.exp (x : ℂ) - 1) := by
  rw [hPow, qFun_eq_div_exp_sub_one' hx, mul_div_assoc', ← pow_succ]


private lemma summable_sumScaleShift {θ : ℝ} (hθ0 : 0 < θ) {h : ℝ → ℂ} (hh : ExpDecaySmooth h)
    {u : ℝ} (hu : 0 < u) :
    Summable (fun n : ℕ => h (((n : ℝ) + θ) / u)) := by
  obtain ⟨C, c, hC, hc, hbd⟩ := hh.2 0
  have hlt : Real.exp (-c / u) < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith) hu)
  have hgeom : Summable (fun n : ℕ => C * (Real.exp (-c / u)) ^ n) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hlt).mul_left C
  refine hgeom.of_norm_bounded fun n => ?_
  have h0 : ‖h (((n : ℝ) + θ) / u)‖ ≤ C * Real.exp (-c * (((n : ℝ) + θ) / u)) := by
    simpa [iteratedDeriv_zero] using hbd (((n : ℝ) + θ) / u) (by positivity)
  refine h0.trans ?_
  have hexp_le : Real.exp (-c * (((n : ℝ) + θ) / u)) ≤ (Real.exp (-c / u)) ^ n := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have : (n : ℝ) / u ≤ ((n : ℝ) + θ) / u := div_le_div_of_nonneg_right (by linarith) hu.le
    calc -c * (((n : ℝ) + θ) / u) ≤ -c * ((n : ℝ) / u) :=
          mul_le_mul_of_nonpos_left this (by linarith)
      _ = (n : ℝ) * (-c / u) := by ring
  exact mul_le_mul_of_nonneg_left hexp_le hC

private lemma d_u_scaleSeries (c : ℂ) (hc : c ≠ 0) (S : PowerSeries ℂ) :
    d_u (scaleSeries c S) = PowerSeries.C c⁻¹ * scaleSeries c (d_u S) := by
  have hcoeff_du : ∀ (A : PowerSeries ℂ) (n : ℕ),
      PowerSeries.coeff n (d_u A) = match n with
        | 0 => 0
        | 1 => 0
        | k + 2 => -(((k + 1 : ℕ) : ℂ) * PowerSeries.coeff (k + 1) A) := fun A n => by
    rw [d_u, map_neg]
    rcases n with _ | _ | k
    · simp [PowerSeries.coeff_mul, PowerSeries.coeff_X_pow]
    · simp [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ, PowerSeries.coeff_X_pow]
    · change -(PowerSeries.coeff (k + 2) (PowerSeries.X ^ 2 * PowerSeries.derivative A)) = _
      rw [PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_derivative]; push_cast; ring
  ext n
  rw [PowerSeries.coeff_C_mul, hcoeff_du]
  conv_rhs => rw [scaleSeries, PowerSeries.coeff_mk, hcoeff_du]
  rcases n with _ | _ | k
  · simp
  · simp
  · simp only [scaleSeries, PowerSeries.coeff_mk, pow_succ]
    field_simp [hc]

private lemma d_u_iter_scaleSeries (c : ℂ) (hc : c ≠ 0) (S : PowerSeries ℂ) (j : ℕ) :
    d_u^[j] (scaleSeries c S) = PowerSeries.C (c⁻¹ ^ j) * scaleSeries c (d_u^[j] S) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hdu_C : ∀ (a : ℂ) (A : PowerSeries ℂ), d_u (PowerSeries.C a * A) = PowerSeries.C a * d_u A := by
      intro a A; simp only [d_u, Derivation.leibniz, PowerSeries.derivative_C, smul_eq_mul]; ring
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hdu_C,
      d_u_scaleSeries c hc, ← mul_assoc, ← map_mul, pow_succ]

private lemma iteratedDeriv_comp_div_const {f : ℝ → ℂ} {c : ℝ} (_hc : c ≠ 0) (j : ℕ) (u : ℝ) :
    iteratedDeriv j (fun v : ℝ => f (v / c)) u = ((c : ℂ)⁻¹ ^ j) * iteratedDeriv j f (u / c) := by
  induction j generalizing f with
  | zero => simp
  | succ j ih =>
    have hderiv : deriv (fun v : ℝ => f (v / c)) = fun v : ℝ => (c : ℂ)⁻¹ * deriv f (v / c) := by
      funext v
      have harg : (fun t : ℝ => f (t / c)) = fun t : ℝ => f (c⁻¹ * t) := by
        funext t; rw [div_eq_inv_mul]
      have hcv : c⁻¹ * v = v / c := (div_eq_inv_mul v c).symm
      rw [harg, deriv_comp_mul_left c⁻¹ f v, Complex.real_smul, Complex.ofReal_inv, hcv]
    rw [iteratedDeriv_succ', hderiv, iteratedDeriv_const_mul_field, ih (f := deriv f),
      ← iteratedDeriv_succ', ← mul_assoc, pow_succ']

private lemma hasAsympExp_comp_div_const {f : ℝ → ℂ} {S : PowerSeries ℂ} {c : ℝ} (hc : 0 < c)
    (hf : ∀ k : ℕ, HasAsympExp (iteratedDeriv k f) (d_u^[k] S)) (j : ℕ) :
    HasAsympExp (iteratedDeriv j (fun u : ℝ => f (u / c))) (d_u^[j] (scaleSeries (c : ℂ) S)) := by
  have hcc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  rw [d_u_iter_scaleSeries (c : ℂ) hcc S j]
  intro M
  obtain ⟨C, hC⟩ := hf j M
  obtain ⟨R, hR⟩ := eventually_atTop.mp hC
  refine ⟨c⁻¹ ^ j * (C * c ^ M), ?_⟩
  filter_upwards [eventually_ge_atTop (max (R * c) 1)] with u hu
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hu)
  have huc_ge : R ≤ u / c := (le_div_iff₀ hc).mpr (le_trans (le_max_left _ _) hu)
  have hbd := hR (u / c) huc_ge
  rw [iteratedDeriv_comp_div_const hc.ne' j u]
  have hsum_eq : ∑ n ∈ Finset.range M,
        PowerSeries.coeff n (PowerSeries.C ((c : ℂ)⁻¹ ^ j) * scaleSeries (c : ℂ) (d_u^[j] S)) *
          (u : ℂ)⁻¹ ^ n =
      ((c : ℂ)⁻¹ ^ j) * ∑ n ∈ Finset.range M,
        PowerSeries.coeff n (d_u^[j] S) * ((u / c : ℝ) : ℂ)⁻¹ ^ n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [PowerSeries.coeff_C_mul, scaleSeries, PowerSeries.coeff_mk]
    push_cast
    rw [inv_div, div_pow, inv_pow]
    have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    field_simp [hcc, huc]
    rw [one_div, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero n huc), mul_one]
  rw [hsum_eq, ← mul_sub, norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hc]
  calc c⁻¹ ^ j * ‖iteratedDeriv j f (u / c) -
        ∑ n ∈ Finset.range M, PowerSeries.coeff n (d_u^[j] S) * ((u / c : ℝ) : ℂ)⁻¹ ^ n‖
      ≤ c⁻¹ ^ j * (C / (u / c) ^ M) := mul_le_mul_of_nonneg_left hbd (by positivity)
    _ = c⁻¹ ^ j * (C * c ^ M) / u ^ M := by
        rw [div_pow]; field_simp [hc.ne', hu_pos.ne']

private lemma X_mul_d_u_iter (T : PowerSeries ℂ) (j : ℕ) :
    PowerSeries.X * d_u^[j] T =
      d_u^[j] (PowerSeries.X * T) +
        match j with
        | 0 => 0
        | k + 1 => ((k + 1 : ℕ) : ℂ) • (PowerSeries.X * d_u^[k] (PowerSeries.X * T)) := by
  have hdu_X_mul : ∀ A : PowerSeries ℂ,
      d_u (PowerSeries.X * A) = PowerSeries.X * d_u A - PowerSeries.X ^ 2 * A := fun A => by
    simp only [d_u, Derivation.leibniz, PowerSeries.derivative_X, smul_eq_mul]; ring
  have hdu_add : ∀ A B : PowerSeries ℂ, d_u (A + B) = d_u A + d_u B := fun A B => by
    simp only [d_u, map_add]; ring
  have hdu_zero : d_u 0 = 0 := by simp [d_u]
  have hdu_smul : ∀ (a : ℂ) (A : PowerSeries ℂ), d_u (a • A) = a • d_u A := fun a A => by
    simp only [d_u, PowerSeries.smul_eq_C_mul, Derivation.leibniz, PowerSeries.derivative_C,
      smul_eq_mul]; ring
  induction j with
  | zero => simp
  | succ j ih =>
    have hstep := congrArg d_u ih
    rw [hdu_X_mul, hdu_add] at hstep
    cases j with
    | zero =>
      simp only [Function.iterate_zero, id_eq, hdu_zero, add_zero] at hstep ⊢
      rw [show (0 : ℕ) + 1 = 1 from rfl, Function.iterate_one, Nat.cast_one, one_smul]
      linear_combination hstep
    | succ k =>
      have hiter_T : d_u^[k + 2] T = d_u (d_u^[k + 1] T) := Function.iterate_succ_apply' d_u (k + 1) T
      have hiter_XT : d_u^[k + 2] (PowerSeries.X * T) = d_u (d_u^[k + 1] (PowerSeries.X * T)) :=
        Function.iterate_succ_apply' d_u (k + 1) (PowerSeries.X * T)
      have hiter_XT1 : d_u^[k + 1] (PowerSeries.X * T) = d_u (d_u^[k] (PowerSeries.X * T)) :=
        Function.iterate_succ_apply' d_u k (PowerSeries.X * T)
      dsimp only at hstep ih
      rw [hdu_smul, hdu_X_mul, ← hiter_T, ← hiter_XT, ← hiter_XT1] at hstep
      have hmulX : PowerSeries.X ^ 2 * d_u^[k + 1] T -
          ((k + 1 : ℕ) : ℂ) • (PowerSeries.X ^ 2 * d_u^[k] (PowerSeries.X * T)) =
          PowerSeries.X * d_u^[k + 1] (PowerSeries.X * T) := by
        have h' := congrArg (PowerSeries.X * ·) ih
        simp only [mul_add, PowerSeries.smul_eq_C_mul] at h' ⊢
        linear_combination h'
      simp only [PowerSeries.smul_eq_C_mul] at hstep hmulX ⊢
      have hC : PowerSeries.C ((k + 1 + 1 : ℕ) : ℂ) = PowerSeries.C ((k + 1 : ℕ) : ℂ) + 1 := by
        push_cast; simp
      rw [hC]
      linear_combination hstep + hmulX

private lemma hasAsympExp_mul_self_of_X_mul {f : ℝ → ℂ} {S : PowerSeries ℂ}
    (hf : HasAsympExp (fun u : ℝ => (u : ℂ)⁻¹ * f u) (PowerSeries.X * S)) :
    HasAsympExp f S := by
  intro M
  obtain ⟨C, hC⟩ := hf (M + 1)
  refine ⟨C, ?_⟩
  filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with u hu_bd hu_pos
  have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
  have hsum : ∑ n ∈ Finset.range (M + 1),
      PowerSeries.coeff n (PowerSeries.X * S) * (u : ℂ)⁻¹ ^ n =
      (u : ℂ)⁻¹ * ∑ n ∈ Finset.range M, PowerSeries.coeff n S * (u : ℂ)⁻¹ ^ n := by
    rw [Finset.sum_range_succ', PowerSeries.coeff_zero_X_mul, zero_mul, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [PowerSeries.coeff_succ_X_mul, pow_succ']
    ring
  rw [hsum, ← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos] at hu_bd
  have hmul := mul_le_mul_of_nonneg_left hu_bd hu_pos.le
  rw [← mul_assoc, mul_inv_cancel₀ hu_pos.ne', one_mul] at hmul
  refine hmul.trans_eq ?_
  rw [pow_succ]; field_simp [hu_pos.ne']

private lemma iteratedDeriv_ofReal_mul {h : ℝ → ℂ}
    (hh : ∀ n : ℕ, ContDiffOn ℝ n h (Ioi (0 : ℝ))) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    iteratedDeriv j (fun v : ℝ => (v : ℂ) * h v) u =
      (u : ℂ) * iteratedDeriv j h u +
        match j with
        | 0 => 0
        | k + 1 => ((k + 1 : ℕ) : ℂ) * iteratedDeriv k h u := by
  have h1 : ContDiffAt ℝ j (fun v : ℝ => (v : ℂ)) u :=
    Complex.ofRealCLM.contDiff.contDiffAt.of_le le_top
  have h2 : ContDiffAt ℝ j h u := (hh j).contDiffAt (isOpen_Ioi.mem_nhds hu)
  rw [iteratedDeriv_fun_mul h1 h2]
  cases j with
  | zero => simp
  | succ k =>
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.sub_zero]
    rw [Finset.sum_range_succ']
    have hd1 : iteratedDeriv 1 (fun v : ℝ => (v : ℂ)) u = 1 := by
      rw [iteratedDeriv_one]; exact (hasDerivAt_id u).ofReal_comp.deriv
    have hzero : ∀ i ∈ Finset.range k,
        ((k + 1).choose (i + 1 + 1) : ℂ) * iteratedDeriv (i + 1 + 1) (fun v : ℝ => (v : ℂ)) u *
          iteratedDeriv (k + 1 - (i + 1 + 1)) h u = 0 := fun i _ => by
      rw [iteratedDeriv_ofReal_ge_two' (i + 1 + 1) (by omega) u, mul_zero, zero_mul]
    rw [Finset.sum_eq_zero hzero, zero_add, Nat.choose_one_right, hd1, mul_one,
      show k + 1 - 1 = k by omega]
    push_cast; ring

private lemma hasAsympExp_ofReal_mul_of_X_mul {h : ℝ → ℂ} {T : PowerSeries ℂ}
    (hh_cd : ∀ n : ℕ, ContDiffOn ℝ n h (Ioi (0 : ℝ)))
    (hh : ∀ k : ℕ, HasAsympExp (iteratedDeriv k h) (d_u^[k] (PowerSeries.X * T))) (j : ℕ) :
    HasAsympExp (iteratedDeriv j (fun u : ℝ => (u : ℂ) * h u)) (d_u^[j] T) := by
  apply hasAsympExp_mul_self_of_X_mul
  rw [X_mul_d_u_iter T j]
  cases j with
  | zero =>
    intro M
    obtain ⟨C, hC⟩ := hh 0 M
    refine ⟨C, ?_⟩
    filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with u hu_bd hu_pos
    have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    simpa [inv_mul_cancel_left₀ huc] using hu_bd
  | succ k =>
    have h1 := hh (k + 1)
    have h2 := (HasAsympExp.const (((k + 1 : ℕ) : ℂ))).mul ((hasAsympExp_inv_pow' 1).mul (hh k))
    have hsum := h1.add h2
    have hser_eq : d_u^[k + 1] (PowerSeries.X * T) +
        PowerSeries.C (((k + 1 : ℕ) : ℂ)) * (PowerSeries.X ^ 1 * d_u^[k] (PowerSeries.X * T)) =
        d_u^[k + 1] (PowerSeries.X * T) +
          ((k + 1 : ℕ) : ℂ) • (PowerSeries.X * d_u^[k] (PowerSeries.X * T)) := by
      rw [pow_one, PowerSeries.smul_eq_C_mul]
    rw [hser_eq] at hsum
    intro M
    obtain ⟨C, hC⟩ := hsum M
    refine ⟨C, ?_⟩
    filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with u hu_bd hu_pos
    have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    have hEq : (u : ℂ)⁻¹ * iteratedDeriv (k + 1) (fun v : ℝ => (v : ℂ) * h v) u =
        iteratedDeriv (k + 1) h u + ((k + 1 : ℕ) : ℂ) * ((u : ℂ)⁻¹ ^ 1 * iteratedDeriv k h u) := by
      rw [iteratedDeriv_ofReal_mul hh_cd (k + 1) hu_pos, pow_one, mul_add,
        inv_mul_cancel_left₀ huc]
      ring
    simpa only [hEq] using hu_bd

private lemma hasAsympExp_pow_mul_of_X_pow_mul : ∀ (p : ℕ) {h : ℝ → ℂ} {T : PowerSeries ℂ},
    (∀ n : ℕ, ContDiffOn ℝ n h (Ioi (0 : ℝ))) →
    (∀ k : ℕ, HasAsympExp (iteratedDeriv k h) (d_u^[k] (PowerSeries.X ^ p * T))) →
    ∀ j : ℕ, HasAsympExp (iteratedDeriv j (fun u : ℝ => (u : ℂ) ^ p * h u)) (d_u^[j] T)
  | 0, h, T, _, hh, j => by simpa using hh j
  | p + 1, h, T, hh_cd, hh, j => by
    have h1 : ∀ k : ℕ, HasAsympExp (iteratedDeriv k (fun u : ℝ => (u : ℂ) * h u))
        (d_u^[k] (PowerSeries.X ^ p * T)) := fun k =>
      hasAsympExp_ofReal_mul_of_X_mul hh_cd (by
        intro m; simpa [pow_succ', mul_assoc] using hh m) k
    have hcd1 : ∀ n : ℕ, ContDiffOn ℝ n (fun u : ℝ => (u : ℂ) * h u) (Ioi (0 : ℝ)) := fun n =>
      (Complex.ofRealCLM.contDiff.contDiffOn.of_le le_top).mul (hh_cd n)
    have h2 := hasAsympExp_pow_mul_of_X_pow_mul p hcd1 h1 j
    have hfn : (fun u : ℝ => (u : ℂ) ^ (p + 1) * h u) = fun u : ℝ => (u : ℂ) ^ p * ((u : ℂ) * h u) := by
      funext u; rw [pow_succ]; ring
    rw [hfn]
    exact h2


private lemma quasipoly_eval_norm_le (P : Quasipoly) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ‖P.eval (n : ℤ)‖ ≤ C * (n : ℝ) ^ P.D := by
  let C : ℝ := ∑ d : Fin (P.D + 1), ∑ r ∈ Finset.Icc 1 P.M, ‖P.c d r‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨C, hC, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hc_le : ∀ d : Fin (P.D + 1),
      ‖P.c d n‖ ≤ ∑ r ∈ Finset.Icc 1 P.M, ‖P.c d r‖ := fun d => by
    let r : ℕ := if n % P.M = 0 then P.M else n % P.M
    have hr_mem : r ∈ Finset.Icc 1 P.M := by
      rw [Finset.mem_Icc]
      dsimp only [r]
      split_ifs with h0
      · exact ⟨P.hM, le_rfl⟩
      · exact ⟨Nat.pos_of_ne_zero h0, (Nat.mod_lt n P.hM).le⟩
    have hc_eq : P.c d n = P.c d r := by
      rw [← P.periodic_mod d n]
      dsimp only [r]
      split_ifs with h0
      · rw [h0, P.periodic_M]
      · rfl
    rw [hc_eq]
    exact Finset.single_le_sum (fun _ _ => norm_nonneg _) hr_mem
  rw [P.eval_nat n]
  calc ‖∑ d : Fin (P.D + 1), P.c d n * (n : ℂ) ^ d.1‖
      ≤ ∑ d : Fin (P.D + 1), ‖P.c d n * (n : ℂ) ^ d.1‖ := norm_sum_le _ _
    _ ≤ ∑ d : Fin (P.D + 1), (∑ r ∈ Finset.Icc 1 P.M, ‖P.c d r‖) * (n : ℝ) ^ P.D := by
        refine Finset.sum_le_sum fun d _ => ?_
        rw [norm_mul, norm_pow, Complex.norm_natCast]
        have hpow : (n : ℝ) ^ d.1 ≤ (n : ℝ) ^ P.D := pow_le_pow_right₀ hn1 (by omega)
        exact mul_le_mul (hc_le d) hpow (by positivity)
          (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ = C * (n : ℝ) ^ P.D := by rw [← Finset.sum_mul]

/-- Polynomial coefficient growth bound for the Lambert series of any quasipolynomial. -/

private lemma value_lambertSeries_exp_neg (P : Quasipoly) {t : ℝ} (ht : 0 < t) :
    value (lambertSeries (fun n => P.eval (n : ℤ))) (Complex.exp (-(t : ℂ))) =
      ∑' n : ℕ, ((n + 1 : ℕ) : ℂ) * P.eval ((n + 1 : ℕ) : ℤ) /
        (Complex.exp (((n + 1 : ℕ) : ℂ) * (t : ℂ)) - 1) := by
  let q : ℂ := Complex.exp (-(t : ℂ))
  have hq_norm : ‖q‖ = Real.exp (-t) := by
    dsimp only [q]
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hx_pos : 0 < Real.exp (-t) := Real.exp_pos _
  have hx_lt : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  obtain ⟨C, hC, hCbd⟩ := quasipoly_eval_norm_le P
  let x : ℝ := Real.exp (-t)
  have hsumm_pair_norm : Summable (fun p : ℕ × ℕ =>
      ‖((p.2 + 1 : ℕ) : ℂ) * P.eval ((p.2 + 1 : ℕ) : ℤ) * q ^ ((p.1 + 1) * (p.2 + 1))‖) := by
    have hA : Summable (fun a : ℕ => x ^ a) := summable_geometric_of_lt_one hx_pos.le hx_lt
    have hx_norm_lt : ‖x‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos hx_pos]; exact hx_lt
    have hB : Summable (fun b : ℕ => (C * x) * ((b + 1 : ℕ) : ℝ) ^ (P.D + 1) * x ^ b) := by
      have hs := summable_pow_mul_geometric_of_norm_lt_one (P.D + 1) hx_norm_lt
      have hs' := (hs.comp_injective (show Function.Injective (fun b : ℕ => b + 1) by
        intro i j h; exact Nat.add_right_cancel h)).mul_left (C * x * x⁻¹)
      refine hs'.congr fun b => ?_
      simp only [Function.comp_def, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp [hx_pos.ne']
    have hAB : Summable (fun p : ℕ × ℕ => x ^ p.1 * ((C * x) * ((p.2 + 1 : ℕ) : ℝ) ^ (P.D + 1) * x ^ p.2)) :=
      hA.mul_of_nonneg hB (fun _ => by positivity) (fun _ => by positivity)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hAB
    rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow, hq_norm]
    have hexp_ge : p.1 + p.2 + 1 ≤ (p.1 + 1) * (p.2 + 1) := by nlinarith
    have hxpow : x ^ ((p.1 + 1) * (p.2 + 1)) ≤ x ^ (p.1 + p.2 + 1) :=
      pow_le_pow_of_le_one hx_pos.le hx_lt.le hexp_ge
    calc ((p.2 + 1 : ℕ) : ℝ) * ‖P.eval ((p.2 + 1 : ℕ) : ℤ)‖ * x ^ ((p.1 + 1) * (p.2 + 1))
        ≤ ((p.2 + 1 : ℕ) : ℝ) * (C * ((p.2 + 1 : ℕ) : ℝ) ^ P.D) * x ^ (p.1 + p.2 + 1) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (hCbd (p.2 + 1) (Nat.succ_pos _)) (by positivity))
            hxpow (by positivity) (by positivity)
      _ = x ^ p.1 * ((C * x) * ((p.2 + 1 : ℕ) : ℝ) ^ (P.D + 1) * x ^ p.2) := by
          rw [pow_add, pow_add, pow_one, pow_succ]; ring
  have hsumm_pair : Summable (fun p : ℕ × ℕ =>
      ((p.2 + 1 : ℕ) : ℂ) * P.eval ((p.2 + 1 : ℕ) : ℤ) * q ^ ((p.1 + 1) * (p.2 + 1))) :=
    hsumm_pair_norm.of_norm
  have hfub := tsum_divisor_fubini (F := fun a b =>
      (b : ℂ) * P.eval (b : ℤ) * q ^ (a * b)) hsumm_pair_norm
  have hval_shift : value (lambertSeries (fun n => P.eval (n : ℤ))) q =
      ∑' n : ℕ, ∑ k ∈ (n + 1).divisors, (k : ℂ) * P.eval (k : ℤ) * q ^ (n + 1) := by
    have hsumm_term : Summable (fun n : ℕ => term (lambertSeries (fun m => P.eval (m : ℤ))) q n) := by
      have hsumm_n : Summable (fun n : ℕ =>
          ∑ k ∈ (n + 1).divisors, (k : ℂ) * P.eval (k : ℤ) * q ^ (n + 1)) := by
        refine hfub.1.congr fun n => Finset.sum_congr rfl fun k hk => ?_
        rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hk)]
      refine (summable_nat_add_iff 1).mp ?_
      refine hsumm_n.congr fun n => ?_
      simp [term, coeff_lambertSeries, Finset.sum_mul]
    rw [value, hsumm_term.tsum_eq_zero_add]
    have h0 : term (lambertSeries (fun n => P.eval (n : ℤ))) q 0 = 0 := by
      simp [term, coeff_lambertSeries]
    rw [h0, zero_add]
    refine tsum_congr fun n => ?_
    simp [term, coeff_lambertSeries, Finset.sum_mul]
  rw [hval_shift]
  have hLHS_eq : (∑' n : ℕ, ∑ k ∈ (n + 1).divisors, (k : ℂ) * P.eval (k : ℤ) * q ^ (n + 1)) =
      ∑' n : ℕ, ∑ d ∈ (n + 1).divisors, (d : ℂ) * P.eval (d : ℤ) * q ^ (((n + 1) / d) * d) := by
    refine tsum_congr fun n => Finset.sum_congr rfl fun d hd => ?_
    rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]
  rw [hLHS_eq, hfub.2]
  have hswap : (∑' a : ℕ, ∑' b : ℕ, ((b + 1 : ℕ) : ℂ) * P.eval ((b + 1 : ℕ) : ℤ) * q ^ ((a + 1) * (b + 1))) =
      ∑' b : ℕ, ∑' a : ℕ, ((b + 1 : ℕ) : ℂ) * P.eval ((b + 1 : ℕ) : ℤ) * q ^ ((a + 1) * (b + 1)) :=
    (Summable.tsum_comm (f := fun a b =>
      ((b + 1 : ℕ) : ℂ) * P.eval ((b + 1 : ℕ) : ℤ) * q ^ ((a + 1) * (b + 1))) hsumm_pair).symm
  rw [hswap]
  refine tsum_congr fun b => ?_
  have hqb_norm : ‖q ^ (b + 1)‖ < 1 := by
    rw [norm_pow, hq_norm]
    exact pow_lt_one₀ hx_pos.le hx_lt (Nat.succ_ne_zero b)
  have hgeom : (∑' a : ℕ, (q ^ (b + 1)) ^ a) = (1 - q ^ (b + 1))⁻¹ :=
    tsum_geometric_of_norm_lt_one hqb_norm
  have hinner : (∑' a : ℕ, ((b + 1 : ℕ) : ℂ) * P.eval ((b + 1 : ℕ) : ℤ) * q ^ ((a + 1) * (b + 1))) =
      ((b + 1 : ℕ) : ℂ) * P.eval ((b + 1 : ℕ) : ℤ) * (q ^ (b + 1) * (1 - q ^ (b + 1))⁻¹) := by
    have hfactor : ∀ a : ℕ,
        ((b + 1 : ℕ) : ℂ) * P.eval ((b + 1 : ℕ) : ℤ) * q ^ ((a + 1) * (b + 1)) =
          (((b + 1 : ℕ) : ℂ) * P.eval ((b + 1 : ℕ) : ℤ) * q ^ (b + 1)) * (q ^ (b + 1)) ^ a := fun a => by
      rw [← pow_mul, mul_assoc (((b + 1 : ℕ) : ℂ) * P.eval ((b + 1 : ℕ) : ℤ)),
        ← pow_add, show b + 1 + (b + 1) * a = (a + 1) * (b + 1) by ring]
    simp_rw [hfactor]
    rw [tsum_mul_left, hgeom, mul_assoc]
  rw [hinner]
  have hqb_eq : q ^ (b + 1) = (Complex.exp (((b + 1 : ℕ) : ℂ) * (t : ℂ)))⁻¹ := by
    dsimp only [q]
    rw [← Complex.exp_nat_mul, ← Complex.exp_neg]
    congr 1; ring
  have hexp_ne : Complex.exp (((b + 1 : ℕ) : ℂ) * (t : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hsub_ne : Complex.exp (((b + 1 : ℕ) : ℂ) * (t : ℂ)) - 1 ≠ 0 := by
    intro h0
    have h1 : Complex.exp (((b + 1 : ℕ) : ℂ) * (t : ℂ)) = 1 := sub_eq_zero.mp h0
    have h1c : ((Real.exp (((b + 1 : ℕ) : ℝ) * t) : ℝ) : ℂ) = (1 : ℂ) := by
      rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_natCast]; exact h1
    have hre : Real.exp (((b + 1 : ℕ) : ℝ) * t) = 1 := Complex.ofReal_injective h1c
    have hpos : 0 < ((b + 1 : ℕ) : ℝ) * t := by positivity
    exact (Real.one_lt_exp_iff.mpr hpos).ne' hre
  have h1sub_ne : 1 - (Complex.exp (((b + 1 : ℕ) : ℂ) * (t : ℂ)))⁻¹ ≠ 0 := by
    intro h0
    have : Complex.exp (((b + 1 : ℕ) : ℂ) * (t : ℂ)) = 1 := by
      have h1 : (Complex.exp (((b + 1 : ℕ) : ℂ) * (t : ℂ)))⁻¹ = 1 := (sub_eq_zero.mp h0).symm
      simpa using congrArg Inv.inv h1
    exact hsub_ne (sub_eq_zero.mpr this)
  rw [hqb_eq]
  field_simp [hexp_ne, hsub_ne, h1sub_ne]

/-- Residue-class decomposition of `value (lambertSeries P.eval) (exp (-u⁻¹))` into shifted
Euler–Maclaurin sums `sumScaleShift (r/M) (hPow d) (u/M)`. -/
private lemma value_lambertSeries_exp_inv_eq (P : Quasipoly) {u : ℝ} (hu : 0 < u) :
    value (lambertSeries (fun n => P.eval (n : ℤ))) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) =
      ∑ d : Fin (P.D + 1), (u : ℂ) ^ (d.1 + 1) *
        ∑ r ∈ Finset.Icc 1 P.M, P.c d r *
          sumScaleShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) (u / (P.M : ℝ)) := by
  rw [value_lambertSeries_exp_neg P (inv_pos.mpr hu)]
  have hMpos : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  have huM : 0 < u / (P.M : ℝ) := div_pos hu hMpos
  have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  -- Equivalence `Fin P.M × ℕ ≃ ℕ` via `n = P.M * k + r0`.
  let e : Fin P.M × ℕ ≃ ℕ :=
    { toFun := fun p => P.M * p.2 + p.1.1
      invFun := fun n => (⟨n % P.M, Nat.mod_lt n P.hM⟩, n / P.M)
      left_inv := fun ⟨⟨r0, hr0⟩, k⟩ => by
        ext
        · dsimp only
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr0]
        · dsimp only
          rw [Nat.mul_add_div P.hM, Nat.div_eq_of_lt hr0, add_zero]
      right_inv := fun n => Nat.div_add_mod n P.M }
  rw [← e.tsum_eq]
  have hterm_eq : ∀ (r0 : Fin P.M) (k : ℕ),
      (((P.M * k + r0.1 + 1 : ℕ) : ℂ) * P.eval ((P.M * k + r0.1 + 1 : ℕ) : ℤ) /
          (Complex.exp (((P.M * k + r0.1 + 1 : ℕ) : ℂ) * ((u⁻¹ : ℝ) : ℂ)) - 1)) =
        ∑ d : Fin (P.D + 1), (u : ℂ) ^ (d.1 + 1) *
          (P.c d (r0.1 + 1) *
            hPow d.1 (((k : ℝ) + ((r0.1 + 1 : ℕ) : ℝ) / (P.M : ℝ)) / (u / (P.M : ℝ)))) := fun r0 k => by
    let n : ℕ := P.M * k + r0.1 + 1
    change ((n : ℂ) * P.eval (n : ℤ) / (Complex.exp ((n : ℂ) * ((u⁻¹ : ℝ) : ℂ)) - 1)) = _
    have hc_eq : ∀ d : Fin (P.D + 1), P.c d n = P.c d (r0.1 + 1) := fun d => by
      rw [← P.periodic_mod d n]
      have hmod : n % P.M = (r0.1 + 1) % P.M := by
        dsimp only [n]
        rw [add_assoc, Nat.mul_add_mod]
      rw [hmod]
      by_cases hlt : r0.1 + 1 < P.M
      · rw [Nat.mod_eq_of_lt hlt]
      · have heq : r0.1 + 1 = P.M := by omega
        rw [heq, Nat.mod_self, P.periodic_M]
    have hPeval : P.eval (n : ℤ) = ∑ d : Fin (P.D + 1), P.c d (r0.1 + 1) * (n : ℂ) ^ d.1 := by
      rw [P.eval_nat n]
      exact Finset.sum_congr rfl fun d _ => by rw [hc_eq d]
    rw [hPeval, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun d _ => ?_
    have harg : (((k : ℝ) + ((r0.1 + 1 : ℕ) : ℝ) / (P.M : ℝ)) / (u / (P.M : ℝ))) = (n : ℝ) / u := by
      dsimp only [n]; push_cast; field_simp [hMpos.ne', hu.ne']; ring
    have harg_ne : (n : ℝ) / u ≠ 0 := div_ne_zero (by positivity) hu.ne'
    rw [harg, hPow, qFun_eq_div_exp_sub_one' harg_ne]
    rw [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_inv,
      div_eq_mul_inv (n : ℂ) (u : ℂ), mul_pow]
    have hcancel : (u : ℂ) ^ (d.1 + 1) * (u : ℂ)⁻¹ ^ (d.1 + 1) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ huc, one_pow]
    calc (n : ℂ) * (P.c d (r0.1 + 1) * (n : ℂ) ^ d.1) / (Complex.exp ((n : ℂ) * (u : ℂ)⁻¹) - 1)
        = (P.c d (r0.1 + 1) * ((n : ℂ) ^ (d.1 + 1) / (Complex.exp ((n : ℂ) * (u : ℂ)⁻¹) - 1))) *
            ((u : ℂ) ^ (d.1 + 1) * (u : ℂ)⁻¹ ^ (d.1 + 1)) := by
          rw [hcancel, mul_one, pow_succ]; ring
      _ = (u : ℂ) ^ (d.1 + 1) *
            (P.c d (r0.1 + 1) * (((n : ℂ) ^ d.1 * (u : ℂ)⁻¹ ^ d.1) *
              ((n : ℂ) * (u : ℂ)⁻¹ / (Complex.exp ((n : ℂ) * (u : ℂ)⁻¹) - 1)))) := by
          rw [pow_succ (n : ℂ) d.1, pow_succ (u : ℂ)⁻¹ d.1]; ring
  have hsumm_d : ∀ (r0 : Fin P.M) (d : Fin (P.D + 1)),
      Summable (fun k : ℕ => (u : ℂ) ^ (d.1 + 1) * (P.c d (r0.1 + 1) *
        hPow d.1 (((k : ℝ) + ((r0.1 + 1 : ℕ) : ℝ) / (P.M : ℝ)) / (u / (P.M : ℝ))))) := fun r0 d =>
    ((summable_sumScaleShift (by positivity : (0 : ℝ) < ((r0.1 + 1 : ℕ) : ℝ) / (P.M : ℝ))
      (hPow_expDecaySmooth d.1) huM).mul_left (P.c d (r0.1 + 1))).mul_left ((u : ℂ) ^ (d.1 + 1))
  let F : Fin P.M × ℕ → ℂ := fun p =>
    ((e p + 1 : ℕ) : ℂ) * P.eval ((e p + 1 : ℕ) : ℤ) /
      (Complex.exp (((e p + 1 : ℕ) : ℂ) * ((u⁻¹ : ℝ) : ℂ)) - 1)
  have hs_row : ∀ r0 : Fin P.M, Summable (fun k : ℕ => F (r0, k)) := fun r0 =>
    (summable_sum fun d _ => hsumm_d r0 d).congr fun k => (hterm_eq r0 k).symm
  have hhas_s : ∀ s : Fin P.M,
      HasSum (fun p : Fin P.M × ℕ => if p.1 = s then F p else 0) (∑' k : ℕ, F (s, k)) := fun s => by
    have hinj : Function.Injective (fun k : ℕ => (s, k)) := fun _ _ h => (Prod.mk.inj h).2
    rw [← hinj.hasSum_iff (fun p hp => by
      have hne : p.1 ≠ s := fun h => hp ⟨p.2, Prod.ext h.symm rfl⟩
      simp [hne])]
    simpa [Function.comp_def] using (hs_row s).hasSum
  have hhas_F : HasSum F (∑ r0 : Fin P.M, ∑' k : ℕ, F (r0, k)) := by
    refine (hasSum_sum fun s _ => hhas_s s).congr_fun fun p => ?_
    simp
  change (∑' p : Fin P.M × ℕ, F p) = _
  rw [hhas_F.tsum_eq]
  have hswap_r : ∑ r0 : Fin P.M, ∑' k : ℕ, F (r0, k) =
      ∑ d : Fin (P.D + 1), (u : ℂ) ^ (d.1 + 1) *
        ∑ r0 : Fin P.M, P.c d (r0.1 + 1) *
          sumScaleShift (((r0.1 + 1 : ℕ) : ℝ) / (P.M : ℝ)) (hPow d.1) (u / (P.M : ℝ)) := by
    calc ∑ r0 : Fin P.M, ∑' k : ℕ, F (r0, k)
        = ∑ r0 : Fin P.M, ∑' k : ℕ, ∑ d : Fin (P.D + 1), (u : ℂ) ^ (d.1 + 1) *
            (P.c d (r0.1 + 1) *
              hPow d.1 (((k : ℝ) + ((r0.1 + 1 : ℕ) : ℝ) / (P.M : ℝ)) / (u / (P.M : ℝ)))) :=
          Finset.sum_congr rfl fun r0 _ => tsum_congr fun k => hterm_eq r0 k
      _ = ∑ r0 : Fin P.M, ∑ d : Fin (P.D + 1), ∑' k : ℕ, (u : ℂ) ^ (d.1 + 1) *
            (P.c d (r0.1 + 1) *
              hPow d.1 (((k : ℝ) + ((r0.1 + 1 : ℕ) : ℝ) / (P.M : ℝ)) / (u / (P.M : ℝ)))) :=
          Finset.sum_congr rfl fun r0 _ => Summable.tsum_finsetSum fun d _ => hsumm_d r0 d
      _ = ∑ d : Fin (P.D + 1), ∑ r0 : Fin P.M, (u : ℂ) ^ (d.1 + 1) *
            (P.c d (r0.1 + 1) *
              sumScaleShift (((r0.1 + 1 : ℕ) : ℝ) / (P.M : ℝ)) (hPow d.1) (u / (P.M : ℝ))) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun r0 _ => ?_
          rw [tsum_mul_left, tsum_mul_left]; rfl
      _ = _ := Finset.sum_congr rfl fun d _ => (Finset.mul_sum _ _ _).symm
  rw [hswap_r]
  refine Finset.sum_congr rfl fun d _ => congrArg ((u : ℂ) ^ (d.1 + 1) * ·) ?_
  refine Finset.sum_bij (fun (r0 : Fin P.M) _ => r0.1 + 1)
    (fun r0 _ => Finset.mem_Icc.mpr ⟨Nat.succ_pos _, r0.isLt⟩)
    (fun a _ b _ h => Fin.ext (by omega))
    (fun r hr => ⟨⟨r - 1, by have := Finset.mem_Icc.mp hr; omega⟩, Finset.mem_univ _,
      by dsimp only; have := Finset.mem_Icc.mp hr; omega⟩)
    (fun _ _ => rfl)

/-- Subtracted shifted Euler–Maclaurin tail function for a single `(d, r)` residue class. -/
private def tailFunDR (P : Quasipoly) (d : Fin (P.D + 1)) (r : ℕ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ (d.1 + 1) *
    (sumScaleShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) (u / (P.M : ℝ)) -
      ((u / (P.M : ℝ) : ℝ) : ℂ) * (∫ y in Ioi (0 : ℝ), hPow d.1 y) -
      ∑ n ∈ Finset.range (d.1 + 2),
        (P.M : ℂ) ^ n * emTermShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) n * (u : ℂ)⁻¹ ^ n)

/-- Polynomial part for a single `(d, r)` residue class. -/
private def polyPartDR (P : Quasipoly) (d : Fin (P.D + 1)) (r : ℕ) : Polynomial ℂ :=
  Polynomial.C ((P.M : ℂ)⁻¹ * (∫ y in Ioi (0 : ℝ), hPow d.1 y)) * Polynomial.X ^ (d.1 + 2) +
    ∑ n ∈ Finset.range (d.1 + 2),
      Polynomial.C ((P.M : ℂ) ^ n * emTermShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) n) *
        Polynomial.X ^ (d.1 + 1 - n)

/-- Total smooth remainder function `remFun P` with exact asymptotic expansion `formalSeries (borelPhi P)`. -/
private def remFun (P : Quasipoly) (u : ℝ) : ℂ :=
  ∑ d : Fin (P.D + 1), ∑ r ∈ Finset.Icc 1 P.M, P.c d r * tailFunDR P d r u

/-- Total polynomial part `polyPart P : Polynomial ℂ` of `value (lambertSeries P.eval) (exp (-u⁻¹))`. -/
private def polyPart (P : Quasipoly) : Polynomial ℂ :=
  ∑ d : Fin (P.D + 1), ∑ r ∈ Finset.Icc 1 P.M, Polynomial.C (P.c d r) * polyPartDR P d r

private lemma value_lambertSeries_eq_remFun_add_polyPart (P : Quasipoly) {u : ℝ} (hu : 0 < u) :
    value (lambertSeries (fun n => P.eval (n : ℤ))) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) =
      remFun P u + (polyPart P).eval (u : ℂ) := by
  have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have heval_sum : ∀ {ι : Type} (s : Finset ι) (f : ι → Polynomial ℂ),
      (∑ i ∈ s, f i).eval (u : ℂ) = ∑ i ∈ s, (f i).eval (u : ℂ) :=
    fun s f => map_sum (Polynomial.evalRingHom (u : ℂ)) f s
  rw [value_lambertSeries_exp_inv_eq P hu]
  dsimp only [remFun, polyPart]
  rw [heval_sum]
  simp_rw [heval_sum, Polynomial.eval_mul, Polynomial.eval_C]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← mul_add, ← mul_assoc, mul_comm ((u : ℂ) ^ (d.1 + 1)) (P.c d r), mul_assoc]
  congr 1
  dsimp only [tailFunDR, polyPartDR]
  rw [Polynomial.eval_add, heval_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hsum_eq : (u : ℂ) ^ (d.1 + 1) *
      ∑ n ∈ Finset.range (d.1 + 2),
        (P.M : ℂ) ^ n * emTermShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) n * (u : ℂ)⁻¹ ^ n =
      ∑ n ∈ Finset.range (d.1 + 2),
        (P.M : ℂ) ^ n * emTermShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) n * (u : ℂ) ^ (d.1 + 1 - n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn_le : n ≤ d.1 + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hpow : (u : ℂ) ^ (d.1 + 1) * (u : ℂ)⁻¹ ^ n = (u : ℂ) ^ (d.1 + 1 - n) := by
      have h1 : (u : ℂ) ^ (d.1 + 1) = (u : ℂ) ^ (d.1 + 1 - n) * (u : ℂ) ^ n := by
        rw [← pow_add, Nat.sub_add_cancel hn_le]
      rw [h1, mul_assoc, ← mul_pow, mul_inv_cancel₀ huc, one_pow, mul_one]
    calc (u : ℂ) ^ (d.1 + 1) *
          ((P.M : ℂ) ^ n * emTermShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) n * (u : ℂ)⁻¹ ^ n)
        = (P.M : ℂ) ^ n * emTermShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) n *
            ((u : ℂ) ^ (d.1 + 1) * (u : ℂ)⁻¹ ^ n) := by ring
      _ = _ := by rw [hpow]
  have hlead : (u : ℂ) ^ (d.1 + 1) * ((u / (P.M : ℝ) : ℝ) : ℂ) = (P.M : ℂ)⁻¹ * (u : ℂ) ^ (d.1 + 2) := by
    push_cast; rw [pow_succ (u : ℂ) (d.1 + 1), div_eq_mul_inv]; ring
  rw [mul_sub, mul_sub, hsum_eq, ← mul_assoc, hlead]
  ring

private lemma d_u_add' (A B : PowerSeries ℂ) : d_u (A + B) = d_u A + d_u B := by
  simp only [d_u, map_add]; ring

private lemma d_u_sub' (A B : PowerSeries ℂ) : d_u (A - B) = d_u A - d_u B := by
  simp only [d_u, map_sub]; ring

private lemma d_u_C_mul' (c : ℂ) (A : PowerSeries ℂ) : d_u (PowerSeries.C c * A) = PowerSeries.C c * d_u A := by
  simp only [d_u, Derivation.leibniz, PowerSeries.derivative_C, smul_eq_mul]; ring

private lemma d_u_iter_add' (A B : PowerSeries ℂ) (j : ℕ) :
    d_u^[j] (A + B) = d_u^[j] A + d_u^[j] B := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih, d_u_add']

private lemma d_u_iter_sub' (A B : PowerSeries ℂ) (j : ℕ) :
    d_u^[j] (A - B) = d_u^[j] A - d_u^[j] B := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih, d_u_sub']

private lemma d_u_iter_C_mul' (c : ℂ) (A : PowerSeries ℂ) (j : ℕ) :
    d_u^[j] (PowerSeries.C c * A) = PowerSeries.C c * d_u^[j] A := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, d_u_C_mul']

private lemma d_u_iter_zero' (j : ℕ) : d_u^[j] (0 : PowerSeries ℂ) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih]; simp [d_u]

private lemma d_u_iter_sum' {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℂ) (j : ℕ) :
    d_u^[j] (∑ i ∈ s, F i) = ∑ i ∈ s, d_u^[j] (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using d_u_iter_zero' j
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, d_u_iter_add', ih]

private lemma hasAsympExp_sub' {f g : ℝ → ℂ} {S T : PowerSeries ℂ}
    (hf : HasAsympExp f S) (hg : HasAsympExp g T) :
    HasAsympExp (fun u => f u - g u) (S - T) := by
  have h1 := hf.add ((HasAsympExp.const (-1 : ℂ)).mul hg)
  have hS : S + PowerSeries.C (-1 : ℂ) * T = S - T := by rw [map_neg, map_one]; ring
  rw [hS] at h1
  intro M
  obtain ⟨C, hC⟩ := h1 M
  refine ⟨C, ?_⟩
  filter_upwards [hC] with u hu
  have hfn : f u + (-1 : ℂ) * g u = f u - g u := by ring
  simpa only [hfn] using hu

private lemma hasAsympExp_sum' {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (S : ι → PowerSeries ℂ)
    (h : ∀ i ∈ s, HasAsympExp (f i) (S i)) :
    HasAsympExp (fun u => ∑ i ∈ s, f i u) (∑ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasAsympExp.const 0
  | @insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private lemma hasAsympExp_congr_atTop' {f g : ℝ → ℂ} {S : PowerSeries ℂ}
    (hfg : f =ᶠ[atTop] g) (hf : HasAsympExp f S) : HasAsympExp g S := by
  intro M
  obtain ⟨C, hC⟩ := hf M
  refine ⟨C, ?_⟩
  filter_upwards [hC, hfg] with u hu hEq
  rw [← hEq]; exact hu

private lemma iteratedDeriv_finset_sum' {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (k : ℕ) {u : ℝ}
    (hcd : ∀ i ∈ s, ContDiffAt ℝ k (f i) u) :
    iteratedDeriv k (fun v : ℝ => ∑ i ∈ s, f i v) u = ∑ i ∈ s, iteratedDeriv k (f i) u := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    cases k with
    | zero => simp
    | succ k' => simp
  | @insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    have hcd_a := hcd a (Finset.mem_insert_self a s)
    have hcd_s : ContDiffAt ℝ k (fun v : ℝ => ∑ i ∈ s, f i v) u :=
      ContDiffAt.sum fun i hi => hcd i (Finset.mem_insert_of_mem hi)
    rw [iteratedDeriv_fun_add hcd_a hcd_s, ih fun i hi => hcd i (Finset.mem_insert_of_mem hi)]

private lemma iteratedDeriv_inv_pow_exact' (n k : ℕ) :
    (∀ u : ℝ, 0 < u →
      iteratedDeriv k (fun v : ℝ => (v : ℂ)⁻¹ ^ n) u =
        ((-1 : ℂ) ^ k * ((n.ascFactorial k : ℕ) : ℂ)) * (u : ℂ)⁻¹ ^ (n + k)) ∧
    d_u^[k] (PowerSeries.X ^ n : PowerSeries ℂ) =
      PowerSeries.C ((-1 : ℂ) ^ k * ((n.ascFactorial k : ℕ) : ℂ)) * PowerSeries.X ^ (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    constructor
    · intro u hu
      have hev : iteratedDeriv k (fun v : ℝ => (v : ℂ)⁻¹ ^ n) =ᶠ[𝓝 u]
          fun v : ℝ => ((-1 : ℂ) ^ k * ((n.ascFactorial k : ℕ) : ℂ)) * (v : ℂ)⁻¹ ^ (n + k) := by
        filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
        exact ih.1 v hv
      rw [iteratedDeriv_succ, hev.deriv_eq]
      have hd := (hasDerivAt_inv_pow_complex' (j := n + k) hu.ne').const_mul
        ((-1 : ℂ) ^ k * ((n.ascFactorial k : ℕ) : ℂ))
      refine hd.deriv.trans ?_
      rw [Nat.ascFactorial_succ, pow_succ (-1 : ℂ) k, show n + (k + 1) = n + k + 1 by omega]
      push_cast; ring
    · rw [Function.iterate_succ_apply', ih.2, d_u_C_mul']
      have hdu_Xpow : d_u (PowerSeries.X ^ (n + k) : PowerSeries ℂ) =
          PowerSeries.C (-((n + k : ℕ) : ℂ)) * PowerSeries.X ^ (n + k + 1) := by
        cases hnk : n + k with
        | zero => simp [d_u]
        | succ m =>
          simp only [d_u, PowerSeries.derivative_X_pow, Nat.add_sub_cancel, map_neg]
          rw [show m + 1 + 1 = 2 + m by omega, pow_add]
          ring
      rw [hdu_Xpow, ← mul_assoc, ← map_mul, Nat.ascFactorial_succ, pow_succ (-1 : ℂ) k,
        show n + (k + 1) = n + k + 1 by omega]
      congr 2; push_cast; ring

private lemma iteratedDeriv_inv_pow_hasAsympExp' (n k : ℕ) :
    HasAsympExp (iteratedDeriv k (fun u : ℝ => (u : ℂ)⁻¹ ^ n))
      (d_u^[k] (PowerSeries.X ^ n : PowerSeries ℂ)) := by
  have h := iteratedDeriv_inv_pow_exact' n k
  rw [h.2]
  have h1 := (HasAsympExp.const ((-1 : ℂ) ^ k * ((n.ascFactorial k : ℕ) : ℂ))).mul
    (hasAsympExp_inv_pow' (n + k))
  refine hasAsympExp_congr_atTop' ?_ h1
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  exact (h.1 u hu).symm



private lemma sumScaleShift_scaled_contDiffOn (M : ℕ) (hM : 0 < M) (d r : ℕ)
    (hr1 : 1 ≤ r) (hrM : r ≤ M) (n : ℕ) :
    ContDiffOn ℝ n (fun u : ℝ => sumScaleShift ((r : ℝ) / (M : ℝ)) (hPow d) (u / (M : ℝ))) (Ioi (0 : ℝ)) := by
  let P1 : Quasipoly := {
    M := M
    hM := hM
    «D» := d
    c := fun d' k => if d'.1 = d ∧ k % M = r % M then 1 else 0
    periodic := fun _ k => by simp [Nat.add_mod_right]
  }
  have hmod : ∀ r' ∈ Finset.Icc 1 M, r' % M = r % M ↔ r' = r := by
    intro r' hr'
    have ⟨hr'1, hr'M⟩ := Finset.mem_Icc.mp hr'
    constructor
    · intro h
      by_cases hlt : r' < M
      · rw [Nat.mod_eq_of_lt hlt] at h
        by_cases hlt2 : r < M
        · rw [Nat.mod_eq_of_lt hlt2] at h; exact h
        · have hrEq : r = M := by omega
          rw [hrEq, Nat.mod_self] at h; omega
      · have hr'Eq : r' = M := by omega
        rw [hr'Eq, Nat.mod_self] at h
        by_cases hlt2 : r < M
        · rw [Nat.mod_eq_of_lt hlt2] at h; omega
        · omega
    · intro h; rw [h]
  have hval : ∀ u : ℝ, 0 < u →
      sumScaleShift ((r : ℝ) / (M : ℝ)) (hPow d) (u / (M : ℝ)) =
        ((u : ℂ) ^ (d + 1))⁻¹ *
          value (lambertSeries (fun k => P1.eval (k : ℤ))) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) := by
    intro u hu
    have hu_ne : (u : ℂ) ^ (d + 1) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hu.ne')
    rw [value_lambertSeries_exp_inv_eq P1 hu]
    have hsum : (∑ d' : Fin (P1.D + 1), (u : ℂ) ^ (d'.1 + 1) *
        ∑ r' ∈ Finset.Icc 1 P1.M, P1.c d' r' *
          sumScaleShift ((r' : ℝ) / (P1.M : ℝ)) (hPow d'.1) (u / (P1.M : ℝ))) =
        (u : ℂ) ^ (d + 1) * sumScaleShift ((r : ℝ) / (M : ℝ)) (hPow d) (u / (M : ℝ)) := by
      have hd_last : (⟨d, Nat.lt_succ_self d⟩ : Fin (P1.D + 1)) ∈ Finset.univ := Finset.mem_univ _
      have houter : ∑ x ∈ Finset.univ.erase (⟨d, Nat.lt_succ_self d⟩ : Fin (P1.D + 1)),
          (u : ℂ) ^ (x.1 + 1) *
            ∑ r' ∈ Finset.Icc 1 P1.M, P1.c x r' *
              sumScaleShift ((r' : ℝ) / (P1.M : ℝ)) (hPow x.1) (u / (P1.M : ℝ)) = 0 := by
        refine Finset.sum_eq_zero fun d' hd' => ?_
        have hne : d'.1 ≠ d := fun h => (Finset.mem_erase.mp hd').1 (Fin.ext h)
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun r' _ => ?_)
        dsimp only [P1]
        simp [hne]
      rw [← Finset.add_sum_erase _ _ hd_last, houter, add_zero]
      have hr_mem : r ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨hr1, hrM⟩
      dsimp only [P1]
      rw [← Finset.add_sum_erase _ _ hr_mem, Finset.sum_eq_zero, add_zero]
      · simp
      · intro r' hr'
        have hne : r' ≠ r := (Finset.mem_erase.mp hr').1
        have hmem : r' ∈ Finset.Icc 1 M := (Finset.mem_erase.mp hr').2
        have hne_mod : r' % M ≠ r % M := mt (hmod r' hmem).mp hne
        simp [hne_mod]
    rw [hsum, inv_mul_cancel_left₀ hu_ne]
  intro u hu
  have heq : (fun t : ℝ => sumScaleShift ((r : ℝ) / (M : ℝ)) (hPow d) (t / (M : ℝ))) =ᶠ[𝓝 u]
      fun t : ℝ => ((t : ℂ) ^ (d + 1))⁻¹ *
        value (lambertSeries (fun k => P1.eval (k : ℤ))) (Complex.exp (-((t⁻¹ : ℝ) : ℂ))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with t ht
    exact hval t ht
  have h1 : ContDiffAt ℝ n (fun t : ℝ => ((t : ℂ) ^ (d + 1))⁻¹) u :=
    ((Complex.ofRealCLM.contDiff.contDiffAt.pow (d + 1)).inv
      (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hu.ne'))).of_le le_top
  have h2 : ContDiffAt ℝ n (fun t : ℝ => value (lambertSeries (fun k => P1.eval (k : ℤ))) (Complex.exp (-((t⁻¹ : ℝ) : ℂ)))) u :=
    value_exp_inv_contDiffAt (quasipoly_lambertSeries_polyBound P1) hu n
  exact ((h1.mul h2).congr_of_eventuallyEq heq).contDiffWithinAt

private lemma tailFunDR_contDiffOn (P : Quasipoly) (d : Fin (P.D + 1)) {r : ℕ} (hr : 1 ≤ r)
    (hrM : r ≤ P.M) (n : ℕ) :
    ContDiffOn ℝ n (tailFunDR P d r) (Ioi (0 : ℝ)) := by
  have hpow : ContDiffOn ℝ n (fun u : ℝ => (u : ℂ) ^ (d.1 + 1)) (Ioi (0 : ℝ)) :=
    (Complex.ofRealCLM.contDiff.pow (d.1 + 1)).contDiffOn.of_le le_top
  have h1 : ContDiffOn ℝ n (fun u : ℝ => sumScaleShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) (u / (P.M : ℝ))) (Ioi (0 : ℝ)) :=
    sumScaleShift_scaled_contDiffOn P.M P.hM d.1 r hr hrM n
  have h2 : ContDiffOn ℝ n (fun u : ℝ => ((u / (P.M : ℝ) : ℝ) : ℂ) * (∫ y in Ioi (0 : ℝ), hPow d.1 y)) (Ioi (0 : ℝ)) := by
    have hdiv : ContDiffOn ℝ n (fun u : ℝ => ((u / (P.M : ℝ) : ℝ) : ℂ)) (Ioi (0 : ℝ)) :=
      (Complex.ofRealCLM.contDiff.comp (contDiff_id.div_const (P.M : ℝ))).contDiffOn.of_le le_top
    exact hdiv.mul contDiffOn_const
  have h3 : ContDiffOn ℝ n (fun u : ℝ => ∑ k ∈ Finset.range (d.1 + 2),
      (P.M : ℂ) ^ k * emTermShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) k * (u : ℂ)⁻¹ ^ k) (Ioi (0 : ℝ)) := by
    refine ContDiffOn.sum fun k _ => contDiffOn_const.mul ?_
    intro u hu
    exact (((Complex.ofRealCLM.contDiff.contDiffAt.inv
      (Complex.ofReal_ne_zero.mpr hu.ne')).pow k).of_le le_top).contDiffWithinAt
  exact hpow.mul ((h1.sub h2).sub h3)

private lemma remFun_contDiffOn (P : Quasipoly) (n : ℕ) :
    ContDiffOn ℝ n (remFun P) (Ioi (0 : ℝ)) :=
  ContDiffOn.sum fun d _ => ContDiffOn.sum fun _r hr =>
    contDiffOn_const.mul (tailFunDR_contDiffOn P d (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2 n)

private lemma tailFunDR_hasAsympExp (P : Quasipoly) (d : Fin (P.D + 1)) {r : ℕ}
    (hr : r ∈ Finset.Icc 1 P.M) (j : ℕ) :
    HasAsympExp (iteratedDeriv j (tailFunDR P d r)) (d_u^[j] (tailSeriesDR P d r)) := by
  have hMpos : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  have hr_b := Finset.mem_Icc.mp hr
  let q : ℚ := (r : ℚ) / (P.M : ℚ)
  have hq_cast : (q : ℝ) = (r : ℝ) / (P.M : ℝ) := by simp [q]
  have hq0 : (0 : ℝ) < (q : ℝ) := by rw [hq_cast]; exact div_pos (by exact_mod_cast hr_b.1) hMpos
  have hq1 : (q : ℝ) ≤ 1 := by rw [hq_cast]; exact (div_le_one hMpos).mpr (by exact_mod_cast hr_b.2)
  let g1 : ℝ → ℂ := fun u =>
    sumScaleShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) (u / (P.M : ℝ)) -
      ((u / (P.M : ℝ) : ℝ) : ℂ) * (∫ y in Ioi (0 : ℝ), hPow d.1 y)
  let g2 : ℝ → ℂ := fun u =>
    ∑ n ∈ Finset.range (d.1 + 2),
      (P.M : ℂ) ^ n * emTermShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) n * (u : ℂ)⁻¹ ^ n
  let g : ℝ → ℂ := fun u => g1 u - g2 u
  have hg1_cd : ∀ n : ℕ, ContDiffOn ℝ n g1 (Ioi (0 : ℝ)) := fun n => by
    have hdiv_cd : ContDiffOn ℝ n (fun u : ℝ => u / (P.M : ℝ)) (Ioi (0 : ℝ)) :=
      contDiffOn_id.div_const (P.M : ℝ)
    have hdiv_maps : MapsTo (fun u : ℝ => u / (P.M : ℝ)) (Ioi (0 : ℝ)) (Ioi (0 : ℝ)) :=
      fun u hu => div_pos hu hMpos
    exact (sumScaleShift_scaled_contDiffOn P.M P.hM d.1 r hr_b.1 hr_b.2 n).sub
      (((Complex.ofRealCLM.contDiff.contDiffOn.of_le le_top).comp hdiv_cd (mapsTo_univ _ _)).mul contDiffOn_const)
  have hg2_cd : ∀ n : ℕ, ContDiffOn ℝ n g2 (Ioi (0 : ℝ)) := fun n => by
    have hinv_cd : ContDiffOn ℝ n (fun u : ℝ => (u : ℂ)⁻¹) (Ioi (0 : ℝ)) :=
      (Complex.ofRealCLM.contDiff.contDiffOn.of_le le_top).inv fun u hu =>
        Complex.ofReal_ne_zero.mpr (ne_of_gt hu)
    exact ContDiffOn.sum fun k _ => contDiffOn_const.mul (hinv_cd.pow k)
  have hg_cd : ∀ n : ℕ, ContDiffOn ℝ n g (Ioi (0 : ℝ)) := fun n => (hg1_cd n).sub (hg2_cd n)
  let S1 : PowerSeries ℂ := scaleSeries (P.M : ℂ) (emSeriesShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1))
  let S2 : PowerSeries ℂ := ∑ n ∈ Finset.range (d.1 + 2),
    PowerSeries.C ((P.M : ℂ) ^ n * emTermShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) n) *
      PowerSeries.X ^ n
  have hS_eq : S1 - S2 = PowerSeries.X ^ (d.1 + 1) * tailSeriesDR P d r := by
    ext m
    rw [map_sub, map_sum]
    have hS1m : PowerSeries.coeff m S1 =
        (P.M : ℂ) ^ m * emTermShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) m := by
      simp [S1, scaleSeries, emSeriesShift]
    have hS2m : ∑ n ∈ Finset.range (d.1 + 2),
          PowerSeries.coeff m (PowerSeries.C ((P.M : ℂ) ^ n * emTermShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) n) *
            PowerSeries.X ^ n) =
        if m < d.1 + 2 then (P.M : ℂ) ^ m * emTermShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) m else 0 := by
      simp_rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, mul_ite, mul_one, mul_zero]
      split_ifs with hm
      · rw [Finset.sum_eq_single m]
        · simp
        · intro b _ hbm; simp [Ne.symm hbm]
        · intro hnot; exact absurd (Finset.mem_range.mpr hm) hnot
      · refine Finset.sum_eq_zero fun b hb => ?_
        have hne : m ≠ b := by have := Finset.mem_range.mp hb; omega
        simp [hne]
    rw [hS1m, hS2m, PowerSeries.coeff_X_pow_mul']
    by_cases hm : m < d.1 + 2
    · simp only [hm, ↓reduceIte, sub_self]
      split_ifs with hge
      · have hmeq : m - (d.1 + 1) = 0 := by omega
        rw [hmeq]; simp [tailSeriesDR]
      · rfl
    · have hge : d.1 + 1 ≤ m := by omega
      have hsub_ne : m - (d.1 + 1) ≠ 0 := by omega
      have hadd : d.1 + 1 + (m - (d.1 + 1)) = m := by omega
      simp only [hm, hge, ↓reduceIte, sub_zero, tailSeriesDR, PowerSeries.coeff_mk, hsub_ne, hadd]
  have hg_asymp : ∀ k : ℕ, HasAsympExp (iteratedDeriv k g) (d_u^[k] (PowerSeries.X ^ (d.1 + 1) * tailSeriesDR P d r)) := by
    intro k
    rw [← hS_eq, d_u_iter_sub']
    have hg1_k : HasAsympExp (iteratedDeriv k g1) (d_u^[k] S1) := by
      have hbase : ∀ m : ℕ, HasAsympExp
          (iteratedDeriv m (fun v : ℝ => sumScaleShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) v -
            (v : ℂ) * (∫ y in Ioi (0 : ℝ), hPow d.1 y)))
          (d_u^[m] (emSeriesShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1))) := fun m => by
        simpa only [hq_cast] using sumScaleShift_iteratedDeriv_hasAsympExp hq0 hq1 (hPow_expDecaySmooth d.1) m
      exact hasAsympExp_comp_div_const hMpos hbase k
    have hg2_k : HasAsympExp (iteratedDeriv k g2) (d_u^[k] S2) := by
      rw [d_u_iter_sum']
      have hsum_asymp : HasAsympExp
          (fun u : ℝ => ∑ n ∈ Finset.range (d.1 + 2),
            ((P.M : ℂ) ^ n * emTermShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) n) *
              iteratedDeriv k (fun v : ℝ => (v : ℂ)⁻¹ ^ n) u)
          (∑ n ∈ Finset.range (d.1 + 2), d_u^[k]
            (PowerSeries.C ((P.M : ℂ) ^ n * emTermShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) n) *
              PowerSeries.X ^ n)) := by
        refine hasAsympExp_sum' _ _ _ fun n _ => ?_
        rw [d_u_iter_C_mul']
        exact (HasAsympExp.const _).mul (iteratedDeriv_inv_pow_hasAsympExp' n k)
      refine hasAsympExp_congr_atTop' ?_ hsum_asymp
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      have hinv_cd : ContDiffAt ℝ k (fun v : ℝ => (v : ℂ)⁻¹) u :=
        (Complex.ofRealCLM.contDiff.contDiffAt.inv (Complex.ofReal_ne_zero.mpr hu.ne')).of_le le_top
      dsimp only [g2]
      rw [iteratedDeriv_finset_sum' _ _ k fun n _ => contDiffAt_const.mul (hinv_cd.pow n)]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [iteratedDeriv_const_mul_field]
    refine hasAsympExp_congr_atTop' ?_ (hasAsympExp_sub' hg1_k hg2_k)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    exact (iteratedDeriv_fun_sub ((hg1_cd k).contDiffAt (isOpen_Ioi.mem_nhds hu))
      ((hg2_cd k).contDiffAt (isOpen_Ioi.mem_nhds hu))).symm
  exact hasAsympExp_pow_mul_of_X_pow_mul (d.1 + 1) hg_cd hg_asymp j

/-- **All-Orders Asymptotic Expansion of `remFun P`**:
Every `u`-derivative of `remFun P` matches `d_u^[j] (formalSeries (borelPhi P))`. -/
private lemma remFun_hasAsympExp (P : Quasipoly) (j : ℕ) :
    HasAsympExp (iteratedDeriv j (remFun P)) (d_u^[j] (formalSeries (borelPhi P))) := by
  rw [formalSeries_borelPhi P, d_u_iter_sum']
  have hsum : HasAsympExp
      (fun u : ℝ => ∑ d : Fin (P.D + 1), ∑ r ∈ Finset.Icc 1 P.M,
        P.c d r * iteratedDeriv j (tailFunDR P d r) u)
      (∑ d : Fin (P.D + 1), d_u^[j]
        (∑ r ∈ Finset.Icc 1 P.M, PowerSeries.C (P.c d r) * tailSeriesDR P d r)) := by
    refine hasAsympExp_sum' _ _ _ fun d _ => ?_
    rw [d_u_iter_sum']
    refine hasAsympExp_sum' _ _ _ fun r hr => ?_
    rw [d_u_iter_C_mul']
    exact (HasAsympExp.const (P.c d r)).mul (tailFunDR_hasAsympExp P d hr j)
  refine hasAsympExp_congr_atTop' ?_ hsum
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  symm
  rw [show remFun P = fun v => ∑ d : Fin (P.D + 1), ∑ r ∈ Finset.Icc 1 P.M, P.c d r * tailFunDR P d r v from rfl]
  have hcd_d : ∀ d ∈ (Finset.univ : Finset (Fin (P.D + 1))),
      ContDiffAt ℝ j (fun v : ℝ => ∑ r ∈ Finset.Icc 1 P.M, P.c d r * tailFunDR P d r v) u :=
    fun d _ => ContDiffAt.sum fun r hr =>
      contDiffAt_const.mul ((tailFunDR_contDiffOn P d (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2 j).contDiffAt
        (isOpen_Ioi.mem_nhds hu))
  rw [iteratedDeriv_finset_sum' _ _ j hcd_d]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [iteratedDeriv_finset_sum' _ _ j fun r hr =>
    contDiffAt_const.mul ((tailFunDR_contDiffOn P d (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2 j).contDiffAt
      (isOpen_Ioi.mem_nhds hu))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [iteratedDeriv_const_mul_field]

/-! ### 6B. Coordinate Transfers (`log u → u`, `u⁻¹` Homogenization, Affine Shift) -/

end RemFunAsymp

/-! ##### Rank-3 Residue Independence on `ω5` and 3-Tuple `SharedLatticeSimplePoleFamily` -/

private lemma borelPref_ne_zero' (d : ℕ) : borelPref d ≠ 0 := by
  unfold borelPref
  have h1 : (-2 : ℂ) ≠ 0 := by norm_num
  have h2 : (-1 : ℂ) ^ (d + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : ((d + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
  have h4 : ((d + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (d + 1)
  have h5 : Complex.I ^ (d + 1) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have h6 : (2 * (Real.pi : ℂ)) ^ (d + 1) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4) h5) h6

private lemma macMahonQP_borelAmp (m : ℕ) (hm : 1 ≤ m) :
    macMahonQP.borelAmp ⟨1, by decide⟩ m = (sigmaNat 2 m : ℂ) := by
  unfold Quasipoly.borelAmp
  have hcdft : ∀ k : ℕ, macMahonQP.cDft ⟨1, by decide⟩ k = 1 := fun k => by
    unfold Quasipoly.cDft Quasipoly.cOdd macMahonQP
    simp only [Nat.factorial_one, Nat.cast_one, div_one, Finset.Icc_self, Finset.sum_singleton,
      one_mul, pow_one, neg_mul, one_mul, sub_neg_eq_add]
    have harg : -(((2 * Real.pi * 1 * (k : ℝ) : ℝ) : ℂ) * Complex.I) =
        (-(k : ℤ) : ℤ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [harg, Complex.exp_int_mul_two_pi_mul_I]
    norm_num
  simp_rw [hcdft, mul_one]
  have hm0 : m ≠ 0 := by omega
  simp only [sigmaNat, hm0, ↓reduceIte, Nat.cast_sum, Nat.cast_pow]
  exact Nat.sum_div_divisors m (fun x : ℕ => (x : ℂ) ^ 2)

private lemma partsMod5OneQP_cDft (k : ℕ) :
    partsMod5OneQP.cDft 0 k = -(Complex.I / 5) * (Real.sin (2 * Real.pi * (k : ℝ) / 5) : ℂ) := by
  unfold Quasipoly.cDft
  have hIcc : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  change ((Nat.factorial 0 : ℂ) / (5 : ℂ)) * ∑ r ∈ Finset.Icc 1 5,
    partsMod5OneQP.cOdd 0 r * Complex.exp (-((2 * Real.pi * (r : ℝ) * (k : ℝ) / 5 : ℝ) : ℂ) * Complex.I) = _
  rw [hIcc]
  have hc1 : partsMod5OneQP.cOdd 0 1 = 1 / 2 := by unfold Quasipoly.cOdd partsMod5OneQP; norm_num
  have hc2 : partsMod5OneQP.cOdd 0 2 = 0 := by unfold Quasipoly.cOdd partsMod5OneQP; norm_num
  have hc3 : partsMod5OneQP.cOdd 0 3 = 0 := by unfold Quasipoly.cOdd partsMod5OneQP; norm_num
  have hc4 : partsMod5OneQP.cOdd 0 4 = -(1 / 2) := by unfold Quasipoly.cOdd partsMod5OneQP; norm_num
  have hc5 : partsMod5OneQP.cOdd 0 5 = 0 := by unfold Quasipoly.cOdd partsMod5OneQP; norm_num
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
    OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true, hc1, hc2, hc3, hc4, hc5,
    zero_mul, add_zero, zero_add, Nat.factorial_zero, Nat.cast_one]
  set θ : ℝ := 2 * Real.pi * (k : ℝ) / 5
  have he1 : -((2 * Real.pi * (1 : ℝ) * (k : ℝ) / 5 : ℝ) : ℂ) * Complex.I = -((θ : ℂ) * Complex.I) := by
    dsimp only [θ]; push_cast; ring
  have he4 : -((2 * Real.pi * (4 : ℝ) * (k : ℝ) / 5 : ℝ) : ℂ) * Complex.I =
      ((θ : ℂ) * Complex.I) + (-(k : ℤ) : ℤ) * (2 * Real.pi * Complex.I) := by
    dsimp only [θ]; push_cast; ring
  rw [show ((4 : ℕ) : ℝ) = 4 by norm_num, he1, he4,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [show (Real.sin θ : ℂ) = Complex.sin (θ : ℂ) from Complex.ofReal_sin θ, Complex.sin]
  ring_nf; rw [Complex.I_sq]; ring

private lemma partsMod5TwoQP_cDft (k : ℕ) :
    partsMod5TwoQP.cDft 0 k = -(Complex.I / 5) * (Real.sin (4 * Real.pi * (k : ℝ) / 5) : ℂ) := by
  unfold Quasipoly.cDft
  have hIcc : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  change ((Nat.factorial 0 : ℂ) / (5 : ℂ)) * ∑ r ∈ Finset.Icc 1 5,
    partsMod5TwoQP.cOdd 0 r * Complex.exp (-((2 * Real.pi * (r : ℝ) * (k : ℝ) / 5 : ℝ) : ℂ) * Complex.I) = _
  rw [hIcc]
  have hc1 : partsMod5TwoQP.cOdd 0 1 = 0 := by unfold Quasipoly.cOdd partsMod5TwoQP; norm_num
  have hc2 : partsMod5TwoQP.cOdd 0 2 = 1 / 2 := by unfold Quasipoly.cOdd partsMod5TwoQP; norm_num
  have hc3 : partsMod5TwoQP.cOdd 0 3 = -(1 / 2) := by unfold Quasipoly.cOdd partsMod5TwoQP; norm_num
  have hc4 : partsMod5TwoQP.cOdd 0 4 = 0 := by unfold Quasipoly.cOdd partsMod5TwoQP; norm_num
  have hc5 : partsMod5TwoQP.cOdd 0 5 = 0 := by unfold Quasipoly.cOdd partsMod5TwoQP; norm_num
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
    OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true, hc1, hc2, hc3, hc4, hc5,
    zero_mul, add_zero, zero_add, Nat.factorial_zero, Nat.cast_one]
  set θ : ℝ := 4 * Real.pi * (k : ℝ) / 5
  have he2 : -((2 * Real.pi * (2 : ℝ) * (k : ℝ) / 5 : ℝ) : ℂ) * Complex.I = -((θ : ℂ) * Complex.I) := by
    dsimp only [θ]; push_cast; ring
  have he3 : -((2 * Real.pi * (3 : ℝ) * (k : ℝ) / 5 : ℝ) : ℂ) * Complex.I =
      ((θ : ℂ) * Complex.I) + (-(k : ℤ) : ℤ) * (2 * Real.pi * Complex.I) := by
    dsimp only [θ]; push_cast; ring
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, show ((3 : ℕ) : ℝ) = 3 by norm_num, he2, he3,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [show (Real.sin θ : ℂ) = Complex.sin (θ : ℂ) from Complex.ofReal_sin θ, Complex.sin]
  ring_nf; rw [Complex.I_sq]; ring

private lemma eleven_pow_mod_five (k : ℕ) : 11 ^ k % 5 = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih => rw [pow_succ, Nat.mul_mod, ih]

private lemma partsMod5_borelAmp_eleven_pow (P : Quasipoly) (hM5 : P.M = 5) (_hD0 : P.D = 0) (k : ℕ) :
    P.borelAmp 0 (11 ^ k) = (sigmaNat 1 (11 ^ k) : ℂ) * P.cDft 0 1 := by
  unfold Quasipoly.borelAmp
  have h11p : Nat.Prime 11 := by decide
  have hdiv : (11 ^ k).divisors = (Finset.range (k + 1)).map ⟨(11 ^ ·), Nat.pow_right_injective (by norm_num)⟩ :=
    Nat.divisors_prime_pow h11p k
  have hcdft_eq : ∀ d ∈ (11 ^ k).divisors, P.cDft 0 d = P.cDft 0 1 := by
    intro d hd
    rw [hdiv, Finset.mem_map] at hd
    obtain ⟨a, _, rfl⟩ := hd
    dsimp only [Function.Embedding.coeFn_mk]
    rw [← P.cDft_mod 0 (11 ^ a), hM5, eleven_pow_mod_five a]
  simp only [Fin.val_zero, zero_add]
  calc ∑ d ∈ (11 ^ k).divisors, (((11 ^ k) / d : ℕ) : ℂ) ^ 1 * P.cDft 0 d
      = ∑ d ∈ (11 ^ k).divisors, (((11 ^ k) / d : ℕ) : ℂ) * P.cDft 0 1 :=
        Finset.sum_congr rfl fun d hd => by rw [pow_one, hcdft_eq d hd]
    _ = (∑ d ∈ (11 ^ k).divisors, (((11 ^ k) / d : ℕ) : ℂ)) * P.cDft 0 1 := (Finset.sum_mul _ _ _).symm
    _ = (sigmaNat 1 (11 ^ k) : ℂ) * P.cDft 0 1 := by
        congr 1
        have hne : 11 ^ k ≠ 0 := pow_ne_zero k (by norm_num)
        simp only [sigmaNat, hne, ↓reduceIte, Nat.cast_sum, pow_one]
        exact Nat.sum_div_divisors (11 ^ k) (fun x : ℕ => (x : ℂ))

private lemma partsMod5_borelAmp_two_mul_eleven_pow (P : Quasipoly) (hM5 : P.M = 5) (_hD0 : P.D = 0) (k : ℕ) :
    P.borelAmp 0 (2 * 11 ^ k) = (sigmaNat 1 (11 ^ k) : ℂ) * (2 * P.cDft 0 1 + P.cDft 0 2) := by
  unfold Quasipoly.borelAmp
  have h11p : Nat.Prime 11 := by decide
  have hcop : Nat.Coprime 2 (11 ^ k) := (by decide : Nat.Coprime 2 11).pow_right k
  have hdiv_union : (2 * 11 ^ k).divisors = (11 ^ k).divisors ∪ (11 ^ k).divisors.image (2 * ·) := by
    ext d
    simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
    have hne11 : 11 ^ k ≠ 0 := pow_ne_zero k (by norm_num)
    have hne2 : 2 * 11 ^ k ≠ 0 := mul_ne_zero (by norm_num) hne11
    constructor
    · rintro ⟨hdvd, _⟩
      by_cases h2d : 2 ∣ d
      · right
        obtain ⟨b, rfl⟩ := h2d
        refine ⟨b, ⟨?_, hne11⟩, rfl⟩
        exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp hdvd
      · left
        have hcop_2d : Nat.Coprime d 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h2d).symm
        exact ⟨hcop_2d.dvd_of_dvd_mul_left hdvd, hne11⟩
    · rintro (⟨hdvd, _⟩ | ⟨b, ⟨hb, _⟩, rfl⟩)
      · exact ⟨dvd_mul_of_dvd_right hdvd 2, hne2⟩
      · exact ⟨mul_dvd_mul_left 2 hb, hne2⟩
  have hdisj : Disjoint (11 ^ k).divisors ((11 ^ k).divisors.image (2 * ·)) := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hd2
    have hdvd : 2 * b ∣ 11 ^ k := Nat.dvd_of_mem_divisors hd1
    have h2dvd : 2 ∣ 11 ^ k := dvd_trans (dvd_mul_right 2 b) hdvd
    have h2_11 : 2 ∣ 11 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2dvd
    omega
  rw [hdiv_union, Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ h => by omega)]
  have h11div : (11 ^ k).divisors = (Finset.range (k + 1)).map ⟨(11 ^ ·), Nat.pow_right_injective (by norm_num)⟩ :=
    Nat.divisors_prime_pow h11p k
  have hmod1 : ∀ d ∈ (11 ^ k).divisors, d % 5 = 1 := by
    intro d hd
    rw [h11div, Finset.mem_map] at hd
    obtain ⟨a, _, rfl⟩ := hd
    exact eleven_pow_mod_five a
  have hS1 : (∑ d ∈ (11 ^ k).divisors, (((2 * 11 ^ k) / d : ℕ) : ℂ) ^ 1 * P.cDft 0 d) =
      (sigmaNat 1 (11 ^ k) : ℂ) * (2 * P.cDft 0 1) := by
    have hterm : ∀ d ∈ (11 ^ k).divisors,
        (((2 * 11 ^ k) / d : ℕ) : ℂ) ^ 1 * P.cDft 0 d = (((11 ^ k) / d : ℕ) : ℂ) * (2 * P.cDft 0 1) := by
      intro d hd
      have hdvd : d ∣ 11 ^ k := Nat.dvd_of_mem_divisors hd
      rw [Nat.mul_div_assoc 2 hdvd, pow_one, ← P.cDft_mod 0 d, hM5, hmod1 d hd]
      push_cast; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    congr 1
    have hne : 11 ^ k ≠ 0 := pow_ne_zero k (by norm_num)
    simp only [sigmaNat, hne, ↓reduceIte, Nat.cast_sum, pow_one]
    exact Nat.sum_div_divisors (11 ^ k) (fun x : ℕ => (x : ℂ))
  have hS2 : (∑ d ∈ (11 ^ k).divisors, (((2 * 11 ^ k) / (2 * d) : ℕ) : ℂ) ^ 1 * P.cDft 0 (2 * d)) =
      (sigmaNat 1 (11 ^ k) : ℂ) * P.cDft 0 2 := by
    have hterm : ∀ d ∈ (11 ^ k).divisors,
        (((2 * 11 ^ k) / (2 * d) : ℕ) : ℂ) ^ 1 * P.cDft 0 (2 * d) = (((11 ^ k) / d : ℕ) : ℂ) * P.cDft 0 2 := by
      intro d hd
      rw [Nat.mul_div_mul_left _ _ (by norm_num : 0 < 2), pow_one, ← P.cDft_mod 0 (2 * d), hM5,
        Nat.mul_mod, hmod1 d hd]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
    congr 1
    have hne : 11 ^ k ≠ 0 := pow_ne_zero k (by norm_num)
    simp only [sigmaNat, hne, ↓reduceIte, Nat.cast_sum, pow_one]
    exact Nat.sum_div_divisors (11 ^ k) (fun x : ℕ => (x : ℂ))
  simp only [Fin.val_zero, zero_add]
  rw [hS1, hS2]; ring

/-- Helper: if a univariate polynomial over a domain vanishes on a strictly increasing sequence of `ℂ` points
`fun k => (λ k : ℂ)`, then all its coefficients vanish! -/
private lemma poly_coeffs_zero_of_strictMono_roots {R : Type*} [CommRing R] [IsDomain R] [Algebra ℂ R]
    (hinj : Function.Injective (algebraMap ℂ R))
    {r : ℕ} {c : Fin (r + 1) → R} {seq : ℕ → ℝ} (hseq : StrictMono seq)
    (hroot : ∀ k : ℕ, ∑ j : Fin (r + 1), algebraMap ℂ R ((-(seq k : ℂ)) ^ j.val) * c j = 0) :
    ∀ j : Fin (r + 1), c j = 0 := by
  classical
  let p : Polynomial R := ∑ j : Fin (r + 1), Polynomial.monomial j.1 (c j)
  have hp_deg : p.natDegree ≤ r := by
    refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun j _ => ?_)
    exact (Polynomial.natDegree_monomial_le (c j)).trans (Nat.lt_succ_iff.mp j.isLt)
  have hp_eval : ∀ k : ℕ, p.eval (algebraMap ℂ R (-(seq k : ℂ))) = 0 := fun k => by
    dsimp only [p]
    change Polynomial.evalRingHom _ (∑ j : Fin (r + 1), _) = 0
    rw [map_sum]
    have hterm : ∀ j : Fin (r + 1),
        (Polynomial.evalRingHom (algebraMap ℂ R (-(seq k : ℂ)))) (Polynomial.monomial j.1 (c j)) =
          algebraMap ℂ R ((-(seq k : ℂ)) ^ j.val) * c j := fun j => by
      simp only [Polynomial.coe_evalRingHom, Polynomial.eval_monomial, map_pow, mul_comm]
    simp_rw [hterm]
    exact hroot k
  have hp0 : p = 0 := by
    by_contra hp_ne
    let pts : Finset R := (Finset.range (r + 2)).image (fun k => algebraMap ℂ R (-(seq k : ℂ)))
    have hpts_inj : Function.Injective (fun k : ℕ => algebraMap ℂ R (-(seq k : ℂ))) := fun a b hab =>
      hseq.injective (Complex.ofReal_injective (neg_injective (hinj hab)))
    have hpts_card : pts.card = r + 2 := by
      dsimp only [pts]
      rw [Finset.card_image_of_injective _ hpts_inj, Finset.card_range]
    have hsub : pts ⊆ p.roots.toFinset := by
      intro x hx
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp_ne, Polynomial.IsRoot.def]
      exact hp_eval k
    have hcard_le : pts.card ≤ p.natDegree :=
      (Finset.card_le_card hsub).trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' p))
    omega
  intro j
  have hcoeff : p.coeff j.1 = c j := by
    dsimp only [p]
    change (Polynomial.lcoeff R j.1) (∑ i : Fin (r + 1), _) = _
    rw [map_sum]
    simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      have hne : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
      simp [hne.symm]
    · intro h; exact (h (Finset.mem_univ j)).elim
  rw [← hcoeff, hp0, Polynomial.coeff_zero]

/-- The 3-tuple of simple-pole Borel transforms `(ΦSimple1 macMahonQP, ΦSimple0 partsMod5OneQP, ΦSimple0 partsMod5TwoQP)`. -/
private def φ3 : Fin 3 → ℂ → ℂ
  | ⟨0, _⟩ => ΦSimple1 macMahonQP rfl
  | ⟨1, _⟩ => ΦSimple0 partsMod5OneQP
  | ⟨2, _⟩ => ΦSimple0 partsMod5TwoQP

/-- Exact shared-lattice residues on `ω5 m = 4π²(m + 1)/5` for the 3-tuple `φ3`. -/
private def res3 : Fin 3 → ℕ → ℂ
  | ⟨0, _⟩, m =>
      if (m + 1) % 5 = 0 then
        (-(1 / 6) : ℂ) * borelPref 1 * macMahonQP.borelAmp ⟨1, by decide⟩ ((m + 1) / 5)
      else 0
  | ⟨1, _⟩, m => (1 / 2 : ℂ) * borelPref 0 * partsMod5OneQP.borelAmp 0 (m + 1)
  | ⟨2, _⟩, m => (1 / 2 : ℂ) * borelPref 0 * partsMod5TwoQP.borelAmp 0 (m + 1)

/-- **Rank-3 Residue Independence on `ω5`**:
Using the 3 explicit subsequences `m + 1 = 11^k`, `m + 1 = 2 * 11^k`, and `m + 1 = 5 * (k + 1)`,
the shared-lattice Stokes operator vanishes at every `m` iff EVERY partial derivative of `P` vanishes! -/
private lemma rank3_macMahon_partsMod5 {r : ℕ}
    (P : MvPolynomial (Fin 3 × Fin (r + 1)) (Polynomial ℂ))
    (hD : ∀ m : ℕ, ∑ i : Fin 3, ∑ j : Fin (r + 1),
      MvPolynomial.C (Polynomial.C (res3 i m * (-(ω5 m : ℂ)) ^ j.val)) * MvPolynomial.pderiv (i, j) P = 0) :
    ∀ ij : Fin 3 × Fin (r + 1), MvPolynomial.pderiv ij P = 0 := by
  let R := MvPolynomial (Fin 3 × Fin (r + 1)) (Polynomial ℂ)
  let ιC : ℂ →+* R := MvPolynomial.C.comp Polynomial.C
  have hιC_inj : Function.Injective ιC :=
    fun _ _ hab => Polynomial.C_injective (MvPolynomial.C_injective _ _ hab)
  have halg_eq : ∀ z : ℂ, algebraMap ℂ R z = MvPolynomial.C (Polynomial.C z) := fun z => by
    rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) R, Polynomial.algebraMap_eq, MvPolynomial.algebraMap_eq]
  -- Write `s₁ = sin(2π/5) > 0`, `s₂ = sin(4π/5)`.
  let s₁ : ℂ := (Real.sin (2 * Real.pi / 5) : ℂ)
  let s₂ : ℂ := (Real.sin (4 * Real.pi / 5) : ℂ)
  have hs₁_pos : 0 < Real.sin (2 * Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hdet_ne : -(s₁ ^ 2 + s₂ ^ 2) ≠ 0 := by
    have hre : 0 < Real.sin (2 * Real.pi / 5) ^ 2 + Real.sin (4 * Real.pi / 5) ^ 2 := by
      nlinarith [sq_nonneg (Real.sin (4 * Real.pi / 5))]
    have hcast : -(s₁ ^ 2 + s₂ ^ 2) = ((-(Real.sin (2 * Real.pi / 5) ^ 2 + Real.sin (4 * Real.pi / 5) ^ 2) : ℝ) : ℂ) := by
      dsimp only [s₁, s₂]; push_cast; ring
    rw [hcast]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  have hsin8 : Real.sin (4 * Real.pi * (2 : ℝ) / 5) = -Real.sin (2 * Real.pi / 5) := by
    have harg : 4 * Real.pi * (2 : ℝ) / 5 = -(2 * Real.pi / 5) + 2 * Real.pi := by ring
    rw [harg, Real.sin_add_two_pi, Real.sin_neg]
  have hc1_1 : partsMod5OneQP.cDft 0 1 = -(Complex.I / 5) * s₁ := by
    rw [partsMod5OneQP_cDft 1]; simp [s₁]
  have hc1_2 : partsMod5OneQP.cDft 0 2 = -(Complex.I / 5) * s₂ := by
    have harg : 2 * Real.pi * ((2 : ℕ) : ℝ) / 5 = 4 * Real.pi / 5 := by push_cast; ring
    rw [partsMod5OneQP_cDft 2, harg]
  have hc2_1 : partsMod5TwoQP.cDft 0 1 = -(Complex.I / 5) * s₂ := by
    rw [partsMod5TwoQP_cDft 1]; simp [s₂]
  have hc2_2 : partsMod5TwoQP.cDft 0 2 = (Complex.I / 5) * s₁ := by
    rw [partsMod5TwoQP_cDft 2]; simp only [Nat.cast_ofNat, hsin8, Complex.ofReal_neg]; dsimp only [s₁]; ring
  have hpref0_ne : ((1 / 2 : ℂ) * borelPref 0 * (-(Complex.I / 5))) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (borelPref_ne_zero' 0))
      (neg_ne_zero.mpr (div_ne_zero Complex.I_ne_zero (by norm_num)))
  -- Subsequence 1: `m₁ k = 11^k - 1` gives `∀ j, s₁ * pderiv (1, j) P + s₂ * pderiv (2, j) P = 0`!
  have hlin1 : ∀ j : Fin (r + 1),
      algebraMap ℂ R s₁ * MvPolynomial.pderiv ((1 : Fin 3), j) P +
        algebraMap ℂ R s₂ * MvPolynomial.pderiv ((2 : Fin 3), j) P = 0 := by
    have hseq : StrictMono (fun k : ℕ => ω5 (11 ^ k - 1)) := fun a b hab => by
      refine ω5_strictMono ?_
      have h1 : 1 ≤ 11 ^ a := Nat.one_le_pow a 11 (by norm_num)
      have hlt : 11 ^ a < 11 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
      omega
    refine poly_coeffs_zero_of_strictMono_roots (by intro x y h; rw [halg_eq, halg_eq] at h; exact hιC_inj h)
      hseq fun k => ?_
    have h11_pos : 1 ≤ 11 ^ k := Nat.one_le_pow k 11 (by norm_num)
    have hsucc : (11 ^ k - 1) + 1 = 11 ^ k := Nat.sub_add_cancel h11_pos
    have hmod5 : ((11 ^ k - 1) + 1) % 5 = 1 := by rw [hsucc, eleven_pow_mod_five k]
    have hres0 : res3 (0 : Fin 3) (11 ^ k - 1) = 0 := by
      simp [res3, hmod5]
    have hres1 : res3 (1 : Fin 3) (11 ^ k - 1) =
        ((1 / 2 : ℂ) * borelPref 0 * (-(Complex.I / 5)) * (sigmaNat 1 (11 ^ k) : ℂ)) * s₁ := by
      simp only [res3, hsucc, partsMod5_borelAmp_eleven_pow partsMod5OneQP rfl rfl k, hc1_1]; ring
    have hres2 : res3 (2 : Fin 3) (11 ^ k - 1) =
        ((1 / 2 : ℂ) * borelPref 0 * (-(Complex.I / 5)) * (sigmaNat 1 (11 ^ k) : ℂ)) * s₂ := by
      simp only [res3, hsucc, partsMod5_borelAmp_eleven_pow partsMod5TwoQP rfl rfl k, hc2_1]; ring
    have hsig_ne : (sigmaNat 1 (11 ^ k) : ℂ) ≠ 0 := by
      have hpos : 0 < sigmaNat 1 (11 ^ k) := by
        have hne : 11 ^ k ≠ 0 := by omega
        simp only [sigmaNat, hne, ↓reduceIte]
        exact Finset.sum_pos (fun d hd => pow_pos (Nat.pos_of_mem_divisors hd) 1)
          ⟨1, Nat.one_mem_divisors.mpr hne⟩
      exact Nat.cast_ne_zero.mpr hpos.ne'
    let fac : ℂ := (1 / 2 : ℂ) * borelPref 0 * (-(Complex.I / 5)) * (sigmaNat 1 (11 ^ k) : ℂ)
    have hfac_ne : algebraMap ℂ R fac ≠ 0 := by
      intro h0
      have : fac = 0 := by
        rw [halg_eq] at h0; exact hιC_inj (h0.trans (map_zero ιC).symm)
      exact mul_ne_zero hpref0_ne hsig_ne this
    have hDm := hD (11 ^ k - 1)
    rw [Fin.sum_univ_three] at hDm
    simp only [hres0, zero_mul, map_zero, Finset.sum_const_zero, zero_add] at hDm
    have hfactored : algebraMap ℂ R fac *
        (∑ j : Fin (r + 1), algebraMap ℂ R ((-(ω5 (11 ^ k - 1) : ℂ)) ^ j.val) *
          (algebraMap ℂ R s₁ * MvPolynomial.pderiv ((1 : Fin 3), j) P +
            algebraMap ℂ R s₂ * MvPolynomial.pderiv ((2 : Fin 3), j) P)) = 0 := by
      rw [← hDm, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hres1, hres2, ← halg_eq, ← halg_eq]
      dsimp only [fac]
      simp only [map_mul]
      ring
    exact (mul_eq_zero.mp hfactored).resolve_left hfac_ne
  -- Subsequence 2: `m₂ k = 2 * 11^k - 1` gives `∀ j, (2 s₁ + s₂) * pderiv (1, j) P + (2 s₂ - s₁) * pderiv (2, j) P = 0`!
  have hlin2 : ∀ j : Fin (r + 1),
      algebraMap ℂ R (2 * s₁ + s₂) * MvPolynomial.pderiv ((1 : Fin 3), j) P +
        algebraMap ℂ R (2 * s₂ - s₁) * MvPolynomial.pderiv ((2 : Fin 3), j) P = 0 := by
    have hseq : StrictMono (fun k : ℕ => ω5 (2 * 11 ^ k - 1)) := fun a b hab => by
      refine ω5_strictMono ?_
      have h1 : 1 ≤ 11 ^ a := Nat.one_le_pow a 11 (by norm_num)
      have hlt : 11 ^ a < 11 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
      omega
    refine poly_coeffs_zero_of_strictMono_roots (by intro x y h; rw [halg_eq, halg_eq] at h; exact hιC_inj h)
      hseq fun k => ?_
    have h11_pos : 1 ≤ 11 ^ k := Nat.one_le_pow k 11 (by norm_num)
    have hsucc : (2 * 11 ^ k - 1) + 1 = 2 * 11 ^ k := by omega
    have hmod5 : ((2 * 11 ^ k - 1) + 1) % 5 = 2 := by
      rw [hsucc, Nat.mul_mod, eleven_pow_mod_five k]
    have hres0 : res3 (0 : Fin 3) (2 * 11 ^ k - 1) = 0 := by
      simp [res3, hmod5]
    have hres1 : res3 (1 : Fin 3) (2 * 11 ^ k - 1) =
        ((1 / 2 : ℂ) * borelPref 0 * (-(Complex.I / 5)) * (sigmaNat 1 (11 ^ k) : ℂ)) * (2 * s₁ + s₂) := by
      simp only [res3, hsucc, partsMod5_borelAmp_two_mul_eleven_pow partsMod5OneQP rfl rfl k, hc1_1, hc1_2]; ring
    have hres2 : res3 (2 : Fin 3) (2 * 11 ^ k - 1) =
        ((1 / 2 : ℂ) * borelPref 0 * (-(Complex.I / 5)) * (sigmaNat 1 (11 ^ k) : ℂ)) * (2 * s₂ - s₁) := by
      simp only [res3, hsucc, partsMod5_borelAmp_two_mul_eleven_pow partsMod5TwoQP rfl rfl k, hc2_1, hc2_2]; ring
    have hsig_ne : (sigmaNat 1 (11 ^ k) : ℂ) ≠ 0 := by
      have hpos : 0 < sigmaNat 1 (11 ^ k) := by
        have hne : 11 ^ k ≠ 0 := by omega
        simp only [sigmaNat, hne, ↓reduceIte]
        exact Finset.sum_pos (fun d hd => pow_pos (Nat.pos_of_mem_divisors hd) 1)
          ⟨1, Nat.one_mem_divisors.mpr hne⟩
      exact Nat.cast_ne_zero.mpr hpos.ne'
    let fac : ℂ := (1 / 2 : ℂ) * borelPref 0 * (-(Complex.I / 5)) * (sigmaNat 1 (11 ^ k) : ℂ)
    have hfac_ne : algebraMap ℂ R fac ≠ 0 := by
      intro h0
      have : fac = 0 := by rw [halg_eq] at h0; exact hιC_inj (h0.trans (map_zero ιC).symm)
      exact mul_ne_zero hpref0_ne hsig_ne this
    have hDm := hD (2 * 11 ^ k - 1)
    rw [Fin.sum_univ_three] at hDm
    simp only [hres0, zero_mul, map_zero, Finset.sum_const_zero, zero_add] at hDm
    have hfactored : algebraMap ℂ R fac *
        (∑ j : Fin (r + 1), algebraMap ℂ R ((-(ω5 (2 * 11 ^ k - 1) : ℂ)) ^ j.val) *
          (algebraMap ℂ R (2 * s₁ + s₂) * MvPolynomial.pderiv ((1 : Fin 3), j) P +
            algebraMap ℂ R (2 * s₂ - s₁) * MvPolynomial.pderiv ((2 : Fin 3), j) P)) = 0 := by
      rw [← hDm, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hres1, hres2, ← halg_eq, ← halg_eq]
      dsimp only [fac]
      simp only [map_mul]
      ring
    exact (mul_eq_zero.mp hfactored).resolve_left hfac_ne
  -- Solve the invertible 2×2 system (`det = -(s₁² + s₂²) ≠ 0`) to kill `i = 1` and `i = 2`!
  have hdet_R : algebraMap ℂ R (-(s₁ ^ 2 + s₂ ^ 2)) ≠ 0 := by
    intro h0; rw [halg_eq] at h0; exact hdet_ne (hιC_inj (h0.trans (map_zero ιC).symm))
  have hpd1 : ∀ j : Fin (r + 1), MvPolynomial.pderiv ((1 : Fin 3), j) P = 0 := fun j => by
    have hcomb : algebraMap ℂ R (-(s₁ ^ 2 + s₂ ^ 2)) * MvPolynomial.pderiv ((1 : Fin 3), j) P = 0 := by
      have h1 := hlin1 j
      have h2 := hlin2 j
      have halg_id : algebraMap ℂ R (-(s₁ ^ 2 + s₂ ^ 2)) =
          algebraMap ℂ R (2 * s₂ - s₁) * algebraMap ℂ R s₁ -
            algebraMap ℂ R s₂ * algebraMap ℂ R (2 * s₁ + s₂) := by
        rw [← map_mul, ← map_mul, ← map_sub]; congr 1; ring
      rw [halg_id]
      linear_combination algebraMap ℂ R (2 * s₂ - s₁) * h1 - algebraMap ℂ R s₂ * h2
    exact (mul_eq_zero.mp hcomb).resolve_left hdet_R
  have hpd2 : ∀ j : Fin (r + 1), MvPolynomial.pderiv ((2 : Fin 3), j) P = 0 := fun j => by
    have hcomb : algebraMap ℂ R (-(s₁ ^ 2 + s₂ ^ 2)) * MvPolynomial.pderiv ((2 : Fin 3), j) P = 0 := by
      have h1 := hlin1 j
      have h2 := hlin2 j
      have halg_id : algebraMap ℂ R (-(s₁ ^ 2 + s₂ ^ 2)) =
          algebraMap ℂ R s₁ * algebraMap ℂ R (2 * s₂ - s₁) -
            algebraMap ℂ R (2 * s₁ + s₂) * algebraMap ℂ R s₂ := by
        rw [← map_mul, ← map_mul, ← map_sub]; congr 1; ring
      rw [halg_id]
      linear_combination algebraMap ℂ R s₁ * h2 - algebraMap ℂ R (2 * s₁ + s₂) * h1
    exact (mul_eq_zero.mp hcomb).resolve_left hdet_R
  -- Subsequence 3: `m₃ k = 5 * k + 4` kills `i = 0` (`MacMahon`)!
  have hpd0 : ∀ j : Fin (r + 1), MvPolynomial.pderiv ((0 : Fin 3), j) P = 0 := by
    have hseq : StrictMono (fun k : ℕ => ω5 (5 * k + 4)) := fun a b hab => ω5_strictMono (by omega)
    refine poly_coeffs_zero_of_strictMono_roots (by intro x y h; rw [halg_eq, halg_eq] at h; exact hιC_inj h)
      hseq fun k => ?_
    have hDm := hD (5 * k + 4)
    rw [Fin.sum_univ_three] at hDm
    have hzero1 : (∑ j : Fin (r + 1), MvPolynomial.C (Polynomial.C (res3 (1 : Fin 3) (5 * k + 4) *
        (-(ω5 (5 * k + 4) : ℂ)) ^ j.val)) * MvPolynomial.pderiv ((1 : Fin 3), j) P) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hpd1 j, mul_zero]
    have hzero2 : (∑ j : Fin (r + 1), MvPolynomial.C (Polynomial.C (res3 (2 : Fin 3) (5 * k + 4) *
        (-(ω5 (5 * k + 4) : ℂ)) ^ j.val)) * MvPolynomial.pderiv ((2 : Fin 3), j) P) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hpd2 j, mul_zero]
    rw [hzero1, hzero2, add_zero, add_zero] at hDm
    have hmod5 : (5 * k + 4 + 1) % 5 = 0 := by omega
    have hdiv5 : (5 * k + 4 + 1) / 5 = k + 1 := by omega
    have hres0_eq : res3 (0 : Fin 3) (5 * k + 4) = (-(1 / 6) : ℂ) * borelPref 1 * (sigmaNat 2 (k + 1) : ℂ) := by
      simp only [res3, hmod5, ↓reduceIte, hdiv5, macMahonQP_borelAmp (k + 1) (Nat.succ_pos k)]
    have hres0_ne : algebraMap ℂ R (res3 (0 : Fin 3) (5 * k + 4)) ≠ 0 := by
      intro h0
      have h0c : res3 (0 : Fin 3) (5 * k + 4) = 0 := by
        rw [halg_eq] at h0; exact hιC_inj (h0.trans (map_zero ιC).symm)
      rw [hres0_eq] at h0c
      have hsig_ne : (sigmaNat 2 (k + 1) : ℂ) ≠ 0 := by
        have hpos : 0 < sigmaNat 2 (k + 1) := by
          simp only [sigmaNat, Nat.succ_ne_zero, ↓reduceIte]
          exact Finset.sum_pos (fun d hd => pow_pos (Nat.pos_of_mem_divisors hd) 2)
            ⟨1, Nat.one_mem_divisors.mpr (Nat.succ_ne_zero k)⟩
        exact Nat.cast_ne_zero.mpr hpos.ne'
      exact mul_ne_zero (mul_ne_zero (by norm_num) (borelPref_ne_zero' 1)) hsig_ne h0c
    have hfac : algebraMap ℂ R (res3 (0 : Fin 3) (5 * k + 4)) *
        ∑ j : Fin (r + 1), algebraMap ℂ R ((-(ω5 (5 * k + 4) : ℂ)) ^ j.val) *
          MvPolynomial.pderiv ((0 : Fin 3), j) P = 0 := by
      rw [← hDm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← halg_eq, map_mul, mul_assoc]
    exact (mul_eq_zero.mp hfac).resolve_left hres0_ne
  rintro ⟨i, j⟩
  fin_cases i
  · exact hpd0 j
  · exact hpd1 j
  · exact hpd2 j

/-- Complete `SharedLatticeSimplePoleFamily` package for `(MacMahon, Parts ≡ 1 mod 5, Parts ≡ 2 mod 5)` on `ω5`. -/
private def macMahon_partsMod5_sharedFamily :
    SharedLatticeSimplePoleFamily 3 φ3 ω5 res3 where
  α₀ := Real.pi / 4
  θ := Real.pi / 6
  ε := 2 * Real.pi ^ 2 / 5
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := by positivity
  ω_pos := ω5_pos 0
  ω_mono := ω5_strictMono
  analyticOn := fun i z hz => by
    have hnot_lat : ∀ m : ℕ, z ≠ (ω5 m : ℂ) := by
      intro m heq
      exact hz.2 ⟨m, heq.symm⟩
    have hnot_neg : ∀ m : ℕ, z ≠ -(ω5 m : ℂ) := by
      intro m heq
      have hre_z : -(2 * Real.pi ^ 2 / 5) < z.re := by
        rcases hz.1 with hball | hsec
        · have hlt : ‖z‖ < 2 * Real.pi ^ 2 / 5 := by simpa [Metric.mem_ball, dist_zero_right] using hball
          have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
          linarith [neg_abs_le z.re]
        · have hre_pos : 0 < z.re := hsec.1
          have : 0 < 2 * Real.pi ^ 2 / 5 := by positivity
          linarith
      have hω_ge : 4 * Real.pi ^ 2 / 5 ≤ ω5 m := by
        unfold ω5
        have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
        nlinarith [Real.pi_pos]
      have hre_eq : z.re = -ω5 m := by rw [heq]; simp
      linarith [sq_pos_of_pos Real.pi_pos]
    fin_cases i
    · refine ΦSimple1_analyticAt macMahonQP rfl fun k => ?_
      rw [ωBase_macMahon k]
      exact ⟨hnot_lat (5 * k + 4), hnot_neg (5 * k + 4)⟩
    · refine ΦSimple0_analyticAt partsMod5OneQP fun m => ?_
      rw [ωBase_partsMod5One m]
      exact ⟨hnot_lat m, hnot_neg m⟩
    · refine ΦSimple0_analyticAt partsMod5TwoQP fun m => ?_
      rw [ωBase_partsMod5Two m]
      exact ⟨hnot_lat m, hnot_neg m⟩
  pole_res := fun i m => by
    fin_cases i
    · dsimp only [φ3, res3]
      by_cases hdiv : (m + 1) % 5 = 0
      · have hk_eq : 5 * ((m + 1) / 5 - 1) + 4 = m := by omega
        have hk_succ : ((m + 1) / 5 - 1) + 1 = (m + 1) / 5 := by omega
        rw [ite_eq_left_iff.mpr (fun h => (h hdiv).elim)]
        have hpr := ΦSimple1_pole_res macMahonQP rfl ((m + 1) / 5 - 1)
        rw [ωBase_macMahon, hk_eq, hk_succ] at hpr
        exact hpr
      · rw [ite_eq_right_iff.mpr (fun h => (hdiv h).elim)]
        have han : AnalyticAt ℂ (ΦSimple1 macMahonQP rfl) (ω5 m : ℂ) := by
          refine ΦSimple1_analyticAt macMahonQP rfl fun k => ?_
          rw [ωBase_macMahon k]
          constructor
          · intro heq
            have hidx : 5 * k + 4 = m := ω5_strictMono.injective (Complex.ofReal_injective heq).symm
            omega
          · intro heq
            have hre : ω5 m = -ω5 (5 * k + 4) := Complex.ofReal_injective (by simpa using heq)
            linarith [ω5_pos m, ω5_pos (5 * k + 4)]
        refine ⟨ΦSimple1 macMahonQP rfl (ω5 m : ℂ), ?_⟩
        simpa using han.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · dsimp only [φ3, res3]
      simpa [ωBase_partsMod5One m] using ΦSimple0_pole_res partsMod5OneQP m
    · dsimp only [φ3, res3]
      simpa [ωBase_partsMod5Two m] using ΦSimple0_pole_res partsMod5TwoQP m
  expType_plus := fun i => by
    have hθ0 : (0 : ℝ) < Real.pi / 6 := by positivity
    have hθ1 : Real.pi / 6 < Real.pi / 2 := by linarith [Real.pi_pos]
    fin_cases i
    · dsimp only [φ3]; simpa [one_mul] using ΦSimple1_expType macMahonQP rfl hθ0 hθ1 1 (Or.inl rfl)
    · dsimp only [φ3]; simpa [one_mul] using ΦSimple0_expType partsMod5OneQP hθ0 hθ1 1 (Or.inl rfl)
    · dsimp only [φ3]; simpa [one_mul] using ΦSimple0_expType partsMod5TwoQP hθ0 hθ1 1 (Or.inl rfl)
  expType_minus := fun i => by
    have hθ0 : (0 : ℝ) < Real.pi / 6 := by positivity
    have hθ1 : Real.pi / 6 < Real.pi / 2 := by linarith [Real.pi_pos]
    fin_cases i
    · dsimp only [φ3]; simpa [neg_mul] using ΦSimple1_expType macMahonQP rfl hθ0 hθ1 (-1) (Or.inr rfl)
    · dsimp only [φ3]; simpa [neg_mul] using ΦSimple0_expType partsMod5OneQP hθ0 hθ1 (-1) (Or.inr rfl)
    · dsimp only [φ3]; simpa [neg_mul] using ΦSimple0_expType partsMod5TwoQP hθ0 hθ1 (-1) (Or.inr rfl)
  hRank := fun P hD => rank3_macMahon_partsMod5 P hD

/-! #### 2E. Flagship Unconditional Joint Differential Independence Theorems over `ℂ(q)` -/

/-- **Flagship Theorem (3-Tuple Joint Differential Independence — Lambert Series)**:
The three Lambert logarithmic-derivative series
1. MacMahon `L₂(q) = ∑ σ₂(n) q^n` (`sigmaSeries 2`),
2. Parts `≡ 1 mod 5` `∑_{n ≡ 1 (5)} n q^n / (1 - q^n)`,
3. Parts `≡ 2 mod 5` `∑_{n ≡ 2 (5)} n q^n / (1 - q^n)`,
are **unconditionally jointly differentially independent over `ℂ(q)`**. -/
theorem macMahon_partsMod5One_partsMod5Two_lambert_joint_algIndep :
    AlgebraicIndependent ℂ (jointCoords
      ![sigmaSeries 2,
        lambertSeries (fun n => partsMod5OneQP.eval (n : ℤ)),
        lambertSeries (fun n => partsMod5TwoQP.eval (n : ℤ))]) := by
  let H3 : Fin 3 → PowerSeries ℂ :=
    ![lambertSeries (fun n => macMahonQP.eval (n : ℤ)),
      lambertSeries (fun n => partsMod5OneQP.eval (n : ℤ)),
      lambertSeries (fun n => partsMod5TwoQP.eval (n : ℤ))]
  have hH3_eq : ![sigmaSeries 2,
        lambertSeries (fun n => partsMod5OneQP.eval (n : ℤ)),
        lambertSeries (fun n => partsMod5TwoQP.eval (n : ℤ))] = H3 := by
    funext i; fin_cases i
    · exact lambertSeries_macMahonQP_eq.symm
    · rfl
    · rfl
  rw [hH3_eq]
  by_contra hdep
  let N3 : Fin 3 → ℕ := ![3, 2, 2]
  let a3 : Fin 3 → Polynomial ℂ := ![polyPart macMahonQP, polyPart partsMod5OneQP, polyPart partsMod5TwoQP]
  let f3 : Fin 3 → ℝ → ℂ :=
    ![fun u => (u : ℂ)⁻¹ ^ 3 * remFun macMahonQP u,
      fun u => (u : ℂ)⁻¹ ^ 2 * remFun partsMod5OneQP u,
      fun u => (u : ℂ)⁻¹ ^ 2 * remFun partsMod5TwoQP u]
  have hH_bd : ∀ i : Fin 3, PolyCoeffBound (H3 i) := fun i => by
    fin_cases i
    · exact quasipoly_lambertSeries_polyBound macMahonQP
    · exact quasipoly_lambertSeries_polyBound partsMod5OneQP
    · exact quasipoly_lambertSeries_polyBound partsMod5TwoQP
  have hf_rel : ∀ (i : Fin 3) {u : ℝ}, 0 < u →
      value (H3 i) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) =
        (u : ℂ) ^ (N3 i) * f3 i u + Polynomial.eval (u : ℂ) (a3 i) := by
    intro i u hu
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    fin_cases i
    · change value (lambertSeries (fun n => macMahonQP.eval (n : ℤ))) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) =
        (u : ℂ) ^ 3 * ((u : ℂ)⁻¹ ^ 3 * remFun macMahonQP u) + Polynomial.eval (u : ℂ) (polyPart macMahonQP)
      rw [value_lambertSeries_eq_remFun_add_polyPart macMahonQP hu, ← mul_assoc, inv_pow,
        mul_inv_cancel₀ (pow_ne_zero 3 hu_ne), one_mul]
    · change value (lambertSeries (fun n => partsMod5OneQP.eval (n : ℤ))) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) =
        (u : ℂ) ^ 2 * ((u : ℂ)⁻¹ ^ 2 * remFun partsMod5OneQP u) + Polynomial.eval (u : ℂ) (polyPart partsMod5OneQP)
      rw [value_lambertSeries_eq_remFun_add_polyPart partsMod5OneQP hu, ← mul_assoc, inv_pow,
        mul_inv_cancel₀ (pow_ne_zero 2 hu_ne), one_mul]
    · change value (lambertSeries (fun n => partsMod5TwoQP.eval (n : ℤ))) (Complex.exp (-((u⁻¹ : ℝ) : ℂ))) =
        (u : ℂ) ^ 2 * ((u : ℂ)⁻¹ ^ 2 * remFun partsMod5TwoQP u) + Polynomial.eval (u : ℂ) (polyPart partsMod5TwoQP)
      rw [value_lambertSeries_eq_remFun_add_polyPart partsMod5TwoQP hu, ← mul_assoc, inv_pow,
        mul_inv_cancel₀ (pow_ne_zero 2 hu_ne), one_mul]
  have hf_asymp : ∀ (i : Fin 3) (j : ℕ),
      HasAsympExp (iteratedDeriv j (f3 i)) (d_u^[j] (formalSeries (φ3 i))) := by
    intro i j
    fin_cases i
    · change HasAsympExp (iteratedDeriv j (fun u : ℝ => (u : ℂ)⁻¹ ^ 3 * remFun macMahonQP u))
        (d_u^[j] (formalSeries (ΦSimple1 macMahonQP rfl)))
      rw [formalSeries_ΦSimple1 macMahonQP rfl (fun _ => by simp [macMahonQP])]
      exact hasAsympExp_inv_pow_mul_iteratedDeriv j 3 (remFun_contDiffOn macMahonQP) (remFun_hasAsympExp macMahonQP)
    · change HasAsympExp (iteratedDeriv j (fun u : ℝ => (u : ℂ)⁻¹ ^ 2 * remFun partsMod5OneQP u))
        (d_u^[j] (formalSeries (ΦSimple0 partsMod5OneQP)))
      rw [formalSeries_ΦSimple0 partsMod5OneQP rfl]
      exact hasAsympExp_inv_pow_mul_iteratedDeriv j 2 (remFun_contDiffOn partsMod5OneQP) (remFun_hasAsympExp partsMod5OneQP)
    · change HasAsympExp (iteratedDeriv j (fun u : ℝ => (u : ℂ)⁻¹ ^ 2 * remFun partsMod5TwoQP u))
        (d_u^[j] (formalSeries (ΦSimple0 partsMod5TwoQP)))
      rw [formalSeries_ΦSimple0 partsMod5TwoQP rfl]
      exact hasAsympExp_inv_pow_mul_iteratedDeriv j 2 (remFun_contDiffOn partsMod5TwoQP) (remFun_hasAsympExp partsMod5TwoQP)
  obtain ⟨r, Q, hQ_ne, hQ_zero⟩ := joint_poly_ode_of_dep hH_bd hf_rel hdep
  exact hQ_ne (shared_lattice_joint_no_nonautonomous_ade_of_asymp macMahon_partsMod5_sharedFamily
    hf_asymp Q (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu; exact hQ_zero u hu))

/-- **Flagship Theorem (3-Tuple Joint Differential Independence — Infinite Euler Products)**:
The three literal infinite Euler products
1. MacMahon's plane-partition generating function `M(q) = ∏_{n ≥ 1} (1 - q^n)^{-n}`,
2. Parts `≡ 1 mod 5` generating function `∏_{n ≡ 1 (5)} (1 - q^n)^{-1}`,
3. Parts `≡ 2 mod 5` generating function `∏_{n ≡ 2 (5)} (1 - q^n)^{-1}`,
are **unconditionally jointly differentially independent over `ℂ(q)`**! -/
theorem macMahon_partsMod5One_partsMod5Two_euler_joint_algIndep :
    AlgebraicIndependent ℂ (jointCoords
      ![macmahonSeries,
        PakPrimes.HarmonicTrap.bose (fun n : ℕ => if n % 5 = 1 then 1 else 0),
        PakPrimes.HarmonicTrap.bose (fun n : ℕ => if n % 5 = 2 then 1 else 0)]) := by
  let G3 : Fin 3 → PowerSeries ℂ :=
    ![macmahonSeries,
      eulerProduct (fun n => partsMod5OneQP.eval (n : ℤ)),
      eulerProduct (fun n => partsMod5TwoQP.eval (n : ℤ))]
  let H3 : Fin 3 → PowerSeries ℂ :=
    ![sigmaSeries 2,
      lambertSeries (fun n => partsMod5OneQP.eval (n : ℤ)),
      lambertSeries (fun n => partsMod5TwoQP.eval (n : ℤ))]
  have hG3_eq : ![macmahonSeries,
        PakPrimes.HarmonicTrap.bose (fun n : ℕ => if n % 5 = 1 then 1 else 0),
        PakPrimes.HarmonicTrap.bose (fun n : ℕ => if n % 5 = 2 then 1 else 0)] = G3 := by
    funext i; fin_cases i
    · rfl
    · change PakPrimes.HarmonicTrap.bose (fun n : ℕ => if n % 5 = 1 then 1 else 0) =
        eulerProduct (fun n => partsMod5OneQP.eval (n : ℤ))
      rw [← eulerProduct_eq_bose]
      congr 1; funext n
      rw [partsMod5OneQP.eval_nat n]
      unfold partsMod5OneQP
      rw [Fin.sum_univ_one]
      split_ifs <;> simp_all
    · change PakPrimes.HarmonicTrap.bose (fun n : ℕ => if n % 5 = 2 then 1 else 0) =
        eulerProduct (fun n => partsMod5TwoQP.eval (n : ℤ))
      rw [← eulerProduct_eq_bose]
      congr 1; funext n
      rw [partsMod5TwoQP_eval_nat n]
      split_ifs <;> simp_all
  rw [hG3_eq]
  refine joint_algIndep_of_log_deriv (H := H3) ?_ ?_ macMahon_partsMod5One_partsMod5Two_lambert_joint_algIndep
  · intro i
    fin_cases i
    · intro h0
      change macmahonSeries = 0 at h0
      have := congrArg PowerSeries.constantCoeff h0
      rw [macmahonSeries_constantCoeff, map_zero] at this; norm_num at this
    · intro h0
      change eulerProduct (fun n => partsMod5OneQP.eval (n : ℤ)) = 0 at h0
      have := congrArg PowerSeries.constantCoeff h0
      rw [eulerProduct_constantCoeff, map_zero] at this; norm_num at this
    · intro h0
      change eulerProduct (fun n => partsMod5TwoQP.eval (n : ℤ)) = 0 at h0
      have := congrArg PowerSeries.constantCoeff h0
      rw [eulerProduct_constantCoeff, map_zero] at this; norm_num at this
  · intro i
    fin_cases i
    · exact macmahonSeries_ode
    · exact eulerProduct_ode _
    · exact eulerProduct_ode _

/-- **Corollary (Nesterenko-Style Pairwise Joint Differential Independence)**:
The generating functions of partitions into parts `≡ 1 mod 5` (`∏_{n ≡ 1 (5)} (1 - q^n)^{-1}`) and
parts `≡ 2 mod 5` (`∏_{n ≡ 2 (5)} (1 - q^n)^{-1}`) are **jointly differentially independent over `ℂ(q)`**. -/
theorem partsMod5One_partsMod5Two_joint_algIndep :
    AlgebraicIndependent ℂ (jointCoords
      ![PakPrimes.HarmonicTrap.bose (fun n : ℕ => if n % 5 = 1 then 1 else 0),
        PakPrimes.HarmonicTrap.bose (fun n : ℕ => if n % 5 = 2 then 1 else 0)]) := by
  let e : Fin 2 → Fin 3 := ![⟨1, by decide⟩, ⟨2, by decide⟩]
  have he : Function.Injective e := by decide
  have hcomp : ![PakPrimes.HarmonicTrap.bose (fun n : ℕ => if n % 5 = 1 then 1 else 0),
        PakPrimes.HarmonicTrap.bose (fun n : ℕ => if n % 5 = 2 then 1 else 0)] =
      ![macmahonSeries,
        PakPrimes.HarmonicTrap.bose (fun n : ℕ => if n % 5 = 1 then 1 else 0),
        PakPrimes.HarmonicTrap.bose (fun n : ℕ => if n % 5 = 2 then 1 else 0)] ∘ e := by
    funext i; fin_cases i <;> rfl
  rw [hcomp]
  exact jointCoords_algIndep_comp macMahon_partsMod5One_partsMod5Two_euler_joint_algIndep e he

/-- **Corollary (MacMahon & Parts `≡ 1 mod 5` Joint Differential Independence)**:
MacMahon's plane-partition generating function `M(q) = ∏ (1 - q^n)^{-n}` and the generating function
of partitions into parts `≡ 1 mod 5` (`∏_{n ≡ 1 (5)} (1 - q^n)^{-1}`) are **jointly differentially
independent over `ℂ(q)`**. -/
theorem macMahon_partsMod5One_joint_algIndep :
    AlgebraicIndependent ℂ (jointCoords
      ![macmahonSeries,
        PakPrimes.HarmonicTrap.bose (fun n : ℕ => if n % 5 = 1 then 1 else 0)]) := by
  let e : Fin 2 → Fin 3 := ![⟨0, by decide⟩, ⟨1, by decide⟩]
  have he : Function.Injective e := by decide
  have hcomp : ![macmahonSeries,
        PakPrimes.HarmonicTrap.bose (fun n : ℕ => if n % 5 = 1 then 1 else 0)] =
      ![macmahonSeries,
        PakPrimes.HarmonicTrap.bose (fun n : ℕ => if n % 5 = 1 then 1 else 0),
        PakPrimes.HarmonicTrap.bose (fun n : ℕ => if n % 5 = 2 then 1 else 0)] ∘ e := by
    funext i; fin_cases i <;> rfl
  rw [hcomp]
  exact jointCoords_algIndep_comp macMahon_partsMod5One_partsMod5Two_euler_joint_algIndep e he

/-! #### 2F. All-Dimension Conformal Scalar Parity Theorem on `S^s` (`∀ s ≥ 2`) -/

/-- Harmonic multiplicity polynomial of a free conformal scalar on the `s`-sphere `S^s` (`s ≥ 2`)
at half-integer/integer energy index `j = 2ℓ + s - 1`:
`w_s(j) = (2^(s-2) * (s-1)!)⁻¹ * j * ∏_{k=1}^{s-2} (j + 2k - (s - 1))`. -/
@[expose] noncomputable def conformalScalarPoly (s : ℕ) : Polynomial ℂ :=
  Polynomial.C (((2 : ℂ) ^ (s - 2) * (Nat.factorial (s - 1) : ℂ))⁻¹) *
    (Polynomial.X * ∏ k ∈ Finset.Icc 1 (s - 2),
      (Polynomial.X + Polynomial.C (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ))))

private lemma natDegree_conformalScalarPoly_le {s : ℕ} (hs : 2 ≤ s) :
    (conformalScalarPoly s).natDegree ≤ s - 1 := by
  unfold conformalScalarPoly
  let Pprod : Polynomial ℂ := ∏ k ∈ Finset.Icc 1 (s - 2),
    (Polynomial.X + Polynomial.C (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ)))
  have h1 : (Polynomial.C (((2 : ℂ) ^ (s - 2) * (Nat.factorial (s - 1) : ℂ))⁻¹) *
      (Polynomial.X * Pprod)).natDegree ≤ (Polynomial.X * Pprod).natDegree :=
    Polynomial.natDegree_C_mul_le _ _
  have h2 : (Polynomial.X * Pprod).natDegree ≤ (Polynomial.X : Polynomial ℂ).natDegree + Pprod.natDegree :=
    Polynomial.natDegree_mul_le
  have h3 : Pprod.natDegree ≤ s - 2 := by
    have hle : Pprod.natDegree ≤ ∑ k ∈ Finset.Icc 1 (s - 2),
        (Polynomial.X + Polynomial.C (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ))).natDegree :=
      Polynomial.natDegree_prod_le (Finset.Icc 1 (s - 2))
        (fun k => Polynomial.X + Polynomial.C (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ)))
    have hsum : ∑ k ∈ Finset.Icc 1 (s - 2),
        (Polynomial.X + Polynomial.C (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ))).natDegree = s - 2 := by
      have heq : ∀ k ∈ Finset.Icc 1 (s - 2),
          (Polynomial.X + Polynomial.C (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ))).natDegree = 1 :=
        fun k _ => Polynomial.natDegree_X_add_C _
      rw [Finset.sum_congr rfl heq]
      simp
    omega
  have hX : (Polynomial.X : Polynomial ℂ).natDegree = 1 := Polynomial.natDegree_X
  exact h1.trans (h2.trans (by omega))

private lemma conformalScalarPoly_eval_neg {s : ℕ} (hs : 2 ≤ s) (z : ℂ) :
    (conformalScalarPoly s).eval (-z) = (-1 : ℂ) ^ (s - 1) * (conformalScalarPoly s).eval z := by
  unfold conformalScalarPoly
  have heval_prod : ∀ w : ℂ,
      (∏ k ∈ Finset.Icc 1 (s - 2),
        (Polynomial.X + Polynomial.C (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ)))).eval w =
      ∏ k ∈ Finset.Icc 1 (s - 2), (w + (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ))) := fun w => by
    change Polynomial.evalRingHom w (∏ k ∈ Finset.Icc 1 (s - 2), _) = _
    rw [map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, heval_prod]
  have hprod_neg : (∏ k ∈ Finset.Icc 1 (s - 2), (-z + (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ)))) =
      (-1 : ℂ) ^ (s - 2) * ∏ k ∈ Finset.Icc 1 (s - 2), (z + (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ))) := by
    have hbij : (∏ k ∈ Finset.Icc 1 (s - 2), (-z + (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ)))) =
        ∏ k ∈ Finset.Icc 1 (s - 2), (-(z + (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ)))) := by
      refine Finset.prod_bij (fun k _ => s - 1 - k) ?_ ?_ ?_ ?_
      · intro k hk
        have ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro a ha b hb hab
        have ⟨_, ha2⟩ := Finset.mem_Icc.mp ha
        have ⟨_, hb2⟩ := Finset.mem_Icc.mp hb
        omega
      · intro b hb
        have ⟨hb1, hb2⟩ := Finset.mem_Icc.mp hb
        exact ⟨s - 1 - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro k hk
        have ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
        have hcast : ((s - 1 - k : ℕ) : ℤ) = (s : ℤ) - 1 - (k : ℤ) := by omega
        have hint : 2 * ((s - 1 - k : ℕ) : ℤ) - ((s : ℤ) - 1) = -(2 * (k : ℤ) - ((s : ℤ) - 1)) := by
          rw [hcast]; ring
        rw [hint, Int.cast_neg]
        ring
    rw [hbij, Finset.prod_neg, show (Finset.Icc 1 (s - 2)).card = s - 2 by simp]
  rw [hprod_neg, show s - 1 = (s - 2) + 1 by omega, pow_succ]
  ring

private lemma conformalScalarPoly_eval_ground {s : ℕ} (hs : 2 ≤ s) :
    (conformalScalarPoly s).eval (((s - 1 : ℕ) : ℂ)) = 1 := by
  unfold conformalScalarPoly
  have heval_prod :
      (∏ k ∈ Finset.Icc 1 (s - 2),
        (Polynomial.X + Polynomial.C (((2 * (k : ℤ) - ((s : ℤ) - 1) : ℤ) : ℂ)))).eval (((s - 1 : ℕ) : ℂ)) =
      ∏ k ∈ Finset.Icc 1 (s - 2), (2 * (k : ℂ)) := by
    change Polynomial.evalRingHom (((s - 1 : ℕ) : ℂ)) (∏ k ∈ Finset.Icc 1 (s - 2), _) = _
    rw [map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_one]
    have hsub : ((s - 1 : ℕ) : ℂ) = (s : ℂ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hsub]; ring
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, heval_prod]
  have hprod_fact : ∀ n : ℕ, ∏ k ∈ Finset.Icc 1 n, (k : ℂ) = (Nat.factorial n : ℂ) := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
      rw [Finset.prod_insert (by simp), ih, Nat.factorial_succ, Nat.cast_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, show (Finset.Icc 1 (s - 2)).card = s - 2 by simp,
    hprod_fact (s - 2)]
  have hfact_eq : (((s - 1 : ℕ) : ℂ) * ((2 : ℂ) ^ (s - 2) * (Nat.factorial (s - 2) : ℂ))) =
      (2 : ℂ) ^ (s - 2) * (Nat.factorial (s - 1) : ℂ) := by
    have hsucc : s - 1 = (s - 2) + 1 := by omega
    conv_rhs => rw [hsucc, Nat.factorial_succ, Nat.cast_mul]
    rw [← hsucc]; ring
  rw [hfact_eq]
  have hne : (2 : ℂ) ^ (s - 2) * (Nat.factorial (s - 1) : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  exact inv_mul_cancel₀ hne

/-- Period-2 quasipolynomial encoding the conformal scalar harmonic degeneracies on `S^s` (`s ≥ 2`),
supported on `j ≡ s - 1 (mod 2)` with `w_s(2ℓ + s - 1) = d_s(ℓ)`. -/
@[expose] noncomputable def conformalScalarSphereQP (s : ℕ) : Quasipoly where
  M := 2
  hM := by norm_num
  «D» := s - 1
  c d n := if n % 2 = (s - 1) % 2 then (conformalScalarPoly s).coeff d.1 else 0
  periodic _ n := by simp

private lemma conformalScalarSphereQP_eval {s : ℕ} (hs : 2 ≤ s) (n : ℤ) :
    (conformalScalarSphereQP s).eval n =
      if (n % 2).toNat = (s - 1) % 2 then (conformalScalarPoly s).eval (n : ℂ) else 0 := by
  unfold Quasipoly.eval conformalScalarSphereQP
  simp only [Nat.cast_ofNat]
  have hmod2 : (n % 2).toNat % 2 = (n % 2).toNat := Nat.mod_eq_of_lt (by omega)
  simp_rw [hmod2]
  split_ifs with h
  · rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (natDegree_conformalScalarPoly_le hs) (Nat.lt_succ_self _)),
      Fin.sum_univ_eq_sum_range (fun d => (conformalScalarPoly s).coeff d * (n : ℂ) ^ d)]
  · exact Finset.sum_eq_zero fun d _ => by simp

private lemma conformalScalarSphereQP_oddPart_eq_zero_iff {s : ℕ} (hs : 2 ≤ s) :
    (∀ n : ℤ, (conformalScalarSphereQP s).oddPart n = 0) ↔ Odd s := by
  have heval_neg : ∀ n : ℤ,
      (conformalScalarSphereQP s).eval (-n) = (-1 : ℂ) ^ (s - 1) * (conformalScalarSphereQP s).eval n := by
    intro n
    rw [conformalScalarSphereQP_eval hs (-n), conformalScalarSphereQP_eval hs n]
    have hmod_neg : ((-n) % 2).toNat = (n % 2).toNat := by omega
    rw [hmod_neg]
    split_ifs
    · rw [Int.cast_neg, conformalScalarPoly_eval_neg hs]
    · simp
  constructor
  · intro hall
    by_contra hnot
    have heven : Even s := Nat.not_odd_iff_even.mp hnot
    have hodd_sub : Odd (s - 1) := by
      rcases heven with ⟨k, rfl⟩
      refine ⟨k - 1, ?_⟩; omega
    have h0 := hall ((s - 1 : ℕ) : ℤ)
    unfold Quasipoly.oddPart at h0
    rw [heval_neg, hodd_sub.neg_one_pow] at h0
    have hev : (conformalScalarSphereQP s).eval ((s - 1 : ℕ) : ℤ) = 1 := by
      rw [conformalScalarSphereQP_eval hs]
      have hmod_s : ((((s - 1 : ℕ) : ℤ) % 2).toNat) = (s - 1) % 2 := by omega
      rw [ite_eq_left_iff.mpr (fun h => (h hmod_s).elim), Int.cast_natCast]
      exact conformalScalarPoly_eval_ground hs
    rw [hev] at h0
    norm_num at h0
  · intro hodd n
    have heven_sub : Even (s - 1) := by
      rcases hodd with ⟨k, rfl⟩
      exact ⟨k, by omega⟩
    unfold Quasipoly.oddPart
    rw [heval_neg, heven_sub.neg_one_pow]
    ring

/-- **All-Dimension Conformal Scalar `S^s` Parity Theorem (Lambert Series, `∀ s ≥ 2`)**:
For EVERY spatial sphere dimension `s ≥ 2`, the thermal logarithmic-derivative Lambert series of a free
conformal scalar on `S^s` is D-algebraic over `ℂ(q)` **if and only if `s` is odd** (`S^3, S^5, S^7, …`
are D-algebraic; `S^2, S^4, S^6, …` are unconditionally D-transcendental over `ℂ(q)`). -/
theorem conformalScalar_sphere_allDim_lambert_iff {s : ℕ} (hs : 2 ≤ s) :
    ¬ AlgebraicIndependent ℂ
        (seriesCoordinates (lambertSeries (fun n => (conformalScalarSphereQP s).eval (n : ℤ)))) ↔
      Odd s :=
  (quasipoly_period2_lambert_iff (conformalScalarSphereQP s) rfl).trans
    (conformalScalarSphereQP_oddPart_eq_zero_iff hs)

/-- **All-Dimension Conformal Scalar `S^s` Parity Theorem (Thermal Partition Function, `∀ s ≥ 2`)**:
For EVERY spatial sphere dimension `s ≥ 2`, the thermal canonical partition function
`Z_{S^s}(q) = ∏_{ℓ ≥ 0} (1 - q^{2ℓ + s - 1})^{-d_s(ℓ)}` of a free conformal scalar on `S^s` is
D-algebraic over `ℂ(q)` **if and only if `s` is odd** (`S^3, S^5, S^7, …` are D-algebraic;
`S^2, S^4, S^6, …` are unconditionally D-transcendental over `ℂ(q)`). -/
theorem conformalScalar_sphere_allDim_eulerProduct_iff {s : ℕ} (hs : 2 ≤ s) :
    ¬ AlgebraicIndependent ℂ
        (seriesCoordinates (eulerProduct (fun n => (conformalScalarSphereQP s).eval (n : ℤ)))) ↔
      Odd s :=
  (quasipoly_period2_eulerProduct_iff (conformalScalarSphereQP s) rfl).trans
    (conformalScalarSphereQP_oddPart_eq_zero_iff hs)

end
end PakPrimes.QuasipolynomialIFF
