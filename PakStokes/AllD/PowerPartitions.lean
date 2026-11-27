module

public import PakStokes.AllD.SquaresPartitionAnalytic
public import PakStokes.AllD.AllDFormalTransfer
public import PakStokes.AllD.TrackedWaves
public import PakStokes.MarkedJacobian
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.MvPolynomial.Equiv
import all PakStokes.AllD.SquaresPartitionAnalytic
import all PakStokes.AllD.AllDFormalTransfer
import all PakStokes.AllD.ExtremeRayProjection
import all PakStokes.AllD.BesicovitchCore
import all PakStokes.AllD.TrackedWaves
import all PakStokes.PolynomialFlow
import all PakStokes.OrdinaryPoint
import all PakStokes.MarkedJacobian
import all PakStokes.WaveProducts
import all PakStokes.PhysicalPhases
import all PakStokes.PhysicalExpression
import all PakStokes.RayAlgebra

/-! # Wave 9: Zero-Tilt Constant-Vandermonde Differential Transcendence of All Power-Partition Products `P_d(q) = ∏_{n ≥ 1} (1 - q^{n^d})^{-1}` (`d ≥ 2`)

Establishes on top of `PakStokesAllD`:

1. **100% Unconditional Formal Power-Series Algebra (`d ≥ 1`):**
   - `powerPartSeries d`, dilations `powerPartDilated d a`, integer powers
     `powerPartZPow d k` (`k ∈ ℤ`), and logarithmic derivatives `logDerivPowerPart d`,
     `logDerivPowerPartDilated d a`, with exact formal log-derivative identities.
   - `kolchin_logDeriv_joint_indep` & `diffTrans_of_logDeriv`: completely formal,
     UFD-free Kolchin log-derivative transfer showing joint differential independence
     of `{F_i}` over `ℂ(q)` implies joint differential independence of `{P_i}`
     (whenever `q P_i' = c_i F_i P_i`, `c_i ≠ 0`, `P_i ≠ 0`).
2. **100% Unconditional Prime Multiplicity & Constant Prime Vandermonde (`d ≥ 2`):**
   - `powerPartMult_prime`: `c_d(p) = 1` for every prime `p` and every `d ≥ 2`.
   - Exact active-ray cone `{A_{d,ℓ} : 0 ≤ ℓ < d}`, extreme-ray functional `ppRotIm`,
     and zero-tilt Besicovitch injectivity on `Core d →₀ ℕ` (`d ≥ 2`).
   - `ppPrimeVandermonde_det_ne_zero`: exact `X`-independent constant `J × J` prime
     Vandermonde determinant non-vanishing for ALL `d ≥ 2` and ANY `J` distinct primes.
3. **Zero-Tilt Constant-Vandermonde Master Theorems (`d ≥ 2`, given `PowerPartStokesProfile d hd`):**
   - `logDerivPowerPart_non_ade`, `powerPart_non_ade`, `powerPart_zpow_non_ade` (`k ∈ ℤ \ {0}`):
     proved directly on the untilted positive real ray `X > 0` with pure constant
     amplitudes (ZERO `RayDensity`, ZERO `FiniteParities`, ZERO `RayGerm`).
   - `logDerivPowerPart_dilations_diff_indep`, `powerPart_dilations_diff_indep`:
     joint differential independence of ANY finite family of distinct dilations
     `{P_d(q^{a_1}), …, P_d(q^{a_s})}` over `ℂ(q)`.
4. **100% UNCONDITIONAL `d = 2` (Partitions into Squares `P_2(q) = ∏_{n ≥ 1} (1 - q^{n²})^{-1}`):**
   - Discharges `powerPartStokesProfileTwo : PowerPartStokesProfile 2 (by decide)`
     completely from Mathlib via `squares_partition_analytic_identity`, yielding
     **ZERO-HYPOTHESIS** kernel-verified proofs of:
     - `powerPart_2_non_ade` (`P_2(q)` is non-ADE over `ℂ(q)`),
     - `logDerivPowerPart_2_non_ade`,
     - `powerPart_2_zpow_non_ade` (`P_2(q)^k` for every `k ∈ ℤ \ {0}`),
     - `logDerivPowerPart_2_dilations_diff_indep` and `powerPart_2_dilations_diff_indep`! -/
public section
namespace CubicTheta.AllD
open Complex Filter Set PowerSeries MvPolynomial Matrix Flow
open scoped Topology Matrix
noncomputable section

/-! ### 1. Formal Power-Partition Products `P_d(q)`, Integer Powers, and Logarithmic Derivatives -/

/-- Sum of `d`-th power divisors `∑_{n^d ∣ N} n^d` for `N ≥ 1`. -/
def powerDivSum (d N : ℕ) : ℕ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n ↦ n ^ d ∣ N), n ^ d

/-- Formal logarithmic derivative `F_d(q^a) = ∑_{m, n ≥ 1} n^d q^{a m n^d} ∈ ℂ[[q]]`. -/
def logDerivPowerPartDilated (d a : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun N ↦ if N = 0 then 0 else if a ∣ N then (powerDivSum d (N / a) : ℂ) else 0

/-- Formal logarithmic derivative `F_d(q) = q (d/dq) log P_d(q) = ∑_{m, n ≥ 1} n^d q^{m n^d}`. -/
def logDerivPowerPart (d : ℕ) : PowerSeries ℂ := logDerivPowerPartDilated d 1

/-- Formal geometric series `(1 - q^m)^{-1} = ∑_{k ≥ 0} q^{k m}` in `ℂ[[q]]`. -/
def geomSeriesPow (m : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun k ↦ if m ∣ k then 1 else 0

/-- Finite truncated Euler product `∏_{n=1}^M (1 - q^{a n^d})^{-1}` in `ℂ[[q]]`. -/
def powerPartTrunc (d a M : ℕ) : PowerSeries ℂ :=
  ∏ n ∈ Finset.Icc 1 M, geomSeriesPow (a * n ^ d)

/-- Formal dilated `d`-th power partition product `P_d(q^a) = ∏_{n ≥ 1} (1 - q^{a n^d})^{-1}`. -/
def powerPartDilated (d a : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun N ↦ PowerSeries.coeff N (powerPartTrunc d a N)

/-- Formal `d`-th power partition product `P_d(q) = ∏_{n ≥ 1} (1 - q^{n^d})^{-1}`. -/
def powerPartSeries (d : ℕ) : PowerSeries ℂ := powerPartDilated d 1

private theorem geomSeriesPow_mul_one_sub {m : ℕ} (hm : 1 ≤ m) :
    (1 - PowerSeries.X ^ m) * geomSeriesPow m = 1 := by
  ext N
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_one]
  by_cases hN : N < m
  · have hmul : PowerSeries.coeff N (PowerSeries.X ^ m * geomSeriesPow m) = 0 := by
      rw [PowerSeries.coeff_X_pow_mul']
      simp [not_le.mpr hN]
    rw [hmul, sub_zero, geomSeriesPow, PowerSeries.coeff_mk]
    by_cases h0 : N = 0
    · subst h0; simp
    · have hnd : ¬ m ∣ N := fun h ↦ by
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h; omega
      simp [h0, hnd]
  · push Not at hN
    have hN0 : N ≠ 0 := by omega
    rw [PowerSeries.coeff_X_pow_mul']
    simp only [hN, hN0, ↓reduceIte, geomSeriesPow, PowerSeries.coeff_mk]
    have hiff : m ∣ N ↔ m ∣ (N - m) := by
      constructor
      · intro h; exact (Nat.dvd_sub_iff_left hN (dvd_refl m)).mpr h
      · intro h
        have hadd : N = (N - m) + m := (Nat.sub_add_cancel hN).symm
        rw [hadd]; exact dvd_add h (dvd_refl m)
    by_cases hdvd : m ∣ N
    · simp [hdvd, hiff.mp hdvd]
    · simp [hdvd, mt hiff.mpr hdvd]

private theorem constantCoeff_geomSeriesPow (m : ℕ) :
    PowerSeries.constantCoeff (geomSeriesPow m) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, geomSeriesPow, PowerSeries.coeff_mk]
  simp

theorem constantCoeff_powerPartDilated (d a : ℕ) :
    PowerSeries.constantCoeff (powerPartDilated d a) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, powerPartDilated, PowerSeries.coeff_mk,
      powerPartTrunc]
  simp

theorem isUnit_powerPartDilated (d a : ℕ) : IsUnit (powerPartDilated d a) :=
  PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [constantCoeff_powerPartDilated]; exact isUnit_one)

theorem powerPartDilated_ne_zero (d a : ℕ) : powerPartDilated d a ≠ 0 :=
  (isUnit_powerPartDilated d a).ne_zero

theorem powerPartSeries_ne_zero (d : ℕ) : powerPartSeries d ≠ 0 :=
  powerPartDilated_ne_zero d 1

/-- Exact integer power `P_d(q)^k ∈ ℂ[[q]]` for EVERY `k : ℤ` (positive, zero, or negative),
defined via the unit `powerPartSeries d`! -/
def powerPartZPow (d : ℕ) (k : ℤ) : PowerSeries ℂ :=
  (((isUnit_powerPartDilated d 1).unit ^ k : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)

theorem powerPartZPow_ne_zero (d : ℕ) (k : ℤ) : powerPartZPow d k ≠ 0 :=
  Units.ne_zero _

theorem powerPartZPow_natCast (d k : ℕ) :
    powerPartZPow d (k : ℤ) = (powerPartSeries d) ^ k := by
  simp [powerPartZPow, powerPartSeries]

private theorem coeff_geomSeriesPow_mul_eq {m N : ℕ} (hm : N < m) (S : PowerSeries ℂ) :
    PowerSeries.coeff N (S * geomSeriesPow m) = PowerSeries.coeff N S := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.sum_eq_single (N, 0)]
  · rw [geomSeriesPow, PowerSeries.coeff_mk]; simp
  · rintro ⟨i, j⟩ hij hne
    have hsum : i + j = N := Finset.mem_antidiagonal.mp hij
    have hj0 : j ≠ 0 := by
      intro h; apply hne; exact Prod.ext (by omega) h
    have hnd : ¬ m ∣ j := fun h ↦ by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) h; omega
    simp [geomSeriesPow, hnd]
  · intro h; exact (h (Finset.mem_antidiagonal.mpr (add_zero N))).elim

private theorem coeff_powerPartTrunc_stable {d a M N : ℕ} (hd : 1 ≤ d) (ha : 1 ≤ a) (hMN : N ≤ M) :
    PowerSeries.coeff N (powerPartTrunc d a M) = PowerSeries.coeff N (powerPartTrunc d a N) := by
  induction M, hMN using Nat.le_induction with
  | base => rfl
  | succ k hNk ih =>
    unfold powerPartTrunc
    rw [show Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
    rw [Finset.prod_insert (by simp), mul_comm]
    have hlt : N < a * (k + 1) ^ d := by
      have h1 : k + 1 ≤ (k + 1) ^ d := Nat.le_self_pow (by omega) (k + 1)
      have h2 : (k + 1) ^ d ≤ a * (k + 1) ^ d := Nat.le_mul_of_pos_left _ ha
      omega
    rw [coeff_geomSeriesPow_mul_eq hlt]
    exact ih

private theorem X_mul_deriv_geomSeriesPow {m : ℕ} (hm : 1 ≤ m) :
    PowerSeries.X * PowerSeries.derivative (R := ℂ) (geomSeriesPow m) =
      (PowerSeries.C (m : ℂ) * PowerSeries.X ^ m * geomSeriesPow m) * geomSeriesPow m := by
  have h1 := congrArg (PowerSeries.derivative (R := ℂ)) (geomSeriesPow_mul_one_sub hm)
  rw [PowerSeries.derivative_one, Derivation.leibniz, map_sub, PowerSeries.derivative_one,
      zero_sub, PowerSeries.derivative_pow, PowerSeries.derivative_X, mul_one, smul_eq_mul,
      smul_eq_mul] at h1
  have h2 : (1 - PowerSeries.X ^ m) * (PowerSeries.X * PowerSeries.derivative (R := ℂ) (geomSeriesPow m)) =
      (PowerSeries.C (m : ℂ) * PowerSeries.X ^ m) * geomSeriesPow m := by
    have hmul := congrArg (PowerSeries.X * ·) h1
    rw [mul_zero, mul_add] at hmul
    have hXpow : PowerSeries.X * (geomSeriesPow m * -((m : PowerSeries ℂ) * PowerSeries.X ^ (m - 1))) =
        -(PowerSeries.C (m : ℂ) * PowerSeries.X ^ m * geomSeriesPow m) := by
      have hpow : PowerSeries.X * PowerSeries.X ^ (m - 1) = (PowerSeries.X : PowerSeries ℂ) ^ m := by
        rw [← pow_succ', Nat.sub_add_cancel hm]
      have hC : (m : PowerSeries ℂ) = PowerSeries.C (m : ℂ) := by simp
      rw [hC]; linear_combination -PowerSeries.C (m : ℂ) * geomSeriesPow m * hpow
    rw [hXpow] at hmul
    linear_combination hmul
  have h3 := congrArg (geomSeriesPow m * ·) h2
  rw [← mul_assoc, mul_comm (geomSeriesPow m) (1 - PowerSeries.X ^ m),
      geomSeriesPow_mul_one_sub hm, one_mul] at h3
  rw [h3]; ring

private theorem X_mul_deriv_finset_prod {ι : Type*} (S : Finset ι)
    (f g : ι → PowerSeries ℂ)
    (h : ∀ i ∈ S, PowerSeries.X * PowerSeries.derivative (R := ℂ) (f i) = g i * f i) :
    PowerSeries.X * PowerSeries.derivative (R := ℂ) (∏ i ∈ S, f i) =
      (∑ i ∈ S, g i) * (∏ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have ha' := h a (Finset.mem_insert_self a S)
    have hS' := ih (fun i hi ↦ h i (Finset.mem_insert_of_mem hi))
    linear_combination f a * hS' + (∏ i ∈ S, f i) * ha'

/-- **100% Unconditional Exact Formal Logarithmic Derivative of `P_d(q^a)`** (`d ≥ 1, a ≥ 1`):
`q · (d/dq) P_d(q^a) = a · F_d(q^a) · P_d(q^a)`. -/
theorem X_mul_deriv_powerPartDilated {d a : ℕ} (hd : 1 ≤ d) (ha : 1 ≤ a) :
    PowerSeries.X * PowerSeries.derivative (R := ℂ) (powerPartDilated d a) =
      (PowerSeries.C (a : ℂ) * logDerivPowerPartDilated d a) * powerPartDilated d a := by
  ext N
  let M := N + 1
  have htrunc := X_mul_deriv_finset_prod (Finset.Icc 1 M)
    (fun n ↦ geomSeriesPow (a * n ^ d))
    (fun n ↦ PowerSeries.C ((a * n ^ d : ℕ) : ℂ) * PowerSeries.X ^ (a * n ^ d) *
      geomSeriesPow (a * n ^ d))
    (fun n hn ↦ by
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hm : 1 ≤ a * n ^ d := Nat.mul_pos ha (pow_pos (by omega) d)
      exact X_mul_deriv_geomSeriesPow hm)
  have hcoeff_eq := congrArg (PowerSeries.coeff N) htrunc
  have hlhs : PowerSeries.coeff N (PowerSeries.X * PowerSeries.derivative (R := ℂ) (powerPartDilated d a)) =
      PowerSeries.coeff N (PowerSeries.X * PowerSeries.derivative (R := ℂ) (powerPartTrunc d a M)) := by
    cases N with
    | zero => simp
    | succ N' =>
      rw [← pow_one (PowerSeries.X : PowerSeries ℂ), PowerSeries.coeff_X_pow_mul',
          PowerSeries.coeff_X_pow_mul']
      simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel,
        PowerSeries.coeff_derivative]
      congr 1
      rw [powerPartDilated, PowerSeries.coeff_mk]
      exact (coeff_powerPartTrunc_stable hd ha (by omega : N' + 1 ≤ M)).symm
  have hsum_coeff (k : ℕ) (hk : k ≤ N) :
      PowerSeries.coeff k (∑ n ∈ Finset.Icc 1 M,
        PowerSeries.C ((a * n ^ d : ℕ) : ℂ) * PowerSeries.X ^ (a * n ^ d) *
          geomSeriesPow (a * n ^ d)) =
      PowerSeries.coeff k (PowerSeries.C (a : ℂ) * logDerivPowerPartDilated d a) := by
    rw [map_sum, PowerSeries.coeff_C_mul, logDerivPowerPartDilated, PowerSeries.coeff_mk]
    have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 M) :
        PowerSeries.coeff k (PowerSeries.C ((a * n ^ d : ℕ) : ℂ) * PowerSeries.X ^ (a * n ^ d) *
          geomSeriesPow (a * n ^ d)) =
        if k = 0 then 0 else if a * n ^ d ∣ k then ((a * n ^ d : ℕ) : ℂ) else 0 := by
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hm : 1 ≤ a * n ^ d := Nat.mul_pos ha (pow_pos (by omega) d)
      rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
      by_cases hk0 : k = 0
      · subst hk0; simp [show ¬ a * n ^ d ≤ 0 by omega]
      · simp only [hk0, ↓reduceIte]
        by_cases hle : a * n ^ d ≤ k
        · simp only [hle, ↓reduceIte, geomSeriesPow, PowerSeries.coeff_mk]
          have hiff : a * n ^ d ∣ k - a * n ^ d ↔ a * n ^ d ∣ k := by
            constructor
            · intro h; rw [← Nat.sub_add_cancel hle]; exact dvd_add h (dvd_refl _)
            · intro h; exact (Nat.dvd_sub_iff_left hle (dvd_refl _)).mpr h
          by_cases hdvd : a * n ^ d ∣ k
          · simp [hdvd, hiff.mpr hdvd]
          · simp [hdvd, mt hiff.mp hdvd]
        · have hnd : ¬ a * n ^ d ∣ k := fun h ↦ hle (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h)
          simp [hle, hnd]
    rw [Finset.sum_congr rfl hterm]
    by_cases hk0 : k = 0
    · subst hk0; simp
    · simp only [hk0, ↓reduceIte]
      by_cases hak : a ∣ k
      · simp only [hak, ↓reduceIte, powerDivSum, Nat.cast_sum, Finset.mul_sum]
        rw [← Finset.sum_filter]
        have hfilt : (Finset.Icc 1 M).filter (fun n ↦ a * n ^ d ∣ k) =
            (Finset.Icc 1 (k / a)).filter (fun n ↦ n ^ d ∣ k / a) := by
          ext n
          simp only [Finset.mem_filter, Finset.mem_Icc]
          constructor
          · rintro ⟨⟨hn1, _⟩, hdvd⟩
            have hdvd' : n ^ d ∣ k / a := by
              obtain ⟨q, hq⟩ := hdvd
              refine ⟨q, ?_⟩
              have hmul : a * (k / a) = k := Nat.mul_div_cancel' hak
              exact Nat.eq_of_mul_eq_mul_left ha (by rw [hmul, hq]; ring)
            have hka_pos : 0 < k / a := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hak) ha
            have hnle : n ≤ k / a :=
              (Nat.le_self_pow (by omega) n).trans (Nat.le_of_dvd hka_pos hdvd')
            exact ⟨⟨hn1, hnle⟩, hdvd'⟩
          · rintro ⟨⟨hn1, hnle⟩, hdvd'⟩
            have hleM : n ≤ M := hnle.trans ((Nat.div_le_self k a).trans (by omega))
            have hdvd : a * n ^ d ∣ k := by
              obtain ⟨q, hq⟩ := hdvd'
              refine ⟨q, ?_⟩
              have hmul : a * (k / a) = k := Nat.mul_div_cancel' hak
              rw [← hmul, hq]; ring
            exact ⟨⟨hn1, hleM⟩, hdvd⟩
        rw [hfilt]
        apply Finset.sum_congr rfl; intro n _
        push_cast; ring
      · simp only [hak, ↓reduceIte, mul_zero]
        apply Finset.sum_eq_zero; intro n _
        have hnd : ¬ a * n ^ d ∣ k := fun h ↦ hak ((dvd_mul_right a (n ^ d)).trans h)
        simp [hnd]
  have hrhs : PowerSeries.coeff N ((∑ n ∈ Finset.Icc 1 M,
        PowerSeries.C ((a * n ^ d : ℕ) : ℂ) * PowerSeries.X ^ (a * n ^ d) *
          geomSeriesPow (a * n ^ d)) * powerPartTrunc d a M) =
      PowerSeries.coeff N ((PowerSeries.C (a : ℂ) * logDerivPowerPartDilated d a) *
        powerPartDilated d a) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    rintro ⟨i, j⟩ hij
    have hsum : i + j = N := Finset.mem_antidiagonal.mp hij
    rw [hsum_coeff i (by omega), powerPartDilated, PowerSeries.coeff_mk,
        coeff_powerPartTrunc_stable hd ha (by omega : j ≤ M)]
  rw [hlhs]
  change PowerSeries.coeff N (PowerSeries.X * PowerSeries.derivative (R := ℂ)
      (∏ n ∈ Finset.Icc 1 M, geomSeriesPow (a * n ^ d))) = _
  rw [hcoeff_eq]
  exact hrhs

theorem X_mul_deriv_powerPartSeries {d : ℕ} (hd : 1 ≤ d) :
    PowerSeries.X * PowerSeries.derivative (R := ℂ) (powerPartSeries d) =
      logDerivPowerPart d * powerPartSeries d := by
  simpa [powerPartSeries, logDerivPowerPart] using X_mul_deriv_powerPartDilated hd le_rfl

/-- **100% Unconditional Exact Logarithmic Derivative of ALL Integer Powers `P_d(q)^k`** (`k ∈ ℤ`). -/
theorem X_mul_deriv_powerPartZPow {d : ℕ} (hd : 1 ≤ d) (k : ℤ) :
    PowerSeries.X * PowerSeries.derivative (R := ℂ) (powerPartZPow d k) =
      (PowerSeries.C (k : ℂ) * logDerivPowerPart d) * powerPartZPow d k := by
  have hnat (m : ℕ) :
      PowerSeries.X * PowerSeries.derivative (R := ℂ) ((powerPartSeries d) ^ m) =
        (PowerSeries.C (m : ℂ) * logDerivPowerPart d) * (powerPartSeries d) ^ m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
          Nat.cast_add, Nat.cast_one, map_add, map_one]
      linear_combination (powerPartSeries d) ^ m * X_mul_deriv_powerPartSeries hd +
        (powerPartSeries d) * ih
  cases k with
  | ofNat m =>
    simpa [powerPartZPow_natCast] using hnat m
  | negSucc m =>
    let u := (isUnit_powerPartDilated d 1).unit
    have hinv_eq : powerPartZPow d (Int.negSucc m) * (powerPartSeries d) ^ (m + 1) = 1 := by
      change ((u ^ (Int.negSucc m) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
        ((u ^ (m + 1) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = 1
      rw [← Units.val_mul, ← zpow_natCast, ← _root_.zpow_add]
      have h0 : Int.negSucc m + ((m + 1 : ℕ) : ℤ) = 0 := by omega
      rw [h0, zpow_zero, Units.val_one]
    have hd_prod := congrArg (PowerSeries.X * PowerSeries.derivative (R := ℂ) ·) hinv_eq
    rw [PowerSeries.derivative_one, mul_zero, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hd_prod
    have hd_prod' : (PowerSeries.X * PowerSeries.derivative (R := ℂ) (powerPartZPow d (Int.negSucc m))) *
        (powerPartSeries d) ^ (m + 1) +
        powerPartZPow d (Int.negSucc m) *
          ((PowerSeries.C ((m + 1 : ℕ) : ℂ) * logDerivPowerPart d) * (powerPartSeries d) ^ (m + 1)) = 0 := by
      linear_combination hd_prod - powerPartZPow d (Int.negSucc m) * hnat (m + 1)
    have hmul := congrArg (· * powerPartZPow d (Int.negSucc m)) hd_prod'
    rw [zero_mul, add_mul] at hmul
    have hcancel1 : (PowerSeries.X * PowerSeries.derivative (R := ℂ) (powerPartZPow d (Int.negSucc m))) *
        (powerPartSeries d) ^ (m + 1) * powerPartZPow d (Int.negSucc m) =
        PowerSeries.X * PowerSeries.derivative (R := ℂ) (powerPartZPow d (Int.negSucc m)) := by
      rw [mul_assoc, mul_comm ((powerPartSeries d) ^ (m + 1)), hinv_eq, mul_one]
    have hcancel2 : powerPartZPow d (Int.negSucc m) *
        ((PowerSeries.C ((m + 1 : ℕ) : ℂ) * logDerivPowerPart d) * (powerPartSeries d) ^ (m + 1)) *
        powerPartZPow d (Int.negSucc m) =
        (PowerSeries.C ((m + 1 : ℕ) : ℂ) * logDerivPowerPart d) * powerPartZPow d (Int.negSucc m) := by
      calc _ = (PowerSeries.C ((m + 1 : ℕ) : ℂ) * logDerivPowerPart d) *
              (powerPartZPow d (Int.negSucc m) * (powerPartSeries d) ^ (m + 1)) *
              powerPartZPow d (Int.negSucc m) := by ring
        _ = _ := by rw [hinv_eq, mul_one]
    rw [hcancel1, hcancel2] at hmul
    have hcast : ((Int.negSucc m : ℤ) : ℂ) = -((m + 1 : ℕ) : ℂ) := by
      simp [Int.cast_negSucc]
    rw [hcast, map_neg]
    linear_combination hmul

/-- Joint formal coordinates `(q, {S_i^{(j)}})` in `ℂ[[q]]`. -/
def jointSeriesCoordinates {s : ℕ} (S : Fin s → PowerSeries ℂ) :
    Option (Fin s × ℕ) → PowerSeries ℂ
  | none => PowerSeries.X
  | some (i, j) => formalJet (S i) j

def powerPartCoordinates (d : ℕ) : ℕ → PowerSeries ℂ :=
  seriesCoordinates (powerPartSeries d)

def logDerivPowerPartCoordinates (d : ℕ) : ℕ → PowerSeries ℂ :=
  seriesCoordinates (logDerivPowerPart d)

def powerPartZPowCoordinates (d : ℕ) (k : ℤ) : ℕ → PowerSeries ℂ :=
  seriesCoordinates (powerPartZPow d k)

def logDerivPowerPartDilationCoordinates (d : ℕ) {s : ℕ} (a : Fin s → ℕ+) :
    Option (Fin s × ℕ) → PowerSeries ℂ :=
  jointSeriesCoordinates (fun i ↦ logDerivPowerPartDilated d (a i).val)

def powerPartDilationCoordinates (d : ℕ) {s : ℕ} (a : Fin s → ℕ+) :
    Option (Fin s × ℕ) → PowerSeries ℂ :=
  jointSeriesCoordinates (fun i ↦ powerPartDilated d (a i).val)

/-! ### 2. 100% Unconditional Formal Kolchin Log-Derivative Transfer (`s ≥ 1`) -/

section Kolchin

private abbrev JetVar (s : ℕ) := Option (Fin s × ℕ)

/-- Euler derivation `θ = q d/dq` on `ℂ[q, {F_i^{(j)}}]`. -/
private def thetaPolyMap {s : ℕ} : JetVar s → MvPolynomial (JetVar s) ℂ
  | none => MvPolynomial.X none
  | some (i, j) => MvPolynomial.X none * MvPolynomial.X (some (i, j + 1))

private def thetaPoly {s : ℕ} (A : MvPolynomial (JetVar s) ℂ) : MvPolynomial (JetVar s) ℂ :=
  ∑ u ∈ A.vars, MvPolynomial.pderiv u A * thetaPolyMap u

private lemma thetaPoly_eq_sum_superset {s : ℕ} (A : MvPolynomial (JetVar s) ℂ)
    (S : Finset (JetVar s)) (hS : A.vars ⊆ S) :
    thetaPoly A = ∑ u ∈ S, MvPolynomial.pderiv u A * thetaPolyMap u := by
  classical
  unfold thetaPoly
  apply Finset.sum_subset hS
  intro u _ hu
  have hp0 : MvPolynomial.pderiv u A = 0 := by
    ext m; rw [MvPolynomial.coeff_pderiv]
    have hc0 : A.coeff (m + Finsupp.single u 1) = 0 := by
      by_contra hne
      exact hu ((MvPolynomial.mem_vars_iff_mem_support u).mpr
        ⟨_, MvPolynomial.mem_support_iff.mpr hne, by simp⟩)
    simp [hc0]
  simp [hp0]

private lemma thetaPoly_add {s : ℕ} (A B : MvPolynomial (JetVar s) ℂ) :
    thetaPoly (A + B) = thetaPoly A + thetaPoly B := by
  classical
  let S := A.vars ∪ B.vars
  rw [thetaPoly_eq_sum_superset (A + B) S (MvPolynomial.vars_add_subset A B),
      thetaPoly_eq_sum_superset A S Finset.subset_union_left,
      thetaPoly_eq_sum_superset B S Finset.subset_union_right, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro u _; rw [map_add, add_mul]

private lemma thetaPoly_mul {s : ℕ} (A B : MvPolynomial (JetVar s) ℂ) :
    thetaPoly (A * B) = thetaPoly A * B + A * thetaPoly B := by
  classical
  let S := A.vars ∪ B.vars
  rw [thetaPoly_eq_sum_superset (A * B) S (MvPolynomial.vars_mul A B),
      thetaPoly_eq_sum_superset A S Finset.subset_union_left,
      thetaPoly_eq_sum_superset B S Finset.subset_union_right,
      Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro u _; rw [MvPolynomial.pderiv_mul]; ring

private lemma thetaPoly_C {s : ℕ} (c : ℂ) : thetaPoly (s := s) (MvPolynomial.C c) = 0 := by
  simp [thetaPoly]

private lemma thetaPoly_X {s : ℕ} (u : JetVar s) :
    thetaPoly (MvPolynomial.X u) = thetaPolyMap u := by
  classical
  unfold thetaPoly
  rw [MvPolynomial.vars_X, Finset.sum_singleton, MvPolynomial.pderiv_X_self, one_mul]

private lemma thetaPoly_eval {s : ℕ} (F : Fin s → PowerSeries ℂ)
    (A : MvPolynomial (JetVar s) ℂ) :
    PowerSeries.X * PowerSeries.derivative (R := ℂ) (MvPolynomial.aeval (jointSeriesCoordinates F) A) =
      MvPolynomial.aeval (jointSeriesCoordinates F) (thetaPoly A) := by
  induction A using MvPolynomial.induction_on with
  | C c =>
    rw [thetaPoly_C, map_zero, MvPolynomial.aeval_C, PowerSeries.algebraMap_apply,
        PowerSeries.derivative_C, mul_zero]
  | add A B hA hB =>
    rw [thetaPoly_add, map_add, map_add, map_add, mul_add, hA, hB]
  | mul_X A u hA =>
    rw [thetaPoly_mul, thetaPoly_X, map_mul (MvPolynomial.aeval (jointSeriesCoordinates F)),
        Derivation.leibniz, smul_eq_mul, smul_eq_mul,
        map_add, map_mul, map_mul, MvPolynomial.aeval_X]
    have hstep : PowerSeries.X * PowerSeries.derivative (R := ℂ) (jointSeriesCoordinates F u) =
        MvPolynomial.aeval (jointSeriesCoordinates F) (thetaPolyMap u) := by
      cases u with
      | none => simp [jointSeriesCoordinates, thetaPolyMap, PowerSeries.derivative_X]
      | some ij =>
        simp only [jointSeriesCoordinates, thetaPolyMap, map_mul, MvPolynomial.aeval_X]
        rw [formalJet, formalJet, Function.iterate_succ_apply']
    linear_combination (MvPolynomial.aeval (jointSeriesCoordinates F) A) * hstep +
      (jointSeriesCoordinates F u) * hA

private lemma pderiv_ne_zero_of_mem_vars {σ : Type*} [DecidableEq σ] {P : MvPolynomial σ ℂ}
    {u : σ} (hu : u ∈ P.vars) : MvPolynomial.pderiv u P ≠ 0 := by
  obtain ⟨m, hm, hmu⟩ := (MvPolynomial.mem_vars_iff_mem_support u).mp hu
  have hc : P.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hm_pos : 0 < m u := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hmu)
  intro h0
  let m' : σ →₀ ℕ := m - Finsupp.single u 1
  have hm_eq : m' + Finsupp.single u 1 = m := by
    ext v
    by_cases hv : v = u
    · subst hv; simp [m']; omega
    · simp [m', Finsupp.single_eq_of_ne hv]
  have h1 := congrArg (fun q : MvPolynomial σ ℂ ↦ q.coeff m') h0
  rw [MvPolynomial.coeff_pderiv, show (0 : MvPolynomial σ ℂ).coeff m' = 0 from rfl, hm_eq] at h1
  have hcast : ((m' u : ℂ) + 1) ≠ 0 := by
    have : (m' u + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero _
    exact_mod_cast this
  exact mul_ne_zero hc hcast h1

private lemma pderiv_vars_subset {σ : Type*} [DecidableEq σ] (v : σ) (P : MvPolynomial σ ℂ) :
    (MvPolynomial.pderiv v P).vars ⊆ P.vars := by
  intro u hu
  obtain ⟨m, hm, hmu⟩ := (MvPolynomial.mem_vars_iff_mem_support u).mp hu
  have hc : (MvPolynomial.pderiv v P).coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hc
  have hP : P.coeff (m + Finsupp.single v 1) ≠ 0 := left_ne_zero_of_mul hc
  refine (MvPolynomial.mem_vars_iff_mem_support u).mpr
    ⟨m + Finsupp.single v 1, MvPolynomial.mem_support_iff.mpr hP, ?_⟩
  rw [Finsupp.mem_support_iff] at hmu ⊢
  simp only [Finsupp.coe_add, Pi.add_apply]
  omega

private lemma vars_sum_subset {σ ι : Type*} [DecidableEq σ] (s : Finset ι)
    (f : ι → MvPolynomial σ ℂ) :
    (∑ i ∈ s, f i).vars ⊆ s.biUnion (fun i ↦ (f i).vars) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.biUnion_insert]
    exact (MvPolynomial.vars_add_subset _ _).trans (Finset.union_subset_union_right ih)

private lemma pderiv_thetaPoly_top {s : ℕ} (A : MvPolynomial (JetVar s) ℂ)
    (i₀ : Fin s) (M : ℕ)
    (hmax : ∀ j > M, some (i₀, j) ∉ A.vars) :
    MvPolynomial.pderiv (some (i₀, M + 1)) (thetaPoly A) =
      MvPolynomial.X none * MvPolynomial.pderiv (some (i₀, M)) A := by
  classical
  have hvan (v : JetVar s) (hv : v ∉ A.vars) : MvPolynomial.pderiv v A = 0 := by
    ext m; rw [MvPolynomial.coeff_pderiv]
    have hc0 : A.coeff (m + Finsupp.single v 1) = 0 := by
      by_contra hne
      exact hv ((MvPolynomial.mem_vars_iff_mem_support v).mpr
        ⟨_, MvPolynomial.mem_support_iff.mpr hne, by simp⟩)
    simp [hc0]
  let S := insert (some (i₀, M)) A.vars
  rw [thetaPoly_eq_sum_superset A S (Finset.subset_insert _ _), map_sum]
  rw [Finset.sum_eq_single (some (i₀, M))]
  · rw [MvPolynomial.pderiv_mul]
    have hp1 : MvPolynomial.pderiv (some (i₀, M + 1)) (MvPolynomial.pderiv (some (i₀, M)) A) = 0 := by
      rw [MvPolynomial.pderiv_comm, hvan _ (hmax (M + 1) (by omega)), map_zero]
    have hp2 : MvPolynomial.pderiv (some (i₀, M + 1)) (thetaPolyMap (some (i₀, M))) =
        MvPolynomial.X none := by
      simp [thetaPolyMap, MvPolynomial.pderiv_X]
    rw [hp1, hp2]; ring
  · intro u hu hne
    rw [MvPolynomial.pderiv_mul]
    have hp1 : MvPolynomial.pderiv (some (i₀, M + 1)) (MvPolynomial.pderiv u A) = 0 := by
      rw [MvPolynomial.pderiv_comm, hvan _ (hmax (M + 1) (by omega)), map_zero]
    have hp2 : MvPolynomial.pderiv (some (i₀, M + 1)) (thetaPolyMap u) = 0 := by
      cases u with
      | none => simp [thetaPolyMap, MvPolynomial.pderiv_X]
      | some ij =>
        rcases ij with ⟨i₁, j₁⟩
        simp only [thetaPolyMap, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
          Pi.single_apply, reduceCtorEq, ↓reduceIte, zero_mul, zero_add, mul_eq_zero]
        right
        split_ifs with h
        · exfalso; apply hne
          have hpair := Option.some.inj h
          have h1 : i₁ = i₀ := congrArg Prod.fst hpair
          have h2 : j₁ = M := Nat.succ.inj (congrArg Prod.snd hpair)
          exact congrArg some (Prod.ext h1 h2)
        · rfl
    simp [hp1, hp2]
  · intro h; exact (h (Finset.mem_insert_self _ _)).elim

/-- Univariate ratio-constancy in char 0: if `u * v' = u' * v` with `u, v ≠ 0` in `R[Y]`,
then `u` and `v` are scalar multiples of each other over `R` (`β • u = α • v` with `α, β ≠ 0`). -/
private lemma poly_wronskian_zero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {u v : Polynomial R} (hu : u ≠ 0) (hv : v ≠ 0)
    (hwr : u * Polynomial.derivative v = Polynomial.derivative u * v) :
    Polynomial.C v.leadingCoeff * u = Polynomial.C u.leadingCoeff * v := by
  have hdeg_eq : ∀ {a b : Polynomial R}, a ≠ 0 → b ≠ 0 →
      a * Polynomial.derivative b = Polynomial.derivative a * b → a.natDegree = b.natDegree := by
    intro a b ha hb h
    by_cases hab : a.natDegree = 0 ∧ b.natDegree = 0
    · omega
    · have hpos : 1 ≤ a.natDegree + b.natDegree := by omega
      have hc := congrArg (fun p ↦ p.coeff (a.natDegree + b.natDegree - 1)) h
      have hmul_c (p q : Polynomial R) :
          (p * Polynomial.derivative q).coeff (p.natDegree + q.natDegree - 1) =
            p.leadingCoeff * q.leadingCoeff * (q.natDegree : R) := by
        rw [Polynomial.coeff_mul]
        by_cases hq0 : q.natDegree = 0
        · rw [hq0, Polynomial.eq_C_of_natDegree_eq_zero hq0, Polynomial.derivative_C]
          simp
        · have hmem : (p.natDegree, q.natDegree - 1) ∈
              Finset.antidiagonal (p.natDegree + q.natDegree - 1) := by
            rw [Finset.mem_antidiagonal]; omega
          rw [Finset.sum_eq_single (p.natDegree, q.natDegree - 1)]
          · rw [Polynomial.coeff_derivative]
            have hsub : q.natDegree - 1 + 1 = q.natDegree := by omega
            have hcast : ((q.natDegree - 1 : ℕ) : R) + 1 = (q.natDegree : R) := by exact_mod_cast hsub
            rw [hsub, Polynomial.leadingCoeff, Polynomial.leadingCoeff]
            linear_combination p.coeff p.natDegree * q.coeff q.natDegree * hcast
          · rintro ⟨i, j⟩ hij hne
            have hsum : i + j = p.natDegree + q.natDegree - 1 := Finset.mem_antidiagonal.mp hij
            have hne' : i ≠ p.natDegree ∨ j ≠ q.natDegree - 1 := by
              by_contra hnot; push Not at hnot; exact hne (Prod.ext hnot.1 hnot.2)
            rw [Polynomial.coeff_derivative]
            by_cases hi : p.natDegree < i
            · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
            · have hj : q.natDegree < j + 1 := by omega
              rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj, zero_mul, mul_zero]
          · intro hnot; exact (hnot hmem).elim
      rw [hmul_c a b, mul_comm (Polynomial.derivative a) b, add_comm a.natDegree b.natDegree,
          hmul_c b a] at hc
      have hprod_ne : a.leadingCoeff * b.leadingCoeff ≠ 0 :=
        mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr ha) (Polynomial.leadingCoeff_ne_zero.mpr hb)
      have heqR : (b.natDegree : R) = (a.natDegree : R) :=
        mul_left_cancel₀ hprod_ne (by linear_combination hc)
      exact (Nat.cast_injective heqR).symm
  have hk : u.natDegree = v.natDegree := hdeg_eq hu hv hwr
  let w : Polynomial R := Polynomial.C v.leadingCoeff * u - Polynomial.C u.leadingCoeff * v
  by_contra hne
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hne
  have hwr_w : w * Polynomial.derivative v = Polynomial.derivative w * v := by
    dsimp only [w]
    rw [map_sub, Polynomial.derivative_C_mul, Polynomial.derivative_C_mul]
    linear_combination Polynomial.C v.leadingCoeff * hwr
  have hdeg_w : w.natDegree = v.natDegree := hdeg_eq hw0 hv hwr_w
  have htop_zero : w.coeff v.natDegree = 0 := by
    dsimp only [w]
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
        Polynomial.leadingCoeff, Polynomial.leadingCoeff, hk]
    ring
  have hlead_ne : w.coeff w.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hw0
  rw [hdeg_w] at hlead_ne
  exact hlead_ne htop_zero

/-- Lifting `poly_wronskian_zero` to any variable `y` of `MvPolynomial σ ℂ`:
if `u * pderiv y v = pderiv y u * v` with `u, v ≠ 0`, then there exist nonzero `α, β`
not involving `y` (with `vars ⊆ (u.vars ∪ v.vars).erase y`) such that `β * u = α * v`. -/
private lemma mvpoly_wronskian_elim {σ : Type*} [DecidableEq σ] (y : σ)
    {u v : MvPolynomial σ ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hwr : u * MvPolynomial.pderiv y v = MvPolynomial.pderiv y u * v) :
    ∃ α β : MvPolynomial σ ℂ, α ≠ 0 ∧ β ≠ 0 ∧
      α.vars ⊆ u.vars.erase y ∧ β.vars ⊆ v.vars.erase y ∧ β * u = α * v := by
  classical
  let e : Option {x : σ // x ≠ y} ≃ σ := Equiv.optionSubtypeNe y
  let Φ : MvPolynomial σ ℂ ≃ₐ[ℂ] Polynomial (MvPolynomial {x : σ // x ≠ y} ℂ) :=
    (MvPolynomial.renameEquiv ℂ e.symm).trans (MvPolynomial.optionEquivLeft ℂ {x : σ // x ≠ y})
  let incl : MvPolynomial {x : σ // x ≠ y} ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
    MvPolynomial.rename Subtype.val
  have hΦ_deriv (P : MvPolynomial σ ℂ) :
      Φ (MvPolynomial.pderiv y P) = Polynomial.derivative (Φ P) := by
    induction P using MvPolynomial.induction_on with
    | C c =>
      simp only [MvPolynomial.pderiv_C, map_zero]
      have hC : Φ (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
        simp [Φ, MvPolynomial.optionEquivLeft_C]
      rw [hC, Polynomial.derivative_C]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p z hp =>
      rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, map_mul, Polynomial.derivative_mul, hp]
      by_cases hzy : z = y
      · subst hzy
        have hX : Φ (MvPolynomial.X z) = Polynomial.X := by
          have he : e.symm z = none := e.symm_apply_eq.mpr rfl
          simp [Φ, he, MvPolynomial.optionEquivLeft_X_none]
        rw [MvPolynomial.pderiv_X_self, map_one, hX, Polynomial.derivative_X]
      · have hX : Φ (MvPolynomial.X z) = Polynomial.C (MvPolynomial.X ⟨z, hzy⟩) := by
          have he : e.symm z = some ⟨z, hzy⟩ := e.symm_apply_eq.mpr rfl
          simp [Φ, he, MvPolynomial.optionEquivLeft_X_some]
        rw [MvPolynomial.pderiv_X, Pi.single_eq_of_ne hzy, map_zero, hX,
            Polynomial.derivative_C]
  have hΦ_C (A : MvPolynomial {x : σ // x ≠ y} ℂ) :
      Φ (incl A) = Polynomial.C A := by
    induction A using MvPolynomial.induction_on with
    | C c => simp [Φ, incl, MvPolynomial.optionEquivLeft_C]
    | add p q hp hq => simp [hp, hq]
    | mul_X p z hp =>
      rw [map_mul, map_mul, hp, Polynomial.C_mul]
      congr 1
      have he : e.symm z.val = some z := e.symm_apply_eq.mpr rfl
      simp [Φ, incl, he, MvPolynomial.optionEquivLeft_X_some]
  have hu' : Φ u ≠ 0 := fun h ↦ hu (Φ.injective (h.trans (map_zero Φ).symm))
  have hv' : Φ v ≠ 0 := fun h ↦ hv (Φ.injective (h.trans (map_zero Φ).symm))
  have hwr' : Φ u * Polynomial.derivative (Φ v) = Polynomial.derivative (Φ u) * Φ v := by
    rw [← hΦ_deriv u, ← hΦ_deriv v, ← map_mul, ← map_mul, hwr]
  have hrel := poly_wronskian_zero hu' hv' hwr'
  let α₀ := (Φ u).leadingCoeff
  let β₀ := (Φ v).leadingCoeff
  let α := incl α₀
  let β := incl β₀
  have hα0 : α ≠ 0 := by
    intro h
    have h0 := congrArg Φ h
    rw [hΦ_C, map_zero] at h0
    exact Polynomial.leadingCoeff_ne_zero.mpr hu' (Polynomial.C_eq_zero.mp h0)
  have hβ0 : β ≠ 0 := by
    intro h
    have h0 := congrArg Φ h
    rw [hΦ_C, map_zero] at h0
    exact Polynomial.leadingCoeff_ne_zero.mpr hv' (Polynomial.C_eq_zero.mp h0)
  have heq : β * u = α * v := Φ.injective (by rw [map_mul, map_mul, hΦ_C, hΦ_C]; exact hrel)
  have hvars_mon (m : σ →₀ ℕ) (c : ℂ) (k : ℕ) :
      (incl ((Φ (MvPolynomial.monomial m c)).coeff k)).vars ⊆ m.support.erase y := by
    let coeffM : MvPolynomial {x : σ // x ≠ y} ℂ :=
      MvPolynomial.C c * ∏ x ∈ m.support.erase y,
        if h : x = y then 1 else MvPolynomial.X ⟨x, h⟩ ^ m x
    have hΦm : Φ (MvPolynomial.monomial m c) = Polynomial.C coeffM * Polynomial.X ^ (m y) := by
      have hmon_eq : MvPolynomial.monomial m c =
          MvPolynomial.C c * (∏ x ∈ m.support.erase y, MvPolynomial.X x ^ m x) *
            MvPolynomial.X y ^ (m y) := by
        rw [MvPolynomial.monomial_eq, Finsupp.prod]
        by_cases hy : y ∈ m.support
        · rw [← Finset.mul_prod_erase _ _ hy]; ring
        · have hmy0 : m y = 0 := Finsupp.notMem_support_iff.mp hy
          rw [Finset.erase_eq_of_notMem hy, hmy0, pow_zero, mul_one]
      rw [hmon_eq, map_mul, map_mul, map_pow, map_prod]
      have hC : Φ (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
        simp [Φ, MvPolynomial.optionEquivLeft_C]
      have hXy : Φ (MvPolynomial.X y) = Polynomial.X := by
        have he : e.symm y = none := e.symm_apply_eq.mpr rfl
        simp [Φ, he, MvPolynomial.optionEquivLeft_X_none]
      have hprod : ∏ x ∈ m.support.erase y, Φ (MvPolynomial.X x ^ m x) =
          Polynomial.C (∏ x ∈ m.support.erase y,
            if h : x = y then 1 else MvPolynomial.X ⟨x, h⟩ ^ m x) := by
        rw [map_prod]
        apply Finset.prod_congr rfl; intro x hx
        have hxy : x ≠ y := (Finset.mem_erase.mp hx).1
        simp only [hxy, ↓reduceDIte, map_pow]
        congr 1
        have he : e.symm x = some ⟨x, hxy⟩ := e.symm_apply_eq.mpr rfl
        simp [Φ, he, MvPolynomial.optionEquivLeft_X_some]
      rw [hC, hXy, hprod, ← Polynomial.C_mul]
    rw [hΦm, Polynomial.coeff_C_mul_X_pow]
    split_ifs with hk
    · have hincl : incl coeffM =
          MvPolynomial.C c * ∏ x ∈ m.support.erase y, MvPolynomial.X x ^ m x := by
        dsimp only [coeffM, incl]
        rw [map_mul, MvPolynomial.rename_C, map_prod]
        congr 1; apply Finset.prod_congr rfl; intro x hx
        have hxy : x ≠ y := (Finset.mem_erase.mp hx).1
        simp only [hxy, ↓reduceDIte, map_pow, MvPolynomial.rename_X]
      rw [hincl]
      refine (MvPolynomial.vars_mul _ _).trans ?_
      rw [MvPolynomial.vars_C, Finset.empty_union]
      have hvars_prod : ∀ S : Finset σ,
          (∏ x ∈ S, (MvPolynomial.X x : MvPolynomial σ ℂ) ^ m x).vars ⊆ S := by
        intro S
        induction S using Finset.induction_on with
        | empty => simp
        | @insert a S ha ih =>
          rw [Finset.prod_insert ha]
          refine (MvPolynomial.vars_mul _ _).trans ?_
          apply Finset.union_subset
          · exact (MvPolynomial.vars_pow _ _).trans (by rw [MvPolynomial.vars_X]; exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self a S))
          · exact ih.trans (Finset.subset_insert a S)
      exact hvars_prod (m.support.erase y)
    · simp
  have hvars_sub (P : MvPolynomial σ ℂ) (k : ℕ) :
      (incl ((Φ P).coeff k)).vars ⊆ P.vars.erase y := by
    have hsum : incl ((Φ P).coeff k) =
        ∑ m ∈ P.support, incl ((Φ (MvPolynomial.monomial m (P.coeff m))).coeff k) := by
      conv_lhs => rw [MvPolynomial.as_sum P]
      rw [map_sum]
      have hcoeff_sum : (∑ m ∈ P.support, Φ (MvPolynomial.monomial m (P.coeff m))).coeff k =
          ∑ m ∈ P.support, (Φ (MvPolynomial.monomial m (P.coeff m))).coeff k := by
        change Polynomial.lcoeff _ k (∑ m ∈ P.support, _) = _
        rw [map_sum]; rfl
      rw [hcoeff_sum, map_sum]
    rw [hsum]
    refine (vars_sum_subset _ _).trans ?_
    intro z hz
    obtain ⟨m, hm, hzm⟩ := Finset.mem_biUnion.mp hz
    have hzm' := hvars_mon m (P.coeff m) k hzm
    rw [Finset.mem_erase] at hzm' ⊢
    exact ⟨hzm'.1, (MvPolynomial.mem_vars_iff_mem_support z).mpr ⟨m, hm, hzm'.2⟩⟩
  exact ⟨α, β, hα0, hβ0, hvars_sub u _, hvars_sub v _, heq⟩

/-- Core Kolchin non-existence lemma: in `ℂ[q, {F_i^{(j)}}]`, NO nonzero pair `(u, v)`
can satisfy `u · θ(v) - θ(u) · v = u · v · ∑ c_i F_i` with some `c_i ≠ 0`! -/
private lemma kolchin_no_logDeriv_relation {s : ℕ} (L : Fin s → ℂ) (hL : ∃ i, L i ≠ 0) :
    ∀ (u v : MvPolynomial (JetVar s) ℂ), u ≠ 0 → v ≠ 0 →
      u * thetaPoly v - thetaPoly u * v ≠
        u * v * (∑ i : Fin s, MvPolynomial.C (L i) * MvPolynomial.X (some (i, 0))) := by
  classical
  let nonQ (u v : MvPolynomial (JetVar s) ℂ) : Finset (Fin s × ℕ) :=
    (u.vars ∪ v.vars).biUnion (fun x ↦ match x with | none => ∅ | some p => {p})
  have mem_nonQ (u v : MvPolynomial (JetVar s) ℂ) (p : Fin s × ℕ) :
      p ∈ nonQ u v ↔ some p ∈ u.vars ∪ v.vars := by
    simp only [nonQ, Finset.mem_biUnion]
    constructor
    · rintro ⟨x, hx, hpx⟩
      cases x with
      | none => exact (Finset.notMem_empty p hpx).elim
      | some q => rw [Finset.mem_singleton.mp hpx]; exact hx
    · intro h; exact ⟨some p, h, Finset.mem_singleton_self p⟩
  suffices h : ∀ n : ℕ, ∀ u v : MvPolynomial (JetVar s) ℂ,
      (nonQ u v).card = n → u ≠ 0 → v ≠ 0 →
      u * thetaPoly v - thetaPoly u * v ≠
        u * v * (∑ i : Fin s, MvPolynomial.C (L i) * MvPolynomial.X (some (i, 0))) by
    intro u v hu hv; exact h (nonQ u v).card u v rfl hu hv
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro u v hcard hu hv heq
    by_cases hne : (nonQ u v).Nonempty
    · obtain ⟨⟨i₀, M⟩, hmem, hmax_m⟩ := (nonQ u v).exists_max_image Prod.snd hne
      have hmax_u : ∀ j > M, some (i₀, j) ∉ u.vars := fun j hj hmem_u ↦ by
        have hmem_nq : (i₀, j) ∈ nonQ u v :=
          (mem_nonQ u v (i₀, j)).mpr (Finset.mem_union_left _ hmem_u)
        have := hmax_m (i₀, j) hmem_nq
        omega
      have hmax_v : ∀ j > M, some (i₀, j) ∉ v.vars := fun j hj hmem_v ↦ by
        have hmem_nq : (i₀, j) ∈ nonQ u v :=
          (mem_nonQ u v (i₀, j)).mpr (Finset.mem_union_right _ hmem_v)
        have := hmax_m (i₀, j) hmem_nq
        omega
      have hvan {P : MvPolynomial (JetVar s) ℂ} {z : JetVar s} (hz : z ∉ P.vars) :
          MvPolynomial.pderiv z P = 0 := by
        ext m; rw [MvPolynomial.coeff_pderiv]
        have hc0 : P.coeff (m + Finsupp.single z 1) = 0 := by
          by_contra hnz
          exact hz ((MvPolynomial.mem_vars_iff_mem_support z).mpr
            ⟨_, MvPolynomial.mem_support_iff.mpr hnz, by simp⟩)
        simp [hc0]
      let topV : JetVar s := some (i₀, M + 1)
      have htop_u : MvPolynomial.pderiv topV u = 0 := hvan (hmax_u (M + 1) (by omega))
      have htop_v : MvPolynomial.pderiv topV v = 0 := hvan (hmax_v (M + 1) (by omega))
      have htop_L : MvPolynomial.pderiv topV
          (∑ i : Fin s, MvPolynomial.C (L i) * MvPolynomial.X (some (i, 0))) = 0 := by
        rw [map_sum]
        apply Finset.sum_eq_zero; intro i _
        rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add,
            MvPolynomial.pderiv_X, Pi.single_eq_of_ne (by simp [topV]), mul_zero]
      have hd := congrArg (MvPolynomial.pderiv topV) heq
      rw [map_sub, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
          MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
          htop_u, htop_v, htop_L,
          pderiv_thetaPoly_top u i₀ M hmax_u, pderiv_thetaPoly_top v i₀ M hmax_v] at hd
      simp only [zero_mul, mul_zero, add_zero, zero_add] at hd
      have hX_fac : MvPolynomial.X none *
          (u * MvPolynomial.pderiv (some (i₀, M)) v - MvPolynomial.pderiv (some (i₀, M)) u * v) = 0 := by
        linear_combination hd
      have hwr : u * MvPolynomial.pderiv (some (i₀, M)) v =
          MvPolynomial.pderiv (some (i₀, M)) u * v :=
        sub_eq_zero.mp ((mul_eq_zero.mp hX_fac).resolve_left (MvPolynomial.X_ne_zero none))
      obtain ⟨α, β, hα0, hβ0, hα_vars, hβ_vars, hrel⟩ :=
        mvpoly_wronskian_elim (some (i₀, M)) hu hv hwr
      have hθ_rel := congrArg thetaPoly hrel
      rw [thetaPoly_mul, thetaPoly_mul] at hθ_rel
      have hnew : (α * thetaPoly β - thetaPoly α * β -
          α * β * (∑ i : Fin s, MvPolynomial.C (L i) * MvPolynomial.X (some (i, 0)))) * v ^ 2 = 0 := by
        linear_combination (β * v) * hθ_rel + (β ^ 2) * heq -
          (v * thetaPoly β + β * thetaPoly v -
            β * v * (∑ i : Fin s, MvPolynomial.C (L i) * MvPolynomial.X (some (i, 0)))) * hrel
      have hαβ_eq : α * thetaPoly β - thetaPoly α * β =
          α * β * (∑ i : Fin s, MvPolynomial.C (L i) * MvPolynomial.X (some (i, 0))) :=
        sub_eq_zero.mp ((mul_eq_zero.mp hnew).resolve_right (pow_ne_zero 2 hv))
      have hsub : nonQ α β ⊆ (nonQ u v).erase (i₀, M) := by
        intro p hp
        have hz : some p ∈ α.vars ∪ β.vars := (mem_nonQ α β p).mp hp
        rw [Finset.mem_erase]
        rcases Finset.mem_union.mp hz with hzu | hzv
        · have h1 := Finset.mem_erase.mp (hα_vars hzu)
          refine ⟨fun h ↦ h1.1 (congrArg some h),
            (mem_nonQ u v p).mpr (Finset.mem_union_left _ h1.2)⟩
        · have h1 := Finset.mem_erase.mp (hβ_vars hzv)
          refine ⟨fun h ↦ h1.1 (congrArg some h),
            (mem_nonQ u v p).mpr (Finset.mem_union_right _ h1.2)⟩
      have hlt : (nonQ α β).card < n := by
        rw [← hcard]
        exact (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem hmem)
      exact ih (nonQ α β).card hlt α β rfl hα0 hβ0 hαβ_eq
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      obtain ⟨i₀, hi₀⟩ := hL
      have hno_some (P : MvPolynomial (JetVar s) ℂ) (hP : P.vars ⊆ u.vars ∪ v.vars)
          (ij : Fin s × ℕ) : some ij ∉ P.vars := fun hmem ↦ by
        have : ij ∈ nonQ u v := (mem_nonQ u v ij).mpr (hP hmem)
        rw [hne] at this; exact Finset.notMem_empty ij this
      have hvan {P : MvPolynomial (JetVar s) ℂ} {z : JetVar s} (hz : z ∉ P.vars) :
          MvPolynomial.pderiv z P = 0 := by
        ext m; rw [MvPolynomial.coeff_pderiv]
        have hc0 : P.coeff (m + Finsupp.single z 1) = 0 := by
          by_contra hnz
          exact hz ((MvPolynomial.mem_vars_iff_mem_support z).mpr
            ⟨_, MvPolynomial.mem_support_iff.mpr hnz, by simp⟩)
        simp [hc0]
      have hθ_only_none (P : MvPolynomial (JetVar s) ℂ) (hP : P.vars ⊆ u.vars ∪ v.vars) :
          thetaPoly P = MvPolynomial.pderiv none P * MvPolynomial.X none := by
        rw [thetaPoly_eq_sum_superset P {none} (fun z hz ↦ by
          cases z with
          | none => simp
          | some ij => exact (hno_some P hP ij hz).elim)]
        simp [thetaPolyMap]
      have hθ_van (P : MvPolynomial (JetVar s) ℂ) (hP : P.vars ⊆ u.vars ∪ v.vars) :
          MvPolynomial.pderiv (some (i₀, 0)) (thetaPoly P) = 0 := by
        rw [hθ_only_none P hP, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_comm,
            hvan (hno_some P hP (i₀, 0)), map_zero, zero_mul, zero_add,
            MvPolynomial.pderiv_X, Pi.single_eq_of_ne (by simp), mul_zero]
      have hd := congrArg (MvPolynomial.pderiv (some (i₀, 0))) heq
      rw [map_sub, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
          MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
          hvan (hno_some u Finset.subset_union_left (i₀, 0)),
          hvan (hno_some v Finset.subset_union_right (i₀, 0)),
          hθ_van u Finset.subset_union_left, hθ_van v Finset.subset_union_right] at hd
      simp only [zero_mul, mul_zero, add_zero, zero_add, sub_self] at hd
      have hdL : MvPolynomial.pderiv (some (i₀, 0))
          (∑ i : Fin s, MvPolynomial.C (L i) * MvPolynomial.X (some (i, 0))) =
          MvPolynomial.C (L i₀) := by
        rw [map_sum, Finset.sum_eq_single i₀]
        · rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add,
              MvPolynomial.pderiv_X_self, mul_one]
        · intro i _ hne_i
          rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add,
              MvPolynomial.pderiv_X, Pi.single_eq_of_ne (by simp [hne_i]), mul_zero]
        · intro h; exact (h (Finset.mem_univ i₀)).elim
      rw [hdL] at hd
      exact mul_ne_zero (mul_ne_zero hu hv) (MvPolynomial.C_ne_zero.mpr hi₀) hd.symm

/-- Universal Faà-di-Bruno / log-derivative jet polynomials `R_{i, j} ∈ ℂ[q, {F_i^{(k)}}]`
satisfying `X^j · P_i^{(j)} = R_{i, j}(F) · P_i`. -/
private def logDerivJetPoly {s : ℕ} (c : Fin s → ℂ) (i : Fin s) :
    ℕ → MvPolynomial (JetVar s) ℂ
  | 0 => 1
  | j + 1 => thetaPoly (logDerivJetPoly c i j) +
      (MvPolynomial.C (c i) * MvPolynomial.X (some (i, 0)) - MvPolynomial.C (j : ℂ)) *
        logDerivJetPoly c i j

private lemma aeval_logDerivJetPoly {s : ℕ} (F P : Fin s → PowerSeries ℂ) (c : Fin s → ℂ)
    (hlog : ∀ i, PowerSeries.X * PowerSeries.derivative (R := ℂ) (P i) =
      (PowerSeries.C (c i) * F i) * P i) (i : Fin s) (j : ℕ) :
    PowerSeries.X ^ j * formalJet (P i) j =
      MvPolynomial.aeval (jointSeriesCoordinates F) (logDerivJetPoly c i j) * P i := by
  induction j with
  | zero => simp [logDerivJetPoly, formalJet]
  | succ j ih =>
    have hstep := congrArg (PowerSeries.X * PowerSeries.derivative (R := ℂ) ·) ih
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_add,
        PowerSeries.derivative_pow, PowerSeries.derivative_X, mul_one] at hstep
    have hlhs1 : PowerSeries.X * (formalJet (P i) j * ((j : PowerSeries ℂ) * PowerSeries.X ^ (j - 1))) =
        (j : PowerSeries ℂ) * (PowerSeries.X ^ j * formalJet (P i) j) := by
      cases j with
      | zero => simp
      | succ j' => simp [pow_succ]; ring
    have hlhs2 : PowerSeries.X * (PowerSeries.X ^ j * PowerSeries.derivative (R := ℂ) (formalJet (P i) j)) =
        PowerSeries.X ^ (j + 1) * formalJet (P i) (j + 1) := by
      rw [formalJet, formalJet, Function.iterate_succ_apply', pow_succ]; ring
    rw [hlhs1, hlhs2, ih] at hstep
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_add] at hstep
    have hstep' : PowerSeries.X ^ (j + 1) * formalJet (P i) (j + 1) +
        (j : PowerSeries ℂ) * (MvPolynomial.aeval (jointSeriesCoordinates F) (logDerivJetPoly c i j) * P i) =
        MvPolynomial.aeval (jointSeriesCoordinates F) (thetaPoly (logDerivJetPoly c i j)) * P i +
        MvPolynomial.aeval (jointSeriesCoordinates F) (logDerivJetPoly c i j) *
          ((PowerSeries.C (c i) * F i) * P i) := by
      linear_combination hstep +
        P i * thetaPoly_eval F (logDerivJetPoly c i j) +
        MvPolynomial.aeval (jointSeriesCoordinates F) (logDerivJetPoly c i j) * hlog i
    rw [logDerivJetPoly, map_add, map_mul, map_sub, map_mul, MvPolynomial.aeval_C,
        MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    simp only [jointSeriesCoordinates, formalJet, Function.iterate_zero, id_eq,
      PowerSeries.algebraMap_apply] at hstep' ⊢
    have hnatC : (j : PowerSeries ℂ) = PowerSeries.C (j : ℂ) := by simp
    rw [hnatC] at hstep'
    linear_combination hstep'

private lemma logDerivJetPoly_pderiv_props {s : ℕ} (c : Fin s → ℂ) (i : Fin s) :
    ∀ j : ℕ,
      (∀ i' r, (i' ≠ i ∨ j ≤ r) → MvPolynomial.pderiv (some (i', r)) (logDerivJetPoly c i j) = 0) ∧
      (∀ j', j = j' + 1 →
        MvPolynomial.pderiv (some (i, j')) (logDerivJetPoly c i j) =
          MvPolynomial.C (c i) * (MvPolynomial.X none) ^ j') := by
  intro j
  induction j with
  | zero =>
    refine ⟨fun i' r _ ↦ by simp [logDerivJetPoly], fun j' h ↦ by omega⟩
  | succ j ih =>
    obtain ⟨hvan, htop⟩ := ih
    have hvars_sub : ∀ u ∈ (logDerivJetPoly c i j).vars,
        u = none ∨ ∃ r < j, u = some (i, r) := by
      intro u hu
      cases u with
      | none => exact Or.inl rfl
      | some ij =>
        right
        by_contra hnot
        have hcond : ij.1 ≠ i ∨ j ≤ ij.2 := by
          by_cases h1 : ij.1 = i
          · right; by_contra hlt; exact hnot ⟨ij.2, by omega, congrArg some (Prod.ext h1 rfl)⟩
          · exact Or.inl h1
        exact pderiv_ne_zero_of_mem_vars hu (hvan ij.1 ij.2 hcond)
    have hpderiv_theta_ge (i' : Fin s) (r : ℕ) (hcond : i' ≠ i ∨ j ≤ r) :
        MvPolynomial.pderiv (some (i', r)) (thetaPoly (logDerivJetPoly c i j)) =
          if i' = i ∧ r = j ∧ 1 ≤ j then
            MvPolynomial.C (c i) * (MvPolynomial.X none) ^ j
          else 0 := by
      classical
      have hvan_r : MvPolynomial.pderiv (some (i', r)) (logDerivJetPoly c i j) = 0 :=
        hvan i' r hcond
      unfold thetaPoly
      rw [map_sum]
      by_cases hcase : i' = i ∧ r = j ∧ 1 ≤ j
      · rcases hcase with ⟨hi', hr, hj1⟩
        subst i'; subst r
        simp only [hj1, and_self, ↓reduceIte]
        let j' := j - 1
        have hj_eq : j = j' + 1 := by omega
        have hmem_or : ∀ u ∈ (logDerivJetPoly c i j).vars, u ≠ some (i, j') →
            MvPolynomial.pderiv (some (i, j))
              (MvPolynomial.pderiv u (logDerivJetPoly c i j) * thetaPolyMap u) = 0 := by
          intro u _ hne
          rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_comm, hvan_r, map_zero, zero_mul, zero_add]
          have hp2 : MvPolynomial.pderiv (some (i, j)) (thetaPolyMap u) = 0 := by
            cases u with
            | none => simp [thetaPolyMap, MvPolynomial.pderiv_X]
            | some ab =>
              rcases ab with ⟨a₁, b₁⟩
              simp only [thetaPolyMap, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
                Pi.single_apply, reduceCtorEq, ↓reduceIte, zero_mul, zero_add, mul_eq_zero]
              right
              split_ifs with h
              · exfalso; apply hne
                have hp := Option.some.inj h
                have h1 : a₁ = i := congrArg Prod.fst hp
                have h2 : b₁ = j' := by have := congrArg Prod.snd hp; omega
                exact congrArg some (Prod.ext h1 h2)
              · rfl
          rw [hp2, mul_zero]
        by_cases hm : some (i, j') ∈ (logDerivJetPoly c i j).vars
        · rw [Finset.sum_eq_single (some (i, j')) hmem_or (fun h ↦ (h hm).elim),
              MvPolynomial.pderiv_mul, MvPolynomial.pderiv_comm, hvan_r, map_zero, zero_mul, zero_add]
          have hp2 : MvPolynomial.pderiv (some (i, j)) (thetaPolyMap (some (i, j'))) =
              MvPolynomial.X none := by
            have heq : j' + 1 = j := hj_eq.symm
            simp [thetaPolyMap, heq, MvPolynomial.pderiv_X]
          rw [hp2, htop j' hj_eq]
          conv_rhs => rw [hj_eq, pow_succ]
          ring
        · have hzero : MvPolynomial.pderiv (some (i, j')) (logDerivJetPoly c i j) = 0 := by
            ext m; rw [MvPolynomial.coeff_pderiv]
            have hc0 : (logDerivJetPoly c i j).coeff (m + Finsupp.single (some (i, j')) 1) = 0 := by
              by_contra hnz
              exact hm ((MvPolynomial.mem_vars_iff_mem_support _).mpr
                ⟨_, MvPolynomial.mem_support_iff.mpr hnz, by simp⟩)
            simp [hc0]
          rw [htop j' hj_eq] at hzero
          have hc0 : c i = 0 := by
            have h1 := congrArg (fun p : MvPolynomial (JetVar s) ℂ ↦ p.coeff (Finsupp.single none j')) hzero
            have hX : (MvPolynomial.X none ^ j' : MvPolynomial (JetVar s) ℂ).coeff (Finsupp.single none j') = 1 := by
              rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial]; simp
            rw [MvPolynomial.coeff_C_mul, hX, mul_one] at h1
            exact h1
          rw [hc0, map_zero, zero_mul]
          apply Finset.sum_eq_zero; intro u hu
          exact hmem_or u hu (fun h ↦ hm (h ▸ hu))
      · simp only [hcase, ↓reduceIte]
        apply Finset.sum_eq_zero; intro u hu
        rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_comm, hvan_r, map_zero, zero_mul, zero_add]
        have hp2 : MvPolynomial.pderiv (some (i', r)) (thetaPolyMap u) = 0 := by
          rcases hvars_sub u hu with rfl | ⟨k, hk, rfl⟩
          · simp [thetaPolyMap, MvPolynomial.pderiv_X]
          · simp only [thetaPolyMap, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
              Pi.single_apply, reduceCtorEq, ↓reduceIte, zero_mul, zero_add, mul_eq_zero]
            right
            split_ifs with h
            · exfalso
              have hp := Option.some.inj h
              have h1 : i = i' := congrArg Prod.fst hp
              have h2 : k + 1 = r := congrArg Prod.snd hp
              rcases hcond with hni | hge
              · exact hni h1.symm
              · exact hcase ⟨h1.symm, by omega, by omega⟩
            · rfl
        rw [hp2, mul_zero]
    refine ⟨fun i' r hcond ↦ ?_, fun j' hj' ↦ ?_⟩
    · have hcond' : i' ≠ i ∨ j ≤ r := by rcases hcond with h | h; exacts [Or.inl h, Or.inr (by omega)]
      have hneg : ¬ (i' = i ∧ r = j ∧ 1 ≤ j) := by
        intro ⟨h1, h2, _⟩; rcases hcond with h | h <;> omega
      rw [logDerivJetPoly, map_add, hpderiv_theta_ge i' r hcond',
          MvPolynomial.pderiv_mul, hvan i' r hcond', mul_zero, add_zero]
      simp only [hneg, ↓reduceIte, zero_add]
      have hne0 : some (i, 0) ≠ some (i', r) := by
        intro h; have hp := Option.some.inj h
        have h1 : i = i' := congrArg Prod.fst hp
        have h2 : 0 = r := congrArg Prod.snd hp
        rcases hcond with hni | hge <;> omega
      rw [map_sub, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, MvPolynomial.pderiv_C,
          MvPolynomial.pderiv_X, Pi.single_eq_of_ne hne0]
      simp
    · have hjj : j' = j := Nat.succ.inj hj'.symm
      subst j'
      rw [logDerivJetPoly, map_add, hpderiv_theta_ge i j (Or.inr le_rfl),
          MvPolynomial.pderiv_mul, hvan i j (Or.inr le_rfl), mul_zero, add_zero]
      cases j with
      | zero =>
        simp [logDerivJetPoly]
      | succ j₀ =>
        have hne0 : some (i, 0) ≠ some (i, j₀ + 1) := by simp
        have hcond1 : i = i ∧ j₀ + 1 = j₀ + 1 ∧ 1 ≤ j₀ + 1 := ⟨rfl, rfl, Nat.succ_pos _⟩
        rw [show (if i = i ∧ j₀ + 1 = j₀ + 1 ∧ 1 ≤ j₀ + 1 then MvPolynomial.C (c i) * MvPolynomial.X none ^ (j₀ + 1) else 0) =
              MvPolynomial.C (c i) * MvPolynomial.X none ^ (j₀ + 1) by simp [hcond1]]
        rw [map_sub, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C,
            MvPolynomial.pderiv_C, MvPolynomial.pderiv_X, Pi.single_eq_of_ne hne0]
        simp

private lemma bind₁_logDerivJetPoly_injective {s : ℕ} (c : Fin s → ℂ) (hc : ∀ i, c i ≠ 0) :
    let sub : JetVar s → MvPolynomial (JetVar s) ℂ := fun
      | none => MvPolynomial.X none
      | some (_, 0) => 1
      | some (i, j + 1) => logDerivJetPoly c i (j + 1)
    ∀ Q : MvPolynomial (JetVar s) ℂ,
      (∀ i : Fin s, some (i, 0) ∉ Q.vars) →
      MvPolynomial.bind₁ sub Q = 0 → Q = 0 := by
  classical
  intro sub Q
  induction Q using (measure fun Q : MvPolynomial (JetVar s) ℂ ↦ Q.totalDegree).wf.induction with
  | h Q ih =>
    intro hno0 hbind
    by_contra hne
    let posVars : Finset (Fin s × ℕ) :=
      Q.vars.biUnion (fun x ↦ match x with | none => ∅ | some p => {p})
    have mem_posVars (p : Fin s × ℕ) : p ∈ posVars ↔ some p ∈ Q.vars := by
      simp only [posVars, Finset.mem_biUnion]
      constructor
      · rintro ⟨x, hx, hpx⟩
        cases x with
        | none => exact (Finset.notMem_empty p hpx).elim
        | some q => rw [Finset.mem_singleton.mp hpx]; exact hx
      · intro h; exact ⟨some p, h, Finset.mem_singleton_self p⟩
    by_cases hpos : posVars.Nonempty
    · obtain ⟨⟨i₀, j₀⟩, hmem, hmax⟩ := posVars.exists_max_image Prod.snd hpos
      have hm_var : some (i₀, j₀) ∈ Q.vars := (mem_posVars (i₀, j₀)).mp hmem
      have hj₀_pos : 1 ≤ j₀ := by
        by_contra h0
        have : j₀ = 0 := by omega
        subst this; exact hno0 i₀ hm_var
      let r := j₀ - 1
      have hj₀_eq : j₀ = r + 1 := by omega
      have hchain : ∀ P : MvPolynomial (JetVar s) ℂ,
          MvPolynomial.pderiv (some (i₀, r)) (MvPolynomial.bind₁ sub P) =
            ∑ u ∈ P.vars, MvPolynomial.bind₁ sub (MvPolynomial.pderiv u P) *
              MvPolynomial.pderiv (some (i₀, r)) (sub u) := by
        intro P
        have hsub (A : MvPolynomial (JetVar s) ℂ) (S : Finset (JetVar s)) (hS : A.vars ⊆ S) :
            ∑ u ∈ A.vars, MvPolynomial.bind₁ sub (MvPolynomial.pderiv u A) *
                MvPolynomial.pderiv (some (i₀, r)) (sub u) =
            ∑ u ∈ S, MvPolynomial.bind₁ sub (MvPolynomial.pderiv u A) *
                MvPolynomial.pderiv (some (i₀, r)) (sub u) := by
          apply Finset.sum_subset hS; intro u _ hu
          have hp0 : MvPolynomial.pderiv u A = 0 := by
            ext m; rw [MvPolynomial.coeff_pderiv]
            have hc0 : A.coeff (m + Finsupp.single u 1) = 0 := by
              by_contra hnz
              exact hu ((MvPolynomial.mem_vars_iff_mem_support u).mpr
                ⟨_, MvPolynomial.mem_support_iff.mpr hnz, by simp⟩)
            simp [hc0]
          simp [hp0]
        induction P using MvPolynomial.induction_on with
        | C a => simp
        | add A B hA hB =>
          let S := A.vars ∪ B.vars
          rw [map_add, map_add, hA, hB, hsub (A + B) S (MvPolynomial.vars_add_subset A B),
              hsub A S Finset.subset_union_left, hsub B S Finset.subset_union_right,
              ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro u _; rw [map_add, map_add, add_mul]
        | mul_X A v hA =>
          let S := insert v A.vars
          have hv_sub : (A * MvPolynomial.X v).vars ⊆ S :=
            (MvPolynomial.vars_mul A (MvPolynomial.X v)).trans (by
              rw [MvPolynomial.vars_X, Finset.union_comm]; exact Finset.Subset.rfl)
          rw [map_mul, MvPolynomial.bind₁_X_right, MvPolynomial.pderiv_mul, hA,
              hsub (A * MvPolynomial.X v) S hv_sub, hsub A S (Finset.subset_insert v A.vars),
              Finset.sum_mul]
          have hX : MvPolynomial.bind₁ sub A * MvPolynomial.pderiv (some (i₀, r)) (sub v) =
              ∑ u ∈ S, MvPolynomial.bind₁ sub (A * MvPolynomial.pderiv u (MvPolynomial.X v)) *
                MvPolynomial.pderiv (some (i₀, r)) (sub u) := by
            rw [Finset.sum_eq_single v]
            · simp
            · intro u _ huv
              rw [MvPolynomial.pderiv_X, Pi.single_eq_of_ne huv.symm, mul_zero, map_zero, zero_mul]
            · intro hnot; exact (hnot (Finset.mem_insert_self v A.vars)).elim
          rw [hX, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro u _
          rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, MvPolynomial.bind₁_X_right]; ring
      have hd := congrArg (MvPolynomial.pderiv (some (i₀, r))) hbind
      rw [map_zero, hchain Q] at hd
      have honly : ∀ u ∈ Q.vars, u ≠ some (i₀, j₀) →
          MvPolynomial.bind₁ sub (MvPolynomial.pderiv u Q) *
            MvPolynomial.pderiv (some (i₀, r)) (sub u) = 0 := by
        intro u hu hne_u
        cases u with
        | none =>
          simp [sub, MvPolynomial.pderiv_X]
        | some ab =>
          rcases ab with ⟨i, j⟩
          cases j with
          | zero => exact (hno0 i hu).elim
          | succ j' =>
            have hle : j' + 1 ≤ j₀ :=
              hmax (i, j' + 1) ((mem_posVars (i, j' + 1)).mpr hu)
            have hcond : i₀ ≠ i ∨ j' + 1 ≤ r := by
              by_cases hi : i₀ = i
              · right
                have hne_j : j' + 1 ≠ j₀ := fun h ↦ hne_u (congrArg some (Prod.ext hi.symm h))
                omega
              · exact Or.inl hi
            rw [show sub (some (i, j' + 1)) = logDerivJetPoly c i (j' + 1) from rfl,
                (logDerivJetPoly_pderiv_props c i (j' + 1)).1 i₀ r hcond, mul_zero]
      rw [Finset.sum_eq_single (some (i₀, j₀)) honly (fun h ↦ (h hm_var).elim)] at hd
      have htop_nz : MvPolynomial.pderiv (some (i₀, r)) (sub (some (i₀, j₀))) ≠ 0 := by
        rw [hj₀_eq, show sub (some (i₀, r + 1)) = logDerivJetPoly c i₀ (r + 1) from rfl,
            (logDerivJetPoly_pderiv_props c i₀ (r + 1)).2 r rfl]
        exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr (hc i₀))
          (pow_ne_zero r (MvPolynomial.X_ne_zero none))
      have hbind0 : MvPolynomial.bind₁ sub (MvPolynomial.pderiv (some (i₀, j₀)) Q) = 0 :=
        (mul_eq_zero.mp hd).resolve_right htop_nz
      have hdeg_pos : 0 < Q.totalDegree := by
        by_contra h0
        have hcQ := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero (not_lt.mp h0))
        rw [hcQ, vars_C] at hm_var
        exact Finset.notMem_empty _ hm_var
      have hno0' : ∀ i : Fin s, some (i, 0) ∉ (MvPolynomial.pderiv (some (i₀, j₀)) Q).vars := by
        intro i hi
        exact hno0 i (pderiv_vars_subset _ _ hi)
      have hp0 := ih (MvPolynomial.pderiv (some (i₀, j₀)) Q)
        (CubicTheta.lower_degree _ Q hdeg_pos) hno0' hbind0
      exact pderiv_ne_zero_of_mem_vars hm_var hp0
    · rw [Finset.not_nonempty_iff_eq_empty] at hpos
      have hvars_none : ∀ u ∈ Q.vars, u = none := by
        intro u hu
        cases u with
        | none => rfl
        | some ab =>
          have : ab ∈ posVars := (mem_posVars ab).mpr hu
          rw [hpos] at this; exact (Finset.notMem_empty ab this).elim
      have hid : MvPolynomial.bind₁ sub Q = Q := by
        conv_lhs => rw [MvPolynomial.as_sum Q]
        conv_rhs => rw [MvPolynomial.as_sum Q]
        rw [map_sum]
        apply Finset.sum_congr rfl; intro m hm
        rw [MvPolynomial.bind₁_monomial, MvPolynomial.monomial_eq]
        congr 1; apply Finsupp.prod_congr; intro u hu
        have huQ := (MvPolynomial.mem_vars_iff_mem_support u).mpr ⟨m, hm, hu⟩
        rw [hvars_none u huQ]
      exact hne (hid.symm.trans hbind)

/-- **100% Unconditional Formal Kolchin Joint Log-Derivative Transfer**:
For ANY `s ≥ 1`, ANY formal power series `F, P : Fin s → PowerSeries ℂ` with `P_i ≠ 0`
and nonzero constants `c_i ≠ 0` satisfying `q · P_i' = c_i · F_i · P_i`,
joint differential independence of `{F_1, …, F_s}` over `ℂ(q)` implies
joint differential independence of `{P_1, …, P_s}` over `ℂ(q)`! -/
theorem kolchin_logDeriv_joint_indep {s : ℕ}
    (F P : Fin s → PowerSeries ℂ) (c : Fin s → ℂ)
    (hP : ∀ i, P i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hlog : ∀ i, PowerSeries.X * PowerSeries.derivative (R := ℂ) (P i) =
      (PowerSeries.C (c i) * F i) * P i)
    (hF : AlgebraicIndependent ℂ (jointSeriesCoordinates F)) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates P) := by
  classical
  let RF := MvPolynomial (JetVar s) ℂ
  let evF : RF →ₐ[ℂ] PowerSeries ℂ := MvPolynomial.aeval (jointSeriesCoordinates F)
  have hevF_inj : Function.Injective evF := algebraicIndependent_iff_injective_aeval.mp hF
  let evalA : MvPolynomial (Fin s) RF →+* PowerSeries ℂ :=
    MvPolynomial.eval₂Hom evF.toRingHom P
  -- Step 1: Any nonzero polynomial in `RF[T_1, ..., T_s]` cannot vanish at `(P_1, ..., P_s)`!
  have hno_rel : ∀ A : MvPolynomial (Fin s) RF, evalA A = 0 → A = 0 := by
    suffices h : ∀ k : ℕ, ∀ A : MvPolynomial (Fin s) RF, A.support.card = k → evalA A = 0 → A = 0 by
      intro A hA; exact h A.support.card A rfl hA
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro A hcard hA0
      by_cases hA : A = 0
      · exact hA
      · have hne : A.support.Nonempty := MvPolynomial.support_nonempty.mpr hA
        obtain ⟨a, ha⟩ := hne
        by_cases hcard1 : (A.support.erase a).Nonempty
        · obtain ⟨b, hb⟩ := hcard1
          have hba : b ≠ a := Finset.ne_of_mem_erase hb
          have hb_mem : b ∈ A.support := Finset.mem_of_mem_erase hb
          let Lfun (m : Fin s →₀ ℕ) : RF :=
            ∑ i : Fin s, MvPolynomial.C ((m i : ℂ) * c i) * MvPolynomial.X (some (i, 0))
          let θA : MvPolynomial (Fin s) RF :=
            ∑ m ∈ A.support, MvPolynomial.monomial m (thetaPoly (A.coeff m) + A.coeff m * Lfun m)
          have hθA_eval : evalA θA = PowerSeries.X * PowerSeries.derivative (R := ℂ) (evalA A) := by
            have hA_sum : A = ∑ m ∈ A.support, MvPolynomial.monomial m (A.coeff m) :=
              MvPolynomial.as_sum A
            conv_rhs => rw [hA_sum]
            simp only [evalA, θA, map_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro m _
            rw [MvPolynomial.eval₂Hom_monomial, MvPolynomial.eval₂Hom_monomial,
                Derivation.leibniz, smul_eq_mul, smul_eq_mul]
            have hev1 : PowerSeries.X * PowerSeries.derivative (R := ℂ) (evF.toRingHom (A.coeff m)) =
                evF.toRingHom (thetaPoly (A.coeff m)) := thetaPoly_eval F (A.coeff m)
            have hprod_d : PowerSeries.X * PowerSeries.derivative (R := ℂ) (m.prod fun i e ↦ P i ^ e) =
                evF.toRingHom (Lfun m) * (m.prod fun i e ↦ P i ^ e) := by
              have hprod_eq : (m.prod fun i e ↦ P i ^ e) = ∏ i : Fin s, P i ^ (m i) := by
                rw [Finsupp.prod]
                exact Finset.prod_subset (Finset.subset_univ _) fun i _ hi ↦ by
                  have hm0 : m i = 0 := Finsupp.notMem_support_iff.mp hi
                  simp [hm0]
              rw [hprod_eq]
              have heach : ∀ i ∈ (Finset.univ : Finset (Fin s)),
                  PowerSeries.X * PowerSeries.derivative (R := ℂ) (P i ^ m i) =
                    (PowerSeries.C ((m i : ℂ) * c i) * F i) * P i ^ m i := fun i _ ↦ by
                induction m i with
                | zero => simp
                | succ e ihe =>
                  rw [pow_succ, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
                      Nat.cast_add, Nat.cast_one, add_mul, one_mul, map_add, map_mul]
                  rw [map_mul] at ihe
                  linear_combination (P i ^ e) * hlog i + (P i) * ihe
              rw [X_mul_deriv_finset_prod Finset.univ (fun i ↦ P i ^ m i) _ heach]
              congr 1
              change _ = evF (Lfun m)
              dsimp only [Lfun, evF]
              rw [map_sum]
              apply Finset.sum_congr rfl; intro i _
              rw [map_mul (MvPolynomial.aeval _), MvPolynomial.aeval_C, MvPolynomial.aeval_X]
              simp [jointSeriesCoordinates, formalJet]
            rw [map_add, map_mul]
            linear_combination -((m.prod fun i e ↦ P i ^ e) * hev1) -
              (evF.toRingHom (A.coeff m) * hprod_d)
          let u : RF := A.coeff a
          let v : RF := A.coeff b
          have hu0 : u ≠ 0 := MvPolynomial.mem_support_iff.mp ha
          have hv0 : v ≠ 0 := MvPolynomial.mem_support_iff.mp hb_mem
          let B : MvPolynomial (Fin s) RF :=
            MvPolynomial.C u * θA - MvPolynomial.C (thetaPoly u + u * Lfun a) * A
          have hB_eval : evalA B = 0 := by
            simp only [B, map_sub, map_mul, hθA_eval, hA0, map_zero, mul_zero, sub_self]
          have hB_supp : B.support ⊆ A.support.erase a := by
            intro m hm
            have hm_nz : B.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
            have hB_c : B.coeff m =
                u * (if m ∈ A.support then thetaPoly (A.coeff m) + A.coeff m * Lfun m else 0) -
                (thetaPoly u + u * Lfun a) * A.coeff m := by
              simp only [B, θA, MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul,
                MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
              congr 2
              rw [Finset.sum_ite_eq']
            rw [hB_c] at hm_nz
            rw [Finset.mem_erase]
            refine ⟨?_, ?_⟩
            · rintro rfl
              simp only [ha, ↓reduceIte, u] at hm_nz
              exact hm_nz (by ring)
            · by_contra hnot
              have h0 : A.coeff m = 0 := MvPolynomial.notMem_support_iff.mp hnot
              simp [hnot, h0] at hm_nz
          have hB_lt : B.support.card < k := by
            rw [← hcard]
            exact (Finset.card_le_card hB_supp).trans_lt (Finset.card_erase_lt_of_mem ha)
          have hB0 : B = 0 := ih B.support.card hB_lt B rfl hB_eval
          have hBb := congrArg (fun p : MvPolynomial (Fin s) RF ↦ p.coeff b) hB0
          rw [show (0 : MvPolynomial (Fin s) RF).coeff b = 0 from rfl] at hBb
          simp only [B, θA, MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul,
            MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq', hb_mem,
            ↓reduceIte] at hBb
          have heq_uv : u * thetaPoly v - thetaPoly u * v =
              u * v * (∑ i : Fin s, MvPolynomial.C ((((a i : ℤ) - (b i : ℤ) : ℤ) : ℂ) * c i) *
                MvPolynomial.X (some (i, 0))) := by
            have hLdiff : Lfun a - Lfun b =
                ∑ i : Fin s, MvPolynomial.C ((((a i : ℤ) - (b i : ℤ) : ℤ) : ℂ) * c i) *
                  MvPolynomial.X (some (i, 0)) := by
              dsimp only [Lfun]
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl; intro i _
              rw [← sub_mul, ← map_sub]; congr 2; push_cast; ring
            rw [← hLdiff]
            linear_combination hBb
          have hex : ∃ i : Fin s, (((a i : ℤ) - (b i : ℤ) : ℤ) : ℂ) * c i ≠ 0 := by
            have hdiff : ∃ i : Fin s, a i ≠ b i := by
              by_contra hall; push Not at hall; exact hba (Finsupp.ext hall).symm
            obtain ⟨i, hi⟩ := hdiff
            refine ⟨i, mul_ne_zero ?_ (hc i)⟩
            have hint : (a i : ℤ) - (b i : ℤ) ≠ 0 := by omega
            exact_mod_cast hint
          exact (kolchin_no_logDeriv_relation _ hex u v hu0 hv0 heq_uv).elim
        · rw [Finset.not_nonempty_iff_eq_empty] at hcard1
          have hsupp : A.support = {a} := by
            ext m
            constructor
            · intro hm
              by_contra hne_a
              have : m ∈ A.support.erase a := Finset.mem_erase.mpr ⟨Finset.mem_singleton.not.mp hne_a, hm⟩
              rw [hcard1] at this; exact Finset.notMem_empty m this
            · intro hm; rw [Finset.mem_singleton.mp hm]; exact ha
          have hA_mono : A = MvPolynomial.monomial a (A.coeff a) := by
            conv_lhs => rw [MvPolynomial.as_sum A, hsupp, Finset.sum_singleton]
          rw [hA_mono, show evalA (MvPolynomial.monomial a (A.coeff a)) =
              evF (A.coeff a) * a.prod (fun i e ↦ P i ^ e) from MvPolynomial.eval₂Hom_monomial ..] at hA0
          have hprod_ne : a.prod (fun i e ↦ P i ^ e) ≠ 0 := by
            rw [Finsupp.prod]
            exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (hP i)
          have hu0 : evF (A.coeff a) = 0 := (mul_eq_zero.mp hA0).resolve_right hprod_ne
          have hca0 : A.coeff a = 0 := hevF_inj (hu0.trans (map_zero evF).symm)
          exact (MvPolynomial.mem_support_iff.mp ha hca0).elim
  -- Step 2: Given any relation `Q(q, {P_i^{(j)}}) = 0`, build `A ∈ RF[T_1, ..., T_s]` clearing `X^K`.
  rw [algebraicIndependent_iff]
  intro Q hQ
  by_contra hQne
  let w (m : JetVar s →₀ ℕ) : ℕ :=
    m.sum fun u e ↦ match u with | none => 0 | some (_, j) => j * e
  let K : ℕ := Q.support.sup w
  let mdeg (m : JetVar s →₀ ℕ) : Fin s →₀ ℕ :=
    Finsupp.onFinset Finset.univ (fun i ↦ m.sum fun u e ↦
      match u with | none => 0 | some (i', _) => if i' = i then e else 0) (fun _ _ ↦ Finset.mem_univ _)
  let termRF (m : JetVar s →₀ ℕ) : RF :=
    MvPolynomial.C (Q.coeff m) * (MvPolynomial.X none) ^ (m none + (K - w m)) *
      m.prod (fun u e ↦ match u with | none => 1 | some (i, j) => (logDerivJetPoly c i j) ^ e)
  let A : MvPolynomial (Fin s) RF :=
    ∑ m ∈ Q.support, MvPolynomial.monomial (mdeg m) (termRF m)
  have hA_eval : evalA A = PowerSeries.X ^ K * MvPolynomial.aeval (jointSeriesCoordinates P) Q := by
    conv_rhs => rw [MvPolynomial.as_sum Q]
    simp only [A, evalA, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m hm
    rw [MvPolynomial.eval₂Hom_monomial, MvPolynomial.aeval_monomial]
    have hm_le : w m ≤ K := Finset.le_sup hm
    have hprod_P : (mdeg m).prod (fun i e ↦ P i ^ e) =
        m.prod (fun u e ↦ match u with | none => 1 | some (i, _) => P i ^ e) := by
      have h1 : (mdeg m).prod (fun i e ↦ P i ^ e) = ∏ i : Fin s, P i ^ (mdeg m i) := by
        rw [Finsupp.prod]
        exact Finset.prod_subset (Finset.subset_univ _) fun i _ hi ↦ by
          simp [Finsupp.notMem_support_iff.mp hi]
      rw [h1]
      have h2 : ∀ i : Fin s, P i ^ (mdeg m i) =
          m.prod (fun u e ↦ match u with | none => 1 | some (i', _) => if i' = i then P i ^ e else 1) := by
        intro i
        change P i ^ (m.sum fun u e ↦ match u with | none => 0 | some (i', _) => if i' = i then e else 0) = _
        rw [Finsupp.sum, Finsupp.prod, ← Finset.prod_pow_eq_pow_sum]
        apply Finset.prod_congr rfl; intro u _
        cases u with
        | none => simp
        | some ij => dsimp only; split_ifs <;> simp
      simp_rw [h2, Finsupp.prod]
      rw [Finset.prod_comm]
      apply Finset.prod_congr rfl; intro u _
      cases u with
      | none => simp
      | some ij => simp
    have hprod_F : evF (m.prod fun u e ↦ match u with
          | none => 1 | some (i, j) => (logDerivJetPoly c i j) ^ e) *
        (m.prod fun u e ↦ match u with | none => 1 | some (i, _) => P i ^ e) =
        PowerSeries.X ^ (w m) *
          (m.prod fun u e ↦ match u with | none => 1 | some (i, j) => (formalJet (P i) j) ^ e) := by
      rw [Finsupp.prod, Finsupp.prod, Finsupp.prod, map_prod, ← Finset.prod_mul_distrib]
      have hw_prod : (PowerSeries.X : PowerSeries ℂ) ^ (w m) =
          ∏ u ∈ m.support, PowerSeries.X ^ (match u with | none => 0 | some (_, j) => j * m u) := by
        dsimp only [w]; rw [Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]; rfl
      rw [hw_prod, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro u _
      cases u with
      | none => simp
      | some ij =>
        rcases ij with ⟨i, j⟩
        rw [map_pow, ← mul_pow, ← aeval_logDerivJetPoly F P c hlog i j, mul_pow, ← pow_mul]
    have hmon_P : m.prod (fun u e ↦ jointSeriesCoordinates P u ^ e) =
        PowerSeries.X ^ (m none) *
          (m.prod fun u e ↦ match u with | none => 1 | some (i, j) => (formalJet (P i) j) ^ e) := by
      rw [Finsupp.prod, Finsupp.prod]
      by_cases h0 : none ∈ m.support
      · rw [← Finset.mul_prod_erase _ _ h0, ← Finset.mul_prod_erase _ _ h0]
        simp only [jointSeriesCoordinates, one_mul]
        congr 1
        apply Finset.prod_congr rfl; intro u hu
        cases u with
        | none => exact ((Finset.mem_erase.mp hu).1 rfl).elim
        | some ij => rfl
      · have hm0 : m none = 0 := Finsupp.notMem_support_iff.mp h0
        rw [hm0, pow_zero, one_mul]
        apply Finset.prod_congr rfl; intro u hu
        cases u with
        | none => exact (h0 hu).elim
        | some ij => rfl
    change evF (termRF m) * (mdeg m).prod (fun i e ↦ P i ^ e) = _
    dsimp only [termRF]
    rw [map_mul, map_mul, map_pow, hprod_P, mul_assoc]
    erw [hprod_F]
    rw [hmon_P]
    have hC_eq : evF (MvPolynomial.C (Q.coeff m)) = PowerSeries.C (Q.coeff m) := by
      dsimp only [evF]; rw [MvPolynomial.aeval_C]; rfl
    have hX_eq : evF (MvPolynomial.X none) = PowerSeries.X := by
      dsimp only [evF]; rw [MvPolynomial.aeval_X]; rfl
    rw [hC_eq, hX_eq]
    simp only [PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have hpowK : PowerSeries.X ^ (m none + (K - w m)) * PowerSeries.X ^ (w m) =
        (PowerSeries.X : PowerSeries ℂ) ^ K * PowerSeries.X ^ (m none) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    calc PowerSeries.C (Q.coeff m) * PowerSeries.X ^ (m none + (K - w m)) *
          (PowerSeries.X ^ (w m) * m.prod fun u e ↦ match u with | none => 1 | some (i, j) => formalJet (P i) j ^ e)
        = PowerSeries.C (Q.coeff m) * (PowerSeries.X ^ (m none + (K - w m)) * PowerSeries.X ^ (w m)) *
          m.prod fun u e ↦ match u with | none => 1 | some (i, j) => formalJet (P i) j ^ e := by ring
      _ = PowerSeries.C (Q.coeff m) * (PowerSeries.X ^ K * PowerSeries.X ^ (m none)) *
          m.prod fun u e ↦ match u with | none => 1 | some (i, j) => formalJet (P i) j ^ e := by rw [hpowK]
      _ = _ := by ring
  rw [hQ, mul_zero] at hA_eval
  have hA0 : A = 0 := hno_rel A hA_eval
  -- Pick any monomial `m₀ ∈ Q.support` and examine the `mdeg m₀` homogeneous component!
  obtain ⟨m₀, hm₀⟩ := MvPolynomial.support_nonempty.mpr hQne
  let d₀ := mdeg m₀
  have hAd₀ := congrArg (fun p : MvPolynomial (Fin s) RF ↦ p.coeff d₀) hA0
  rw [show (0 : MvPolynomial (Fin s) RF).coeff d₀ = 0 from rfl] at hAd₀
  simp only [A, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial] at hAd₀
  let sub : JetVar s → RF := fun
    | none => MvPolynomial.X none
    | some (i, 0) => 1
    | some (i, j + 1) => logDerivJetPoly c i (j + 1)
  let shiftMon (m : JetVar s →₀ ℕ) : JetVar s →₀ ℕ :=
    Finsupp.onFinset (insert none m.support) (fun u ↦
      match u with
      | none => m none + (K - w m)
      | some (_, 0) => 0
      | some (i, j + 1) => m (some (i, j + 1))) (fun u hu ↦ by
        cases u with
        | none => exact Finset.mem_insert_self _ _
        | some ij =>
          rcases ij with ⟨i, j⟩
          cases j with
          | zero => exact (hu rfl).elim
          | succ j' => exact Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr hu))
  have hshift_inj : Set.InjOn shiftMon {m : JetVar s →₀ ℕ | m ∈ Q.support ∧ mdeg m = d₀} := by
    rintro m₁ ⟨hm₁, hd₁⟩ m₂ ⟨hm₂, hd₂⟩ heq
    have hpos : ∀ i j, m₁ (some (i, j + 1)) = m₂ (some (i, j + 1)) := fun i j ↦ by
      simpa [shiftMon] using DFunLike.congr_fun heq (some (i, j + 1))
    have hw_eq : w m₁ = w m₂ := by
      let S := m₁.support ∪ m₂.support
      have hwS (m : JetVar s →₀ ℕ) (hS : m.support ⊆ S) :
          w m = ∑ u ∈ S, match u with | none => 0 | some (_, j) => j * m u := by
        dsimp only [w]; rw [Finsupp.sum]
        apply Finset.sum_subset hS; intro u _ hu
        have hm0 : m u = 0 := Finsupp.notMem_support_iff.mp hu
        cases u with | none => rfl | some ij => simp [hm0]
      rw [hwS m₁ Finset.subset_union_left, hwS m₂ Finset.subset_union_right]
      apply Finset.sum_congr rfl; intro u _
      cases u with
      | none => rfl
      | some ij =>
        rcases ij with ⟨i, j⟩
        cases j with
        | zero => simp
        | succ j' => rw [hpos i j']
    have hnone : m₁ none = m₂ none := by
      have h1 : m₁ none + (K - w m₁) = m₂ none + (K - w m₂) := by
        simpa [shiftMon] using DFunLike.congr_fun heq none
      rw [hw_eq] at h1; omega
    have hzero (i : Fin s) : m₁ (some (i, 0)) = m₂ (some (i, 0)) := by
      let S := insert (some (i, 0)) (m₁.support ∪ m₂.support)
      have hdegS (m : JetVar s →₀ ℕ) (hS : m.support ⊆ S) :
          mdeg m i = m (some (i, 0)) + ∑ u ∈ S.erase (some (i, 0)),
            match u with | none => 0 | some (i', _) => if i' = i then m u else 0 := by
        change (m.sum fun u e ↦ match u with | none => 0 | some (i', _) => if i' = i then e else 0) = _
        rw [Finsupp.sum]
        have h1 : (∑ u ∈ m.support, match u with | none => 0 | some (i', _) => if i' = i then m u else 0) =
            ∑ u ∈ S, match u with | none => 0 | some (i', _) => if i' = i then m u else 0 := by
          apply Finset.sum_subset hS; intro u _ hu
          have hm0 : m u = 0 := Finsupp.notMem_support_iff.mp hu
          cases u with | none => rfl | some ab => simp [hm0]
        rw [h1, ← Finset.add_sum_erase S _ (Finset.mem_insert_self _ _)]
        simp
      have hd_eq : mdeg m₁ i = mdeg m₂ i := by rw [hd₁, hd₂]
      rw [hdegS m₁ (Finset.subset_union_left.trans (Finset.subset_insert _ _)),
          hdegS m₂ (Finset.subset_union_right.trans (Finset.subset_insert _ _))] at hd_eq
      have hrest : (∑ u ∈ S.erase (some (i, 0)),
            match u with | none => 0 | some (i', _) => if i' = i then m₁ u else 0) =
          (∑ u ∈ S.erase (some (i, 0)),
            match u with | none => 0 | some (i', _) => if i' = i then m₂ u else 0) := by
        apply Finset.sum_congr rfl; intro u hu
        have hne0 := (Finset.mem_erase.mp hu).1
        cases u with
        | none => rfl
        | some ab =>
          rcases ab with ⟨i', j⟩
          cases j with
          | zero =>
            dsimp only
            split_ifs with hii
            · subst hii; exact (hne0 rfl).elim
            · rfl
          | succ j' => rw [hpos i' j']
      omega
    ext u
    cases u with
    | none => exact hnone
    | some ij =>
      rcases ij with ⟨i, j⟩
      cases j with
      | zero => exact hzero i
      | succ j' => exact hpos i j'
  let Qd₀ : MvPolynomial (JetVar s) ℂ :=
    ∑ m ∈ Q.support.filter (fun m ↦ mdeg m = d₀), MvPolynomial.monomial (shiftMon m) (Q.coeff m)
  have hQd₀_ne : Qd₀ ≠ 0 := by
    intro h0
    have hc := congrArg (fun p : MvPolynomial (JetVar s) ℂ ↦ p.coeff (shiftMon m₀)) h0
    rw [show (0 : MvPolynomial (JetVar s) ℂ).coeff (shiftMon m₀) = 0 from rfl] at hc
    simp only [Qd₀, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial] at hc
    have hm₀_f : m₀ ∈ Q.support.filter (fun m ↦ mdeg m = d₀) :=
      Finset.mem_filter.mpr ⟨hm₀, rfl⟩
    rw [Finset.sum_eq_single m₀] at hc
    · simp only [↓reduceIte] at hc
      exact MvPolynomial.mem_support_iff.mp hm₀ hc
    · intro m hm hne_m
      have hfm := Finset.mem_filter.mp hm
      have hns : shiftMon m ≠ shiftMon m₀ := fun h ↦ hne_m (hshift_inj hfm ⟨hm₀, rfl⟩ h)
      simp only [hns, ↓reduceIte]
    · intro h; exact (h hm₀_f).elim
  have hQd₀_no0 : ∀ i : Fin s, some (i, 0) ∉ Qd₀.vars := by
    intro i hi
    obtain ⟨m, hm, hm_nz⟩ := (MvPolynomial.mem_vars_iff_mem_support _).mp hi
    have hcoeff_ne : Qd₀.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
    simp only [Qd₀, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial] at hcoeff_ne
    obtain ⟨m', _, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff_ne
    split_ifs at hne' with heq
    · subst heq; simp [shiftMon] at hm_nz
    · exact hne' rfl
  have hQd₀_bind : MvPolynomial.bind₁ sub Qd₀ = 0 := by
    rw [← hAd₀, ← Finset.sum_filter]
    simp only [Qd₀, map_sum]
    apply Finset.sum_congr rfl; intro m _
    rw [MvPolynomial.bind₁_monomial]
    dsimp only [termRF]
    have hprod_eq : (shiftMon m).prod (fun u e ↦ sub u ^ e) =
        (MvPolynomial.X none) ^ (m none + (K - w m)) *
          m.prod (fun u e ↦ match u with | none => 1 | some (i, j) => (logDerivJetPoly c i j) ^ e) := by
      have h1 : (shiftMon m).prod (fun u e ↦ sub u ^ e) =
          ∏ u ∈ insert none m.support, sub u ^ (shiftMon m u) := by
        rw [Finsupp.prod]
        apply Finset.prod_subset
        · intro u hu
          have hnz := Finsupp.mem_support_iff.mp hu
          cases u with
          | none => exact Finset.mem_insert_self _ _
          | some ij =>
            rcases ij with ⟨i, j⟩
            cases j with
            | zero => simp [shiftMon] at hnz
            | succ j' =>
              exact Finset.mem_insert_of_mem (Finsupp.mem_support_iff.mpr (by simpa [shiftMon] using hnz))
        · intro u _ hu; simp [Finsupp.notMem_support_iff.mp hu]
      rw [h1]
      have hsplit : (∏ u ∈ insert none m.support, sub u ^ (shiftMon m u)) =
          sub none ^ (shiftMon m none) *
            ∏ u ∈ (insert none m.support).erase none, sub u ^ (shiftMon m u) :=
        (Finset.mul_prod_erase _ _ (Finset.mem_insert_self _ _)).symm
      rw [hsplit]
      congr 1
      rw [Finsupp.prod]
      have h2 : (∏ u ∈ (insert none m.support).erase none, sub u ^ (shiftMon m u)) =
          ∏ u ∈ m.support.erase none,
            match u with | none => 1 | some (i, j) => (logDerivJetPoly c i j) ^ (m u) := by
        rw [Finset.erase_insert_eq_erase]
        apply Finset.prod_congr rfl; intro u hu
        have hne0 := (Finset.mem_erase.mp hu).1
        cases u with
        | none => exact (hne0 rfl).elim
        | some ij =>
          rcases ij with ⟨i, j⟩
          cases j with
          | zero => simp [shiftMon, logDerivJetPoly]
          | succ j' => simp [sub, shiftMon]
      rw [h2]
      by_cases h0 : none ∈ m.support
      · rw [← Finset.mul_prod_erase _ _ h0]; dsimp only; rw [one_mul]
      · rw [Finset.erase_eq_of_notMem h0]
    change MvPolynomial.C (Q.coeff m) * (shiftMon m).prod (fun u e ↦ sub u ^ e) = _
    rw [hprod_eq]; ring
  exact hQd₀_ne (bind₁_logDerivJetPoly_injective c hc Qd₀ hQd₀_no0 hQd₀_bind)

/-- **100% Unconditional Single-Series Log-Derivative Differential Transcendence Transfer**:
if `F ∈ ℂ[[q]]` is differentially transcendental over `ℂ(q)` and `q · P' = c · F · P`
(`c ≠ 0, P ≠ 0`), then `P` is differentially transcendental over `ℂ(q)`. -/
theorem diffTrans_of_logDeriv {F P : PowerSeries ℂ} {c : ℂ}
    (hP : P ≠ 0) (hc : c ≠ 0)
    (hlog : PowerSeries.X * PowerSeries.derivative (R := ℂ) P = (PowerSeries.C c * F) * P)
    (hF : AlgebraicIndependent ℂ (seriesCoordinates F)) :
    AlgebraicIndependent ℂ (seriesCoordinates P) := by
  let e : ℕ ≃ Option (Fin 1 × ℕ) :=
    { toFun := fun | 0 => none | j + 1 => some (0, j)
      invFun := fun | none => 0 | some (_, j) => j + 1
      left_inv := fun | 0 => rfl | _ + 1 => rfl
      right_inv := fun | none => rfl | some (i, _) => by rw [Subsingleton.elim i 0] }
  have hF' : AlgebraicIndependent ℂ (jointSeriesCoordinates (fun _ : Fin 1 ↦ F)) :=
    (algebraicIndependent_equiv' e (by funext n; cases n <;> rfl)).mp hF
  have hP' := kolchin_logDeriv_joint_indep (fun _ : Fin 1 ↦ F) (fun _ : Fin 1 ↦ P)
    (fun _ : Fin 1 ↦ c) (fun _ ↦ hP) (fun _ ↦ hc) (fun _ ↦ hlog) hF'
  exact (algebraicIndependent_equiv' e (by funext n; cases n <;> rfl)).mpr hP'

end Kolchin

/-! ### 3. 100% Unconditional Prime Multiplicity, Active Rays, Extreme-Ray Geometry & Constant Vandermonde (`d ≥ 2`) -/

/-- Power-partition wave multiplicity `c_d(N) = ∑_{k^d ∣ N} 1/k` (`N ≥ 1`). -/
def powerPartMult (d N : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 N).filter (fun k ↦ k ^ d ∣ N), (k : ℝ)⁻¹

theorem powerPartMult_nonneg (d N : ℕ) : 0 ≤ powerPartMult d N :=
  Finset.sum_nonneg fun _ _ ↦ by positivity

theorem powerPartMult_ge_one {d N : ℕ} (hN : 1 ≤ N) : 1 ≤ powerPartMult d N := by
  have h1 : 1 ∈ (Finset.Icc 1 N).filter (fun k ↦ k ^ d ∣ N) := by
    simp [hN]
  calc (1 : ℝ) = ((1 : ℕ) : ℝ)⁻¹ := by simp
    _ ≤ powerPartMult d N := Finset.single_le_sum (f := fun k : ℕ ↦ (k : ℝ)⁻¹)
      (fun _ _ ↦ by positivity) h1

theorem powerPartMult_le_self (d N : ℕ) : powerPartMult d N ≤ (N : ℝ) := by
  calc powerPartMult d N
      ≤ ∑ _k ∈ (Finset.Icc 1 N).filter (fun k ↦ k ^ d ∣ N), (1 : ℝ) := by
        apply Finset.sum_le_sum; intro k hk
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
        exact inv_le_one_of_one_le₀ hk1
    _ ≤ ∑ _k ∈ Finset.Icc 1 N, (1 : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) (fun _ _ _ ↦ zero_le_one)
    _ = (N : ℝ) := by simp

/-- **100% Unconditional Exact Prime Multiplicity Theorem (`d ≥ 2`)**:
for EVERY prime `p` and EVERY `d ≥ 2`, `c_d(p) = 1` identically! -/
theorem powerPartMult_prime {d p : ℕ} (hd : 2 ≤ d) (hp : p.Prime) :
    powerPartMult d p = 1 := by
  have hfilt : (Finset.Icc 1 p).filter (fun k ↦ k ^ d ∣ p) = {1} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hdvd⟩
      exact Nat.isUnit_iff.mp (rfree_of_prime hd hp k hdvd)
    · rintro rfl
      exact ⟨⟨le_rfl, hp.one_lt.le⟩, by simp⟩
  rw [powerPartMult, hfilt, Finset.sum_singleton]
  simp

/-- Active Stokes ray angle `θ_{d, ℓ} = π (d - 1 - 2 ℓ) / (2 d)` for `0 ≤ ℓ < d`. -/
def ppAngle (d ℓ : ℕ) : ℝ :=
  Real.pi * ((d : ℝ) - 1 - 2 * (ℓ : ℝ)) / (2 * (d : ℝ))

/-- Active Stokes ray `A_{d, ℓ} = (2 π)^{1 + 1/d} exp(i θ_{d, ℓ})` for `d ≥ 2`. -/
def ppRay (d ℓ : ℕ) : ℂ :=
  (((2 * Real.pi) ^ (1 + 1 / (d : ℝ)) : ℝ) : ℂ) * Complex.exp (I * (ppAngle d ℓ : ℂ))

/-- The unique maximum-argument extreme ray `A_{d, 0}` (`arg = +π(d-1)/(2d)`). -/
def ppExtremeRay (d : ℕ) : ℂ := ppRay d 0

theorem ppRay_re_pos {d ℓ : ℕ} (hd : 2 ≤ d) (hℓ : ℓ < d) : 0 < (ppRay d ℓ).re := by
  have hR : 0 < (2 * Real.pi) ^ (1 + 1 / (d : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hre : (ppRay d ℓ).re = (2 * Real.pi) ^ (1 + 1 / (d : ℝ)) * Real.cos (ppAngle d ℓ) := by
    unfold ppRay
    rw [mul_comm I, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.exp_ofReal_mul_I_re]
  rw [hre]
  apply mul_pos hR
  apply Real.cos_pos_of_mem_Ioo
  unfold ppAngle
  have hℓ_le : (ℓ : ℝ) ≤ (d : ℝ) - 1 := by
    have : ℓ + 1 ≤ d := hℓ
    have hcast : (ℓ : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast this
    linarith
  have hℓ_nn : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg ℓ
  constructor
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]

theorem ppExtremeRay_ne_zero {d : ℕ} (hd : 2 ≤ d) : ppExtremeRay d ≠ 0 := by
  intro h
  have hpos := ppRay_re_pos (ℓ := 0) hd (by omega)
  rw [ppExtremeRay] at h
  rw [h] at hpos
  simp at hpos

/-- Extreme-ray test functional `z ↦ -Im(exp(-i θ_{d, 0}) z)`.
Vanishes on the extreme ray `ℝ_{≥ 0} A_{d, 0}` and is strictly positive on every
other active ray `A_{d, ℓ}` (`1 ≤ ℓ < d`)! -/
def ppRotIm (d : ℕ) (z : ℂ) : ℝ := -(Complex.exp (-I * (ppAngle d 0 : ℂ)) * z).im

@[simp] theorem ppRotIm_zero (d : ℕ) : ppRotIm d 0 = 0 := by simp [ppRotIm]

@[simp] theorem ppRotIm_add (d : ℕ) (x y : ℂ) : ppRotIm d (x + y) = ppRotIm d x + ppRotIm d y := by
  simp [ppRotIm, mul_add]; ring

theorem ppRotIm_smul_real (d : ℕ) (t : ℝ) (z : ℂ) :
    ppRotIm d ((t : ℂ) * z) = t * ppRotIm d z := by
  unfold ppRotIm
  rw [mul_left_comm, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  ring

theorem ppRotIm_ray {d ℓ : ℕ} (hd : 2 ≤ d) :
    ppRotIm d (ppRay d ℓ) =
      (2 * Real.pi) ^ (1 + 1 / (d : ℝ)) * Real.sin ((ℓ : ℝ) * Real.pi / (d : ℝ)) := by
  unfold ppRotIm ppRay
  rw [mul_left_comm, ← Complex.exp_add]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hdiff : ppAngle d ℓ - ppAngle d 0 = -((ℓ : ℝ) * Real.pi / (d : ℝ)) := by
    unfold ppAngle; field_simp [hd0]; ring
  have hexp : -I * (ppAngle d 0 : ℂ) + I * (ppAngle d ℓ : ℂ) =
      ((ppAngle d ℓ - ppAngle d 0 : ℝ) : ℂ) * I := by push_cast; ring
  rw [hexp, hdiff, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  ring

theorem ppRotIm_extreme {d : ℕ} (hd : 2 ≤ d) : ppRotIm d (ppExtremeRay d) = 0 := by
  simp [ppExtremeRay, ppRotIm_ray hd]

theorem ppRotIm_other_pos {d ℓ : ℕ} (hd : 2 ≤ d) (hℓ0 : 0 < ℓ) (hℓ : ℓ < d) :
    0 < ppRotIm d (ppRay d ℓ) := by
  rw [ppRotIm_ray hd]
  have hR : 0 < (2 * Real.pi) ^ (1 + 1 / (d : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hℓ_pos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
  have hℓ_lt : (ℓ : ℝ) < (d : ℝ) := by exact_mod_cast hℓ
  apply mul_pos hR
  apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
  rw [div_lt_iff₀ hd_pos]
  nlinarith [Real.pi_pos]

theorem ppRotIm_nonneg {d ℓ : ℕ} (hd : 2 ≤ d) (hℓ : ℓ < d) : 0 ≤ ppRotIm d (ppRay d ℓ) := by
  cases ℓ with
  | zero => rw [show ppRay d 0 = ppExtremeRay d from rfl, ppRotIm_extreme hd]
  | succ ℓ' => exact (ppRotIm_other_pos hd (Nat.succ_pos ℓ') hℓ).le

theorem ppExtremeRay_face_iff {d : ℕ} {a b : ℂ} (ha : 0 ≤ ppRotIm d a) (hb : 0 ≤ ppRotIm d b) :
    ppRotIm d (a + b) = 0 ↔ ppRotIm d a = 0 ∧ ppRotIm d b = 0 := by
  rw [ppRotIm_add]; constructor <;> intro h
  · constructor <;> linarith
  · linarith

/-- Zero-tilt extreme-ray frequency map `(Core d →₀ ℕ) →+ ℂ` sending `b ↦ b^{1/d} A_{d, 0}`
for EVERY `d ≥ 2`! -/
def ppKeyRate (d : ℕ) : (Core d →₀ ℕ) →+ ℂ where
  toFun k := ((readRootKey d k : ℝ) : ℂ) * ppExtremeRay d
  map_zero' := by simp
  map_add' k₁ k₂ := by simp [map_add, add_mul]

theorem ppKeyRate_injective (d : ℕ) (hd : 2 ≤ d) : Function.Injective (ppKeyRate d) := by
  intro k₁ k₂ h
  exact readRootKey_injective d hd
    (Complex.ofReal_injective (mul_right_cancel₀ (ppExtremeRay_ne_zero hd) h))

theorem ppRotIm_keyRate {d : ℕ} (hd : 2 ≤ d) (k : Core d →₀ ℕ) :
    ppRotIm d (ppKeyRate d k) = 0 := by
  change ppRotIm d (((readRootKey d k : ℝ) : ℂ) * ppExtremeRay d) = 0
  rw [ppRotIm_smul_real, ppRotIm_extreme hd, mul_zero]

/-- Mode key of `N ∈ ℕ+` in `Core d →₀ ℕ`: if `N = k^d * b`, then `N^{1/d} = k * b^{1/d}`. -/
def ppModeKey (d : ℕ) (hd : 2 ≤ d) (N : ℕ+) : Core d →₀ ℕ :=
  Finsupp.single (rFreeCore d (by omega) N) (rFreeRoot d (by omega) N)

theorem ppKeyRate_modeKey (d : ℕ) (hd : 2 ≤ d) (N : ℕ+) :
    ppKeyRate d (ppModeKey d hd N) =
      (((N.val : ℝ) ^ (1 / (d : ℝ)) : ℝ) : ℂ) * ppExtremeRay d := by
  change ((readRootKey d (ppModeKey d hd N) : ℝ) : ℂ) * ppExtremeRay d = _
  congr 2
  rw [ppModeKey, readRootKey_single]
  have hfac := rFreeRoot_pow_mul_core d (by omega) N
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hm0 : 0 ≤ (rFreeRoot d (by omega) N : ℝ) := Nat.cast_nonneg _
  have hc0 : 0 ≤ ((rFreeCore d (by omega) N).val : ℝ) := Nat.cast_nonneg _
  rw [← hfac, Nat.cast_mul, Nat.cast_pow, Real.mul_rpow (pow_nonneg hm0 _) hc0,
      ← Real.rpow_natCast, ← Real.rpow_mul hm0, mul_one_div_cancel hd0, Real.rpow_one]

theorem ppModeKey_eq_single_one (d : ℕ) (hd : 2 ≤ d) (N : ℕ+) (b : Core d) :
    ppModeKey d hd N = Finsupp.single b 1 ↔ N.val = b.val := by
  constructor
  · intro hk
    have hval := DFunLike.congr_fun hk (rFreeCore d (by omega) N)
    simp only [ppModeKey, Finsupp.single_eq_same, Finsupp.single_apply] at hval
    have hm_pos := rFreeRoot_pos d (by omega) N
    by_cases hbc : b = rFreeCore d (by omega) N
    · simp only [hbc, ↓reduceIte] at hval
      have hfac := rFreeRoot_pow_mul_core d (by omega) N
      rw [hval, one_pow, one_mul, ← hbc] at hfac
      exact hfac.symm
    · simp only [hbc, ↓reduceIte] at hval
      exact absurd hval hm_pos.ne'
  · intro hNb
    have huniq := rfree_factor_unique (r := d) (by omega)
      (rFreeRoot_pos d (by omega) N) one_pos
      (by simpa [hNb] using rFreeRoot_pow_mul_core d (by omega) N)
    simp [ppModeKey, huniq.1, huniq.2]

/-- **The Exact `X`-Independent Constant `J × J` Prime Vandermonde Matrix** (`d ≥ 2`):
`M_{i, j} = -(A_{d, 0} p_i^{1/d}) · (-A_{d, 0} p_i^{1/d})^j = z_i^{j + 1}`! -/
def ppPrimeVandermonde (d : ℕ) {J : ℕ} (p : Fin J → ℕ) : Matrix (Fin J) (Fin J) ℂ :=
  Matrix.of fun i j ↦
    -(ppExtremeRay d * (((p i : ℝ) ^ (1 / (d : ℝ)) : ℝ) : ℂ)) *
      (-(ppExtremeRay d * (((p i : ℝ) ^ (1 / (d : ℝ)) : ℝ) : ℂ))) ^ j.val

/-- **100% Unconditional Constant Prime Vandermonde Non-Vanishing Theorem (`d ≥ 2`)**:
for EVERY `d ≥ 2`, EVERY `J : ℕ`, and ANY injective family of positive integers
(in particular ANY `J` distinct primes — NO `p_i > d` restriction!),
`det (ppPrimeVandermonde d p) ≠ 0`! -/
theorem ppPrimeVandermonde_det_ne_zero {d : ℕ} (hd : 2 ≤ d) {J : ℕ}
    (p : Fin J → ℕ) (hp_pos : ∀ i, 0 < p i) (hp_inj : Function.Injective p) :
    (ppPrimeVandermonde d p).det ≠ 0 := by
  let z (i : Fin J) : ℂ := -(ppExtremeRay d * (((p i : ℝ) ^ (1 / (d : ℝ)) : ℝ) : ℂ))
  have hM : ppPrimeVandermonde d p = Matrix.diagonal z * Matrix.vandermonde z := by
    ext i j; simp [ppPrimeVandermonde, z, Matrix.diagonal_mul, Matrix.vandermonde_apply]
  rw [hM, Matrix.det_mul, Matrix.det_diagonal]
  have hd_pos : (0 : ℝ) < 1 / (d : ℝ) := by
    have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    positivity
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr; intro i _
    have hpi : (0 : ℝ) < (p i : ℝ) := by exact_mod_cast hp_pos i
    exact neg_ne_zero.mpr (mul_ne_zero (ppExtremeRay_ne_zero hd)
      (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hpi _).ne'))
  · rw [Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    have h1 := neg_inj.mp hij
    have h2 := Complex.ofReal_injective (mul_left_cancel₀ (ppExtremeRay_ne_zero hd) h1)
    have h3 := (Real.rpow_left_inj (Nat.cast_nonneg _) (Nat.cast_nonneg _) hd_pos.ne').mp h2
    exact hp_inj (Nat.cast_injective h3)

/-! ### 4. Unit-Disk Convergence of `logDerivPowerPartDilated d a`, `PowerPartStokesProfile d hd`, and Zero-Tilt Constant-Vandermonde Master Theorems (`d ≥ 2`) -/

private lemma shifted_geom_pp (k : ℕ) {r : ℝ} (hr : 0 < r) (h1 : r < 1) :
    Summable (fun n : ℕ ↦ (n + 1 : ℝ) ^ k * r ^ n) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one k
    (show ‖r‖ < 1 by simpa [abs_of_pos hr] using h1)
  have h := (hs.comp_injective (show Function.Injective (fun n : ℕ ↦ n + 1) by
    intro i k' hh; exact Nat.add_right_cancel hh)).mul_right r⁻¹
  simpa [Function.comp_def, pow_succ, mul_assoc, hr.ne'] using h

private lemma powerDivSum_le_sq (d N : ℕ) : powerDivSum d N ≤ N ^ 2 := by
  calc powerDivSum d N
      ≤ ∑ _n ∈ (Finset.Icc 1 N).filter (fun n ↦ n ^ d ∣ N), N := by
        apply Finset.sum_le_sum; intro n hn
        have hNpos : 0 < N := by
          have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
          have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
          omega
        exact Nat.le_of_dvd hNpos (Finset.mem_filter.mp hn).2
    _ ≤ ∑ _n ∈ Finset.Icc 1 N, N := Finset.sum_le_sum_of_subset (Finset.filter_subset ..)
    _ = N ^ 2 := by simp [sq]

private lemma ppLogDeriv_coeff_bound (d a j n : ℕ) :
    ‖PowerSeries.coeff n (formalJet (logDerivPowerPartDilated d a) j)‖ ≤
      (j.factorial * (j + 1 : ℝ) ^ 2) * (n + 1 : ℝ) ^ (j + 2) := by
  rw [formalJet, PowerSeries.coeff_iterate_derivative, logDerivPowerPartDilated, PowerSeries.coeff_mk]
  have h1 : ‖if n + j = 0 then (0 : ℂ) else
      if a ∣ n + j then (powerDivSum d ((n + j) / a) : ℂ) else 0‖ ≤ ((n + j : ℕ) : ℝ) ^ 2 := by
    split_ifs with h0 hdvd
    · simp only [norm_zero]; positivity
    · rw [Complex.norm_natCast]
      have hle : powerDivSum d ((n + j) / a) ≤ (n + j) ^ 2 :=
        (powerDivSum_le_sq d _).trans (Nat.pow_le_pow_left (Nat.div_le_self _ _) 2)
      exact_mod_cast hle
    · simp only [norm_zero]; positivity
  have h2 : (((n + j : ℕ) : ℝ) ^ 2) ≤ (j + 1 : ℝ) ^ 2 * (n + 1 : ℝ) ^ 2 := by
    have hsum : ((n + j : ℕ) : ℝ) ≤ (j + 1 : ℝ) * (n + 1 : ℝ) := by
      push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) j]
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hsum 2
  have h3 : (((n + 1).ascFactorial j : ℕ) : ℝ) ≤ j.factorial * (n + 1 : ℝ) ^ j := by
    exact_mod_cast Nat.ascFactorial_le_factorial_mul_pow (n + 1) j
  rw [norm_mul, Complex.norm_natCast]
  calc _ ≤ (j.factorial * (n + 1 : ℝ) ^ j) * ((j + 1 : ℝ) ^ 2 * (n + 1 : ℝ) ^ 2) :=
        mul_le_mul h3 (h1.trans h2) (norm_nonneg _) (by positivity)
    _ = (j.factorial * (j + 1 : ℝ) ^ 2) * (n + 1 : ℝ) ^ (j + 2) := by
        rw [pow_add]; ring

private lemma ppLogDeriv_bound_on (d a j : ℕ) {q : ℂ} {r : ℝ} (h : ‖q‖ ≤ r) (n : ℕ) :
    ‖psTerm (formalJet (logDerivPowerPartDilated d a) j) q n‖ ≤
      (j.factorial * (j + 1 : ℝ) ^ 2) * ((n + 1 : ℝ) ^ (j + 2) * r ^ n) := by
  rw [psTerm, norm_mul, norm_pow, ← mul_assoc]
  exact mul_le_mul (ppLogDeriv_coeff_bound d a j n)
    (pow_le_pow_left₀ (norm_nonneg _) h _) (by positivity) (by positivity)

theorem ppLogDeriv_jet_abs (d a j : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    PSAbsAt (formalJet (logDerivPowerPartDilated d a) j) q := by
  obtain ⟨r, hr, h1⟩ := exists_between hq
  exact ((shifted_geom_pp (j + 2) ((norm_nonneg _).trans_lt hr) h1).mul_left _).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (ppLogDeriv_bound_on d a j hr.le)

theorem ppLogDeriv_jet_deriv (d a j : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasDerivAt (psValue (formalJet (logDerivPowerPartDilated d a) j))
      (psValue (formalJet (logDerivPowerPartDilated d a) (j + 1)) q) q := by
  obtain ⟨r, hr, h1⟩ := exists_between hq
  have rp := (norm_nonneg _).trans_lt hr
  let f (n : ℕ) (z : ℂ) := psTerm (formalJet (logDerivPowerPartDilated d a) j) z (n + 1)
  let g (n : ℕ) (z : ℂ) := psTerm (formalJet (logDerivPowerPartDilated d a) (j + 1)) z n
  have hd (n : ℕ) (z : ℂ) : HasDerivAt (f n) (g n z) z := by
    have he : PowerSeries.coeff n (formalJet (logDerivPowerPartDilated d a) (j + 1)) =
        PowerSeries.coeff (n + 1) (formalJet (logDerivPowerPartDilated d a) j) * (n + 1) := by
      rw [formalJet, Function.iterate_succ_apply', PowerSeries.coeff_derivative]; rfl
    simpa [f, g, psTerm, he, mul_assoc] using
      ((hasDerivAt_pow (n + 1) z).const_mul (PowerSeries.coeff (n + 1) (formalJet (logDerivPowerPartDilated d a) j)))
  have hs := hasDerivAt_tsum_of_isPreconnected
    ((shifted_geom_pp (j + 3) rp h1).mul_left (↑(j + 1).factorial * (↑(j + 1) + 1 : ℝ) ^ 2))
    (t := Metric.ball (0 : ℂ) r) Metric.isOpen_ball (convex_ball (0 : ℂ) _).isPreconnected
    (fun n z _ ↦ hd n z) (fun n z hz ↦ ppLogDeriv_bound_on d a _ (by simpa using (Metric.mem_ball.mp hz).le) n)
    (y₀ := q) (by simpa using hr)
    ((ppLogDeriv_jet_abs d a j hq).of_norm.comp_injective
      (show Function.Injective (fun n : ℕ ↦ n + 1) by intro i k hh; exact Nat.add_right_cancel hh))
    (by simpa using hr)
  have near : psValue (formalJet (logDerivPowerPartDilated d a) j) =ᶠ[𝓝 q]
      fun z ↦ PowerSeries.coeff 0 (formalJet (logDerivPowerPartDilated d a) j) + ∑' n, f n z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show q ∈ Metric.ball (0 : ℂ) 1 by simpa using hq)] with z hz
    have h := (ppLogDeriv_jet_abs d a j (by simpa using hz : ‖z‖ < 1)).of_norm.sum_add_tsum_nat_add 1
    simpa [psValue, f, psTerm] using h.symm
  exact (hs.const_add _).congr_of_eventuallyEq near

theorem ppLogDeriv_jet_analytic (d a j : ℕ) :
    AnalyticOnNhd ℂ (psValue (formalJet (logDerivPowerPartDilated d a) j)) (Metric.ball 0 1) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro q hq
  exact (ppLogDeriv_jet_deriv d a j (by simpa using hq)).differentiableAt.differentiableWithinAt

theorem ppLogDeriv_dilated_value_eq {d a : ℕ} (ha : 1 ≤ a) {q : ℂ} (_hq : ‖q‖ < 1) :
    psValue (logDerivPowerPartDilated d a) q = psValue (logDerivPowerPart d) (q ^ a) := by
  let f (n : ℕ) : ℕ := a * n
  have hinj : Function.Injective f := fun x y h ↦ Nat.eq_of_mul_eq_mul_left ha h
  have hzero : ∀ k ∉ Set.range f, psTerm (logDerivPowerPartDilated d a) q k = 0 := by
    intro k hk
    by_cases hk0 : k = 0
    · simp [psTerm, logDerivPowerPartDilated, hk0]
    · have hnd : ¬ a ∣ k := fun ⟨n, hn⟩ ↦ hk ⟨n, hn.symm⟩
      simp [psTerm, logDerivPowerPartDilated, hk0, hnd]
  have hsupp : Function.support (psTerm (logDerivPowerPartDilated d a) q) ⊆ Set.range f := by
    intro k hk
    by_contra hnot
    exact hk (hzero k hnot)
  rw [psValue, ← hinj.tsum_eq hsupp, psValue]
  apply tsum_congr; intro n
  cases n with
  | zero => simp [psTerm, logDerivPowerPartDilated, logDerivPowerPart, f]
  | succ n' =>
    have han0 : a * (n' + 1) ≠ 0 := mul_ne_zero (by omega) (Nat.succ_ne_zero n')
    have hdiv : a * (n' + 1) / a = n' + 1 := Nat.mul_div_cancel_left (n' + 1) ha
    simp only [psTerm, logDerivPowerPartDilated, logDerivPowerPart, PowerSeries.coeff_mk, f,
      han0, Nat.succ_ne_zero, ↓reduceIte, dvd_mul_right, hdiv, one_dvd, Nat.div_one, pow_mul]

/-- The rescaled logarithmic derivative `F̃_d(X) = d X^{-(d+1)} F_d(exp(-X^{-d}))` on `X > 0`. -/
def rescaledLogDerivPP (d : ℕ) (X : ℝ) : ℂ :=
  ((d : ℂ) * ((X : ℂ)⁻¹) ^ (d + 1)) * psValue (logDerivPowerPart d) (qRayD (d + 1) X)

/-- Rate `A_{d, ℓ} N^{1/d}` of the `(ℓ, N)` pure-exponential wave for `P_d(q)`. -/
def ppWaveRate (d : ℕ) (ℓ : Fin d) (N : ℕ+) : ℂ :=
  (((N.val : ℝ) ^ (1 / (d : ℝ)) : ℝ) : ℂ) * ppRay d ℓ.val

theorem ppWaveRate_re_pos {d : ℕ} (hd : 2 ≤ d) (ℓ : Fin d) (N : ℕ+) :
    0 < (ppWaveRate d ℓ N).re := by
  simp only [ppWaveRate, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hN : (0 : ℝ) < (N.val : ℝ) := by exact_mod_cast N.property
  exact mul_pos (Real.rpow_pos_of_pos hN _) (ppRay_re_pos hd ℓ.isLt)

private lemma summable_pow_mul_exp_neg_rpow {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : 0 < c) (K : ℕ) :
    Summable (fun N : ℕ+ ↦ (N.val : ℝ) ^ K * Real.exp (-c * (N.val : ℝ) ^ (1 / (d : ℝ)))) := by
  let M : ℕ := d * (K + 2)
  have hbound (N : ℕ+) :
      (N.val : ℝ) ^ K * Real.exp (-c * (N.val : ℝ) ^ (1 / (d : ℝ))) ≤
        ((M.factorial : ℝ) / c ^ M) * ((N.val : ℝ) ^ 2)⁻¹ := by
    have hN : (0 : ℝ) < (N.val : ℝ) := by exact_mod_cast N.property
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    have hu : 0 ≤ c * (N.val : ℝ) ^ (1 / (d : ℝ)) := by positivity
    have hexp := Real.pow_div_factorial_le_exp _ hu M
    have hpow : (c * (N.val : ℝ) ^ (1 / (d : ℝ))) ^ M = c ^ M * (N.val : ℝ) ^ (K + 2) := by
      rw [mul_pow]; congr 1
      change ((N.val : ℝ) ^ (1 / (d : ℝ))) ^ (d * (K + 2)) = _
      rw [pow_mul, ← Real.rpow_natCast ((N.val : ℝ) ^ _), ← Real.rpow_mul hN.le,
          one_div, inv_mul_cancel₀ hd0, Real.rpow_one]
    rw [hpow] at hexp
    have hinv : Real.exp (-c * (N.val : ℝ) ^ (1 / (d : ℝ))) ≤
        (M.factorial : ℝ) / (c ^ M * (N.val : ℝ) ^ (K + 2)) := by
      rw [neg_mul, Real.exp_neg]
      calc _ ≤ (c ^ M * (N.val : ℝ) ^ (K + 2) / (M.factorial : ℝ))⁻¹ :=
            inv_anti₀ (by positivity) hexp
        _ = _ := inv_div _ _
    calc (N.val : ℝ) ^ K * Real.exp (-c * (N.val : ℝ) ^ (1 / (d : ℝ)))
        ≤ (N.val : ℝ) ^ K * ((M.factorial : ℝ) / (c ^ M * (N.val : ℝ) ^ (K + 2))) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = ((M.factorial : ℝ) / c ^ M) * ((N.val : ℝ) ^ 2)⁻¹ := by
          rw [pow_add]; field_simp [hN.ne', hc.ne']
  have h2 : Summable (fun n : ℕ ↦ ((n : ℝ) ^ 2)⁻¹) := by simp
  exact Summable.of_nonneg_of_le (fun _ ↦ by positivity) hbound ((h2.subtype (fun n ↦ 0 < n)).mul_left _)

/-- Exact pure-exponential `j`-th `X`-derivative wave expansion `H̃_d^{(j)}(X)` (`d ≥ 2`),
with **constant** amplitudes (`loss = 0`, ZERO `RayDensity`!). -/
def ppWaveJet (d : ℕ) (hd : 2 ≤ d) (j : ℕ) : WaveExpansion (Fin d × ℕ+) where
  rate := fun ℓN ↦ ppWaveRate d ℓN.1 ℓN.2
  amplitude := fun ℓN _ ↦
    -((powerPartMult d ℓN.2.val : ℝ) : ℂ) * ppWaveRate d ℓN.1 ℓN.2 *
      (-ppWaveRate d ℓN.1 ℓN.2) ^ j
  budget := fun ℓN ↦
    ‖-((powerPartMult d ℓN.2.val : ℝ) : ℂ) * ppWaveRate d ℓN.1 ℓN.2 *
      (-ppWaveRate d ℓN.1 ℓN.2) ^ j‖ * Real.exp (-(ppWaveRate d ℓN.1 ℓN.2).re)
  loss := 0
  re_nonneg := fun ℓN ↦ (ppWaveRate_re_pos hd ℓN.1 ℓN.2).le
  budget_nonneg := fun _ ↦ by positivity
  summable_budget := by
    rw [← (Equiv.sigmaEquivProd (Fin d) ℕ+).summable_iff]
    refine (summable_sigma_of_nonneg (fun _ ↦ mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))).mpr
      ⟨fun ℓ ↦ ?_, hasSum_fintype _ |>.summable⟩
    have hc : 0 < (ppRay d ℓ.val).re := ppRay_re_pos hd ℓ.isLt
    let C : ℝ := ‖ppRay d ℓ.val‖ ^ (j + 1)
    have hdom := (summable_pow_mul_exp_neg_rpow hd hc (j + 2)).mul_left C
    refine Summable.of_nonneg_of_le (fun _ ↦ mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))
      (fun N ↦ ?_) hdom
    have hN1 : (1 : ℝ) ≤ (N.val : ℝ) := by exact_mod_cast N.property
    have hre : (ppWaveRate d ℓ N).re = (ppRay d ℓ.val).re * (N.val : ℝ) ^ (1 / (d : ℝ)) := by
      simp [ppWaveRate, Complex.mul_re, mul_comm]
    have hrpow_le : (N.val : ℝ) ^ (1 / (d : ℝ)) ≤ (N.val : ℝ) := by
      have h1 : 1 / (d : ℝ) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast (show 0 < d by omega))]; exact_mod_cast (show 1 ≤ d by omega)
      simpa using Real.rpow_le_rpow_of_exponent_le hN1 h1
    have hnorm_rate : ‖ppWaveRate d ℓ N‖ ≤ ‖ppRay d ℓ.val‖ * (N.val : ℝ) := by
      rw [ppWaveRate, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (by positivity) _), mul_comm]
      exact mul_le_mul_of_nonneg_left hrpow_le (norm_nonneg _)
    have hmult : ‖((powerPartMult d N.val : ℝ) : ℂ)‖ ≤ (N.val : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (powerPartMult_nonneg d N.val)]
      exact powerPartMult_le_self d N.val
    change ‖-((powerPartMult d N.val : ℝ) : ℂ) * ppWaveRate d ℓ N * (-ppWaveRate d ℓ N) ^ j‖ *
      Real.exp (-(ppWaveRate d ℓ N).re) ≤ _
    rw [norm_mul, norm_mul, norm_neg, norm_pow, norm_neg, hre, ← neg_mul]
    have hpow_tot : ‖ppWaveRate d ℓ N‖ * ‖ppWaveRate d ℓ N‖ ^ j ≤
        ‖ppRay d ℓ.val‖ ^ (j + 1) * (N.val : ℝ) ^ (j + 1) := by
      rw [← pow_succ', ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm_rate (j + 1)
    calc ‖((powerPartMult d N.val : ℝ) : ℂ)‖ * ‖ppWaveRate d ℓ N‖ * ‖ppWaveRate d ℓ N‖ ^ j *
          Real.exp (-(ppRay d ℓ.val).re * (N.val : ℝ) ^ (1 / (d : ℝ)))
        = ‖((powerPartMult d N.val : ℝ) : ℂ)‖ * (‖ppWaveRate d ℓ N‖ * ‖ppWaveRate d ℓ N‖ ^ j) *
          Real.exp (-(ppRay d ℓ.val).re * (N.val : ℝ) ^ (1 / (d : ℝ))) := by ring
      _ ≤ (N.val : ℝ) * (‖ppRay d ℓ.val‖ ^ (j + 1) * (N.val : ℝ) ^ (j + 1)) *
          Real.exp (-(ppRay d ℓ.val).re * (N.val : ℝ) ^ (1 / (d : ℝ))) := by gcongr
      _ = C * ((N.val : ℝ) ^ (j + 2) * Real.exp (-(ppRay d ℓ.val).re * (N.val : ℝ) ^ (1 / (d : ℝ)))) := by
          dsimp [C]; rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]; ring
  bound := by
    filter_upwards with x ℓN
    simp only [pow_zero, mul_one]
    rw [mul_assoc (‖_‖), ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

theorem ppWaveJet_derivatives {d : ℕ} (hd : 2 ≤ d) (j : ℕ) :
    iteratedDeriv j (ppWaveJet d hd 0).value =ᶠ[atTop] (ppWaveJet d hd j).value := by
  apply WaveExpansion.iteratedDeriv_value (ppWaveJet d hd)
  intro l
  filter_upwards with x ℓN
  simp only [WaveExpansion.term, ppWaveJet]
  have h1 : HasDerivAt (fun y : ℝ ↦ -ppWaveRate d ℓN.1 ℓN.2 * (y : ℂ))
      (-ppWaveRate d ℓN.1 ℓN.2) x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-ppWaveRate d ℓN.1 ℓN.2)
  have h2 := h1.cexp.mul_const
    (-((powerPartMult d ℓN.2.val : ℝ) : ℂ) * ppWaveRate d ℓN.1 ℓN.2 * (-ppWaveRate d ℓN.1 ℓN.2) ^ l)
  convert h2 using 1
  rw [pow_succ]; ring

/-- **Minimal Analytic Input Profile for All-$d$ Power Partitions (`d ≥ 2`)**:
Just ONE polynomial `polarPoly ∈ ℂ[X⁻¹]` and the pure-exponential wave decomposition
`F̃_d(X) = polarPoly(X⁻¹) + H̃_d(X)` on the untilted positive real ray `X > 0`!
(Discharged 100% unconditionally below at `d = 2` via `powerPartStokesProfileTwo`!) -/
structure PowerPartStokesProfile (d : ℕ) (hd : 2 ≤ d) where
  polarPoly : Polynomial ℂ
  decomp : ∀ᶠ X : ℝ in atTop,
    rescaledLogDerivPP d X =
      polarPoly.eval ((X : ℂ)⁻¹) + (ppWaveJet d hd 0).value X

/-- **Pure Constant-Amplitude Half-Space Expansion (`ConstTracked d`)**:
NO `RayDensity`, NO `FiniteParities`, NO `RayGerm` — amplitudes are literal constants in `ℂ`,
and extreme-ray projection lands directly in `MvPowerSeries (Core d) ℂ`! -/
private structure ConstTracked (d : ℕ) where
  Index : Type
  exp : WaveExpansion Index
  is_const : ∀ i, ∃ c : ℂ, ∀ x : ℝ, exp.amplitude i x = c
  finite_window : ∀ R : ℝ, {i : Index | (exp.rate i).re ≤ R}.Finite
  halfSpace : ∀ i : Index, 0 ≤ ppRotIm d (exp.rate i)
  extreme_range : ∀ i : Index, ppRotIm d (exp.rate i) = 0 →
    ∃ k : Core d →₀ ℕ, exp.rate i = ppKeyRate d k

namespace ConstTracked

private def constAmp {d : ℕ} (e : ConstTracked d) (i : e.Index) : ℂ := e.exp.amplitude i 0

private lemma amplitude_eq_constAmp {d : ℕ} (e : ConstTracked d) (i : e.Index) (x : ℝ) :
    e.exp.amplitude i x = e.constAmp i := by
  obtain ⟨c, hc⟩ := e.is_const i
  rw [hc x, constAmp, hc 0]

private def ofConst (d : ℕ) (c : ℂ) : ConstTracked d where
  Index := Unit
  exp :=
    { rate := fun _ ↦ 0
      amplitude := fun _ _ ↦ c
      budget := fun _ ↦ ‖c‖
      loss := 0
      re_nonneg := fun _ ↦ by simp
      budget_nonneg := fun _ ↦ norm_nonneg _
      summable_budget := hasSum_fintype _ |>.summable
      bound := Eventually.of_forall fun _ _ ↦ by simp }
  is_const := fun _ ↦ ⟨c, fun _ ↦ rfl⟩
  finite_window := fun _ ↦ Set.toFinite _
  halfSpace := fun _ ↦ by simp
  extreme_range := fun _ _ ↦ ⟨0, by simp⟩

private def add {d : ℕ} (a b : ConstTracked d) : ConstTracked d where
  Index := a.Index ⊕ b.Index
  exp := a.exp.add b.exp
  is_const := by rintro (i | j); exacts [a.is_const i, b.is_const j]
  finite_window R := by
    refine (((a.finite_window R).image Sum.inl).union ((b.finite_window R).image Sum.inr)).subset ?_
    rintro (i | j) h
    · exact Or.inl ⟨i, h, rfl⟩
    · exact Or.inr ⟨j, h, rfl⟩
  halfSpace := by rintro (i | j); exacts [a.halfSpace i, b.halfSpace j]
  extreme_range := by rintro (i | j) h; exacts [a.extreme_range i h, b.extreme_range j h]

private def mul {d : ℕ} (a b : ConstTracked d) : ConstTracked d where
  Index := a.Index × b.Index
  exp := a.exp.mul b.exp
  is_const := fun ⟨i, j⟩ ↦ by
    obtain ⟨c₁, hc₁⟩ := a.is_const i
    obtain ⟨c₂, hc₂⟩ := b.is_const j
    exact ⟨c₁ * c₂, fun x ↦ by change a.exp.amplitude i x * b.exp.amplitude j x = _; rw [hc₁, hc₂]⟩
  finite_window R := by
    refine ((a.finite_window R).prod (b.finite_window R)).subset ?_
    rintro ⟨i, j⟩ h
    change (a.exp.rate i).re + (b.exp.rate j).re ≤ R at h
    exact ⟨(le_add_of_nonneg_right (b.exp.re_nonneg j)).trans h,
      (le_add_of_nonneg_left (a.exp.re_nonneg i)).trans h⟩
  halfSpace := fun ⟨i, j⟩ ↦ by
    change 0 ≤ ppRotIm d (a.exp.rate i + b.exp.rate j)
    rw [ppRotIm_add]; exact add_nonneg (a.halfSpace i) (b.halfSpace j)
  extreme_range := fun ⟨i, j⟩ h0 ↦ by
    change ppRotIm d (a.exp.rate i + b.exp.rate j) = 0 at h0
    obtain ⟨h1, h2⟩ := (ppExtremeRay_face_iff (a.halfSpace i) (b.halfSpace j)).mp h0
    obtain ⟨k₁, hk₁⟩ := a.extreme_range i h1
    obtain ⟨k₂, hk₂⟩ := b.extreme_range j h2
    exact ⟨k₁ + k₂, by change a.exp.rate i + b.exp.rate j = _; rw [hk₁, hk₂, map_add]⟩

private abbrev Fiber {d : ℕ} (e : ConstTracked d) (k : Core d →₀ ℕ) :=
  {i : e.Index // e.exp.rate i = ppKeyRate d k}

private noncomputable instance fiberFintype {d : ℕ} (e : ConstTracked d) (k : Core d →₀ ℕ) :
    Fintype (Fiber e k) := by
  apply Set.Finite.fintype (s := {i : e.Index | e.exp.rate i = ppKeyRate d k})
  apply (e.finite_window (ppKeyRate d k).re).subset
  intro i hi; change (e.exp.rate i).re ≤ _; rw [show e.exp.rate i = ppKeyRate d k from hi]

/-- Extreme-ray marked series landing directly in `MvPowerSeries (Core d) ℂ`! -/
private def marked {d : ℕ} (e : ConstTracked d) : MvPowerSeries (Core d) ℂ :=
  fun k ↦ ∑ i : Fiber e k, e.constAmp i.val

private theorem separate_zero {d : ℕ} (e : ConstTracked d)
    (hzero : ∀ᶠ x : ℝ in atTop, e.exp.value x = 0) : e.marked = 0 := by
  classical
  let padded : Set ℝ := range (fun i ↦ (e.exp.rate i).re) ∪ range (Nat.cast : ℕ → ℝ)
  have padded_fin (R : ℝ) : (padded ∩ Iic R).Finite := by
    obtain ⟨N, hN⟩ := exists_nat_gt R
    refine (((e.finite_window R).image (fun i ↦ (e.exp.rate i).re)).union
      ((Set.finite_le_nat N).image (Nat.cast : ℕ → ℝ))).subset ?_
    rintro x ⟨(⟨i, rfl⟩ | ⟨n, rfl⟩), hx⟩
    · exact Or.inl ⟨i, hx, rfl⟩
    · exact Or.inr ⟨n, by exact_mod_cast (show (n : ℝ) ≤ N from hx.trans hN.le), rfl⟩
  let rank (x : padded) := (padded ∩ Iic (x : ℝ)).ncard
  have hinc : StrictMono rank := by
    intro x y h
    apply Set.ncard_lt_ncard _ (padded_fin _)
    exact Set.ssubset_iff_subset_ne.mpr ⟨inter_subset_inter_right _ (Iic_subset_Iic.mpr h.le),
      fun eqn ↦ (not_le.mpr h)
        ((eqn ▸ (show (y : ℝ) ∈ padded ∩ Iic (y : ℝ) from ⟨y.property, le_rfl⟩) :
          (y : ℝ) ∈ padded ∩ Iic (x : ℝ))).2⟩
  let iso : padded ≃o range rank := hinc.orderIso rank
  have : Infinite padded := Infinite.of_injective
    (fun n : ℕ ↦ (⟨n, Or.inr ⟨n, rfl⟩⟩ : padded))
    (fun _ _ h ↦ Nat.cast_injective (congrArg Subtype.val h))
  let _ : Infinite (range rank) := Infinite.of_injective _ iso.injective
  let enum : ℕ ≃o padded := (Nat.Subtype.orderIsoOfNat _).trans iso.symm
  let w (n : ℕ) : ℝ := enum n
  have hw : StrictMono w := fun _ _ h ↦ enum.strictMono h
  let clusterIdx (i : e.Index) : ℕ := enum.symm ⟨(e.exp.rate i).re, Or.inl ⟨i, rfl⟩⟩
  have hw_idx (i : e.Index) : w (clusterIdx i) = (e.exp.rate i).re := by simp [w, clusterIdx]
  let Freq (n : ℕ) := {y : ℝ // ∃ i : e.Index, (e.exp.rate i).re = w n ∧ -(e.exp.rate i).im = y}
  have (n : ℕ) : Fintype (Freq n) := by
    apply Set.Finite.fintype (s := {y : ℝ | ∃ i : e.Index, (e.exp.rate i).re = w n ∧ -(e.exp.rate i).im = y})
    refine ((e.finite_window (w n)).image (fun i ↦ -(e.exp.rate i).im)).subset ?_
    rintro y ⟨i, hi, rfl⟩; exact ⟨i, hi.le, rfl⟩
  let g (i : e.Index) : Σ n, Freq n := ⟨clusterIdx i, ⟨-(e.exp.rate i).im, i, (hw_idx i).symm, rfl⟩⟩
  have hrate (i : e.Index) : e.exp.rate i = ⟨w (g i).1, -((g i).2 : ℝ)⟩ :=
    Complex.ext (hw_idx i).symm (by simp [g])
  have hasymp (k : Σ n, Freq n) :
      (∀ᶠ x : ℝ in atTop, e.exp.groupAmplitude g k x = 0) ∨
        ∃ v : ℝ, ∃ z : ℂ, z ≠ 0 ∧
          Tendsto (fun x : ℝ ↦ x ^ v • e.exp.groupAmplitude g k x) atTop (𝓝 z) := by
    let z : ℂ := ∑' i : g ⁻¹' {k}, e.constAmp i.val
    have hconst : ∀ x : ℝ, e.exp.groupAmplitude g k x = z := fun x ↦ by
      unfold WaveExpansion.groupAmplitude
      exact tsum_congr fun i ↦ e.amplitude_eq_constAmp i.val x
    by_cases hz : z = 0
    · left; filter_upwards with x; rw [hconst x, hz]
    · right; refine ⟨0, z, hz, ?_⟩
      simp [hconst]
  have hsep := separate_physical_products e.exp g w (fun _ j ↦ j.val) hrate hw
    (fun _ ↦ Subtype.val_injective) hzero hasymp
  apply MvPowerSeries.ext; intro k
  change (∑ i : Fiber e k, e.constAmp i.val) = 0
  by_cases hex : ∃ i : e.Index, e.exp.rate i = ppKeyRate d k
  · obtain ⟨i₀, hi₀⟩ := hex
    have hset : {i : e.Index | e.exp.rate i = ppKeyRate d k} = g ⁻¹' {g i₀} := by
      ext i
      simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff]
      constructor
      · intro hir
        have hre : (e.exp.rate i).re = (e.exp.rate i₀).re := by rw [hir, hi₀]
        have him : -(e.exp.rate i).im = -(e.exp.rate i₀).im := by rw [hir, hi₀]
        have hidx : clusterIdx i = clusterIdx i₀ := hw.injective (by rw [hw_idx, hw_idx, hre])
        exact Sigma.ext hidx ((Subtype.heq_iff_coe_eq (fun y ↦ by simp only [g, hidx])).mpr him)
      · intro hg; rw [hrate i, hg, ← hrate i₀, hi₀]
    obtain ⟨x, hx⟩ := (hsep (g i₀).1 (g i₀).2).exists
    change (∑' j : g ⁻¹' {g i₀}, e.exp.amplitude j x) = 0 at hx
    let _ : Fintype {i : e.Index | e.exp.rate i = ppKeyRate d k} := fiberFintype e k
    rw [← tsum_congr_set_coe (fun i ↦ e.exp.amplitude i x) hset, tsum_fintype] at hx
    have hsum_eq : (∑ i : Fiber e k, e.constAmp i.val) =
        ∑ i : {i : e.Index | e.exp.rate i = ppKeyRate d k}, e.exp.amplitude i.val x := by
      refine Fintype.sum_equiv (Equiv.refl _) _ _ fun i ↦ (e.amplitude_eq_constAmp i.val x).symm
    exact hsum_eq.trans hx
  · have : IsEmpty (Fiber e k) := ⟨fun i ↦ hex ⟨i.val, i.property⟩⟩
    simp

private theorem marked_ofConst {d : ℕ} (hd : 2 ≤ d) (c : ℂ) :
    (ofConst d c).marked = MvPowerSeries.C c := by
  classical
  apply MvPowerSeries.ext; intro k
  rw [MvPowerSeries.coeff_C]
  by_cases hk : k = 0
  · subst hk
    let E : Fiber (ofConst d c) 0 ≃ Unit :=
      ⟨fun i ↦ i.val, fun u ↦ ⟨u, by simp [ofConst]⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
    change (∑ i : Fiber (ofConst d c) 0, (ofConst d c).constAmp i.val) = c
    rw [Fintype.sum_equiv E (fun i ↦ (ofConst d c).constAmp i.val) (fun _ ↦ c) (fun _ ↦ rfl)]
    simp
  · have : IsEmpty (Fiber (ofConst d c) k) :=
      ⟨fun i ↦ hk ((ppKeyRate_injective d hd) ((map_zero (ppKeyRate d)).trans i.property)).symm⟩
    simp [marked, MvPowerSeries.coeff_apply, hk]

private theorem marked_add {d : ℕ} (a b : ConstTracked d) :
    (a.add b).marked = a.marked + b.marked := by
  classical
  apply MvPowerSeries.ext; intro k
  rw [map_add]
  change (∑ i : Fiber (a.add b) k, _) = MvPowerSeries.coeff k a.marked + MvPowerSeries.coeff k b.marked
  let E : Fiber (a.add b) k ≃ Fiber a k ⊕ Fiber b k :=
    { toFun := fun | ⟨.inl j, h⟩ => .inl ⟨j, h⟩ | ⟨.inr j, h⟩ => .inr ⟨j, h⟩
      invFun := fun | .inl j => ⟨.inl j.val, j.property⟩ | .inr j => ⟨.inr j.val, j.property⟩
      left_inv := by rintro ⟨(j | j), h⟩ <;> rfl
      right_inv := by rintro (j | j) <;> rfl }
  rw [Fintype.sum_equiv E _ (Sum.elim (fun i ↦ a.constAmp i.val) (fun i ↦ b.constAmp i.val))
      (by rintro ⟨(j | j), h⟩ <;> rfl), Fintype.sum_sum_type]
  rfl

private theorem marked_mul {d : ℕ} (hd : 2 ≤ d) (a b : ConstTracked d) :
    (a.mul b).marked = a.marked * b.marked := by
  classical
  apply MvPowerSeries.ext; intro k
  rw [MvPowerSeries.coeff_mul, ← Finset.sum_coe_sort]
  have hsplit : ∀ i : Fiber (a.mul b) k,
      ∃ d₁ d₂ : Core d →₀ ℕ, d₁ + d₂ = k ∧ a.exp.rate i.val.1 = ppKeyRate d d₁ ∧
        b.exp.rate i.val.2 = ppKeyRate d d₂ := fun i ↦ by
    have hrate : a.exp.rate i.val.1 + b.exp.rate i.val.2 = ppKeyRate d k := i.property
    have hrot : ppRotIm d (a.exp.rate i.val.1 + b.exp.rate i.val.2) = 0 := by
      rw [hrate]; exact ppRotIm_keyRate hd k
    obtain ⟨h1, h2⟩ := (ppExtremeRay_face_iff (a.halfSpace i.val.1) (b.halfSpace i.val.2)).mp hrot
    obtain ⟨d₁, hd₁⟩ := a.extreme_range i.val.1 h1
    obtain ⟨d₂, hd₂⟩ := b.extreme_range i.val.2 h2
    exact ⟨d₁, d₂, ppKeyRate_injective d hd (by rw [map_add, ← hd₁, ← hd₂, hrate]), hd₁, hd₂⟩
  choose d₁ d₂ hsum hd₁ hd₂ using hsplit
  let E : Fiber (a.mul b) k ≃
      (Σ p : ↥(Finset.antidiagonal k), Fiber a p.val.1 × Fiber b p.val.2) :=
    { toFun := fun i ↦ ⟨⟨(d₁ i, d₂ i), Finset.mem_antidiagonal.mpr (hsum i)⟩,
        ⟨i.val.1, hd₁ i⟩, ⟨i.val.2, hd₂ i⟩⟩
      invFun := fun ⟨p, i, j⟩ ↦ ⟨(i.val, j.val), by
        change a.exp.rate i.val + b.exp.rate j.val = ppKeyRate d k
        rw [i.property, j.property, ← map_add, Finset.mem_antidiagonal.mp p.property]⟩
      left_inv := fun _ ↦ rfl
      right_inv := by
        rintro ⟨⟨⟨s₁, s₂⟩, hp⟩, ⟨i, hi⟩, ⟨j, hj⟩⟩
        let u : Fiber (a.mul b) k := ⟨(i, j), by
          change a.exp.rate i + b.exp.rate j = ppKeyRate d k
          rw [hi, hj, ← map_add, Finset.mem_antidiagonal.mp hp]⟩
        have hs₁ : d₁ u = s₁ := ppKeyRate_injective d hd ((hd₁ u).symm.trans hi)
        have hs₂ : d₂ u = s₂ := ppKeyRate_injective d hd ((hd₂ u).symm.trans hj)
        have hp_eq : (⟨(d₁ u, d₂ u), Finset.mem_antidiagonal.mpr (hsum u)⟩ : ↥(Finset.antidiagonal k)) =
            ⟨(s₁, s₂), hp⟩ := Subtype.ext (Prod.ext hs₁ hs₂)
        have hpair : HEq
            ((⟨i, hd₁ u⟩, ⟨j, hd₂ u⟩) : Fiber a (d₁ u) × Fiber b (d₂ u))
            ((⟨i, hi⟩, ⟨j, hj⟩) : Fiber a s₁ × Fiber b s₂) := by
          have aux : ∀ (t₁ t₂ : Core d →₀ ℕ) (ht₁ : a.exp.rate i = ppKeyRate d t₁)
              (ht₂ : b.exp.rate j = ppKeyRate d t₂), t₁ = s₁ → t₂ = s₂ →
              HEq ((⟨i, ht₁⟩, ⟨j, ht₂⟩) : Fiber a t₁ × Fiber b t₂)
                ((⟨i, hi⟩, ⟨j, hj⟩) : Fiber a s₁ × Fiber b s₂) := by
            rintro _ _ _ _ rfl rfl; rfl
          exact aux (d₁ u) (d₂ u) (hd₁ u) (hd₂ u) hs₁ hs₂
        exact Sigma.ext hp_eq hpair }
  change (∑ i : Fiber (a.mul b) k, (a.mul b).constAmp i.val) = _
  rw [Fintype.sum_equiv E (fun i ↦ (a.mul b).constAmp i.val)
        (fun x ↦ a.constAmp x.2.1.val * b.constAmp x.2.2.val) (fun _ ↦ rfl),
      Fintype.sum_sigma]
  apply Finset.sum_congr rfl; intro p _
  rw [Fintype.sum_prod_type]
  simp [marked, MvPowerSeries.coeff_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

private def ofPPWaveJet (d : ℕ) (hd : 2 ≤ d) (j : ℕ) : ConstTracked d where
  Index := Fin d × ℕ+
  exp := ppWaveJet d hd j
  is_const := fun ℓN ↦ ⟨_, fun _ ↦ rfl⟩
  finite_window R := by
    have hsub : {ℓN : Fin d × ℕ+ | (ppWaveRate d ℓN.1 ℓN.2).re ≤ R} ⊆
        ⋃ ℓ : Fin d, (fun N ↦ (ℓ, N)) '' {N : ℕ+ | (ppWaveRate d ℓ N).re ≤ R} := by
      rintro ⟨ℓ, N⟩ h; exact mem_iUnion.mpr ⟨ℓ, N, h, rfl⟩
    refine (Set.finite_iUnion fun ℓ ↦ ?_).subset hsub
    apply Set.Finite.image
    have hc : 0 < (ppRay d ℓ.val).re := ppRay_re_pos hd ℓ.isLt
    obtain ⟨M, hM⟩ := exists_nat_gt (max 0 (R / (ppRay d ℓ.val).re) ^ d)
    have hsubN : {N : ℕ+ | (ppWaveRate d ℓ N).re ≤ R} ⊆
        Subtype.val ⁻¹' (Set.Iic M) := by
      intro N hN
      change (ppWaveRate d ℓ N).re ≤ R at hN
      have hre : (ppWaveRate d ℓ N).re = (N.val : ℝ) ^ (1 / (d : ℝ)) * (ppRay d ℓ.val).re := by
        simp [ppWaveRate, Complex.mul_re]
      rw [hre] at hN
      have hle : (N.val : ℝ) ^ (1 / (d : ℝ)) ≤ max 0 (R / (ppRay d ℓ.val).re) :=
        ((le_div_iff₀ hc).mpr hN).trans (le_max_right _ _)
      have hpow : (N.val : ℝ) ≤ max 0 (R / (ppRay d ℓ.val).re) ^ d := by
        have h1 := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) hle d
        have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
        rw [← Real.rpow_natCast ((N.val : ℝ) ^ _), ← Real.rpow_mul (Nat.cast_nonneg _),
            one_div, inv_mul_cancel₀ hd0, Real.rpow_one] at h1
        exact h1
      change N.val ≤ M
      exact_mod_cast (hpow.trans hM.le)
    exact ((Set.finite_Iic M).preimage Subtype.val_injective.injOn).subset hsubN
  halfSpace := fun ℓN ↦ by
    change 0 ≤ ppRotIm d ((((ℓN.2.val : ℝ) ^ (1 / (d : ℝ)) : ℝ) : ℂ) * ppRay d ℓN.1.val)
    rw [ppRotIm_smul_real]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (ppRotIm_nonneg hd ℓN.1.isLt)
  extreme_range := fun ℓN h0 ↦ by
    change ppRotIm d ((((ℓN.2.val : ℝ) ^ (1 / (d : ℝ)) : ℝ) : ℂ) * ppRay d ℓN.1.val) = 0 at h0
    rw [ppRotIm_smul_real] at h0
    have hpos : 0 < (ℓN.2.val : ℝ) ^ (1 / (d : ℝ)) :=
      Real.rpow_pos_of_pos (by exact_mod_cast ℓN.2.property) _
    have hray0 : ppRotIm d (ppRay d ℓN.1.val) = 0 := (mul_eq_zero.mp h0).resolve_left hpos.ne'
    have hℓ0 : ℓN.1.val = 0 := by
      by_contra hne
      linarith [ppRotIm_other_pos hd (Nat.pos_of_ne_zero hne) ℓN.1.isLt]
    refine ⟨ppModeKey d hd ℓN.2, ?_⟩
    rw [ppKeyRate_modeKey d hd ℓN.2]
    change (((ℓN.2.val : ℝ) ^ (1 / (d : ℝ)) : ℝ) : ℂ) * ppRay d ℓN.1.val = _
    rw [hℓ0]; rfl

private theorem marked_ofPPWaveJet_single_prime {d : ℕ} (hd : 2 ≤ d) (j : ℕ)
    {p : ℕ} (hp : p.Prime) :
    let b : Core d := ⟨p, rfree_of_prime hd hp⟩
    MvPowerSeries.coeff (Finsupp.single b 1) (ofPPWaveJet d hd j).marked =
      -(ppExtremeRay d * (((p : ℝ) ^ (1 / (d : ℝ)) : ℝ) : ℂ)) *
        (-(ppExtremeRay d * (((p : ℝ) ^ (1 / (d : ℝ)) : ℝ) : ℂ))) ^ j := by
  intro b
  change (∑ i : Fiber (ofPPWaveJet d hd j) (Finsupp.single b 1),
      (ofPPWaveJet d hd j).constAmp i.val) = _
  let pP : ℕ+ := ⟨p, hp.pos⟩
  let i₀ : Fiber (ofPPWaveJet d hd j) (Finsupp.single b 1) :=
    ⟨(⟨0, by omega⟩, pP), by
      have hk := (ppModeKey_eq_single_one d hd pP b).mpr rfl
      rw [← hk, ppKeyRate_modeKey d hd pP]; rfl⟩
  have huniq : ∀ i : Fiber (ofPPWaveJet d hd j) (Finsupp.single b 1), i = i₀ := by
    rintro ⟨⟨ℓ, N⟩, hrate⟩
    have hrot : ppRotIm d (ppWaveRate d ℓ N) = 0 := by
      change ppRotIm d ((ofPPWaveJet d hd j).exp.rate (ℓ, N)) = 0
      rw [hrate]; exact ppRotIm_keyRate hd _
    change ppRotIm d ((((N.val : ℝ) ^ (1 / (d : ℝ)) : ℝ) : ℂ) * ppRay d ℓ.val) = 0 at hrot
    rw [ppRotIm_smul_real] at hrot
    have hpos : 0 < (N.val : ℝ) ^ (1 / (d : ℝ)) := Real.rpow_pos_of_pos (by exact_mod_cast N.property) _
    have hray0 : ppRotIm d (ppRay d ℓ.val) = 0 := (mul_eq_zero.mp hrot).resolve_left hpos.ne'
    have hℓ0 : ℓ.val = 0 := by
      by_contra hne; linarith [ppRotIm_other_pos hd (Nat.pos_of_ne_zero hne) ℓ.isLt]
    have hrate' : ppKeyRate d (ppModeKey d hd N) = ppKeyRate d (Finsupp.single b 1) := by
      rw [ppKeyRate_modeKey d hd N, ← hrate]
      change (((N.val : ℝ) ^ (1 / (d : ℝ)) : ℝ) : ℂ) * ppRay d 0 =
        (((N.val : ℝ) ^ (1 / (d : ℝ)) : ℝ) : ℂ) * ppRay d ℓ.val
      rw [hℓ0]
    have hNp : N.val = p := (ppModeKey_eq_single_one d hd N b).mp (ppKeyRate_injective d hd hrate')
    exact Subtype.ext (Prod.ext (Fin.ext hℓ0) (PNat.eq hNp))
  rw [Finset.sum_eq_single i₀ (fun i _ hne ↦ (hne (huniq i)).elim) (fun h ↦ (h (Finset.mem_univ _)).elim)]
  have hpP : pP.val = p := rfl
  change -((powerPartMult d pP.val : ℝ) : ℂ) * ((((pP.val : ℝ) ^ (1 / (d : ℝ)) : ℝ) : ℂ) * ppRay d 0) *
      (-((((pP.val : ℝ) ^ (1 / (d : ℝ)) : ℝ) : ℂ) * ppRay d 0)) ^ j = _
  rw [hpP, powerPartMult_prime hd hp, Complex.ofReal_one, ppExtremeRay]
  ring

private theorem evalPoly_constTracked {d : ℕ} (hd : 2 ≤ d) {J : ℕ}
    (f : Fin J → ConstTracked d) (P : MvPolynomial (Fin J) ℂ) :
    ∃ E : ConstTracked d,
      (∀ᶠ x : ℝ in atTop, E.exp.value x = MvPolynomial.eval (fun j ↦ (f j).exp.value x) P) ∧
      E.marked = MvPolynomial.aeval (fun j ↦ (f j).marked) P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨ofConst d c, Eventually.of_forall fun x ↦ ?_, by rw [marked_ofConst hd, MvPolynomial.aeval_C]; rfl⟩
    simp [ofConst, WaveExpansion.value, WaveExpansion.term]
  | add p q hp hq =>
    obtain ⟨Ep, hvp, hmp⟩ := hp
    obtain ⟨Eq, hvq, hmq⟩ := hq
    refine ⟨Ep.add Eq, ?_, by rw [marked_add, hmp, hmq, map_add]⟩
    filter_upwards [Ep.exp.value_add Eq.exp, hvp, hvq] with x hadd hp' hq'
    rw [show (Ep.add Eq).exp.value x = (Ep.exp.add Eq.exp).value x from rfl, hadd, hp', hq', map_add]
  | mul_X p j hp =>
    obtain ⟨Ep, hvp, hmp⟩ := hp
    refine ⟨Ep.mul (f j), ?_, by rw [marked_mul hd, hmp, map_mul, MvPolynomial.aeval_X]⟩
    filter_upwards [Ep.exp.value_mul (f j).exp, hvp] with x hmul hp'
    rw [show (Ep.mul (f j)).exp.value x = (Ep.exp.mul (f j).exp).value x from rfl, hmul, hp',
        map_mul, MvPolynomial.eval_X]

end ConstTracked

/-- **Unconditional Formal-to-Autonomous Transfer for `logDerivPowerPart d`** (`d ≥ 2`):
any nontrivial ADE over `ℂ(q)` satisfied by `F_d(q)` yields a nonzero autonomous
polynomial relation in the `X`-derivatives of `H̃_d(X) = F̃_d(X) - polarPoly(X⁻¹)`! -/
private theorem pp_formal_transfer {d : ℕ} (hd : 2 ≤ d) (P : PowerPartStokesProfile d hd)
    (Q : MvPolynomial ℕ ℂ) (hQ : Q ≠ 0)
    (hzero : MvPolynomial.aeval (logDerivPowerPartCoordinates d) Q = 0) :
    ∃ (J : ℕ) (R : MvPolynomial (Fin J) ℂ), R ≠ 0 ∧
      ∀ᶠ X : ℝ in atTop, MvPolynomial.eval (fun j : Fin J ↦ (ppWaveJet d hd j).value X) R = 0 := by
  classical
  have hd3 : 3 ≤ d + 1 := by omega
  let src : ℕ → ℝ → ℂ
    | 0 => qRayD (d + 1)
    | j + 1 => fun X ↦ psValue (formalJet (logDerivPowerPart d) j) (qRayD (d + 1) X)
  have hsrc_an {X : ℝ} (hX : 0 < X) (j : ℕ) : AnalyticAt ℝ (src j) X := by
    cases j with
    | zero => exact qRayD_analytic hX
    | succ j =>
      exact (((ppLogDeriv_jet_analytic d 1 j) _ (by simpa using qRayD_disk hX)).restrictScalars
        (𝕜 := ℝ)).comp (qRayD_analytic hX)
  have hsrc_deriv {X : ℝ} (hX : 0 < X) (j : ℕ) :
      HasDerivAt (src (j + 1)) (speedD (d + 1) X * src (j + 2) X) X := by
    simpa [src, logDerivPowerPart, Function.comp_def, mul_comm] using!
      ((ppLogDeriv_jet_deriv d 1 j (qRayD_disk hX)).scomp X (qRayD_deriv hd3 hX))
  have hrel (X : ℝ) (hX : 0 < X) : MvPolynomial.eval (fun i ↦ src i X) Q = 0 := by
    have ha (j : ℕ) : PSAbsAt (logDerivPowerPartCoordinates d j) (qRayD (d + 1) X) := by
      cases j with
      | zero => exact (ps_nome_abs _).1
      | succ j => exact ppLogDeriv_jet_abs d 1 j (qRayD_disk hX)
    have he : (fun i ↦ psValue (logDerivPowerPartCoordinates d i) (qRayD (d + 1) X)) =
        fun i ↦ src i X := by
      funext i; cases i with
      | zero => exact (ps_nome_abs _).2
      | succ j => rfl
    have hh := (ps_polynomial_value Q ha).2
    rw [hzero, he] at hh
    simpa [psValue, psTerm] using hh.symm
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 P.decomp
  let X₀ : ℝ := max L₀ 1
  have hX₀_pos : 0 < X₀ := lt_of_lt_of_le zero_lt_one (le_max_right L₀ 1)
  obtain ⟨n, A, x, hx, ordinary, ident⟩ :=
    ordinary_relation (Ioi (0 : ℝ)) ⟨X₀, hX₀_pos⟩ src ⟨Q, hQ, hrel⟩
  let v (i : Fin (n + 1)) := src i.val
  let g (i : Fin (n + 1)) (X : ℝ) := MvPolynomial.eval (fun j ↦ v j X) (MvPolynomial.pderiv i A)
  let top := Fin.last n
  let S := g top
  have hd_v {X : ℝ} (hX : 0 < X) (i : Fin (n + 1)) : DifferentiableAt ℝ (v i) X :=
    (hsrc_an hX i.val).differentiableAt
  have chain (B : MvPolynomial (Fin (n + 1)) ℂ) {X : ℝ} (hX : 0 < X) :=
    polynomial_chain B v (fun i ↦ deriv (v i)) X (fun i ↦ (hd_v hX i).hasDerivAt)
  have vanish {X : ℝ} (hX : 0 < X) : ∑ i, g i X * deriv (v i) X = 0 := by
    have near : (fun z ↦ MvPolynomial.eval (fun i ↦ v i z) A) =ᶠ[𝓝 X] (fun _ ↦ 0) :=
      (lt_mem_nhds hX).mono fun z hz ↦ ident z hz
    exact (chain A hX).deriv.symm.trans (near.deriv_eq.trans (deriv_const ..))
  have hn : n ≠ 0 := by
    rintro rfl
    have he := vanish hx
    change ∑ i : Fin 1, g i x * deriv (v i) x = 0 at he
    rw [Fin.sum_univ_one] at he
    have ds : deriv (v 0) x = speedD (d + 1) x := (qRayD_deriv hd3 hx).deriv
    rw [ds] at he
    have hs : speedD (d + 1) x ≠ 0 := by
      unfold speedD recipD qRayD
      have hr0 : ((d + 1 - 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show d + 1 - 1 ≠ 0 by omega)
      have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
      exact mul_ne_zero (mul_ne_zero hr0 (pow_ne_zero (d + 1) (inv_ne_zero hx0)))
        (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
    exact mul_ne_zero ordinary hs he
  let invS (X : ℝ) := (S X)⁻¹
  let u : Fin (n + 1) ⊕ Fin 2 → ℝ → ℂ := Sum.elim v ![recipD, invS]
  let G := Generated u x
  have gv (i : Fin (n + 1)) : G (v i) := Generated.coord (u := u) (.inl i)
  have gr : G recipD := Generated.coord (u := u) (.inr 0)
  have gw : G invS := Generated.coord (u := u) (.inr 1)
  have gc (c : ℂ) : G (fun _ ↦ c) := Generated.const _
  have gs : G (speedD (d + 1)) := ((gc ((d + 1 - 1 : ℕ) : ℂ)).mul (gr.pow (d + 1))).mul (gv 0)
  have gg (i : Fin (n + 1)) : G (g i) := Generated.evalPoly v gv _
  have pos : ∀ᶠ X in 𝓝 x, 0 < X := lt_mem_nhds hx
  have Snz : ∀ᶠ X in 𝓝 x, S X ≠ 0 := (chain (MvPolynomial.pderiv top A) hx).continuousAt.eventually_ne ordinary
  have low (i : Fin (n + 1)) (hi : i ≠ top) : G (deriv (v i)) := by
    obtain ⟨k, hk⟩ := i
    cases k with
    | zero => exact gs.congr (pos.mono fun X hX ↦ (qRayD_deriv hd3 hX).deriv.symm)
    | succ k =>
      have lt : k + 2 < n + 1 := by
        have h : k + 1 ≠ n := fun eqn ↦ hi (Fin.ext eqn); omega
      apply (gs.mul (gv ⟨k + 2, lt⟩)).congr
      exact pos.mono fun X hX ↦ (hsrc_deriv hX k).deriv.symm
  let lowSum := ∑ i ∈ Finset.univ.erase top, g i * deriv (v i)
  have gl : G lowSum := Generated.finsetSum _ _ (fun i hi ↦ (gg i).mul (low i (Finset.mem_erase.mp hi).1))
  have dv (i : Fin (n + 1)) : G (deriv (v i)) := by
    by_cases hi : i = top
    · subst i
      apply (((gc (-1)).mul gl).mul gw).congr
      filter_upwards [pos, Snz] with X hX nz
      have he := vanish hX
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ top)] at he
      change (-1) * lowSum X * (S X)⁻¹ = deriv (v top) X
      have hh : S X * deriv (v top) X + lowSum X = 0 := by simpa [S, lowSum, Finset.sum_apply] using he
      field_simp [nz]; linear_combination -hh
    · exact low i hi
  have dS : G (deriv S) := by
    let D (i : Fin (n + 1)) (X : ℝ) :=
      MvPolynomial.eval (fun k ↦ v k X) (MvPolynomial.pderiv i (MvPolynomial.pderiv top A))
    have gen (i) : G (D i) := Generated.evalPoly v gv _
    apply (Generated.finsetSum Finset.univ _ (fun i _ ↦ (gen i).mul (dv i))).congr
    filter_upwards [pos] with X hX
    simpa [D, Finset.sum_apply] using (chain (MvPolynomial.pderiv top A) hX).deriv.symm
  have smooth : ∀ᶠ X in 𝓝 x, ∀ i, DifferentiableAt ℝ (u i) X := by
    filter_upwards [pos, Snz] with X hX nz i
    rcases i with i | i
    · exact hd_v hX i
    · fin_cases i
      · exact (recipD_deriv hX).differentiableAt
      · exact (chain (MvPolynomial.pderiv top A) hX).differentiableAt.inv nz
  have closed (i) : G (deriv (u i)) := by
    rcases i with i | i
    · exact dv i
    · fin_cases i
      · change G (deriv recipD)
        exact ((gc (-1)).mul (gr.pow 2)).congr (pos.mono fun X hX ↦ by simpa using (recipD_deriv hX).deriv.symm)
      · apply (((gc (-1)).mul dS).mul (gw.pow 2)).congr
        filter_upwards [pos, Snz] with X hX nz
        have hi := ((chain (MvPolynomial.pderiv top A) hX).differentiableAt.hasDerivAt.inv nz).deriv
        change (-1) * deriv S X * ((S X)⁻¹) ^ 2 = deriv invS X
        change deriv invS X = -deriv S X / (S X) ^ 2 at hi
        rw [hi]; simp [inv_pow, div_eq_mul_inv]
  let reg (X : ℝ) : ℂ := rescaledLogDerivPP d X - P.polarPoly.eval (recipD X)
  have hpolyG : G (fun X ↦ P.polarPoly.eval (recipD X)) := by
    induction P.polarPoly using Polynomial.induction_on' with
    | add p q hp hq => exact (hp.add hq).congr (Eventually.of_forall fun X ↦ by simp)
    | monomial k c => exact ((gc c).mul (gr.pow k)).congr (Eventually.of_forall fun X ↦ by simp)
  have readout : G reg := by
    exact ((((gc (d : ℂ)).mul (gr.pow (d + 1))).mul (gv ⟨1, by omega⟩)).sub hpolyG).congr
      (Eventually.of_forall fun X ↦ by simp [reg, rescaledLogDerivPP, v, src, recipD, formalJet])
  obtain ⟨R, hRne, hR_loc⟩ := autonomous_readout u x reg readout smooth closed
  -- Analytic continuation on `Ioi 0` from `𝓝 x` to `atTop`!
  have hreg_an (X : ℝ) (hX : 0 < X) : AnalyticAt ℝ reg X := by
    have hrec : AnalyticAt ℝ recipD X :=
      (Complex.ofRealCLM.analyticAt X).inv (Complex.ofReal_ne_zero.mpr hX.ne')
    have hpol : AnalyticAt ℝ (fun y ↦ P.polarPoly.eval (recipD y)) X := by
      induction P.polarPoly using Polynomial.induction_on' with
      | add p q hp hq =>
        simpa only [Polynomial.eval_add] using hp.fun_add hq
      | monomial k c =>
        simpa only [Polynomial.eval_monomial] using analyticAt_const.fun_mul (hrec.fun_pow k)
    exact ((analyticAt_const.fun_mul (hrec.fun_pow (d + 1))).fun_mul (hsrc_an hX 1)).fun_sub hpol
  have hreg_jet_an (X : ℝ) (hX : 0 < X) (k : ℕ) : AnalyticAt ℝ (iteratedDeriv k reg) X := by
    induction k with
    | zero => simpa using hreg_an X hX
    | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
  have hpoly_an_gen {m : ℕ} (B : MvPolynomial (Fin m) ℂ) : AnalyticOnNhd ℝ
      (fun X ↦ MvPolynomial.eval (fun j : Fin m ↦ iteratedDeriv j.val reg X) B) (Ioi 0) := by
    intro X hX
    induction B using MvPolynomial.induction_on with
    | C => simpa using analyticAt_const
    | add a b ha hb => simpa only [map_add] using ha.fun_add hb
    | mul_X a j ha => simpa only [map_mul, eval_X] using ha.fun_mul (hreg_jet_an X hX j.val)
  have hpoly_an := hpoly_an_gen R
  have hR_tail : ∀ᶠ X : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin _ ↦ iteratedDeriv j.val reg X) R = 0 :=
    (eventually_gt_atTop (0 : ℝ)).mono fun X hX ↦
      hpoly_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_Ioi _).isPreconnected hx hR_loc hX
  have hreg_eq : reg =ᶠ[atTop] (ppWaveJet d hd 0).value := by
    filter_upwards [P.decomp] with X hX
    simp only [reg, recipD, hX, add_sub_cancel_left]
  have hjet_eq (k : ℕ) : iteratedDeriv k reg =ᶠ[atTop] (ppWaveJet d hd k).value := by
    obtain ⟨L, hL⟩ := eventually_atTop.1 hreg_eq
    have h1 : iteratedDeriv k reg =ᶠ[atTop] iteratedDeriv k (ppWaveJet d hd 0).value :=
      (eventually_gt_atTop L).mono fun X hX ↦ by
        have hloc : reg =ᶠ[𝓝 X] (ppWaveJet d hd 0).value :=
          (lt_mem_nhds hX).mono fun y hy ↦ hL y hy.le
        exact hloc.iteratedDeriv_eq k
    exact h1.trans (ppWaveJet_derivatives hd k)
  refine ⟨_, R, hRne, ?_⟩
  have hall := (Filter.eventually_all_finset
    (Finset.univ : Finset (Fin (Fintype.card (Fin (n + 1) ⊕ Fin 2) + 1)))).mpr
    fun j _ ↦ hjet_eq j.val
  filter_upwards [hR_tail, hall] with X h0 hj
  rw [← h0]
  exact congrArg (fun f ↦ MvPolynomial.eval f R) (funext fun j ↦ (hj j (Finset.mem_univ j)).symm)

/-- **Zero-Tilt Constant-Vandermonde Master Theorem for `logDerivPowerPart d` (`d ≥ 2`)**:
For EVERY integer `d ≥ 2`, given `P : PowerPartStokesProfile d hd`, the logarithmic
derivative `F_d(q) = q (d/dq) log P_d(q)` is differentially transcendental over `ℂ(q)` —
proved on the **untilted** real ray `X > 0` via the exact constant `J × J` prime Vandermonde
matrix `ppPrimeVandermonde d`! -/
theorem logDerivPowerPart_non_ade {d : ℕ} (hd : 2 ≤ d) (P : PowerPartStokesProfile d hd) :
    AlgebraicIndependent ℂ (logDerivPowerPartCoordinates d) := by
  rw [algebraicIndependent_iff]
  intro Q hQ
  by_contra hQne
  obtain ⟨J, R, hRne, hR_zero⟩ := pp_formal_transfer hd P Q hQne hQ
  let f : Fin J → ConstTracked d := fun j ↦ ConstTracked.ofPPWaveJet d hd j.val
  obtain ⟨E, hE_val, hE_marked⟩ := ConstTracked.evalPoly_constTracked hd f R
  have hE_zero : ∀ᶠ X : ℝ in atTop, E.exp.value X = 0 := by
    filter_upwards [hE_val, hR_zero] with X h1 h2
    rw [h1]; exact h2
  have hmarked_zero : MvPolynomial.aeval (fun j : Fin J ↦ (f j).marked) R = 0 := by
    rw [← hE_marked]; exact E.separate_zero hE_zero
  let p : Fin J → ℕ := fun i ↦ Nat.nth Nat.Prime i.val
  have hp_prime : ∀ i : Fin J, (p i).Prime := fun i ↦
    Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i.val
  have hp_inj : Function.Injective p := fun i j h ↦
    Fin.ext ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective h)
  let marks : Fin J → Core d := fun i ↦ ⟨p i, rfree_of_prime hd (hp_prime i)⟩
  have hjac_eq : Matrix.of (fun i j : Fin J ↦
      MvPowerSeries.coeff (Finsupp.single (marks i) 1) (f j).marked) =
      ppPrimeVandermonde d p := by
    ext i j
    exact ConstTracked.marked_ofPPWaveJet_single_prime hd j.val (hp_prime i)
  have hunit : IsUnit (Matrix.of (fun i j : Fin J ↦
      MvPowerSeries.coeff (Finsupp.single (marks i) 1) (f j).marked)).det := by
    rw [hjac_eq, isUnit_iff_ne_zero]
    exact ppPrimeVandermonde_det_ne_zero hd p (fun i ↦ (hp_prime i).pos) hp_inj
  have hindep : AlgebraicIndependent ℂ (fun j : Fin J ↦ (f j).marked) :=
    CubicTheta.independent_of_marked_jacobian marks (fun j ↦ (f j).marked) hunit
  exact hRne ((algebraicIndependent_iff.mp hindep) R hmarked_zero)

/-- **Zero-Tilt Constant-Vandermonde Master Theorem for `P_d(q)` (`d ≥ 2`)**:
For EVERY integer `d ≥ 2`, given `P : PowerPartStokesProfile d hd`, the `d`-th power
partition product `P_d(q) = ∏_{n ≥ 1} (1 - q^{n^d})^{-1}` is differentially
transcendental over `ℂ(q)`! -/
theorem powerPart_non_ade {d : ℕ} (hd : 2 ≤ d) (P : PowerPartStokesProfile d hd) :
    AlgebraicIndependent ℂ (powerPartCoordinates d) :=
  diffTrans_of_logDeriv (powerPartSeries_ne_zero d) one_ne_zero
    (by simpa using X_mul_deriv_powerPartSeries (by omega : 1 ≤ d))
    (logDerivPowerPart_non_ade hd P)

/-- **All-`d` Nonzero Integer Power Differential Transcendence Theorem (`d ≥ 2`, `k ∈ ℤ \ {0}`)**:
For EVERY `d ≥ 2`, EVERY nonzero integer `k ≠ 0` (positive OR negative!), given
`P : PowerPartStokesProfile d hd`, `P_d(q)^k` is differentially transcendental over `ℂ(q)`! -/
theorem powerPart_zpow_non_ade {d : ℕ} (hd : 2 ≤ d) (P : PowerPartStokesProfile d hd)
    {k : ℤ} (hk : k ≠ 0) :
    AlgebraicIndependent ℂ (powerPartZPowCoordinates d k) :=
  diffTrans_of_logDeriv (powerPartZPow_ne_zero d k) (by exact_mod_cast hk)
    (X_mul_deriv_powerPartZPow (by omega : 1 ≤ d) k)
    (logDerivPowerPart_non_ade hd P)

/-! ### 5. Joint Differential Independence of Arbitrary Distinct Power-Partition Dilations (`d ≥ 2`) -/

section Dilations

private def ppDilScale (d m : ℕ) : ℝ := (m : ℝ) ^ (-(1 / (d : ℝ)))

private lemma ppDilScale_pos {d m : ℕ} (hm : 0 < m) : 0 < ppDilScale d m :=
  Real.rpow_pos_of_pos (by exact_mod_cast hm) _

private lemma ppQRay_dilScale {d : ℕ} (hd : 2 ≤ d) (m : ℕ+) (X : ℝ) :
    qRayD (d + 1) (ppDilScale d m.val * X) = (qRayD (d + 1) X) ^ m.val := by
  have hm : (0 : ℝ) < (m.val : ℝ) := by exact_mod_cast m.property
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hσ_pow : (ppDilScale d m.val) ^ d = (m.val : ℝ)⁻¹ := by
    unfold ppDilScale
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm.le, neg_mul, one_div, inv_mul_cancel₀ hd0,
        Real.rpow_neg_one]
  unfold qRayD
  rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
  congr 2
  have hsub : d + 1 - 1 = d := by omega
  rw [hsub, mul_pow, hσ_pow, div_mul_eq_div_div, div_inv_eq_mul]
  ring

/-- Additive extreme-ray dilation lattice `(Core d →₀ ℕ) →+ ℂ` with common denominator `A`. -/
private def ppDilKeyRate (d A : ℕ) : (Core d →₀ ℕ) →+ ℂ where
  toFun k := ((readRootKey d k / (A : ℝ) : ℝ) : ℂ) * ppExtremeRay d
  map_zero' := by simp
  map_add' k₁ k₂ := by simp [map_add, add_div, add_mul]

private lemma ppDilKeyRate_injective {d A : ℕ} (hd : 2 ≤ d) (hA : 0 < A) :
    Function.Injective (ppDilKeyRate d A) := by
  intro k₁ k₂ h
  have h1 := Complex.ofReal_injective (mul_right_cancel₀ (ppExtremeRay_ne_zero hd) h)
  exact readRootKey_injective d hd ((div_left_inj₀ (by exact_mod_cast hA.ne')).mp h1)

private lemma ppRotIm_dilKeyRate {d A : ℕ} (hd : 2 ≤ d) (k : Core d →₀ ℕ) :
    ppRotIm d (ppDilKeyRate d A k) = 0 := by
  change ppRotIm d (((readRootKey d k / (A : ℝ) : ℝ) : ℂ) * ppExtremeRay d) = 0
  rw [ppRotIm_smul_real, ppRotIm_extreme hd, mul_zero]

private def ppDilCore {d : ℕ} (hd : 2 ≤ d) (m N : ℕ+) : Core d :=
  rFreeCore d (by omega) ⟨m.val ^ (d - 1) * N.val, mul_pos (pow_pos m.property _) N.property⟩

private def ppDilRoot {d : ℕ} (hd : 2 ≤ d) (m N : ℕ+) : ℕ :=
  rFreeRoot d (by omega) ⟨m.val ^ (d - 1) * N.val, mul_pos (pow_pos m.property _) N.property⟩

private def ppDilExp {d : ℕ} (hd : 2 ≤ d) (A : ℕ) (m N : ℕ+) : ℕ :=
  (A / m.val) * ppDilRoot hd m N

private def ppDilModeExp {d : ℕ} (hd : 2 ≤ d) (A : ℕ) (m N : ℕ+) : Core d →₀ ℕ :=
  Finsupp.single (ppDilCore hd m N) (ppDilExp hd A m N)

private lemma ppDilExp_pos {d : ℕ} (hd : 2 ≤ d) {A : ℕ} (hA : 0 < A) {m : ℕ+}
    (hdiv : m.val ∣ A) (N : ℕ+) : 0 < ppDilExp hd A m N :=
  mul_pos (Nat.div_pos (Nat.le_of_dvd hA hdiv) m.property) (rFreeRoot_pos d (by omega) _)

/-- Pure-`ℕ` key identity for power-partition dilations: `m · e(m, N)^d · c(m, N) = A^d · N`. -/
private lemma ppDil_nat_identity {d : ℕ} (hd : 2 ≤ d) {A : ℕ} {m : ℕ+}
    (hdiv : m.val ∣ A) (N : ℕ+) :
    m.val * (ppDilExp hd A m N) ^ d * (ppDilCore hd m N).val = A ^ d * N.val := by
  have hfac : (ppDilRoot hd m N) ^ d * (ppDilCore hd m N).val = m.val ^ (d - 1) * N.val :=
    rFreeRoot_pow_mul_core d (by omega) _
  have hmul : m.val * (A / m.val) = A := Nat.mul_div_cancel' hdiv
  have hd_sub : 1 + (d - 1) = d := by omega
  calc m.val * (ppDilExp hd A m N) ^ d * (ppDilCore hd m N).val
      = m.val * ((A / m.val) ^ d * (ppDilRoot hd m N) ^ d) * (ppDilCore hd m N).val := by
        simp only [ppDilExp, mul_pow]
    _ = m.val * (A / m.val) ^ d * ((ppDilRoot hd m N) ^ d * (ppDilCore hd m N).val) := by ring
    _ = m.val * (A / m.val) ^ d * (m.val ^ (d - 1) * N.val) := by rw [hfac]
    _ = (m.val ^ 1 * m.val ^ (d - 1)) * (A / m.val) ^ d * N.val := by ring
    _ = (m.val * (A / m.val)) ^ d * N.val := by rw [← pow_add, hd_sub, ← mul_pow]
    _ = A ^ d * N.val := by rw [hmul]

private lemma ppDilKeyRate_modeExp {d : ℕ} (hd : 2 ≤ d) {A : ℕ} (hA : 0 < A)
    {m : ℕ+} (hdiv : m.val ∣ A) (N : ℕ+) :
    ppDilKeyRate d A (ppDilModeExp hd A m N) =
      ((ppDilScale d m.val : ℝ) : ℂ) * ppWaveRate d ⟨0, by omega⟩ N := by
  have hreal : readRootKey d (ppDilModeExp hd A m N) / (A : ℝ) =
      ppDilScale d m.val * (N.val : ℝ) ^ (1 / (d : ℝ)) := by
    rw [ppDilModeExp, readRootKey_single]
    have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
    have hmpos : (0 : ℝ) < (m.val : ℝ) := by exact_mod_cast m.pos
    have hNpos : (0 : ℝ) < (N.val : ℝ) := by exact_mod_cast N.pos
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    apply (pow_left_inj₀ (by positivity)
      (mul_nonneg (ppDilScale_pos m.pos).le (Real.rpow_nonneg hNpos.le _))
      (show d ≠ 0 by omega)).mp
    have hpow_l : (((ppDilExp hd A m N : ℝ) * ((ppDilCore hd m N).val : ℝ) ^ (1 / (d : ℝ))) /
        (A : ℝ)) ^ d = ((ppDilExp hd A m N : ℝ) ^ d * ((ppDilCore hd m N).val : ℝ)) / (A : ℝ) ^ d := by
      rw [div_pow, mul_pow, ← Real.rpow_natCast (((ppDilCore hd m N).val : ℝ) ^ _),
          ← Real.rpow_mul (Nat.cast_nonneg _), one_div, inv_mul_cancel₀ hd0, Real.rpow_one]
    have hpow_r : (ppDilScale d m.val * (N.val : ℝ) ^ (1 / (d : ℝ))) ^ d =
        (m.val : ℝ)⁻¹ * (N.val : ℝ) := by
      rw [mul_pow]; congr 1
      · unfold ppDilScale
        rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le, neg_mul, one_div,
            inv_mul_cancel₀ hd0, Real.rpow_neg_one]
      · rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, one_div,
            inv_mul_cancel₀ hd0, Real.rpow_one]
    rw [hpow_l, hpow_r]
    have hnat : ((m.val : ℝ) * (ppDilExp hd A m N : ℝ) ^ d * ((ppDilCore hd m N).val : ℝ)) =
        (A : ℝ) ^ d * (N.val : ℝ) := by exact_mod_cast ppDil_nat_identity hd hdiv N
    field_simp [hApos.ne', hmpos.ne']; linarith
  change ((readRootKey d (ppDilModeExp hd A m N) / (A : ℝ) : ℝ) : ℂ) * ppExtremeRay d = _
  rw [hreal, ppWaveRate, Complex.ofReal_mul]; simp [ppExtremeRay, mul_assoc]

private lemma ppDilCore_prime_dvd_iff {d : ℕ} (hd : 2 ≤ d) (m q : ℕ+)
    (hq_prime : q.val.Prime) (hm_lt : m.val < q.val) :
    q.val ∣ (ppDilCore hd m q).val ∧
      ∀ p : ℕ, p.Prime → m.val < p → (p ∣ (ppDilCore hd m q).val ↔ p = q.val) := by
  have hcop_m : Nat.Coprime (m.val ^ (d - 1)) q.val :=
    (hq_prime.coprime_iff_not_dvd.mpr fun h ↦
      (not_le.mpr hm_lt) (Nat.le_of_dvd m.property h)).symm.pow_left _
  obtain ⟨c₀, m₀, hm₀, hfac₀⟩ :=
    rfree_factorization (r := d) (by omega) (m.val ^ (d - 1)) (pow_pos m.property (d - 1))
  have hc₀_dvd : c₀.val ∣ m.val ^ (d - 1) := ⟨m₀ ^ d, by linarith⟩
  have hrf_prod : RFree d (c₀.val * q.val) :=
    rfree_mul_of_coprime (by omega) c₀.property (rfree_of_prime hd hq_prime)
      (hcop_m.coprime_dvd_left hc₀_dvd)
  let cProd : Core d := ⟨c₀.val * q.val, hrf_prod⟩
  have huniq := rfree_factor_unique (r := d) (by omega)
    (c₁ := ppDilCore hd m q) (c₂ := cProd)
    (m₁ := ppDilRoot hd m q) (m₂ := m₀)
    (rFreeRoot_pos d (by omega) _) hm₀
    (by
      have h1 : (ppDilRoot hd m q) ^ d * (ppDilCore hd m q).val = m.val ^ (d - 1) * q.val :=
        rFreeRoot_pow_mul_core d (by omega) _
      rw [h1]
      change m.val ^ (d - 1) * q.val = m₀ ^ d * (c₀.val * q.val)
      rw [← mul_assoc, hfac₀])
  have hc_val : (ppDilCore hd m q).val = c₀.val * q.val := congrArg Subtype.val huniq.1
  refine ⟨⟨c₀.val, by rw [hc_val, mul_comm]⟩, fun p hp hm_lt_p ↦ ⟨fun hp_dvd ↦ ?_, ?_⟩⟩
  · rw [hc_val] at hp_dvd
    rcases hp.dvd_mul.mp hp_dvd with hp_c₀ | hp_q
    · have hp_m : p ∣ m.val := hp.dvd_of_dvd_pow (hp_c₀.trans hc₀_dvd)
      exact absurd (Nat.le_of_dvd m.property hp_m) (not_le.mpr hm_lt_p)
    · exact (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hp_q
  · rintro rfl; exact ⟨c₀.val, by rw [hc_val, mul_comm]⟩

/-- **Pure-`ℕ` Block Dominance Lemma for Power-Partition Dilations (`d ≥ 2`)**. -/
private lemma ppDil_block_dominance {d : ℕ} (hd : 2 ≤ d) {A : ℕ} (hA : 0 < A)
    {m₁ m₂ q N : ℕ+} (hdiv₁ : m₁.val ∣ A) (hdiv₂ : m₂.val ∣ A)
    (hq_prime : q.val.Prime) (hq₁ : m₁.val < q.val) (hq₂ : m₂.val < q.val)
    (hm_le : m₂.val ≤ m₁.val) (hcore : ppDilCore hd m₂ N = ppDilCore hd m₁ q) :
    ppDilExp hd A m₁ q ≤ ppDilExp hd A m₂ N ∧
      (ppDilExp hd A m₂ N = ppDilExp hd A m₁ q → m₂ = m₁ ∧ N = q) := by
  have hq_dvd_c : q.val ∣ (ppDilCore hd m₂ N).val := by
    rw [hcore]; exact (ppDilCore_prime_dvd_iff hd m₁ q hq_prime hq₁).1
  have hfac₂ : (ppDilRoot hd m₂ N) ^ d * (ppDilCore hd m₂ N).val = m₂.val ^ (d - 1) * N.val :=
    rFreeRoot_pow_mul_core d (by omega) _
  have hq_dvd_prod : q.val ∣ m₂.val ^ (d - 1) * N.val :=
    hq_dvd_c.trans ⟨(ppDilRoot hd m₂ N) ^ d, by rw [mul_comm (ppDilCore hd m₂ N).val]; exact hfac₂.symm⟩
  have hq_not_m₂ : ¬ q.val ∣ m₂.val := fun h ↦ (not_le.mpr hq₂) (Nat.le_of_dvd m₂.pos h)
  obtain ⟨w, hw_eq⟩ := (hq_prime.dvd_mul.mp hq_dvd_prod).resolve_left
    fun h ↦ hq_not_m₂ (hq_prime.dvd_of_dvd_pow h)
  have hw_pos : 0 < w := by
    by_contra h0
    have hw0 : w = 0 := by omega
    rw [hw0, mul_zero] at hw_eq
    exact N.pos.ne' hw_eq
  have hid₁ := ppDil_nat_identity hd hdiv₁ q
  have hid₂ := ppDil_nat_identity hd hdiv₂ N
  rw [hcore] at hid₂
  have hc_pos : 0 < (ppDilCore hd m₁ q).val := rfree_pos (ppDilCore hd m₁ q).property
  have hpow_eq : m₂.val * (ppDilExp hd A m₂ N) ^ d = m₁.val * (ppDilExp hd A m₁ q) ^ d * w := by
    apply Nat.eq_of_mul_eq_mul_right hc_pos
    calc m₂.val * (ppDilExp hd A m₂ N) ^ d * (ppDilCore hd m₁ q).val
        = A ^ d * N.val := hid₂
      _ = (A ^ d * q.val) * w := by rw [hw_eq]; ring
      _ = (m₁.val * (ppDilExp hd A m₁ q) ^ d * (ppDilCore hd m₁ q).val) * w := by rw [hid₁]
      _ = m₁.val * (ppDilExp hd A m₁ q) ^ d * w * (ppDilCore hd m₁ q).val := by ring
  have hle_pow : (ppDilExp hd A m₁ q) ^ d ≤ (ppDilExp hd A m₂ N) ^ d := by
    apply Nat.le_of_mul_le_mul_left _ m₂.pos
    rw [hpow_eq]
    calc m₂.val * (ppDilExp hd A m₁ q) ^ d
        ≤ m₁.val * (ppDilExp hd A m₁ q) ^ d := Nat.mul_le_mul_right _ hm_le
      _ ≤ m₁.val * (ppDilExp hd A m₁ q) ^ d * w := Nat.le_mul_of_pos_right _ hw_pos
  have hle : ppDilExp hd A m₁ q ≤ ppDilExp hd A m₂ N := by
    by_contra hlt
    have := Nat.pow_lt_pow_left (show ppDilExp hd A m₂ N < ppDilExp hd A m₁ q by omega) (by omega : d ≠ 0)
    omega
  refine ⟨hle, fun heq ↦ ?_⟩
  rw [heq] at hpow_eq
  have he_pos : 0 < (ppDilExp hd A m₁ q) ^ d := pow_pos (ppDilExp_pos hd hA hdiv₁ q) d
  have hmw : m₂.val = m₁.val * w := by
    apply Nat.eq_of_mul_eq_mul_right he_pos
    calc m₂.val * (ppDilExp hd A m₁ q) ^ d = m₁.val * (ppDilExp hd A m₁ q) ^ d * w := hpow_eq
      _ = m₁.val * w * (ppDilExp hd A m₁ q) ^ d := by ring
  have hw1 : w = 1 := by
    have h1 : m₁.val * 1 ≤ m₁.val * w := Nat.mul_le_mul_left _ hw_pos
    have h2 : m₁.val * w ≤ m₁.val * 1 := by rw [← hmw, mul_one]; exact hm_le
    exact Nat.eq_of_mul_eq_mul_left m₁.property (le_antisymm h2 h1)
  exact ⟨PNat.eq (by rw [hmw, hw1, mul_one]), PNat.eq (by rw [hw_eq, hw1, mul_one])⟩

/-- `PowerClass 0`-amplitude half-space tracked expansion for power-partition dilations!
Notice: NO `FiniteParities M` needed — every single amplitude lies in `PowerClass 0`! -/
private structure PPTracked (d : ℕ) (keyRate : (Core d →₀ ℕ) →+ ℂ) where
  Index : Type
  exp : WaveExpansion Index
  finite_window : ∀ R : ℝ, {i : Index | (exp.rate i).re ≤ R}.Finite
  pc0 : ∀ i : Index, PowerClass 0 (exp.amplitude i)
  halfSpace : ∀ i : Index, 0 ≤ ppRotIm d (exp.rate i)
  extreme_range : ∀ i : Index, ppRotIm d (exp.rate i) = 0 →
    ∃ k : Core d →₀ ℕ, exp.rate i = keyRate k

namespace PPTracked

private def ofCoeff {d : ℕ} {keyRate : (Core d →₀ ℕ) →+ ℂ}
    (a : Physical.RayCoefficient) (ha : PowerClass 0 a.value) : PPTracked d keyRate where
  Index := Unit
  exp := a.expansion
  finite_window _ := Set.toFinite _
  pc0 _ := ha
  halfSpace _ := by change 0 ≤ ppRotIm d 0; simp
  extreme_range _ _ := ⟨0, by simp [Physical.RayCoefficient.expansion]⟩

private def add {d : ℕ} {keyRate : (Core d →₀ ℕ) →+ ℂ}
    (a b : PPTracked d keyRate) : PPTracked d keyRate where
  Index := a.Index ⊕ b.Index
  exp := a.exp.add b.exp
  finite_window R := by
    refine (((a.finite_window R).image Sum.inl).union ((b.finite_window R).image Sum.inr)).subset ?_
    rintro (i | j) h
    · exact Or.inl ⟨i, h, rfl⟩
    · exact Or.inr ⟨j, h, rfl⟩
  pc0 := by rintro (i | j); exacts [a.pc0 i, b.pc0 j]
  halfSpace := by rintro (i | j); exacts [a.halfSpace i, b.halfSpace j]
  extreme_range := by rintro (i | j) h; exacts [a.extreme_range i h, b.extreme_range j h]

private def mul {d : ℕ} {keyRate : (Core d →₀ ℕ) →+ ℂ}
    (a b : PPTracked d keyRate) : PPTracked d keyRate where
  Index := a.Index × b.Index
  exp := a.exp.mul b.exp
  finite_window R := by
    refine ((a.finite_window R).prod (b.finite_window R)).subset ?_
    rintro ⟨i, j⟩ h
    change (a.exp.rate i).re + (b.exp.rate j).re ≤ R at h
    exact ⟨(le_add_of_nonneg_right (b.exp.re_nonneg j)).trans h,
      (le_add_of_nonneg_left (a.exp.re_nonneg i)).trans h⟩
  pc0 := fun ⟨i, j⟩ ↦ by
    have h := (a.pc0 i).mul (b.pc0 j); rwa [zero_add] at h
  halfSpace := fun ⟨i, j⟩ ↦ by
    change 0 ≤ ppRotIm d (a.exp.rate i + b.exp.rate j)
    rw [ppRotIm_add]; exact add_nonneg (a.halfSpace i) (b.halfSpace j)
  extreme_range := fun ⟨i, j⟩ h0 ↦ by
    change ppRotIm d (a.exp.rate i + b.exp.rate j) = 0 at h0
    obtain ⟨h1, h2⟩ := (ppExtremeRay_face_iff (a.halfSpace i) (b.halfSpace j)).mp h0
    obtain ⟨k₁, hk₁⟩ := a.extreme_range i h1
    obtain ⟨k₂, hk₂⟩ := b.extreme_range j h2
    exact ⟨k₁ + k₂, by change a.exp.rate i + b.exp.rate j = _; rw [hk₁, hk₂, map_add]⟩

private abbrev Fiber {d : ℕ} {keyRate : (Core d →₀ ℕ) →+ ℂ}
    (e : PPTracked d keyRate) (k : Core d →₀ ℕ) :=
  {i : e.Index // e.exp.rate i = keyRate k}

private noncomputable instance fiberFintype {d : ℕ} {keyRate : (Core d →₀ ℕ) →+ ℂ}
    (e : PPTracked d keyRate) (k : Core d →₀ ℕ) : Fintype (Fiber e k) := by
  apply Set.Finite.fintype (s := {i : e.Index | e.exp.rate i = keyRate k})
  apply (e.finite_window (keyRate k).re).subset
  intro i hi; change (e.exp.rate i).re ≤ _; rw [show e.exp.rate i = keyRate k from hi]

private def marked {d : ℕ} {keyRate : (Core d →₀ ℕ) →+ ℂ}
    (e : PPTracked d keyRate) : MvPowerSeries (Core d) RayGerm :=
  fun k ↦ ∑ i : Fiber e k, Germ.ofFun (e.exp.amplitude i.val)

private theorem separate_zero {d : ℕ} {keyRate : (Core d →₀ ℕ) →+ ℂ}
    (e : PPTracked d keyRate) (hzero : ∀ᶠ x : ℝ in atTop, e.exp.value x = 0) :
    e.marked = 0 := by
  classical
  let padded : Set ℝ := range (fun i ↦ (e.exp.rate i).re) ∪ range (Nat.cast : ℕ → ℝ)
  have padded_fin (R : ℝ) : (padded ∩ Iic R).Finite := by
    obtain ⟨N, hN⟩ := exists_nat_gt R
    refine (((e.finite_window R).image (fun i ↦ (e.exp.rate i).re)).union
      ((Set.finite_le_nat N).image (Nat.cast : ℕ → ℝ))).subset ?_
    rintro x ⟨(⟨i, rfl⟩ | ⟨n, rfl⟩), hx⟩
    · exact Or.inl ⟨i, hx, rfl⟩
    · exact Or.inr ⟨n, by exact_mod_cast (show (n : ℝ) ≤ N from hx.trans hN.le), rfl⟩
  let rank (x : padded) := (padded ∩ Iic (x : ℝ)).ncard
  have hinc : StrictMono rank := by
    intro x y h
    apply Set.ncard_lt_ncard _ (padded_fin _)
    exact Set.ssubset_iff_subset_ne.mpr ⟨inter_subset_inter_right _ (Iic_subset_Iic.mpr h.le),
      fun eqn ↦ (not_le.mpr h)
        ((eqn ▸ (show (y : ℝ) ∈ padded ∩ Iic (y : ℝ) from ⟨y.property, le_rfl⟩) :
          (y : ℝ) ∈ padded ∩ Iic (x : ℝ))).2⟩
  let iso : padded ≃o range rank := hinc.orderIso rank
  have : Infinite padded := Infinite.of_injective
    (fun n : ℕ ↦ (⟨n, Or.inr ⟨n, rfl⟩⟩ : padded))
    (fun _ _ h ↦ Nat.cast_injective (congrArg Subtype.val h))
  let _ : Infinite (range rank) := Infinite.of_injective _ iso.injective
  let enum : ℕ ≃o padded := (Nat.Subtype.orderIsoOfNat _).trans iso.symm
  let w (n : ℕ) : ℝ := enum n
  have hw : StrictMono w := fun _ _ h ↦ enum.strictMono h
  let clusterIdx (i : e.Index) : ℕ := enum.symm ⟨(e.exp.rate i).re, Or.inl ⟨i, rfl⟩⟩
  have hw_idx (i : e.Index) : w (clusterIdx i) = (e.exp.rate i).re := by simp [w, clusterIdx]
  let Freq (n : ℕ) := {y : ℝ // ∃ i : e.Index, (e.exp.rate i).re = w n ∧ -(e.exp.rate i).im = y}
  have (n : ℕ) : Fintype (Freq n) := by
    apply Set.Finite.fintype (s := {y : ℝ | ∃ i : e.Index, (e.exp.rate i).re = w n ∧ -(e.exp.rate i).im = y})
    refine ((e.finite_window (w n)).image (fun i ↦ -(e.exp.rate i).im)).subset ?_
    rintro y ⟨i, hi, rfl⟩; exact ⟨i, hi.le, rfl⟩
  let g (i : e.Index) : Σ n, Freq n := ⟨clusterIdx i, ⟨-(e.exp.rate i).im, i, (hw_idx i).symm, rfl⟩⟩
  have hrate (i : e.Index) : e.exp.rate i = ⟨w (g i).1, -((g i).2 : ℝ)⟩ :=
    Complex.ext (hw_idx i).symm (by simp [g])
  have hasymp (k : Σ n, Freq n) :
      (∀ᶠ x : ℝ in atTop, e.exp.groupAmplitude g k x = 0) ∨
        ∃ v : ℝ, ∃ z : ℂ, z ≠ 0 ∧
          Tendsto (fun x : ℝ ↦ x ^ v • e.exp.groupAmplitude g k x) atTop (𝓝 z) := by
    have hfin : (g ⁻¹' {k}).Finite := (e.finite_window (w k.1)).subset fun i hi ↦ by
      have he : g i = k := hi; change (e.exp.rate i).re ≤ _; rw [hrate i, he]
    let _ := hfin.fintype
    have hpar : FiniteParities 1 (e.exp.groupAmplitude g k) := by
      unfold WaveExpansion.groupAmplitude
      simpa [tsum_fintype] using FiniteParities.finsetSum one_pos Finset.univ
        (fun i : g ⁻¹' {k} ↦ e.exp.amplitude i) (fun i _ ↦ FiniteParities.of_zero one_pos (e.pc0 i))
    exact hpar.leading_dichotomy one_pos
  have hsep := separate_physical_products e.exp g w (fun _ j ↦ j.val) hrate hw
    (fun _ ↦ Subtype.val_injective) hzero hasymp
  apply MvPowerSeries.ext; intro k
  change (∑ i : Fiber e k, Germ.ofFun (e.exp.amplitude i.val)) = 0
  by_cases hex : ∃ i : e.Index, e.exp.rate i = keyRate k
  · obtain ⟨i₀, hi₀⟩ := hex
    have hset : {i : e.Index | e.exp.rate i = keyRate k} = g ⁻¹' {g i₀} := by
      ext i
      simp only [mem_ofPred_eq, mem_preimage, mem_singleton_iff]
      constructor
      · intro hir
        have hre : (e.exp.rate i).re = (e.exp.rate i₀).re := by rw [hir, hi₀]
        have him : -(e.exp.rate i).im = -(e.exp.rate i₀).im := by rw [hir, hi₀]
        have hidx : clusterIdx i = clusterIdx i₀ := hw.injective (by rw [hw_idx, hw_idx, hre])
        exact Sigma.ext hidx ((Subtype.heq_iff_coe_eq (fun y ↦ by simp only [g, hidx])).mpr him)
      · intro hg; rw [hrate i, hg, ← hrate i₀, hi₀]
    have hz := hsep (g i₀).1 (g i₀).2
    let H := Germ.coeRingHom (atTop : Filter ℝ) (R := ℂ)
    change (∑ i : Fiber e k, H (e.exp.amplitude i.val)) = 0
    rw [← map_sum]
    apply Germ.coe_eq.mpr
    filter_upwards [hz] with x hx
    change (∑' j : g ⁻¹' {g i₀}, e.exp.amplitude j x) = 0 at hx
    let _ : Fintype {i : e.Index | e.exp.rate i = keyRate k} := fiberFintype e k
    rw [← tsum_congr_set_coe (fun i ↦ e.exp.amplitude i x) hset, tsum_fintype] at hx
    have hsum_eq : (∑ i : Fiber e k, e.exp.amplitude i.val x) =
        ∑ i : {i : e.Index | e.exp.rate i = keyRate k}, e.exp.amplitude i.val x :=
      Fintype.sum_equiv (Equiv.refl _) _ _ fun _ ↦ rfl
    simpa only [Finset.sum_apply] using hsum_eq.trans hx
  · have : IsEmpty (Fiber e k) := ⟨fun i ↦ hex ⟨i.val, i.property⟩⟩
    simp

private theorem marked_ofCoeff {d : ℕ} {keyRate : (Core d →₀ ℕ) →+ ℂ}
    (a : Physical.RayCoefficient) (ha : PowerClass 0 a.value) (hinj : Function.Injective keyRate) :
    (ofCoeff (d := d) (keyRate := keyRate) a ha).marked = MvPowerSeries.C (Germ.ofFun a.value) := by
  classical
  apply MvPowerSeries.ext; intro k
  rw [MvPowerSeries.coeff_C]
  by_cases hk : k = 0
  · subst hk
    let E : Fiber (ofCoeff (d := d) (keyRate := keyRate) a ha) 0 ≃ Unit :=
      ⟨fun i ↦ i.val, fun u ↦ ⟨u, by simp [ofCoeff, Physical.RayCoefficient.expansion]⟩,
        fun _ ↦ rfl, fun _ ↦ rfl⟩
    change (∑ i : Fiber _ 0, (Germ.ofFun ((ofCoeff a ha).exp.amplitude i.val) : RayGerm)) = _
    rw [Fintype.sum_equiv E
      (fun i : Fiber (ofCoeff (d := d) (keyRate := keyRate) a ha) 0 ↦
        (Germ.ofFun ((ofCoeff (d := d) (keyRate := keyRate) a ha).exp.amplitude i.val) : RayGerm))
      (fun _ ↦ (Germ.ofFun a.value : RayGerm)) (fun _ ↦ rfl)]
    simp
  · have : IsEmpty (Fiber (ofCoeff (d := d) (keyRate := keyRate) a ha) k) :=
      ⟨fun i ↦ hk (hinj ((map_zero keyRate).trans i.property)).symm⟩
    simp [marked, MvPowerSeries.coeff_apply, hk]

private theorem marked_add {d : ℕ} {keyRate : (Core d →₀ ℕ) →+ ℂ}
    (a b : PPTracked d keyRate) : (a.add b).marked = a.marked + b.marked := by
  classical
  apply MvPowerSeries.ext; intro k
  rw [map_add]
  change (∑ i : Fiber (a.add b) k, _) = MvPowerSeries.coeff k a.marked + MvPowerSeries.coeff k b.marked
  let E : Fiber (a.add b) k ≃ Fiber a k ⊕ Fiber b k :=
    { toFun := fun | ⟨.inl j, h⟩ => .inl ⟨j, h⟩ | ⟨.inr j, h⟩ => .inr ⟨j, h⟩
      invFun := fun | .inl j => ⟨.inl j.val, j.property⟩ | .inr j => ⟨.inr j.val, j.property⟩
      left_inv := by rintro ⟨(j | j), h⟩ <;> rfl
      right_inv := by rintro (j | j) <;> rfl }
  rw [Fintype.sum_equiv E _
      (Sum.elim (fun i : Fiber a k ↦ (Germ.ofFun (a.exp.amplitude i.val) : RayGerm))
        (fun i : Fiber b k ↦ (Germ.ofFun (b.exp.amplitude i.val) : RayGerm)))
      (by rintro ⟨(j | j), h⟩ <;> rfl), Fintype.sum_sum_type]
  rfl

private theorem marked_mul {d : ℕ} {keyRate : (Core d →₀ ℕ) →+ ℂ}
    (a b : PPTracked d keyRate) (hinj : Function.Injective keyRate)
    (hface : ∀ k, ppRotIm d (keyRate k) = 0) :
    (a.mul b).marked = a.marked * b.marked := by
  classical
  apply MvPowerSeries.ext; intro k
  rw [MvPowerSeries.coeff_mul, ← Finset.sum_coe_sort]
  have hsplit : ∀ i : Fiber (a.mul b) k,
      ∃ d₁ d₂ : Core d →₀ ℕ, d₁ + d₂ = k ∧ a.exp.rate i.val.1 = keyRate d₁ ∧
        b.exp.rate i.val.2 = keyRate d₂ := fun i ↦ by
    have hrate : a.exp.rate i.val.1 + b.exp.rate i.val.2 = keyRate k := i.property
    have hrot : ppRotIm d (a.exp.rate i.val.1 + b.exp.rate i.val.2) = 0 := by rw [hrate]; exact hface k
    obtain ⟨h1, h2⟩ := (ppExtremeRay_face_iff (a.halfSpace i.val.1) (b.halfSpace i.val.2)).mp hrot
    obtain ⟨d₁, hd₁⟩ := a.extreme_range i.val.1 h1
    obtain ⟨d₂, hd₂⟩ := b.extreme_range i.val.2 h2
    exact ⟨d₁, d₂, hinj (by rw [map_add, ← hd₁, ← hd₂, hrate]), hd₁, hd₂⟩
  choose d₁ d₂ hsum hd₁ hd₂ using hsplit
  let E : Fiber (a.mul b) k ≃
      (Σ p : ↥(Finset.antidiagonal k), Fiber a p.val.1 × Fiber b p.val.2) :=
    { toFun := fun i ↦ ⟨⟨(d₁ i, d₂ i), Finset.mem_antidiagonal.mpr (hsum i)⟩,
        ⟨i.val.1, hd₁ i⟩, ⟨i.val.2, hd₂ i⟩⟩
      invFun := fun ⟨p, i, j⟩ ↦ ⟨(i.val, j.val), by
        change a.exp.rate i.val + b.exp.rate j.val = keyRate k
        rw [i.property, j.property, ← map_add, Finset.mem_antidiagonal.mp p.property]⟩
      left_inv := fun _ ↦ rfl
      right_inv := by
        rintro ⟨⟨⟨s₁, s₂⟩, hp⟩, ⟨i, hi⟩, ⟨j, hj⟩⟩
        let u : Fiber (a.mul b) k := ⟨(i, j), by
          change a.exp.rate i + b.exp.rate j = keyRate k
          rw [hi, hj, ← map_add, Finset.mem_antidiagonal.mp hp]⟩
        have hs₁ : d₁ u = s₁ := hinj ((hd₁ u).symm.trans hi)
        have hs₂ : d₂ u = s₂ := hinj ((hd₂ u).symm.trans hj)
        have hp_eq : (⟨(d₁ u, d₂ u), Finset.mem_antidiagonal.mpr (hsum u)⟩ : ↥(Finset.antidiagonal k)) =
            ⟨(s₁, s₂), hp⟩ := Subtype.ext (Prod.ext hs₁ hs₂)
        have hpair : HEq
            ((⟨i, hd₁ u⟩, ⟨j, hd₂ u⟩) : Fiber a (d₁ u) × Fiber b (d₂ u))
            ((⟨i, hi⟩, ⟨j, hj⟩) : Fiber a s₁ × Fiber b s₂) := by
          have aux : ∀ (t₁ t₂ : Core d →₀ ℕ) (ht₁ : a.exp.rate i = keyRate t₁)
              (ht₂ : b.exp.rate j = keyRate t₂), t₁ = s₁ → t₂ = s₂ →
              HEq ((⟨i, ht₁⟩, ⟨j, ht₂⟩) : Fiber a t₁ × Fiber b t₂)
                ((⟨i, hi⟩, ⟨j, hj⟩) : Fiber a s₁ × Fiber b s₂) := by
            rintro _ _ _ _ rfl rfl; rfl
          exact aux (d₁ u) (d₂ u) (hd₁ u) (hd₂ u) hs₁ hs₂
        exact Sigma.ext hp_eq hpair }
  change (∑ i : Fiber (a.mul b) k, (Germ.ofFun ((a.mul b).exp.amplitude i.val) : RayGerm)) = _
  rw [Fintype.sum_equiv E
      (fun i : Fiber (a.mul b) k ↦ (Germ.ofFun ((a.mul b).exp.amplitude i.val) : RayGerm))
      (fun x ↦ (Germ.ofFun (a.exp.amplitude x.2.1.val) : RayGerm) *
        (Germ.ofFun (b.exp.amplitude x.2.2.val) : RayGerm)) (fun _ ↦ rfl),
      Fintype.sum_sigma]
  apply Finset.sum_congr rfl; intro p _
  rw [Fintype.sum_prod_type]
  simp [marked, MvPowerSeries.coeff_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

end PPTracked

/-- Exact `ℓ`-th `X`-derivative of `X^{d + 1} · exp(-r X)`:
`∑_{t = 0}^ℓ C(ℓ, t) · (d + 1).descFactorial t · X^{d + 1 - t} · (-r)^{ℓ - t} · exp(-r X)`. -/
private def ppDilAmp (d : ℕ) (σ : ℝ) (r : ℂ) (ℓ : ℕ) (X : ℝ) : ℂ :=
  ((d : ℂ)⁻¹ * ((σ : ℂ) ^ (d + 1))) *
    ∑ t ∈ Finset.range (ℓ + 1),
      ((Nat.choose ℓ t * (d + 1).descFactorial t : ℕ) : ℂ) *
        (if t ≤ d + 1 then (X : ℂ) ^ (d + 1 - t) else 0) * (-(((σ : ℝ) : ℂ) * r)) ^ (ℓ - t)

private lemma ppDilAmp_deriv (d : ℕ) (σ : ℝ) (r : ℂ) (ℓ : ℕ) (X : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Complex.exp (-(((σ : ℝ) : ℂ) * r) * (y : ℂ)) * ppDilAmp d σ r ℓ y)
      (Complex.exp (-(((σ : ℝ) : ℂ) * r) * (X : ℂ)) * ppDilAmp d σ r (ℓ + 1) X) X := by
  let lam : ℂ := ((σ : ℝ) : ℂ) * r
  let f (y : ℝ) : ℂ := ((d : ℂ)⁻¹ * ((σ : ℂ) ^ (d + 1))) * (y : ℂ) ^ (d + 1)
  let g (y : ℝ) : ℂ := Complex.exp (-lam * (y : ℂ))
  have hf_iter (k : ℕ) (y : ℝ) :
      iteratedDeriv k f y = ((d : ℂ)⁻¹ * ((σ : ℂ) ^ (d + 1))) *
        (((d + 1).descFactorial k : ℕ) : ℂ) * (if k ≤ d + 1 then (y : ℂ) ^ (d + 1 - k) else 0) := by
    have hpow (m k : ℕ) (y : ℝ) :
        iteratedDeriv k (fun z : ℝ ↦ (z : ℂ) ^ m) y =
          ((m.descFactorial k : ℕ) : ℂ) * (if k ≤ m then (y : ℂ) ^ (m - k) else 0) := by
      induction k generalizing y with
      | zero => simp
      | succ k ih =>
        rw [iteratedDeriv_succ, show iteratedDeriv k (fun z : ℝ ↦ (z : ℂ) ^ m) =
          fun z : ℝ ↦ ((m.descFactorial k : ℕ) : ℂ) * (if k ≤ m then (z : ℂ) ^ (m - k) else 0) from funext ih]
        by_cases hk : k + 1 ≤ m
        · have hk' : k ≤ m := by omega
          simp only [hk', hk, ↓reduceIte]
          have hd : HasDerivAt (fun z : ℝ ↦ ((m.descFactorial k : ℕ) : ℂ) * (z : ℂ) ^ (m - k))
              (((m.descFactorial k : ℕ) : ℂ) * (((m - k : ℕ) : ℂ) * (y : ℂ) ^ (m - k - 1))) y := by
            have h1 := ((Complex.ofRealCLM.hasDerivAt (x := y)).pow (m - k)).const_mul
              ((m.descFactorial k : ℕ) : ℂ)
            simpa [mul_one] using h1
          rw [hd.deriv, Nat.descFactorial_succ, show m - (k + 1) = m - k - 1 by omega]
          push_cast; ring
        · by_cases hk' : k ≤ m
          · have hkm : k = m := by omega
            subst k
            simp only [le_refl, ↓reduceIte, Nat.sub_self, pow_zero, mul_one, show ¬ m + 1 ≤ m by omega,
              deriv_const', mul_zero]
          · simp only [hk', hk, ↓reduceIte, mul_zero, deriv_const']
    change iteratedDeriv k (fun z : ℝ ↦ ((d : ℂ)⁻¹ * ((σ : ℂ) ^ (d + 1))) * (z : ℂ) ^ (d + 1)) y = _
    rw [iteratedDeriv_const_mul_field, hpow (d + 1) k y]; ring
  have hg_iter (k : ℕ) (y : ℝ) :
      iteratedDeriv k g y = (-lam) ^ k * Complex.exp (-lam * (y : ℂ)) := by
    induction k generalizing y with
    | zero => simp [g]
    | succ k ih =>
      rw [iteratedDeriv_succ, show iteratedDeriv k g = fun z : ℝ ↦ (-lam) ^ k * Complex.exp (-lam * (z : ℂ)) from funext ih]
      have hd : HasDerivAt (fun z : ℝ ↦ (-lam) ^ k * Complex.exp (-lam * (z : ℂ)))
          ((-lam) ^ (k + 1) * Complex.exp (-lam * (y : ℂ))) y := by
        have hlin : HasDerivAt (fun z : ℝ ↦ (-lam) * (z : ℂ)) (-lam) y := by
          simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).const_mul (-lam)
        convert (hlin.cexp).const_mul ((-lam) ^ k) using 1
        rw [pow_succ]; ring
      exact hd.deriv
  have hleib (k : ℕ) (y : ℝ) :
      iteratedDeriv k (fun z : ℝ ↦ f z * g z) y =
        Complex.exp (-lam * (y : ℂ)) * ppDilAmp d σ r k y := by
    have hcf : ContDiff ℝ k f := contDiff_const.mul (Complex.ofRealCLM.contDiff.pow (d + 1))
    have hcg : ContDiff ℝ k g := (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
    rw [iteratedDeriv_fun_mul hcf.contDiffAt hcg.contDiffAt]
    simp only [ppDilAmp, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro t _
    rw [hf_iter t y, hg_iter (k - t) y]
    push_cast; dsimp [lam]; ring
  have hd_leib : HasDerivAt (iteratedDeriv ℓ (fun z : ℝ ↦ f z * g z))
      (iteratedDeriv (ℓ + 1) (fun z : ℝ ↦ f z * g z) X) X := by
    have hcf : ContDiff ℝ (ℓ + 1) f := contDiff_const.mul (Complex.ofRealCLM.contDiff.pow (d + 1))
    have hcg : ContDiff ℝ (ℓ + 1) g := (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
    rw [iteratedDeriv_succ]
    exact ((hcf.mul hcg).differentiable_iteratedDeriv ℓ (by exact_mod_cast Nat.lt_succ_self ℓ) X).hasDerivAt
  rw [show iteratedDeriv ℓ (fun z : ℝ ↦ f z * g z) =
      fun y : ℝ ↦ Complex.exp (-lam * (y : ℂ)) * ppDilAmp d σ r ℓ y from funext (hleib ℓ),
      hleib (ℓ + 1) X] at hd_leib
  exact hd_leib

private lemma ppDilAmp_powerClass (d : ℕ) (σ : ℝ) (r : ℂ) (ℓ : ℕ) :
    PowerClass 0 (ppDilAmp d σ r ℓ) := by
  have hterm (t : ℕ) : PowerClass 0 (fun X : ℝ ↦
      ((d : ℂ)⁻¹ * ((σ : ℂ) ^ (d + 1))) *
        (((Nat.choose ℓ t * (d + 1).descFactorial t : ℕ) : ℂ) *
          (if t ≤ d + 1 then (X : ℂ) ^ (d + 1 - t) else 0) * (-(((σ : ℝ) : ℂ) * r)) ^ (ℓ - t))) := by
    by_cases ht : t ≤ d + 1
    · simp only [ht, ↓reduceIte]
      have hpow : PowerClass 0 (fun X : ℝ ↦ (X : ℂ) ^ (d + 1 - t)) := by
        refine ⟨(d + 1 - t : ℕ), fun _ ↦ 1, RayDensity.const 1, ?_⟩
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
        have h1 : raySum (fun _ ↦ (1 : ℂ)) X = 1 := by
          simp only [raySum, integral_smul_const, integral_exp_neg_Ioi_zero, one_smul]
        simp [h1, Complex.real_smul, Real.rpow_natCast]
      have hconst := PowerClass.const (((d : ℂ)⁻¹ * ((σ : ℂ) ^ (d + 1))) *
        (((Nat.choose ℓ t * (d + 1).descFactorial t : ℕ) : ℂ) * (-(((σ : ℝ) : ℂ) * r)) ^ (ℓ - t)))
      have hm := hconst.mul hpow
      rw [zero_add] at hm
      exact hm.congr (Eventually.of_forall fun X ↦ by ring)
    · simp only [ht, ↓reduceIte, mul_zero, zero_mul]
      exact PowerClass.const 0
  have hsum : ∀ S : Finset ℕ, PowerClass 0 (fun X : ℝ ↦
      ∑ t ∈ S, ((d : ℂ)⁻¹ * ((σ : ℂ) ^ (d + 1))) *
        (((Nat.choose ℓ t * (d + 1).descFactorial t : ℕ) : ℂ) *
          (if t ≤ d + 1 then (X : ℂ) ^ (d + 1 - t) else 0) * (-(((σ : ℝ) : ℂ) * r)) ^ (ℓ - t))) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using PowerClass.const 0
    | @insert a S ha ih =>
      simpa [Finset.sum_insert ha] using (hterm a).add ih
  exact (hsum (Finset.range (ℓ + 1))).congr (Eventually.of_forall fun X ↦ by
    simp only [ppDilAmp, Finset.mul_sum])

private lemma ppDilAmp_limit (d : ℕ) (σ : ℝ) (r : ℂ) (ℓ : ℕ) :
    Tendsto (fun X : ℝ ↦ ((X ^ (-((d + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * ppDilAmp d σ r ℓ X)
      atTop (𝓝 (((d : ℂ)⁻¹ * ((σ : ℂ) ^ (d + 1))) * (-(((σ : ℝ) : ℂ) * r)) ^ ℓ)) := by
  have hterm (t : ℕ) (ht : t ∈ Finset.range (ℓ + 1)) :
      Tendsto (fun X : ℝ ↦ ((X ^ (-((d + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
        (((Nat.choose ℓ t * (d + 1).descFactorial t : ℕ) : ℂ) *
          (if t ≤ d + 1 then (X : ℂ) ^ (d + 1 - t) else 0) * (-(((σ : ℝ) : ℂ) * r)) ^ (ℓ - t)))
      atTop (𝓝 (if t = 0 then (-(((σ : ℝ) : ℂ) * r)) ^ ℓ else 0)) := by
    by_cases ht0 : t = 0
    · subst ht0
      simp only [↓reduceIte, Nat.choose_zero_right, Nat.descFactorial_zero, mul_one, Nat.cast_one,
        Nat.zero_le, Nat.sub_zero, one_mul]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      have hX0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
      rw [Real.rpow_neg hX.le, Real.rpow_natCast, Complex.ofReal_inv, Complex.ofReal_pow]
      field_simp [hX0]
    · simp only [ht0, ↓reduceIte]
      by_cases htle : t ≤ d + 1
      · simp only [htle, ↓reduceIte]
        have hpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ht0
        have hdec : Tendsto (fun X : ℝ ↦ ((X ^ (-(t : ℝ)) : ℝ) : ℂ)) atTop (𝓝 0) :=
          (Complex.continuous_ofReal.tendsto 0).comp (tendsto_rpow_neg_atTop hpos)
        have hmul := (hdec.const_mul (((Nat.choose ℓ t * (d + 1).descFactorial t : ℕ) : ℂ) *
          (-(((σ : ℝ) : ℂ) * r)) ^ (ℓ - t)))
        rw [mul_zero] at hmul
        refine hmul.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
        have hpow : ((X ^ (-((d + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * (X : ℂ) ^ (d + 1 - t) =
            ((X ^ (-(t : ℝ)) : ℝ) : ℂ) := by
          rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Real.rpow_natCast X (d + 1 - t),
              ← Real.rpow_add hX]
          congr 2; have : ((d + 1 - t : ℕ) : ℝ) = ((d + 1 : ℕ) : ℝ) - (t : ℝ) := Nat.cast_sub htle
          linarith
        linear_combination (((Nat.choose ℓ t * (d + 1).descFactorial t : ℕ) : ℂ) *
          (-(((σ : ℝ) : ℂ) * r)) ^ (ℓ - t)) * hpow.symm
      · simp only [htle, ↓reduceIte, mul_zero, zero_mul]
        exact tendsto_const_nhds
  have hsum := tendsto_finsetSum (Finset.range (ℓ + 1)) hterm
  rw [Finset.sum_ite_eq' (Finset.range (ℓ + 1)) 0] at hsum
  simp only [Finset.mem_range.mpr (Nat.succ_pos ℓ), ↓reduceIte] at hsum
  have hmul := hsum.const_mul ((d : ℂ)⁻¹ * ((σ : ℂ) ^ (d + 1)))
  refine hmul.congr fun X ↦ ?_
  simp only [ppDilAmp, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro t _; ring

/-- Scaled wave expansion for `iteratedDeriv ℓ` of `d⁻¹ (σ X)^{d+1} H̃_d(σ X)`. -/
private def ppDilWaveExp (d : ℕ) (hd : 2 ≤ d) (σ : ℝ) (hσ : 0 < σ) (ℓ : ℕ) :
    WaveExpansion (Fin d × ℕ+) where
  rate := fun ℓN ↦ ((σ : ℝ) : ℂ) * ppWaveRate d ℓN.1 ℓN.2
  amplitude := fun ℓN X ↦
    (-((powerPartMult d ℓN.2.val : ℝ) : ℂ) * ppWaveRate d ℓN.1 ℓN.2) *
      ppDilAmp d σ (ppWaveRate d ℓN.1 ℓN.2) ℓ X
  budget := fun ℓN ↦
    (‖-((powerPartMult d ℓN.2.val : ℝ) : ℂ) * ppWaveRate d ℓN.1 ℓN.2‖ *
      (‖(d : ℂ)⁻¹ * ((σ : ℂ) ^ (d + 1))‖ *
        ∑ t ∈ Finset.range (ℓ + 1),
          ((Nat.choose ℓ t * (d + 1).descFactorial t : ℕ) : ℝ) *
            (σ * ‖ppWaveRate d ℓN.1 ℓN.2‖) ^ (ℓ - t))) *
      Real.exp (-(σ * (ppWaveRate d ℓN.1 ℓN.2).re))
  loss := d + 1
  re_nonneg := fun ℓN ↦ by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hσ.le (ppWaveRate_re_pos hd ℓN.1 ℓN.2).le
  budget_nonneg := fun ℓN ↦
    mul_nonneg (mul_nonneg (norm_nonneg _)
      (mul_nonneg (norm_nonneg _)
        (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _)
          (pow_nonneg (mul_nonneg hσ.le (norm_nonneg _)) _))))
      (Real.exp_nonneg _)
  summable_budget := by
    rw [← (Equiv.sigmaEquivProd (Fin d) ℕ+).summable_iff]
    refine (summable_sigma_of_nonneg fun ℓN ↦
      mul_nonneg (mul_nonneg (norm_nonneg _)
        (mul_nonneg (norm_nonneg _)
          (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _)
            (pow_nonneg (mul_nonneg hσ.le (norm_nonneg _)) _))))
        (Real.exp_nonneg _)).mpr ⟨fun j ↦ ?_, hasSum_fintype _ |>.summable⟩
    have hc : 0 < σ * (ppRay d j.val).re := mul_pos hσ (ppRay_re_pos hd j.isLt)
    let Ksum : ℝ := ∑ t ∈ Finset.range (ℓ + 1),
      ((Nat.choose ℓ t * (d + 1).descFactorial t : ℕ) : ℝ) * (1 + σ * ‖ppRay d j.val‖) ^ ℓ
    let C : ℝ := ‖ppRay d j.val‖ * (‖(d : ℂ)⁻¹ * ((σ : ℂ) ^ (d + 1))‖ * Ksum)
    have hdom := (summable_pow_mul_exp_neg_rpow hd hc (ℓ + 2)).mul_left C
    refine Summable.of_nonneg_of_le (fun N ↦
      mul_nonneg (mul_nonneg (norm_nonneg _)
        (mul_nonneg (norm_nonneg _)
          (Finset.sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _)
            (pow_nonneg (mul_nonneg hσ.le (norm_nonneg _)) _))))
        (Real.exp_nonneg _)) (fun N ↦ ?_) hdom
    have hN1 : (1 : ℝ) ≤ (N.val : ℝ) := by exact_mod_cast N.property
    have hrpow_le : (N.val : ℝ) ^ (1 / (d : ℝ)) ≤ (N.val : ℝ) := by
      have h1 : 1 / (d : ℝ) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast (show 0 < d by omega))]; exact_mod_cast (show 1 ≤ d by omega)
      simpa using Real.rpow_le_rpow_of_exponent_le hN1 h1
    have hnorm_rate : ‖ppWaveRate d j N‖ ≤ ‖ppRay d j.val‖ * (N.val : ℝ) := by
      rw [ppWaveRate, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (by positivity) _), mul_comm]
      exact mul_le_mul_of_nonneg_left hrpow_le (norm_nonneg _)
    have hpref : ‖-((powerPartMult d N.val : ℝ) : ℂ) * ppWaveRate d j N‖ ≤
        ‖ppRay d j.val‖ * (N.val : ℝ) ^ 2 := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (powerPartMult_nonneg d N.val)]
      calc powerPartMult d N.val * ‖ppWaveRate d j N‖
          ≤ (N.val : ℝ) * (‖ppRay d j.val‖ * (N.val : ℝ)) :=
            mul_le_mul (powerPartMult_le_self d N.val) hnorm_rate (norm_nonneg _) (by positivity)
        _ = ‖ppRay d j.val‖ * (N.val : ℝ) ^ 2 := by ring
    have hsum_le : (∑ t ∈ Finset.range (ℓ + 1),
          ((Nat.choose ℓ t * (d + 1).descFactorial t : ℕ) : ℝ) *
            (σ * ‖ppWaveRate d j N‖) ^ (ℓ - t)) ≤ Ksum * (N.val : ℝ) ^ ℓ := by
      dsimp only [Ksum]; rw [Finset.sum_mul]
      apply Finset.sum_le_sum; intro t _
      have h1 : σ * ‖ppWaveRate d j N‖ ≤ (1 + σ * ‖ppRay d j.val‖) * (N.val : ℝ) := by
        have := mul_le_mul_of_nonneg_left hnorm_rate hσ.le
        nlinarith [norm_nonneg (ppRay d j.val)]
      have h2 : (σ * ‖ppWaveRate d j N‖) ^ (ℓ - t) ≤
          (1 + σ * ‖ppRay d j.val‖) ^ ℓ * (N.val : ℝ) ^ ℓ := by
        calc (σ * ‖ppWaveRate d j N‖) ^ (ℓ - t)
            ≤ ((1 + σ * ‖ppRay d j.val‖) * (N.val : ℝ)) ^ (ℓ - t) :=
              pow_le_pow_left₀ (by positivity) h1 _
          _ ≤ ((1 + σ * ‖ppRay d j.val‖) * (N.val : ℝ)) ^ ℓ :=
              pow_le_pow_right₀ (by nlinarith [mul_nonneg hσ.le (norm_nonneg (ppRay d j.val))])
                (Nat.sub_le ℓ t)
          _ = (1 + σ * ‖ppRay d j.val‖) ^ ℓ * (N.val : ℝ) ^ ℓ := mul_pow ..
      calc _ ≤ ((Nat.choose ℓ t * (d + 1).descFactorial t : ℕ) : ℝ) *
              ((1 + σ * ‖ppRay d j.val‖) ^ ℓ * (N.val : ℝ) ^ ℓ) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = _ := by ring
    have hre : -(σ * (ppWaveRate d j N).re) = -(σ * (ppRay d j.val).re) * (N.val : ℝ) ^ (1 / (d : ℝ)) := by
      simp [ppWaveRate, Complex.mul_re]; ring
    simp only [Equiv.sigmaEquivProd_apply]
    rw [hre]
    calc _ ≤ (‖ppRay d j.val‖ * (N.val : ℝ) ^ 2 *
            (‖(d : ℂ)⁻¹ * ((σ : ℂ) ^ (d + 1))‖ * (Ksum * (N.val : ℝ) ^ ℓ))) *
          Real.exp (-(σ * (ppRay d j.val).re) * (N.val : ℝ) ^ (1 / (d : ℝ))) := by gcongr
      _ = C * ((N.val : ℝ) ^ (ℓ + 2) *
          Real.exp (-(σ * (ppRay d j.val).re) * (N.val : ℝ) ^ (1 / (d : ℝ)))) := by
          dsimp [C]; rw [pow_add]; ring
  bound := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX ℓN
    have hre_eq : (((σ : ℝ) : ℂ) * ppWaveRate d ℓN.1 ℓN.2).re = σ * (ppWaveRate d ℓN.1 ℓN.2).re := by
      simp [Complex.mul_re]
    have hcancel_rhs : ∀ A : ℝ,
        A * Real.exp (-(σ * (ppWaveRate d ℓN.1 ℓN.2).re)) *
          Real.exp (σ * (ppWaveRate d ℓN.1 ℓN.2).re) * X ^ (d + 1) = A * X ^ (d + 1) := fun A ↦ by
      rw [mul_assoc A, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    rw [hre_eq, hcancel_rhs, norm_mul, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    unfold ppDilAmp
    rw [norm_mul, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc ‖∑ t ∈ Finset.range (ℓ + 1),
            ((Nat.choose ℓ t * (d + 1).descFactorial t : ℕ) : ℂ) *
              (if t ≤ d + 1 then (X : ℂ) ^ (d + 1 - t) else 0) *
                (-(((σ : ℝ) : ℂ) * ppWaveRate d ℓN.1 ℓN.2)) ^ (ℓ - t)‖
        ≤ ∑ t ∈ Finset.range (ℓ + 1),
            ‖((Nat.choose ℓ t * (d + 1).descFactorial t : ℕ) : ℂ) *
              (if t ≤ d + 1 then (X : ℂ) ^ (d + 1 - t) else 0) *
                (-(((σ : ℝ) : ℂ) * ppWaveRate d ℓN.1 ℓN.2)) ^ (ℓ - t)‖ := norm_sum_le _ _
      _ ≤ ∑ t ∈ Finset.range (ℓ + 1),
            ((Nat.choose ℓ t * (d + 1).descFactorial t : ℕ) : ℝ) *
              (σ * ‖ppWaveRate d ℓN.1 ℓN.2‖) ^ (ℓ - t) * X ^ (d + 1) := by
          apply Finset.sum_le_sum; intro t _
          rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow, norm_neg, norm_mul,
              Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ]
          split_ifs with ht
          · rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans_le hX)]
            have hpow : X ^ (d + 1 - t) ≤ X ^ (d + 1) := pow_le_pow_right₀ hX (Nat.sub_le _ _)
            calc _ = ((Nat.choose ℓ t * (d + 1).descFactorial t : ℕ) : ℝ) *
                    (σ * ‖ppWaveRate d ℓN.1 ℓN.2‖) ^ (ℓ - t) * X ^ (d + 1 - t) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
          · simp; positivity
      _ = _ := (Finset.sum_mul _ _ _).symm

private lemma ppDilWaveExp_value_zero {d : ℕ} (hd : 2 ≤ d) (σ : ℝ) (hσ : 0 < σ) :
    ∀ᶠ X : ℝ in atTop,
      (ppDilWaveExp d hd σ hσ 0).value X =
        ((d : ℂ)⁻¹ * (((σ * X : ℝ) : ℂ) ^ (d + 1))) * (ppWaveJet d hd 0).value (σ * X) := by
  filter_upwards [(ppDilWaveExp d hd σ hσ 0).norm_summable,
    (tendsto_id.const_mul_atTop hσ).eventually (ppWaveJet d hd 0).norm_summable] with X _ _
  unfold WaveExpansion.value
  rw [← tsum_mul_left]
  apply tsum_congr; intro ℓN
  simp only [WaveExpansion.term, ppDilWaveExp, ppWaveJet, ppDilAmp, Nat.zero_add, Finset.range_one,
    Finset.sum_singleton, Nat.choose_zero_right, Nat.descFactorial_zero, mul_one, Nat.cast_one,
    Nat.zero_le, ↓reduceIte, Nat.sub_zero, pow_zero, one_mul, Complex.ofReal_mul, mul_pow]
  have hexp : -(((σ : ℝ) : ℂ) * ppWaveRate d ℓN.1 ℓN.2) * (X : ℂ) =
      -ppWaveRate d ℓN.1 ℓN.2 * ((σ : ℂ) * (X : ℂ)) := by ring
  rw [hexp]; ring

private lemma ppDilWaveExp_derivatives {d : ℕ} (hd : 2 ≤ d) (σ : ℝ) (hσ : 0 < σ) (ℓ : ℕ) :
    iteratedDeriv ℓ (ppDilWaveExp d hd σ hσ 0).value =ᶠ[atTop] (ppDilWaveExp d hd σ hσ ℓ).value := by
  apply WaveExpansion.iteratedDeriv_value (ppDilWaveExp d hd σ hσ)
  intro k
  filter_upwards with X ℓN
  have hd_a := (ppDilAmp_deriv d σ (ppWaveRate d ℓN.1 ℓN.2) k X).const_mul
    (-((powerPartMult d ℓN.2.val : ℝ) : ℂ) * ppWaveRate d ℓN.1 ℓN.2)
  convert hd_a using 1
  · funext y; simp only [WaveExpansion.term, ppDilWaveExp]; ring
  · simp only [WaveExpansion.term, ppDilWaveExp]; ring

private def ppFall (e : ℤ) (c : ℂ) : ℕ → ℂ
  | 0 => c
  | m + 1 => ppFall e c m * (((e : ℝ) - (m : ℝ) : ℝ) : ℂ)

private lemma ppIteratedDeriv_zero_fun (ℓ : ℕ) :
    iteratedDeriv ℓ (fun _ : ℝ ↦ (0 : ℂ)) = fun _ : ℝ ↦ (0 : ℂ) := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    ext X
    rw [iteratedDeriv_succ, ih, deriv_const']

private lemma ppDilPolar_props {d : ℕ} (hd : 2 ≤ d) (P : PowerPartStokesProfile d hd)
    (σ : ℝ) (ℓ : ℕ) :
    let pol (X : ℝ) : ℂ := ((d : ℂ)⁻¹ * (((σ * X : ℝ) : ℂ) ^ (d + 1))) *
      P.polarPoly.eval ((((σ * X : ℝ) : ℂ))⁻¹)
    PowerClass 0 (iteratedDeriv ℓ pol) ∧
      ∃ (B : ℝ) (L : ℕ), 0 ≤ B ∧ ∀ᶠ X : ℝ in atTop, ‖iteratedDeriv ℓ pol X‖ ≤ B * X ^ L := by
  intro pol
  have hmon (k : ℕ) (c : ℂ) :
      let f (X : ℝ) : ℂ := c * (X : ℂ) ^ (d + 1) * ((X : ℂ)⁻¹) ^ k
      PowerClass 0 (iteratedDeriv ℓ f) ∧
      ∃ (B : ℝ) (L : ℕ), 0 ≤ B ∧ ∀ᶠ X : ℝ in atTop, ‖iteratedDeriv ℓ f X‖ ≤ B * X ^ L := by
    intro f
    let e : ℤ := (d + 1 : ℤ) - (k : ℤ)
    have hf_eq : ∀ X > 0, f X = c * ((X ^ (e : ℝ) : ℝ) : ℂ) := fun X hX ↦ by
      dsimp only [f, e]
      rw [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_natCast,
          Real.rpow_sub hX, ← Nat.cast_add_one, Real.rpow_natCast, Real.rpow_natCast,
          Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_pow, inv_pow,
          div_eq_mul_inv, mul_assoc]
    have hiter (m : ℕ) : ∀ X > 0, iteratedDeriv m f X =
        ppFall e c m * ((X ^ ((e : ℝ) - (m : ℝ)) : ℝ) : ℂ) := by
      induction m with
      | zero =>
        intro X hX
        simp only [iteratedDeriv_zero, ppFall, Nat.cast_zero, sub_zero]
        exact hf_eq X hX
      | succ m ih =>
        intro X hX
        rw [iteratedDeriv_succ]
        have hnear : iteratedDeriv m f =ᶠ[𝓝 X]
            fun y ↦ ppFall e c m * ((y ^ ((e : ℝ) - (m : ℝ)) : ℝ) : ℂ) :=
          (lt_mem_nhds hX).mono fun y hy ↦ ih y hy
        rw [hnear.deriv_eq]
        have hd1 := ((Real.hasDerivAt_rpow_const (x := X) (p := (e : ℝ) - (m : ℝ))
          (Or.inl hX.ne')).ofReal_comp).const_mul (ppFall e c m)
        rw [hd1.deriv, ppFall, Nat.cast_add, Nat.cast_one,
            show (e : ℝ) - (m : ℝ) - 1 = (e : ℝ) - ((m : ℝ) + 1) by ring]
        push_cast; ring
    constructor
    · refine ⟨e - (ℓ : ℤ), fun _ ↦ ppFall e c ℓ, RayDensity.const _, ?_⟩
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      have h1 : raySum (fun _ ↦ ppFall e c ℓ) X = ppFall e c ℓ := by
        simp only [raySum, integral_smul_const, integral_exp_neg_Ioi_zero, one_smul]
      rw [hiter ℓ X hX, h1, zero_add, Complex.real_smul, mul_comm]
      push_cast; rfl
    · refine ⟨‖ppFall e c ℓ‖, d + 1, norm_nonneg _, ?_⟩
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
      have hX0 : 0 < X := zero_lt_one.trans_le hX
      rw [hiter ℓ X hX0, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg hX0.le _)]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hle : (e : ℝ) - (ℓ : ℝ) ≤ ((d + 1 : ℕ) : ℝ) := by
        dsimp [e]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) ℓ]
      have hr := Real.rpow_le_rpow_of_exponent_le hX hle
      rwa [Real.rpow_natCast] at hr
  have hpol_eq : pol = fun X : ℝ ↦ ∑ k ∈ P.polarPoly.support,
      (((d : ℂ)⁻¹ * (σ : ℂ) ^ (d + 1) * P.polarPoly.coeff k * ((σ : ℂ)⁻¹) ^ k) *
        (X : ℂ) ^ (d + 1) * ((X : ℂ)⁻¹) ^ k) := by
    funext X
    dsimp only [pol]
    rw [Polynomial.eval_eq_sum, Polynomial.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [Complex.ofReal_mul, mul_pow, mul_inv, mul_pow]
    ring
  have hsum_rec : ∀ S : Finset ℕ,
      let f (X : ℝ) : ℂ := ∑ k ∈ S,
        (((d : ℂ)⁻¹ * (σ : ℂ) ^ (d + 1) * P.polarPoly.coeff k * ((σ : ℂ)⁻¹) ^ k) *
          (X : ℂ) ^ (d + 1) * ((X : ℂ)⁻¹) ^ k)
      (∀ X > 0, ContDiffAt ℝ ℓ f X) ∧
      PowerClass 0 (iteratedDeriv ℓ f) ∧
      ∃ (B : ℝ) (L : ℕ), 0 ≤ B ∧ ∀ᶠ X : ℝ in atTop, ‖iteratedDeriv ℓ f X‖ ≤ B * X ^ L := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨fun _ _ ↦ contDiffAt_const, ?_, 0, 0, le_rfl, ?_⟩
      · simpa only [Finset.sum_empty, ppIteratedDeriv_zero_fun] using PowerClass.const 0
      · filter_upwards with X; simp
    | @insert k S hk ih =>
      obtain ⟨hcdS, hpcS, BS, LS, hBS, hbS⟩ := ih
      let fk (X : ℝ) : ℂ :=
        ((d : ℂ)⁻¹ * (σ : ℂ) ^ (d + 1) * P.polarPoly.coeff k * ((σ : ℂ)⁻¹) ^ k) *
          (X : ℂ) ^ (d + 1) * ((X : ℂ)⁻¹) ^ k
      let fS (X : ℝ) : ℂ := ∑ r ∈ S,
        (((d : ℂ)⁻¹ * (σ : ℂ) ^ (d + 1) * P.polarPoly.coeff r * ((σ : ℂ)⁻¹) ^ r) *
          (X : ℂ) ^ (d + 1) * ((X : ℂ)⁻¹) ^ r)
      have hcdk : ∀ X > 0, ContDiffAt ℝ ℓ fk X := fun X hX ↦ by
        have hco : ContDiffAt ℝ ℓ (fun y : ℝ ↦ (y : ℂ)) X := Complex.ofRealCLM.contDiff.contDiffAt
        exact (contDiffAt_const.mul (hco.pow (d + 1))).mul
          ((hco.inv (Complex.ofReal_ne_zero.mpr hX.ne')).pow k)
      have hsplit : ∀ X > 0, iteratedDeriv ℓ (fun y ↦ fk y + fS y) X =
          iteratedDeriv ℓ fk X + iteratedDeriv ℓ fS X := fun X hX ↦
        iteratedDeriv_fun_add (hcdk X hX) (hcdS X hX)
      obtain ⟨hpck, Bk, Lk, hBk, hbk⟩ := hmon k _
      have hfun_eq : (fun X : ℝ ↦ ∑ r ∈ insert k S,
          (((d : ℂ)⁻¹ * (σ : ℂ) ^ (d + 1) * P.polarPoly.coeff r * ((σ : ℂ)⁻¹) ^ r) *
            (X : ℂ) ^ (d + 1) * ((X : ℂ)⁻¹) ^ r)) = fun X : ℝ ↦ fk X + fS X := by
        funext X; exact Finset.sum_insert hk
      rw [hfun_eq]
      refine ⟨fun X hX ↦ (hcdk X hX).add (hcdS X hX),
        (hpck.add hpcS).congr ((eventually_gt_atTop (0 : ℝ)).mono fun X hX ↦ (hsplit X hX).symm),
        Bk + BS, max Lk LS, add_nonneg hBk hBS, ?_⟩
      filter_upwards [eventually_ge_atTop (1 : ℝ), hbk, hbS] with X hX h1 h2
      rw [hsplit X (zero_lt_one.trans_le hX)]
      calc ‖iteratedDeriv ℓ fk X + iteratedDeriv ℓ fS X‖
          ≤ ‖iteratedDeriv ℓ fk X‖ + ‖iteratedDeriv ℓ fS X‖ := norm_add_le _ _
        _ ≤ Bk * X ^ Lk + BS * X ^ LS := add_le_add h1 h2
        _ ≤ Bk * X ^ max Lk LS + BS * X ^ max Lk LS :=
            add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX (le_max_left ..)) hBk)
              (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX (le_max_right ..)) hBS)
        _ = (Bk + BS) * X ^ max Lk LS := by ring
  rw [hpol_eq]
  exact ⟨(hsum_rec P.polarPoly.support).2.1, (hsum_rec P.polarPoly.support).2.2⟩

private def ppDilPolarCoeff {d : ℕ} (hd : 2 ≤ d) (P : PowerPartStokesProfile d hd)
    (σ : ℝ) (_hσ : 0 < σ) (ℓ : ℕ) : Physical.RayCoefficient :=
  let pol (X : ℝ) : ℂ := ((d : ℂ)⁻¹ * (((σ * X : ℝ) : ℂ) ^ (d + 1))) *
    P.polarPoly.eval ((((σ * X : ℝ) : ℂ))⁻¹)
  let hb := (ppDilPolar_props hd P σ ℓ).2
  { value := iteratedDeriv ℓ pol
    budget := Classical.choose hb
    loss := Classical.choose (Classical.choose_spec hb)
    nonneg := (Classical.choose_spec (Classical.choose_spec hb)).1
    bound := (Classical.choose_spec (Classical.choose_spec hb)).2 }

private lemma ppDilPolarCoeff_powerClass {d : ℕ} (hd : 2 ≤ d) (P : PowerPartStokesProfile d hd)
    (σ : ℝ) (hσ : 0 < σ) (ℓ : ℕ) :
    PowerClass 0 (ppDilPolarCoeff hd P σ hσ ℓ).value :=
  (ppDilPolar_props hd P σ ℓ).1

private def ppQPolyRayCoeff {d : ℕ} (hd : 2 ≤ d) (j ℓ : ℕ) : Physical.RayCoefficient := by
  by_cases hℓ : ℓ ≤ j
  · have hq := qPolyCoeff_QCoeff (d := d + 1) (by omega) j ℓ hℓ
    have hb := hq.poly_bound
    exact ⟨qPolyCoeff (d + 1) j ℓ, Classical.choose hb, Classical.choose (Classical.choose_spec hb),
      (Classical.choose_spec (Classical.choose_spec hb)).1,
      (Classical.choose_spec (Classical.choose_spec hb)).2⟩
  · exact ⟨qPolyCoeff (d + 1) j ℓ, 0, 0, le_rfl,
      Eventually.of_forall fun X ↦ by rw [qPolyCoeff_gt j ℓ (by omega)]; simp⟩

private lemma ppQPolyRayCoeff_powerClass {d : ℕ} (hd : 2 ≤ d) (j ℓ : ℕ) :
    PowerClass 0 (ppQPolyRayCoeff hd j ℓ).value := by
  unfold ppQPolyRayCoeff
  split_ifs with hℓ
  · exact (qPolyCoeff_QCoeff (d := d + 1) (by omega) j ℓ hℓ).powerClass_zero (by omega)
  · exact (PowerClass.const 0).congr (Eventually.of_forall fun X ↦ (qPolyCoeff_gt j ℓ (by omega) X).symm)

private def ppDilWaveTracked {d : ℕ} (hd : 2 ≤ d) {A : ℕ} (hA : 0 < A)
    (m : ℕ+) (hdiv : m.val ∣ A) (ℓ : ℕ) : PPTracked d (ppDilKeyRate d A) where
  Index := Fin d × ℕ+
  exp := ppDilWaveExp d hd (ppDilScale d m.val) (ppDilScale_pos m.pos) ℓ
  finite_window R := by
    have hσ := ppDilScale_pos (d := d) m.pos
    have hsub : {ℓN : Fin d × ℕ+ | (((ppDilScale d m.val : ℝ) : ℂ) * ppWaveRate d ℓN.1 ℓN.2).re ≤ R} ⊆
        ⋃ j : Fin d, (fun N ↦ (j, N)) '' {N : ℕ+ | (ppWaveRate d j N).re ≤ R / ppDilScale d m.val} := by
      rintro ⟨j, N⟩ h
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
      exact mem_iUnion.mpr ⟨j, N, (le_div_iff₀' hσ).mpr h, rfl⟩
    refine (Set.finite_iUnion fun j ↦ ?_).subset hsub
    apply Set.Finite.image
    have hc := ppRay_re_pos hd j.isLt
    obtain ⟨M, hM⟩ := exists_nat_gt (max 0 ((R / ppDilScale d m.val) / (ppRay d j.val).re) ^ d)
    have hsubN : {N : ℕ+ | (ppWaveRate d j N).re ≤ R / ppDilScale d m.val} ⊆
        Subtype.val ⁻¹' (Set.Iic M) := by
      intro N hN; change (ppWaveRate d j N).re ≤ _ at hN
      have hre : (ppWaveRate d j N).re = (N.val : ℝ) ^ (1 / (d : ℝ)) * (ppRay d j.val).re := by
        simp [ppWaveRate, Complex.mul_re]
      rw [hre] at hN
      have hle : (N.val : ℝ) ^ (1 / (d : ℝ)) ≤ max 0 ((R / ppDilScale d m.val) / (ppRay d j.val).re) :=
        ((le_div_iff₀ hc).mpr hN).trans (le_max_right _ _)
      have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _) hle d
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
      rw [← Real.rpow_natCast ((N.val : ℝ) ^ _), ← Real.rpow_mul (Nat.cast_nonneg _),
          one_div, inv_mul_cancel₀ hd0, Real.rpow_one] at hpow
      change N.val ≤ M; exact_mod_cast (hpow.trans hM.le)
    exact ((Set.finite_Iic M).preimage Subtype.val_injective.injOn).subset hsubN
  pc0 := fun ℓN ↦ by
    have h := (PowerClass.const (-((powerPartMult d ℓN.2.val : ℝ) : ℂ) * ppWaveRate d ℓN.1 ℓN.2)).mul
      (ppDilAmp_powerClass d (ppDilScale d m.val) (ppWaveRate d ℓN.1 ℓN.2) ℓ)
    rwa [zero_add] at h
  halfSpace := fun ℓN ↦ by
    change 0 ≤ ppRotIm d (((ppDilScale d m.val : ℝ) : ℂ) *
      ((((ℓN.2.val : ℝ) ^ (1 / (d : ℝ)) : ℝ) : ℂ) * ppRay d ℓN.1.val))
    rw [← mul_assoc, ← Complex.ofReal_mul, ppRotIm_smul_real]
    exact mul_nonneg (mul_nonneg (ppDilScale_pos m.pos).le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (ppRotIm_nonneg hd ℓN.1.isLt)
  extreme_range := fun ℓN h0 ↦ by
    change ppRotIm d (((ppDilScale d m.val : ℝ) : ℂ) *
      ((((ℓN.2.val : ℝ) ^ (1 / (d : ℝ)) : ℝ) : ℂ) * ppRay d ℓN.1.val)) = 0 at h0
    rw [← mul_assoc, ← Complex.ofReal_mul, ppRotIm_smul_real] at h0
    have hpos : 0 < ppDilScale d m.val * (ℓN.2.val : ℝ) ^ (1 / (d : ℝ)) :=
      mul_pos (ppDilScale_pos m.pos) (Real.rpow_pos_of_pos (by exact_mod_cast ℓN.2.pos) _)
    have hray0 : ppRotIm d (ppRay d ℓN.1.val) = 0 := (mul_eq_zero.mp h0).resolve_left hpos.ne'
    have hℓ0 : ℓN.1.val = 0 := by
      by_contra hne; linarith [ppRotIm_other_pos hd (Nat.pos_of_ne_zero hne) ℓN.1.isLt]
    refine ⟨ppDilModeExp hd A m ℓN.2, ?_⟩
    rw [ppDilKeyRate_modeExp hd hA hdiv ℓN.2]
    change ((ppDilScale d m.val : ℝ) : ℂ) * ppWaveRate d ℓN.1 ℓN.2 = _
    congr 2; exact Fin.ext hℓ0

private def ppDilJetTracked {d : ℕ} (hd : 2 ≤ d) (P : PowerPartStokesProfile d hd)
    {A : ℕ} (hA : 0 < A) (m : ℕ+) (hdiv : m.val ∣ A) (j : ℕ) :
    PPTracked d (ppDilKeyRate d A) :=
  let rec go : ℕ → PPTracked d (ppDilKeyRate d A)
    | 0 =>
      let q0 := ppQPolyRayCoeff hd j 0
      let b0 := ppDilPolarCoeff hd P (ppDilScale d m.val) (ppDilScale_pos m.pos) 0
      (PPTracked.ofCoeff q0 (ppQPolyRayCoeff_powerClass hd j 0)).mul
        ((PPTracked.ofCoeff b0 (ppDilPolarCoeff_powerClass hd P _ _ 0)).add
          (ppDilWaveTracked hd hA m hdiv 0))
    | k + 1 =>
      let qk := ppQPolyRayCoeff hd j (k + 1)
      let bk := ppDilPolarCoeff hd P (ppDilScale d m.val) (ppDilScale_pos m.pos) (k + 1)
      (go k).add ((PPTracked.ofCoeff qk (ppQPolyRayCoeff_powerClass hd j (k + 1))).mul
        ((PPTracked.ofCoeff bk (ppDilPolarCoeff_powerClass hd P _ _ (k + 1))).add
          (ppDilWaveTracked hd hA m hdiv (k + 1))))
  go j

private lemma ppDilJetTracked_value {d : ℕ} (hd : 2 ≤ d) (P : PowerPartStokesProfile d hd)
    {A : ℕ} (hA : 0 < A) (m : ℕ+) (hdiv : m.val ∣ A) (j : ℕ) :
    ∀ᶠ X : ℝ in atTop,
      (ppDilJetTracked hd P hA m hdiv j).exp.value X =
        psValue (formalJet (logDerivPowerPartDilated d m.val) j) (qRayD (d + 1) X) := by
  have hd3 : 3 ≤ d + 1 := by omega
  let σ := ppDilScale d m.val
  let hσ := ppDilScale_pos (d := d) m.pos
  let pol (X : ℝ) : ℂ := ((d : ℂ)⁻¹ * (((σ * X : ℝ) : ℂ) ^ (d + 1))) *
    P.polarPoly.eval ((((σ * X : ℝ) : ℂ))⁻¹)
  have hval_split : ∀ᶠ X : ℝ in atTop,
      psValue (logDerivPowerPartDilated d m.val) (qRayD (d + 1) X) =
        pol X + (ppDilWaveExp d hd σ hσ 0).value X := by
    have hdec := (tendsto_id.const_mul_atTop hσ).eventually P.decomp
    filter_upwards [eventually_gt_atTop (0 : ℝ), hdec, ppDilWaveExp_value_zero hd σ hσ] with X hX hD hW
    simp only [id_eq, rescaledLogDerivPP] at hD
    have hσX : 0 < σ * X := mul_pos hσ hX
    have hq : psValue (logDerivPowerPartDilated d m.val) (qRayD (d + 1) X) =
        psValue (logDerivPowerPart d) (qRayD (d + 1) (σ * X)) := by
      rw [ppLogDeriv_dilated_value_eq m.pos (qRayD_disk hX), ppQRay_dilScale hd m X]
    rw [hq, hW]; dsimp only [pol]
    have hD' : ((d : ℂ) * (((σ * X : ℝ) : ℂ)⁻¹) ^ (d + 1)) *
        psValue (logDerivPowerPart d) (qRayD (d + 1) (σ * X)) =
        P.polarPoly.eval (((σ * X : ℝ) : ℂ)⁻¹) + (ppWaveJet d hd 0).value (σ * X) := hD
    have hmul := congrArg (((d : ℂ)⁻¹ * (((σ * X : ℝ) : ℂ) ^ (d + 1))) * ·) hD'
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    have hσX0 : ((σ * X : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσX.ne'
    have hcan : ((d : ℂ)⁻¹ * ((σ * X : ℝ) : ℂ) ^ (d + 1)) *
        ((d : ℂ) * (((σ * X : ℝ) : ℂ)⁻¹) ^ (d + 1)) = 1 := by
      rw [inv_pow]; field_simp [hd0, hσX0]
    rw [← mul_assoc, hcan, one_mul, mul_add] at hmul
    exact hmul
  have hiter_split (ℓ : ℕ) :
      iteratedDeriv ℓ (fun X ↦ psValue (logDerivPowerPartDilated d m.val) (qRayD (d + 1) X)) =ᶠ[atTop]
        fun X ↦ (ppDilPolarCoeff hd P σ hσ ℓ).value X + (ppDilWaveExp d hd σ hσ ℓ).value X := by
    obtain ⟨L, hL⟩ := eventually_atTop.1 hval_split
    have h1 : iteratedDeriv ℓ (fun X ↦ psValue (logDerivPowerPartDilated d m.val) (qRayD (d + 1) X)) =ᶠ[atTop]
        iteratedDeriv ℓ (fun X ↦ pol X + (ppDilWaveExp d hd σ hσ 0).value X) :=
      (eventually_gt_atTop L).mono fun X hX ↦ by
        have hloc : (fun x ↦ psValue (logDerivPowerPartDilated d m.val) (qRayD (d + 1) x)) =ᶠ[𝓝 X]
            fun x ↦ pol x + (ppDilWaveExp d hd σ hσ 0).value x :=
          (lt_mem_nhds hX).mono fun y hy ↦ hL y hy.le
        exact hloc.iteratedDeriv_eq ℓ
    have hpol_cd (k : ℕ) (X : ℝ) (hX : 0 < X) : DifferentiableAt ℝ (iteratedDeriv k pol) X := by
      have han : ∀ r, AnalyticAt ℝ (iteratedDeriv r pol) X := fun r ↦ by
        induction r with
        | zero =>
          have hσX0 : ((σ * X : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_pos hσ hX).ne'
          have hlin : AnalyticAt ℝ (fun y : ℝ ↦ ((σ * y : ℝ) : ℂ)) X :=
            (Complex.ofRealCLM.analyticAt _).comp (analyticAt_const.fun_mul analyticAt_id)
          have hinv : AnalyticAt ℝ (fun y : ℝ ↦ (((σ * y : ℝ) : ℂ))⁻¹) X := hlin.inv hσX0
          have hpoly : AnalyticAt ℝ (fun y : ℝ ↦ P.polarPoly.eval (((σ * y : ℝ) : ℂ)⁻¹)) X := by
            induction P.polarPoly using Polynomial.induction_on' with
            | add p q hp hq => simpa only [Polynomial.eval_add] using hp.fun_add hq
            | monomial r c =>
              have hc : AnalyticAt ℝ (fun _ : ℝ ↦ c) X := analyticAt_const
              simpa only [Polynomial.eval_monomial] using hc.fun_mul (hinv.fun_pow r)
          have hd_c : AnalyticAt ℝ (fun _ : ℝ ↦ (d : ℂ)⁻¹) X := analyticAt_const
          simpa only [iteratedDeriv_zero] using
            (hd_c.fun_mul (hlin.fun_pow (d + 1))).fun_mul hpoly
        | succ r ihr => rw [iteratedDeriv_succ]; exact ihr.deriv
      exact (han k).differentiableAt
    have hwav_diff (k : ℕ) : ∀ᶠ X : ℝ in atTop,
        DifferentiableAt ℝ (iteratedDeriv k (ppDilWaveExp d hd σ hσ 0).value) X := by
      have hd_val := (ppDilWaveExp d hd σ hσ k).hasDerivAt_value (ppDilWaveExp d hd σ hσ (k + 1))
        (Eventually.of_forall fun X ℓN ↦ by
          have hd_a := (ppDilAmp_deriv d σ (ppWaveRate d ℓN.1 ℓN.2) k X).const_mul
            (-((powerPartMult d ℓN.2.val : ℝ) : ℂ) * ppWaveRate d ℓN.1 ℓN.2)
          convert hd_a using 1
          · funext y; simp only [WaveExpansion.term, ppDilWaveExp]; ring
          · simp only [WaveExpansion.term, ppDilWaveExp]; ring)
      obtain ⟨Lw, hLw⟩ := eventually_atTop.1 (ppDilWaveExp_derivatives hd σ hσ k)
      filter_upwards [hd_val, eventually_gt_atTop Lw] with X hX hLX
      exact hX.differentiableAt.congr_of_eventuallyEq ((lt_mem_nhds hLX).mono fun y hy ↦ hLw y hy.le)
    have hadd_iter : ∀ k, iteratedDeriv k (fun X ↦ pol X + (ppDilWaveExp d hd σ hσ 0).value X) =ᶠ[atTop]
        fun X ↦ iteratedDeriv k pol X + iteratedDeriv k (ppDilWaveExp d hd σ hσ 0).value X := by
      intro k
      induction k with
      | zero => filter_upwards with X; simp
      | succ k ih =>
        obtain ⟨L1, hL1⟩ := eventually_atTop.1 ih
        filter_upwards [eventually_gt_atTop (max L1 0), hwav_diff k] with X hX hdw
        have hX0 : 0 < X := lt_of_le_of_lt (le_max_right _ _) hX
        have hL1X : L1 < X := lt_of_le_of_lt (le_max_left _ _) hX
        rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ]
        have hnear : iteratedDeriv k (fun y ↦ pol y + (ppDilWaveExp d hd σ hσ 0).value y) =ᶠ[𝓝 X]
            fun y ↦ iteratedDeriv k pol y + iteratedDeriv k (ppDilWaveExp d hd σ hσ 0).value y :=
          (lt_mem_nhds hL1X).mono fun y hy ↦ hL1 y hy.le
        rw [hnear.deriv_eq, deriv_fun_add (hpol_cd k X hX0) hdw]
    filter_upwards [h1, hadd_iter ℓ, ppDilWaveExp_derivatives hd σ hσ ℓ] with X h1' h2' h3'
    rw [h1', h2', h3']; rfl
  have hjet_eq_iter : ∀ᶠ X : ℝ in atTop,
      psValue (formalJet (logDerivPowerPartDilated d m.val) j) (qRayD (d + 1) X) =
        ∑ ℓ ∈ Finset.range (j + 1),
          qPolyCoeff (d + 1) j ℓ X *
            ((ppDilPolarCoeff hd P σ hσ ℓ).value X + (ppDilWaveExp d hd σ hσ ℓ).value X) := by
    have hsmooth : ∀ ℓ ≤ j, ∀ᶠ X : ℝ in atTop,
        DifferentiableAt ℝ (iteratedDeriv ℓ (fun y ↦ psValue (logDerivPowerPartDilated d m.val) (qRayD (d + 1) y))) X := by
      intro ℓ _
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      have han : ∀ r, AnalyticAt ℝ (iteratedDeriv r (fun y ↦ psValue (logDerivPowerPartDilated d m.val) (qRayD (d + 1) y))) X := by
        intro r; induction r with
        | zero =>
          exact (((ppLogDeriv_jet_analytic d m.val 0) _ (by simpa using qRayD_disk hX)).restrictScalars
            (𝕜 := ℝ)).comp (qRayD_analytic hX)
        | succ r ihr => rw [iteratedDeriv_succ]; exact ihr.deriv
      exact (han ℓ).differentiableAt
    have hiterQ (k : ℕ) {X : ℝ} (hX : 0 < X) :
        psValue (formalJet (logDerivPowerPartDilated d m.val) k) (qRayD (d + 1) X) =
          iterQDeriv (d + 1) k (fun y ↦ psValue (logDerivPowerPartDilated d m.val) (qRayD (d + 1) y)) X := by
      induction k generalizing X with
      | zero => rfl
      | succ k ihk =>
        change _ = invSpeedD (d + 1) X * deriv (iterQDeriv (d + 1) k _) X
        have hnear : iterQDeriv (d + 1) k (fun y ↦ psValue (logDerivPowerPartDilated d m.val) (qRayD (d + 1) y)) =ᶠ[𝓝 X]
            fun y ↦ psValue (formalJet (logDerivPowerPartDilated d m.val) k) (qRayD (d + 1) y) :=
          (lt_mem_nhds hX).mono fun y hy ↦ (ihk hy).symm
        have hcomp : HasDerivAt (fun y ↦ psValue (formalJet (logDerivPowerPartDilated d m.val) k) (qRayD (d + 1) y))
            (speedD (d + 1) X * psValue (formalJet (logDerivPowerPartDilated d m.val) (k + 1)) (qRayD (d + 1) X)) X := by
          simpa [Function.comp_def, mul_comm] using!
            ((ppLogDeriv_jet_deriv d m.val k (qRayD_disk hX)).scomp X (qRayD_deriv hd3 hX))
        rw [hnear.deriv_eq, hcomp.deriv, ← mul_assoc, invSpeedD_mul_speedD hd3 hX, one_mul]
    have hchain := iterQDeriv_eq_sum hd3 (fun y ↦ psValue (logDerivPowerPartDilated d m.val) (qRayD (d + 1) y)) j hsmooth
    have hall := (Filter.eventually_all_finset (Finset.range (j + 1))).mpr fun ℓ _ ↦ hiter_split ℓ
    filter_upwards [eventually_gt_atTop (0 : ℝ), hchain, hall] with X hX hch hl
    rw [hiterQ j hX, hch]
    apply Finset.sum_congr rfl; intro ℓ hℓ; rw [hl ℓ hℓ]
  have hgo_val : ∀ k ≤ j, ∀ᶠ X : ℝ in atTop,
      (ppDilJetTracked.go hd P hA m hdiv j k).exp.value X =
        ∑ ℓ ∈ Finset.range (k + 1),
          qPolyCoeff (d + 1) j ℓ X *
            ((ppDilPolarCoeff hd P σ hσ ℓ).value X + (ppDilWaveExp d hd σ hσ ℓ).value X) := by
    intro k hk
    induction k with
    | zero =>
      filter_upwards [(PPTracked.ofCoeff (ppQPolyRayCoeff hd j 0) _).exp.value_mul _,
        (PPTracked.ofCoeff (ppDilPolarCoeff hd P σ hσ 0) _).exp.value_add _] with X hm ha
      change ((PPTracked.ofCoeff (ppQPolyRayCoeff hd j 0) _).exp.mul
        ((PPTracked.ofCoeff (ppDilPolarCoeff hd P σ hσ 0) _).exp.add
          (ppDilWaveTracked hd hA m hdiv 0).exp)).value X = _
      rw [hm, ha]
      have hrc (a : Physical.RayCoefficient) : a.expansion.value X = a.value X := by
        unfold WaveExpansion.value WaveExpansion.term Physical.RayCoefficient.expansion; simp
      change (ppQPolyRayCoeff hd j 0).expansion.value X *
        ((ppDilPolarCoeff hd P σ hσ 0).expansion.value X + (ppDilWaveExp d hd σ hσ 0).value X) = _
      rw [hrc, hrc]
      have hq : (ppQPolyRayCoeff hd j 0).value X = qPolyCoeff (d + 1) j 0 X := by
        unfold ppQPolyRayCoeff; split_ifs; rfl
      rw [hq]; simp
    | succ k ih =>
      filter_upwards [ih (by omega),
        (ppDilJetTracked.go hd P hA m hdiv j k).exp.value_add _,
        (PPTracked.ofCoeff (ppQPolyRayCoeff hd j (k + 1)) _).exp.value_mul _,
        (PPTracked.ofCoeff (ppDilPolarCoeff hd P σ hσ (k + 1)) _).exp.value_add _] with X hprev hadd hm ha
      change ((ppDilJetTracked.go hd P hA m hdiv j k).exp.add
        ((PPTracked.ofCoeff (ppQPolyRayCoeff hd j (k + 1)) _).exp.mul
          ((PPTracked.ofCoeff (ppDilPolarCoeff hd P σ hσ (k + 1)) _).exp.add
            (ppDilWaveTracked hd hA m hdiv (k + 1)).exp))).value X = _
      rw [hadd, hprev, hm, ha]
      conv_rhs => rw [Finset.sum_range_succ]
      congr 1
      have hrc (a : Physical.RayCoefficient) : a.expansion.value X = a.value X := by
        unfold WaveExpansion.value WaveExpansion.term Physical.RayCoefficient.expansion; simp
      change (ppQPolyRayCoeff hd j (k + 1)).expansion.value X *
        ((ppDilPolarCoeff hd P σ hσ (k + 1)).expansion.value X +
          (ppDilWaveExp d hd σ hσ (k + 1)).value X) = _
      rw [hrc, hrc]
      have hq : (ppQPolyRayCoeff hd j (k + 1)).value X = qPolyCoeff (d + 1) j (k + 1) X := by
        unfold ppQPolyRayCoeff; split_ifs; rfl
      rw [hq]
  filter_upwards [hgo_val j le_rfl, hjet_eq_iter] with X h1 h2
  exact h1.trans h2.symm

private lemma ppDilJetTracked_marked_eq {d : ℕ} (hd : 2 ≤ d) (P : PowerPartStokesProfile d hd)
    {A : ℕ} (hA : 0 < A) (m : ℕ+) (hdiv : m.val ∣ A) (j : ℕ) :
    (ppDilJetTracked hd P hA m hdiv j).marked =
      ∑ ℓ ∈ Finset.range (j + 1),
        MvPowerSeries.C (Germ.ofFun (qPolyCoeff (d + 1) j ℓ)) *
          (MvPowerSeries.C (Germ.ofFun (ppDilPolarCoeff hd P (ppDilScale d m.val) (ppDilScale_pos m.pos) ℓ).value) +
            (ppDilWaveTracked hd hA m hdiv ℓ).marked) := by
  have hinj := ppDilKeyRate_injective hd hA
  have hface := fun k ↦ ppRotIm_dilKeyRate (A := A) hd k
  have hgo : ∀ k ≤ j, (ppDilJetTracked.go hd P hA m hdiv j k).marked =
      ∑ ℓ ∈ Finset.range (k + 1),
        MvPowerSeries.C (Germ.ofFun (qPolyCoeff (d + 1) j ℓ)) *
          (MvPowerSeries.C (Germ.ofFun (ppDilPolarCoeff hd P (ppDilScale d m.val) (ppDilScale_pos m.pos) ℓ).value) +
            (ppDilWaveTracked hd hA m hdiv ℓ).marked) := by
    intro k hk
    have hq_val (r : ℕ) : (ppQPolyRayCoeff hd j r).value = qPolyCoeff (d + 1) j r := by
      unfold ppQPolyRayCoeff; split_ifs <;> rfl
    induction k with
    | zero =>
      simp only [ppDilJetTracked.go, PPTracked.marked_mul _ _ hinj hface,
        PPTracked.marked_add, PPTracked.marked_ofCoeff _ _ hinj, hq_val,
        Nat.zero_add, Finset.range_one, Finset.sum_singleton]
    | succ k ih =>
      simp only [ppDilJetTracked.go, PPTracked.marked_add, PPTracked.marked_mul _ _ hinj hface,
        PPTracked.marked_ofCoeff _ _ hinj, hq_val, ih (by omega), Finset.sum_range_succ]
  exact hgo j le_rfl

private lemma ppDilWaveTracked_coeff {d : ℕ} (hd : 2 ≤ d) {A : ℕ} (hA : 0 < A)
    (m : ℕ+) (hdiv : m.val ∣ A) (ℓ : ℕ) (k : Core d →₀ ℕ) :
    ((∀ N : ℕ+, k ≠ ppDilModeExp hd A m N) →
        MvPowerSeries.coeff k (ppDilWaveTracked hd hA m hdiv ℓ).marked = 0) ∧
    (∀ N : ℕ+, k = ppDilModeExp hd A m N →
        MvPowerSeries.coeff k (ppDilWaveTracked hd hA m hdiv ℓ).marked =
          Germ.ofFun ((ppDilWaveExp d hd (ppDilScale d m.val) (ppDilScale_pos m.pos) ℓ).amplitude
            (⟨0, by omega⟩, N))) := by
  have hinj := ppDilKeyRate_injective hd hA
  have hfiber (ℓN : Fin d × ℕ+) :
      (ppDilWaveTracked hd hA m hdiv ℓ).exp.rate ℓN = ppDilKeyRate d A k ↔
        ℓN.1 = ⟨0, by omega⟩ ∧ ppDilModeExp hd A m ℓN.2 = k := by
    constructor
    · intro hrate
      have hrot : ppRotIm d ((ppDilWaveTracked hd hA m hdiv ℓ).exp.rate ℓN) = 0 := by
        rw [hrate]; exact ppRotIm_dilKeyRate hd k
      have hℓ0 : ℓN.1.val = 0 := by
        change ppRotIm d (((ppDilScale d m.val : ℝ) : ℂ) *
          ((((ℓN.2.val : ℝ) ^ (1 / (d : ℝ)) : ℝ) : ℂ) * ppRay d ℓN.1.val)) = 0 at hrot
        rw [← mul_assoc, ← Complex.ofReal_mul, ppRotIm_smul_real] at hrot
        have hpos : 0 < ppDilScale d m.val * (ℓN.2.val : ℝ) ^ (1 / (d : ℝ)) :=
          mul_pos (ppDilScale_pos m.pos) (Real.rpow_pos_of_pos (by exact_mod_cast ℓN.2.pos) _)
        have hray0 := (mul_eq_zero.mp hrot).resolve_left hpos.ne'
        by_contra hne; linarith [ppRotIm_other_pos hd (Nat.pos_of_ne_zero hne) ℓN.1.isLt]
      have hℓeq : ℓN.1 = ⟨0, by omega⟩ := Fin.ext hℓ0
      refine ⟨hℓeq, hinj ?_⟩
      rw [ppDilKeyRate_modeExp hd hA hdiv ℓN.2, ← hrate]
      change ((ppDilScale d m.val : ℝ) : ℂ) * ppWaveRate d ⟨0, by omega⟩ ℓN.2 =
        ((ppDilScale d m.val : ℝ) : ℂ) * ppWaveRate d ℓN.1 ℓN.2
      rw [hℓeq]
    · rintro ⟨hℓ, hk⟩
      rw [← hk, ppDilKeyRate_modeExp hd hA hdiv ℓN.2]
      change ((ppDilScale d m.val : ℝ) : ℂ) * ppWaveRate d ℓN.1 ℓN.2 = _
      rw [hℓ]
  have hmode_inj : Function.Injective (ppDilModeExp hd A m) := fun N₁ N₂ h ↦ by
    have h1 := congrArg (ppDilKeyRate d A) h
    rw [ppDilKeyRate_modeExp hd hA hdiv N₁, ppDilKeyRate_modeExp hd hA hdiv N₂] at h1
    have h2 := mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ppDilScale_pos (d := d) m.property).ne') h1
    have h3 := Complex.ofReal_injective (mul_right_cancel₀ (ppExtremeRay_ne_zero hd) h2)
    have hd_pos : (0 : ℝ) < 1 / (d : ℝ) := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
      positivity
    exact PNat.eq (Nat.cast_injective ((Real.rpow_left_inj (Nat.cast_nonneg _) (Nat.cast_nonneg _) hd_pos.ne').mp h3))
  constructor
  · intro hall
    change (∑ i : PPTracked.Fiber (ppDilWaveTracked hd hA m hdiv ℓ) k, _) = 0
    have : IsEmpty (PPTracked.Fiber (ppDilWaveTracked hd hA m hdiv ℓ) k) :=
      ⟨fun i ↦ hall i.val.2 ((hfiber i.val).mp i.property).2.symm⟩
    simp
  · intro N hN
    change (∑ i : PPTracked.Fiber (ppDilWaveTracked hd hA m hdiv ℓ) k, _) = _
    let i₀ : PPTracked.Fiber (ppDilWaveTracked hd hA m hdiv ℓ) k :=
      ⟨(⟨0, by omega⟩, N), (hfiber _).mpr ⟨rfl, hN.symm⟩⟩
    have huniq : ∀ i : PPTracked.Fiber (ppDilWaveTracked hd hA m hdiv ℓ) k, i = i₀ := fun i ↦ by
      obtain ⟨hℓ, hmode⟩ := (hfiber i.val).mp i.property
      exact Subtype.ext (Prod.ext hℓ (hmode_inj (hmode.trans hN)))
    rw [Finset.sum_eq_single i₀ (fun i _ hne ↦ (hne (huniq i)).elim) (fun h ↦ (h (Finset.mem_univ _)).elim)]
    rfl

private def ppOptionToPolyMv (ι : Type*) :
    MvPolynomial (Option ι) ℂ →ₐ[ℂ] MvPolynomial ι (Polynomial ℂ) :=
  MvPolynomial.aeval fun
    | none => MvPolynomial.C Polynomial.X
    | some x => MvPolynomial.X x

private def ppPolyMvToOption (ι : Type*) :
    MvPolynomial ι (Polynomial ℂ) →+* MvPolynomial (Option ι) ℂ :=
  MvPolynomial.eval₂Hom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X none))
    (fun x ↦ MvPolynomial.X (some x))

private lemma ppOptionToPolyMv_injective (ι : Type*) :
    Function.Injective (ppOptionToPolyMv ι) :=
  Function.LeftInverse.injective (g := ppPolyMvToOption ι) (fun Q ↦ by
    induction Q using MvPolynomial.induction_on with
    | C c => simp [ppOptionToPolyMv, ppPolyMvToOption]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p u hp => rw [map_mul, map_mul, hp]; cases u <;> simp [ppOptionToPolyMv, ppPolyMvToOption])

private lemma ppEval₂_optionToPolyMv {ι : Type*} (q : ℂ) (f : ι → ℂ)
    (Q : MvPolynomial (Option ι) ℂ) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom q) f (ppOptionToPolyMv ι Q) =
      MvPolynomial.eval (Option.elim' q f) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [ppOptionToPolyMv]
  | add p r hp hr => rw [map_add, MvPolynomial.eval₂_add, map_add, hp, hr]
  | mul_X p u hp => rw [map_mul, MvPolynomial.eval₂_mul, map_mul, hp]; cases u <;> simp [ppOptionToPolyMv]

private def ppPolyToGerm (d : ℕ) : Polynomial ℂ →+* RayGerm :=
  (Germ.coeRingHom (atTop : Filter ℝ)).comp
    { toFun := fun R X ↦ R.eval (qRayD (d + 1) X)
      map_one' := by funext X; simp
      map_mul' := fun R S ↦ by funext X; simp
      map_zero' := by funext X; simp
      map_add' := fun R S ↦ by funext X; simp }

private lemma ppPolyToGerm_injective {d : ℕ} (hd : 2 ≤ d) :
    Function.Injective (ppPolyToGerm d) := by
  intro R S hRS
  suffices h0 : R - S = 0 from sub_eq_zero.mp h0
  have hev : ∀ᶠ X : ℝ in atTop, (R - S).eval (qRayD (d + 1) X) = 0 :=
    Germ.coe_eq.mp (by change ppPolyToGerm d (R - S) = 0; rw [map_sub, hRS, sub_self])
  obtain ⟨L, hL⟩ := eventually_atTop.1 hev
  let L₀ : ℝ := max L 1
  have hq_inj : Set.InjOn (qRayD (d + 1)) (Ici L₀) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one ((le_max_right L 1).trans hx)
    have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one ((le_max_right L 1).trans hy)
    have hreal : Real.exp (-(1 / x ^ d)) = Real.exp (-(1 / y ^ d)) := by
      simpa [qRayD] using Complex.ofReal_injective hxy
    have hpow : x ^ d = y ^ d := inv_injective (by simpa only [one_div] using neg_inj.mp (Real.exp_injective hreal))
    exact (pow_left_inj₀ hx0.le hy0.le (by omega)).mp hpow
  have hinf : (qRayD (d + 1) '' Ici L₀).Infinite := (Ici_infinite L₀).image hq_inj
  by_contra hne0
  obtain ⟨z, ⟨X, hX, rfl⟩, hnot⟩ := hinf.exists_notMem_finset (R - S).roots.toFinset
  exact hnot (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne0).mpr (hL X ((le_max_left L 1).trans hX))))

private def ppPolyRayCoeff (d : ℕ) (R : Polynomial ℂ) : Physical.RayCoefficient where
  value := fun X ↦ R.eval (qRayD (d + 1) X)
  budget := ∑ k ∈ R.support, ‖R.coeff k‖
  loss := 0
  nonneg := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  bound := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    rw [pow_zero, mul_one, Polynomial.eval_eq_sum]
    calc ‖R.sum fun k c ↦ c * qRayD (d + 1) X ^ k‖
        ≤ ∑ k ∈ R.support, ‖R.coeff k * qRayD (d + 1) X ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ R.support, ‖R.coeff k‖ := by
          apply Finset.sum_le_sum; intro k _
          rw [norm_mul, norm_pow]
          exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (qRayD_disk hX).le)

private lemma ppPolyRayCoeff_powerClass {d : ℕ} (hd : 2 ≤ d) (R : Polynomial ℂ) :
    PowerClass 0 (ppPolyRayCoeff d R).value := by
  have hq : PowerClass 0 (qRayD (d + 1)) := by
    have h := exp_inv_pow_powerClass (r := d) (by omega) (-1)
    exact h.congr (Eventually.of_forall fun X ↦ by simp [qRayD, neg_div])
  have hpow : ∀ n : ℕ, PowerClass 0 (fun X ↦ qRayD (d + 1) X ^ n) := by
    intro n; induction n with
    | zero => simpa using PowerClass.const (1 : ℂ)
    | succ n ih => have hm := ih.mul hq; rw [zero_add] at hm; simpa only [pow_succ] using hm
  induction R using Polynomial.induction_on' with
  | add P Q hP hQ => exact (hP.add hQ).congr (Eventually.of_forall fun X ↦ by simp [ppPolyRayCoeff])
  | monomial n c =>
    have hm := (PowerClass.const c).mul (hpow n); rw [zero_add] at hm
    exact hm.congr (Eventually.of_forall fun X ↦ by simp [ppPolyRayCoeff, Polynomial.eval_monomial])

private lemma ppEvalPolyMv_tracked {d A : ℕ} (hd : 2 ≤ d) (hA : 0 < A) {ι : Type*}
    (f : ι → PPTracked d (ppDilKeyRate d A)) (Q : MvPolynomial ι (Polynomial ℂ)) :
    let _ : Algebra (Polynomial ℂ) RayGerm := (ppPolyToGerm d).toAlgebra
    ∃ E : PPTracked d (ppDilKeyRate d A),
      (∀ᶠ X : ℝ in atTop, E.exp.value X =
        MvPolynomial.eval₂ (Polynomial.evalRingHom (qRayD (d + 1) X)) (fun i ↦ (f i).exp.value X) Q) ∧
      E.marked = MvPolynomial.aeval (R := Polynomial ℂ) (fun i ↦ (f i).marked) Q := by
  let _ : Algebra (Polynomial ℂ) RayGerm := (ppPolyToGerm d).toAlgebra
  have hinj := ppDilKeyRate_injective hd hA
  have hface := fun k ↦ ppRotIm_dilKeyRate (A := A) hd k
  induction Q using MvPolynomial.induction_on with
  | C R =>
    refine ⟨PPTracked.ofCoeff (ppPolyRayCoeff d R) (ppPolyRayCoeff_powerClass hd R),
      Eventually.of_forall fun X ↦ ?_, ?_⟩
    · simp [PPTracked.ofCoeff, WaveExpansion.value, WaveExpansion.term,
        Physical.RayCoefficient.expansion, ppPolyRayCoeff]
    · rw [PPTracked.marked_ofCoeff _ _ hinj, MvPolynomial.aeval_C, MvPowerSeries.algebraMap_apply]; rfl
  | add p q hp hq =>
    obtain ⟨Ep, hvp, hmp⟩ := hp
    obtain ⟨Eq, hvq, hmq⟩ := hq
    refine ⟨Ep.add Eq, ?_, by rw [PPTracked.marked_add, hmp, hmq, map_add]⟩
    filter_upwards [Ep.exp.value_add Eq.exp, hvp, hvq] with X hadd hp' hq'
    rw [show (Ep.add Eq).exp.value X = (Ep.exp.add Eq.exp).value X from rfl, hadd, hp', hq',
        MvPolynomial.eval₂_add]
  | mul_X p i hp =>
    obtain ⟨Ep, hvp, hmp⟩ := hp
    refine ⟨Ep.mul (f i), ?_, by rw [PPTracked.marked_mul _ _ hinj hface, hmp, map_mul, MvPolynomial.aeval_X]⟩
    filter_upwards [Ep.exp.value_mul (f i).exp, hvp] with X hmul hp'
    rw [show (Ep.mul (f i)).exp.value X = (Ep.exp.mul (f i).exp).value X from rfl, hmul, hp',
        MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]

private lemma ppCoeff_prod_singleVar {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (g : ι → MvPowerSeries ι R)
    (hsingle : ∀ r (m : ι →₀ ℕ), MvPowerSeries.coeff m (g r) ≠ 0 → ∃ k : ℕ, m = Finsupp.single r k)
    (m : ι →₀ ℕ) :
    MvPowerSeries.coeff m (∏ r : ι, g r) =
      ∏ r : ι, MvPowerSeries.coeff (Finsupp.single r (m r)) (g r) := by
  classical
  suffices ∀ (S : Finset ι) (m : ι →₀ ℕ),
      ((∃ i ∉ S, m i ≠ 0) → MvPowerSeries.coeff m (∏ r ∈ S, g r) = 0) ∧
      ((∀ i ∉ S, m i = 0) → MvPowerSeries.coeff m (∏ r ∈ S, g r) =
        ∏ r ∈ S, MvPowerSeries.coeff (Finsupp.single r (m r)) (g r)) by
    exact (this Finset.univ m).2 fun i hi ↦ (hi (Finset.mem_univ i)).elim
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro m; constructor
    · rintro ⟨i, _, hi⟩
      rw [Finset.prod_empty, MvPowerSeries.coeff_one]
      have hm0 : m ≠ 0 := fun h ↦ hi (by simp [h])
      simp only [hm0, ↓reduceIte]
    · intro hall
      have hm0 : m = 0 := Finsupp.ext fun i ↦ hall i (Finset.notMem_empty i)
      rw [hm0, Finset.prod_empty, Finset.prod_empty, MvPowerSeries.coeff_one]
      simp only [↓reduceIte]
  | @insert a S ha ih =>
    intro m; rw [Finset.prod_insert ha, MvPowerSeries.coeff_mul]
    constructor
    · rintro ⟨i, hi, hmi⟩
      apply Finset.sum_eq_zero; rintro ⟨u, v⟩ huv
      have hsum : u + v = m := Finset.mem_antidiagonal.mp huv
      by_cases hu : MvPowerSeries.coeff u (g a) = 0
      · rw [hu, zero_mul]
      · obtain ⟨k, rfl⟩ := hsingle a u hu
        have hia : i ≠ a := fun h ↦ hi (h ▸ Finset.mem_insert_self a S)
        have hvi : v i ≠ 0 := by
          have h1 := DFunLike.congr_fun hsum i
          rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hia, zero_add] at h1
          exact h1.symm ▸ hmi
        rw [(ih v).1 ⟨i, fun h ↦ hi (Finset.mem_insert_of_mem h), hvi⟩, mul_zero]
    · intro hall
      let u₀ : ι →₀ ℕ := Finsupp.single a (m a)
      let v₀ : ι →₀ ℕ := m - u₀
      have huv₀ : u₀ + v₀ = m := by
        ext i; by_cases h : i = a <;> simp [u₀, v₀, h]
      rw [Finset.sum_eq_single (u₀, v₀)]
      · rw [Finset.prod_insert ha, (ih v₀).2]
        · congr 1; apply Finset.prod_congr rfl; intro r hr
          have hra : r ≠ a := fun h ↦ ha (h ▸ hr)
          simp [v₀, u₀, hra]
        · intro i hi
          by_cases hia : i = a
          · subst hia; simp [v₀, u₀]
          · simp [v₀, u₀, hia, hall i (fun h ↦ hi ((Finset.mem_insert.mp h).resolve_left hia))]
      · rintro ⟨u, v⟩ huv hne
        have hsum : u + v = m := Finset.mem_antidiagonal.mp huv
        by_cases hu : MvPowerSeries.coeff u (g a) = 0
        · rw [hu, zero_mul]
        · obtain ⟨k, rfl⟩ := hsingle a u hu
          by_cases hva : v a ≠ 0
          · rw [(ih v).1 ⟨a, ha, hva⟩, mul_zero]
          · push Not at hva
            have hka : k = m a := by
              have := DFunLike.congr_fun hsum a
              simpa [hva] using this
            have hu_eq : Finsupp.single a k = u₀ := by rw [hka]
            have hv_eq : v = v₀ := by
              ext i
              have h1 := DFunLike.congr_fun hsum i
              by_cases h : i = a
              · subst h; simp [v₀, u₀, hva]
              · rw [Finsupp.add_apply, Finsupp.single_eq_of_ne h, zero_add] at h1
                simp only [v₀, u₀, Finsupp.tsub_apply, Finsupp.single_eq_of_ne h,
                  Nat.sub_zero]
                exact h1
            exact (hne (Prod.ext hu_eq hv_eq)).elim
      · intro hnot; exact (hnot (Finset.mem_antidiagonal.mpr huv₀)).elim

private lemma ppTendsto_matrix_det {J : ℕ} (M : ℝ → Matrix (Fin J) (Fin J) ℂ)
    (L : Matrix (Fin J) (Fin J) ℂ)
    (h : ∀ i j : Fin J, Tendsto (fun X ↦ M X i j) atTop (𝓝 (L i j))) :
    Tendsto (fun X ↦ (M X).det) atTop (𝓝 L.det) := by
  have hsum : ∀ (S : Finset (Equiv.Perm (Fin J))),
      Tendsto (fun X ↦ ∑ σ ∈ S, (Equiv.Perm.sign σ : ℤ) • ∏ i : Fin J, M X (σ i) i)
        atTop (𝓝 (∑ σ ∈ S, (Equiv.Perm.sign σ : ℤ) • ∏ i : Fin J, L (σ i) i)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert σ S hσ ih =>
      simp only [Finset.sum_insert hσ]
      have hprod : Tendsto (fun X ↦ ∏ i : Fin J, M X (σ i) i) atTop (𝓝 (∏ i : Fin J, L (σ i) i)) := by
        have hrec : ∀ T : Finset (Fin J),
            Tendsto (fun X ↦ ∏ i ∈ T, M X (σ i) i) atTop (𝓝 (∏ i ∈ T, L (σ i) i)) := fun T ↦ by
          induction T using Finset.induction_on with
          | empty => simp
          | @insert i T hi ihT =>
            simp only [Finset.prod_insert hi]; exact (h (σ i) i).mul ihT
        exact hrec Finset.univ
      have hsm : Tendsto (fun X ↦ (Equiv.Perm.sign σ : ℤ) • ∏ i : Fin J, M X (σ i) i)
          atTop (𝓝 ((Equiv.Perm.sign σ : ℤ) • ∏ i : Fin J, L (σ i) i)) := by
        simpa [zsmul_eq_mul] using hprod.const_mul ((Equiv.Perm.sign σ : ℤ) : ℂ)
      exact hsm.add ih
  simpa only [Matrix.det_apply, Units.smul_def] using hsum Finset.univ

private lemma ppMapDomain_apply_inj {α β : Type*} {f : α → β} (hf : Function.Injective f)
    (x : α →₀ ℕ) (a : α) : (x.mapDomain f) (f a) = x a := by
  classical
  rw [Finsupp.mapDomain_apply, Finsupp.sum]
  by_cases ha : a ∈ x.support
  · rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hba
      exact Finsupp.single_eq_of_ne (fun h ↦ hba (hf h.symm))
    · intro h; exact (h ha).elim
  · rw [Finsupp.notMem_support_iff.mp ha]
    apply Finset.sum_eq_zero; intro b hb
    have hba : b ≠ a := fun h ↦ ha (h ▸ hb)
    exact Finsupp.single_eq_of_ne (fun h ↦ hba (hf h.symm))

private theorem logDerivPowerPart_dilations_diff_indep_dec {d : ℕ} (hd : 2 ≤ d)
    (P : PowerPartStokesProfile d hd) {s : ℕ} (a : Fin s → ℕ+)
    (hdec : ∀ i j : Fin s, i < j → (a j).val < (a i).val) :
    AlgebraicIndependent ℂ (logDerivPowerPartDilationCoordinates d a) := by
  classical
  have hd3 : 3 ≤ d + 1 := by omega
  let A : ℕ := ∏ i : Fin s, (a i).val
  have hA_pos : 0 < A := Finset.prod_pos fun i _ ↦ (a i).property
  have hA_dvd : ∀ i : Fin s, (a i).val ∣ A := fun i ↦
    Finset.dvd_prod_of_mem (fun k ↦ (a k).val) (Finset.mem_univ i)
  have hA_ge : ∀ i : Fin s, (a i).val ≤ A := fun i ↦ Nat.le_of_dvd hA_pos (hA_dvd i)
  have hdec_le : ∀ i j : Fin s, i ≤ j → (a j).val ≤ (a i).val := fun i j hij ↦ by
    rcases hij.eq_or_lt with rfl | hlt; exact le_rfl; exact (hdec i j hlt).le
  let _ : Algebra (Polynomial ℂ) RayGerm := (ppPolyToGerm d).toAlgebra
  have hpoly_inj : Function.Injective (algebraMap (Polynomial ℂ) RayGerm) := ppPolyToGerm_injective hd
  rw [algebraicIndependent_iff]
  intro Q hQ_eval
  let J : ℕ := (Q.vars.sup fun u ↦ Option.elim' 0 (fun ij ↦ ij.2) u) + 1
  have hQ_vars : ∀ u ∈ Q.vars, ∀ ij : Fin s × ℕ, u = some ij → ij.2 < J := by
    intro u hu ij heq; subst heq
    have hle : ij.2 ≤ Q.vars.sup fun u ↦ Option.elim' 0 (fun p ↦ p.2) u :=
      Finset.le_sup (f := fun u ↦ Option.elim' 0 (fun p ↦ p.2) u) hu
    omega
  let ι := Fin s ×ₗ Fin J
  let emb : Option ι → Option (Fin s × ℕ) := Option.map fun r ↦ ((ofLex r).1, (ofLex r).2.val)
  let liftVar : Option (Fin s × ℕ) → Option ι
    | none => none
    | some (i, j) => if h : j < J then some (toLex (i, ⟨j, h⟩)) else none
  let Q₀ : MvPolynomial (Option ι) ℂ := MvPolynomial.rename liftVar Q
  have hQ_eq : MvPolynomial.rename emb Q₀ = Q := by
    rw [MvPolynomial.rename_rename, MvPolynomial.rename_eq_aeval]
    have hcongr : ∀ u ∈ Q.vars, emb (liftVar u) = u := fun u hu ↦ by
      cases u with
      | none => rfl
      | some ij => simp only [liftVar, hQ_vars (some ij) hu ij rfl, ↓reduceDIte, emb, Option.map_some, ofLex_toLex]
    have h1 : MvPolynomial.aeval (MvPolynomial.X (R := ℂ) ∘ (emb ∘ liftVar)) Q =
        MvPolynomial.aeval (MvPolynomial.X (R := ℂ)) Q := by
      simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
      apply Finset.sum_congr rfl; intro m hm; congr 1
      apply Finsupp.prod_congr; intro u hu
      simp only [Function.comp_apply, hcongr u ((MvPolynomial.mem_vars_iff_mem_support u).mpr ⟨m, hm, hu⟩)]
    rw [h1]
    exact congrFun (congrArg DFunLike.coe (MvPolynomial.aeval_X_left (R := ℂ) (σ := Option (Fin s × ℕ)))) Q
  let Q₁ : MvPolynomial ι (Polynomial ℂ) := ppOptionToPolyMv ι Q₀
  let fTracked : ι → PPTracked d (ppDilKeyRate d A) :=
    fun r ↦ ppDilJetTracked hd P hA_pos (a (ofLex r).1) (hA_dvd (ofLex r).1) (ofLex r).2.val
  obtain ⟨E, hE_val, hE_marked⟩ := ppEvalPolyMv_tracked hd hA_pos fTracked Q₁
  have hE_zero : ∀ᶠ X : ℝ in atTop, E.exp.value X = 0 := by
    have hall_f : ∀ᶠ X : ℝ in atTop, ∀ r : ι,
        (fTracked r).exp.value X =
          psValue (formalJet (logDerivPowerPartDilated d (a (ofLex r).1).val) (ofLex r).2.val) (qRayD (d + 1) X) :=
      ((Filter.eventually_all_finset (Finset.univ : Finset ι)).mpr fun r _ ↦
        ppDilJetTracked_value hd P hA_pos (a (ofLex r).1) (hA_dvd (ofLex r).1) (ofLex r).2.val).mono
        fun X hX r ↦ hX r (Finset.mem_univ r)
    filter_upwards [eventually_gt_atTop (0 : ℝ), hE_val, hall_f] with X hX hEv hfv
    rw [hEv]
    have hcongr_ev : MvPolynomial.eval₂ (Polynomial.evalRingHom (qRayD (d + 1) X))
          (fun r ↦ (fTracked r).exp.value X) Q₁ =
        MvPolynomial.eval₂ (Polynomial.evalRingHom (qRayD (d + 1) X))
          (fun r ↦ psValue (formalJet (logDerivPowerPartDilated d (a (ofLex r).1).val) (ofLex r).2.val)
            (qRayD (d + 1) X)) Q₁ := by congr 1; funext r; exact hfv r
    rw [hcongr_ev, ppEval₂_optionToPolyMv]
    let g_X : Option (Fin s × ℕ) → ℂ := fun u ↦
      psValue (logDerivPowerPartDilationCoordinates d a u) (qRayD (d + 1) X)
    have hps_coord : Option.elim' (qRayD (d + 1) X)
          (fun r ↦ psValue (formalJet (logDerivPowerPartDilated d (a (ofLex r).1).val) (ofLex r).2.val)
            (qRayD (d + 1) X)) = g_X ∘ emb := by
      funext u; cases u with
      | none => exact (ps_nome_abs (qRayD (d + 1) X)).2.symm
      | some r => rfl
    have habs_coord : ∀ u : Option (Fin s × ℕ),
        PSAbsAt (logDerivPowerPartDilationCoordinates d a u) (qRayD (d + 1) X) := by
      rintro (_ | ⟨i, j⟩)
      · exact (ps_nome_abs _).1
      · exact ppLogDeriv_jet_abs d (a i).val j (qRayD_disk hX)
    rw [hps_coord, ← MvPolynomial.eval_rename emb g_X Q₀, hQ_eq]
    have hps := (ps_polynomial_value Q habs_coord).2
    rw [← hps, hQ_eval]; simp [psValue, psTerm]
  have hmarked_zero : MvPolynomial.aeval (R := Polynomial ℂ) (fun r ↦ (fTracked r).marked) Q₁ = 0 := by
    rw [← hE_marked]; exact E.separate_zero hE_zero
  -- Choose fresh primes `q_r > A` indexed by `ι = Fin s ×ₗ Fin J`.
  let idxEquiv : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let primeOf (r : ι) : ℕ+ :=
    ⟨Nat.nth Nat.Prime (A + (idxEquiv r).val + 1),
      (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _).pos⟩
  have hprime_prime (r : ι) : (primeOf r).val.Prime :=
    Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
  have hprime_gt_A (r : ι) : A < (primeOf r).val := by
    have hle : A + (idxEquiv r).val + 1 ≤ Nat.nth Nat.Prime (A + (idxEquiv r).val + 1) :=
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).id_le _
    change A < Nat.nth Nat.Prime (A + (idxEquiv r).val + 1); omega
  have hprime_inj : Function.Injective primeOf := fun r₁ r₂ h ↦
    idxEquiv.injective (Fin.ext (by
      have h1 := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective (congrArg Subtype.val h)
      omega))
  let marks : ι → Core d := fun r ↦ ppDilCore hd (a (ofLex r).1) (primeOf r)
  have hmarks_inj : Function.Injective marks := fun r₁ r₂ h ↦ by
    have h1 := (ppDilCore_prime_dvd_iff hd (a (ofLex r₁).1) (primeOf r₁) (hprime_prime r₁)
      (lt_of_le_of_lt (hA_ge _) (hprime_gt_A r₁))).1
    rw [show ppDilCore hd (a (ofLex r₁).1) (primeOf r₁) = marks r₁ from rfl, h] at h1
    have h2 := ((ppDilCore_prime_dvd_iff hd (a (ofLex r₂).1) (primeOf r₂) (hprime_prime r₂)
      (lt_of_le_of_lt (hA_ge _) (hprime_gt_A r₂))).2 (primeOf r₁).val (hprime_prime r₁)
      (lt_of_le_of_lt (hA_ge _) (hprime_gt_A r₁))).mp h1
    exact hprime_inj (PNat.eq h2)
  let restr : MvPowerSeries (Core d) RayGerm →+* MvPowerSeries ι RayGerm :=
    restrictVars marks hmarks_inj
  let fRestr : ι → MvPowerSeries ι RayGerm := fun r ↦ restr (fTracked r).marked
  let Jac : Matrix ι ι (MvPowerSeries ι RayGerm) :=
    Matrix.of fun r c ↦ MvPowerSeries.pderiv r (fRestr c)
  have hJac_single : ∀ (r c : ι) (m : ι →₀ ℕ),
      MvPowerSeries.coeff m (Jac r c) ≠ 0 →
        ∃ N : ℕ+, ppDilCore hd (a (ofLex c).1) N = marks r ∧
          m = Finsupp.single r (ppDilExp hd A (a (ofLex c).1) N - 1) := by
    intro r c m hm
    change MvPowerSeries.coeff m (MvPowerSeries.pderiv r (fRestr c)) ≠ 0 at hm
    rw [MvPowerSeries.coeff_pderiv] at hm
    have hc_nz : MvPowerSeries.coeff ((m + Finsupp.single r 1).mapDomain marks) (fTracked c).marked ≠ 0 :=
      left_ne_zero_of_mul hm
    rw [show fTracked c = ppDilJetTracked hd P hA_pos (a (ofLex c).1) (hA_dvd (ofLex c).1) (ofLex c).2.val from rfl,
        ppDilJetTracked_marked_eq, map_sum] at hc_nz
    obtain ⟨ℓ, _, hℓ_nz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc_nz
    rw [MvPowerSeries.coeff_C_mul] at hℓ_nz
    have hadd_nz := right_ne_zero_of_mul hℓ_nz
    have hmap_ne0 : (m + Finsupp.single r 1).mapDomain marks ≠ 0 := fun h0 ↦ by
      have h1 := DFunLike.congr_fun h0 (marks r)
      rw [ppMapDomain_apply_inj hmarks_inj, Finsupp.add_apply, Finsupp.single_eq_same] at h1
      simp at h1
    rw [map_add, MvPowerSeries.coeff_C] at hadd_nz
    simp only [hmap_ne0, ↓reduceIte, zero_add] at hadd_nz
    have hex : ∃ N : ℕ+, (m + Finsupp.single r 1).mapDomain marks = ppDilModeExp hd A (a (ofLex c).1) N := by
      by_contra hnot; push Not at hnot
      exact hadd_nz ((ppDilWaveTracked_coeff hd hA_pos (a (ofLex c).1) (hA_dvd (ofLex c).1) ℓ _).1 hnot)
    obtain ⟨N, hN⟩ := hex
    have he_pos := ppDilExp_pos hd hA_pos (hA_dvd (ofLex c).1) N
    have hcore_eq : ppDilCore hd (a (ofLex c).1) N = marks r := by
      by_contra hne_c
      have h1 := DFunLike.congr_fun hN (marks r)
      rw [ppMapDomain_apply_inj hmarks_inj, Finsupp.add_apply, Finsupp.single_eq_same,
          ppDilModeExp, Finsupp.single_eq_of_ne (Ne.symm hne_c)] at h1
      omega
    have hm_single : m = Finsupp.single r (ppDilExp hd A (a (ofLex c).1) N - 1) := by
      ext x
      have h1 := DFunLike.congr_fun hN (marks x)
      rw [ppMapDomain_apply_inj hmarks_inj, Finsupp.add_apply, ppDilModeExp, hcore_eq] at h1
      by_cases hxr : x = r
      · subst hxr; simp only [Finsupp.single_eq_same] at h1 ⊢; omega
      · have hmx : marks x ≠ marks r := fun h ↦ hxr (hmarks_inj h)
        simp only [Finsupp.single_eq_of_ne hmx, Finsupp.single_eq_of_ne hxr, add_zero] at h1 ⊢
        exact h1
    exact ⟨N, hcore_eq, hm_single⟩
  let mStar : ι →₀ ℕ := Finsupp.onFinset Finset.univ
    (fun r ↦ ppDilExp hd A (a (ofLex r).1) (primeOf r) - 1) (fun _ _ ↦ Finset.mem_univ _)
  have hmStar_apply (r : ι) : mStar r = ppDilExp hd A (a (ofLex r).1) (primeOf r) - 1 := rfl
  -- Step A: `mStar` is the lexicographically minimal nonzero monomial of `Jac.det`!
  have hmin : ∀ m : ι →₀ ℕ, MvPowerSeries.coeff m Jac.det ≠ 0 → toLex mStar ≤ toLex m := by
    intro m hm
    rw [Matrix.det_apply, map_sum] at hm
    obtain ⟨π, _, hπ_nz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    rw [Units.smul_def, map_zsmul] at hπ_nz
    have hprod_nz : MvPowerSeries.coeff m (∏ r : ι, Jac r (π.symm r)) ≠ 0 := by
      have hprod_eq : (∏ r : ι, Jac (π r) r) = ∏ r : ι, Jac r (π.symm r) :=
        Fintype.prod_equiv π _ (fun r ↦ Jac r (π.symm r)) fun r ↦ by simp
      rw [← hprod_eq]; intro h0; exact hπ_nz (by rw [h0, smul_zero])
    rw [ppCoeff_prod_singleVar (fun r ↦ Jac r (π.symm r))
        (fun r m' hm' ↦ by obtain ⟨N, _, rfl⟩ := hJac_single r (π.symm r) m' hm'; exact ⟨_, rfl⟩)] at hprod_nz
    have hrow_nz (r : ι) : MvPowerSeries.coeff (Finsupp.single r (m r)) (Jac r (π.symm r)) ≠ 0 :=
      fun h0 ↦ hprod_nz (Finset.prod_eq_zero (Finset.mem_univ r) h0)
    by_contra hlt_lex
    have hlt : toLex m < toLex mStar := lt_of_not_ge hlt_lex
    obtain ⟨r₀, hprefix, hr₀_lt⟩ := (Finsupp.Lex.lt_iff).mp hlt
    have hblock_fixed : ∀ k : ℕ, k ≤ (ofLex r₀).1.val →
        ∀ r : ι, (ofLex r).1.val < k → (ofLex (π.symm r)).1 = (ofLex r).1 := by
      intro k
      induction k with
      | zero => intro _ r hr; omega
      | succ k ihk =>
        intro hk r hr
        by_cases hrk : (ofLex r).1.val < k
        · exact ihk (by omega) r hrk
        · have hr_eq : (ofLex r).1.val = k := by omega
          have hr_lt_r₀ : r < r₀ := Prod.Lex.left _ _ (show (ofLex r).1 < (ofLex r₀).1 by
            exact Fin.lt_def.mpr (by omega))
          have hmr_eq : m r = mStar r := hprefix r hr_lt_r₀
          obtain ⟨N, hcore, hm_single⟩ := hJac_single r (π.symm r) _ (hrow_nz r)
          have hmr_val : m r = ppDilExp hd A (a (ofLex (π.symm r)).1) N - 1 := by
            have := DFunLike.congr_fun hm_single r; simpa only [Finsupp.single_eq_same] using this
          have hge_block : k ≤ (ofLex (π.symm r)).1.val := by
            by_contra hlt_k
            let S : Finset ι := Finset.univ.filter fun x ↦ (ofLex x).1.val < k
            have hmaps : Set.MapsTo (π.symm : ι → ι) S S := fun x hx ↦ by
              simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
              rw [ihk (by omega) x hx]; exact hx
            have hsurj := Finset.surjOn_of_injOn_of_card_le _ (fun x hx ↦ hmaps hx)
              π.symm.injective.injOn le_rfl
            have hmemS : π.symm r ∈ (S : Set ι) := by
              simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_univ, true_and]; omega
            obtain ⟨x, hxS, hxeq⟩ := hsurj hmemS
            have hxr : x = r := π.symm.injective hxeq
            subst hxr
            simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_univ, true_and] at hxS
            omega
          have hle_a : (a (ofLex (π.symm r)).1).val ≤ (a (ofLex r).1).val :=
            hdec_le (ofLex r).1 (ofLex (π.symm r)).1 (Fin.le_def.mpr (by omega))
          have hdom := ppDil_block_dominance hd hA_pos (hA_dvd (ofLex r).1) (hA_dvd (ofLex (π.symm r)).1)
            (hprime_prime r) (lt_of_le_of_lt (hA_ge _) (hprime_gt_A r))
            (lt_of_le_of_lt (hA_ge _) (hprime_gt_A r)) hle_a hcore
          have he_eq : ppDilExp hd A (a (ofLex (π.symm r)).1) N = ppDilExp hd A (a (ofLex r).1) (primeOf r) := by
            have h1 := ppDilExp_pos hd hA_pos (hA_dvd (ofLex r).1) (primeOf r)
            have h2 := ppDilExp_pos hd hA_pos (hA_dvd (ofLex (π.symm r)).1) N
            rw [hmr_eq, hmStar_apply] at hmr_val; omega
          have ha_eq := (hdom.2 he_eq).1
          by_contra hne_blk
          rcases lt_or_gt_of_ne hne_blk with hlt' | hgt'
          · exact (hdec _ _ hlt').ne (congrArg Subtype.val ha_eq).symm
          · exact (hdec _ _ hgt').ne (congrArg Subtype.val ha_eq)
    have hge_r₀ : (ofLex r₀).1.val ≤ (ofLex (π.symm r₀)).1.val := by
      by_contra hlt_k
      let S : Finset ι := Finset.univ.filter fun x ↦ (ofLex x).1.val < (ofLex r₀).1.val
      have hmaps : Set.MapsTo (π.symm : ι → ι) S S := fun x hx ↦ by
        simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        rw [hblock_fixed (ofLex r₀).1.val le_rfl x hx]; exact hx
      have hsurj := Finset.surjOn_of_injOn_of_card_le _ (fun x hx ↦ hmaps hx)
        π.symm.injective.injOn le_rfl
      have hmemS : π.symm r₀ ∈ (S : Set ι) := by
        simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_univ, true_and]; omega
      obtain ⟨x, hxS, hxeq⟩ := hsurj hmemS
      have hxr : x = r₀ := π.symm.injective hxeq
      subst hxr
      simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_univ, true_and] at hxS
      omega
    obtain ⟨N₀, hcore₀, hm_single₀⟩ := hJac_single r₀ (π.symm r₀) _ (hrow_nz r₀)
    have hmr₀ : m r₀ = ppDilExp hd A (a (ofLex (π.symm r₀)).1) N₀ - 1 := by
      have := DFunLike.congr_fun hm_single₀ r₀; simpa only [Finsupp.single_eq_same] using this
    have hdom₀ := (ppDil_block_dominance hd hA_pos (hA_dvd (ofLex r₀).1) (hA_dvd (ofLex (π.symm r₀)).1)
      (hprime_prime r₀) (lt_of_le_of_lt (hA_ge _) (hprime_gt_A r₀))
      (lt_of_le_of_lt (hA_ge _) (hprime_gt_A r₀)) (hdec_le _ _ hge_r₀) hcore₀).1
    have hlt_r₀' : m r₀ < ppDilExp hd A (a (ofLex r₀).1) (primeOf r₀) - 1 := hr₀_lt
    omega
  -- Step B: Leading coefficient `coeff mStar Jac.det` equals `B.det` for a block-triangular matrix `B`
  -- with Vandermonde-unit diagonal blocks in `RayGerm`!
  let B : Matrix ι ι RayGerm :=
    Matrix.of fun r c ↦ MvPowerSeries.coeff (Finsupp.single r (mStar r)) (Jac r c)
  have hcoeff_det : MvPowerSeries.coeff mStar Jac.det = B.det := by
    rw [Matrix.det_apply, Matrix.det_apply, map_sum]
    apply Finset.sum_congr rfl; intro π _
    rw [Units.smul_def, Units.smul_def, map_zsmul]; congr 1
    have hprod_eq : (∏ r : ι, Jac (π r) r) = ∏ r : ι, Jac r (π.symm r) :=
      Fintype.prod_equiv π _ (fun r ↦ Jac r (π.symm r)) fun r ↦ by simp
    have hprod_B : (∏ r : ι, B (π r) r) = ∏ r : ι, B r (π.symm r) :=
      Fintype.prod_equiv π _ (fun r ↦ B r (π.symm r)) fun r ↦ by simp
    rw [hprod_eq, hprod_B, ppCoeff_prod_singleVar (fun r ↦ Jac r (π.symm r))
        (fun r m' hm' ↦ by obtain ⟨N, _, rfl⟩ := hJac_single r (π.symm r) m' hm'; exact ⟨_, rfl⟩)]
    rfl
  let blk (r : ι) : Fin s := (ofLex r).1
  have hB_tri : Bᵀ.BlockTriangular blk := by
    intro c r hlt; change B r c = 0; by_contra hnz
    obtain ⟨N, hcore, hm_single⟩ := hJac_single r c _ hnz
    have hmr : mStar r = ppDilExp hd A (a (ofLex c).1) N - 1 := by
      have := DFunLike.congr_fun hm_single r; simpa only [Finsupp.single_eq_same] using this
    have hdom := ppDil_block_dominance hd hA_pos (hA_dvd (ofLex r).1) (hA_dvd (ofLex c).1)
      (hprime_prime r) (lt_of_le_of_lt (hA_ge _) (hprime_gt_A r))
      (lt_of_le_of_lt (hA_ge _) (hprime_gt_A r)) (hdec_le _ _ hlt.le) hcore
    have he_eq : ppDilExp hd A (a (ofLex c).1) N = ppDilExp hd A (a (ofLex r).1) (primeOf r) := by
      have h1 := ppDilExp_pos hd hA_pos (hA_dvd (ofLex r).1) (primeOf r)
      have h2 := ppDilExp_pos hd hA_pos (hA_dvd (ofLex c).1) N
      rw [hmStar_apply] at hmr; omega
    exact (hdec (ofLex r).1 (ofLex c).1 hlt).ne (congrArg Subtype.val (hdom.2 he_eq).1)
  have hB_det : B.det = ∏ i : Fin s, (Matrix.of fun ν j : Fin J ↦ B (toLex (i, ν)) (toLex (i, j))).det := by
    rw [← Matrix.det_transpose, hB_tri.det_fintype]
    apply Finset.prod_congr rfl; intro i _
    let e : {x : ι // blk x = i} ≃ Fin J :=
      { toFun := fun x ↦ (ofLex x.val).2
        invFun := fun ν ↦ ⟨toLex (i, ν), rfl⟩
        left_inv := fun ⟨x, hx⟩ ↦ Subtype.ext (ofLex.injective (Prod.ext hx.symm rfl))
        right_inv := fun _ ↦ rfl }
    rw [← Matrix.det_reindex_self e (Bᵀ.toSquareBlock blk i), ← Matrix.det_transpose]; rfl
  have hblock_unit (i : Fin s) :
      IsUnit (Matrix.of fun ν j : Fin J ↦ B (toLex (i, ν)) (toLex (i, j))).det := by
    let σ := ppDilScale d (a i).val
    let hσ := ppDilScale_pos (d := d) (a i).pos
    let M (X : ℝ) : Matrix (Fin J) (Fin J) ℂ :=
      Matrix.of fun ν j ↦ ((ppDilExp hd A (a i) (primeOf (toLex (i, ν))) : ℕ) : ℂ) *
        ∑ ℓ ∈ Finset.range (j.val + 1),
          qPolyCoeff (d + 1) j.val ℓ X *
            (ppDilWaveExp d hd σ hσ ℓ).amplitude (⟨0, by omega⟩, primeOf (toLex (i, ν))) X
    have hB_eq (ν j : Fin J) : B (toLex (i, ν)) (toLex (i, j)) = Germ.ofFun (fun X ↦ M X ν j) := by
      let r := toLex (i, ν); let c := toLex (i, j)
      change MvPowerSeries.coeff (Finsupp.single r (mStar r)) (MvPowerSeries.pderiv r (fRestr c)) = _
      rw [MvPowerSeries.coeff_pderiv]
      have he_pos := ppDilExp_pos hd hA_pos (hA_dvd i) (primeOf r)
      have hmr_eq : mStar r = ppDilExp hd A (a i) (primeOf r) - 1 := rfl
      have hsucc : mStar r + 1 = ppDilExp hd A (a i) (primeOf r) := by
        rw [hmr_eq]; exact Nat.sub_add_cancel he_pos
      have hadd_s : Finsupp.single r (mStar r) + Finsupp.single r 1 =
          Finsupp.single r (ppDilExp hd A (a i) (primeOf r)) := by rw [← Finsupp.single_add, hsucc]
      have hmap_s : (Finsupp.single r (ppDilExp hd A (a i) (primeOf r))).mapDomain marks =
          ppDilModeExp hd A (a i) (primeOf r) := by rw [Finsupp.mapDomain_single]; rfl
      have hmode_ne0 : ppDilModeExp hd A (a i) (primeOf r) ≠ 0 := fun h0 ↦ by
        have := DFunLike.congr_fun h0 (ppDilCore hd (a i) (primeOf r))
        simp only [ppDilModeExp, Finsupp.single_eq_same, Finsupp.coe_zero, Pi.zero_apply] at this
        exact he_pos.ne' this
      rw [Finsupp.single_eq_same, hadd_s]
      change MvPowerSeries.coeff ((Finsupp.single r (ppDilExp hd A (a i) (primeOf r))).mapDomain marks)
        (fTracked c).marked * ((mStar r : RayGerm) + 1) = _
      rw [hmap_s, show fTracked c = ppDilJetTracked hd P hA_pos (a i) (hA_dvd i) j.val from rfl,
          ppDilJetTracked_marked_eq, map_sum]
      have hterm_eq (ℓ : ℕ) :
          MvPowerSeries.coeff (ppDilModeExp hd A (a i) (primeOf r))
            (MvPowerSeries.C (Germ.ofFun (qPolyCoeff (d + 1) j.val ℓ)) *
              (MvPowerSeries.C (Germ.ofFun (ppDilPolarCoeff hd P σ hσ ℓ).value) +
                (ppDilWaveTracked hd hA_pos (a i) (hA_dvd i) ℓ).marked)) =
          Germ.ofFun (fun X ↦ qPolyCoeff (d + 1) j.val ℓ X *
            (ppDilWaveExp d hd σ hσ ℓ).amplitude (⟨0, by omega⟩, primeOf r) X) := by
        rw [MvPowerSeries.coeff_C_mul, map_add, MvPowerSeries.coeff_C]
        simp only [hmode_ne0, ↓reduceIte, zero_add]
        rw [(ppDilWaveTracked_coeff hd hA_pos (a i) (hA_dvd i) ℓ _).2 (primeOf r) rfl]; rfl
      rw [Finset.sum_congr rfl (fun ℓ _ ↦ hterm_eq ℓ)]
      have hnat : ((mStar r : RayGerm) + 1) =
          Germ.ofFun (fun _ : ℝ ↦ ((ppDilExp hd A (a i) (primeOf r) : ℕ) : ℂ)) := by
        rw [show ((mStar r : RayGerm) + 1) = ((mStar r + 1 : ℕ) : RayGerm) by push_cast; rfl, hsucc]; rfl
      rw [hnat, mul_comm]
      let H := Germ.coeRingHom (atTop : Filter ℝ) (R := ℂ)
      change H _ * ∑ ℓ ∈ Finset.range (j.val + 1), H _ = _
      rw [← map_sum, ← map_mul]; apply Germ.coe_eq.mpr
      filter_upwards with X
      change ((ppDilExp hd A (a i) (primeOf r) : ℕ) : ℂ) *
        (∑ ℓ ∈ Finset.range (j.val + 1), fun X ↦ qPolyCoeff (d + 1) j.val ℓ X *
          (ppDilWaveExp d hd σ hσ ℓ).amplitude (⟨0, by omega⟩, primeOf r) X) X = M X ν j
      rw [Finset.sum_apply]; rfl
    have hdet_germ : (Matrix.of fun ν j : Fin J ↦ B (toLex (i, ν)) (toLex (i, j))).det =
        Germ.ofFun (fun X ↦ (M X).det) := by
      let H := Germ.coeRingHom (atTop : Filter ℝ) (R := ℂ)
      have hmat : (Matrix.of fun ν j : Fin J ↦ B (toLex (i, ν)) (toLex (i, j))) =
          H.mapMatrix (Matrix.of fun ν j : Fin J ↦ fun X ↦ M X ν j) := by ext ν j; exact hB_eq ν j
      rw [hmat, ← RingHom.map_det]; apply Germ.coe_eq.mpr
      filter_upwards with X
      simp only [Matrix.det_apply, Finset.sum_apply, Pi.smul_apply, Finset.prod_apply, Matrix.of_apply]
    rw [hdet_germ]
    let colScale (X : ℝ) (j : Fin J) : ℂ :=
      ((X ^ (-(((d + 1) * j.val : ℕ) : ℝ) - ((d + 1 : ℕ) : ℝ)) : ℝ) : ℂ)
    let Mscaled (X : ℝ) : Matrix (Fin J) (Fin J) ℂ := Matrix.of fun ν j ↦ colScale X j * M X ν j
    let rowC (ν : Fin J) : ℂ := ((ppDilExp hd A (a i) (primeOf (toLex (i, ν))) : ℕ) : ℂ) *
      (-ppWaveRate d ⟨0, by omega⟩ (primeOf (toLex (i, ν)))) *
      ((d : ℂ)⁻¹ * (σ : ℂ) ^ (d + 1))
    let α (ν : Fin J) : ℂ := -(((d : ℂ)⁻¹) * (((σ : ℝ) : ℂ) * ppWaveRate d ⟨0, by omega⟩ (primeOf (toLex (i, ν)))))
    let L : Matrix (Fin J) (Fin J) ℂ := Matrix.of fun ν j ↦ rowC ν * (α ν) ^ j.val
    have hlim_entry (ν j : Fin J) : Tendsto (fun X ↦ Mscaled X ν j) atTop (𝓝 (L ν j)) := by
      have hterm_lim (ℓ : ℕ) (hℓ : ℓ ∈ Finset.range (j.val + 1)) :
          Tendsto (fun X : ℝ ↦ colScale X j * (qPolyCoeff (d + 1) j.val ℓ X *
            (ppDilWaveExp d hd σ hσ ℓ).amplitude (⟨0, by omega⟩, primeOf (toLex (i, ν))) X))
          atTop (𝓝 (if ℓ = j.val then
            (-ppWaveRate d ⟨0, by omega⟩ (primeOf (toLex (i, ν)))) *
              ((d : ℂ)⁻¹ * (σ : ℂ) ^ (d + 1)) * (α ν) ^ j.val else 0)) := by
        have hℓ_le : ℓ ≤ j.val := by have := Finset.mem_range.mp hℓ; omega
        have hamp_lim := (ppDilAmp_limit d σ (ppWaveRate d ⟨0, by omega⟩ (primeOf (toLex (i, ν)))) ℓ).const_mul
          (-((powerPartMult d (primeOf (toLex (i, ν))).val : ℝ) : ℂ) *
            ppWaveRate d ⟨0, by omega⟩ (primeOf (toLex (i, ν))))
        rw [powerPartMult_prime hd (hprime_prime (toLex (i, ν))), Complex.ofReal_one, neg_mul, one_mul] at hamp_lim
        by_cases hℓj : ℓ = j.val
        · subst hℓj; simp only [↓reduceIte]
          have hq_lim := qPolyCoeff_diag_limit (d := d + 1) hd3 j.val
          have hprod := hq_lim.mul hamp_lim
          have hlim_eq : ((((d + 1 - 1 : ℕ) : ℂ)⁻¹) ^ j.val) *
              ((-ppWaveRate d ⟨0, by omega⟩ (primeOf (toLex (i, ν)))) *
                (((d : ℂ)⁻¹ * (σ : ℂ) ^ (d + 1)) * (-(((σ : ℝ) : ℂ) * ppWaveRate d ⟨0, by omega⟩ (primeOf (toLex (i, ν))))) ^ j.val)) =
              (-ppWaveRate d ⟨0, by omega⟩ (primeOf (toLex (i, ν)))) *
                ((d : ℂ)⁻¹ * (σ : ℂ) ^ (d + 1)) * (α ν) ^ j.val := by
            have hdsub : (d + 1 - 1 : ℕ) = d := by omega
            rw [hdsub]; dsimp only [α]
            rw [show -((d : ℂ)⁻¹ * (((σ : ℝ) : ℂ) * ppWaveRate d ⟨0, by omega⟩ (primeOf (toLex (i, ν))))) =
                (d : ℂ)⁻¹ * (-(((σ : ℝ) : ℂ) * ppWaveRate d ⟨0, by omega⟩ (primeOf (toLex (i, ν))))) by ring, mul_pow]
            ring
          rw [hlim_eq] at hprod
          refine hprod.congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
          have hcol : colScale X j =
              ((X ^ (-(((d + 1) * j.val : ℕ) : ℝ)) : ℝ) : ℂ) * ((X ^ (-((d + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
            dsimp [colScale]; rw [← Complex.ofReal_mul, ← Real.rpow_add hX]; congr 2
          rw [hcol]
          change ((X ^ (-(((d + 1) * j.val : ℕ) : ℝ)) : ℝ) : ℂ) * qPolyCoeff (d + 1) j.val j.val X *
            (-ppWaveRate d ⟨0, by omega⟩ (primeOf (toLex (i, ν))) *
              (((X ^ (-((d + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
                ppDilAmp d σ (ppWaveRate d ⟨0, by omega⟩ (primeOf (toLex (i, ν)))) j.val X)) = _
          simp only [ppDilWaveExp, powerPartMult_prime hd (hprime_prime (toLex (i, ν))),
            Complex.ofReal_one, neg_mul, one_mul]
          ring
        · simp only [hℓj, ↓reduceIte]
          have hlt : (((d + 1 : ℤ) * (j.val : ℤ)) - ((j.val - ℓ : ℕ) : ℤ)) < (((d + 1) * j.val : ℕ) : ℤ) := by
            have : 0 < j.val - ℓ := by omega
            push_cast; omega
          have hq_lim := (qPolyCoeff_QCoeff (d := d + 1) hd3 j.val ℓ hℓ_le).tendsto_zero_of_lt hd3 hlt
          have hprod := hq_lim.mul hamp_lim
          rw [zero_mul] at hprod
          refine hprod.congr' ?_
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
          have hcol : colScale X j =
              ((X ^ (-((((d + 1) * j.val : ℕ) : ℤ) : ℝ)) : ℝ) : ℂ) * ((X ^ (-((d + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
            dsimp [colScale]; rw [← Complex.ofReal_mul, ← Real.rpow_add hX]; congr 2
          rw [hcol]
          change ((X ^ (-((((d + 1) * j.val : ℕ) : ℤ) : ℝ)) : ℝ) : ℂ) * qPolyCoeff (d + 1) j.val ℓ X *
            (-ppWaveRate d ⟨0, by omega⟩ (primeOf (toLex (i, ν))) *
              (((X ^ (-((d + 1 : ℕ) : ℝ)) : ℝ) : ℂ) *
                ppDilAmp d σ (ppWaveRate d ⟨0, by omega⟩ (primeOf (toLex (i, ν)))) ℓ X)) = _
          simp only [ppDilWaveExp, powerPartMult_prime hd (hprime_prime (toLex (i, ν))),
            Complex.ofReal_one, neg_mul, one_mul]
          ring
      have hsum := (tendsto_finsetSum (Finset.range (j.val + 1)) hterm_lim).const_mul
        ((ppDilExp hd A (a i) (primeOf (toLex (i, ν))) : ℕ) : ℂ)
      rw [Finset.sum_ite_eq' (Finset.range (j.val + 1)) j.val] at hsum
      simp only [Finset.mem_range.mpr (Nat.lt_succ_self j.val), ↓reduceIte] at hsum
      have hL_eq : ((ppDilExp hd A (a i) (primeOf (toLex (i, ν))) : ℕ) : ℂ) *
          ((-ppWaveRate d ⟨0, by omega⟩ (primeOf (toLex (i, ν)))) *
            ((d : ℂ)⁻¹ * (σ : ℂ) ^ (d + 1)) * (α ν) ^ j.val) = L ν j := by
        simp only [L, rowC, Matrix.of_apply]; ring
      rw [hL_eq] at hsum
      refine hsum.congr fun X ↦ ?_
      simp only [Mscaled, M, Matrix.of_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro ℓ _; ring
    have hlim_det := ppTendsto_matrix_det Mscaled L hlim_entry
    have hL_det_ne0 : L.det ≠ 0 := by
      have hL_eq : L = Matrix.diagonal rowC * Matrix.vandermonde α := by
        ext ν j; simp only [L, Matrix.of_apply, Matrix.diagonal_mul, Matrix.vandermonde_apply]
      rw [hL_eq, Matrix.det_mul, Matrix.det_diagonal]
      have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
      have hσ0 : (σ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ.ne'
      have hd_pos : (0 : ℝ) < 1 / (d : ℝ) := by
        have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
        positivity
      apply mul_ne_zero
      · apply Finset.prod_ne_zero_iff.mpr; intro ν _
        have hrate_ne : ppWaveRate d ⟨0, by omega⟩ (primeOf (toLex (i, ν))) ≠ 0 :=
          mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by exact_mod_cast (primeOf _).property) _).ne')
            (ppExtremeRay_ne_zero hd)
        exact mul_ne_zero (mul_ne_zero (by exact_mod_cast (ppDilExp_pos hd hA_pos (hA_dvd i) _).ne')
          (neg_ne_zero.mpr hrate_ne)) (mul_ne_zero (inv_ne_zero hd0) (pow_ne_zero _ hσ0))
      · rw [Matrix.det_vandermonde_ne_zero_iff]
        intro ν₁ ν₂ hα
        have h1 := neg_inj.mp hα
        have h2 := mul_left_cancel₀ (inv_ne_zero hd0) h1
        have h3 := mul_left_cancel₀ hσ0 h2
        have h4 := Complex.ofReal_injective (mul_right_cancel₀ (ppExtremeRay_ne_zero hd) h3)
        have h5 := Nat.cast_injective ((Real.rpow_left_inj (Nat.cast_nonneg _) (Nat.cast_nonneg _) hd_pos.ne').mp h4)
        exact congrArg (fun x ↦ (ofLex x).2) (hprime_inj (PNat.eq h5))
    have hev_nz : ∀ᶠ X : ℝ in atTop, (M X).det ≠ 0 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ), hlim_det.eventually_ne hL_det_ne0] with X _ hsc
      have hsc_eq : Mscaled X = M X * Matrix.diagonal (colScale X) := by
        ext ν j; simp only [Mscaled, Matrix.of_apply, Matrix.mul_diagonal]; ring
      rw [hsc_eq, Matrix.det_mul, Matrix.det_diagonal] at hsc
      exact left_ne_zero_of_mul hsc
    refine isUnit_iff_exists_inv.mpr ⟨Germ.ofFun (fun X ↦ ((M X).det)⁻¹), ?_⟩
    apply Germ.coe_eq.mpr
    filter_upwards [hev_nz] with X hX; exact mul_inv_cancel₀ hX
  have hunit_det : IsUnit (MvPowerSeries.coeff mStar Jac.det) := by
    rw [hcoeff_det, hB_det]
    exact Finset.prod_induction _ (fun x ↦ IsUnit x) (fun _ _ ha hb ↦ ha.mul hb) isUnit_one
      (fun i _ ↦ hblock_unit i)
  have hnzd : Jac.det ∈ nonZeroDivisors (MvPowerSeries ι RayGerm) :=
    lex_nonZeroDivisor_of_unit Jac.det mStar hunit_det hmin
  have hindep : AlgebraicIndependent (Polynomial ℂ) fRestr :=
    independent_of_marked_jacobian_domain hpoly_inj id fRestr hnzd
  have hrestr_alg (P : MvPolynomial ι (Polynomial ℂ)) :
      MvPolynomial.aeval (R := Polynomial ℂ) fRestr P =
        restr (MvPolynomial.aeval (R := Polynomial ℂ) (fun r ↦ (fTracked r).marked) P) := by
    induction P using MvPolynomial.induction_on with
    | C R =>
      simp only [MvPolynomial.aeval_C, MvPowerSeries.algebraMap_apply]
      exact (restrictVars_C marks hmarks_inj (algebraMap (Polynomial ℂ) RayGerm R)).symm
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p r hp => simp only [map_mul, MvPolynomial.aeval_X, hp]; rfl
  have hQ₁_zero : Q₁ = 0 := (algebraicIndependent_iff.mp hindep) Q₁ (by rw [hrestr_alg, hmarked_zero, map_zero])
  have hQ₀_zero : Q₀ = 0 := ppOptionToPolyMv_injective ι (hQ₁_zero.trans (map_zero _).symm)
  rw [← hQ_eq, hQ₀_zero, map_zero]

/-- **All-`d` Joint Differential Independence of Distinct Power-Partition Log-Derivative Dilations (`d ≥ 2`)**:
For EVERY `d ≥ 2`, given `P : PowerPartStokesProfile d hd` and ANY finite family of distinct
positive integers `a_1, …, a_s`, `{F_d(q^{a_1}), …, F_d(q^{a_s})}` are jointly
differentially independent over `ℂ(q)`. -/
theorem logDerivPowerPart_dilations_diff_indep {d : ℕ} (hd : 2 ≤ d)
    (P : PowerPartStokesProfile d hd) {s : ℕ} (a : Fin s → ℕ+) (ha : Function.Injective a) :
    AlgebraicIndependent ℂ (logDerivPowerPartDilationCoordinates d a) := by
  classical
  let S : Finset ℕ := Finset.univ.image fun i : Fin s ↦ (a i).val
  have hcard : S.card = s := by
    rw [Finset.card_image_of_injective _ (fun _ _ h ↦ ha (PNat.eq h)), Finset.card_fin]
  let ord : Fin s ≃o S := S.orderIsoOfFin hcard
  have hex : ∀ k : Fin s, ∃ i : Fin s, (a i).val = (ord (Fin.rev k)).val := fun k ↦ by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (ord (Fin.rev k)).property
    exact ⟨i, hi⟩
  let fπ : Fin s → Fin s := fun k ↦ Classical.choose (hex k)
  have hfπ_val (k : Fin s) : (a (fπ k)).val = (ord (Fin.rev k)).val := Classical.choose_spec (hex k)
  have hdec : ∀ i j : Fin s, i < j → (a (fπ j)).val < (a (fπ i)).val := fun i j hij ↦ by
    rw [hfπ_val i, hfπ_val j]; exact ord.strictMono (Fin.rev_lt_rev.mpr hij)
  have hfπ_inj : Function.Injective fπ := fun i j hij ↦ by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (hdec i j hlt).ne (by rw [hij])
    · exact (hdec j i hgt).ne (by rw [hij])
  let π : Fin s ≃ Fin s := Equiv.ofBijective fπ (Finite.injective_iff_bijective.mp hfπ_inj)
  have hindep_dec := logDerivPowerPart_dilations_diff_indep_dec hd P (a ∘ π) hdec
  let e : Option (Fin s × ℕ) ≃ Option (Fin s × ℕ) :=
    Equiv.optionCongr (π.prodCongr (Equiv.refl ℕ))
  have hcomp : logDerivPowerPartDilationCoordinates d (a ∘ π) =
      logDerivPowerPartDilationCoordinates d a ∘ e := by funext u; cases u <;> rfl
  rw [hcomp] at hindep_dec
  exact (algebraicIndependent_equiv' e rfl).mp hindep_dec

/-- **All-`d` Joint Differential Independence of Distinct Power-Partition Product Dilations (`d ≥ 2`)**:
For EVERY `d ≥ 2`, given `P : PowerPartStokesProfile d hd` and ANY finite family of distinct
positive integers `a_1, …, a_s`, `{P_d(q^{a_1}), …, P_d(q^{a_s})}` are jointly
differentially independent over `ℂ(q)`! -/
theorem powerPart_dilations_diff_indep {d : ℕ} (hd : 2 ≤ d)
    (P : PowerPartStokesProfile d hd) {s : ℕ} (a : Fin s → ℕ+) (ha : Function.Injective a) :
    AlgebraicIndependent ℂ (powerPartDilationCoordinates d a) :=
  kolchin_logDeriv_joint_indep
    (fun i ↦ logDerivPowerPartDilated d (a i).val)
    (fun i ↦ powerPartDilated d (a i).val)
    (fun i ↦ ((a i).val : ℂ))
    (fun i ↦ powerPartDilated_ne_zero d (a i).val)
    (fun i ↦ by exact_mod_cast (a i).property.ne')
    (fun i ↦ X_mul_deriv_powerPartDilated (by omega) (a i).property)
    (logDerivPowerPart_dilations_diff_indep hd P a ha)

end Dilations

/-! ### 6. 100% UNCONDITIONAL `d = 2` (Partitions into Squares `P_2(q) = ∏_{n ≥ 1} (1 - q^{n²})^{-1}`)! -/

private lemma ppRay_two_zero : ppRay 2 0 = sqRay0 := by
  unfold ppRay ppAngle sqRay0
  have hangle : Real.pi * (((2 : ℕ) : ℝ) - 1 - 2 * ((0 : ℕ) : ℝ)) / (2 * ((2 : ℕ) : ℝ)) = Real.pi / 4 := by
    norm_num
  rw [hangle, mul_comm I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hpow : (2 * Real.pi) ^ (1 + 1 / ((2 : ℕ) : ℝ)) = Real.sqrt 2 * (2 * Real.pi ^ (3 / 2 : ℝ)) := by
    rw [show (1 + 1 / ((2 : ℕ) : ℝ)) = (3 / 2 : ℝ) by norm_num,
        Real.mul_rpow (by norm_num) Real.pi_pos.le,
        show (2 : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt 2 * 2 by
          rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
              Real.rpow_add zero_lt_two, Real.rpow_one]]
    ring
  rw [hpow]; push_cast
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr zero_lt_two).ne'
  field_simp [hs2]
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  ring_nf; rw [hsq]; ring

private lemma ppRay_two_one : ppRay 2 1 = sqRay1 := by
  unfold ppRay ppAngle sqRay1
  have hangle : Real.pi * (((2 : ℕ) : ℝ) - 1 - 2 * ((1 : ℕ) : ℝ)) / (2 * ((2 : ℕ) : ℝ)) = -(Real.pi / 4) := by
    norm_num; ring
  rw [hangle, mul_comm I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hpow : (2 * Real.pi) ^ (1 + 1 / ((2 : ℕ) : ℝ)) = Real.sqrt 2 * (2 * Real.pi ^ (3 / 2 : ℝ)) := by
    rw [show (1 + 1 / ((2 : ℕ) : ℝ)) = (3 / 2 : ℝ) by norm_num,
        Real.mul_rpow (by norm_num) Real.pi_pos.le,
        show (2 : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt 2 * 2 by
          rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
              Real.rpow_add zero_lt_two, Real.rpow_one]]
    ring
  rw [hpow]; push_cast
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr zero_lt_two).ne'
  field_simp [hs2]
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  ring_nf; rw [hsq]; ring

private lemma psValue_logDeriv_two_eq {X : ℝ} (hX : 0 < X) :
    psValue (logDerivPowerPart 2) (qRayD 3 X) =
      ∑' n : ℕ+, (((n.val : ℝ) ^ 2 / (Real.exp ((n.val : ℝ) ^ 2 / X ^ 2) - 1) : ℝ) : ℂ) := by
  let t : ℝ := 1 / X ^ 2
  have ht : 0 < t := by positivity
  let term (mn : ℕ+ × ℕ+) : ℂ := ((mn.2.val : ℂ) ^ 2) * (qRayD 3 X) ^ (mn.1.val * mn.2.val ^ 2)
  have hq_norm : ‖qRayD 3 X‖ = Real.exp (-t) := by
    unfold qRayD; dsimp only [t]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hsum_prod : Summable (fun mn : ℕ+ × ℕ+ ↦ ‖term mn‖) := by
    have hsum_norm : Summable (fun mn : ℕ+ × ℕ+ ↦ (mn.2.val : ℝ) ^ 2 * Real.exp (-t * (mn.1.val * mn.2.val ^ 2))) := by
      rw [← (Equiv.sigmaEquivProd ℕ+ ℕ+).summable_iff]
      refine (summable_sigma_of_nonneg fun _ ↦ mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)).mpr ⟨fun m ↦ ?_, ?_⟩
      · have hm : 0 < t * (m.val : ℝ) := mul_pos ht (by exact_mod_cast m.pos)
        have h2 := (Real.summable_pow_mul_exp_neg_nat_mul 2 hm).comp_injective PNat.coe_injective
        refine Summable.of_nonneg_of_le (fun _ ↦ mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)) (fun n ↦ ?_) h2
        simp only [Function.comp_def, Equiv.sigmaEquivProd_apply]
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        apply Real.exp_le_exp.mpr
        have hn1 : (n.val : ℝ) ≤ (n.val : ℝ) ^ 2 := by
          have : (1 : ℝ) ≤ (n.val : ℝ) := by exact_mod_cast n.pos
          nlinarith
        have hmul_le : t * (m.val : ℝ) * (n.val : ℝ) ≤ t * (m.val : ℝ) * (n.val : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hn1 hm.le
        have hmul_eq : -t * ((m.val : ℝ) * (n.val : ℝ) ^ 2) = -(t * (m.val : ℝ) * (n.val : ℝ) ^ 2) := by ring
        linarith
      · have hbound (m : ℕ+) :
            (∑' n : ℕ+, (n.val : ℝ) ^ 2 * Real.exp (-t * (m.val * n.val ^ 2))) ≤
              (∑' n : ℕ+, (n.val : ℝ) ^ 2 * Real.exp (-(t / 2) * (n.val : ℝ))) *
                Real.exp (-(t / 2) * (m.val : ℝ)) := by
          rw [← tsum_mul_right]
          have hsn : Summable (fun n : ℕ+ ↦ (n.val : ℝ) ^ 2 * Real.exp (-(t / 2) * (n.val : ℝ))) :=
            (Real.summable_pow_mul_exp_neg_nat_mul 2 (half_pos ht)).comp_injective PNat.coe_injective
          have hsm : Summable (fun n : ℕ+ ↦ (n.val : ℝ) ^ 2 * Real.exp (-t * (m.val * n.val ^ 2))) := by
            have hm : 0 < t * (m.val : ℝ) := mul_pos ht (by exact_mod_cast m.pos)
            refine Summable.of_nonneg_of_le (fun _ ↦ mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)) (fun n ↦ ?_)
              ((Real.summable_pow_mul_exp_neg_nat_mul 2 hm).comp_injective PNat.coe_injective)
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
            apply Real.exp_le_exp.mpr
            have hn1 : (n.val : ℝ) ≤ (n.val : ℝ) ^ 2 := by
              have : (1 : ℝ) ≤ (n.val : ℝ) := by exact_mod_cast n.pos
              nlinarith
            have hmul_le : t * (m.val : ℝ) * (n.val : ℝ) ≤ t * (m.val : ℝ) * (n.val : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_left hn1 hm.le
            have hmul_eq : -t * ((m.val : ℝ) * (n.val : ℝ) ^ 2) = -(t * (m.val : ℝ) * (n.val : ℝ) ^ 2) := by ring
            linarith
          refine hsm.tsum_le_tsum (fun n ↦ ?_) (hsn.mul_right _)
          have hm1 : (1 : ℝ) ≤ (m.val : ℝ) := by exact_mod_cast m.pos
          have hn1 : (1 : ℝ) ≤ (n.val : ℝ) := by exact_mod_cast n.pos
          have hnn : (n.val : ℝ) ≤ (n.val : ℝ) ^ 2 := by nlinarith
          have hadd : (n.val : ℝ) + (m.val : ℝ) ≤ 2 * ((m.val : ℝ) * (n.val : ℝ) ^ 2) := by nlinarith
          rw [mul_assoc, ← Real.exp_add]
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          apply Real.exp_le_exp.mpr
          nlinarith
        have hdom := ((Real.summable_pow_mul_exp_neg_nat_mul 0 (half_pos ht)).comp_injective PNat.coe_injective).mul_left
          (∑' n : ℕ+, (n.val : ℝ) ^ 2 * Real.exp (-(t / 2) * (n.val : ℝ)))
        refine Summable.of_nonneg_of_le (fun _ ↦ tsum_nonneg fun _ ↦ mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))
          (fun m ↦ ?_) hdom
        simpa only [Function.comp_def, Equiv.sigmaEquivProd_apply, pow_zero, one_mul] using hbound m
    refine hsum_norm.congr fun mn ↦ ?_
    simp only [term, norm_mul, norm_pow, Complex.norm_natCast, hq_norm, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  have h_eq1 : psValue (logDerivPowerPart 2) (qRayD 3 X) = ∑' mn : ℕ+ × ℕ+, term mn := by
    let g (mn : ℕ+ × ℕ+) : ℕ := mn.1.val * mn.2.val ^ 2
    rw [(hsum_prod.of_norm.hasSum.tsum_fiberwise g).tsum_eq.symm]
    unfold psValue
    apply tsum_congr; intro N
    by_cases hN0 : N = 0
    · subst hN0
      have : IsEmpty (g ⁻¹' {0}) := ⟨fun mn ↦ mul_ne_zero mn.val.1.pos.ne'
        (pow_ne_zero 2 mn.val.2.pos.ne') mn.property⟩
      simp [psTerm, logDerivPowerPart, logDerivPowerPartDilated]
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
      let S := (Finset.Icc 1 N).filter (fun n ↦ n ^ 2 ∣ N)
      let e : g ⁻¹' {N} ≃ S :=
        { toFun := fun mn ↦ ⟨mn.val.2.val, Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨mn.val.2.pos,
              (Nat.le_self_pow (show 2 ≠ 0 by decide) mn.val.2.val).trans
                (Nat.le_of_dvd hNpos ⟨mn.val.1.val, by rw [mul_comm]; exact mn.property.symm⟩)⟩,
             ⟨mn.val.1.val, by rw [mul_comm]; exact mn.property.symm⟩⟩⟩
          invFun := fun n ↦
            have hn_pos : 0 < n.val := (Finset.mem_Icc.mp (Finset.mem_filter.mp n.property).1).1
            have hdvd : n.val ^ 2 ∣ N := (Finset.mem_filter.mp n.property).2
            have hm_pos : 0 < N / n.val ^ 2 := Nat.div_pos (Nat.le_of_dvd hNpos hdvd) (pow_pos hn_pos 2)
            ⟨(⟨N / n.val ^ 2, hm_pos⟩, ⟨n.val, hn_pos⟩), Nat.div_mul_cancel hdvd⟩
          left_inv := fun ⟨⟨m, n⟩, hmn⟩ ↦ Subtype.ext (Prod.ext (PNat.eq (by
            change N / n.val ^ 2 = m.val
            have h1 : m.val * n.val ^ 2 = N := hmn
            rw [← h1]; exact Nat.mul_div_cancel m.val (pow_pos n.pos 2))) rfl)
          right_inv := fun ⟨n, _⟩ ↦ rfl }
      let _ : Fintype (g ⁻¹' {N}) := Fintype.ofEquiv S e.symm
      rw [tsum_fintype, Fintype.sum_equiv e (fun mn ↦ term mn.val)
        (fun n ↦ ((n.val : ℂ) ^ 2) * (qRayD 3 X) ^ N)
        (fun mn ↦ by simp only [term, e, Equiv.coe_fn_mk, show mn.val.1.val * mn.val.2.val ^ 2 = N from mn.property])]
      rw [Finset.univ_eq_attach, Finset.sum_attach S (fun n ↦ ((n : ℂ) ^ 2) * (qRayD 3 X) ^ N),
          ← Finset.sum_mul]
      simp [psTerm, logDerivPowerPart, logDerivPowerPartDilated, powerDivSum, hN0, S]
  have hsum_swap : Summable (fun nm : ℕ+ × ℕ+ ↦ term (nm.2, nm.1)) :=
    hsum_prod.of_norm.comp_injective (Equiv.prodComm ℕ+ ℕ+).injective
  have h_eq2 : (∑' mn : ℕ+ × ℕ+, term mn) = ∑' n : ℕ+, ∑' m : ℕ+, term (m, n) := by
    rw [← (Equiv.prodComm ℕ+ ℕ+).tsum_eq term]
    exact hsum_swap.tsum_prod' fun n ↦ hsum_prod.of_norm.comp_injective fun m₁ m₂ h ↦ by injection h
  rw [h_eq1, h_eq2]
  apply tsum_congr; intro n
  have hq_n : ‖(qRayD 3 X) ^ (n.val ^ 2)‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) (qRayD_disk hX) (pow_ne_zero 2 n.pos.ne')
  have hgeom : (∑' m : ℕ+, ((qRayD 3 X) ^ (n.val ^ 2)) ^ m.val) =
      ((qRayD 3 X) ^ (n.val ^ 2)) * (1 - (qRayD 3 X) ^ (n.val ^ 2))⁻¹ := by
    rw [tsum_pnat_eq_tsum_succ (f := fun m : ℕ ↦ ((qRayD 3 X) ^ (n.val ^ 2)) ^ m)]
    simp_rw [pow_succ' ((qRayD 3 X) ^ (n.val ^ 2))]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hq_n]
  have hterm_n : (∑' m : ℕ+, term (m, n)) =
      ((n.val : ℂ) ^ 2) * ∑' m : ℕ+, ((qRayD 3 X) ^ (n.val ^ 2)) ^ m.val := by
    rw [← tsum_mul_left]
    apply tsum_congr; intro m; simp [term, ← pow_mul, mul_comm]
  rw [hterm_n, hgeom]
  have hexp_n : (qRayD 3 X) ^ (n.val ^ 2) = (((Real.exp ((n.val : ℝ) ^ 2 / X ^ 2))⁻¹ : ℝ) : ℂ) := by
    simp only [qRayD, ← Complex.ofReal_pow, ← Real.exp_nat_mul, ← Real.exp_neg]
    congr 2; push_cast; ring
  rw [hexp_n]
  have hepos : 0 < Real.exp ((n.val : ℝ) ^ 2 / X ^ 2) := Real.exp_pos _
  have hegt1 : 1 < Real.exp ((n.val : ℝ) ^ 2 / X ^ 2) :=
    Real.one_lt_exp_iff.mpr (div_pos (pow_pos (Nat.cast_pos.mpr n.pos) 2) (pow_pos hX 2))
  have hE0 : ((Real.exp ((n.val : ℝ) ^ 2 / X ^ 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hepos.ne'
  have hE1 : ((Real.exp ((n.val : ℝ) ^ 2 / X ^ 2) : ℝ) : ℂ) - 1 ≠ 0 := by
    intro h; have hre := congrArg Complex.re h
    rw [Complex.sub_re, Complex.ofReal_re, Complex.one_re, Complex.zero_re] at hre; linarith
  have hden : (1 : ℂ) - (((Real.exp ((n.val : ℝ) ^ 2 / X ^ 2) : ℝ) : ℂ))⁻¹ ≠ 0 := by
    intro h; have h1 : (1 - (((Real.exp ((n.val : ℝ) ^ 2 / X ^ 2) : ℝ) : ℂ))⁻¹) *
      ((Real.exp ((n.val : ℝ) ^ 2 / X ^ 2) : ℝ) : ℂ) = 0 := by rw [h, zero_mul]
    rw [sub_mul, one_mul, inv_mul_cancel₀ hE0] at h1; exact hE1 h1
  push_cast
  field_simp [hE0, hE1, hden]

/-- **100% UNCONDITIONAL Non-Vacuity Witness (`d = 2`, Partitions into Squares!)**:
Discharges `PowerPartStokesProfile 2 (by decide)` completely from Mathlib via
`squares_partition_analytic_identity` with zero unproven holes or extra assumptions. -/
def powerPartStokesProfileTwo : PowerPartStokesProfile 2 (by decide) where
  polarPoly := Polynomial.C sqPartConst - Polynomial.X
  decomp := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), (ppWaveJet 2 (by decide) 0).norm_summable] with X hX hws
    have hid := squares_partition_analytic_identity hX
    rw [rescaledLogDerivPP, psValue_logDeriv_two_eq hX,
        show ((2 : ℕ) : ℂ) = 2 by norm_num, show (2 + 1 : ℕ) = 3 by rfl,
        hid, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, sub_eq_add_neg]
    congr 1
    -- Regroup the `(k, m)` wave sum by `N = k² m` into `(ppWaveJet 2 _ 0).value X`!
    let w (ℓ : Fin 2) (km : ℕ+ × ℕ+) : ℂ :=
      -((Real.sqrt (km.2.val : ℝ) : ℝ) : ℂ) *
        (ppRay 2 ℓ.val * Complex.exp (-ppRay 2 ℓ.val * (((km.1.val : ℝ) * Real.sqrt (km.2.val : ℝ) * X : ℝ) : ℂ)))
    have hsum_w (ℓ : Fin 2) : Summable (fun km : ℕ+ × ℕ+ ↦ ‖w ℓ km‖) := by
      let c : ℝ := 2 * Real.pi ^ (3 / 2 : ℝ) * X
      have hc : 0 < c := by positivity
      have hre_ray : (ppRay 2 ℓ.val).re = 2 * Real.pi ^ (3 / 2 : ℝ) := by
        fin_cases ℓ
        · dsimp only; exact (congrArg Complex.re ppRay_two_zero).trans (by simp [sqRay0])
        · dsimp only; exact (congrArg Complex.re ppRay_two_one).trans (by simp [sqRay1])
      rw [← (Equiv.sigmaEquivProd ℕ+ ℕ+).summable_iff]
      refine (summable_sigma_of_nonneg fun _ ↦ norm_nonneg _).mpr ⟨fun k ↦ ?_, ?_⟩
      · have hdom := (summable_pow_mul_exp_neg_rpow (d := 2) (by decide)
          (mul_pos hc (Nat.cast_pos.mpr k.pos)) 1).mul_left ‖ppRay 2 ℓ.val‖
        refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun m ↦ ?_) hdom
        simp only [Equiv.sigmaEquivProd_apply]
        dsimp only [w]
        rw [norm_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp]
        have hre_e : (-ppRay 2 ℓ.val * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)).re =
            -(c * (k.val : ℝ)) * (m.val : ℝ) ^ (1 / (2 : ℝ)) := by
          rw [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
              sub_zero, hre_ray, Real.sqrt_eq_rpow]; dsimp [c]; ring
        rw [hre_e]
        have hsq_le : Real.sqrt (m.val : ℝ) ≤ (m.val : ℝ) := by
          have hm1 : (1 : ℝ) ≤ (m.val : ℝ) := by exact_mod_cast m.pos
          have h2 : Real.sqrt (m.val : ℝ) ^ 2 = (m.val : ℝ) := Real.sq_sqrt (by positivity)
          nlinarith [Real.sqrt_nonneg (m.val : ℝ)]
        calc Real.sqrt (m.val : ℝ) * (‖ppRay 2 ℓ.val‖ * Real.exp (-(c * (k.val : ℝ)) * (m.val : ℝ) ^ (1 / (2 : ℝ))))
            ≤ (m.val : ℝ) * (‖ppRay 2 ℓ.val‖ * Real.exp (-(c * (k.val : ℝ)) * (m.val : ℝ) ^ (1 / (2 : ℝ)))) :=
              mul_le_mul_of_nonneg_right hsq_le (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _))
          _ = ‖ppRay 2 ℓ.val‖ * ((m.val : ℝ) ^ 1 * Real.exp (-(c * (k.val : ℝ)) * (m.val : ℝ) ^ (1 / (2 : ℝ)))) := by ring
      · let c₀ : ℝ := c / 2
        have hc₀ : 0 < c₀ := half_pos hc
        let S₀ := ∑' m : ℕ+, (m.val : ℝ) ^ 1 * Real.exp (-c₀ * (m.val : ℝ) ^ (1 / (2 : ℝ)))
        have hS₀ : Summable (fun m : ℕ+ ↦ (m.val : ℝ) ^ 1 * Real.exp (-c₀ * (m.val : ℝ) ^ (1 / (2 : ℝ)))) :=
          summable_pow_mul_exp_neg_rpow (d := 2) (by decide) hc₀ 1
        have hdom := ((Real.summable_pow_mul_exp_neg_nat_mul 0 hc₀).comp_injective PNat.coe_injective).mul_left
          (‖ppRay 2 ℓ.val‖ * S₀)
        refine Summable.of_nonneg_of_le (fun _ ↦ tsum_nonneg fun _ ↦ norm_nonneg _) (fun k ↦ ?_) hdom
        have hk1 : (1 : ℝ) ≤ (k.val : ℝ) := by exact_mod_cast k.pos
        have hle_m (m : ℕ+) : ‖w ℓ (k, m)‖ ≤
            (‖ppRay 2 ℓ.val‖ * Real.exp (-c₀ * (k.val : ℝ))) *
              ((m.val : ℝ) ^ 1 * Real.exp (-c₀ * (m.val : ℝ) ^ (1 / (2 : ℝ)))) := by
          have hm1 : (1 : ℝ) ≤ (m.val : ℝ) := by exact_mod_cast m.pos
          have hm_r : (1 : ℝ) ≤ (m.val : ℝ) ^ (1 / (2 : ℝ)) := Real.one_le_rpow hm1 (by norm_num)
          have hsq_le : Real.sqrt (m.val : ℝ) ≤ (m.val : ℝ) := by
            have h2 : Real.sqrt (m.val : ℝ) ^ 2 = (m.val : ℝ) := Real.sq_sqrt (by positivity)
            nlinarith [Real.sqrt_nonneg (m.val : ℝ)]
          dsimp only [w]
          rw [norm_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp]
          have hre_e : (-ppRay 2 ℓ.val * (((k.val : ℝ) * Real.sqrt (m.val : ℝ) * X : ℝ) : ℂ)).re =
              -(2 * c₀ * (k.val : ℝ) * (m.val : ℝ) ^ (1 / (2 : ℝ))) := by
            rw [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
                sub_zero, hre_ray, Real.sqrt_eq_rpow]; dsimp [c₀, c]; ring
          rw [hre_e]
          have hexp_s : Real.exp (-(2 * c₀ * (k.val : ℝ) * (m.val : ℝ) ^ (1 / (2 : ℝ)))) ≤
              Real.exp (-c₀ * (k.val : ℝ)) * Real.exp (-c₀ * (m.val : ℝ) ^ (1 / (2 : ℝ))) := by
            rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
            have h1 : (k.val : ℝ) + (m.val : ℝ) ^ (1 / (2 : ℝ)) ≤
                2 * ((k.val : ℝ) * (m.val : ℝ) ^ (1 / (2 : ℝ))) := by nlinarith
            nlinarith
          calc Real.sqrt (m.val : ℝ) * (‖ppRay 2 ℓ.val‖ * Real.exp _)
              ≤ (m.val : ℝ) * (‖ppRay 2 ℓ.val‖ * (Real.exp (-c₀ * (k.val : ℝ)) *
                  Real.exp (-c₀ * (m.val : ℝ) ^ (1 / (2 : ℝ))))) :=
                mul_le_mul hsq_le (mul_le_mul_of_nonneg_left hexp_s (norm_nonneg _))
                  (mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)) (Nat.cast_nonneg _)
            _ = _ := by ring
        have hinner : Summable (fun m : ℕ+ ↦ ‖w ℓ (k, m)‖) :=
          Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle_m (hS₀.mul_left _)
        have hts := hinner.tsum_le_tsum hle_m (hS₀.mul_left _)
        rw [tsum_mul_left] at hts
        simp only [Function.comp_def, Equiv.sigmaEquivProd_apply, pow_zero, one_mul]
        exact hts.trans_eq (by dsimp only [S₀]; ring)
    have hgroup (ℓ : Fin 2) : (∑' km : ℕ+ × ℕ+, w ℓ km) =
        ∑' N : ℕ+, (ppWaveJet 2 (by decide) 0).term X (ℓ, N) := by
      let g (km : ℕ+ × ℕ+) : ℕ+ := ⟨km.1.val ^ 2 * km.2.val, mul_pos (pow_pos km.1.pos 2) km.2.pos⟩
      rw [(hsum_w ℓ).of_norm.hasSum.tsum_fiberwise g |>.tsum_eq.symm]
      apply tsum_congr; intro N
      let S := (Finset.Icc 1 N.val).filter (fun k ↦ k ^ 2 ∣ N.val)
      let e : g ⁻¹' {N} ≃ S :=
        { toFun := fun km ↦ ⟨km.val.1.val, Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨km.val.1.pos,
              (Nat.le_self_pow (show 2 ≠ 0 by decide) km.val.1.val).trans
                (Nat.le_of_dvd N.pos ⟨km.val.2.val, (congrArg Subtype.val km.property).symm⟩)⟩,
             ⟨km.val.2.val, (congrArg Subtype.val km.property).symm⟩⟩⟩
          invFun := fun k ↦
            have hk_pos : 0 < k.val := (Finset.mem_Icc.mp (Finset.mem_filter.mp k.property).1).1
            have hdvd : k.val ^ 2 ∣ N.val := (Finset.mem_filter.mp k.property).2
            have hm_pos : 0 < N.val / k.val ^ 2 := Nat.div_pos (Nat.le_of_dvd N.pos hdvd) (pow_pos hk_pos 2)
            ⟨(⟨k.val, hk_pos⟩, ⟨N.val / k.val ^ 2, hm_pos⟩), PNat.eq (Nat.mul_div_cancel' hdvd)⟩
          left_inv := fun ⟨⟨k, m⟩, hkm⟩ ↦ Subtype.ext (Prod.ext rfl (PNat.eq (by
            change N.val / k.val ^ 2 = m.val
            have h1 : k.val ^ 2 * m.val = N.val := congrArg Subtype.val hkm
            rw [← h1]; exact Nat.mul_div_cancel_left m.val (pow_pos k.pos 2))))
          right_inv := fun ⟨k, _⟩ ↦ rfl }
      let _ : Fintype (g ⁻¹' {N}) := Fintype.ofEquiv S e.symm
      rw [tsum_fintype, Fintype.sum_equiv e (fun km ↦ w ℓ km.val)
          (fun k ↦ -(((k.val : ℝ)⁻¹ : ℝ) : ℂ) * (((N.val : ℝ) ^ (1 / (2 : ℝ)) : ℝ) : ℂ) *
            (ppRay 2 ℓ.val * Complex.exp (-ppWaveRate 2 ℓ N * (X : ℂ))))
          (fun km ↦ by
            have hkm : km.val.1.val ^ 2 * km.val.2.val = N.val := congrArg Subtype.val km.property
            have hk_pos : (0 : ℝ) < (km.val.1.val : ℝ) := by exact_mod_cast km.val.1.pos
            have hN_sqrt : (N.val : ℝ) ^ (1 / (2 : ℝ)) = (km.val.1.val : ℝ) * Real.sqrt (km.val.2.val : ℝ) := by
              rw [← hkm, ← Real.sqrt_eq_rpow, Nat.cast_mul, Nat.cast_pow,
                  Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk_pos.le]
            have hkm_sqrt : Real.sqrt (km.val.2.val : ℝ) = (km.val.1.val : ℝ)⁻¹ * (N.val : ℝ) ^ (1 / (2 : ℝ)) := by
              rw [hN_sqrt]; field_simp [hk_pos.ne']
            dsimp only [w, e, Equiv.coe_fn_mk, ppWaveRate]
            rw [← hN_sqrt, hkm_sqrt, Nat.cast_ofNat]
            push_cast
            have hexp : -ppRay 2 ℓ.val * ((((N.val : ℝ) ^ (1 / (2 : ℝ)) : ℝ) : ℂ) * (X : ℂ)) =
                -((((N.val : ℝ) ^ (1 / (2 : ℝ)) : ℝ) : ℂ) * ppRay 2 ℓ.val) * (X : ℂ) := by ring
            rw [hexp]; ring)]
      rw [Finset.univ_eq_attach,
          Finset.sum_attach S (fun k : ℕ ↦ -(((k : ℝ)⁻¹ : ℝ) : ℂ) * (((N.val : ℝ) ^ (1 / (2 : ℝ)) : ℝ) : ℂ) *
            (ppRay 2 ℓ.val * Complex.exp (-ppWaveRate 2 ℓ N * (X : ℂ)))),
          ← Finset.sum_mul, ← Finset.sum_mul]
      have hsum_c : (∑ k ∈ S, -(((k : ℝ)⁻¹ : ℝ) : ℂ)) = -((powerPartMult 2 N.val : ℝ) : ℂ) := by
        rw [Finset.sum_neg_distrib, powerPartMult, Complex.ofReal_sum]
      rw [hsum_c]
      simp only [WaveExpansion.term, ppWaveJet, ppWaveRate, pow_zero, mul_one, Nat.cast_ofNat]
      ring
    have hval_split : (ppWaveJet 2 (by decide) 0).value X =
        (∑' N : ℕ+, (ppWaveJet 2 (by decide) 0).term X (0, N)) +
        (∑' N : ℕ+, (ppWaveJet 2 (by decide) 0).term X (1, N)) := by
      unfold WaveExpansion.value
      rw [hws.of_norm.tsum_prod' (fun ℓ ↦ hws.of_norm.comp_injective fun N₁ N₂ h ↦ by injection h),
          tsum_fintype, Fin.sum_univ_two]
    have hwk_sum (ℓ : Fin 2) : Summable (fun k : ℕ+ ↦ ∑' m : ℕ+, w ℓ (k, m)) := by
      have h1 := ((Equiv.sigmaEquivProd ℕ+ ℕ+).summable_iff.mpr (hsum_w ℓ))
      have h2 := (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mp h1
      refine Summable.of_norm_bounded (g := fun k : ℕ+ ↦ ∑' m : ℕ+, ‖w ℓ (k, m)‖) h2.2 fun k ↦ ?_
      exact norm_tsum_le_tsum_norm ((hsum_w ℓ).comp_injective fun m₁ m₂ h ↦ by injection h)
    rw [hval_split, ← hgroup 0, ← hgroup 1,
        (hsum_w 0).of_norm.tsum_prod' (fun k ↦ (hsum_w 0).of_norm.comp_injective fun m₁ m₂ h ↦ by injection h),
        (hsum_w 1).of_norm.tsum_prod' (fun k ↦ (hsum_w 1).of_norm.comp_injective fun m₁ m₂ h ↦ by injection h),
        ← (hwk_sum 0).tsum_add (hwk_sum 1), ← tsum_neg]
    apply tsum_congr; intro k
    have hs0 : Summable (fun m : ℕ+ ↦ w 0 (k, m)) :=
      ((hsum_w 0).of_norm.comp_injective fun m₁ m₂ h ↦ by injection h)
    have hs1 : Summable (fun m : ℕ+ ↦ w 1 (k, m)) :=
      ((hsum_w 1).of_norm.comp_injective fun m₁ m₂ h ↦ by injection h)
    rw [← hs0.tsum_add hs1, ← tsum_neg]
    apply tsum_congr; intro m
    dsimp only [w]
    rw [show (0 : Fin 2).val = 0 from rfl, show (1 : Fin 2).val = 1 from rfl,
        ppRay_two_zero, ppRay_two_one]
    ring

/-! ### 7. 100% UNCONDITIONAL Partitions-into-Squares Theorems (`d = 2`, ZERO External Hypotheses!) -/

/-- **100% UNCONDITIONAL Differential Transcendence of `F_2(q) = ∑_{n ≥ 1} n² q^{n²} / (1 - q^{n²})`**:
ZERO external hypotheses! -/
theorem logDerivPowerPart_2_non_ade :
    AlgebraicIndependent ℂ (logDerivPowerPartCoordinates 2) :=
  logDerivPowerPart_non_ade (by decide) powerPartStokesProfileTwo

/-- **100% UNCONDITIONAL Differential Transcendence of Partitions into Squares
`P_2(q) = ∏_{n ≥ 1} (1 - q^{n²})^{-1}` over `ℂ(q)`**: ZERO external hypotheses! -/
theorem powerPart_2_non_ade :
    AlgebraicIndependent ℂ (powerPartCoordinates 2) :=
  powerPart_non_ade (by decide) powerPartStokesProfileTwo

/-- **100% UNCONDITIONAL Differential Transcendence of ALL Nonzero Integer Powers
`P_2(q)^k` (`k ∈ ℤ \ {0}`) over `ℂ(q)`**: ZERO external hypotheses! -/
theorem powerPart_2_zpow_non_ade {k : ℤ} (hk : k ≠ 0) :
    AlgebraicIndependent ℂ (powerPartZPowCoordinates 2 k) :=
  powerPart_zpow_non_ade (by decide) powerPartStokesProfileTwo hk

/-- **100% UNCONDITIONAL Joint Differential Independence of Distinct Square-Partition
Log-Derivative Dilations `{F_2(q^{a_1}), …, F_2(q^{a_s})}`**: ZERO external hypotheses! -/
theorem logDerivPowerPart_2_dilations_diff_indep {s : ℕ} (a : Fin s → ℕ+)
    (ha : Function.Injective a) :
    AlgebraicIndependent ℂ (logDerivPowerPartDilationCoordinates 2 a) :=
  logDerivPowerPart_dilations_diff_indep (by decide) powerPartStokesProfileTwo a ha

/-- **100% UNCONDITIONAL Joint Differential Independence of Distinct Square-Partition
Product Dilations `{P_2(q^{a_1}), …, P_2(q^{a_s})}`**: ZERO external hypotheses! -/
theorem powerPart_2_dilations_diff_indep {s : ℕ} (a : Fin s → ℕ+)
    (ha : Function.Injective a) :
    AlgebraicIndependent ℂ (powerPartDilationCoordinates 2 a) :=
  powerPart_dilations_diff_indep (by decide) powerPartStokesProfileTwo a ha

end
end CubicTheta.AllD
