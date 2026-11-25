module

public import PakPrimes.HigherOrderStokes
public import PakPrimes.AutonomousTransfer
public import PakPrimes.DivisorAndMacMahon
public import PakPrimes.HarmonicTrapShift
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Data.Nat.Nth
public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-! # Unconditional Quasipolynomial Euler-Product Parity Theorem

This module formalizes the **Unconditional Quasipolynomial Euler-Product Parity Theorem**
in Lean 4 (zero extra hypotheses, fully proved, strictly `[propext, Classical.choice, Quot.sound]`):

For any complex quasipolynomial `P(n) = ∑_{d=0}^D c_d(n) n^d` of period `M ≥ 1` whose odd part
`P^-(n) = (P(n) - P(-n)) / 2` is not identically zero on `ℤ`, and any weight `w : ℕ → ℂ`
eventually agreeing with `P` (allowing arbitrary finite perturbations), both:
- the weighted Lambert logarithmic derivative
  `H_w(q) = ∑_{n ≥ 1} n w(n) q^n / (1 - q^n) = ∑_{n ≥ 1} (∑_{d ∣ n} d w(d)) q^n`, and
- the weighted Euler product `G_w(q) = ∏_{n ≥ 1} (1 - q^n)^{-w(n)}` (including the literal
  infinite product `PakPrimes.HarmonicTrap.bose w` when `w : ℕ → ℕ`)

are **unconditionally differentially transcendental over `ℂ(q)`** (`AlgebraicIndependent ℂ (seriesCoordinates ...)`).

## Proof Architecture
1. **Discrete Fourier & Divisor-Sum Pole Nonvanishing**:
   Using the odd-part coefficients `c_d^-(r)` and their DFT `c_dft(d, k) = (d!/M) ∑_{r=1}^M c_d^-(r) e^{-2πi r k/M}`,
   the divisor-sum amplitudes `A_d(m) = ∑_{k ∣ m} (m/k)^{d+1} c_dft(d, k)` are nonzero for infinitely
   many `m ≥ 1` (proved elementarily via `m = d₀ q` for large primes `q`).
2. **Shifted Euler–Maclaurin Asymptotics**:
   Two-piece integration by parts with `bernoulliFun` on `[0, θ]` and `[θ, 1]` yields the full
   all-orders `1/u` asymptotic expansion of `∑_{k ≥ 0} h((k + θ) / u)` and all its `u`-derivatives.
3. **Closed-Form Global Mittag-Leffler Borel Transform**:
   Combining `riemannZeta_two_mul_nat` with Mathlib's Bernoulli Fourier series
   (`hasSum_one_div_nat_pow_mul_cos`, `hasSum_one_div_nat_pow_mul_sin`) and `Polynomial.bernoulli_eval_one_sub`
   (which makes the even part `P^+` cancel identically for every `j ≥ 1`), the exact Borel transform
   `borelPhi P ξ = ∑_{m ≥ 1} ∑_{d=0}^D pref_d A_d(m) ((ξ - ω_m)^{-(d+3)} + (-1)^{d+1} (ξ + ω_m)^{-(d+3)})`
   with `ω_m = 4π² m / M` satisfies `PakPrimes.HigherOrderStokes.HigherOrderBorelData`.
4. **Autonomous Nome Transfer + Higher-Order Stokes–Vandermonde + Differential-Algebra Transfer**:
   `autonomous_transfer` (`q = e^{-e^{-y}}`) → `y = log u` → `no_nonautonomous_ade_of_higher_order_borel`
   establishes differential transcendence of `H_P(q)`, and fraction-field transcendence-degree
   arguments extend it to all finite perturbations `w =ᶠ P` and to the Euler products `G_w(q)`.
5. **Six Unconditional Zero-Hypothesis Corollaries**:
   - Parts `≡ 1 mod 5` alone (`∏_{n ≡ 1 (5)} (1 - q^n)^{-1}`), contrasted with Rogers–Ramanujan `±1 mod 5`.
   - 3D free conformal scalar on `S²` (`Z_{S²}(z) = M(z)/M(z²)²`), contrasted with `S³`.
   - 3D harmonic trap shifted by `± 1/2` quantum (`P(n) = (n² ± n)/2`), contrasted with the `3/2` trap.
   - Rational convex polytope Ehrhart products for `[0, 1]` (`L(n) = n + 1`, `I(n) = n - 1`).
   - Twisted odd Dirichlet character Lambert series (`χ_{-3}`, `χ_{-4}` with `n^{2m}`).
   - Finite perturbation invariance (`w(n) = 1_{n ≡ 1 (5)} + δ_{n,1} - 3 δ_{n,2}`).
-/

set_option maxHeartbeats 1600000

public section
namespace PakPrimes.QuasipolynomialEulerParity

open Complex Real Filter MeasureTheory Set MvPolynomial
open PakPrimes.BorelStokesVandermonde PakPrimes.GeneralTheorem2 PakPrimes.HigherOrderStokes
  PakPrimes.PrimeNome PakPrimes.DivisorAndMacMahon
open scoped Topology Interval BigOperators

noncomputable section

/-! ### 1. Quasipolynomials, Parity Decomposition, DFT, and Infinite Nonzero Poles -/

/-- A complex quasipolynomial `P(n) = ∑_{d=0}^D c_d(n) n^d` of period `M ≥ 1`. -/
structure Quasipoly where
  M : ℕ
  hM : 0 < M
  D : ℕ
  c : Fin (D + 1) → ℕ → ℂ
  periodic : ∀ (d : Fin (D + 1)) (n : ℕ), c d (n + M) = c d n

namespace Quasipoly

lemma periodic_add_mul (P : Quasipoly) (d : Fin (P.D + 1)) (r k : ℕ) :
    P.c d (r + k * P.M) = P.c d r := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show r + (k + 1) * P.M = (r + k * P.M) + P.M by ring, P.periodic, ih]

lemma periodic_mod (P : Quasipoly) (d : Fin (P.D + 1)) (n : ℕ) :
    P.c d (n % P.M) = P.c d n := by
  have h := P.periodic_add_mul d (n % P.M) (n / P.M)
  rw [show n % P.M + n / P.M * P.M = P.M * (n / P.M) + n % P.M by ring, Nat.div_add_mod] at h
  exact h.symm

lemma periodic_M (P : Quasipoly) (d : Fin (P.D + 1)) : P.c d P.M = P.c d 0 := by
  simpa using P.periodic d 0

/-- Evaluation of a quasipolynomial at any integer `n : ℤ`. -/
@[expose] def eval (P : Quasipoly) (n : ℤ) : ℂ :=
  ∑ d : Fin (P.D + 1), P.c d ((n % (P.M : ℤ)).toNat) * (n : ℂ) ^ d.1

lemma eval_nat (P : Quasipoly) (n : ℕ) :
    P.eval (n : ℤ) = ∑ d : Fin (P.D + 1), P.c d n * (n : ℂ) ^ d.1 := by
  unfold eval
  refine Finset.sum_congr rfl fun d _ => ?_
  have hmod : (((n : ℤ) % (P.M : ℤ)).toNat) = n % P.M := by
    rw [← Int.natCast_emod, Int.toNat_natCast]
  rw [hmod, P.periodic_mod]
  push_cast
  rfl

/-- Odd part `P^-(n) = (P(n) - P(-n)) / 2` on `ℤ`. -/
@[expose] def oddPart (P : Quasipoly) (n : ℤ) : ℂ :=
  (P.eval n - P.eval (-n)) / 2

/-- Even part `P^+(n) = (P(n) + P(-n)) / 2` on `ℤ`. -/
@[expose] def evenPart (P : Quasipoly) (n : ℤ) : ℂ :=
  (P.eval n + P.eval (-n)) / 2

/-- Odd-part coefficient sequence `c_d^-(n) = (c_d(n) - (-1)^d c_d(M - n % M)) / 2`. -/
@[expose] def cOdd (P : Quasipoly) (d : Fin (P.D + 1)) (n : ℕ) : ℂ :=
  (P.c d n - (-1 : ℂ) ^ d.1 * P.c d (P.M - n % P.M)) / 2

/-- Even-part coefficient sequence `c_d^+(n) = (c_d(n) + (-1)^d c_d(M - n % M)) / 2`. -/
@[expose] def cEven (P : Quasipoly) (d : Fin (P.D + 1)) (n : ℕ) : ℂ :=
  (P.c d n + (-1 : ℂ) ^ d.1 * P.c d (P.M - n % P.M)) / 2

lemma c_eq_cOdd_add_cEven (P : Quasipoly) (d : Fin (P.D + 1)) (n : ℕ) :
    P.c d n = P.cOdd d n + P.cEven d n := by
  dsimp only [cOdd, cEven]; ring

lemma cOdd_periodic (P : Quasipoly) (d : Fin (P.D + 1)) (n : ℕ) :
    P.cOdd d (n + P.M) = P.cOdd d n := by
  simp only [cOdd, P.periodic, Nat.add_mod_right]

lemma cOdd_mod (P : Quasipoly) (d : Fin (P.D + 1)) (n : ℕ) :
    P.cOdd d (n % P.M) = P.cOdd d n := by
  simp only [cOdd, P.periodic_mod, Nat.mod_mod]

lemma cOdd_reflect (P : Quasipoly) (d : Fin (P.D + 1)) {r : ℕ} (hr1 : 1 ≤ r) (hrM : r ≤ P.M) :
    P.cOdd d (P.M - r) = -((-1 : ℂ) ^ d.1 * P.cOdd d r) := by
  by_cases hEq : r = P.M
  · subst hEq
    simp only [Nat.sub_self, cOdd, Nat.zero_mod, Nat.mod_self, Nat.sub_zero, P.periodic_M]
    rcases Nat.even_or_odd d.1 with he | ho
    · rw [he.neg_one_pow]; ring
    · rw [ho.neg_one_pow]; ring
  · have hr_lt : r < P.M := lt_of_le_of_ne hrM hEq
    have hMr_lt : P.M - r < P.M := by omega
    have hsub : P.M - (P.M - r) = r := by omega
    simp only [cOdd, Nat.mod_eq_of_lt hr_lt, Nat.mod_eq_of_lt hMr_lt, hsub]
    rcases Nat.even_or_odd d.1 with he | ho
    · rw [he.neg_one_pow]; ring
    · rw [ho.neg_one_pow]; ring

lemma cEven_reflect (P : Quasipoly) (d : Fin (P.D + 1)) {r : ℕ} (hr1 : 1 ≤ r) (hrM : r ≤ P.M) :
    P.cEven d (P.M - r) = (-1 : ℂ) ^ d.1 * P.cEven d r := by
  by_cases hEq : r = P.M
  · subst hEq
    simp only [Nat.sub_self, cEven, Nat.zero_mod, Nat.mod_self, Nat.sub_zero, P.periodic_M]
    rcases Nat.even_or_odd d.1 with he | ho
    · rw [he.neg_one_pow]; ring
    · rw [ho.neg_one_pow]; ring
  · have hr_lt : r < P.M := lt_of_le_of_ne hrM hEq
    have hMr_lt : P.M - r < P.M := by omega
    have hsub : P.M - (P.M - r) = r := by omega
    simp only [cEven, Nat.mod_eq_of_lt hr_lt, Nat.mod_eq_of_lt hMr_lt, hsub]
    rcases Nat.even_or_odd d.1 with he | ho
    · rw [he.neg_one_pow]; ring
    · rw [ho.neg_one_pow]; ring

lemma cEven_M_of_odd (P : Quasipoly) (d : Fin (P.D + 1)) (hodd : Odd d.1) :
    P.cEven d P.M = 0 := by
  simp only [cEven, Nat.mod_self, Nat.sub_zero, P.periodic_M, hodd.neg_one_pow]
  ring

lemma cOdd_M_of_even (P : Quasipoly) (d : Fin (P.D + 1)) (heven : Even d.1) :
    P.cOdd d P.M = 0 := by
  simp only [cOdd, Nat.mod_self, Nat.sub_zero, P.periodic_M, heven.neg_one_pow]
  ring

private lemma neg_emod_toNat (n : ℤ) {M : ℕ} (hM : 0 < M) :
    ((-n) % (M : ℤ)).toNat = if (n % (M : ℤ)).toNat = 0 then 0 else M - (n % (M : ℤ)).toNat := by
  have hM0 : (M : ℤ) ≠ 0 := by omega
  have hMpos : (0 : ℤ) < (M : ℤ) := by omega
  have hnonneg : 0 ≤ n % (M : ℤ) := Int.emod_nonneg n hM0
  have hlt : n % (M : ℤ) < (M : ℤ) := Int.emod_lt_of_pos n hMpos
  have hneg_nonneg : 0 ≤ (-n) % (M : ℤ) := Int.emod_nonneg (-n) hM0
  have hneg_lt : (-n) % (M : ℤ) < (M : ℤ) := Int.emod_lt_of_pos (-n) hMpos
  have hsum_dvd : (M : ℤ) ∣ (n % (M : ℤ)) + ((-n) % (M : ℤ)) := by
    have h1 : n % (M : ℤ) ≡ n [ZMOD (M : ℤ)] := Int.mod_modEq n (M : ℤ)
    have h2 : (-n) % (M : ℤ) ≡ -n [ZMOD (M : ℤ)] := Int.mod_modEq (-n) (M : ℤ)
    have h3 : (n % (M : ℤ)) + ((-n) % (M : ℤ)) ≡ n + (-n) [ZMOD (M : ℤ)] := h1.add h2
    rw [add_neg_cancel] at h3
    exact Int.dvd_of_emod_eq_zero h3
  split_ifs with hz
  · have hmod0 : n % (M : ℤ) = 0 := by omega
    rw [hmod0, zero_add] at hsum_dvd
    have hneg0 : (-n) % (M : ℤ) = 0 := by
      rcases hsum_dvd with ⟨k, hk⟩
      have hk0 : k = 0 := by nlinarith
      subst hk0; omega
    omega
  · have hpos : 0 < n % (M : ℤ) := by omega
    rcases hsum_dvd with ⟨k, hk⟩
    have hk1 : k = 1 := by nlinarith
    subst hk1
    omega

lemma oddPart_eq_sum_cOdd (P : Quasipoly) (n : ℤ) :
    P.oddPart n = ∑ d : Fin (P.D + 1), P.cOdd d ((n % (P.M : ℤ)).toNat) * (n : ℂ) ^ d.1 := by
  unfold oddPart eval
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hMpos : (0 : ℤ) < (P.M : ℤ) := by exact_mod_cast P.hM
  have hlt : (n % (P.M : ℤ)).toNat < P.M := by
    have h1 := Int.emod_lt_of_pos n hMpos
    have h2 := Int.emod_nonneg n (ne_of_gt hMpos)
    omega
  have hneg_pow : ((-n : ℤ) : ℂ) ^ d.1 = (-1 : ℂ) ^ d.1 * (n : ℂ) ^ d.1 := by
    push_cast
    rw [show -(n : ℂ) = (-1 : ℂ) * (n : ℂ) by ring, mul_pow]
  rw [hneg_pow, neg_emod_toNat n P.hM]
  unfold cOdd
  rw [Nat.mod_eq_of_lt hlt]
  split_ifs with hz
  · rw [hz, Nat.sub_zero, P.periodic_M]
    ring
  · ring

/-- If `P^-` is not identically zero on `ℤ`, then some `cOdd d r` (`1 ≤ r ≤ M`) is nonzero. -/
lemma exists_cOdd_ne_zero (P : Quasipoly) (hodd : ∃ n : ℤ, P.oddPart n ≠ 0) :
    ∃ (d : Fin (P.D + 1)) (r : ℕ), r ∈ Finset.Icc 1 P.M ∧ P.cOdd d r ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨n, hn⟩ := hodd
  apply hn
  rw [P.oddPart_eq_sum_cOdd]
  refine Finset.sum_eq_zero fun d _ => ?_
  have hzero : P.cOdd d ((n % (P.M : ℤ)).toNat) = 0 := by
    by_cases h0 : (n % (P.M : ℤ)).toNat = 0
    · rw [h0]
      have hM_mem : P.M ∈ Finset.Icc 1 P.M := Finset.mem_Icc.mpr ⟨P.hM, le_rfl⟩
      have hper : P.cOdd d P.M = P.cOdd d 0 := by simpa using P.cOdd_periodic d 0
      rw [← hper]
      exact hall d P.M hM_mem
    · have hMpos : (0 : ℤ) < (P.M : ℤ) := by exact_mod_cast P.hM
      have hlt : (n % (P.M : ℤ)).toNat < P.M := by
        have h1 := Int.emod_lt_of_pos n hMpos
        have h2 := Int.emod_nonneg n (ne_of_gt hMpos)
        omega
      exact hall d _ (Finset.mem_Icc.mpr ⟨by omega, le_of_lt hlt⟩)
  rw [hzero, zero_mul]

/-- Discrete Fourier transform of the odd-part coefficient sequence `c_d^-`:
`c_dft(P, d, k) = (d! / M) * ∑_{r=1}^M c_d^-(r) * exp(-2π i r k / M)`. -/
@[expose] def cDft (P : Quasipoly) (d : Fin (P.D + 1)) (k : ℕ) : ℂ :=
  ((d.1.factorial : ℂ) / (P.M : ℂ)) *
    ∑ r ∈ Finset.Icc 1 P.M,
      P.cOdd d r * Complex.exp (-((2 * Real.pi * (r : ℝ) * (k : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I)

lemma cDft_periodic (P : Quasipoly) (d : Fin (P.D + 1)) (k : ℕ) :
    P.cDft d (k + P.M) = P.cDft d k := by
  unfold cDft
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  have hMne : (P.M : ℝ) ≠ 0 := by exact_mod_cast P.hM.ne'
  have harg :
      -((2 * Real.pi * (r : ℝ) * ((k + P.M : ℕ) : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I =
      -((2 * Real.pi * (r : ℝ) * (k : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I +
        (-(r : ℤ) : ℤ) * (2 * Real.pi * I) := by
    have hR : 2 * Real.pi * (r : ℝ) * ((k + P.M : ℕ) : ℝ) / (P.M : ℝ) =
        2 * Real.pi * (r : ℝ) * (k : ℝ) / (P.M : ℝ) + (r : ℝ) * (2 * Real.pi) := by
      push_cast; field_simp [hMne]
    rw [hR]
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma cDft_mod (P : Quasipoly) (d : Fin (P.D + 1)) (k : ℕ) :
    P.cDft d (k % P.M) = P.cDft d k := by
  have h : ∀ q : ℕ, P.cDft d (k % P.M + q * P.M) = P.cDft d (k % P.M) := fun q => by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show k % P.M + (q + 1) * P.M = (k % P.M + q * P.M) + P.M by ring, P.cDft_periodic, ih]
  have h1 := h (k / P.M)
  rw [show k % P.M + k / P.M * P.M = P.M * (k / P.M) + k % P.M by ring, Nat.div_add_mod] at h1
  exact h1.symm

lemma cDft_bounded (P : Quasipoly) (d : Fin (P.D + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, ‖P.cDft d k‖ ≤ C := by
  let C : ℝ := ((d.1.factorial : ℝ) / (P.M : ℝ)) *
    ∑ r ∈ Finset.Icc 1 P.M, ‖P.cOdd d r‖
  refine ⟨C, by positivity, fun k => ?_⟩
  unfold cDft
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖∑ r ∈ Finset.Icc 1 P.M,
          P.cOdd d r * Complex.exp (-((2 * Real.pi * (r : ℝ) * (k : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I)‖
      ≤ ∑ r ∈ Finset.Icc 1 P.M,
          ‖P.cOdd d r * Complex.exp (-((2 * Real.pi * (r : ℝ) * (k : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I)‖ :=
        norm_sum_le _ _
    _ = ∑ r ∈ Finset.Icc 1 P.M, ‖P.cOdd d r‖ := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [norm_mul]
        have hnorm1 : ‖Complex.exp (-((2 * Real.pi * (r : ℝ) * (k : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I)‖ = 1 := by
          rw [show -((2 * Real.pi * (r : ℝ) * (k : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I =
            ((-(2 * Real.pi * (r : ℝ) * (k : ℝ) / (P.M : ℝ)) : ℝ) : ℂ) * I by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _
        rw [hnorm1, mul_one]

/-- Finite Fourier orthogonality on `{0, ..., M - 1}`. -/
private lemma sum_root_of_unity_eq {M : ℕ} (hM : 0 < M) {a : ℤ} (ha : ¬ (M : ℤ) ∣ a) :
    ∑ k ∈ Finset.range M,
      Complex.exp (((2 * Real.pi * (a : ℝ) * (k : ℝ) / (M : ℝ) : ℝ) : ℂ) * I) = 0 := by
  let ζ : ℂ := Complex.exp (((2 * Real.pi * (a : ℝ) / (M : ℝ) : ℝ) : ℂ) * I)
  have hpow : ∀ k : ℕ,
      Complex.exp (((2 * Real.pi * (a : ℝ) * (k : ℝ) / (M : ℝ) : ℝ) : ℂ) * I) = ζ ^ k := fun k => by
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  simp_rw [hpow]
  have hζM : ζ ^ M = 1 := by
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul]
    have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    have harg : (M : ℂ) * ((((2 * Real.pi * (a : ℝ) / (M : ℝ) : ℝ) : ℂ)) * I) =
        (a : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      have hMneC : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
      push_cast; field_simp [hMneC]
    rw [harg]
    exact Complex.exp_int_mul_two_pi_mul_I a
  have hζne : ζ ≠ 1 := by
    intro h1
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨m, hm⟩ := h1
    have hIm := congrArg Complex.im hm
    have h2pi_re : (2 * (Real.pi : ℂ)).re = 2 * Real.pi := by norm_cast
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, add_zero, zero_mul, Complex.intCast_re, Complex.intCast_im, h2pi_re] at hIm
    have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have hEqR : (a : ℝ) = (m : ℝ) * (M : ℝ) := by
      have h1' : (2 * Real.pi) * ((a : ℝ) / (M : ℝ)) = (2 * Real.pi) * (m : ℝ) := by
        rw [← mul_div_assoc, hIm, mul_comm]
      have h2' : (a : ℝ) / (M : ℝ) = (m : ℝ) := mul_left_cancel₀ hpi h1'
      exact (div_eq_iff hMne).mp h2'
    have hEqZ : a = m * (M : ℤ) := by exact_mod_cast hEqR
    exact ha ⟨m, by linarith⟩
  have hgeom := geom_sum_mul ζ M
  rw [hζM, sub_self] at hgeom
  exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hζne)

/-- DFT inversion: if `c_d^-` does not vanish identically, then its DFT `cDft P d` is nonzero at
some `k ∈ {1, ..., M}`. -/
lemma exists_cDft_ne_zero (P : Quasipoly) (d : Fin (P.D + 1))
    (hr : ∃ r ∈ Finset.Icc 1 P.M, P.cOdd d r ≠ 0) :
    ∃ k ∈ Finset.Icc 1 P.M, P.cDft d k ≠ 0 := by
  obtain ⟨r₀, hr₀_mem, hr₀_ne⟩ := hr
  have hr₀_bounds := Finset.mem_Icc.mp hr₀_mem
  have hinv : ∑ k ∈ Finset.range P.M,
      P.cDft d k * Complex.exp (((2 * Real.pi * (r₀ : ℝ) * (k : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I) =
      (d.1.factorial : ℂ) * P.cOdd d r₀ := by
    have hpull : ∑ k ∈ Finset.range P.M,
        P.cDft d k * Complex.exp (((2 * Real.pi * (r₀ : ℝ) * (k : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I) =
        ((d.1.factorial : ℂ) / (P.M : ℂ)) *
          ∑ r ∈ Finset.Icc 1 P.M, ∑ k ∈ Finset.range P.M,
            P.cOdd d r * Complex.exp (-((2 * Real.pi * (r : ℝ) * (k : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I) *
              Complex.exp (((2 * Real.pi * (r₀ : ℝ) * (k : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      unfold cDft
      rw [mul_assoc, Finset.sum_mul]
    rw [hpull]
    have hinner : ∀ r ∈ Finset.Icc 1 P.M,
        ∑ k ∈ Finset.range P.M,
          P.cOdd d r * Complex.exp (-((2 * Real.pi * (r : ℝ) * (k : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I) *
            Complex.exp (((2 * Real.pi * (r₀ : ℝ) * (k : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I) =
        if r = r₀ then (P.M : ℂ) * P.cOdd d r₀ else 0 := fun r hr_mem => by
      have hr_bounds := Finset.mem_Icc.mp hr_mem
      have hterm : ∀ k : ℕ,
          P.cOdd d r * Complex.exp (-((2 * Real.pi * (r : ℝ) * (k : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I) *
            Complex.exp (((2 * Real.pi * (r₀ : ℝ) * (k : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I) =
          P.cOdd d r * Complex.exp (((2 * Real.pi * (((r₀ : ℤ) - (r : ℤ) : ℤ) : ℝ) * (k : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I) := fun k => by
        rw [mul_assoc, ← Complex.exp_add]
        congr 2
        push_cast; ring
      simp_rw [hterm, ← Finset.mul_sum]
      split_ifs with hEq
      · subst hEq
        simp [mul_comm]
      · have hndvd : ¬ (P.M : ℤ) ∣ ((r₀ : ℤ) - (r : ℤ)) := by
          intro ⟨q, hq⟩
          have hne0 : q ≠ 0 := by intro hq0; subst hq0; omega
          have h1 : (P.M : ℤ) * 1 ≤ |(P.M : ℤ) * q| := by
            rw [abs_mul, abs_of_pos (by exact_mod_cast P.hM : (0 : ℤ) < P.M)]
            have : (1 : ℤ) ≤ |q| := Int.one_le_abs hne0
            nlinarith
          have h2 : |(r₀ : ℤ) - (r : ℤ)| < (P.M : ℤ) := by
            rw [abs_lt]; omega
          rw [hq] at h2
          linarith
        rw [sum_root_of_unity_eq P.hM hndvd, mul_zero]
    rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq' (Finset.Icc 1 P.M) r₀]
    simp only [hr₀_mem, ↓reduceIte]
    have hMne : (P.M : ℂ) ≠ 0 := by exact_mod_cast P.hM.ne'
    field_simp [hMne]
  have hsum_ne : ∑ k ∈ Finset.range P.M,
      P.cDft d k * Complex.exp (((2 * Real.pi * (r₀ : ℝ) * (k : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I) ≠ 0 := by
    rw [hinv]
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero d.1) hr₀_ne
  obtain ⟨k, hk_mem, hk_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  have hk_lt : k < P.M := Finset.mem_range.mp hk_mem
  have hdft_ne : P.cDft d k ≠ 0 := left_ne_zero_of_mul hk_ne
  by_cases hk0 : k = 0
  · subst hk0
    refine ⟨P.M, Finset.mem_Icc.mpr ⟨P.hM, le_rfl⟩, ?_⟩
    have hper : P.cDft d P.M = P.cDft d 0 := by simpa using P.cDft_periodic d 0
    rw [hper]
    exact hdft_ne
  · exact ⟨k, Finset.mem_Icc.mpr ⟨by omega, le_of_lt hk_lt⟩, hdft_ne⟩

/-- Divisor-sum Borel amplitude `A_d(m) = ∑_{k ∣ m} (m / k)^{d+1} cDft(P, d, k)` for `m ≥ 1`. -/
@[expose] def borelAmp (P : Quasipoly) (d : Fin (P.D + 1)) (m : ℕ) : ℂ :=
  ∑ k ∈ Nat.divisors m, ((m / k : ℕ) : ℂ) ^ (d.1 + 1) * P.cDft d k

lemma borelAmp_norm_le (P : Quasipoly) (d : Fin (P.D + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m →
      ‖P.borelAmp d m‖ ≤ C * (sigmaNat (d.1 + 1) m : ℝ) := by
  obtain ⟨C, hC, hbd⟩ := P.cDft_bounded d
  refine ⟨C, hC, fun m hm => ?_⟩
  unfold borelAmp
  have hsum_sig : (sigmaNat (d.1 + 1) m : ℝ) = ∑ k ∈ Nat.divisors m, ((m / k : ℕ) : ℝ) ^ (d.1 + 1) := by
    have hm0 : m ≠ 0 := by omega
    simp only [sigmaNat, hm0, ↓reduceIte, Nat.cast_sum, Nat.cast_pow]
    exact (Nat.sum_div_divisors m (fun x : ℕ => (x : ℝ) ^ (d.1 + 1))).symm
  rw [hsum_sig, Finset.mul_sum]
  calc ‖∑ k ∈ Nat.divisors m, ((m / k : ℕ) : ℂ) ^ (d.1 + 1) * P.cDft d k‖
      ≤ ∑ k ∈ Nat.divisors m, ‖((m / k : ℕ) : ℂ) ^ (d.1 + 1) * P.cDft d k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Nat.divisors m, C * ((m / k : ℕ) : ℝ) ^ (d.1 + 1) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_pow, Complex.norm_natCast, mul_comm C]
        exact mul_le_mul_of_nonneg_left (hbd k) (by positivity)

/-- Divisors of `d₀ * q` when `q` is prime and `d₀ < q` (with `1 ≤ d₀`). -/
private lemma divisors_mul_prime_of_lt {d₀ q : ℕ} (hd₀ : 1 ≤ d₀) (hq : Nat.Prime q) (_hlt : d₀ < q) :
    Nat.divisors (d₀ * q) = d₀.divisors ∪ d₀.divisors.image (· * q) := by
  have hd₀0 : d₀ ≠ 0 := by omega
  have hq0 : q ≠ 0 := hq.ne_zero
  have hprod0 : d₀ * q ≠ 0 := mul_ne_zero hd₀0 hq0
  ext e
  simp only [Nat.mem_divisors, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨he, _⟩
    by_cases hqe : q ∣ e
    · right
      obtain ⟨a, rfl⟩ := hqe
      refine ⟨a, ⟨?_, hd₀0⟩, mul_comm a q⟩
      exact (Nat.mul_dvd_mul_iff_right (Nat.pos_of_ne_zero hq0)).mp (by simpa [mul_comm] using he)
    · left
      have hcop : Nat.Coprime e q := (hq.coprime_iff_not_dvd.mpr hqe).symm
      exact ⟨hcop.dvd_of_dvd_mul_right he, hd₀0⟩
  · rintro (⟨he, _⟩ | ⟨a, ⟨ha, _⟩, rfl⟩)
    · exact ⟨dvd_mul_of_dvd_left he q, hprod0⟩
    · exact ⟨Nat.mul_dvd_mul_right ha q, hprod0⟩

private lemma disjoint_divisors_mul_prime_of_lt {d₀ q : ℕ} (hd₀ : 1 ≤ d₀) (_hq : Nat.Prime q)
    (hlt : d₀ < q) :
    Disjoint d₀.divisors (d₀.divisors.image (· * q)) := by
  rw [Finset.disjoint_left]
  intro e he1 he2
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he2
  have ha_pos : 1 ≤ a := Nat.pos_of_mem_divisors ha
  have hle : a * q ≤ d₀ := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors he1)
  have hge : q ≤ a * q := Nat.le_mul_of_pos_left q ha_pos
  omega

/-- Set of pole indices `m : ℕ` (corresponding to `m + 1 ≥ 1`) where at least one Borel amplitude
`A_d(m + 1)` is nonzero. -/
@[expose] def poleSet (P : Quasipoly) : Set ℕ :=
  {m : ℕ | ∃ d : Fin (P.D + 1), P.borelAmp d (m + 1) ≠ 0}

/-- **Key Non-Cancellation Theorem**: Whenever `P^-` is not identically zero on `ℤ`,
`poleSet P` is infinite (proved elementarily via `m + 1 = d₀ * q` for arbitrarily large primes `q`). -/
theorem infinite_poleSet (P : Quasipoly) (hodd : ∃ n : ℤ, P.oddPart n ≠ 0) :
    (P.poleSet).Infinite := by
  obtain ⟨d, r, hr_mem, hr_ne⟩ := P.exists_cOdd_ne_zero hodd
  obtain ⟨k₀, hk₀_mem, hk₀_ne⟩ := P.exists_cDft_ne_zero d ⟨r, hr_mem, hr_ne⟩
  have hex : ∃ n : ℕ, 1 ≤ n ∧ P.cDft d n ≠ 0 := ⟨k₀, (Finset.mem_Icc.mp hk₀_mem).1, hk₀_ne⟩
  classical
  let d₀ : ℕ := Nat.find hex
  have hd₀_spec : 1 ≤ d₀ ∧ P.cDft d d₀ ≠ 0 := Nat.find_spec hex
  have hd₀_min : ∀ e : ℕ, 1 ≤ e → e < d₀ → P.cDft d e = 0 := fun e he1 helt => by
    by_contra hne
    exact Nat.find_min hex helt ⟨he1, hne⟩
  obtain ⟨C, hC, hCbd⟩ := P.cDft_bounded d
  have hc_pos : 0 < ‖P.cDft d d₀‖ := norm_pos_iff.mpr hd₀_spec.2
  let B : ℝ := (d₀ : ℝ) * (d₀ : ℝ) ^ (d.1 + 1) * C
  rw [Set.infinite_iff_exists_gt]
  intro N
  obtain ⟨Q_nat, hQ_nat⟩ := exists_nat_gt (B / ‖P.cDft d d₀‖)
  obtain ⟨q, hq_ge, hq_prime⟩ := Nat.exists_infinite_primes (max (max (N + 2) (d₀ + 1)) (Q_nat + 1))
  have hq_gt_N : N + 1 < q := by omega
  have hq_gt_d₀ : d₀ < q := by omega
  have hq_gt_Q : Q_nat < q := by omega
  have hprod_pos : 1 ≤ d₀ * q := Nat.mul_pos hd₀_spec.1 hq_prime.pos
  refine ⟨d₀ * q - 1, ?_, ?_⟩
  · refine ⟨d, ?_⟩
    rw [Nat.sub_add_cancel hprod_pos]
    unfold borelAmp
    rw [divisors_mul_prime_of_lt hd₀_spec.1 hq_prime hq_gt_d₀,
      Finset.sum_union (disjoint_divisors_mul_prime_of_lt hd₀_spec.1 hq_prime hq_gt_d₀)]
    -- First sum: only `e = d₀` survives by minimality of `d₀`!
    have hsum1 : ∑ e ∈ d₀.divisors, ((d₀ * q / e : ℕ) : ℂ) ^ (d.1 + 1) * P.cDft d e =
        (q : ℂ) ^ (d.1 + 1) * P.cDft d d₀ := by
      rw [Finset.sum_eq_single d₀]
      · rw [Nat.mul_div_cancel_left q hd₀_spec.1]
      · intro e he hne
        have he1 : 1 ≤ e := Nat.pos_of_mem_divisors he
        have hele : e ≤ d₀ := Nat.le_of_dvd hd₀_spec.1 (Nat.dvd_of_mem_divisors he)
        rw [hd₀_min e he1 (lt_of_le_of_ne hele hne), mul_zero]
      · intro hnot
        exact absurd (Nat.mem_divisors_self d₀ (by omega)) hnot
    -- Second sum: norm is bounded by `B`!
    have hsum2_bd : ‖∑ e ∈ d₀.divisors.image (· * q),
        ((d₀ * q / e : ℕ) : ℂ) ^ (d.1 + 1) * P.cDft d e‖ ≤ B := by
      rw [Finset.sum_image (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_right hq_prime.pos hab)]
      have hcard_le : (d₀.divisors.card : ℝ) ≤ (d₀ : ℝ) := by
        have hsub : d₀.divisors ⊆ Finset.Icc 1 d₀ := fun a ha =>
          Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,
            Nat.le_of_dvd hd₀_spec.1 (Nat.dvd_of_mem_divisors ha)⟩
        have hc : d₀.divisors.card ≤ d₀ := by
          calc d₀.divisors.card ≤ (Finset.Icc 1 d₀).card := Finset.card_le_card hsub
            _ = d₀ := by rw [Nat.card_Icc]; omega
        exact_mod_cast hc
      calc ‖∑ a ∈ d₀.divisors, ((d₀ * q / (a * q) : ℕ) : ℂ) ^ (d.1 + 1) * P.cDft d (a * q)‖
          ≤ ∑ a ∈ d₀.divisors, ‖((d₀ * q / (a * q) : ℕ) : ℂ) ^ (d.1 + 1) * P.cDft d (a * q)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _a ∈ d₀.divisors, ((d₀ : ℝ) ^ (d.1 + 1) * C) := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [Nat.mul_div_mul_right d₀ a hq_prime.pos, norm_mul, norm_pow, Complex.norm_natCast]
            have hdiv_le : ((d₀ / a : ℕ) : ℝ) ≤ (d₀ : ℝ) := by exact_mod_cast Nat.div_le_self d₀ a
            exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hdiv_le _) (hCbd _)
              (norm_nonneg _) (by positivity)
        _ = (d₀.divisors.card : ℝ) * ((d₀ : ℝ) ^ (d.1 + 1) * C) := by simp
        _ ≤ (d₀ : ℝ) * ((d₀ : ℝ) ^ (d.1 + 1) * C) :=
            mul_le_mul_of_nonneg_right hcard_le (by positivity)
        _ = B := by dsimp only [B]; ring
    rw [hsum1]
    intro h0
    have heq_neg : (q : ℂ) ^ (d.1 + 1) * P.cDft d d₀ =
        -(∑ e ∈ d₀.divisors.image (· * q), ((d₀ * q / e : ℕ) : ℂ) ^ (d.1 + 1) * P.cDft d e) :=
      eq_neg_of_add_eq_zero_left h0
    have hnorm_le : (q : ℝ) ^ (d.1 + 1) * ‖P.cDft d d₀‖ ≤ B := by
      have h1 := congrArg norm heq_neg
      rw [norm_mul, norm_pow, Complex.norm_natCast, norm_neg] at h1
      exact h1.le.trans hsum2_bd
    have hq_le_pow : (q : ℝ) ≤ (q : ℝ) ^ (d.1 + 1) := by
      have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_prime.one_le
      simpa using pow_le_pow_right₀ hq1 (Nat.succ_pos d.1)
    have hB_lt : B < (q : ℝ) * ‖P.cDft d d₀‖ := by
      have hqR : B / ‖P.cDft d d₀‖ < (q : ℝ) :=
        hQ_nat.trans (by exact_mod_cast hq_gt_Q)
      exact (div_lt_iff₀ hc_pos).mp hqR
    nlinarith [mul_le_mul_of_nonneg_right hq_le_pow hc_pos.le]
  · have hge : q ≤ d₀ * q := Nat.le_mul_of_pos_left q hd₀_spec.1
    omega

end Quasipoly

/-! ### 2. Weighted Lambert Series, Complex Euler Products, and Differential-Algebra Transfer -/

/-- Weighted Lambert logarithmic derivative series
`H_w(q) = ∑_{n ≥ 1} n w(n) q^n / (1 - q^n) = ∑_{n ≥ 1} (∑_{d ∣ n} d w(d)) q^n`. -/
@[expose] def lambertSeries (w : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => if n = 0 then 0 else ∑ d ∈ Nat.divisors n, (d : ℂ) * w d

lemma coeff_lambertSeries (w : ℕ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (lambertSeries w) =
      if n = 0 then 0 else ∑ d ∈ Nat.divisors n, (d : ℂ) * w d := by
  simp [lambertSeries]

lemma lambertSeries_eq_modeSum (w : ℕ → ℕ) :
    lambertSeries (fun n => (w n : ℂ)) = PakPrimes.HarmonicTrap.modeSum w := by
  ext n
  by_cases hn : n = 0
  · subst hn; simp [lambertSeries, PakPrimes.HarmonicTrap.modeSum]
  · simp [lambertSeries, PakPrimes.HarmonicTrap.modeSum, hn]

/-- Recursive coefficients of the general complex-exponent Euler product
`G_w(q) = ∏_{n ≥ 1} (1 - q^n)^{-w(n)}`, uniquely determined by `G_w(0) = 1` and
`q G_w'(q) = H_w(q) G_w(q)`. -/
@[expose] def eulerCoeff (w : ℕ → ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 =>
    (∑ k ∈ (Finset.range (n + 1)).attach,
      PowerSeries.coeff (k.1 + 1) (lambertSeries w) * eulerCoeff w (n - k.1)) / ((n + 1 : ℕ) : ℂ)
termination_by n => n
decreasing_by
  have hk := Finset.mem_range.mp k.2
  omega

lemma eulerCoeff_zero (w : ℕ → ℂ) : eulerCoeff w 0 = 1 := by
  rw [eulerCoeff]

lemma eulerCoeff_succ (w : ℕ → ℂ) (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) * eulerCoeff w (n + 1) =
      ∑ k ∈ Finset.range (n + 1),
        PowerSeries.coeff (k + 1) (lambertSeries w) * eulerCoeff w (n - k) := by
  conv_lhs => rw [eulerCoeff]
  have hne : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [mul_div_cancel₀ _ hne]
  rw [Finset.sum_attach (Finset.range (n + 1)) fun k =>
    PowerSeries.coeff (k + 1) (lambertSeries w) * eulerCoeff w (n - k)]

/-- Formal Euler product `G_w(q) = ∏_{n ≥ 1} (1 - q^n)^{-w(n)}` for arbitrary complex weights
`w : ℕ → ℂ`. -/
@[expose] def eulerProduct (w : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (eulerCoeff w)

theorem eulerProduct_constantCoeff (w : ℕ → ℂ) :
    PowerSeries.constantCoeff (eulerProduct w) = 1 := by
  simp [eulerProduct, eulerCoeff_zero]

theorem eulerProduct_ne_zero (w : ℕ → ℂ) : eulerProduct w ≠ 0 := by
  intro h0
  have h1 := congrArg PowerSeries.constantCoeff h0
  rw [eulerProduct_constantCoeff, map_zero] at h1
  exact one_ne_zero h1

theorem eulerProduct_ode (w : ℕ → ℂ) :
    PowerSeries.X * PowerSeries.derivative (eulerProduct w) =
      lambertSeries w * eulerProduct w := by
  ext n
  cases n with
  | zero =>
    rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_lambertSeries]
    simp
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
        PowerSeries.coeff i (lambertSeries w) * PowerSeries.coeff j (eulerProduct w)) (m + 1),
      Finset.sum_range_succ']
    have h0 : PowerSeries.coeff 0 (lambertSeries w) = 0 := by simp [lambertSeries]
    rw [h0, zero_mul, add_zero]
    simp only [eulerProduct, PowerSeries.coeff_mk]
    have hL : eulerCoeff w (m + 1) * ((m : ℂ) + 1) =
        ∑ k ∈ Finset.range (m + 1),
          PowerSeries.coeff (k + 1) (lambertSeries w) * eulerCoeff w (m - k) := by
      rw [mul_comm, ← Nat.cast_succ, eulerCoeff_succ]
    rw [hL]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show m + 1 - (k + 1) = m - k by omega]

/-- Uniqueness of solutions to `X * F' = H * F` with `F(0) = 1` when `H(0) = 0`. -/
theorem eq_eulerProduct_of_ode (w : ℕ → ℂ) {F : PowerSeries ℂ}
    (h0 : PowerSeries.constantCoeff F = 1)
    (hode : PowerSeries.X * PowerSeries.derivative F = lambertSeries w * F) :
    F = eulerProduct w := by
  ext n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff, h0, eulerProduct_constantCoeff]
    | succ m =>
      have hF := congrArg (PowerSeries.coeff (m + 1)) hode
      have hG := congrArg (PowerSeries.coeff (m + 1)) (eulerProduct_ode w)
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul] at hF hG
      have hm1 : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      apply mul_right_cancel₀ hm1
      rw [hF, hG]
      refine Finset.sum_congr rfl fun ab hab => ?_
      have hab' : ab.1 + ab.2 = m + 1 := by simpa using hab
      by_cases ha : ab.1 = 0
      · simp [ha, coeff_lambertSeries]
      · rw [ih ab.2 (by omega)]

/-- For nonnegative integer weights `w : ℕ → ℕ`, `eulerProduct w` equals the literal infinite
Euler product `PakPrimes.HarmonicTrap.bose w = ∏' i, ((1 - X^(i+1))⁻¹)^(w (i+1))`. -/
theorem eulerProduct_eq_bose (w : ℕ → ℕ) :
    eulerProduct (fun n => (w n : ℂ)) = PakPrimes.HarmonicTrap.bose w := by
  symm
  refine eq_eulerProduct_of_ode (fun n => (w n : ℂ)) (PakPrimes.HarmonicTrap.bose_constantCoeff w) ?_
  rw [lambertSeries_eq_modeSum]
  exact PakPrimes.HarmonicTrap.bose_euler w

/-! #### Pure-Algebra Differential Transfer in `FractionRing (PowerSeries ℂ)` -/

private abbrev PS := PowerSeries ℂ
private abbrev FracPS := FractionRing PS
private abbrev embPS : PS →ₐ[ℂ] FracPS := IsScalarTower.toAlgHom ℂ PS FracPS
private abbrev genPS {ι : Type} (v : ι → PS) : IntermediateField ℂ FracPS :=
  IntermediateField.adjoin ℂ (Set.range fun i => embPS (v i))

private lemma mem_eval_ps {ι : Type} (v : ι → PS) (P : MvPolynomial ι ℂ) :
    embPS (MvPolynomial.aeval v P) ∈ genPS v := by
  rw [MvPolynomial.comp_aeval_apply]
  induction P using MvPolynomial.induction_on with
  | C r => simp only [MvPolynomial.aeval_C]; exact (genPS v).algebraMap_mem r
  | add P Q hP hQ => simpa only [map_add] using (genPS v).add_mem hP hQ
  | mul_X P i hP =>
    simpa only [map_mul, MvPolynomial.aeval_X] using
      (genPS v).mul_mem hP (IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self i))

private lemma poly_deriv_mem_ps {ι : Type} (v : ι → PS)
    (h : ∀ i, embPS (PowerSeries.derivative (v i)) ∈ genPS v) (P : MvPolynomial ι ℂ) :
    embPS (PowerSeries.derivative (MvPolynomial.aeval v P)) ∈ genPS v := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ => simpa only [map_add] using (genPS v).add_mem hP hQ
  | mul_X P i hP =>
    simp only [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, smul_eq_mul, map_add]
    exact (genPS v).add_mem ((genPS v).mul_mem (mem_eval_ps v P) (h i))
      ((genPS v).mul_mem (IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self i)) hP)

private lemma deriv_mem_ps {ι : Type} (v : ι → PS)
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
  exact (genPS v).div_mem ((genPS v).sub_mem (poly_deriv_mem_ps v h P)
    ((genPS v).mul_mem hf (poly_deriv_mem_ps v h Q))) (mem_eval_ps v Q)

private lemma chain_ps {ι : Type} [Fintype ι] (v : ι → PS) (P : MvPolynomial ι ℂ) :
    PowerSeries.derivative (MvPolynomial.aeval v P) =
      ∑ i, MvPolynomial.aeval v (MvPolynomial.pderiv i P) * PowerSeries.derivative (v i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ, add_mul, Finset.sum_add_distrib]
  | mul_X P k hP =>
    rw [map_mul, MvPolynomial.aeval_X, Derivation.leibniz, hP]
    simp [Pi.single_apply, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
      apply_ite, ite_mul, mul_assoc]

private lemma regular_relation_ps {v : ℕ → PS} (hn : ¬ AlgebraicIndependent ℂ v) :
    ∃ (n : ℕ) (Q : MvPolynomial (Fin (n + 1)) ℂ),
      MvPolynomial.aeval (fun i => v i.val) Q = 0 ∧
      MvPolynomial.aeval (fun i => v i.val) (MvPolynomial.pderiv (Fin.last n) Q) ≠ 0 := by
  classical
  rw [algebraicIndependent_iff] at hn
  push Not at hn
  let rel (P : MvPolynomial ℕ ℂ) := P ≠ 0 ∧ MvPolynomial.aeval v P = 0
  have hex : ∃ d : ℕ, ∃ P : MvPolynomial ℕ ℂ, P.totalDegree = d ∧ rel P := by
    obtain ⟨P, hP, hne⟩ := hn; exact ⟨_, P, rfl, hne, hP⟩
  obtain ⟨P, hd, hp⟩ := Nat.find_spec hex
  have hv : P.vars.Nonempty := by
    by_contra! h
    have H := MvPolynomial.vars_eq_empty_iff_eq_C.mp h
    have hzero := hp.2
    rw [H, MvPolynomial.aeval_C] at hzero
    have hc := (algebraMap ℂ PS).injective (hzero.trans (map_zero _).symm)
    exact hp.1 (H.trans (by rw [hc, map_zero]))
  let n := P.vars.max' hv
  have hm : n ∈ P.vars := Finset.max'_mem _ _
  obtain ⟨Q, hQ⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range P
    (Fin.val : Fin (n + 1) → ℕ) Fin.val_injective
    (fun i hi => ⟨⟨i, Nat.lt_succ_of_le (Finset.le_max' _ _ hi)⟩, rfl⟩)
  have hdeg : 0 < P.totalDegree := by
    by_contra! hh
    have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hh)
    rw [hc, MvPolynomial.vars_C] at hm
    exact Finset.notMem_empty _ hm
  have hne : MvPolynomial.pderiv n P ≠ 0 := by
    obtain ⟨m, hm', h⟩ := (MvPolynomial.mem_vars_iff_mem_support n).mp hm
    have := Finsupp.mem_support_iff.mp h
    intro hz
    have he := congrArg (fun f : MvPolynomial ℕ ℂ => f.coeff (m - Finsupp.single n 1)) hz
    rw [MvPolynomial.coeff_pderiv, Finsupp.sub_add_single_one_cancel this] at he
    change _ = (0 : ℂ) at he
    refine (mul_ne_zero (MvPolynomial.mem_support_iff.mp hm') ?_) he
    exact_mod_cast Nat.succ_ne_zero (((m - Finsupp.single n 1 : ℕ →₀ ℕ)) n)
  have hnot : ¬ rel (MvPolynomial.pderiv n P) :=
    fun h => Nat.find_min hex (hd ▸ PakPrimes.BorelStokesVandermonde.degree_pderiv_lt n P hdeg) ⟨_, rfl, h⟩
  refine ⟨n, Q, ?_, ?_⟩
  · simpa [← hQ, MvPolynomial.aeval_rename, Function.comp_def] using hp.2
  · intro he
    apply hnot ⟨hne, ?_⟩
    have hd' := MvPolynomial.pderiv_rename (f := (Fin.val : Fin (n + 1) → ℕ))
      Fin.val_injective (Fin.last n) Q
    simp only [Fin.val_last] at hd'
    rw [← hQ, hd']
    simpa [MvPolynomial.aeval_rename, Function.comp_def] using he

private lemma finite_state_ps {F : PS} (hdep : ¬ AlgebraicIndependent ℂ (seriesCoordinates F)) :
    ∃ (n : ℕ) (v : Fin (n + 1) → PS), embPS PowerSeries.X ∈ genPS v ∧ embPS F ∈ genPS v ∧
      ∀ i, embPS (PowerSeries.derivative (v i)) ∈ genPS v := by
  classical
  obtain ⟨n, Q, hQ, hS⟩ := regular_relation_ps hdep
  let v (i : Fin (n + 1)) : PS := seriesCoordinates F i.val
  let s := Fin.last n
  let w (i : Fin (n + 1)) := MvPolynomial.aeval v (MvPolynomial.pderiv i Q)
  have van : ∑ i, w i * PowerSeries.derivative (v i) = 0 := by
    rw [← chain_ps, hQ, map_zero]
  have hv (i : Fin (n + 1)) : embPS (v i) ∈ genPS v :=
    IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self _)
  have hn : 0 < n := by
    by_contra! hh
    obtain rfl := Nat.eq_zero_of_le_zero hh
    change (∑ i : Fin 1, w i * PowerSeries.derivative (v i)) = 0 at van
    have van0 : w 0 * PowerSeries.derivative (v 0) = 0 := by simpa only [Fin.sum_univ_one] using van
    have h₀ : PowerSeries.derivative (v 0) = 1 := PowerSeries.derivative_X
    rw [h₀, mul_one] at van0
    exact hS van0
  refine ⟨n, v, hv 0, hv ⟨1, by omega⟩, ?_⟩
  have low (i : Fin (n + 1)) (hi : i ≠ s) : embPS (PowerSeries.derivative (v i)) ∈ genPS v := by
    rcases i with ⟨i, hi'⟩
    cases i with
    | zero =>
      change embPS (PowerSeries.derivative PowerSeries.X) ∈ genPS v
      simp
    | succ k =>
      have hh : k + 1 ≠ n := fun h => hi (Fin.ext h)
      have hl : k + 2 < n + 1 := by omega
      have he := Function.iterate_succ_apply' PowerSeries.derivative k F
      exact he ▸ hv (⟨k + 2, hl⟩ : Fin (n + 1))
  intro i
  by_cases hi : i = s
  · subst i
    let S := Finset.univ.erase s
    let a := ∑ j ∈ S, w j * PowerSeries.derivative (v j)
    have ha : embPS a ∈ genPS v := by
      dsimp [a]
      rw [map_sum]
      exact (genPS v).sum_mem fun j hj => by
        rw [map_mul]; exact (genPS v).mul_mem (mem_eval_ps v _) (low j (Finset.mem_erase.mp hj).1)
    have hbot : embPS (w s) ≠ 0 :=
      (map_ne_zero_iff embPS (IsFractionRing.injective PS FracPS)).mpr hS
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)] at van
    change w s * PowerSeries.derivative (v s) + a = 0 at van
    have hm := congrArg embPS van
    simp only [map_zero, map_add, map_mul] at hm
    have he : embPS (PowerSeries.derivative (v s)) = -embPS a / embPS (w s) := by
      apply (eq_div_iff hbot).mpr
      linear_combination hm
    rw [he]
    exact (genPS v).div_mem ((genPS v).neg_mem ha) (mem_eval_ps v _)
  · exact low i hi

private lemma not_independent_in_gen_ps {ι : Type} [Fintype ι] (v : ι → PS)
    (y : ℕ → PS) (h : ∀ i, embPS (y i) ∈ genPS v) : ¬ AlgebraicIndependent ℂ y := by
  intro hi
  have hfg : (genPS v).FG := IntermediateField.fg_adjoin_of_finite (Set.finite_range _)
  let : Algebra.EssFiniteType ℂ (genPS v) := IntermediateField.essFiniteType_iff.mpr hfg
  have hE : AlgebraicIndependent ℂ (embPS ∘ y) :=
    (embPS.algebraicIndependent_iff (IsFractionRing.injective PS FracPS)).mpr hi
  have hS : AlgebraicIndependent ℂ (fun i => (⟨embPS (y i), h i⟩ : genPS v)) :=
    hE.of_comp (genPS v).val
  let : Finite ℕ := finite_of_algebraicIndependent hS
  exact not_finite ℕ

/-- **Pure-Algebra Log-Derivative Transfer**:
If `G ≠ 0` satisfies `X * G' = H * G` in `ℂ[[X]]` and `H` is differentially transcendental over
`ℂ(X)`, then `G` is differentially transcendental over `ℂ(X)`. -/
theorem algIndep_of_log_deriv {G H : PowerSeries ℂ}
    (hG : G ≠ 0) (hode : PowerSeries.X * PowerSeries.derivative G = H * G)
    (hH : AlgebraicIndependent ℂ (seriesCoordinates H)) :
    AlgebraicIndependent ℂ (seriesCoordinates G) := by
  by_contra hdep
  obtain ⟨n, v, hX, hGmem, hv⟩ := finite_state_ps hdep
  have hGne : embPS G ≠ 0 :=
    (map_ne_zero_iff embPS (IsFractionRing.injective PS FracPS)).mpr hG
  have hHmem : embPS H ∈ genPS v := by
    have hm := congrArg embPS hode
    simp only [map_mul] at hm
    have hEq : embPS H = embPS PowerSeries.X * embPS (PowerSeries.derivative G) / embPS G := by
      apply (eq_div_iff hGne).mpr
      exact hm.symm
    rw [hEq]
    exact (genPS v).div_mem ((genPS v).mul_mem hX (deriv_mem_ps v hv hGmem)) hGmem
  apply not_independent_in_gen_ps v (seriesCoordinates H) _ hH
  intro i
  cases i with
  | zero => exact hX
  | succ j =>
    change embPS (seriesJet H j) ∈ genPS v
    induction j with
    | zero => exact hHmem
    | succ j ih =>
      simpa only [seriesJet, Function.iterate_succ_apply'] using deriv_mem_ps v hv ih

/-- Any polynomial in `PowerSeries.X` embeds into `genPS v` whenever `embPS X ∈ genPS v`. -/
private lemma poly_mem_gen_ps {ι : Type} (v : ι → PS) (hX : embPS PowerSeries.X ∈ genPS v)
    (p : Polynomial ℂ) : embPS (p : PowerSeries ℂ) ∈ genPS v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.coe_add, map_add]
    exact (genPS v).add_mem hp hq
  | monomial k a =>
    rw [Polynomial.coe_monomial]
    have hmon : (PowerSeries.monomial k a : PowerSeries ℂ) = PowerSeries.C a * PowerSeries.X ^ k := by
      ext m
      simp [PowerSeries.coeff_monomial]
    rw [hmon, map_mul, map_pow]
    exact (genPS v).mul_mem ((genPS v).algebraMap_mem a) ((genPS v).pow_mem hX k)

/-- **Pure-Algebra Rational Perturbation Transfer**:
Adding any rational power series `R` (`D * R = N` for polynomials `D ≠ 0`, `N`) preserves
differential transcendence over `ℂ(X)`. -/
theorem algIndep_of_add_rat {H R : PowerSeries ℂ} {D N : Polynomial ℂ}
    (hD : D ≠ 0) (hDR : (D : PowerSeries ℂ) * R = (N : PowerSeries ℂ))
    (hH : AlgebraicIndependent ℂ (seriesCoordinates H)) :
    AlgebraicIndependent ℂ (seriesCoordinates (H + R)) := by
  by_contra hdep
  obtain ⟨n, v, hX, hHRmem, hv⟩ := finite_state_ps hdep
  have hD_ps_ne : (D : PowerSeries ℂ) ≠ 0 := by
    intro h0; exact hD (Polynomial.coe_inj.mp (h0.trans Polynomial.coe_zero.symm))
  have hD_emb_ne : embPS (D : PowerSeries ℂ) ≠ 0 :=
    (map_ne_zero_iff embPS (IsFractionRing.injective PS FracPS)).mpr hD_ps_ne
  have hRmem : embPS R ∈ genPS v := by
    have hm := congrArg embPS hDR
    rw [map_mul] at hm
    have hEq : embPS R = embPS (N : PowerSeries ℂ) / embPS (D : PowerSeries ℂ) := by
      apply (eq_div_iff hD_emb_ne).mpr
      rw [mul_comm]; exact hm
    rw [hEq]
    exact (genPS v).div_mem (poly_mem_gen_ps v hX N) (poly_mem_gen_ps v hX D)
  have hHmem : embPS H ∈ genPS v := by
    have hEq : embPS H = embPS (H + R) - embPS R := by rw [map_add]; ring
    rw [hEq]
    exact (genPS v).sub_mem hHRmem hRmem
  apply not_independent_in_gen_ps v (seriesCoordinates H) _ hH
  intro i
  cases i with
  | zero => exact hX
  | succ j =>
    change embPS (seriesJet H j) ∈ genPS v
    induction j with
    | zero => exact hHmem
    | succ j ih =>
      simpa only [seriesJet, Function.iterate_succ_apply'] using deriv_mem_ps v hv ih

/-- If `w₁` and `w₂` agree for all `n ≥ N₀`, then `lambertSeries w₁ - lambertSeries w₂` is rational
in `X`, so `lambertSeries w₁` and `lambertSeries w₂` have equivalent differential transcendence. -/
theorem algIndep_lambertSeries_of_eventually_eq {w₁ w₂ : ℕ → ℂ} {N₀ : ℕ}
    (heq : ∀ n : ℕ, N₀ ≤ n → w₁ n = w₂ n)
    (h₂ : AlgebraicIndependent ℂ (seriesCoordinates (lambertSeries w₂))) :
    AlgebraicIndependent ℂ (seriesCoordinates (lambertSeries w₁)) := by
  let R : PowerSeries ℂ := lambertSeries w₁ - lambertSeries w₂
  have hsplit : lambertSeries w₁ = lambertSeries w₂ + R := by dsimp [R]; ring
  rw [hsplit]
  -- Each single term `k * (w₁ k - w₂ k) * X^k / (1 - X^k)` is cleared by `1 - X^k`.
  let S : Finset ℕ := Finset.Ico 1 N₀
  let D : Polynomial ℂ := ∏ k ∈ S, (1 - Polynomial.X ^ k)
  let N : Polynomial ℂ :=
    ∑ k ∈ S, Polynomial.C ((k : ℂ) * (w₁ k - w₂ k)) * Polynomial.X ^ k *
      ∏ j ∈ S.erase k, (1 - Polynomial.X ^ j)
  have hD_ne : D ≠ 0 := by
    dsimp only [D]
    rw [Finset.prod_ne_zero_iff]
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    intro h0
    have hc := congrArg (fun p : Polynomial ℂ => p.coeff 0) h0
    simp [Polynomial.coeff_X_pow, show (0 : ℕ) ≠ k by omega] at hc
  -- Prove `(1 - X^k) * lambertSingle k = X^k` where `lambertSingle k = ∑_{m ≥ 1} X^{m*k}`.
  have hR_eq : R = ∑ k ∈ S, PowerSeries.C ((k : ℂ) * (w₁ k - w₂ k)) *
      (PowerSeries.X ^ k * (1 - PowerSeries.X ^ k)⁻¹) := by
    ext n
    have hterm_coeff : ∀ k ∈ S,
        PowerSeries.coeff n (PowerSeries.C ((k : ℂ) * (w₁ k - w₂ k)) *
          (PowerSeries.X ^ k * (1 - PowerSeries.X ^ k)⁻¹)) =
        if n ≠ 0 ∧ k ∣ n then (k : ℂ) * (w₁ k - w₂ k) else 0 := fun k hk => by
      have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
      have hgeom : (1 - (PowerSeries.X : PowerSeries ℂ) ^ k)⁻¹ =
          PakPrimes.DivisorAndMacMahon.EulerGeometric (k - 1) := by
        rw [PakPrimes.DivisorAndMacMahon.EulerGeometric_eq_inv, Nat.sub_add_cancel hk1]
      have hmul : PowerSeries.X ^ k * PakPrimes.DivisorAndMacMahon.EulerGeometric (k - 1) =
          PakPrimes.DivisorAndMacMahon.EulerGeometric (k - 1) - 1 := by
        have hinv : PakPrimes.DivisorAndMacMahon.EulerGeometric (k - 1) *
            (1 - (PowerSeries.X : PowerSeries ℂ) ^ k) = 1 := by
          rw [PakPrimes.DivisorAndMacMahon.EulerGeometric_eq_inv, Nat.sub_add_cancel hk1]
          exact PowerSeries.inv_mul_cancel _ (by simp [show k ≠ 0 by omega])
        linear_combination -hinv
      rw [hgeom, hmul, PowerSeries.coeff_C_mul, map_sub,
        PakPrimes.DivisorAndMacMahon.EulerGeometric, PowerSeries.coeff_mk, PowerSeries.coeff_one,
        Nat.sub_add_cancel hk1]
      by_cases hn0 : n = 0
      · subst hn0; simp
      · simp only [hn0, ↓reduceIte, sub_zero, ne_eq, not_false_eq_true, true_and]
        split_ifs <;> ring
    rw [map_sum, Finset.sum_congr rfl hterm_coeff]
    dsimp only [R]
    rw [map_sub, coeff_lambertSeries, coeff_lambertSeries]
    by_cases hn0 : n = 0
    · subst hn0; simp
    · simp only [hn0, ↓reduceIte, ne_eq, not_false_eq_true, true_and, ← Finset.sum_sub_distrib]
      have hsub_div : (∑ d ∈ Nat.divisors n, ((d : ℂ) * w₁ d - (d : ℂ) * w₂ d)) =
          ∑ d ∈ (Nat.divisors n).filter (fun d => d ∈ S), (d : ℂ) * (w₁ d - w₂ d) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun d hd => ?_
        have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
        by_cases hdN : d < N₀
        · have hmem : d ∈ S := Finset.mem_Ico.mpr ⟨hd1, hdN⟩
          simp only [hmem, ↓reduceIte]; ring
        · have hnot : d ∉ S := by simp [S, hdN]
          simp only [hnot, ↓reduceIte, heq d (by omega), sub_self]
      rw [hsub_div, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext k
      simp only [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨fun ⟨⟨h2, _⟩, h1⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨h2, hn0⟩, h1⟩⟩
  have hDR : (D : PowerSeries ℂ) * R = (N : PowerSeries ℂ) := by
    rw [hR_eq, Finset.mul_sum]
    dsimp only [D, N]
    have hcoe_sum :
        ((∑ k ∈ S, Polynomial.C ((k : ℂ) * (w₁ k - w₂ k)) * Polynomial.X ^ k *
          ∏ j ∈ S.erase k, (1 - Polynomial.X ^ j) : Polynomial ℂ) : PowerSeries ℂ) =
        ∑ k ∈ S, ((Polynomial.C ((k : ℂ) * (w₁ k - w₂ k)) * Polynomial.X ^ k *
          ∏ j ∈ S.erase k, (1 - Polynomial.X ^ j) : Polynomial ℂ) : PowerSeries ℂ) :=
      map_sum Polynomial.coeToPowerSeries.ringHom _ S
    rw [hcoe_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    let Qk : Polynomial ℂ := ∏ j ∈ S.erase k, (1 - Polynomial.X ^ j)
    have hDsplit : (∏ j ∈ S, (1 - Polynomial.X ^ j) : Polynomial ℂ) =
        (1 - Polynomial.X ^ k) * Qk :=
      (Finset.mul_prod_erase S (fun j => 1 - Polynomial.X ^ j) hk).symm
    change ((∏ j ∈ S, (1 - Polynomial.X ^ j) : Polynomial ℂ) : PowerSeries ℂ) *
        (PowerSeries.C ((k : ℂ) * (w₁ k - w₂ k)) * (PowerSeries.X ^ k * (1 - PowerSeries.X ^ k)⁻¹)) =
      ((Polynomial.C ((k : ℂ) * (w₁ k - w₂ k)) * Polynomial.X ^ k * Qk : Polynomial ℂ) : PowerSeries ℂ)
    rw [hDsplit]
    simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_pow,
      Polynomial.coe_X, Polynomial.coe_C]
    have hcancel : (1 - (PowerSeries.X : PowerSeries ℂ) ^ k) *
        (1 - (PowerSeries.X : PowerSeries ℂ) ^ k)⁻¹ = 1 :=
      PowerSeries.mul_inv_cancel _ (by simp [show k ≠ 0 by omega])
    calc ((1 - PowerSeries.X ^ k) * (Qk : PowerSeries ℂ)) *
          (PowerSeries.C ((k : ℂ) * (w₁ k - w₂ k)) * (PowerSeries.X ^ k * (1 - PowerSeries.X ^ k)⁻¹))
        = (PowerSeries.C ((k : ℂ) * (w₁ k - w₂ k)) * PowerSeries.X ^ k * (Qk : PowerSeries ℂ)) *
          ((1 - PowerSeries.X ^ k) * (1 - PowerSeries.X ^ k)⁻¹) := by ring
      _ = _ := by rw [hcancel, mul_one]
  exact algIndep_of_add_rat hD_ne hDR h₂

/-! ### 3. Smooth Kernel `hPow d` and Shifted Euler–Maclaurin Asymptotics (`sumScaleShift`) -/

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

private lemma iteratedDeriv_qFun_zero' (n : ℕ) :
    iteratedDeriv n qFun 0 = (bernoulli n : ℂ) := by
  have hcexp : ∀ k : ℕ, iteratedDeriv k Complex.exp 0 = 1 := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iteratedDeriv_succ', show deriv Complex.exp = Complex.exp from by ext z; simp, ih]
  have hqC : ∀ m : ℕ, iteratedDeriv m qComplex 0 = (bernoulli m : ℂ) := fun m => by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      have hq_an : AnalyticAt ℂ qComplex 0 := by simpa using qComplex_analytic_ofReal' 0
      have hexp_an : AnalyticAt ℂ (fun z : ℂ => Complex.exp z - 1) 0 := by fun_prop
      have heq_nhds : (fun z : ℂ => qComplex z * (Complex.exp z - 1)) =ᶠ[𝓝 (0 : ℂ)] id := by
        have hne : ∀ᶠ z in 𝓝 (0 : ℂ), expAux z ≠ 0 :=
          (expAux_analytic' 0).continuousAt.eventually_ne (by rw [expAux_zero']; exact one_ne_zero)
        filter_upwards [hne] with z hz
        exact qComplex_mul_exp_sub_one' z hz
      have hderiv_eq := heq_nhds.iteratedDeriv_eq (m + 1)
      rw [iteratedDeriv_fun_mul hq_an.contDiffAt hexp_an.contDiffAt] at hderiv_eq
      have hexp_deriv : ∀ k : ℕ, iteratedDeriv k (fun z : ℂ => Complex.exp z - 1) 0 =
          if k = 0 then 0 else 1 := fun k => by
        cases k with
        | zero => simp
        | succ k' =>
          rw [iteratedDeriv_succ', show deriv (fun z : ℂ => Complex.exp z - 1) = Complex.exp from
            by ext z; simp, hcexp k']; simp
      have h_lhs : (∑ k ∈ Finset.range (m + 1 + 1),
          ((m + 1).choose k : ℂ) * iteratedDeriv k qComplex 0 *
            iteratedDeriv (m + 1 - k) (fun z : ℂ => Complex.exp z - 1) 0) =
          ∑ k ∈ Finset.range (m + 1), ((m + 1).choose k : ℂ) * iteratedDeriv k qComplex 0 := by
        rw [Finset.sum_range_succ]
        simp only [Nat.sub_self, hexp_deriv 0, ↓reduceIte, mul_zero, add_zero]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkne : m + 1 - k ≠ 0 := by have := Finset.mem_range.mp hk; omega
        simp [hexp_deriv (m + 1 - k), hkne]
      have h_rhs : iteratedDeriv (m + 1) (id : ℂ → ℂ) 0 = if m = 0 then 1 else 0 := by
        cases m with
        | zero => simp
        | succ k' =>
          rw [iteratedDeriv_succ', show deriv (id : ℂ → ℂ) = fun _ => 1 from by ext z; simp,
            iteratedDeriv_const]
      rw [h_lhs, h_rhs] at hderiv_eq
      have hbern : (∑ k ∈ Finset.range (m + 1), ((m + 1).choose k : ℂ) * (bernoulli k : ℂ)) =
          if m = 0 then 1 else 0 := by
        have hb := congrArg (fun q : ℚ => (q : ℂ)) (sum_bernoulli (m + 1))
        cases m with
        | zero => simp
        | succ k' =>
          have hne1 : k' + 1 + 1 ≠ 1 := by omega
          simp only [hne1, ↓reduceIte, Rat.cast_zero, Rat.cast_sum, Rat.cast_mul,
            Rat.cast_natCast] at hb
          simpa [Nat.succ_ne_zero] using hb
      have hdiff : ∑ k ∈ Finset.range (m + 1),
          ((m + 1).choose k : ℂ) * (iteratedDeriv k qComplex 0 - (bernoulli k : ℂ)) = 0 := by
        simp_rw [mul_sub, Finset.sum_sub_distrib, hderiv_eq, hbern, sub_self]
      rw [Finset.sum_range_succ] at hdiff
      have htail : ∑ k ∈ Finset.range m,
          ((m + 1).choose k : ℂ) * (iteratedDeriv k qComplex 0 - (bernoulli k : ℂ)) = 0 :=
        Finset.sum_eq_zero fun k hk => by rw [ih k (Finset.mem_range.mp hk), sub_self, mul_zero]
      rw [htail, zero_add, Nat.choose_succ_self_right] at hdiff
      exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left
        (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)))
  change iteratedDeriv n (fun t : ℝ => qComplex (t : ℂ)) 0 = _
  rw [iteratedDeriv_ofReal_comp' qComplex_analytic_ofReal' n 0]
  exact hqC n

private lemma qFun_contDiff' : ContDiff ℝ (⊤ : ℕ∞) qFun :=
  contDiff_iff_contDiffAt.mpr fun x =>
    ((qComplex_analytic_ofReal' x).restrictScalars.contDiffAt.comp x
      (Complex.ofRealCLM.contDiff.contDiffAt)).of_le le_top

private lemma eds_deriv {h : ℝ → ℂ} (hh : ExpDecaySmooth h) : ExpDecaySmooth (deriv h) := by
  refine ⟨(contDiff_infty_iff_deriv.mp hh.1).2, fun r => ?_⟩
  obtain ⟨C, c, hC, hc, hbd⟩ := hh.2 (r + 1)
  exact ⟨C, c, hC, hc, fun x hx => by rw [← iteratedDeriv_succ']; exact hbd x hx⟩

private lemma eds_const_mul {h : ℝ → ℂ} (a : ℂ) (hh : ExpDecaySmooth h) :
    ExpDecaySmooth (fun x => a * h x) := by
  refine ⟨contDiff_const.mul hh.1, fun r => ?_⟩
  obtain ⟨C, c, hC, hc, hbd⟩ := hh.2 r
  refine ⟨‖a‖ * C, c, mul_nonneg (norm_nonneg a) hC, hc, fun x hx => ?_⟩
  rw [iteratedDeriv_const_mul_field, norm_mul]
  calc ‖a‖ * ‖iteratedDeriv r h x‖ ≤ ‖a‖ * (C * Real.exp (-c * x)) :=
        mul_le_mul_of_nonneg_left (hbd x hx) (norm_nonneg a)
    _ = ‖a‖ * C * Real.exp (-c * x) := by ring

private lemma eds_sub {f g : ℝ → ℂ} (hf : ExpDecaySmooth f) (hg : ExpDecaySmooth g) :
    ExpDecaySmooth (fun x => f x - g x) := by
  refine ⟨hf.1.sub hg.1, fun r => ?_⟩
  obtain ⟨Cf, cf, hCf, hcf, hbf⟩ := hf.2 r
  obtain ⟨Cg, cg, hCg, hcg, hbg⟩ := hg.2 r
  refine ⟨Cf + Cg, min cf cg, by positivity, lt_min hcf hcg, fun x hx => ?_⟩
  rw [iteratedDeriv_fun_sub (hf.1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
    (hg.1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))]
  have h1 : Real.exp (-cf * x) ≤ Real.exp (-min cf cg * x) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left cf cg])
  have h2 : Real.exp (-cg * x) ≤ Real.exp (-min cf cg * x) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right cf cg])
  calc ‖iteratedDeriv r f x - iteratedDeriv r g x‖
      ≤ ‖iteratedDeriv r f x‖ + ‖iteratedDeriv r g x‖ := norm_sub_le _ _
    _ ≤ Cf * Real.exp (-cf * x) + Cg * Real.exp (-cg * x) := add_le_add (hbf x hx) (hbg x hx)
    _ ≤ Cf * Real.exp (-min cf cg * x) + Cg * Real.exp (-min cf cg * x) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hCf) (mul_le_mul_of_nonneg_left h2 hCg)
    _ = (Cf + Cg) * Real.exp (-min cf cg * x) := by ring

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

private lemma eds_emStep {h : ℝ → ℂ} (a : ℕ) (hh : ExpDecaySmooth h) :
    ExpDecaySmooth (emStep a h) :=
  eds_sub (eds_const_mul (-(a : ℂ)) hh) (eds_mul_ofReal (eds_deriv hh))

private lemma eds_emIter {h : ℝ → ℂ} (j : ℕ) (hh : ExpDecaySmooth h) :
    ExpDecaySmooth (emIter j h) := by
  induction j with
  | zero => exact hh
  | succ j ih => exact eds_emStep j ih

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

/-- Smooth exponentially decaying kernel `hPow d x = x^{d+1} / (e^x - 1) = x^d * qFun x`. -/
@[expose] def hPow (d : ℕ) (x : ℝ) : ℂ := (x : ℂ) ^ d * qFun x

private lemma hPow_expDecaySmooth (d : ℕ) : ExpDecaySmooth (hPow d) :=
  eds_pow_ofReal_mul d qFun_expDecaySmooth'

private lemma hPow_eq_div_exp_sub_one (d : ℕ) {x : ℝ} (hx : x ≠ 0) :
    hPow d x = (x : ℂ) ^ (d + 1) / (Complex.exp (x : ℂ) - 1) := by
  rw [hPow, qFun_eq_div_exp_sub_one' hx, mul_div_assoc', ← pow_succ]

private lemma iteratedDeriv_hPow_zero (d r : ℕ) :
    iteratedDeriv r (hPow d) 0 =
      if r < d then 0
      else ((r.factorial : ℂ) / ((r - d).factorial : ℂ)) * (bernoulli (r - d) : ℂ) := by
  unfold hPow
  have hpow : ContDiffAt ℝ r (fun x : ℝ => (x : ℂ) ^ d) 0 :=
    (Complex.ofRealCLM.contDiff.pow d).contDiffAt.of_le le_top
  have hq : ContDiffAt ℝ r qFun 0 := qFun_contDiff'.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedDeriv_fun_mul hpow hq]
  have hid : ∀ i : ℕ, iteratedDeriv i (fun x : ℝ => (x : ℂ) ^ d) 0 =
      if i = d then (d.factorial : ℂ) else 0 := fun i => by
    have hcomp := iteratedDeriv_ofReal_comp' (F := fun z : ℂ => z ^ d) (fun _ => by fun_prop) i 0
    change iteratedDeriv i (fun x : ℝ => (fun z : ℂ => z ^ d) (x : ℂ)) 0 = _
    rw [hcomp, iteratedDeriv_pow]
    by_cases hi : i = d
    · subst hi; simp [Nat.descFactorial_self]
    · simp only [hi, ↓reduceIte]
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · simp [zero_pow (by omega : d - i ≠ 0)]
      · simp [Nat.descFactorial_of_lt hgt]
  split_ifs with hlt
  · refine Finset.sum_eq_zero fun i hi => ?_
    have hi_lt : i < d := (Finset.mem_range.mp hi).trans_le (by omega)
    simp [hid i, hi_lt.ne]
  · have hle : d ≤ r := by omega
    rw [Finset.sum_eq_single d]
    · rw [hid d, iteratedDeriv_qFun_zero']
      simp only [↓reduceIte]
      have hch := congrArg (fun k : ℕ => (k : ℂ)) (Nat.choose_mul_factorial_mul_factorial hle)
      push_cast at hch
      have hfac1 : ((r - d).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      field_simp [hfac1]
      linear_combination (bernoulli (r - d) : ℂ) * hch
    · intro i _ hine; simp [hid i, hine]
    · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot

/-- Reflection identity `bernoulliFun k (1 - q) = (-1)^k * bernoulliFun k q` for rational `q : ℚ`. -/
private lemma bernoulliFun_one_sub_rat (k : ℕ) (q : ℚ) :
    bernoulliFun k (1 - (q : ℝ)) = (-1 : ℝ) ^ k * bernoulliFun k (q : ℝ) := by
  unfold bernoulliFun
  have h1 : (1 - (q : ℝ)) = algebraMap ℚ ℝ (1 - q) := by simp
  have h2 : (q : ℝ) = algebraMap ℚ ℝ q := by simp
  rw [h1, h2, Polynomial.eval_map_apply, Polynomial.eval_map_apply, Polynomial.bernoulli_eval_one_sub]
  simp

/-- Shifted positive-lattice sum `∑_{n ≥ 0} h((n + θ) / u)` for `θ ∈ (0, 1]`. -/
@[expose] def sumScaleShift (θ : ℝ) (h : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑' n : ℕ, h (((n : ℝ) + θ) / u)

/-- Shifted Euler–Maclaurin `1/u^r` coefficient `-B_{r+1}(θ) / (r+1)! * h^{(r)}(0)`. -/
@[expose] def emTermShift (θ : ℝ) (h : ℝ → ℂ) (r : ℕ) : ℂ :=
  -(((bernoulliFun (r + 1) θ : ℝ) : ℂ) / ((r + 1).factorial : ℂ)) * iteratedDeriv r h 0

/-- Formal shifted Euler–Maclaurin power series `∑_{r ≥ 0} emTermShift θ h r * w^r`. -/
@[expose] def emSeriesShift (θ : ℝ) (h : ℝ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (emTermShift θ h)

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

/-- Two-piece periodic-Bernoulli remainder integral on `[0, θ]` and `[θ, 1]`. -/
private def emIntTermShift (θ : ℝ) (h : ℝ → ℂ) (u : ℝ) (r n : ℕ) : ℂ :=
  (u : ℂ)⁻¹ ^ r *
    ((∫ t in (0 : ℝ)..θ, ((bernoulliFun r (t + 1 - θ) / (r.factorial : ℝ) : ℝ) : ℂ) *
        iteratedDeriv r h (((n : ℝ) + t) / u)) +
     (∫ t in θ..1, ((bernoulliFun r (t - θ) / (r.factorial : ℝ) : ℝ) : ℂ) *
        iteratedDeriv r h (((n : ℝ) + t) / u)))

private lemma emIntTermShift_norm_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {h : ℝ → ℂ} (hh : ExpDecaySmooth h) (r : ℕ) :
    ∃ (Cr cr Br : ℝ), 0 ≤ Cr ∧ 0 < cr ∧ 0 ≤ Br ∧
      ∀ {u : ℝ}, 0 < u → ∀ n : ℕ,
        ‖emIntTermShift θ h u r n‖ ≤
          u⁻¹ ^ r * (Cr * Br) * (Real.exp (-cr / u)) ^ n := by
  obtain ⟨Cr, cr, hCr, hcr, hbd⟩ := hh.2 r
  have hcont_b : ContinuousOn (fun s : ℝ => |bernoulliFun r s / (r.factorial : ℝ)|) (Icc 0 1) :=
    (((continuous_bernoulliFun r).div_const _).abs).continuousOn
  obtain ⟨sm, _, hsm⟩ := isCompact_Icc.exists_isMaxOn ⟨0, left_mem_Icc.mpr zero_le_one⟩ hcont_b
  let M_b : ℝ := |bernoulliFun r sm / (r.factorial : ℝ)|
  have hMb_nn : 0 ≤ M_b := abs_nonneg _
  refine ⟨Cr, cr, M_b, hCr, hcr, hMb_nn, fun {u} hu n => ?_⟩
  have hpiece : ∀ {a b : ℝ} (hab : a ≤ b) (ha0 : 0 ≤ a) (f_arg : ℝ → ℝ),
      Continuous f_arg → (∀ t ∈ Icc a b, f_arg t ∈ Icc (0 : ℝ) 1) →
      ‖∫ t in a..b, ((bernoulliFun r (f_arg t) / (r.factorial : ℝ) : ℝ) : ℂ) *
          iteratedDeriv r h (((n : ℝ) + t) / u)‖ ≤
        (b - a) * (Cr * M_b * (Real.exp (-cr / u)) ^ n) := by
    intro a b hab ha0 f_arg hf_cont hf_mem
    have hint1 : IntervalIntegrable (fun t : ℝ =>
        ((bernoulliFun r (f_arg t) / (r.factorial : ℝ) : ℝ) : ℂ) *
          iteratedDeriv r h (((n : ℝ) + t) / u)) volume a b := by
      refine Continuous.intervalIntegrable ?_ a b
      exact (Complex.continuous_ofReal.comp
        (((continuous_bernoulliFun r).comp hf_cont).div_const _)).mul
        ((eds_iteratedDeriv_smooth hh r).1.continuous.comp
          ((continuous_const.add continuous_id).div_const u))
    calc ‖∫ t in a..b, _‖
        ≤ ∫ t in a..b, ‖((bernoulliFun r (f_arg t) / (r.factorial : ℝ) : ℝ) : ℂ) *
            iteratedDeriv r h (((n : ℝ) + t) / u)‖ :=
          intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ _t in a..b, ((Cr * M_b * (Real.exp (-cr / u)) ^ n : ℝ)) := by
          refine intervalIntegral.integral_mono_on hab hint1.norm intervalIntegrable_const fun t ht => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have hb_le : |bernoulliFun r (f_arg t) / (r.factorial : ℝ)| ≤ M_b := hsm (hf_mem t ht)
          have ht_nn : 0 ≤ ((n : ℝ) + t) / u := div_nonneg (by linarith [ht.1]) hu.le
          have hh_le := hbd (((n : ℝ) + t) / u) ht_nn
          have hexp_le : Real.exp (-cr * (((n : ℝ) + t) / u)) ≤ (Real.exp (-cr / u)) ^ n := by
            rw [← Real.exp_nat_mul]
            apply Real.exp_le_exp.mpr
            have : (n : ℝ) / u ≤ ((n : ℝ) + t) / u :=
              div_le_div_of_nonneg_right (by linarith [ht.1]) hu.le
            calc -cr * (((n : ℝ) + t) / u) ≤ -cr * ((n : ℝ) / u) :=
                  mul_le_mul_of_nonpos_left this (by linarith)
              _ = (n : ℝ) * (-cr / u) := by ring
          calc |bernoulliFun r (f_arg t) / (r.factorial : ℝ)| *
                ‖iteratedDeriv r h (((n : ℝ) + t) / u)‖
              ≤ M_b * (Cr * Real.exp (-cr * (((n : ℝ) + t) / u))) :=
                mul_le_mul hb_le hh_le (norm_nonneg _) hMb_nn
            _ ≤ M_b * (Cr * (Real.exp (-cr / u)) ^ n) := by gcongr
            _ = Cr * M_b * (Real.exp (-cr / u)) ^ n := by ring
      _ = (b - a) * (Cr * M_b * (Real.exp (-cr / u)) ^ n) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
  have hp1 := hpiece hθ0 le_rfl (fun t => t + 1 - θ) (by fun_prop)
    (fun t ht => ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩)
  have hp2 := hpiece hθ1 hθ0 (fun t => t - θ) (by fun_prop)
    (fun t ht => ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩)
  unfold emIntTermShift
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  have hsum_le : ‖(∫ t in (0 : ℝ)..θ, ((bernoulliFun r (t + 1 - θ) / (r.factorial : ℝ) : ℝ) : ℂ) *
        iteratedDeriv r h (((n : ℝ) + t) / u)) +
      (∫ t in θ..1, ((bernoulliFun r (t - θ) / (r.factorial : ℝ) : ℝ) : ℂ) *
        iteratedDeriv r h (((n : ℝ) + t) / u))‖ ≤
      Cr * M_b * (Real.exp (-cr / u)) ^ n := by
    calc ‖(∫ t in (0 : ℝ)..θ, ((bernoulliFun r (t + 1 - θ) / (r.factorial : ℝ) : ℝ) : ℂ) *
            iteratedDeriv r h (((n : ℝ) + t) / u)) +
          (∫ t in θ..1, ((bernoulliFun r (t - θ) / (r.factorial : ℝ) : ℝ) : ℂ) *
            iteratedDeriv r h (((n : ℝ) + t) / u))‖
        ≤ ‖∫ t in (0 : ℝ)..θ, ((bernoulliFun r (t + 1 - θ) / (r.factorial : ℝ) : ℝ) : ℂ) *
            iteratedDeriv r h (((n : ℝ) + t) / u)‖ +
          ‖∫ t in θ..1, ((bernoulliFun r (t - θ) / (r.factorial : ℝ) : ℝ) : ℂ) *
            iteratedDeriv r h (((n : ℝ) + t) / u)‖ := norm_add_le _ _
      _ ≤ (θ - 0) * (Cr * M_b * (Real.exp (-cr / u)) ^ n) +
          (1 - θ) * (Cr * M_b * (Real.exp (-cr / u)) ^ n) := add_le_add hp1 hp2
      _ = Cr * M_b * (Real.exp (-cr / u)) ^ n := by ring
  calc u⁻¹ ^ r * ‖_‖ ≤ u⁻¹ ^ r * (Cr * M_b * (Real.exp (-cr / u)) ^ n) :=
        mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = u⁻¹ ^ r * (Cr * M_b) * (Real.exp (-cr / u)) ^ n := by ring

private lemma summable_emIntTermShift {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {h : ℝ → ℂ} (hh : ExpDecaySmooth h) (r : ℕ) {u : ℝ} (hu : 0 < u) :
    Summable (fun n : ℕ => emIntTermShift θ h u r n) := by
  obtain ⟨Cr, cr, Br, hCr, hcr, hBr, hbd⟩ := emIntTermShift_norm_le hθ0 hθ1 hh r
  have hlt : Real.exp (-cr / u) < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith) hu)
  have hgeom : Summable (fun n : ℕ => (u⁻¹ ^ r * (Cr * Br)) * (Real.exp (-cr / u)) ^ n) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hlt).mul_left _
  exact hgeom.of_norm_bounded fun n => hbd hu n

private lemma sum_emIntTermShift_zero {θ : ℝ} {h : ℝ → ℂ} (hh : ExpDecaySmooth h)
    {u : ℝ} (hu : 0 < u) (N : ℕ) :
    ∑ n ∈ Finset.range N, emIntTermShift θ h u 0 n =
      (u : ℂ) * (∫ y in (0 : ℝ)..((N : ℝ) / u), h y) := by
  have heach : ∀ n ∈ Finset.range N,
      emIntTermShift θ h u 0 n = ∫ x in ((n : ℕ) : ℝ)..((n + 1 : ℕ) : ℝ), h (x / u) := fun n _ => by
    unfold emIntTermShift
    simp only [pow_zero, one_mul, bernoulliFun_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      Complex.ofReal_one, iteratedDeriv_zero]
    have hc : Continuous (fun t : ℝ => h (((n : ℝ) + t) / u)) :=
      (eds_continuous hh).comp ((continuous_const.add continuous_id).div_const u)
    rw [intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 θ)
      (hc.intervalIntegrable θ 1)]
    have hcomp := intervalIntegral.integral_comp_add_left (fun x : ℝ => h (x / u)) (n : ℝ)
      (a := (0 : ℝ)) (b := 1)
    simpa [add_zero, Nat.cast_add, Nat.cast_one] using hcomp
  rw [Finset.sum_congr rfl heach]
  have hadj := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun x : ℝ => h (x / u)) (a := fun k : ℕ => (k : ℝ)) (n := N) fun k _ =>
      ((eds_continuous hh).comp (continuous_id.div_const u)).intervalIntegrable _ _
  simp only [Nat.cast_zero] at hadj
  rw [hadj]
  have hdiv := intervalIntegral.integral_comp_div h hu.ne' (a := (0 : ℝ)) (b := (N : ℝ))
  rw [zero_div] at hdiv
  rw [hdiv, Complex.real_smul]

private lemma emIntTermShift_ibp_zero {θ : ℝ} {h : ℝ → ℂ} (hh : ExpDecaySmooth h)
    {u : ℝ} (n : ℕ) :
    h (((n : ℝ) + θ) / u) =
      emIntTermShift θ h u 0 n -
        ((bernoulliFun 1 (1 - θ) : ℝ) : ℂ) * (h (((n + 1 : ℕ) : ℝ) / u) - h ((n : ℝ) / u)) +
        emIntTermShift θ h u 1 n := by
  have hpiece : ∀ (c a b : ℝ),
      ((bernoulliFun 1 (b + c) : ℝ) : ℂ) * h (((n : ℝ) + b) / u) -
        ((bernoulliFun 1 (a + c) : ℝ) : ℂ) * h (((n : ℝ) + a) / u) =
      (∫ t in a..b, h (((n : ℝ) + t) / u)) +
        (u : ℂ)⁻¹ * ∫ t in a..b, ((bernoulliFun 1 (t + c) : ℝ) : ℂ) *
          deriv h (((n : ℝ) + t) / u) := fun c a b => by
    let F : ℝ → ℂ := fun t => ((bernoulliFun 1 (t + c) : ℝ) : ℂ) * h (((n : ℝ) + t) / u)
    let F' : ℝ → ℂ := fun t => h (((n : ℝ) + t) / u) +
      ((bernoulliFun 1 (t + c) : ℝ) : ℂ) * ((u : ℂ)⁻¹ * deriv h (((n : ℝ) + t) / u))
    have hderiv : ∀ t ∈ [[a, b]], HasDerivAt F (F' t) t := fun t _ => by
      have hb : HasDerivAt (fun s : ℝ => ((bernoulliFun 1 (s + c) : ℝ) : ℂ)) (1 : ℂ) t := by
        have h1 := ((antideriv_bernoulliFun 0 (t + c)).comp t ((hasDerivAt_id t).add_const c)).ofReal_comp
        simpa using h1
      have hg : HasDerivAt (fun s : ℝ => h (((n : ℝ) + s) / u))
          ((u : ℂ)⁻¹ * deriv h (((n : ℝ) + t) / u)) t := by
        have harg : HasDerivAt (fun s : ℝ => ((n : ℝ) + s) / u) (1 / u) t := by
          simpa using (((hasDerivAt_id t).const_add (n : ℝ)).div_const u)
        have hh' := (eds_differentiable hh (((n : ℝ) + t) / u)).hasDerivAt.scomp t harg
        refine hh'.congr_deriv ?_
        rw [Complex.real_smul]; push_cast; rw [one_div, mul_comm]
      exact (hb.mul hg).congr_deriv (by dsimp [F']; ring)
    have hi1 : IntervalIntegrable (fun t : ℝ => h (((n : ℝ) + t) / u)) volume a b :=
      ((eds_continuous hh).comp ((continuous_const.add continuous_id).div_const u)).intervalIntegrable a b
    have hi2 : IntervalIntegrable (fun t : ℝ =>
        ((bernoulliFun 1 (t + c) : ℝ) : ℂ) * ((u : ℂ)⁻¹ * deriv h (((n : ℝ) + t) / u))) volume a b :=
      ((Complex.continuous_ofReal.comp ((continuous_bernoulliFun 1).comp (continuous_id.add continuous_const))).mul
        (continuous_const.mul ((eds_continuous (eds_deriv hh)).comp
          ((continuous_const.add continuous_id).div_const u)))).intervalIntegrable a b
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hi1.add hi2)
    rw [intervalIntegral.integral_add hi1 hi2] at hftc
    have hpull : (∫ t in a..b, ((bernoulliFun 1 (t + c) : ℝ) : ℂ) * ((u : ℂ)⁻¹ * deriv h (((n : ℝ) + t) / u))) =
        (u : ℂ)⁻¹ * ∫ t in a..b, ((bernoulliFun 1 (t + c) : ℝ) : ℂ) * deriv h (((n : ℝ) + t) / u) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun t _ => by ring
    rw [hpull] at hftc
    exact hftc.symm
  have h1 := hpiece (1 - θ) 0 θ
  have h2 := hpiece (-θ) θ 1
  have hb1 : bernoulliFun 1 (θ + (1 - θ)) = 1 / 2 := by
    rw [show θ + (1 - θ) = 1 by ring, bernoulliFun_one]; norm_num
  have hb0 : bernoulliFun 1 (θ + -θ) = -(1 / 2) := by
    rw [show θ + -θ = 0 by ring, bernoulliFun_one]; norm_num
  have hadd1 : (0 : ℝ) + (1 - θ) = 1 - θ := by ring
  have hadd2 : (1 : ℝ) + -θ = 1 - θ := by ring
  have hsub1 : ∀ t : ℝ, t + (1 - θ) = t + 1 - θ := fun t => by ring
  have hsub2 : ∀ t : ℝ, t + -θ = t - θ := fun t => by ring
  rw [hb1, hadd1] at h1
  rw [hb0, hadd2] at h2
  simp_rw [hsub1] at h1
  simp_rw [hsub2] at h2
  have hI0 : emIntTermShift θ h u 0 n =
      (∫ t in (0 : ℝ)..θ, h (((n : ℝ) + t) / u)) + (∫ t in θ..1, h (((n : ℝ) + t) / u)) := by
    unfold emIntTermShift; simp
  have hI1 : emIntTermShift θ h u 1 n =
      (u : ℂ)⁻¹ * (∫ t in (0 : ℝ)..θ, ((bernoulliFun 1 (t + 1 - θ) : ℝ) : ℂ) * deriv h (((n : ℝ) + t) / u)) +
      (u : ℂ)⁻¹ * (∫ t in θ..1, ((bernoulliFun 1 (t - θ) : ℝ) : ℂ) * deriv h (((n : ℝ) + t) / u)) := by
    unfold emIntTermShift
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one, iteratedDeriv_one]
    ring
  have hn1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hI0, hI1, hn1]
  have h00 : ((n : ℝ) + 0) / u = (n : ℝ) / u := by ring
  rw [h00] at h1
  push_cast at h1 h2
  linear_combination h1 + h2

private lemma emIntTermShift_ibp_succ {θ : ℝ} {h : ℝ → ℂ} (hh : ExpDecaySmooth h)
    {u : ℝ} (r n : ℕ) :
    emIntTermShift θ h u (r + 1) n =
      (u : ℂ)⁻¹ ^ (r + 1) * (((bernoulliFun (r + 2) (1 - θ) : ℝ) : ℂ) / ((r + 2).factorial : ℂ)) *
        (iteratedDeriv (r + 1) h (((n + 1 : ℕ) : ℝ) / u) - iteratedDeriv (r + 1) h ((n : ℝ) / u)) -
      emIntTermShift θ h u (r + 2) n := by
  have hpiece : ∀ (c a b : ℝ),
      ((bernoulliFun (r + 2) (b + c) / ((r + 2).factorial : ℝ) : ℝ) : ℂ) *
          iteratedDeriv (r + 1) h (((n : ℝ) + b) / u) -
        ((bernoulliFun (r + 2) (a + c) / ((r + 2).factorial : ℝ) : ℝ) : ℂ) *
          iteratedDeriv (r + 1) h (((n : ℝ) + a) / u) =
      (∫ t in a..b, ((bernoulliFun (r + 1) (t + c) / ((r + 1).factorial : ℝ) : ℝ) : ℂ) *
          iteratedDeriv (r + 1) h (((n : ℝ) + t) / u)) +
        (u : ℂ)⁻¹ * ∫ t in a..b,
          ((bernoulliFun (r + 2) (t + c) / ((r + 2).factorial : ℝ) : ℝ) : ℂ) *
            iteratedDeriv (r + 2) h (((n : ℝ) + t) / u) := fun c a b => by
    let F : ℝ → ℂ := fun t =>
      ((bernoulliFun (r + 2) (t + c) / ((r + 2).factorial : ℝ) : ℝ) : ℂ) *
        iteratedDeriv (r + 1) h (((n : ℝ) + t) / u)
    let F' : ℝ → ℂ := fun t =>
      ((bernoulliFun (r + 1) (t + c) / ((r + 1).factorial : ℝ) : ℝ) : ℂ) *
        iteratedDeriv (r + 1) h (((n : ℝ) + t) / u) +
      ((bernoulliFun (r + 2) (t + c) / ((r + 2).factorial : ℝ) : ℝ) : ℂ) *
        ((u : ℂ)⁻¹ * iteratedDeriv (r + 2) h (((n : ℝ) + t) / u))
    have hderiv : ∀ t ∈ [[a, b]], HasDerivAt F (F' t) t := fun t _ => by
      have hbR : HasDerivAt (fun s : ℝ => bernoulliFun (r + 2) (s + c) / ((r + 2).factorial : ℝ))
          (bernoulliFun (r + 1) (t + c) / ((r + 1).factorial : ℝ)) t := by
        have h1 := (((hasDerivAt_bernoulliFun (r + 2) (t + c)).comp t
          ((hasDerivAt_id t).add_const c)).div_const ((r + 2).factorial : ℝ))
        refine h1.congr_deriv ?_
        rw [show r + 2 - 1 = r + 1 by omega, Nat.factorial_succ (r + 1)]
        push_cast
        have hr2 : ((r : ℝ) + 1 + 1) ≠ 0 := by positivity
        have hfac : ((r + 1).factorial : ℝ) ≠ 0 := by positivity
        field_simp [hr2, hfac]
        ring
      have hg : HasDerivAt (fun s : ℝ => iteratedDeriv (r + 1) h (((n : ℝ) + s) / u))
          ((u : ℂ)⁻¹ * iteratedDeriv (r + 2) h (((n : ℝ) + t) / u)) t := by
        have harg : HasDerivAt (fun s : ℝ => ((n : ℝ) + s) / u) (1 / u) t := by
          simpa using (((hasDerivAt_id t).const_add (n : ℝ)).div_const u)
        have hh' := (eds_differentiable (eds_iteratedDeriv_smooth hh (r + 1))
          (((n : ℝ) + t) / u)).hasDerivAt.scomp t harg
        refine hh'.congr_deriv ?_
        rw [Complex.real_smul, ← iteratedDeriv_succ]; push_cast; rw [one_div, mul_comm]
      exact (hbR.ofReal_comp.mul hg).congr_deriv (by dsimp [F'])
    have hi1 : IntervalIntegrable (fun t : ℝ =>
        ((bernoulliFun (r + 1) (t + c) / ((r + 1).factorial : ℝ) : ℝ) : ℂ) *
          iteratedDeriv (r + 1) h (((n : ℝ) + t) / u)) volume a b :=
      ((Complex.continuous_ofReal.comp
        (((continuous_bernoulliFun (r + 1)).comp (continuous_id.add continuous_const)).div_const _)).mul
        ((eds_continuous (eds_iteratedDeriv_smooth hh (r + 1))).comp
          ((continuous_const.add continuous_id).div_const u))).intervalIntegrable a b
    have hi2 : IntervalIntegrable (fun t : ℝ =>
        ((bernoulliFun (r + 2) (t + c) / ((r + 2).factorial : ℝ) : ℝ) : ℂ) *
          ((u : ℂ)⁻¹ * iteratedDeriv (r + 2) h (((n : ℝ) + t) / u))) volume a b :=
      ((Complex.continuous_ofReal.comp
        (((continuous_bernoulliFun (r + 2)).comp (continuous_id.add continuous_const)).div_const _)).mul
        (continuous_const.mul ((eds_continuous (eds_iteratedDeriv_smooth hh (r + 2))).comp
          ((continuous_const.add continuous_id).div_const u)))).intervalIntegrable a b
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hi1.add hi2)
    rw [intervalIntegral.integral_add hi1 hi2] at hftc
    have hpull : (∫ t in a..b, ((bernoulliFun (r + 2) (t + c) / ((r + 2).factorial : ℝ) : ℝ) : ℂ) *
          ((u : ℂ)⁻¹ * iteratedDeriv (r + 2) h (((n : ℝ) + t) / u))) =
        (u : ℂ)⁻¹ * ∫ t in a..b, ((bernoulliFun (r + 2) (t + c) / ((r + 2).factorial : ℝ) : ℝ) : ℂ) *
          iteratedDeriv (r + 2) h (((n : ℝ) + t) / u) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun t _ => by ring
    rw [hpull] at hftc
    exact hftc.symm
  have h1 := hpiece (1 - θ) 0 θ
  have h2 := hpiece (-θ) θ 1
  have hend : bernoulliFun (r + 2) (θ + (1 - θ)) = bernoulliFun (r + 2) (θ + -θ) := by
    rw [show θ + (1 - θ) = 1 by ring, show θ + -θ = 0 by ring]
    exact bernoulliFun_endpoints_eq_of_ne_one (by omega)
  rw [hend, show (0 : ℝ) + (1 - θ) = 1 - θ by ring, show ((n : ℝ) + 0) / u = (n : ℝ) / u by ring] at h1
  rw [show (1 : ℝ) + -θ = 1 - θ by ring] at h2
  have hsub1 : ∀ t : ℝ, t + (1 - θ) = t + 1 - θ := fun t => by ring
  have hsub2 : ∀ t : ℝ, t + -θ = t - θ := fun t => by ring
  simp_rw [hsub1] at h1
  simp_rw [hsub2] at h2
  have hsum := congrArg (fun z : ℂ => (u : ℂ)⁻¹ ^ (r + 1) * z) (congrArg₂ (· + ·) h1 h2)
  have hn1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hI1 : emIntTermShift θ h u (r + 1) n =
      (u : ℂ)⁻¹ ^ (r + 1) *
        ((∫ t in (0 : ℝ)..θ, ((bernoulliFun (r + 1) (t + 1 - θ) / ((r + 1).factorial : ℝ) : ℝ) : ℂ) *
            iteratedDeriv (r + 1) h (((n : ℝ) + t) / u)) +
         (∫ t in θ..1, ((bernoulliFun (r + 1) (t - θ) / ((r + 1).factorial : ℝ) : ℝ) : ℂ) *
            iteratedDeriv (r + 1) h (((n : ℝ) + t) / u))) := rfl
  have hI2 : emIntTermShift θ h u (r + 2) n =
      (u : ℂ)⁻¹ ^ (r + 1) * ((u : ℂ)⁻¹ *
        ((∫ t in (0 : ℝ)..θ, ((bernoulliFun (r + 2) (t + 1 - θ) / ((r + 2).factorial : ℝ) : ℝ) : ℂ) *
            iteratedDeriv (r + 2) h (((n : ℝ) + t) / u)) +
         (∫ t in θ..1, ((bernoulliFun (r + 2) (t - θ) / ((r + 2).factorial : ℝ) : ℝ) : ℂ) *
            iteratedDeriv (r + 2) h (((n : ℝ) + t) / u)))) := by
    unfold emIntTermShift; rw [pow_succ]; ring
  rw [hI1, hI2, hn1]
  push_cast at hsum ⊢
  linear_combination -hsum

private lemma euler_maclaurin_shift_finite {θ : ℝ} {h : ℝ → ℂ} (hh : ExpDecaySmooth h)
    {u : ℝ} (hu : 0 < u) (N K : ℕ) :
    ∑ n ∈ Finset.range N, h (((n : ℝ) + θ) / u) =
      (u : ℂ) * (∫ y in (0 : ℝ)..((N : ℝ) / u), h y) +
        (∑ k ∈ Finset.range (K + 1),
          (-1 : ℂ) ^ (k + 1) * (((bernoulliFun (k + 1) (1 - θ) : ℝ) : ℂ) / ((k + 1).factorial : ℂ)) *
            (u : ℂ)⁻¹ ^ k * (iteratedDeriv k h ((N : ℝ) / u) - iteratedDeriv k h 0)) +
        (-1 : ℂ) ^ K * ∑ n ∈ Finset.range N, emIntTermShift θ h u (K + 1) n := by
  induction K with
  | zero =>
    simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, pow_one, Nat.factorial_one,
      Nat.cast_one, div_one, pow_zero, mul_one, iteratedDeriv_zero, one_mul]
    have hsum : ∑ n ∈ Finset.range N, h (((n : ℝ) + θ) / u) =
        (∑ n ∈ Finset.range N, emIntTermShift θ h u 0 n) -
        ((bernoulliFun 1 (1 - θ) : ℝ) : ℂ) *
          (∑ n ∈ Finset.range N, (h (((n + 1 : ℕ) : ℝ) / u) - h ((n : ℝ) / u))) +
        (∑ n ∈ Finset.range N, emIntTermShift θ h u 1 n) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => emIntTermShift_ibp_zero hh n
    have htele : ∑ n ∈ Finset.range N, (h (((n + 1 : ℕ) : ℝ) / u) - h ((n : ℝ) / u)) =
        h ((N : ℝ) / u) - h 0 := by
      have hsub := Finset.sum_range_sub (fun n : ℕ => h ((n : ℝ) / u)) N
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div] at hsub ⊢
      exact hsub
    rw [hsum, sum_emIntTermShift_zero hh hu N, htele]
    ring
  | succ K ih =>
    have hsplit : ∑ n ∈ Finset.range N, emIntTermShift θ h u (K + 1) n =
        (u : ℂ)⁻¹ ^ (K + 1) *
          (((bernoulliFun (K + 2) (1 - θ) : ℝ) : ℂ) / ((K + 2).factorial : ℂ)) *
          (iteratedDeriv (K + 1) h ((N : ℝ) / u) - iteratedDeriv (K + 1) h 0) -
        ∑ n ∈ Finset.range N, emIntTermShift θ h u (K + 2) n := by
      have hterm : ∑ n ∈ Finset.range N, emIntTermShift θ h u (K + 1) n =
          ∑ n ∈ Finset.range N,
            ((u : ℂ)⁻¹ ^ (K + 1) * (((bernoulliFun (K + 2) (1 - θ) : ℝ) : ℂ) / ((K + 2).factorial : ℂ)) *
              (iteratedDeriv (K + 1) h (((n + 1 : ℕ) : ℝ) / u) - iteratedDeriv (K + 1) h ((n : ℝ) / u)) -
            emIntTermShift θ h u (K + 2) n) :=
        Finset.sum_congr rfl fun n _ => emIntTermShift_ibp_succ hh K n
      rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
      have hsub := Finset.sum_range_sub (fun n : ℕ => iteratedDeriv (K + 1) h ((n : ℝ) / u)) N
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div] at hsub ⊢
      rw [hsub]
    rw [ih, hsplit]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [show K + 1 + 1 = K + 2 by omega, pow_succ (-1 : ℂ) (K + 1), pow_succ (-1 : ℂ) K]
    ring

private lemma euler_maclaurin_shift_tsum {q : ℚ} (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) ≤ 1)
    {h : ℝ → ℂ} (hh : ExpDecaySmooth h) {u : ℝ} (hu : 0 < u) (K : ℕ) :
    sumScaleShift (q : ℝ) h u =
      (u : ℂ) * (∫ y in Ioi (0 : ℝ), h y) +
        ∑ r ∈ Finset.range (K + 1), emTermShift (q : ℝ) h r * (u : ℂ)⁻¹ ^ r +
        (-1 : ℂ) ^ K * ∑' n : ℕ, emIntTermShift (q : ℝ) h u (K + 1) n := by
  let θ : ℝ := (q : ℝ)
  have hL : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, h (((n : ℝ) + θ) / u))
      atTop (𝓝 (sumScaleShift θ h u)) :=
    (summable_sumScaleShift hq0 hh hu).hasSum.tendsto_sum_nat
  have hDiv : Tendsto (fun N : ℕ => (N : ℝ) / u) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hu
  have hInt : Tendsto (fun N : ℕ => (u : ℂ) * (∫ y in (0 : ℝ)..((N : ℝ) / u), h y))
      atTop (𝓝 ((u : ℂ) * (∫ y in Ioi (0 : ℝ), h y))) :=
    tendsto_const_nhds.mul (intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
      (by simpa using eds_integrableOn hh 0) hDiv)
  have hSumK : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (K + 1),
        (-1 : ℂ) ^ (k + 1) * (((bernoulliFun (k + 1) (1 - θ) : ℝ) : ℂ) / ((k + 1).factorial : ℂ)) *
          (u : ℂ)⁻¹ ^ k * (iteratedDeriv k h ((N : ℝ) / u) - iteratedDeriv k h 0))
      atTop (𝓝 (∑ k ∈ Finset.range (K + 1), emTermShift θ h k * (u : ℂ)⁻¹ ^ k)) := by
    refine tendsto_finsetSum _ fun k _ => ?_
    have hl := (eds_tendsto_atTop hh k).comp hDiv
    have heq : (-1 : ℂ) ^ (k + 1) * (((bernoulliFun (k + 1) (1 - θ) : ℝ) : ℂ) / ((k + 1).factorial : ℂ)) *
          (u : ℂ)⁻¹ ^ k * ((0 : ℂ) - iteratedDeriv k h 0) = emTermShift θ h k * (u : ℂ)⁻¹ ^ k := by
      dsimp only [emTermShift, θ]
      rw [bernoulliFun_one_sub_rat (k + 1) q]
      push_cast
      have hsq : (-1 : ℂ) ^ (k + 1) * (-1 : ℂ) ^ (k + 1) = 1 := by rw [← mul_pow]; norm_num
      linear_combination -(((bernoulliFun (k + 1) (q : ℝ) : ℝ) : ℂ) / ((k + 1).factorial : ℂ) *
        iteratedDeriv k h 0 * (u : ℂ)⁻¹ ^ k) * hsq
    rw [← heq]
    exact tendsto_const_nhds.mul (hl.sub tendsto_const_nhds)
  have hRem : Tendsto (fun N : ℕ => (-1 : ℂ) ^ K * ∑ n ∈ Finset.range N, emIntTermShift θ h u (K + 1) n)
      atTop (𝓝 ((-1 : ℂ) ^ K * ∑' n : ℕ, emIntTermShift θ h u (K + 1) n)) :=
    tendsto_const_nhds.mul (summable_emIntTermShift hq0.le hq1 hh (K + 1) hu).hasSum.tendsto_sum_nat
  have hR : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, h (((n : ℝ) + θ) / u)) atTop
      (𝓝 ((u : ℂ) * (∫ y in Ioi (0 : ℝ), h y) +
        ∑ r ∈ Finset.range (K + 1), emTermShift θ h r * (u : ℂ)⁻¹ ^ r +
        (-1 : ℂ) ^ K * ∑' n : ℕ, emIntTermShift θ h u (K + 1) n)) := by
    refine ((hInt.add hSumK).add hRem).congr fun N => ?_
    exact (euler_maclaurin_shift_finite hh hu N K).symm
  exact tendsto_nhds_unique hL hR

theorem sumScaleShift_hasAsympExp {q : ℚ} (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) ≤ 1)
    {h : ℝ → ℂ} (hh : ExpDecaySmooth h) :
    HasAsympExp (fun u : ℝ => sumScaleShift (q : ℝ) h u - (u : ℂ) * (∫ y in Ioi (0 : ℝ), h y))
      (emSeriesShift (q : ℝ) h) := by
  intro M
  obtain ⟨Cm, cm, Bm, hCm, hcm, hBm, hbd⟩ := emIntTermShift_norm_le hq0.le hq1 hh (M + 1)
  let C_rem : ℝ := Cm * Bm * ((1 + cm) / cm)
  refine ⟨C_rem + ‖emTermShift (q : ℝ) h M‖, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
  have hu_pos : 0 < u := by linarith
  have hEM := euler_maclaurin_shift_tsum hq0 hq1 hh hu_pos M
  have hsplit_sum : (∑ r ∈ Finset.range (M + 1), emTermShift (q : ℝ) h r * (u : ℂ)⁻¹ ^ r) =
      (∑ r ∈ Finset.range M, PowerSeries.coeff r (emSeriesShift (q : ℝ) h) * (u : ℂ)⁻¹ ^ r) +
        emTermShift (q : ℝ) h M * (u : ℂ)⁻¹ ^ M := by
    rw [Finset.sum_range_succ]; congr 1
    exact Finset.sum_congr rfl fun r _ => by simp [emSeriesShift]
  have h_id : (sumScaleShift (q : ℝ) h u - (u : ℂ) * (∫ y in Ioi (0 : ℝ), h y)) -
        ∑ r ∈ Finset.range M, PowerSeries.coeff r (emSeriesShift (q : ℝ) h) * (u : ℂ)⁻¹ ^ r =
      emTermShift (q : ℝ) h M * (u : ℂ)⁻¹ ^ M +
        (-1 : ℂ) ^ M * ∑' n : ℕ, emIntTermShift (q : ℝ) h u (M + 1) n := by
    rw [hEM, hsplit_sum]; ring
  have hnorm_m : ‖emTermShift (q : ℝ) h M * (u : ℂ)⁻¹ ^ M‖ = ‖emTermShift (q : ℝ) h M‖ / u ^ M := by
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos,
      _root_.inv_pow, div_eq_mul_inv]
  have hlt : Real.exp (-cm / u) < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith) hu_pos)
  have hdom : Summable (fun n : ℕ => (u⁻¹ ^ (M + 1) * (Cm * Bm)) * (Real.exp (-cm / u)) ^ n) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hlt).mul_left _
  have hsn : Summable (fun n : ℕ => ‖emIntTermShift (q : ℝ) h u (M + 1) n‖) :=
    (summable_emIntTermShift hq0.le hq1 hh (M + 1) hu_pos).norm
  have hgeom_bound : (1 - Real.exp (-cm / u))⁻¹ ≤ u * ((1 + cm) / cm) := by
    have h1 : 1 - Real.exp (-cm / u) ≥ (cm / u) / (1 + cm / u) := by
      have hexp : 1 + cm / u ≤ Real.exp (cm / u) := by linarith [Real.add_one_le_exp (cm / u)]
      have hpos1 : 0 < 1 + cm / u := by positivity
      have hinv : Real.exp (-cm / u) ≤ (1 + cm / u)⁻¹ := by
        rw [show -cm / u = -(cm / u) by ring, Real.exp_neg]
        exact inv_anti₀ hpos1 hexp
      have hdiff : (cm / u) / (1 + cm / u) = 1 - (1 + cm / u)⁻¹ := by field_simp [hpos1.ne']; ring
      linarith
    have hpos_lhs : 0 < (cm / u) / (1 + cm / u) := by positivity
    have hinv2 := inv_anti₀ hpos_lhs h1
    refine hinv2.trans ?_
    have hEq : ((cm / u) / (1 + cm / u))⁻¹ = u * ((1 + cm / u) / cm) := by
      field_simp [hu_pos.ne', hcm.ne']
    rw [hEq]
    have hdiv_le : cm / u ≤ cm := div_le_self hcm.le hu
    gcongr
  have h_tsum_bd : ‖∑' n : ℕ, emIntTermShift (q : ℝ) h u (M + 1) n‖ ≤ C_rem / u ^ M := by
    calc ‖∑' n : ℕ, emIntTermShift (q : ℝ) h u (M + 1) n‖
        ≤ ∑' n : ℕ, ‖emIntTermShift (q : ℝ) h u (M + 1) n‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' n : ℕ, (u⁻¹ ^ (M + 1) * (Cm * Bm)) * (Real.exp (-cm / u)) ^ n :=
          hsn.tsum_le_tsum (fun n => hbd hu_pos n) hdom
      _ = u⁻¹ ^ (M + 1) * (Cm * Bm) * (1 - Real.exp (-cm / u))⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hlt]
      _ ≤ u⁻¹ ^ (M + 1) * (Cm * Bm) * (u * ((1 + cm) / cm)) := by
          gcongr
      _ = C_rem / u ^ M := by
          dsimp only [C_rem]; rw [pow_succ, _root_.inv_pow]; field_simp [hu_pos.ne']
  rw [h_id]
  calc ‖emTermShift (q : ℝ) h M * (u : ℂ)⁻¹ ^ M +
        (-1 : ℂ) ^ M * ∑' n : ℕ, emIntTermShift (q : ℝ) h u (M + 1) n‖
      ≤ ‖emTermShift (q : ℝ) h M * (u : ℂ)⁻¹ ^ M‖ +
        ‖(-1 : ℂ) ^ M * ∑' n : ℕ, emIntTermShift (q : ℝ) h u (M + 1) n‖ := norm_add_le _ _
    _ = ‖emTermShift (q : ℝ) h M‖ / u ^ M + ‖∑' n : ℕ, emIntTermShift (q : ℝ) h u (M + 1) n‖ := by
        rw [hnorm_m, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    _ ≤ ‖emTermShift (q : ℝ) h M‖ / u ^ M + C_rem / u ^ M := add_le_add le_rfl h_tsum_bd
    _ = (C_rem + ‖emTermShift (q : ℝ) h M‖) / u ^ M := by ring

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

private lemma sumScaleShift_hasDerivAt {θ : ℝ} (hθ0 : 0 < θ) {H : ℝ → ℂ} (hH : ExpDecaySmooth H)
    (j : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => (v : ℂ)⁻¹ ^ j * sumScaleShift θ H v)
      ((u : ℂ)⁻¹ ^ (j + 1) * sumScaleShift θ (emStep j H) u) u := by
  let t : Set ℝ := Metric.ball u (u / 2)
  have ht_open : IsOpen t := Metric.isOpen_ball
  have ht_conn : IsPreconnected t := (convex_ball u (u / 2)).isPreconnected
  have hu_mem : u ∈ t := Metric.mem_ball_self (by positivity)
  let g : ℕ → ℝ → ℂ := fun n v => (v : ℂ)⁻¹ ^ j * H (((n : ℝ) + θ) / v)
  let g' : ℕ → ℝ → ℂ := fun n v => (v : ℂ)⁻¹ ^ (j + 1) * emStep j H (((n : ℝ) + θ) / v)
  have hK : ExpDecaySmooth (emStep j H) := eds_emStep j hH
  obtain ⟨CK, cK, hCK, hcK, hbdK⟩ := hK.2 0
  let qK : ℝ := Real.exp (-cK / (3 * u / 2))
  have hqK_lt : qK < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith) (by positivity))
  let w : ℕ → ℝ := fun n => ((u / 2)⁻¹ ^ (j + 1) * CK) * qK ^ n
  have hw_summ : Summable w := (summable_geometric_of_lt_one (Real.exp_pos _).le hqK_lt).mul_left _
  have hg_deriv : ∀ (n : ℕ) (y : ℝ), y ∈ t → HasDerivAt (g n) (g' n y) y := fun n y hy => by
    have hy_dist : |y - u| < u / 2 := by simpa [t, Metric.mem_ball, Real.dist_eq] using hy
    have hy_pos : 0 < y := by linarith [(abs_lt.mp hy_dist).1]
    have h1 := hasDerivAt_inv_pow_complex' (j := j) hy_pos.ne'
    have h2 : HasDerivAt (fun v : ℝ => H (((n : ℝ) + θ) / v))
        (deriv H (((n : ℝ) + θ) / y) * (-((((n : ℝ) + θ) / y ^ 2 : ℝ) : ℂ))) y := by
      have harg : HasDerivAt (fun v : ℝ => ((n : ℝ) + θ) / v) (-(((n : ℝ) + θ) / y ^ 2)) y := by
        refine ((hasDerivAt_inv hy_pos.ne').const_mul ((n : ℝ) + θ)).congr_deriv ?_; ring
      have hH' := (eds_differentiable hH (((n : ℝ) + θ) / y)).hasDerivAt.scomp y harg
      refine hH'.congr_deriv ?_; rw [Complex.real_smul]; push_cast; ring
    refine (h1.mul h2).congr_deriv ?_
    dsimp only [g', emStep]
    have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy_pos.ne'
    rw [pow_succ]; push_cast; field_simp [hyc]; ring
  have hg_bound : ∀ (n : ℕ) (y : ℝ), y ∈ t → ‖g' n y‖ ≤ w n := fun n y hy => by
    have hy_dist : |y - u| < u / 2 := by simpa [t, Metric.mem_ball, Real.dist_eq] using hy
    have hy_lo : u / 2 < y := by linarith [(abs_lt.mp hy_dist).1]
    have hy_hi : y < 3 * u / 2 := by linarith [(abs_lt.mp hy_dist).2]
    have hy_pos : 0 < y := by linarith
    dsimp only [g', w]
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy_pos]
    have hinv_le : y⁻¹ ^ (j + 1) ≤ (u / 2)⁻¹ ^ (j + 1) :=
      pow_le_pow_left₀ (by positivity) (inv_anti₀ (by positivity) hy_lo.le) _
    have hK_bd : ‖emStep j H (((n : ℝ) + θ) / y)‖ ≤ CK * Real.exp (-cK * (((n : ℝ) + θ) / y)) := by
      simpa [iteratedDeriv_zero] using hbdK (((n : ℝ) + θ) / y) (by positivity)
    have hexp_le : Real.exp (-cK * (((n : ℝ) + θ) / y)) ≤ qK ^ n := by
      dsimp only [qK]; rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hdiv : (n : ℝ) / (3 * u / 2) ≤ ((n : ℝ) + θ) / y := by
        calc (n : ℝ) / (3 * u / 2) ≤ ((n : ℝ) + θ) / (3 * u / 2) :=
              div_le_div_of_nonneg_right (by linarith) (by positivity)
          _ ≤ ((n : ℝ) + θ) / y := div_le_div_of_nonneg_left (by positivity) hy_pos hy_hi.le
      calc -cK * (((n : ℝ) + θ) / y) ≤ -cK * ((n : ℝ) / (3 * u / 2)) :=
            mul_le_mul_of_nonpos_left hdiv (by linarith)
        _ = (n : ℝ) * (-cK / (3 * u / 2)) := by ring
    calc y⁻¹ ^ (j + 1) * ‖emStep j H (((n : ℝ) + θ) / y)‖
        ≤ (u / 2)⁻¹ ^ (j + 1) * (CK * Real.exp (-cK * (((n : ℝ) + θ) / y))) :=
          mul_le_mul hinv_le hK_bd (norm_nonneg _) (by positivity)
      _ ≤ (u / 2)⁻¹ ^ (j + 1) * (CK * qK ^ n) := by gcongr
      _ = ((u / 2)⁻¹ ^ (j + 1) * CK) * qK ^ n := by ring
  have hg0 : Summable (fun n : ℕ => g n u) :=
    (summable_sumScaleShift hθ0 hH hu).mul_left ((u : ℂ)⁻¹ ^ j)
  have htsum := hasDerivAt_tsum_of_isPreconnected hw_summ ht_open ht_conn hg_deriv hg_bound hu_mem hg0 hu_mem
  have heq_fn : (fun v : ℝ => ∑' n : ℕ, g n v) = fun v : ℝ => (v : ℂ)⁻¹ ^ j * sumScaleShift θ H v := by
    funext v; dsimp only [g, sumScaleShift]; exact tsum_mul_left
  have heq_deriv : ∑' n : ℕ, g' n u = (u : ℂ)⁻¹ ^ (j + 1) * sumScaleShift θ (emStep j H) u := by
    dsimp only [g', sumScaleShift]; exact tsum_mul_left
  rw [heq_fn, heq_deriv] at htsum
  exact htsum

private lemma sumScaleShift_pow_contDiffOn {θ : ℝ} (hθ0 : 0 < θ) (n : ℕ) :
    ∀ {h : ℝ → ℂ} (_hh : ExpDecaySmooth h) (k : ℕ),
      ContDiffOn ℝ n (fun u : ℝ => (u : ℂ)⁻¹ ^ k * sumScaleShift θ h u) (Ioi (0 : ℝ)) := by
  induction n with
  | zero =>
    intro h hh k
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun u hu => ((sumScaleShift_hasDerivAt hθ0 hh k hu).continuousAt).continuousWithinAt
  | succ n ih =>
    intro h hh k
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun u hu => ((sumScaleShift_hasDerivAt hθ0 hh k hu).differentiableAt).differentiableWithinAt,
      by simp, ?_⟩
    have hderiv_eq : EqOn (deriv (fun u : ℝ => (u : ℂ)⁻¹ ^ k * sumScaleShift θ h u))
        (fun u : ℝ => (u : ℂ)⁻¹ ^ (k + 1) * sumScaleShift θ (emStep k h) u) (Ioi (0 : ℝ)) :=
      fun u hu => (sumScaleShift_hasDerivAt hθ0 hh k hu).deriv
    exact (ih (eds_emStep k hh) (k + 1)).congr hderiv_eq

private lemma sumScaleShift_contDiffOn {θ : ℝ} (hθ0 : 0 < θ) {h : ℝ → ℂ} (hh : ExpDecaySmooth h)
    (n : ℕ) : ContDiffOn ℝ n (sumScaleShift θ h) (Ioi (0 : ℝ)) := by
  simpa using sumScaleShift_pow_contDiffOn hθ0 n hh 0

/-- Integration by parts: `∫_{0}^∞ (emStep a H) = (1 - a) * ∫_{0}^∞ H`. -/
private lemma integral_Ioi_emStep {H : ℝ → ℂ} (hH : ExpDecaySmooth H) (a : ℕ) :
    ∫ y in Ioi (0 : ℝ), emStep a H y = (1 - (a : ℂ)) * ∫ y in Ioi (0 : ℝ), H y := by
  have hint_H : IntegrableOn H (Ioi (0 : ℝ)) := by simpa [iteratedDeriv_zero] using eds_integrableOn hH 0
  have hint_uv' : IntegrableOn (fun y : ℝ => (y : ℂ) * deriv H y) (Ioi (0 : ℝ)) := by
    simpa [iteratedDeriv_zero] using eds_integrableOn (eds_mul_ofReal (eds_deriv hH)) 0
  have hint_u'v : IntegrableOn (fun y : ℝ => (1 : ℂ) * H y) (Ioi (0 : ℝ)) := by simpa using hint_H
  have hzero : Tendsto (fun y : ℝ => (y : ℂ) * H y) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun y : ℝ => (y : ℂ) * H y) 0 :=
      (Complex.continuous_ofReal.mul (eds_continuous hH)).continuousAt
    simpa using hcont.continuousWithinAt.tendsto
  have htop : Tendsto (fun y : ℝ => (y : ℂ) * H y) atTop (𝓝 0) := by
    simpa [iteratedDeriv_zero] using eds_tendsto_atTop (eds_mul_ofReal hH) 0
  have hibp := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun y : ℝ => (y : ℂ)) (v := H) (u' := fun _ => (1 : ℂ)) (v' := deriv H)
    (fun x _ => (hasDerivAt_id x).ofReal_comp)
    (fun x _ => (eds_differentiable hH x).hasDerivAt)
    hint_uv' hint_u'v hzero htop
  simp only [one_mul] at hibp
  have heq : emStep a H = fun y : ℝ => (-(a : ℂ) * H y) - ((y : ℂ) * deriv H y) := rfl
  rw [heq, integral_sub (hint_H.const_mul (-(a : ℂ))) hint_uv', integral_const_mul, hibp]
  ring

private lemma integral_Ioi_emIter_one' {h : ℝ → ℂ} (hh : ExpDecaySmooth h) :
    ∫ y in Ioi (0 : ℝ), emIter 1 h y = ∫ y in Ioi (0 : ℝ), h y := by
  simpa [emIter] using integral_Ioi_emStep hh 0

private lemma integral_Ioi_emIter_ge_two {h : ℝ → ℂ} (hh : ExpDecaySmooth h) (k : ℕ) :
    ∫ y in Ioi (0 : ℝ), emIter (k + 2) h y = 0 := by
  induction k with
  | zero =>
    have h1 := integral_Ioi_emStep (eds_emIter 1 hh) 1
    simpa [emIter] using h1
  | succ k ih =>
    have h1 := integral_Ioi_emStep (eds_emIter (k + 2) hh) (k + 2)
    change ∫ y in Ioi (0 : ℝ), emStep (k + 2) (emIter (k + 2) h) y = 0
    rw [h1, ih, mul_zero]

/-- Exact derivative at `0` of `emStep a H`: `(emStep a H)^{(k)}(0) = -(a + k) H^{(k)}(0)`. -/
private lemma iteratedDeriv_emStep_zero {H : ℝ → ℂ} (hH : ExpDecaySmooth H) (a k : ℕ) :
    iteratedDeriv k (emStep a H) 0 = -(((a + k : ℕ) : ℂ)) * iteratedDeriv k H 0 := by
  have h1 : ContDiffAt ℝ k (fun x : ℝ => -(a : ℂ) * H x) 0 :=
    contDiffAt_const.mul (hH.1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
  have h2 : ContDiffAt ℝ k (fun x : ℝ => (x : ℂ) * deriv H x) 0 :=
    (Complex.ofRealCLM.contDiff.contDiffAt.of_le le_top).mul
      ((eds_deriv hH).1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
  change iteratedDeriv k (fun x : ℝ => -(a : ℂ) * H x - (x : ℂ) * deriv H x) 0 = _
  rw [iteratedDeriv_fun_sub h1 h2, iteratedDeriv_const_mul_field]
  have hmul : iteratedDeriv k (fun x : ℝ => (x : ℂ) * deriv H x) 0 =
      (k : ℂ) * iteratedDeriv k H 0 := by
    have hid_cd : ContDiffAt ℝ k (fun x : ℝ => (x : ℂ)) 0 :=
      Complex.ofRealCLM.contDiff.contDiffAt.of_le le_top
    rw [iteratedDeriv_fun_mul hid_cd
      ((eds_deriv hH).1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))]
    cases k with
    | zero => simp
    | succ m =>
      rw [Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero,
        Complex.ofReal_zero, zero_mul, add_zero]
      rw [Finset.sum_range_succ']
      have hd1 : iteratedDeriv 1 (fun t : ℝ => (t : ℂ)) 0 = 1 := by
        rw [iteratedDeriv_one]; exact (hasDerivAt_id (0 : ℝ)).ofReal_comp.deriv
      have hzero : ∀ i ∈ Finset.range m,
          ((m + 1).choose (i + 1 + 1) : ℂ) *
            iteratedDeriv (i + 1 + 1) (fun t : ℝ => (t : ℂ)) 0 *
            iteratedDeriv (m + 1 - (i + 1 + 1)) (deriv H) 0 = 0 := fun i _ => by
        rw [iteratedDeriv_ofReal_ge_two' (i + 1 + 1) (by omega) 0, mul_zero, zero_mul]
      rw [Finset.sum_eq_zero hzero, zero_add, Nat.choose_one_right, hd1, mul_one,
        show m + 1 - 1 = m by omega, ← iteratedDeriv_succ']
  rw [hmul]; push_cast; ring

/-- Exact formal identity `d_u (X^a * emSeriesShift θ H) = X^{a+1} * emSeriesShift θ (emStep a H)`. -/
private lemma d_u_X_pow_mul_emSeriesShift (θ : ℝ) {H : ℝ → ℂ} (hH : ExpDecaySmooth H) (a : ℕ) :
    d_u (PowerSeries.X ^ a * emSeriesShift θ H) =
      PowerSeries.X ^ (a + 1) * emSeriesShift θ (emStep a H) := by
  have hcoeff_du : ∀ (S : PowerSeries ℂ) (n : ℕ),
      PowerSeries.coeff n (d_u S) = match n with
        | 0 => 0
        | 1 => 0
        | k + 2 => -(((k + 1 : ℕ) : ℂ) * PowerSeries.coeff (k + 1) S) := fun S n => by
    rw [d_u, map_neg]
    rcases n with _ | _ | k
    · simp [PowerSeries.coeff_mul, PowerSeries.coeff_X_pow]
    · simp [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ, PowerSeries.coeff_X_pow]
    · change -(PowerSeries.coeff (k + 2) (PowerSeries.X ^ 2 * PowerSeries.derivative S)) = _
      rw [PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_derivative]; push_cast; ring
  ext n
  rw [hcoeff_du]
  rcases n with _ | _ | m
  · simp [PowerSeries.coeff_X_pow_mul']
  · simp only [PowerSeries.coeff_X_pow_mul']
    split_ifs with hle
    · have ha0 : a = 0 := by omega
      subst ha0
      simp [emSeriesShift, emTermShift, iteratedDeriv_emStep_zero hH 0 0]
    · rfl
  · by_cases hlt : m + 2 < a + 1
    · have h1 : ¬ a ≤ m + 1 := by omega
      have h2 : ¬ a + 1 ≤ m + 2 := by omega
      simp [PowerSeries.coeff_X_pow_mul', h1, h2]
    · have h1 : a ≤ m + 1 := by omega
      have h2 : a + 1 ≤ m + 2 := by omega
      have hsub : m + 2 - (a + 1) = m + 1 - a := by omega
      simp only [PowerSeries.coeff_X_pow_mul', h1, h2, ↓reduceIte, hsub, emSeriesShift,
        PowerSeries.coeff_mk, emTermShift, iteratedDeriv_emStep_zero hH a (m + 1 - a)]
      have hadd : a + (m + 1 - a) = m + 1 := by omega
      rw [hadd]
      ring

private lemma d_u_iter_emSeriesShift (θ : ℝ) {h : ℝ → ℂ} (hh : ExpDecaySmooth h) (j : ℕ) :
    d_u^[j] (emSeriesShift θ h) = PowerSeries.X ^ j * emSeriesShift θ (emIter j h) := by
  induction j with
  | zero => simp [emIter]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, d_u_X_pow_mul_emSeriesShift θ (eds_emIter j hh) j]
    rfl

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

/-- **All-Orders Shifted Euler–Maclaurin Asymptotics**:
For any rational `q ∈ (0, 1]` and smooth exponentially decaying `h`, every `u`-derivative
`iteratedDeriv j (sumScaleShift q h u - u * ∫ h)` has asymptotic expansion `d_u^[j] (emSeriesShift q h)`. -/
theorem sumScaleShift_iteratedDeriv_hasAsympExp {q : ℚ} (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) ≤ 1)
    {h : ℝ → ℂ} (hh : ExpDecaySmooth h) (j : ℕ) :
    HasAsympExp (iteratedDeriv j (fun u : ℝ => sumScaleShift (q : ℝ) h u - (u : ℂ) * (∫ y in Ioi (0 : ℝ), h y)))
      (d_u^[j] (emSeriesShift (q : ℝ) h)) := by
  let I0 : ℂ := ∫ y in Ioi (0 : ℝ), h y
  let f0 : ℝ → ℂ := fun u => sumScaleShift (q : ℝ) h u - (u : ℂ) * I0
  let G : ℕ → ℝ → ℂ := fun k => match k with
    | 0 => fun u => sumScaleShift (q : ℝ) h u - (u : ℂ) * I0
    | 1 => fun u => (u : ℂ)⁻¹ * sumScaleShift (q : ℝ) (emIter 1 h) u - I0
    | k + 2 => fun u => (u : ℂ)⁻¹ ^ (k + 2) * sumScaleShift (q : ℝ) (emIter (k + 2) h) u
  have hG_deriv : ∀ (k : ℕ) (u : ℝ), 0 < u → HasDerivAt (G k) (G (k + 1) u) u := by
    intro k u hu
    match k with
    | 0 =>
      have h1 := sumScaleShift_hasDerivAt hq0 hh 0 hu
      have h2 := ((hasDerivAt_id u).ofReal_comp).mul_const I0
      have hsub : HasDerivAt (fun v : ℝ => sumScaleShift (q : ℝ) h v - (v : ℂ) * I0)
          ((u : ℂ)⁻¹ * sumScaleShift (q : ℝ) (emStep 0 h) u - I0) u := by
        convert h1.sub h2 using 1
        · funext v; simp
        · simp
      simpa [G, emIter] using hsub
    | 1 =>
      have h1 := sumScaleShift_hasDerivAt hq0 (eds_emIter 1 hh) 1 hu
      simpa [G, emIter] using h1.sub_const I0
    | k + 2 =>
      exact sumScaleShift_hasDerivAt hq0 (eds_emIter (k + 2) hh) (k + 2) hu
  have hiter_eq : ∀ (k : ℕ) (u : ℝ), 0 < u → iteratedDeriv k f0 u = G k u := by
    intro k
    induction k with
    | zero => intro u _; rfl
    | succ k ih =>
      intro u hu
      have hev : iteratedDeriv k f0 =ᶠ[𝓝 u] G k := by
        filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
        exact ih v hv
      rw [iteratedDeriv_succ, hev.deriv_eq]
      exact (hG_deriv k u hu).deriv
  rw [d_u_iter_emSeriesShift (q : ℝ) hh j]
  have hG_asymp : HasAsympExp (G j) (PowerSeries.X ^ j * emSeriesShift (q : ℝ) (emIter j h)) := by
    match j with
    | 0 =>
      simpa [G, emIter] using sumScaleShift_hasAsympExp hq0 hq1 hh
    | 1 =>
      have hexp1 := (hasAsympExp_inv_pow' 1).mul (sumScaleShift_hasAsympExp hq0 hq1 (eds_emIter 1 hh))
      intro M
      obtain ⟨C, hC⟩ := hexp1 M
      refine ⟨C, ?_⟩
      filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with u hu_bd hu_pos
      have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
      have heq_u : G 1 u = (u : ℂ)⁻¹ ^ 1 *
          (sumScaleShift (q : ℝ) (emIter 1 h) u - (u : ℂ) * (∫ y in Ioi (0 : ℝ), emIter 1 h y)) := by
        dsimp only [G, I0]
        rw [integral_Ioi_emIter_one' hh, pow_one, mul_sub]
        congr 1; field_simp [huc]
      simpa only [heq_u] using hu_bd
    | k + 2 =>
      have hexp := (hasAsympExp_inv_pow' (k + 2)).mul
        (sumScaleShift_hasAsympExp hq0 hq1 (eds_emIter (k + 2) hh))
      intro M
      obtain ⟨C, hC⟩ := hexp M
      refine ⟨C, ?_⟩
      filter_upwards [hC] with u hu_bd
      have heq_u : G (k + 2) u = (u : ℂ)⁻¹ ^ (k + 2) *
          (sumScaleShift (q : ℝ) (emIter (k + 2) h) u - (u : ℂ) * (∫ y in Ioi (0 : ℝ), emIter (k + 2) h y)) := by
        dsimp only [G]
        rw [integral_Ioi_emIter_ge_two hh k, mul_zero, sub_zero]
      simpa only [heq_u] using hu_bd
  intro M
  obtain ⟨C, hC⟩ := hG_asymp M
  refine ⟨C, ?_⟩
  filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with u hu_bd hu_pos
  change ‖iteratedDeriv j f0 u - _‖ ≤ _
  rw [hiter_eq j u hu_pos]
  exact hu_bd

/-- Formal series rescaling `S(c * X)` sending `coeff n S ↦ c^n * coeff n S`. -/
@[expose] def scaleSeries (c : ℂ) (S : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => c ^ n * PowerSeries.coeff n S

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

/-- Exact algebraic commutator identity for `d_u = -X² ∂_X`:
`X * d_u^[j] T = d_u^[j](X * T) + j * X * d_u^[j-1](X * T)`. -/
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

/-- Multiplying a smooth function `h ~ X * T` by `u` shifts its all-orders derivative asymptotics
from `d_u^[j] (X * T)` to `d_u^[j] T`. -/
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

/-- Iterated version: if `h ~ X^p * T` (all derivatives), then `u^p * h u ~ T` (all derivatives). -/
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

/-! ### 4. Divisor-Sum Fubini, Global Mittag-Leffler Borel Transform `borelPhi`, & `HigherOrderBorelData` -/

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

/-- General Fubini identity for divisor convolutions on `ℂ`. -/
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
private lemma summable_sigmaNat_div_pow_plus_two (a : ℕ) :
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

/-- Euler factorization of the divisor-sum Borel Dirichlet series at `2*j + d + 1`. -/
private lemma tsum_borelAmp_div_pow (P : Quasipoly) (d : Fin (P.D + 1)) {j : ℕ} (hj : 1 ≤ j) :
    ∑' m : ℕ, P.borelAmp d (m + 1) / ((m + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1) =
      (∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (2 * j))⁻¹) *
        (∑' k : ℕ, P.cDft d (k + 1) / ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1)) := by
  obtain ⟨C, hC, hCbd⟩ := P.cDft_bounded d
  let F : ℕ → ℕ → ℂ := fun q k => (((q : ℂ) ^ (2 * j))⁻¹) * (P.cDft d k / ((k : ℂ) ^ (2 * j + d.1 + 1)))
  have hF_norm : Summable (fun p : ℕ × ℕ => ‖F (p.1 + 1) (p.2 + 1)‖) := by
    have hprod := (summable_one_div_nat_pow_succ (p := 2 * j) (by omega)).mul_of_nonneg
      ((summable_one_div_nat_pow_succ (p := 2 * j + d.1 + 1) (by omega)).mul_left C)
      (fun _ => by positivity) (fun _ => by positivity)
    refine hprod.of_nonneg_of_le (fun _ => norm_nonneg _) fun p => ?_
    dsimp only [F]
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast, norm_div, norm_pow, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hCbd _) (by positivity)
  have hfub := (tsum_divisor_fubini hF_norm).2
  have hLHS : ∀ m : ℕ,
      P.borelAmp d (m + 1) / ((m + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1) =
        ∑ k ∈ Nat.divisors (m + 1), F ((m + 1) / k) k := fun m => by
    unfold Quasipoly.borelAmp
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k hk => ?_
    dsimp only [F]
    have hk_dvd : k ∣ m + 1 := Nat.dvd_of_mem_divisors hk
    have hk_ne : (k : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hk).ne'
    have hq_ne : (((m + 1) / k : ℕ) : ℂ) ≠ 0 := by
      have : 0 < (m + 1) / k := Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos m) hk_dvd) (Nat.pos_of_mem_divisors hk)
      exact_mod_cast this.ne'
    have hmul : (((m + 1) / k : ℕ) : ℂ) * (k : ℂ) = ((m + 1 : ℕ) : ℂ) := by
      exact_mod_cast Nat.div_mul_cancel hk_dvd
    rw [← hmul, mul_pow, show 2 * j + d.1 + 1 = 2 * j + (d.1 + 1) by omega,
      pow_add (((m + 1) / k : ℕ) : ℂ) (2 * j) (d.1 + 1)]
    field_simp [hk_ne, hq_ne]
  rw [tsum_congr hLHS, hfub]
  have hRHS : ∀ n : ℕ, (∑' k : ℕ, F (n + 1) (k + 1)) =
      (((n + 1 : ℕ) : ℂ) ^ (2 * j))⁻¹ *
        ∑' k : ℕ, P.cDft d (k + 1) / ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1) := fun n => by
    dsimp only [F]
    exact tsum_mul_left
  rw [tsum_congr hRHS, tsum_mul_right]

/-- Base Borel lattice frequency `ωBase P m = 4π² (m + 1) / M`. -/
@[expose] def ωBase (P : Quasipoly) (m : ℕ) : ℝ :=
  4 * Real.pi ^ 2 * ((m + 1 : ℕ) : ℝ) / (P.M : ℝ)

private lemma ωBase_pos (P : Quasipoly) (m : ℕ) : 0 < ωBase P m := by
  unfold ωBase
  have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  positivity

private lemma ωBase_strictMono (P : Quasipoly) : StrictMono (ωBase P) := by
  intro a b hab
  unfold ωBase
  have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
  gcongr

private lemma ωBase_ge_base (P : Quasipoly) (m : ℕ) :
    4 * Real.pi ^ 2 / (P.M : ℝ) ≤ ωBase P m := by
  unfold ωBase
  have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
  have h4 : 4 * Real.pi ^ 2 ≤ 4 * Real.pi ^ 2 * ((m + 1 : ℕ) : ℝ) :=
    le_mul_of_one_le_right (by positivity) h1
  exact div_le_div_of_nonneg_right h4 hM.le

/-- Exact Mittag-Leffler prefactor `-2 * (-1)^{d+1} * (d+1) * (d+2) * i^{d+1} * (2π)^{d+1}`. -/
@[expose] def borelPref (d : ℕ) : ℂ :=
  -2 * (-1 : ℂ) ^ (d + 1) * ((d + 1 : ℕ) : ℂ) * ((d + 2 : ℕ) : ℂ) *
    I ^ (d + 1) * (2 * (Real.pi : ℂ)) ^ (d + 1)

private lemma borelPref_ne_zero (d : ℕ) : borelPref d ≠ 0 := by
  unfold borelPref
  have h1 : (-2 : ℂ) ≠ 0 := by norm_num
  have h2 : (-1 : ℂ) ^ (d + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : ((d + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
  have h4 : ((d + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (d + 1)
  have h5 : I ^ (d + 1) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have h6 : (2 * (Real.pi : ℂ)) ^ (d + 1) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4) h5) h6

/-- Single lattice-point term of the global Mittag-Leffler Borel transform `borelPhi P`. -/
@[expose] def borelTerm (P : Quasipoly) (m : ℕ) (ξ : ℂ) : ℂ :=
  ∑ d : Fin (P.D + 1), borelPref d.1 * P.borelAmp d (m + 1) *
    (((ξ - (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹ +
      (-1 : ℂ) ^ (d.1 + 1) * ((ξ + (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹)

/-- **Closed-Form Global Mittag-Leffler Borel Transform** for any quasipolynomial `P`:
`Φ_P(ξ) = ∑_{m ≥ 1} ∑_{d=0}^D pref_d * A_d(m) * ((ξ - 4π² m/M)^{-(d+3)} + (-1)^{d+1} (ξ + 4π² m/M)^{-(d+3)})`. -/
@[expose] def borelPhi (P : Quasipoly) (ξ : ℂ) : ℂ :=
  ∑' m : ℕ, borelTerm P m ξ

private lemma borelTerm_eq_zero_of_notMem_poleSet {P : Quasipoly} {m : ℕ} (hm : m ∉ P.poleSet) (ξ : ℂ) :
    borelTerm P m ξ = 0 := by
  unfold borelTerm
  refine Finset.sum_eq_zero fun d _ => ?_
  have h0 : P.borelAmp d (m + 1) = 0 := by
    by_contra hne
    exact hm ⟨d, hne⟩
  rw [h0, mul_zero, zero_mul]

/-- Uniform summable majorant for `borelTerm P m z` whenever `‖z - ωBase P m‖, ‖z + ωBase P m‖ ≥ ωBase P m / 2`. -/
private lemma exists_borelTerm_majorant (P : Quasipoly) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ (m : ℕ) (z : ℂ),
        ωBase P m / 2 ≤ ‖z - (ωBase P m : ℂ)‖ →
        ωBase P m / 2 ≤ ‖z + (ωBase P m : ℂ)‖ →
        ‖borelTerm P m z‖ ≤ u m := by
  have hC : ∀ d : Fin (P.D + 1), ∃ C : ℝ, 0 ≤ C ∧
      ∀ m : ℕ, 1 ≤ m → ‖P.borelAmp d m‖ ≤ C * (sigmaNat (d.1 + 1) m : ℝ) :=
    fun d => P.borelAmp_norm_le d
  choose C hC_nn hC_bd using hC
  let coef : Fin (P.D + 1) → ℝ := fun d =>
    ‖borelPref d.1‖ * C d * (2 * ((2 * Real.pi ^ 2 / (P.M : ℝ)) ^ (d.1 + 3))⁻¹)
  let u : ℕ → ℝ := fun m =>
    ∑ d : Fin (P.D + 1), coef d * ((sigmaNat (d.1 + 1) (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ (d.1 + 3))
  have hu_sum : Summable u :=
    summable_sum fun d _ => (summable_sigmaNat_div_pow_plus_two d.1).mul_left (coef d)
  refine ⟨u, hu_sum, fun m z hsub hadd => ?_⟩
  unfold borelTerm
  calc ‖∑ d : Fin (P.D + 1), _‖
      ≤ ∑ d : Fin (P.D + 1), ‖borelPref d.1 * P.borelAmp d (m + 1) *
          (((z - (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹ +
            (-1 : ℂ) ^ (d.1 + 1) * ((z + (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹)‖ := norm_sum_le _ _
    _ ≤ ∑ d : Fin (P.D + 1), coef d * ((sigmaNat (d.1 + 1) (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ (d.1 + 3)) := by
        refine Finset.sum_le_sum fun d _ => ?_
        have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
        have hw_half_pos : 0 < ωBase P m / 2 := by have := ωBase_pos P m; positivity
        have hinv1 : ‖((z - (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹‖ ≤ ((ωBase P m / 2) ^ (d.1 + 3))⁻¹ := by
          rw [norm_inv, norm_pow]
          exact inv_anti₀ (pow_pos hw_half_pos _) (pow_le_pow_left₀ hw_half_pos.le hsub _)
        have hinv2 : ‖(-1 : ℂ) ^ (d.1 + 1) * ((z + (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹‖ ≤
            ((ωBase P m / 2) ^ (d.1 + 3))⁻¹ := by
          rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_inv, norm_pow]
          exact inv_anti₀ (pow_pos hw_half_pos _) (pow_le_pow_left₀ hw_half_pos.le hadd _)
        have hsum_inv : ‖((z - (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹ +
            (-1 : ℂ) ^ (d.1 + 1) * ((z + (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹‖ ≤
            2 * ((ωBase P m / 2) ^ (d.1 + 3))⁻¹ := by
          calc ‖_ + _‖ ≤ ‖((z - (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹‖ +
                ‖(-1 : ℂ) ^ (d.1 + 1) * ((z + (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹‖ := norm_add_le _ _
            _ ≤ ((ωBase P m / 2) ^ (d.1 + 3))⁻¹ + ((ωBase P m / 2) ^ (d.1 + 3))⁻¹ := add_le_add hinv1 hinv2
            _ = 2 * ((ωBase P m / 2) ^ (d.1 + 3))⁻¹ := by ring
        have hw_split : ωBase P m / 2 = (2 * Real.pi ^ 2 / (P.M : ℝ)) * ((m + 1 : ℕ) : ℝ) := by
          unfold ωBase; ring
        have hamp := hC_bd d (m + 1) (Nat.succ_pos m)
        have hCd := hC_nn d
        rw [norm_mul, norm_mul]
        calc ‖borelPref d.1‖ * ‖P.borelAmp d (m + 1)‖ * ‖_‖
            ≤ ‖borelPref d.1‖ * (C d * (sigmaNat (d.1 + 1) (m + 1) : ℝ)) *
                (2 * ((ωBase P m / 2) ^ (d.1 + 3))⁻¹) := by
              gcongr
          _ = coef d * ((sigmaNat (d.1 + 1) (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ (d.1 + 3)) := by
              dsimp only [coef]
              rw [hw_split, mul_pow, mul_inv, div_eq_mul_inv]
              ring

private lemma ωBase_tail_diff_norm_ge (P : Quasipoly) (w₀ : ℂ) (R : ℝ) :
    ∃ N : ℕ, ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball w₀ R →
      ωBase P (k + N) / 2 ≤ ‖z - (ωBase P (k + N) : ℂ)‖ ∧
      ωBase P (k + N) / 2 ≤ ‖z + (ωBase P (k + N) : ℂ)‖ := by
  have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  have hpiM : 0 < 2 * Real.pi ^ 2 / (P.M : ℝ) := by positivity
  let N : ℕ := Nat.ceil ((‖w₀‖ + R) / (2 * Real.pi ^ 2 / (P.M : ℝ)))
  refine ⟨N, fun k z hz => ?_⟩
  have hN : (‖w₀‖ + R) / (2 * Real.pi ^ 2 / (P.M : ℝ)) ≤ (N : ℝ) := Nat.le_ceil _
  have hM1 : ‖w₀‖ + R ≤ (2 * Real.pi ^ 2 / (P.M : ℝ)) * (N : ℝ) :=
    ((div_le_iff₀ hpiM).mp hN).trans_eq (by ring)
  have hM2 : 2 * (‖w₀‖ + R) ≤ ωBase P (k + N) := by
    have hle : (N : ℝ) ≤ ((k + N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : N ≤ k + N + 1)
    have hsplit : ωBase P (k + N) = 2 * ((2 * Real.pi ^ 2 / (P.M : ℝ)) * ((k + N + 1 : ℕ) : ℝ)) := by
      unfold ωBase; ring
    rw [hsplit]
    nlinarith
  have hz_norm : ‖z‖ ≤ ‖w₀‖ + R := by
    have hball : ‖z - w₀‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    calc ‖z‖ = ‖(z - w₀) + w₀‖ := by ring_nf
      _ ≤ ‖z - w₀‖ + ‖w₀‖ := norm_add_le _ _
      _ ≤ R + ‖w₀‖ := by linarith
      _ = ‖w₀‖ + R := by ring
  have hsub : ωBase P (k + N) / 2 ≤ ‖z - (ωBase P (k + N) : ℂ)‖ := by
    have htri := norm_add_le ((ωBase P (k + N) : ℂ) - z) z
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ωBase_pos P (k + N)),
      norm_sub_rev] at htri
    linarith
  have hadd : ωBase P (k + N) / 2 ≤ ‖z + (ωBase P (k + N) : ℂ)‖ := by
    have htri := norm_add_le (z + (ωBase P (k + N) : ℂ)) (-z)
    rw [add_neg_cancel_comm, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (ωBase_pos P (k + N))] at htri
    linarith
  exact ⟨hsub, hadd⟩

private lemma ωBase_add_ne_zero_of_wedge (P : Quasipoly) {w : ℂ}
    (hw : w ∈ borelWedge (Real.pi / 4) (2 * Real.pi ^ 2 / (P.M : ℝ))) (m : ℕ) :
    w + (ωBase P m : ℂ) ≠ 0 := by
  have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  intro h0
  rcases hw with hw_ball | ⟨hw_re, _⟩
  · have hlt : ‖w‖ < 2 * Real.pi ^ 2 / (P.M : ℝ) := by simpa [Metric.mem_ball] using hw_ball
    have heq : w = -(ωBase P m : ℂ) := eq_neg_of_add_eq_zero_left h0
    rw [heq, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ωBase_pos P m)] at hlt
    have hge := ωBase_ge_base P m
    have hpos : 0 < 2 * Real.pi ^ 2 / (P.M : ℝ) := by positivity
    have h24 : 4 * Real.pi ^ 2 / (P.M : ℝ) = 2 * (2 * Real.pi ^ 2 / (P.M : ℝ)) := by ring
    linarith
  · have hre := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith [ωBase_pos P m]

private lemma norm_sub_exp_mul_real_ge' (σ : ℝ) (A : ℝ) (v : ℝ) :
    |A * Real.sin σ| ≤ ‖Complex.exp (I * (σ : ℂ)) * (v : ℂ) - (A : ℂ)‖ := by
  rw [norm_sub_rev]
  let w : ℂ := (A : ℂ) - Complex.exp (I * (σ : ℂ)) * (v : ℂ)
  have hexp_σ : Complex.exp (I * (σ : ℂ)) = Complex.exp ((σ : ℂ) * I) := by congr 1; ring
  have hw_re : w.re = A - Real.cos σ * v := by
    dsimp only [w]
    rw [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, hexp_σ,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hw_im : w.im = -(Real.sin σ * v) := by
    dsimp only [w]
    rw [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, hexp_σ,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, zero_sub]
  have h_nsq : (A * Real.sin σ) ^ 2 ≤ Complex.normSq w := by
    rw [Complex.normSq_apply, hw_re, hw_im]
    have hid := Real.sin_sq_add_cos_sq σ
    have hid' : (A - Real.cos σ * v) * (A - Real.cos σ * v) +
        (-(Real.sin σ * v)) * (-(Real.sin σ * v)) =
        (v - A * Real.cos σ) ^ 2 + (A * Real.sin σ) ^ 2 +
          (v ^ 2 - A ^ 2) * (Real.sin σ ^ 2 + Real.cos σ ^ 2 - 1) := by ring
    rw [hid', hid, sub_self, mul_zero, add_zero]
    linarith [sq_nonneg (v - A * Real.cos σ)]
  change |A * Real.sin σ| ≤ ‖w‖
  rw [Complex.norm_def]
  exact Real.le_sqrt_of_sq_le (by rw [sq_abs]; exact h_nsq)

private lemma norm_add_exp_mul_real_ge' (σ : ℝ) (hcos : 0 ≤ Real.cos σ) {A : ℝ} {v : ℝ} (hv : 0 ≤ v) :
    A ≤ ‖Complex.exp (I * (σ : ℂ)) * (v : ℂ) + (A : ℂ)‖ := by
  have hexp_σ : Complex.exp (I * (σ : ℂ)) = Complex.exp ((σ : ℂ) * I) := by congr 1; ring
  have hre : (Complex.exp (I * (σ : ℂ)) * (v : ℂ) + (A : ℂ)).re = Real.cos σ * v + A := by
    rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re, hexp_σ,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hle : A ≤ (Complex.exp (I * (σ : ℂ)) * (v : ℂ) + (A : ℂ)).re := by rw [hre]; nlinarith
  exact hle.trans (le_trans (le_abs_self _) (Complex.abs_re_le_norm _))

/-- Strictly increasing enumeration of the nonzero pole indices in `P.poleSet`. -/
@[expose] def poleIdx (P : Quasipoly) : ℕ → ℕ :=
  Nat.nth (· ∈ P.poleSet)

/-- Strictly increasing positive pole frequencies `ω_k = 4π² (poleIdx P k + 1) / M`. -/
@[expose] def poleFreq (P : Quasipoly) (k : ℕ) : ℝ :=
  ωBase P (poleIdx P k)

/-- Exact pole order at `poleFreq P k` (`3 ≤ poleOrd ≤ D + 3`). -/
@[expose] def poleOrd (P : Quasipoly) (hodd : ∃ n : ℤ, P.oddPart n ≠ 0) (k : ℕ) : ℕ := by
  classical
  have hmem : poleIdx P k ∈ P.poleSet := Nat.nth_mem_of_infinite (P.infinite_poleSet hodd) k
  let S : Finset ℕ := (Finset.univ.filter fun d : Fin (P.D + 1) =>
    P.borelAmp d (poleIdx P k + 1) ≠ 0).image Fin.val
  have hS_ne : S.Nonempty := by
    obtain ⟨d, hd⟩ := hmem
    exact ⟨d.1, Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, hd⟩, rfl⟩⟩
  exact S.max' hS_ne + 3

/-- Exact principal part coefficients `pp k s` at `poleFreq P k`. -/
@[expose] def polePP (P : Quasipoly) (k s : ℕ) : ℂ :=
  if hs : 3 ≤ s ∧ s - 3 ≤ P.D then
    borelPref (s - 3) * P.borelAmp ⟨s - 3, by omega⟩ (poleIdx P k + 1)
  else 0

/-- **Genuine `HigherOrderBorelData` witness** for the global Mittag-Leffler Borel transform
`borelPhi P` whenever `P^-` is not identically zero on `ℤ`. -/
private def borelPhi_borelData (P : Quasipoly) (hodd : ∃ n : ℤ, P.oddPart n ≠ 0) :
    HigherOrderBorelData (borelPhi P) 0 (poleFreq P) (poleOrd P hodd) (polePP P) where
  α₀ := Real.pi / 4
  θ := Real.pi / 6
  ε := 2 * Real.pi ^ 2 / (P.M : ℝ)
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := by
    have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
    positivity
  ω_pos := ωBase_pos P (poleIdx P 0)
  ω_mono := (ωBase_strictMono P).comp (Nat.nth_strictMono (P.infinite_poleSet hodd))
  ord_pos := fun k => by
    unfold poleOrd
    dsimp only
    omega
  pp_lead_ne_zero := fun k => by
    classical
    let S : Finset ℕ := (Finset.univ.filter fun d : Fin (P.D + 1) =>
      P.borelAmp d (poleIdx P k + 1) ≠ 0).image Fin.val
    have hmem : poleIdx P k ∈ P.poleSet := Nat.nth_mem_of_infinite (P.infinite_poleSet hodd) k
    have hS_ne : S.Nonempty := by
      obtain ⟨d, hd⟩ := hmem
      exact ⟨d.1, Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, hd⟩, rfl⟩⟩
    have hmax_mem : S.max' hS_ne ∈ S := Finset.max'_mem S hS_ne
    obtain ⟨d₀, hd₀_filt, hd₀_val⟩ := Finset.mem_image.mp hmax_mem
    have hd₀_ne : P.borelAmp d₀ (poleIdx P k + 1) ≠ 0 := (Finset.mem_filter.mp hd₀_filt).2
    have hord_eq : poleOrd P hodd k = d₀.1 + 3 := by
      change S.max' hS_ne + 3 = d₀.1 + 3
      omega
    rw [polePP, hord_eq]
    have hcond : 3 ≤ d₀.1 + 3 ∧ d₀.1 + 3 - 3 ≤ P.D := ⟨by omega, by omega⟩
    rw [dite_eq_left hcond]
    have hfin : (⟨d₀.1 + 3 - 3, by omega⟩ : Fin (P.D + 1)) = d₀ := Fin.ext (by simp)
    rw [hfin]
    have hsub3 : d₀.1 + 3 - 3 = d₀.1 := by omega
    rw [hsub3]
    exact mul_ne_zero (borelPref_ne_zero d₀.1) hd₀_ne
  analyticOn := fun w hw => by
    simp only [rotatedPuncturedWedge, puncturedWedge, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_mul, Set.mem_sdiff] at hw
    obtain ⟨u, hu_sum, hu_bd⟩ := exists_borelTerm_majorant P
    obtain ⟨N, hN⟩ := ωBase_tail_diff_norm_ge P w 1
    let head : ℂ → ℂ := fun z => ∑ m ∈ Finset.range N, borelTerm P m z
    let tail : ℂ → ℂ := fun z => ∑' k : ℕ, borelTerm P (k + N) z
    have htail_diff : DifferentiableOn ℂ tail (Metric.ball w 1) := by
      refine Complex.differentiableOn_tsum_of_summable_norm
        (u := fun k => u (k + N)) ((summable_nat_add_iff N).2 hu_sum) (fun k => ?_)
        Metric.isOpen_ball (fun k z hz => hu_bd (k + N) z (hN k z hz).1 (hN k z hz).2)
      refine DifferentiableOn.fun_sum fun d _ => ?_
      refine DifferentiableOn.const_mul ?_ _
      refine DifferentiableOn.add ?_ (DifferentiableOn.const_mul ?_ _)
      · refine DifferentiableOn.inv ((differentiableOn_id.sub (differentiableOn_const _)).pow _)
          fun z hz h0 => ?_
        have hsub0 : z - (ωBase P (k + N) : ℂ) = 0 := eq_zero_of_pow_eq_zero h0
        have h1 := (hN k z hz).1; rw [hsub0, norm_zero] at h1
        linarith [ωBase_pos P (k + N)]
      · refine DifferentiableOn.inv ((differentiableOn_id.add (differentiableOn_const _)).pow _)
          fun z hz h0 => ?_
        have hadd0 : z + (ωBase P (k + N) : ℂ) = 0 := eq_zero_of_pow_eq_zero h0
        have h1 := (hN k z hz).2; rw [hadd0, norm_zero] at h1
        linarith [ωBase_pos P (k + N)]
    have htail_ana : AnalyticAt ℂ tail w :=
      (htail_diff.analyticOnNhd Metric.isOpen_ball) w (Metric.mem_ball_self zero_lt_one)
    have hhead_ana : AnalyticAt ℂ head w := by
      refine Finset.analyticAt_fun_sum (Finset.range N) fun m _ => ?_
      by_cases hm : m ∈ P.poleSet
      · refine Finset.analyticAt_fun_sum Finset.univ fun d _ => ?_
        refine AnalyticAt.mul analyticAt_const ?_
        refine AnalyticAt.add ?_ (AnalyticAt.mul analyticAt_const ?_)
        · refine ((analyticAt_id.sub analyticAt_const).pow _).inv ?_
          refine pow_ne_zero _ (sub_ne_zero.mpr fun hEq => hw.2 ?_)
          have hinf : (Set.ofPred (fun x : ℕ => x ∈ P.poleSet)).Infinite := P.infinite_poleSet hodd
          have hmem_range : m ∈ Set.range (poleIdx P) := by
            rw [poleIdx, Nat.range_nth_of_infinite hinf]
            exact hm
          obtain ⟨k, rfl⟩ := hmem_range
          exact ⟨k, hEq.symm⟩
        · refine ((analyticAt_id.add analyticAt_const).pow _).inv ?_
          exact pow_ne_zero _ (ωBase_add_ne_zero_of_wedge P hw.1 m)
      · have hz : borelTerm P m = fun _ => 0 := funext fun z => borelTerm_eq_zero_of_notMem_poleSet hm z
        rw [hz]; exact analyticAt_const
    have hev : borelPhi P =ᶠ[𝓝 w] fun z => head z + tail z := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one)] with z hz
      have hts : Summable (fun k : ℕ => borelTerm P (k + N) z) :=
        ((summable_nat_add_iff N).2 hu_sum).of_norm_bounded fun k =>
          hu_bd (k + N) z (hN k z hz).1 (hN k z hz).2
      have hsum_all := (summable_nat_add_iff (f := fun m => borelTerm P m z) N).1 hts
      exact (hsum_all.sum_add_tsum_nat_add N).symm
    exact (hhead_ana.add htail_ana).congr hev.symm
  pole_principalPart := fun k => by
    classical
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
    let m₀ : ℕ := poleIdx P k
    let w : ℂ := (ωBase P m₀ : ℂ)
    let R : ℝ := 2 * Real.pi ^ 2 / (P.M : ℝ)
    have hR : 0 < R := by
      have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
      dsimp only [R]; positivity
    obtain ⟨u, hu_sum, hu_bd⟩ := exists_borelTerm_majorant P
    obtain ⟨N₀, hN₀⟩ := ωBase_tail_diff_norm_ge P w R
    let N₁ : ℕ := max N₀ (m₀ + 1)
    have hN₁ : ∀ (j : ℕ) (z : ℂ), z ∈ Metric.ball w R →
        ωBase P (j + N₁) / 2 ≤ ‖z - (ωBase P (j + N₁) : ℂ)‖ ∧
        ωBase P (j + N₁) / 2 ≤ ‖z + (ωBase P (j + N₁) : ℂ)‖ := fun j z hz => by
      have hj := hN₀ (j + (N₁ - N₀)) z hz
      have hidx : j + (N₁ - N₀) + N₀ = j + N₁ := by omega
      simpa only [hidx] using hj
    let mid : ℂ → ℂ := fun z => ∑ m ∈ (Finset.range N₁).erase m₀, borelTerm P m z
    let tail : ℂ → ℂ := fun z => ∑' j : ℕ, borelTerm P (j + N₁) z
    let reg₀ : ℂ → ℂ := fun z => ∑ d : Fin (P.D + 1), borelPref d.1 * P.borelAmp d (m₀ + 1) *
      ((-1 : ℂ) ^ (d.1 + 1) * ((z + w) ^ (d.1 + 3))⁻¹)
    have htail_diff : DifferentiableOn ℂ tail (Metric.ball w R) := by
      refine Complex.differentiableOn_tsum_of_summable_norm
        (u := fun j => u (j + N₁)) ((summable_nat_add_iff N₁).2 hu_sum) (fun j => ?_)
        Metric.isOpen_ball (fun j z hz => hu_bd (j + N₁) z (hN₁ j z hz).1 (hN₁ j z hz).2)
      refine DifferentiableOn.fun_sum fun d _ => ?_
      refine DifferentiableOn.const_mul ?_ _
      refine DifferentiableOn.add ?_ (DifferentiableOn.const_mul ?_ _)
      · refine DifferentiableOn.inv ((differentiableOn_id.sub (differentiableOn_const _)).pow _)
          fun z hz h0 => ?_
        have h1 := (hN₁ j z hz).1; rw [eq_zero_of_pow_eq_zero h0, norm_zero] at h1
        linarith [ωBase_pos P (j + N₁)]
      · refine DifferentiableOn.inv ((differentiableOn_id.add (differentiableOn_const _)).pow _)
          fun z hz h0 => ?_
        have h1 := (hN₁ j z hz).2; rw [eq_zero_of_pow_eq_zero h0, norm_zero] at h1
        linarith [ωBase_pos P (j + N₁)]
    have htail_cont : ContinuousAt tail w :=
      (htail_diff.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))).continuousAt
    have hmid_ana : AnalyticAt ℂ mid w := by
      refine Finset.analyticAt_fun_sum ((Finset.range N₁).erase m₀) fun m hm => ?_
      have hne : m ≠ m₀ := (Finset.mem_erase.mp hm).1
      refine Finset.analyticAt_fun_sum Finset.univ fun d _ => ?_
      refine AnalyticAt.mul analyticAt_const (AnalyticAt.add ?_ (AnalyticAt.mul analyticAt_const ?_))
      · refine ((analyticAt_id.sub analyticAt_const).pow _).inv ?_
        refine pow_ne_zero _ (sub_ne_zero.mpr fun hEq => hne ?_)
        change (ωBase P m₀ : ℂ) = (ωBase P m : ℂ) at hEq
        have hR_eq : ωBase P m₀ = ωBase P m := by exact_mod_cast hEq
        exact ((ωBase_strictMono P).injective hR_eq).symm
      · refine ((analyticAt_id.add analyticAt_const).pow _).inv ?_
        refine pow_ne_zero _ fun h0 => ?_
        change (ωBase P m₀ : ℂ) + (ωBase P m : ℂ) = 0 at h0
        have hre := congrArg Complex.re h0
        simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
        linarith [ωBase_pos P m₀, ωBase_pos P m]
    have hmid_cont : ContinuousAt mid w := hmid_ana.continuousAt
    have hreg₀_ana : AnalyticAt ℂ reg₀ w := by
      refine Finset.analyticAt_fun_sum Finset.univ fun d _ => ?_
      refine AnalyticAt.mul analyticAt_const (AnalyticAt.mul analyticAt_const ?_)
      refine ((analyticAt_id.add analyticAt_const).pow _).inv ?_
      refine pow_ne_zero _ fun h0 => ?_
      change (ωBase P m₀ : ℂ) + (ωBase P m₀ : ℂ) = 0 at h0
      have hre := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
      linarith [ωBase_pos P m₀]
    have hreg₀_cont : ContinuousAt reg₀ w := hreg₀_ana.continuousAt
    -- Algebraic cancellation of the singular part at `m₀`!
    have hcancel : ∀ z : ℂ,
        borelTerm P m₀ z - ∑ s ∈ Finset.Icc 1 (poleOrd P hodd k), polePP P k s / (z - w) ^ s =
          reg₀ z := fun z => by
      let S : Finset ℕ := (Finset.univ.filter fun d : Fin (P.D + 1) =>
        P.borelAmp d (m₀ + 1) ≠ 0).image Fin.val
      have hmem : m₀ ∈ P.poleSet := Nat.nth_mem_of_infinite (P.infinite_poleSet hodd) k
      have hS_ne : S.Nonempty := by
        obtain ⟨d, hd⟩ := hmem
        exact ⟨d.1, Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, hd⟩, rfl⟩⟩
      have hord_def : poleOrd P hodd k = S.max' hS_ne + 3 := rfl
      have hpp_sum : ∑ s ∈ Finset.Icc 1 (poleOrd P hodd k), polePP P k s / (z - w) ^ s =
          ∑ d : Fin (P.D + 1), borelPref d.1 * P.borelAmp d (m₀ + 1) * ((z - w) ^ (d.1 + 3))⁻¹ := by
        have hsum_range : ∑ s ∈ Finset.Icc 1 (poleOrd P hodd k), polePP P k s / (z - w) ^ s =
            ∑ d ∈ Finset.range (S.max' hS_ne + 1),
              polePP P k (d + 3) / (z - w) ^ (d + 3) := by
          rw [hord_def]
          have hsub : Finset.Icc 1 (S.max' hS_ne + 3) =
              {1, 2} ∪ (Finset.range (S.max' hS_ne + 1)).image (· + 3) := by
            ext s; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert,
              Finset.mem_singleton, Finset.mem_image, Finset.mem_range]
            constructor
            · intro ⟨h1, h2⟩
              by_cases hs : s ≤ 2
              · left; omega
              · right; exact ⟨s - 3, by omega, by omega⟩
            · rintro ((rfl | rfl) | ⟨a, ha, rfl⟩) <;> omega
          have hdisj : Disjoint ({1, 2} : Finset ℕ) ((Finset.range (S.max' hS_ne + 1)).image (· + 3)) := by
            rw [Finset.disjoint_left]
            intro s hs1 hs2
            obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hs2
            simp only [Finset.mem_insert, Finset.mem_singleton] at hs1
            omega
          rw [hsub, Finset.sum_union hdisj,
            Finset.sum_image (fun a _ b _ hab => by omega)]
          have hz12 : ∑ s ∈ ({1, 2} : Finset ℕ), polePP P k s / (z - w) ^ s = 0 := by
            refine Finset.sum_eq_zero fun s hs => ?_
            simp only [Finset.mem_insert, Finset.mem_singleton] at hs
            have hnot : ¬ (3 ≤ s ∧ s - 3 ≤ P.D) := by omega
            rw [polePP, dite_eq_right hnot, zero_div]
          rw [hz12, zero_add]
        rw [hsum_range]
        have hmax_le : S.max' hS_ne ≤ P.D := by
          have hm' := Finset.max'_mem S hS_ne
          obtain ⟨d, _, hd⟩ := Finset.mem_image.mp hm'
          omega
        have hFin : (∑ d : Fin (P.D + 1), borelPref d.1 * P.borelAmp d (m₀ + 1) * ((z - w) ^ (d.1 + 3))⁻¹) =
            ∑ d ∈ Finset.range (P.D + 1),
              if hd : d < P.D + 1 then
                borelPref d * P.borelAmp ⟨d, hd⟩ (m₀ + 1) * ((z - w) ^ (d + 3))⁻¹
              else 0 := by
          rw [← Fin.sum_univ_eq_sum_range (fun d => if hd : d < P.D + 1 then
            borelPref d * P.borelAmp ⟨d, hd⟩ (m₀ + 1) * ((z - w) ^ (d + 3))⁻¹ else 0)]
          refine Finset.sum_congr rfl fun d _ => ?_
          simp [d.isLt]
        rw [hFin]
        have hsub_rng : Finset.range (S.max' hS_ne + 1) ⊆ Finset.range (P.D + 1) :=
          Finset.range_mono (by omega)
        rw [← Finset.sum_subset hsub_rng]
        · refine Finset.sum_congr rfl fun d hd => ?_
          have hd_lt : d < P.D + 1 := by have := Finset.mem_range.mp hd; omega
          have hcond : 3 ≤ d + 3 ∧ d + 3 - 3 ≤ P.D := ⟨by omega, by omega⟩
          simp only [polePP, dite_eq_left hcond, dite_eq_left hd_lt, div_eq_mul_inv]
          have hsub3 : d + 3 - 3 = d := by omega
          simp only [hsub3]; rfl
        · intro d hd hnot
          have hd_lt : d < P.D + 1 := Finset.mem_range.mp hd
          rw [dite_eq_left hd_lt]
          have hamp0 : P.borelAmp ⟨d, hd_lt⟩ (m₀ + 1) = 0 := by
            by_contra hne
            have hmemS : d ∈ S := Finset.mem_image.mpr
              ⟨⟨d, hd_lt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, rfl⟩
            have hle := Finset.le_max' S d hmemS
            exact hnot (Finset.mem_range.mpr (by omega))
          rw [hamp0, mul_zero, zero_mul]
      rw [hpp_sum]
      unfold borelTerm
      dsimp only [reg₀]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun d _ => ?_
      change borelPref d.1 * P.borelAmp d (m₀ + 1) *
          (((z - w) ^ (d.1 + 3))⁻¹ + (-1 : ℂ) ^ (d.1 + 1) * ((z + w) ^ (d.1 + 3))⁻¹) -
        borelPref d.1 * P.borelAmp d (m₀ + 1) * ((z - w) ^ (d.1 + 3))⁻¹ = _
      ring
    have hev : (fun z : ℂ => borelPhi P z -
          ∑ s ∈ Finset.Icc 1 (poleOrd P hodd k), polePP P k s / (z - w) ^ s) =ᶠ[𝓝[≠] w]
        fun z => reg₀ z + mid z + tail z := by
      have hball : Metric.ball w R \ {w} ∈ 𝓝[≠] w := by
        rw [Set.sdiff_eq, Set.inter_comm]
        exact inter_mem_nhdsWithin _ (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))
      filter_upwards [hball] with z ⟨hz_ball, _⟩
      have hts : Summable (fun j : ℕ => borelTerm P (j + N₁) z) :=
        ((summable_nat_add_iff N₁).2 hu_sum).of_norm_bounded fun j =>
          hu_bd (j + N₁) z (hN₁ j z hz_ball).1 (hN₁ j z hz_ball).2
      have hsum_all := (summable_nat_add_iff (f := fun m => borelTerm P m z) N₁).1 hts
      have hm₀_mem : m₀ ∈ Finset.range N₁ := Finset.mem_range.mpr (by omega)
      have hsplit : borelPhi P z = borelTerm P m₀ z + mid z + tail z := by
        have h1 := (hsum_all.sum_add_tsum_nat_add N₁).symm
        have her := (Finset.add_sum_erase (Finset.range N₁) (fun m => borelTerm P m z) hm₀_mem).symm
        rw [borelPhi]
        exact h1.trans (by rw [her, add_assoc])
      rw [hsplit]
      have hc := hcancel z
      linear_combination hc
    refine ⟨reg₀ w + mid w + tail w, ?_⟩
    exact ((hreg₀_cont.add hmid_cont).add htail_cont).continuousWithinAt.tendsto.congr' hev.symm
  expType_plus := by
    obtain ⟨u, hu_sum, hu_bd⟩ := exists_borelTerm_majorant P
    refine ⟨∑' m : ℕ, u m, 0, tsum_nonneg fun m => by
      have := hu_bd m 0 (by simp [abs_of_pos (ωBase_pos P m)]; linarith [ωBase_pos P m])
        (by simp [abs_of_pos (ωBase_pos P m)]; linarith [ωBase_pos P m])
      exact le_trans (norm_nonneg _) this, le_rfl, fun v hv => ?_⟩
    let μ : ℂ := Complex.exp (I * ((0 + Real.pi / 6 : ℝ) : ℂ))
    have hμ_eq : μ = Complex.exp (I * ((Real.pi / 6 : ℝ) : ℂ)) := by simp [μ]
    have hμ_norm : ‖μ‖ = 1 := by
      rw [hμ_eq, show I * ((Real.pi / 6 : ℝ) : ℂ) = ((Real.pi / 6 : ℝ) : ℂ) * I by ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have hterm_bd : ∀ m : ℕ, ‖borelTerm P m (μ * (v : ℂ))‖ ≤ u m := fun m => by
      refine hu_bd m (μ * (v : ℂ)) ?_ ?_
      · rw [hμ_eq]
        have h1 := norm_sub_exp_mul_real_ge' (Real.pi / 6) (ωBase P m) v
        have hsin : |ωBase P m * Real.sin (Real.pi / 6)| = ωBase P m / 2 := by
          rw [Real.sin_pi_div_six, abs_of_pos (by have := ωBase_pos P m; positivity)]; ring
        exact hsin.symm.trans_le h1
      · rw [hμ_eq]
        have hcos : 0 ≤ Real.cos (Real.pi / 6) := by rw [Real.cos_pi_div_six]; positivity
        exact le_trans (by linarith [ωBase_pos P m]) (norm_add_exp_mul_real_ge' (Real.pi / 6) hcos hv)
    have hsn : Summable (fun m : ℕ => ‖borelTerm P m (μ * (v : ℂ))‖) :=
      hu_sum.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_bd
    change ‖μ * borelPhi P (μ * (v : ℂ))‖ ≤ (∑' m : ℕ, u m) * Real.exp (0 * v)
    rw [norm_mul, hμ_norm, one_mul, zero_mul, Real.exp_zero, mul_one, borelPhi]
    calc ‖∑' m : ℕ, borelTerm P m (μ * (v : ℂ))‖
        ≤ ∑' m : ℕ, ‖borelTerm P m (μ * (v : ℂ))‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' m : ℕ, u m := hsn.tsum_le_tsum hterm_bd hu_sum
  expType_minus := by
    obtain ⟨u, hu_sum, hu_bd⟩ := exists_borelTerm_majorant P
    refine ⟨∑' m : ℕ, u m, 0, tsum_nonneg fun m => by
      have := hu_bd m 0 (by simp [abs_of_pos (ωBase_pos P m)]; linarith [ωBase_pos P m])
        (by simp [abs_of_pos (ωBase_pos P m)]; linarith [ωBase_pos P m])
      exact le_trans (norm_nonneg _) this, le_rfl, fun v hv => ?_⟩
    let μ : ℂ := Complex.exp (I * ((0 - Real.pi / 6 : ℝ) : ℂ))
    have hμ_eq : μ = Complex.exp (I * ((-Real.pi / 6 : ℝ) : ℂ)) := by
      dsimp only [μ]; congr 2; push_cast; ring
    have hμ_norm : ‖μ‖ = 1 := by
      rw [hμ_eq, show I * ((-Real.pi / 6 : ℝ) : ℂ) = ((-Real.pi / 6 : ℝ) : ℂ) * I by ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have hterm_bd : ∀ m : ℕ, ‖borelTerm P m (μ * (v : ℂ))‖ ≤ u m := fun m => by
      refine hu_bd m (μ * (v : ℂ)) ?_ ?_
      · rw [hμ_eq]
        have h1 := norm_sub_exp_mul_real_ge' (-Real.pi / 6) (ωBase P m) v
        have hsin : |ωBase P m * Real.sin (-Real.pi / 6)| = ωBase P m / 2 := by
          rw [show (-Real.pi / 6 : ℝ) = -(Real.pi / 6) by ring, Real.sin_neg, mul_neg, abs_neg,
            Real.sin_pi_div_six, abs_of_pos (by have := ωBase_pos P m; positivity)]; ring
        exact hsin.symm.trans_le h1
      · rw [hμ_eq]
        have hcos : 0 ≤ Real.cos (-Real.pi / 6) := by
          rw [show (-Real.pi / 6 : ℝ) = -(Real.pi / 6) by ring, Real.cos_neg, Real.cos_pi_div_six]
          positivity
        exact le_trans (by linarith [ωBase_pos P m]) (norm_add_exp_mul_real_ge' (-Real.pi / 6) hcos hv)
    have hsn : Summable (fun m : ℕ => ‖borelTerm P m (μ * (v : ℂ))‖) :=
      hu_sum.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_bd
    change ‖μ * borelPhi P (μ * (v : ℂ))‖ ≤ (∑' m : ℕ, u m) * Real.exp (0 * v)
    rw [norm_mul, hμ_norm, one_mul, zero_mul, Real.exp_zero, mul_one, borelPhi]
    calc ‖∑' m : ℕ, borelTerm P m (μ * (v : ℂ))‖
        ≤ ∑' m : ℕ, ‖borelTerm P m (μ * (v : ℂ))‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' m : ℕ, u m := hsn.tsum_le_tsum hterm_bd hu_sum

/-! ### 5. Exact Formal Series Matching via Bernoulli Fourier Series & Even-Part Cancellation -/

private lemma iteratedDeriv_sub_pow_inv (w : ℂ) (p r : ℕ) (hp : 1 ≤ p) {z : ℂ} (hz : z ≠ w) :
    iteratedDeriv r (fun ζ : ℂ => ((ζ - w) ^ p)⁻¹) z =
      (-1 : ℂ) ^ r * (((p + r - 1).factorial : ℂ) / ((p - 1).factorial : ℂ)) *
        ((z - w) ^ (p + r))⁻¹ := by
  induction r generalizing z with
  | zero =>
    have hfac : ((p - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    simp [div_self hfac]
  | succ r ih =>
    have hev : iteratedDeriv r (fun ζ : ℂ => ((ζ - w) ^ p)⁻¹) =ᶠ[𝓝 z]
        fun ζ : ℂ => (-1 : ℂ) ^ r * (((p + r - 1).factorial : ℂ) / ((p - 1).factorial : ℂ)) *
          ((ζ - w) ^ (p + r))⁻¹ := by
      filter_upwards [(isOpen_ne (x := w)).mem_nhds hz] with ζ hζ
      exact ih hζ
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hzw : z - w ≠ 0 := sub_ne_zero.mpr hz
    have hpow : HasDerivAt (fun ζ : ℂ => (ζ - w) ^ (p + r))
        (((p + r : ℕ) : ℂ) * (z - w) ^ (p + r - 1)) z := by
      have h1 := ((hasDerivAt_id z).sub_const w).pow (p + r)
      refine h1.congr_deriv ?_; simp
    have hinv : HasDerivAt (fun ζ : ℂ => ((ζ - w) ^ (p + r))⁻¹)
        (-(((p + r : ℕ) : ℂ)) * ((z - w) ^ (p + (r + 1)))⁻¹) z := by
      have h1 := hpow.inv (pow_ne_zero (p + r) hzw)
      refine h1.congr_deriv ?_
      have hexp1 : (p + r - 1) + (p + (r + 1)) = 2 * (p + r) := by omega
      have hsq : ((z - w) ^ (p + r)) ^ 2 = (z - w) ^ (2 * (p + r)) := by
        rw [← pow_mul, mul_comm]
      rw [hsq, ← hexp1, pow_add]
      field_simp [pow_ne_zero (p + r - 1) hzw, pow_ne_zero (p + (r + 1)) hzw]
    rw [(hinv.const_mul _).deriv]
    have hfac_step : ((p + (r + 1) - 1).factorial : ℂ) =
        ((p + r : ℕ) : ℂ) * ((p + r - 1).factorial : ℂ) := by
      have heq : p + (r + 1) - 1 = (p + r - 1) + 1 := by omega
      rw [heq, Nat.factorial_succ]
      have heq2 : p + r - 1 + 1 = p + r := by omega
      rw [heq2]; push_cast; ring
    have hfac0 : ((p - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [hfac_step, pow_succ (-1 : ℂ) r]
    field_simp [hfac0]

private lemma iteratedDeriv_add_pow_inv (w : ℂ) (p r : ℕ) (hp : 1 ≤ p) {z : ℂ} (hz : z + w ≠ 0) :
    iteratedDeriv r (fun ζ : ℂ => ((ζ + w) ^ p)⁻¹) z =
      (-1 : ℂ) ^ r * (((p + r - 1).factorial : ℂ) / ((p - 1).factorial : ℂ)) *
        ((z + w) ^ (p + r))⁻¹ := by
  have hz' : z ≠ -w := fun h0 => hz (by rw [h0]; ring)
  have hfn : (fun ζ : ℂ => ((ζ + w) ^ p)⁻¹) = fun ζ => ((ζ - (-w)) ^ p)⁻¹ := by
    funext ζ; rw [sub_neg_eq_add]
  rw [hfn, iteratedDeriv_sub_pow_inv (-w) p r hp hz', sub_neg_eq_add]

private lemma iteratedDeriv_tsum_ball' {R : ℝ} (hR : 0 < R) (f : ℕ → ℂ → ℂ)
    (hf_an : ∀ n : ℕ, AnalyticOnNhd ℂ (f n) (Metric.ball 0 R))
    (hf_bd : ∀ k : ℕ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ (n : ℕ) (z : ℂ), z ∈ Metric.ball 0 R → ‖iteratedDeriv k (f n) z‖ ≤ u n)
    (m : ℕ) :
    iteratedDeriv m (fun z : ℂ => ∑' n : ℕ, f n z) 0 = ∑' n : ℕ, iteratedDeriv m (f n) 0 := by
  let s : Set ℂ := Metric.ball (0 : ℂ) R
  have hs_open : IsOpen s := Metric.isOpen_ball
  have h0_mem : (0 : ℂ) ∈ s := Metric.mem_ball_self hR
  have h_sum : ∀ z ∈ s, Summable (fun n : ℕ => f n z) := fun z hz => by
    obtain ⟨u, hu_sum, hu_bd⟩ := hf_bd 0
    exact hu_sum.of_norm_bounded fun n => by simpa [iteratedDeriv_zero] using hu_bd n z hz
  have h_unif : ∀ (k : ℕ), 1 ≤ k → k ≤ m →
      SummableLocallyUniformlyOn (fun n => iteratedDerivWithin k (f n) s) s := fun k _ _ => by
    obtain ⟨u, hu_sum, hu_bd⟩ := hf_bd k
    refine SummableLocallyUniformlyOn_of_locally_bounded hs_open fun K hK _ => ⟨u, hu_sum, fun n z hzK => ?_⟩
    rw [iteratedDerivWithin_of_isOpen hs_open (hK hzK)]
    exact hu_bd n z (hK hzK)
  have h_diff : ∀ (n k : ℕ) (z : ℂ), k ≤ m → z ∈ s →
      DifferentiableAt ℂ (iteratedDerivWithin k (f n) s) z := fun n k z _ hzs => by
    have hcd : ContDiffOn ℂ (⊤ : ℕ∞) (f n) s := (hf_an n).contDiffOn hs_open.uniqueDiffOn
    have hd_on : DifferentiableOn ℂ (iteratedDerivWithin k (f n) s) s :=
      hcd.differentiableOn_iteratedDerivWithin (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top k))
        hs_open.uniqueDiffOn
    exact hd_on.differentiableAt (hs_open.mem_nhds hzs)
  have h_res := iteratedDerivWithin_tsum m hs_open h0_mem h_sum h_unif h_diff
  rw [iteratedDerivWithin_of_isOpen hs_open h0_mem] at h_res
  exact h_res.trans (tsum_congr fun n => iteratedDerivWithin_of_isOpen hs_open h0_mem)

private lemma ωBase_ball_lower (P : Quasipoly) {m : ℕ} {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) (2 * Real.pi ^ 2 / (P.M : ℝ))) :
    ωBase P m / 2 ≤ ‖z - (ωBase P m : ℂ)‖ ∧ ωBase P m / 2 ≤ ‖z + (ωBase P m : ℂ)‖ := by
  have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  have hz_norm : ‖z‖ < 2 * Real.pi ^ 2 / (P.M : ℝ) := by simpa [Metric.mem_ball] using hz
  have hge := ωBase_ge_base P m
  have h24 : 4 * Real.pi ^ 2 / (P.M : ℝ) = 2 * (2 * Real.pi ^ 2 / (P.M : ℝ)) := by ring
  have hhalf : 2 * Real.pi ^ 2 / (P.M : ℝ) ≤ ωBase P m / 2 := by linarith
  have hsub : ωBase P m / 2 ≤ ‖z - (ωBase P m : ℂ)‖ := by
    have htri := norm_add_le ((ωBase P m : ℂ) - z) z
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ωBase_pos P m),
      norm_sub_rev] at htri
    linarith
  have hadd : ωBase P m / 2 ≤ ‖z + (ωBase P m : ℂ)‖ := by
    have htri := norm_add_le (z + (ωBase P m : ℂ)) (-z)
    rw [add_neg_cancel_comm, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (ωBase_pos P m)] at htri
    linarith
  exact ⟨hsub, hadd⟩

/-- Termwise derivative formula for `borelPhi P` at `ξ = 0`. -/
private lemma iteratedDeriv_borelPhi_zero (P : Quasipoly) (r : ℕ) :
    iteratedDeriv r (borelPhi P) 0 =
      ∑' m : ℕ, ∑ d : Fin (P.D + 1),
        borelPref d.1 * P.borelAmp d (m + 1) *
          ((-1 : ℂ) ^ (d.1 + 1) * (1 + (-1 : ℂ) ^ r) *
            (((d.1 + 2 + r).factorial : ℂ) / ((d.1 + 2).factorial : ℂ)) *
            ((ωBase P m : ℂ) ^ (d.1 + 3 + r))⁻¹) := by
  let R : ℝ := 2 * Real.pi ^ 2 / (P.M : ℝ)
  have hM : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  have hR : 0 < R := by dsimp only [R]; positivity
  have h_an : ∀ m : ℕ, AnalyticOnNhd ℂ (borelTerm P m) (Metric.ball 0 R) := fun m z hz => by
    obtain ⟨hsub, hadd⟩ := ωBase_ball_lower P (m := m) hz
    refine Finset.analyticAt_fun_sum Finset.univ fun d _ => ?_
    refine AnalyticAt.mul analyticAt_const (AnalyticAt.add ?_ (AnalyticAt.mul analyticAt_const ?_))
    · refine ((analyticAt_id.sub analyticAt_const).pow _).inv (pow_ne_zero _ fun h0 => ?_)
      have h0' : z - (ωBase P m : ℂ) = 0 := h0
      rw [h0', norm_zero] at hsub; linarith [ωBase_pos P m]
    · refine ((analyticAt_id.add analyticAt_const).pow _).inv (pow_ne_zero _ fun h0 => ?_)
      have h0' : z + (ωBase P m : ℂ) = 0 := h0
      rw [h0', norm_zero] at hadd; linarith [ωBase_pos P m]
  have hterm_deriv : ∀ (m k : ℕ) (z : ℂ), z ∈ Metric.ball 0 R →
      iteratedDeriv k (borelTerm P m) z =
        ∑ d : Fin (P.D + 1), borelPref d.1 * P.borelAmp d (m + 1) *
          ((-1 : ℂ) ^ k * (((d.1 + 2 + k).factorial : ℂ) / ((d.1 + 2).factorial : ℂ)) *
            (((z - (ωBase P m : ℂ)) ^ (d.1 + 3 + k))⁻¹ +
              (-1 : ℂ) ^ (d.1 + 1) * ((z + (ωBase P m : ℂ)) ^ (d.1 + 3 + k))⁻¹)) := fun m k z hz => by
    obtain ⟨hsub, hadd⟩ := ωBase_ball_lower P hz
    have hz1 : z ≠ (ωBase P m : ℂ) := fun h0 => by
      have : z - (ωBase P m : ℂ) = 0 := by rw [h0, sub_self]
      rw [this, norm_zero] at hsub; linarith [ωBase_pos P m]
    have hz2 : z + (ωBase P m : ℂ) ≠ 0 := fun h0 => by
      rw [h0, norm_zero] at hadd; linarith [ωBase_pos P m]
    unfold borelTerm
    have hcd : ∀ d ∈ (Finset.univ : Finset (Fin (P.D + 1))),
        ContDiffAt ℂ k (fun ζ : ℂ => borelPref d.1 * P.borelAmp d (m + 1) *
          (((ζ - (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹ +
            (-1 : ℂ) ^ (d.1 + 1) * ((ζ + (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹)) z := fun d _ => by
      have ha1 : AnalyticAt ℂ (fun ζ : ℂ => ((ζ - (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹) z :=
        ((analyticAt_id.sub analyticAt_const).pow _).inv (pow_ne_zero _ (sub_ne_zero.mpr hz1))
      have ha2 : AnalyticAt ℂ (fun ζ : ℂ => ((ζ + (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹) z :=
        ((analyticAt_id.add analyticAt_const).pow _).inv (pow_ne_zero _ hz2)
      exact (analyticAt_const.mul (ha1.add (analyticAt_const.mul ha2))).contDiffAt.of_le le_top
    rw [iteratedDeriv_fun_sum hcd]
    refine Finset.sum_congr rfl fun d _ => ?_
    have ha1 : ContDiffAt ℂ k (fun ζ : ℂ => ((ζ - (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹) z :=
      (((analyticAt_id.sub analyticAt_const).pow _).inv (pow_ne_zero _ (sub_ne_zero.mpr hz1))).contDiffAt.of_le le_top
    have ha2 : ContDiffAt ℂ k (fun ζ : ℂ => (-1 : ℂ) ^ (d.1 + 1) * ((ζ + (ωBase P m : ℂ)) ^ (d.1 + 3))⁻¹) z :=
      (analyticAt_const.mul (((analyticAt_id.add analyticAt_const).pow _).inv (pow_ne_zero _ hz2))).contDiffAt.of_le le_top
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_add ha1 ha2, iteratedDeriv_const_mul_field,
      iteratedDeriv_sub_pow_inv _ (d.1 + 3) k (by omega) hz1,
      iteratedDeriv_add_pow_inv _ (d.1 + 3) k (by omega) hz2]
    have hs1 : d.1 + 3 + k - 1 = d.1 + 2 + k := by omega
    have hs2 : d.1 + 3 - 1 = d.1 + 2 := by omega
    rw [hs1, hs2]
    ring
  have h_bd : ∀ k : ℕ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ (m : ℕ) (z : ℂ), z ∈ Metric.ball 0 R → ‖iteratedDeriv k (borelTerm P m) z‖ ≤ u m := fun k => by
    have hC : ∀ d : Fin (P.D + 1), ∃ C : ℝ, 0 ≤ C ∧
        ∀ m : ℕ, 1 ≤ m → ‖P.borelAmp d m‖ ≤ C * (sigmaNat (d.1 + 1) m : ℝ) :=
      fun d => P.borelAmp_norm_le d
    choose C hC_nn hC_bd using hC
    let coef : Fin (P.D + 1) → ℝ := fun d =>
      ‖borelPref d.1‖ * C d *
        (((d.1 + 2 + k).factorial : ℝ) / ((d.1 + 2).factorial : ℝ)) *
        (2 * (R ^ (d.1 + 3 + k))⁻¹)
    let u : ℕ → ℝ := fun m =>
      ∑ d : Fin (P.D + 1), coef d * ((sigmaNat (d.1 + 1) (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ (d.1 + 3))
    have hu_sum : Summable u :=
      summable_sum fun d _ => (summable_sigmaNat_div_pow_plus_two d.1).mul_left (coef d)
    refine ⟨u, hu_sum, fun m z hz => ?_⟩
    obtain ⟨hsub, hadd⟩ := ωBase_ball_lower P hz
    rw [hterm_deriv m k z hz]
    calc ‖∑ d : Fin (P.D + 1), _‖
        ≤ ∑ d : Fin (P.D + 1), ‖borelPref d.1 * P.borelAmp d (m + 1) *
            ((-1 : ℂ) ^ k * (((d.1 + 2 + k).factorial : ℂ) / ((d.1 + 2).factorial : ℂ)) *
              (((z - (ωBase P m : ℂ)) ^ (d.1 + 3 + k))⁻¹ +
                (-1 : ℂ) ^ (d.1 + 1) * ((z + (ωBase P m : ℂ)) ^ (d.1 + 3 + k))⁻¹))‖ := norm_sum_le _ _
      _ ≤ ∑ d : Fin (P.D + 1), coef d * ((sigmaNat (d.1 + 1) (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ (d.1 + 3)) := by
          refine Finset.sum_le_sum fun d _ => ?_
          have hw_half_pos : 0 < ωBase P m / 2 := by have := ωBase_pos P m; positivity
          have hinv1 : ‖((z - (ωBase P m : ℂ)) ^ (d.1 + 3 + k))⁻¹‖ ≤ ((ωBase P m / 2) ^ (d.1 + 3 + k))⁻¹ := by
            rw [norm_inv, norm_pow]
            exact inv_anti₀ (pow_pos hw_half_pos _) (pow_le_pow_left₀ hw_half_pos.le hsub _)
          have hinv2 : ‖(-1 : ℂ) ^ (d.1 + 1) * ((z + (ωBase P m : ℂ)) ^ (d.1 + 3 + k))⁻¹‖ ≤
              ((ωBase P m / 2) ^ (d.1 + 3 + k))⁻¹ := by
            rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_inv, norm_pow]
            exact inv_anti₀ (pow_pos hw_half_pos _) (pow_le_pow_left₀ hw_half_pos.le hadd _)
          have hsum_inv : ‖((z - (ωBase P m : ℂ)) ^ (d.1 + 3 + k))⁻¹ +
              (-1 : ℂ) ^ (d.1 + 1) * ((z + (ωBase P m : ℂ)) ^ (d.1 + 3 + k))⁻¹‖ ≤
              2 * ((ωBase P m / 2) ^ (d.1 + 3 + k))⁻¹ := by
            calc ‖_ + _‖ ≤ ‖((z - (ωBase P m : ℂ)) ^ (d.1 + 3 + k))⁻¹‖ +
                  ‖(-1 : ℂ) ^ (d.1 + 1) * ((z + (ωBase P m : ℂ)) ^ (d.1 + 3 + k))⁻¹‖ := norm_add_le _ _
              _ ≤ ((ωBase P m / 2) ^ (d.1 + 3 + k))⁻¹ + ((ωBase P m / 2) ^ (d.1 + 3 + k))⁻¹ :=
                  add_le_add hinv1 hinv2
              _ = 2 * ((ωBase P m / 2) ^ (d.1 + 3 + k))⁻¹ := by ring
          have hw_split : ωBase P m / 2 = R * ((m + 1 : ℕ) : ℝ) := by unfold ωBase; dsimp only [R]; ring
          have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
          have hpow_le : ((m + 1 : ℕ) : ℝ) ^ (d.1 + 3) ≤ ((m + 1 : ℕ) : ℝ) ^ (d.1 + 3 + k) :=
            pow_le_pow_right₀ hm1 (by omega)
          have hamp := hC_bd d (m + 1) (Nat.succ_pos m)
          have hCd := hC_nn d
          simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_div,
            Complex.norm_natCast]
          calc ‖borelPref d.1‖ * ‖P.borelAmp d (m + 1)‖ *
                ((((d.1 + 2 + k).factorial : ℝ) / ((d.1 + 2).factorial : ℝ)) * ‖_‖)
              ≤ ‖borelPref d.1‖ * (C d * (sigmaNat (d.1 + 1) (m + 1) : ℝ)) *
                  ((((d.1 + 2 + k).factorial : ℝ) / ((d.1 + 2).factorial : ℝ)) *
                    (2 * ((ωBase P m / 2) ^ (d.1 + 3 + k))⁻¹)) := by
                gcongr
            _ = coef d * ((sigmaNat (d.1 + 1) (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ (d.1 + 3 + k)) := by
                dsimp only [coef]
                rw [hw_split, mul_pow, mul_inv, div_eq_mul_inv]
                ring
            _ ≤ coef d * ((sigmaNat (d.1 + 1) (m + 1) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ (d.1 + 3)) := by
                have hcoef_nn : 0 ≤ coef d := by dsimp only [coef]; positivity
                gcongr
  have hts := iteratedDeriv_tsum_ball' hR (borelTerm P) h_an h_bd r
  change iteratedDeriv r (borelPhi P) 0 = _ at hts
  rw [hts]
  refine tsum_congr fun m => ?_
  rw [hterm_deriv m r 0 (Metric.mem_ball_self hR)]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hneg_pow : ((0 - (ωBase P m : ℂ)) ^ (d.1 + 3 + r))⁻¹ =
      (-1 : ℂ) ^ (d.1 + 3 + r) * ((ωBase P m : ℂ) ^ (d.1 + 3 + r))⁻¹ := by
    rw [zero_sub, show -(ωBase P m : ℂ) = (-1 : ℂ) * (ωBase P m : ℂ) by ring, mul_pow, mul_inv]
    congr 1
    rcases Nat.even_or_odd (d.1 + 3 + r) with he | ho
    · rw [he.neg_one_pow, inv_one]
    · rw [ho.neg_one_pow, inv_neg, inv_one]
  rw [hneg_pow, zero_add]
  have hsign1 : (-1 : ℂ) ^ r * (-1 : ℂ) ^ (d.1 + 3 + r) = (-1 : ℂ) ^ (d.1 + 1) := by
    rw [← pow_add, show r + (d.1 + 3 + r) = (d.1 + 1) + 2 * (r + 1) by omega, pow_add, pow_mul]
    norm_num
  have hsign2 : (-1 : ℂ) ^ r * (-1 : ℂ) ^ (d.1 + 1) = (-1 : ℂ) ^ (d.1 + 1) * (-1 : ℂ) ^ r := mul_comm _ _
  linear_combination
    (borelPref d.1 * P.borelAmp d (m + 1) * (((d.1 + 2 + r).factorial : ℂ) / ((d.1 + 2).factorial : ℂ)) *
      ((ωBase P m : ℂ) ^ (d.1 + 3 + r))⁻¹) * hsign1

/-- Odd-order derivatives of `borelPhi P` at `0` vanish identically. -/
private lemma iteratedDeriv_borelPhi_zero_odd (P : Quasipoly) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (borelPhi P) 0 = 0 := by
  rw [iteratedDeriv_borelPhi_zero]
  have hterm0 : ∀ m : ℕ, ∑ d : Fin (P.D + 1),
      borelPref d.1 * P.borelAmp d (m + 1) *
        ((-1 : ℂ) ^ (d.1 + 1) * (1 + (-1 : ℂ) ^ (2 * k + 1)) *
          (((d.1 + 2 + (2 * k + 1)).factorial : ℂ) / ((d.1 + 2).factorial : ℂ)) *
          ((ωBase P m : ℂ) ^ (d.1 + 3 + (2 * k + 1)))⁻¹) = 0 := fun m => by
    refine Finset.sum_eq_zero fun d _ => ?_
    have hodd : (-1 : ℂ) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [hodd]; ring
  simp_rw [hterm0]
  exact tsum_zero

/-- Even-part cancellation: `∑_{r=1}^M cEven d r * B_{2j+d+1}(r/M) = 0` for all `j ≥ 1`. -/
private lemma sum_cEven_bernoulliFun_eq_zero (P : Quasipoly) (d : Fin (P.D + 1)) {j : ℕ} (hj : 1 ≤ j) :
    ∑ r ∈ Finset.Icc 1 P.M,
      P.cEven d r * ((bernoulliFun (2 * j + d.1 + 1) ((r : ℝ) / (P.M : ℝ)) : ℝ) : ℂ) = 0 := by
  have hMpos := P.hM
  have hsplit : Finset.Icc 1 P.M = insert P.M (Finset.Ico 1 P.M) := by
    ext r; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  -- Boundary term `r = M`: `r / M = 1`.
  have hM_term : P.cEven d P.M *
      ((bernoulliFun (2 * j + d.1 + 1) ((P.M : ℝ) / (P.M : ℝ)) : ℝ) : ℂ) = 0 := by
    have hMne : (P.M : ℝ) ≠ 0 := by exact_mod_cast P.hM.ne'
    rw [div_self hMne, bernoulliFun_endpoints_eq_of_ne_one (by omega), bernoulliFun_eval_zero]
    rcases Nat.even_or_odd d.1 with he | ho
    · have hodd_idx : Odd (2 * j + d.1 + 1) := by
        obtain ⟨t, ht⟩ := he; exact ⟨j + t, by omega⟩
      rw [bernoulli_eq_zero_of_odd hodd_idx (by omega)]; simp
    · rw [P.cEven_M_of_odd d ho, zero_mul]
  rw [hM_term, zero_add]
  -- Interior sum `r ∈ Ico 1 M`: pairing `r ↦ M - r` negates the sum!
  let S : ℂ := ∑ r ∈ Finset.Ico 1 P.M,
    P.cEven d r * ((bernoulliFun (2 * j + d.1 + 1) ((r : ℝ) / (P.M : ℝ)) : ℝ) : ℂ)
  have hneg : S = -S := by
    dsimp only [S]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun r _ => P.M - r) ?_ ?_ ?_ ?_
    · intro r hr; simp only [Finset.mem_Ico] at hr ⊢; omega
    · intro a ha b hb hab; simp only [Finset.mem_Ico] at ha hb; omega
    · intro r hr; simp only [Finset.mem_Ico] at hr
      exact ⟨P.M - r, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro r hr
      simp only [Finset.mem_Ico] at hr
      have hMne : (P.M : ℝ) ≠ 0 := by exact_mod_cast P.hM.ne'
      have hsub_div : ((P.M - r : ℕ) : ℝ) / (P.M : ℝ) = 1 - (((r : ℚ) / (P.M : ℚ) : ℚ) : ℝ) := by
        rw [Nat.cast_sub hr.2.le]; push_cast; field_simp [hMne]
      have hrat : (r : ℝ) / (P.M : ℝ) = (((r : ℚ) / (P.M : ℚ) : ℚ) : ℝ) := by push_cast; rfl
      rw [P.cEven_reflect d hr.1 hr.2.le, hsub_div,
        bernoulliFun_one_sub_rat (2 * j + d.1 + 1) ((r : ℚ) / (P.M : ℚ)), ← hrat]
      push_cast
      have hpow : (-1 : ℂ) ^ d.1 * (-1 : ℂ) ^ (2 * j + d.1 + 1) = -1 := by
        rw [← pow_add, show d.1 + (2 * j + d.1 + 1) = 2 * (j + d.1) + 1 by omega, pow_succ,
          pow_mul]; norm_num
      linear_combination (P.cEven d r * ((bernoulliFun (2 * j + d.1 + 1) ((r : ℝ) / (P.M : ℝ)) : ℝ) : ℂ)) * hpow
  have h2S : (2 : ℂ) * S = 0 := by linear_combination hneg
  exact (mul_eq_zero.mp h2S).resolve_left (by norm_num)

/-- Trigonometric parity of `cOdd d`: expresses `cDft P d k` as a pure cosine sum (for `d` odd)
or pure `-i * sin` sum (for `d` even). -/
private lemma sum_cOdd_cos_eq_zero_of_even (P : Quasipoly) (d : Fin (P.D + 1)) (heven : Even d.1) (k : ℕ) :
    ∑ r ∈ Finset.Icc 1 P.M,
      P.cOdd d r * (Real.cos (2 * Real.pi * (k : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ) = 0 := by
  have hMpos := P.hM
  have hsplit : Finset.Icc 1 P.M = insert P.M (Finset.Ico 1 P.M) := by
    ext r; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
  rw [hsplit, Finset.sum_insert (by simp), P.cOdd_M_of_even d heven, zero_mul, zero_add]
  let S : ℂ := ∑ r ∈ Finset.Ico 1 P.M,
    P.cOdd d r * (Real.cos (2 * Real.pi * (k : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ)
  have hneg : S = -S := by
    dsimp only [S]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun r _ => P.M - r) ?_ ?_ ?_ ?_
    · intro r hr; simp only [Finset.mem_Ico] at hr ⊢; omega
    · intro a ha b hb hab; simp only [Finset.mem_Ico] at ha hb; omega
    · intro r hr; simp only [Finset.mem_Ico] at hr
      exact ⟨P.M - r, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro r hr
      simp only [Finset.mem_Ico] at hr
      have hMne : (P.M : ℝ) ≠ 0 := by exact_mod_cast P.hM.ne'
      have hcos : Real.cos (2 * Real.pi * (k : ℝ) * (((P.M - r : ℕ) : ℝ) / (P.M : ℝ))) =
          Real.cos (2 * Real.pi * (k : ℝ) * ((r : ℝ) / (P.M : ℝ))) := by
        have harg : 2 * Real.pi * (k : ℝ) * (((P.M - r : ℕ) : ℝ) / (P.M : ℝ)) =
            -(2 * Real.pi * (k : ℝ) * ((r : ℝ) / (P.M : ℝ))) + (k : ℤ) * (2 * Real.pi) := by
          rw [Nat.cast_sub hr.2.le]; push_cast; field_simp [hMne]; ring
        rw [harg, Real.cos_add_int_mul_two_pi, Real.cos_neg]
      rw [P.cOdd_reflect d hr.1 hr.2.le, heven.neg_one_pow, hcos]
      ring
  have h2S : (2 : ℂ) * S = 0 := by linear_combination hneg
  exact (mul_eq_zero.mp h2S).resolve_left (by norm_num)

private lemma sum_cOdd_sin_eq_zero_of_odd (P : Quasipoly) (d : Fin (P.D + 1)) (hodd : Odd d.1) (k : ℕ) :
    ∑ r ∈ Finset.Icc 1 P.M,
      P.cOdd d r * (Real.sin (2 * Real.pi * (k : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ) = 0 := by
  have hMpos := P.hM
  have hsplit : Finset.Icc 1 P.M = insert P.M (Finset.Ico 1 P.M) := by
    ext r; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have hMne : (P.M : ℝ) ≠ 0 := by exact_mod_cast P.hM.ne'
  have hsinM : Real.sin (2 * Real.pi * (k : ℝ) * ((P.M : ℝ) / (P.M : ℝ))) = 0 := by
    rw [div_self hMne, mul_one, show 2 * Real.pi * (k : ℝ) = ((2 * (k : ℤ) : ℤ) : ℝ) * Real.pi by
      push_cast; ring]
    exact Real.sin_int_mul_pi (2 * (k : ℤ))
  rw [hsinM, Complex.ofReal_zero, mul_zero, zero_add]
  let S : ℂ := ∑ r ∈ Finset.Ico 1 P.M,
    P.cOdd d r * (Real.sin (2 * Real.pi * (k : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ)
  have hneg : S = -S := by
    dsimp only [S]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun r _ => P.M - r) ?_ ?_ ?_ ?_
    · intro r hr; simp only [Finset.mem_Ico] at hr ⊢; omega
    · intro a ha b hb hab; simp only [Finset.mem_Ico] at ha hb; omega
    · intro r hr; simp only [Finset.mem_Ico] at hr
      exact ⟨P.M - r, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro r hr
      simp only [Finset.mem_Ico] at hr
      have hsin : Real.sin (2 * Real.pi * (k : ℝ) * (((P.M - r : ℕ) : ℝ) / (P.M : ℝ))) =
          -Real.sin (2 * Real.pi * (k : ℝ) * ((r : ℝ) / (P.M : ℝ))) := by
        have harg : 2 * Real.pi * (k : ℝ) * (((P.M - r : ℕ) : ℝ) / (P.M : ℝ)) =
            -(2 * Real.pi * (k : ℝ) * ((r : ℝ) / (P.M : ℝ))) + (k : ℤ) * (2 * Real.pi) := by
          rw [Nat.cast_sub hr.2.le]; push_cast; field_simp [hMne]; ring
        rw [harg, Real.sin_add_int_mul_two_pi, Real.sin_neg]
      rw [P.cOdd_reflect d hr.1 hr.2.le, hodd.neg_one_pow, hsin]
      push_cast; ring
  have h2S : (2 : ℂ) * S = 0 := by linear_combination hneg
  exact (mul_eq_zero.mp h2S).resolve_left (by norm_num)

/-- Unified Bernoulli–Fourier identity for the odd part `cOdd d` (verified to > 50 dps). -/
private lemma sum_cOdd_bernoulliFun_eq_tsum_cDft (P : Quasipoly) (d : Fin (P.D + 1)) {j : ℕ} (hj : 1 ≤ j) :
    -(∑ r ∈ Finset.Icc 1 P.M,
        P.cOdd d r * (P.M : ℂ) ^ (2 * j + d.1) *
          (((bernoulliFun (2 * j + d.1 + 1) ((r : ℝ) / (P.M : ℝ)) : ℝ) : ℂ) /
            ((2 * j + d.1 + 1 : ℕ) : ℂ))) =
      (-1 : ℂ) ^ j * I ^ (d.1 + 1) * 2 *
        (((2 * j + d.1).factorial : ℂ) / (d.1.factorial : ℂ)) *
        ((P.M : ℂ) / (2 * (Real.pi : ℂ))) ^ (2 * j + d.1 + 1) *
        ∑' k : ℕ, P.cDft d (k + 1) / ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1) := by
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hMne : (P.M : ℂ) ≠ 0 := by exact_mod_cast P.hM.ne'
  have hfac_d : (d.1.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hfac_m : ((2 * j + d.1 + 1).factorial : ℂ) =
      ((2 * j + d.1 + 1 : ℕ) : ℂ) * ((2 * j + d.1).factorial : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hm_ne : ((2 * j + d.1 + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * j + d.1)
  have h_r_mem : ∀ r ∈ Finset.Icc 1 P.M, ((r : ℝ) / (P.M : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := fun r hr => by
    have hrb := Finset.mem_Icc.mp hr
    have hMpos : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
    exact ⟨by positivity, (div_le_one hMpos).mpr (by exact_mod_cast hrb.2)⟩
  rcases Nat.even_or_odd d.1 with ⟨a, ha⟩ | ⟨a, ha⟩
  · -- Even `d = 2 * a`: use `hasSum_one_div_nat_pow_mul_sin` at `k_idx = j + a`.
    have hd_eq : d.1 = 2 * a := by omega
    have hm_eq : 2 * j + d.1 + 1 = 2 * (j + a) + 1 := by omega
    have hja : j + a ≠ 0 := by omega
    have hB_sin : ∀ r ∈ Finset.Icc 1 P.M,
        ((bernoulliFun (2 * j + d.1 + 1) ((r : ℝ) / (P.M : ℝ)) : ℝ) : ℂ) =
          (-1 : ℂ) ^ (j + a + 1) * 2 * ((2 * j + d.1 + 1).factorial : ℂ) /
            (2 * (Real.pi : ℂ)) ^ (2 * j + d.1 + 1) *
            ∑' k : ℕ, (Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ) /
              ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1) := fun r hr => by
      have hs := hasSum_one_div_nat_pow_mul_sin hja (h_r_mem r hr)
      have hs_shift : HasSum (fun k : ℕ =>
          1 / ((k + 1 : ℕ) : ℝ) ^ (2 * (j + a) + 1) *
            Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))))
          ((-1 : ℝ) ^ (j + a + 1) * (2 * Real.pi) ^ (2 * (j + a) + 1) / 2 /
            ((2 * (j + a) + 1).factorial : ℝ) *
            bernoulliFun (2 * (j + a) + 1) ((r : ℝ) / (P.M : ℝ))) := by
        have h0 : 1 / ((0 : ℕ) : ℝ) ^ (2 * (j + a) + 1) *
            Real.sin (2 * Real.pi * ((0 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) = 0 := by simp
        have h1 := (hasSum_nat_add_iff' 1).mpr hs
        simpa [Finset.sum_range_one, h0, bernoulliFun] using h1
      have hts := congrArg (fun x : ℝ => (x : ℂ)) hs_shift.tsum_eq
      rw [Complex.ofReal_tsum] at hts
      have hts' : (∑' k : ℕ, (Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ) /
            ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1)) =
          (-1 : ℂ) ^ (j + a + 1) * (2 * (Real.pi : ℂ)) ^ (2 * j + d.1 + 1) / 2 /
            ((2 * j + d.1 + 1).factorial : ℂ) *
            ((bernoulliFun (2 * j + d.1 + 1) ((r : ℝ) / (P.M : ℝ)) : ℝ) : ℂ) := by
        rw [hm_eq]
        refine (tsum_congr fun k => ?_).trans (by push_cast at hts; exact hts)
        push_cast; ring
      rw [hts']
      have hfac_ne : ((2 * j + d.1 + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hsq : (-1 : ℂ) ^ (j + a + 1) * (-1 : ℂ) ^ (j + a + 1) = 1 := by rw [← mul_pow]; norm_num
      field_simp [hpi, hfac_ne]
      linear_combination -((bernoulliFun (2 * j + d.1 + 1) ((r : ℝ) / (P.M : ℝ)) : ℝ) : ℂ) * hsq
    have hsumm_r : ∀ r ∈ Finset.Icc 1 P.M,
        Summable (fun k : ℕ => P.cOdd d r *
          ((Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ) /
            ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1))) := fun r _ => by
      refine ((summable_one_div_nat_pow_succ (p := 2 * j + d.1 + 1) (by omega)).mul_left ‖P.cOdd d r‖).of_norm_bounded fun k => ?_
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow, Complex.norm_natCast,
        div_eq_mul_inv]
      have hsin1 : |Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ)))| ≤ 1 :=
        Real.abs_sin_le_one _
      calc ‖P.cOdd d r‖ * (|Real.sin _| * (((k + 1 : ℕ) : ℝ) ^ (2 * j + d.1 + 1))⁻¹)
          ≤ ‖P.cOdd d r‖ * (1 * (((k + 1 : ℕ) : ℝ) ^ (2 * j + d.1 + 1))⁻¹) := by gcongr
        _ = ‖P.cOdd d r‖ * (((k + 1 : ℕ) : ℝ) ^ (2 * j + d.1 + 1))⁻¹ := by ring
    have hswap : (∑ r ∈ Finset.Icc 1 P.M, P.cOdd d r *
        ∑' k : ℕ, (Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ) /
          ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1)) =
        I * ((P.M : ℂ) / (d.1.factorial : ℂ)) *
          ∑' k : ℕ, P.cDft d (k + 1) / ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1) := by
      simp_rw [← tsum_mul_left]
      rw [← Summable.tsum_finsetSum hsumm_r]
      refine tsum_congr fun k => ?_
      have h_exp_sin : ∑ r ∈ Finset.Icc 1 P.M, P.cOdd d r *
          Complex.exp (-((2 * Real.pi * (r : ℝ) * ((k + 1 : ℕ) : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I) =
          -I * ∑ r ∈ Finset.Icc 1 P.M,
            P.cOdd d r * (Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ) := by
        have hcos0 := sum_cOdd_cos_eq_zero_of_even P d ⟨a, by omega⟩ (k + 1)
        have hterm : ∀ r ∈ Finset.Icc 1 P.M,
            P.cOdd d r * Complex.exp (-((2 * Real.pi * (r : ℝ) * ((k + 1 : ℕ) : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I) =
            P.cOdd d r * (Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ) -
            I * (P.cOdd d r * (Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ)) := fun r _ => by
          have harg : -((2 * Real.pi * (r : ℝ) * ((k + 1 : ℕ) : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I =
              (-(2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ)) : ℝ) : ℂ) * I := by
            push_cast; ring
          rw [harg, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
            ← Complex.ofReal_cos, ← Complex.ofReal_sin]
          ring
        rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hcos0, zero_sub, ← Finset.mul_sum]
        ring
      have hdft_k : P.cDft d (k + 1) =
          ((d.1.factorial : ℂ) / (P.M : ℂ)) * (-I * ∑ r ∈ Finset.Icc 1 P.M,
            P.cOdd d r * (Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ)) := by
        rw [Quasipoly.cDft, h_exp_sin]
      rw [hdft_k]
      have hI2 : I * I = -1 := Complex.I_mul_I
      have hden : ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1) ≠ 0 :=
        pow_ne_zero _ (by exact_mod_cast Nat.succ_ne_zero k)
      have hsum_eq : ∑ r ∈ Finset.Icc 1 P.M,
            P.cOdd d r * ((Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ) /
              ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1)) =
          (∑ r ∈ Finset.Icc 1 P.M,
            P.cOdd d r * (Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ)) /
            ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1) := by
        rw [Finset.sum_div]; refine Finset.sum_congr rfl fun r _ => by ring
      rw [hsum_eq]
      generalize (∑ r ∈ Finset.Icc 1 P.M,
        P.cOdd d r * (Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ)) = S
      field_simp [hMne, hfac_d, hden]
      linear_combination S * hI2
    have hLHS : -(∑ r ∈ Finset.Icc 1 P.M,
          P.cOdd d r * (P.M : ℂ) ^ (2 * j + d.1) *
            (((bernoulliFun (2 * j + d.1 + 1) ((r : ℝ) / (P.M : ℝ)) : ℝ) : ℂ) /
              ((2 * j + d.1 + 1 : ℕ) : ℂ))) =
        -((P.M : ℂ) ^ (2 * j + d.1) * (-1 : ℂ) ^ (j + a + 1) * 2 * ((2 * j + d.1 + 1).factorial : ℂ) /
          (((2 * j + d.1 + 1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ)) ^ (2 * j + d.1 + 1))) *
          (∑ r ∈ Finset.Icc 1 P.M, P.cOdd d r *
            ∑' k : ℕ, (Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ) /
              ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [hB_sin r hr]; ring
    rw [hLHS, hswap, hfac_m, div_pow, pow_succ (P.M : ℂ) (2 * j + d.1)]
    have hIpow : I ^ (d.1 + 1) = (-1 : ℂ) ^ a * I := by
      rw [hd_eq, pow_succ, pow_mul, Complex.I_sq]
    rw [hIpow, pow_add (-1 : ℂ) (j + a) 1, pow_add (-1 : ℂ) j a, pow_one]
    field_simp [hm_ne, hpi, hfac_d]
  · -- Odd `d = 2 * a + 1`: use `hasSum_one_div_nat_pow_mul_cos` at `k_idx = j + a + 1`.
    have hd_eq : d.1 = 2 * a + 1 := by omega
    have hm_eq : 2 * j + d.1 + 1 = 2 * (j + a + 1) := by omega
    have hja : j + a + 1 ≠ 0 := by omega
    have hB_cos : ∀ r ∈ Finset.Icc 1 P.M,
        ((bernoulliFun (2 * j + d.1 + 1) ((r : ℝ) / (P.M : ℝ)) : ℝ) : ℂ) =
          (-1 : ℂ) ^ (j + a + 2) * 2 * ((2 * j + d.1 + 1).factorial : ℂ) /
            (2 * (Real.pi : ℂ)) ^ (2 * j + d.1 + 1) *
            ∑' k : ℕ, (Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ) /
              ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1) := fun r hr => by
      have hs := hasSum_one_div_nat_pow_mul_cos hja (h_r_mem r hr)
      have hs_shift : HasSum (fun k : ℕ =>
          1 / ((k + 1 : ℕ) : ℝ) ^ (2 * (j + a + 1)) *
            Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))))
          ((-1 : ℝ) ^ (j + a + 1 + 1) * (2 * Real.pi) ^ (2 * (j + a + 1)) / 2 /
            ((2 * (j + a + 1)).factorial : ℝ) *
            bernoulliFun (2 * (j + a + 1)) ((r : ℝ) / (P.M : ℝ))) := by
        have h0 : 1 / ((0 : ℕ) : ℝ) ^ (2 * (j + a + 1)) *
            Real.cos (2 * Real.pi * ((0 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) = 0 := by
          simp [zero_pow (by omega : 2 * (j + a + 1) ≠ 0)]
        have h1 := (hasSum_nat_add_iff' 1).mpr hs
        simpa [Finset.sum_range_one, h0, bernoulliFun] using h1
      have hts := congrArg (fun x : ℝ => (x : ℂ)) hs_shift.tsum_eq
      rw [Complex.ofReal_tsum] at hts
      have hts' : (∑' k : ℕ, (Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ) /
            ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1)) =
          (-1 : ℂ) ^ (j + a + 2) * (2 * (Real.pi : ℂ)) ^ (2 * j + d.1 + 1) / 2 /
            ((2 * j + d.1 + 1).factorial : ℂ) *
            ((bernoulliFun (2 * j + d.1 + 1) ((r : ℝ) / (P.M : ℝ)) : ℝ) : ℂ) := by
        rw [hm_eq]
        refine (tsum_congr fun k => ?_).trans (by push_cast at hts; exact hts)
        push_cast; ring
      rw [hts']
      have hfac_ne : ((2 * j + d.1 + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hsq : (-1 : ℂ) ^ (j + a + 2) * (-1 : ℂ) ^ (j + a + 2) = 1 := by rw [← mul_pow]; norm_num
      field_simp [hpi, hfac_ne]
      linear_combination -((bernoulliFun (2 * j + d.1 + 1) ((r : ℝ) / (P.M : ℝ)) : ℝ) : ℂ) * hsq
    have hsumm_r : ∀ r ∈ Finset.Icc 1 P.M,
        Summable (fun k : ℕ => P.cOdd d r *
          ((Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ) /
            ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1))) := fun r _ => by
      refine ((summable_one_div_nat_pow_succ (p := 2 * j + d.1 + 1) (by omega)).mul_left ‖P.cOdd d r‖).of_norm_bounded fun k => ?_
      rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow, Complex.norm_natCast,
        div_eq_mul_inv]
      have hcos1 : |Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ)))| ≤ 1 :=
        Real.abs_cos_le_one _
      calc ‖P.cOdd d r‖ * (|Real.cos _| * (((k + 1 : ℕ) : ℝ) ^ (2 * j + d.1 + 1))⁻¹)
          ≤ ‖P.cOdd d r‖ * (1 * (((k + 1 : ℕ) : ℝ) ^ (2 * j + d.1 + 1))⁻¹) := by gcongr
        _ = ‖P.cOdd d r‖ * (((k + 1 : ℕ) : ℝ) ^ (2 * j + d.1 + 1))⁻¹ := by ring
    have hswap : (∑ r ∈ Finset.Icc 1 P.M, P.cOdd d r *
        ∑' k : ℕ, (Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ) /
          ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1)) =
        ((P.M : ℂ) / (d.1.factorial : ℂ)) *
          ∑' k : ℕ, P.cDft d (k + 1) / ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1) := by
      simp_rw [← tsum_mul_left]
      rw [← Summable.tsum_finsetSum hsumm_r]
      refine tsum_congr fun k => ?_
      have h_exp_cos : ∑ r ∈ Finset.Icc 1 P.M, P.cOdd d r *
          Complex.exp (-((2 * Real.pi * (r : ℝ) * ((k + 1 : ℕ) : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I) =
          ∑ r ∈ Finset.Icc 1 P.M,
            P.cOdd d r * (Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ) := by
        have hsin0 := sum_cOdd_sin_eq_zero_of_odd P d ⟨a, by omega⟩ (k + 1)
        have hterm : ∀ r ∈ Finset.Icc 1 P.M,
            P.cOdd d r * Complex.exp (-((2 * Real.pi * (r : ℝ) * ((k + 1 : ℕ) : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I) =
            P.cOdd d r * (Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ) -
            I * (P.cOdd d r * (Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ)) := fun r _ => by
          have harg : -((2 * Real.pi * (r : ℝ) * ((k + 1 : ℕ) : ℝ) / (P.M : ℝ) : ℝ) : ℂ) * I =
              (-(2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ)) : ℝ) : ℂ) * I := by
            push_cast; ring
          rw [harg, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
            ← Complex.ofReal_cos, ← Complex.ofReal_sin]
          ring
        rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hsin0, mul_zero,
          sub_zero]
      have hdft_k : P.cDft d (k + 1) =
          ((d.1.factorial : ℂ) / (P.M : ℂ)) * ∑ r ∈ Finset.Icc 1 P.M,
            P.cOdd d r * (Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ) := by
        rw [Quasipoly.cDft, h_exp_cos]
      rw [hdft_k]
      have hden : ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1) ≠ 0 :=
        pow_ne_zero _ (by exact_mod_cast Nat.succ_ne_zero k)
      have hsum_eq : ∑ r ∈ Finset.Icc 1 P.M,
            P.cOdd d r * ((Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ) /
              ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1)) =
          (∑ r ∈ Finset.Icc 1 P.M,
            P.cOdd d r * (Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ)) /
            ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1) := by
        rw [Finset.sum_div]; refine Finset.sum_congr rfl fun r _ => by ring
      rw [hsum_eq]
      field_simp [hMne, hfac_d, hden]
    have hLHS : -(∑ r ∈ Finset.Icc 1 P.M,
          P.cOdd d r * (P.M : ℂ) ^ (2 * j + d.1) *
            (((bernoulliFun (2 * j + d.1 + 1) ((r : ℝ) / (P.M : ℝ)) : ℝ) : ℂ) /
              ((2 * j + d.1 + 1 : ℕ) : ℂ))) =
        -((P.M : ℂ) ^ (2 * j + d.1) * (-1 : ℂ) ^ (j + a + 2) * 2 * ((2 * j + d.1 + 1).factorial : ℂ) /
          (((2 * j + d.1 + 1 : ℕ) : ℂ) * (2 * (Real.pi : ℂ)) ^ (2 * j + d.1 + 1))) *
          (∑ r ∈ Finset.Icc 1 P.M, P.cOdd d r *
            ∑' k : ℕ, (Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * ((r : ℝ) / (P.M : ℝ))) : ℂ) /
              ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [hB_cos r hr]; ring
    rw [hLHS, hswap, hfac_m, div_pow, pow_succ (P.M : ℂ) (2 * j + d.1)]
    have hIpow : I ^ (d.1 + 1) = (-1 : ℂ) ^ (a + 1) := by
      rw [hd_eq, show 2 * a + 1 + 1 = 2 * (a + 1) by omega, pow_mul, Complex.I_sq]
    have hsign : -((-1 : ℂ) ^ (j + a + 2)) = (-1 : ℂ) ^ j * (-1 : ℂ) ^ (a + 1) := by
      rw [← pow_add, show j + (a + 1) = j + a + 1 by omega,
        show j + a + 2 = (j + a + 1) + 1 by omega, pow_succ]
      ring
    rw [hIpow]
    field_simp [hm_ne, hpi, hfac_d]
    linear_combination
      (2 * ((2 * j + d.1).factorial : ℂ) * (P.M : ℂ) ^ (2 * j + d.1) * (P.M : ℂ) *
        ∑' k : ℕ, P.cDft d (k + 1) / ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1)) * hsign

/-- Shifted Euler–Maclaurin tail series for a single `(d, r)` residue class after removing the
`n < d + 2` terms and shifting down by `X^{d + 1}` (so `[X^0] = 0` and `[X^m]` for `m ≥ 1`
equals `M^{d + 1 + m} * emTermShift (r/M) (hPow d) (d + 1 + m)`). -/
@[expose] def tailSeriesDR (P : Quasipoly) (d : Fin (P.D + 1)) (r : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun m =>
    if m = 0 then 0
    else (P.M : ℂ) ^ (d.1 + 1 + m) *
      emTermShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) (d.1 + 1 + m)

/-- **Master Formal Series Identity**:
`formalSeries (borelPhi P)` equals the weighted sum of all shifted Euler–Maclaurin tail series
`∑_{d=0}^D ∑_{r=1}^M P.c d r * tailSeriesDR P d r`! -/
theorem formalSeries_borelPhi (P : Quasipoly) :
    formalSeries (borelPhi P) =
      ∑ d : Fin (P.D + 1), ∑ r ∈ Finset.Icc 1 P.M,
        PowerSeries.C (P.c d r) * tailSeriesDR P d r := by
  ext n
  cases n with
  | zero =>
    simp [formalSeries, tailSeriesDR, map_sum, PowerSeries.coeff_C_mul]
  | succ m =>
    have hL : PowerSeries.coeff (m + 1) (formalSeries (borelPhi P)) = iteratedDeriv m (borelPhi P) 0 := by
      simp [formalSeries]
    rw [hL, map_sum]
    simp_rw [map_sum, PowerSeries.coeff_C_mul, tailSeriesDR, PowerSeries.coeff_mk,
      ite_eq_right_iff.mpr fun h => (Nat.succ_ne_zero m h).elim]
    rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- Even `m = 2 * k`: let `j = k + 1 ≥ 1`, so `m + 1 = 2 * j - 1`.
      have hm_eq : m = 2 * k := by omega
      subst hm_eq
      let j : ℕ := k + 1
      have hj : 1 ≤ j := Nat.succ_pos k
      have hLHS_sum : iteratedDeriv (2 * k) (borelPhi P) 0 =
          ∑ d : Fin (P.D + 1),
            borelPref d.1 *
              (2 * (-1 : ℂ) ^ (d.1 + 1) *
                (((2 * j + d.1).factorial : ℂ) / ((d.1 + 2).factorial : ℂ)) *
                ((P.M : ℂ) / (4 * (Real.pi : ℂ) ^ 2)) ^ (2 * j + d.1 + 1)) *
              ∑' n : ℕ, P.borelAmp d (n + 1) / ((n + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1) := by
        rw [iteratedDeriv_borelPhi_zero]
        have hsumm_d : ∀ d ∈ (Finset.univ : Finset (Fin (P.D + 1))),
            Summable (fun n : ℕ => borelPref d.1 * P.borelAmp d (n + 1) *
              ((-1 : ℂ) ^ (d.1 + 1) * (1 + (-1 : ℂ) ^ (2 * k)) *
                (((d.1 + 2 + 2 * k).factorial : ℂ) / ((d.1 + 2).factorial : ℂ)) *
                ((ωBase P n : ℂ) ^ (d.1 + 3 + 2 * k))⁻¹)) := fun d _ => by
          obtain ⟨C, hC, hCbd⟩ := P.borelAmp_norm_le d
          have hMpos : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
          let c0 : ℝ := ‖borelPref d.1‖ * C * 2 *
            (((d.1 + 2 + 2 * k).factorial : ℝ) / ((d.1 + 2).factorial : ℝ)) *
            ((P.M : ℝ) / (4 * Real.pi ^ 2)) ^ (d.1 + 3 + 2 * k)
          refine ((summable_sigmaNat_div_pow_plus_two d.1).mul_left c0).of_norm_bounded fun n => ?_
          have hev : (-1 : ℂ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
          have hw_eq : (ωBase P n : ℂ) = ((4 * (Real.pi : ℂ) ^ 2) / (P.M : ℂ)) * ((n + 1 : ℕ) : ℂ) := by
            unfold ωBase; push_cast; ring
          have hm1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          have hpow_le : ((n + 1 : ℕ) : ℝ) ^ (d.1 + 3) ≤ ((n + 1 : ℕ) : ℝ) ^ (d.1 + 3 + 2 * k) :=
            pow_le_pow_right₀ hm1 (by omega)
          have h11 : ‖(1 + (1 : ℂ))‖ = 2 := by norm_num
          rw [hev, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_neg, norm_one,
            one_pow, one_mul, h11, norm_div, Complex.norm_natCast, Complex.norm_natCast, norm_inv,
            norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ωBase_pos P n)]
          have hwR : (ωBase P n)⁻¹ ^ (d.1 + 3 + 2 * k) =
              ((P.M : ℝ) / (4 * Real.pi ^ 2)) ^ (d.1 + 3 + 2 * k) *
                (((n + 1 : ℕ) : ℝ) ^ (d.1 + 3 + 2 * k))⁻¹ := by
            unfold ωBase; rw [inv_div, div_pow, mul_pow, div_pow, div_eq_mul_inv, mul_inv, div_eq_mul_inv]
            ring
          rw [← inv_pow, hwR]
          have hamp := hCbd (n + 1) (Nat.succ_pos n)
          calc ‖borelPref d.1‖ * ‖P.borelAmp d (n + 1)‖ *
                (2 * (((d.1 + 2 + 2 * k).factorial : ℝ) / ((d.1 + 2).factorial : ℝ)) *
                  (((P.M : ℝ) / (4 * Real.pi ^ 2)) ^ (d.1 + 3 + 2 * k) *
                    (((n + 1 : ℕ) : ℝ) ^ (d.1 + 3 + 2 * k))⁻¹))
              ≤ ‖borelPref d.1‖ * (C * (sigmaNat (d.1 + 1) (n + 1) : ℝ)) *
                  (2 * (((d.1 + 2 + 2 * k).factorial : ℝ) / ((d.1 + 2).factorial : ℝ)) *
                    (((P.M : ℝ) / (4 * Real.pi ^ 2)) ^ (d.1 + 3 + 2 * k) *
                      (((n + 1 : ℕ) : ℝ) ^ (d.1 + 3 + 2 * k))⁻¹)) := by gcongr
            _ = c0 * ((sigmaNat (d.1 + 1) (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (d.1 + 3 + 2 * k)) := by
                dsimp only [c0]; rw [div_eq_mul_inv]; ring
            _ ≤ c0 * ((sigmaNat (d.1 + 1) (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (d.1 + 3)) := by
                have hc0 : 0 ≤ c0 := by dsimp only [c0]; positivity
                gcongr
        rw [Summable.tsum_finsetSum hsumm_d]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← tsum_mul_left]
        refine tsum_congr fun n => ?_
        have hev : (-1 : ℂ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
        have h1 : d.1 + 2 + 2 * k = 2 * j + d.1 := by dsimp [j]; omega
        have h2 : d.1 + 3 + 2 * k = 2 * j + d.1 + 1 := by dsimp [j]; omega
        have hw_inv : ((ωBase P n : ℂ) ^ (2 * j + d.1 + 1))⁻¹ =
            ((P.M : ℂ) / (4 * (Real.pi : ℂ) ^ 2)) ^ (2 * j + d.1 + 1) *
              (((n + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1))⁻¹ := by
          unfold ωBase; push_cast
          rw [div_pow, mul_pow, inv_div, div_pow, div_eq_mul_inv, mul_inv, div_eq_mul_inv]; ring
        rw [hev, h1, h2, hw_inv, div_eq_mul_inv (P.borelAmp d (n + 1))]
        ring
      rw [hLHS_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      -- Rewrite the RHS `r`-sum using `c = cOdd + cEven`, `sum_cEven_bernoulliFun_eq_zero`, and `sum_cOdd_bernoulliFun_eq_tsum_cDft`.
      have hRHS_d : (∑ r ∈ Finset.Icc 1 P.M,
            P.c d r * ((P.M : ℂ) ^ (d.1 + 1 + (2 * k + 1)) *
              emTermShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) (d.1 + 1 + (2 * k + 1)))) =
          ((bernoulli (2 * j) : ℂ) / ((2 * j).factorial : ℂ)) *
            (-(∑ r ∈ Finset.Icc 1 P.M,
              P.cOdd d r * (P.M : ℂ) ^ (2 * j + d.1) *
                (((bernoulliFun (2 * j + d.1 + 1) ((r : ℝ) / (P.M : ℝ)) : ℝ) : ℂ) /
                  ((2 * j + d.1 + 1 : ℕ) : ℂ)))) := by
        have hidx1 : d.1 + 1 + (2 * k + 1) = 2 * j + d.1 := by dsimp [j]; omega
        have hnotlt : ¬ (2 * j + d.1 < d.1) := by omega
        have hsub_d : 2 * j + d.1 - d.1 = 2 * j := by omega
        have hfac_step : ((2 * j + d.1 + 1).factorial : ℂ) =
            ((2 * j + d.1 + 1 : ℕ) : ℂ) * ((2 * j + d.1).factorial : ℂ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        have hfac_ne : ((2 * j + d.1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
        have hterm_r : ∀ r ∈ Finset.Icc 1 P.M,
            P.c d r * ((P.M : ℂ) ^ (d.1 + 1 + (2 * k + 1)) *
              emTermShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) (d.1 + 1 + (2 * k + 1))) =
            -((bernoulli (2 * j) : ℂ) / ((2 * j).factorial : ℂ)) *
              (P.cOdd d r * (P.M : ℂ) ^ (2 * j + d.1) *
                (((bernoulliFun (2 * j + d.1 + 1) ((r : ℝ) / (P.M : ℝ)) : ℝ) : ℂ) /
                  ((2 * j + d.1 + 1 : ℕ) : ℂ))) -
            ((bernoulli (2 * j) : ℂ) / ((2 * j).factorial : ℂ)) *
              ((P.M : ℂ) ^ (2 * j + d.1) / ((2 * j + d.1 + 1 : ℕ) : ℂ)) *
              (P.cEven d r * ((bernoulliFun (2 * j + d.1 + 1) ((r : ℝ) / (P.M : ℝ)) : ℝ) : ℂ)) := fun r _ => by
          rw [hidx1, emTermShift, iteratedDeriv_hPow_zero, ite_eq_right_iff.mpr fun h => (hnotlt h).elim,
            hsub_d, hfac_step, P.c_eq_cOdd_add_cEven d r]
          field_simp [hfac_ne]
          ring
        rw [Finset.sum_congr rfl hterm_r, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, sum_cEven_bernoulliFun_eq_zero P d hj, mul_zero, sub_zero]
        ring
      rw [hRHS_d, sum_cOdd_bernoulliFun_eq_tsum_cDft P d hj, tsum_borelAmp_div_pow P d hj]
      -- Identify `∑' n, ((n + 1 : ℂ) ^ (2 * j))⁻¹ = riemannZeta (2 * j)` and apply `riemannZeta_two_mul_nat`!
      have hzeta : (∑' n : ℕ, (((n + 1 : ℕ) : ℂ) ^ (2 * j))⁻¹) = riemannZeta (2 * (j : ℂ)) := by
        have hre : (1 : ℝ) < (2 * (j : ℂ)).re := by
          have : (2 * (j : ℂ)).re = 2 * (j : ℝ) := by norm_cast
          rw [this]; have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
          linarith
        rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
        refine tsum_congr fun n => ?_
        rw [one_div, show (2 * (j : ℂ)) = ((2 * j : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast]
        push_cast; rfl
      rw [hzeta, riemannZeta_two_mul_nat (by omega : j ≠ 0)]
      unfold borelPref
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hfac_d : (d.1.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hfac_d2 : ((d.1 + 2).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hfac_2j : ((2 * j).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hfac_rel : ((d.1 + 2).factorial : ℂ) =
          ((d.1 + 2 : ℕ) : ℂ) * ((d.1 + 1 : ℕ) : ℂ) * (d.1.factorial : ℂ) := by
        rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
      have hsq_d1 : (-1 : ℂ) ^ (d.1 + 1) * (-1 : ℂ) ^ (d.1 + 1) = 1 := by rw [← mul_pow]; norm_num
      have hsign_j : -((-1 : ℂ) ^ (j + 1)) = (-1 : ℂ) ^ j := by rw [pow_succ]; ring
      have hpow4pi : (4 * (Real.pi : ℂ) ^ 2) ^ (2 * j + d.1 + 1) =
          (2 * (Real.pi : ℂ)) ^ (2 * j) * (2 * (Real.pi : ℂ)) ^ (d.1 + 1) *
            (2 * (Real.pi : ℂ)) ^ (2 * j + d.1 + 1) := by
        have h4 : 4 * (Real.pi : ℂ) ^ 2 = (2 * (Real.pi : ℂ)) ^ 2 := by ring
        rw [h4, ← pow_mul, ← pow_add, ← pow_add]
        congr 1; omega
      have hpow2pi : (2 * (Real.pi : ℂ)) ^ (2 * j) =
          2 * (2 : ℂ) ^ (2 * j - 1) * (Real.pi : ℂ) ^ (2 * j) := by
        rw [mul_pow, show (2 : ℂ) ^ (2 * j) = 2 * (2 : ℂ) ^ (2 * j - 1) by
          conv_lhs => rw [show 2 * j = (2 * j - 1) + 1 by omega, pow_succ]
          exact mul_comm _ _]
      rw [hfac_rel, div_pow (P.M : ℂ) (4 * (Real.pi : ℂ) ^ 2), div_pow (P.M : ℂ) (2 * (Real.pi : ℂ)),
        hpow4pi, hpow2pi]
      have hd1_ne : ((d.1 + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d.1
      have hd2_ne : ((d.1 + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (d.1 + 1)
      have h2pi_ne : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) hpi
      have h2j1_ne : (2 : ℂ) ^ (2 * j - 1) ≠ 0 := pow_ne_zero (2 * j - 1) (by norm_num)
      field_simp [hpi, hfac_d, hd1_ne, hd2_ne, hfac_2j, h2pi_ne, h2j1_ne]
      have hmul_sign : -((-1 : ℂ) ^ (d.1 + 1) * (-1 : ℂ) ^ (d.1 + 1) * (-1 : ℂ) ^ (j + 1)) =
          (-1 : ℂ) ^ j := by rw [hsq_d1, one_mul, hsign_j]
      linear_combination
        (((2 * j + d.1).factorial : ℂ) * (P.M : ℂ) ^ (2 * j + d.1 + 1) * (bernoulli (2 * j) : ℂ) *
          ∑' k : ℕ, P.cDft d (k + 1) / ((k + 1 : ℕ) : ℂ) ^ (2 * j + d.1 + 1)) * hmul_sign
    · -- Odd `m = 2 * k + 1`: BOTH sides vanish (`B_{2k+3} = 0` on RHS, `iteratedDeriv_borelPhi_zero_odd` on LHS)!
      have hm_eq : m = 2 * k + 1 := by omega
      subst hm_eq
      rw [iteratedDeriv_borelPhi_zero_odd P k]
      symm
      refine Finset.sum_eq_zero fun d _ => Finset.sum_eq_zero fun r _ => ?_
      have hnotlt : ¬ (d.1 + 1 + (2 * k + 1 + 1) < d.1) := by omega
      have hsub_d : d.1 + 1 + (2 * k + 1 + 1) - d.1 = 2 * k + 3 := by omega
      have hodd_b : Odd (2 * k + 3) := ⟨k + 1, by omega⟩
      rw [emTermShift, iteratedDeriv_hPow_zero, ite_eq_right_iff.mpr fun h => (hnotlt h).elim, hsub_d,
        bernoulli_eq_zero_of_odd hodd_b (by omega)]
      simp

/-! ### 6. Ray Identity, Smooth Remainder Asymptotics, Coordinate Transfers, and Master Theorems -/

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
theorem quasipoly_lambertSeries_polyBound (P : Quasipoly) :
    PolyCoeffBound (lambertSeries (fun n => P.eval (n : ℤ))) := by
  obtain ⟨C, hC, hCbd⟩ := quasipoly_eval_norm_le P
  refine ⟨C, P.D + 2, hC, fun n => ?_⟩
  rw [coeff_lambertSeries]
  by_cases hn0 : n = 0
  · subst hn0; simp; positivity
  · simp only [hn0, ↓reduceIte]
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    have hsub : n.divisors ⊆ Finset.Icc 1 n := fun d hd =>
      Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
        Nat.le_of_dvd hn_pos (Nat.dvd_of_mem_divisors hd)⟩
    have hcard : n.divisors.card ≤ n := by
      calc n.divisors.card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hsub
        _ = n := by rw [Nat.card_Icc]; omega
    calc ‖∑ d ∈ n.divisors, (d : ℂ) * P.eval (d : ℤ)‖
        ≤ ∑ d ∈ n.divisors, ‖(d : ℂ) * P.eval (d : ℤ)‖ := norm_sum_le _ _
      _ ≤ ∑ _d ∈ n.divisors, (C * (n : ℝ) ^ (P.D + 1)) := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hd_pos : 1 ≤ d := Nat.pos_of_mem_divisors hd
          have hd_le : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_dvd hn_pos (Nat.dvd_of_mem_divisors hd)
          rw [norm_mul, Complex.norm_natCast]
          calc (d : ℝ) * ‖P.eval (d : ℤ)‖
              ≤ (d : ℝ) * (C * (d : ℝ) ^ P.D) := mul_le_mul_of_nonneg_left (hCbd d hd_pos) (by positivity)
            _ = C * (d : ℝ) ^ (P.D + 1) := by rw [pow_succ]; ring
            _ ≤ C * (n : ℝ) ^ (P.D + 1) :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hd_le _) hC
      _ = (n.divisors.card : ℝ) * (C * (n : ℝ) ^ (P.D + 1)) := by simp
      _ ≤ (n : ℝ) * (C * (n : ℝ) ^ (P.D + 1)) := by
          have hcr : (n.divisors.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right hcr (by positivity)
      _ = C * (n : ℝ) ^ (P.D + 2) := by rw [pow_succ]; ring
      _ ≤ C * ((n : ℝ) + 1) ^ (P.D + 2) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) _) hC

/-- Exact Lambert series identity on the positive real ray `q = exp (-t)` (`t > 0`). -/
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

private lemma tailFunDR_contDiffOn (P : Quasipoly) (d : Fin (P.D + 1)) {r : ℕ} (hr : 1 ≤ r)
    (n : ℕ) : ContDiffOn ℝ n (tailFunDR P d r) (Ioi (0 : ℝ)) := by
  have hMpos : (0 : ℝ) < (P.M : ℝ) := by exact_mod_cast P.hM
  have hrpos : (0 : ℝ) < (r : ℝ) / (P.M : ℝ) := div_pos (by exact_mod_cast hr) hMpos
  have hdiv_cd : ContDiffOn ℝ n (fun u : ℝ => u / (P.M : ℝ)) (Ioi (0 : ℝ)) :=
    (contDiffOn_id.div_const (P.M : ℝ))
  have hdiv_maps : MapsTo (fun u : ℝ => u / (P.M : ℝ)) (Ioi (0 : ℝ)) (Ioi (0 : ℝ)) :=
    fun u hu => div_pos hu hMpos
  have hS_cd : ContDiffOn ℝ n
      (fun u : ℝ => sumScaleShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) (u / (P.M : ℝ))) (Ioi (0 : ℝ)) :=
    (sumScaleShift_contDiffOn hrpos (hPow_expDecaySmooth d.1) n).comp hdiv_cd hdiv_maps
  have hlin_cd : ContDiffOn ℝ n
      (fun u : ℝ => ((u / (P.M : ℝ) : ℝ) : ℂ) * (∫ y in Ioi (0 : ℝ), hPow d.1 y)) (Ioi (0 : ℝ)) :=
    ((Complex.ofRealCLM.contDiff.contDiffOn.of_le le_top).comp hdiv_cd (mapsTo_univ _ _)).mul contDiffOn_const
  have hinv_cd : ContDiffOn ℝ n (fun u : ℝ => (u : ℂ)⁻¹) (Ioi (0 : ℝ)) :=
    (Complex.ofRealCLM.contDiff.contDiffOn.of_le le_top).inv fun u hu =>
      Complex.ofReal_ne_zero.mpr (ne_of_gt hu)
  have hsum_cd : ContDiffOn ℝ n
      (fun u : ℝ => ∑ k ∈ Finset.range (d.1 + 2),
        (P.M : ℂ) ^ k * emTermShift ((r : ℝ) / (P.M : ℝ)) (hPow d.1) k * (u : ℂ)⁻¹ ^ k)
      (Ioi (0 : ℝ)) :=
    ContDiffOn.sum fun k _ => contDiffOn_const.mul (hinv_cd.pow k)
  exact ((Complex.ofRealCLM.contDiff.contDiffOn.of_le le_top).pow (d.1 + 1)).mul
    ((hS_cd.sub hlin_cd).sub hsum_cd)

private lemma remFun_contDiffOn (P : Quasipoly) (n : ℕ) :
    ContDiffOn ℝ n (remFun P) (Ioi (0 : ℝ)) :=
  ContDiffOn.sum fun d _ => ContDiffOn.sum fun _r hr =>
    contDiffOn_const.mul (tailFunDR_contDiffOn P d (Finset.mem_Icc.mp hr).1 n)

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
    exact ((sumScaleShift_contDiffOn (hq_cast ▸ hq0) (hPow_expDecaySmooth d.1) n).comp hdiv_cd hdiv_maps).sub
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
      contDiffAt_const.mul ((tailFunDR_contDiffOn P d (Finset.mem_Icc.mp hr).1 j).contDiffAt
        (isOpen_Ioi.mem_nhds hu))
  rw [iteratedDeriv_finset_sum' _ _ j hcd_d]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [iteratedDeriv_finset_sum' _ _ j fun r hr =>
    contDiffAt_const.mul ((tailFunDR_contDiffOn P d (Finset.mem_Icc.mp hr).1 j).contDiffAt
      (isOpen_Ioi.mem_nhds hu))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [iteratedDeriv_const_mul_field]

/-! ### 6B. Coordinate Transfers (`log u → u`, `u⁻¹` Homogenization, Affine Shift) -/

private def triangularInv' {R : Type*} [Field R] {J : ℕ}
    (a b : Fin J → R) (c : Fin J → Fin J → R) : ℕ → MvPolynomial (Fin J) R
  | n =>
    if hn : n < J then
      let k : Fin J := ⟨n, hn⟩
      MvPolynomial.C (a k)⁻¹ *
        (MvPolynomial.X k - MvPolynomial.C (b k) -
          ∑ i ∈ (Finset.range n).attach,
            if hi : i.1 < J then MvPolynomial.C (c k ⟨i.1, hi⟩) * triangularInv' a b c i.1 else 0)
    else 0
termination_by n => n
decreasing_by
  exact Finset.mem_range.mp i.2

private lemma triangular_aeval_injective' {R : Type*} [Field R] {J : ℕ}
    (a b : Fin J → R) (c : Fin J → Fin J → R) (ha : ∀ k, a k ≠ 0)
    (Φ : Fin J → MvPolynomial (Fin J) R)
    (hΦ : ∀ k : Fin J, Φ k = MvPolynomial.C (a k) * MvPolynomial.X k + MvPolynomial.C (b k) +
      ∑ i ∈ Finset.range k.1,
        if hi : i < J then MvPolynomial.C (c k ⟨i, hi⟩) * MvPolynomial.X ⟨i, hi⟩ else 0) :
    Function.Injective (MvPolynomial.aeval Φ : MvPolynomial (Fin J) R →ₐ[R] MvPolynomial (Fin J) R) := by
  let ψ : Fin J → MvPolynomial (Fin J) R := fun k => triangularInv' a b c k.1
  have hleft : ∀ k : Fin J, MvPolynomial.aeval ψ (Φ k) = MvPolynomial.X k := fun k => by
    rw [hΦ k, map_add, map_add, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, map_sum]
    have hsum : (∑ i ∈ Finset.range k.1, MvPolynomial.aeval ψ
        (if hi : i < J then MvPolynomial.C (c k ⟨i, hi⟩) * MvPolynomial.X ⟨i, hi⟩ else 0)) =
        ∑ i ∈ Finset.range k.1,
          if hi : i < J then MvPolynomial.C (c k ⟨i, hi⟩) * triangularInv' a b c i else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hi
      · simp [ψ]
      · simp
    rw [hsum]
    change MvPolynomial.C (a k) * triangularInv' a b c k.1 + MvPolynomial.C (b k) + _ = MvPolynomial.X k
    conv_lhs => arg 1; arg 1; arg 2; rw [triangularInv']
    rw [dite_eq_left k.isLt]
    dsimp only
    simp only [Fin.eta]
    rw [Finset.sum_attach (Finset.range k.1)
      (fun i => if hi : i < J then MvPolynomial.C (c k ⟨i, hi⟩) * triangularInv' a b c i else 0)]
    have hinv : (MvPolynomial.C (a k) : MvPolynomial (Fin J) R) * MvPolynomial.C (a k)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ (ha k), map_one]
    linear_combination (MvPolynomial.X k - MvPolynomial.C (b k) -
      ∑ i ∈ Finset.range k.1,
        if hi : i < J then MvPolynomial.C (c k ⟨i, hi⟩) * triangularInv' a b c i else 0) * hinv
  intro P Q hPQ
  have hcomp : ∀ R' : MvPolynomial (Fin J) R,
      MvPolynomial.aeval ψ (MvPolynomial.aeval Φ R') = R' := fun R' => by
    rw [MvPolynomial.comp_aeval_apply, show (fun k => MvPolynomial.aeval ψ (Φ k)) = MvPolynomial.X from
      funext hleft, MvPolynomial.aeval_X_left_apply]
  calc P = MvPolynomial.aeval ψ (MvPolynomial.aeval Φ P) := (hcomp P).symm
    _ = MvPolynomial.aeval ψ (MvPolynomial.aeval Φ Q) := by rw [hPQ]
    _ = Q := hcomp Q

private lemma evalU_aeval' {J K : ℕ}
    (Φ : Fin J → MvPolynomial (Fin K) (Polynomial ℂ))
    (P : MvPolynomial (Fin J) (Polynomial ℂ)) (u : ℂ) (z : Fin K → ℂ) :
    MvPolynomial.eval z (MvPolynomial.map (Polynomial.evalRingHom u) (MvPolynomial.aeval Φ P)) =
      MvPolynomial.eval
        (fun j => MvPolynomial.eval z (MvPolynomial.map (Polynomial.evalRingHom u) (Φ j)))
        (MvPolynomial.map (Polynomial.evalRingHom u) P) := by
  induction P using MvPolynomial.induction_on with
  | C q => simp
  | add A B hA hB =>
    simp only [map_add] at hA hB ⊢
    rw [hA, hB]
  | mul_X A j hA =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.map_X, MvPolynomial.eval_X] at hA ⊢
    rw [hA]

private lemma map_aeval_poly_rat' {J K : ℕ}
    (Φ : Fin J → MvPolynomial (Fin K) (Polynomial ℂ))
    (P : MvPolynomial (Fin J) (Polynomial ℂ)) :
    MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (MvPolynomial.aeval Φ P) =
      MvPolynomial.aeval
        (fun j => MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (Φ j))
        (MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) P) := by
  induction P using MvPolynomial.induction_on with
  | C q => simp
  | add A B hA hB => simp only [map_add, hA, hB]
  | mul_X A j hA => simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, hA]

private lemma analytic_poly_jet_eq_zero_of_atTop' {J : ℕ} {φ : ℝ → ℂ}
    (hφ : ∀ y : ℝ, AnalyticAt ℝ φ y) (P : MvPolynomial (Fin J) ℂ)
    (htop : ∀ᶠ y : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ y) P = 0) :
    ∀ y : ℝ, MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ y) P = 0 := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp htop
  have hnhds : ∀ᶠ y in 𝓝 (R + 1),
      MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ y) P = 0 := by
    filter_upwards [isOpen_Ioi.mem_nhds (by linarith : R < R + 1)] with y hy
    exact hR y (le_of_lt hy)
  have han_jet : ∀ (k : ℕ) (y : ℝ), AnalyticAt ℝ (iteratedDeriv k φ) y := fun k y => by
    induction k generalizing y with
    | zero => simpa using hφ y
    | succ k ih => rw [iteratedDeriv_succ]; exact (ih y).deriv
  have han_poly : AnalyticOnNhd ℝ
      (fun y : ℝ => MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ y) P) Set.univ := by
    clear htop hR hnhds
    intro y _
    induction P using MvPolynomial.induction_on with
    | C a => simpa using analyticAt_const
    | add A B hA hB =>
      rw [show (fun z : ℝ => MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ z) (A + B)) =
          (fun z => MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ z) A) +
            fun z => MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ z) B from
        funext fun z => map_add _ A B]
      exact hA.add hB
    | mul_X A j hA =>
      rw [show (fun z : ℝ => MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ z)
            (A * MvPolynomial.X j)) =
          (fun z => MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ z) A) *
            iteratedDeriv j.1 φ from
        (funext fun z => by rw [map_mul, MvPolynomial.eval_X]; rfl)]
      exact hA.mul (han_jet j.1 y)
  intro y
  exact han_poly.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    convex_univ.isPreconnected (Set.mem_univ (R + 1)) hnhds (Set.mem_univ y)

private lemma mvPolynomial_finZero_eq_C' {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin 0) R) : P = MvPolynomial.C (P.coeff 0) := by
  ext m
  have hm : m = 0 := Subsingleton.elim m 0
  subst hm; simp

private def stirling2C' : ℕ → ℕ → ℂ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | k + 1, j + 1 => ((j + 1 : ℕ) : ℂ) * stirling2C' k (j + 1) + stirling2C' k j

private lemma stirling2C'_eq_zero_of_lt {k j : ℕ} (hkj : k < j) : stirling2C' k j = 0 := by
  induction k generalizing j with
  | zero =>
    cases j with
    | zero => omega
    | succ j => rfl
  | succ k ih =>
    cases j with
    | zero => omega
    | succ j =>
      simp only [stirling2C']
      rw [ih (by omega), ih (by omega)]; ring

private lemma stirling2C'_self (k : ℕ) : stirling2C' k k = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [stirling2C', stirling2C'_eq_zero_of_lt (Nat.lt_succ_self k), ih]; ring

private lemma contDiffOn_Ioi_iteratedDeriv_differentiableAt' {F : ℝ → ℂ}
    (hF : ∀ n : ℕ, ContDiffOn ℝ n F (Ioi (0 : ℝ))) (r : ℕ) {u : ℝ} (hu : 0 < u) :
    DifferentiableAt ℝ (iteratedDeriv r F) u := by
  have hcd : ContDiffOn ℝ ((r + 1 : ℕ) : ℕ∞) F (Ioi (0 : ℝ)) := hF (r + 1)
  have hd_on : DifferentiableOn ℝ (iteratedDerivWithin r F (Ioi (0 : ℝ))) (Ioi (0 : ℝ)) :=
    hcd.differentiableOn_iteratedDerivWithin (by exact_mod_cast (by omega : r < r + 1))
      isOpen_Ioi.uniqueDiffOn
  have hev : iteratedDeriv r F =ᶠ[𝓝 u] iteratedDerivWithin r F (Ioi (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
    exact (iteratedDerivWithin_of_isOpen isOpen_Ioi hv).symm
  exact (hd_on.differentiableAt (isOpen_Ioi.mem_nhds hu)).congr_of_eventuallyEq hev

private lemma iteratedDeriv_comp_exp' {F : ℝ → ℂ}
    (hF : ∀ n : ℕ, ContDiffOn ℝ n F (Ioi (0 : ℝ))) :
    ∀ (k : ℕ) (y : ℝ),
      iteratedDeriv k (fun z : ℝ => F (Real.exp z)) y =
        ∑ j ∈ Finset.range (k + 1),
          stirling2C' k j * (Real.exp y : ℂ) ^ j * iteratedDeriv j F (Real.exp y) := by
  intro k
  induction k with
  | zero => intro y; simp [stirling2C']
  | succ k ih =>
    intro y
    have heq_fn : iteratedDeriv k (fun z : ℝ => F (Real.exp z)) = fun z : ℝ =>
        ∑ j ∈ Finset.range (k + 1),
          stirling2C' k j * (Real.exp z : ℂ) ^ j * iteratedDeriv j F (Real.exp z) := funext ih
    rw [iteratedDeriv_succ, heq_fn]
    have hterm_deriv : ∀ j ∈ Finset.range (k + 1),
        HasDerivAt
          (fun z : ℝ => stirling2C' k j * (Real.exp z : ℂ) ^ j * iteratedDeriv j F (Real.exp z))
          (stirling2C' k j * (j : ℂ) * ((Real.exp y : ℂ) ^ j * iteratedDeriv j F (Real.exp y)) +
            stirling2C' k j * ((Real.exp y : ℂ) ^ (j + 1) * iteratedDeriv (j + 1) F (Real.exp y)))
          y := fun j _ => by
      have hexp : HasDerivAt (fun z : ℝ => (Real.exp z : ℂ)) (Real.exp y : ℂ) y :=
        (Real.hasDerivAt_exp y).ofReal_comp
      have hpow : HasDerivAt (fun z : ℝ => (Real.exp z : ℂ) ^ j)
          ((j : ℂ) * (Real.exp y : ℂ) ^ j) y := by
        cases j with
        | zero => simpa using hasDerivAt_const y (1 : ℂ)
        | succ j' =>
          refine (hexp.pow (j' + 1)).congr_deriv ?_
          rw [pow_succ (Real.exp y : ℂ) j']; push_cast; ring
      have hF' : HasDerivAt (fun z : ℝ => iteratedDeriv j F (Real.exp z))
          (iteratedDeriv (j + 1) F (Real.exp y) * (Real.exp y : ℂ)) y := by
        have hdf := (contDiffOn_Ioi_iteratedDeriv_differentiableAt' hF j (Real.exp_pos y)).hasDerivAt
        refine (hdf.scomp y (Real.hasDerivAt_exp y)).congr_deriv ?_
        rw [Complex.real_smul, ← iteratedDeriv_succ]; ring
      refine ((hpow.const_mul (stirling2C' k j)).mul hF').congr_deriv ?_
      rw [pow_succ]; ring
    have hsum_deriv : HasDerivAt
        (fun z : ℝ => ∑ j ∈ Finset.range (k + 1),
          stirling2C' k j * (Real.exp z : ℂ) ^ j * iteratedDeriv j F (Real.exp z))
        (∑ j ∈ Finset.range (k + 1),
          (stirling2C' k j * (j : ℂ) * ((Real.exp y : ℂ) ^ j * iteratedDeriv j F (Real.exp y)) +
            stirling2C' k j * ((Real.exp y : ℂ) ^ (j + 1) * iteratedDeriv (j + 1) F (Real.exp y))))
        y := by
      refine (HasDerivAt.sum hterm_deriv).congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
      simp only [Finset.sum_apply]
    rw [hsum_deriv.deriv, Finset.sum_add_distrib]
    let T : ℕ → ℂ := fun j => (Real.exp y : ℂ) ^ j * iteratedDeriv j F (Real.exp y)
    have h1 : (∑ j ∈ Finset.range (k + 1), stirling2C' k j * (j : ℂ) * T j) =
        ∑ j ∈ Finset.range (k + 2), stirling2C' k j * (j : ℂ) * T j := by
      conv_rhs =>
        rw [Finset.sum_range_succ, stirling2C'_eq_zero_of_lt (Nat.lt_succ_self k),
          zero_mul, zero_mul, add_zero]
    have h2 : (∑ j ∈ Finset.range (k + 1), stirling2C' k j * T (j + 1)) =
        ∑ j ∈ Finset.range (k + 2), (if j = 0 then 0 else stirling2C' k (j - 1)) * T j := by
      rw [Finset.sum_range_succ' (fun j => (if j = 0 then 0 else stirling2C' k (j - 1)) * T j)]
      simp
    dsimp only [T] at h1 h2
    rw [h1, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    cases j with
    | zero => simp [stirling2C']
    | succ j' =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one, stirling2C']
      ring

private lemma autonomous_log_to_poly_ode' {ψ : ℝ → ℂ} (hψ : ∀ y : ℝ, AnalyticAt ℝ ψ y)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ) (hP_ne : P ≠ 0)
    (hP_top : ∀ᶠ y : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 ψ y) P = 0) :
    ∃ Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ), Q ≠ 0 ∧
      ∀ᶠ u : ℝ in atTop,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 (fun v => ψ (Real.log v)) u)
          (evalU Q (u : ℂ)) = 0 := by
  have hall : ∀ y : ℝ, MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 ψ y) P = 0 :=
    analytic_poly_jet_eq_zero_of_atTop' hψ P hP_top
  let F : ℝ → ℂ := fun u => ψ (Real.log u)
  have hF_cd : ∀ n : ℕ, ContDiffOn ℝ n F (Ioi (0 : ℝ)) := fun n => by
    have hψ_cd : ContDiff ℝ (⊤ : ℕ∞) ψ := contDiff_iff_contDiffAt.mpr fun y => (hψ y).contDiffAt
    have hlog_cd : ContDiffOn ℝ (⊤ : ℕ∞) Real.log (Ioi (0 : ℝ)) :=
      Real.contDiffOn_log.mono fun x hx => ne_of_gt hx
    exact (hψ_cd.comp_contDiffOn hlog_cd).of_le (WithTop.coe_le_coe.mpr le_top)
  let Φ : Fin (r + 1) → MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := fun k =>
    ∑ j ∈ Finset.range (k.1 + 1),
      if hj : j < r + 1 then
        MvPolynomial.C (Polynomial.C (stirling2C' k.1 j) * Polynomial.X ^ j) * MvPolynomial.X ⟨j, hj⟩
      else 0
  let Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
    MvPolynomial.aeval Φ (MvPolynomial.map Polynomial.C P)
  refine ⟨Q, ?_, ?_⟩
  · let ι : Polynomial ℂ →+* RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ)
    have hι_inj : Function.Injective ι := RatFunc.algebraMap_injective ℂ
    have hx_rat_ne : (RatFunc.X : RatFunc ℂ) ≠ 0 := by
      rw [← RatFunc.algebraMap_X]
      exact (map_ne_zero_iff ι hι_inj).mpr Polynomial.X_ne_zero
    have ha_ne : ∀ k : Fin (r + 1), (RatFunc.X ^ k.1 : RatFunc ℂ) ≠ 0 := fun k =>
      pow_ne_zero k.1 hx_rat_ne
    let Φ_rat : Fin (r + 1) → MvPolynomial (Fin (r + 1)) (RatFunc ℂ) := fun k =>
      MvPolynomial.map ι (Φ k)
    have hΦ_rat : ∀ k : Fin (r + 1),
        Φ_rat k =
          MvPolynomial.C (RatFunc.X ^ k.1 : RatFunc ℂ) * MvPolynomial.X k +
            MvPolynomial.C (0 : RatFunc ℂ) +
            ∑ i ∈ Finset.range k.1,
              if hi : i < r + 1 then
                MvPolynomial.C (RatFunc.C (stirling2C' k.1 i) * RatFunc.X ^ i) *
                  MvPolynomial.X ⟨i, hi⟩
              else 0 := fun k => by
      dsimp only [Φ_rat, Φ]
      rw [map_sum, Finset.sum_range_succ, dite_eq_left k.isLt, map_mul, MvPolynomial.map_C,
        MvPolynomial.map_X]
      have hhead : (∑ x ∈ Finset.range k.1, MvPolynomial.map ι
          (if hj : x < r + 1 then
            MvPolynomial.C (Polynomial.C (stirling2C' k.1 x) * Polynomial.X ^ x) *
              MvPolynomial.X (⟨x, hj⟩ : Fin (r + 1))
          else 0)) =
          ∑ i ∈ Finset.range k.1,
            if hi : i < r + 1 then
              MvPolynomial.C (RatFunc.C (stirling2C' k.1 i) * RatFunc.X ^ i) *
                MvPolynomial.X (⟨i, hi⟩ : Fin (r + 1))
            else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs with hi
        · simp [ι, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
        · simp
      have htop : ι (Polynomial.C (stirling2C' k.1 k.1) * Polynomial.X ^ k.1) =
          (RatFunc.X ^ k.1 : RatFunc ℂ) := by
        rw [stirling2C'_self, map_one, one_mul, map_pow, RatFunc.algebraMap_X]
      simp only [Fin.eta]
      rw [htop, hhead, map_zero, add_zero]
      exact add_comm _ _
    have hinj := triangular_aeval_injective' (R := RatFunc ℂ)
      (fun k => RatFunc.X ^ k.1) (fun _ => 0)
      (fun k i => RatFunc.C (stirling2C' k.1 i.1) * RatFunc.X ^ i.1) ha_ne Φ_rat hΦ_rat
    intro hQ0
    have hmap0 : MvPolynomial.map ι Q = 0 := by rw [hQ0, map_zero]
    dsimp only [Q] at hmap0
    rw [map_aeval_poly_rat', MvPolynomial.map_map] at hmap0
    have hP0_rat : MvPolynomial.map (ι.comp Polynomial.C) P = 0 :=
      hinj (hmap0.trans (map_zero _).symm)
    have hcomp_inj : Function.Injective (ι.comp Polynomial.C : ℂ →+* RatFunc ℂ) :=
      hι_inj.comp Polynomial.C_injective
    exact hP_ne ((MvPolynomial.map_injective (σ := Fin (r + 1)) _ hcomp_inj)
      (hP0_rat.trans (map_zero _).symm))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hev_comp : (fun z : ℝ => F (Real.exp z)) = ψ := by
      funext z; simp [F, Real.log_exp]
    have hderiv_k : ∀ k : Fin (r + 1),
        iteratedDeriv k.1 ψ (Real.log u) =
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 F u)
            (evalU (Φ k) (u : ℂ)) := fun k => by
      have hid := iteratedDeriv_comp_exp' hF_cd k.1 (Real.log u)
      rw [hev_comp, Real.exp_log hu] at hid
      rw [hid]
      dsimp only [Φ, evalU]
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj_lt : j < r + 1 :=
        Nat.lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) k.isLt
      rw [dite_eq_left hj_lt, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
        Polynomial.coe_evalRingHom, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      simp [Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
    have hev_Q : MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 F u)
        (evalU Q (u : ℂ)) =
        MvPolynomial.eval (fun k : Fin (r + 1) => iteratedDeriv k.1 ψ (Real.log u))
          (evalU (MvPolynomial.map Polynomial.C P) (u : ℂ)) := by
      dsimp only [Q, evalU]
      rw [evalU_aeval']
      refine congrArg (fun f => MvPolynomial.eval f _) (funext fun k => ?_)
      simpa [evalU] using (hderiv_k k).symm
    have heval_C : evalU (MvPolynomial.map Polynomial.C P) (u : ℂ) = P := by
      dsimp only [evalU]
      rw [MvPolynomial.map_map]
      have hid_hom : (Polynomial.evalRingHom (u : ℂ)).comp Polynomial.C = RingHom.id ℂ := by
        ext x; simp
      rw [hid_hom, MvPolynomial.map_id]
    rw [hev_Q, heval_C]
    exact hall (Real.log u)

private lemma iteratedDeriv_inv_real' (r : ℕ) {u : ℝ} (hu : u ≠ 0) :
    iteratedDeriv r (fun v : ℝ => (v : ℂ)⁻¹) u =
      (-1 : ℂ) ^ r * (r.factorial : ℂ) * (u : ℂ)⁻¹ ^ (r + 1) := by
  induction r generalizing u with
  | zero => simp
  | succ r ih =>
    have hne : ∀ᶠ y in 𝓝 u, y ≠ 0 := (isOpen_ne (x := (0 : ℝ))).mem_nhds hu
    have hev : iteratedDeriv r (fun v : ℝ => (v : ℂ)⁻¹) =ᶠ[𝓝 u]
        fun y : ℝ => (-1 : ℂ) ^ r * (r.factorial : ℂ) * (y : ℂ)⁻¹ ^ (r + 1) := by
      filter_upwards [hne] with y hy; exact ih hy
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hd := (hasDerivAt_inv_pow_complex' (j := r + 1) hu).const_mul
      ((-1 : ℂ) ^ r * (r.factorial : ℂ))
    refine hd.deriv.trans ?_
    rw [Nat.factorial_succ, pow_succ]; push_cast; ring

private lemma homogenize_inv_mul_ode' {G H : ℝ → ℂ}
    (hGH : ∀ u : ℝ, 0 < u → G u = H u * (u : ℂ)⁻¹)
    (hH_cd : ∀ n : ℕ, ContDiffOn ℝ n H (Ioi (0 : ℝ)))
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hQ_ne : Q ≠ 0)
    (hQ_top : ∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 G u) (evalU Q (u : ℂ)) = 0) :
    ∃ Q_hom : MvPolynomial (Fin (r + 1)) (Polynomial ℂ), Q_hom ≠ 0 ∧
      ∀ᶠ u : ℝ in atTop,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 H u) (evalU Q_hom (u : ℂ)) = 0 := by
  let M : ℕ := r + 1
  let d : ℕ := Q.totalDegree
  let c_inv : Fin (r + 1) → Fin (r + 1) → Polynomial ℂ := fun k i =>
    Polynomial.C ((k.1.choose i.1 : ℂ) * (-1 : ℂ) ^ (k.1 - i.1) * ((k.1 - i.1).factorial : ℂ)) *
      Polynomial.X ^ (M - (k.1 - i.1 + 1))
  let Φ : Fin (r + 1) → MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := fun k =>
    ∑ i ∈ Finset.range (k.1 + 1),
      if hi : i < r + 1 then MvPolynomial.C (c_inv k ⟨i, hi⟩) * MvPolynomial.X ⟨i, hi⟩ else 0
  let Q_hom : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
    ∑ α ∈ Q.support,
      MvPolynomial.C (Q.coeff α * Polynomial.X ^ (M * (d - ∑ k : Fin (r + 1), α k))) *
        ∏ k : Fin (r + 1), (Φ k) ^ (α k)
  refine ⟨Q_hom, ?_, ?_⟩
  · let ι : Polynomial ℂ →+* RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ)
    have hι_inj : Function.Injective ι := RatFunc.algebraMap_injective ℂ
    have hx_ne : (RatFunc.X : RatFunc ℂ) ≠ 0 := by
      rw [← RatFunc.algebraMap_X]
      exact (map_ne_zero_iff ι hι_inj).mpr Polynomial.X_ne_zero
    let xM : RatFunc ℂ := RatFunc.X ^ M
    have hxM_ne : xM ≠ 0 := pow_ne_zero M hx_ne
    let ψ : Fin (r + 1) → MvPolynomial (Fin (r + 1)) (RatFunc ℂ) := fun k =>
      MvPolynomial.C xM⁻¹ * MvPolynomial.map ι (Φ k)
    have hψ_tri : ∀ k : Fin (r + 1),
        ψ k =
          MvPolynomial.C (RatFunc.X⁻¹ : RatFunc ℂ) * MvPolynomial.X k +
            MvPolynomial.C (0 : RatFunc ℂ) +
            ∑ i ∈ Finset.range k.1,
              if hi : i < r + 1 then
                MvPolynomial.C (xM⁻¹ * ι (c_inv k ⟨i, hi⟩)) * MvPolynomial.X ⟨i, hi⟩
              else 0 := fun k => by
      dsimp only [ψ, Φ]
      rw [map_sum, Finset.sum_range_succ, mul_add, Finset.mul_sum]
      have hhead : (∑ i ∈ Finset.range k.1, MvPolynomial.C xM⁻¹ * MvPolynomial.map ι
          (if hi : i < r + 1 then
            MvPolynomial.C (c_inv k ⟨i, hi⟩) * MvPolynomial.X (⟨i, hi⟩ : Fin (r + 1)) else 0)) =
          ∑ i ∈ Finset.range k.1,
            if hi : i < r + 1 then
              MvPolynomial.C (xM⁻¹ * ι (c_inv k ⟨i, hi⟩)) * MvPolynomial.X (⟨i, hi⟩ : Fin (r + 1))
            else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs with hi
        · simp only [map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
          rw [← mul_assoc, ← map_mul]
        · simp
      have htop : MvPolynomial.C xM⁻¹ * MvPolynomial.map ι
          (if hk : k.1 < r + 1 then
            MvPolynomial.C (c_inv k ⟨k.1, hk⟩) * MvPolynomial.X ⟨k.1, hk⟩ else 0) =
          MvPolynomial.C (RatFunc.X⁻¹ : RatFunc ℂ) * MvPolynomial.X k := by
        rw [dite_eq_left k.isLt, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
          ← mul_assoc, ← map_mul]
        have hcoeff : xM⁻¹ * ι (c_inv k ⟨k.1, k.isLt⟩) = (RatFunc.X⁻¹ : RatFunc ℂ) := by
          dsimp only [c_inv, xM]
          simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, Nat.factorial_zero,
            mul_one, zero_add, Polynomial.C_1, one_mul]
          rw [map_pow, RatFunc.algebraMap_X]
          have hM_sub : M - 1 = r := by omega
          rw [hM_sub, show M = r + 1 from rfl, pow_succ]
          field_simp [hx_ne]
        simp only [Fin.eta]
        rw [hcoeff]
      rw [htop, hhead, map_zero, add_zero]
      exact add_comm _ _
    have hinj := triangular_aeval_injective' (R := RatFunc ℂ)
      (fun _ => (RatFunc.X⁻¹ : RatFunc ℂ)) (fun _ => 0)
      (fun k i => xM⁻¹ * ι (c_inv k i)) (fun _ => inv_ne_zero hx_ne) ψ hψ_tri
    have hmap_Qhom : MvPolynomial.map ι Q_hom =
        MvPolynomial.C (xM ^ d) * MvPolynomial.aeval ψ (MvPolynomial.map ι Q) := by
      have hQ_as_sum : MvPolynomial.map ι Q =
          ∑ α ∈ Q.support, MvPolynomial.C (ι (Q.coeff α)) * ∏ k : Fin (r + 1), MvPolynomial.X k ^ α k := by
        conv_lhs => rw [Q.as_sum, map_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [MvPolynomial.monomial_eq, Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _
          (fun _ _ => pow_zero _), map_mul, MvPolynomial.map_C, map_prod]
        refine congrArg _ (Finset.prod_congr rfl fun k _ => ?_)
        rw [map_pow, MvPolynomial.map_X]
      dsimp only [Q_hom]
      rw [map_sum]
      conv_rhs => rw [hQ_as_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      have hα_le : ∑ k : Fin (r + 1), α k ≤ d := by
        have hs : (α.sum fun _ e => e) = ∑ k : Fin (r + 1), α k :=
          Finsupp.sum_fintype _ _ fun _ => rfl
        exact hs ▸ MvPolynomial.le_totalDegree hα
      have hΦ_split : ∀ k : Fin (r + 1), MvPolynomial.map ι (Φ k) = MvPolynomial.C xM * ψ k := fun k => by
        dsimp only [ψ]
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hxM_ne, map_one, one_mul]
      have hLHS1 : MvPolynomial.map ι
          (MvPolynomial.C (Q.coeff α * Polynomial.X ^ (M * (d - ∑ k : Fin (r + 1), α k)))) =
          (MvPolynomial.C (ι (Q.coeff α) * RatFunc.X ^ (M * (d - ∑ k : Fin (r + 1), α k))) :
            MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) := by
        rw [MvPolynomial.map_C, map_mul, map_pow, RatFunc.algebraMap_X]
      have hprod_C : (∏ k : Fin (r + 1), (MvPolynomial.C xM : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) ^ α k) =
          MvPolynomial.C (xM ^ ∑ k : Fin (r + 1), α k) := by
        simp_rw [← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum]
      have hLHS2 : MvPolynomial.map ι (∏ k : Fin (r + 1), Φ k ^ α k) =
          MvPolynomial.C (xM ^ ∑ k : Fin (r + 1), α k) * ∏ k : Fin (r + 1), ψ k ^ α k := by
        calc MvPolynomial.map ι (∏ k : Fin (r + 1), Φ k ^ α k)
            = ∏ k : Fin (r + 1), (MvPolynomial.C xM * ψ k) ^ α k := by
                rw [map_prod]
                refine Finset.prod_congr rfl fun k _ => by rw [map_pow, hΦ_split]
          _ = ∏ k : Fin (r + 1), ((MvPolynomial.C xM : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) ^ α k *
                ψ k ^ α k) := Finset.prod_congr rfl fun k _ => mul_pow _ _ _
          _ = (∏ k : Fin (r + 1), (MvPolynomial.C xM : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) ^ α k) *
                ∏ k : Fin (r + 1), ψ k ^ α k := Finset.prod_mul_distrib
          _ = MvPolynomial.C (xM ^ ∑ k : Fin (r + 1), α k) * ∏ k : Fin (r + 1), ψ k ^ α k := by
                rw [hprod_C]
      have hRHS2 : MvPolynomial.aeval ψ
            (MvPolynomial.C (ι (Q.coeff α)) * ∏ k : Fin (r + 1), MvPolynomial.X k ^ α k) =
          MvPolynomial.C (ι (Q.coeff α)) * ∏ k : Fin (r + 1), ψ k ^ α k := by
        rw [map_mul, MvPolynomial.aeval_C, map_prod]
        simp_rw [map_pow, MvPolynomial.aeval_X]; rfl
      have hC_eq : ι (Q.coeff α) * RatFunc.X ^ (M * (d - ∑ k : Fin (r + 1), α k)) *
          xM ^ ∑ k : Fin (r + 1), α k = xM ^ d * ι (Q.coeff α) := by
        dsimp only [xM]
        rw [← pow_mul, ← pow_mul, mul_assoc (ι (Q.coeff α)), ← pow_add, ← mul_add,
          Nat.sub_add_cancel hα_le]; ring
      rw [map_mul, hLHS1, hLHS2, hRHS2,
        ← mul_assoc (MvPolynomial.C (ι (Q.coeff α) * RatFunc.X ^ (M * (d - ∑ k : Fin (r + 1), α k)))),
        ← mul_assoc (MvPolynomial.C (xM ^ d)), ← map_mul, ← map_mul, hC_eq]
    intro hQhom0
    have hmap0 : MvPolynomial.map ι Q_hom = 0 := by rw [hQhom0, map_zero]
    rw [hmap_Qhom, mul_eq_zero] at hmap0
    rcases hmap0 with hxM0 | hae0
    · have : xM ^ d = 0 := by simpa using congrArg (MvPolynomial.eval 0) hxM0
      exact pow_ne_zero d hxM_ne this
    · have hQrat0 : MvPolynomial.map ι Q = 0 := hinj (hae0.trans (map_zero _).symm)
      exact hQ_ne ((MvPolynomial.map_injective (σ := Fin (r + 1)) ι hι_inj)
        (hQrat0.trans (map_zero _).symm))
  · filter_upwards [hQ_top, eventually_gt_atTop (0 : ℝ)] with u hu_Q hu_pos
    have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    have hderiv_k : ∀ k : Fin (r + 1),
        (u : ℂ) ^ M * iteratedDeriv k.1 G u =
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 H u)
            (evalU (Φ k) (u : ℂ)) := fun k => by
      have hev_nhds : G =ᶠ[𝓝 u] fun v : ℝ => H v * (v : ℂ)⁻¹ := by
        filter_upwards [isOpen_Ioi.mem_nhds hu_pos] with v hv
        exact hGH v hv
      have hcd_H : ContDiffAt ℝ k.1 H u := (hH_cd k.1).contDiffAt (isOpen_Ioi.mem_nhds hu_pos)
      have hcd_inv : ContDiffAt ℝ k.1 (fun v : ℝ => (v : ℂ)⁻¹) u :=
        (Complex.ofRealCLM.contDiff.contDiffAt.inv huc).of_le le_top
      rw [hev_nhds.iteratedDeriv_eq, iteratedDeriv_fun_mul hcd_H hcd_inv, Finset.mul_sum]
      dsimp only [Φ, evalU]
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi_le : i ≤ k.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hi_lt : i < r + 1 := Nat.lt_of_le_of_lt hi_le k.isLt
      rw [dite_eq_left hi_lt, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
        Polynomial.coe_evalRingHom, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
        iteratedDeriv_inv_real' (k.1 - i) hu_pos.ne']
      dsimp only [c_inv]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      have hexp_sum : M - (k.1 - i + 1) + (k.1 - i + 1) = M := by omega
      calc (u : ℂ) ^ M * ((k.1.choose i : ℂ) * iteratedDeriv i H u *
            ((-1 : ℂ) ^ (k.1 - i) * ((k.1 - i).factorial : ℂ) * (u : ℂ)⁻¹ ^ (k.1 - i + 1)))
          = ((k.1.choose i : ℂ) * (-1 : ℂ) ^ (k.1 - i) * ((k.1 - i).factorial : ℂ) *
              ((u : ℂ) ^ (M - (k.1 - i + 1)) * (u : ℂ) ^ (k.1 - i + 1) * (u : ℂ)⁻¹ ^ (k.1 - i + 1))) *
              iteratedDeriv i H u := by
            rw [← pow_add, hexp_sum]; ring
        _ = _ := by
            rw [mul_assoc ((u : ℂ) ^ (M - (k.1 - i + 1))), ← mul_pow, mul_inv_cancel₀ huc,
              one_pow, mul_one]
    have hsum_eval : MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 H u)
        (evalU Q_hom (u : ℂ)) =
        (u : ℂ) ^ (M * d) *
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 G u) (evalU Q (u : ℂ)) := by
      dsimp only [Q_hom, evalU]
      rw [map_sum, map_sum]
      have hQ_eval : MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 G u)
          (MvPolynomial.map (Polynomial.evalRingHom (u : ℂ)) Q) =
          ∑ α ∈ Q.support, (Q.coeff α).eval (u : ℂ) *
            ∏ k : Fin (r + 1), (iteratedDeriv k.1 G u) ^ (α k) := by
        conv_lhs => rw [Q.as_sum, map_sum, map_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [MvPolynomial.monomial_eq, Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _
          (fun _ _ => pow_zero _)]
        simp [Polynomial.coe_evalRingHom]
      rw [hQ_eval, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      have hα_le : ∑ k : Fin (r + 1), α k ≤ d := by
        have hs : (α.sum fun _ e => e) = ∑ k : Fin (r + 1), α k :=
          Finsupp.sum_fintype _ _ fun _ => rfl
        exact hs ▸ MvPolynomial.le_totalDegree hα
      simp only [map_mul, MvPolynomial.map_C, Polynomial.coe_evalRingHom, MvPolynomial.eval_C,
        map_prod, map_pow, Polynomial.eval_X]
      have hprod_eq : (∏ k : Fin (r + 1), (MvPolynomial.eval (fun j => iteratedDeriv j.1 H u)
          (MvPolynomial.map (Polynomial.evalRingHom (u : ℂ)) (Φ k))) ^ α k) =
          (u : ℂ) ^ (M * ∑ k : Fin (r + 1), α k) *
            ∏ k : Fin (r + 1), (iteratedDeriv k.1 G u) ^ α k := by
        calc _ = ∏ k : Fin (r + 1), ((u : ℂ) ^ M * iteratedDeriv k.1 G u) ^ α k :=
              Finset.prod_congr rfl fun k _ => by simpa [evalU] using congrArg (· ^ α k) (hderiv_k k).symm
          _ = ∏ k : Fin (r + 1), ((u : ℂ) ^ (M * α k) * (iteratedDeriv k.1 G u) ^ α k) :=
              Finset.prod_congr rfl fun k _ => by rw [mul_pow, ← pow_mul]
          _ = (∏ k : Fin (r + 1), (u : ℂ) ^ (M * α k)) *
                ∏ k : Fin (r + 1), (iteratedDeriv k.1 G u) ^ α k := Finset.prod_mul_distrib
          _ = (u : ℂ) ^ (∑ k : Fin (r + 1), M * α k) *
                ∏ k : Fin (r + 1), (iteratedDeriv k.1 G u) ^ α k := by rw [Finset.prod_pow_eq_pow_sum]
          _ = _ := by rw [← Finset.mul_sum]
      have hexp_u : (u : ℂ) ^ (M * (d - ∑ k : Fin (r + 1), α k)) *
          (u : ℂ) ^ (M * ∑ k : Fin (r + 1), α k) = (u : ℂ) ^ (M * d) := by
        rw [← pow_add, ← mul_add, Nat.sub_add_cancel hα_le]
      rw [hprod_eq]
      calc (Q.coeff α).eval (u : ℂ) * (u : ℂ) ^ (M * (d - ∑ k : Fin (r + 1), α k)) *
            ((u : ℂ) ^ (M * ∑ k : Fin (r + 1), α k) * ∏ k : Fin (r + 1), iteratedDeriv k.1 G u ^ α k)
          = ((u : ℂ) ^ (M * (d - ∑ k : Fin (r + 1), α k)) *
              (u : ℂ) ^ (M * ∑ k : Fin (r + 1), α k)) *
              ((Q.coeff α).eval (u : ℂ) * ∏ k : Fin (r + 1), iteratedDeriv k.1 G u ^ α k) := by ring
        _ = _ := by rw [hexp_u]
    rw [hsum_eval, hu_Q, mul_zero]

private def iteratedDerivPoly' (n : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  (Polynomial.derivative (R := ℂ))^[n] p

private lemma iteratedDeriv_poly_ofReal' (n : ℕ) (p : Polynomial ℂ) (x : ℝ) :
    iteratedDeriv n (fun v : ℝ => p.eval (v : ℂ)) x = (iteratedDerivPoly' n p).eval (x : ℂ) := by
  induction n generalizing p with
  | zero => simp [iteratedDerivPoly']
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hderiv : deriv (fun v : ℝ => p.eval (v : ℂ)) =
        fun v : ℝ => p.derivative.eval (v : ℂ) := by
      funext v
      have hd := (p.hasDerivAt (v : ℂ)).scomp v (hasDerivAt_id v).ofReal_comp
      simpa [Function.comp_def] using hd.deriv
    rw [hderiv, ih p.derivative]
    dsimp only [iteratedDerivPoly']
    exact congrArg (fun q : Polynomial ℂ => q.eval (x : ℂ))
      (Function.iterate_succ_apply (Polynomial.derivative (R := ℂ)) n p).symm

private lemma poly_ofReal_contDiffAt' (p : Polynomial ℂ) (n : ℕ) (u : ℝ) :
    ContDiffAt ℝ n (fun v : ℝ => p.eval (v : ℂ)) u := by
  have heq : (fun v : ℝ => p.eval (v : ℂ)) =
      fun v : ℝ => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (v : ℂ) ^ i := by
    funext v; rw [Polynomial.eval_eq_sum_range]
  rw [heq]
  exact ContDiffAt.sum fun i _ =>
    contDiffAt_const.mul ((Complex.ofRealCLM.contDiff.contDiffAt.of_le le_top).pow i)

private lemma poly_ode_of_add_poly' {H f : ℝ → ℂ} (b : Polynomial ℂ)
    (hHf : ∀ u : ℝ, 0 < u → H u = f u + b.eval (u : ℂ))
    (hf_cd : ∀ n : ℕ, ContDiffOn ℝ n f (Ioi (0 : ℝ)))
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hQ_ne : Q ≠ 0)
    (hQ_top : ∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 H u) (evalU Q (u : ℂ)) = 0) :
    ∃ Q' : MvPolynomial (Fin (r + 1)) (Polynomial ℂ), Q' ≠ 0 ∧
      ∀ᶠ u : ℝ in atTop,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 f u) (evalU Q' (u : ℂ)) = 0 := by
  let Φ : Fin (r + 1) → MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := fun k =>
    MvPolynomial.X k + MvPolynomial.C (iteratedDerivPoly' k.1 b)
  let Q' : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := MvPolynomial.aeval Φ Q
  refine ⟨Q', ?_, ?_⟩
  · let ι : Polynomial ℂ →+* RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ)
    have hι_inj : Function.Injective ι := RatFunc.algebraMap_injective ℂ
    let Φ_rat : Fin (r + 1) → MvPolynomial (Fin (r + 1)) (RatFunc ℂ) := fun k =>
      MvPolynomial.map ι (Φ k)
    have hΦ_rat : ∀ k : Fin (r + 1),
        Φ_rat k =
          MvPolynomial.C (1 : RatFunc ℂ) * MvPolynomial.X k +
            MvPolynomial.C (ι (iteratedDerivPoly' k.1 b)) +
            ∑ i ∈ Finset.range k.1,
              if hi : i < r + 1 then MvPolynomial.C (0 : RatFunc ℂ) * MvPolynomial.X ⟨i, hi⟩ else 0 := fun k => by
      dsimp only [Φ_rat, Φ]
      simp only [map_add, MvPolynomial.map_X, MvPolynomial.map_C, map_one, one_mul, map_zero,
        zero_mul, dite_eq_ite, ite_self, Finset.sum_const_zero, add_zero]
    have hinj := triangular_aeval_injective' (R := RatFunc ℂ)
      (fun _ => (1 : RatFunc ℂ)) (fun k => ι (iteratedDerivPoly' k.1 b)) (fun _ _ => 0)
      (fun _ => one_ne_zero) Φ_rat hΦ_rat
    intro hQ'0
    have hmap0 : MvPolynomial.map ι Q' = 0 := by rw [hQ'0, map_zero]
    dsimp only [Q'] at hmap0
    rw [map_aeval_poly_rat'] at hmap0
    have hQ_rat0 : MvPolynomial.map ι Q = 0 := hinj (hmap0.trans (map_zero _).symm)
    exact hQ_ne ((MvPolynomial.map_injective (σ := Fin (r + 1)) ι hι_inj)
      (hQ_rat0.trans (map_zero _).symm))
  · filter_upwards [hQ_top, eventually_gt_atTop (0 : ℝ)] with u hu_Q hu_pos
    have hderiv_k : ∀ k : Fin (r + 1),
        iteratedDeriv k.1 H u =
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 f u)
            (evalU (Φ k) (u : ℂ)) := fun k => by
      have hev_nhds : H =ᶠ[𝓝 u] fun v : ℝ => f v + b.eval (v : ℂ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hu_pos] with v hv
        exact hHf v hv
      have hcd_f : ContDiffAt ℝ k.1 f u := (hf_cd k.1).contDiffAt (isOpen_Ioi.mem_nhds hu_pos)
      have hcd_b : ContDiffAt ℝ k.1 (fun v : ℝ => b.eval (v : ℂ)) u := poly_ofReal_contDiffAt' b k.1 u
      rw [hev_nhds.iteratedDeriv_eq, iteratedDeriv_fun_add hcd_f hcd_b,
        iteratedDeriv_poly_ofReal' k.1 b u]
      simp [Φ, evalU]
    have hev_Q' : MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 f u)
        (evalU Q' (u : ℂ)) =
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 H u) (evalU Q (u : ℂ)) := by
      dsimp only [Q', evalU]
      rw [evalU_aeval']
      refine congrArg (fun f => MvPolynomial.eval f _) (funext fun k => ?_)
      simpa [evalU] using (hderiv_k k).symm
    rw [hev_Q', hu_Q]

/-! ### 6C. Master Unconditional Quasipolynomial Euler-Product Parity Theorems -/

private lemma quasipoly_lambert_no_autonomous_ode (P : Quasipoly)
    (hodd : ∃ n : ℤ, P.oddPart n ≠ 0) {J : ℕ}
    (Q_aut : MvPolynomial (Fin J) ℂ) (hQ_ne : Q_aut ≠ 0)
    (hQ_zero : ∀ᶠ y : ℝ in atTop,
      MvPolynomial.eval
        (fun j : Fin J => iteratedDeriv j.1 (scaledRay (lambertSeries (fun n => P.eval (n : ℤ)))) y)
        Q_aut = 0) : False := by
  have hP_an : ∀ y : ℝ, AnalyticAt ℝ (scaledRay (lambertSeries (fun n => P.eval (n : ℤ)))) y :=
    fun y => scaledRay_analytic (quasipoly_lambertSeries_polyBound P).to_diskCoeffBound y
  cases J with
  | zero =>
    have hc := mvPolynomial_finZero_eq_C' Q_aut
    obtain ⟨y, hy⟩ := hQ_zero.exists
    rw [hc, MvPolynomial.eval_C] at hy
    exact hQ_ne (hc.trans (by rw [hy, map_zero]))
  | succ r =>
    obtain ⟨Q, hQ_nz, hQ_top⟩ := autonomous_log_to_poly_ode' hP_an Q_aut hQ_ne hQ_zero
    let G : ℝ → ℂ := fun u => scaledRay (lambertSeries (fun n => P.eval (n : ℤ))) (Real.log u)
    let H : ℝ → ℂ := fun u => remFun P u + (polyPart P).eval (u : ℂ)
    have hGH : ∀ u : ℝ, 0 < u → G u = H u * (u : ℂ)⁻¹ := fun u hu => by
      have ht_eq : tRay (Real.log u) = (u : ℂ)⁻¹ := by
        unfold tRay; rw [Real.exp_neg, Real.exp_log hu]; push_cast; rfl
      have hq_eq : qRay (Real.log u) = Complex.exp (-((u⁻¹ : ℝ) : ℂ)) := by
        unfold qRay; rw [Real.exp_neg (Real.log u), Real.exp_log hu, Complex.ofReal_exp]; push_cast; rfl
      dsimp only [G, H, scaledRay]
      rw [ht_eq, hq_eq, value_lambertSeries_eq_remFun_add_polyPart P hu, mul_comm]
    have hH_cd : ∀ n : ℕ, ContDiffOn ℝ n H (Ioi (0 : ℝ)) := fun n =>
      (remFun_contDiffOn P n).add (fun u _ => (poly_ofReal_contDiffAt' (polyPart P) n u).contDiffWithinAt)
    obtain ⟨Q_hom, hQhom_ne, hQhom_top⟩ := homogenize_inv_mul_ode' hGH hH_cd Q hQ_nz hQ_top
    obtain ⟨Q', hQ'_ne, hQ'_top⟩ :=
      poly_ode_of_add_poly' (polyPart P) (fun _ _ => rfl) (remFun_contDiffOn P) Q_hom hQhom_ne hQhom_top
    exact hQ'_ne (no_nonautonomous_ade_of_higher_order_borel (borelPhi_borelData P hodd)
      (remFun_hasAsympExp P) Q' hQ'_top)

/-- **Master Theorem A (Pure Quasipolynomial Lambert Series)**:
If a complex quasipolynomial `P` has nonzero odd part `P^- ≠ 0`, then its weighted Lambert series
`H_P(q) = ∑_{n ≥ 1} n P(n) q^n / (1 - q^n)` is unconditionally differentially transcendental over `ℂ(q)`. -/
theorem quasipoly_lambert_pure_algebraicIndependent (P : Quasipoly)
    (hodd : ∃ n : ℤ, P.oddPart n ≠ 0) :
    AlgebraicIndependent ℂ (seriesCoordinates (lambertSeries (fun n => P.eval (n : ℤ)))) := by
  by_contra hdep
  obtain ⟨J, Q_aut, hQ_ne, hQ_zero⟩ :=
    autonomous_transfer_disk (quasipoly_lambertSeries_polyBound P).to_diskCoeffBound hdep
  exact quasipoly_lambert_no_autonomous_ode P hodd Q_aut hQ_ne hQ_zero

/-- **Master Theorem B (Eventually Quasipolynomial Lambert Series — Arbitrary Finite Perturbations)**:
If `w : ℕ → ℂ` agrees for all sufficiently large `n` with a complex quasipolynomial `P` having
nonzero odd part `P^- ≠ 0`, then `H_w(q) = ∑_{n ≥ 1} n w(n) q^n / (1 - q^n)` is unconditionally
differentially transcendental over `ℂ(q)`. -/
theorem quasipoly_lambert_algebraicIndependent (P : Quasipoly)
    (hodd : ∃ n : ℤ, P.oddPart n ≠ 0) {w : ℕ → ℂ}
    (hw : ∀ᶠ n : ℕ in atTop, w n = P.eval (n : ℤ)) :
    AlgebraicIndependent ℂ (seriesCoordinates (lambertSeries w)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hw
  exact algIndep_lambertSeries_of_eventually_eq hN (quasipoly_lambert_pure_algebraicIndependent P hodd)

/-- **Master Theorem C (General Logarithmic-Derivative Transfer)**:
Any nonzero formal power series `G ∈ ℂ[[q]]` whose logarithmic derivative `q G'(q) / G(q)` equals
`H_w(q)` for an eventually-quasipolynomial weight `w` with `P^- ≠ 0` is unconditionally
differentially transcendental over `ℂ(q)`. -/
theorem quasipoly_logDeriv_algebraicIndependent (P : Quasipoly)
    (hodd : ∃ n : ℤ, P.oddPart n ≠ 0) {w : ℕ → ℂ}
    (hw : ∀ᶠ n : ℕ in atTop, w n = P.eval (n : ℤ))
    {G : PowerSeries ℂ} (hG : G ≠ 0)
    (hode : PowerSeries.X * PowerSeries.derivative G = lambertSeries w * G) :
    AlgebraicIndependent ℂ (seriesCoordinates G) :=
  algIndep_of_log_deriv hG hode (quasipoly_lambert_algebraicIndependent P hodd hw)

/-- **Master Theorem D (Complex-Exponent Euler Products)**:
For any weight `w : ℕ → ℂ` eventually agreeing with a quasipolynomial `P` with `P^- ≠ 0`,
the canonical Euler product `G_w(q) = ∏_{n ≥ 1} (1 - q^n)^{-w(n)}` is unconditionally
differentially transcendental over `ℂ(q)`. -/
theorem quasipoly_eulerProduct_algebraicIndependent (P : Quasipoly)
    (hodd : ∃ n : ℤ, P.oddPart n ≠ 0) {w : ℕ → ℂ}
    (hw : ∀ᶠ n : ℕ in atTop, w n = P.eval (n : ℤ)) :
    AlgebraicIndependent ℂ (seriesCoordinates (eulerProduct w)) :=
  quasipoly_logDeriv_algebraicIndependent P hodd hw (eulerProduct_ne_zero w) (eulerProduct_ode w)

/-- **Master Theorem E (Literal Infinite Bose–Euler Products)**:
For any nonnegative integer weight `g : ℕ → ℕ` eventually agreeing with a quasipolynomial `P`
with `P^- ≠ 0`, the literal infinite product `∏'_{n ≥ 1} (1 - q^n)^{-g(n)}`
(`PakPrimes.HarmonicTrap.bose g`) is unconditionally differentially transcendental over `ℂ(q)`. -/
theorem quasipoly_bose_algebraicIndependent (P : Quasipoly)
    (hodd : ∃ n : ℤ, P.oddPart n ≠ 0) {g : ℕ → ℕ}
    (hg : ∀ᶠ n : ℕ in atTop, (g n : ℂ) = P.eval (n : ℤ)) :
    AlgebraicIndependent ℂ (seriesCoordinates (PakPrimes.HarmonicTrap.bose g)) := by
  rw [← eulerProduct_eq_bose g]
  exact quasipoly_eulerProduct_algebraicIndependent P hodd hg

/-! ### 7. Six Unconditional Zero-Hypothesis Corollaries and Even-Parity Controls -/

/-! #### 7.1 Parts `≡ 1 mod 5` Alone vs. Rogers–Ramanujan (`±1 mod 5`) -/

/-- Quasipolynomial `1_{n ≡ 1 (5)}` (period `M = 5`, degree `D = 0`). -/
@[expose] def partsMod5OneQP : Quasipoly where
  M := 5
  hM := by norm_num
  D := 0
  c _ n := if n % 5 = 1 then 1 else 0
  periodic _ n := by simp

private lemma partsMod5OneQP_eval_nat (n : ℕ) :
    partsMod5OneQP.eval (n : ℤ) = if n % 5 = 1 then 1 else 0 := by
  rw [partsMod5OneQP.eval_nat n]
  unfold partsMod5OneQP
  rw [Fin.sum_univ_one]
  simp

private lemma partsMod5OneQP_oddPart_ne_zero : ∃ n : ℤ, partsMod5OneQP.oddPart n ≠ 0 := by
  refine ⟨1, ?_⟩
  unfold Quasipoly.oddPart Quasipoly.eval partsMod5OneQP
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  simp

/-- **Corollary 1a (Parts `≡ 1 mod 5` Lambert Series)**:
`∑_{n ≡ 1 (5)} n q^n / (1 - q^n)` is unconditionally D-transcendental over `ℂ(q)`. -/
theorem partsMod5One_lambert_algebraicIndependent :
    AlgebraicIndependent ℂ (seriesCoordinates (lambertSeries (fun n => if n % 5 = 1 then 1 else 0))) :=
  quasipoly_lambert_algebraicIndependent partsMod5OneQP partsMod5OneQP_oddPart_ne_zero
    (Eventually.of_forall fun n => (partsMod5OneQP_eval_nat n).symm)

/-- **Corollary 1b (Parts `≡ 1 mod 5` Partition Generating Function)**:
`∏_{n ≡ 1 (5)} (1 - q^n)^{-1}` is unconditionally D-transcendental over `ℂ(q)` — in sharp
contrast to the Rogers–Ramanujan product `∏_{n ≡ ±1 (5)} (1 - q^n)^{-1}`, which is modular and
D-algebraic. -/
theorem partsMod5One_algebraicIndependent :
    AlgebraicIndependent ℂ
      (seriesCoordinates (PakPrimes.HarmonicTrap.bose (fun n => if n % 5 = 1 then 1 else 0))) :=
  quasipoly_bose_algebraicIndependent partsMod5OneQP partsMod5OneQP_oddPart_ne_zero
    (Eventually.of_forall fun n => by
      rw [partsMod5OneQP_eval_nat]; split_ifs <;> simp)

/-- Even-parity control: Rogers–Ramanujan indicator `1_{n ≡ ±1 (5)}`. -/
@[expose] def rogersRamanujanQP : Quasipoly where
  M := 5
  hM := by norm_num
  D := 0
  c _ n := if n % 5 = 1 ∨ n % 5 = 4 then 1 else 0
  periodic _ n := by simp

/-- Rogers–Ramanujan has identically vanishing odd part `P^-(n) = 0` for all `n ∈ ℤ`. -/
theorem rogersRamanujan_oddPart_eq_zero (n : ℤ) : rogersRamanujanQP.oddPart n = 0 := by
  unfold Quasipoly.oddPart Quasipoly.eval rogersRamanujanQP
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, mul_one, Nat.cast_ofNat]
  have h1 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases h1 with h | h | h | h | h <;>
  · have hneg : (-n) % 5 = (5 - n % 5) % 5 := by omega
    simp [hneg, h]

/-! #### 7.2 3D Free Conformal Scalar on `S²` (`Z_{S²}(z) = M(z) / M(z²)²`) vs. `S³` -/

/-- Quasipolynomial `n · 1_{2 ∤ n}` (period `M = 2`, degree `D = 1`) for the 3D free conformal
scalar on `S²` (`E_l = 2l + 1`, degeneracy `2l + 1`). -/
@[expose] def conformalScalarS2QP : Quasipoly where
  M := 2
  hM := by norm_num
  D := 1
  c d n := if d.1 = 1 ∧ n % 2 = 1 then 1 else 0
  periodic d n := by simp

private lemma conformalScalarS2QP_eval_nat (n : ℕ) :
    conformalScalarS2QP.eval (n : ℤ) = if n % 2 = 1 then (n : ℂ) else 0 := by
  rw [conformalScalarS2QP.eval_nat n]
  unfold conformalScalarS2QP
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, zero_ne_one, false_and, ↓reduceIte, zero_mul, zero_add,
    true_and, pow_one]
  split_ifs <;> simp

private lemma conformalScalarS2QP_oddPart_ne_zero : ∃ n : ℤ, conformalScalarS2QP.oddPart n ≠ 0 := by
  refine ⟨1, ?_⟩
  unfold Quasipoly.oddPart Quasipoly.eval conformalScalarS2QP
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp

/-- **Corollary 2a (3D Free Conformal Scalar on `S²` Lambert Series)**:
`∑_{k ≥ 0} (2k+1)² z^{2k+1} / (1 - z^{2k+1})` is unconditionally D-transcendental over `ℂ(z)`. -/
theorem conformalScalarS2_lambert_algebraicIndependent :
    AlgebraicIndependent ℂ
      (seriesCoordinates (lambertSeries (fun n => if n % 2 = 1 then (n : ℂ) else 0))) :=
  quasipoly_lambert_algebraicIndependent conformalScalarS2QP conformalScalarS2QP_oddPart_ne_zero
    (Eventually.of_forall fun n => (conformalScalarS2QP_eval_nat n).symm)

/-- **Corollary 2b (3D Free Conformal Scalar on `S²` Partition Function)**:
`Z_{S²}(z) = ∏_{k ≥ 0} (1 - z^{2k+1})^{-(2k+1)} = M(z) / M(z²)²` is unconditionally
D-transcendental over `ℂ(z)`. -/
theorem conformalScalarS2_algebraicIndependent :
    AlgebraicIndependent ℂ
      (seriesCoordinates (PakPrimes.HarmonicTrap.bose (fun n => if n % 2 = 1 then n else 0))) :=
  quasipoly_bose_algebraicIndependent conformalScalarS2QP conformalScalarS2QP_oddPart_ne_zero
    (Eventually.of_forall fun n => by
      rw [conformalScalarS2QP_eval_nat]; split_ifs <;> simp)

/-- Exact MacMahon quotient identity `Z_{S²}(z) · M(z²)² = M(z)`. -/
theorem conformalScalarS2_mul_macMahonExpand_sq :
    PakPrimes.HarmonicTrap.bose (fun n => if n % 2 = 1 then n else 0) *
        (PowerSeries.expand 2 (by norm_num) macmahonSeries) ^ 2 =
      macmahonSeries := by
  let Z : PowerSeries ℂ := PakPrimes.HarmonicTrap.bose (fun n => if n % 2 = 1 then n else 0)
  let M2 : PowerSeries ℂ := PowerSeries.expand 2 (by norm_num) macmahonSeries
  have hM2_ode : PowerSeries.X * PowerSeries.derivative M2 =
      PowerSeries.C (2 : ℂ) * PowerSeries.expand 2 (by norm_num) (sigmaSeries 2) * M2 := by
    have hcoeff_euler : ∀ (F : PowerSeries ℂ) (n : ℕ),
        PowerSeries.coeff n (PowerSeries.X * PowerSeries.derivative F) = (n : ℂ) * PowerSeries.coeff n F := by
      intro F n
      cases n with
      | zero => simp [PowerSeries.coeff_zero_X_mul]
      | succ k => rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]; push_cast; ring
    have hexp_euler : PowerSeries.X * PowerSeries.derivative M2 =
        PowerSeries.C (2 : ℂ) * PowerSeries.expand 2 (by norm_num)
          (PowerSeries.X * PowerSeries.derivative macmahonSeries) := by
      ext n
      rw [hcoeff_euler, PowerSeries.coeff_C_mul]
      by_cases h2 : 2 ∣ n
      · obtain ⟨m, rfl⟩ := h2
        dsimp only [M2]
        rw [PowerSeries.coeff_expand_mul, PowerSeries.coeff_expand_mul, hcoeff_euler]
        push_cast; ring
      · dsimp only [M2]
        rw [PowerSeries.coeff_expand_of_not_dvd 2 (by norm_num) macmahonSeries h2,
          PowerSeries.coeff_expand_of_not_dvd 2 (by norm_num) _ h2, mul_zero, mul_zero]
    rw [hexp_euler, macmahonSeries_ode, map_mul, mul_assoc]
  have hZ_ode : PowerSeries.X * PowerSeries.derivative Z =
      lambertSeries (fun n => if n % 2 = 1 then (n : ℂ) else 0) * Z := by
    dsimp only [Z]
    rw [← eulerProduct_eq_bose]
    have hw : (fun n : ℕ => ((if n % 2 = 1 then n else 0 : ℕ) : ℂ)) =
        fun n : ℕ => if n % 2 = 1 then (n : ℂ) else 0 := by funext n; split_ifs <;> simp
    rw [hw]; exact eulerProduct_ode _
  have hprod_ode : PowerSeries.X * PowerSeries.derivative (Z * M2 ^ 2) =
      lambertSeries (fun n => (n : ℂ)) * (Z * M2 ^ 2) := by
    have hD : PowerSeries.X * PowerSeries.derivative (Z * M2 ^ 2) =
        (lambertSeries (fun n => if n % 2 = 1 then (n : ℂ) else 0) +
          PowerSeries.C (4 : ℂ) * PowerSeries.expand 2 (by norm_num) (sigmaSeries 2)) * (Z * M2 ^ 2) := by
      rw [Derivation.leibniz, PowerSeries.derivative_pow]
      simp only [smul_eq_mul, Nat.cast_ofNat, show 2 - 1 = 1 by rfl, pow_one]
      have h4 : PowerSeries.C (4 : ℂ) = PowerSeries.C (2 : ℂ) * PowerSeries.C (2 : ℂ) := by
        rw [← map_mul]; norm_num
      have h2C : (2 : PowerSeries ℂ) = PowerSeries.C (2 : ℂ) := by
        rw [← map_ofNat (PowerSeries.C (R := ℂ)) 2]
      rw [h4, h2C]
      linear_combination M2 ^ 2 * hZ_ode + PowerSeries.C (2 : ℂ) * Z * M2 * hM2_ode
    rw [hD]
    congr 1
    ext n
    rw [map_add, PowerSeries.coeff_C_mul, coeff_lambertSeries, coeff_lambertSeries]
    by_cases hn0 : n = 0
    · subst hn0
      have he0 : PowerSeries.coeff 0 (PowerSeries.expand 2 (by norm_num) (sigmaSeries 2)) = 0 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_expand,
          ← PowerSeries.coeff_zero_eq_constantCoeff]
        simp [sigmaSeries]
      simp [he0]
    · simp only [hn0, ↓reduceIte]
      have hsplit : ∑ d ∈ n.divisors, (d : ℂ) * (d : ℂ) =
          (∑ d ∈ n.divisors.filter (fun d => d % 2 = 1), (d : ℂ) * (d : ℂ)) +
            ∑ d ∈ n.divisors.filter (fun d => ¬ d % 2 = 1), (d : ℂ) * (d : ℂ) :=
        (Finset.sum_filter_add_sum_filter_not n.divisors (fun d => d % 2 = 1) _).symm
      have hodd_sum : (∑ d ∈ n.divisors, (d : ℂ) * if d % 2 = 1 then (d : ℂ) else 0) =
          ∑ d ∈ n.divisors.filter (fun d => d % 2 = 1), (d : ℂ) * (d : ℂ) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun d _ => by split_ifs <;> simp
      have heven_sum : (4 : ℂ) * PowerSeries.coeff n (PowerSeries.expand 2 (by norm_num) (sigmaSeries 2)) =
          ∑ d ∈ n.divisors.filter (fun d => ¬ d % 2 = 1), (d : ℂ) * (d : ℂ) := by
        by_cases h2 : 2 ∣ n
        · obtain ⟨m, rfl⟩ := h2
          have hm0 : m ≠ 0 := by omega
          rw [PowerSeries.coeff_expand_mul]
          simp only [sigmaSeries, PowerSeries.coeff_mk, hm0, ↓reduceIte, Finset.mul_sum]
          refine Finset.sum_bij (fun k _ => 2 * k)
            (fun k hk => Finset.mem_filter.mpr
              ⟨Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left 2 (Nat.dvd_of_mem_divisors hk), hn0⟩,
                by omega⟩)
            (fun a _ b _ h => by omega)
            (fun d hd => by
              obtain ⟨hdv, hne⟩ := Finset.mem_filter.mp hd
              have h2d : 2 ∣ d := by omega
              obtain ⟨k, rfl⟩ := h2d
              exact ⟨k, Nat.mem_divisors.mpr ⟨(Nat.mul_dvd_mul_iff_left (by norm_num)).mp
                (Nat.dvd_of_mem_divisors hdv), hm0⟩, rfl⟩)
            (fun k _ => by push_cast; ring)
        · rw [PowerSeries.coeff_expand_of_not_dvd 2 (by norm_num) (sigmaSeries 2) h2, mul_zero]
          symm
          refine Finset.sum_eq_zero fun d hd => ?_
          obtain ⟨hdv, hne⟩ := Finset.mem_filter.mp hd
          have h2d : 2 ∣ d := by omega
          exact absurd (dvd_trans h2d (Nat.dvd_of_mem_divisors hdv)) h2
      rw [hsplit, hodd_sum, heven_sum]
  have hM_eq_lam : sigmaSeries 2 = lambertSeries (fun n => (n : ℂ)) := by
    ext n
    rw [coeff_lambertSeries]
    by_cases hn0 : n = 0
    · subst hn0; simp [sigmaSeries]
    · simp only [sigmaSeries, PowerSeries.coeff_mk, hn0, ↓reduceIte]
      exact Finset.sum_congr rfl fun d _ => by ring
  have hZ_eq : Z * M2 ^ 2 = eulerProduct (fun n => (n : ℂ)) := by
    refine eq_eulerProduct_of_ode (fun n => (n : ℂ)) ?_ hprod_ode
    rw [map_mul, map_pow, PakPrimes.HarmonicTrap.bose_constantCoeff,
      PowerSeries.constantCoeff_expand, macmahonSeries_constantCoeff]
    ring
  have hM_eq : macmahonSeries = eulerProduct (fun n => (n : ℂ)) :=
    eq_eulerProduct_of_ode (fun n => (n : ℂ)) macmahonSeries_constantCoeff (hM_eq_lam ▸ macmahonSeries_ode)
  exact hZ_eq.trans hM_eq.symm

/-- Even-parity control: 3D free conformal scalar on `S³` (`P(n) = n²`, `D = 2`, `M = 1`). -/
@[expose] def conformalScalarS3QP : Quasipoly where
  M := 1
  hM := by norm_num
  D := 2
  c d _ := if d.1 = 2 then 1 else 0
  periodic _ _ := rfl

/-- The 3D conformal scalar on `S³` has identically vanishing odd part `P^-(n) = 0`. -/
theorem conformalScalarS3_oddPart_eq_zero (n : ℤ) : conformalScalarS3QP.oddPart n = 0 := by
  unfold Quasipoly.oddPart Quasipoly.eval conformalScalarS3QP
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Int.cast_neg]
  norm_num

/-! #### 7.3 3D Harmonic Trap Shifted by `± 1/2` Quantum vs. Physical `3/2` Trap -/

/-- General shifted 3D harmonic trap quasipolynomial `P_s(n) = (n² + s n) / 2` (`M = 1, D = 2`). -/
@[expose] def shiftedTrap3DQP (s : ℂ) : Quasipoly where
  M := 1
  hM := by norm_num
  D := 2
  c d _ := if d.1 = 2 then 1 / 2 else if d.1 = 1 then s / 2 else 0
  periodic _ _ := rfl

private lemma shiftedTrap3DQP_eval_nat (s : ℂ) (n : ℕ) :
    (shiftedTrap3DQP s).eval (n : ℤ) = ((n : ℂ) ^ 2 + s * (n : ℂ)) / 2 := by
  rw [(shiftedTrap3DQP s).eval_nat n]
  unfold shiftedTrap3DQP
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num; ring

private lemma shiftedTrap3DQP_oddPart_ne_zero {s : ℂ} (hs : s ≠ 0) :
    ∃ n : ℤ, (shiftedTrap3DQP s).oddPart n ≠ 0 := by
  refine ⟨1, ?_⟩
  unfold Quasipoly.oddPart Quasipoly.eval shiftedTrap3DQP
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Int.cast_one, Int.cast_neg]
  norm_num
  exact hs

/-- **Corollary 3a (General Nonzero Shift 3D Harmonic Trap Lambert Series)**:
For EVERY `s ≠ 0`, `∑_{n ≥ 1} n ((n² + s n)/2) q^n / (1 - q^n)` is unconditionally
D-transcendental over `ℂ(q)`. -/
theorem shiftedTrap3D_lambert_algebraicIndependent {s : ℂ} (hs : s ≠ 0) :
    AlgebraicIndependent ℂ
      (seriesCoordinates (lambertSeries (fun n => ((n : ℂ) ^ 2 + s * (n : ℂ)) / 2))) :=
  quasipoly_lambert_algebraicIndependent (shiftedTrap3DQP s) (shiftedTrap3DQP_oddPart_ne_zero hs)
    (Eventually.of_forall fun n => (shiftedTrap3DQP_eval_nat s n).symm)

/-- **Corollary 3b (3D Harmonic Trap Shifted by `+1/2` Quantum)**:
`∏_{n ≥ 1} (1 - q^n)^{-C(n+1, 2)}` (`P(n) = (n² + n)/2`) is unconditionally D-transcendental over `ℂ(q)`. -/
theorem shiftedTrap3D_plus_algebraicIndependent :
    AlgebraicIndependent ℂ
      (seriesCoordinates (PakPrimes.HarmonicTrap.bose (fun n => (n + 1).choose 2))) :=
  quasipoly_bose_algebraicIndependent (shiftedTrap3DQP 1) (shiftedTrap3DQP_oddPart_ne_zero one_ne_zero)
    (Eventually.of_forall fun n => by
      rw [shiftedTrap3DQP_eval_nat]
      have h2 : 2 * ((n + 1).choose 2) = (n + 1) * n := by
        have hd := Nat.descFactorial_eq_factorial_mul_choose (n + 1) 2
        simp [Nat.descFactorial, Nat.factorial] at hd
        nlinarith [hd]
      have h2c : (2 : ℂ) * (((n + 1).choose 2 : ℕ) : ℂ) = ((n : ℂ) + 1) * (n : ℂ) := by
        exact_mod_cast h2
      linear_combination (1 / 2 : ℂ) * h2c)

/-- **Corollary 3c (3D Harmonic Trap Shifted by `-1/2` Quantum)**:
`∏_{n ≥ 1} (1 - q^n)^{-C(n, 2)}` (`P(n) = (n² - n)/2`, `PakPrimes.HarmonicTrap.bose (·.choose 2)`)
is unconditionally D-transcendental over `ℂ(q)`. -/
theorem shiftedTrap3D_minus_algebraicIndependent :
    AlgebraicIndependent ℂ
      (seriesCoordinates (PakPrimes.HarmonicTrap.bose (fun n => n.choose 2))) :=
  quasipoly_bose_algebraicIndependent (shiftedTrap3DQP (-1))
    (shiftedTrap3DQP_oddPart_ne_zero (by norm_num))
    (Eventually.of_forall fun n => by
      rw [shiftedTrap3DQP_eval_nat]
      cases n with
      | zero => simp
      | succ k =>
        have h2 : 2 * ((k + 1).choose 2) = (k + 1) * k := by
          have hd := Nat.descFactorial_eq_factorial_mul_choose (k + 1) 2
          simp [Nat.descFactorial, Nat.factorial] at hd
          nlinarith [hd]
        have h2c : (2 : ℂ) * (((k + 1).choose 2 : ℕ) : ℂ) = ((k : ℂ) + 1) * (k : ℂ) := by
          exact_mod_cast h2
        push_cast
        linear_combination (1 / 2 : ℂ) * h2c)

/-- Even-parity control: physical `3/2`-zero-point 3D harmonic trap in half-quanta
(`P(E) = 1_{2 ∤ E} · (E² - 1) / 8`, matching `PakPrimes.HarmonicTrap.centeredDeg`). -/
@[expose] def centeredTrap3DQP : Quasipoly where
  M := 2
  hM := by norm_num
  D := 2
  c d n := if n % 2 = 1 then (if d.1 = 2 then 1 / 8 else if d.1 = 0 then -(1 / 8) else 0) else 0
  periodic d n := by simp

/-- The physical `3/2` harmonic trap has identically vanishing odd part `P^-(E) = 0`. -/
theorem centeredTrap3D_oddPart_eq_zero (n : ℤ) : centeredTrap3DQP.oddPart n = 0 := by
  unfold Quasipoly.oddPart Quasipoly.eval centeredTrap3DQP
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  have hmod : ((-n) % (2 : ℤ)).toNat = (n % (2 : ℤ)).toNat := by
    congr 1; omega
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Int.cast_neg, Nat.cast_ofNat, hmod]
  norm_num

/-! #### 7.4 Rational Convex Polytope Ehrhart Products for `[0, 1]` -/

/-- Ehrhart polynomial `L_{[0,1]}(n) = n + 1` (`M = 1, D = 1`). -/
@[expose] def ehrhartSegmentQP : Quasipoly where
  M := 1
  hM := by norm_num
  D := 1
  c _ _ := 1
  periodic _ _ := rfl

/-- Interior Ehrhart polynomial `I_{[0,1]}(n) = n - 1` (`M = 1, D = 1`). -/
@[expose] def ehrhartSegmentInteriorQP : Quasipoly where
  M := 1
  hM := by norm_num
  D := 1
  c d _ := if d.1 = 1 then 1 else -1
  periodic _ _ := rfl

private lemma ehrhartSegmentQP_eval_nat (n : ℕ) :
    ehrhartSegmentQP.eval (n : ℤ) = (n : ℂ) + 1 := by
  rw [ehrhartSegmentQP.eval_nat n]
  unfold ehrhartSegmentQP
  rw [Fin.sum_univ_two]; simp; ring

private lemma ehrhartSegmentInteriorQP_eval_nat (n : ℕ) :
    ehrhartSegmentInteriorQP.eval (n : ℤ) = (n : ℂ) - 1 := by
  rw [ehrhartSegmentInteriorQP.eval_nat n]
  unfold ehrhartSegmentInteriorQP
  rw [Fin.sum_univ_two]; simp; ring

private lemma ehrhartSegmentQP_oddPart_ne_zero : ∃ n : ℤ, ehrhartSegmentQP.oddPart n ≠ 0 := by
  refine ⟨1, ?_⟩
  unfold Quasipoly.oddPart Quasipoly.eval ehrhartSegmentQP
  rw [Fin.sum_univ_two, Fin.sum_univ_two]; norm_num

private lemma ehrhartSegmentInteriorQP_oddPart_ne_zero :
    ∃ n : ℤ, ehrhartSegmentInteriorQP.oddPart n ≠ 0 := by
  refine ⟨1, ?_⟩
  unfold Quasipoly.oddPart Quasipoly.eval ehrhartSegmentInteriorQP
  rw [Fin.sum_univ_two, Fin.sum_univ_two]; norm_num

/-- **Corollary 4a (Closed-Segment Ehrhart Euler Product)**:
`∏_{n ≥ 1} (1 - q^n)^{-(n + 1)}` is unconditionally D-transcendental over `ℂ(q)`. -/
theorem ehrhartSegment_algebraicIndependent :
    AlgebraicIndependent ℂ
      (seriesCoordinates (PakPrimes.HarmonicTrap.bose (fun n => n + 1))) :=
  quasipoly_bose_algebraicIndependent ehrhartSegmentQP ehrhartSegmentQP_oddPart_ne_zero
    (Eventually.of_forall fun n => by rw [ehrhartSegmentQP_eval_nat]; push_cast; rfl)

/-- **Corollary 4b (Open-Segment Interior Ehrhart Euler Product)**:
`∏_{n ≥ 1} (1 - q^n)^{-(n - 1)}` is unconditionally D-transcendental over `ℂ(q)` (even though
the Ehrhart quotient `G_L / G_I = ∏_{n ≥ 1} (1 - q^n)^{-2}` is modular and D-algebraic!). -/
theorem ehrhartSegmentInterior_algebraicIndependent :
    AlgebraicIndependent ℂ
      (seriesCoordinates (PakPrimes.HarmonicTrap.bose (fun n => n - 1))) :=
  quasipoly_bose_algebraicIndependent ehrhartSegmentInteriorQP ehrhartSegmentInteriorQP_oddPart_ne_zero
    (eventually_atTop.mpr ⟨1, fun n hn => by
      rw [ehrhartSegmentInteriorQP_eval_nat, Nat.cast_sub hn, Nat.cast_one]⟩)

/-- Even-parity control: Ehrhart difference `L_{[0,1]}(n) - I_{[0,1]}(n) = 2`. -/
@[expose] def ehrhartSegmentQuotientQP : Quasipoly where
  M := 1
  hM := by norm_num
  D := 0
  c _ _ := 2
  periodic _ _ := rfl

/-- The Ehrhart quotient weight `L - I = 2` has identically vanishing odd part. -/
theorem ehrhartSegment_quotient_oddPart_eq_zero (n : ℤ) :
    ehrhartSegmentQuotientQP.oddPart n = 0 := by
  unfold Quasipoly.oddPart Quasipoly.eval ehrhartSegmentQuotientQP
  simp

/-! #### 7.5 Twisted Odd Dirichlet Character Lambert & Euler Series (`χ_{-3}`, `χ_{-4}`) -/

/-- Primitive odd quadratic character `χ_{-3}` modulo 3. -/
@[expose] def chi3Val (n : ℕ) : ℂ :=
  if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0

/-- Primitive odd quadratic character `χ_{-4}` modulo 4. -/
@[expose] def chi4Val (n : ℕ) : ℂ :=
  if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0

/-- Quasipolynomial `χ_{-3}(n) · n^{2m}` (`M = 3, D = 2m`). -/
@[expose] def chi3PowQP (m : ℕ) : Quasipoly where
  M := 3
  hM := by norm_num
  D := 2 * m
  c d n := if d.1 = 2 * m then chi3Val n else 0
  periodic d n := by simp [chi3Val]

/-- Quasipolynomial `χ_{-4}(n) · n^{2m}` (`M = 4, D = 2m`). -/
@[expose] def chi4PowQP (m : ℕ) : Quasipoly where
  M := 4
  hM := by norm_num
  D := 2 * m
  c d n := if d.1 = 2 * m then chi4Val n else 0
  periodic d n := by simp [chi4Val]

private lemma chi3PowQP_eval_nat (m n : ℕ) :
    (chi3PowQP m).eval (n : ℤ) = chi3Val n * (n : ℂ) ^ (2 * m) := by
  rw [(chi3PowQP m).eval_nat n]
  unfold chi3PowQP
  rw [Finset.sum_eq_single (Fin.last (2 * m))]
  · simp
  · intro d _ hd
    have hne : d.1 ≠ 2 * m := fun h => hd (Fin.ext h)
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma chi4PowQP_eval_nat (m n : ℕ) :
    (chi4PowQP m).eval (n : ℤ) = chi4Val n * (n : ℂ) ^ (2 * m) := by
  rw [(chi4PowQP m).eval_nat n]
  unfold chi4PowQP
  rw [Finset.sum_eq_single (Fin.last (2 * m))]
  · simp
  · intro d _ hd
    have hne : d.1 ≠ 2 * m := fun h => hd (Fin.ext h)
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma chi3PowQP_oddPart_ne_zero (m : ℕ) : ∃ n : ℤ, (chi3PowQP m).oddPart n ≠ 0 := by
  refine ⟨1, ?_⟩
  unfold Quasipoly.oddPart Quasipoly.eval chi3PowQP
  rw [Finset.sum_eq_single (Fin.last (2 * m)), Finset.sum_eq_single (Fin.last (2 * m))]
  · simp only [Fin.val_last, ↓reduceIte, Int.cast_one, Int.cast_neg, one_pow, mul_one,
      Nat.cast_ofNat]
    have hev : (-1 : ℂ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
    rw [hev, mul_one]
    have h1 : ((1 : ℤ) % (3 : ℤ)).toNat = 1 := by decide
    have h2 : ((-1 : ℤ) % (3 : ℤ)).toNat = 2 := by decide
    rw [h1, h2]; simp [chi3Val]
  · intro d _ hd; simp [show d.1 ≠ 2 * m from fun h => hd (Fin.ext h)]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro d _ hd; simp [show d.1 ≠ 2 * m from fun h => hd (Fin.ext h)]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma chi4PowQP_oddPart_ne_zero (m : ℕ) : ∃ n : ℤ, (chi4PowQP m).oddPart n ≠ 0 := by
  refine ⟨1, ?_⟩
  unfold Quasipoly.oddPart Quasipoly.eval chi4PowQP
  rw [Finset.sum_eq_single (Fin.last (2 * m)), Finset.sum_eq_single (Fin.last (2 * m))]
  · simp only [Fin.val_last, ↓reduceIte, Int.cast_one, Int.cast_neg, one_pow, mul_one,
      Nat.cast_ofNat]
    have hev : (-1 : ℂ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
    rw [hev, mul_one]
    have h1 : ((1 : ℤ) % (4 : ℤ)).toNat = 1 := by decide
    have h2 : ((-1 : ℤ) % (4 : ℤ)).toNat = 3 := by decide
    rw [h1, h2]; simp [chi4Val]
  · intro d _ hd; simp [show d.1 ≠ 2 * m from fun h => hd (Fin.ext h)]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro d _ hd; simp [show d.1 ≠ 2 * m from fun h => hd (Fin.ext h)]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Corollary 5a (`χ_{-3}`-Twisted Odd-Character Lambert Series)**:
For every `m : ℕ`, `∑_{n ≥ 1} χ_{-3}(n) n^{2m + 1} q^n / (1 - q^n)` is unconditionally
D-transcendental over `ℂ(q)`. -/
theorem twistedLambertChi3_algebraicIndependent (m : ℕ) :
    AlgebraicIndependent ℂ
      (seriesCoordinates (lambertSeries (fun n => chi3Val n * (n : ℂ) ^ (2 * m)))) :=
  quasipoly_lambert_algebraicIndependent (chi3PowQP m) (chi3PowQP_oddPart_ne_zero m)
    (Eventually.of_forall fun n => (chi3PowQP_eval_nat m n).symm)

/-- **Corollary 5b (`χ_{-3}`-Twisted Euler Product)**:
For every `m : ℕ`, `∏_{n ≥ 1} (1 - q^n)^{-χ_{-3}(n) n^{2m}}` is unconditionally D-transcendental over `ℂ(q)`. -/
theorem twistedEulerChi3_algebraicIndependent (m : ℕ) :
    AlgebraicIndependent ℂ
      (seriesCoordinates (eulerProduct (fun n => chi3Val n * (n : ℂ) ^ (2 * m)))) :=
  quasipoly_eulerProduct_algebraicIndependent (chi3PowQP m) (chi3PowQP_oddPart_ne_zero m)
    (Eventually.of_forall fun n => (chi3PowQP_eval_nat m n).symm)

/-- **Corollary 5c (`χ_{-4}`-Twisted Odd-Character Lambert Series)**:
For every `m : ℕ`, `∑_{n ≥ 1} χ_{-4}(n) n^{2m + 1} q^n / (1 - q^n)` is unconditionally
D-transcendental over `ℂ(q)`. -/
theorem twistedLambertChi4_algebraicIndependent (m : ℕ) :
    AlgebraicIndependent ℂ
      (seriesCoordinates (lambertSeries (fun n => chi4Val n * (n : ℂ) ^ (2 * m)))) :=
  quasipoly_lambert_algebraicIndependent (chi4PowQP m) (chi4PowQP_oddPart_ne_zero m)
    (Eventually.of_forall fun n => (chi4PowQP_eval_nat m n).symm)

/-- **Corollary 5d (`χ_{-4}`-Twisted Euler Product)**:
For every `m : ℕ`, `∏_{n ≥ 1} (1 - q^n)^{-χ_{-4}(n) n^{2m}}` is unconditionally D-transcendental over `ℂ(q)`. -/
theorem twistedEulerChi4_algebraicIndependent (m : ℕ) :
    AlgebraicIndependent ℂ
      (seriesCoordinates (eulerProduct (fun n => chi4Val n * (n : ℂ) ^ (2 * m)))) :=
  quasipoly_eulerProduct_algebraicIndependent (chi4PowQP m) (chi4PowQP_oddPart_ne_zero m)
    (Eventually.of_forall fun n => (chi4PowQP_eval_nat m n).symm)

/-! #### 7.6 Finite-Perturbation Invariance Control (`1_{n ≡ 1 (5)} + δ_{n,1} - 3 δ_{n,2}`) -/

/-- Finitely perturbed weight `w(n) = 1_{n ≡ 1 (5)} + δ_{n,1} - 3 δ_{n,2}`. -/
@[expose] def partsMod5OnePerturbed (n : ℕ) : ℂ :=
  (if n % 5 = 1 then 1 else 0) + (if n = 1 then 1 else 0) - (if n = 2 then 3 else 0)

/-- **Corollary 6a (Finite Perturbation Control — Lambert Series)**:
Adding `δ_{n,1} - 3 δ_{n,2}` changes the Lambert series by the rational function
`q/(1 - q) - 6 q²/(1 - q²) ∈ ℂ(q)` and leaves differential transcendence completely invariant. -/
theorem partsMod5One_perturbed_lambert_algebraicIndependent :
    AlgebraicIndependent ℂ (seriesCoordinates (lambertSeries partsMod5OnePerturbed)) :=
  quasipoly_lambert_algebraicIndependent partsMod5OneQP partsMod5OneQP_oddPart_ne_zero
    (eventually_atTop.mpr ⟨3, fun n hn => by
      rw [partsMod5OneQP_eval_nat]
      unfold partsMod5OnePerturbed
      have h1 : n ≠ 1 := by omega
      have h2 : n ≠ 2 := by omega
      simp [h1, h2]⟩)

/-- **Corollary 6b (Finite Perturbation Control — Euler Product)**:
`(1 - q)^{-1} (1 - q²)^3 ∏_{n ≡ 1 (5)} (1 - q^n)^{-1}` is unconditionally D-transcendental over `ℂ(q)`. -/
theorem partsMod5One_perturbed_algebraicIndependent :
    AlgebraicIndependent ℂ (seriesCoordinates (eulerProduct partsMod5OnePerturbed)) :=
  quasipoly_eulerProduct_algebraicIndependent partsMod5OneQP partsMod5OneQP_oddPart_ne_zero
    (eventually_atTop.mpr ⟨3, fun n hn => by
      rw [partsMod5OneQP_eval_nat]
      unfold partsMod5OnePerturbed
      have h1 : n ≠ 1 := by omega
      have h2 : n ≠ 2 := by omega
      simp [h1, h2]⟩)

end
end PakPrimes.QuasipolynomialEulerParity

