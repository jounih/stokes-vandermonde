module

public import PakPrimes.HigherOrderStokes
public import PakPrimes.AutonomousTransfer
public import PakPrimes.HolderGamma
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Pak–Yeliussizov Differential Transcendence for Meromorphic EGFs (`EGF → OGF`)

This module formalizes the end-to-end **Borel–EGF differential-transcendence bridge**
(`EGF → OGF`) in `PowerSeries ℂ` directly on top of `PakPrimes.HigherOrderStokes`, proving
unconditional OGF differential transcendence for wide families of meromorphic EGFs:

1. **Exact Formal `EGF → OGF` Bridge (`ogfOfSeq`, `ogfOfEGF`, `ogf_algebraicIndependent_of_higherOrderBorel`)**:
   For any `E : ℂ → ℂ`, its Ordinary Generating Function is
   `ogfOfEGF E = PowerSeries.mk fun n => iteratedDeriv n E 0`,
   satisfying `formalSeries E = PowerSeries.X * ogfOfEGF E`.
   Using the exact algebraic identity expressing `PowerSeries.X ^ (2 * j + 1) * seriesJet F j`
   in terms of `d_u^[k] (PowerSeries.X * F)` (`0 ≤ k ≤ j`) and inverting the triangular
   differential substitution in `LaurentSeries ℂ`, ANY `HigherOrderBorelData` witness on `E`
   implies `AlgebraicIndependent ℂ (seriesCoordinates (ogfOfEGF E))` in `ℂ[[x]]`.
2. **Polynomial-Shift & Subring Transfer (`algIndep_seriesCoordinates_add_poly`, `ogf_no_poly_ade_of_higherOrderBorel`)**:
   Proves invariance of `AlgebraicIndependent ℂ (seriesCoordinates F)` under adding any
   polynomial `p : Polynomial ℂ`, and derives explicit non-existence of non-autonomous
   differential equations over `ℂ[x]`.
3. **Arbitrary-Order Meromorphic Pole Engine (`laurent_jet_expansion`, `pole_principalPart_of_simpleZero_div_pow`)**:
   Derives principal-part expansions of arbitrary finite order `p ≥ 1` for quotients `g / f^p`
   at any simple zero of `f`.
4. **Tier-1 Showcase Corollaries (Zero Hypotheses, Strictly Standard Axioms)**:
   - **Bernoulli Numbers OGF** (`bernOGF_algebraicIndependent`): `E(ξ) = ξ / (e^ξ - 1)` (`θ₀ = π/2`).
   - **Tangent & Secant / Euler Numbers OGFs** (`tanOGF_algebraicIndependent`, `secOGF_algebraicIndependent`),
     plus explicit `D`-algebraicity of `tan` and `sec`.
   - **Double-Pole `sec^2 ξ` & Arbitrary-Order `sec^p ξ` OGFs** (`sec2OGF_algebraicIndependent`, `secPowOGF_algebraicIndependent`).
   - **General Briot–Bouquet Rational-Exponential Family** (`ratExpOGF_algebraicIndependent`):
     `E(ξ) = (1 - c * exp (lam * ξ))⁻¹ ^ p` for ALL `lam ≠ 0`, `‖c‖ = 1` (`c ≠ 1`), and `p ≥ 1`
     (including **Euler/Genocchi** `(1 + exp ξ)⁻¹ ^ p`), together with its explicit Briot–Bouquet
     autonomous ODE `(E' + p lam E)^p = (p lam)^p E^{p+1}`.
   - **Higher-Order Dirichlet, Trigamma, and Lambert OGFs**.
-/

set_option maxHeartbeats 1200000

public section
namespace PakPrimes.PakYeliussizovEGF

open Complex Real Filter MeasureTheory Set MvPolynomial
open PakPrimes.BorelStokesVandermonde
open PakPrimes.GeneralTheorem2
open PakPrimes.HigherOrderStokes
open PakPrimes.PrimeNome
open PakPrimes.HolderGamma
open scoped Topology Interval

noncomputable section

/-! ### 1. Exact OGF Definitions and the `EGF → OGF` Algebraic Bridge -/

/-- Ordinary generating function `∑_{n ≥ 0} a_n x^n` associated with a sequence `a : ℕ → ℂ`. -/
@[expose] def ogfOfSeq (a : ℕ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk a

/-- Ordinary generating function `∑_{n ≥ 0} E^{(n)}(0) x^n` associated with an EGF `E : ℂ → ℂ`
(where `E(ξ) = ∑_{n ≥ 0} E^{(n)}(0) ξ^n / n!`). -/
@[expose] def ogfOfEGF (E : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => iteratedDeriv n E 0

/-- Exact formal identity `formalSeries E = x * ogfOfEGF E` in `ℂ[[x]]`. -/
lemma formalSeries_eq_X_mul_ogfOfEGF (E : ℂ → ℂ) :
    formalSeries E = PowerSeries.X * ogfOfEGF E := by
  ext n
  cases n with
  | zero =>
    simp [formalSeries]
  | succ k =>
    simp [formalSeries, ogfOfEGF, PowerSeries.coeff_succ_X_mul]

private lemma d_u_C_mul (c : ℂ) (A : PowerSeries ℂ) :
    d_u (PowerSeries.C c * A) = PowerSeries.C c * d_u A := by
  simp only [d_u, Derivation.leibniz, PowerSeries.derivative_C, smul_eq_mul]
  ring

private lemma d_u_mul (A B : PowerSeries ℂ) :
    d_u (A * B) = d_u A * B + A * d_u B := by
  simp only [d_u, Derivation.leibniz, smul_eq_mul]
  ring

private lemma d_u_X_pow (m : ℕ) :
    d_u (PowerSeries.X ^ m : PowerSeries ℂ) =
      -(PowerSeries.C (m : ℂ) * PowerSeries.X ^ (m + 1)) := by
  cases m with
  | zero =>
    simp [d_u]
  | succ m =>
    rw [d_u, PowerSeries.derivative_pow, PowerSeries.derivative_X, mul_one, Nat.succ_sub_one]
    have hm : ((m + 1 : ℕ) : PowerSeries ℂ) = PowerSeries.C ((m + 1 : ℕ) : ℂ) := by
      rw [← map_natCast PowerSeries.C]
    rw [hm]
    ring

/-- Explicit triangular coefficients expressing `x^{2j+1} (d/dx)^j F` in terms of `d_u^k (x F)`. -/
private def backCoeff : ℕ → ℕ → ℂ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | j + 1, 0 => -((j + 1 : ℕ) : ℂ) * backCoeff j 0
  | j + 1, k + 1 => -((j + k + 2 : ℕ) : ℂ) * backCoeff j (k + 1) - backCoeff j k

private lemma backCoeff_gt {j k : ℕ} (hk : j < k) : backCoeff j k = 0 := by
  induction j generalizing k with
  | zero =>
    cases k with
    | zero => omega
    | succ m => rfl
  | succ j ih =>
    cases k with
    | zero => omega
    | succ m =>
      have hm1 : j < m + 1 := by omega
      have hm2 : j < m := by omega
      simp [backCoeff, ih hm1, ih hm2]

private lemma backCoeff_diag (j : ℕ) : backCoeff j j = (-1 : ℂ) ^ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [backCoeff, backCoeff_gt (Nat.lt_succ_self j), mul_zero, zero_sub, ih, pow_succ]
    ring

private lemma X_pow_mul_seriesJet (F : PowerSeries ℂ) (j : ℕ) :
    PowerSeries.X ^ (2 * j + 1) * seriesJet F j =
      ∑ k ∈ Finset.range (j + 1),
        PowerSeries.C (backCoeff j k) * PowerSeries.X ^ (j - k) * d_u^[k] (PowerSeries.X * F) := by
  let S : PowerSeries ℂ := PowerSeries.X * F
  induction j with
  | zero =>
    simp [seriesJet, backCoeff]
  | succ j ih =>
    have hdu_lhs :
        d_u (PowerSeries.X ^ (2 * j + 1) * seriesJet F j) =
          -(PowerSeries.C ((2 * j + 1 : ℕ) : ℂ) * PowerSeries.X ^ (2 * j + 2) * seriesJet F j) -
            PowerSeries.X ^ (2 * (j + 1) + 1) * seriesJet F (j + 1) := by
      rw [d_u_mul, d_u_X_pow]
      have hdu_jet : d_u (seriesJet F j) = -(PowerSeries.X ^ 2 * seriesJet F (j + 1)) := by
        rw [d_u, seriesJet, seriesJet, Function.iterate_succ_apply']
      rw [hdu_jet, show (2 * j + 1) + 1 = 2 * j + 2 by omega,
        show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega, pow_add]
      ring
    have hstep_lhs :
        PowerSeries.X ^ (2 * (j + 1) + 1) * seriesJet F (j + 1) =
          -(PowerSeries.C ((2 * j + 1 : ℕ) : ℂ) * PowerSeries.X) *
              (PowerSeries.X ^ (2 * j + 1) * seriesJet F j) -
            d_u (PowerSeries.X ^ (2 * j + 1) * seriesJet F j) := by
      rw [hdu_lhs, show 2 * j + 2 = 1 + (2 * j + 1) by omega, pow_add, pow_one]
      ring
    rw [hstep_lhs, ih]
    have h_first :
        -(PowerSeries.C ((2 * j + 1 : ℕ) : ℂ) * PowerSeries.X) *
            ∑ k ∈ Finset.range (j + 1),
              PowerSeries.C (backCoeff j k) * PowerSeries.X ^ (j - k) * d_u^[k] S =
          ∑ k ∈ Finset.range (j + 1),
            PowerSeries.C (-((2 * j + 1 : ℕ) : ℂ) * backCoeff j k) *
              PowerSeries.X ^ (j + 1 - k) * d_u^[k] S := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [show j + 1 - k = 1 + (j - k) by omega, pow_add, pow_one, map_mul, map_neg]
      ring
    have h_du_sum :
        d_u (∑ k ∈ Finset.range (j + 1),
              PowerSeries.C (backCoeff j k) * PowerSeries.X ^ (j - k) * d_u^[k] S) =
          ∑ k ∈ Finset.range (j + 1),
            (PowerSeries.C (-((j - k : ℕ) : ℂ) * backCoeff j k) *
                PowerSeries.X ^ (j + 1 - k) * d_u^[k] S +
              PowerSeries.C (backCoeff j k) * PowerSeries.X ^ (j + 1 - (k + 1)) *
                d_u^[k + 1] S) := by
      have h_lin : ∀ (s : Finset ℕ) (f : ℕ → PowerSeries ℂ),
          d_u (∑ k ∈ s, f k) = ∑ k ∈ s, d_u (f k) := by
        intro s f
        simp only [d_u, map_sum, Finset.mul_sum, Finset.sum_neg_distrib]
      rw [h_lin]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [mul_assoc (PowerSeries.C (backCoeff j k)), d_u_C_mul, d_u_mul, d_u_X_pow,
        ← Function.iterate_succ_apply' d_u k S,
        show j + 1 - k = (j - k) + 1 by omega,
        show j + 1 - (k + 1) = j - k by omega]
      simp only [map_mul, map_neg]
      ring
    rw [h_first, h_du_sum, Finset.sum_add_distrib]
    let A (k : ℕ) : PowerSeries ℂ :=
      PowerSeries.C (-((j + k + 1 : ℕ) : ℂ) * backCoeff j k) * PowerSeries.X ^ (j + 1 - k) * d_u^[k] S
    let B (k : ℕ) : PowerSeries ℂ :=
      PowerSeries.C (backCoeff j k) * PowerSeries.X ^ (j + 1 - (k + 1)) * d_u^[k + 1] S
    have h_comb_A :
        ∑ k ∈ Finset.range (j + 1),
            PowerSeries.C (-((2 * j + 1 : ℕ) : ℂ) * backCoeff j k) *
              PowerSeries.X ^ (j + 1 - k) * d_u^[k] S -
          ∑ k ∈ Finset.range (j + 1),
            PowerSeries.C (-((j - k : ℕ) : ℂ) * backCoeff j k) *
              PowerSeries.X ^ (j + 1 - k) * d_u^[k] S =
          ∑ k ∈ Finset.range (j + 1), A k := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hcast : ((j - k : ℕ) : ℂ) = (j : ℂ) - (k : ℂ) := by
        rw [Nat.cast_sub hk_le]
      have hcoeff :
          (-((2 * j + 1 : ℕ) : ℂ) * backCoeff j k) - (-((j - k : ℕ) : ℂ) * backCoeff j k) =
            -((j + k + 1 : ℕ) : ℂ) * backCoeff j k := by
        rw [hcast]
        push_cast
        ring
      dsimp only [A]
      rw [← hcoeff, map_sub, sub_mul, sub_mul]
    have h_sub_all :
        (∑ k ∈ Finset.range (j + 1), A k) - (∑ k ∈ Finset.range (j + 1), B k) =
          ∑ k ∈ Finset.range (j + 2),
            PowerSeries.C (backCoeff (j + 1) k) * PowerSeries.X ^ (j + 1 - k) * d_u^[k] S := by
      have hA_ext : ∑ k ∈ Finset.range (j + 1), A k = ∑ k ∈ Finset.range (j + 2), A k := by
        rw [Finset.sum_range_succ (n := j + 1) A]
        have hA_end : A (j + 1) = 0 := by
          simp [A, backCoeff_gt (Nat.lt_succ_self j)]
        rw [hA_end, add_zero]
      have hB_ext :
          ∑ k ∈ Finset.range (j + 1), B k =
            ∑ k ∈ Finset.range (j + 2), (if k = 0 then (0 : PowerSeries ℂ) else B (k - 1)) := by
        rw [Finset.sum_range_succ' (n := j + 1) (fun k => if k = 0 then 0 else B (k - 1))]
        simp
      rw [hA_ext, hB_ext, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      cases k with
      | zero =>
        simp [A, backCoeff]
      | succ k =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one, A, B, backCoeff]
        have hcoeff :
            (-((j + (k + 1) + 1 : ℕ) : ℂ) * backCoeff j (k + 1)) - backCoeff j k =
              -((j + k + 2 : ℕ) : ℂ) * backCoeff j (k + 1) - backCoeff j k := by
          push_cast; ring
        rw [← hcoeff, map_sub, sub_mul, sub_mul]
    calc
      (∑ k ∈ Finset.range (j + 1),
          PowerSeries.C (-((2 * j + 1 : ℕ) : ℂ) * backCoeff j k) *
            PowerSeries.X ^ (j + 1 - k) * d_u^[k] S) -
        ((∑ k ∈ Finset.range (j + 1),
            PowerSeries.C (-((j - k : ℕ) : ℂ) * backCoeff j k) *
              PowerSeries.X ^ (j + 1 - k) * d_u^[k] S) +
          ∑ k ∈ Finset.range (j + 1), B k)
          = ((∑ k ∈ Finset.range (j + 1),
              PowerSeries.C (-((2 * j + 1 : ℕ) : ℂ) * backCoeff j k) *
                PowerSeries.X ^ (j + 1 - k) * d_u^[k] S) -
              (∑ k ∈ Finset.range (j + 1),
                PowerSeries.C (-((j - k : ℕ) : ℂ) * backCoeff j k) *
                  PowerSeries.X ^ (j + 1 - k) * d_u^[k] S)) -
            ∑ k ∈ Finset.range (j + 1), B k := by ring
      _ = (∑ k ∈ Finset.range (j + 1), A k) - ∑ k ∈ Finset.range (j + 1), B k := by
          rw [h_comb_A]
      _ = _ := h_sub_all

private lemma uLaurent_mul_coe_X :
    uLaurent * ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) = 1 := by
  rw [uLaurent, PowerSeries.coe_X, HahnSeries.single_mul_single, mul_one, neg_add_cancel]
  rfl

private lemma polyToLaurent_C (c : ℂ) :
    polyToLaurent (Polynomial.C c) = ((PowerSeries.C c : PowerSeries ℂ) : LaurentSeries ℂ) := by
  rw [polyToLaurent, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C]
  have h1 : algebraMap ℂ (LaurentSeries ℂ) c = HahnSeries.C c := HahnSeries.ofPowerSeries_C c
  have h2 : ((PowerSeries.C c : PowerSeries ℂ) : LaurentSeries ℂ) = HahnSeries.C c :=
    PowerSeries.coe_C c
  exact h1.trans h2.symm

private lemma polyToLaurent_X : polyToLaurent Polynomial.X = uLaurent := by
  simp [polyToLaurent]

private lemma polyToLaurent_X_pow (k : ℕ) :
    polyToLaurent (Polynomial.X ^ k) = uLaurent ^ k := by
  rw [map_pow, polyToLaurent_X]

private def backJetPoly (r j : ℕ) : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
  ∑ k ∈ Finset.range (j + 1),
    if hk : k < r + 1 then
      MvPolynomial.C (Polynomial.C (backCoeff j k) * Polynomial.X ^ (j + 1 + k)) *
        MvPolynomial.X ⟨k, hk⟩
    else 0

private lemma formalEvalPoly_backJetPoly (F : PowerSeries ℂ) {r j : ℕ} (hjr : j ≤ r) :
    formalEvalPoly (PowerSeries.X * F) (backJetPoly r j) =
      ((seriesJet F j : PowerSeries ℂ) : LaurentSeries ℂ) := by
  have hps := congrArg (fun S : PowerSeries ℂ => (S : LaurentSeries ℂ)) (X_pow_mul_seriesJet F j)
  have hmul := congrArg (fun L : LaurentSeries ℂ => uLaurent ^ (2 * j + 1) * L) hps
  rw [map_mul, map_pow, ← mul_assoc, ← mul_pow, uLaurent_mul_coe_X, one_pow, one_mul] at hmul
  rw [hmul, map_sum, Finset.mul_sum]
  unfold formalEvalPoly backJetPoly
  rw [MvPolynomial.eval₂_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hkr : k < r + 1 := Nat.lt_succ_of_le (hk_le.trans hjr)
  simp only [hkr, ↓reduceDIte, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
  rw [map_mul, polyToLaurent_C, polyToLaurent_X_pow]
  simp only [map_mul, map_pow]
  have hexp : 2 * j + 1 = (j + 1 + k) + (j - k) := by omega
  conv_rhs => rw [hexp, pow_add]
  calc
    ((PowerSeries.C (backCoeff j k) : PowerSeries ℂ) : LaurentSeries ℂ) * uLaurent ^ (j + 1 + k) *
        ((d_u^[k] (PowerSeries.X * F) : PowerSeries ℂ) : LaurentSeries ℂ)
        = ((PowerSeries.C (backCoeff j k) : PowerSeries ℂ) : LaurentSeries ℂ) *
            (uLaurent ^ (j + 1 + k) *
              (uLaurent * ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ)) ^ (j - k)) *
            ((d_u^[k] (PowerSeries.X * F) : PowerSeries ℂ) : LaurentSeries ℂ) := by
          rw [uLaurent_mul_coe_X, one_pow, mul_one]
    _ = _ := by
          rw [mul_pow]
          ring

private noncomputable def invBackStep (x : ℕ → ℂ) (u : ℂ) : ℕ → (ℕ → ℂ)
  | 0 => fun _ => u⁻¹ * x 1
  | j + 1 =>
    let prev := invBackStep x u j
    fun k =>
      if k = j + 1 then
        ((-1 : ℂ) ^ (j + 1) * u ^ (2 * (j + 1) + 1))⁻¹ *
          (x (j + 2) - ∑ m ∈ Finset.range (j + 1), backCoeff (j + 1) m * u ^ (j + 2 + m) * prev m)
      else prev k

private lemma invBackStep_stable (x : ℕ → ℂ) (u : ℂ) {m n : ℕ} (hmn : m ≤ n) :
    invBackStep x u n m = invBackStep x u m m := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := Nat.le_zero.mp hmn
    rfl
  | succ n ih =>
    rcases eq_or_lt_of_le hmn with rfl | hlt
    · rfl
    · have hne : m ≠ n + 1 := by omega
      dsimp only [invBackStep]
      simp only [hne, ↓reduceIte]
      exact ih (Nat.lt_succ_iff.mp hlt)

private noncomputable def invBack (x : ℕ → ℂ) (u : ℂ) (k : ℕ) : ℂ :=
  invBackStep x u k k

private lemma eval_evalU_backJetPoly (x : ℕ → ℂ) {u : ℂ} (hu : u ≠ 0) {r j : ℕ} (hjr : j ≤ r) :
    MvPolynomial.eval (fun i : Fin (r + 1) => invBack x u i.val) (evalU (backJetPoly r j) u) =
      x (j + 1) := by
  unfold evalU backJetPoly
  rw [map_sum, map_sum]
  have hsum :
      ∑ k ∈ Finset.range (j + 1),
          MvPolynomial.eval (fun i : Fin (r + 1) => invBack x u i.val)
            (MvPolynomial.map (Polynomial.evalRingHom u)
              (if hk : k < r + 1 then
                MvPolynomial.C (Polynomial.C (backCoeff j k) * Polynomial.X ^ (j + 1 + k)) *
                  MvPolynomial.X ⟨k, hk⟩
              else 0)) =
        ∑ k ∈ Finset.range (j + 1), backCoeff j k * u ^ (j + 1 + k) * invBack x u k := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_le : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hkr : k < r + 1 := Nat.lt_succ_of_le (hk_le.trans hjr)
    simp [hkr]
  rw [hsum]
  cases j with
  | zero =>
    rw [Nat.zero_add, Finset.sum_range_one]
    simp only [backCoeff, invBack, invBackStep]
    rw [add_zero, pow_one, one_mul, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
  | succ j =>
    rw [Finset.sum_range_succ, backCoeff_diag]
    have hprev :
        ∑ k ∈ Finset.range (j + 1), backCoeff (j + 1) k * u ^ (j + 1 + 1 + k) * invBack x u k =
          ∑ k ∈ Finset.range (j + 1),
            backCoeff (j + 1) k * u ^ (j + 2 + k) * invBackStep x u j k := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [invBack, invBackStep_stable x u hk_le, show j + 1 + 1 + k = j + 2 + k by omega]
    have hlast :
        invBack x u (j + 1) =
          ((-1 : ℂ) ^ (j + 1) * u ^ (2 * (j + 1) + 1))⁻¹ *
            (x (j + 2) - ∑ m ∈ Finset.range (j + 1),
              backCoeff (j + 1) m * u ^ (j + 2 + m) * invBackStep x u j m) := by
      simp [invBack, invBackStep]
    have hnz : (-1 : ℂ) ^ (j + 1) * u ^ (2 * (j + 1) + 1) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hu)
    rw [hprev, show j + 1 + 1 + (j + 1) = 2 * (j + 1) + 1 by omega, hlast,
      ← mul_assoc _ _ (x (j + 2) - ∑ m ∈ Finset.range (j + 1),
        backCoeff (j + 1) m * u ^ (j + 2 + m) * invBackStep x u j m),
      mul_inv_cancel₀ hnz, one_mul]
    ring

/-- **Purely Algebraic `EGF → OGF` Bridge**:
If `X * F` satisfies no nonzero non-autonomous polynomial ODE over `ℂ[u]` with respect to `d_u`,
then `(x, F, F', F'', ...)` is algebraically independent over `ℂ` in `ℂ[[x]]`. -/
theorem algebraicIndependent_ogf_of_no_ade {F : PowerSeries ℂ}
    (hno : ∀ {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)),
      formalEvalPoly (PowerSeries.X * F) P = 0 → P = 0) :
    AlgebraicIndependent ℂ (seriesCoordinates F) := by
  classical
  rw [algebraicIndependent_iff]
  intro Q hQ
  let r : ℕ := Q.support.sup fun m => m.support.sup id
  let M : ℕ := Q.support.sup fun m => m 0
  let Qpoly : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
    ∑ m ∈ Q.support,
      MvPolynomial.C (Polynomial.C (Q.coeff m) * Polynomial.X ^ (M - m 0)) *
        ∏ i ∈ m.support.erase 0, backJetPoly r (i - 1) ^ m i
  have hvars_le : ∀ m ∈ Q.support, ∀ i ∈ m.support, i ≤ r := fun m hm i hi =>
    le_trans (Finset.le_sup (f := id) hi)
      (Finset.le_sup (f := fun n : ℕ →₀ ℕ => n.support.sup id) hm)
  have hm0_le : ∀ m ∈ Q.support, m 0 ≤ M := fun m hm =>
    Finset.le_sup (f := fun n : ℕ →₀ ℕ => n 0) hm
  have hQpoly_zero : formalEvalPoly (PowerSeries.X * F) Qpoly = 0 := by
    have hL : ((MvPolynomial.aeval (seriesCoordinates F) Q : PowerSeries ℂ) : LaurentSeries ℂ) = 0 := by
      rw [hQ, PowerSeries.coe_zero]
    have hmul :
        uLaurent ^ M * ((MvPolynomial.aeval (seriesCoordinates F) Q : PowerSeries ℂ) : LaurentSeries ℂ) = 0 := by
      rw [hL, mul_zero]
    rw [← hmul]
    unfold Qpoly formalEvalPoly
    rw [MvPolynomial.eval₂_sum]
    conv_rhs =>
      rw [MvPolynomial.as_sum Q, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm_le : m 0 ≤ M := hm0_le m hm
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_prod,
      MvPolynomial.aeval_monomial, PowerSeries.algebraMap_apply]
    simp only [map_mul, polyToLaurent_C]
    have hprod_eq :
        ∏ i ∈ m.support.erase 0,
            (MvPolynomial.eval₂ polyToLaurent
              (fun j : Fin (r + 1) =>
                ((d_u^[j.val] (PowerSeries.X * F) : PowerSeries ℂ) : LaurentSeries ℂ)))
              (backJetPoly r (i - 1) ^ m i) =
          ∏ i ∈ m.support.erase 0, ((seriesCoordinates F i : PowerSeries ℂ) : LaurentSeries ℂ) ^ m i := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
      have hi_mem : i ∈ m.support := (Finset.mem_erase.mp hi).2
      have hi_le : i ≤ r := hvars_le m hm i hi_mem
      have hi_sub : i - 1 ≤ r := Nat.le_trans (Nat.sub_le i 1) hi_le
      have hcoord : seriesCoordinates F i = seriesJet F (i - 1) := by
        cases i with
        | zero => exact absurd rfl hi0
        | succ k => rfl
      rw [MvPolynomial.eval₂_pow, hcoord]
      change (formalEvalPoly (PowerSeries.X * F) (backJetPoly r (i - 1))) ^ m i = _
      rw [formalEvalPoly_backJetPoly F hi_sub]
    rw [hprod_eq]
    have hsplit_prod :
        ∏ i ∈ m.support, ((seriesCoordinates F i : PowerSeries ℂ) : LaurentSeries ℂ) ^ m i =
          ((seriesCoordinates F 0 : PowerSeries ℂ) : LaurentSeries ℂ) ^ m 0 *
            ∏ i ∈ m.support.erase 0, ((seriesCoordinates F i : PowerSeries ℂ) : LaurentSeries ℂ) ^ m i := by
      by_cases h0 : (0 : ℕ) ∈ m.support
      · rw [← Finset.mul_prod_erase m.support _ h0]
      · have hm00 : m 0 = 0 := Finsupp.notMem_support_iff.mp h0
        rw [hm00, pow_zero, one_mul, Finset.erase_eq_of_notMem h0]
    have h_uX :
        uLaurent ^ (M - m 0) = uLaurent ^ M * ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) ^ m 0 := by
      conv_lhs =>
        rw [← mul_one (uLaurent ^ (M - m 0)), ← one_pow (m 0), ← uLaurent_mul_coe_X, mul_pow,
          ← mul_assoc, ← pow_add, Nat.sub_add_cancel hm_le]
    have hmon_prod :
        (m.prod fun i e => seriesCoordinates F i ^ e) =
          ∏ i ∈ m.support, seriesCoordinates F i ^ m i := rfl
    rw [hmon_prod, map_prod, polyToLaurent_X_pow, Algebra.algebraMap_self, RingHom.id_apply]
    simp only [map_pow]
    rw [hsplit_prod, show seriesCoordinates F 0 = PowerSeries.X from rfl, h_uX]
    ring
  have hQpoly0 : Qpoly = 0 := hno Qpoly hQpoly_zero
  refine MvPolynomial.funext_set
    (fun i => if i = 0 then {c : ℂ | c ≠ 0} else Set.univ)
    (fun i => ?_)
    fun x hx => ?_
  · split_ifs
    · have : ({c : ℂ | c ≠ 0} : Set ℂ) = Set.univ \ {0} := by
        ext c; simp [Set.mem_sdiff, Set.mem_singleton_iff]
      rw [this]
      exact Set.infinite_univ.sdiff (Set.finite_singleton 0)
    · exact Set.infinite_univ
  · have hx0 : x 0 ≠ 0 := by simpa using hx 0 (Set.mem_univ 0)
    let u : ℂ := (x 0)⁻¹
    have hu : u ≠ 0 := inv_ne_zero hx0
    have hu_inv : u⁻¹ = x 0 := inv_inv (x 0)
    have hev0 : MvPolynomial.eval (fun i : Fin (r + 1) => invBack x u i.val) (evalU Qpoly u) = 0 := by
      rw [hQpoly0, evalU, map_zero, map_zero]
    have h_eq :
        MvPolynomial.eval (fun i : Fin (r + 1) => invBack x u i.val) (evalU Qpoly u) =
          u ^ M * MvPolynomial.eval x Q := by
      unfold Qpoly evalU
      simp only [map_sum, map_mul, map_pow, MvPolynomial.map_C, MvPolynomial.eval_C,
        Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_X, map_prod]
      conv_rhs => rw [MvPolynomial.as_sum Q, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm_le : m 0 ≤ M := hm0_le m hm
      have hprod_x :
          ∏ i ∈ m.support.erase 0,
              (MvPolynomial.eval (fun k : Fin (r + 1) => invBack x u k.val))
                (MvPolynomial.map (Polynomial.evalRingHom u) (backJetPoly r (i - 1))) ^ m i =
            ∏ i ∈ m.support.erase 0, x i ^ m i := by
        refine Finset.prod_congr rfl fun i hi => ?_
        have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
        have hi_mem : i ∈ m.support := (Finset.mem_erase.mp hi).2
        have hi_le : i ≤ r := hvars_le m hm i hi_mem
        have hi_sub : i - 1 ≤ r := Nat.le_trans (Nat.sub_le i 1) hi_le
        change (MvPolynomial.eval (fun k : Fin (r + 1) => invBack x u k.val)
            (evalU (backJetPoly r (i - 1)) u)) ^ m i = x i ^ m i
        rw [eval_evalU_backJetPoly x hu hi_sub, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi0)]
      have hsplit_x :
          MvPolynomial.eval x (monomial m (Q.coeff m)) =
            Q.coeff m * x 0 ^ m 0 * ∏ i ∈ m.support.erase 0, x i ^ m i := by
        rw [MvPolynomial.eval_monomial, Finsupp.prod]
        by_cases h0 : (0 : ℕ) ∈ m.support
        · rw [← Finset.mul_prod_erase m.support _ h0, mul_assoc]
        · have hm00 : m 0 = 0 := Finsupp.notMem_support_iff.mp h0
          rw [hm00, pow_zero, mul_one, Finset.erase_eq_of_notMem h0]
      have hu_pow : u ^ (M - m 0) = u ^ M * x 0 ^ m 0 := by
        conv_lhs =>
          rw [← mul_one (u ^ (M - m 0)), ← one_pow (m 0), ← mul_inv_cancel₀ hu, mul_pow,
            ← mul_assoc, ← pow_add, Nat.sub_add_cancel hm_le, hu_inv]
      rw [hprod_x, hsplit_x, hu_pow]
      ring
    rw [h_eq] at hev0
    exact ((mul_eq_zero.mp hev0).resolve_left (pow_ne_zero M hu)).trans (map_zero _).symm

/-- **Main Pak–Yeliussizov `EGF → OGF` Bridge Theorem (`ogf_algebraicIndependent_of_higherOrderBorel`)**:
For ANY analytic EGF `E : ℂ → ℂ` satisfying `HigherOrderBorelData E θ₀ ω ord pp`,
its Ordinary Generating Function `ogfOfEGF E = ∑_{n ≥ 0} E^{(n)}(0) x^n` is
**differentially transcendental over `ℂ(x)`** (`AlgebraicIndependent ℂ (seriesCoordinates (ogfOfEGF E))`). -/
theorem ogf_algebraicIndependent_of_higherOrderBorel
    {E : ℂ → ℂ} {θ₀ : ℝ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ}
    (h : HigherOrderBorelData E θ₀ ω ord pp) :
    AlgebraicIndependent ℂ (seriesCoordinates (ogfOfEGF E)) :=
  algebraicIndependent_ogf_of_no_ade fun P hP => by
    rw [← formalSeries_eq_X_mul_ogfOfEGF] at hP
    exact higher_order_stokes_vandermonde_no_ade h P hP

/-- Explicit non-autonomous polynomial-coefficient ODE non-existence over `ℂ[x]` for `ogfOfEGF E`. -/
theorem ogf_no_poly_ade_of_higherOrderBorel
    {E : ℂ → ℂ} {θ₀ : ℝ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ}
    (h : HigherOrderBorelData E θ₀ ω ord pp)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : MvPolynomial.eval₂ (Polynomial.aeval PowerSeries.X).toRingHom
      (fun j : Fin (r + 1) => seriesJet (ogfOfEGF E) j.val) P = 0) :
    P = 0 := by
  classical
  have hind := ogf_algebraicIndependent_of_higherOrderBorel h
  rw [algebraicIndependent_iff] at hind
  ext n k
  by_contra hne
  let P' : MvPolynomial ℕ ℂ :=
    ∑ m ∈ P.support,
      Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial ℕ ℂ) (P.coeff m) *
        ∏ j : Fin (r + 1), MvPolynomial.X (j.val + 1) ^ m j
  have hP'_eval : MvPolynomial.aeval (seriesCoordinates (ogfOfEGF E)) P' = 0 := by
    simp only [P', map_sum, map_mul, map_prod, map_pow, aeval_X]
    have haev : ∀ p : Polynomial ℂ,
        MvPolynomial.aeval (seriesCoordinates (ogfOfEGF E))
          (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial ℕ ℂ) p) =
        (Polynomial.aeval PowerSeries.X) p := by
      intro p
      induction p using Polynomial.induction_on with
      | C c => simp [PowerSeries.algebraMap_eq]
      | add a b ha hb => simp [map_add, ha, hb]
      | monomial d a _ => simp [map_mul, map_pow, PowerSeries.algebraMap_eq, seriesCoordinates]
    simp_rw [haev]
    conv_rhs => rw [← hP, MvPolynomial.as_sum P, MvPolynomial.eval₂_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.eval₂_monomial, Finsupp.prod_of_support_subset _
      (Finset.subset_univ _) _ (fun _ _ => pow_zero _)]
    rfl
  have hP'0 : P' = 0 := hind P' hP'_eval
  have h_eq : ∀ x : ℕ → ℂ, MvPolynomial.eval x P' = 0 := fun x => by rw [hP'0, map_zero]
  have hP_eval0 : ∀ (x₀ : ℂ) (y : Fin (r + 1) → ℂ),
      MvPolynomial.eval y (evalU P x₀) = 0 := fun x₀ y => by
    let x : ℕ → ℂ := fun i => match i with
      | 0 => x₀
      | m + 1 => if hm : m < r + 1 then y ⟨m, hm⟩ else 0
    have hx := h_eq x
    dsimp only [P'] at hx
    simp only [map_sum, map_mul, map_prod, map_pow, eval_X] at hx
    have hev_p : ∀ p : Polynomial ℂ,
        MvPolynomial.eval x (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial ℕ ℂ) p) =
          p.eval x₀ := by
      intro p
      induction p using Polynomial.induction_on with
      | C c => simp
      | add a b ha hb => simp [map_add, ha, hb]
      | monomial d a _ => simp [x]
    have hxj : ∀ j : Fin (r + 1), x (j.val + 1) = y j := fun j => by
      change (if hm : j.val < r + 1 then y ⟨j.val, hm⟩ else 0) = y j
      split_ifs with hlt
      · rfl
      · exact absurd j.isLt hlt
    simp_rw [hev_p, hxj] at hx
    unfold evalU
    conv_lhs => rw [MvPolynomial.as_sum P, map_sum, map_sum]
    rw [← hx]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.map_monomial, MvPolynomial.eval_monomial, Finsupp.prod_of_support_subset _
      (Finset.subset_univ _) _ (fun _ _ => pow_zero _)]
    rfl
  have hU0 : ∀ x₀ : ℂ, evalU P x₀ = 0 := fun x₀ =>
    MvPolynomial.funext fun y => hP_eval0 x₀ y
  have hcoeff0 : ∀ x₀ : ℂ, (P.coeff n).eval x₀ = 0 := fun x₀ => by
    have hc := congrArg (fun R : MvPolynomial (Fin (r + 1)) ℂ => R.coeff n) (hU0 x₀)
    simpa [evalU, MvPolynomial.coeff_map] using hc
  have hp0 : P.coeff n = 0 :=
    Polynomial.funext fun x₀ => (hcoeff0 x₀).trans Polynomial.eval_zero.symm
  exact hne (by simp [hp0])

/-! ### 2. Polynomial-Shift Transfer (`F ↦ F + p(x)`) -/

private lemma derivative_aeval_poly (p : Polynomial ℂ) :
    PowerSeries.derivative (Polynomial.aeval PowerSeries.X p : PowerSeries ℂ) =
      Polynomial.aeval PowerSeries.X (Polynomial.derivative p) := by
  induction p using Polynomial.induction_on with
  | C c =>
    simp [PowerSeries.algebraMap_eq]
  | add a b ha hb =>
    simp [map_add, ha, hb]
  | monomial k a _ =>
    cases k with
    | zero => simp [PowerSeries.algebraMap_eq]
    | succ m =>
      simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
        PowerSeries.algebraMap_eq, Polynomial.derivative_C_mul_X_pow, Nat.succ_sub_one,
        Derivation.leibniz, PowerSeries.derivative_C, PowerSeries.derivative_pow,
        PowerSeries.derivative_X, mul_one, smul_eq_mul]
      rw [← map_natCast PowerSeries.C (m + 1 + 1)]
      ring

private lemma seriesJet_aeval_poly (p : Polynomial ℂ) (j : ℕ) :
    seriesJet (Polynomial.aeval PowerSeries.X p : PowerSeries ℂ) j =
      Polynomial.aeval PowerSeries.X (Polynomial.derivative^[j] p) := by
  induction j with
  | zero => simp [seriesJet]
  | succ j ih =>
    rw [seriesJet, Function.iterate_succ_apply', ← seriesJet, ih, derivative_aeval_poly,
      ← Function.iterate_succ_apply' Polynomial.derivative j p]

private def shiftPolyVar (p : Polynomial ℂ) : ℕ → MvPolynomial ℕ ℂ
  | 0 => MvPolynomial.X 0
  | j + 1 => MvPolynomial.X (j + 1) +
      Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial ℕ ℂ) (Polynomial.derivative^[j] p)

private lemma aeval_shiftPolyVar (G : PowerSeries ℂ) (p : Polynomial ℂ) (i : ℕ) :
    MvPolynomial.aeval (seriesCoordinates G) (shiftPolyVar p i) =
      seriesCoordinates (G + Polynomial.aeval PowerSeries.X p) i := by
  cases i with
  | zero =>
    simp [shiftPolyVar, seriesCoordinates]
  | succ j =>
    have hjet : seriesJet (G + Polynomial.aeval PowerSeries.X p) j =
        seriesJet G j + seriesJet (Polynomial.aeval PowerSeries.X p) j := by
      induction j with
      | zero => simp [seriesJet]
      | succ j ih =>
        simp only [seriesJet, Function.iterate_succ_apply'] at ih ⊢
        rw [ih, map_add]
    have hpoly : MvPolynomial.aeval (seriesCoordinates G)
        (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial ℕ ℂ) (Polynomial.derivative^[j] p)) =
        Polynomial.aeval PowerSeries.X (Polynomial.derivative^[j] p) := by
      induction (Polynomial.derivative^[j] p) using Polynomial.induction_on with
      | C c => simp [PowerSeries.algebraMap_eq]
      | add a b ha hb => simp [map_add, ha, hb]
      | monomial k a _ => simp [map_mul, map_pow, PowerSeries.algebraMap_eq, seriesCoordinates]
    simp only [shiftPolyVar, map_add, aeval_X, seriesCoordinates, hjet, seriesJet_aeval_poly, hpoly]

private lemma bind₁_shiftPolyVar_cancel (p : Polynomial ℂ) (Q : MvPolynomial ℕ ℂ) :
    MvPolynomial.bind₁ (shiftPolyVar (-p)) (MvPolynomial.bind₁ (shiftPolyVar p) Q) = Q := by
  have hcomp :
      (MvPolynomial.bind₁ (shiftPolyVar (-p))).comp (MvPolynomial.bind₁ (shiftPolyVar p)) =
        AlgHom.id ℂ (MvPolynomial ℕ ℂ) := by
    refine MvPolynomial.algHom_ext fun i => ?_
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.id_apply, MvPolynomial.bind₁_X_right]
    cases i with
    | zero => simp [shiftPolyVar]
    | succ j =>
      have hneg : Polynomial.derivative^[j] (-p) = -(Polynomial.derivative^[j] p) := by
        induction j with
        | zero => rfl
        | succ j ih =>
          rw [Function.iterate_succ_apply', ih, map_neg,
            ← Function.iterate_succ_apply' Polynomial.derivative j p]
      have hid : ∀ q : Polynomial ℂ,
          MvPolynomial.bind₁ (shiftPolyVar (-p))
            (Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial ℕ ℂ) q) =
          Polynomial.aeval (MvPolynomial.X 0 : MvPolynomial ℕ ℂ) q := by
        intro q
        induction q using Polynomial.induction_on with
        | C c => simp
        | add a b ha hb => simp [map_add, ha, hb]
        | monomial k a _ => simp [map_mul, map_pow, shiftPolyVar]
      simp only [shiftPolyVar, map_add, bind₁_X_right, hneg, map_neg, hid]
      ring
  exact AlgHom.congr_fun hcomp Q

/-- Adding any polynomial `p(x)` to a power series `G` preserves differential algebraic independence
over `ℂ`. -/
theorem algIndep_seriesCoordinates_add_poly (G : PowerSeries ℂ) (p : Polynomial ℂ) :
    AlgebraicIndependent ℂ (seriesCoordinates (G + Polynomial.aeval PowerSeries.X p)) ↔
      AlgebraicIndependent ℂ (seriesCoordinates G) := by
  have fwd : ∀ (H : PowerSeries ℂ) (q : Polynomial ℂ),
      AlgebraicIndependent ℂ (seriesCoordinates H) →
      AlgebraicIndependent ℂ (seriesCoordinates (H + Polynomial.aeval PowerSeries.X q)) := by
    intro H q hH
    rw [algebraicIndependent_iff] at hH ⊢
    intro Q hQ
    have hQ' : MvPolynomial.aeval (seriesCoordinates H) (MvPolynomial.bind₁ (shiftPolyVar q) Q) = 0 := by
      rw [MvPolynomial.aeval_bind₁]
      have hfn : (fun i => MvPolynomial.aeval (seriesCoordinates H) (shiftPolyVar q i)) =
          seriesCoordinates (H + Polynomial.aeval PowerSeries.X q) :=
        funext (aeval_shiftPolyVar H q)
      rw [hfn, hQ]
    have hbind0 := hH _ hQ'
    have := congrArg (MvPolynomial.bind₁ (shiftPolyVar (-q))) hbind0
    simpa [bind₁_shiftPolyVar_cancel] using this
  constructor
  · intro hGp
    have hG := fwd (G + Polynomial.aeval PowerSeries.X p) (-p) hGp
    simpa [map_neg, add_neg_cancel_right] using hG
  · exact fwd G p

/-! ### 3. Arbitrary-Order Meromorphic Pole & Exponential-Type Helpers -/

private lemma laurent_jet_expansion {H : ℂ → ℂ} {z₀ : ℂ} (hH : AnalyticAt ℂ H z₀) :
    ∀ p : ℕ, ∃ (a : ℕ → ℂ) (L : ℂ), a 0 = H z₀ ∧
      Filter.Tendsto
        (fun z : ℂ => H z / (z - z₀) ^ p - ∑ s ∈ Finset.Icc 1 p, a (p - s) / (z - z₀) ^ s)
        (𝓝[≠] z₀) (𝓝 L) := by
  intro p
  induction p generalizing H with
  | zero =>
    refine ⟨fun _ => H z₀, H z₀, rfl, ?_⟩
    simpa using hH.continuousAt.continuousWithinAt.tendsto
  | succ p ih =>
    let H₁ : ℂ → ℂ := dslope H z₀
    have hH₁ : AnalyticAt ℂ H₁ z₀ := hH.hasFPowerSeriesAt.dslope_fslope.analyticAt
    obtain ⟨a₁, L₁, _, hL₁⟩ := ih hH₁
    let a : ℕ → ℂ := fun k => match k with | 0 => H z₀ | k + 1 => a₁ k
    refine ⟨a, L₁, rfl, ?_⟩
    refine hL₁.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
    have hz_ne : z - z₀ ≠ 0 := sub_ne_zero.mpr hz
    have hdslope : H z = H z₀ + (z - z₀) * H₁ z := by
      dsimp only [H₁]
      rw [dslope_of_ne _ hz, slope_def_field, mul_div_cancel₀ _ hz_ne]
      ring
    have hsplit_sum :
        ∑ s ∈ Finset.Icc 1 (p + 1), a (p + 1 - s) / (z - z₀) ^ s =
          H z₀ / (z - z₀) ^ (p + 1) +
            ∑ s ∈ Finset.Icc 1 p, a₁ (p - s) / (z - z₀) ^ s := by
      have hIcc : Finset.Icc 1 (p + 1) = insert (p + 1) (Finset.Icc 1 p) := by
        ext s; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : p + 1 ∉ Finset.Icc 1 p := by simp
      rw [hIcc, Finset.sum_insert hnot, Nat.sub_self]
      congr 1
      refine Finset.sum_congr rfl fun s hs => ?_
      have hsp : s ≤ p := (Finset.mem_Icc.mp hs).2
      rw [show p + 1 - s = (p - s) + 1 by omega]
    dsimp only
    rw [hdslope, hsplit_sum, pow_succ']
    field_simp [hz_ne]
    ring

private lemma pole_principalPart_of_simpleZero_div_pow
    {g f : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀) (hf : AnalyticAt ℂ f z₀)
    (hf0 : f z₀ = 0) (hf' : deriv f z₀ ≠ 0) (p : ℕ) (_hp : 1 ≤ p) :
    ∃ (c : ℕ → ℂ) (L : ℂ), c p = g z₀ / (deriv f z₀) ^ p ∧
      Filter.Tendsto
        (fun z : ℂ => g z / (f z) ^ p - ∑ s ∈ Finset.Icc 1 p, c s / (z - z₀) ^ s)
        (𝓝[≠] z₀) (𝓝 L) := by
  let h : ℂ → ℂ := dslope f z₀
  have hh : AnalyticAt ℂ h z₀ := hf.hasFPowerSeriesAt.dslope_fslope.analyticAt
  have hh0 : h z₀ = deriv f z₀ := by simp [h, dslope_same]
  have hh_ne : h z₀ ≠ 0 := hh0 ▸ hf'
  let H : ℂ → ℂ := fun z => g z / (h z) ^ p
  have hH : AnalyticAt ℂ H z₀ := hg.div (hh.pow p) (pow_ne_zero p hh_ne)
  obtain ⟨a, L, ha0, hL⟩ := laurent_jet_expansion hH p
  let c : ℕ → ℂ := fun s => if s = p then g z₀ / (deriv f z₀) ^ p else a (p - s)
  refine ⟨c, L, by simp [c], ?_⟩
  refine hL.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
  have hf_eq : f z = (z - z₀) * h z := by
    dsimp only [h]
    rw [dslope_of_ne _ hz, slope_def_field, hf0, sub_zero, mul_div_cancel₀ _ (sub_ne_zero.mpr hz)]
  have hdiv : H z / (z - z₀) ^ p = g z / (f z) ^ p := by
    dsimp only [H]
    rw [hf_eq, mul_pow, div_div, mul_comm ((h z) ^ p)]
  have hsum :
      ∑ s ∈ Finset.Icc 1 p, a (p - s) / (z - z₀) ^ s =
        ∑ s ∈ Finset.Icc 1 p, c s / (z - z₀) ^ s := by
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hsp : s = p
    · subst hsp
      simp [c, ha0, H, hh0]
    · simp [c, hsp]
  rw [hdiv, hsum]

private lemma expType_of_continuousOn_of_bdd {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Icc 0 1))
    {C₁ : ℝ} (hbd : ∀ v : ℝ, 1 ≤ v → ‖f v‖ ≤ C₁) :
    ExpType f := by
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  let C : ℝ := max (max M₀ 0) (max C₁ 0)
  have hC : 0 ≤ C := le_trans (le_max_right M₀ 0) (le_max_left _ _)
  refine ⟨C, 0, hC, le_rfl, fun v hv => ?_⟩
  rw [zero_mul, Real.exp_zero, mul_one]
  by_cases hv1 : v ≤ 1
  · exact (hM₀ v ⟨hv, hv1⟩).trans ((le_max_left M₀ 0).trans (le_max_left _ _))
  · push Not at hv1
    exact (hbd v hv1.le).trans ((le_max_left C₁ 0).trans (le_max_right _ _))

private lemma expType_pull_pow {μ : ℂ} (hμ : ‖μ‖ = 1) {f : ℂ → ℂ}
    (hf : ExpType (Minor.pull μ f)) (p : ℕ) :
    ExpType (Minor.pull μ fun ξ => f ξ ^ p) := by
  obtain ⟨C, D, hC, hD, hbd⟩ := hf
  refine ⟨C ^ p, (p : ℝ) * D, pow_nonneg hC p, mul_nonneg (Nat.cast_nonneg p) hD, fun v hv => ?_⟩
  have h1 := hbd v hv
  rw [Minor.pull, norm_mul, hμ, one_mul] at h1 ⊢
  calc ‖f (μ * (v : ℂ)) ^ p‖ = ‖f (μ * (v : ℂ))‖ ^ p := norm_pow _ p
    _ ≤ (C * Real.exp (D * v)) ^ p := pow_le_pow_left₀ (norm_nonneg _) h1 p
    _ = C ^ p * Real.exp ((p : ℝ) * D * v) := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring

private lemma norm_exp_I_mul_real (σ : ℝ) : ‖Complex.exp (I * (σ : ℂ))‖ = 1 := by
  rw [show I * (σ : ℂ) = (σ : ℂ) * I by ring]
  exact Complex.norm_exp_ofReal_mul_I σ

/-! ### 4. Showcase Corollary 1: Bernoulli Numbers OGF (`∑ B_n x^n`) -/

/-- The Bernoulli EGF `E_Bern(ξ) = ξ / (e^ξ - 1)` with removable singularity `E_Bern(0) = 1`. -/
@[expose] def bernEGF (ξ : ℂ) : ℂ :=
  (dslope Complex.exp 0 ξ)⁻¹

lemma bernEGF_zero : bernEGF 0 = 1 := by
  simp [bernEGF, dslope_same, Complex.deriv_exp]

lemma bernEGF_eq_of_ne_zero {ξ : ℂ} (hξ : ξ ≠ 0) :
    bernEGF ξ = ξ / (Complex.exp ξ - 1) := by
  rw [bernEGF, dslope_of_ne _ hξ, slope_def_field, Complex.exp_zero, sub_zero, inv_div]

lemma bernEGF_eq_phiBern_add (ξ : ℂ) :
    bernEGF ξ = phiBern ξ + (1 - ξ / 2) := by
  simp only [bernEGF, phiBern]
  ring

lemma iteratedDeriv_bernEGF_zero (n : ℕ) :
    iteratedDeriv n bernEGF 0 = (bernoulli n : ℂ) := by
  have hphi : AnalyticAt ℂ phiBern 0 := phiBern_analyticAt (Or.inl rfl)
  have hlin : AnalyticAt ℂ (fun ξ : ℂ => 1 - ξ / 2) 0 :=
    analyticAt_const.sub (analyticAt_id.mul analyticAt_const)
  have hfn : bernEGF = phiBern + fun ξ : ℂ => 1 - ξ / 2 := funext bernEGF_eq_phiBern_add
  rw [hfn, iteratedDeriv_add (hphi.contDiffAt.of_le le_top) (hlin.contDiffAt.of_le le_top),
    iteratedDeriv_phiBern_zero]
  rcases n with _ | _ | n
  · simp [bernoulli_zero]
  · simp only [Nat.le_refl, ↓reduceIte, zero_add, iteratedDeriv_one, bernoulli_one]
    have hder : deriv (fun ξ : ℂ => (1 : ℂ) - ξ / 2) 0 = -(2⁻¹ : ℂ) := by simp
    rw [hder]
    norm_num
  · have hdlin : deriv (fun ξ : ℂ => (1 : ℂ) - ξ / 2) = fun _ => -(2⁻¹ : ℂ) := by
      ext ξ; simp
    have h0 : iteratedDeriv (n + 2) (fun ξ : ℂ => (1 : ℂ) - ξ / 2) 0 = 0 := by
      rw [iteratedDeriv_succ', hdlin, iteratedDeriv_succ', deriv_const', iteratedDeriv_const]
      simp
    rw [h0, add_zero, ite_eq_right_iff.mpr (by omega)]

/-- The formal ordinary generating function `∑_{n ≥ 0} B_n x^n` of the Bernoulli numbers. -/
@[expose] def bernOGF : PowerSeries ℂ :=
  ogfOfSeq fun n => (bernoulli n : ℂ)

lemma ogfOfEGF_bernEGF : ogfOfEGF bernEGF = bernOGF := by
  ext n
  simp [ogfOfEGF, bernOGF, ogfOfSeq, iteratedDeriv_bernEGF_zero]

/-- **Showcase Corollary 1 (Bernoulli Numbers OGF)**:
`∑_{n ≥ 0} B_n x^n` is unconditionally differentially transcendental over `ℂ(x)` in `ℂ[[x]]`. -/
theorem bernOGF_algebraicIndependent :
    AlgebraicIndependent ℂ (seriesCoordinates bernOGF) := by
  have hphi_ind : AlgebraicIndependent ℂ (seriesCoordinates (ogfOfEGF phiBern)) :=
    ogf_algebraicIndependent_of_higherOrderBorel phiBern_borelData
  let p : Polynomial ℂ := Polynomial.C 1 - Polynomial.C (1 / 2 : ℂ) * Polynomial.X
  have hshift :
      bernOGF = ogfOfEGF phiBern + Polynomial.aeval PowerSeries.X p := by
    ext n
    cases n with
    | zero =>
      simp [bernOGF, ogfOfSeq, ogfOfEGF, phiBern_zero, p, bernoulli_zero, PowerSeries.algebraMap_eq]
    | succ n =>
      cases n with
      | zero =>
        have hdphi : iteratedDeriv 1 phiBern 0 = 0 := by
          rw [iteratedDeriv_phiBern_zero]; simp
        simp only [bernOGF, ogfOfSeq, ogfOfEGF, PowerSeries.coeff_mk, map_add, hdphi, zero_add,
          p, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, PowerSeries.algebraMap_eq,
          bernoulli_one]
        have hC : (PowerSeries.C (1 : ℂ)).coeff 1 = 0 := by simp
        have hCX : (PowerSeries.C (1 / 2 : ℂ) * PowerSeries.X).coeff 1 = 1 / 2 := by
          rw [mul_comm, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_C]
        rw [hC, hCX, zero_sub]
        norm_num
      | succ k =>
        have hlin : (Polynomial.aeval PowerSeries.X p : PowerSeries ℂ).coeff (k + 2) = 0 := by
          simp only [p, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
            PowerSeries.algebraMap_eq]
          have hC : (PowerSeries.C (1 : ℂ)).coeff (k + 2) = 0 := by simp
          have hCX : (PowerSeries.C (1 / 2 : ℂ) * PowerSeries.X).coeff (k + 2) = 0 := by
            rw [mul_comm, PowerSeries.coeff_succ_X_mul]
            simp
          rw [hC, hCX, sub_zero]
        rw [map_add, hlin, add_zero]
        simp only [bernOGF, ogfOfSeq, ogfOfEGF, PowerSeries.coeff_mk, iteratedDeriv_phiBern_zero]
        rw [ite_eq_right_iff.mpr (by omega)]
  rw [hshift]
  exact (algIndep_seriesCoordinates_add_poly (ogfOfEGF phiBern) p).mpr hphi_ind

/-! ### 5. Trigonometric & Arbitrary-Order Secant Witnesses (`tan`, `sec`, `sec^2`, `sec^p`) -/

/-- Real-axis pole sequence `(m + 1/2) π` of `tan ξ` and `sec ξ`. -/
@[expose] def trigPole (m : ℕ) : ℝ := ((m : ℝ) + 1 / 2) * Real.pi

private lemma trigPole_pos : 0 < trigPole 0 := by
  unfold trigPole
  positivity

private lemma trigPole_mono : StrictMono trigPole := by
  intro a b hab
  unfold trigPole
  have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  nlinarith [Real.pi_pos]

private lemma cos_nat_mul_pi (m : ℕ) : Complex.cos ((m : ℂ) * Real.pi) = (-1 : ℂ) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Complex.cos_add, ih,
      Complex.cos_pi, Complex.sin_pi, pow_succ]
    ring

private lemma sin_nat_mul_pi (m : ℕ) : Complex.sin ((m : ℂ) * Real.pi) = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Complex.sin_add, ih,
      Complex.cos_pi, Complex.sin_pi]
    ring

private lemma cos_trigPole (m : ℕ) : Complex.cos (trigPole m : ℂ) = 0 := by
  have heq : (trigPole m : ℂ) = (m : ℂ) * Real.pi + Real.pi / 2 := by
    unfold trigPole; push_cast; ring
  rw [heq, Complex.cos_add, cos_nat_mul_pi, sin_nat_mul_pi, Complex.cos_pi_div_two]
  ring

private lemma sin_trigPole (m : ℕ) : Complex.sin (trigPole m : ℂ) = (-1 : ℂ) ^ m := by
  have heq : (trigPole m : ℂ) = (m : ℂ) * Real.pi + Real.pi / 2 := by
    unfold trigPole; push_cast; ring
  rw [heq, Complex.sin_add, cos_nat_mul_pi, sin_nat_mul_pi, Complex.sin_pi_div_two]
  ring

private lemma cos_ne_zero_on_puncturedWedge {z : ℂ}
    (hz : z ∈ puncturedWedge (Real.pi / 3) 1 trigPole) :
    Complex.cos z ≠ 0 := by
  intro hcos
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  have hre : z.re = ((k : ℝ) + 1 / 2) * Real.pi := by
    rw [hk]
    have hk' : (2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2 = (((k : ℝ) + 1 / 2) * Real.pi : ℝ) := by
      push_cast; ring
    rw [hk', Complex.ofReal_re]
  rcases lt_or_ge k 0 with hk_neg | hk_nonneg
  · have hk_le : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk_neg
    have hz_re_neg : z.re ≤ -(Real.pi / 2) := by
      rw [hre]; nlinarith [Real.pi_pos]
    rcases hz.1 with hball | hsec
    · rw [Metric.mem_ball, dist_zero_right] at hball
      have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
      have h2 : Real.pi / 2 ≤ |z.re| := by
        rw [abs_of_nonpos (by linarith [Real.pi_pos])]
        linarith
      linarith [Real.pi_gt_three]
    · linarith [hsec.1, Real.pi_pos]
  · apply hz.2
    refine ⟨k.toNat, ?_⟩
    rw [hk]
    have hk_eq : (k.toNat : ℂ) = (k : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hk_nonneg
    unfold trigPole
    push_cast
    rw [hk_eq]
    ring

private lemma cos_norm_ge_on_ray {σ : ℝ} (_hsin : Real.sin σ ≠ 0) {v : ℝ}
    (hv : 1 / 2 ≤ |v * Real.sin σ|) :
    (Real.exp (1 / 2) - Real.exp (-(1 / 2))) / 2 ≤
      ‖Complex.cos (Complex.exp (I * (σ : ℂ)) * (v : ℂ))‖ := by
  let w : ℂ := Complex.exp (I * (σ : ℂ)) * (v : ℂ)
  have hw_im : w.im = v * Real.sin σ := by
    have hexp : Complex.exp (I * (σ : ℂ)) = Complex.exp ((σ : ℂ) * I) := by congr 1; ring
    dsimp only [w]
    rw [Complex.mul_im, hexp, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hcos_def : Complex.cos w = (Complex.exp (I * w) + Complex.exp (-I * w)) / 2 := by
    rw [Complex.cos, mul_comm w I]
    congr 1; ring_nf
  have h1 : ‖Complex.exp (I * w)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp, show (I * w).re = -w.im by simp]
  have h2 : ‖Complex.exp (-I * w)‖ = Real.exp w.im := by
    rw [Complex.norm_exp, show (-I * w).re = w.im by simp]
  have hrev1 : Real.exp w.im - Real.exp (-w.im) ≤ ‖Complex.exp (I * w) + Complex.exp (-I * w)‖ := by
    have htri := norm_sub_norm_le (Complex.exp (-I * w)) (-(Complex.exp (I * w)))
    rw [sub_neg_eq_add, norm_neg, h1, h2, add_comm] at htri
    exact htri
  have hrev2 : Real.exp (-w.im) - Real.exp w.im ≤ ‖Complex.exp (I * w) + Complex.exp (-I * w)‖ := by
    have htri := norm_sub_norm_le (Complex.exp (I * w)) (-(Complex.exp (-I * w)))
    rw [sub_neg_eq_add, norm_neg, h1, h2] at htri
    exact htri
  have habs_exp : Real.exp |w.im| - Real.exp (-|w.im|) ≤ ‖Complex.exp (I * w) + Complex.exp (-I * w)‖ := by
    rcases le_or_gt 0 w.im with hw_pos | hw_neg
    · rw [abs_of_nonneg hw_pos]; exact hrev1
    · rw [abs_of_neg hw_neg, neg_neg]; exact hrev2
  have hmono : Real.exp (1 / 2) - Real.exp (-(1 / 2)) ≤ Real.exp |w.im| - Real.exp (-|w.im|) := by
    have h_abs : 1 / 2 ≤ |w.im| := by simpa [hw_im] using hv
    have ha : Real.exp (1 / 2) ≤ Real.exp |w.im| := Real.exp_le_exp.mpr h_abs
    have hb : Real.exp (-|w.im|) ≤ Real.exp (-(1 / 2)) := Real.exp_le_exp.mpr (by linarith)
    linarith
  rw [hcos_def, norm_div, Complex.norm_ofNat]
  exact div_le_div_of_nonneg_right (hmono.trans habs_exp) (by norm_num)

private lemma cos_ne_zero_on_pi_div_four_ray {σ : ℝ} (hsin : Real.sin σ ≠ 0) (v : ℝ) :
    Complex.cos (Complex.exp (I * (σ : ℂ)) * (v : ℂ)) ≠ 0 := by
  intro h0
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp h0
  have him : (Complex.exp (I * (σ : ℂ)) * (v : ℂ)).im = 0 := by
    rw [hk]
    have hk' : (2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2 = (((k : ℝ) + 1 / 2) * Real.pi : ℝ) := by
      push_cast; ring
    rw [hk', Complex.ofReal_im]
  have him' : v * Real.sin σ = 0 := by
    have hexp : Complex.exp (I * (σ : ℂ)) = Complex.exp ((σ : ℂ) * I) := by congr 1; ring
    rw [Complex.mul_im, hexp, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im] at him
    linarith
  have hv0 : v = 0 := (mul_eq_zero.mp him').resolve_right hsin
  subst hv0
  simp at h0

private lemma abs_sin_pi_div_four_ge_half : (1 / 2 : ℝ) ≤ |Real.sin (Real.pi / 4)| := by
  rw [Real.sin_pi_div_four, abs_of_pos (by positivity)]
  have h1 : (1 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  linarith

private lemma sec_expType_ray {σ : ℝ} (hge : 1 / 2 ≤ |Real.sin σ|) :
    ExpType (Minor.pull (Complex.exp (I * (σ : ℂ))) (fun ξ => (Complex.cos ξ)⁻¹)) := by
  let μ : ℂ := Complex.exp (I * (σ : ℂ))
  have hsin : Real.sin σ ≠ 0 := fun h => by
    rw [h, abs_zero] at hge; linarith
  have hμ_norm : ‖μ‖ = 1 := norm_exp_I_mul_real σ
  have hcont : ContinuousOn (fun v : ℝ => Minor.pull μ (fun ξ => (Complex.cos ξ)⁻¹) v) (Icc 0 1) := by
    intro v _
    have hne := cos_ne_zero_on_pi_div_four_ray hsin v
    have hc : ContinuousAt (fun x : ℝ => μ * (Complex.cos (μ * (x : ℂ)))⁻¹) v :=
      continuousAt_const.mul
        ((Complex.continuous_cos.continuousAt.comp
          (continuousAt_const.mul Complex.continuous_ofReal.continuousAt)).inv₀ hne)
    exact hc.continuousWithinAt
  let δ : ℝ := (Real.exp (1 / 2) - Real.exp (-(1 / 2))) / 2
  have hδ_pos : 0 < δ := by
    have : Real.exp (-(1 / 2)) < Real.exp (1 / 2) := Real.exp_lt_exp.mpr (by norm_num)
    dsimp only [δ]; linarith
  refine expType_of_continuousOn_of_bdd hcont (C₁ := δ⁻¹) fun v hv => ?_
  have hsin_ge : 1 / 2 ≤ |v * Real.sin σ| := by
    rw [abs_mul, abs_of_nonneg (by linarith)]
    calc 1 / 2 ≤ 1 * |Real.sin σ| := by linarith
      _ ≤ v * |Real.sin σ| := mul_le_mul_of_nonneg_right hv (abs_nonneg _)
  have hcos_bd := cos_norm_ge_on_ray hsin hsin_ge
  rw [Minor.pull, norm_mul, hμ_norm, one_mul, norm_inv]
  exact inv_anti₀ hδ_pos hcos_bd

private lemma tan_expType_ray {σ : ℝ} (hge : 1 / 2 ≤ |Real.sin σ|) :
    ExpType (Minor.pull (Complex.exp (I * (σ : ℂ))) Complex.tan) := by
  let μ : ℂ := Complex.exp (I * (σ : ℂ))
  have hsin : Real.sin σ ≠ 0 := fun h => by
    rw [h, abs_zero] at hge; linarith
  have hμ_norm : ‖μ‖ = 1 := norm_exp_I_mul_real σ
  have hcont : ContinuousOn (fun v : ℝ => Minor.pull μ Complex.tan v) (Icc 0 1) := by
    intro v _
    have hne := cos_ne_zero_on_pi_div_four_ray hsin v
    have hc : ContinuousAt (fun x : ℝ => μ * Complex.tan (μ * (x : ℂ))) v := by
      have htan : ContinuousAt Complex.tan (μ * (v : ℂ)) :=
        (Complex.hasDerivAt_tan hne).continuousAt
      have hmul_cont : ContinuousAt (fun x : ℝ => μ * (x : ℂ)) v :=
        continuousAt_const.mul (Complex.continuous_ofReal.continuousAt (x := v))
      exact continuousAt_const.mul
        (ContinuousAt.comp (f := fun x : ℝ => μ * (x : ℂ)) (g := Complex.tan) htan hmul_cont)
    exact hc.continuousWithinAt
  let δ : ℝ := 1 + 2 / (Real.exp 1 - 1)
  refine expType_of_continuousOn_of_bdd hcont (C₁ := δ) fun v hv => ?_
  let w : ℂ := μ * (v : ℂ)
  have hw_im : w.im = v * Real.sin σ := by
    have hexp : Complex.exp (I * (σ : ℂ)) = Complex.exp ((σ : ℂ) * I) := by congr 1; ring
    dsimp only [w, μ]
    rw [Complex.mul_im, hexp, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h_abs : 1 / 2 ≤ |w.im| := by
    rw [hw_im, abs_mul, abs_of_nonneg (by linarith)]
    calc 1 / 2 ≤ 1 * |Real.sin σ| := by linarith
      _ ≤ v * |Real.sin σ| := mul_le_mul_of_nonneg_right hv (abs_nonneg _)
  have hcos_def : Complex.cos w = (Complex.exp (I * w) + Complex.exp (-I * w)) / 2 := by
    rw [Complex.cos, mul_comm w I]; congr 1; ring_nf
  have hsin_def : Complex.sin w = (Complex.exp (-I * w) - Complex.exp (I * w)) * I / 2 := by
    rw [Complex.sin]
    have h1 : Complex.exp (w * I) = Complex.exp (I * w) := by congr 1; ring
    have h2 : Complex.exp (-(w * I)) = Complex.exp (-I * w) := by congr 1; ring
    rw [show -w * I = -(w * I) by ring, h1, h2]
  have h1 : ‖Complex.exp (I * w)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp, show (I * w).re = -w.im by simp]
  have h2 : ‖Complex.exp (-I * w)‖ = Real.exp w.im := by
    rw [Complex.norm_exp, show (-I * w).re = w.im by simp]
  have hsin_le : ‖Complex.sin w‖ ≤ (Real.exp |w.im| + Real.exp (-|w.im|)) / 2 := by
    rw [hsin_def, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    calc ‖Complex.exp (-I * w) - Complex.exp (I * w)‖
        ≤ ‖Complex.exp (-I * w)‖ + ‖Complex.exp (I * w)‖ := norm_sub_le _ _
      _ = Real.exp w.im + Real.exp (-w.im) := by rw [h1, h2]
      _ = Real.exp |w.im| + Real.exp (-|w.im|) := by
          rcases le_or_gt 0 w.im with hw_pos | hw_neg
          · rw [abs_of_nonneg hw_pos]
          · rw [abs_of_neg hw_neg, neg_neg, add_comm]
  have hcos_ge : (Real.exp |w.im| - Real.exp (-|w.im|)) / 2 ≤ ‖Complex.cos w‖ := by
    rw [hcos_def, norm_div, Complex.norm_ofNat]
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    rcases le_or_gt 0 w.im with hw_pos | hw_neg
    · rw [abs_of_nonneg hw_pos]
      have htri := norm_sub_norm_le (Complex.exp (-I * w)) (-(Complex.exp (I * w)))
      rwa [sub_neg_eq_add, norm_neg, h1, h2, add_comm] at htri
    · rw [abs_of_neg hw_neg, neg_neg]
      have htri := norm_sub_norm_le (Complex.exp (I * w)) (-(Complex.exp (-I * w)))
      rwa [sub_neg_eq_add, norm_neg, h1, h2] at htri
  have hden_pos : 0 < Real.exp |w.im| - Real.exp (-|w.im|) := by
    have : -|w.im| < |w.im| := by linarith
    linarith [Real.exp_lt_exp.mpr this]
  have hratio : (Real.exp |w.im| + Real.exp (-|w.im|)) / (Real.exp |w.im| - Real.exp (-|w.im|)) ≤ δ := by
    have h_e1 : 0 < Real.exp 1 - 1 := by linarith [Real.one_lt_exp_iff.mpr one_pos]
    have h_ebound : Real.exp 1 ≤ Real.exp (2 * |w.im|) := Real.exp_le_exp.mpr (by linarith)
    have h_inv : (Real.exp (2 * |w.im|) - 1)⁻¹ ≤ (Real.exp 1 - 1)⁻¹ :=
      inv_anti₀ h_e1 (by linarith)
    have h_id : (Real.exp |w.im| + Real.exp (-|w.im|)) / (Real.exp |w.im| - Real.exp (-|w.im|)) =
        1 + 2 / (Real.exp (2 * |w.im|) - 1) := by
      have hexp_pos : 0 < Real.exp |w.im| := Real.exp_pos _
      have hexp2_ne : Real.exp |w.im| ^ 2 - 1 ≠ 0 := by
        have hgt : 1 < Real.exp |w.im| := Real.one_lt_exp_iff.mpr (by linarith)
        nlinarith
      rw [Real.exp_neg, show 2 * |w.im| = |w.im| + |w.im| by ring, Real.exp_add, ← sq]
      field_simp [hexp_pos.ne', hden_pos.ne', hexp2_ne]
      ring
    rw [h_id]
    dsimp only [δ]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linarith
  rw [Minor.pull, norm_mul, hμ_norm, one_mul, Complex.tan_eq_sin_div_cos, norm_div]
  calc ‖Complex.sin w‖ / ‖Complex.cos w‖
      ≤ ((Real.exp |w.im| + Real.exp (-|w.im|)) / 2) / ((Real.exp |w.im| - Real.exp (-|w.im|)) / 2) :=
        div_le_div₀ (by positivity) hsin_le (by positivity) hcos_ge
    _ = (Real.exp |w.im| + Real.exp (-|w.im|)) / (Real.exp |w.im| - Real.exp (-|w.im|)) := by
        field_simp
    _ ≤ δ := hratio

/-- Genuine `HigherOrderBorelData` witness for `Complex.tan` along `θ₀ = 0`
with simple poles at `(m + 1/2) π` of residue `-1`. -/
def tan_borelData :
    HigherOrderBorelData Complex.tan 0 trigPole (fun _ => 1) (fun _ s => if s = 1 then -1 else 0) where
  α₀ := Real.pi / 3
  θ := Real.pi / 4
  ε := 1
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := one_pos
  ω_pos := trigPole_pos
  ω_mono := trigPole_mono
  ord_pos := fun _ => le_rfl
  pp_lead_ne_zero := fun _ => by simp
  analyticOn := fun z hz => by
    rw [rotatedPuncturedWedge] at hz
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at hz
    have hne := cos_ne_zero_on_puncturedWedge hz
    rw [show Complex.tan = fun w => Complex.sin w / Complex.cos w from funext Complex.tan_eq_sin_div_cos]
    exact Complex.differentiable_sin.analyticAt z |>.div (Complex.differentiable_cos.analyticAt z) hne
  pole_principalPart := fun m => by
    let z_m : ℂ := (trigPole m : ℂ)
    have hderiv : deriv Complex.cos z_m = -((-1 : ℂ) ^ m) := by
      rw [Complex.deriv_cos, sin_trigPole]
    have hderiv_ne : deriv Complex.cos z_m ≠ 0 := by
      rw [hderiv]; exact neg_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    obtain ⟨c, L, hc1, hL⟩ := pole_principalPart_of_simpleZero_div_pow
      (Complex.differentiable_sin.analyticAt z_m)
      (Complex.differentiable_cos.analyticAt z_m)
      (cos_trigPole m) hderiv_ne 1 le_rfl
    have hc_val : c 1 = -1 := by
      rw [hc1, sin_trigPole, hderiv, pow_one]
      have hpow_ne : (-1 : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
      field_simp [hpow_ne]
    refine ⟨L, ?_⟩
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
    refine hL.congr' (eventually_nhdsWithin_of_forall fun z _ => ?_)
    dsimp only [z_m]
    simp only [pow_one, Finset.Icc_self, Finset.sum_singleton, ↓reduceIte,
      Complex.tan_eq_sin_div_cos]
    rw [hc_val]
  expType_plus := by
    have h := tan_expType_ray abs_sin_pi_div_four_ge_half
    simpa [zero_add] using h
  expType_minus := by
    have hge : 1 / 2 ≤ |Real.sin (-(Real.pi / 4))| := by
      simpa [Real.sin_neg, abs_neg] using abs_sin_pi_div_four_ge_half
    have h := tan_expType_ray hge
    simpa [zero_sub] using h

/-- **Showcase Corollary 2A (Tangent / Odd Euler Numbers OGF)**:
`ogfOfEGF Complex.tan = ∑_{n ≥ 0} tan^{(n)}(0) x^n` is unconditionally differentially
transcendental over `ℂ(x)`. -/
theorem tanOGF_algebraicIndependent :
    AlgebraicIndependent ℂ (seriesCoordinates (ogfOfEGF Complex.tan)) :=
  ogf_algebraicIndependent_of_higherOrderBorel tan_borelData

/-- Explicit `D`-algebraicity of the tangent EGF (`tan' = 1 + tan^2`): the EGF is D-algebraic
while the OGF `ogfOfEGF Complex.tan` is D-transcendental. -/
theorem tan_D_algebraic {ξ : ℂ} (hcos : Complex.cos ξ ≠ 0) :
    deriv Complex.tan ξ = 1 + Complex.tan ξ ^ 2 := by
  rw [(Complex.hasDerivAt_tan hcos).deriv, Complex.tan_eq_sin_div_cos]
  have h1 := Complex.sin_sq_add_cos_sq ξ
  field_simp [hcos]
  rw [← h1]
  ring

/-- Genuine `HigherOrderBorelData` witness for `sec ξ = (cos ξ)⁻¹` along `θ₀ = 0`
with simple poles at `(m + 1/2) π` of residue `(-1)^(m + 1)`. -/
def sec_borelData :
    HigherOrderBorelData (fun ξ => (Complex.cos ξ)⁻¹) 0 trigPole (fun _ => 1)
      (fun m s => if s = 1 then (-1 : ℂ) ^ (m + 1) else 0) where
  α₀ := Real.pi / 3
  θ := Real.pi / 4
  ε := 1
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := one_pos
  ω_pos := trigPole_pos
  ω_mono := trigPole_mono
  ord_pos := fun _ => le_rfl
  pp_lead_ne_zero := fun m => by simp
  analyticOn := fun z hz => by
    rw [rotatedPuncturedWedge] at hz
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at hz
    exact (Complex.differentiable_cos.analyticAt z).inv (cos_ne_zero_on_puncturedWedge hz)
  pole_principalPart := fun m => by
    let z_m : ℂ := (trigPole m : ℂ)
    have hderiv : deriv Complex.cos z_m = (-1 : ℂ) ^ (m + 1) := by
      rw [Complex.deriv_cos, sin_trigPole, pow_succ]; ring
    have hderiv_ne : deriv Complex.cos z_m ≠ 0 := by
      rw [hderiv]; exact pow_ne_zero _ (by norm_num)
    obtain ⟨c, L, hc1, hL⟩ := pole_principalPart_of_simpleZero_div_pow
      (analyticAt_const (v := (1 : ℂ)))
      (Complex.differentiable_cos.analyticAt z_m)
      (cos_trigPole m) hderiv_ne 1 le_rfl
    have hc_val : c 1 = (-1 : ℂ) ^ (m + 1) := by
      rw [hc1, hderiv, pow_one, one_div, ← inv_pow]
      have : ((-1 : ℂ))⁻¹ = -1 := by norm_num
      rw [this]
    refine ⟨L, ?_⟩
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
    refine hL.congr' (eventually_nhdsWithin_of_forall fun z _ => ?_)
    dsimp only [z_m]
    simp only [pow_one, Finset.Icc_self, Finset.sum_singleton, ↓reduceIte, one_div]
    rw [hc_val]
  expType_plus := by
    have h := sec_expType_ray abs_sin_pi_div_four_ge_half
    simpa [zero_add] using h
  expType_minus := by
    have hge : 1 / 2 ≤ |Real.sin (-(Real.pi / 4))| := by
      simpa [Real.sin_neg, abs_neg] using abs_sin_pi_div_four_ge_half
    have h := sec_expType_ray hge
    simpa [zero_sub] using h

/-- **Showcase Corollary 2B (Secant / Even Euler Numbers OGF)**:
`ogfOfEGF (fun ξ => (Complex.cos ξ)⁻¹)` is unconditionally differentially transcendental over `ℂ(x)`. -/
theorem secOGF_algebraicIndependent :
    AlgebraicIndependent ℂ (seriesCoordinates (ogfOfEGF fun ξ => (Complex.cos ξ)⁻¹)) :=
  ogf_algebraicIndependent_of_higherOrderBorel sec_borelData

/-- Explicit `D`-algebraicity of the secant EGF (`(sec')^2 = sec^4 - sec^2`). -/
theorem sec_D_algebraic {ξ : ℂ} (hcos : Complex.cos ξ ≠ 0) :
    deriv (fun w => (Complex.cos w)⁻¹) ξ ^ 2 =
      (Complex.cos ξ)⁻¹ ^ 4 - (Complex.cos ξ)⁻¹ ^ 2 := by
  have hd : HasDerivAt (fun w => (Complex.cos w)⁻¹)
      (-(-Complex.sin ξ) / Complex.cos ξ ^ 2) ξ :=
    (Complex.hasDerivAt_cos ξ).inv hcos
  rw [hd.deriv]
  have h1 := Complex.sin_sq_add_cos_sq ξ
  field_simp [hcos]
  rw [← h1]
  ring

private lemma secPow_exist (p : ℕ) (hp : 1 ≤ p) (m : ℕ) :
    ∃ (c : ℕ → ℂ) (L : ℂ), c p = 1 / deriv Complex.cos (trigPole m : ℂ) ^ p ∧
      Filter.Tendsto
        (fun z : ℂ => 1 / Complex.cos z ^ p - ∑ s ∈ Finset.Icc 1 p, c s / (z - (trigPole m : ℂ)) ^ s)
        (𝓝[≠] (trigPole m : ℂ)) (𝓝 L) :=
  pole_principalPart_of_simpleZero_div_pow
    (analyticAt_const (v := (1 : ℂ))) (Complex.differentiable_cos.analyticAt (trigPole m : ℂ))
    (cos_trigPole m)
    (by rw [Complex.deriv_cos, sin_trigPole]; exact neg_ne_zero.mpr (pow_ne_zero _ (by norm_num)))
    p hp

/-- Arbitrary-order principal-part coefficients for `(cos ξ)⁻¹ ^ p` (`1 ≤ p`). -/
noncomputable def secPowPP (p : ℕ) (hp : 1 ≤ p) (m s : ℕ) : ℂ :=
  (Classical.choose (secPow_exist p hp m)) s

/-- Genuine `HigherOrderBorelData` witness for `(cos ξ)⁻¹ ^ p` (`1 ≤ p`) with poles of exact
order `p` at `(m + 1/2) π`. -/
def secPow_borelData (p : ℕ) (hp : 1 ≤ p) :
    HigherOrderBorelData (fun ξ => (Complex.cos ξ)⁻¹ ^ p) 0 trigPole (fun _ => p)
      (secPowPP p hp) where
  α₀ := Real.pi / 3
  θ := Real.pi / 4
  ε := 1
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := one_pos
  ω_pos := trigPole_pos
  ω_mono := trigPole_mono
  ord_pos := fun _ => hp
  pp_lead_ne_zero := fun m => by
    obtain ⟨L, hc_eq, _⟩ := Classical.choose_spec (secPow_exist p hp m)
    unfold secPowPP
    rw [hc_eq, Complex.deriv_cos, sin_trigPole]
    exact div_ne_zero one_ne_zero (pow_ne_zero p (neg_ne_zero.mpr (pow_ne_zero _ (by norm_num))))
  analyticOn := fun z hz => by
    rw [rotatedPuncturedWedge] at hz
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at hz
    exact ((Complex.differentiable_cos.analyticAt z).inv (cos_ne_zero_on_puncturedWedge hz)).pow p
  pole_principalPart := fun m => by
    obtain ⟨L, _, hL⟩ := Classical.choose_spec (secPow_exist p hp m)
    refine ⟨L, ?_⟩
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
    refine hL.congr' (eventually_nhdsWithin_of_forall fun z _ => ?_)
    simp only [secPowPP, one_div, inv_pow]
  expType_plus := by
    have hsec := sec_expType_ray abs_sin_pi_div_four_ge_half
    have hpow := expType_pull_pow (norm_exp_I_mul_real (Real.pi / 4)) hsec p
    simpa [zero_add] using hpow
  expType_minus := by
    have hge : 1 / 2 ≤ |Real.sin (-(Real.pi / 4))| := by
      simpa [Real.sin_neg, abs_neg] using abs_sin_pi_div_four_ge_half
    have hsec := sec_expType_ray hge
    have hpow := expType_pull_pow (norm_exp_I_mul_real (-(Real.pi / 4))) hsec p
    simpa [zero_sub] using hpow

/-- **Showcase Corollary 3A (Arbitrary-Order Secant Powers `(cos ξ)⁻¹ ^ p`)**:
For every `p ≥ 1`, `ogfOfEGF (fun ξ => (Complex.cos ξ)⁻¹ ^ p)` is unconditionally differentially
transcendental over `ℂ(x)`. -/
theorem secPowOGF_algebraicIndependent (p : ℕ) (hp : 1 ≤ p) :
    AlgebraicIndependent ℂ (seriesCoordinates (ogfOfEGF fun ξ => (Complex.cos ξ)⁻¹ ^ p)) :=
  ogf_algebraicIndependent_of_higherOrderBorel (secPow_borelData p hp)

/-- Explicit double-pole `HigherOrderBorelData` witness for `sec^2 ξ = (cos ξ)⁻¹ ^ 2`
(`ord _ = 2`, `pp _ s = if s = 2 then 1 else 0`). -/
def sec2_borelData :
    HigherOrderBorelData (fun ξ => (Complex.cos ξ)⁻¹ ^ 2) 0 trigPole (fun _ => 2)
      (fun _ s => if s = 2 then 1 else 0) where
  α₀ := Real.pi / 3
  θ := Real.pi / 4
  ε := 1
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := one_pos
  ω_pos := trigPole_pos
  ω_mono := trigPole_mono
  ord_pos := fun _ => by omega
  pp_lead_ne_zero := fun _ => by simp
  analyticOn := fun z hz => by
    rw [rotatedPuncturedWedge] at hz
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at hz
    exact ((Complex.differentiable_cos.analyticAt z).inv (cos_ne_zero_on_puncturedWedge hz)).pow 2
  pole_principalPart := fun m => by
    let z_m : ℂ := (trigPole m : ℂ)
    let hsin : ℂ → ℂ := dslope Complex.sin 0
    have hsin_ana : AnalyticAt ℂ hsin 0 :=
      Complex.differentiable_sin.analyticAt 0 |>.hasFPowerSeriesAt.dslope_fslope.analyticAt
    have hsin0 : hsin 0 = 1 := by simp [hsin, dslope_same, Complex.deriv_sin]
    have hsin_even : ∀ w : ℂ, hsin (-w) = hsin w := by
      intro w
      by_cases hw : w = 0
      · subst hw; simp
      · dsimp only [hsin]
        rw [dslope_of_ne _ (neg_ne_zero.mpr hw), dslope_of_ne _ hw, slope_def_field,
          slope_def_field, Complex.sin_zero, sub_zero, Complex.sin_neg]
        field_simp [hw]
        ring
    have hsin_deriv0 : deriv hsin 0 = 0 := by
      have hd1 : HasDerivAt hsin (deriv hsin 0) 0 := hsin_ana.differentiableAt.hasDerivAt
      have hd1' : HasDerivAt hsin (deriv hsin 0) (-(0 : ℂ)) := by simpa using hd1
      have hd2 : HasDerivAt (fun w : ℂ => hsin (-w)) (deriv hsin 0 * (-1)) 0 := by
        simpa [Function.comp_def] using hd1'.comp 0 (hasDerivAt_neg (0 : ℂ))
      have heq : (fun w : ℂ => hsin (-w)) = hsin := funext hsin_even
      rw [heq] at hd2
      have hsame := hd1.unique hd2
      linear_combination (1 / 2 : ℂ) * hsame
    let G : ℂ → ℂ := fun w => (hsin w)⁻¹ ^ 2
    have hG_ana : AnalyticAt ℂ G 0 := (hsin_ana.inv (by rw [hsin0]; exact one_ne_zero)).pow 2
    have hG0 : G 0 = 1 := by simp [G, hsin0]
    have hG_deriv0 : deriv G 0 = 0 := by
      have hd_inv : HasDerivAt (fun w => (hsin w)⁻¹) (-(deriv hsin 0) / hsin 0 ^ 2) 0 :=
        hsin_ana.differentiableAt.hasDerivAt.inv (by rw [hsin0]; exact one_ne_zero)
      have hd_pow := hd_inv.pow 2
      rw [hsin_deriv0, hsin0] at hd_pow
      have hG_eq_pow : G = (fun w => (hsin w)⁻¹) ^ 2 := rfl
      rw [hG_eq_pow]
      simpa using hd_pow.deriv
    let R : ℂ → ℂ := dslope (dslope G 0) 0
    have hR_ana : AnalyticAt ℂ R 0 :=
      (hG_ana.hasFPowerSeriesAt.dslope_fslope.analyticAt).hasFPowerSeriesAt.dslope_fslope.analyticAt
    refine ⟨R 0, ?_⟩
    have htend_shift : Tendsto (fun z : ℂ => z - z_m) (𝓝[≠] z_m) (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, eventually_nhdsWithin_of_forall fun z hz => sub_ne_zero.mpr hz⟩
      have hc : ContinuousAt (fun z : ℂ => z - z_m) z_m :=
        continuousAt_id.sub continuousAt_const
      have ht : Tendsto (fun z : ℂ => z - z_m) (𝓝 z_m) (𝓝 0) := by
        simpa [sub_self] using hc.tendsto
      exact ht.mono_left nhdsWithin_le_nhds
    have hR_tend : Tendsto (fun z : ℂ => R (z - z_m)) (𝓝[≠] z_m) (𝓝 (R 0)) :=
      hR_ana.continuousAt.continuousWithinAt.tendsto.comp htend_shift
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
    refine hR_tend.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
    have hcos_shift : Complex.cos z = (-1 : ℂ) ^ (m + 1) * Complex.sin (z - z_m) := by
      have hz_split : z = z_m + (z - z_m) := by ring
      conv_lhs => rw [hz_split, Complex.cos_add, cos_trigPole, sin_trigPole]
      rw [pow_succ]; ring
    have hw_ne : z - z_m ≠ 0 := sub_ne_zero.mpr hz
    have hsin_eq : Complex.sin (z - z_m) = (z - z_m) * hsin (z - z_m) := by
      dsimp only [hsin]
      simp only [dslope_of_ne _ hw_ne, slope_def_field, Complex.sin_zero, sub_zero]
      rw [mul_div_cancel₀ _ hw_ne]
    have hG_eq : G (z - z_m) = 1 + (z - z_m) ^ 2 * R (z - z_m) := by
      have h1 : dslope G 0 (z - z_m) = (G (z - z_m) - 1) / (z - z_m) := by
        simp only [dslope_of_ne _ hw_ne, slope_def_field, hG0, sub_zero]
      have h2 : R (z - z_m) = dslope G 0 (z - z_m) / (z - z_m) := by
        dsimp only [R]
        simp only [dslope_of_ne _ hw_ne, slope_def_field, dslope_same, hG_deriv0, sub_zero]
      rw [h1, div_div, ← pow_two] at h2
      rw [h2, mul_div_cancel₀ _ (pow_ne_zero 2 hw_ne)]
      ring
    have hcos_sq : Complex.cos z ^ 2 = (z - z_m) ^ 2 * (hsin (z - z_m)) ^ 2 := by
      rw [hcos_shift, mul_pow, ← pow_mul, mul_comm (m + 1) 2, pow_mul,
        show (-1 : ℂ) ^ 2 = 1 by norm_num, one_pow, one_mul, hsin_eq, mul_pow]
    have hsum_eq :
        (∑ s ∈ Finset.Icc 1 2, (if s = 2 then (1 : ℂ) else 0) / (z - z_m) ^ s) =
          1 / (z - z_m) ^ 2 := by
      have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
      rw [hIcc, Finset.sum_pair (by decide)]
      simp
    dsimp only
    rw [show (Complex.cos z)⁻¹ ^ 2 = (Complex.cos z ^ 2)⁻¹ by rw [inv_pow],
      hcos_sq, mul_inv,
      show (hsin (z - z_m) ^ 2)⁻¹ = G (z - z_m) from by dsimp only [G]; rw [inv_pow],
      hG_eq, mul_add, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hw_ne), one_mul]
    rw [show ∑ s ∈ Finset.Icc 1 2, (if s = 2 then (1 : ℂ) else 0) / (z - (trigPole m : ℂ)) ^ s =
      1 / (z - z_m) ^ 2 from by simpa [z_m] using hsum_eq]
    ring
  expType_plus := by
    have hsec := sec_expType_ray abs_sin_pi_div_four_ge_half
    have hpow := expType_pull_pow (norm_exp_I_mul_real (Real.pi / 4)) hsec 2
    simpa [zero_add] using hpow
  expType_minus := by
    have hge : 1 / 2 ≤ |Real.sin (-(Real.pi / 4))| := by
      simpa [Real.sin_neg, abs_neg] using abs_sin_pi_div_four_ge_half
    have hsec := sec_expType_ray hge
    have hpow := expType_pull_pow (norm_exp_I_mul_real (-(Real.pi / 4))) hsec 2
    simpa [zero_sub] using hpow

/-- **Showcase Corollary 3B (Double-Pole `sec^2 ξ = 1 + tan^2 ξ` OGF)**:
`ogfOfEGF (fun ξ => (Complex.cos ξ)⁻¹ ^ 2)` is unconditionally differentially transcendental
over `ℂ(x)`. -/
theorem sec2OGF_algebraicIndependent :
    AlgebraicIndependent ℂ (seriesCoordinates (ogfOfEGF fun ξ => (Complex.cos ξ)⁻¹ ^ 2)) :=
  ogf_algebraicIndependent_of_higherOrderBorel sec2_borelData

/-! ### 6. Showcase Corollary 4: General Briot–Bouquet Rational-Exponential Family `(1 - c e^{lam ξ})^{-p}` -/

@[expose] noncomputable def ratExpAngle (c : ℂ) : ℝ :=
  if 0 < (c⁻¹).arg then (c⁻¹).arg else (c⁻¹).arg + 2 * Real.pi

private lemma ratExpAngle_mem_Ioo {c : ℂ} (hc_norm : ‖c‖ = 1) (hc_ne : c ≠ 1) :
    ratExpAngle c ∈ Set.Ioo 0 (2 * Real.pi) := by
  have hc_inv_norm : ‖c⁻¹‖ = 1 := by simp [hc_norm]
  have hc_inv_ne : c⁻¹ ≠ 1 := fun h => hc_ne (inv_inj.mp (by simpa using h))
  have harg_ne : (c⁻¹).arg ≠ 0 := by
    intro h0
    have hexp := Complex.norm_mul_exp_arg_mul_I (c⁻¹)
    rw [hc_inv_norm, h0] at hexp
    simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at hexp
    exact hc_inv_ne hexp.symm
  have hmem := Complex.arg_mem_Ioc (c⁻¹)
  dsimp only [ratExpAngle]
  split_ifs with hpos
  · exact ⟨hpos, lt_of_le_of_lt hmem.2 (by linarith [Real.pi_pos])⟩
  · have hneg : (c⁻¹).arg < 0 := lt_of_le_of_ne (not_lt.mp hpos) harg_ne
    refine ⟨?_, ?_⟩
    · linarith [hmem.1]
    · linarith [hneg]

private lemma exp_ratExpAngle {c : ℂ} (hc_norm : ‖c‖ = 1) :
    Complex.exp ((ratExpAngle c : ℂ) * I) = c⁻¹ := by
  have hc_inv_norm : ‖c⁻¹‖ = 1 := by simp [hc_norm]
  have hexp := Complex.norm_mul_exp_arg_mul_I (c⁻¹)
  rw [hc_inv_norm, Complex.ofReal_one, one_mul] at hexp
  dsimp only [ratExpAngle]
  split_ifs
  · exact hexp
  · push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    exact hexp

@[expose] noncomputable def ratExpRayAngle (lam : ℂ) : ℝ :=
  (I / lam).arg

private lemma mul_exp_ratExpRayAngle {lam : ℂ} (hlam : lam ≠ 0) :
    lam * Complex.exp (I * (ratExpRayAngle lam : ℂ)) = I * (‖lam‖ : ℂ) := by
  have hnorm : ‖I / lam‖ = ‖lam‖⁻¹ := by
    rw [norm_div, Complex.norm_I, one_div]
  have hexp := Complex.norm_mul_exp_arg_mul_I (I / lam)
  rw [hnorm] at hexp
  rw [mul_comm I (ratExpRayAngle lam : ℂ)]
  change ((‖lam‖⁻¹ : ℝ) : ℂ) * Complex.exp ((ratExpRayAngle lam : ℂ) * I) = I / lam at hexp
  have hmul := congrArg (fun z : ℂ => lam * (‖lam‖ : ℂ) * z) hexp
  have hlam_norm_ne : (‖lam‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hlam)
  calc lam * Complex.exp ((ratExpRayAngle lam : ℂ) * I)
      = lam * (‖lam‖ : ℂ) * (((‖lam‖⁻¹ : ℝ) : ℂ) * Complex.exp ((ratExpRayAngle lam : ℂ) * I)) := by
        push_cast; field_simp [hlam_norm_ne]
    _ = lam * (‖lam‖ : ℂ) * (I / lam) := hmul
    _ = I * (‖lam‖ : ℂ) := by field_simp [hlam]

@[expose] noncomputable def ratExpPole (lam c : ℂ) (m : ℕ) : ℝ :=
  (ratExpAngle c + 2 * Real.pi * (m : ℝ)) / ‖lam‖

private lemma ratExpPole_pos {lam c : ℂ} (hlam : lam ≠ 0) (hc_norm : ‖c‖ = 1) (hc_ne : c ≠ 1) :
    0 < ratExpPole lam c 0 := by
  unfold ratExpPole
  have hα := (ratExpAngle_mem_Ioo hc_norm hc_ne).1
  have hnorm : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  positivity

private lemma ratExpPole_mono {lam c : ℂ} (hlam : lam ≠ 0) : StrictMono (ratExpPole lam c) := by
  intro a b hab
  unfold ratExpPole
  have hnorm : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  exact div_lt_div_of_pos_right (by nlinarith [Real.pi_pos]) hnorm

private lemma one_sub_mul_exp_ne_zero_on_wedge {lam c : ℂ} (hlam : lam ≠ 0)
    (hc_norm : ‖c‖ = 1) (hc_ne : c ≠ 1) {z : ℂ}
    (hz : z ∈ rotatedPuncturedWedge (ratExpRayAngle lam) (Real.pi / 3)
      (min (ratExpAngle c / ‖lam‖) ((2 * Real.pi - ratExpAngle c) / ‖lam‖) / 2)
      (ratExpPole lam c)) :
    1 - c * Complex.exp (lam * z) ≠ 0 := by
  intro h0
  have hcexp : Complex.exp (lam * z) = c⁻¹ := by
    have heq : c * Complex.exp (lam * z) = 1 := (sub_eq_zero.mp h0).symm
    have hc_ne0 : c ≠ 0 := fun h => by rw [h, norm_zero] at hc_norm; norm_num at hc_norm
    exact eq_inv_of_mul_eq_one_right heq
  rw [← exp_ratExpAngle hc_norm, Complex.exp_eq_exp_iff_exists_int] at hcexp
  obtain ⟨k, hk⟩ := hcexp
  let θ₀ : ℝ := ratExpRayAngle lam
  let μ : ℂ := Complex.exp (I * (θ₀ : ℂ))
  let w : ℂ := Complex.exp (-I * (θ₀ : ℂ)) * z
  have hz_eq : z = μ * w := by
    dsimp only [μ, w]
    rw [← mul_assoc, ← Complex.exp_add, show I * (θ₀ : ℂ) + -I * (θ₀ : ℂ) = 0 by ring,
      Complex.exp_zero, one_mul]
  have hlamz : lam * z = I * (‖lam‖ : ℂ) * w := by
    rw [hz_eq, ← mul_assoc, mul_exp_ratExpRayAngle hlam]
  have hw_eq : w = (((ratExpAngle c + 2 * Real.pi * (k : ℝ)) / ‖lam‖ : ℝ) : ℂ) := by
    have hnorm_ne : (‖lam‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hlam)
    have hk' : I * (‖lam‖ : ℂ) * w =
        I * (ratExpAngle c + 2 * Real.pi * (k : ℂ) : ℂ) := by
      rw [← hlamz, hk]; ring
    have hw1 := congrArg (fun u : ℂ => (I * (‖lam‖ : ℂ))⁻¹ * u) hk'
    have hI_ne : (I * (‖lam‖ : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero hnorm_ne
    rw [← mul_assoc, inv_mul_cancel₀ hI_ne, one_mul] at hw1
    rw [hw1]
    push_cast
    field_simp [Complex.I_ne_zero, hnorm_ne]
  have hα := ratExpAngle_mem_Ioo hc_norm hc_ne
  have hnorm_pos : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
  rcases lt_or_ge k 0 with hk_neg | hk_nonneg
  · have hk_le : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk_neg
    have hw_re_le : w.re ≤ -((2 * Real.pi - ratExpAngle c) / ‖lam‖) := by
      calc w.re = (ratExpAngle c + 2 * Real.pi * (k : ℝ)) / ‖lam‖ := by
            rw [hw_eq, Complex.ofReal_re]
        _ ≤ (-(2 * Real.pi - ratExpAngle c)) / ‖lam‖ :=
            div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) hnorm_pos.le
        _ = -((2 * Real.pi - ratExpAngle c) / ‖lam‖) := neg_div _ _
    rcases hz.1 with hball | hsec
    · rw [Metric.mem_ball, dist_zero_right] at hball
      have hmin_le : min (ratExpAngle c / ‖lam‖) ((2 * Real.pi - ratExpAngle c) / ‖lam‖) / 2 <
          (2 * Real.pi - ratExpAngle c) / ‖lam‖ := by
        have hpos2 : 0 < (2 * Real.pi - ratExpAngle c) / ‖lam‖ := div_pos (by linarith [hα.2]) hnorm_pos
        linarith [min_le_right (ratExpAngle c / ‖lam‖) ((2 * Real.pi - ratExpAngle c) / ‖lam‖)]
      have h1 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
      have h2 : (2 * Real.pi - ratExpAngle c) / ‖lam‖ ≤ |w.re| := by
        rw [abs_of_nonpos (by linarith [div_pos (by linarith [hα.2] : 0 < 2 * Real.pi - ratExpAngle c) hnorm_pos])]
        linarith
      change ‖w‖ < _ at hball
      linarith
    · have hre_pos : 0 < w.re := hsec.1
      have hpos2 : 0 < (2 * Real.pi - ratExpAngle c) / ‖lam‖ := div_pos (by linarith [hα.2]) hnorm_pos
      linarith
  · apply hz.2
    refine ⟨k.toNat, ?_⟩
    change (ratExpPole lam c k.toNat : ℂ) = w
    rw [hw_eq]
    have hk_eq : (k.toNat : ℂ) = (k : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hk_nonneg
    unfold ratExpPole
    push_cast
    rw [hk_eq]

private lemma ratExp_expType_ray {lam c : ℂ} (hlam : lam ≠ 0) (hc_norm : ‖c‖ = 1) (hc_ne : c ≠ 1)
    {σ : ℝ} (hsin : Real.sin σ ≠ 0) :
    ExpType (Minor.pull (Complex.exp (I * ((ratExpRayAngle lam + σ : ℝ) : ℂ)))
      (fun ξ => (1 - c * Complex.exp (lam * ξ))⁻¹)) := by
  let θ₀ : ℝ := ratExpRayAngle lam
  let μ : ℂ := Complex.exp (I * ((θ₀ + σ : ℝ) : ℂ))
  have hμ_norm : ‖μ‖ = 1 := norm_exp_I_mul_real (θ₀ + σ)
  have hlamμ : lam * μ = I * (‖lam‖ : ℂ) * Complex.exp (I * (σ : ℂ)) := by
    have hexp : μ = Complex.exp (I * (θ₀ : ℂ)) * Complex.exp (I * (σ : ℂ)) := by
      dsimp only [μ]
      rw [← Complex.exp_add]
      congr 1; push_cast; ring
    rw [hexp, ← mul_assoc, mul_exp_ratExpRayAngle hlam]
  have hre_coeff : (lam * μ).re = -(‖lam‖ * Real.sin σ) := by
    have hexp : Complex.exp (I * (σ : ℂ)) = Complex.exp ((σ : ℂ) * I) := by congr 1; ring
    rw [hlamμ, hexp]
    simp [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hre_ne0 : (lam * μ).re ≠ 0 := by
    rw [hre_coeff]
    exact neg_ne_zero.mpr (mul_ne_zero (norm_ne_zero_iff.mpr hlam) hsin)
  have hne_all : ∀ v : ℝ, 1 - c * Complex.exp (lam * (μ * (v : ℂ))) ≠ 0 := by
    intro v h0
    rcases eq_or_ne v 0 with rfl | hv_ne
    · simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, sub_eq_zero] at h0
      exact hc_ne h0.symm
    · have hnorm_one : ‖c * Complex.exp (lam * (μ * (v : ℂ)))‖ = 1 := by
        have := (sub_eq_zero.mp h0).symm
        rw [this, norm_one]
      rw [norm_mul, hc_norm, one_mul, Complex.norm_exp] at hnorm_one
      have hexp0 : (lam * (μ * (v : ℂ))).re = 0 := Real.exp_injective (by simpa using hnorm_one)
      have hre_v : (lam * (μ * (v : ℂ))).re = (lam * μ).re * v := by
        rw [← mul_assoc]
        simp [Complex.mul_re]
      rw [hre_v] at hexp0
      exact (mul_eq_zero.mp hexp0).elim hre_ne0 hv_ne
  have hcont : ContinuousOn
      (fun v : ℝ => Minor.pull μ (fun ξ => (1 - c * Complex.exp (lam * ξ))⁻¹) v) (Icc 0 1) := by
    intro v _
    have hmul_cont : ContinuousAt (fun x : ℝ => lam * (μ * (x : ℂ))) v :=
      continuousAt_const.mul (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt (x := v)))
    have hc : ContinuousAt
        (fun x : ℝ => μ * (1 - c * Complex.exp (lam * (μ * (x : ℂ))))⁻¹) v :=
      continuousAt_const.mul
        ((continuousAt_const.sub (continuousAt_const.mul
          (Complex.continuous_exp.continuousAt.comp hmul_cont))).inv₀ (hne_all v))
    exact hc.continuousWithinAt
  let a : ℝ := |(lam * μ).re|
  have ha_pos : 0 < a := abs_pos.mpr hre_ne0
  let δ : ℝ := 1 - Real.exp (-a)
  have hδ_pos : 0 < δ := by
    dsimp only [δ]; linarith [Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ha_pos)]
  refine expType_of_continuousOn_of_bdd hcont (C₁ := δ⁻¹) fun v hv => ?_
  have hre_v : (lam * (μ * (v : ℂ))).re = (lam * μ).re * v := by
    rw [← mul_assoc]; simp [Complex.mul_re]
  have hnorm_cexp : ‖c * Complex.exp (lam * (μ * (v : ℂ)))‖ = Real.exp ((lam * μ).re * v) := by
    rw [norm_mul, hc_norm, one_mul, Complex.norm_exp, hre_v]
  have hden_ge : δ ≤ ‖1 - c * Complex.exp (lam * (μ * (v : ℂ)))‖ := by
    rcases lt_or_gt_of_ne hre_ne0 with hneg | hpos
    · have hle : (lam * μ).re * v ≤ -a := by
        dsimp only [a]; rw [abs_of_neg hneg]; nlinarith
      have hnorm_le : ‖c * Complex.exp (lam * (μ * (v : ℂ)))‖ ≤ Real.exp (-a) := by
        rw [hnorm_cexp]; exact Real.exp_le_exp.mpr hle
      have htri := norm_sub_norm_le (1 : ℂ) (c * Complex.exp (lam * (μ * (v : ℂ))))
      rw [norm_one] at htri
      linarith
    · have hge : a ≤ (lam * μ).re * v := by
        dsimp only [a]; rw [abs_of_pos hpos]; nlinarith
      have hnorm_ge : Real.exp a ≤ ‖c * Complex.exp (lam * (μ * (v : ℂ)))‖ := by
        rw [hnorm_cexp]; exact Real.exp_le_exp.mpr hge
      have hsub1 : Real.exp a - 1 ≥ 1 - Real.exp (-a) := by
        have hexp_pos : 0 < Real.exp a := Real.exp_pos a
        rw [Real.exp_neg]
        have hsq : (Real.exp a - 1) - (1 - (Real.exp a)⁻¹) = (Real.exp a - 1) ^ 2 / Real.exp a := by
          field_simp [hexp_pos.ne']
        linarith [div_nonneg (sq_nonneg (Real.exp a - 1)) hexp_pos.le]
      have htri := norm_sub_norm_le (c * Complex.exp (lam * (μ * (v : ℂ)))) (1 : ℂ)
      rw [norm_one, norm_sub_rev] at htri
      linarith
  rw [Minor.pull, norm_mul, hμ_norm, one_mul, norm_inv]
  exact inv_anti₀ hδ_pos hden_ge

private lemma ratExp_pole_eval_and_deriv {lam c : ℂ} (hlam : lam ≠ 0) (hc_norm : ‖c‖ = 1) (m : ℕ) :
    let z_m : ℂ := Complex.exp (I * (ratExpRayAngle lam : ℂ)) * (ratExpPole lam c m : ℂ)
    1 - c * Complex.exp (lam * z_m) = 0 ∧
      deriv (fun z => 1 - c * Complex.exp (lam * z)) z_m = -lam := by
  intro z_m
  have hlamz : lam * z_m = I * (‖lam‖ : ℂ) * (ratExpPole lam c m : ℂ) := by
    dsimp only [z_m]; rw [← mul_assoc, mul_exp_ratExpRayAngle hlam]
  have hnorm_ne : (‖lam‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hlam)
  have harg_eq : lam * z_m = ((ratExpAngle c + 2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * I := by
    rw [hlamz]; unfold ratExpPole; push_cast; field_simp [hnorm_ne]
  have hc_exp : c * Complex.exp (lam * z_m) = 1 := by
    rw [harg_eq]
    push_cast
    rw [add_mul, Complex.exp_add,
      show (2 * (Real.pi : ℂ) * (m : ℂ)) * I = (m : ℂ) * (2 * Real.pi * I) by ring,
      Complex.exp_nat_mul_two_pi_mul_I, mul_one, exp_ratExpAngle hc_norm]
    have hc0 : c ≠ 0 := fun h => by rw [h, norm_zero] at hc_norm; norm_num at hc_norm
    exact mul_inv_cancel₀ hc0
  refine ⟨by rw [hc_exp, sub_self], ?_⟩
  have hd : HasDerivAt (fun z => 1 - c * Complex.exp (lam * z))
      (-(c * (Complex.exp (lam * z_m) * (lam * 1)))) z_m := by
    have he := (Complex.hasDerivAt_exp (lam * z_m)).comp z_m ((hasDerivAt_id z_m).const_mul lam)
    exact ((hasDerivAt_const z_m 1).sub (he.const_mul c)).congr_deriv (by ring)
  rw [hd.deriv, show -(c * (Complex.exp (lam * z_m) * (lam * 1))) = -(c * Complex.exp (lam * z_m) * lam) by ring,
    hc_exp, one_mul]

private lemma ratExp_exist (lam c : ℂ) (hlam : lam ≠ 0) (hc_norm : ‖c‖ = 1)
    (p : ℕ) (hp : 1 ≤ p) (m : ℕ) :
    ∃ (a : ℕ → ℂ) (L : ℂ),
      a p = 1 / deriv (fun z => 1 - c * Complex.exp (lam * z))
          (Complex.exp (I * (ratExpRayAngle lam : ℂ)) * (ratExpPole lam c m : ℂ)) ^ p ∧
        Filter.Tendsto
          (fun z : ℂ =>
            1 / (1 - c * Complex.exp (lam * z)) ^ p -
              ∑ s ∈ Finset.Icc 1 p, a s /
                (z - Complex.exp (I * (ratExpRayAngle lam : ℂ)) * (ratExpPole lam c m : ℂ)) ^ s)
          (𝓝[≠] (Complex.exp (I * (ratExpRayAngle lam : ℂ)) * (ratExpPole lam c m : ℂ)))
          (𝓝 L) :=
  let h := ratExp_pole_eval_and_deriv hlam hc_norm m
  pole_principalPart_of_simpleZero_div_pow
    (analyticAt_const (v := (1 : ℂ)))
    (analyticAt_const.sub (analyticAt_const.mul ((analyticAt_const.mul analyticAt_id).cexp)))
    h.1 (h.2.symm ▸ neg_ne_zero.mpr hlam) p hp

noncomputable def ratExpPP (lam c : ℂ) (hlam : lam ≠ 0) (hc_norm : ‖c‖ = 1)
    (p : ℕ) (hp : 1 ≤ p) (m s : ℕ) : ℂ :=
  (Classical.choose (ratExp_exist lam c hlam hc_norm p hp m)) s

/-- Genuine rotated `HigherOrderBorelData` witness for the general rational-exponential EGF
`E_{lam, c, p}(ξ) = (1 - c e^{lam ξ})⁻¹ ^ p` (`lam ≠ 0`, `‖c‖ = 1`, `c ≠ 1`, `p ≥ 1`). -/
def ratExp_borelData (lam c : ℂ) (hlam : lam ≠ 0) (hc_norm : ‖c‖ = 1) (hc_ne : c ≠ 1)
    (p : ℕ) (hp : 1 ≤ p) :
    HigherOrderBorelData (fun ξ => (1 - c * Complex.exp (lam * ξ))⁻¹ ^ p)
      (ratExpRayAngle lam) (ratExpPole lam c) (fun _ => p)
      (ratExpPP lam c hlam hc_norm p hp) where
  α₀ := Real.pi / 3
  θ := Real.pi / 4
  ε := min (ratExpAngle c / ‖lam‖) ((2 * Real.pi - ratExpAngle c) / ‖lam‖) / 2
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := by
    have hα := ratExpAngle_mem_Ioo hc_norm hc_ne
    have hnorm : 0 < ‖lam‖ := norm_pos_iff.mpr hlam
    have h1 : 0 < ratExpAngle c / ‖lam‖ := div_pos hα.1 hnorm
    have h2 : 0 < (2 * Real.pi - ratExpAngle c) / ‖lam‖ := div_pos (by linarith [hα.2]) hnorm
    positivity
  ω_pos := ratExpPole_pos hlam hc_norm hc_ne
  ω_mono := ratExpPole_mono hlam
  ord_pos := fun _ => hp
  pp_lead_ne_zero := fun m => by
    obtain ⟨L, hc_eq, _⟩ := Classical.choose_spec (ratExp_exist lam c hlam hc_norm p hp m)
    unfold ratExpPP
    rw [hc_eq, (ratExp_pole_eval_and_deriv hlam hc_norm m).2]
    exact div_ne_zero one_ne_zero (pow_ne_zero p (neg_ne_zero.mpr hlam))
  analyticOn := fun z hz => by
    have hne := one_sub_mul_exp_ne_zero_on_wedge hlam hc_norm hc_ne hz
    exact ((analyticAt_const.sub (analyticAt_const.mul
      ((analyticAt_const.mul analyticAt_id).cexp))).inv hne).pow p
  pole_principalPart := fun m => by
    obtain ⟨L, _, hL⟩ := Classical.choose_spec (ratExp_exist lam c hlam hc_norm p hp m)
    refine ⟨L, ?_⟩
    refine hL.congr' (eventually_nhdsWithin_of_forall fun z _ => ?_)
    simp only [ratExpPP, one_div, inv_pow]
  expType_plus := by
    have hsin : Real.sin (Real.pi / 4) ≠ 0 := by rw [Real.sin_pi_div_four]; positivity
    have h1 := ratExp_expType_ray hlam hc_norm hc_ne hsin
    exact expType_pull_pow (norm_exp_I_mul_real (ratExpRayAngle lam + Real.pi / 4)) h1 p
  expType_minus := by
    have hsin : Real.sin (-(Real.pi / 4)) ≠ 0 := by
      rw [Real.sin_neg, Real.sin_pi_div_four]; exact neg_ne_zero.mpr (by positivity)
    have h1 := ratExp_expType_ray hlam hc_norm hc_ne hsin
    have hpow := expType_pull_pow (norm_exp_I_mul_real (ratExpRayAngle lam + -(Real.pi / 4))) h1 p
    simpa [sub_eq_add_neg] using hpow

/-- **Showcase Corollary 4A (General Briot–Bouquet Rational-Exponential OGFs)**:
For ANY `lam ≠ 0`, ANY unit-circle `c` (`‖c‖ = 1, c ≠ 1`), and ANY pole order `p ≥ 1`,
`ogfOfEGF (fun ξ => (1 - c * Complex.exp (lam * ξ))⁻¹ ^ p)` is unconditionally differentially
transcendental over `ℂ(x)`. -/
theorem ratExpOGF_algebraicIndependent (lam c : ℂ) (hlam : lam ≠ 0) (hc_norm : ‖c‖ = 1)
    (hc_ne : c ≠ 1) (p : ℕ) (hp : 1 ≤ p) :
    AlgebraicIndependent ℂ
      (seriesCoordinates (ogfOfEGF fun ξ => (1 - c * Complex.exp (lam * ξ))⁻¹ ^ p)) :=
  ogf_algebraicIndependent_of_higherOrderBorel (ratExp_borelData lam c hlam hc_norm hc_ne p hp)

/-- Explicit autonomous Briot–Bouquet first-order algebraic ODE for `E(ξ) = (1 - c e^{lam ξ})⁻¹ ^ p`:
`(E'(ξ) + p lam E(ξ)) ^ p = (p lam) ^ p * E(ξ) ^ (p + 1)`. -/
theorem ratExp_D_algebraic (lam c : ℂ) (p : ℕ) {ξ : ℂ}
    (hne : 1 - c * Complex.exp (lam * ξ) ≠ 0) :
    let E : ℂ → ℂ := fun z => (1 - c * Complex.exp (lam * z))⁻¹ ^ p
    (deriv E ξ + (p : ℂ) * lam * E ξ) ^ p = ((p : ℂ) * lam) ^ p * E ξ ^ (p + 1) := by
  intro E
  let w : ℂ → ℂ := fun z => 1 - c * Complex.exp (lam * z)
  have hw_deriv : HasDerivAt w (-(c * (Complex.exp (lam * ξ) * (lam * 1)))) ξ := by
    have he := (Complex.hasDerivAt_exp (lam * ξ)).comp ξ ((hasDerivAt_id ξ).const_mul lam)
    exact ((hasDerivAt_const ξ 1).sub (he.const_mul c)).congr_deriv (by ring)
  have hinv_deriv : HasDerivAt (fun z => (w z)⁻¹)
      (-(-(c * (Complex.exp (lam * ξ) * (lam * 1)))) / w ξ ^ 2) ξ :=
    hw_deriv.inv hne
  have hpow_deriv := hinv_deriv.pow p
  have hE_deriv : deriv E ξ = (p : ℂ) * lam * (c * Complex.exp (lam * ξ)) * (w ξ)⁻¹ ^ (p + 1) := by
    rw [show E = fun z => (w z)⁻¹ ^ p from rfl]
    change deriv ((fun z => (w z)⁻¹) ^ p) ξ = _
    rw [hpow_deriv.deriv]
    cases p with
    | zero => simp
    | succ q =>
      rw [Nat.succ_sub_one, pow_succ', inv_pow, inv_pow]
      field_simp [hne]
      ring
  have hsum : deriv E ξ + (p : ℂ) * lam * E ξ = (p : ℂ) * lam * (w ξ)⁻¹ ^ (p + 1) := by
    have hc_eq : c * Complex.exp (lam * ξ) = 1 - w ξ := by dsimp only [w]; ring
    rw [hE_deriv, hc_eq]
    dsimp only [E]
    calc (p : ℂ) * lam * (1 - w ξ) * (w ξ)⁻¹ ^ (p + 1) + (p : ℂ) * lam * (w ξ)⁻¹ ^ p
        = (p : ℂ) * lam * (w ξ)⁻¹ ^ (p + 1) -
            (p : ℂ) * lam * (w ξ * (w ξ)⁻¹) * (w ξ)⁻¹ ^ p + (p : ℂ) * lam * (w ξ)⁻¹ ^ p := by
          rw [pow_succ (w ξ)⁻¹ p]; ring
      _ = (p : ℂ) * lam * (w ξ)⁻¹ ^ (p + 1) := by
          rw [mul_inv_cancel₀ hne, mul_one]; ring
  rw [hsum, mul_pow, ← pow_mul, mul_comm (p + 1) p, pow_mul]

/-- **Showcase Corollary 4B (Euler / Genocchi Arbitrary-Order Family `(1 + e^ξ)⁻¹ ^ p`)**:
For every `p ≥ 1`, `ogfOfEGF (fun ξ => (1 + Complex.exp ξ)⁻¹ ^ p)` is unconditionally
differentially transcendental over `ℂ(x)`. -/
theorem eulerGenocchiPowOGF_algebraicIndependent (p : ℕ) (hp : 1 ≤ p) :
    AlgebraicIndependent ℂ
      (seriesCoordinates (ogfOfEGF fun ξ => (1 + Complex.exp ξ)⁻¹ ^ p)) := by
  have h := ratExpOGF_algebraicIndependent (1 : ℂ) (-1 : ℂ) one_ne_zero (by simp)
    (by norm_num) p hp
  simpa [sub_neg_eq_add, one_mul] using h

/-! ### 7. Showcase Corollary 5: Higher-Order Dirichlet, Trigamma, and Lambert OGFs -/

/-- **Showcase Corollary 5A (Hurwitz / Zeta Double-Pole OGF)**:
(Remark: mathematically this corresponds to `∑_{k ≥ 0} (k + 1)! ζ(k + 2) x^k`, not proved here.)
`ogfOfEGF trigammaSeries` is unconditionally differentially
transcendental over `ℂ(x)`. -/
theorem trigammaOGF_algebraicIndependent :
    AlgebraicIndependent ℂ (seriesCoordinates (ogfOfEGF trigammaSeries)) :=
  ogf_algebraicIndependent_of_higherOrderBorel trigammaSeries_borelData

/-- **Showcase Corollary 5B (Rotated Lambert Divisor Double-Pole OGF)**:
For any `θ₀ : ℝ`, `ogfOfEGF (lambertBorelSeries θ₀)` is unconditionally differentially
transcendental over `ℂ(x)`. -/
theorem lambertOGF_algebraicIndependent (θ₀ : ℝ) :
    AlgebraicIndependent ℂ (seriesCoordinates (ogfOfEGF (lambertBorelSeries θ₀))) :=
  ogf_algebraicIndependent_of_higherOrderBorel (lambertBorelSeries_borelData θ₀)

/-- **Showcase Corollary 5C (Rotated Triple-Pole OGF)**:
For any `θ₀ : ℝ`, `ogfOfEGF (triplePoleSeries θ₀)` is unconditionally differentially
transcendental over `ℂ(x)`. -/
theorem triplePoleOGF_algebraicIndependent (θ₀ : ℝ) :
    AlgebraicIndependent ℂ (seriesCoordinates (ogfOfEGF (triplePoleSeries θ₀))) :=
  ogf_algebraicIndependent_of_higherOrderBorel (triplePoleSeries_borelData θ₀)

/-- **Showcase Corollary 5D (General Higher-Order Dirichlet-Pole OGFs)**:
For any `p ≥ 2`, `θ₀ : ℝ`, and nonzero summable coefficients `c : ℕ → ℂ`,
`ogfOfEGF (dirichletPoleSeries c θ₀ p)` is unconditionally differentially transcendental over `ℂ(x)`. -/
theorem dirichletPoleOGF_algebraicIndependent
    (c : ℕ → ℂ) (θ₀ : ℝ) (p : ℕ) (hp : 2 ≤ p)
    (hc_ne : ∀ n : ℕ, 1 ≤ n → c n ≠ 0)
    (hsumm : Summable (fun n : ℕ => ‖c (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ p)) :
    AlgebraicIndependent ℂ (seriesCoordinates (ogfOfEGF (dirichletPoleSeries c θ₀ p))) :=
  ogf_algebraicIndependent_of_higherOrderBorel
    (dirichletPoleSeries_borelData c θ₀ p hp hc_ne hsumm)

end
end PakPrimes.PakYeliussizovEGF
